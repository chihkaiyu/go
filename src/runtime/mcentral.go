// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Central free lists.
//
// See malloc.go for an overview.
//
// The mcentral doesn't actually contain the list of free objects; the mspan does.
// Each mcentral is two lists of mspans: those with free objects (c->nonempty)
// and those that are completely allocated (c->empty).

package runtime

import "runtime/internal/atomic"

// Central list of free objects of a given size.
//
//go:notinheap
type mcentral struct {
	lock      mutex     // 可能同時會有多個 mcache 向 mcentral 要求 mspan，所以需要 lcok
	spanclass spanClass // 表示此 mcentral 是負責哪個 span class
	nonempty  mSpanList // 仍有可用 object 的 mspan linked list
	empty     mSpanList // 無可用 object 的 mspan linked list 或是被 cached 在 mcache 了

	// nmalloc is the cumulative count of objects allocated from
	// this mcentral, assuming all spans in mcaches are
	// fully-allocated. Written atomically, read under STW.
	nmalloc uint64 // 此 mcentral 所分配的 object 數量
}

// Initialize a single central free list.
func (c *mcentral) init(spc spanClass) {
	c.spanclass = spc
	c.nonempty.init()
	c.empty.init()
}

// Allocate a span to use in an mcache.
func (c *mcentral) cacheSpan() *mspan {
	// Deduct credit for this span allocation and sweep if necessary.
	spanBytes := uintptr(class_to_allocnpages[c.spanclass.sizeclass()]) * _PageSize
	deductSweepCredit(spanBytes, 0)

	lock(&c.lock) // mcentral 是共用的，需要 lock
	traceDone := false
	if trace.enabled {
		traceGCSweepStart()
	}
	sg := mheap_.sweepgen
retry:
	var s *mspan
	// 試著在 nonempty mspan linked-list (還有可用 object 的 mspan) 找出可用的 mspan
	for s = c.nonempty.first; s != nil; s = s.next {
		// sg-2 代表該 mspan 需要 sweep，試著將他的狀態改成 sg-1，即為該 mspan 正在被 swept
		if s.sweepgen == sg-2 && atomic.Cas(&s.sweepgen, sg-2, sg-1) {
			c.nonempty.remove(s)  // 將該 mspan 從 nonempty 移除
			c.empty.insertBack(s) // 將該 mspan insert 到 empty 的尾巴
			unlock(&c.lock)       // 找到可用的 mspan 了，可以 unlock mcentral 了
			s.sweep(true)         // sweep 該 mspan
			goto havespan
		}
		if s.sweepgen == sg-1 {
			// the span is being swept by background sweeper, skip
			continue
		}
		// we have a nonempty span that does not require sweeping, allocate from it
		// 該 mspan 可以直接使用，不需 sweep，直接將他從 nonempty 移除，並 insert 到 empty 的尾巴
		c.nonempty.remove(s)
		c.empty.insertBack(s)
		unlock(&c.lock)
		goto havespan
	}

	// 試著在 empty mspan linked-list (已經沒有空間或被 cached 的 mspan) 找出可用的 mspan
	for s = c.empty.first; s != nil; s = s.next {
		// 與上面一樣，找出需 sweep 的 mspan 並試著改他的狀態
		if s.sweepgen == sg-2 && atomic.Cas(&s.sweepgen, sg-2, sg-1) {
			// we have an empty span that requires sweeping,
			// sweep it and see if we can free some space in it
			c.empty.remove(s)
			// swept spans are at the end of the list
			c.empty.insertBack(s)
			unlock(&c.lock)

			// sweep 該 mspan
			s.sweep(true)

			// 看看 swept 後的 mspan 的 freeIndex 是否可用
			freeIndex := s.nextFreeIndex()
			if freeIndex != s.nelems {
				s.freeindex = freeIndex
				goto havespan
			}
			lock(&c.lock)
			// the span is still empty after sweep
			// it is already in the empty list, so just retry
			// 該 mspan 在 swept 後還是空的，並且已經在 empty 裡了，直接 retry
			// 這裡我自己也不是很清楚為什麼是直接 retry，而不是繼續檢查 empty list 裡的其他 mspan
			goto retry
		}
		if s.sweepgen == sg-1 {
			// the span is being swept by background sweeper, skip
			continue
		}
		// already swept empty span,
		// all subsequent ones must also be either swept or in process of sweeping
		// 上面是原文註解，但我依然不是很清楚為什麼這裡直接 break。
		// 例如第一個 mspan 是不需要 sweep 的話 (單純滿了)，那便直接 break 不繼續檢查其他 mspan 了嗎？
		break
	}
	if trace.enabled {
		traceGCSweepDone()
		traceDone = true
	}
	unlock(&c.lock)

	// Replenish central list if empty.
	s = c.grow() // 在 nonempty 及 empty 都找不到可用的 mspan，需要向 mheap 申請
	if s == nil {
		return nil
	}
	lock(&c.lock)
	c.empty.insertBack(s)
	unlock(&c.lock)

	// At this point s is a non-empty span, queued at the end of the empty list,
	// c is unlocked.
havespan:
	if trace.enabled && !traceDone {
		traceGCSweepDone()
	}
	n := int(s.nelems) - int(s.allocCount)
	if n == 0 || s.freeindex == s.nelems || uintptr(s.allocCount) == s.nelems {
		throw("span has no free objects")
	}
	// Assume all objects from this span will be allocated in the
	// mcache. If it gets uncached, we'll adjust this.
	atomic.Xadd64(&c.nmalloc, int64(n))
	usedBytes := uintptr(s.allocCount) * s.elemsize
	atomic.Xadd64(&memstats.heap_live, int64(spanBytes)-int64(usedBytes))
	if trace.enabled {
		// heap_live changed.
		traceHeapAlloc()
	}
	if gcBlackenEnabled != 0 {
		// heap_live changed.
		gcController.revise()
	}
	freeByteBase := s.freeindex &^ (64 - 1)
	whichByte := freeByteBase / 8
	// Init alloc bits cache.
	s.refillAllocCache(whichByte)

	// Adjust the allocCache so that s.freeindex corresponds to the low bit in
	// s.allocCache.
	s.allocCache >>= s.freeindex % 64

	return s
}

// Return span from an mcache.
func (c *mcentral) uncacheSpan(s *mspan) {
	if s.allocCount == 0 {
		throw("uncaching span but s.allocCount == 0")
	}

	sg := mheap_.sweepgen
	stale := s.sweepgen == sg+1
	if stale {
		// Span was cached before sweep began. It's our
		// responsibility to sweep it.
		//
		// Set sweepgen to indicate it's not cached but needs
		// sweeping and can't be allocated from. sweep will
		// set s.sweepgen to indicate s is swept.
		atomic.Store(&s.sweepgen, sg-1)
	} else {
		// Indicate that s is no longer cached.
		atomic.Store(&s.sweepgen, sg)
	}

	n := int(s.nelems) - int(s.allocCount)
	if n > 0 {
		// cacheSpan updated alloc assuming all objects on s
		// were going to be allocated. Adjust for any that
		// weren't. We must do this before potentially
		// sweeping the span.
		atomic.Xadd64(&c.nmalloc, -int64(n))

		lock(&c.lock)
		c.empty.remove(s)
		c.nonempty.insert(s)
		if !stale {
			// mCentral_CacheSpan conservatively counted
			// unallocated slots in heap_live. Undo this.
			//
			// If this span was cached before sweep, then
			// heap_live was totally recomputed since
			// caching this span, so we don't do this for
			// stale spans.
			atomic.Xadd64(&memstats.heap_live, -int64(n)*int64(s.elemsize))
		}
		unlock(&c.lock)
	}

	if stale {
		// Now that s is in the right mcentral list, we can
		// sweep it.
		s.sweep(false)
	}
}

// freeSpan updates c and s after sweeping s.
// It sets s's sweepgen to the latest generation,
// and, based on the number of free objects in s,
// moves s to the appropriate list of c or returns it
// to the heap.
// freeSpan reports whether s was returned to the heap.
// If preserve=true, it does not move s (the caller
// must take care of it).
func (c *mcentral) freeSpan(s *mspan, preserve bool, wasempty bool) bool {
	if sg := mheap_.sweepgen; s.sweepgen == sg+1 || s.sweepgen == sg+3 {
		throw("freeSpan given cached span")
	}
	s.needzero = 1

	if preserve {
		// preserve is set only when called from (un)cacheSpan above,
		// the span must be in the empty list.
		if !s.inList() {
			throw("can't preserve unlinked span")
		}
		atomic.Store(&s.sweepgen, mheap_.sweepgen)
		return false
	}

	lock(&c.lock)

	// Move to nonempty if necessary.
	if wasempty {
		c.empty.remove(s)
		c.nonempty.insert(s)
	}

	// delay updating sweepgen until here. This is the signal that
	// the span may be used in an mcache, so it must come after the
	// linked list operations above (actually, just after the
	// lock of c above.)
	atomic.Store(&s.sweepgen, mheap_.sweepgen)

	if s.allocCount != 0 {
		unlock(&c.lock)
		return false
	}

	c.nonempty.remove(s)
	unlock(&c.lock)
	mheap_.freeSpan(s, false)
	return true
}

// grow allocates a new empty span from the heap and initializes it for c's size class.
func (c *mcentral) grow() *mspan {
	// 根據該 mcentral 的 spanclass 計算要申請的量
	npages := uintptr(class_to_allocnpages[c.spanclass.sizeclass()])
	size := uintptr(class_to_size[c.spanclass.sizeclass()])
	n := (npages << _PageShift) / size

	s := mheap_.alloc(npages, c.spanclass, false, true) // 向 mheap 申請 mspan 來使用
	if s == nil {
		return nil
	}

	p := s.base()
	s.limit = p + size*n

	heapBitsForAddr(s.base()).initSpan(s)
	return s
}
