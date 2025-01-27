// Original work -- Copyright 2015 The Rust Project Developers. See the COPYRIGHT file at the
// top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Modified work -- Copyright 2021 Ves Language Developers
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT
// or http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use std::ptr::NonNull;
use std::{cell::RefCell, rc::Rc};

use crate::{proxy_allocator::ProxyAllocator, Cc, Trace};

use super::Color;
use cc_box_ptr::{free, CcBoxPtr};

pub(crate) type Ptr<T> = Rc<T>;
pub(crate) type ContextPtr = Ptr<InnerCcContext>;

/// The default minimum number of roots required to trigger the GC.
pub const GC_DEFAULT_MIN_ROOTS_TO_TRIGGER: usize = 1000;

/// The default minimum number of bytes required to trigger the GC.
pub const GC_DEFAULT_MIN_BYTES_TO_TRIGGER: usize = 1024 * 1024; // 1MB

/// The multiplier that will be used to adjust the GC threshold after every automatic collection cycle.
pub const GC_DEFAULT_HEAP_GROWTH_FACTOR: f64 = 2.0;

/// A Cc context that wraps the roots used by the GC to collect reference cycles in the object graph.
/// The context calls collect_cycles() in its [`Drop`] impl to ensure that no memory is leaked.
/// Note: The user must be careful not to create cycles between [`Cc`]s from different contexts. The implementation will panic
/// in debug builds should a cycle like this be found during collection.
#[derive(Default, Debug, Clone)]
pub struct CcContext {
    pub(crate) inner: ContextPtr,
}

impl std::ops::Drop for CcContext {
    fn drop(&mut self) {
        if Ptr::strong_count(&self.inner) == self.inner.number_of_roots_buffered() + 1 {
            self.collect_cycles();
        }
    }
}

impl CcContext {
    /// Creates a new [`CcContext`].
    pub fn new() -> Self {
        Self {
            inner: Ptr::new(InnerCcContext {
                roots: RefCell::new(Vec::new()),
                #[cfg(feature = "auto_gc")]
                gc: RefCell::new(GcData::default()),
            }),
        }
    }

    /// Allocates a new `Cc` in this context.
    #[inline]
    pub fn cc<T: Trace>(&self, obj: T) -> Cc<T> {
        Cc::new(self.inner.clone(), obj)
    }

    /// Returns the nubmer of references to the context.
    #[inline]
    pub fn n_context_refs(&self) -> usize {
        Ptr::strong_count(&self.inner)
    }

    /// Creates a new `Cc<T>`, with the `Default` value for `T`.
    ///
    /// # Examples
    ///
    /// ```

    /// use bacon_rajan_cc::{Cc, CcContext};
    ///
    /// let ctx = CcContext::new();
    /// let x: Cc<i32> = ctx.default();
    /// assert_eq!(*x, 0);
    /// ```
    #[inline]
    pub fn default<T>(&self) -> Cc<T>
    where
        T: Default + Trace,
    {
        self.cc(Default::default())
    }

    /// Return the number of potential cycle roots currently buffered for cycle
    /// collection.
    ///
    /// Whenever a `Cc<T>`'s reference count is decremented, it has the possibility
    /// of becoming the root of some cycle that is no longer live and can now be
    /// reclaimed. These possible roots are buffered for cycle detection and
    /// collection at a later point in time. This enables library users to avoid
    /// frequent tracing and perform that tracing at a convenient time. Part of
    /// choosing a convenient time might be when the number of potential cycle roots
    /// reaches some critical threshold. This method allows you to check the current
    /// number of possible roots buffered.
    ///
    /// ```rust
    /// use bacon_rajan_cc::{CcContext, Cc, Trace, Tracer};
    /// use std::cell::RefCell;
    ///
    /// struct Gadget {
    ///     parent: Option<Cc<RefCell<Gadget>>>,
    ///     children: Vec<Cc<RefCell<Gadget>>>,
    ///     // ...
    /// }
    ///
    /// impl Trace for Gadget {
    ///     fn trace(&self, _tracer: &mut Tracer) { /* ... */ }
    /// }
    ///
    /// fn add_child(parent: &mut Cc<RefCell<Gadget>>) -> Cc<RefCell<Gadget>> {
    ///     let child = parent.get_context().cc(RefCell::new(Gadget { parent: None, children: vec!() }));
    ///     child.borrow_mut().parent = Some(parent.clone());
    ///     parent.borrow_mut().children.push(child.clone());
    ///     child
    /// }
    ///
    /// pub fn main() {
    ///     let ctx = CcContext::new();
    ///
    ///     // No possible roots, as we haven't created any `Cc<T>`s yet.
    ///     assert_eq!(ctx.number_of_roots_buffered(), 0);
    ///
    ///     {
    ///         let mut parent = ctx.cc(RefCell::new(Gadget { parent: None, children: vec!() }));
    ///         let mut children = vec!();
    ///         for _ in 0..10 {
    ///             children.push(add_child(&mut parent));
    ///         }
    ///
    ///         // No possible roots, we have only incremented reference counts and
    ///         // created new `Cc<T>`s. We have not decremented any reference
    ///         // counts or created any dead cycles.
    ///         assert_eq!(ctx.number_of_roots_buffered(), 0);
    ///     }
    ///
    ///     // None of the Gadgets are reachable anymore, but they had cyclic
    ///     // references between parents and children. However, because their
    ///     // reference counts were decremented when we left the block, they should
    ///     // be buffered for cycle collection.
    ///     assert_eq!(ctx.number_of_roots_buffered(),
    ///                1 /* parent */ + 10 /* children */);
    ///
    ///     // If we had actually implemented `Trace` for `Gadget` rather than just
    ///     // stubbing it out, we could call `collect_cycles` here to reclaim the
    ///     // cycle.
    /// }
    /// ```
    #[inline]
    pub fn number_of_roots_buffered(&self) -> usize {
        self.inner.number_of_roots_buffered()
    }

    /// Invoke cycle collection for all `Cc<T>`s on this thread.
    ///
    /// You may wish to do this when the roots buffer reaches a certain size, when
    /// memory is low, or at opportune moments within your application (such as when
    /// the user has been inactive for `n` seconds in a GUI application).
    ///
    /// This happens in three phases:
    ///
    /// 1. `mark_roots`: We mark the roots and decrement reference counts as we
    /// go. This is optimistically removing the strong references held by the
    /// potentially dead cycles.
    ///
    /// 2. `scan_roots`: Then we perform a second traversal which marks the garbage
    /// nodes with a reference count of 0 as White and the non-garbage nodes with a
    /// reference count > 0 as Black. The latter group's reference count is restored
    /// to its previous value from before step (1).
    ///
    /// 3. `collect_roots`: Finally, the buffer of possible dead cycle roots is
    /// emptied and members of dead cycles (White nodes) are dropped.
    ///
    /// ```rust
    /// use bacon_rajan_cc::{Cc, CcContext, Trace, Tracer};
    /// use std::cell::RefCell;
    ///
    /// // The number of Gadgets allocated at any given time.
    /// thread_local!(static GADGET_COUNT: RefCell<usize> = RefCell::new(0));
    ///
    /// struct Gadget {
    ///     parent: Option<Cc<RefCell<Gadget>>>,
    ///     children: Vec<Cc<RefCell<Gadget>>>,
    ///     // ...
    /// }
    ///
    /// impl Gadget {
    ///     fn new() -> Gadget {
    ///         GADGET_COUNT.with(|c| *c.borrow_mut() += 1);
    ///         Gadget { parent: None, children: vec!() }
    ///     }
    /// }
    ///
    /// impl Trace for Gadget {
    ///     fn trace(&self, tracer: &mut Tracer) {
    ///         self.parent.trace(tracer);
    ///         self.children.trace(tracer);
    ///     }
    /// }
    ///
    /// impl Drop for Gadget {
    ///     fn drop(&mut self) {
    ///         GADGET_COUNT.with(|c| *c.borrow_mut() -= 1);
    ///     }
    /// }
    ///
    /// fn add_child(parent: &mut Cc<RefCell<Gadget>>) -> Cc<RefCell<Gadget>> {
    ///     let child = parent.get_context().cc(RefCell::new(Gadget::new()));
    ///     child.borrow_mut().parent = Some(parent.clone());
    ///     parent.borrow_mut().children.push(child.clone());
    ///     child
    /// }
    ///
    /// pub fn main() {
    ///     // Initially, no gadgets.
    ///     GADGET_COUNT.with(|c| assert_eq!(*c.borrow(), 0));
    ///
    ///     let ctx = CcContext::new();
    ///     {
    ///         // Create cycles.
    ///
    ///         let mut parent = ctx.cc(RefCell::new(Gadget::new()));
    ///         for _ in 0..10 {
    ///             add_child(&mut parent);
    ///         }
    ///
    ///         // We created 1 parent and 10 child gadgets.
    ///         GADGET_COUNT.with(|c| assert_eq!(*c.borrow(), 11));
    ///     }
    ///
    ///     // The members of the cycle are now dead, but because of the cycles
    ///     // could not be eagerly collected.
    ///     GADGET_COUNT.with(|c| assert_eq!(*c.borrow(), 11));
    ///
    ///     // After calling `collect_cycles`, the cycles are detected and the
    ///     // members of the dead cycles are dropped.
    ///     ctx.collect_cycles();
    ///     GADGET_COUNT.with(|c| assert_eq!(*c.borrow(), 0));
    /// }
    /// ```
    #[inline]
    pub fn collect_cycles(&self) {
        self.inner.collect_cycles()
    }

    /// Returns the proxy allocator used by this context. You should only use this allocator
    /// inside the objects held by [`Cc`]s. Using it elsewhere will result in nonsensical GC triggers
    /// unrelated to the actual memory used by the object graph.
    #[cfg(feature = "auto_gc")]
    #[inline(always)]
    pub fn proxy_allocator(&self) -> ProxyAllocator {
        self.inner.proxy_allocator()
    }

    /// Returns the number of bytes allocated with the proxy allocator.
    /// This number includes the bookkeeping memory of each [`Cc`] pointer.
    #[cfg(feature = "auto_gc")]
    #[inline]
    pub fn bytes_allocated(&self) -> usize {
        self.inner.gc.borrow().alloc.bytes_allocated()
    }

    /// Returns the number of bytes required to kick off the next garbage collection cycle.
    #[cfg(feature = "auto_gc")]
    #[inline]
    pub fn gc_threshold(&self) -> usize {
        self.inner.gc.borrow().gc_threshold
    }

    /// Returns the minimum number of bytes required to kick off a garbage collection cycle.
    /// The adaptive threshold never goes below this value.
    #[cfg(feature = "auto_gc")]
    #[inline]
    pub fn min_gc_threshold(&self) -> usize {
        self.inner.gc.borrow().min_gc_threshold
    }

    /// Returns minimum number of cycle roots required to kick off the next garbage collection cycle.
    /// This strategy works independently from [`gc_threshold`].
    #[cfg(feature = "auto_gc")]
    #[inline]
    pub fn root_threshold(&self) -> usize {
        self.inner.gc.borrow().root_threshold
    }

    /// Returns the factor that will be used to grow or shrink the GC threshold every time an automatic GC pass runs.
    #[cfg(feature = "auto_gc")]
    #[inline]
    pub fn heap_growth_factor(&self) -> f64 {
        self.inner.gc.borrow().heap_growth_factor
    }

    /// Sets the minimum number of bytes required to kick off the next garbage collection cycle.
    /// Settings this to 0 is equivalent to disabling the memory-based GC trigger.
    #[cfg(feature = "auto_gc")]
    #[inline]
    pub fn set_gc_threshold(&self, n: usize) {
        let mut gc = self.inner.gc.borrow_mut();
        gc.min_gc_threshold = n;
        gc.gc_threshold = n;
    }

    /// Sets the minimum number of roots required to kick off the next garbage collection cycle.
    /// Settings this to 0 is equivalent to disabling the root-based GC trigger.
    #[cfg(feature = "auto_gc")]
    #[inline]
    pub fn set_root_threshold(&self, n: usize) {
        self.inner.gc.borrow_mut().root_threshold = n;
    }

    /// Sets the factor that will be used to grow or shrink the GC threshold every time an automatic GC pass runs.
    #[cfg(feature = "auto_gc")]
    #[inline]
    pub fn set_heap_growth_factor(&self, factor: f64) {
        self.inner.gc.borrow_mut().heap_growth_factor = factor;
    }
}

#[derive(Debug)]
pub(crate) struct GcData {
    heap_growth_factor: f64,
    min_gc_threshold: usize,
    gc_threshold: usize,
    root_threshold: usize,
    alloc: ProxyAllocator,
}

impl Default for GcData {
    fn default() -> Self {
        Self {
            heap_growth_factor: GC_DEFAULT_HEAP_GROWTH_FACTOR,
            min_gc_threshold: GC_DEFAULT_MIN_BYTES_TO_TRIGGER,
            gc_threshold: GC_DEFAULT_MIN_BYTES_TO_TRIGGER,
            root_threshold: GC_DEFAULT_MIN_ROOTS_TO_TRIGGER,
            alloc: ProxyAllocator::new(),
        }
    }
}

#[derive(Default, Debug)]
pub(crate) struct InnerCcContext {
    roots: RefCell<Vec<NonNull<dyn CcBoxPtr>>>,
    #[cfg(feature = "auto_gc")]
    gc: RefCell<GcData>,
}

impl InnerCcContext {
    #[cfg(feature = "auto_gc")]
    #[inline]
    pub fn proxy_allocator(&self) -> ProxyAllocator {
        self.gc.borrow().alloc.clone()
    }

    /// May trigger the GC if either the root threshold or memory usage threshold has been reached.
    #[cfg(feature = "auto_gc")]
    pub fn maybe_run_gc(&self) {
        let gc = self.gc.borrow();

        if (self.roots.borrow().len() < gc.root_threshold || gc.root_threshold == 0)
            && (gc.alloc.bytes_allocated() < gc.gc_threshold || gc.gc_threshold == 0)
        {
            return;
        }

        #[cfg(feature = "gc_debug")]
        log::info!(
            "[GC] Triggered garbage collection with (roots: {} >= {}) or (bytes: {}b > {}b)",
            self.roots.borrow().len(),
            gc.root_threshold,
            gc.alloc.bytes_allocated(),
            gc.gc_threshold
        );

        #[cfg(feature = "gc_debug")]
        log::info!(
            "[GC] Starting the garbage collector with HEAP = {}b",
            gc.alloc.bytes_allocated(),
        );

        #[cfg(feature = "gc_debug")]
        let before = gc.alloc.bytes_allocated();
        self.collect_cycles();
        let after = gc.alloc.bytes_allocated();
        let factor = gc.heap_growth_factor;
        let min = gc.min_gc_threshold;

        std::mem::drop(gc);

        let new_threshold = ((factor * after as f64) as usize).max(min);
        self.gc.borrow_mut().gc_threshold = new_threshold;

        #[cfg(feature = "gc_debug")]
        log::info!(
            "[GC] GC has finished, changing the heap size ({}b -> {}b). Next collection will performed at HEAP = {}b",
            before, after, new_threshold
        );
    }

    #[cfg(not(debug_assertions))]
    fn check_ptr_ref_is_from_the_same_context(&self, _box_ptr: &dyn CcBoxPtr) {}

    #[cfg(debug_assertions)]
    fn check_ptr_ref_is_from_the_same_context(&self, box_ptr: &dyn CcBoxPtr) {
        let ctx = Ptr::into_raw(box_ptr.data().ctx.clone());

        // Check that the given Cc belongs to the same context
        debug_assert_eq!(
            Ptr::as_ptr(&box_ptr.data().ctx),
            self as *const _,
            "Attempted to mix Ccs from different contexts"
        );

        unsafe { Ptr::from_raw(ctx) };
    }

    fn check_ptr_is_from_the_same_context(&self, box_ptr: NonNull<dyn CcBoxPtr>) {
        self.check_ptr_ref_is_from_the_same_context(unsafe { box_ptr.as_ref() })
    }

    #[inline]
    pub(crate) fn add_root(&self, box_ptr: NonNull<dyn CcBoxPtr>) {
        self.check_ptr_is_from_the_same_context(box_ptr);
        self.roots.borrow_mut().push(box_ptr);
    }

    #[inline]
    pub fn number_of_roots_buffered(&self) -> usize {
        self.roots.borrow().len()
    }

    pub fn collect_cycles(&self) {
        self.mark_roots();
        self.scan_roots();
        self.collect_roots();
    }

    /// Consider every node that's been stored in the buffer since the last
    /// collection. If the node is Purple, then the last operation on it was a
    /// decrement of its reference count, and it hasn't been touched since then. It
    /// is potentially the root of a garbage cycle. Perform a graph traversal and
    /// optimistically decrement reference counts as we go. At the end of the
    /// traversal, anything whose reference count became 0 was part of a garbage
    /// cycle. Anything whose reference count did not become 0 was not part of a
    /// garbage cycle, and we will have to restore its old reference count in
    /// `scan_roots`.
    fn mark_roots(&self) {
        fn mark_gray(this: &InnerCcContext, cc_box_ptr: &dyn CcBoxPtr) {
            this.check_ptr_ref_is_from_the_same_context(cc_box_ptr);

            if cc_box_ptr.color() == Color::Gray {
                return;
            }

            cc_box_ptr.data().color.set(Color::Gray);

            cc_box_ptr.trace(&mut |t| {
                t.dec_strong();
                mark_gray(this, t);
            });
        }

        let old_roots: Vec<_> = {
            let mut v = self.roots.borrow_mut();
            let drained = v.drain(..);
            drained.collect()
        };

        #[allow(clippy::unnecessary_filter_map)]
        let mut new_roots: Vec<_> = old_roots
            .into_iter()
            .filter_map(|s| {
                self.check_ptr_is_from_the_same_context(s);

                let keep = unsafe {
                    let box_ptr: &dyn CcBoxPtr = s.as_ref();
                    if box_ptr.color() == Color::Purple {
                        mark_gray(&self, box_ptr);
                        true
                    } else {
                        box_ptr.data().buffered.set(false);

                        if box_ptr.color() == Color::Black && box_ptr.strong() == 0 {
                            free(s);
                        }

                        false
                    }
                };

                if keep {
                    Some(s)
                } else {
                    None
                }
            })
            .collect();

        let mut v = self.roots.borrow_mut();
        v.append(&mut new_roots);
    }

    /// This is the second traversal, after marking. Color each node in the graph as
    /// White nodes if its reference count is 0 and it is part of a garbage cycle,
    /// or Black if the node is still live.
    fn scan_roots(&self) {
        fn scan_black(this: &InnerCcContext, s: &dyn CcBoxPtr) {
            this.check_ptr_ref_is_from_the_same_context(s);

            s.data().color.set(Color::Black);
            s.trace(&mut |t| {
                t.data().strong.set(t.strong() + 1);
                if t.color() != Color::Black {
                    scan_black(this, t);
                }
            });
        }

        fn scan(this: &InnerCcContext, s: &dyn CcBoxPtr) {
            if s.color() != Color::Gray {
                return;
            }

            if s.strong() > 0 {
                scan_black(this, s);
            } else {
                s.data().color.set(Color::White);
                s.trace(&mut |t| {
                    scan(this, t);
                });
            }
        }

        let mut v = self.roots.borrow_mut();
        for s in &mut *v {
            self.check_ptr_is_from_the_same_context(*s);
            let p: &mut dyn CcBoxPtr = unsafe { s.as_mut() };
            scan(&self, p);
        }
    }

    /// Go through all the White roots and their garbage cycles and collect these nodes.
    /// If a White node is still in the roots buffer, then leave it
    /// there. It will be freed in the next collection when we iterate over the
    /// buffer in `mark_roots`.
    fn collect_roots(&self) {
        // Collecting the nodes into this Vec is a difference from the original
        // Bacon-Rajan paper. We need this because we have destructors and
        // running them during traversal will cause cycles to be broken which
        // ruins the rest of our traversal.
        let mut white = Vec::new();

        fn collect_white(
            this: &InnerCcContext,
            s: &(dyn CcBoxPtr + 'static),
            white: &mut Vec<NonNull<dyn CcBoxPtr>>,
        ) {
            this.check_ptr_ref_is_from_the_same_context(s);

            if s.color() == Color::White && !s.buffered() {
                s.data().color.set(Color::Black);
                s.trace(&mut |t| {
                    collect_white(&this, t, white);
                });
                s.inc_weak();
                white.push(s.into());
            }
        }

        {
            let mut v = self.roots.borrow_mut();
            for s in v.drain(..) {
                let ptr: &dyn CcBoxPtr = unsafe { s.as_ref() };
                ptr.data().buffered.set(false);
                if ptr.color() == Color::Black && ptr.strong() == 0 {
                    ptr.data().color.set(Color::White);
                }
                collect_white(self, ptr, &mut white);
            }
        };

        // Run drop on each of nodes. The previous increment of the weak count during traversal will
        // ensure that all of the memory stays alive during this loop.
        for i in &white {
            unsafe {
                free(*i);
            }
        }

        // It's now safe to deallocate the memory as long as we are the last weak reference.
        for i in &white {
            unsafe {
                // Only deallocate if our weak reference is the only one.
                if i.as_ref().weak() == 1 {
                    crate::deallocate(*i);
                } else {
                    // undo s.inc_weak() from collect_white
                    i.as_ref().dec_weak();
                }
            }
        }
    }
}
