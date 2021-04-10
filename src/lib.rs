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

//! Context-contained reference-counted boxes (the `Cc<T>` type).
//!
//! The `Cc<T>` type provides shared ownership of an immutable value.
//! Destruction is deterministic, and will occur as soon as the last owner is
//! gone. It is marked as non-sendable because it avoids the overhead of atomic
//! reference counting (_this will be changed_).
//!
//! The `downgrade` method can be used to create a non-owning `Weak<T>` pointer
//! to the box. A `Weak<T>` pointer can be upgraded to an `Cc<T>` pointer, but
//! will return `None` if the value has already been dropped.
//!
//! For example, a tree with parent pointers can be represented by putting the
//! nodes behind strong `Cc<T>` pointers, and then storing the parent pointers
//! as `Weak<T>` pointers.
//!
//! # Examples
//!
//! ```
//! use bacon_rajan_cc::CcContext;
//!
//! let ctx = CcContext::new();
//! let cc = ctx.cc(5);
//! assert_eq!(*cc, 5);
//! ```

#![deny(missing_docs)]

extern crate core;
use core::cell::Cell;
use core::cmp::Ordering;
use core::fmt;
use core::hash::{Hash, Hasher};
use core::mem::forget;
use core::ops::{Deref, Drop};

use core::ptr;
use std::ptr::NonNull;

use std::alloc::{dealloc, Layout};

/// Implementation of cycle detection and collection.
pub mod collect;
/// Tracing traits, types, and implementation.
pub mod trace;

pub use collect::CcContext;
pub use trace::{Trace, Tracer};

mod cc_box_ptr;
use cc_box_ptr::CcBoxPtr;
use collect::ContextPtr;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[doc(hidden)]
pub enum Color {
    /// In use or free.
    Black,

    /// Possible member of a cycle.
    Gray,

    /// Member of a garbage cycle.
    White,

    /// Possible root of cycle.
    Purple,

    /// Candidate cycle undergoing sigma-computation. Not yet in use.
    #[allow(dead_code)]
    Red,

    /// Candidate cycle awaiting epoch boundary. Not yet in use.
    #[allow(dead_code)]
    Orange,
}

#[derive(Debug)]
#[doc(hidden)]
pub struct CcBoxData {
    ctx: ContextPtr,
    strong: Cell<usize>,
    weak: Cell<usize>,
    buffered: Cell<bool>,
    color: Cell<Color>,
}

#[derive(Debug)]
#[doc(hidden)]
pub struct CcBox<T: Trace> {
    value: T,
    data: CcBoxData,
}

/// A reference-counted pointer type over an immutable value.
///
/// See the [module level documentation](./) for more details.
pub struct Cc<T: 'static + Trace> {
    // FIXME #12808: strange names to try to avoid interfering with field
    // accesses of the contained type via Deref
    _ptr: NonNull<CcBox<T>>,
}

impl<T: Trace> Cc<T> {
    fn new(ctx: ContextPtr, value: T) -> Cc<T> {
        unsafe {
            Cc {
                // There is an implicit weak pointer owned by all the strong
                // pointers, which ensures that the weak destructor never frees
                // the allocation while the strong destructor is running, even
                // if the weak pointer is stored inside the strong one.
                _ptr: NonNull::new_unchecked(Box::into_raw(Box::new(CcBox {
                    value,
                    data: CcBoxData {
                        ctx,
                        strong: Cell::new(1),
                        weak: Cell::new(1),
                        buffered: Cell::new(false),
                        color: Cell::new(Color::Black),
                    },
                }))),
            }
        }
    }

    /// Returns the context that this [`Cc`] was allocated in.
    ///
    /// # Examples
    ///
    /// ```
    /// use bacon_rajan_cc::{Cc, CcContext};
    ///
    /// let ctx = CcContext::new();
    /// let cc = ctx.cc("a string");
    ///
    /// fn test(s: Cc<&'static str>) -> Cc<i32> {
    ///     s.get_context().cc(5)
    /// }
    ///
    /// assert_eq!(*cc, "a string");
    /// assert_eq!(*test(cc.clone()), 5);
    /// ```
    pub fn get_context(&self) -> CcContext {
        CcContext {
            inner: self.data().ctx.clone(),
        }
    }

    /// Downgrades the `Cc<T>` to a `Weak<T>` reference.
    ///
    /// # Examples
    ///
    /// ```
    /// use bacon_rajan_cc::{Cc, CcContext};
    ///
    /// let ctx = CcContext::new();
    /// let five = ctx.cc(5);
    ///
    /// let weak_five = five.downgrade();
    /// ```
    pub fn downgrade(&self) -> Weak<T> {
        self.inc_weak();
        Weak { _ptr: self._ptr }
    }

    /// Constructs a new Cc from the given raw `CcBox` pointer. This function must be called once and only once per every leaked `CcBox`.
    ///
    /// # Safety
    /// The caller must guarantee that this pointer hasn't been returned to `from_raw` before.
    /// Failing to uphold this condition will lead to a use after free.
    ///
    /// # Examples
    ///
    /// ```
    /// use bacon_rajan_cc::{Cc, CcContext};
    ///
    /// let ctx = CcContext::new();
    /// let five = ctx.cc(5);
    /// let cloned = five.clone();
    /// let raw = unsafe { five.leak() };
    /// assert_eq!(cloned.strong_count(), 2);
    ///
    /// std::mem::drop(cloned);
    ///
    /// let reconstructed = unsafe { Cc::from_raw(raw) };
    /// assert_eq!(reconstructed.strong_count(), 1);
    /// ```
    pub unsafe fn from_raw(ptr: NonNull<CcBox<T>>) -> Self {
        Self { _ptr: ptr }
    }

    /// Leaks the inner pointer to the baking CcBox<T>. This operation is unsafe for the following reasons:
    ///
    /// # Safety
    /// 1) The caller must returned the leaked pointer to [`Cc`] or the memory will be leaked as the ref count will never go to 0;
    /// 2) The caller must ensure that the pointer is returned to [`Cc`] once and only once, since the Cc will be deallocated as soon as the count reaches 0.
    ///
    /// # Examples
    ///
    /// ```
    /// use bacon_rajan_cc::{Cc, CcContext};
    ///
    /// let ctx = CcContext::new();
    /// let five = ctx.cc(5);
    /// let cloned = five.clone();
    /// let raw = unsafe { five.leak() };
    /// assert_eq!(cloned.strong_count(), 2);
    ///
    /// std::mem::drop(cloned);
    ///
    /// let reconstructed = unsafe { Cc::from_raw(raw) };
    /// assert_eq!(reconstructed.strong_count(), 1);
    /// ```
    #[inline]
    pub unsafe fn leak(self) -> NonNull<CcBox<T>> {
        let this = std::mem::ManuallyDrop::new(self);
        this._ptr
    }
}

impl<T: Trace> Cc<T> {
    unsafe fn release(&mut self) {
        debug_assert!(self.strong() == 0);
        self.data().color.set(Color::Black);

        // If it is in the buffer, then it will be freed later in the
        // `mark_roots` procedure.
        if self.buffered() {
            return;
        }

        crate::cc_box_ptr::free(self._ptr);
    }

    fn possible_root(&mut self) {
        debug_assert!(self.strong() > 0);

        if self.color() == Color::Purple {
            return;
        }

        self.data().color.set(Color::Purple);
        if self.buffered() {
            return;
        }

        self.data().buffered.set(true);
        let ptr: NonNull<dyn CcBoxPtr> = self._ptr;

        self.data().ctx.add_root(ptr)
    }
}

impl<T: 'static + Trace> Cc<T> {
    /// Returns true if there are no other `Cc` or `Weak<T>` values that share
    /// the same inner value.
    ///
    /// # Examples
    ///
    /// ```
    /// use bacon_rajan_cc::CcContext;
    ///
    /// let ctx = CcContext::new();
    /// let five = ctx.cc(5);
    /// assert_eq!(five.is_unique(), true);
    ///
    /// let another_five = five.clone();
    /// assert_eq!(five.is_unique(), false);
    /// assert_eq!(another_five.is_unique(), false);
    /// ```
    #[inline]
    pub fn is_unique(&self) -> bool {
        self.weak_count() == 0 && self.strong_count() == 1
    }

    /// Unwraps the contained value if the `Cc<T>` is unique.
    ///
    /// If the `Cc<T>` is not unique, an `Err` is returned with the same `Cc<T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bacon_rajan_cc::CcContext;
    ///
    /// let ctx = CcContext::new();
    /// let x = ctx.cc(3);
    /// assert_eq!(x.try_unwrap(), Ok(3));
    ///
    /// let x = ctx.cc(4);
    /// let _y = x.clone();
    /// assert_eq!(x.try_unwrap(), Err(ctx.cc(4)));
    /// ```
    #[inline]
    pub fn try_unwrap(self) -> Result<T, Cc<T>> {
        if self.is_unique() {
            unsafe {
                // Copy the contained object.
                let val = ptr::read(&*self);
                // Destruct the box and skip our Drop. We can ignore the
                // refcounts because we know we're unique.
                dealloc(self._ptr.cast().as_ptr(), Layout::new::<CcBox<T>>());
                forget(self);
                Ok(val)
            }
        } else {
            Err(self)
        }
    }

    /// Returns a mutable reference to the contained value if the `Cc<T>` is
    /// unique.
    ///
    /// Returns `None` if the `Cc<T>` is not unique.
    ///
    /// # Examples
    ///
    /// ```
    /// use bacon_rajan_cc::{Cc, CcContext};
    ///
    /// let ctx = CcContext::new();
    /// let mut x = ctx.cc(3);
    /// *Cc::get_mut(&mut x).unwrap() = 4;
    /// assert_eq!(*x, 4);
    ///
    /// let _y = x.clone();
    /// assert!(Cc::get_mut(&mut x).is_none());
    /// ```
    #[inline]
    pub fn get_mut(&mut self) -> Option<&mut T> {
        if self.is_unique() {
            let inner = unsafe { self._ptr.as_mut() };
            Some(&mut inner.value)
        } else {
            None
        }
    }

    /// Get the number of strong references to this value.
    #[inline]
    pub fn strong_count(&self) -> usize {
        self.strong()
    }

    /// Get the number of weak references to this value.
    #[inline]
    pub fn weak_count(&self) -> usize {
        self.weak() - 1
    }
}

impl<T: 'static + Clone + Trace> Cc<T> {
    /// Make a mutable reference from the given `Cc<T>`.
    ///
    /// This is also referred to as a copy-on-write operation because the inner
    /// data is cloned if the reference count is greater than one.
    ///
    /// # Examples
    ///
    /// ```
    /// use bacon_rajan_cc::CcContext;
    ///
    /// let ctx = CcContext::new();
    /// let mut five = ctx.cc(5);
    ///
    /// let mut_five = five.make_unique();
    /// ```
    #[inline]
    pub fn make_unique(&mut self) -> &mut T {
        if !self.is_unique() {
            *self = Cc::new(self.data().ctx.clone(), (**self).clone())
        }
        // This unsafety is ok because we're guaranteed that the pointer
        // returned is the *only* pointer that will ever be returned to T. Our
        // reference count is guaranteed to be 1 at this point, and we required
        // the `Cc<T>` itself to be `mut`, so we're returning the only possible
        // reference to the inner value.
        let inner = unsafe { self._ptr.as_mut() };
        &mut inner.value
    }
}

impl<T: Trace> Deref for Cc<T> {
    type Target = T;

    #[inline(always)]
    fn deref(&self) -> &T {
        if self.strong_count() > 0 {
            unsafe { &self._ptr.as_ref().value }
        } else {
            panic!("Invalid access during cycle collection");
        }
    }
}

impl<T: Trace> Drop for Cc<T> {
    /// Drops the `Cc<T>`.
    ///
    /// This will decrement the strong reference count. If the strong reference
    /// count becomes zero and the only other references are `Weak<T>` ones,
    /// `drop`s the inner value.
    ///
    /// # Examples
    ///
    /// ```
    /// use bacon_rajan_cc::CcContext;
    ///
    /// let ctx = CcContext::new();
    /// {
    ///     let five = ctx.cc(5);
    ///
    ///     // stuff
    ///
    ///     drop(five); // explicit drop
    /// }
    /// {
    ///     let five = ctx.cc(5);
    ///
    ///     // stuff
    ///
    /// } // implicit drop
    /// ```
    fn drop(&mut self) {
        unsafe {
            if self.strong() > 0 {
                self.dec_strong();
                if self.strong() == 0 {
                    self.release();
                } else {
                    self.possible_root();
                }
            }
        }
    }
}

impl<T: Trace> Clone for Cc<T> {
    /// Makes a clone of the `Cc<T>`.
    ///
    /// When you clone an `Cc<T>`, it will create another pointer to the data and
    /// increase the strong reference counter.
    ///
    /// # Examples
    ///
    /// ```
    /// use bacon_rajan_cc::CcContext;
    ///
    /// let ctx = CcContext::new();
    /// let five = ctx.cc(5);
    ///
    /// five.clone();
    /// ```
    #[inline]
    fn clone(&self) -> Cc<T> {
        self.inc_strong();
        Cc { _ptr: self._ptr }
    }
}

impl<T: PartialEq + Trace> PartialEq for Cc<T> {
    /// Equality for two `Cc<T>`s.
    ///
    /// Two `Cc<T>`s are equal if their inner value are equal.
    ///
    /// # Examples
    ///
    /// ```
    /// use bacon_rajan_cc::CcContext;
    ///
    /// let ctx = CcContext::new();
    /// let five = ctx.cc(5);
    ///
    /// assert!(five == ctx.cc(5));
    /// ```
    #[inline(always)]
    fn eq(&self, other: &Cc<T>) -> bool {
        **self == **other
    }

    /// Inequality for two `Cc<T>`s.
    ///
    /// Two `Cc<T>`s are unequal if their inner value are unequal.
    ///
    /// # Examples
    ///
    /// ```
    /// use bacon_rajan_cc::CcContext;
    ///
    /// let ctx = CcContext::new();
    /// let five = ctx.cc(5);
    ///
    /// assert!(five != ctx.cc(6));
    /// ```
    #[inline(always)]
    fn ne(&self, other: &Cc<T>) -> bool {
        **self != **other
    }
}

impl<T: Eq + Trace> Eq for Cc<T> {}

impl<T: PartialOrd + Trace> PartialOrd for Cc<T> {
    /// Partial comparison for two `Cc<T>`s.
    ///
    /// The two are compared by calling `partial_cmp()` on their inner values.
    ///
    /// # Examples
    ///
    /// ```
    /// use bacon_rajan_cc::CcContext;
    ///
    /// let ctx = CcContext::new();
    /// let five = ctx.cc(5);
    ///
    /// assert_eq!(five.partial_cmp(&ctx.cc(5)), Some(std::cmp::Ordering::Equal));
    /// ```
    #[inline(always)]
    fn partial_cmp(&self, other: &Cc<T>) -> Option<Ordering> {
        (**self).partial_cmp(&**other)
    }

    /// Less-than comparison for two `Cc<T>`s.
    ///
    /// The two are compared by calling `<` on their inner values.
    ///
    /// # Examples
    ///
    /// ```
    /// use bacon_rajan_cc::CcContext;
    ///
    /// let ctx = CcContext::new();
    /// let five = ctx.cc(5);
    ///
    /// assert!(five < ctx.cc(6));
    /// ```
    #[inline(always)]
    fn lt(&self, other: &Cc<T>) -> bool {
        **self < **other
    }

    /// 'Less-than or equal to' comparison for two `Cc<T>`s.
    ///
    /// The two are compared by calling `<=` on their inner values.
    ///
    /// # Examples
    ///
    /// ```
    /// use bacon_rajan_cc::CcContext;
    ///
    /// let ctx = CcContext::new();
    /// let five = ctx.cc(5);
    ///
    /// assert!(five <= ctx.cc(5));
    /// ```
    #[inline(always)]
    fn le(&self, other: &Cc<T>) -> bool {
        **self <= **other
    }

    /// Greater-than comparison for two `Cc<T>`s.
    ///
    /// The two are compared by calling `>` on their inner values.
    ///
    /// # Examples
    ///
    /// ```
    /// use bacon_rajan_cc::CcContext;
    ///
    /// let ctx = CcContext::new();
    /// let five = ctx.cc(5);
    ///
    /// assert!(five > ctx.cc(4));
    /// ```
    #[inline(always)]
    fn gt(&self, other: &Cc<T>) -> bool {
        **self > **other
    }

    /// 'Greater-than or equal to' comparison for two `Cc<T>`s.
    ///
    /// The two are compared by calling `>=` on their inner values.
    ///
    /// # Examples
    ///
    /// ```
    /// use bacon_rajan_cc::CcContext;
    ///
    /// let ctx = CcContext::new();
    /// let five = ctx.cc(5);
    ///
    /// assert!(five >= ctx.cc(5));
    /// ```
    #[inline(always)]
    fn ge(&self, other: &Cc<T>) -> bool {
        **self >= **other
    }
}

impl<T: Ord + Trace> Ord for Cc<T> {
    /// Comparison for two `Cc<T>`s.
    ///
    /// The two are compared by calling `cmp()` on their inner values.
    ///
    /// # Examples
    ///
    /// ```
    /// use bacon_rajan_cc::CcContext;
    ///
    /// let ctx = CcContext::new();
    /// let five = ctx.cc(5);
    ///
    /// assert_eq!(five.cmp(&ctx.cc(5)), std::cmp::Ordering::Equal);
    /// ```
    #[inline]
    fn cmp(&self, other: &Cc<T>) -> Ordering {
        (**self).cmp(&**other)
    }
}

// FIXME (#18248) Make `T` `Sized?`
impl<T: Hash + Trace> Hash for Cc<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (**self).hash(state);
    }
}

impl<T: fmt::Display + Trace> fmt::Display for Cc<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

impl<T: fmt::Debug + Trace> fmt::Debug for Cc<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<T: Trace> fmt::Pointer for Cc<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Pointer::fmt(&self._ptr, f)
    }
}

/// A weak version of `Cc<T>`.
///
/// Weak references do not count when determining if the inner value should be
/// dropped.
///
/// See the [module level documentation](./) for more.
pub struct Weak<T: Trace> {
    // FIXME #12808: strange names to try to avoid interfering with
    // field accesses of the contained type via Deref
    _ptr: NonNull<CcBox<T>>,
}

impl<T: Trace> Weak<T> {
    /// Upgrades a weak reference to a strong reference.
    ///
    /// Upgrades the `Weak<T>` reference to an `Cc<T>`, if possible.
    ///
    /// Returns `None` if there were no strong references and the data was
    /// destroyed.
    ///
    /// # Examples
    ///
    /// ```
    /// use bacon_rajan_cc::{Cc, CcContext};
    ///
    /// let ctx = CcContext::new();
    /// let five = ctx.cc(5);
    ///
    /// let weak_five = five.downgrade();
    ///
    /// let strong_five: Option<Cc<_>> = weak_five.upgrade();
    /// ```
    pub fn upgrade(&self) -> Option<Cc<T>> {
        if self.strong() == 0 {
            None
        } else {
            self.inc_strong();
            Some(Cc { _ptr: self._ptr })
        }
    }
}

impl<T: Trace> Drop for Weak<T> {
    /// Drops the `Weak<T>`.
    ///
    /// This will decrement the weak reference count.
    ///
    /// # Examples
    ///
    /// ```
    /// use bacon_rajan_cc::CcContext;
    ///
    /// let ctx = CcContext::new();
    /// {
    ///     let five = ctx.cc(5);
    ///     let weak_five = five.downgrade();
    ///
    ///     // stuff
    ///
    ///     drop(weak_five); // explicit drop
    /// }
    /// {
    ///     let five = ctx.cc(5);
    ///     let weak_five = five.downgrade();
    ///
    ///     // stuff
    ///
    /// } // implicit drop
    /// ```
    fn drop(&mut self) {
        unsafe {
            if self.weak() > 0 {
                self.dec_weak();
                // The weak count starts at 1, and will only go to zero if all
                // the strong pointers have disappeared.
                if self.weak() == 0 {
                    dealloc(self._ptr.cast().as_ptr(), Layout::new::<CcBox<T>>())
                }
            }
        }
    }
}

impl<T: Trace> Clone for Weak<T> {
    /// Makes a clone of the `Weak<T>`.
    ///
    /// This increases the weak reference count.
    ///
    /// # Examples
    ///
    /// ```
    /// use bacon_rajan_cc::CcContext;
    ///
    /// let ctx = CcContext::new();
    /// let weak_five = ctx.cc(5).downgrade();
    ///
    /// weak_five.clone();
    /// ```
    #[inline]
    fn clone(&self) -> Weak<T> {
        self.inc_weak();
        Weak { _ptr: self._ptr }
    }
}

impl<T: fmt::Debug + Trace> fmt::Debug for Weak<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "(Weak)")
    }
}

impl<T: Trace> Trace for Cc<T> {
    fn trace(&self, tracer: &mut Tracer) {
        unsafe {
            tracer(self._ptr.as_ref());
        }
    }
}

impl<T: Trace> Trace for Weak<T> {
    fn trace(&self, _tracer: &mut Tracer) {
        // Weak references should not be traced.
    }
}

impl<T: Trace> Trace for CcBox<T> {
    fn trace(&self, tracer: &mut Tracer) {
        Trace::trace(&self.value, tracer);
    }
}

#[doc(hidden)]
impl<T: Trace> CcBoxPtr for Cc<T> {
    #[inline(always)]
    fn data(&self) -> &CcBoxData {
        unsafe {
            // Safe to assume this here, as if it weren't true, we'd be breaking
            // the contract anyway.
            // This allows the null check to be elided in the destructor if we
            // manipulated the reference count in the same function.
            &self._ptr.as_ref().data
        }
    }
}

impl<T: Trace> CcBoxPtr for Weak<T> {
    #[inline(always)]
    fn data(&self) -> &CcBoxData {
        unsafe {
            // Safe to assume this here, as if it weren't true, we'd be breaking
            // the contract anyway.
            // This allows the null check to be elided in the destructor if we
            // manipulated the reference count in the same function.
            &self._ptr.as_ref().data
        }
    }
}

impl<T: Trace> CcBoxPtr for CcBox<T> {
    #[inline(always)]
    fn data(&self) -> &CcBoxData {
        &self.data
    }
}

unsafe fn deallocate(ptr: NonNull<dyn CcBoxPtr>) {
    dealloc(ptr.cast().as_ptr(), Layout::for_value(ptr.as_ref()));
}

unsafe fn drop_value(ptr: NonNull<dyn CcBoxPtr>) {
    ptr::drop_in_place(ptr.as_ptr());
}

#[cfg(test)]
mod tests {
    use super::collect::CcContext;
    use super::{Cc, Trace, Tracer, Weak};

    use std::boxed::Box;
    use std::cell::RefCell;
    use std::clone::Clone;
    use std::mem::drop;
    use std::option::Option;
    use std::option::Option::{None, Some};
    use std::result::Result::{Err, Ok};

    #[test]
    #[should_panic]
    fn test_mixed_contexts() {
        let ctx1 = CcContext::new();
        let ctx2 = CcContext::new();

        struct Cycle {
            next: RefCell<Option<Cc<Cycle>>>,
        }
        impl Trace for Cycle {
            fn trace(&self, tracer: &mut Tracer) {
                self.next.trace(tracer)
            }
        }

        let cc1 = ctx1.cc(Cycle {
            next: RefCell::new(None),
        });
        let cc2 = ctx2.cc(Cycle {
            next: RefCell::new(None),
        });
        *cc1.next.borrow_mut() = Some(cc2.clone());
        *cc2.next.borrow_mut() = Some(cc1.clone());

        std::mem::drop(cc1);
        std::mem::drop(cc2);

        ctx1.collect_cycles();
        ctx2.collect_cycles();
    }

    #[test]
    fn test_leak_and_from_raw() {
        let ctx = CcContext::new();

        let x = ctx.cc(RefCell::new(5));
        let y = x.clone();
        assert_eq!(x.strong_count(), 2);
        assert_eq!(x.weak_count(), 0);

        let y = unsafe { y.leak() };
        assert_eq!(x.strong_count(), 2);
        assert_eq!(x.weak_count(), 0);

        std::mem::drop(x);

        let y = unsafe { Cc::from_raw(y) };
        assert_eq!(y.strong_count(), 1);
        assert_eq!(y.weak_count(), 0);
        assert_eq!(y.is_unique(), true);

        let weak = Cc::downgrade(&y);
        assert_eq!(y.strong_count(), 1);
        assert_eq!(y.weak_count(), 1);
        assert_eq!(y.is_unique(), false);

        let y = unsafe { y.leak() };
        assert_eq!(
            weak.upgrade().map(|cc| (
                cc.weak_count(),
                cc.strong_count() - 1 /* compensate for the Cc we're calling strong_count() on */
            )),
            Some((1, 1))
        );

        let y = unsafe { Cc::from_raw(y) };
        assert_eq!(
            weak.upgrade()
                .map(|cc| (cc.weak_count(), cc.strong_count() - 1 /* See above */)),
            Some((1, 1))
        );
        std::mem::drop(y);

        assert_eq!(weak.upgrade(), None);
    }

    #[test]
    fn test_leak_with_collector() {
        use std::cell::Cell;
        use std::rc::Rc;

        let count = Rc::new(Cell::new(0));

        struct Obj {
            count: Rc<Cell<i32>>,
            next_op: Cc<RefCell<Option<Obj>>>,
        }

        impl Clone for Obj {
            fn clone(&self) -> Self {
                self.count.set(self.count.get() + 1);
                Obj {
                    count: self.count.clone(),
                    next_op: self.next_op.clone(),
                }
            }
        }

        impl Trace for Obj {
            fn trace(&self, tracer: &mut Tracer) {
                self.next_op.trace(tracer);
            }
        }

        impl Obj {
            fn new(ctx: &CcContext, count: Rc<Cell<i32>>, next_op: Option<Obj>) -> Obj {
                count.set(count.get() + 1);
                Obj {
                    count,
                    next_op: ctx.cc(RefCell::new(next_op)),
                }
            }
        }

        impl Drop for Obj {
            fn drop(&mut self) {
                self.count.set(self.count.get() - 1);
            }
        }

        let ctx = CcContext::new();

        let leaked;
        {
            let q;
            {
                let z = Obj::new(&ctx, count.clone(), None);
                let y = Obj::new(&ctx, count.clone(), Some(z.clone()));
                let x = Obj::new(&ctx, count.clone(), Some(y));
                *(*z.next_op).borrow_mut() = Some(x.clone());
                q = x;
                leaked = unsafe { z.next_op.clone().leak() };
            }

            ctx.collect_cycles();
            assert_eq!(count.get(), 4);

            *(*q.next_op).borrow_mut() = None;
        }

        ctx.collect_cycles();
        assert_eq!(count.get(), 1);

        std::mem::drop(unsafe { Cc::from_raw(leaked) });
        assert_eq!(count.get(), 0);
    }

    // Tests copied from `Rc<T>`.

    #[test]
    fn test_clone() {
        let ctx = CcContext::new();
        {
            let x = ctx.cc(RefCell::new(5));
            let y = x.clone();
            *(*x).borrow_mut() = 20;
            assert_eq!(*y.borrow(), 20);
        }
        ctx.collect_cycles();
    }

    #[test]
    fn test_simple() {
        let ctx = CcContext::new();
        let x = ctx.cc(5);
        assert_eq!(*x, 5);
    }

    #[test]
    fn test_simple_clone() {
        let ctx = CcContext::new();
        {
            let x = ctx.cc(5);
            let y = x.clone();
            assert_eq!(*x, 5);
            assert_eq!(*y, 5);
        }
        ctx.collect_cycles();
    }

    #[test]
    fn test_destructor() {
        let ctx = CcContext::new();
        let x: Cc<Box<_>> = ctx.cc(Box::new(5));
        assert_eq!(**x, 5);
    }

    #[test]
    fn test_live() {
        let ctx = CcContext::new();
        {
            let x = ctx.cc(5);
            let y = x.downgrade();
            assert!(y.upgrade().is_some());
        }
        ctx.collect_cycles();
    }

    #[test]
    fn test_dead() {
        let ctx = CcContext::new();
        let x = ctx.cc(5);
        let y = x.downgrade();
        drop(x);
        assert!(y.upgrade().is_none());
    }

    #[test]
    fn weak_self_cyclic() {
        let ctx = CcContext::new();
        {
            struct Cycle {
                x: RefCell<Option<Weak<Cycle>>>,
            }

            impl Trace for Cycle {
                fn trace(&self, _: &mut Tracer) {}
            }

            let a = ctx.cc(Cycle {
                x: RefCell::new(None),
            });
            let b = a.clone().downgrade();
            *a.x.borrow_mut() = Some(b);
        }
        ctx.collect_cycles();
        // hopefully we don't double-free (or leak)...
    }

    #[test]
    fn is_unique() {
        let ctx = CcContext::new();
        {
            let x = ctx.cc(3);
            assert!(x.is_unique());
            let y = x.clone();
            assert!(!x.is_unique());
            drop(y);
            assert!(x.is_unique());
            let w = x.downgrade();
            assert!(!x.is_unique());
            drop(w);
            assert!(x.is_unique());
        }
        ctx.collect_cycles();
    }

    #[test]
    fn test_strong_count() {
        let ctx = CcContext::new();
        {
            let a = ctx.cc(0u32);
            assert!(a.strong_count() == 1);
            let w = a.downgrade();
            assert!(a.strong_count() == 1);
            let b = w.upgrade().expect("upgrade of live rc failed");
            assert!(b.strong_count() == 2);
            assert!(b.strong_count() == 2);
            drop(w);
            drop(a);
            assert!(b.strong_count() == 1);
            let c = b.clone();
            assert!(b.strong_count() == 2);
            assert!(c.strong_count() == 2);
        }
        ctx.collect_cycles();
    }

    #[test]
    fn test_weak_count() {
        let ctx = CcContext::new();
        {
            let a = ctx.cc(0u32);
            assert!(a.strong_count() == 1);
            assert!(a.weak_count() == 0);
            let w = a.downgrade();
            assert!(a.strong_count() == 1);
            assert!(a.weak_count() == 1);
            drop(w);
            assert!(a.strong_count() == 1);
            assert!(a.weak_count() == 0);
            let c = a.clone();
            assert!(a.strong_count() == 2);
            assert!(a.weak_count() == 0);
            drop(c);
        }
        ctx.collect_cycles();
    }

    #[test]
    fn try_unwrap() {
        let ctx = CcContext::new();
        {
            let x = ctx.cc(3);
            assert_eq!(x.try_unwrap(), Ok(3));
            let x = ctx.cc(4);
            let _y = x.clone();
            assert_eq!(x.try_unwrap(), Err(ctx.cc(4)));
            let x = ctx.cc(5);
            let _w = x.downgrade();
            assert_eq!(x.try_unwrap(), Err(ctx.cc(5)));
        }
        ctx.collect_cycles();
    }

    #[test]
    fn get_mut() {
        let ctx = CcContext::new();
        {
            let mut x = ctx.cc(3);
            *x.get_mut().unwrap() = 4;
            assert_eq!(*x, 4);
            let y = x.clone();
            assert!(x.get_mut().is_none());
            drop(y);
            assert!(x.get_mut().is_some());
            let _w = x.downgrade();
            assert!(x.get_mut().is_none());
        }
        ctx.collect_cycles();
    }

    #[test]
    fn test_cowrc_clone_make_unique() {
        let ctx = CcContext::new();
        {
            let mut cow0 = ctx.cc(75);
            let mut cow1 = cow0.clone();
            let mut cow2 = cow1.clone();

            assert!(75 == *cow0.make_unique());
            assert!(75 == *cow1.make_unique());
            assert!(75 == *cow2.make_unique());

            *cow0.make_unique() += 1;
            *cow1.make_unique() += 2;
            *cow2.make_unique() += 3;

            assert!(76 == *cow0);
            assert!(77 == *cow1);
            assert!(78 == *cow2);

            // none should point to the same backing memory
            assert!(*cow0 != *cow1);
            assert!(*cow0 != *cow2);
            assert!(*cow1 != *cow2);
        }
        ctx.collect_cycles();
    }

    #[test]
    fn test_cowrc_clone_unique2() {
        let ctx = CcContext::new();
        {
            let mut cow0 = ctx.cc(75);
            let cow1 = cow0.clone();
            let cow2 = cow1.clone();

            assert!(75 == *cow0);
            assert!(75 == *cow1);
            assert!(75 == *cow2);

            *cow0.make_unique() += 1;

            assert!(76 == *cow0);
            assert!(75 == *cow1);
            assert!(75 == *cow2);

            // cow1 and cow2 should share the same contents
            // cow0 should have a unique reference
            assert!(*cow0 != *cow1);
            assert!(*cow0 != *cow2);
            assert!(*cow1 == *cow2);
        }
        ctx.collect_cycles();
    }

    #[test]
    fn test_cowrc_clone_weak() {
        let ctx = CcContext::new();
        {
            let mut cow0 = ctx.cc(75);
            let cow1_weak = cow0.downgrade();

            assert!(75 == *cow0);
            assert!(75 == *cow1_weak.upgrade().unwrap());

            *cow0.make_unique() += 1;

            assert!(76 == *cow0);
            assert!(cow1_weak.upgrade().is_none());
        }
        ctx.collect_cycles();
    }

    #[test]
    fn test_show() {
        let ctx = CcContext::new();
        let foo = ctx.cc(75);
        assert_eq!(format!("{:?}", foo), "75");
    }

    #[cfg(not(all(target_os = "macos", miri)))]
    #[test]
    fn test_map() {
        let ctx = CcContext::new();
        let mut map = std::collections::HashMap::new();

        map.insert("Foo".to_string(), 4);

        let x = ctx.cc(map);
        assert_eq!(x.get("Foo"), Some(&4));
    }

    #[test]
    fn list_cycle() {
        use std::cell::RefCell;

        struct List(Vec<Cc<RefCell<List>>>);
        impl Trace for List {
            fn trace(&self, tracer: &mut Tracer) {
                self.0.trace(tracer);
            }
        }

        let ctx = CcContext::new();
        {
            let a = ctx.cc(RefCell::new(List(Vec::new())));
            let b = ctx.cc(RefCell::new(List(Vec::new())));
            {
                let mut a = (*a).borrow_mut();
                a.0.push(b.clone());
            }
            {
                let mut b = (*b).borrow_mut();
                b.0.push(a.clone());
            }
        }
        ctx.collect_cycles();
    }

    #[test]
    fn test_retain_weak() {
        let ctx = CcContext::new();
        let retained_weak_a;
        {
            struct A {
                x: Cc<RefCell<Option<A>>>,
            }
            struct WeakA {
                _x: Weak<RefCell<Option<A>>>,
            }
            impl A {
                fn downgrade(this: &Self) -> WeakA {
                    WeakA {
                        _x: Cc::downgrade(&this.x),
                    }
                }
            }
            impl Clone for A {
                fn clone(&self) -> Self {
                    A { x: self.x.clone() }
                }
            }
            impl Trace for A {
                fn trace(&self, tracer: &mut Tracer) {
                    self.x.trace(tracer);
                }
            }
            let a = A {
                x: ctx.cc(RefCell::new(None)),
            };
            *(*a.x).borrow_mut() = Some(a.clone());
            retained_weak_a = A::downgrade(&a);
        }
        ctx.collect_cycles();
        let _x = retained_weak_a;
    }

    #[test]
    fn test_double_visit_scan_black() {
        let count = std::rc::Rc::new(std::cell::Cell::new(0));
        struct A {
            count: std::rc::Rc<std::cell::Cell<i32>>,
            next_op: Cc<RefCell<Option<A>>>,
        }
        impl Clone for A {
            fn clone(&self) -> Self {
                self.count.set(self.count.get() + 1);
                A {
                    count: self.count.clone(),
                    next_op: self.next_op.clone(),
                }
            }
        }
        impl Trace for A {
            fn trace(&self, tracer: &mut Tracer) {
                self.next_op.trace(tracer);
            }
        }
        impl A {
            fn new(
                ctx: &CcContext,
                count: std::rc::Rc<std::cell::Cell<i32>>,
                next_op: Option<A>,
            ) -> A {
                count.set(count.get() + 1);
                A {
                    count,
                    next_op: ctx.cc(RefCell::new(next_op)),
                }
            }
        }
        impl Drop for A {
            fn drop(&mut self) {
                self.count.set(self.count.get() - 1);
            }
        }
        let ctx = CcContext::new();
        {
            let q;
            {
                let z = A::new(&ctx, count.clone(), None);
                let y = A::new(&ctx, count.clone(), Some(z.clone()));
                let x = A::new(&ctx, count.clone(), Some(y));
                *(*z.next_op).borrow_mut() = Some(x.clone());
                q = x;
            }
            ctx.collect_cycles();
            *(*q.next_op).borrow_mut() = None;
        }
        ctx.collect_cycles();
        assert_eq!(count.get(), 0);
    }
}
