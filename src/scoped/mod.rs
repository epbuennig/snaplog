//! A scoped [`ScopedSnaplog`][Snaplog] and it's associated types. A `ScopedSnaplog` is used to
//! record snapshots of changes to only part of a value, such as successive edits to a file's name
//! without editing it's ancestors.
//!
//! To scope a type, implement [`IntoScoped`], a trait to denote how to deconstruct and reconstruct
//! the type, the `ScopedSnaplog` takes care of the rest.
//!
//! # Examples
//! All examples in this module assume this type is given.
//!
//! Given a type like this:
//! ```
//! use snaplog::scoped::IntoScoped;
//!
//! #[derive(Debug, PartialEq)]
//! pub struct Prefixed {
//!     pub prefix: Option<&'static str>,
//!     pub content: &'static str,
//! }
//!
//! impl Prefixed {
//!     pub fn new(s: &'static str) -> Self {
//!         let parts = s.split_once(':');
//!
//!         Self {
//!             prefix: parts.map(|(p, _)| p),
//!             content: parts.map(|(_, c)| c).unwrap_or(s),
//!         }
//!     }
//! }
//!
//! impl IntoScoped for Prefixed {
//!     type Scope = &'static str;
//!     type Ignored = Option<&'static str>;
//!
//!     fn into_scoped(self) -> (Self::Scope, Self::Ignored) {
//!         (self.content, self.prefix)
//!     }
//!
//!     fn from_scoped(scope: Self::Scope, ignored: Self::Ignored) -> Self {
//!         Self {
//!             prefix: ignored,
//!             content: scope,
//!         }
//!     }
//! }
//! ```
//!
//! You can use the [`Snaplog`] like this:
//! ```
//! # use snaplog::{Select, scoped::{Snaplog, __Prefixed as Prefixed}};
//! let mut snaplog = Snaplog::new(Prefixed::new("prefix:content"));
//! assert_eq!(snaplog.has_changes(), false);
//!
//! snaplog.record_change(|prev| { assert_eq!(prev, &"content"); "content-copy" });
//! snaplog.record_change(|prev| { assert_eq!(prev, &"content-copy"); "new" });
//! assert_eq!(snaplog.has_changes(), true);
//!
//! assert_eq!(snaplog[Select::Initial], "content");
//! assert_eq!(snaplog[Select::At(1)],   "content-copy");
//! assert_eq!(snaplog[Select::Current], "new");
//!
//! snaplog.clear_history();
//!
//! assert_eq!(snaplog.history(), ["new"]);
//! assert_eq!(snaplog.has_changes(), false);
//! # Ok::<_, Box<dyn std::error::Error>>(())
//! ```
//!
//! And when all changes are done you can simply recombine the parts:
//! ```
//! # use snaplog::{Select, scoped::{Snaplog, __Prefixed as Prefixed}};
//! # let mut snaplog = Snaplog::new(Prefixed::new("prefix:content"));
//! # snaplog.record("content-copy");
//! # snaplog.record("new");
//! assert_eq!(snaplog.into_current(), Prefixed::new("prefix:new"));
//! ```

use crate::full;
use crate::{EmptyHistoryError, Select};

use std::collections::TryReserveError;
use std::ops::RangeBounds;

mod docs_impl;

#[doc(hidden)]
pub use docs_impl::__Prefixed;

/// A trait for types that can be scoped into parts to apply changes only partially. See
/// [`ScopedSnaplog`][Snaplog] for examples.
pub trait IntoScoped {
    /// The type of the scope that is used when applying changes.
    type Scope;

    /// The type of the part that is ignored when applying changes.
    type Ignored;

    /// Separates `Self` into it's scoped and ignored part.
    fn into_scoped(self) -> (Self::Scope, Self::Ignored);

    /// Creates `Self` from it's scope and ignored part.
    fn from_scoped(scope: Self::Scope, ignored: Self::Ignored) -> Self;
}

/// A [`Snaplog`][full] that is scoped to only part of of a type.
///
/// # Examples
/// ```
/// # use snaplog::{Select, scoped::{Snaplog, __Prefixed as Prefixed}};
/// let mut snaplog = Snaplog::new(Prefixed::new("prefix:content"));
/// assert_eq!(snaplog.has_changes(), false);
///
/// snaplog.record_change(|prev| { assert_eq!(prev, &"content"); "content-copy" });
/// snaplog.record_change(|prev| { assert_eq!(prev, &"content-copy"); "new" });
/// assert_eq!(snaplog.has_changes(), true);
///
/// assert_eq!(snaplog[Select::Initial], "content");
/// assert_eq!(snaplog[Select::At(1)],   "content-copy");
/// assert_eq!(snaplog[Select::Current], "new");
///
/// snaplog.clear_history();
///
/// assert_eq!(snaplog.history(), ["new"]);
/// assert_eq!(snaplog.has_changes(), false);
/// # Ok::<_, Box<dyn std::error::Error>>(())
/// ```
///
/// [full]: full::Snaplog
#[derive(Debug, PartialEq, Eq)]
pub struct Snaplog<T: IntoScoped> {
    full: full::Snaplog<T::Scope>,
    ignored: T::Ignored,
}

/// Various constructor functions.
impl<T: IntoScoped> Snaplog<T> {
    /// Creates a new [`Snaplog`] from the given `initial` snapshot with no recorded changes.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::scoped::{Snaplog, __Prefixed as Prefixed};
    /// let snaplog = Snaplog::new(Prefixed::new("prefix:content"));
    ///
    /// assert_eq!(snaplog.initial(), &"content");
    /// assert_eq!(snaplog.ignored(), &Some("prefix"));
    /// assert_eq!(snaplog.has_changes(), false);
    /// ```
    pub fn new(initial: T) -> Self {
        let (scope, ignored) = initial.into_scoped();

        Self {
            full: full::Snaplog::new(scope),
            ignored,
        }
    }

    /// Creates a new [`Snaplog`] for the given `history` backing vector.
    ///
    /// # Errors
    /// Returns an error if `history` was empty.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::scoped::{Snaplog, __Prefixed as Prefixed};
    /// assert!(Snaplog::<Prefixed>::try_from_vec(vec!["content"], None).is_ok());
    /// assert!(Snaplog::<Prefixed>::try_from_vec(vec![], Some("prefix")).is_err());
    /// ```
    pub fn try_from_vec(
        history: Vec<T::Scope>,
        ignored: T::Ignored,
    ) -> Result<Self, EmptyHistoryError> {
        Ok(Self {
            full: full::Snaplog::try_from_vec(history)?,
            ignored,
        })
    }

    /// Creates a new [`Snaplog`] for the given `history` backing vector.
    ///
    /// # Panics
    /// Panics if `history` was empty.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::scoped::{Snaplog, __Prefixed as Prefixed};
    /// let snaplog: Snaplog<Prefixed> = Snaplog::from_vec(vec![""], None);
    /// ```
    ///
    /// This panics:
    /// ```should_panic
    /// # use snaplog::scoped::{Snaplog, __Prefixed as Prefixed};
    /// let snaplog: Snaplog<Prefixed> = Snaplog::from_vec(vec![], Some("Prefix"));
    /// ```
    pub fn from_vec(history: Vec<T::Scope>, ignored: T::Ignored) -> Self {
        match Self::try_from_vec(history, ignored) {
            Ok(this) => this,
            Err(_) => panic!("history must not be empty"),
        }
    }

    /// Creates a new [`Snaplog`] from the given `history`. The elements are collected into a
    /// [`Vec`] the if you already have a vec at hand use [`from_vec`][Self::try_from_vec]. The
    /// first element is used as the initial element.
    ///
    /// # Errors
    /// Returns an error if `history` was empty.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::scoped::{Snaplog, __Prefixed as Prefixed};
    /// assert!(Snaplog::<Prefixed>::try_from_history(["a", "b", "c"], None).is_ok());
    /// assert!(Snaplog::<Prefixed>::try_from_history(std::iter::empty(), Some("a")).is_err());
    /// ```
    pub fn try_from_history<I>(history: I, ignored: T::Ignored) -> Result<Self, EmptyHistoryError>
    where
        I: IntoIterator<Item = T::Scope>,
    {
        Self::try_from_vec(history.into_iter().collect(), ignored)
    }

    /// Creates a new [`Snaplog`] from the given `history`. The elements are collected into a
    /// [`Vec`] the if you already have a vec at hand use [`from_vec`][Self::from_vec]. The first
    /// element is used as the initial element.
    ///
    /// # Panics
    /// Panics if `history` was empty.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::scoped::{Snaplog, __Prefixed as Prefixed};
    /// let snaplog: Snaplog<Prefixed> = Snaplog::from_history(["a", "b", "c"], None);
    /// ```
    ///
    /// This panics:
    /// ```should_panic
    /// # use snaplog::scoped::{Snaplog, __Prefixed as Prefixed};
    /// let snaplog: Snaplog<Prefixed> = Snaplog::from_history(std::iter::empty(), Some("prefix"));
    /// ```
    pub fn from_history<I>(history: I, ignored: T::Ignored) -> Self
    where
        I: IntoIterator<Item = T::Scope>,
    {
        Self::from_vec(history.into_iter().collect(), ignored)
    }
}

/// First class [`Snaplog`] members.
impl<T: IntoScoped> Snaplog<T> {
    /// Returns a reference to the internal [`Snaplog`].
    ///
    /// # Examples
    /// ```
    /// # use snaplog::{full, scoped::{Snaplog, __Prefixed as Prefixed}};
    /// let snaplog = Snaplog::new(Prefixed::new("prefix:content"));
    ///
    /// assert_eq!(snaplog.scope(), &full::Snaplog::new("content"));
    /// ```
    pub fn scope(&self) -> &full::Snaplog<T::Scope> {
        &self.full
    }

    /// Returns a mutable reference to the internal [`full::Snaplog`].
    ///
    /// # Examples
    /// ```
    /// # use snaplog::{full, scoped::{Snaplog, __Prefixed as Prefixed}};
    /// let mut snaplog = Snaplog::new(Prefixed::new("prefix:content"));
    ///
    /// assert_eq!(snaplog.scope(), &mut full::Snaplog::new("content"));
    /// ```
    pub fn scope_mut(&mut self) -> &mut full::Snaplog<T::Scope> {
        &mut self.full
    }

    /// Returns a reference to the ignored part of this [`Snaplog`].
    ///
    /// # Examples
    /// ```
    /// # use snaplog::scoped::{Snaplog, __Prefixed as Prefixed};
    /// let snaplog = Snaplog::new(Prefixed::new("prefix:content"));
    ///
    /// assert_eq!(snaplog.ignored(), &Some("prefix"));
    /// ```
    pub fn ignored(&self) -> &T::Ignored {
        &self.ignored
    }

    /// Returns a mutable reference to the internal [`full::Snaplog`].
    ///
    /// # Examples
    /// ```
    /// # use snaplog::{full, scoped::{Snaplog, __Prefixed as Prefixed}};
    /// let mut snaplog = Snaplog::new(Prefixed::new("prefix:content"));
    ///
    /// assert_eq!(snaplog.into_scope(), full::Snaplog::new("content"));
    /// ```
    pub fn into_scope(self) -> full::Snaplog<T::Scope> {
        self.full
    }
}

/// Implementations similar to [`full::Snaplog`].
impl<T: IntoScoped> Snaplog<T> {
    /// Records a snapshot in this [`Snaplog`].
    ///
    /// # Examples
    /// ```
    /// # use snaplog::scoped::{Snaplog, __Prefixed as Prefixed};
    /// let mut snaplog = Snaplog::new(Prefixed::new("prefix:a"));
    ///
    /// snaplog.record("b");
    /// snaplog.record("c");
    /// assert_eq!(snaplog.history(), ["a", "b", "c"]);
    /// ```
    pub fn record(&mut self, snapshot: T::Scope) {
        self.full.record(snapshot);
    }

    /// Records multiple snapshots in this [`Snaplog`].
    ///
    /// # Examples
    /// ```
    /// # use snaplog::scoped::{Snaplog, __Prefixed as Prefixed};
    /// let mut snaplog = Snaplog::new(Prefixed::new("prefix:a"));
    ///
    /// snaplog.record_all(["b", "c", "d"]);
    /// assert_eq!(snaplog.history(), ["a", "b", "c", "d"]);
    /// ```
    pub fn record_all<I>(&mut self, snapshots: I)
    where
        I: IntoIterator<Item = T::Scope>,
    {
        self.full.record_all(snapshots);
    }

    /// Records a change to the current element in this [`Snaplog`].
    ///
    /// # Examples
    /// ```
    /// # use snaplog::scoped::{Snaplog, __Prefixed as Prefixed};
    /// let mut snaplog = Snaplog::new(Prefixed::new("prefix:a"));
    ///
    /// snaplog.record_change(|prev| { assert_eq!(prev, &"a"); "b" });
    /// snaplog.record_change(|prev| { assert_eq!(prev, &"b"); "c" });
    /// assert_eq!(snaplog.history(), ["a", "b", "c"]);
    /// ```
    pub fn record_change<F>(&mut self, f: F)
    where
        F: FnMut(&T::Scope) -> T::Scope,
    {
        self.full.record_change(f)
    }

    /// Records a change to the current element in this [`Snaplog`].
    ///
    /// # Errors
    /// Returns the inner error if the closure failed.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::scoped::{Snaplog, __Prefixed as Prefixed};
    /// let mut snaplog = Snaplog::new(Prefixed::new("prefix:a"));
    ///
    /// snaplog.try_record_change(|prev| { assert_eq!(prev, &"a"); Ok("b") })?;
    /// snaplog.try_record_change(|prev| { assert_eq!(prev, &"b"); Ok("c") })?;
    /// assert_eq!(snaplog.try_record_change(|prev| Err(())), Err(()));
    /// assert_eq!(snaplog.history(), ["a", "b", "c"]);
    /// # Ok::<_, ()>(())
    /// ```
    pub fn try_record_change<F, E>(&mut self, f: F) -> Result<(), E>
    where
        F: FnMut(&T::Scope) -> Result<T::Scope, E>,
    {
        self.full.try_record_change(f)
    }

    /// Records multiple successive changes to the current element in this [`Snaplog`].
    ///
    /// # Examples
    /// ```
    /// # use snaplog::scoped::{Snaplog, __Prefixed as Prefixed};
    /// let mut snaplog = Snaplog::new(Prefixed::new("prefix:a"));
    ///
    /// snaplog.record_changes_all(&mut ["b", "c", "d"], |change, _| *change);
    /// assert_eq!(snaplog.history(), ["a", "b", "c", "d"]);
    /// ```
    pub fn record_changes_all<F, M>(&mut self, mutations: &mut [M], f: F)
    where
        F: FnMut(&mut M, &T::Scope) -> T::Scope,
    {
        self.full.record_changes_all(mutations, f);
    }

    /// Returns whether or not there are any changes recorded in this [`Snaplog`].
    ///
    /// # Examples
    /// ```
    /// # use snaplog::scoped::{Snaplog, __Prefixed as Prefixed};
    /// let mut snaplog = Snaplog::new(Prefixed::new("prefix:a"));
    ///
    /// assert_eq!(snaplog.has_changes(), false);
    /// snaplog.record("b");
    /// snaplog.record("c");
    /// assert_eq!(snaplog.has_changes(), true);
    /// ```
    pub fn has_changes(&self) -> bool {
        self.full.has_changes()
    }

    /// Returns the initial element.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::scoped::{Snaplog, __Prefixed as Prefixed};
    /// let mut snaplog = Snaplog::new(Prefixed::new("prefix:a"));
    ///
    /// snaplog.record("b");
    /// snaplog.record("c");
    /// assert_eq!(snaplog.initial(), &"a");
    /// ```
    pub fn initial(&self) -> &T::Scope {
        self.full.initial()
    }

    /// Returns the element at the given [`Select`].
    ///
    /// # Examples
    /// ```
    /// # use snaplog::{Select, scoped::{Snaplog, __Prefixed as Prefixed}};
    /// let mut snaplog = Snaplog::new(Prefixed::new("prefix:a"));
    ///
    /// snaplog.record("b");
    /// snaplog.record("c");
    /// assert_eq!(snaplog.snapshot_at(Select::At(1)), &"b");
    /// ```
    pub fn snapshot_at(&self, select: Select) -> &T::Scope {
        self.full.snapshot_at(select)
    }

    /// Returns the current element, that is the last recorded change or the initial element if
    /// there are no none.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::scoped::{Snaplog, __Prefixed as Prefixed};
    /// let mut snaplog = Snaplog::new(Prefixed::new("prefix:a"));
    ///
    /// snaplog.record("b");
    /// snaplog.record("c");
    /// assert_eq!(snaplog.current(), &"c");
    /// ```
    pub fn current(&self) -> &T::Scope {
        self.full.current()
    }

    /// Returns the initial element.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::scoped::{Snaplog, __Prefixed as Prefixed};
    /// let mut snaplog = Snaplog::new(Prefixed::new("prefix:a"));
    ///
    /// snaplog.record("b");
    /// snaplog.record("c");
    /// assert_eq!(snaplog.initial_mut(), &mut "a");
    /// ```
    pub fn initial_mut(&mut self) -> &mut T::Scope {
        self.full.initial_mut()
    }

    /// Returns the element at the given [`Select`].
    ///
    /// # Examples
    /// ```
    /// # use snaplog::{Select, scoped::{Snaplog, __Prefixed as Prefixed}};
    /// let mut snaplog = Snaplog::new(Prefixed::new("prefix:a"));
    ///
    /// snaplog.record("b");
    /// snaplog.record("c");
    /// assert_eq!(snaplog.snapshot_at_mut(Select::At(1)), &mut "b");
    /// ```
    pub fn snapshot_at_mut(&mut self, select: Select) -> &mut T::Scope {
        self.full.snapshot_at_mut(select)
    }

    /// Returns the current element, that is the last recorded change or the initial element if
    /// there are no none.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::scoped::{Snaplog, __Prefixed as Prefixed};
    /// let mut snaplog = Snaplog::new(Prefixed::new("prefix:a"));
    ///
    /// snaplog.record("b");
    /// snaplog.record("c");
    /// assert_eq!(snaplog.current_mut(), &mut "c");
    /// ```
    pub fn current_mut(&mut self) -> &mut T::Scope {
        self.full.current_mut()
    }

    /// Clones the element at the given [`Select`].
    ///
    /// # Examples
    /// ```
    /// # use snaplog::{scoped::{Snaplog, __Prefixed as Prefixed}, Select};
    /// let mut snaplog = Snaplog::new(Prefixed::new("prefix:a"));
    ///
    /// snaplog.record("b");
    /// snaplog.record("c");
    /// assert_eq!(snaplog.clone_snapshot_at(Select::At(1)), Prefixed::new("prefix:b"));
    /// ```
    pub fn clone_snapshot_at(&self, select: Select) -> T
    where
        T::Scope: Clone,
        T::Ignored: Clone,
    {
        // TODO: let the user decide how to reconstruct from references? breaks IntoScoped interface
        T::from_scoped(self.snapshot_at(select).clone(), self.ignored.clone())
    }

    /// Returns the full history recorded in this [`Snaplog`], including the initial element.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::scoped::{Snaplog, __Prefixed as Prefixed};
    /// let mut snaplog = Snaplog::new(Prefixed::new("prefix:a"));
    ///
    /// snaplog.record("b");
    /// snaplog.record("c");
    /// assert_eq!(snaplog.history(), ["a", "b", "c"]);
    /// ```
    pub fn history(&self) -> &[T::Scope] {
        self.full.history()
    }

    /// Returns a mutable reference to the underlying `history`.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::scoped::{Snaplog, __Prefixed as Prefixed};
    /// let mut snaplog: Snaplog<Prefixed> = Snaplog::try_from_history(
    ///     ["a", "b", "c", "d", "e"],
    ///     None,
    /// )?;
    /// let history = snaplog.history_mut();
    ///
    /// history[0] = "g";
    /// assert_eq!(snaplog.history(), ["g", "b", "c", "d", "e"]);
    /// # Ok::<_, Box<dyn std::error::Error>>(())
    /// ```
    pub fn history_mut(&mut self) -> &mut [T::Scope] {
        self.full.history_mut()
    }

    /// Drains the history in the specified range, a left open range is interpreted as starting
    /// behind the initial element, elements that are not yielded from the [`Iterator`] are dropped.
    ///
    /// # Panics
    /// Panics if the lower range bound is inclusive `0`.
    /// Panics if the lower or upper bound are out of range.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::scoped::{Snaplog, __Prefixed as Prefixed};
    /// let mut snaplog: Snaplog<Prefixed> = Snaplog::try_from_history(
    ///     ["a", "b", "c", "d", "e"],
    ///     None,
    /// )?;
    ///
    /// snaplog.drain(2..=3);
    /// assert_eq!(snaplog.history(), ["a", "b", "e"]);
    /// # Ok::<_, Box<dyn std::error::Error>>(())
    /// ```
    /// The unbounded range is reinterpreted as starting at `1`:
    /// ```
    /// # use snaplog::scoped::{Snaplog, __Prefixed as Prefixed};
    /// # let mut snaplog: Snaplog<Prefixed> = Snaplog::try_from_history(["a", "b", "c", "d", "e"],
    /// # None)?;
    /// snaplog.drain(..);
    /// assert_eq!(snaplog.history(), ["a"]);
    /// # Ok::<_, Box<dyn std::error::Error>>(())
    /// ```
    /// The only invalid lower bound is `0`:
    /// ```should_panic
    /// # use snaplog::scoped::{Snaplog, __Prefixed as Prefixed};
    /// # let mut snaplog: Snaplog<Prefixed> = Snaplog::try_from_history(["a", "b", "c", "d", "e"],
    /// # None)?;
    /// snaplog.drain(0..);
    /// # Ok::<_, Box<dyn std::error::Error>>(())
    /// ```
    pub fn drain<'r, R>(&'r mut self, range: R) -> impl Iterator<Item = T::Scope> + 'r
    where
        R: RangeBounds<usize> + 'r,
    {
        self.full.drain(range)
    }

    /// Wipe the recorded history, keeping only the current element as the new initial element.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::scoped::{Snaplog, __Prefixed as Prefixed};
    /// let mut snaplog = Snaplog::new(Prefixed::new("prefix:a"));
    ///
    /// snaplog.record("b");
    /// snaplog.record("c");
    /// snaplog.clear_history();
    /// assert_eq!(snaplog.initial(), &"c");
    /// assert_eq!(snaplog.has_changes(), false);
    /// ```
    pub fn clear_history(&mut self) {
        self.full.clear_history();
    }

    /// Wipe the recorded changes, keeping only the initial element.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::scoped::{Snaplog, __Prefixed as Prefixed};
    /// let mut snaplog = Snaplog::new(Prefixed::new("prefix:a"));
    ///
    /// snaplog.record("b");
    /// snaplog.record("c");
    /// snaplog.reset();
    /// assert_eq!(snaplog.initial(), &"a");
    /// assert_eq!(snaplog.has_changes(), false);
    /// ```
    pub fn reset(&mut self) {
        self.full.reset();
    }

    /// Reserve space for `n` additional elements.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::scoped::{Snaplog, Prefixed};
    /// let mut snaplog = Snaplog::new(Prefixed::new("prefix:a"));
    /// snaplog.reserve(10);
    /// ```
    pub fn reserve(&mut self, n: usize) {
        self.full.reserve(n);
    }

    /// Reserve space for `n` additional elements.
    ///
    /// # Errors
    /// Returns an error if [`Vec::try_reserve`] failed.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::scoped::{Snaplog, Prefixed};
    /// let mut snaplog = Snaplog::new(Prefixed::new("prefix:a"));
    /// snaplog.try_reserve(10)?;
    /// # Ok::<_, Box<dyn std::error::Error>>(())
    /// ```
    pub fn try_reserve(&mut self, n: usize) -> Result<(), TryReserveError> {
        self.full.try_reserve(n)
    }

    /// Returns an iterator over references of the whole underling history.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::scoped::{Snaplog, __Prefixed as Prefixed};
    /// let mut snaplog: Snaplog<Prefixed> = Snaplog::try_from_history(
    ///     ["a", "b", "c", "d", "e"],
    ///     None,
    /// )?;
    ///
    /// let mut copy = vec![];
    /// for (snapshot, _) in snaplog.iter() {
    ///     copy.push(*snapshot);
    /// }
    ///
    /// assert_eq!(copy, ["a", "b", "c", "d", "e"]);
    /// # Ok::<_, Box<dyn std::error::Error>>(())
    /// ```
    pub fn iter(&self) -> Iter<'_, T> {
        self.into_iter()
    }

    /// Returns an iterator over mutable references of the whole underling history.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::scoped::{Snaplog, __Prefixed as Prefixed};
    /// let mut snaplog: Snaplog<Prefixed> = Snaplog::try_from_history(
    ///     ["a", "b", "c", "d", "e"],
    ///     None,
    /// )?;
    ///
    /// for (snapshot, _) in snaplog.iter_mut().filter(|&(&mut s, _)| s == "a" || s == "d") {
    ///     *snapshot = "f";
    /// }
    ///
    /// assert_eq!(snaplog.history(), ["f", "b", "c", "f", "e"]);
    /// # Ok::<_, Box<dyn std::error::Error>>(())
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        self.into_iter()
    }

    /// Unwrap the [`Snaplog`] into it's initial snapshot.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::scoped::{Snaplog, __Prefixed as Prefixed};
    /// let mut snaplog = Snaplog::new(Prefixed::new("prefix:a"));
    ///
    /// snaplog.record("b");
    /// snaplog.record("c");
    /// assert_eq!(snaplog.into_initial(), Prefixed::new("prefix:a"));
    /// ```
    pub fn into_initial(self) -> T {
        T::from_scoped(self.full.into_initial(), self.ignored)
    }

    /// Unwrap the [`Snaplog`] into it's current snapshot.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::scoped::{Snaplog, __Prefixed as Prefixed};
    /// let mut snaplog = Snaplog::new(Prefixed::new("prefix:a"));
    ///
    /// snaplog.record("b");
    /// snaplog.record("c");
    /// assert_eq!(snaplog.into_current(), Prefixed::new("prefix:c"));
    /// ```
    pub fn into_current(self) -> T {
        T::from_scoped(self.full.into_current(), self.ignored)
    }

    /// Unwrap the [`Snaplog`] into it's current snapshot.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::{Select, scoped::{Snaplog, __Prefixed as Prefixed}};
    /// let mut snaplog = Snaplog::new(Prefixed::new("prefix:a"));
    ///
    /// snaplog.record("b");
    /// snaplog.record("c");
    /// assert_eq!(snaplog.into_snapshot_at(Select::At(1)), Prefixed::new("prefix:b"));
    /// ```
    pub fn into_snapshot_at(self, select: Select) -> T {
        T::from_scoped(self.full.into_snapshot_at(select), self.ignored)
    }

    /// Unwrap the [`Snaplog`] into it's history.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::{full, scoped::{Snaplog, __Prefixed as Prefixed}};
    /// let mut snaplog = Snaplog::new(Prefixed::new("prefix:a"));
    ///
    /// snaplog.record("b");
    /// snaplog.record("c");
    /// assert_eq!(
    ///     snaplog.into_inner(),
    ///     (full::Snaplog::from_history(["a", "b", "c"]), Some("prefix"))
    /// );
    /// ```
    pub fn into_inner(self) -> (full::Snaplog<T::Scope>, T::Ignored) {
        (self.full, self.ignored)
    }
}

/// Unsafe implementations.
impl<T: IntoScoped> Snaplog<T> {
    /// Creates a new [`Snaplog`] for the given `history` backing vector.
    ///
    /// # Safety
    /// The caller must ensure that the [`Vec`] contains at least one element.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::scoped::{Snaplog, __Prefixed as Prefixed};
    /// // this is fine
    /// let snaplog: Snaplog<Prefixed> = unsafe {
    ///     Snaplog::from_vec_unchecked(vec!["content"], None)
    /// };
    ///
    /// // this will later fail
    /// let snaplog: Snaplog<Prefixed> = unsafe {
    ///     Snaplog::from_vec_unchecked(vec![], Some("prefix"))
    /// };
    /// ```
    pub unsafe fn from_vec_unchecked(history: Vec<T::Scope>, ignored: T::Ignored) -> Self {
        Self {
            // SAFETY: invariants must be upheld by the caller
            full: unsafe { full::Snaplog::from_vec_unchecked(history) },
            ignored,
        }
    }

    /// Creates a new [`Snaplog`] for the given `history` backing vector.
    ///
    /// # Safety
    /// The caller must ensure that the `iter` contains at least one element.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::scoped::{Snaplog, __Prefixed as Prefixed};
    /// // this is fine
    /// let snaplog: Snaplog<Prefixed> = unsafe {
    ///     Snaplog::from_history_unchecked(["a", "b", "c"], None)
    /// };
    ///
    /// // this will later fail
    /// let snaplog: Snaplog<Prefixed> = unsafe {
    ///     Snaplog::from_history_unchecked(std::iter::empty(), Some("prefix"))
    /// };
    /// ```
    pub unsafe fn from_history_unchecked<I>(history: I, ignored: T::Ignored) -> Self
    where
        I: IntoIterator<Item = T::Scope>,
    {
        // SAFETY: invariants must be upheld by the caller
        unsafe { Self::from_vec_unchecked(history.into_iter().collect(), ignored) }
    }

    /// Returns a mutable reference to the underlying [`Vec`]. The first element of this vector is
    /// the initial element and is always set.
    ///
    /// # Safety
    /// The caller must ensure that the [`Vec`] retains at least one element after mutation, this
    /// element serves as the initial element.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::scoped::{Snaplog, __Prefixed as Prefixed};
    /// let mut snaplog: Snaplog<Prefixed> = Snaplog::try_from_history(
    ///     ["a", "b", "c", "d", "e", "f", "g"],
    ///     None,
    /// )?;
    ///
    /// // SAFETY: no elements are removed
    /// let inner = unsafe { snaplog.history_mut_vec() };
    /// inner[5] = "h";
    /// inner[6] = "i";
    /// inner.drain(1..=3);
    /// inner.push("j");
    ///
    /// assert_eq!(snaplog.history(), ["a", "e", "h", "i", "j"]);
    /// # Ok::<_, Box<dyn std::error::Error>>(())
    /// ```
    pub unsafe fn history_mut_vec(&mut self) -> &mut Vec<T::Scope> {
        // SAFETY: invariants must be upheld by the caller
        unsafe { self.full.history_mut_vec() }
    }

    /// Returns a mutable reference to the ignored part.
    ///
    /// # Safety
    /// There are no safety concerns in the current version but this is unsafe because mutation that
    /// changes things like Hashing may not be expected in other parts of the code, the caller must
    /// uphold invariants over the ignored part's mutation.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::scoped::{Snaplog, __Prefixed as Prefixed};
    /// let mut snaplog: Snaplog<Prefixed> = Snaplog::try_from_history(
    ///     ["a", "b", "c", "d", "e"],
    ///     None,
    /// )?;
    ///
    /// // SAFETY: there are no invariants regarding Prefixed not having it's prefix mutated
    /// let inner = unsafe { snaplog.ignored_mut() };
    /// *inner = Some("new_prefix");
    ///
    /// assert_eq!(snaplog.into_current(), Prefixed::new("new_prefix:e"));
    /// # Ok::<_, Box<dyn std::error::Error>>(())
    /// ```
    pub unsafe fn ignored_mut(&mut self) -> &mut T::Ignored {
        &mut self.ignored
    }
}

// first class traits
impl<T: IntoScoped> Clone for Snaplog<T>
where
    T::Scope: Clone,
    T::Ignored: Clone,
{
    fn clone(&self) -> Self {
        Self {
            full: self.full.clone(),
            ignored: self.ignored.clone(),
        }
    }

    fn clone_from(&mut self, source: &Self) {
        self.full.clone_from(&source.full);
        self.ignored.clone_from(&source.ignored);
    }
}

impl<T: IntoScoped> std::ops::Index<Select> for Snaplog<T> {
    type Output = T::Scope;

    fn index(&self, index: Select) -> &Self::Output {
        self.snapshot_at(index)
    }
}

impl<T: IntoScoped> std::ops::IndexMut<Select> for Snaplog<T> {
    fn index_mut(&mut self, index: Select) -> &mut Self::Output {
        self.snapshot_at_mut(index)
    }
}

// iter
impl<T: IntoScoped> std::iter::Extend<T::Scope> for Snaplog<T> {
    fn extend<I: IntoIterator<Item = T::Scope>>(&mut self, iter: I) {
        self.full.extend(iter);
    }
}

// iter
/// An [`Iterator`] over all snapshot scopes and references to the ignored part.
///
/// # Examples
/// ```
/// # use snaplog::scoped::{Snaplog, __Prefixed as Prefixed, IntoScoped};
/// # type Scope = &'static str;
/// # type Ignored = Option<&'static str>;
/// let mut snaplog = Snaplog::new(Prefixed::new("prefix:content"));
/// let mut iter = snaplog.into_iter();
///
/// for snapshot in iter {
///     let s: (Scope, Ignored) = snapshot;
/// }
///
/// let mut snaplog = Snaplog::new(Prefixed::new("prefix:content"));
///
/// for snapshot in snaplog {
///     let s: (Scope, Ignored) = snapshot;
/// }
/// ```
#[derive(Debug)]
pub struct IntoIter<T: IntoScoped> {
    inner: full::IntoIter<T::Scope>,
    ignored: T::Ignored,
}

impl<T: IntoScoped> IntoIter<T> {
    /// Returns a reference to the ignored part.
    pub fn ignored(&self) -> &T::Ignored {
        &self.ignored
    }
}

impl<T: IntoScoped> Iterator for IntoIter<T>
where
    T::Ignored: Clone,
{
    type Item = (T::Scope, T::Ignored);

    fn next(&mut self) -> Option<Self::Item> {
        // TODO: reduce last unnecessary clone by using a peeking iter and storing it as an Option
        self.inner.next().map(|s| (s, self.ignored.clone()))
    }
}

impl<T: IntoScoped> IntoIterator for Snaplog<T>
where
    T::Ignored: Clone,
{
    type Item = (T::Scope, T::Ignored);
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        Self::IntoIter {
            inner: self.full.into_iter(),
            ignored: self.ignored,
        }
    }
}

// TODO: exact size iter etc

/// An [`Iterator`] over references to snapshot scopes and references to the ignored part.
///
/// # Examples
/// ```
/// # use snaplog::scoped::{Snaplog, __Prefixed as Prefixed, IntoScoped};
/// # type Scope = &'static str;
/// # type Ignored = Option<&'static str>;
/// let mut snaplog = Snaplog::new(Prefixed::new("prefix:content"));
///
/// for snapshot in snaplog.iter() {
///     let s: (&Scope, &Ignored) = snapshot;
/// }
///
/// for snapshot in &snaplog {
///     let s: (&Scope, &Ignored) = snapshot;
/// }
/// ```
#[derive(Debug)]
pub struct Iter<'cl, T: IntoScoped> {
    inner: full::Iter<'cl, T::Scope>,
    ignored: &'cl T::Ignored,
}

impl<'cl, T: IntoScoped> Iter<'cl, T> {
    /// Returns a reference to the ignored part.
    pub fn ignored(&self) -> &'cl T::Ignored {
        self.ignored
    }
}

impl<'cl, T: IntoScoped> Iterator for Iter<'cl, T> {
    type Item = (&'cl T::Scope, &'cl T::Ignored);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|s| (s, self.ignored))
    }
}

impl<'cl, T: IntoScoped> IntoIterator for &'cl Snaplog<T> {
    type Item = (&'cl T::Scope, &'cl T::Ignored);
    type IntoIter = Iter<'cl, T>;

    fn into_iter(self) -> Self::IntoIter {
        Iter {
            inner: self.full.iter(),
            ignored: &self.ignored,
        }
    }
}

/// An [`Iterator`] over mutable references to snapshot scopes and references to the ignored part.
///
/// # Examples
/// ```
/// # use snaplog::scoped::{Snaplog, __Prefixed as Prefixed, IntoScoped};
/// # type Scope = &'static str;
/// # type Ignored = Option<&'static str>;
/// let mut snaplog = Snaplog::new(Prefixed::new("prefix:content"));
///
/// for snapshot in snaplog.iter_mut() {
///     let s: (&mut Scope, &Ignored) = snapshot;
/// }
///
/// for snapshot in &mut snaplog {
///     let s: (&mut Scope, &Ignored) = snapshot;
/// }
/// ```
#[derive(Debug)]
pub struct IterMut<'cl, T: IntoScoped> {
    inner: full::IterMut<'cl, T::Scope>,
    ignored: &'cl T::Ignored,
}

impl<'cl, T: IntoScoped> IterMut<'cl, T> {
    /// Returns a reference to the ignored part.
    pub fn ignored(&self) -> &'cl T::Ignored {
        self.ignored
    }
}

impl<'cl, T: IntoScoped> Iterator for IterMut<'cl, T> {
    type Item = (&'cl mut T::Scope, &'cl T::Ignored);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|s| (s, self.ignored))
    }
}

impl<'cl, T: IntoScoped> IntoIterator for &'cl mut Snaplog<T> {
    type Item = (&'cl mut T::Scope, &'cl T::Ignored);
    type IntoIter = IterMut<'cl, T>;

    fn into_iter(self) -> Self::IntoIter {
        IterMut {
            inner: self.full.iter_mut(),
            ignored: &mut self.ignored,
        }
    }
}

// conversions
impl<T: IntoScoped> From<T> for Snaplog<T> {
    fn from(initial: T) -> Self {
        Self::new(initial)
    }
}

impl<T: IntoScoped> From<Snaplog<T>> for (full::Snaplog<T::Scope>, T::Ignored) {
    fn from(snaplog: Snaplog<T>) -> Self {
        snaplog.into_inner()
    }
}

impl<T: IntoScoped> TryFrom<(Vec<T::Scope>, T::Ignored)> for Snaplog<T> {
    type Error = EmptyHistoryError;

    fn try_from(value: (Vec<T::Scope>, T::Ignored)) -> Result<Self, Self::Error> {
        Self::try_from_vec(value.0, value.1)
    }
}
