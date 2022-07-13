//! A full [`Snaplog`] and it's associated types. A `Snaplog` is used to record snapshots of changes
//! to a value, such as successive edits to a file's contents.
//!
//! # Examples
//! ```
//! # use snaplog::{full::Snaplog, Select};
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! let mut snaplog: Snaplog<_> = vec![
//!     "content".to_string(),
//!     "new-content".to_string()
//! ].try_into()?;
//!
//! snaplog.record_change(|prev| format!("{prev}-change"));
//! snaplog.record("final-content".to_string());
//!
//! assert_eq!(snaplog[Select::Initial], "content");
//! assert_eq!(snaplog[Select::At(2)],   "new-content-change");
//! assert_eq!(snaplog[Select::Current], "final-content");
//!
//! snaplog.clear_history();
//!
//! assert_eq!(snaplog.history(), ["final-content"]);
//! assert_eq!(snaplog.has_changes(), false);
//! # Ok(())
//! # }
//! ```

use crate::{EmptyHistoryError, Select, INVARIANT_UNWRAP};

/// A struct for recording the history of changes done to a given `T` by storing a snapshot after
/// each change. The history of snapshots is stored in [`Vec`] in ascending order, that means the
/// first element is the initial element.
///
/// # Examples
/// ```
/// # use snaplog::{full::Snaplog, Select};
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// let mut snaplog: Snaplog<_> = vec![
///     "/path/to/file".to_string(),
///     "/path/to/file-backup".to_string(),
///     "/path/file-backup".to_string()
/// ].try_into()?;
///
/// assert_eq!(snaplog.has_changes(), true);
///
/// snaplog.record_change(|prev| format!("{prev}-copy"));
/// snaplog.record_change(|_| "/path/file".to_string());
///
/// assert_eq!(snaplog[Select::Initial], "/path/to/file");
/// assert_eq!(snaplog[Select::At(3)],   "/path/file-backup-copy");
/// assert_eq!(snaplog[Select::Current], "/path/file");
///
/// snaplog.clear_history();
///
/// assert_eq!(snaplog.history(), ["/path/file"]);
/// assert_eq!(snaplog.has_changes(), false);
/// # Ok(())
/// # }
/// ```
#[derive(Debug)]
#[repr(transparent)]
pub struct Snaplog<T> {
    history: Vec<T>,
}

impl<T> Snaplog<T> {
    /// Creates a new [`Snaplog`] from the given `initial` snapshot with no recorded changes.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::full::Snaplog;
    /// let snaplog = Snaplog::new(0);
    ///
    /// assert_eq!(snaplog.initial(), snaplog.current());
    /// assert_eq!(snaplog.has_changes(), false);
    /// ```
    #[inline]
    pub fn new(initial: T) -> Self {
        Self {
            history: vec![initial],
        }
    }

    /// Creates a new [`Snaplog`] for the given `history` backing vector.
    ///
    /// # Errors
    /// Returns an error if `history` was empty.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::full::Snaplog;
    /// assert!(Snaplog::try_from_vec(vec![0]).is_ok());
    /// assert!(Snaplog::<()>::try_from_vec(vec![]).is_err());
    /// ```
    #[inline]
    pub fn try_from_vec(history: Vec<T>) -> Result<Self, EmptyHistoryError> {
        if history.is_empty() {
            Err(EmptyHistoryError(()))
        } else {
            Ok(Self { history })
        }
    }

    /// Creates a new [`Snaplog`] for the given `history` backing vector.
    ///
    /// # Panics
    /// Panics if `history` was empty.
    ///
    ///
    /// # Examples
    /// ```
    /// # use snaplog::full::Snaplog;
    /// let snaplog = Snaplog::from_vec(vec![0]);
    /// ```
    ///
    /// This panics:
    /// ```should_panic
    /// # use snaplog::full::Snaplog;
    /// let snaplog: Snaplog<i32> = Snaplog::from_vec(vec![]);
    /// ```
    #[inline]
    pub fn from_vec(history: Vec<T>) -> Self {
        match Self::try_from_vec(history) {
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
    /// # use snaplog::full::Snaplog;
    /// assert!(Snaplog::try_from_history(0..=10).is_ok());
    /// assert!(Snaplog::<i32>::try_from_history(std::iter::empty()).is_err());
    /// ```
    #[inline]
    pub fn try_from_history<I>(history: I) -> Result<Self, EmptyHistoryError>
    where
        I: Iterator<Item = T>,
    {
        Self::try_from_vec(history.collect())
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
    /// # use snaplog::full::Snaplog;
    /// let snaplog = Snaplog::from_history(0..=10);
    /// ```
    ///
    /// This panics:
    /// ```should_panic
    /// # use snaplog::full::Snaplog;
    /// let snaplog: Snaplog<i32> = Snaplog::from_history(std::iter::empty());
    /// ```
    #[inline]
    pub fn from_history<I>(history: I) -> Self
    where
        I: Iterator<Item = T>,
    {
        Self::from_vec(history.collect())
    }

    /// Records a snapshot in this [`Snaplog`].
    ///
    /// # Examples
    /// ```
    /// # use snaplog::full::Snaplog;
    /// let mut snaplog = Snaplog::new("a");
    ///
    /// snaplog.record("b");
    /// snaplog.record("c");
    /// assert_eq!(snaplog.history(), ["a", "b", "c"]);
    /// ```
    #[inline]
    pub fn record(&mut self, snapshot: T) {
        self.history.push(snapshot);
    }

    /// Records multiple snapshots in this [`Snaplog`].
    ///
    /// # Examples
    /// ```
    /// # use snaplog::full::Snaplog;
    /// let mut snaplog = Snaplog::new("a");
    ///
    /// snaplog.record_all(["b", "c", "d"]);
    /// assert_eq!(snaplog.history(), ["a", "b", "c", "d"]);
    /// ```
    pub fn record_all<I>(&mut self, snapshots: I)
    where
        I: IntoIterator<Item = T>,
    {
        self.history.extend(snapshots);
    }

    /// Records a change to the current element in this [`Snaplog`].
    ///
    /// # Examples
    /// ```
    /// # use snaplog::full::Snaplog;
    /// let mut snaplog = Snaplog::new("a");
    ///
    /// snaplog.record_change(|prev| { assert_eq!(prev, &"a"); "b" });
    /// snaplog.record_change(|prev| { assert_eq!(prev, &"b"); "c" });
    /// assert_eq!(snaplog.history(), ["a", "b", "c"]);
    /// ```
    #[inline]
    pub fn record_change<F>(&mut self, mut f: F)
    where
        F: FnMut(&T) -> T,
    {
        self.history.push(f(self.current()));
    }

    // NOTE: this may be superseded by an impl using a single Generator that takes the current arg
    // and yields the next, but it would have to be some kind of generator that can give a goos size
    // estimation which in turn would hurt the ergonomics
    //
    // this impl:
    // pub fn record_changes_all<G>(&mut self, generator: G)
    //     where for<'t> G: Generator<&'t T, Yield = T, Return = ()>
    //
    // came with live time problems when I tested it out and using it with generator syntax eg.:
    // let snapshot = Snapshot::new("initial".to_string());
    // snapshot.record_changes_all(|prev| yield format!("{prev}-edit"));
    //
    // the current impl is the closest thing to an ergonomic size hint generator

    /// Records multiple successive changes to the current element in this [`Snaplog`].
    ///
    /// # Examples
    /// ```
    /// # use snaplog::full::Snaplog;
    /// let mut snaplog = Snaplog::new("a");
    ///
    /// snaplog.record_changes_all(&mut ["b", "c", "d"], |change, _| *change);
    /// assert_eq!(snaplog.history(), ["a", "b", "c", "d"]);
    /// ```
    pub fn record_changes_all<F, M>(&mut self, mutations: &mut [M], mut f: F)
    where
        F: FnMut(&mut M, &T) -> T,
    {
        self.history.reserve(mutations.len());

        for mutation in mutations {
            self.history.push(f(mutation, self.current()));
        }
    }

    /// Returns whether or not there are any changes recorded in this [`Snaplog`].
    ///
    /// # Examples
    /// ```
    /// # use snaplog::full::Snaplog;
    /// let mut snaplog = Snaplog::new("a");
    ///
    /// assert_eq!(snaplog.has_changes(), false);
    /// snaplog.record_change(|_| "b");
    /// snaplog.record_change(|_| "c");
    /// assert_eq!(snaplog.has_changes(), true);
    /// ```
    #[inline]
    pub fn has_changes(&self) -> bool {
        self.history.len() > 1
    }

    /// Returns the initial element.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::full::Snaplog;
    /// let mut snaplog = Snaplog::new("a");
    ///
    /// snaplog.record_change(|_| "b");
    /// snaplog.record_change(|_| "c");
    /// assert_eq!(snaplog.initial(), &"a");
    /// ```
    #[inline]
    pub fn initial(&self) -> &T {
        self.history.first().expect(INVARIANT_UNWRAP)
    }

    /// Returns the current element, that is the last recorded change or the initial element if
    /// there are no none.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::full::Snaplog;
    /// let mut snaplog = Snaplog::new("a");
    ///
    /// snaplog.record_change(|_| "b");
    /// snaplog.record_change(|_| "c");
    /// assert_eq!(snaplog.current(), &"c");
    /// ```
    #[inline]
    pub fn current(&self) -> &T {
        self.history.last().expect(INVARIANT_UNWRAP)
    }

    /// Returns the full history recorded in this [`Snaplog`], including the initial element.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::full::Snaplog;
    /// let mut snaplog = Snaplog::new("a");
    ///
    /// snaplog.record_change(|_| "b");
    /// snaplog.record_change(|_| "c");
    /// assert_eq!(snaplog.history(), ["a", "b", "c"]);
    /// ```
    #[inline]
    pub fn history(&self) -> &[T] {
        self.history.as_slice()
    }

    /// Returns a mutable reference to the underlying `history`.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::full::Snaplog;
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut snaplog = Snaplog::try_from_history(0..=10)?;
    /// let history = snaplog.history_mut();
    ///
    /// history[0] = 10;
    /// assert_eq!(snaplog.history(), [10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn history_mut(&mut self) -> &mut [T] {
        self.history.as_mut_slice()
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
    /// # use snaplog::full::Snaplog;
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut snaplog = Snaplog::try_from_history(0..=10)?;
    ///
    /// snaplog.drain(2..=8);
    /// assert_eq!(snaplog.history(), [0, 1, 9, 10]);
    /// # Ok(())
    /// # }
    /// ```
    /// The unbounded range is reinterpreted as starting at `1`:
    /// ```
    /// # use snaplog::full::Snaplog;
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # let mut snaplog = Snaplog::try_from_history(0..=10)?;
    /// snaplog.drain(..);
    /// assert_eq!(snaplog.history(), [0]);
    /// # Ok(())
    /// # }
    /// ```
    /// The only invalid lower bound is `0`:
    /// ```should_panic
    /// # use snaplog::full::Snaplog;
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # let mut snaplog = Snaplog::try_from_history(0..=10)?;
    /// snaplog.drain(0..);
    /// # Ok(())
    /// # }
    /// ```
    pub fn drain<R>(&mut self, range: R) -> impl Iterator<Item = T> + '_
    where
        R: std::ops::RangeBounds<usize>,
    {
        let start_bound = match range.start_bound() {
            std::ops::Bound::Included(&idx) if idx == 0 => panic!("cannot drain initial element"),
            std::ops::Bound::Included(&idx) => std::ops::Bound::Included(idx),
            std::ops::Bound::Excluded(&idx) => std::ops::Bound::Excluded(idx),
            std::ops::Bound::Unbounded => std::ops::Bound::Excluded(0),
        };

        self.history
            .drain((start_bound, range.end_bound().cloned()))
    }

    /// Wipe the recorded history, keeping only the current element as the new initial element.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::full::Snaplog;
    /// let mut snaplog = Snaplog::new("a");
    ///
    /// snaplog.record_change(|_| "b");
    /// snaplog.record_change(|_| "c");
    /// snaplog.clear_history();
    /// assert_eq!(snaplog.initial(), &"c");
    /// assert_eq!(snaplog.has_changes(), false);
    /// ```
    pub fn clear_history(&mut self) {
        self.history.drain(..self.history.len() - 1);
    }

    /// Wipe the recorded changes, keeping only the initial element.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::full::Snaplog;
    /// let mut snaplog = Snaplog::new("a");
    ///
    /// snaplog.record_change(|_| "b");
    /// snaplog.record_change(|_| "c");
    /// snaplog.reset();
    /// assert_eq!(snaplog.initial(), &"a");
    /// assert_eq!(snaplog.has_changes(), false);
    /// ```
    #[inline]
    pub fn reset(&mut self) {
        self.history.drain(1..);
    }

    /// Returns an iterator over references of the whole underling history.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::full::Snaplog;
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut snaplog = Snaplog::try_from_history(0..=10)?;
    ///
    /// let mut copy = vec![];
    /// for &snapshot in snaplog.iter() {
    ///     copy.push(snapshot);
    /// }
    ///
    /// assert_eq!(copy, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn iter(&self) -> Iter<'_, T> {
        self.history.iter()
    }

    /// Returns an iterator over mutable references of the whole underling history.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::full::Snaplog;
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut snaplog = Snaplog::try_from_history(0..=10)?;
    ///
    /// for snapshot in snaplog.iter_mut().filter(|&&mut n| n % 2 == 0) {
    ///     *snapshot = 2;
    /// }
    ///
    /// assert_eq!(snaplog.history(), [2, 1, 2, 3, 2, 5, 2, 7, 2, 9, 2]);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        self.history.iter_mut()
    }

    /// Unwrap the [`Snaplog`] into it's initial snapshot.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::full::Snaplog;
    /// let mut snaplog = Snaplog::new("a");
    ///
    /// snaplog.record_change(|_| "b");
    /// snaplog.record_change(|_| "c");
    /// assert_eq!(snaplog.into_initial(), "a");
    /// ```
    pub fn into_initial(mut self) -> T {
        self.history.swap_remove(0)
    }

    /// Unwrap the [`Snaplog`] into it's current snapshot.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::full::Snaplog;
    /// let mut snaplog = Snaplog::new("a");
    ///
    /// snaplog.record_change(|_| "b");
    /// snaplog.record_change(|_| "c");
    /// assert_eq!(snaplog.into_current(), "c");
    /// ```
    pub fn into_current(mut self) -> T {
        self.history.pop().expect(INVARIANT_UNWRAP)
    }

    /// Unwrap the [`Snaplog`] into it's current snapshot.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::{full::Snaplog, Select};
    /// let mut snaplog = Snaplog::new("a");
    ///
    /// snaplog.record_change(|_| "b");
    /// snaplog.record_change(|_| "c");
    /// assert_eq!(snaplog.into_snapshot_at(Select::At(1)), "b");
    /// ```
    pub fn into_snapshot_at(mut self, select: Select) -> T {
        select.index_into_remove(&mut self.history)
    }

    /// Unwrap the [`Snaplog`] into it's history.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::full::Snaplog;
    /// let mut snaplog = Snaplog::new("a");
    ///
    /// snaplog.record_change(|_| "b");
    /// snaplog.record_change(|_| "c");
    /// assert_eq!(snaplog.into_vec(), ["a", "b", "c"]);
    /// ```
    pub fn into_vec(self) -> Vec<T> {
        self.history
    }
}

// unsafe interface
impl<T> Snaplog<T> {
    /// Creates a new [`Snaplog`] for the given `history` backing vector.
    ///
    /// # Safety
    /// The caller must ensure that the [`Vec`] contains at least one element.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::full::Snaplog;
    /// // this is fine
    /// let snaplog = unsafe { Snaplog::from_vec_unchecked(vec![0]) };
    ///
    /// // this will later fail
    /// let snaplog: Snaplog<i32> = unsafe { Snaplog::from_vec_unchecked(vec![]) };
    /// ```
    #[inline]
    pub unsafe fn from_vec_unchecked(history: Vec<T>) -> Self {
        Self { history }
    }

    /// Creates a new [`Snaplog`] for the given `history` backing vector.
    ///
    /// # Safety
    /// The caller must ensure that the `iter` contains at least one element.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::full::Snaplog;
    /// // this is fine
    /// let snaplog = unsafe { Snaplog::from_iter_unchecked(0..=10) };
    ///
    /// // this will later fail
    /// let snaplog: Snaplog<i32> = unsafe { Snaplog::from_iter_unchecked(std::iter::empty()) };
    /// ```
    #[inline]
    pub unsafe fn from_iter_unchecked<I>(history: I) -> Self
    where
        I: Iterator<Item = T>,
    {
        // SAFETY: invariants must be upheld by the caller
        unsafe { Self::from_vec_unchecked(history.collect()) }
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
    /// # use snaplog::full::Snaplog;
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut snaplog = Snaplog::try_from_history(0..=10)?;
    ///
    /// // SAFETY: no elements are removed
    /// let inner = unsafe { snaplog.history_mut_unchecked() };
    /// inner[5] = 100;
    /// inner[6] = 200;
    /// inner.drain(1..=3);
    /// inner.push(300);
    ///
    /// assert_eq!(snaplog.history(), [0, 4, 100, 200, 7, 8, 9, 10, 300]);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub unsafe fn history_mut_unchecked(&mut self) -> &mut Vec<T> {
        &mut self.history
    }
}

// first class traits
impl<T: PartialEq> PartialEq for Snaplog<T> {
    fn eq(&self, other: &Self) -> bool {
        // it is assumed that inequality is more common than equality
        //
        // 'trickle through' snaps (changes are not completely overwritten)
        //
        // eg.: if two snaplogs only differed in the number they appended to a file name on
        // snapshot[1] but are other wise the same:
        //
        // [0] "/a/rather/long/file/path"   // move file up
        // [1] "/a/rather/long/path"        // rename append _x where x differs on each snaplog
        // [2] "/a/rather/long/path_x"      // move file up
        // [3] "/a/rather/path_x"           // move file up
        // [4] "/a/path_x"                  // move file up
        // [5] "/path_x"
        //
        // the change for snapshot[1] is still noticeable at snapshot[5], so not all snapshots need
        // to be compared to check for inequality
        if self.initial() == other.initial() && self.history.len() == other.history.len() {
            // if they hav the same length they must both have changes if one has
            if self.has_changes() {
                (self.history.last() == other.history.last())
                    && (self.history[1..self.history.len() - 1]
                        == other.history[1..other.history.len() - 1])
            } else {
                true // no changes and initials are equal
            }
        } else {
            false // non equal initials or changelog length
        }
    }
}

impl<T: Eq> Eq for Snaplog<T> {}

impl<T: Clone> Clone for Snaplog<T> {
    fn clone(&self) -> Self {
        Self {
            history: self.history.clone(),
        }
    }

    fn clone_from(&mut self, source: &Self) {
        self.history.clone_from(&source.history)
    }
}

impl<T> std::ops::Index<Select> for Snaplog<T> {
    type Output = T;

    #[inline]
    fn index(&self, index: Select) -> &Self::Output {
        index.index_into(&self.history)
    }
}

impl<T> std::ops::IndexMut<Select> for Snaplog<T> {
    #[inline]
    fn index_mut(&mut self, index: Select) -> &mut Self::Output {
        index.index_into_mut(&mut self.history)
    }
}

// iter
impl<T> std::iter::Extend<T> for Snaplog<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        self.history.extend(iter);
    }
}

// TODO: try_from_itertor, this is likely blocked by `try_trait_v2`
// impl<T> std::iter::FromIterator<T> for Snaplog<T> {
//     fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
//         // Self::try_from_history(iter)
//         unimplemented!("is not infallible")
//     }
// }

/// A type alias for [`std::slice::Iter`].
///
/// # Examples
/// ```
/// # use snaplog::full::Snaplog;
/// let snaplog = Snaplog::new(());
///
/// for snapshot in snaplog.into_iter() {
///     let s: () = snapshot;
/// }
///
/// let snaplog = Snaplog::new(());
///
/// for snapshot in snaplog {
///     let s: () = snapshot;
/// }
/// ```
type IntoIter<T> = std::vec::IntoIter<T>;

impl<T> IntoIterator for Snaplog<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.history.into_iter()
    }
}

/// A type alias for [`std::slice::Iter`].
///
/// # Examples
/// ```
/// # use snaplog::full::Snaplog;
/// let snaplog = Snaplog::new(());
///
/// for snapshot in snaplog.iter() {
///     let s: &() = snapshot;
/// }
///
/// for snapshot in &snaplog {
///     let s: &() = snapshot;
/// }
/// ```
type Iter<'cl, T> = std::slice::Iter<'cl, T>;

impl<'cl, T> IntoIterator for &'cl Snaplog<T> {
    type Item = &'cl T;
    type IntoIter = Iter<'cl, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// A type alias for [`std::slice::IterMut`].
///
/// # Examples
/// ```
/// # use snaplog::full::Snaplog;
/// let mut snaplog = Snaplog::new(());
///
/// for snapshot in snaplog.iter_mut() {
///     let s: &mut () = snapshot;
/// }
///
/// for snapshot in &mut snaplog {
///     let s: &mut () = snapshot;
/// }
/// ```
type IterMut<'cl, T> = std::slice::IterMut<'cl, T>;

impl<'cl, T> IntoIterator for &'cl mut Snaplog<T> {
    type Item = &'cl mut T;
    type IntoIter = IterMut<'cl, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

// conversions
impl<T> From<T> for Snaplog<T> {
    #[inline]
    fn from(initial: T) -> Self {
        Self::new(initial)
    }
}

impl<T> TryFrom<Vec<T>> for Snaplog<T> {
    type Error = EmptyHistoryError;

    #[inline]
    fn try_from(value: Vec<T>) -> Result<Self, Self::Error> {
        Self::try_from_vec(value)
    }
}
