//! Snaplog is a library that provides the [`Snaplog`] type, a struct that records changes to a
//! value of type `T` by saving a snapshot of the value after each change.
//!
//! # Examples
//! ```
//! use snaplog::{Select, Snaplog};
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! let mut snaplog: Snaplog<_> = vec![
//!     "/path/to/file".to_string(),
//!     "/path/to/file-backup".to_string(),
//!     "/path/file-backup".to_string()
//! ].try_into()?;
//!
//! assert_eq!(snaplog.has_changes(), true);
//!
//! snaplog.record(|prev| format!("{prev}-copy"));
//! snaplog.record(|_| "/path/file".to_string());
//!
//! assert_eq!(snaplog[Select::Initial], "/path/to/file");
//! assert_eq!(snaplog[Select::At(3)],   "/path/file-backup-copy");
//! assert_eq!(snaplog[Select::Current], "/path/file");
//!
//! snaplog.clear_history();
//!
//! assert_eq!(snaplog.history(), ["/path/file"]);
//! assert_eq!(snaplog.has_changes(), false);
//! # Ok(())
//! # }
//! ```

#![warn(
    clippy::missing_panics_doc,
    clippy::missing_errors_doc,
    rustdoc::missing_doc_code_examples
)]
#![deny(missing_docs, missing_debug_implementations, unsafe_op_in_unsafe_fn)]

/// Select a snapshot in a snaplog.
///
/// If a snaplog has not yet be mutated then `Select::Current == Select::Initial == Select::At(0)`.
///
/// # Examples
/// ```
/// # use snaplog::{Select, Snaplog};
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// let mut snaplog = Snaplog::from_history((0..=10).map(|n| n * 2).collect())?;
///
/// assert_eq!(snaplog[Select::Initial], 0);
/// assert_eq!(snaplog[Select::At(0)],   0);
/// assert_eq!(snaplog[Select::At(1)],   2);
/// assert_eq!(snaplog[Select::At(9)],   18);
/// assert_eq!(snaplog[Select::At(10)],  20);
/// assert_eq!(snaplog[Select::Current], 20);
/// # Ok(())
/// # }
/// ```
#[derive(Debug, Clone, Copy)]
pub enum Select {
    /// The initial snapshot before all changes.
    Initial,

    /// The snapshot after `n` changes.
    At(usize),

    /// The current snapshot after all changes.
    Current,
}

/// An [Error][std::error::Error] that occurs when trying to create a [`Snaplog`] from an empty
/// [`Vec`].
pub struct EmptyHistoryError(());

impl std::fmt::Debug for EmptyHistoryError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("EmptyHistoryError").finish()
    }
}

impl std::fmt::Display for EmptyHistoryError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("the given history was empty but at least one element is required")
    }
}

impl std::error::Error for EmptyHistoryError {}

/// A struct for recording the history of changes done to a given `T` by storing a snapshot after
/// each change. See [module level documentation][crate] for examples.
#[derive(Debug, Clone)]
#[repr(transparent)]
pub struct Snaplog<T> {
    history: Vec<T>,
}

impl<T> Snaplog<T> {
    /// Creates a new [`Snaplog`] from the given `initial` snapshot with no recorded changes.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::Snaplog;
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

    /// Creates a new [`Snaplog`] from the given `history`.
    ///
    /// # Errors
    /// Returns an error if `history` was empty.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::Snaplog;
    /// assert!(Snaplog::from_history(vec![0]).is_ok());
    /// assert!(Snaplog::<()>::from_history(vec![]).is_err());
    /// ```
    #[inline]
    pub fn from_history(history: Vec<T>) -> Result<Self, EmptyHistoryError> {
        if history.is_empty() {
            Err(EmptyHistoryError(()))
        } else {
            Ok(Self { history })
        }
    }

    /// Records a change to the current element in this [`Snaplog`].
    ///
    /// # Examples
    /// ```
    /// # use snaplog::Snaplog;
    /// let mut snaplog = Snaplog::new("a");
    ///
    /// snaplog.record(|prev| { assert_eq!(prev, &"a"); "b" });
    /// snaplog.record(|prev| { assert_eq!(prev, &"b"); "c" });
    /// assert_eq!(snaplog.history(), ["a", "b", "c"]);
    /// ```
    #[inline]
    pub fn record<F>(&mut self, mut f: F)
    where
        F: FnMut(&T) -> T,
    {
        self.history.push(f(self.current()));
    }

    /// Records multiple successive changes to the current element in this [`Snaplog`].
    ///
    /// # Examples
    /// ```
    /// # use snaplog::Snaplog;
    /// let mut snaplog = Snaplog::new("a");
    ///
    /// snaplog.record_all(&mut ["b", "c", "d"], |change, _| *change);
    /// assert_eq!(snaplog.history(), ["a", "b", "c", "d"]);
    /// ```
    pub fn record_all<F, M>(&mut self, mutations: &mut [M], mut f: F)
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
    /// # use snaplog::Snaplog;
    /// let mut snaplog = Snaplog::new("a");
    ///
    /// assert_eq!(snaplog.has_changes(), false);
    /// snaplog.record(|_| "b");
    /// snaplog.record(|_| "c");
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
    /// # use snaplog::Snaplog;
    /// let mut snaplog = Snaplog::new("a");
    ///
    /// snaplog.record(|_| "b");
    /// snaplog.record(|_| "c");
    /// assert_eq!(snaplog.initial(), &"a");
    /// ```
    #[inline]
    pub fn initial(&self) -> &T {
        self.history
            .first()
            .expect("must have at least one element")
    }

    /// Returns the current element, that is the last recorded change or the initial element if
    /// there are no none.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::Snaplog;
    /// let mut snaplog = Snaplog::new("a");
    ///
    /// snaplog.record(|_| "b");
    /// snaplog.record(|_| "c");
    /// assert_eq!(snaplog.current(), &"c");
    /// ```
    #[inline]
    pub fn current(&self) -> &T {
        self.history.last().expect("must have at least one element")
    }

    /// Returns the full history recorded in this [`Snaplog`], including the initial element.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::Snaplog;
    /// let mut snaplog = Snaplog::new("a");
    ///
    /// snaplog.record(|_| "b");
    /// snaplog.record(|_| "c");
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
    /// # use snaplog::Snaplog;
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut snaplog = Snaplog::from_history((0..=10).collect())?;
    /// let history = snaplog.history_mut();
    ///
    /// history[0] = 10;
    /// assert_eq!(snaplog.history(), [10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn history_mut(&mut self) -> &mut [T] {
        &mut self.history
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
    /// # use snaplog::Snaplog;
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut snaplog = Snaplog::from_history((0..=10).collect())?;
    ///
    /// snaplog.drain(2..=8);
    /// assert_eq!(snaplog.history(), [0, 1, 9, 10]);
    /// # Ok(())
    /// # }
    /// ```
    /// The unbounded range is reinterpreted as starting at `1`:
    /// ```
    /// # use snaplog::Snaplog;
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # let mut snaplog = Snaplog::from_history((0..=10).collect())?;
    /// snaplog.drain(..);
    /// assert_eq!(snaplog.history(), [0]);
    /// # Ok(())
    /// # }
    /// ```
    /// The only invalid lower bound is `0`:
    /// ```should_panic
    /// # use snaplog::Snaplog;
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # let mut snaplog = Snaplog::from_history((0..=10).collect())?;
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
    /// # use snaplog::Snaplog;
    /// let mut snaplog = Snaplog::new("a");
    ///
    /// snaplog.record(|_| "b");
    /// snaplog.record(|_| "c");
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
    /// # use snaplog::Snaplog;
    /// let mut snaplog = Snaplog::new("a");
    ///
    /// snaplog.record(|_| "b");
    /// snaplog.record(|_| "c");
    /// snaplog.reset();
    /// assert_eq!(snaplog.initial(), &"a");
    /// assert_eq!(snaplog.has_changes(), false);
    /// ```
    #[inline]
    pub fn reset(&mut self) {
        self.history.drain(1..);
    }

    /// Unwrap the [`Snaplog`] into it's history.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::Snaplog;
    /// let mut snaplog = Snaplog::new("a");
    ///
    /// snaplog.record(|_| "b");
    /// snaplog.record(|_| "c");
    /// assert_eq!(snaplog.into_vec(), ["a", "b", "c"]);
    /// ```
    pub fn into_vec(self) -> Vec<T> {
        self.history
    }
}

// unsafe interface
impl<T> Snaplog<T> {
    /// Creates a new [`Snaplog`] for the given `history`.
    ///
    /// # Safety
    /// The caller must ensure that the [`Vec`] contains at least one element.
    ///
    /// # Examples
    /// ```
    /// # use snaplog::Snaplog;
    /// assert!(Snaplog::from_history(vec![0]).is_ok());
    /// assert!(Snaplog::<()>::from_history(vec![]).is_err());
    /// ```
    #[inline]
    pub unsafe fn from_history_unchecked(history: Vec<T>) -> Self {
        Self { history }
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
    /// # use snaplog::Snaplog;
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut snaplog = Snaplog::from_history((0..=10).collect())?;
    ///
    /// // SAFETY: no elements are removed
    /// let inner = unsafe { snaplog.history_mut_unchecked() };
    /// inner[5] = 100;
    /// inner[6] = 200;
    /// assert_eq!(snaplog.history(), [0, 1, 2, 3, 4, 100, 200, 7, 8, 9, 10]);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub unsafe fn history_mut_unchecked(&mut self) -> &mut Vec<T> {
        &mut self.history
    }
}

impl<T: PartialEq> std::cmp::PartialEq for Snaplog<T> {
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

impl<T: Eq> std::cmp::Eq for Snaplog<T> {}

impl<T> std::ops::Index<Select> for Snaplog<T> {
    type Output = T;

    #[inline]
    fn index(&self, index: Select) -> &Self::Output {
        match index {
            Select::Initial => self.initial(),
            Select::At(idx) => &self.history[idx],
            Select::Current => self.current(),
        }
    }
}

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
        Self::from_history(value)
    }
}
