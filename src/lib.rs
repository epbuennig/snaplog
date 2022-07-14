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
//! snaplog.record_change(|prev| format!("{prev}-copy"));
//! snaplog.record_change(|_| "/path/file".to_string());
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

#![warn(missing_docs, clippy::missing_panics_doc, clippy::missing_errors_doc)]
#![deny(missing_debug_implementations, unsafe_op_in_unsafe_fn)]

// re-exports
pub mod full;
pub use full::Snaplog;

pub mod scoped;
pub use scoped::Snaplog as ScopedSnaplog;

const INVARIANT_UNWRAP: &str = "must have at least one element";

/// Select a snapshot in a snaplog.
///
/// If a snaplog has not yet be mutated then `Select::Current == Select::Initial == Select::At(0)`.
///
/// # Examples
/// ```
/// # use snaplog::{Select, Snaplog};
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// let mut snaplog = Snaplog::try_from_history((0..=10).map(|n| n * 2))?;
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
    /// Select the initial snapshot before all changes.
    Initial,

    /// Select the snapshot after `n` changes.
    At(usize),

    /// Select the current snapshot after all changes.
    Current,
}

impl Select {
    fn index_into<'s, T>(&self, slice: &'s [T]) -> &'s T {
        match self {
            Select::Initial => slice.first().expect(INVARIANT_UNWRAP),
            Select::At(idx) => &slice[*idx],
            Select::Current => slice.last().expect(INVARIANT_UNWRAP),
        }
    }

    fn index_into_mut<'s, T>(&self, slice: &'s mut [T]) -> &'s mut T {
        match self {
            Select::Initial => slice.first_mut().expect(INVARIANT_UNWRAP),
            Select::At(idx) => &mut slice[*idx],
            Select::Current => slice.last_mut().expect(INVARIANT_UNWRAP),
        }
    }

    fn index_into_remove<T>(&self, slice: &mut Vec<T>) -> T {
        match self {
            Select::Initial => slice.swap_remove(0),
            Select::At(idx) => slice.swap_remove(*idx),
            Select::Current => slice.pop().expect(INVARIANT_UNWRAP),
        }
    }
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
