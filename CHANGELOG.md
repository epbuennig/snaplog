# Changelog

---
## [Unreleased]
### Added
- `Snaplog::try_record_change` for fallible changes

### Changed
- removed inline attributes

---
## [0.3.1]
### Added
- `Snaplog::snapshot_at`
- `Snaplog::initial_mut` (these are added for consistency but will be removed as well as their
  immutable version)
- `Snaplog::current_mut` (these are added for consistency but will be removed as well as their
  immutable version)
- `Snaplog::snapshot_at_mut`
- `Snaplog::clone_snapshot_at`

### Fixed
- inconsistent doc examples
- fixed changelog link


---
## [0.3.0]
### Added
- `scoped::Snaplog`

### Changes
- more consistent documentation
- relaxed bounds on `[try_]from_history[_unchecked]` form `Iterator` to `IntoIterator`
- more consistent naming (previous name to new name):
  - `Snaplog::from_iter_unchecked` => `Snaplog::from_history_unchecked`
  - `Snaplog::history_mut_unchecked` => `Snaplog::history_mut_vec`


---
## [0.2.1]
### Fixed
- made iter types and module public


---
## [0.2.0] - 2022-07-11
### Added
- `Snaplog::record` (previously took change, now takes snapshot)
- `Snaplog::record_all` (previously took changes, now takes snapshots)
- `Snaplog::from_vec` fallible `try_*`, unchecked `*_unchecked` and panicing version
- `Snaplog::from_history` fallible `try_*`, unchecked `*_unchecked` and panicing version
- `Iter`, `IterMut`, `IntoIter` type aliases, iterator implementations
- `IndexMut` impl for `Snaplog`
- `into_initial`, `into_snapshot_at`, `into_current`

### Changes
- more consistent documentation
- more consistent naming (previous name to new name):
  - `Snaplog::from_history` => `Snaplog::from_vec`
  - `Snaplog::record` => `Snaplog::record_change`
  - `Snaplog::record_all` => `Snaplog::record_changes_all`
- made `Clone::clone_from` use `Vec` optimized path

### Fixed
- fixed typo in README and docs


---
## [0.1.0] - 2022-07-10
Initial Release


[Unreleased]: https://github.com/epbuennig/snaplog/compare/v0.3.1...master
[0.3.1]: https://github.com/epbuennig/snaplog/compare/v0.3.0...v0.3.1
[0.3.0]: https://github.com/epbuennig/snaplog/compare/v0.2.1...v0.3.0
[0.2.1]: https://github.com/epbuennig/snaplog/compare/v0.2.0...v0.2.1
[0.2.0]: https://github.com/epbuennig/snaplog/compare/v0.1.0...v0.2.0
[0.1.0]: https://github.com/epbuennig/snaplog/compare/master...v0.1.0
