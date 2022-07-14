# Changelog

---
## [Unreleased]


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


[Unreleased]: https://github.com/epbuennig/snaplog/compare/v0.2.1...master
[0.2.1]: https://github.com/epbuennig/snaplog/compare/v0.2.0...v0.2.1
[0.2.0]: https://github.com/epbuennig/snaplog/compare/v0.1.0...v0.2.0
[0.1.0]: https://github.com/epbuennig/snaplog/compare/master...v0.1.0
