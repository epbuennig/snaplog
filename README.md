# Snaplog
Snaplog is a library that provides the `Snaplog` type, a struct that records changes to a value of
type `T`.

# Examples
```rust
use snaplog::{Select, Snaplog};
let mut snaplog: Snaplog<_> = vec![
    "/path/to/file".to_string(),
    "/path/to/file-backup".to_string(),
    "/path/file-backup".to_string()
].try_into()?;

assert_eq!(snaplog.has_changes(), true);

snaplog.record_change(|prev| format!("{prev}-copy"));
snaplog.record_change(|_| "/path/file".to_string());

assert_eq!(snaplog[Select::Initial], "/path/to/file");
assert_eq!(snaplog[Select::At(3)],   "/path/file-backup-copy");
assert_eq!(snaplog[Select::Current], "/path/file");

snaplog.clear_history();

assert_eq!(snaplog.history(), ["/path/file"]);
assert_eq!(snaplog.has_changes(), false);
```

# Links
- [docs.rs/snaplog](https://docs.rs/snaplog)
- [crates.io/snaplog](https://crates.io/snaplog)
