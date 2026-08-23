//! Readable, convergent version control.
//!
//! Historica starts with a deliberately small core. Persistence and rendering
//! will be added only after their readable artifacts are specified.
//!
//! Persistence is asked for rather than assumed: everything that touches a
//! folder goes through [`fs::Filesystem`], and [`fs::Disk`] — the `disk`
//! feature, on by default — is the implementation that is `std::fs`. See
//! `docs/decisions/0025-the-folder-is-asked-for.md`.

#![forbid(unsafe_code)]
#![deny(missing_docs)]

mod ancestry;

pub mod conflict;
pub mod core;
pub mod diff;
pub mod format;
pub mod fs;
pub mod merge;
pub mod naming;
pub mod record;
pub mod replay;
pub mod store;
pub mod tree;
pub mod working;
