//! Readable, convergent version control.
//!
//! Historica starts with a deliberately small core. Persistence and rendering
//! will be added only after their readable artifacts are specified.

#![forbid(unsafe_code)]
#![deny(missing_docs)]

pub mod conflict;
pub mod core;
pub mod diff;
pub mod format;
pub mod merge;
pub mod naming;
pub mod record;
pub mod replay;
pub mod store;
pub mod tree;
pub mod working;
