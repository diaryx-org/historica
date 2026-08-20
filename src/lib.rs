//! Readable, convergent version control.
//!
//! Historica starts with a deliberately small core. Persistence and rendering
//! will be added only after their readable artifacts are specified.

#![forbid(unsafe_code)]
#![deny(missing_docs)]

pub mod core;
pub mod diff;
pub mod format;
pub mod replay;
pub mod store;
pub mod tree;
