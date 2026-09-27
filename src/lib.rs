//! Readable, convergent version control.
//!
//! Every fact a history holds is written as a document a person can read, and
//! two copies that merge the same concurrent work arrive at the same bytes.
//! The library is the whole of it: the `historica` binary decides nothing the
//! library has not, so every answer a command gives is one a caller can ask
//! for directly, which decision 0053 is why.
//!
//! Persistence is asked for rather than assumed: everything that touches a
//! folder goes through [`fs::Filesystem`], and [`fs::Disk`] — the `disk`
//! feature, on by default — is the implementation that is `std::fs`. See
//! `docs/decisions/0025-the-folder-is-asked-for.md`.

#![forbid(unsafe_code)]
#![deny(missing_docs)]
#![cfg_attr(verus_keep_ghost, feature(proc_macro_hygiene, cfg_eval))]
// The proofs never ask what a derived `Clone` returns.
#![cfg_attr(verus_keep_ghost, verifier::allow(autoderive_clone_without_spec))]

mod ancestry;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use vstd::prelude::*;

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
mod trusted;
pub mod update;
pub mod working;
pub mod wrote;
