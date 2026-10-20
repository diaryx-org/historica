//! Remarks on somebody else's history, and the layer that carries them back.
//!
//! Two halves, and a caller may want either alone.
//!
//! **The remark** ([`annotation`]) is the W3C Web Annotation Data Model,
//! flattened into a metadata block: a target, a selector quoting the passage
//! with a little of its context, a motivation, a body, and the revision the
//! reader was looking at. [`anchor`] finds the quoted passage again in text
//! that has since changed, and says how sure it is. One motivation, `editing`, is
//! a patch rather than a note — the quoted passage and what should stand in
//! its place — and [`apply`] is the pure half of taking one. Another,
//! `offering`, points to a fork and the revision in it offered: a forge's
//! pull request, written in the offerer's own chain.
//!
//! **The thread** ([`thread`]) is what replies make of a remark. A reply may
//! close or reopen the thread it answers, or label it, and [`fold`] turns a
//! thread into its state, given whose replies count. It needs only the
//! remarks, so it is in the model half.
//!
//! **The layer** ([`layer`]) is the transport. A layer is a companion
//! chain — somebody else's single-writer history, fetched into a directory
//! beside your own, kept current by fetching again, and carried onward when
//! your own history leaves.
//!
//! # The loop
//!
//! ```text
//!   author ──── publishes ────▶ reader
//!                                 │ remarks, in a chain of their own
//!   author ◀─── publishes ────────┘
//!     │ keeps that chain as a layer, and carries it
//!     └──────── publishes ────▶ every other reader
//! ```
//!
//! Nothing about the mechanism knows which direction it is running in: the
//! reader who remarks on the author's letters does exactly what the author
//! did — writes, snapshots, publishes — and the author receives it the same
//! way the reader received the letters. "Comment access" is not a permission
//! anywhere in this; it is the machinery run the other way.
//!
//! And a remark reaching a third reader is still the remark's author's. It
//! travels as their own chain, digest-verified end to end, with the author's
//! own signed claims carried alongside it — so the store in the middle is a
//! courier rather than a witness. That is the property the whole shape
//! is for, and it is why a layer is a chain and not a pile of copied
//! documents.
//!
//! # Reading one
//!
//! ```no_run
//! use historica_remark::{Reader, layer::Layers};
//!
//! let layers = Layers::at("vault/history/remarks");
//! let reader = Reader::new();
//! for name in layers.names()? {
//!     let layer = layers.layer(&name)?;
//!     let who = layers.sender(&name);
//!     for remark in layer.remarks(&reader, &who, None)? {
//!         println!("{who} on {}: {}", remark.annotation.target, remark.annotation.body);
//!     }
//! }
//! # Ok::<(), historica_remark::Error>(())
//! ```
//!
//! # Writing one
//!
//! A remark is content, and content is the caller's. This crate does not
//! record, snapshot or publish — historica does that, and a caller that keeps
//! documents already has its own way of writing one. So the writing side here
//! is [`Annotation::fields`], which hands back the metadata in order for a
//! caller to write with its own document machinery, and
//! [`Annotation::render`] for a caller that has none.
//!
//! # Features
//!
//! `default-features = false` leaves the annotation model and `fig`: no
//! historica, no store, no filesystem. What a renderer, a viewer or an
//! importer takes.
//!
//! - `layer` — the transport. Everything that touches a store.

#![cfg_attr(docsrs, feature(doc_cfg))]

pub mod annotation;
mod document;
mod error;
pub mod thread;

#[cfg(feature = "layer")]
#[cfg_attr(docsrs, doc(cfg(feature = "layer")))]
pub mod layer;

pub use annotation::{
    AT_FIELD, Anchor, Annotation, AnyTarget, Applied, COLOR_FIELD, CREATOR_FIELD, EXACT_FIELD,
    FIELDS, FORK_FIELD, Fields, LABEL_FIELD, MOTIVATION_FIELD, Motivation, Offer, PREFIX_FIELD,
    REPLACEMENT_FIELD, Reader, SUFFIX_FIELD, Selector, Status, TARGET_FIELD, THREAD_FIELD,
    TIP_FIELD, TargetCheck, UNLABEL_FIELD, VIA_FIELD, anchor, apply,
};
pub use error::{Error, Result};
pub use thread::{Post, Thread, fold};

#[cfg(feature = "layer")]
pub use layer::{Export, Layers, Received, Remark, Repo};
