---
title: historica
nav_title: historica
nav_order: 60
description: historica — an experiment in convergent version control where the readable files are the authority. History as documents, not a database.
audience: public
part_of: '[historica](/README.md)'
id: q26ctzx
---
<section class="pj-head">
  <div class="wrap">
    <p><a class="crumb" href="../about/#projects">diaryx.org / projects /</a></p>
    <div class="pj-title" style="margin-top: 1rem">
      <h1>historica</h1>
      <span class="pj-tags">
        <span class="tag-chip">Rust</span>
        <span class="tag-chip">MIT / Apache-2.0</span>
      </span>
    </div>
    <p class="pj-tagline">
      Version control where the readable files are the authority.
    </p>
  </div>
</section>

<section class="pj-main">
<div class="wrap pj-layout reveal">
<div class="pj-body">

historica is an experiment in readable, convergent version
control. It follows one non-negotiable rule: a person must be able
to inspect the history, understand its relationships, and recover
stored content without decoding an opaque database or binary
operation log.

- **History as documents.** Immutable revisions in a Merkle DAG, named by SHA-256 digests — the ID of a revision is what `shasum -a 256` already prints for its file.
- **Honest rewrites.** Supersession is explicit, so amending or rewriting a change is recorded rather than hidden.
- **Convergence without coordination.** History merges by set union; heads are discovered deterministically.
- **A photograph is a photograph.** Binary content is stored as payloads beside the documents — not as a diff with `+` down the margin.
- **The corpus is the spec.** Hand-written valid and invalid files are executed as tests, each refusal naming its reason.

## Where it fits

historica keeps a journal's history beside its entries —
convergent, inspectable, and durable on plain files — which is the
same bet everything else at Diaryx makes. In the app it does more
than remember: what you publish to a circle is a derived historica
store, and what your readers write back travels home the same way.

Two siblings extend it rather than living inside it:

- [historica-remark](https://github.com/diaryx-org/historica-remark) — a reader's remarks on a chain, and the layer that carries them back. The annotation model works with no historica at all.
- [historica-minisign](https://github.com/diaryx-org/historica-minisign) — signing, so a remark that arrives under someone's name can be shown to be theirs.

## Status

The core model, strict revision and operation formats, and replay
all exist and are corpus-tested, and the app runs its publishing
and remark layers on them. It isn't a general-purpose VCS today.

</div>
<aside class="pj-aside">
<div class="install">
<span class="install-head">Install</span>
<div class="cmd">cargo add historica <small>Rust</small></div>
</div>
<div class="facts">
<div class="row"><span class="k">Language</span><span class="v">Rust</span></div>
<div class="row"><span class="k">Used by</span><span class="v"><a href="../index.html">Diaryx</a> — entry history, publishing, and remark layers</span></div>
<div class="row"><span class="k">Source</span><span class="v"><a href="https://github.com/diaryx-org/historica">github.com/diaryx-org/historica</a></span></div>
<div class="row"><span class="k">Packages</span><span class="v"><a href="https://crates.io/crates/historica">crates.io/crates/historica</a></span></div>
<div class="row"><span class="k">License</span><span class="v">MIT or Apache-2.0</span></div>
</div>
</aside>
</div>
</section>
