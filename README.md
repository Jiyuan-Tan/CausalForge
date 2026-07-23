# CausalForge

CausalForge lays foundations for **formalized, machine-checked causal inference**
and builds an **AI theorem pipeline** on top of it. It contains two
[Lean 4](https://leanprover.github.io/) packages with a one-way dependency:

- **`Causalean/`** — the foundational library. Built on
  [Mathlib](https://github.com/leanprover-community/mathlib4), it formalizes core
  objects and results of modern causal inference — structural causal models,
  do-calculus, potential outcomes, identification (backdoor, frontdoor, IV, DID,
  LATE, …), partial identification / bounds, panel and design-based inference,
  causal discovery, and semiparametric estimation theory — with full
  machine-checked proofs. Documented in [`doc/API.md`](doc/API.md).
- **`CausalSmith/`** — an umbrella package containing `CausalSmith research`, an
  LLM-driven pipeline that proposes and formally verifies new causal-inference
  theorems on top of Causalean. Causalean never imports CausalSmith.

> This repository is a periodically synced snapshot of an internal development
> repo: history arrives as squashed sync commits, and process/working material is
> not included. Issues are welcome; for substantial contributions please open an
> issue first so changes can be coordinated with the internal tree.

## Quick start (fresh clone)

```sh
# 1. Toolchain — elan reads lean-toolchain and installs the pinned Lean version
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh   # if you don't have elan

# 2. Build the library (the Mathlib cache makes this minutes instead of hours)
lake exe cache get
lake build

# 3. Retrieval tooling — how you actually find things in a ~7000-declaration library
cd CausalSmith/tools && npm install
npm run search -- "backdoor adjustment"
```

Step 3 needs Node ≥ 20.20.2 and is worth doing before you read any Lean source:
the library is large, and `npm run search` is the intended entry point for
locating a definition, lemma, or module. Everything above works offline from a
fresh clone — there are no API keys, no sibling checkouts, and no network
dependencies beyond Mathlib's cache.

Then, depending on what you came for:

| You want to… | Start at |
|---|---|
| Find a specific definition or lemma | `npm run search -- "<concept>"` (see below) |
| Orient in an unfamiliar area | `npm run search -- --scope module "<area>"` |
| Browse a module's API | [`doc/API.md`](doc/API.md), section `## <n>. <path>` |
| Contribute a declaration | Write the docstring — see [Documentation](#documentation) |
| Run the theorem-generation pipeline | [Running the pipeline](#running-the-theorem-generation-pipeline) |

## Running the theorem-generation pipeline

The `CausalSmith research` pipeline — which proposes a new causal-inference
theorem, formalizes it, and machine-verifies the proof against Causalean — is
**agent-driven, not a command you type by hand.** You run it by asking an agent
(e.g. Claude Code in this repo) to use the **`causalsmith` skill**, and the skill
owns the whole discover → formalize → verify → bank workflow (spawning
sub-agents, arming watchers, handling checkpoints) on your behalf.

There are two ways to start a run:

- **You provide the topic.** Ask the agent to run the causalsmith skill on a
  topic you name, e.g. *"use the causalsmith skill to research weak-overlap
  minimax rates"* or *"run `/causalsmith research` on proximal identification
  under completeness failure."* The agent turns your topic into a proposal and
  drives it through to a banked result.
- **You let the skill choose the topic.** Ask the agent to *"use the causalsmith
  skill and let it pick a promising topic"* — it invokes the topic-selection
  sub-skill (`causalsmith-topics`) to search the literature, propose a niche, and
  proceed automatically.

Either way you interact with the agent in plain language; you do **not** need to
know the qid/specialization arguments or the internal stage machinery — the skill
handles them. The default novelty target is the `field` tier (novel relative to
the literature); say *"aim for flagship"* or *"allow subfield"* to change it.

**We recommend running in auto mode.** A full run is long and involves many
discovery/formalization/verification rounds, so add *"run it in auto mode / don't
ask me"* when you start. In auto mode the agent decides the routine math and
proof questions itself and only pauses at the genuine hard stops — most
importantly the final checkpoint where it asks you whether to bank/accept the
verified result. Without it, the run halts for your input at every stage
boundary.

Once a run is accepted, two follow-on modes are available (again, just ask the
agent):

- **Present** — *"use the causalsmith skill to present `<result>`"* turns an
  accepted, verified theorem into an arXiv-grade paper bundle plus interactive
  web artifacts.
- **Study** — *"use the causalsmith skill to study `<requirement>`"* builds a
  reusable Causalean substrate module from a plain-English requirement, bypassing
  the theorem pipeline.

Run artifacts (proposals, proof state, review logs) land under
`CausalSmith/doc/research/active/<run-id>/`; accepted results are banked under
`CausalSmith/doc/research/_bank/` and promoted into the library.

Setup prerequisites (Node, API access, environment) live in
[`CausalSmith/doc/SETUP.md`](CausalSmith/doc/SETUP.md), and the full workflow
reference is [`CausalSmith/doc/USER_MANUAL.md`](CausalSmith/doc/USER_MANUAL.md).

## Finding things in the library

Causalean has ~7000 declarations, so grep is usually the wrong tool. The project
ships a ranked retrieval CLI over a docstring-derived index
(`doc/library_index.json`), which is the same engine the CausalSmith pipeline
uses to find reusable lemmas:

```sh
cd CausalSmith/tools

# Concept search (default) — lexical ranking over names, statements, docstrings
npm run search -- "weak overlap minimax rate"

# Type-pattern search, loogle-style
npm run search -- --type "Measure _ → ℝ≥0∞"

# Goal-directed: paste a Lean goal, get lemmas that could close it
npm run search -- --goal "∀ x, f x ≤ g x"

# Module-level orientation: "which file should I read?" rather than "which lemma?"
npm run search -- --scope module "design-based interference"
```

Useful flags: `--k N` (results, default 8), `--cluster panel|exactid|partialid|stat|experimentation|scm`
to restrict the search area, and `--semantic` to add an embedding tier on top of
lexical ranking. The embedding tier requires `npm run embed:library` (Python 3 +
`sentence-transformers`); `--scope module` switches it on automatically whenever
the embeddings are present and fresh, so that mode is slower on first use.

Each hit shows the score, fully-qualified name, type signature, source file,
whether it is `tier-1` or carries a `⚠usesSorry` flag, and the docstring's
plain-English first paragraph — enough to decide whether to open the file.

If the CLI reports a missing or stale index, regenerate it:

```sh
lake build && lake exe library_index      # from the repository root
```

Two other retrieval surfaces:

- **Library explorer web app** — `CausalSmith/site/` (Astro) renders the same
  index as a browsable `/library` section with natural-language cards for
  headline theorems. `cd CausalSmith/site && npm install && npm run dev`.
- **`lean-lsp-mcp`** — if you work through an MCP-capable editor or agent, it
  gives in-file goal inspection and single-file declaration search, complementing
  the project-wide ranked search above.

## Repository layout

```
Causalean/            Foundational Lean library (the deliverable)
  Graph/              DAGs, d-separation (Bayes Ball), SWIG, c-components
  SCM/                Structural causal models, do-calculus, Markov properties;
                      ID/ (identifiability, do-calculus), PartialID/, Examples/
  PO/                 Potential outcomes: consistency, counterfactuals, laws;
                      ID/Exact/ (backdoor, frontdoor, ATE, DID, LATE, RDD, …),
                      ID/Partial/ (Manski, Balke–Pearl, Lee, Fréchet, random-set)
  Panel/              Panel-data substrate and estimand characterization
  Experimentation/    Design-based / randomization & anytime-valid inference
  Stat/, Estimation/  Semiparametric inference, concentration, DML/AIPW, minimax
  ML/                 Learning-theoretic foundations (ERM, risk, rates); uses FoML
  Discovery/          Causal discovery (invariant prediction)
  Mathlib/            Project-local Mathlib-style additions (promotion staging)
CausalSmith/          Theorem-generation pipeline (depends on Causalean)
  CausalSmith/        Generated + hand-written theorem outputs
  tools/              TypeScript pipeline (see CausalSmith/doc/SETUP.md)
  site/               Library-explorer web app (/library)
  doc/                Pipeline API, USER_MANUAL.md, SETUP.md; research/_bank/
                      holds the pipeline's banked runs
doc/                  Causalean docs: API.md, library_index.json
```

## Building

[`elan`](https://github.com/leanprover/elan) pins the Lean toolchain (see
[`lean-toolchain`](lean-toolchain)); with `elan` and `lake` installed the two
packages build independently:

```sh
lake exe cache get          # fetch Mathlib build cache (do this first — it saves hours)
lake build                  # Causalean, the foundational library
lake -d CausalSmith build   # CausalSmith pipeline package (optional; depends on Causalean)
```

A full `lake build` is slow. When iterating, build a single module —
`lake build Causalean.PO.ID.Exact.Frontdoor` — or use `lean-lsp-mcp` for
incremental diagnostics without a build.

A fresh clone builds with no extra setup: the one non-Mathlib dependency,
`FoML` (Rademacher-complexity foundations, consumed by
`Causalean/Stat/Concentration/`, `Causalean/Estimation/`, `Causalean/ML/`), is a
vendored, MIT-licensed adaptation of
[`auto-res/lean-rademacher`](https://github.com/auto-res/lean-rademacher) carried
in-tree under [`third_party/lean-rademacher/`](third_party/lean-rademacher/) (see
its `UPSTREAM.md`). See [`CausalSmith/doc/SETUP.md`](CausalSmith/doc/SETUP.md) for
the pipeline's additional prerequisites.

## Documentation

- **[`doc/API.md`](doc/API.md)** — per-module API reference (derived from
  declaration docstrings).
- **[`CausalSmith/doc/USER_MANUAL.md`](CausalSmith/doc/USER_MANUAL.md)** — how to
  run the `CausalSmith research` pipeline.
- **[`CausalSmith/doc/SETUP.md`](CausalSmith/doc/SETUP.md)** — environment
  prerequisites for the pipeline.

Per-declaration documentation is **docstring-canonical**: each declaration's
plain-English description is authored once, in its Lean docstring, where the
first paragraph is a self-contained natural-language translation of the formal
statement written for a reader with no Lean background. Everything else —
`doc/API.md`'s per-declaration tables, `doc/library_index.json`, the search
embeddings, and the web explorer — is *derived* from those docstrings and
regenerated, never hand-edited.

So to document something, write its docstring; to describe a whole file, write
its `/-! -/` module docstring. After changing declarations or docstrings,
regenerate the derived views:

```sh
lake build && lake exe library_index                 # index (reads the .olean, so build first)
cd CausalSmith/tools && npm run doc:gen              # API.md generated tables
npm run embed:library && npm run lint:embeddings     # semantic search tier (optional)
```

`npm run doc:check` guards `doc/API.md` freshness in CI.

## License

Licensed under the [Apache License 2.0](LICENSE). See [`NOTICE`](NOTICE) for
attribution and third-party dependencies.
