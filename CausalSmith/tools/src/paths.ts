import path from "node:path";
import { existsSync, mkdirSync } from "node:fs";

/**
 * Path helpers for the causalsmith pipeline.
 *
 * After the Causalean/CausalSmith package split, the pipeline lives inside the
 * CausalSmith package (a sibling of Causalean). Output paths are computed relative
 * to the CausalSmith package root (the directory containing CausalSmith's
 * `lakefile.toml`), which `cli.ts` resolves and passes in as `pkgRoot`.
 *
 * Layout (relative to `pkgRoot = <repo>/CausalSmith/`):
 *   CausalSmith/Panel/<QidCamel>/         Lean source for panel theorems
 *   CausalSmith/ExactID/<QidCamel>/       Lean source for exact-ID theorems
 *   CausalSmith/PartialID/<QidCamel>/     Lean source for partial-ID theorems
 *   CausalSmith/Stat/<QidCamel>/          Lean source for stat / estimation-and-inference theorems
 *   doc/research/active/<qid>/            Research-mode causalsmith runs (eid_*, pid_*, stat_*, panel_*)
 *   doc/research/_bank/                   Research-mode result bank (proposer-output, novelty-tiered)
 *   doc/study/runs/<qid>/                 Legacy study-mode formalization runs (insight-id qids)
 *   doc/study/_literature_bank/           Legacy study-mode result bank (paper-extracted, flat — no novelty tiers)
 *   tools/src/discovery/prompts/          Discovery-phase prompts (Stages −1, 0, 0.5, 1)
 *   tools/src/formalization/prompts/      Formalization-phase prompts (Stages 2, 3, 4, 5; intervention)
 *   tools/src/templates/                  Jinja templates (LaTeX skeletons)
 *
 * Research vs study split: research-mode qids carry a known prefix (panel_, eid_,
 * pid_, stat_, exp_, or scm_) chosen by the proposer; study-mode qids are raw insight ids
 * extracted from a paper (no prefix). The two share the same state machine but
 * are partitioned on disk so `findActiveStates` only scans its own kind and a
 * malformed state file in one kind cannot brick resumes in the other.
 *
 * The legacy parameter name `repoRoot` is preserved throughout this module
 * for backwards-compatibility with existing call sites, but semantically it
 * is now the CausalSmith package root.
 */

const KNOWN_RESEARCH_PREFIXES = ["eid_", "pid_", "stat_", "panel_", "exp_", "scm_"];

function assertSlug(label: "qid" | "specialization", value: string): string {
  // why: run ids become path SEGMENTS, so this guard exists to block path TRAVERSAL — not to
  // normalize the id. Reject `/ \ . .. `/absolute/empty; otherwise pass the value through UNCHANGED.
  // Colon-form study insight ids (e.g. `angrist1990:i1`) are valid single path segments and must
  // round-trip identically: the qid IS the identity used for the dir name, state, and lean-subdir
  // invariant, so any rewrite here (sanitize/hash) would either collide two ids onto one path or
  // desync the dir name from the persisted `state.qid`. Pass-through keeps it bijective and in sync.
  if (
    value === "" ||
    value === "." ||
    value === ".." ||
    value.includes("..") ||
    path.isAbsolute(value) ||
    value.includes("/") ||
    value.includes("\\")
  ) {
    throw new Error(`Invalid ${label} slug: ${value}`);
  }
  return value;
}

export function legacyRunPrefix(qid: string, specialization: string): string {
  return `${assertSlug("qid", qid)}_${assertSlug("specialization", specialization)}`;
}

export type FormalizationKind = "research" | "study";

/**
 * Insight-style qids (no recognized research prefix) come from study-pipeline S4
 * dispatch and live under `study/`. Everything else is a research-mode qid.
 *
 * Recognized research prefixes are the current cluster prefixes (`panel_`,
 * `eid_`, `pid_`, `stat_`, `exp_`, `scm_`). Insight-style ids remain readable
 * only through the retired study-run compatibility path.
 */
export function formalizationKind(qid: string): FormalizationKind {
  if (KNOWN_RESEARCH_PREFIXES.some((p) => qid.startsWith(p))) return "research";
  return "study";
}

export function isInsightStyleQid(qid: string): boolean {
  return formalizationKind(qid) === "study";
}

/**
 * Convert a qid to its CausalSmith Lean-folder camel form.
 *
 * Research-mode qids preserve the historical convention `<UPPERPREFIX>_<PascalTail>`
 * (e.g. `pid_did_anticipation_bounded` → `PID_DidAnticipationBounded`, `panel_minimal_basis`
 * → `PANEL_MinimalBasis`). Study-mode (insight-style) qids have no prefix to uppercase, so
 * they get clean PascalCase joined without underscores (`manski_nonparametric_bounds`
 * → `ManskiNonparametricBounds`).
 *
 * **Mode suffix** (post-2026-05 layout). Pipeline-produced artifacts carry a
 * suffix reflecting their origin so the on-disk layout under
 * `CausalSmith/CausalSmith/{Panel,ExactID,PartialID}/` makes the distinction
 * visible at a glance:
 *
 *   research-mode qids → `<...>_Research`  (proposer / causalsmith-discovered)
 *   study-mode qids    → `<...>_Study`     (extracted from a paper by the retired study pipeline)
 *
 * Pre-existing hand-written panel theorems (`Q1_MinimalBasis`, `Q1_SignFlip`,
 * `Q1_SpectralThreshold`, `Q1_StaggeredMinimalBasis`) predate this convention
 * and remain un-suffixed; the absence of a suffix marks them as legacy
 * hand-written substrate. New runs always emit the suffix.
 *
 * Callers that need the raw camel name without a suffix should use
 * `qidToCamelBare`.
 */
export function qidToCamel(qid: string): string {
  const bare = qidToCamelBare(qid);
  if (!bare) return bare;
  const suffix = formalizationKind(qid) === "research" ? "_Research" : "_Study";
  return `${bare}${suffix}`;
}

/** Camel form without the `_Research` / `_Study` mode suffix. */
export function qidToCamelBare(qid: string): string {
  const parts = qid.split("_").filter(Boolean);
  if (parts.length === 0) return "";
  if (isInsightStyleQid(qid)) {
    return parts
      .map((part) => part.charAt(0).toUpperCase() + part.slice(1))
      .join("");
  }
  const [prefix, ...rest] = parts;
  const head = prefix.toUpperCase();
  const tail = rest
    .map((part) => part.charAt(0).toUpperCase() + part.slice(1))
    .join("");
  return tail ? `${head}_${tail}` : head;
}

/**
 * Substrate cluster for a qid. Determines which subdirectory under
 * `CausalSmith/` the auto-generated Lean lives in.
 *
 *   eid_*    → ExactID    (backdoor, frontdoor, IV, DID, DTR, LATE, mediation)
 *   pid_*    → PartialID  (Manski, Balke-Pearl, sensitivity, bounds, missing-data)
 *   stat_*   → Stat       (estimation and inference theory of a causal estimand:
 *                          minimax rate / efficiency bound / limit law / coverage
 *                          theorem + estimator; NOT a new
 *                          identification or bounds claim — the rate/efficiency
 *                          IS the kernel)
 *   panel_*  → Panel      (free-form panel kernel)
 *   else     → Panel      (default — study-mode insight qids can override via
 *                          `state.lean_subdir` since substrate is not derivable
 *                          from the id alone; see `assertLeanSubdirInvariant`)
 */
export function substrateForQid(
  qid: string,
): "Panel" | "ExactID" | "PartialID" | "Stat" | "Experimentation" | "SCM" {
  if (qid.startsWith("eid_")) return "ExactID";
  if (qid.startsWith("pid_")) return "PartialID";
  if (qid.startsWith("stat_")) return "Stat";
  if (qid.startsWith("exp_")) return "Experimentation";
  if (qid.startsWith("scm_")) return "SCM";
  return "Panel";
}

export function canonicalLeanSubdir(qid: string): string {
  return path.posix.join("CausalSmith", substrateForQid(qid), qidToCamel(qid));
}

/**
 * Allowed lean_subdir values for a qid. Research-mode qids return a single
 * canonical value (the substrate prefix is load-bearing). Study-mode qids
 * accept any of the three substrates because the id does not encode one;
 * `paper_dispatcher` stamps the chosen substrate when seeding the state.
 *
 * **Legacy un-suffixed forms are also accepted** for both modes: any pipeline
 * run that predates the `_Research` / `_Study` suffix convention lives under the
 * bare camel name. The invariant check therefore accepts the suffixed canonical
 * form AND its bare counterpart.
 */
export function allowedLeanSubdirs(qid: string): string[] {
  const camel = qidToCamel(qid);
  const bare = qidToCamelBare(qid);
  const camels = camel === bare ? [camel] : [camel, bare];
  if (formalizationKind(qid) === "research") {
    const substrate = substrateForQid(qid);
    return camels.map((c) => path.posix.join("CausalSmith", substrate, c));
  }
  const subs: Array<"Panel" | "ExactID" | "PartialID" | "Stat"> = ["Panel", "ExactID", "PartialID", "Stat"];
  const result: string[] = [];
  for (const s of subs) for (const c of camels) result.push(path.posix.join("CausalSmith", s, c));
  return result;
}

/**
 * Root of research-mode pipeline output. Research, study, and presentation
 * artifacts deliberately live under their respective top-level mode roots.
 */
export function researchRoot(repoRoot: string): string {
  return path.join(repoRoot, "doc", "research");
}

/** @deprecated Use `researchRoot`; retained for research-only compatibility. */
export function formalizationRoot(repoRoot: string): string {
  return researchRoot(repoRoot);
}

/**
 * Per-mode root for formalization-phase run artifacts.
 */
export function formalizationKindRoot(repoRoot: string, kind: FormalizationKind): string {
  return kind === "research"
    ? path.join(researchRoot(repoRoot), "active")
    : path.join(repoRoot, "doc", "study", "runs");
}

/**
 * Per-run directory. Routes by `formalizationKind(qid)`.
 */
export function formalizationDir(repoRoot: string, qid: string): string {
  const safeQid = assertSlug("qid", qid);
  return path.join(formalizationKindRoot(repoRoot, formalizationKind(safeQid)), safeQid);
}

/**
 * Per-run LOG directory: `<formalizationDir(qid)>/logs/`. Holds every transient run-log
 * artifact (the reviewer-call debug log, launch stdout redirects, run-liveness/pid files, and the
 * per-stage agent transcripts under `logs/stages/_<stageId>__<sub-stage>.log`) so the qid folder
 * root stays uncluttered — only the durable spec/state/graph/review artifacts live at the root.
 * Use `ensureLogsDir` to also create it.
 */
export function logsDir(repoRoot: string, qid: string): string {
  return path.join(formalizationDir(repoRoot, qid), "logs");
}

/** `logsDir(...)`, created (recursively) if absent. Called once at run start so the folder exists
 *  before any stage writes a log into it. */
export function ensureLogsDir(repoRoot: string, qid: string): string {
  const dir = logsDir(repoRoot, qid);
  mkdirSync(dir, { recursive: true });
  return dir;
}

/** Which sub-stage phase an artifact belongs to under the qid folder. */
export type ArtifactPhase = "discovery" | "formalization" | "root";

/**
 * Resolve an artifact path under the qid folder, organized by phase
 * (`discovery/` or `formalization/` subfolder; `root` = the qid folder itself,
 * for state.json + run logs).
 *
 * `filename` is the CANONICAL bare name new runs write (causalsmith-style: no
 * redundant `<qid>_<spec>_` prefix, since the folder is already `<qid>`).
 * `legacyFilenames` are the historical prefixed names (e.g.
 * `<qid>_<spec>_state.json`, `<qid>_review_decision.json`) that pre-rename runs
 * and un-migrated banked entries still carry on disk.
 *
 * Resolution prefers, in order:
 *   1. canonical bare, nested (the location new runs write to)
 *   2. canonical bare, flat (pre-subfolder-split layout)
 *   3. each legacy name, nested
 *   4. each legacy name, flat
 * The FIRST existing candidate wins; if none exists (a brand-new write) the
 * canonical bare nested path is returned. So old/banked entries keep resolving
 * to their prefixed file, new runs read+write the bare name, and
 * writers/readers/banking/causalsmith all share this one resolver. Writers must
 * mkdir the dirname (subfolder).
 */
export function artifactPath(
  repoRoot: string,
  qid: string,
  phase: ArtifactPhase,
  filename: string,
  legacyFilenames: string[] = [],
): string {
  const dir = formalizationDir(repoRoot, qid);
  const names = [filename, ...legacyFilenames];
  const candidates: string[] = [];
  if (phase === "root") {
    for (const n of names) candidates.push(path.join(dir, n));
  } else {
    // canonical-then-legacy, nested-before-flat within each name family so a
    // freshly written bare/nested file always shadows a stale legacy/flat one.
    candidates.push(path.join(dir, phase, filename)); // 1
    candidates.push(path.join(dir, filename)); // 2
    for (const n of legacyFilenames) {
      candidates.push(path.join(dir, phase, n)); // 3
      candidates.push(path.join(dir, n)); // 4
    }
  }
  for (const c of candidates) if (existsSync(c)) return c;
  return candidates[0];
}

/**
 * True for a run's state-file basename: the bare `state.json` (causalsmith
 * style), the legacy prefixed `<qid>_<spec>_state.json`, or either's
 * `.archived.json` form. Used by the bank/upgrade scanners that locate a
 * state file inside an entry dir without knowing the spec up front.
 */
export function isStateFileName(name: string): boolean {
  return (
    name === "state.json" ||
    name === "state.archived.json" ||
    name.endsWith("_state.json") ||
    name.endsWith("_state.archived.json")
  );
}

/**
 * Resolve a bare-named artifact inside an ALREADY-RESOLVED directory, falling
 * back to a legacy prefixed name when only that exists on disk. For the handful
 * of call sites that build qid-folder paths by hand instead of via
 * `artifactPath` (graph store, D0 working/ledger/review artifacts). Mirrors
 * `artifactPath`'s prefer-bare-then-legacy rule: writes land on the bare name.
 */
export function resolveInDir(dir: string, bare: string, legacy: string[] = []): string {
  const barePath = path.join(dir, bare);
  if (existsSync(barePath)) return barePath;
  for (const l of legacy) {
    const lp = path.join(dir, l);
    if (existsSync(lp)) return lp;
  }
  return barePath;
}

export function statePath(repoRoot: string, qid: string, specialization: string): string {
  const prefix = legacyRunPrefix(qid, specialization);
  return artifactPath(repoRoot, qid, "root", "state.json", [`${prefix}_state.json`]);
}

export function pipelineLogPath(repoRoot: string, qid: string, specialization: string): string {
  const prefix = legacyRunPrefix(qid, specialization);
  return artifactPath(repoRoot, qid, "root", "pipeline.jsonl", [`${prefix}_pipeline.jsonl`]);
}

/**
 * The `reviews/` subfolder holding ALL review artifacts of a run: the event log
 * (`reviews.jsonl`), the D0.5 panel verdicts (`review_math.json`,
 * `review_rubric.json`), the D-1 angle reviews (`angle*_v*.json`), and the cold
 * tier-referee verdict (`review_general.json`). Resolves the bare `reviews/` dir,
 * falling back to the legacy `<qid>_<spec>_reviews/` dir name.
 */
export function reviewsDir(repoRoot: string, qid: string, specialization: string): string {
  const prefix = legacyRunPrefix(qid, specialization);
  return resolveInDir(formalizationDir(repoRoot, qid), "reviews", [`${prefix}_reviews`]);
}

export function reviewsLogPath(repoRoot: string, qid: string, specialization: string): string {
  const prefix = legacyRunPrefix(qid, specialization);
  const dir = formalizationDir(repoRoot, qid);
  // canonical (nested in reviews/) first, then the pre-move legacy locations at
  // the run root (bare, then prefixed) so existing/banked runs still resolve.
  const candidates = [
    path.join(dir, "reviews", "reviews.jsonl"),
    path.join(dir, `${prefix}_reviews`, "reviews.jsonl"),
    path.join(dir, "reviews.jsonl"),
    path.join(dir, `${prefix}_reviews.jsonl`),
  ];
  for (const c of candidates) if (existsSync(c)) return c;
  return candidates[0];
}

export function texPath(repoRoot: string, qid: string, specialization: string): string {
  const prefix = legacyRunPrefix(qid, specialization);
  return artifactPath(repoRoot, qid, "discovery", "writeup.tex", [`${prefix}.tex`]);
}

export function proposalTexPath(repoRoot: string, qid: string, specialization: string): string {
  const prefix = legacyRunPrefix(qid, specialization);
  return artifactPath(repoRoot, qid, "discovery", "proposal.tex", [`${prefix}_proposal.tex`]);
}

/**
 * Global, cross-run substrate-debt ledger. Stage 4 appends one row per
 * assumed-but-should-be-proven named hypothesis (missing-substrate gate) so the
 * outstanding infrastructure to build is tracked in one place.
 */
export function substrateDebtPath(repoRoot: string): string {
  return path.join(formalizationRoot(repoRoot), "SUBSTRATE_DEBT.md");
}

/**
 * Global, cross-run cited-dependencies registry. Holds `gate_class:"cited"`
 * assumptions — borrowed results NOT discharged at run time, formalized + assumed
 * + matched against an external `cite:` source. Unlike SUBSTRATE_DEBT.md these are
 * never "owed a build"; they may graduate to a real lemma in a future run.
 */
export function citedDependenciesPath(repoRoot: string): string {
  return path.join(formalizationRoot(repoRoot), "CITED_DEPENDENCIES.md");
}

export function proposalOutputJsonPath(
  repoRoot: string,
  qid: string,
  specialization: string,
): string {
  const prefix = legacyRunPrefix(qid, specialization);
  return artifactPath(
    repoRoot,
    qid,
    "discovery",
    "proposal_output_template.json",
    [`${prefix}_proposal_output_template.json`],
  );
}

export function proposalReviewOutputJsonPath(
  repoRoot: string,
  qid: string,
  specialization: string,
): string {
  const prefix = legacyRunPrefix(qid, specialization);
  return artifactPath(
    repoRoot,
    qid,
    "discovery",
    "proposal_review_output_template.json",
    [`${prefix}_proposal_review_output_template.json`],
  );
}

export function gapsJsonPath(repoRoot: string, qid: string, specialization: string): string {
  const prefix = legacyRunPrefix(qid, specialization);
  return artifactPath(repoRoot, qid, "discovery", "gaps.json", [`${prefix}_gaps.json`]);
}

export function mdPath(repoRoot: string, qid: string, specialization: string): string {
  const prefix = legacyRunPrefix(qid, specialization);
  return artifactPath(repoRoot, qid, "formalization", "formalization.md", [`${prefix}.md`]);
}

/**
 * F1 formalization plan: the machine-checkable map from every typed-core node to
 * the Lean object that realizes it (CausalSmith/doc/research/F1_F2_PLAN_REDESIGN.md
 * §4). Replaces the `.md` as the F1→F2 handoff. F1 authors it, F2 syncs deviations back.
 */
export function planPath(repoRoot: string, qid: string, specialization: string): string {
  const prefix = legacyRunPrefix(qid, specialization);
  return artifactPath(repoRoot, qid, "formalization", "plan.json", [`${prefix}_plan.json`]);
}

export function sorriesPath(repoRoot: string, qid: string, specialization: string): string {
  const prefix = legacyRunPrefix(qid, specialization);
  return artifactPath(repoRoot, qid, "formalization", "sorries.md", [`${prefix}_sorries.md`]);
}

export function assumptionTablePath(
  repoRoot: string,
  qid: string,
  specialization: string,
): string {
  const prefix = legacyRunPrefix(qid, specialization);
  return artifactPath(repoRoot, qid, "formalization", "assumption_table.md", [
    `${prefix}_assumption_table.md`,
  ]);
}

/**
 * F2.5 tex↔Lean crosswalk: machine-readable correspondence backbone keyed by
 * stable .md block id (P-/T-). Read by the future paper↔Lean linked view and
 * by the F2.5 PASS snapshot.
 */
export function crosswalkJsonPath(
  repoRoot: string,
  qid: string,
  specialization: string,
): string {
  const prefix = legacyRunPrefix(qid, specialization);
  return artifactPath(repoRoot, qid, "formalization", "crosswalk.json", [
    `${prefix}_crosswalk.json`,
  ]);
}

/** Human-readable rendering of the F2.5 crosswalk (sibling of the JSON). */
export function crosswalkMdPath(
  repoRoot: string,
  qid: string,
  specialization: string,
): string {
  const prefix = legacyRunPrefix(qid, specialization);
  return artifactPath(repoRoot, qid, "formalization", "crosswalk.md", [
    `${prefix}_crosswalk.md`,
  ]);
}

/**
 * F5 COMPLETE crosswalk: the lemma-inclusive, line-final tex↔Lean correspondence
 * emitted at end of pipeline (proofs done). Distinct from the F2.5 `_crosswalk`
 * gate snapshot — this is the descriptive visualization backbone covering
 * definitions, assumptions, theorems, lemmas, and propositions.
 */
export function crosswalkFullJsonPath(
  repoRoot: string,
  qid: string,
  specialization: string,
): string {
  const prefix = legacyRunPrefix(qid, specialization);
  return artifactPath(repoRoot, qid, "formalization", "crosswalk_full.json", [
    `${prefix}_crosswalk_full.json`,
  ]);
}

/** Human-readable rendering of the F5 complete crosswalk (sibling of the JSON). */
export function crosswalkFullMdPath(
  repoRoot: string,
  qid: string,
  specialization: string,
): string {
  const prefix = legacyRunPrefix(qid, specialization);
  return artifactPath(repoRoot, qid, "formalization", "crosswalk_full.md", [
    `${prefix}_crosswalk_full.md`,
  ]);
}

export function leanTheoremDir(repoRoot: string, leanSubdir: string): string {
  return path.join(repoRoot, ...leanSubdir.split("/"));
}

/**
 * Per-paper scratch directory for disposable agent probes (for example,
 * `Main.lean` and one-off `#check` files).  It deliberately lives beside the
 * paper's source, rather than at the CausalSmith package root, so concurrent
 * papers never share scratch names.
 *
 * This directory is not part of the formalization: callers which inventory,
 * review, or build a paper must exclude it.
 */
export const PAPER_TMP_DIR = "tmp";

export function paperTmpDir(repoRoot: string, leanSubdir: string): string {
  return path.join(leanTheoremDir(repoRoot, leanSubdir), PAPER_TMP_DIR);
}

/** Create and return a paper's disposable agent workspace. */
export function ensurePaperTmpDir(repoRoot: string, leanSubdir: string): string {
  const dir = paperTmpDir(repoRoot, leanSubdir);
  mkdirSync(dir, { recursive: true });
  return dir;
}

/** Whether a recursive path below a paper belongs to its disposable workspace. */
export function isPaperTmpPath(relativePath: string): boolean {
  return relativePath.split(/[\\/]+/).includes(PAPER_TMP_DIR);
}

/**
 * Root of the research-mode result bank. Holds proposer-output entries
 * (`accepted`/`downgraded`/`failed`/`legacy` tier subdirs) and is
 * the only bank that participates in novelty / burned-seed / `--upgrade`
 * machinery.
 */
export function researchBankRoot(repoRoot: string): string {
  return path.join(researchRoot(repoRoot), "_bank");
}

/**
 * Root of the literature-mode result bank. Holds study-mode entries
 * (study-pipeline S4 dispatch → causalsmith → S5 banking) in a flat layout — no
 * novelty tiers, since these are paper-reformalizations rather than
 * proposer-discovered novel theorems. Read by study-pipeline S5 and (future)
 * literature-corpus consumers.
 */
export function literatureBankRoot(repoRoot: string): string {
  return path.join(repoRoot, "doc", "study", "_literature_bank");
}

/**
 * Bank root keyed by formalization kind. Research-mode qids land in the
 * tiered `_bank/`; study-mode qids land in the flat `_literature_bank/`.
 * Callers that always want the research bank (novelty/upgrade machinery,
 * burned seeds, drift stat, legacy pointers) should call `researchBankRoot`
 * directly to make the constraint explicit.
 */
export function bankRootFor(repoRoot: string, kind: FormalizationKind): string {
  return kind === "research" ? researchBankRoot(repoRoot) : literatureBankRoot(repoRoot);
}

/**
 * Phase a prompt belongs to. The pipeline used to bundle every prompt under
 * `tools/src/research/prompts/`; after the discovery/formalization split,
 * each prompt lives in the subdir for its phase. Routing is by filename prefix
 * so adding a new stage-N prompt does not require touching this table.
 *
 *   stage_neg1_*, stage0_*   → discovery     (Stages −1, 0, 0.5 — math claim only)
 *   stage1_*, stage2_*, stage3_*, stage4_*, stage5_*, intervention*, correction_*
 *                            → formalization (Stage 1 is the NL formalization plan;
 *                                             1.5 reviews it; 2–5 are Lean.)
 */
export function promptPhase(name: string): "discovery" | "formalization" {
  // `stage_flagship_rubric.txt` is a shared block injected into BOTH discovery
  // reviewers (-0.5 / 0.5); it physically lives under discovery/prompts.
  if (
    name.startsWith("stage_neg1") ||
    name.startsWith("stage0") ||
    name === "stage_flagship_rubric.txt"
  ) {
    return "discovery";
  }
  return "formalization";
}

/**
 * Per-sub-stage subfolder for a prompt, within its phase's `prompts/` dir.
 * Deterministic (prefix-based) so it resolves identically for reading a real
 * prompt and for writing a test stub. Order matters (stage0_5 before stage0,
 * stage1_5 before stage1). Returns "" for anything unmapped (phase root).
 */
export function promptSubfolder(name: string): string {
  // Discovery (D stages)
  if (name === "stage_flagship_rubric.txt") return "_shared"; // D-0.5 + D0.5
  if (name.startsWith("stage_neg1_1") || name.startsWith("stage_neg1_2")) return "D-1";
  if (name.startsWith("stage_neg1_review")) return "D-0.5";
  if (name.startsWith("stage0_5") || name.startsWith("stage0_R")) return "D0.5";
  if (name.startsWith("stage0")) return "D0";
  // Formalization (F stages)
  if (name.startsWith("stage1_5")) return "F1.5";
  if (name.startsWith("stage1")) return "F1";
  if (name.startsWith("stage2")) return "F2";
  if (
    name === "failure_classifier.txt" ||
    name.startsWith("stage3_") ||
    name.startsWith("stage4_") ||
    name.startsWith("correction_")
  ) {
    return "F4";
  }
  if (name.startsWith("stage5")) return "F5";
  if (name.startsWith("proof_") || name.startsWith("intervention")) {
    return "F4";
  }
  return "";
}

export function promptPath(repoRoot: string, name: string): string {
  return path.join(repoRoot, "tools", "src", promptPhase(name), "prompts", promptSubfolder(name), name);
}

export function templatePath(repoRoot: string, name: string): string {
  return path.join(repoRoot, "tools", "src", "templates", name);
}
