/*!
 * Transport-agnostic, multi-mode retrieval core over the Causalean library index.
 *
 * Motivation: the pipeline GENERATES `doc/library_index.json` but the agent loop does
 * not CONSUME it — the scaffolder is driven by path lists + a hardcoded name-glob
 * reuse list and is told to search by hand, so it only finds declarations it thought
 * to look up. This core turns the index into ranked candidates so the scaffold brief
 * can PUSH the likely-relevant existing decls at the agent (concept mode), and so a
 * future F3 / MCP consumer can do goal-directed and type-pattern Causalean lemma
 * search that lean-lsp only offers for Mathlib.
 *
 * Three query modes share one index load + one Candidate shape:
 *   - concept     : NL keyword + alias-lexicon expansion (the scaffold-reuse mode)
 *   - typePattern : loogle-style symbol-set match over the Lean `statement`
 *   - goal        : a `sorry`'s goal type → lemmas whose conclusion shape overlaps it
 *
 * Best-effort by construction: a missing / unreadable / integrity-broken index yields
 * an empty result (never a throw), so retrieval can never break brief assembly.
 *
 * See doc/research/2026-06-17-causalean-reuse-retrieval-design.md.
 */

import { existsSync, readFileSync, readdirSync } from "node:fs";
import { join } from "node:path";
import { isTier1, type AreaSidecar, type LibDecl, type Library } from "../library/schema.js";
import { CLUSTER_SUBSTRATE_ROOTS, inClusterSubstrate, type ClusterKey } from "../constants.js";
import { expandQuery, normalizeConcept } from "./causal_aliases.js";
import type { SemanticTier } from "./semantic_tier.js";

// ─── public types ───────────────────────────────────────────────────────────

export type Query =
  | { mode: "concept"; title: string; label?: string; bodyTerms?: string[] }
  | { mode: "typePattern"; pattern: string }
  | { mode: "goal"; goalType: string };

export interface SearchOpts {
  /** Restrict to the cluster's substrate roots; null/undefined = whole library. */
  cluster?: ClusterKey | null;
  /** Max candidates returned (default 5). */
  topK?: number;
  exclude?: Set<string>;
  semantic?: {
    tier: SemanticTier;
    queryVec: Float32Array;
    simFloor?: number;      // min cosine for a semantic candidate (default 0.1, tuned for the FT encoder)
    kSem?: number;          // semantic candidates fused in (default 30, tuned for the FT encoder)
    k0?: number;            // RRF damping constant (default 60)
    lexConfident?: number;  // lexical top-score that protects lexical from dense (default LEX_CONFIDENT_DEFAULT)
    graphProp?: number;     // Ch4 one-hop refs-graph propagation λ (0/undefined = off)
    fusion?: "rrf" | "weighted"; // fusion method (default "rrf" — confidence-aware RRF)
    wLex?: number;          // weighted-fusion lexical weight (default 0.3)
    wDense?: number;        // weighted-fusion dense weight (default 0.7)
  };
}

export interface Candidate {
  name: string;
  statement: string;
  docFirstPara: string;
  module: string;
  file: string;
  tier1: boolean;
  usesSorry: boolean;
  score: number;
  matchedVia: "name" | "doc" | "statement" | "alias" | "module-fallback" | "semantic";
}

export interface Retrieval {
  search(q: Query, opts?: SearchOpts): Candidate[];
  get(name: string): LibDecl | null;
  /** Loaded library, or null when the index is unavailable / broken. */
  readonly library: Library | null;
}

// ─── tokenization helpers ───────────────────────────────────────────────────

const STOP = new Set([
  "the", "a", "an", "of", "for", "to", "in", "on", "at", "and", "or", "is", "be",
  "with", "by", "as", "its", "this", "that", "over", "under", "via", "per", "into",
  "from", "each", "both", "all", "any", "not", "no", "given", "where", "when",
]);

/** Crude singular stem (plurals only); keeps short tokens intact. */
function stem(t: string): string {
  if (t.length > 4 && t.endsWith("ies")) return t.slice(0, -3) + "y";
  if (t.length > 3 && t.endsWith("ss")) return t;
  if (t.length > 3 && t.endsWith("s")) return t.slice(0, -1);
  return t;
}

// Connective / structural words that occur INSIDE multi-word concept phrases (e.g.
// "conditional independence of potential outcomes", "average treatment effect") but
// are not themselves the discriminator. They are filtered from NAME matching when they
// arrive via ALIAS expansion — in a terse identifier such a match is incidental and
// buries the real concept decls (whose distinctive word often lives only in the
// docstring). They are NOT filtered from doc/statement matching, and a token the user
// TYPED keeps full name weight regardless.
// Low-discriminating tokens. Used two ways: (1) dropped from ALIAS expansion so a
// connective word in an alias phrase ("control" from "negative control") never injects
// a name match; (2) counted at a FRACTIONAL weight in the name channel (see
// `weightedNameOverlap`) so that several generic hits cannot outrank one specific hit —
// e.g. "treatment"+"effect" on a Panel `TreatmentEffectFixed` must not beat "quantile"
// on `Stat.quantile_le_iff`, and the 30-decl MTW `…Bridge…` family must not swamp a
// proximal "bridge function" whose real signal lives in the body.
const GENERIC_NAME_TOKENS = new Set([
  "conditional", "independence", "independent", "potential", "outcome", "outcomes",
  "average", "treatment", "effect", "effects", "mean", "common", "observed",
  "response", "function", "functional", "model", "distribution", "condition", "parameter",
  "general", "standard", "value", "values", "variable", "variables", "estimator",
  "estimation", "regression", "sample", "control", "controls",
  // "causal" matches the whole `…Causal…` module subtree; "method"/"approach" are
  // connective words in alias phrases ("control function method", "synthetic control
  // method") — both produce false name matches via alias expansion.
  "causal", "method", "approach",
  // Structural-metaphor / type-constructor tokens that name large, semantically-mixed
  // families: "system" suffixes ~1100 PO/Estimation bundles; "bridge" names the MTW IV
  // response-type family, Panel CellBridge, GoodmanBacon, AND proximal proxy bridges.
  // The specific co-token (population, cell, balke) is what should discriminate.
  "system", "bridge",
  // number-word connectives in alias phrases ("two way fixed effects") that otherwise
  // name-match unrelated decls (`TwoProxyAssumptions`, `oneLp`).
  "two", "one",
  // F1-plan template words: every P-/L- item body carries a "Type: …" field, so "type"
  // spuriously matches `ResponseType…`/`EdgeType…` decls (and re-grants the tier bonus).
  "type", "types",
  // "set" is a ubiquitous structural noun (~200 decls: `identifiedSet`, `CriterionSet`,
  // `RandomSet`, `ancestralSet`, …). "covariate set"/"adjustment set" must not let
  // `CriterionSet.identifiedSet` outrank `backdoorAdjustment`; the co-token discriminates.
  "set",
]);

/** Lowercase word tokens, stopword-filtered, plural-stemmed. */
function tokenize(s: string): string[] {
  return s
    .toLowerCase()
    .split(/[^a-z0-9]+/)
    .filter((t) => t.length > 1 && !STOP.has(t))
    .map(stem);
}

/** Tokens of a fully-qualified decl name, splitting dots AND camelCase. */
function nameTokens(name: string): string[] {
  return name
    .split(".")
    .flatMap((seg) => seg.replace(/([a-z0-9])([A-Z])/g, "$1 $2"))
    .flatMap(tokenize);
}

/**
 * Concatenated content of all `…`-backtick spans in an F1 item — where the plan writes
 * Lean/math (`Submodule.orthogonalProjection`, `Set.Icc`, `‖h₀‖`, `⟨·,·⟩`). This is the
 * raw material for the type-signature pass: word-poor geometry items carry their
 * discriminating content here, not in prose.
 */
export function backtickSpans(text: string): string {
  const out: string[] = [];
  for (const m of text.matchAll(/`([^`]+)`/g)) out.push(m[1]);
  return out.join(" ");
}

/** First paragraph of a docstring (the NL translation), whitespace-collapsed. */
function firstPara(doc: string | null | undefined): string {
  if (!doc) return "";
  return doc.split(/\n\s*\n/)[0].replace(/\s+/g, " ").trim();
}

/** Notable unicode math operators worth matching structurally in a Lean statement. */
const MATH_SYMBOLS = /[∀∃∫∑∏⨆⨅⊥≤≥≠∈∉⊆⊂∩∪→↔¬·×]/u;

/**
 * Vocabulary-independent "shape" of a Lean statement / type: identifier runs
 * (incl. dotted names like `Set.Icc`) plus notable math operators. Holes/underscores
 * are dropped so a `_`-pattern term matches anything.
 */
export function symbolSet(s: string): Set<string> {
  const out = new Set<string>();
  for (const m of s.matchAll(/[A-Za-z][A-Za-z0-9_.']*/g)) {
    const tok = m[0].toLowerCase();
    if (tok.length > 1) out.add(tok);
    // Split qualified names: `MeasureTheory.condExp` also yields `measuretheory`
    // and `condexp`, so a pattern/goal of `condExp` matches a namespaced statement.
    if (tok.includes(".")) for (const part of tok.split(".")) if (part.length > 1) out.add(part);
  }
  for (const ch of s) if (MATH_SYMBOLS.test(ch)) out.add(ch);
  return out;
}

function overlap(a: Set<string>, b: Set<string>): number {
  let n = 0;
  for (const t of a) if (b.has(t)) n++;
  return n;
}

/**
 * Name-channel overlap where a {@link GENERIC_NAME_TOKENS} hit counts for only a
 * fraction of a specific hit. A decl name is short, so without this a couple of generic
 * matches ("treatment"+"effect", "bridge") dominate a single high-signal match
 * ("quantile", "population"). Four generic hits ≈ one specific hit.
 */
const GENERIC_NAME_WEIGHT = 0.25;
function weightedNameOverlap(terms: Set<string>, nameT: Set<string>): number {
  let w = 0;
  for (const t of terms) if (nameT.has(t)) w += GENERIC_NAME_TOKENS.has(t) ? GENERIC_NAME_WEIGHT : 1;
  return w;
}

// ─── precomputed per-decl index (memoized by root) ──────────────────────────

interface IndexedDecl {
  d: LibDecl;
  nameT: Set<string>;
  docT: Set<string>;
  stmtT: Set<string>;
  sym: Set<string>;
  tier1: boolean;
}

const libCache = new Map<string, Library | null>();
const indexCache = new Map<string, IndexedDecl[] | null>();
const ixByNameCache = new Map<string, Map<string, IndexedDecl>>();

/**
 * Lenient index load for retrieval. Unlike `loadLibrary` (which THROWS on sidecar
 * integrity drift — stale headline/review entries vs the current index), this never
 * throws: it reads `library_index.json` and treats the sidecars as a best-effort tier
 * signal. A stale headline simply matches no decl. Strict integrity is the job of
 * `check_library_index`, not of retrieval — coupling to it would silently disable the
 * feature whenever the curation lags the code (the common mid-development state).
 */
export function loadLibraryLenient(root: string): Library | null {
  const idxPath = join(root, "doc", "library_index.json");
  if (!existsSync(idxPath)) return null;
  let raw: {
    commit?: string;
    toolchain?: string;
    entries?: (Omit<LibDecl, "proofRefs"> & { proofRefs?: unknown })[];
    modules?: Record<string, string | null>;
  };
  try {
    raw = JSON.parse(readFileSync(idxPath, "utf8"));
  } catch {
    return null;
  }
  const entries: LibDecl[] = Array.isArray(raw.entries)
    ? raw.entries.map((e) => ({
        ...e,
        proofRefs: Array.isArray(e.proofRefs) ? e.proofRefs.filter((r): r is string => typeof r === "string") : [],
      }))
    : [];
  if (entries.length === 0) return null;
  const sidecars: Record<string, AreaSidecar> = {};
  try {
    for (const f of readdirSync(join(root, "doc", "library_review")).filter((x) => x.endsWith(".json"))) {
      try {
        const sc = JSON.parse(readFileSync(join(root, "doc", "library_review", f), "utf8")) as Partial<AreaSidecar>;
        sidecars[f.replace(/\.json$/, "")] = {
          headline_theorems: Array.isArray(sc.headline_theorems) ? sc.headline_theorems : [],
          reviews: Array.isArray(sc.reviews) ? sc.reviews : [],
          flags: Array.isArray(sc.flags) ? sc.flags : [],
        };
      } catch {
        /* skip a malformed sidecar — tier boost is best-effort */
      }
    }
  } catch {
    /* no review dir — fine */
  }
  return {
    commit: typeof raw.commit === "string" ? raw.commit : "unknown",
    toolchain: typeof raw.toolchain === "string" ? raw.toolchain : "unknown",
    entries,
    modules: raw.modules ?? {},
    sidecars,
  };
}

function getLibrary(root: string): Library | null {
  if (libCache.has(root)) return libCache.get(root)!;
  const lib = loadLibraryLenient(root);
  libCache.set(root, lib);
  return lib;
}

function getIndexed(root: string): IndexedDecl[] | null {
  if (indexCache.has(root)) return indexCache.get(root)!;
  const lib = getLibrary(root);
  if (!lib) {
    indexCache.set(root, null);
    return null;
  }
  const arr = lib.entries.map((d) => ({
    d,
    nameT: new Set(nameTokens(d.name)),
    docT: new Set(tokenize(firstPara(d.doc))),
    stmtT: new Set(tokenize(d.statement)),
    sym: symbolSet(d.statement),
    tier1: isTier1(d, lib.sidecars),
  }));
  indexCache.set(root, arr);
  return arr;
}

/** Name → IndexedDecl, memoized per root — lets semantic-only hits recover display metadata. */
function getIndexedByName(root: string): Map<string, IndexedDecl> {
  let m = ixByNameCache.get(root);
  if (!m) {
    m = new Map((getIndexed(root) ?? []).map((ix) => [ix.d.name, ix]));
    ixByNameCache.set(root, m);
  }
  return m;
}

/** Drop memoized library/index state (tests that mutate fixtures on disk). */
export function clearRetrievalCache(): void {
  libCache.clear();
  indexCache.clear();
  ixByNameCache.clear();
  conceptCache.clear();
}

// ─── cluster filter ─────────────────────────────────────────────────────────

// Single definition, shared with the semantic tier so the two cannot drift apart.
const inCluster = inClusterSubstrate;

// ─── per-mode scoring ───────────────────────────────────────────────────────

type Scored = { score: number; via: Candidate["matchedVia"] };

// Reuse demerits, shared by all modes: a sorried decl imports proof debt; an
// auto-generated `instance` (e.g. `instIsProbabilityMeasure…`) is implementation glue,
// never an API-level reuse target.
const penalty = (ix: IndexedDecl): number =>
  (ix.d.usesSorry ? -3 : 0) + (ix.d.kind === "instance" ? -5 : 0);

/** Query-dependent (decl-independent) token sets for a concept query. Computing these —
 *  especially `expandQuery` over the alias lexicon — is the expensive part of concept
 *  scoring, and it is identical for every decl in a search, so it is memoized by query
 *  text. Without this it was recomputed once per decl (≈6.5k× per query), making the
 *  eval O(nDecls·nQueries) in alias expansion. */
interface PreparedConcept { terms: Set<string>; origTerms: Set<string>; specific: Set<string>; }
const conceptCache = new Map<string, PreparedConcept>();
function prepConcept(q: Extract<Query, { mode: "concept" }>): PreparedConcept {
  const queryText = [q.title, ...(q.bodyTerms ?? [])].join(" ");
  const hit = conceptCache.get(queryText);
  if (hit) return hit;
  const origTerms = new Set(tokenize(queryText));
  // An alias-injected connective token (e.g. "control" from "negative control",
  // "variable" from "proxy variables") is a weak discriminator everywhere — in names
  // AND in prose it matches unrelated decls. Drop generics from the alias expansion;
  // the user's own typed tokens always stay (so an explicit "control" still matches).
  const aliasTerms = expandQuery(queryText).terms.flatMap(tokenize).filter((t) => !GENERIC_NAME_TOKENS.has(t));
  const terms = new Set([...origTerms, ...aliasTerms]);
  // Specific (non-generic) signal — precomputed once, used for the tier-1 bonus gate below.
  const specific = new Set([...terms].filter((t) => !GENERIC_NAME_TOKENS.has(t)));
  const prepared = { terms, origTerms, specific };
  conceptCache.set(queryText, prepared);
  return prepared;
}

function scoreConcept(q: Extract<Query, { mode: "concept" }>, ix: IndexedDecl): Scored {
  const { terms, origTerms, specific } = prepConcept(q);

  const nameOv = weightedNameOverlap(terms, ix.nameT);
  const docOv = overlap(terms, ix.docT);
  const stmtOv = overlap(terms, ix.stmtT);
  if (nameOv + docOv + stmtOv === 0) return { score: 0, via: "name" };

  // Specific (non-generic) signal anywhere. A match driven ONLY by generic tokens
  // (e.g. a tier-1 MTW `…Bridge…` decl hit solely by "bridge") is not a real fit, so it
  // must not collect the curation bonus — otherwise 25 tier-1 decls float to the top of
  // a symbol-heavy F1 item whose true content (inner products, projections) is word-poor.
  // (`specific` is precomputed in prepConcept.)
  const hasSpecific =
    overlap(specific, ix.nameT) + overlap(specific, ix.docT) + overlap(specific, ix.stmtT) > 0;

  const score =
    3 * nameOv +
    2 * Math.min(docOv, 4) +
    1 * Math.min(stmtOv, 4) +
    (ix.tier1 && hasSpecific ? 2 : 0) +
    penalty(ix);

  const origNameOv = overlap(origTerms, ix.nameT);
  const via: Candidate["matchedVia"] =
    nameOv > 0 ? (origNameOv > 0 ? "name" : "alias") : docOv > 0 ? "doc" : "statement";
  return { score, via };
}

// Operators in almost every Prop — they carry no discriminating shape, so a pattern made
// only of these (`→ ∀ ≤`) must not match the whole library. The structural operators
// (∫ ⨆ ⨅ ⊥ ⊆ ∩ ∪ × ·) are kept: they ARE distinctive.
const UBIQUITOUS_SYM = new Set(["→", "∀", "∃", "≤", "≥", "∈", "∉", "↔", "¬"]);

function scoreTypePattern(pattern: string, ix: IndexedDecl): Scored {
  const psym = symbolSet(pattern);
  psym.delete("_");
  for (const s of UBIQUITOUS_SYM) psym.delete(s);
  if (psym.size === 0) return { score: 0, via: "statement" };
  const n = overlap(psym, ix.sym);
  if (n === 0) return { score: 0, via: "statement" };
  const frac = n / psym.size;
  const score = 4 * n + 8 * frac + (ix.tier1 ? 1 : 0) + penalty(ix);
  return { score, via: "statement" };
}

// Generic shape tokens that carry little discriminating signal for goal matching.
const GENERIC_SYM = new Set([
  "→", "∀", "∃", "≤", "≥", "∈", "fun", "prop", "type", "real", "set", "nat",
]);

function scoreGoal(goalType: string, ix: IndexedDecl): Scored {
  const gsym = symbolSet(goalType);
  let n = 0;
  let idHits = 0;
  for (const s of gsym) {
    if (!ix.sym.has(s)) continue;
    n++;
    if (/^[a-z]/i.test(s) && s.length > 2 && !GENERIC_SYM.has(s)) idHits++;
  }
  if (n === 0) return { score: 0, via: "statement" };
  const score = 2 * n + 4 * idHits + (ix.tier1 ? 1 : 0) + penalty(ix);
  return { score, via: "statement" };
}

function scoreDecl(q: Query, ix: IndexedDecl): Scored {
  switch (q.mode) {
    case "concept":
      return scoreConcept(q, ix);
    case "typePattern":
      return scoreTypePattern(q.pattern, ix);
    case "goal":
      return scoreGoal(q.goalType, ix);
  }
}

function toCandidate(ix: IndexedDecl, score: number, via: Candidate["matchedVia"]): Candidate {
  return {
    name: ix.d.name,
    statement: ix.d.statement,
    docFirstPara: firstPara(ix.d.doc),
    module: ix.d.module,
    file: ix.d.file,
    tier1: ix.tier1,
    usesSorry: ix.d.usesSorry,
    score,
    matchedVia: via,
  };
}

// Reciprocal-Rank Fusion of the lexical and semantic ranked lists. The two score scales are
// incomparable (lexical ~0-20, cosine 0-1), so we fuse by RANK, not score: a decl's blended
// weight is Σ_lists 1/(k0 + rank). This is always-on (no thin-gate): the harness showed the
// lexical-score "thin" signal fires ~3% of the time and misses the gap stratum where semantic
// is ~4× better. Lexical candidates keep their metadata + matchedVia; semantic-only hits are
// tagged "semantic". Exported for testing.
/** Per-decl display metadata a semantic-only hit needs to render like a lexical one. */
export type DeclMeta = Pick<Candidate, "statement" | "docFirstPara" | "module" | "file" | "tier1" | "usesSorry">;

/** Lexical top-hit score at/above which lexical is treated as trustworthy and its hits are
 *  protected from dense displacement. Re-tuned for the FINE-TUNED encoder (Phase 2): the
 *  dense tier is now stronger than lexical almost everywhere, so lexical protection should
 *  rarely fire — 40 is above nearly all real lexical scores, disabling protection except for
 *  an exceptionally strong multi-token name match. (Under the old weak off-the-shelf encoder
 *  the tuned value was 10; the fine-tune inverted which channel to trust.) Held-out sweep:
 *  40 gave overall hit@3 0.609 vs 0.301 under the old throttled fusion. */
export const LEX_CONFIDENT_DEFAULT = 40;

export function blendSemantic(
  lexical: Candidate[],
  semantic: { name: string; sim: number }[],
  topK: number,
  k0 = 60,
  resolve?: (name: string) => DeclMeta | null,
  confidentScore = LEX_CONFIDENT_DEFAULT,
): Candidate[] {
  // Confidence-aware fusion. Lexical hits that clear `confidentScore` (name-strong) are pinned
  // at the head in lexical order, so a dense-boosted but wrong decl can't displace a correct
  // lexical top hit. When lexical is weak (gap queries — nothing clears the bar) the head is
  // empty and dense drives the full RRF blend, preserving the gap-stratum win.
  const head = lexical.filter((c) => c.score >= confidentScore);
  const headNames = new Set(head.map((c) => c.name));

  const rrf = new Map<string, number>();
  lexical.forEach((c, i) => {
    if (!headNames.has(c.name)) rrf.set(c.name, (rrf.get(c.name) ?? 0) + 1 / (k0 + i + 1));
  });
  semantic.forEach((h, i) => {
    if (!headNames.has(h.name)) rrf.set(h.name, (rrf.get(h.name) ?? 0) + 1 / (k0 + i + 1));
  });
  const lexByName = new Map(lexical.map((c) => [c.name, c]));
  const tail: Candidate[] = [...rrf].map(([name, score]) => {
    const lex = lexByName.get(name);
    if (lex) return { ...lex, score };
    // Semantic-only hit: recover real statement/file/module so the Stage-2 reuse
    // contract has a signature to inspect. Without the resolver (or an unresolvable
    // name) fall back to empty — never throw.
    const meta = resolve?.(name) ?? null;
    return {
      name,
      statement: meta?.statement ?? "",
      docFirstPara: meta?.docFirstPara ?? "",
      module: meta?.module ?? "",
      file: meta?.file ?? "",
      tier1: meta?.tier1 ?? false,
      usesSorry: meta?.usesSorry ?? false,
      score,
      matchedVia: "semantic" as const,
    };
  });
  tail.sort((a, b) => b.score - a.score || a.name.localeCompare(b.name));
  return [...head, ...tail].slice(0, topK);
}

/**
 * Alternative to {@link blendSemantic}'s rank-based RRF: min-max-normalized WEIGHTED SCORE SUM
 * (Phase 2d). RRF fuses by rank alone and discards the dense cosine's magnitude; with a strong
 * fine-tuned encoder that magnitude is informative (0.9 ≫ 0.5). Each channel is min-max-normalized
 * over its own present candidates, then `score = wLex·lexNorm + wDense·denseNorm` (a decl missing
 * from a channel contributes 0 there). A decl present in both channels is rewarded by both.
 * Exported for testing / the eval A/B; `blendSemantic` remains the production default.
 */
export function blendWeighted(
  lexical: Candidate[],
  semantic: { name: string; sim: number }[],
  topK: number,
  wLex = 0.3,
  wDense = 0.7,
  resolve?: (name: string) => DeclMeta | null,
  confidentScore = LEX_CONFIDENT_DEFAULT,
): Candidate[] {
  // Same confidence-aware protection as blendSemantic: a name-strong lexical hit (score ≥
  // confidentScore) is pinned at the head in lexical order, so dense magnitude can't displace a
  // correct confident lexical top hit. This is what preserves the lexical-favouring anchor (real
  // F1-item) distribution while dense magnitude drives the gap stratum where lexical is weak.
  const head = lexical.filter((c) => c.score >= confidentScore);
  const headNames = new Set(head.map((c) => c.name));
  const lexTail = lexical.filter((c) => !headNames.has(c.name));
  const semTail = semantic.filter((h) => !headNames.has(h.name));

  const lexByName = new Map(lexTail.map((c) => [c.name, c]));
  const simByName = new Map(semTail.map((h) => [h.name, h.sim]));
  const lexVals = lexTail.map((c) => c.score);
  const simVals = semTail.map((h) => h.sim);
  const norm = (v: number, vals: number[]): number => {
    if (vals.length === 0) return 0;
    let mn = vals[0], mx = vals[0];
    for (const x of vals) { if (x < mn) mn = x; if (x > mx) mx = x; }
    return mx > mn ? (v - mn) / (mx - mn) : 1; // all-equal present channel → full credit (no div0)
  };
  const names = new Set([...lexByName.keys(), ...simByName.keys()]);
  const tail: Candidate[] = [...names].map((name) => {
    const lex = lexByName.get(name);
    const sim = simByName.get(name);
    const score = (lex ? wLex * norm(lex.score, lexVals) : 0) + (sim !== undefined ? wDense * norm(sim, simVals) : 0);
    if (lex) return { ...lex, score };
    const meta = resolve?.(name) ?? null;
    return {
      name,
      statement: meta?.statement ?? "",
      docFirstPara: meta?.docFirstPara ?? "",
      module: meta?.module ?? "",
      file: meta?.file ?? "",
      tier1: meta?.tier1 ?? false,
      usesSorry: meta?.usesSorry ?? false,
      score,
      matchedVia: "semantic" as const,
    };
  });
  tail.sort((a, b) => b.score - a.score || a.name.localeCompare(b.name));
  return [...head, ...tail].slice(0, topK);
}

export interface RankedName {
  name: string;
  score: number;
}

/** Aggregate proof-term premises from a ranked neighbour list.
 *  Neighbour rank is 0-based and contributes weight 1/(rank+2). Exported for tests. */
export function rankPremisesFromProofRefs(neighbours: { proofRefs: string[]; name?: string }[]): RankedName[] {
  const scores = new Map<string, number>();
  neighbours.forEach((n, i) => {
    const w = 1 / (i + 2);
    for (const p of n.proofRefs) scores.set(p, (scores.get(p) ?? 0) + w);
  });
  return [...scores]
    .map(([name, score]) => ({ name, score }))
    .sort((a, b) => b.score - a.score || a.name.localeCompare(b.name));
}

/** Reciprocal-rank fusion over ranked name lists, using 0-based ranks as specified.
 *  A duplicate within one list contributes only at its first rank. Exported for tests. */
export function fuseRankedListsRrf(lists: string[][], k0: number, topK: number): RankedName[] {
  const scores = new Map<string, number>();
  for (const list of lists) {
    const seen = new Set<string>();
    list.forEach((name, rank) => {
      if (seen.has(name)) return;
      seen.add(name);
      scores.set(name, (scores.get(name) ?? 0) + 1 / (k0 + rank));
    });
  }
  return [...scores]
    .map(([name, score]) => ({ name, score }))
    .sort((a, b) => b.score - a.score || a.name.localeCompare(b.name))
    .slice(0, topK);
}

/**
 * Rerank the fused candidate list with a cross-encoder (Phase 2c). The bi-encoder must compress
 * each decl to a single point; the cross-encoder attends the query tokens against each decl's
 * text jointly and resolves the "several plausibly-related lemmas — which one" confusions that
 * dominate rank-2-vs-rank-7 errors. Only the top-`pool` (the bi-encoder's recall pool) is
 * reordered — reranking is expensive per pair, and beyond the pool the fused order is retained.
 *
 * `scores[i]` is the reranker score for `fused[i]` (for i < pool); it is written onto the
 * candidate's `score` so the downstream confidence gate (Phase 3) reads calibrated raw material.
 * A pool-tail (i ≥ pool) keeps its fused score + relative order and sits below the reranked pool.
 * Exported for testing.
 */
export function applyRerank(
  fused: Candidate[],
  scores: number[],
  pool: number,
  topK: number,
): Candidate[] {
  const n = Math.min(pool, fused.length, scores.length);
  const head = fused
    .slice(0, n)
    .map((c, i) => ({ ...c, score: scores[i] }))
    .sort((a, b) => b.score - a.score || a.name.localeCompare(b.name));
  return [...head, ...fused.slice(n)].slice(0, topK);
}

// ─── factory ────────────────────────────────────────────────────────────────

/**
 * Bind a retrieval instance to a Causalean package root (the dir containing
 * `doc/library_index.json`). Index load is memoized per root. The returned object
 * is the transport-agnostic surface an MCP wrapper / F3 caller re-exposes.
 */
export function createRetrieval(root: string): Retrieval {
  const lib = getLibrary(root);
  const byName = lib ? new Map(lib.entries.map((e) => [e.name, e])) : new Map<string, LibDecl>();
  const searchImpl = (q: Query, opts: SearchOpts = {}): Candidate[] => {
      const indexed = getIndexed(root);
      if (!indexed) return [];
      const topK = opts.topK ?? 5;
      const out: Candidate[] = [];
      for (const ix of indexed) {
        if (!inCluster(ix.d.file, opts.cluster)) continue;
        if (opts.exclude?.has(ix.d.name)) continue;
        const { score, via } = scoreDecl(q, ix);
        if (score > 0) out.push(toCandidate(ix, score, via));
      }
      out.sort((a, b) => b.score - a.score || a.name.localeCompare(b.name));
      const lexical = out;
      if (q.mode === "goal") {
        if (!opts.semantic) return lexical.slice(0, topK);
        const neighbours = searchImpl(
          { mode: "concept", title: q.goalType },
          { ...opts, topK: 40 },
        )
          .map((c) => byName.get(c.name) ?? null)
          .filter((d): d is LibDecl =>
            d !== null &&
            d.kind === "theorem" &&
            d.proofRefs.length > 0 &&
            !(opts.exclude?.has(d.name) ?? false),
          )
          .slice(0, 30);
        const premiseNames = rankPremisesFromProofRefs(neighbours).map((p) => p.name);
        const fused = fuseRankedListsRrf(
          [premiseNames, lexical.map((c) => c.name)],
          10,
          premiseNames.length + lexical.length,
        );
        const lexByName = new Map(lexical.map((c) => [c.name, c]));
        const ixByName = getIndexedByName(root);
        return fused.flatMap(({ name, score }) => {
          const lex = lexByName.get(name);
          if (lex) return [{ ...lex, score }];
          const ix = ixByName.get(name);
          if (!ix) return [];
          if (!inCluster(ix.d.file, opts.cluster)) return [];
          if (opts.exclude?.has(ix.d.name)) return [];
          return [toCandidate(ix, score, "semantic")];
        }).slice(0, topK);
      }
      if (!opts.semantic) return lexical.slice(0, topK);
      const s = opts.semantic;
      const semantic = s.tier.topK(s.queryVec, {
        // Defaults re-tuned for the fine-tuned encoder (Phase 2): a much stronger dense tier
        // wants more candidates fused (kSem 10→30) and a far lower floor (0.3→0.1) — the old
        // 0.3 floor filtered out many correct fine-tuned hits before fusion could see them.
        k: s.kSem ?? 30,
        floor: s.simFloor ?? 0.1,
        cluster: opts.cluster ?? null,
        exclude: opts.exclude ?? new Set(),
        graphProp: s.graphProp,
      });
      const ixByName = getIndexedByName(root);
      const resolve = (name: string): DeclMeta | null => {
        const ix = ixByName.get(name);
        return ix
          ? {
              statement: ix.d.statement,
              docFirstPara: firstPara(ix.d.doc),
              module: ix.d.module,
              file: ix.d.file,
              tier1: ix.tier1,
              usesSorry: ix.d.usesSorry,
            }
          : null;
      };
      return s.fusion === "weighted"
        ? blendWeighted(lexical, semantic, topK, s.wLex ?? 0.3, s.wDense ?? 0.7, resolve)
        : blendSemantic(lexical, semantic, topK, s.k0 ?? 60, resolve, s.lexConfident);
  };
  return {
    library: lib,
    get(name) {
      return byName.get(name) ?? null;
    },
    search: searchImpl,
  };
}

// ─── F1 plan parsing ────────────────────────────────────────────────────────

export interface F1Item {
  /** P (primitive/definition), L (lemma/helper), or A (assumption). */
  kind: "P" | "L" | "A";
  /** e.g. "P-2", "L-3a", "A-1". */
  label: string;
  /** Concept title after the label, e.g. "Propensity clip". */
  title: string;
  /** The block body text, for extra query terms (often where the concept actually is). */
  body: string;
}

/**
 * Extract the P- / L- / A-block items from an F1 NL artifact. Handles BOTH artifact
 * dialects: header style (`### P-2: Title`, the literature bank) and bold-inline style
 * (`**P-2 (Title).** body…`, the causalsmith research output, where label, title, and
 * body share one line). A block's body runs to the next labeled block or markdown
 * header. Tolerant: returns [] when neither dialect's labels are present.
 */
export function parseF1Items(md: string): F1Item[] {
  // Require an emphasis marker (header `##`, bold `**`, optionally after a `-`/`*`
  // bullet) so an in-text reference like "P-3 holds for every v" is not captured.
  const startRe = /^\s{0,3}(?:[-*+]\s+)?(#{2,5}\s*|\*\*)\s*([PLA])-(\d+)([a-z]?)\b(.*)$/;
  const items: F1Item[] = [];
  let cur: F1Item | null = null;
  let buf: string[] = [];
  const flush = () => {
    if (cur) {
      cur.body = buf.join(" ").replace(/\s+/g, " ").trim().slice(0, 400);
      items.push(cur);
    }
    cur = null;
    buf = [];
  };
  for (const ln of md.split(/\r?\n/)) {
    const m = startRe.exec(ln);
    if (m) {
      flush();
      const kind = m[2] as "P" | "L" | "A";
      const rest = m[5] ?? "";
      // Bold dialect packs `(Title).** body…` after the label; split title from body
      // at the closing `**`. Header dialect has only the title on the line.
      let span = rest;
      let bodyOnLine = "";
      if (m[1].includes("**")) {
        const i = rest.indexOf("**");
        span = i >= 0 ? rest.slice(0, i) : rest;
        bodyOnLine = i >= 0 ? rest.slice(i + 2) : "";
      }
      // Only a LEADING paren is the title (`**P-1 (Title).**`); a mid-text paren is
      // usually inline math (`… H_a(B) …`), not the title.
      const paren = span.match(/^\s*\(([^)]+)\)/);
      let title = paren ? paren[1] : span.replace(/^[\s:.\-–—]+/, "");
      title = title.replace(/[`*]/g, "").replace(/[.\s]+$/, "").trim();
      if (!title) {
        // label-only-bold dialect (`**P-1** (Title; …)`): title sits in the body paren.
        const p2 = bodyOnLine.match(/^\s*\(([^;)]+)/);
        if (p2) title = p2[1].replace(/[`*]/g, "").trim();
      }
      cur = { kind, label: `${kind}-${m[3]}${m[4]}`, title, body: "" };
      buf = [bodyOnLine.replace(/\*\*/g, "")];
    } else if (cur) {
      if (/^\s{0,3}#{1,5}\s/.test(ln)) flush(); // a section header ends the block
      else buf.push(ln);
    }
  }
  flush();
  return items;
}

// re-export so consumers (brief renderer, tests) have one import surface.
export { expandQuery, normalizeConcept };
