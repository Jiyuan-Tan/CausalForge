// NL↔Lean crosslinks for the paper's formal blocks — a CLOSED-WORLD assignment.
//
// The site shows each formal block beside its Lean statement, parsed into rows
// (one hypothesis, one conclusion clause each), and highlights the two together
// on hover. This module decides which paper text belongs to which Lean row.
//
// The shape of the decision is what keeps it honest. Both sides are enumerated
// DETERMINISTICALLY before any model call: the Lean statement is parsed into
// identified rows, the paper block into identified segments that tile it exactly
// and never cut a tag or a formula. The model then answers a closed question —
// for every row, which segments state it (or "unstated"); for every displayed
// formula, which declaration realizes it (or "presentation-only") — using ids,
// never quoted text. Totality is schema-enforced, so an unanswered row is a
// failed reply rather than a silent hole; and because the model never authors a
// span, none of the v2 span machinery (verbatim re-checking, overlap
// resolution, provenance arbitration, a repair round, a coverage ledger) has
// anything left to do. Deleting all of it is the point of v3.
//
// Two model calls per bundle-ish: one batched ASSIGN pass over cache-missing
// blocks, one batched VERIFY pass that audits every assignment and every
// "unstated"/"presentation-only" claim, flipping a wrong claim to a demanded
// assignment in the same reply.

import { createHash } from "node:crypto";
import { readFile } from "node:fs/promises";
import { join } from "node:path";
import { z } from "zod";
import { loadJsonCache } from "./cache.js";
import { parseJsonLoose } from "./gates.js";
import { writeJsonAtomic } from "./json_io.js";
import { presentationPrompt } from "./prompt_io.js";
import { hashEnvBody } from "./tex_anchors.js";
import {
  assignRowIds,
  isPropRecord,
  structurePropRecordView,
  structureStatementView,
  type StructuredView,
} from "./lean_structure.js";
import { scanPropDefinitionSignature } from "./lean_statement.js";
import { segmentBlock, segmentText, segmentationProblems, type NlSegment } from "./nl_segments.js";
import { MODELS } from "../models.js";
import type { LeanSnippet } from "./types.js";

/** Cache/artifact generation. One string: v3 has no rules-version dimension —
 *  a prompt edit that changes what a correct answer looks like is a policy bump. */
export const NL_LINKS_POLICY = "nl-links-v3";
export const NL_LINKS_ARTIFACT = "nl_links.json";
export const NL_LINKS_CACHE = "nl_links_cache.json";
export const NL_LINKS_VERIFY_CACHE = "nl_links_verify_cache.json";

/** Web-only drawer entries: they carry no body block in the paper, so there is
 *  no prose to assign. */
const NO_BODY_BLOCK_ENVS: ReadonlySet<string> = new Set(["citedv", "auxiliary", "symbol"]);

/** Does this crosswalk entry get crosslinks at all? Exported so the operator's
 *  dry-run sweep selects exactly what the stage selects, with no second copy of
 *  the rule to drift. */
export function selectsForNlLinks(entry: { env: string; status: string }): boolean {
  return !NO_BODY_BLOCK_ENVS.has(entry.env) && entry.status !== "presentation-synthesized";
}

/** Hard ceiling on one request's variable material. A pathological block would
 *  otherwise become a request that stalls or is truncated server-side — a silent
 *  hang or a silently half-read prompt. Fail with the size instead; the dry-run
 *  sweep reports the observed maximum so this is visible long before it fires. */
export const MAX_PROMPT_BYTES = 400_000;

/** Payload budget per batched request, for both passes. */
export const CHUNK_CHARS = 60_000;

/**
 * Ceiling on CLAIMS per verification request, independent of bytes.
 *
 * Derived from the rollout: 100-claim requests truncated reproducibly (one reply
 * left all 100 unjudged, the next 99 of 100), while every request that came back
 * complete carried 64 claims or fewer. A reply must name every claim, so its
 * length grows with the claim count while the payload's byte budget only bounds
 * the QUESTION — nothing bounded the answer. 50 sits comfortably below the
 * largest observed good request rather than at its edge.
 */
export const MAX_VERIFY_CLAIMS = 50;

/**
 * Version of what the ASSIGNMENT pass is asked for — bumped when the reply
 * contract changes, so receipts answering the older question are not replayed.
 * rules2: a display may carry SEVERAL declaration entries (one per named
 * quantity it defines), where the contract previously forced exactly one.
 *
 * NOT bumped for a prompt clarification that only disambiguates an answer shape
 * the schema already rejected. The presentation-only wording (a display is
 * presentation-only ONLY when no declaration realizes it, never alongside a decl
 * entry) is such a case: the decl/presentationOnly XOR has been enforced from
 * the start, so no cached receipt can hold the shape the clarification forbids —
 * every valid receipt already answers the clarified question, and re-billing
 * would buy nothing. Bump this only when a receipt that is VALID today could
 * legitimately differ tomorrow.
 *
 * The closed declaration vocabulary (the NAMEABLE DECLARATIONS appendix) is the
 * same kind of change and is likewise not a bump: it only removes answers the
 * gate already refused — a fabricated name never resolved, so no cached VALID
 * receipt can contain one. `blockCacheKey` hashes the block's inputs, never the
 * prompt, so every receipt replays untouched.
 */
export const ASSIGN_RULES_VERSION = "rules2";

/** Label under which a snippet's own statement appears among its pieces. */
export const STATEMENT_PART = "statement";

/**
 * Digest of EXACT bytes — no normalization of any kind. `hashEnvBody` folds
 * whitespace, which is right for content keys but wrong here: the segment
 * offsets index a specific string, and a whitespace REDISTRIBUTION (same total
 * length, different positions) would keep both a folded hash and the byte count
 * while shifting every offset. Local on purpose; `hashEnvBody` keeps its own
 * meaning everywhere else.
 */
export function rawDigest(text: string): string {
  return createHash("sha256").update(text, "utf8").digest("hex");
}

/** codex runner shape (subset of PaperDeps.runCodex); kept local to avoid a
 *  runtime import cycle with pipeline.ts. */
export interface CodexRunner {
  runCodex: (a: {
    prompt: string;
    cwd: string;
    reasoningEffort?: "minimal" | "low" | "medium" | "high" | "xhigh";
    leanLsp?: boolean;
    model?: string;
  }) => Promise<{ stdout: string; stderr: string }>;
}

/**
 * Cache load that survives a corrupted file. `loadJsonCache` propagates a JSON
 * parse error, which is right for caches whose entries are expensive verdicts an
 * operator should be told about — but these hold only derived assignments, and a
 * run that dies on a truncated cache is worse than one that re-assigns. On
 * damage: warn loudly, start empty, and let the next `writeJsonAtomic` replace
 * the damaged file (so it is repaired, never a re-bill loop).
 */
async function loadPairCache(path: string): Promise<Record<string, unknown>> {
  try {
    return await loadJsonCache<Record<string, unknown>>(path, { repair: false });
  } catch (e) {
    console.warn(
      `P4 nl-links: ${path} is unreadable (${(e as Error).message}); starting from an empty cache ` +
        `and rewriting it. Previously cached assignments for this bundle will be recomputed.`,
    );
    return {};
  }
}

// ---------------------------------------------------------------------------
// Inputs

const escapeRegExp = (s: string): string => s.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");

/**
 * Inner HTML of the `formal-block` div carrying `data-objid="<objId>"`, from the
 * emitted paper_body.html. Depth-aware (an env body may contain nested divs) and
 * anchored on the block's own opening tag — inline `<span class="leanref"
 * data-objid=…>` links carry the same attribute and must never be mistaken for a
 * block. Returns null when the object has no body block (prose/cited/auxiliary
 * drawer entries, presentation-only blocks, which carry `data-presentation-only`
 * instead).
 */
export function extractBlockHtml(html: string, objId: string): string | null {
  const attr = new RegExp(`data-objid="${escapeRegExp(objId)}"`);
  const openRe = /<div\b[^>]*class="formal-block[^"]*"[^>]*>/g;
  for (const open of html.matchAll(openRe)) {
    if (!attr.test(open[0])) continue;
    const start = open.index + open[0].length;
    const tagRe = /<div\b[^>]*>|<\/div\s*>/g;
    tagRe.lastIndex = start;
    let depth = 1;
    for (let t = tagRe.exec(html); t !== null; t = tagRe.exec(html)) {
      depth += t[0].startsWith("</") ? -1 : 1;
      if (depth === 0) return html.slice(start, t.index);
    }
    return null; // unbalanced markup: no block rather than a truncated one
  }
  return null;
}

/** One Lean text a `lean` span may come from. `part` is the stable provenance
 *  the artifact records (the site keys the snippet's own statement off the fixed
 *  `STATEMENT_PART`, a component off its label); `label` is the human name shown
 *  in the prompt's block header — the decl name for the statement. The two are
 *  separate so that changing what the artifact records can never move a cache
 *  key, which is a hash of the PROMPT text. */
export interface LeanPiece {
  part: string;
  label: string;
  text: string;
}

/** The snippet's own statement plus each component's statement, kept SEPARATE so
 *  a validated span can never straddle two pieces and always names exactly one. */
export function leanPieces(snippet: LeanSnippet): LeanPiece[] {
  return [
    { part: STATEMENT_PART, label: snippet.decl || STATEMENT_PART, text: snippet.statement ?? "" },
    ...(snippet.components ?? []).map((c) => ({ part: c.label, label: c.label, text: c.statement ?? "" })),
  ].filter((p) => p.text.trim().length > 0);
}

/** The Lean material as the prompts show it: one labelled block per piece. */
export function leanPromptText(pieces: LeanPiece[]): string {
  return pieces.map((p) => `-- ${p.label}\n${p.text}`).join("\n\n");
}

// ---------------------------------------------------------------------------
// Reference closure: the definitions a composite block's formulas actually name
//
// A definition block often prints a formula that is realized by a helper decl
// the snippet never mentions — the block's own pieces reference it, and it is
// nowhere in the material, so no pair can ever be authored for that formula.
// These are the def-kind declarations reachable from the block's pieces by
// statement reference, which the author call is shown as further pieces.

const DEF_KINDS: ReadonlySet<string> = new Set(["def", "abbrev", "structure"]);
/** A folded helper is not a pairing target; feeding it only costs tokens. */
const MAX_CLOSURE_PIECE_LINES = 40;
/** Prompt-budget guard: deterministic truncation of a pathological closure.
 *  Raised 24 → 32 (operator decision, 2026-08-31): at 24 a paper's own displayed
 *  constants could sit one piece past the cut and be unpairable. Measured cost
 *  across all bundles: +7% Lean material, far inside the per-request ceiling. */
const MAX_CLOSURE_PIECES = 32;
const CLOSURE_DEPTH = 5;

/** One declaration as `paper_library_index.json` records it. */
export interface IndexedLeanDecl {
  name: string;
  kind: string;
  file: string;
  line: number;
  source?: string;
  statement?: string;
  refs?: string[];
  proofRefs?: string[];
  /** Declarations from OTHER packages that this one references — the index
   *  records them here rather than as entries of their own, because they are not
   *  the paper's code. They are still real declarations a display can realize. */
  extRefs?: Array<{ n: string; m?: string }>;
}

export interface DeclIndex {
  byName: Map<string, IndexedLeanDecl>;
  /** Short name → decl, only where the short name is unambiguous. */
  byShort: Map<string, IndexedLeanDecl>;
  /** Every nameable declaration, sorted — the closed vocabulary a display link
   *  may draw on, shown to the model so it cannot invent a plausible name. */
  names: string[];
}

/**
 * Index every declaration the paper can name — its OWN entries, plus the
 * upstream declarations those entries reference across package boundaries.
 *
 * The cross-package half matters: `paper_library_index.json` lists only the
 * paper's own modules as entries, so a Causalean definition a paper's Lean code
 * builds on (`Causalean.Stat.hellingerSqDensity`) appears nowhere in `entries` —
 * only in some entry's `extRefs`. Without it, a display that genuinely realizes
 * that definition had no nameable answer and every attempt was refused. Only
 * REFERENCED upstream declarations are added, so the vocabulary stays the
 * development's own reach rather than all of Causalean.
 *
 * Own entries win a short name outright: an external is only reachable by its
 * short name when no entry of the paper's own code shares it.
 */
export function buildDeclIndex(entries: IndexedLeanDecl[]): DeclIndex {
  const byName = new Map<string, IndexedLeanDecl>();
  const shortHits = new Map<string, IndexedLeanDecl[]>();
  const extByName = new Map<string, IndexedLeanDecl>();
  const extShortHits = new Map<string, IndexedLeanDecl[]>();
  const shortOf = (name: string) => name.slice(name.lastIndexOf(".") + 1);
  for (const e of entries) {
    if (typeof e?.name !== "string" || e.name.length === 0) continue;
    byName.set(e.name, e);
    shortHits.set(shortOf(e.name), [...(shortHits.get(shortOf(e.name)) ?? []), e]);
  }
  for (const e of entries) {
    for (const ref of e?.extRefs ?? []) {
      if (typeof ref?.n !== "string" || ref.n.length === 0 || byName.has(ref.n) || extByName.has(ref.n)) continue;
      // `kind: "external"` keeps these out of the closure walk (def-kinds only)
      // and out of the piece text, which they have none of.
      const decl: IndexedLeanDecl = { name: ref.n, kind: "external", file: ref.m ?? "", line: 0 };
      extByName.set(ref.n, decl);
      extShortHits.set(shortOf(ref.n), [...(extShortHits.get(shortOf(ref.n)) ?? []), decl]);
    }
  }
  const byShort = new Map<string, IndexedLeanDecl>();
  for (const [short, hits] of shortHits) if (hits.length === 1) byShort.set(short, hits[0]);
  for (const [short, hits] of extShortHits) {
    if (hits.length === 1 && !shortHits.has(short)) byShort.set(short, hits[0]);
  }
  for (const [name, decl] of extByName) byName.set(name, decl);
  return { byName, byShort, names: [...byName.keys()].sort() };
}

/**
 * The closed declaration vocabulary, appended ONCE to each request.
 *
 * `displayLinks` was the last open-vocabulary answer in v3, and an open
 * vocabulary invites plausible fabrication: structure-field-shaped names
 * (`RealLaw.propensity`) for declarations that exist under quite different ones.
 * Listing every nameable declaration turns it into a choice, which is what the
 * rest of the design already relies on. Appended at the REQUEST level, never
 * inside a block's section, so it cannot move a per-block cache key.
 */
export function declVocabularyAppendix(index: DeclIndex): string {
  return [
    "NAMEABLE DECLARATIONS — every declaration of this development. A `decl` must be one of these,",
    "copied exactly. A name that is not on this list does not exist.",
    ...index.names,
  ].join("\n");
}

const shortName = (name: string): string => name.slice(name.lastIndexOf(".") + 1);

/** Index lookup by fully-qualified name, else by unambiguous short name. */
export function resolveIndexed(index: DeclIndex, name: string): IndexedLeanDecl | null {
  return index.byName.get(name) ?? index.byShort.get(shortName(name)) ?? null;
}

/** A decl's own text: the source slice (for a def the body IS the statement),
 *  falling back to the recorded type when no source was captured. */
function declText(e: IndexedLeanDecl): string {
  return (e.source ?? "").trim() || (e.statement ?? "").trim();
}

/** The decls a piece references. Prefers the index's recorded references —
 *  `proofRefs` counts too for a def, whose body is its statement — and falls
 *  back to tokenizing the text against index names when none were recorded. */
export function referencedDecls(index: DeclIndex, e: IndexedLeanDecl): IndexedLeanDecl[] {
  const named = [...(e.refs ?? []), ...(DEF_KINDS.has(e.kind) ? e.proofRefs ?? [] : [])];
  const names = named.length > 0
    ? named
    : [...new Set(declText(e).match(/[A-Za-z_][A-Za-z0-9_.'!?]*/g) ?? [])];
  const out: IndexedLeanDecl[] = [];
  const seen = new Set<string>();
  for (const n of names) {
    const hit = resolveIndexed(index, n);
    if (hit && hit.name !== e.name && !seen.has(hit.name)) {
      seen.add(hit.name);
      out.push(hit);
    }
  }
  return out;
}

/** A component label may name a theorem's binders rather than a decl. */
const seedDeclName = (label: string): string => label.replace(/^hypotheses of /, "").trim();

/**
 * The def-kind declarations reachable from a block's existing pieces by
 * statement reference, up to `maxDepth`, as further labelled pieces. Traversal
 * continues only through def-kind decls (a def's body is part of the formula
 * being explained); anything already shown, over the line cap, or beyond the
 * piece budget is skipped. Deterministic: depth, then file, then line.
 */
export function closurePieces(args: {
  seedNames: string[];
  index: DeclIndex;
  existing: LeanPiece[];
  maxDepth?: number;
  maxLines?: number;
  maxPieces?: number;
}): LeanPiece[] {
  const maxDepth = args.maxDepth ?? CLOSURE_DEPTH;
  const maxLines = args.maxLines ?? MAX_CLOSURE_PIECE_LINES;
  const already = new Set(args.existing.map((p) => shortName(p.part)));
  const shown = new Set(args.existing.map((p) => p.text.trim()));
  const found = new Map<string, { decl: IndexedLeanDecl; depth: number; text: string }>();
  const visited = new Set<string>();
  let frontier: IndexedLeanDecl[] = [];
  for (const label of args.seedNames) {
    const hit = resolveIndexed(args.index, seedDeclName(label));
    if (hit && !visited.has(hit.name)) {
      visited.add(hit.name);
      frontier.push(hit);
    }
  }
  for (let depth = 1; depth <= maxDepth && frontier.length > 0; depth++) {
    const next: IndexedLeanDecl[] = [];
    for (const node of frontier) {
      for (const ref of referencedDecls(args.index, node)) {
        if (visited.has(ref.name)) continue;
        visited.add(ref.name);
        if (!DEF_KINDS.has(ref.kind)) continue; // traverse only through definitions
        next.push(ref);
        const text = declText(ref);
        if (!text || already.has(shortName(ref.name)) || shown.has(text.trim())) continue;
        if (text.split("\n").length > maxLines) continue;
        found.set(ref.name, { decl: ref, depth, text });
      }
    }
    frontier = next;
  }
  return [...found.values()]
    .sort((a, b) =>
      (a.depth - b.depth) ||
      a.decl.file.localeCompare(b.decl.file) ||
      (a.decl.line - b.decl.line) ||
      a.decl.name.localeCompare(b.decl.name))
    .slice(0, args.maxPieces ?? MAX_CLOSURE_PIECES)
    .map((f) => ({ part: f.decl.name, label: f.decl.name, text: f.text }));
}

/** Load the run's declaration index, written earlier in P4 by `paper_index`.
 *  Absent or empty is a hard failure: the closure would silently degrade to
 *  "this block references nothing", which is exactly the blind spot it exists
 *  to close. */
export async function loadDeclIndex(outDir: string): Promise<DeclIndex> {
  const path = join(outDir, "paper_library_index.json");
  let raw: string;
  try {
    raw = await readFile(path, "utf8");
  } catch {
    throw new Error(
      `P4 nl-links: ${path} is missing; the Lean reference closure cannot be computed. ` +
        `Run the paper_index step (P4 emits it before this sub-step) and retry.`,
    );
  }
  const entries = (JSON.parse(raw) as { entries?: IndexedLeanDecl[] }).entries;
  if (!Array.isArray(entries) || entries.length === 0) {
    throw new Error(`P4 nl-links: ${path} lists no declarations; the Lean reference closure cannot be computed.`);
  }
  return buildDeclIndex(entries);
}

/** Everything the author call sees for one object: the snippet's own pieces
 *  plus its reference closure. */
export function leanPiecesWithClosure(snippet: LeanSnippet, index: DeclIndex): LeanPiece[] {
  const own = leanPieces(snippet);
  const seedNames = [snippet.decl, ...(snippet.components ?? []).map((c) => c.label)].filter(
    (n) => typeof n === "string" && n.length > 0 && n !== "(composite)",
  );
  return [...own, ...closurePieces({ seedNames, index, existing: own })];
}

// ---------------------------------------------------------------------------
// The artifact

const RowAssignment = z.object({
  row: z.string().min(1),
  segments: z.array(z.string().min(1)).optional(),
  unstated: z.literal(true).optional(),
});
/** One display's link to one declaration. A display that DEFINES several named
 *  quantities gets several entries — one per declaration — so the segment can
 *  light up each of them; a display nothing realizes gets exactly one
 *  `presentationOnly` entry. The two forms never mix for the same segment. */
const DisplayLink = z.object({
  segment: z.string().min(1),
  decl: z.string().min(1).optional(),
  presentationOnly: z.literal(true).optional(),
});
const SegmentSchema = z.object({
  id: z.string().min(1),
  kind: z.enum(["text", "display"]),
  start: z.number().int().nonnegative(),
  end: z.number().int().positive(),
  /** Elements open at `start`, outermost first — see nl_segments.ts. */
  openPath: z.array(z.string()),
});
const BlockView = z.object({
  /** sha256 of the EXACT block inner HTML these offsets index, unnormalized.
   *  The site must refuse to apply segments whose digest does not match the HTML
   *  it holds: offsets computed against other bytes would highlight the wrong
   *  text. This is the decisive check. */
  digest: z.string().min(1),
  /** Length of that same HTML in the offsets' own unit — a cheap pre-check
   *  before hashing, not a second guarantee. */
  byteLength: z.number().int().nonnegative(),
  /** Absent for a block with no statement telescope to structure. */
  structured: z.unknown().optional(),
  /** True when rowlessness is BY DESIGN (a non-Prop definition or a composite
   *  with no unique proposition): the site can say so rather than treating it
   *  as a gap. */
  rowless: z.literal(true).optional(),
  segments: z.array(SegmentSchema),
  /** ALWAYS present, possibly empty. A rowless block emits `assignments: []`
   *  and a block with no displays emits `displayLinks: []` — the consumer reads
   *  arrays unconditionally rather than guarding every access. */
  assignments: z.array(RowAssignment),
  displayLinks: z.array(DisplayLink),
});
export const NlLinks = z.object({
  commit: z.string(),
  qid: z.string(),
  spec: z.string(),
  policy: z.literal(NL_LINKS_POLICY),
  blocks: z.record(z.string(), BlockView),
});
export type NlLinks = z.infer<typeof NlLinks>;
export type RowAssignment = z.infer<typeof RowAssignment>;
export type DisplayLink = z.infer<typeof DisplayLink>;

// ---------------------------------------------------------------------------
// Per-block inputs — all computed before any model call

export interface BlockInput {
  objId: string;
  blockHtml: string;
  /** `rawDigest(blockHtml)` — binds the offsets to the exact bytes. */
  digest: string;
  /** `blockHtml.length` — a cheap pre-check in the offsets' own unit. */
  byteLength: number;
  pieces: LeanPiece[];
  segments: NlSegment[];
  structured: StructuredView | null;
  /** No statement telescope BY DESIGN (non-Prop definition or ambiguous composite). */
  rowless: boolean;
  rows: Array<{ id: string; kind: "hyp" | "conclusion"; code: string }>;
  /** The block's own labelled pieces — the candidates the prompt shows. NOT the
   *  validity test for a display link: a display may realize any declaration of
   *  the development, and the closure is only a 32-piece window onto it. */
  vocabulary: string[];
  /** The paper's whole declaration index — the vocabulary a display link is
   *  actually checked against. */
  index: DeclIndex;
  key: string;
}

/**
 * Resolve a display link's declaration to the FULLY-QUALIFIED name, or null.
 *
 * Stricter than `resolveIndexed`, deliberately. That helper falls back to the
 * short name whenever the last dotted component is unambiguous, which accepts
 * `Bogus.UniqueDecl` — a name whose own prefix contradicts the declaration it
 * resolves to. A producer that waves such a name through hands the consumer a
 * string its own resolver may reject, orphaning the token. So:
 *   - a bare name may use the short-name route, and is normalized;
 *   - a DOTTED name must be the real full name, or a genuine dotted suffix of
 *     it (`Loggap.cellPhi` for `CausalSmith.Stat.Loggap.cellPhi`). A prefix that
 *     contradicts the resolution is refused rather than silently corrected — it
 *     signals the model was confused about which declaration it meant.
 */
export function resolveDeclName(index: DeclIndex, decl: string): string | null {
  const exact = index.byName.get(decl);
  if (exact) return exact.name;
  if (!decl.includes(".")) {
    // bare short name: unambiguous-short resolution, normalized to the FQ name
    const hit = resolveIndexed(index, decl);
    return hit ? hit.name : null;
  }
  // Dotted input: a genuine dotted SUFFIX resolves iff exactly one declaration
  // carries it — independent of short-name uniqueness, so `B.foo` still
  // disambiguates two decls sharing the short name `foo`. A dotted input whose
  // suffix matches nothing (or several) is refused, never guessed.
  const suffix = `.${decl}`;
  const matches: string[] = [];
  for (const name of index.byName.keys()) {
    if (name.endsWith(suffix)) {
      matches.push(name);
      if (matches.length > 1) return null;
    }
  }
  return matches.length === 1 ? matches[0] : null;
}

/** Does this name identify a declaration of the paper's Lean development? */
export function declIsKnown(index: DeclIndex, decl: string): boolean {
  return resolveDeclName(index, decl) !== null;
}

/** Content key: block HTML, the enumerated rows and segments, and the Lean
 *  material. Packaging (which chunk a block lands in) is deliberately not part
 *  of it, so re-batching never re-bills. */
export function blockCacheKey(input: Omit<BlockInput, "key">): string {
  return hashEnvBody(
    [
      NL_LINKS_POLICY,
      ASSIGN_RULES_VERSION,
      `${rawDigest(input.blockHtml)}:${input.blockHtml.length}`,
      hashEnvBody(input.rows.map((r) => `${r.id} ${r.code}`).join("\n")),
      hashEnvBody(input.segments.map((s) => `${s.id} ${s.start} ${s.end}`).join("\n")),
      hashEnvBody(leanPromptText(input.pieces)),
    ].join("|"),
  );
}

/**
 * Is this statement a theorem-like one, i.e. does it HAVE a hypothesis/goal
 * telescope to structure? Read off the source's leading keyword, past any
 * docstring or attributes. Prop-valued definitions are recognized separately;
 * other definitions, non-Prop structures, abbreviations, and composites with
 * no identifiable proposition are rowless.
 */
export function isTheoremLike(statement: string): boolean {
  const head = statement
    .replace(/\/--[\s\S]*?-\/|\/-[\s\S]*?-\//g, " ")
    .replace(/@\[[^\]]*\]/g, " ")
    .trimStart();
  return /^(private\s+|protected\s+|nonrec\s+|noncomputable\s+)*(theorem|lemma)\b/.test(head);
}

/** True only for a definition with an explicitly Prop-valued body. */
export function isPropDefinition(statement: string): boolean {
  return scanPropDefinitionSignature(statement) !== null;
}

/** The proposition a block presents. Composite snippets have an empty own
 * statement, but often contain exactly one Prop-valued declaration plus
 * supporting data structures/abbreviations. In that unambiguous case the Prop
 * declaration is the block's logical statement and must receive the same
 * fine-grained treatment as a direct anchor. Multiple proposition components
 * stay rowless: choosing one would silently hide part of the composite claim. */
function propositionStatement(snippet: LeanSnippet): string {
  const own = snippet.statement ?? "";
  if (own.trim().length > 0) return own;
  const components = snippet.components ?? [];
  const propositionLike = (statement: string) =>
    isTheoremLike(statement) || isPropDefinition(statement) || isPropRecord(statement);
  // Composite producers put the principal declaration first. Prefer it when
  // it is proposition-bearing even if supporting components include other
  // Props (ExperimentClass followed by the IidSampling/Overlap it bundles).
  const first = components[0]?.statement ?? "";
  if (propositionLike(first)) return first;
  const candidates = components
    .map((component) => component.statement ?? "")
    .filter(propositionLike);
  return candidates.length === 1 ? candidates[0] : "";
}

/** Build one block's closed world. Returns null when the block has no Lean
 *  material or no segments — nothing to assign. */
export function buildBlockInput(args: {
  objId: string;
  blockHtml: string;
  snippet: LeanSnippet;
  index: DeclIndex;
}): BlockInput | null {
  const pieces = leanPiecesWithClosure(args.snippet, args.index);
  if (pieces.length === 0) return null;
  const segments = segmentBlock(args.blockHtml);
  if (segments.length === 0) return null;
  const problems = segmentationProblems(args.blockHtml, segments);
  if (problems.length > 0) {
    throw new Error(`P4 nl-links: ${args.objId} segmentation is not a partition: ${problems.join("; ")}`);
  }
  // Rowlessness is only acceptable when the statement has no proposition to
  // decompose. A theorem/lemma, explicit `: Prop :=` definition, or Prop-valued
  // record that fails to structure is a parser regression, never an excuse for
  // an opaque block.
  const statement = propositionStatement(args.snippet);
  const theoremLike = statement.trim().length > 0 && isTheoremLike(statement);
  const propositionLike = theoremLike || isPropDefinition(statement) || isPropRecord(statement);
  const structured = propositionLike
    ? structureStatementView(statement) ?? structurePropRecordView(statement)
    : null;
  if (propositionLike && structured === null) {
    throw new Error(
      `P4 nl-links: ${args.objId} is a theorem/lemma or Prop-valued declaration whose statement ` +
        `the structurer could not parse. ` +
        `That is a parser regression, not a rowless object — fix the structurer (or the statement) ` +
        `rather than shipping a proposition with no rows.`,
    );
  }
  const rows = structured ? assignRowIds(structured) : [];
  const partial: Omit<BlockInput, "key"> = {
    objId: args.objId,
    blockHtml: args.blockHtml,
    digest: rawDigest(args.blockHtml),
    byteLength: args.blockHtml.length,
    pieces,
    segments,
    structured,
    rowless: !propositionLike,
    rows,
    vocabulary: pieces.map((p) => p.label),
    index: args.index,
  };
  return { ...partial, key: blockCacheKey(partial) };
}

/** Chunk items by rendered size: sorted by obj_id, filled to the budget, an
 *  oversized item alone. Deterministic — the same inputs always chunk the same. */
export function chunkBySize<T extends { objId: string }>(
  items: T[],
  section: (t: T) => string,
  budget = CHUNK_CHARS,
  /** A second, non-byte budget — used to bound the ANSWER's size, which the
   *  payload's byte budget says nothing about. An item over the cap runs alone. */
  units?: { of: (t: T) => number; max: number },
): T[][] {
  const ordered = [...items].sort((a, b) => a.objId.localeCompare(b.objId));
  const chunks: T[][] = [];
  let current: T[] = [];
  let size = 0;
  let unitCount = 0;
  for (const item of ordered) {
    const cost = section(item).length;
    const itemUnits = units ? units.of(item) : 0;
    const overBytes = size + cost > budget;
    const overUnits = units !== undefined && unitCount + itemUnits > units.max;
    if (current.length > 0 && (overBytes || overUnits)) {
      chunks.push(current);
      current = [];
      size = 0;
      unitCount = 0;
    }
    current.push(item);
    size += cost;
    unitCount += itemUnits;
  }
  if (current.length > 0) chunks.push(current);
  return chunks;
}

/** Claims one block puts to the verifier: one per row, one per display. */
export const claimCount = (input: VerifyInput): number =>
  input.block.rows.length + input.block.segments.filter((s) => s.kind === "display").length;

// ---------------------------------------------------------------------------
// Pass 1 — assignment

/** One object's section of an assignment request. */
export function assignSection(input: BlockInput): string {
  const parts = [
    `### ${input.objId}`,
    "LEAN ROWS:",
    input.rows.map((r) => `${r.id} [${r.kind}] ${r.code.replace(/\n\s*/g, " ")}`).join("\n"),
    "PAPER SEGMENTS:",
    input.segments.map((s) => `${s.id} [${s.kind}] ${segmentText(input.blockHtml, s)}`).join("\n"),
  ];
  if (input.vocabulary.length > 0) {
    parts.push("DECLARATIONS:", leanPromptText(input.pieces));
  }
  return parts.join("\n");
}

const AssignReply = z.object({
  blocks: z.record(z.string(), z.object({
    assignments: z.array(RowAssignment),
    displayLinks: z.array(DisplayLink),
  })),
});

/** Rewrite every display link's decl to its resolved fully-qualified name, so
 *  the artifact never carries the input string. Applied to fresh answers, to
 *  cached ones, and to verifier corrections, so the invariant holds on replay
 *  as well as on a paid run. */
export function normalizeDisplayLinks(index: DeclIndex, links: DisplayLink[]): DisplayLink[] {
  return links.map((d) => {
    if (d.decl === undefined) return d;
    const resolved = resolveDeclName(index, d.decl);
    return resolved === null || resolved === d.decl ? d : { ...d, decl: resolved };
  });
}

/**
 * Drop a `presentationOnly` entry from a display that also names declarations.
 *
 * The two forms are contradictory, so a reply giving both is confused — but not
 * ambiguously so: `presentationOnly` asserts that NO declaration realizes the
 * display, and naming one already denies exactly that, so the declaration claim
 * subsumes the other. Coercing costs nothing in rigor — the verifier audits the
 * surviving claim as it audits any other, and can still overturn it to
 * presentation-only — and refusing instead throws away an otherwise complete
 * answer for the whole request. The artifact's XOR is unchanged; this only
 * decides which side of it a self-contradictory reply lands on. Every other
 * totality violation is still refused.
 */
export function coerceDisplayLinks(
  links: DisplayLink[],
): { links: DisplayLink[]; coerced: string[] } {
  const named = new Set(links.flatMap((d) => (d.decl !== undefined ? [d.segment] : [])));
  const coerced = [...new Set(links.flatMap((d) =>
    d.presentationOnly && named.has(d.segment) ? [d.segment] : []))].sort();
  if (coerced.length === 0) return { links, coerced };
  return {
    links: links.filter((d) => !(d.presentationOnly && named.has(d.segment))),
    coerced,
  };
}

/** Everything a reply must answer for one block, and nothing it may invent. */
export function assignmentProblems(input: BlockInput, reply: {
  assignments: RowAssignment[];
  displayLinks: DisplayLink[];
}): string[] {
  const problems: string[] = [];
  const rowIds = new Set(input.rows.map((r) => r.id));
  const segIds = new Set(input.segments.map((s) => s.id));
  const displayIds = new Set(input.segments.filter((s) => s.kind === "display").map((s) => s.id));
  const seenRows = new Set<string>();
  for (const a of reply.assignments) {
    if (!rowIds.has(a.row)) problems.push(`assignment names row ${a.row}, which is not a row of this block`);
    else if (seenRows.has(a.row)) problems.push(`row ${a.row} is answered more than once`);
    seenRows.add(a.row);
    const hasSegments = (a.segments?.length ?? 0) > 0;
    if (hasSegments === (a.unstated === true)) {
      problems.push(`row ${a.row} must name segments or be marked unstated, not both or neither`);
    }
    for (const s of a.segments ?? []) {
      if (!segIds.has(s)) problems.push(`row ${a.row} names segment ${s}, which is not a segment of this block`);
    }
  }
  const missingRows = [...rowIds].filter((r) => !seenRows.has(r));
  if (missingRows.length > 0) {
    problems.push(`${missingRows.length} row(s) unanswered: ${missingRows.slice(0, 12).join(", ")}`);
  }
  const entriesFor = new Map<string, DisplayLink[]>();
  for (const d of reply.displayLinks) {
    if (!displayIds.has(d.segment)) {
      problems.push(`displayLink names ${d.segment}, which is not a display segment of this block`);
      continue;
    }
    entriesFor.set(d.segment, [...(entriesFor.get(d.segment) ?? []), d]);
  }
  for (const [segId, entries] of entriesFor) {
    const declared: string[] = [];
    let presentationOnly = 0;
    for (const d of entries) {
      if ((d.decl !== undefined) === (d.presentationOnly === true)) {
        problems.push(
          `display ${segId} has an entry that neither names a declaration nor is marked presentation-only ` +
            `(or does both)`,
        );
        continue;
      }
      if (d.presentationOnly) {
        presentationOnly++;
        continue;
      }
      const resolved = resolveDeclName(input.index, d.decl!);
      if (resolved === null) {
        problems.push(
          `display ${segId} names declaration "${d.decl}", which no declaration of this paper's ` +
            `Lean development matches (checked paper_library_index.json; a short name shared by two ` +
            `declarations, or a qualified name whose prefix contradicts the declaration it would ` +
            `resolve to, is refused rather than guessed)`,
        );
        continue;
      }
      // Dedupe on the RESOLVED name: two spellings of one declaration are one link.
      if (declared.includes(resolved)) {
        problems.push(`display ${segId} names declaration "${resolved}" more than once`);
      } else declared.push(resolved);
    }
    if (presentationOnly > 0 && declared.length > 0) {
      problems.push(`display ${segId} is both linked to a declaration and marked presentation-only`);
    }
    if (presentationOnly > 1) problems.push(`display ${segId} is marked presentation-only more than once`);
  }
  const missingDisplays = [...displayIds].filter((d) => !entriesFor.has(d));
  if (missingDisplays.length > 0) {
    problems.push(`${missingDisplays.length} display(s) unanswered: ${missingDisplays.slice(0, 12).join(", ")}`);
  }
  return problems;
}

const CachedBlock = z.object({
  policy: z.literal(NL_LINKS_POLICY),
  key: z.string().min(1),
  complete: z.literal(true),
  assignments: z.array(RowAssignment),
  displayLinks: z.array(DisplayLink),
});

/** One batched assignment call. A reply that does not answer exactly this
 *  chunk's blocks, rows and displays throws; nothing from it is cached. */
export async function assignChunk(args: {
  chunk: BlockInput[];
  deps: CodexRunner;
  repoRoot: string;
}): Promise<Map<string, { assignments: RowAssignment[]; displayLinks: DisplayLink[]; coerced: string[] }>> {
  const ids = args.chunk.map((c) => c.objId);
  // One appendix per REQUEST, not per block: it is identical for every block of
  // a bundle, and keeping it out of the sections keeps it out of the cache keys.
  const appendix = declVocabularyAppendix(args.chunk[0].index);
  const payload = `${args.chunk.map(assignSection).join("\n\n")}\n\n${appendix}`;
  if (payload.length > MAX_PROMPT_BYTES) {
    throw new Error(
      `P4 nl-links: a request for ${ids.join(", ")} would send ${payload.length} bytes, over the ` +
        `${MAX_PROMPT_BYTES}-byte prompt ceiling. Split the block or shrink its Lean closure.`,
    );
  }
  const basePrompt = await presentationPrompt("p4_nl_links", { objects_payload: payload });
  let priorProblem = "";
  for (let attempt = 0; attempt < 2; attempt++) {
    const prompt = priorProblem === "" ? basePrompt :
      `${basePrompt}\n\nCORRECTION REQUIRED\n` +
      `Your previous JSON was rejected by the deterministic totality validator:\n${priorProblem}\n` +
      `Return the COMPLETE JSON answer again. Use only ids listed above; in particular, ` +
      `displayLinks may name only segments explicitly labeled [display].`;
    const res = await args.deps.runCodex({
      prompt,
      cwd: args.repoRoot,
      reasoningEffort: "medium",
      leanLsp: false,
    });
    try {
      const parsed = AssignReply.safeParse(parseJsonLoose(res.stdout));
      if (!parsed.success) {
        throw new Error(`P4 nl-links: the request for ${ids.join(", ")} returned invalid JSON: ${parsed.error.message}`);
      }
      const answered = new Set(Object.keys(parsed.data.blocks));
      const missing = ids.filter((id) => !answered.has(id));
      const extra = [...answered].filter((id) => !ids.includes(id));
      if (missing.length > 0 || extra.length > 0) {
        throw new Error(
          `P4 nl-links: the reply must answer exactly the objects asked about` +
            (missing.length > 0 ? `; unanswered: ${missing.slice(0, 8).join(", ")}` : "") +
            (extra.length > 0 ? `; not asked about: ${extra.slice(0, 8).join(", ")}` : "") +
            ". Not cached.",
        );
      }
      const out = new Map<string, { assignments: RowAssignment[]; displayLinks: DisplayLink[]; coerced: string[] }>();
      for (const input of args.chunk) {
        const raw = parsed.data.blocks[input.objId];
        const { links: displayLinks, coerced } = coerceDisplayLinks(raw.displayLinks);
        const block = { assignments: raw.assignments, displayLinks };
        const problems = assignmentProblems(input, block);
        if (problems.length > 0) {
          throw new Error(
            `P4 nl-links: ${input.objId}'s assignment is not total: ${problems.slice(0, 6).join("; ")}. Not cached.`,
          );
        }
        out.set(input.objId, {
          assignments: block.assignments,
          displayLinks: normalizeDisplayLinks(input.index, block.displayLinks),
          coerced,
        });
      }
      return out;
    } catch (error) {
      if (attempt === 1) throw error;
      priorProblem = error instanceof Error ? error.message : String(error);
    }
  }
  throw new Error(`P4 nl-links: assignment retry for ${ids.join(", ")} ended unexpectedly`);
}

// ---------------------------------------------------------------------------
// Pass 2 — verification
//
// The assignment pass answers a closed question, so it cannot produce a
// malformed span — but it can still be WRONG: a row pointed at the wrong
// sentence, or claimed unstated when the paper plainly states it. This pass
// audits every claim, including the negative ones, and a wrongly-claimed
// "unstated" is corrected in the same reply by naming the segments it should
// have had. That is why v3 needs no separate repair round.

export interface VerifyInput {
  objId: string;
  block: BlockInput;
  assignments: RowAssignment[];
  displayLinks: DisplayLink[];
}

/**
 * One object's section of a verification request: the block's FULL context
 * (segments, rows, declarations) and the claims this request asks about. A block
 * with more claims than one request can carry is split — the context repeats,
 * the claims do not.
 */
export function verifySectionFor(input: VerifyInput, asked?: ReadonlySet<string>): string {
  const seg = new Map(input.block.segments.map((s) => [s.id, s] as const));
  const show = (id: string) => {
    const s = seg.get(id);
    return s ? `${id}: ${segmentText(input.block.blockHtml, s)}` : id;
  };
  const flat = (code: string | undefined) => (code ?? "").replace(/\n\s*/g, " ");
  // Enumerated from the block, so every row and display is audited even if the
  // assignment under review somehow failed to mention one.
  const byRow = new Map(input.assignments.map((a) => [a.row, a] as const));
  const byDisplay = new Map<string, DisplayLink[]>();
  for (const d of input.displayLinks) byDisplay.set(d.segment, [...(byDisplay.get(d.segment) ?? []), d]);
  const wanted = (id: string) => asked === undefined || asked.has(id);
  const claims = [
    ...input.block.rows.filter((r) => wanted(r.id)).map((r) => {
      const a = byRow.get(r.id);
      if (!a) return `${r.id} (NO CLAIM RECORDED) — ${flat(r.code)}`;
      return a.unstated
        ? `${r.id} UNSTATED — ${flat(r.code)}`
        : `${r.id} -> ${(a.segments ?? []).join(", ")} — ${flat(r.code)}`;
    }),
    ...input.block.segments.filter((s) => s.kind === "display" && wanted(s.id)).map((s) => {
      const entries = byDisplay.get(s.id) ?? [];
      if (entries.length === 0) return `${s.id} (NO CLAIM RECORDED)`;
      if (entries.some((d) => d.presentationOnly)) return `${s.id} PRESENTATION-ONLY`;
      // The claim is the whole set: adding or dropping one declaration changes it.
      return `${s.id} -> ${entries.map((d) => d.decl).join(", ")}`;
    }),
  ];
  return [
    `### ${input.objId}`,
    "PAPER SEGMENTS:",
    input.block.segments.map((s) => show(s.id)).join("\n"),
    "LEAN ROWS:",
    input.block.rows.map((r) => `${r.id} [${r.kind}] ${flat(r.code)}`).join("\n"),
    "DECLARATIONS:",
    leanPromptText(input.block.pieces),
    "CLAIMS TO AUDIT:",
    claims.join("\n"),
  ].join("\n");
}

/** The whole block's section — also the text its cache key hashes, so this
 *  rendering must not change when a block is split across requests. */
export const verifySection = (input: VerifyInput): string => verifySectionFor(input);

/** One request's share of one block: its context plus a subset of its claims. */
export interface VerifyUnit {
  objId: string;
  input: VerifyInput;
  /** Claim ids (row ids and display segment ids) this request asks about. */
  claims: string[];
}

/**
 * Split one block into request-sized units. A block whose claims fit in one
 * request stays whole — the common case, and the one whose packing must not
 * change. A larger block is cut at claim-id order into consecutive groups, so
 * the split is deterministic and a re-run asks the same questions.
 */
export function verifyUnits(input: VerifyInput, max = MAX_VERIFY_CLAIMS): VerifyUnit[] {
  const all = chunkClaims([input]).map((c) => c.slice(input.objId.length + 1));
  if (all.length <= max) return [{ objId: input.objId, input, claims: all }];
  const units: VerifyUnit[] = [];
  for (let i = 0; i < all.length; i += max) {
    units.push({ objId: input.objId, input, claims: all.slice(i, i + max) });
  }
  return units;
}

const Verdict = z.object({
  obj_id: z.string().min(1),
  /** A row id or a display segment id — whichever claim this verdict is about. */
  claim: z.string().min(1),
  ok: z.boolean(),
  /** When `ok` is false: what it should be instead. */
  segments: z.array(z.string().min(1)).optional(),
  unstated: z.literal(true).optional(),
  /** The display's corrected declaration SET — the whole replacement, so a
   *  correction can add or drop declarations, not only swap one. */
  decls: z.array(z.string().min(1)).optional(),
  presentationOnly: z.literal(true).optional(),
});
const VerifyReply = z.object({ verdicts: z.array(Verdict) });
type Verdict = z.infer<typeof Verdict>;

const CachedVerify = z.object({
  policy: z.literal(NL_LINKS_POLICY),
  key: z.string().min(1),
  complete: z.literal(true),
  verdicts: z.array(Verdict),
});

/**
 * Every claim a chunk must have judged, derived from the BLOCK — its rows and
 * its display segments — never from the answer being audited. Deriving it from
 * the assignments would let an answer that omitted a row also escape review of
 * that row: the omission would define its own audit scope.
 */
export function chunkClaims(chunk: VerifyInput[]): string[] {
  return chunk.flatMap((v) => [
    ...v.block.rows.map((r) => `${v.objId} ${r.id}`),
    ...v.block.segments.filter((s) => s.kind === "display").map((s) => `${v.objId} ${s.id}`),
  ]);
}

/** The verdicts must tile the chunk's claims exactly, and every correction must
 *  name ids that exist. */
export function verifyProblems(chunk: VerifyInput[], verdicts: Verdict[]): string[] {
  return verifyUnitProblems(chunk.map((input) => ({
    objId: input.objId, input, claims: chunkClaims([input]).map((c) => c.slice(input.objId.length + 1)),
  })), verdicts);
}

/**
 * The same contract over the subset a request actually asked about: every asked
 * claim judged exactly once, nothing else judged, every correction naming ids
 * that exist. A split block's request is answerable on its own terms — it is
 * never held to claims it was not shown.
 */
export function verifyUnitProblems(units: VerifyUnit[], verdicts: Verdict[]): string[] {
  const expected = new Set(units.flatMap((u) => u.claims.map((c) => `${u.objId} ${c}`)));
  const byObj = new Map(units.map((u) => [u.objId, u.input] as const));
  const problems: string[] = [];
  const seen = new Set<string>();
  for (const v of verdicts) {
    const k = `${v.obj_id} ${v.claim}`;
    if (!expected.has(k)) {
      problems.push(`verdict for ${v.obj_id}/${v.claim}, which is not a claim in this request`);
      continue;
    }
    if (seen.has(k)) problems.push(`${v.obj_id}/${v.claim} is judged more than once`);
    seen.add(k);
    if (v.ok) continue;
    const block = byObj.get(v.obj_id)!.block;
    const isRow = block.rows.some((r) => r.id === v.claim);
    if (isRow) {
      const hasSegments = (v.segments?.length ?? 0) > 0;
      if (hasSegments === (v.unstated === true)) {
        problems.push(`correction for ${v.obj_id}/${v.claim} must name segments or mark it unstated`);
      }
      for (const s of v.segments ?? []) {
        if (!block.segments.some((x) => x.id === s)) {
          problems.push(`correction for ${v.obj_id}/${v.claim} names unknown segment ${s}`);
        }
      }
    } else {
      const hasDecls = (v.decls?.length ?? 0) > 0;
      if (hasDecls === (v.presentationOnly === true)) {
        problems.push(
          `correction for ${v.obj_id}/${v.claim} must give the declarations it should name, or mark ` +
            `it presentation-only`,
        );
      }
      const seenDecls: string[] = [];
      for (const decl of v.decls ?? []) {
        const resolved = resolveDeclName(block.index, decl);
        if (resolved === null) {
          problems.push(
            `correction for ${v.obj_id}/${v.claim} names declaration "${decl}", which no declaration ` +
              `of this paper's Lean development matches`,
          );
        } else if (seenDecls.includes(resolved)) {
          problems.push(`correction for ${v.obj_id}/${v.claim} names "${resolved}" more than once`);
        } else seenDecls.push(resolved);
      }
    }
  }
  const missing = [...expected].filter((k) => !seen.has(k));
  if (missing.length > 0) {
    problems.push(
      `${missing.length} claim(s) unjudged: ${missing.slice(0, 8).map((m) => m.replace(" ", "/")).join(", ")}`,
    );
  }
  return problems;
}

/** Apply the verdicts, replacing every corrected claim in place. */
export function applyVerdicts(
  input: VerifyInput,
  verdicts: Verdict[],
): { assignments: RowAssignment[]; displayLinks: DisplayLink[]; corrections: number } {
  const fq = (decl: string) => resolveDeclName(input.block.index, decl) ?? decl;
  const byClaim = new Map(verdicts.filter((v) => v.obj_id === input.objId).map((v) => [v.claim, v] as const));
  let corrections = 0;
  const assignments = input.assignments.map((a) => {
    const v = byClaim.get(a.row);
    if (!v || v.ok) return a;
    corrections++;
    return v.unstated ? { row: a.row, unstated: true as const } : { row: a.row, segments: v.segments ?? [] };
  });
  // A display's entries are replaced as a set, so one verdict rewrites all of
  // them at once — dropping a declaration is as expressible as adding one.
  const displayLinks: DisplayLink[] = [];
  const rewritten = new Set<string>();
  for (const d of input.displayLinks) {
    const v = byClaim.get(d.segment);
    if (!v || v.ok) {
      displayLinks.push(d);
      continue;
    }
    if (rewritten.has(d.segment)) continue; // already replaced by this verdict
    rewritten.add(d.segment);
    corrections++;
    if (v.presentationOnly) displayLinks.push({ segment: d.segment, presentationOnly: true as const });
    else for (const decl of v.decls ?? []) displayLinks.push({ segment: d.segment, decl: fq(decl) });
  }
  return { assignments, displayLinks, corrections };
}

/** A verify receipt's key: the audit question for ONE block. Deliberately not a
 *  chunk hash — chunking is packaging, and keying on it made one changed block
 *  re-key every block it happened to be batched with, and made a shifted chunk
 *  boundary re-key the neighbours too. */
export function verifyCacheKey(input: VerifyInput): string {
  return hashEnvBody(`${NL_LINKS_POLICY}|verify|${verifySection(input)}`);
}

/** The same input with a verdict already applied — the state a correction leaves
 *  behind, and therefore the question the NEXT run will ask. */
function corrected(input: VerifyInput, applied: { assignments: RowAssignment[]; displayLinks: DisplayLink[] }): VerifyInput {
  return { ...input, assignments: applied.assignments, displayLinks: applied.displayLinks };
}

/** All-ok verdicts for a block's claims — what the verifier has just told us
 *  about the state it corrected TO. */
function allOk(input: VerifyInput): Verdict[] {
  return chunkClaims([input]).map((c) => ({ obj_id: input.objId, claim: c.slice(input.objId.length + 1), ok: true }));
}

export async function verifyChunks(args: {
  inputs: VerifyInput[];
  cachePath: string;
  deps: CodexRunner;
  repoRoot: string;
}): Promise<{
  results: Map<string, { assignments: RowAssignment[]; displayLinks: DisplayLink[] }>;
  corrections: number;
  calls: number;
}> {
  const cache = await loadPairCache(args.cachePath);
  const results = new Map<string, { assignments: RowAssignment[]; displayLinks: DisplayLink[] }>();
  const live = new Set<string>();
  const verdictsFor = new Map<string, Verdict[]>();
  let corrections = 0;
  let calls = 0;

  // Per-block cache read. A receipt is honoured only if it still answers this
  // block's claims exactly (the same re-validation the assignment cache does).
  const misses: VerifyInput[] = [];
  for (const input of args.inputs) {
    const key = verifyCacheKey(input);
    live.add(key);
    const cached = CachedVerify.safeParse(cache[key]);
    if (cached.success && cached.data.key === key && verifyProblems([input], cached.data.verdicts).length === 0) {
      verdictsFor.set(input.objId, cached.data.verdicts);
    } else {
      delete cache[key];
      misses.push(input);
    }
  }

  // Requests are packed from UNITS, not blocks: a block with more claims than one
  // reply can carry is split, its context repeated in each request. Packing
  // still prefers whole blocks — only an over-cap block is ever cut.
  //
  // The appendix is a constant per request and is deliberately NOT charged
  // against the per-block budget: subtracting it would shrink the block content
  // of every request and multiply the request count (measured: 3x) to no
  // purpose, since the ceiling that actually matters is MAX_PROMPT_BYTES and the
  // whole request stays far inside it.
  const units = misses.flatMap((input) => verifyUnits(input));
  const judged = new Map<string, Verdict[]>();
  for (const chunk of chunkBySize(units, (u) => verifySectionFor(u.input, new Set(u.claims)), CHUNK_CHARS, {
    of: (u) => u.claims.length, max: MAX_VERIFY_CLAIMS,
  })) {
    const payload = `${chunk.map((u) => verifySectionFor(u.input, new Set(u.claims))).join("\n\n")}\n\n` +
      declVocabularyAppendix(chunk[0].input.block.index);
    const res = await args.deps.runCodex({
      prompt: await presentationPrompt("p4_nl_links_verify", { claims_payload: payload }),
      cwd: args.repoRoot,
      reasoningEffort: "medium",
      leanLsp: false,
      model: MODELS.codexPresentation,
    });
    calls++;
    const parsed = VerifyReply.safeParse(parseJsonLoose(res.stdout));
    if (!parsed.success) {
      throw new Error(
        `P4 nl-links verification returned invalid JSON for ` +
          `${[...new Set(chunk.map((u) => u.objId))].join(", ")}: ${parsed.error.message}`,
      );
    }
    const problems = verifyUnitProblems(chunk, parsed.data.verdicts);
    if (problems.length > 0) {
      throw new Error(
        `P4 nl-links verification did not judge every claim exactly once ` +
          `(${[...new Set(chunk.map((u) => u.objId))].join(", ")}): ${problems.slice(0, 6).join("; ")}. Not cached.`,
      );
    }
    for (const v of parsed.data.verdicts) judged.set(v.obj_id, [...(judged.get(v.obj_id) ?? []), v]);
    // A receipt is written only for a block whose EVERY claim has now been
    // judged. A block still missing a request caches nothing, so an interrupted
    // run re-asks only the requests it never got — never the whole block, and
    // never a half-audited block presented as complete.
    for (const objId of new Set(chunk.map((u) => u.objId))) {
      const input = misses.find((m) => m.objId === objId)!;
      const own = judged.get(objId) ?? [];
      if (verifyProblems([input], own).length > 0) continue;
      const key = verifyCacheKey(input);
      cache[key] = { policy: NL_LINKS_POLICY, key, complete: true, verdicts: own };
    }
    await writeJsonAtomic(args.cachePath, cache); // persist after each PAID request
  }
  for (const [objId, own] of judged) verdictsFor.set(objId, own);

  for (const input of args.inputs) {
    const applied = applyVerdicts(input, verdictsFor.get(input.objId) ?? []);
    corrections += applied.corrections;
    results.set(input.objId, { assignments: applied.assignments, displayLinks: applied.displayLinks });
    if (applied.corrections === 0) continue;
    // SETTLE. A correction rewrites the assignment, so the next run asks a
    // DIFFERENT question about this block and would pay to re-audit the
    // verifier's own answer. Record that answer as already-verified: the
    // corrected values are what the verifier just said they should be, so
    // re-asking it adds nothing. Without this every correction costs a call on
    // every subsequent run (observed live: 3 chunks re-billed, then 2 more).
    const settled = corrected(input, applied);
    const settledKey = verifyCacheKey(settled);
    live.add(settledKey);
    cache[settledKey] = {
      policy: NL_LINKS_POLICY, key: settledKey, complete: true, verdicts: allOk(settled),
    };
    // The pre-correction receipt answers a question no later run will ask — the
    // assignment it audited has just been rewritten — so it is dropped in the
    // SAME run. Otherwise the next run prunes it and the caches differ between
    // two runs that did no work, which is indistinguishable from real churn.
    const rawKey = verifyCacheKey(input);
    if (rawKey !== settledKey) {
      live.delete(rawKey);
      delete cache[rawKey];
    }
  }

  // Payload-keyed entries are dead weight once their question changes; pruned
  // only after every block is settled, so an interrupted run discards nothing.
  for (const key of Object.keys(cache)) if (!live.has(key)) delete cache[key];
  await writeJsonAtomic(args.cachePath, cache);
  return { results, corrections, calls };
}

// ---------------------------------------------------------------------------
// Stage entry point

export interface NlLinkSelectable {
  obj_id: string;
  env: string;
  status: string;
}

/**
 * Segment, assign, verify, and write `nl_links.json` plus the two caches into
 * `outDir`. A codex/transport failure fails the stage loudly; a block whose Lean
 * statement will not parse still ships its segments (the site falls back to the
 * unstructured rendering) rather than blocking the emit.
 */
export async function ensureNlLinks(args: {
  outDir: string;
  repoRoot: string;
  commit: string;
  qid: string;
  spec: string;
  entries: NlLinkSelectable[];
  snippets: Record<string, LeanSnippet>;
  paperBodyHtml: string;
  deps: CodexRunner;
  log?: (message: string) => void;
}): Promise<{
  artifact: NlLinks;
  blocks: number;
  rows: number;
  segments: number;
  unstated: number;
  corrections: number;
  /** Self-contradictory display answers straightened out rather than refused. */
  coercions: number;
  unstructured: string[];
  summary: string;
}> {
  const cachePath = join(args.outDir, NL_LINKS_CACHE);
  const cache = await loadPairCache(cachePath);
  let indexPromise: Promise<DeclIndex> | null = null;
  const declIndex = (): Promise<DeclIndex> => (indexPromise ??= loadDeclIndex(args.outDir));

  // Pass 0 — free: build every block's closed world and settle cache hits.
  const inputs = new Map<string, BlockInput>();
  const ready = new Map<string, { assignments: RowAssignment[]; displayLinks: DisplayLink[] }>();
  const misses: BlockInput[] = [];
  const unstructured: string[] = [];
  let coercions = 0;
  for (const entry of args.entries) {
    if (!selectsForNlLinks(entry)) continue;
    const snippet = args.snippets[entry.obj_id];
    if (!snippet) continue;
    const blockHtml = extractBlockHtml(args.paperBodyHtml, entry.obj_id);
    if (blockHtml === null || blockHtml.trim().length === 0) continue;
    const input = buildBlockInput({ objId: entry.obj_id, blockHtml, snippet, index: await declIndex() });
    if (!input) continue;
    inputs.set(entry.obj_id, input);
    if (input.rowless) unstructured.push(entry.obj_id);
    const cached = CachedBlock.safeParse(cache[entry.obj_id]);
    if (cached.success && cached.data.key === input.key) {
      // A receipt is honoured only if it still SATISFIES the contract. The key
      // proves the inputs are unchanged, not that the stored answer was ever
      // total — a receipt written before a validator gained a rule, or edited by
      // hand, would otherwise replay a hole for ever.
      const stale = assignmentProblems(input, cached.data);
      if (stale.length === 0) {
        ready.set(entry.obj_id, {
          assignments: cached.data.assignments,
          displayLinks: normalizeDisplayLinks(input.index, cached.data.displayLinks),
        });
        continue;
      }
      console.warn(
        `P4 nl-links: discarding ${entry.obj_id}'s cached assignment — it no longer satisfies the ` +
          `totality contract (${stale.slice(0, 3).join("; ")}); re-asking.`,
      );
    }
    delete cache[entry.obj_id];
    // Nothing to ask about: no rows to assign and no displays to link.
    if (input.rows.length === 0 && !input.segments.some((s) => s.kind === "display")) {
      ready.set(entry.obj_id, { assignments: [], displayLinks: [] });
      cache[entry.obj_id] = {
        policy: NL_LINKS_POLICY, key: input.key, complete: true, assignments: [], displayLinks: [],
      };
      continue;
    }
    misses.push(input);
  }
  await writeJsonAtomic(cachePath, cache);

  // Pass 1 — paid: one assignment request per chunk of missing blocks.
  for (const chunk of chunkBySize(misses, assignSection)) {
    const assigned = await assignChunk({ chunk, deps: args.deps, repoRoot: args.repoRoot });
    for (const input of chunk) {
      const block = assigned.get(input.objId)!;
      for (const segment of block.coerced) {
        coercions++;
        const line =
          `P4 nl-links: ${input.objId} display ${segment} was given both a declaration link and ` +
          `presentation-only; kept the declaration link (naming a declaration already denies that ` +
          `none realizes the display).`;
        console.warn(line);
        args.log?.(line);
      }
      ready.set(input.objId, { assignments: block.assignments, displayLinks: block.displayLinks });
      cache[input.objId] = {
        policy: NL_LINKS_POLICY, key: input.key, complete: true,
        assignments: block.assignments, displayLinks: block.displayLinks,
      };
    }
    await writeJsonAtomic(cachePath, cache);
  }

  // Pass 2 — paid: audit every claim, correcting in place.
  const verifyInputs: VerifyInput[] = [];
  for (const [objId, input] of inputs) {
    const block = ready.get(objId);
    if (!block || (block.assignments.length === 0 && block.displayLinks.length === 0)) continue;
    verifyInputs.push({ objId, block: input, assignments: block.assignments, displayLinks: block.displayLinks });
  }
  let corrections = 0;
  if (verifyInputs.length > 0) {
    const verified = await verifyChunks({
      inputs: verifyInputs,
      cachePath: join(args.outDir, NL_LINKS_VERIFY_CACHE),
      deps: args.deps,
      repoRoot: args.repoRoot,
    });
    corrections = verified.corrections;
    // The corrected assignment is what ships, so it is what the cache must hold.
    for (const [objId, block] of verified.results) {
      ready.set(objId, block);
      const input = inputs.get(objId)!;
      cache[objId] = {
        policy: NL_LINKS_POLICY, key: input.key, complete: true,
        assignments: block.assignments, displayLinks: block.displayLinks,
      };
    }
    await writeJsonAtomic(cachePath, cache);
  }

  const blocksOut: Record<string, unknown> = {};
  let rows = 0;
  let segments = 0;
  let unstatedRows = 0;
  for (const [objId, input] of inputs) {
    const block = ready.get(objId) ?? { assignments: [], displayLinks: [] };
    rows += input.rows.length;
    segments += input.segments.length;
    unstatedRows += block.assignments.filter((a) => a.unstated).length;
    blocksOut[objId] = {
      digest: input.digest,
      byteLength: input.byteLength,
      ...(input.structured ? { structured: input.structured } : {}),
      ...(input.rowless ? { rowless: true as const } : {}),
      segments: input.segments,
      assignments: block.assignments,
      displayLinks: block.displayLinks,
    };
  }
  const artifact = NlLinks.parse({
    commit: args.commit, qid: args.qid, spec: args.spec, policy: NL_LINKS_POLICY, blocks: blocksOut,
  });
  await writeJsonAtomic(join(args.outDir, NL_LINKS_ARTIFACT), artifact);
  if (unstructured.length > 0) {
    args.log?.(
      `P4 nl-links: ${unstructured.length} block(s) are rowless by design ` +
        `(non-Prop definition or composite with no unique proposition): ${unstructured.slice(0, 8).join(", ")}`,
    );
  }
  return {
    artifact,
    blocks: inputs.size,
    rows,
    segments,
    unstated: unstatedRows,
    corrections,
    coercions,
    unstructured,
    summary:
      `P4 nl-links: ${inputs.size} block(s), ${rows} Lean row(s) over ${segments} paper segment(s), ` +
      `${unstatedRows} row(s) unstated in the prose, ${corrections} claim(s) corrected by review, ` +
      `${coercions} contradictory display answer(s) coerced, ${unstructured.length} block(s) rowless by design.`,
  };
}
