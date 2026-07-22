// F2.5 tex↔Lean crosswalk: deterministic anchor skeleton + reviewer-verdict
// merge + drift→finding folding. Design: code owns anchors (LLMs are unreliable
// at line numbers, which the future paper↔Lean click-to-jump view needs); the
// codex reviewer owns only the semantic drift verdict, keyed by obj_id. Mirrors
// the "code routes, reviewer tags" + deterministic-floor pattern already in
// stage2_5.ts. At F2.5 (default mode) it covers definitions (P-blocks → Lean
// def/structure) and theorem statements (T-blocks); LEMMAS ARE EXCLUDED — they
// churn in F3 so their names / anchors are unstable there, whereas defs and
// theorem statements are frozen by the F2.5 PASS gate and are the stable-named
// set worth gating. At F5 (full mode, `includeLemmas`) the proofs are filled and
// the lemma set is final, so `buildCompleteCrosswalk` ALSO anchors L-block lemmas
// / propositions and re-stamps line numbers from the final files — the complete
// tex↔Lean correspondence backbone for the visualization (descriptive, not a
// gate: F3 restructuring makes paper↔Lean lemmas many-to-many).

import { mkdir, writeFile } from "node:fs/promises";
import path from "node:path";
import type { CrosswalkEntry, CrosswalkVerdict } from "../types.js";
import type { ReviewResult } from "../judgment.js";
import { isUndeliveredNode, type FormalizationGraph } from "../graph/types.js";
import {
  parseMdBlocks,
  type CrosswalkOpts,
  type LeanDecl,
  parseLeanDecls,
  isCanonicalHeadline,
  parseAllDecls,
} from "./crosswalk_parse.js";
import { findHiddenStatementDefs, type HiddenDefFlavor } from "./crosswalk_semantics.js";

export * from "./crosswalk_parse.js";
export * from "./crosswalk_semantics.js";

/** Verdicts that pass (no drift). Everything else in the vocabulary blocks. */
const PASSING_VERDICTS = new Set<CrosswalkVerdict>(["exact", "equivalent", "unmatched"]);

/** Verdicts that ASSERT the paper object was verified to MATCH a Lean decl. A
 *  `lean: null` anchor under one of these is contradictory — equivalence/exactness
 *  verified against nothing — the cheap invariant that catches a stale or
 *  disconnected anchor (`unmatched` is the honest verdict for a genuinely
 *  unanchored paper object, so it is NOT in this set). */
export const VERIFIED_MATCH_VERDICTS = new Set<CrosswalkVerdict>(["exact", "equivalent"]);

/** Self-consistency lint: entries whose verdict claims a verified Lean match but
 *  carry no anchor. A consumer's equivalence gate SKIPS `lean: null` rows, so such
 *  a row silently opts out of verification while asserting it passed. */
export function crosswalkVerifiedWithoutAnchor(entries: CrosswalkEntry[]): CrosswalkEntry[] {
  return entries.filter((e) => e.lean == null && VERIFIED_MATCH_VERDICTS.has(e.verdict));
}

/** One obj_id whose Lean anchor changed between a prior table and a fresh rescan. */
export interface AnchorDrift {
  obj_id: string;
  priorDecl: string | null;
  freshDecl: string | null;
  verdict: CrosswalkVerdict;
}

/** Anchor drift between a prior table (whose verdicts were assigned against ITS
 *  anchors) and a freshly-scanned skeleton of the SAME, now-restructured Lean. A
 *  row whose Lean decl changed (gained / lost / retargeted) has a verdict that is
 *  no longer verified against its current anchor. obj_ids absent from `fresh` are
 *  paper-only (legitimately unanchored) and are not compared. */
export function anchorDriftFindings(
  prior: CrosswalkEntry[],
  fresh: CrosswalkEntry[],
): AnchorDrift[] {
  const freshByObj = new Map(fresh.map((e) => [e.obj_id, e.lean?.decl ?? null]));
  const out: AnchorDrift[] = [];
  for (const p of prior) {
    if (!freshByObj.has(p.obj_id)) continue;
    const priorDecl = p.lean?.decl ?? null;
    const freshDecl = freshByObj.get(p.obj_id) ?? null;
    if (priorDecl !== freshDecl) out.push({ obj_id: p.obj_id, priorDecl, freshDecl, verdict: p.verdict });
  }
  return out;
}

/** A verdict the codex reviewer assigns, keyed by obj_id. Anchors NOT included. */
export interface ReviewerCrosswalkVerdict {
  obj_id: string;
  verdict: CrosswalkVerdict;
  clauses?: { src: string; lean: string; v: CrosswalkVerdict }[];
  note?: string;
  fix_locus?: "lean-scaffold" | "nl-plan" | "math-source";
}


// ---------------------------------------------------------------------------
// Skeleton build (anchors only — no verdicts)
// ---------------------------------------------------------------------------

/**
 * Build the deterministic crosswalk skeleton: one entry per paper object (union
 * of .md P-/T- blocks and Lean decls carrying an obj_id), matched by obj_id.
 * Every field EXCEPT verdict/clauses/note/fix_locus is filled here; verdict is
 * left `unmatched` for the reviewer. A .md block with no Lean decl gets
 * `lean: null`; a Lean decl whose obj_id has no .md block gets empty `tex`.
 */
export async function buildCrosswalkSkeleton(
  leanDir: string,
  mdPath: string,
  opts: CrosswalkOpts = {},
): Promise<CrosswalkEntry[]> {
  const allMd = await parseMdBlocks(mdPath);
  // Default (F2.5) mode excludes lemmas — they churn in F3. Full (F5) mode keeps
  // them: by then the proofs are filled and the lemma set is final.
  const mdBlocks = opts.includeLemmas
    ? allMd
    : allMd.filter((b) => b.kind !== "lemma" && b.kind !== "proposition");
  const leanDecls = await parseLeanDecls(leanDir, opts);
  const leanByObjId = new Map<string, LeanDecl>();
  for (const d of leanDecls) {
    if (!d.objId) continue;
    const cur = leanByObjId.get(d.objId);
    // Prefer the canonical headline decl `t<n>_thm` over a same-prefixed helper /
    // bridge / aggregate (`t1_thm_bridge`, `t1_thm_random_aggregate_from_pieces`,
    // `t5_geometry`) that ALSO derives the T-obj_id from its `t<n>_` name. Without
    // this, an earlier-in-file helper shadows the real headline in the crosswalk
    // and the paper would verify the wrong decl. First-wins for non-theorem
    // obj_ids (P-/L-) and when no canonical headline is present.
    if (!cur) leanByObjId.set(d.objId, d);
    else if (isCanonicalHeadline(d.objId, d.name) && !isCanonicalHeadline(d.objId, cur.name))
      leanByObjId.set(d.objId, d);
  }
  const entries: CrosswalkEntry[] = [];
  const seen = new Set<string>();
  for (const b of mdBlocks) {
    seen.add(b.objId);
    const d = leanByObjId.get(b.objId);
    entries.push({
      obj_id: b.objId,
      kind: b.kind,
      title: b.title,
      tex: { label: b.texLabel, line_range: b.texLineRange },
      lean: d ? { file: d.file, decl: d.name, decl_kind: d.declKind, line: d.line } : null,
      verdict: "unmatched",
    });
  }
  // Lean decls with an obj_id that has no matching .md block (possible fabricated
  // block or a stale id) — surface them so the reviewer can flag or dismiss.
  for (const d of leanDecls) {
    if (!d.objId || seen.has(d.objId)) continue;
    seen.add(d.objId);
    entries.push({
      obj_id: d.objId,
      kind: d.declKind === "theorem" ? "theorem" : "definition",
      title: `(Lean-only: ${d.name})`,
      tex: { label: "", line_range: "" },
      lean: { file: d.file, decl: d.name, decl_kind: d.declKind, line: d.line },
      verdict: "unmatched",
    });
  }
  // Hidden-statement-def augmentation: build-inline Prop-valued / ∃-real-constant
  // defs reached from a T-block STATEMENT but carrying no obj_id are invisible to
  // BOTH the obj_id skeleton (no P-row) and the per-hypothesis matrix (not a named
  // hypothesis), so any dropped/weakened clause inside them makes Lean certify a
  // different statement than the paper. Surface each as its own row so check K is
  // forced to unfold and compare it. Applies in both F2.5 (gate) and F5
  // (descriptive) modes.
  const hidden = await findHiddenStatementDefs(leanDir);
  for (const m of hidden) {
    if (entries.some((e) => e.lean?.decl === m.name)) continue; // already represented
    entries.push({
      obj_id: `AUX-${m.name}`,
      kind: "definition",
      title: `Build-inline ${HIDDEN_FLAVOR_BLURB[m.flavor]}; reached from ${m.reachedFrom.join(", ")} (check K)`,
      tex: { label: "", line_range: "" },
      lean: { file: m.file, decl: m.name, decl_kind: m.kind, line: m.line },
      verdict: "unmatched",
    });
  }
  return sortCrosswalkEntries(entries);
}

/** Per-flavor reviewer instruction for an `AUX-` hidden-def row. */
const HIDDEN_FLAVOR_BLURB: Record<HiddenDefFlavor, string> = {
  "const-exist":
    "∃-real-constant membership predicate — audit uniform-constant laundering on the converse",
  structure:
    "assumption-bundle structure — verify every field matches its .tex condition (no dropped or weakened field)",
  predicate:
    "inline predicate / assumption — verify it faithfully encodes its .tex condition (no dropped or weakened clause)",
  quantity:
    "ℝ-valued computational quantity — verify the formula (rate exponent / estimand / threshold) matches the paper exactly (no altered constant, exponent, or sign)",
};

/**
 * The F2.5 check-K reviewer instruction (skeleton + how to fill per-obj_id
 * verdicts, incl. the AUX hidden-def rows). Shared by the live stage and the
 * `scripts/dev` review probe so the probe is faithful and the wording never
 * drifts between them. `scopePrefix` carries the optional incremental
 * re-review block.
 */
export function crosswalkReviewInstruction(skeleton: CrosswalkEntry[], scopePrefix = ""): string {
  return (
    scopePrefix +
    "Review Lean scaffold against NL and TeX.\n\n" +
    "=== CROSSWALK SKELETON (check K — fill verdicts ONLY, keyed by obj_id) ===\n" +
    "The objects below were extracted deterministically (obj_id, Lean file:decl, .tex anchor). " +
    "Do NOT invent obj_ids or anchors. Per check K, for each `definition`/`assumption` row unfold " +
    "the Lean decl body and compare clause-by-clause to the .md signature + .tex; return a top-level " +
    "`crosswalk` array of `{obj_id, verdict, clauses?, note?, fix_locus?}` covering these obj_ids.\n" +
    "Rows with an `AUX-` obj_id are build-inline defs / structures (no .tex/.md anchor) reached from the " +
    "listed T-block's STATEMENT — inline predicates, membership classes, or assumption-bundle structures " +
    "(whose FIELDS are conditions) that hide from both the P-row crosswalk and the hypothesis matrix. " +
    "UNFOLD each and verify it faithfully encodes the .tex condition it stands for: any dropped, weakened, " +
    "strengthened (over-assumed), or quantifier-swapped clause/field makes Lean certify a different " +
    "statement than the paper. For the subset whose title flags `uniform-constant laundering` " +
    "(it `∃`-quantifies real constants), also decide whether, used inside its parent converse / lower-bound " +
    "theorem, the per-law `∃`-constant membership silently weakens a stated uniform-over-class claim " +
    "(witness free to carry n-dependent / blowing-up constants) — `exact`/`equivalent` only if the class is " +
    "fixed-constant or carries an explicit n-independence clause. Otherwise give a drift verdict " +
    "(e.g. `weaker-in-Lean`) with `fix_locus`.\n" +
    JSON.stringify(skeleton, null, 2)
  );
}

/** Stable crosswalk order: P-blocks, then T-blocks, then L-blocks, then AUX
 *  hidden-def rows; numeric within a kind, lexical for AUX. */
export function sortCrosswalkEntries(entries: CrosswalkEntry[]): CrosswalkEntry[] {
  const rank = (id: string) => {
    const m = id.match(/^([PTL])-(\d+)([a-z]?)$/);
    if (m) {
      const kindRank = m[1] === "P" ? 0 : m[1] === "T" ? 1 : 2;
      return [kindRank, Number(m[2]), m[3]] as const;
    }
    if (id.startsWith("AUX-")) return [3, 0, id] as const;
    return [9, 0, ""] as const;
  };
  return [...entries].sort((a, b) => {
    const ra = rank(a.obj_id);
    const rb = rank(b.obj_id);
    return ra[0] - rb[0] || ra[1] - rb[1] || ra[2].localeCompare(rb[2]);
  });
}

/**
 * F5 COMPLETE crosswalk: the full tex↔Lean correspondence backbone for the
 * visualization. Runs on the final proof-review-loop files, so the Lean
 * is final and lemma names are stable. Builds the lemma-inclusive skeleton (this
 * RE-STAMPS every `(file, line)` from the final files — the deferred F2.5
 * re-stamp), then carries the F2.5 def/assumption/theorem drift verdicts forward
 * from the PASS snapshot so the gated rows keep their adjudicated verdict while
 * the anchors are refreshed. Lemma / proposition rows stay DESCRIPTIVE (verdict
 * `unmatched`; a `lean: null` row is a paper object with no Lean counterpart, a
 * Lean-only entry is a lemma the proof introduced that the paper does not name) —
 * F3 restructuring makes paper↔Lean lemmas many-to-many, so this is information
 * for the viz, never a gate.
 */
export async function buildCompleteCrosswalk(
  leanDir: string,
  mdPath: string,
  f25Snapshot: CrosswalkEntry[] | undefined,
): Promise<CrosswalkEntry[]> {
  const full = await buildCrosswalkSkeleton(leanDir, mdPath, { includeLemmas: true });
  const prior = new Map((f25Snapshot ?? []).map((e) => [e.obj_id, e]));
  return full.map((e) => {
    const p = prior.get(e.obj_id);
    if (!p) return e; // lemma / newly-seen rows: descriptive, no carried verdict
    // The F2.5 verdict was assigned against the F2.5 anchor. If F3 restructuring
    // (de-laundering) RETARGETED the anchor (gained / lost / changed decl), that
    // verdict is no longer verified against the CURRENT decl — inheriting a
    // verified-match verdict (`exact`/`equivalent`) onto a fresh anchor would
    // launder it (the bug that let P-8 ship `equivalent` against a decl it was
    // never checked against). Refresh the anchor regardless, but withhold the
    // unverified verdict: downgrade to `unmatched` with a provenance note.
    const anchorChanged = (p.lean?.decl ?? null) !== (e.lean?.decl ?? null);
    if (anchorChanged && VERIFIED_MATCH_VERDICTS.has(p.verdict)) {
      return {
        ...e,
        verdict: "unmatched" as CrosswalkVerdict,
        note:
          `anchor drifted since F2.5 (${p.lean?.decl ?? "null"} → ${e.lean?.decl ?? "null"}); ` +
          `the F2.5 '${p.verdict}' verdict was not re-verified against the new decl`,
      };
    }
    // Keep the FRESH anchor + line (re-stamp) from `full`; inherit the F2.5
    // adjudicated verdict / clauses / note / fix_locus.
    return {
      ...e,
      verdict: p.verdict,
      clauses: p.clauses ?? e.clauses,
      note: p.note ?? e.note,
      fix_locus: p.fix_locus ?? e.fix_locus,
    };
  });
}

const GRAPH_DECL_KIND: Record<string, string> = {
  definition: "def",
  assumption: "structure",
  theorem: "theorem",
  lemma: "lemma",
};

/**
 * Build the complete crosswalk directly from the (core-keyed) formalization graph —
 * the plan-driven replacement for `buildCompleteCrosswalk(leanDir, mdPath, …)`. The
 * graph already carries every paper object (NL statement, Lean link from F2/F3
 * extraction, review verdict) and a causalsmith-compatible `obj_id` alias, so F5 no
 * longer parses the `.md`. One row per content node (definition / assumption /
 * theorem / lemma); setup and gate nodes are not crosswalk rows.
 */
export async function buildCompleteCrosswalkFromGraph(graph: FormalizationGraph, leanDir?: string): Promise<CrosswalkEntry[]> {
  const out: CrosswalkEntry[] = [];
  const declLines = new Map<string, number>();
  const shortCount = new Map<string, number>(); // how many decls share a short name within one file
  if (leanDir) {
    for (const d of await parseAllDecls(leanDir)) {
      declLines.set(`${d.file}\0${d.name}`, d.line);
      // why: count by the SHORT (last `.`-segment) name — parseAllDecls may record a decl either short
      // (`same_thm`, inside a namespace block) or dotted (`B.same_thm`), so keying the ambiguity count
      // by the raw name would miss that both share the short name and wrongly treat it as unique.
      const dShort = d.name.includes(".") ? d.name.slice(d.name.lastIndexOf(".") + 1) : d.name;
      const sk = `${d.file}\0${dShort}`;
      shortCount.set(sk, (shortCount.get(sk) ?? 0) + 1);
    }
  }
  const leanAnchor = (file: string, decl: string, declKind: string): NonNullable<CrosswalkEntry["lean"]> | null => {
    // why: graph extraction stores namespaced decls as FULLY-QUALIFIED names (`Foo.t1_thm`) while
    // `parseAllDecls` indexes the SHORT name — real CausalSmith files use namespaces, so fall back to
    // the short name (last `.` segment) so a real local decl still gets its numeric anchor. Use the
    // fallback ONLY when the short name is UNIQUE in that file: an ambiguous short name (two namespaces
    // defining the same short decl in one file) must downgrade to unresolved, not bind to a wrong line.
    const short = decl.includes(".") ? decl.slice(decl.lastIndexOf(".") + 1) : decl;
    const line =
      declLines.get(`${file}\0${decl}`) ??
      (shortCount.get(`${file}\0${short}`) === 1 ? declLines.get(`${file}\0${short}`) : undefined);
    if (line === undefined) return null; // crosswalk lean.line is numeric; unresolved anchors downgrade rather than persist null.
    return {
      file,
      decl,
      decl_kind: declKind,
      line,
    };
  };
  for (const n of graph.nodes) {
    if (!(n.kind === "definition" || n.kind === "assumption" || n.kind === "theorem" || n.kind === "lemma")) continue;
    if (isUndeliveredNode(n)) continue;
    const objId = n.obj_id ?? n.id;
    const title = (n.nl?.statement ?? "").replace(/\s+/g, " ").trim().slice(0, 80) || objId;
    const lean =
      n.lean?.decl_name && n.lean.file !== null
        // why: `file:null` marks plan-reuse/library decls, not checked run-local declarations.
        ? leanAnchor(n.lean.file ?? "Basic.lean", n.lean.decl_name, GRAPH_DECL_KIND[n.kind] ?? "def")
        : null;
    // A row with NO Lean anchor cannot be a VERIFIED match — a `matched` review on an unanchored node
    // (e.g. an agent-introduced assumption standing in for an inline hypothesis like `hε`/`hz0`) was
    // "verified against nothing". Only an anchored node may be `equivalent`; otherwise it is
    // `unmatched` (a real `drift` is preserved). Keeps the crosswalk from ever claiming equivalence
    // against a `lean:null` anchor — the exact contradiction the F5 consistency gate rejects.
    const verdict: CrosswalkVerdict =
      n.review?.status === "drift"
        ? "drift"
        : (n.review?.status === "matched" || n.review?.status === "derived") && lean != null
          ? "equivalent"
          : "unmatched";
    out.push({
      obj_id: objId,
      kind: n.kind,
      title,
      tex: { label: objId, line_range: n.nl?.tex_anchor ?? "" },
      lean,
      verdict,
    });
  }
  return sortCrosswalkEntries(out);
}

// ---------------------------------------------------------------------------
// Verdict merge + rendering + finding fold
// ---------------------------------------------------------------------------

/** Merge reviewer verdicts (keyed by obj_id) into the skeleton. Anchors are
 *  never overwritten; only verdict/clauses/note/fix_locus are taken from the
 *  reviewer. Reviewer entries with no matching skeleton obj_id are ignored
 *  (code owns the entry set). */
export function mergeCrosswalkVerdicts(
  skeleton: CrosswalkEntry[],
  verdicts: ReviewerCrosswalkVerdict[] | undefined,
): CrosswalkEntry[] {
  if (!verdicts || verdicts.length === 0) return skeleton;
  const byId = new Map(verdicts.map((v) => [v.obj_id, v]));
  return skeleton.map((e) => {
    const v = byId.get(e.obj_id);
    if (!v) return e;
    return {
      ...e,
      verdict: v.verdict ?? e.verdict,
      clauses: v.clauses ?? e.clauses,
      note: v.note ?? e.note,
      fix_locus: v.fix_locus ?? e.fix_locus,
    };
  });
}

/**
 * Split the fresh skeleton into rows that must be re-audited by codex (`stale`)
 * vs rows whose verdict can be REUSED from the last F2.5 PASS snapshot (`cached`).
 *
 * SOUND coarse rule (mirrors the freeze floor's snapshot, no graph trust needed):
 *  - If there is no prior snapshot, or ANY def/abbrev/structure changed
 *    (`defsUnchanged === false`), everything is stale — a changed definition can
 *    shift an unchanged theorem's meaning, so re-audit all.
 *  - Otherwise a row is reusable iff the prior snapshot has its obj_id, its .tex
 *    anchor is unchanged, AND: for a THEOREM row, its own decl-body hash is
 *    unchanged (`thmHashUnchanged`); for a def/abbrev/structure row, nothing more
 *    is needed (no def changed, by `defsUnchanged`).
 * Cached rows keep their FRESH anchors (line numbers may have shifted) with the
 * prior verdict/clauses/note spliced in.
 */
export function splitCrosswalkByCache(
  skeleton: CrosswalkEntry[],
  prior: CrosswalkEntry[] | undefined,
  defsUnchanged: boolean,
  thmHashUnchanged: (declName: string) => boolean,
): { stale: CrosswalkEntry[]; cached: CrosswalkEntry[] } {
  if (!prior || prior.length === 0 || !defsUnchanged) return { stale: skeleton, cached: [] };
  const priorById = new Map(prior.map((e) => [e.obj_id, e]));
  const stale: CrosswalkEntry[] = [];
  const cached: CrosswalkEntry[] = [];
  for (const e of skeleton) {
    const p = priorById.get(e.obj_id);
    const anchorSame =
      !!p && p.tex.label === e.tex.label && p.tex.line_range === e.tex.line_range;
    const isThm = e.lean?.decl_kind === "theorem";
    const reusable =
      !!p && anchorSame && (isThm ? !!e.lean && thmHashUnchanged(e.lean.decl) : true);
    if (reusable && p) {
      cached.push({
        ...e,
        verdict: p.verdict,
        clauses: p.clauses ?? e.clauses,
        note: p.note ?? e.note,
        fix_locus: p.fix_locus ?? e.fix_locus,
      });
    } else {
      stale.push(e);
    }
  }
  return { stale, cached };
}

/** Human-readable rendering of the crosswalk (sibling of the JSON backbone). */
export function renderCrosswalkMd(entries: CrosswalkEntry[]): string {
  const lines: string[] = [
    "# tex↔Lean crosswalk",
    "",
    "Definition/assumption/theorem (and, in the F5 complete table, lemma)",
    "correspondence. Durable anchors: `obj_id` (.md/.tex side) and `(file, decl)`",
    "(Lean side). Line numbers are convenience and re-derivable.",
    "",
    "**Guarantee boundary (read this).** The Lean column is machine-verified at the",
    "STATEMENT level: a sorry-free theorem/lemma certifies its *statement* is true.",
    "The `.tex` PROOFS are NOT Lean-verified at the proof level — they are human",
    "narratives refereed once at D0.5 and reconciled to the Lean *statements* by",
    "the proof-review loop. A `.tex` proof step can therefore be wrong while the (true) statement",
    "is Lean-certified; where the two disagree, the Lean proof is the ground truth.",
    "",
    "| obj_id | kind | Lean (file:decl) | .tex anchor | verdict | note |",
    "|---|---|---|---|---|---|",
  ];
  for (const e of entries) {
    const lean = e.lean ? `${e.lean.file}:${e.lean.decl} (L${e.lean.line})` : "(none)";
    const tex = e.tex.label || e.tex.line_range || "(none)";
    lines.push(
      `| ${e.obj_id} | ${e.kind} | \`${lean}\` | ${tex} | ${e.verdict} | ${(e.note ?? "").replace(/\|/g, "\\|")} |`,
    );
  }
  // Per-definition clause breakdowns (only where the reviewer supplied them).
  for (const e of entries) {
    if (!e.clauses || e.clauses.length === 0) continue;
    lines.push("", `### ${e.obj_id} clause matrix`, "", "| .md clause | Lean | verdict |", "|---|---|---|");
    for (const c of e.clauses) {
      lines.push(`| ${c.src.replace(/\|/g, "\\|")} | ${c.lean.replace(/\|/g, "\\|")} | ${c.v} |`);
    }
  }
  return lines.join("\n") + "\n";
}

/** Persist the merged crosswalk: JSON backbone (future view reads this) + the
 *  human-readable .md rendering. Written on EVERY F2.5 outcome. */
export async function persistCrosswalk(
  jsonPath: string,
  mdPath: string,
  entries: CrosswalkEntry[],
): Promise<void> {
  await mkdir(path.dirname(jsonPath), { recursive: true });
  await writeFile(jsonPath, JSON.stringify(entries, null, 2) + "\n", "utf8");
  await writeFile(mdPath, renderCrosswalkMd(entries), "utf8");
}

/** Blocking crosswalk entries (drift verdict that is not exact/equivalent and
 *  not the un-verdicted placeholder). */
export function blockingCrosswalkEntries(entries: CrosswalkEntry[]): CrosswalkEntry[] {
  return entries.filter((e) => !PASSING_VERDICTS.has(e.verdict));
}

/**
 * Fold crosswalk drift into the F2.5 ReviewResult so the existing classification
 * + `fixLocusRouteFromReview` machinery routes it — no new routing logic. A
 * blocking def/assumption/theorem drift becomes a class-S finding tagged with the
 * reviewer's fix_locus. On a `reject` the findings are appended (so the
 * intervention judge sees them); on pass/revise the verdict becomes `revise`.
 * Returns the review unchanged when nothing blocks.
 */
export function foldCrosswalkIntoReview(
  review: ReviewResult,
  entries: CrosswalkEntry[],
): ReviewResult {
  const blocking = blockingCrosswalkEntries(entries);
  if (blocking.length === 0) return review;
  const findings = blocking.map((e) => ({
    label: e.lean ? `${e.lean.file}:${e.lean.decl}` : e.obj_id,
    verdict: "FLAG-K",
    one_line:
      `Crosswalk drift [${e.obj_id} ${e.kind}]: ${e.verdict}. ` +
      (e.note ?? `Lean encoding diverges from the .tex/.md definition; re-align ${e.obj_id}.`),
    fix_locus: e.fix_locus ?? ("lean-scaffold" as const),
  }));
  console.warn(
    `[causalsmith] Stage 2.5 crosswalk: ${blocking.length} definition/assumption drift finding(s) ` +
      `(${blocking.map((e) => `${e.obj_id}:${e.verdict}`).join(", ")}).`,
  );
  if (review.status === "reject") {
    return {
      ...review,
      perItemFindings: [...review.perItemFindings, ...findings],
      verbatim_critique:
        `${review.verbatim_critique}\n\n` +
        `Stage 2.5 crosswalk drift (appended): ${findings.map((f) => `[${f.label}] ${f.one_line}`).join(" ")}`,
    };
  }
  const priorFindings = review.status === "revise" ? review.perItemFindings : [];
  const priorCritique = review.status === "revise" ? review.verbatim_critique : "";
  return {
    status: "revise",
    classification: "S",
    perItemFindings: [...priorFindings, ...findings],
    verbatim_critique:
      (priorCritique ? `${priorCritique}\n\n` : "") +
      `Stage 2.5 crosswalk: ${blocking.length} definition/assumption drift finding(s). ` +
      `The Lean encoding of these paper objects diverges from the .tex/.md definition — ` +
      `re-align each (or route upstream if the .md/.tex itself is wrong, per fix_locus). ` +
      findings.map((f) => `[${f.label}] ${f.one_line}`).join(" "),
  };
}
