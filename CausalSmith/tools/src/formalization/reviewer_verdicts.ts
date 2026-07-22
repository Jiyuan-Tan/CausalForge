import type { CitedReviewReceipt, CrosswalkEntry, CrosswalkVerdict, DeliveryReviewReceipt } from "../types.js";
import type { SubstrateGate } from "../judgment.js";
import type { FormalizationGraph } from "../graph/types.js";

/**
 * Normalize a reviewer-supplied object id without shredding TeX symbol ids.
 * Ordinary graph ids never contain whitespace and reviewers occasionally append a declaration
 * name after them. Symbol ids legitimately contain TeX spaces and commas (`\mathcal H`,
 * `I_0,I_1`, `\mathsf R`), so they must be preserved verbatim.
 */
export function normalizeReviewerObjId(raw: unknown, expectedIds: Iterable<string> = []): string {
  const id = String(raw ?? "").trim();
  // Prefer an exact known id, then the longest known prefix followed by reviewer-added prose.
  // Longest-first prevents a short symbol name from capturing a longer one.
  const expected = [...expectedIds].sort((a, b) => b.length - a.length);
  const known = expected.find((candidate) =>
    id === candidate || id.startsWith(candidate + " ") || id.startsWith(candidate + ":"));
  if (known) return known;
  return id.startsWith("sym:") ? id : id.split(/\s+/)[0];
}

/** Concurrency-limited `map` preserving input order (results[i] ↔ items[i]). Local to keep the
 *  formalization layer independent of causalsmith's `gates.ts` copy. */
export async function mapLimit<T, R>(items: T[], limit: number, fn: (item: T, i: number) => Promise<R>): Promise<R[]> {
  const results = new Array<R>(items.length);
  let next = 0;
  const workers = Array.from({ length: Math.max(1, Math.min(limit, items.length)) }, async () => {
    for (;;) {
      const i = next++;
      if (i >= items.length) return;
      results[i] = await fn(items[i], i);
    }
  });
  await Promise.all(workers);
  return results;
}

interface StatementVerdict { obj_id: string; verdict: "matched" | "drift"; note?: string }
interface AssumptionVerdict {
  obj_id: string;
  verdict: "faithful-refinement" | "regularity-bookkeeping" | "substrate-gate" | "content-gate";
  note?: string;
}
export interface ReviewerOutput {
  status?: "ok" | "flagged";
  statement_verdicts?: StatementVerdict[];
  assumption_verdicts?: AssumptionVerdict[];
  substrate_gates?: SubstrateGate[];
  escalate?: { kind: string; obj_id?: string; reason: string; witness?: unknown } | null;
}

/** A concrete obstruction proving the STATEMENT (not the proof effort) is wrong — the gate that
 *  licenses an F3→D0 rewind. A `counterexample` exhibits a model satisfying the hypotheses where the
 *  conclusion fails; `hyps-insufficient` shows the stated hypotheses don't pin the conclusion;
 *  `hyps-contradictory` shows they're jointly unsatisfiable (vacuous). Absent a witness a
 *  `statement-wrong` escalation stays local (`fix-source`) — a filler that merely gave up has none,
 *  so it can never reach discovery. */
export type StatementWitness = {
  type: "counterexample" | "hyps-insufficient" | "hyps-contradictory";
  detail: string;
};
/** Where a flagged statement defect's fault lives (the reviewer classifies; the loop routes). */
export type ReviewerEscalation = { kind: string; obj_id?: string; reason: string; witness?: StatementWitness };

export interface ReviewerResult {
  graph: FormalizationGraph;
  ok: boolean;
  escalate: ReviewerEscalation | null;
  blocking: string[]; // obj_ids flagged drift / content-gate (incl. setup/env-structure decls)
  /** Per-target reviewer diagnosis for every `blocking` obj_id (the drift verdict's `note`). The
   *  loop forwards these verbatim into the F2 re-scaffold directive so the scaffolder gets the
   *  reviewer's SPECIFIC fix ("should be eventual / ∀ᶠ n", "constant must be uniform", …) instead
   *  of a generic "make it match the note" — the difference between a targeted fix and blind retries.
   *  Optional: absent (or empty) means the reviewer supplied no per-target diagnosis for this round. */
  driftNotes?: Record<string, string>;
  substrateGates: SubstrateGate[];
  /** One receipt per undelivered node and independent F4 reviewer. */
  deliveryReviewReceipts?: DeliveryReviewReceipt[];
  /** One source-and-locator-bound receipt per delivered cited node and F4 reviewer. */
  citedReviewReceipts?: CitedReviewReceipt[];
}

/** Tolerantly normalize the model's `escalate` object — capture `kind`/`obj_id`/`reason`
 *  even when the model uses a synonym key (`route`/`detail`/`note`/`id`), so the loop's
 *  routing and the surfaced reason are never silently dropped (the prior `reason: undefined`
 *  bug that made escalations log as `{status, route}` with no explanation). */
function normalizeEscalate(raw: unknown): ReviewerEscalation | null {
  // The model sometimes emits `escalate` as an ARRAY (e.g. [{target, reason}, …], one per flagged
  // target). Only surface it as a routing escalation if SOME item carries a recognized `kind`;
  // a kind-less array is just redundant with the drift verdicts already in `blocking`, so we
  // return null and let the loop route those to F2 revise — instead of HALTING on a manufactured
  // `unadjudicable` (proof_review_loop routes a non-scaffold-mismatch escalate to the orchestrator).
  if (Array.isArray(raw)) {
    for (const item of raw) {
      const norm = normalizeEscalate(item);
      if (norm && norm.kind && norm.kind !== "unadjudicable") return norm;
    }
    return null;
  }
  if (!raw || typeof raw !== "object") return null;
  const e = raw as Record<string, unknown>;
  const kindRaw = e.kind ?? e.route ?? e.type;
  const reason = String(e.reason ?? e.detail ?? e.note ?? e.message ?? "").trim();
  const objId = e.obj_id ?? e.id ?? e.object ?? e.target;
  // A contentless escalate object (no kind AND no reason — e.g. the model emits `escalate: {}`
  // or a stray empty object) is NOT a real escalation. Manufacturing an `unadjudicable` from it
  // spuriously halts a loop whose targets all matched — treat it as null.
  if (kindRaw == null && !reason) return null;
  const kind = String(kindRaw ?? "unadjudicable").trim();
  const witness = normalizeWitness(e.witness);
  return { kind, reason, ...(objId ? { obj_id: String(objId) } : {}), ...(witness ? { witness } : {}) };
}

/** Parse the model's `witness` object; drop it unless BOTH a recognized type and a non-empty detail
 *  are present — a witness with no concrete obstruction is not a witness and must not unlock D0. */
function normalizeWitness(raw: unknown): StatementWitness | null {
  if (!raw || typeof raw !== "object") return null;
  const w = raw as Record<string, unknown>;
  const type = String(w.type ?? w.kind ?? "").trim();
  const detail = String(w.detail ?? w.reason ?? w.note ?? "").trim();
  if (!detail) return null;
  if (type !== "counterexample" && type !== "hyps-insufficient" && type !== "hyps-contradictory") return null;
  return { type, detail };
}

export function parseJsonObject(stdout: string): ReviewerOutput {
  const fenced = stdout.replace(/```(?:json)?/gi, "");
  // Robust extraction: a reviewer (esp. the Claude/opus convergence model with Read/Grep) often
  // emits PROSE around the JSON — analysis text that itself contains `{`/`}` (set-builder, code,
  // a second object). The naive first-`{`…last-`}` slice then grabs a brace inside the prose and
  // `JSON.parse` fails at position 1. Instead, scan (string-aware, so braces inside string literals
  // are ignored) for every BALANCED top-level `{…}` object, then return the LARGEST one that parses
  // to an object — the verdict object dwarfs any incidental prose brace.
  const candidates: string[] = [];
  let depth = 0, startIdx = -1, inStr = false, esc = false;
  for (let i = 0; i < fenced.length; i++) {
    const c = fenced[i];
    if (inStr) {
      if (esc) esc = false;
      else if (c === "\\") esc = true;
      else if (c === '"') inStr = false;
      continue;
    }
    if (c === '"') inStr = true;
    else if (c === "{") { if (depth === 0) startIdx = i; depth++; }
    else if (c === "}") {
      if (depth > 0) { depth--; if (depth === 0 && startIdx >= 0) { candidates.push(fenced.slice(startIdx, i + 1)); startIdx = -1; } }
    }
  }
  candidates.sort((a, b) => b.length - a.length);
  const hasReviewerShape = (o: Record<string, unknown>): boolean => {
    const status = o.status;
    // why: copied core/plan blobs often carry `status`; require a reviewer-owned key to select JSON.
    return ["statement_verdicts", "assumption_verdicts", "substrate_gates", "escalate"].some((k) => k in o)
      && (status === undefined || status === "ok" || status === "flagged");
  };
  for (const cand of candidates) {
    try {
      const o = JSON.parse(cand);
      // Prefer the actual verdict object; copied source/plan JSON without reviewer keys is unsafe.
      if (o && typeof o === "object" && !Array.isArray(o) && hasReviewerShape(o as Record<string, unknown>)) return o as ReviewerOutput;
    } catch { /* try the next candidate */ }
  }
  throw new Error("reviewer: no parseable ReviewerOutput JSON object in output");
}

const minimalRow = (obj_id: string, verdict: CrosswalkVerdict, note?: string): CrosswalkEntry => ({
  obj_id,
  kind: "theorem",
  title: "",
  tex: { label: "", line_range: "" },
  lean: null,
  verdict,
  ...(note ? { note } : {}),
});

/** The reviewer sometimes returns *_verdicts as a keyed object
 * ({ "P-1:decl": {verdict, observations} } or { "P-8 triangularClass": "faithful: …" })
 * instead of the documented array. Coerce both shapes to an array of verdict records,
 * recovering obj_id from the key (leading token before the first ':' or space) when it
 * isn't a field, and wrapping a bare-string value as { verdict }. Without this, `.map`
 * (or a spread) throws and the whole loop dies on an otherwise-valid review. */
/** Verdict tokens, NEGATIVE (failure) checked before POSITIVE so "mostly faithful, but a drift in X"
 *  grades as drift. Used to recover a verdict from a free-prose sentence. */
// NEGATIVE (failure) signals — a small, STABLE vocabulary (the reviewer is consistent about how it
// names a problem). POSITIVE is unbounded (it invents "aligned"/"factored_equivalent"/"sound"/…), so
// we enumerate positives broadly; an UNRECOGNIZED verdict still defaults to drift for statements
// (faithfulness-safe — flag, never silently pass).
const NEG_VERDICTS = ["content-gate", "contentgate", "content gate", "derived", "drift", "drifted", "drifting", "partial",
  "vacuous", "crux", "weaker", "weakened", "over-claim", "overclaim", "over-state", "overstate",
  "overstates", "mismatch", "gerrymander", "laundered", "narrower", "not equivalent", "not faithful",
  "unmatched", "not matched", "unfaithful", "non-faithful", "incorrect", "invalid", "unsound",
  "inconsistent", "not correct", "not valid", "not sound", "not consistent", "not ok"];
const POS_VERDICTS = ["faithful-refinement", "faithful", "regularity-bookkeeping", "substrate-gate",
  "matched", "match", "equivalent", "exact", "correct", "pass", "ok", "aligned", "consistent", "sound",
  "accurate", "preserved", "concordant", "captures", "encodes", "agrees", "holds", "valid", "fine",
  // `untagged` is a SETUP-symbol TAGGING GAP (no @realizes tag to grade), not a proven drift — treat
  // as non-blocking so a missing tag does not reroute; the note still surfaces it for tagging.
  "untagged", "tagging-gap", "tagging gap"];
const OBJ_ID_RE = /^\s*\(?\*{0,2}\s*([A-Za-z]{1,3}-?\d+[A-Za-z0-9]*)\b/;

const escapeRegExp = (s: string): string => s.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
const containsVerdictPhrase = (text: string, phrase: string): boolean =>
  new RegExp(`(?:^|[^a-z0-9])${escapeRegExp(phrase)}(?:$|[^a-z0-9])`, "i").test(text);
const positiveRoot = "(?:faithful|match(?:ed)?|equivalent|exact|correct|pass|ok|align(?:ed)?|consistent|sound|accurate|preserved|concordant|valid|fine)";
// Failure/negation cues that GOVERN a positive root. A reviewer rejects equivalence in prose far
// more often than with a listed NEG token, and every such phrasing ("fails to match", "cannot
// match", "no match") CONTAINS a positive root — so without this the positive scan below reads an
// explicit rejection as a pass. Matching is deliberately cue→root (not a bare cue anywhere in the
// head), so an incidental "no"/"not" in an explanation cannot flip a genuine verdict.
const NEGATION_CUE =
  "(?:not|never|no|cannot|can[''`]?t|won[''`]?t|does\\s*n[''`]?t|did\\s*n[''`]?t|is\\s*n[''`]?t|" +
  "are\\s*n[''`]?t|fails?|failed|failing|unable|lacks?|lacking|missing|absent|without)";
// Up to two intervening tokens so "fails TO match" / "not exactly equivalent" are caught. The
// window biases toward FAIL on an ambiguous head — the deliberate direction for this classifier,
// whose contract is "flag, never silently pass".
const GENERIC_NEGATION_RE = new RegExp(
  `\\b${NEGATION_CUE}\\b(?:\\s+[a-z0-9_-]+){0,2}\\s+${positiveRoot}\\b`,
  "i",
);
const NEGATIVE_PREFIX_RE =
  /\b(?:mis|in|un|non)[-]?(?:align(?:ed)?|accurate|exact|correct|valid|sound|consistent|faithful|match(?:ed)?|preserved|equivalent)\b/i;
const CONTRAST_NEGATIVE_RE =
  /\b(?:drift(?:s|ed|ing)?|mismatch(?:es|ed|ing)?|overclaim(?:s|ed|ing)?|weaken(?:s|ed|ing)?|conditionaliz(?:e|es|ed|ing)|partial(?:ly)?|incorrect|invalid|unsound|inconsistent|wrong)\b/i;

/**
 * HEDGED positives — a real positive token that is QUALIFIED rather than negated, so no negation
 * cue fires. Observed live: `A-6: mostly faithful with an important gate/strengthening caveat`
 * (whose own body then reports "a substantive closure/gate issue"), and `aligned_with_caveat`.
 * A qualified approval is not an approval; grade it `unknown`, which is fail-closed at every
 * call site. `caveat` is matched unanchored so the `aligned_with_caveat` token form is caught
 * (`_` is a word character, so \b would not fire there).
 */
const HEDGE_RE =
  /\b(?:mostly|largely|broadly|essentially|substantially|nearly|almost|partially|partly|roughly|somewhat|arguably|approximately|virtually|modulo|except|excepting|barring|provided|assuming|if|unless)\b|caveat|\b(?:aside|apart|save)\s+(?:from|for)\b/i;

/**
 * The verdict's leading clause: everything before the first `.`/`;`, capped at 12 words. Wider
 * than the 3-word head (so `faithful with a caveat` is caught) but still short of the
 * explanation, so `faithful; uses the derived consequence` stays a clean pass.
 */
const leadClause = (text: string): string =>
  text.split(/[.;]/)[0].trim().split(/\s+/).slice(0, 12).join(" ");

// Shared negative-first classifier: unknown/non-faithful verdict tokens must never merge to pass.
export const verdictClass = (raw: unknown): "pass" | "fail" | "unknown" => {
  const text = String(raw ?? "").toLowerCase();
  // The verdict is the leading clause. Do not let words in its explanation (for example,
  // "faithful; uses the derived consequence") flip the result. A contrastive clause is the one
  // exception: "faithful, but drifted" must fail.
  const head = text.split(/\s+/).slice(0, 3).join(" ");
  if (GENERIC_NEGATION_RE.test(head) || NEGATIVE_PREFIX_RE.test(head)) return "fail";
  if (NEG_VERDICTS.some((t) => containsVerdictPhrase(head, t))) return "fail";
  const contrast = text.match(/\b(?:but|however|yet)\b([\s\S]*)$/)?.[1] ?? "";
  if (GENERIC_NEGATION_RE.test(contrast) || NEGATIVE_PREFIX_RE.test(contrast) || CONTRAST_NEGATIVE_RE.test(contrast)
      || NEG_VERDICTS.some((t) => containsVerdictPhrase(contrast, t))) return "fail";
  // A QUALIFIED positive is not a pass. Checked before the positive scan, since these verdicts
  // open with a genuine positive token and qualify it rather than negating it.
  if (HEDGE_RE.test(leadClause(text))) return "unknown";
  if (POS_VERDICTS.some((t) => containsVerdictPhrase(head, t))) return "pass";
  return "unknown";
};

// Setup-world symbol-space shape tests (shared by the symbol-cluster review AND the pre-review
// "is there a symbol to check?" gate, so a settled node graph never "covers" an untagged symbol).
const isRangeSpace = (sp: string) => /[{[(]\s*-?\s*[0-9]/.test(sp);
const isProductSpace = (sp: string) => / x |[×⨯]/.test(sp);
/** A core symbol is IN-SCOPE for the cluster review iff it has a range-shaped, non-product space and is
 *  not a `role:"derived"` schedule sequence — mirrors the filter in the symbol-cluster builder. */
export const symbolInScope = (s: { name?: string; space?: string; type?: string; role?: string }): boolean => {
  const sp = s.space || s.type;
  return !!(s.name && sp && s.role !== "derived" && isRangeSpace(sp) && !isProductSpace(sp));
};

/** Parse a bare-string verdict like "A-1: faithful. <explanation>" or "L-11 — partial drift: …" into
 *  a {obj_id, verdict, note} record. The reviewer sometimes returns *_verdicts as an array of such
 *  prose strings instead of objects; without this they have no `obj_id` field and get dropped (the
 *  loop then spins re-reviewing the same nodes because their verdict is never recorded). */
function parseStringVerdict(s: string, expectedIds: Iterable<string> = []): Record<string, unknown> {
  const expected = normalizeReviewerObjId(s, expectedIds);
  const knownPrefix = [...expectedIds].includes(expected) ? expected : null;
  const symbolMatch = s.match(/^\s*(sym:\\\(.*?\\\))\s*(?::|[\-–—])\s*/);
  const idm = knownPrefix ? null : s.match(OBJ_ID_RE);
  const objId = knownPrefix ?? symbolMatch?.[1] ?? idm?.[1];
  if (!objId) return { verdict: s };
  const consumed = knownPrefix
    ? s.indexOf(knownPrefix) + knownPrefix.length
    : symbolMatch
      ? symbolMatch[0].length
      : idm![0].length;
  const rest = s.slice(consumed).replace(/^[\s:.\-–—)]+/, "");
  // Grade off the LEADING few words only — the verdict is the head ("faithful", "partial drift"),
  // NOT a verdict-like word buried in the explanation ("uses the DERIVED consequence" is faithful).
  const head = rest.toLowerCase().split(/\s+/).slice(0, 3).join(" ");
  const cls = verdictClass(head);
  let verdict = cls === "fail" ? "drift" : cls === "pass" ? "faithful" : "";
  if (cls === "pass" && /\b(?:untagged|tagging[ -]gap)\b/i.test(head)) verdict = "untagged";
  if (!verdict) verdict = rest.split(/[\s.:,]/)[0] || "";
  return { obj_id: objId, verdict, note: rest.trim() || s.trim() };
}

/** Coerce one verdict element (object | bare-prose string | scalar) to a record. */
function coerceVerdict(el: unknown, expectedIds: Iterable<string> = []): Record<string, unknown> {
  if (typeof el === "string") return parseStringVerdict(el, expectedIds);
  if (el && typeof el === "object") return el as Record<string, unknown>;
  return { verdict: el };
}

export function toVerdictArray(x: unknown, expectedIds: Iterable<string> = []): Record<string, unknown>[] {
  if (Array.isArray(x)) return x.map((el) => coerceVerdict(el, expectedIds));
  if (x && typeof x === "object") {
    return Object.entries(x as Record<string, unknown>).map(([k, val]) => {
      const obj: Record<string, unknown> =
        val && typeof val === "object" ? { ...(val as Record<string, unknown>) } : { verdict: val };
      // Derive the obj_id from the key WITHOUT splitting on ":" — node ids are `prefix:name`
      // (`def:feasible-rate`, `sym:e_P`, `oeq:feasible-upper`), so a `:`-split truncates them to the
      // bare prefix (`def`/`sym`/`oeq`) and they match no node (→ spurious reroute/escalate). Take the
      // first whitespace token, then strip a trailing `:` (covers `"P-8: note"` / `"def:feasible-rate: …"`).
      if (obj.obj_id == null && obj.id == null && obj.object == null) {
        obj.obj_id = normalizeReviewerObjId(k, expectedIds).replace(/:$/, "").trim();
      }
      return obj;
    });
  }
  return [];
}

/**
 * Resolve `*_verdicts` to arrays of records with recovered obj_ids at the PARSE boundary.
 *
 * `mergeOutputs` is a plain reducer, so it re-parses via `toVerdictArray` WITHOUT an
 * expected-id list. A prose-string verdict ("def:rate-bound: matched — …" — a documented
 * live model-output shape) that reaches it unresolved loses its obj_id IRREVERSIBLY (the
 * string becomes `{verdict: <whole string>}`, and later expectedIds-aware passes see an
 * object, not a string, and cannot re-parse it). The merged row then grades as a synthetic
 * "missing reviewer verdict" drift over a real matched — a spurious blocker. Callers must
 * apply this to every peer output BEFORE any merge.
 */
export function resolveVerdictIds(out: ReviewerOutput, expectedIds: Iterable<string>): ReviewerOutput {
  return {
    ...out,
    ...(out.statement_verdicts !== undefined
      ? { statement_verdicts: toVerdictArray(out.statement_verdicts, expectedIds) as unknown as StatementVerdict[] }
      : {}),
    ...(out.assumption_verdicts !== undefined
      ? { assumption_verdicts: toVerdictArray(out.assumption_verdicts, expectedIds) as unknown as AssumptionVerdict[] }
      : {}),
  };
}

/** Merge two reviewer outputs (dual convergence): a target is blocking if EITHER flags it. */
export function mergeOutputs(a: ReviewerOutput, b: ReviewerOutput): ReviewerOutput {
  // why: a present verdict record whose verdict is MISSING/unknown must fail closed, not pass.
  // Pass 1 returns any explicit negative/unknown token; pass 2 returns an explicit pass token;
  // if BOTH are absent (a verdictless record) fall back to the negative default `neg`, never a pass.
  const worst = (x?: string, y?: string, neg = "drift") => {
    for (const v of [x, y]) if (v != null && verdictClass(v) !== "pass") return v;
    for (const v of [x, y]) if (v != null) return v;
    return neg;
  };
  // Preserve the per-target diagnostic note through the merge. Rebuilding each verdict as bare
  // {obj_id, verdict} here dropped the note, so `runReviewer`'s `driftNotes` (which forwards the
  // reviewer's specific "how to fix" to the F2 scaffolder — fix ①) came out EMPTY and the scaffolder
  // only ever saw bare obj_ids → it re-emitted the same shape → the F2.5 reroute whack-a-mole'd.
  // Prefer the note tied to a non-pass (drift) verdict — that's the diagnosis worth relaying; else
  // keep any present note.
  const mergeNote = (
    cur?: { verdict?: string; note?: string },
    inc?: { verdict?: string; note?: string },
  ): string | undefined => {
    for (const r of [cur, inc]) if (r?.note?.trim() && r.verdict != null && verdictClass(r.verdict) !== "pass") return r.note.trim();
    for (const r of [cur, inc]) if (r?.note?.trim()) return r.note.trim();
    return undefined;
  };
  const byId = new Map<string, StatementVerdict>();
  for (const v of [...toVerdictArray(a.statement_verdicts), ...toVerdictArray(b.statement_verdicts)] as unknown as StatementVerdict[]) {
    const cur = byId.get(v.obj_id);
    // Negative-first merge preserves derived/partial/unknown over-claim verdicts from either peer.
    // A PRESENT record with a missing verdict must itself fail closed as `drift` (coerce BEFORE merge,
    // so it can down-rank a `matched` peer — otherwise an `undefined` is skipped and the peer wins).
    byId.set(v.obj_id, {
      obj_id: v.obj_id,
      verdict: worst(cur?.verdict, v.verdict ?? "drift", "drift") as "matched" | "drift",
      note: mergeNote(cur, v),
    });
  }
  const aById = new Map<string, AssumptionVerdict>();
  for (const v of [...toVerdictArray(a.assumption_verdicts), ...toVerdictArray(b.assumption_verdicts)] as unknown as AssumptionVerdict[]) {
    const cur = aById.get(v.obj_id);
    // A PRESENT assumption record with a missing verdict must fail closed as `content-gate` (coerce
    // before merge so it can down-rank a faithful peer, not be skipped as `undefined`).
    aById.set(v.obj_id, {
      obj_id: v.obj_id,
      verdict: worst(cur?.verdict, v.verdict ?? "content-gate", "content-gate") as AssumptionVerdict["verdict"],
      note: mergeNote(cur, v),
    });
  }
  return {
    status: a.status === "flagged" || b.status === "flagged" ? "flagged" : "ok",
    statement_verdicts: [...byId.values()],
    assumption_verdicts: [...aById.values()],
    substrate_gates: [...(a.substrate_gates ?? []), ...(b.substrate_gates ?? [])],
    escalate: a.escalate ?? b.escalate ?? null,
  };
}

/** A graded reviewer output: per-target verdict rows, the blocking (drift/reject) obj_ids,
 *  the routing escalation (if any), and accepted substrate gates. Pure (no graph/IO) so it can
 *  be unit-tested and re-run against a captured `_reviewer_calls.log` transcript. */
export interface GradedReview {
  rows: CrosswalkEntry[];
  blocking: string[];
  escalate: ReviewerEscalation | null;
  substrateGates: SubstrateGate[];
}

/**
 * Map a parsed `ReviewerOutput` to graded verdicts, tolerating the schema drift the model
 * actually emits. The model does not always emit the documented keys/values — seen:
 *   - verdicts as a keyed object instead of an array (handled by `toVerdictArray`);
 *   - `statement_verdict`/`assumption_verdict` for `verdict`; `match` for `matched`;
 *     `detail`/`observation`(singular) for `note`;
 *   - `equivalent`/`partial`/`drift` (not just the documented `matched`/`derived`/…);
 *   - `escalate` as an ARRAY (handled by `normalizeEscalate`).
 * A STATEMENT verdict that isn't clearly a match defaults to `drift` (flag, never silently pass).
 * An ASSUMPTION verdict is rejected on `content-gate`/`derived`/`drift`/`partial`/`crux` and
 * accepted on `faithful-refinement`/`regularity-bookkeeping`/`substrate-gate`/`equivalent`.
 */
/**
 * `aliases` maps EVERY name a node may legitimately be called by → the canonical id used in
 * `expectedObjIds`. A node has two valid names (graph `id` e.g. `lem:admissible-swaps-…`, and
 * `obj_id` e.g. `L-1`), and `nodeIdToObjId` only rewrites short ids (`l1`→`L-1`) — so a descriptive
 * id reaches `expectedObjIds` unchanged while the reviewer may answer under EITHER name. Without
 * canonicalisation, a verdict returned under the other name is not `seen`, its real `matched` is
 * dropped, and a synthetic `drift`/"missing reviewer verdict" is invented over it: a coin-flip
 * blocker that passes or fails on which alias the model happened to pick. (Observed live 2026-07-11.)
 */
export function gradeReviewerOutput(
  out: ReviewerOutput,
  expectedObjIds: Iterable<string> = [],
  aliases: ReadonlyMap<string, string> = new Map(),
): GradedReview {
  const expected = [...expectedObjIds];
  const recognized = [...new Set([...expected, ...aliases.keys()])];
  /** Resolve any alias of a node to the canonical id the caller expects. */
  const canon = (id: string): string => aliases.get(id) ?? id;
  // obj_id may arrive as "P-9", "P-9:IsATEFunctional", or "P-9 IsATEFunctional" (decl name
  // appended) — take the leading token (obj_ids never contain space).
  const vId = (v: Record<string, unknown>): string =>
    normalizeReviewerObjId(v.obj_id ?? v.id ?? v.object ?? v.target, recognized);
  // STATEMENT: only an explicit pass is `matched`; unknown defaults to drift (flag, never silently pass).
  const stmtMatched = (v: Record<string, unknown>): boolean =>
    verdictClass(v.verdict ?? v.statement_verdict) === "pass";
  // ASSUMPTION: accept only an explicit pass (substrate-gate/regularity are legitimate visible debt).
  const assumRejected = (v: Record<string, unknown>): boolean =>
    // why: unknown assumption verdict tokens must not silently count as F4 convergence passes.
    verdictClass(v.verdict ?? v.assumption_verdict) !== "pass";
  const vNote = (v: Record<string, unknown>): string | undefined => {
    const raw = v.note ?? v.detail ?? v.reason ?? v.message ?? v.observation
      ?? (Array.isArray(v.observations) ? (v.observations as unknown[]).join(" ") : v.observations);
    const s = raw == null ? "" : String(raw).trim();
    return s ? s : undefined;
  };
  const sv = toVerdictArray(out.statement_verdicts, recognized);
  const av = toVerdictArray(out.assumption_verdicts, recognized);
  const rows: CrosswalkEntry[] = [
    ...sv.map((v) => minimalRow(canon(vId(v)), stmtMatched(v) ? "equivalent" : "drift", vNote(v))),
    ...av.map((v) => minimalRow(canon(vId(v)), assumRejected(v) ? "drift" : "equivalent", vNote(v))),
  ]
    // Drop verdicts whose obj_id couldn't be parsed: they map to no node (applyVerdictsToGraph
    // skips them) and a nameless `drift` would spuriously halt the loop with `flagged: , , ,`.
    .filter((r) => r.obj_id.trim().length > 0);
  // When the caller names an expected frontier, never forward a model-invented/truncated id to
  // F2. Unexpected rows are ignored; only a missing canonical expected id synthesizes a blocker.
  const expectedSet = new Set(expected);
  const filteredRows = expected.length > 0 ? rows.filter((row) => expectedSet.has(row.obj_id)) : rows;
  // Alias/schema drift can produce multiple rows for one canonical target. Collapse them
  // negative-first so graph state and `blocking` can never disagree about the same object.
  const rowsById = new Map<string, CrosswalkEntry>();
  for (const row of filteredRows) {
    const prior = rowsById.get(row.obj_id);
    if (!prior || row.verdict === "drift" || prior.verdict !== "drift") {
      rowsById.set(row.obj_id, {
        ...(row.verdict === "drift" || prior?.verdict !== "drift" ? row : prior),
        ...((prior?.note || row.note)
          ? { note: [prior?.note, row.note].filter(Boolean).filter((v, i, a) => a.indexOf(v) === i).join(" | ") }
          : {}),
      });
    }
  }
  const canonicalRows = [...rowsById.values()];
  const seen = new Set(canonicalRows.map((r) => r.obj_id));
  for (const id of expected) {
    if (!seen.has(id)) {
      // why: missing target verdicts are reviewer dropouts, not passes.
      canonicalRows.push(minimalRow(id, "drift", "missing reviewer verdict"));
    }
  }
  const blocking = canonicalRows.filter((r) => r.verdict === "drift").map((r) => r.obj_id);
  const rawEscalate = normalizeEscalate(out.escalate);
  const normalizedEscalateId = rawEscalate?.obj_id
    ? canon(normalizeReviewerObjId(rawEscalate.obj_id, recognized))
    : null;
  const escalate = rawEscalate
    ? {
        ...rawEscalate,
        // A reviewer may invent/truncate an id. Keep the escalation itself fail-closed, but never
        // forward an unexpected pseudo-target into the F2 edit list.
        ...(normalizedEscalateId && (expected.length === 0 || expectedSet.has(normalizedEscalateId))
          ? { obj_id: normalizedEscalateId }
          : { obj_id: undefined }),
      }
    : null;
  return { rows: canonicalRows, blocking, escalate, substrateGates: Array.isArray(out.substrate_gates) ? out.substrate_gates : [] };
}
