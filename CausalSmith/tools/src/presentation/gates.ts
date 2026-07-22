import { lintAnchors, lintDefinitionOrder, lintNegativeContributionFraming, lintReferences, parseAnchoredEnvs, repairObjRefs, type LintProblem } from "./tex_anchors.js";
import { citedKeys, type BibEntry } from "./citations.js";
import {
  normalizeRawModelJson,
  repairLatexStringsDeep,
} from "../discovery/core/latex_serialization.js";

/**
 * P3 gate logic, kept pure (model runners injected) so the revision loop and
 * each gate are unit-testable. Hard gates are pass/fail; the soft rubric only
 * drives bounded revision.
 */

export interface StatementCheck {
  obj_id: string;
  envBody: string;
  leanStatement: string;
  /** file/decl/line pointer so the auditor can read the surrounding Lean context. */
  leanPointer: string;
  /** A main result (theorem/lemma) — audited individually at high effort; definitions/assumptions
   *  are short structural comparisons, batched at medium. Keyed off the env KIND (not the obj_id
   *  prefix, which changed from `T-`/`L-` aliases to node ids like `thm:`/`lem:`). */
  isMainResult: boolean;
  /** Exact source-matched propositions erased from the journal-style hypothesis list. */
  citedDependencies?: string;
}

export interface ProofCheck {
  obj_id: string;
  proofTex: string;
  leanPointer: string;
  /** "main" (theorem, audited individually at high effort) or "auxiliary"
   *  (lemma, audited in batches at medium effort). Defaults to "main". */
  tier?: "main" | "auxiliary";
}

export interface GateRunners {
  equivalence(s: StatementCheck, notation: string): Promise<{ verdict: string; detail?: string }>;
  proofAudit(p: ProofCheck): Promise<{ verdict: string; issues?: string[] }>;
  overclaim(
    frontMatter: string,
    frozenEnvsTex: string,
  ): Promise<{ clean: boolean; flags?: { sentence: string; fix?: string }[] }>;
  citationSupport(
    sentence: string,
    entry: BibEntry,
  ): Promise<{ verdict: "supported" | "unsupported" | "unverifiable"; reason?: string }>;
  /** Optional batch pre-pass (cost economy): verdicts keyed by `${key}|${sentence}`.
   *  Pairs missing from the result fall through to individual citationSupport calls. */
  citationSupportBatch?(
    pairs: { sentence: string; entry: BibEntry }[],
  ): Promise<Map<string, { verdict: "supported" | "unsupported" | "unverifiable"; reason?: string }>>;
  /** Optional batch pre-pass for auxiliary (lemma) proofs: verdicts keyed by
   *  obj_id. Proofs missing from the result fall through to individual
   *  proofAudit calls. */
  proofAuditBatch?(
    proofs: ProofCheck[],
  ): Promise<Map<string, { verdict: string; issues?: string[] }>>;
}

export interface HardGateInput {
  paperTex: string;
  notation: string;
  knownObjIds: Set<string>;
  frozenHashes: Map<string, string>;
  proofs: ProofCheck[];
  frontMatter: string;
  frozenEnvsTex: string;
  bibEntries: BibEntry[];
}

/** Sentences of the paper that carry \cite commands, with their keys. */
export function citingSentences(tex: string): { sentence: string; keys: string[] }[] {
  const stripped = tex
    .replace(/(?<!\\)%.*$/gm, "")
    // structural commands glue unrelated text into one "sentence"
    .replace(/\\(?:section|subsection|paragraph|label)\*?\{[^}]*\}/g, "\n")
    .replace(/\\(?:begin|end)\{[^}]*\}/g, "\n");
  const out: { sentence: string; keys: string[] }[] = [];
  for (const sentence of stripped.split(/(?<=[.!?])\s+(?=[A-Z\\])/)) {
    if (!/\\cite/.test(sentence)) continue;
    const keys = [...citedKeys(sentence)];
    if (keys.length > 0) out.push({ sentence: sentence.trim(), keys });
  }
  return out;
}

export interface RefineCheck {
  obj_id: string;
  envBody: string;
  leanStatement: string;
  leanPointer: string;
  driftDetail: string;
  citedDependencies?: string;
}
export type RefineRunner = (
  c: RefineCheck,
  notation: string,
) => Promise<{ refinedBody: string; changed: boolean; note?: string }>;
export type ReauditRunner = (
  s: StatementCheck,
  notation: string,
) => Promise<{ verdict: string; detail?: string }>;

/**
 * Bounded statement refinement (additive guard before the equivalence hard-halt). Re-audits the
 * paper statement against the Lean ground truth; on drift it refines the paper body TOWARD Lean
 * fidelity and re-audits, up to `maxRounds`. Lean is trusted; the graph NL was only the draft.
 * Stops early when the refiner reports it cannot tighten further (`changed=false`). Returns the
 * final body, whether it is now faithful, and whether it escalated (still drifting → the caller
 * keeps it in the hard-halt set).
 */
export async function refineStatement(opts: {
  check: StatementCheck;
  notation: string;
  maxRounds: number;
  reaudit: ReauditRunner;
  refine: RefineRunner;
}): Promise<{ body: string; faithful: boolean; escalated: boolean; rounds: number; detail?: string; note?: string }> {
  let body = opts.check.envBody;
  let lastNote: string | undefined;
  let v = await opts.reaudit({ ...opts.check, envBody: body }, opts.notation);
  let round = 0;
  while (v.verdict !== "faithful" && round < opts.maxRounds) {
    round++;
    const r = await opts.refine(
      {
        obj_id: opts.check.obj_id,
        envBody: body,
        leanStatement: opts.check.leanStatement,
        leanPointer: opts.check.leanPointer,
        driftDetail: v.detail ?? "drift",
        citedDependencies: opts.check.citedDependencies,
      },
      opts.notation,
    );
    if (!r.changed) break; // refiner cannot tighten further → escalate with the current body
    body = r.refinedBody;
    lastNote = r.note;
    v = await opts.reaudit({ ...opts.check, envBody: body }, opts.notation);
  }
  const faithful = v.verdict === "faithful";
  return { body, faithful, escalated: !faithful, rounds: round, detail: v.detail, note: lastNote };
}

/** Max concurrent codex audits in the hard gates (proof / citation). The audits are independent
 *  (each proof/citation pair against its own source), so they run concurrently rather than in a
 *  sequential `for…await` loop. */
export const GATE_CONCURRENCY = 6;

/** Concurrency-limited map: run `fn` over `items` with at most `limit` in flight, results in order. */
export async function mapLimit<T, R>(items: T[], limit: number, fn: (item: T, i: number) => Promise<R>): Promise<R[]> {
  const results = new Array<R>(items.length);
  let next = 0;
  const worker = async (): Promise<void> => {
    while (next < items.length) {
      const i = next++;
      results[i] = await fn(items[i], i);
    }
  };
  await Promise.all(Array.from({ length: Math.min(limit, items.length) }, worker));
  return results;
}

export async function runHardGates(inp: HardGateInput, r: GateRunners): Promise<LintProblem[]> {
  const problems: LintProblem[] = [];
  problems.push(...lintAnchors(inp.paperTex, inp.knownObjIds, inp.frozenHashes));
  problems.push(...lintDefinitionOrder(inp.paperTex, inp.notation));
  problems.push(...lintReferences(inp.paperTex));
  problems.push(...lintNegativeContributionFraming(inp.paperTex));
  problems.push(...repairObjRefs(inp.paperTex, new Set(parseAnchoredEnvs(inp.paperTex).map((e) => e.obj_id))).problems); // why: P3 revisions must not defer dangling obj refs to P4.

  const pool = new Set(inp.bibEntries.map((e) => e.key));
  for (const k of citedKeys(inp.paperTex)) {
    if (!pool.has(k)) problems.push({ gate: "cite-pool", detail: `\\cite{${k}} not in the verified pool` });
  }

  // Proof audit: auxiliary (lemma) proofs are batched; the main (theorem) proofs are audited
  // individually — in PARALLEL (each vs its own Lean proof, independent).
  const auxProofs = inp.proofs.filter((p) => p.tier === "auxiliary");
  const proofPre = auxProofs.length > 0 ? ((await r.proofAuditBatch?.(auxProofs)) ?? new Map()) : new Map();
  const proofVerdicts = await mapLimit(inp.proofs, GATE_CONCURRENCY, async (p) => ({
    p,
    v: proofPre.get(p.obj_id) ?? (await r.proofAudit(p)),
  }));
  for (const { p, v } of proofVerdicts) {
    if (v.verdict !== "faithful") {
      problems.push({
        gate: "proof-audit",
        detail: `${p.obj_id}: ${(v.issues ?? ["unfaithful"]).join("; ")}`,
      });
    }
  }
  const oc = await r.overclaim(inp.frontMatter, inp.frozenEnvsTex);
  if (!oc.clean) {
    for (const f of oc.flags ?? []) {
      problems.push({ gate: "overclaim", detail: `${f.sentence}${f.fix ? ` → ${f.fix}` : ""}` });
    }
    if ((oc.flags ?? []).length === 0) problems.push({ gate: "overclaim", detail: "flagged without detail" });
  }
  const byKey = new Map(inp.bibEntries.map((e) => [e.key, e]));
  const pairs: { sentence: string; entry: BibEntry }[] = [];
  for (const { sentence, keys } of citingSentences(inp.paperTex)) {
    for (const k of keys) {
      const entry = byKey.get(k);
      if (!entry) continue; // already a cite-pool problem
      pairs.push({ sentence, entry });
    }
  }
  // Citation support: batched first, individual fallbacks audited in PARALLEL.
  const pre = (await r.citationSupportBatch?.(pairs)) ?? new Map();
  const citeVerdicts = await mapLimit(pairs, GATE_CONCURRENCY, async ({ sentence, entry }) => ({
    sentence,
    entry,
    v: pre.get(`${entry.key}|${sentence}`) ?? (await r.citationSupport(sentence, entry)),
  }));
  for (const { sentence, entry, v } of citeVerdicts) {
    const k = entry.key;
    if (v.verdict === "unsupported") {
      problems.push({ gate: "citation-support", detail: `${k}: ${v.reason ?? "unsupported"} — "${sentence.slice(0, 120)}"` });
    } else if (v.verdict === "unverifiable") {
      // advisory: evidence is silent, nothing contradicts — callers filter
      // this gate out of the hard pass/fail set and log it instead.
      problems.push({ gate: "citation-unverifiable", detail: `${k}: ${v.reason ?? ""} — "${sentence.slice(0, 120)}"` });
    }
  }
  return problems;
}

export interface RubricReview {
  scores: Record<string, number>;
  weaknesses: string[];
}

/** Boundary validation for a model-emitted rubric review. Malformed JSON must be
 *  rejected here, not scored: a string score becomes NaN, and `NaN < RUBRIC_PASS`
 *  is false — a garbage review would silently pass the gate. */
export function parseRubricReview(v: unknown): RubricReview | null {
  if (typeof v !== "object" || v === null) return null;
  const o = v as { scores?: unknown; weaknesses?: unknown };
  if (typeof o.scores !== "object" || o.scores === null) return null;
  const entries = Object.entries(o.scores as Record<string, unknown>);
  if (entries.length === 0 || !entries.every(([, s]) => typeof s === "number" && Number.isFinite(s))) return null;
  const weaknesses = o.weaknesses === undefined ? [] : o.weaknesses;
  if (!Array.isArray(weaknesses) || !weaknesses.every((w) => typeof w === "string")) return null;
  return { scores: o.scores as Record<string, number>, weaknesses };
}

const reviewMeans = (reviews: RubricReview[]): number[] =>
  reviews
    .map((r) => {
      const v = Object.values(r.scores);
      return v.reduce((a, b) => a + b, 0) / Math.max(1, v.length);
    })
    .sort((a, b) => a - b);

export function medianRubric(reviews: RubricReview[]): number {
  const means = reviewMeans(reviews);
  return means.length === 0 ? 0 : means[Math.floor(means.length / 2)];
}

/** Pass statistic for a 2-reviewer ensemble: the harsher reviewer binds. */
export function minRubric(reviews: RubricReview[]): number {
  const means = reviewMeans(reviews);
  return means.length === 0 ? 0 : means[0];
}

/** Bounded gate-revise loop. `run` re-evaluates the gates; `revise` mutates the paper. */
export async function gateLoop(opts: {
  maxRounds: number;
  run: () => Promise<LintProblem[]>;
  revise: (problems: LintProblem[], round: number) => Promise<void>;
}): Promise<{ ok: boolean; rounds: number; problems: LintProblem[] }> {
  let problems = await opts.run();
  let round = 0;
  while (problems.length > 0 && round < opts.maxRounds) {
    round++;
    await opts.revise(problems, round);
    problems = await opts.run();
  }
  return { ok: problems.length === 0, rounds: round, problems };
}

/** Extracts the first parseable JSON object from model output. */
export function parseJsonLoose(text: string): unknown {
  // Model-authored JSON carrying TeX gets the same three-layer escape defense as
  // the D-stage boundaries: `normalizeRawModelJson` repairs BOTH invalid escapes
  // (`\(m\ge1\)`) and the silent collision class (`\to` decoding to a tab) on the
  // raw bytes, where they are still distinguishable; the post-parse deep repair
  // then restores control characters that arrived pre-encoded as valid `\u00XX`
  // escapes. `repairUnknownJsonEscapes` stays as the legacy fallback.
  const parseCandidate = (candidate: string): unknown => {
    const attempts = [
      () => JSON.parse(normalizeRawModelJson(candidate)),
      () => JSON.parse(candidate),
      () => JSON.parse(repairUnknownJsonEscapes(candidate)),
    ];
    for (const attempt of attempts) {
      try {
        const parsed = attempt();
        repairLatexStringsDeep(parsed);
        return parsed;
      } catch {
        /* try the next repair tier */
      }
    }
    return null;
  };
  const first = text.indexOf("{");
  const last = text.lastIndexOf("}");
  if (first >= 0 && last > first) {
    const whole = parseCandidate(text.slice(first, last + 1));
    if (whole !== null) return whole;
    let depth = 0;
    let start = -1;
    for (let i = first; i <= last; i++) {
      const c = text[i];
      if (c === "{") {
        if (depth === 0) start = i;
        depth++;
      } else if (c === "}") {
        depth--;
        if (depth === 0 && start >= 0) {
          const parsed = parseCandidate(text.slice(start, i + 1));
          if (parsed !== null) return parsed;
          start = -1;
        }
      }
    }
  }
  return null;
}

/**
 * Quote only genuinely unknown backslash escapes inside JSON strings.
 *
 * A regex cannot do this safely: in the valid JSON source `"\\\\(x\\\\)"`,
 * the second backslash is followed by `(` and looks invalid in isolation, but
 * it has already been consumed by the valid `\\\\` escape.  Scanning escape
 * pairs atomically preserves that source while repairing model output such as
 * `"\\(x\\)"` to `"\\\\(x\\\\)"`.
 */
export function repairUnknownJsonEscapes(candidate: string): string {
  let out = "";
  let inString = false;
  for (let i = 0; i < candidate.length; i++) {
    const c = candidate[i];
    if (!inString) {
      out += c;
      if (c === '"') inString = true;
      continue;
    }
    if (c === '"') {
      out += c;
      inString = false;
      continue;
    }
    if (c !== "\\") {
      out += c;
      continue;
    }
    const next = candidate[i + 1];
    if (next !== undefined && /["\\/bfnrtu]/.test(next)) {
      out += c + next;
      i += 1;
    } else {
      out += "\\\\";
    }
  }
  return out;
}
