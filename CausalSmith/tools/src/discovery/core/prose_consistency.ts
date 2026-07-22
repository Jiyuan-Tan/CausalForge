// Prose-consistency lint over the D0 core.
//
// Catches the failure mode where a LATE headline reframe changes the formal
// statements but the PROSE fields (tldr / project_justification / related_work /
// interpretation / technical_internal_limitation / honest_scope) are carried over
// STALE. D0-RENDER is a verbatim render (`renderCoreTex`, no reconciliation), so a
// reframe whose directive omits the explicit D0 prose-update channel leaves the prose
// asserting a claim the revised statements no longer deliver (observed 2026-07-10:
// a barrier-led reframe left a stale "matching-bounds / frontier" TL;DR).
//
// Two signals, BOTH ADVISORY (non-blocking): they surface the drift so the D0.R
// prose-sync rule / the D0.5 referee can fix it, rather than letting it render silently.
import type { Core } from "./schema.js";
import { coreNodeIds } from "./schema.js";
import { extractCitationRefs } from "./node_ids.js";

export interface ProseWarning {
  code: "PROSE-DANGLING-REF" | "PROSE-OPEN-OVERCLAIM";
  field: string; // which prose field the drift is in
  message: string;
}

/** The prose fields, as (fieldName, text) pairs, skipping absent ones. */
function proseFields(core: Core): Array<{ field: string; text: string }> {
  const out: Array<{ field: string; text: string }> = [];
  if (core.tldr) out.push({ field: "tldr", text: core.tldr });
  const pj = core.project_justification;
  if (pj) {
    out.push({ field: "project_justification.gap", text: pj.gap });
    out.push({ field: "project_justification.niche", text: pj.niche });
    out.push({ field: "project_justification.fill", text: pj.fill });
  }
  if (core.related_work) out.push({ field: "related_work", text: core.related_work });
  if (core.interpretation) out.push({ field: "interpretation", text: core.interpretation });
  if (core.technical_internal_limitation) {
    out.push({ field: "technical_internal_limitation", text: core.technical_internal_limitation });
  }
  if (core.honest_scope) out.push({ field: "honest_scope", text: core.honest_scope });
  return out;
}

// Ids are read through `extractCitationRefs` (core/node_ids.ts) — the SAME strict
// citation semantics the D0 consistency gate uses. A fifth private copy of the id
// regex used to live here and repeated the gate's misread: it matched the node
// segment of a `<paper>/<node-id>` cross-paper reference and reported the other
// paper's lemma as a dangling id in `related_work`. Positioning prose names other
// papers by construction, so this lint sees qualified references more often than
// most callers, not less.

// Positive "we established a result" verbs. Deliberately excludes "provide" (matches
// only `prove[ns]?`/`proved`, never `provid…`) and other soft verbs to keep FPs low.
const ESTABLISH =
  /\b(?:determin\w*|establish\w*|prove[ns]?|proved|obtain\w*|deriv\w*|settl\w*|characteriz\w*|resolv\w*|pin\s+down|nail\s+down)\b/i;
// A negation / open-acknowledgement anywhere in the clause suppresses the flag (the
// prose is honestly saying the target is NOT established).
const NEGATION =
  /\b(?:not|cannot|can't|never|no\b|without|fails?\s+to|leaves?\b|leave\b|remains?\s+open|open\s+question|conjectur\w*|do(?:es)?\s+not|is\s+not)\b/i;

const STOPWORDS = new Set([
  "the", "and", "for", "with", "that", "this", "which", "under", "over", "from",
  "into", "onto", "when", "where", "while", "these", "those", "there", "their",
  "such", "than", "then", "each", "every", "given", "using", "based", "whose",
  "result", "results", "bound", "bounds", "rate", "rates", "class", "problem",
]);

/** Distinctive lowercased words (letters only, length ≥ 6, non-stopword) of a text. */
function distinctiveTerms(text: string): Set<string> {
  const out = new Set<string>();
  for (const w of text.toLowerCase().match(/[a-z]{6,}/g) ?? []) {
    if (!STOPWORDS.has(w)) out.add(w);
  }
  return out;
}

function isOpen(s: Core["statements"][number]): boolean {
  return s.kind === "openendedquestion" || s.kind === "conjecture" || /^(?:oeq|conj):/.test(s.id);
}

/**
 * The part of an OPEN statement that states what is actually OPEN.
 *
 * A well-scoped open question narrows itself by first reciting what is already
 * settled ("The Gaussian spectral subproblem is settled: square summability is
 * necessary and sufficient for L² existence … Does there exist …?"). Terms from that
 * recital name PROVED material, not the open target, so treating them as open-only
 * made the lint flag honest prose for agreeing with the recital — and it recurs for
 * every correctly-narrowed open node, not just the one that surfaced it.
 *
 * Drop a sentence only when it is BOTH non-interrogative AND asserts establishment.
 * The interrogative carve-out is load-bearing: `ESTABLISH` matches `deriv\w*`, so the
 * question "…which alternative derivative-aware calibration conditions are necessary
 * and sufficient?" reads as an establishment claim and would otherwise be dropped too,
 * emptying the term set and silencing the signal entirely.
 */
function openTargetText(statement: string): string {
  const sentences = statement.split(/(?<=[.;!?])\s+/);
  const kept = sentences.filter((s) => /\?/.test(s) || !ESTABLISH.test(s) || NEGATION.test(s));
  // All sentences recite settled material ⇒ no narrowing to do; fall back to the whole
  // statement rather than silently dropping the node from the check.
  return kept.length > 0 ? kept.join(" ") : statement;
}

/**
 * Lint the core for prose that has drifted from the formal statements.
 *
 * - PROSE-DANGLING-REF: prose cites a `thm:`/`oeq:`/… id that is not a current core
 *   node (a reframe renamed/removed the object the prose still names). Deterministic,
 *   but "a pure id-resolution check" is only zero-false-positive once "an id" is
 *   defined correctly: a `<paper>/<node-id>` cross-paper reference and an id declared
 *   in a node's `external_refs` both name another paper's result and are NOT stale
 *   references. Resolution alone cannot tell those from a dangling id — the earlier
 *   version claimed zero false positives and emitted one.
 * - PROSE-OPEN-OVERCLAIM: a prose sentence uses an "established" verb (no negation) on
 *   a distinctive term that appears ONLY in an OPEN statement (openendedquestion /
 *   conjecture) and in NO proved/to-prove non-open statement — i.e. the prose claims to
 *   have established the very object the note leaves open. Conservative: tied to a term
 *   unique to an open node, so genuinely-proved claims (whose terms appear in a
 *   non-open statement) do not fire.
 */
export function checkProseConsistency(core: Core): ProseWarning[] {
  const warnings: ProseWarning[] = [];
  const ids = coreNodeIds(core);

  const openStmts = core.statements.filter(isOpen);
  // Terms distinctive to the OPEN nodes: appear in an open statement but in NO
  // non-open statement (so they name the open target, not a shared/proved object).
  const nonOpenText = core.statements
    .filter((s) => !isOpen(s))
    .map((s) => s.statement.toLowerCase())
    .join("  ");
  const openOnlyTerms = new Map<string, string>(); // term -> owning open-statement id
  for (const s of openStmts) {
    for (const t of distinctiveTerms(openTargetText(s.statement))) {
      if (!nonOpenText.includes(t) && !openOnlyTerms.has(t)) openOnlyTerms.set(t, s.id);
    }
  }

  // Ids any node declares as belonging to ANOTHER paper. Prose naming one is
  // provenance, not a stale reference — see `external_refs` in core/schema.ts.
  const declaredExternal = new Set(
    core.statements.flatMap((s) => (s.external_refs ?? []).map((r) => r.slice(r.indexOf("/") + 1).toLowerCase())),
  );

  for (const { field, text } of proseFields(core)) {
    // Signal A — dangling id references.
    for (const ref of extractCitationRefs(text)) {
      if (!ids.has(ref) && !declaredExternal.has(ref)) {
        warnings.push({
          code: "PROSE-DANGLING-REF",
          field,
          message: `prose cites \`${ref}\`, which is not a current core node — stale after a rename/reframe? Fix the prose or the reference.`,
        });
      }
    }
    // Signal B — establishment claim on an open-only target.
    if (openOnlyTerms.size > 0) {
      for (const sentence of text.split(/(?<=[.;!?])\s+/)) {
        if (!ESTABLISH.test(sentence) || NEGATION.test(sentence)) continue;
        const lower = sentence.toLowerCase();
        for (const [term, owner] of openOnlyTerms) {
          if (lower.includes(term)) {
            // CIRCULAR MATCH. `ESTABLISH` contains status verbs (`settl\w*`,
            // `characteriz\w*`, …) and `distinctiveTerms` accepts any non-stopword word,
            // so one token can supply BOTH halves of the test. A well-scoped open node
            // recites what IS settled before posing its question ("The Gaussian spectral
            // subproblem is settled: … Does there exist …?"), which makes `settled` a
            // term unique to an open statement — and then every honest sentence saying
            // some OTHER result is settled flags itself. Observed 4+ times on
            // stat_cot_observational_efficiency, where the cited criterion really is
            // proved. Re-test with the term removed: if nothing else in the sentence
            // claims establishment, the term WAS the verb and the match is vacuous.
            // Deliberately not a stopword list — `deriv\w*` also matches "derivative",
            // a real mathematical term in these statements, so dropping every
            // ESTABLISH-shaped word would silence genuine over-claims.
            if (!ESTABLISH.test(lower.split(term).join(" "))) continue;
            warnings.push({
              code: "PROSE-OPEN-OVERCLAIM",
              field,
              message: `prose claims to have established "${term}" ("${sentence.trim().slice(0, 120)}"), but that is described by the OPEN statement \`${owner}\`. Verify the prose is not over-claiming a result the note leaves open.`,
            });
            break; // one flag per sentence is enough
          }
        }
      }
    }
  }
  return warnings;
}
