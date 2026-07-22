// Why a node did — or did not — survive into the next D0 round.
//
// This question used to be answerable only by evaluating FIVE predicates scattered
// across ~750 lines of `runStage0Solve`, each written as its own `if` over the same
// prior working state. Nothing reported a verdict, so a node that fell through every
// branch left no trace at all: no record, no warning, no log line. Diagnosing one such
// disappearance took an hour and two wrong causes, and the node in question was a
// finished flagship-adjacent theorem with a 4.5k-character proof.
//
// The traversal is trivial; the CLASSIFICATION is the hard part, so that is what lives
// here — as a pure function over plain sets, with an explicit verdict (and a reason)
// for every id. `runStage0Solve` executes the plan; it no longer decides it.
//
// NOTE ON THE `dropped` VERDICTS: these preserve the existing behaviour exactly. They
// are reported rather than repaired, because at least one of them (legacy-compat
// suppression) is deliberate and the other is a judgment call that should be made
// deliberately rather than smuggled in under a refactor. See `stage0_solve`'s warning.
//
// SCOPE — what this does NOT decide. The frozen-member carry in `stage0_solve` still
// reads `validIds` directly, because its question ("is this frozen member's proof
// reusable?") OVERLAPS the ones here rather than partitioning with them: a node can be
// both a frozen member and an OEQ answer, and those two rules disagree about it. One
// mutually-exclusive verdict cannot represent an overlap, and forcing it to changed
// behaviour in exactly that case. The equivalence test pins all three predicates.

import type { SolvedMember, WorkingState } from "./stages/d0_working.js";

/** What happens to one node from the previous round's working state. */
export type CarryVerdict =
  /** Proof reused as-is. */
  | { fate: "carried"; as: "agent-node" | "proto-member" | "oeq-answer" }
  /** Statement kept, proof invalidated — dispatched again as an open target. */
  | { fate: "re-derive"; as: "agent-node" | "proto-member" | "oeq-answer"; reason: string }
  /** Leaves the working state entirely. */
  | { fate: "dropped"; reason: string };

export interface CarryPlan {
  /** Verdict for every id in the previous round's `solved` map. */
  verdicts: Map<string, CarryVerdict>;
  ids(fate: CarryVerdict["fate"]): string[];
  /** One human-readable line, for a log or an error message. */
  explain(id: string): string;
}

export interface CarryInputs {
  prev: WorkingState | null;
  /** Ids frozen in `proto_core.json`. */
  protoIds: ReadonlySet<string>;
  /** Ids whose stored snapshot still matches the proto — see `computeValidNodes`. */
  validIds: ReadonlySet<string>;
  /** Theorems recorded as the answer to some OEQ. */
  resolutionTheoremIds: ReadonlySet<string>;
  /** OEQ source id -> answer theorem id, for resolutions that survived this round's checks. */
  persistedOeqReplacements: ReadonlyMap<string, string>;
}

/**
 * Classify every node in the previous round's working state.
 *
 * The ordering below is significant and mirrors the original branch order: a
 * resolution theorem is governed ONLY by its source→answer mapping, never by the
 * ordinary validity rules, because its OEQ source still lives in the frozen proto and
 * a stale answer must not collide with a freshly emitted one.
 */
export function planCarry(input: CarryInputs): CarryPlan {
  const { prev, protoIds, validIds, resolutionTheoremIds, persistedOeqReplacements } = input;
  const verdicts = new Map<string, CarryVerdict>();
  const persistedAnswerIds = new Set(persistedOeqReplacements.values());

  for (const [id, rec] of Object.entries(prev?.solved ?? {})) {
    verdicts.set(id, classify(id, rec));
  }

  function classify(id: string, rec: SolvedMember): CarryVerdict {
    const valid = validIds.has(id);

    if (resolutionTheoremIds.has(id)) {
      // Governed by the source->answer mapping. The mapping surviving means the QUESTION
      // is unchanged, so this is still its answer regardless of whether the PROOF is fresh.
      // `resolved_oeqs` is the authoritative semantic relation. `owner` is only
      // provenance and may be absent/stale (for example after an id repair), so it
      // must not decide whether this theorem is still the answer. Checking only that
      // the owner's source key exists can also retain T1 after that source was remapped
      // to T2. Require the theorem id itself to be the surviving map value.
      const mappingHeld = persistedAnswerIds.has(id);
      if (!mappingHeld) {
        return {
          fate: "dropped",
          reason:
            "answers an OEQ whose source->answer mapping did not persist this round " +
            "(no explicit mapping recorded, or the frozen OEQ's fingerprint changed, so the " +
            "question itself moved); suppressed so a stale answer cannot collide with a " +
            "freshly emitted one",
        };
      }
      if (valid) return { fate: "carried", as: "oeq-answer" };
      // Previously DROPPED here, which discarded a finished theorem and sent the OEQ back
      // to the frontier to be re-answered under a new id. The question is unchanged; only
      // the proof needs redoing, so treat it like any other stale node and keep the id.
      return {
        fate: "re-derive",
        as: "oeq-answer",
        reason: "the question is unchanged but the answer's content closure moved; re-prove under the same id",
      };
    }

    if (rec.node) {
      // Agent-authored: `solved` is the ONLY place its statement is defined.
      if (valid) return { fate: "carried", as: "agent-node" };
      if (protoIds.has(id)) {
        // Shares an id with a frozen node, so the proto still defines the statement.
        return { fate: "re-derive", as: "proto-member", reason: "content closure changed since it was proved" };
      }
      return { fate: "re-derive", as: "agent-node", reason: "content closure changed since it was proved" };
    }

    if (protoIds.has(id)) {
      return valid
        ? { fate: "carried", as: "proto-member" }
        : { fate: "re-derive", as: "proto-member", reason: "content closure changed since it was proved" };
    }

    return {
      fate: "dropped",
      reason: "record carries no statement definition and names no frozen proto node",
    };
  }

  return {
    verdicts,
    ids: (fate) => [...verdicts].filter(([, v]) => v.fate === fate).map(([id]) => id),
    explain: (id) => {
      const v = verdicts.get(id);
      if (!v) return `${id}: absent from the previous round's working state`;
      if (v.fate === "carried") return `${id}: carried (${v.as})`;
      if (v.fate === "re-derive") return `${id}: re-derive (${v.as}) — ${v.reason}`;
      return `${id}: DROPPED — ${v.reason}`;
    },
  };
}
