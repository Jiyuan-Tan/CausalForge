// Condensed runtime echo of the meta-orchestrator's playbook.
//
// WHY: over a long run the causalsmith-main skill and its phase sub-skills can
// drift out of the orchestrator's attention, so on resume it can forget what
// to do at the checkpoint it just hit. This module re-surfaces, on every halt, a SHORT
// operative reminder for (1) the checkpoint just reached and (2) the next
// phase — carried in the `next_step_guidance` field of the pipeline.jsonl
// checkpoint line (the line the SKILL tells the orchestrator to read) and
// echoed to the console.
//
// SINGLE SOURCE OF TRUTH: `.claude/skills/causalsmith-main/SKILL.md` is the
// canonical entry point; it dispatches `causalsmith-d` / `causalsmith-f` and uses
// `causalsmith-shared/reference.md` for shared procedures. This file holds only
// the STABLE invariants + a pointer to the relevant skill section.
// Keep each entry to ~2 sentences: what to do at THIS halt, and what the next
// phase is. Do NOT grow it into a copy of the skill — point, don't paste.

import type { Stage } from "./types.js";

/**
 * AUTO-MODE banner, prepended to the per-stage reminder when the run is
 * autonomous (`state.auto_mode`). In practice the orchestrator forgets it is in
 * auto mode after a long run and reverts to asking the user, so this re-asserts
 * the rule on EVERY checkpoint line it reads. F5 (CKPT 2) is the one designated
 * stop — bank/promote/commit always wait for the user.
 */
function autoBanner(stage: Stage): string {
  if (stage === "5") {
    return (
      "⚙ AUTO MODE — CKPT 2 is the designated stop: present the result and bank-tier recommendation; " +
      "wait for user approval before banking, committing, or promoting.\n\n"
    );
  }
  return (
    "⚙ AUTO MODE — decide, act, and `--resume` without asking the user. Handle substrate, literature, maximality, and de-laundering autonomously; " +
    "report only a false claim, proven intractability, or a cap/budget block. Otherwise drive to CKPT 2.\n\n"
  );
}

/**
 * Condensed orchestrator reminder for a halt at `stage` with `status`.
 * Returns `undefined` for stages that never need a human decision (so the
 * pipeline log stays quiet on ordinary `completed` transitions). When
 * `autoMode` is set, an AUTO-MODE banner is prepended so the orchestrator does
 * not forget the run is autonomous.
 */
export function checkpointGuidance(
  stage: Stage,
  status: string,
  flags: { substrate_build_required?: string | null } = {},
  autoMode = false,
  message = "",
): string | undefined {
  // Only checkpoints and blocks hand control back to the orchestrator.
  if (status !== "checkpoint" && status !== "blocked") return undefined;

  const base = perStageGuidance(stage, flags, message);
  if (base === undefined) return undefined;
  return autoMode ? autoBanner(stage) + base : base;
}

function perStageGuidance(
  stage: Stage,
  flags: { substrate_build_required?: string | null },
  message = "",
): string | undefined {
  switch (stage) {
    case "-0.5":
      return (
        "D-0.5: NO-PASS is terminal, not merely stopped — read its verdict. If it passed, next is D0 solve. " +
        "SKILL §'Watch keys' D-0.5 row."
      );

    case "0":
      return (
        "D0: adjudicate proposed changes; inject literature-grounded directives for open gaps; test maximality (proved ≠ best). " +
        "Improve unless a genuine research barrier; never auto-bank. Next is D0.5 → F1. SKILL §'D0 — three checkpoint events'."
      );

    case "0.5": {
      // The D0.5 halt is NOT always a pass — it can also be a non-converging
      // revise loop or a below-floor tier. All three share status "checkpoint",
      // so branch on the actual verdict in the halt message (never assert PASS
      // blindly — that canned wording once fooled the orchestrator into treating
      // a non-converging halt as a pass and resuming toward F1).
      const m = message.toLowerCase();
      if (m.includes("non-converging") || m.includes("non converging")) {
        return (
          "D0.5 NON-CONVERGING — not a pass (stage stays \"0\"; no general review). Read the findings; repair the source proto/definitions/assumptions toward truth, never by strengthening; add a D0 directive and rerun D0 → D0.5, or rewind D0/D-1.2. " +
          "F1 waits for a real pass."
        );
      }
      if (m.includes("below novelty floor") || m.includes("below-floor") || m.includes("< floor")) {
        return (
          "D0.5 BELOW NOVELTY FLOOR — not a pass. Do not lower the user's floor: inject the directed improvement and rerun D0 → D0.5, or bank downgraded / re-anchor at D-1.2. " +
          "F1 waits for the floor."
        );
      }
      const negativePass = /\b(did not pass|not pass|no-pass|fail(?:ed|s|ure)?)\b/.test(m);
      const explicitPass = /\b(pass(?:ed|es)?|cleared)\b/.test(m);
      if (!negativePass && explicitPass && (m.includes("floor") || m.includes("go/no-go"))) {
        // why: "did not pass the floor" must not route to PASS guidance.
        return (
          "D0.5 PASS: confirm stage_completed=\"0.5\" and reviews/review_general.json, then decide whether to enter F1–F5. " +
          "On resume, F1 → F1.5 reaches consolidated CKPT 1 for depth, reuse, and statement-fidelity audit. SKILL §'F1 CKPT 1'."
        );
      }
      // Unknown D0.5 halt shape — do NOT assume pass; force a verdict-body read.
      return (
        "D0.5 halt: read its message and stage_completed. Only stage \"0.5\" plus reviews/review_general.json is PASS; stage \"0\" means repair findings / lift tier and rerun D0.5. " +
        "Never infer PASS from the stage alone. SKILL §'Watch keys' D0.5 row."
      );
    }

    case "1":
      // F1 only halts on a substrate-build block now (the plan-audit halt moved
      // to F1.5 — the consolidated CKPT 1).
      if (flags.substrate_build_required) {
        return (
          "SUBSTRATE-BUILD: build every Defer item via --study or a background builder. Gate only the minimal irreducible theory absent from Mathlib; derive all surrounding support rather than laundering it into a hypothesis. " +
          "Verify each build (0-sorry, axiom-clean, statement-match), clear the flag, and resume. At the next checkpoint replace each gate, rewind F2.5 (not F1), and re-pass F4 before banking; never hand-patch the plan. SKILL §'Cross-cutting actions'."
        );
      }
      return undefined;

    case "1.5":
      return (
        "CONSOLIDATED CKPT 1: audit plan depth, reuse, and statement fidelity. For missing infrastructure, dispatch builders, proceed minimally gated, and discharge gates next checkpoint; never hand-patch the plan. " +
        "Then F2–F4 follows its route; reject laundering, and edit .tex only by upward, dischargeable strengthening. SKILL §'F2–F4 loop'."
      );

    case "2.5":
    case "3":
    case "3.5":
    case "4":
      return (
        "F2–F4: follow the checkpoint route (hint / build-substrate / fix-source—verify rewind / unclear / bank-partial / abandon); keep running while revisions converge. " +
        "Use fix-source/failed only when .tex is wrong; unclear is undetermined, so investigate. After hand de-laundering, run F3.5→F5, record added_assumptions, restore laundering_count=0, and make the bank call. SKILL §'F2–F4 loop'."
      );

    case "5":
      return (
        "F5 / CKPT 2: banking, promotion, and commit require user approval; bank `failed` only if the math is wrong. " +
        "A clean bank writes CHECKPOINT_NEXT.md for the user's next command. SKILL §F5 / Phase 4."
      );

    default:
      return undefined;
  }
}
