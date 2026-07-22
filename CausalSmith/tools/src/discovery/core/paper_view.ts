// THE single authority for "what is the current, complete paper".
//
// Why this module exists
// ----------------------
// D0 keeps the paper's content in several stores, and each reviewer used to
// assemble its own view from a different subset:
//
//   D0.5.1/D0.5.2  rendered core.json                      (in-memory)
//   D0.5.G         read writeup.tex                        (from disk)
//   D0.R           edited raw core.json                    (in-memory)
//   D0 adjudicator read proto_core.json + proposed_*.json  (from disk)
//
// Those views disagree. The most expensive disagreement: when a round proposes a
// structural change, `stage0_solve` deliberately withholds that round's fresh
// proofs from core.json and banks them in proposed_proofs.json. A reviewer
// assembling from core.json alone therefore reads STALE proof text and reports
// the result as "merely asserted" / "incomplete" — a plumbing artifact delivered
// as a mathematical defect. That drove an eight-round REJECT loop on the
// 2026-07-18 stat_cot_observational_efficiency run.
//
// Fixing that per-reviewer is what created the drift in the first place. So the
// rule is: NOBODY assembles the paper themselves. Every consumer calls
// `loadPaperView` and reads `view.core` / `view.tex`. A new reviewer added later
// is correct by construction rather than by remembering to overlay.
import { readFile } from "node:fs/promises";
import { existsSync } from "node:fs";
import { artifactPath } from "../../paths.js";
import type { PipelineContext } from "../../types.js";
import { loadWorkingState } from "../stages/d0_working.js";
import { readRoundProposals } from "../solve/proposals.js";
import { CoreSchema, type Core } from "./schema.js";
import { renderCoreTex } from "./render_tex.js";
import { coreJsonPath } from "../stages/d0_core.js";
import { readTypedCore } from "./core_io.js";

/** A same-round proof payload banked in `proposed_proofs.json` while a structural
 *  proposal is pending. */
export interface ProvisionalProof {
  id: string;
  proof_tex: string;
}

export interface PaperView {
  /** The core with this round's provisional proofs overlaid. Use this for review,
   *  for rendering, and as the edit base — never the raw core.json. */
  core: Core;
  /** Deterministic render of `core`. Identical bytes for every consumer. */
  tex: string;
  /** Ids whose proof came from `proposed_proofs.json` rather than core.json. */
  overlaid: string[];
  /** Provisional proofs naming no core statement — a plumbing fault, surfaced. */
  unmatchedProofs: string[];
  /** Provenance, for the one-line log every consumer emits. */
  provenance: { corePath: string; provisionalPath: string | null; statements: number; texChars: number };
}

/** Overlay provisional proofs onto a copy of the core. Pure; does not mutate input. */
export function overlayProvisionalProofs<
  C extends { statements: Array<{ id: string; proof_tex?: string }> },
>(core: C, proofs: ProvisionalProof[]): { core: C; applied: string[]; unmatched: string[] } {
  const next = structuredClone(core);
  const byId = new Map(next.statements.map((s) => [s.id, s] as const));
  const applied: string[] = [];
  const unmatched: string[] = [];
  for (const proof of proofs) {
    const stmt = byId.get(proof.id);
    if (!stmt || typeof proof.proof_tex !== "string" || proof.proof_tex.trim().length === 0) {
      unmatched.push(proof.id);
      continue;
    }
    stmt.proof_tex = proof.proof_tex;
    applied.push(proof.id);
  }
  return { core: next, applied, unmatched };
}

async function readProvisionalProofs(ctx: PipelineContext): Promise<{ proofs: ProvisionalProof[]; path: string | null }> {
  // `working.proposals` is AUTHORITATIVE when present; the per-kind files are a derived
  // mirror (solve/proposals.ts). Reading the mirror here let the reviewer grade one set of
  // proofs while the apply committed another -- the two stores can disagree, and D0.5/D0.R
  // both consume this view. Prefer the authoritative copy, mirror only as the legacy
  // fallback, exactly as the apply resolves it.
  const working = await loadWorkingState(ctx);
  // Route through the canonical accessor so a pre-fold run's legacy leftovers
  // fail LOUD here too — a reviewer must never grade a paper against a
  // phantom-empty proof payload (the incident class the fold exists to kill).
  const round = await readRoundProposals(ctx, working);
  if (round.proofs.length > 0) return { proofs: round.proofs, path: "working.proposals" };
  return { proofs: [], path: null };
}

/** Assemble the canonical paper view. Fail-closed: a missing or empty core is a
 *  plumbing failure, never something to hand a referee and let it render a verdict on. */
export async function loadPaperView(ctx: PipelineContext, opts?: { corePath?: string }): Promise<PaperView> {
  const corePath = opts?.corePath ?? coreJsonPath(ctx);
  if (!existsSync(corePath)) {
    throw new Error(`Cannot assemble the paper view: core is absent at ${corePath}. This is a plumbing failure.`);
  }
  const raw = await readTypedCore(corePath);
  const { proofs, path: provisionalPath } = await readProvisionalProofs(ctx);
  const { core, applied, unmatched } = overlayProvisionalProofs(raw, proofs);
  const tex = renderCoreTex(core);
  if (tex.trim().length === 0) {
    throw new Error(`Assembled paper view is EMPTY (core ${corePath} rendered to 0 chars). Refusing to review nothing.`);
  }
  return {
    core,
    tex,
    overlaid: applied,
    unmatchedProofs: unmatched,
    provenance: { corePath, provisionalPath, statements: core.statements.length, texChars: tex.length },
  };
}

/** One-line provenance log. Every consumer emits this, so a paper-assembly problem is
 *  visible in the transcript rather than inferred from a downstream verdict. The whole
 *  prompt's char count cannot reveal it — the static rubric dominates that number. */
export function logPaperView(view: PaperView, consumer: string): void {
  console.error(
    `[${consumer}] paper view: ${view.provenance.statements} statement(s), ${view.provenance.texChars} tex chars, ` +
      `${view.overlaid.length} provisional proof(s) overlaid` +
      (view.overlaid.length > 0 ? ` (${view.overlaid.join(", ")})` : "") +
      ` from ${view.provenance.corePath}`,
  );
  if (view.unmatchedProofs.length > 0) {
    console.error(
      `[${consumer}] PLUMBING FAULT: ${view.unmatchedProofs.length} provisional proof(s) name no core statement ` +
        `and are NOT in the reviewed paper: ${view.unmatchedProofs.join(", ")}.`,
    );
  }
}
