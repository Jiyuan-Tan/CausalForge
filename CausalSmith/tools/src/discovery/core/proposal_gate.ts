// The D-1.2 proposal gate (D0_CORE_REDESIGN.md §12).
//
// Mechanical, no LLM. Runs the D0 structural gate (G1–G7, requireDischarged:false
// — a proto_core proves nothing yet) and adds the proposal-specific extensions
// GP1–GP3 over the SINGLE proposal core (formal fields + prose fields; the .tex is
// a deterministic render of it). It checks WELL-FORMEDNESS only; standardness-
// truthfulness, practicality, and soundness are D-0.5's judgment, not the gate's.
import { CoreSchema } from "./schema.js";
import { runStructuralGate, type GateViolation } from "./gate.js";

export type ProposalGateCode = GateViolation["code"] | "GP1" | "GP2" | "GP3";

export interface ProposalGateViolation {
  code: ProposalGateCode;
  where: string;
  message: string;
}

export interface ProposalGateResult {
  ok: boolean;
  violations: ProposalGateViolation[];
}

/**
 * Gate a D-1.2 proposal = the single proposal core (formal + prose fields).
 *
 * - G1–G7 + schema: the shared D0 structural gate, never discharged at D-1.
 * - GP1 standardness: the human-meaningful tag fields are non-empty. (The
 *   exactly-one-of {standard,novel} XOR is enforced by the schema refine; the
 *   cite-resolves check is G6. GP1 adds the non-emptiness the schema permits.)
 * - GP2 all-to-prove: D-1 authors claims, not proofs — every statement is
 *   status:"to-prove" with no route/proof_tex filled (those are D0's).
 * - GP3 prose-field presence: the proposal narrative is present (tldr,
 *   project_justification {gap,niche,fill}, related_work, an SC6 comparator
 *   promise table) and every statement
 *   carries non-empty justification + gap + consumer. The prose lives in the core
 *   (single source of truth); the .tex is rendered deterministically from it, so
 *   coverage is field-presence, not \coreref resolution.
 */
export function runProposalGate(coreInput: unknown): ProposalGateResult {
  const base = runStructuralGate(coreInput, { requireDischarged: false });
  const violations: ProposalGateViolation[] = [...base.violations];

  // If the core doesn't even parse, the GP checks can't run meaningfully — the
  // schema violations are already in `violations`; fix those first.
  const parsed = CoreSchema.safeParse(coreInput);
  if (!parsed.success) return { ok: false, violations };
  const core = parsed.data;

  // GP1 — standardness: tag fields carry real content.
  for (const a of core.assumptions) {
    if (a.standard && a.standard.name.trim() === "") {
      violations.push({ code: "GP1", where: a.id, message: "standard.name is empty" });
    }
    if (a.novel && a.novel.justification.trim() === "") {
      violations.push({
        code: "GP1",
        where: a.id,
        message: "novel.justification is empty — a novel assumption must justify itself",
      });
    }
  }

  // GP2 — all-to-prove: nothing is proven at D-1.
  for (const s of core.statements) {
    if (s.status !== "to-prove") {
      violations.push({
        code: "GP2",
        where: s.id,
        message: `statement must be status:"to-prove" at D-1 (found '${s.status}') — D0 proves, D-1 only claims`,
      });
    }
    if (s.route !== undefined && s.route.trim() !== "") {
      violations.push({
        code: "GP2",
        where: s.id,
        message: "statement must leave 'route' empty at D-1 — D0-CORE fills the proof strategy",
      });
    }
    if (s.proof_tex !== undefined && s.proof_tex.trim() !== "") {
      violations.push({
        code: "GP2",
        where: s.id,
        message: "statement must leave 'proof_tex' empty at D-1 — D0-PROVE fills the proof",
      });
    }
  }

  // GP3 — prose-field presence. The proposal narrative lives in the core; the .tex
  // is rendered from it. Require the top-level narrative + per-statement motivation.
  const blank = (v: unknown): boolean => typeof v !== "string" || v.trim() === "";
  if (blank(core.tldr)) {
    violations.push({ code: "GP3", where: "<core>", message: "missing tldr" });
  }
  const pj = core.project_justification;
  if (!pj) {
    violations.push({ code: "GP3", where: "<core>", message: "missing project_justification (gap → niche → fill)" });
  } else {
    for (const k of ["gap", "niche", "fill"] as const) {
      if (blank(pj[k])) {
        violations.push({ code: "GP3", where: "project_justification", message: `project_justification.${k} is empty` });
      }
    }
  }
  if (blank(core.related_work)) {
    violations.push({ code: "GP3", where: "<core>", message: "missing related_work" });
  }
  if (!Array.isArray(core.comparator_promise_table ?? core.comparator_promises)) {
    violations.push({
      code: "GP3",
      where: "<core>",
      message: "missing comparator_promise_table (use [] when no theorem-level comparator is named)",
    });
  }
  for (const s of core.statements) {
    for (const k of ["justification", "gap", "consumer"] as const) {
      if (blank(s[k])) {
        violations.push({ code: "GP3", where: s.id, message: `statement is missing prose field '${k}'` });
      }
    }
  }

  return { ok: violations.length === 0, violations };
}
