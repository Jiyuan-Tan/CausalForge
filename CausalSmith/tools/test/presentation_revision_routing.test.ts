import { describe, it, expect } from "vitest";
import {
  actionForFinding,
  renderRoutingPlan,
  KIND_ACTION,
  partitionFindings,
  MAX_P5_REVISION_PASSES,
  findingFingerprint,
  requiresNewResearch,
  revisionMode,
} from "../src/presentation/revision_routing.js";
import type { ReviewFinding } from "../src/presentation/revision_brief.js";

const f = (kind: ReviewFinding["kind"], section = "s"): ReviewFinding => ({
  severity: "major",
  section,
  issue: "i",
  fix: "x",
  kind,
});

describe("holistic revision routing", () => {
  it("maps each kind to its orchestrator action", () => {
    expect(KIND_ACTION.prose).toEqual({ type: "revise" });
    expect(KIND_ACTION.structure).toEqual({ type: "revise" });
    expect(KIND_ACTION.statement).toEqual({ type: "escalate" });
    expect(KIND_ACTION.citation).toEqual({ type: "decide" });
    expect(KIND_ACTION.other).toEqual({ type: "decide" });
  });
  it("treats an absent kind as `other` → decide", () => {
    expect(actionForFinding(f(undefined))).toEqual({ type: "decide" });
  });
  it("renders a plan grouping by action incl. an out-of-scope + decide section", () => {
    const md = renderRoutingPlan({
      recommendation: "major_revision",
      findings: [f("prose"), { ...f("structure", "global"), issue: "retitle the paper" }, f("statement"), f("other")],
    });
    expect(md).toContain("holistic revision (reframe)");
    expect(md).not.toContain("rewind P");
    expect(md).toContain("escalate");
    expect(md).toMatch(/your call|decide/i);
  });
  it("allows only rewrite findings into unattended revision", () => {
    const p = partitionFindings([f("prose"), f("structure"), f("statement"), f("citation"), f("other")]);
    expect(p.repairable).toHaveLength(2);
    expect(p.blocked).toHaveLength(3);
    expect(MAX_P5_REVISION_PASSES).toBe(2);
  });
  it("uses one reviser for local and paper-wide structure, enabling reframing only when warranted", () => {
    const local = { ...f("structure", "Discussion"), issue: "paragraph is hard to follow" };
    const global = { ...f("structure", "global"), issue: "reframe the contribution for econometric readers" };
    expect(actionForFinding(local)).toEqual({ type: "revise" });
    expect(actionForFinding(global)).toEqual({ type: "revise" });
    expect(revisionMode([local])).toBe("local");
    expect(revisionMode([global])).toBe("reframe");
  });
  it("blocks new-research remedies and uses stable issue ids", () => {
    const research = { ...f("prose"), finding_id: "missing-simulation", remedy: "simulation" as const };
    expect(requiresNewResearch(research)).toBe(true);
    expect(actionForFinding(research)).toEqual({ type: "escalate" });
    expect(findingFingerprint(research)).toBe("missing simulation");
  });
});
