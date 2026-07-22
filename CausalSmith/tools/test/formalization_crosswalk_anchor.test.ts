import { describe, it, expect } from "vitest";
import {
  crosswalkVerifiedWithoutAnchor,
  anchorDriftFindings,
  buildCompleteCrosswalkFromGraph,
} from "../src/formalization/crosswalk.js";
import type { CrosswalkEntry, CrosswalkVerdict } from "../src/types.js";
import type { FormalizationGraph } from "../src/graph/types.js";

const entry = (
  obj_id: string,
  verdict: CrosswalkVerdict,
  decl: string | null,
): CrosswalkEntry => ({
  obj_id,
  kind: "assumption",
  title: obj_id,
  tex: { label: `obj:${obj_id}`, line_range: "1-2" },
  lean: decl == null ? null : { file: "Basic.lean", decl, decl_kind: "def", line: 1 },
  verdict,
});

describe("crosswalkVerifiedWithoutAnchor (the lean:null + verified-verdict contradiction)", () => {
  it("flags exact/equivalent rows with no anchor", () => {
    const rows = [
      entry("P-8", "equivalent", null), // contradiction
      entry("P-2", "exact", null), // contradiction
      entry("P-7", "unmatched", null), // honest: unanchored paper object
      entry("P-1", "equivalent", "ConditionalRegression"), // anchored, fine
    ];
    const flagged = crosswalkVerifiedWithoutAnchor(rows).map((e) => e.obj_id);
    expect(flagged).toEqual(["P-8", "P-2"]);
  });

  it("does not flag a genuinely unanchored row (verdict unmatched)", () => {
    expect(crosswalkVerifiedWithoutAnchor([entry("L-1", "unmatched", null)])).toEqual([]);
  });
});

describe("anchorDriftFindings (table verdict assigned against a since-changed anchor)", () => {
  it("detects null→decl, decl→decl', and decl→null; ignores unchanged and paper-only", () => {
    const prior = [
      entry("P-8", "equivalent", null), // gained an anchor
      entry("P-3", "exact", "lamDagger"), // retargeted
      entry("P-9", "exact", "rhoRate"), // unchanged
      entry("P-7", "equivalent", "oldDecl"), // lost its anchor
      entry("P-99", "equivalent", "gone"), // paper-only in prior, absent from fresh
    ];
    const fresh = [
      entry("P-8", "unmatched", "ProportionalFolds"),
      entry("P-3", "unmatched", "lamStar"),
      entry("P-9", "unmatched", "rhoRate"),
      entry("P-7", "unmatched", null),
    ];
    const drifts = anchorDriftFindings(prior, fresh);
    expect(drifts.map((d) => `${d.obj_id}:${d.priorDecl}->${d.freshDecl}`)).toEqual([
      "P-8:null->ProportionalFolds",
      "P-3:lamDagger->lamStar",
      "P-7:oldDecl->null",
    ]);
    // P-9 (unchanged) and P-99 (absent from fresh) are not drifts
    expect(drifts.some((d) => d.obj_id === "P-9" || d.obj_id === "P-99")).toBe(false);
  });

  it("carries the prior verdict so the caller can flag laundered verified verdicts", () => {
    const drifts = anchorDriftFindings(
      [entry("P-8", "equivalent", null)],
      [entry("P-8", "unmatched", "ProportionalFolds")],
    );
    expect(drifts[0].verdict).toBe("equivalent");
  });
});

describe("buildCompleteCrosswalkFromGraph anchor-aware verdict", () => {
  const node = (id: string, status: string, declName: string | null) => ({
    id, kind: "assumption", provenance: "agent-introduced",
    review: { status }, lean: { decl_name: declName, file: declName ? "Basic.lean" : null },
    nl: { statement: `${id} statement` },
  });

  it("downgrades a `matched` node with NO Lean anchor to `unmatched` (never `equivalent` against lean:null)", async () => {
    // Regression: an agent-introduced assumption standing in for an inline hypothesis (`hε`/`hz0`) is
    // reviewed `matched` but has no decl — it must NOT surface as a verified match with a null anchor
    // (the F5 "verified against nothing" contradiction).
    const graph = { nodes: [node("postdesign_wald_epsilon_admissible", "matched", null)], edges: [] } as unknown as FormalizationGraph;
    const rows = await buildCompleteCrosswalkFromGraph(graph);
    const row = rows.find((r) => r.obj_id === "postdesign_wald_epsilon_admissible")!;
    expect(row.lean).toBeNull();
    expect(row.verdict).toBe("unmatched");
    // And the F5 gate no longer flags it.
    expect(crosswalkVerifiedWithoutAnchor(rows)).toEqual([]);
  });

  it("keeps `drift` on an unanchored node (a real negative verdict is not hidden)", async () => {
    const graph = { nodes: [node("x", "drift", null)], edges: [] } as unknown as FormalizationGraph;
    const rows = await buildCompleteCrosswalkFromGraph(graph);
    expect(rows.find((r) => r.obj_id === "x")!.verdict).toBe("drift");
  });
});
