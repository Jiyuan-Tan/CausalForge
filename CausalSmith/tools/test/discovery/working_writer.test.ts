import { describe, it, expect } from "vitest";
import { recordProof, refreshSnapshots } from "../../src/discovery/working_writer.js";
import { computeValidNodes } from "../../src/discovery/stages/d0_working.js";
import type { WorkingState } from "../../src/discovery/stages/d0_working.js";
import type { Core, CoreStatement } from "../../src/discovery/core/schema.js";

function makeCore(
  stmts: Array<Record<string, unknown>>,
  assumptions: Array<Record<string, unknown>> = [],
  definitions: Array<Record<string, unknown>> = [],
): Core {
  return {
    title: "t",
    assumptions: assumptions as never,
    definitions: definitions as never,
    statements: stmts as never,
    bibliography: [],
  } as unknown as Core;
}

const stmt = (over: Record<string, unknown> = {}): CoreStatement =>
  ({ id: "lem:a", kind: "lemma", status: "proved", statement: "S", depends_on: [], ...over }) as CoreStatement;

function emptyWorking(): WorkingState {
  return { round: 1, solved: {}, resolved_oeqs: {} } as WorkingState;
}

describe("recordProof", () => {
  it("writes proof, snapshot, node and owner", () => {
    const w = emptyWorking();
    const node = stmt();
    recordProof(w, makeCore([node]), { id: node.id, snapshotOf: node, proofTex: "P", node, owner: "unit-1" });

    expect(w.solved["lem:a"].proof_tex).toBe("P");
    expect(w.solved["lem:a"].owner).toBe("unit-1");
    expect(w.solved["lem:a"].snapshot.stmt).toBe("S");
  });

  it("omits node and owner rather than storing undefined for a frozen proto member", () => {
    // A proto member's definition already lives in the proto; a literal `node: undefined`
    // key would make the record look like an agent-added node with a missing definition.
    const w = emptyWorking();
    const node = stmt();
    recordProof(w, makeCore([node]), { id: node.id, snapshotOf: node, proofTex: "P" });

    expect("node" in w.solved["lem:a"]).toBe(false);
    expect("owner" in w.solved["lem:a"]).toBe(false);
    expect("partial" in w.solved["lem:a"]).toBe(false);
  });

  it("snapshots the statement given by snapshotOf, not the stored node", () => {
    // Validity is measured against the statement as written, while the catalog can
    // hold a re-opened form of the same node.
    const w = emptyWorking();
    const written = stmt({ statement: "AS-WRITTEN" });
    const reopened = stmt({ statement: "AS-WRITTEN", status: "to-prove", proof_tex: undefined });
    recordProof(w, makeCore([written]), {
      id: "lem:a",
      snapshotOf: written,
      proofTex: "partial",
      node: reopened,
      partial: true,
    });

    expect(w.solved["lem:a"].snapshot.stmt).toBe("AS-WRITTEN");
    expect(w.solved["lem:a"].node?.status).toBe("to-prove");
    expect(w.solved["lem:a"].partial).toBe(true);
  });

  it("snapshots against proto, so an in-flight core-only definition does not leak in", () => {
    // The hazard the four hand-written loops disagreed about: two snapshotted against
    // the assembled core, which holds definitions the proto has not accepted yet.
    const node = stmt({ depends_on: ["def:x"] });
    const proto = makeCore([node], [], []);
    const core = makeCore([node], [], [{ id: "def:x", construction: "IN-FLIGHT" }]);
    const w = emptyWorking();

    recordProof(w, proto, { id: "lem:a", snapshotOf: node, proofTex: "P", node });

    expect(w.solved["lem:a"].snapshot.defs).toEqual({});
    expect(computeValidNodes(w, proto).has("lem:a")).toBe(true);
    void core;
  });
});

describe("refreshSnapshots", () => {
  it("re-snapshots after a statement rewrite and reports what moved", () => {
    const before = stmt({ statement: "OLD" });
    const proto = makeCore([before]);
    const w = emptyWorking();
    recordProof(w, proto, { id: "lem:a", snapshotOf: before, proofTex: "P", node: before });

    const after = stmt({ statement: "NEW" });
    const moved = refreshSnapshots(w, makeCore([after]), makeCore([after]));

    expect(moved).toEqual(["lem:a"]);
    expect(w.solved["lem:a"].snapshot.stmt).toBe("NEW");
    expect(w.solved["lem:a"].node?.statement).toBe("NEW");
  });

  it("reports nothing when no snapshot actually changed", () => {
    const node = stmt();
    const proto = makeCore([node]);
    const w = emptyWorking();
    recordProof(w, proto, { id: "lem:a", snapshotOf: node, proofTex: "P", node });

    expect(refreshSnapshots(w, proto, proto)).toEqual([]);
  });

  it("leaves open obligations alone under skipPartial", () => {
    // A partial's snapshot describes what the agent was asked to extend; refreshing it
    // would quietly retarget the obligation.
    const before = stmt({ statement: "OLD" });
    const proto = makeCore([before]);
    const w = emptyWorking();
    recordProof(w, proto, { id: "lem:a", snapshotOf: before, proofTex: "partial", node: before, partial: true });

    const after = makeCore([stmt({ statement: "NEW" })]);
    expect(refreshSnapshots(w, after, after, { skipPartial: true })).toEqual([]);
    expect(w.solved["lem:a"].snapshot.stmt).toBe("OLD");

    expect(refreshSnapshots(w, after, after)).toEqual(["lem:a"]);
    expect(w.solved["lem:a"].snapshot.stmt).toBe("NEW");
  });

  it("ignores records whose id is absent from the core", () => {
    const node = stmt();
    const w = emptyWorking();
    recordProof(w, makeCore([node]), { id: "lem:a", snapshotOf: node, proofTex: "P", node });

    expect(refreshSnapshots(w, makeCore([]), makeCore([]))).toEqual([]);
    expect(w.solved["lem:a"].proof_tex).toBe("P");
  });

  it("does not invent a node key for a record that had none", () => {
    const node = stmt();
    const proto = makeCore([node]);
    const w = emptyWorking();
    recordProof(w, proto, { id: "lem:a", snapshotOf: node, proofTex: "P" });

    refreshSnapshots(w, proto, proto);
    expect("node" in w.solved["lem:a"]).toBe(false);
  });
});
