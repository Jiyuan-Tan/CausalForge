import { describe, it, expect } from "vitest";
import { recordProof } from "../../src/discovery/working_writer.js";
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
    expect(w.solved["lem:a"].node?.proof_tex).toBe("P");
    expect(w.solved["lem:a"].owner).toBe("unit-1");
    expect(w.solved["lem:a"].snapshot.stmt).toBe("S");
  });

  it("omits node and an absent owner rather than storing undefined for a frozen proto member", () => {
    // A proto member's definition already lives in the proto; a literal `node: undefined`
    // key would make the record look like an agent-added node with a missing definition.
    const w = emptyWorking();
    const node = stmt();
    recordProof(w, makeCore([node]), { id: node.id, snapshotOf: node, proofTex: "P" });

    expect("node" in w.solved["lem:a"]).toBe(false);
    expect("owner" in w.solved["lem:a"]).toBe(false);
    expect("partial" in w.solved["lem:a"]).toBe(false);
  });

  it("preserves a durable frozen-overlay owner across proof refreshes and permits an explicit transition", () => {
    const w = emptyWorking();
    const node = stmt();
    const proto = makeCore([node]);

    recordProof(w, proto, {
      id: node.id,
      snapshotOf: node,
      proofTex: "P1",
      owner: "thm:directed-root",
    });
    expect(w.solved[node.id]).toMatchObject({ proof_tex: "P1", owner: "thm:directed-root" });
    expect("node" in w.solved[node.id]).toBe(false);

    // The merge/apply refresh path normally omits owner for a frozen member. It must
    // not erase the directed ownership receipt when replacing the proof record.
    recordProof(w, proto, { id: node.id, snapshotOf: node, proofTex: "P2" });
    expect(w.solved[node.id]).toMatchObject({ proof_tex: "P2", owner: "thm:directed-root" });
    expect("node" in w.solved[node.id]).toBe(false);

    // An explicit semantic reassignment remains possible and wins deterministically.
    recordProof(w, proto, {
      id: node.id,
      snapshotOf: node,
      proofTex: "P3",
      owner: "thm:new-root",
    });
    expect(w.solved[node.id]).toMatchObject({ proof_tex: "P3", owner: "thm:new-root" });
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
    expect(w.solved["lem:a"].node?.proof_tex).toBeUndefined();
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

describe("recordProof wired-closure snapshots (Batch B — refreshSnapshots is retired)", () => {
  it("includes defs/assumptions the PROOF TEXT cites in the snapshot closure", () => {
    // The old flow wired the workspace core, then re-synced snapshots from it.
    // Now the wire happens at the write: a def cited only in the proof body is
    // part of the validity basis, so editing it re-opens the node.
    const node = stmt({ depends_on: [] });
    const proto = makeCore([node], [], [{ id: "def:d", name: "D", construction: "X = 1" }]);
    const w = emptyWorking();
    recordProof(w, proto, { id: "lem:a", snapshotOf: node, proofTex: "By def:d, done.", node });

    expect(w.solved["lem:a"].snapshot.defs).toEqual({ "def:d": "X = 1" });
    expect(w.solved["lem:a"].snapshot.depends_on).toContain("def:d");
    // ...and the record reads STALE once that def's construction moves.
    const edited = makeCore([node], [], [{ id: "def:d", name: "D", construction: "X = 2" }]);
    expect(computeValidNodes(w, edited).has("lem:a")).toBe(false);
    expect(computeValidNodes(w, proto).has("lem:a")).toBe(true);
  });

  it("a prose-cited helper's statement change invalidates the citing record (audit BB1)", () => {
    // Pre-Batch-B this propagation flowed through the refresh-synced wired node;
    // now the snapshot's cited closure feeds computeValidNodes directly.
    const helper = stmt({ id: "lem:b", statement: "HELPER-V1" });
    const main = stmt({ id: "thm:a", kind: "theorem", depends_on: [] });
    const proto = makeCore([main, helper]);
    const w = emptyWorking();
    recordProof(w, proto, { id: "lem:b", snapshotOf: helper, proofTex: "P", node: helper });
    recordProof(w, proto, { id: "thm:a", snapshotOf: main, proofTex: "By lem:b, done.", node: main });
    expect(computeValidNodes(w, proto).has("thm:a")).toBe(true);
    const edited = makeCore([main, { ...helper, statement: "HELPER-V2" } as CoreStatement]);
    expect(computeValidNodes(w, edited).has("lem:b")).toBe(false);
    expect(computeValidNodes(w, edited).has("thm:a")).toBe(false); // propagated
  });

  it("never adds a self-reference to the closure", () => {
    const node = stmt();
    const proto = makeCore([node]);
    const w = emptyWorking();
    recordProof(w, proto, { id: "lem:a", snapshotOf: node, proofTex: "Recall lem:a itself.", node });
    expect(w.solved["lem:a"].snapshot.depends_on).not.toContain("lem:a");
  });

  it("does not invent a node key for a record that had none", () => {
    const node = stmt();
    const proto = makeCore([node]);
    const w = emptyWorking();
    recordProof(w, proto, { id: "lem:a", snapshotOf: node, proofTex: "P" });
    expect("node" in w.solved["lem:a"]).toBe(false);
  });
});
