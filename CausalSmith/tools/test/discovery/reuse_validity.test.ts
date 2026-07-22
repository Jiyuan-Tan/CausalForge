// Proof-reuse validity. Each defect here let a round REUSE a proof it should have
// re-derived (silent corruption) or re-derive one it should have kept (wasted work).
// From the D-stage audit triage, 2026-07-20.

import { describe, it, expect } from "vitest";
import { computeValidNodes, pruneOrphanLemmas, snapshotMember, type WorkingState } from "../../src/discovery/stages/d0_working.js";
import type { Core, CoreStatement } from "../../src/discovery/core/schema.js";

const proto = (statements: CoreStatement[]): Core => ({
  qid: "q", symbols: [], assumptions: [], definitions: [], statements,
  target_estimand: "tau", bibliography: [],
} as never);

const st = (over: Partial<CoreStatement> = {}): CoreStatement => ({
  id: "thm:a", kind: "theorem", statement: "S", depends_on: [], status: "proved",
  proof_tex: "QED.", ...over,
} as CoreStatement);

const solved = (p: Core, s: CoreStatement, over: Record<string, unknown> = {}) => ({
  proof_tex: "QED.", snapshot: snapshotMember(p, s), ...over,
});

describe("a settled record with NO proof is not reusable", () => {
  it("marks an empty-proof record stale", () => {
    const P = proto([st()]);
    const prev: WorkingState = { round: 1, solved: { "thm:a": solved(P, P.statements[0], { proof_tex: "" }) } };
    expect(computeValidNodes(prev, P).has("thm:a")).toBe(false);
  });

  it("still reuses a record with a real proof", () => {
    const P = proto([st()]);
    const prev: WorkingState = { round: 1, solved: { "thm:a": solved(P, P.statements[0]) } };
    expect(computeValidNodes(prev, P).has("thm:a")).toBe(true);
  });

  it("EXEMPTS cited — its justification is the citation, so it carries no proof", () => {
    const cited = st({ id: "lem:c", kind: "lemma", status: "cited", proof_tex: undefined,
      source: { cite: "K", locator: "Thm 1" } } as never);
    const P = proto([cited]);
    const prev: WorkingState = { round: 1, solved: { "lem:c": solved(P, cited, { proof_tex: "" }) } };
    expect(computeValidNodes(prev, P).has("lem:c")).toBe(true);
  });
});

describe("a dependency that VANISHED invalidates its consumer", () => {
  it("marks a node stale when a statement dependency is in neither store", () => {
    // Staleness propagation only reaches deps still present, so a DELETED dependency
    // silently left its consumer reusable -- a proof resting on nothing.
    const P = proto([st({ depends_on: ["lem:deleted"] })]);
    const prev: WorkingState = { round: 1, solved: { "thm:a": solved(P, P.statements[0]) } };
    expect(computeValidNodes(prev, P).has("thm:a")).toBe(false);
  });

  it("does not penalise a def:/ass: dependency, which snapshots already cover", () => {
    const P = proto([st({ depends_on: ["ass:overlap", "def:env"] })]);
    const prev: WorkingState = { round: 1, solved: { "thm:a": solved(P, P.statements[0]) } };
    expect(computeValidNodes(prev, P).has("thm:a")).toBe(true);
  });
});

describe("the FROZEN proto outranks a same-id agent record", () => {
  it("marks an agent record stale when its claim contradicts the proto", () => {
    // The agent record used to WIN the id lookup, so its proof was validated against the
    // agent's claim rather than the frozen one it must discharge.
    const P = proto([st({ id: "thm:a", statement: "THE FROZEN CLAIM" })]);
    const agent = st({ id: "thm:a", statement: "A DIFFERENT CLAIM" });
    const prev: WorkingState = {
      round: 1,
      solved: { "thm:a": { proof_tex: "QED.", snapshot: snapshotMember(P, agent), node: agent } },
    };
    expect(computeValidNodes(prev, P).has("thm:a")).toBe(false);
  });

  it("marks it stale when only the DEPENDENCIES differ", () => {
    const P = proto([st({ id: "thm:a", statement: "SAME", depends_on: ["ass:overlap"] })]);
    const agent = st({ id: "thm:a", statement: "SAME", depends_on: ["ass:other"] });
    const prev: WorkingState = {
      round: 1,
      solved: { "thm:a": { proof_tex: "QED.", snapshot: snapshotMember(P, agent), node: agent } },
    };
    expect(computeValidNodes(prev, P).has("thm:a")).toBe(false);
  });

  it("marks it stale when only the KIND differs — which the snapshot does not record", () => {
    // Pins the collision check INDEPENDENTLY of the map-order fix. `snapshotMember`
    // records statement/deps/defs/assumptions but NOT kind, so a kind-only divergence is
    // invisible to the snapshot comparison and only this check can catch it.
    const P = proto([st({ id: "thm:a", statement: "SAME", kind: "theorem" })]);
    const agent = st({ id: "thm:a", statement: "SAME", kind: "lemma" });
    const prev: WorkingState = {
      round: 1,
      solved: { "thm:a": { proof_tex: "QED.", snapshot: snapshotMember(P, agent), node: agent } },
    };
    expect(computeValidNodes(prev, P).has("thm:a")).toBe(false);
  });

  it("keeps an agent record whose claim agrees with the proto", () => {
    const P = proto([st({ id: "thm:a", statement: "SAME CLAIM" })]);
    const agent = st({ id: "thm:a", statement: "SAME CLAIM" });
    const prev: WorkingState = {
      round: 1,
      solved: { "thm:a": { proof_tex: "QED.", snapshot: snapshotMember(P, agent), node: agent } },
    };
    expect(computeValidNodes(prev, P).has("thm:a")).toBe(true);
  });
});

describe("orphan pruning reconciles divergent stores through union reachability", () => {
  // A working-only consumer must protect its helper even though the derived core omitted
  // that consumer. Conversely, a working-only lemma with no depender now has a cleanup
  // path instead of making every future prune refuse to run.
  const lemma = st({ id: "lem:helper", kind: "lemma", statement: "H" });

  it("keeps a helper reached from a working-only consumer", () => {
    const P = proto([lemma]);
    const core_ = proto([lemma]);            // core is MISSING the consumer thm:consumer
    const working: WorkingState = {
      round: 1,
      solved: {
        "lem:helper": { proof_tex: "QED.", snapshot: snapshotMember(P, lemma), node: lemma },
        // agent-authored consumer, carried but never assembled into core
        "thm:consumer": {
          proof_tex: "QED.", snapshot: snapshotMember(P, lemma),
          node: st({ id: "thm:consumer", depends_on: ["lem:helper"] }),
        },
      },
    };
    const res = pruneOrphanLemmas(core_, working, P);
    expect(res.pruned, "the working-only consumer keeps its helper reachable").toEqual([]);
    expect(Object.keys(working.solved), "the authoritative record must survive").toContain("lem:helper");
  });

  it("prunes a genuinely orphaned working-only partial lemma", () => {
    const P = proto([]);
    const core_ = proto([]);
    const orphan = st({ id: "lem:abandoned-route", kind: "lemma", statement: "H" });
    const working: WorkingState = {
      round: 8,
      solved: {
        "lem:abandoned-route": {
          proof_tex: "Thirteen kilobytes of abandoned partial work.",
          snapshot: snapshotMember(P, orphan),
          node: orphan,
          partial: true,
        },
      },
    };

    const res = pruneOrphanLemmas(core_, working, P);
    expect(res.pruned).toEqual(["lem:abandoned-route"]);
    expect(working.solved["lem:abandoned-route"]).toBeUndefined();
  });

  it("still prunes a genuine orphan when the stores agree", () => {
    const P = proto([lemma]);
    const core_ = proto([lemma]);            // a lemma reachable from no non-lemma claim
    const working: WorkingState = {
      round: 1,
      solved: { "lem:helper": { proof_tex: "QED.", snapshot: snapshotMember(P, lemma), node: lemma } },
    };
    const res = pruneOrphanLemmas(core_, working, P);
    expect(res.pruned).toEqual(["lem:helper"]);
  });
});

describe("dependency-only rewires do NOT invalidate reuse (content basis rule)", () => {
  // "dep change alone triggers re-derivation via snapshot invalidation" cost one run
  // >=3 re-derivations of a byte-identical flagship theorem. Validity now rests on the
  // statement text plus the CONTENT the proof was solved against, not the edge list.
  const protoWith = (statements: CoreStatement[], defs: Array<{ id: string; construction: string }> = [],
    assumptions: Array<{ id: string; condition: string }> = []): Core => ({
    qid: "q", symbols: [], assumptions, definitions: defs, statements,
    target_estimand: "tau", bibliography: [],
  } as never);

  it("keeps a proof when an edge to an UNCHANGED def is added", () => {
    const before = protoWith([st({ depends_on: [] })], [{ id: "def:env", construction: "U = a" }]);
    const after = protoWith([st({ depends_on: ["def:env"] })], [{ id: "def:env", construction: "U = a" }]);
    const prev: WorkingState = { round: 1, solved: { "thm:a": solved(before, before.statements[0]) } };
    expect(computeValidNodes(prev, after).has("thm:a")).toBe(true);
  });

  it("keeps a proof when an edge to an UNCHANGED def is removed", () => {
    const before = protoWith([st({ depends_on: ["def:env"] })], [{ id: "def:env", construction: "U = a" }]);
    const after = protoWith([st({ depends_on: [] })], [{ id: "def:env", construction: "U = a" }]);
    const prev: WorkingState = { round: 1, solved: { "thm:a": solved(before, before.statements[0]) } };
    expect(computeValidNodes(prev, after).has("thm:a")).toBe(true);
  });

  it("still invalidates when a def in the STORED closure changed — even with its edge removed", () => {
    // The removed-AND-edited case: the proof was solved against the old construction, so
    // dropping the edge must not launder the content change past the reuse check.
    const before = protoWith([st({ depends_on: ["def:env"] })], [{ id: "def:env", construction: "U = a" }]);
    const after = protoWith([st({ depends_on: [] })], [{ id: "def:env", construction: "U = CHANGED" }]);
    const prev: WorkingState = { round: 1, solved: { "thm:a": solved(before, before.statements[0]) } };
    expect(computeValidNodes(prev, after).has("thm:a")).toBe(false);
  });

  it("still invalidates when a def in the stored closure was DELETED", () => {
    const before = protoWith([st({ depends_on: ["def:env"] })], [{ id: "def:env", construction: "U = a" }]);
    const after = protoWith([st({ depends_on: [] })], []);
    const prev: WorkingState = { round: 1, solved: { "thm:a": solved(before, before.statements[0]) } };
    expect(computeValidNodes(prev, after).has("thm:a")).toBe(false);
  });

  it("still invalidates when a stored-closure ASSUMPTION's condition changed", () => {
    const before = protoWith([st({ depends_on: ["ass:overlap"] })], [], [{ id: "ass:overlap", condition: "e in (0,1)" }]);
    const after = protoWith([st({ depends_on: ["ass:overlap"] })], [], [{ id: "ass:overlap", condition: "e in (c,1-c)" }]);
    const prev: WorkingState = { round: 1, solved: { "thm:a": solved(before, before.statements[0]) } };
    expect(computeValidNodes(prev, after).has("thm:a")).toBe(false);
  });
});

describe("round-5: a reopened frozen CITED node keeps its citation", () => {
  // Two audit rounds disagreed here. Round 3 said a reopened cited node must shed `source`
  // (the schema ties cited <=> source); round 5 said dropping it destroys the only durable
  // locator. The carried-node branch documents the resolution: a cited node awaiting
  // revalidation stays a schema-valid cited leaf, and `partial` on its working record
  // carries the invalidation. Round 3's advice applied to a different context -- pushing
  // into the CORE, where `partial` is not representable.
  it("keeps status cited and source, and marks the cursor partial", async () => {
    const { applyProposedChanges } = await import("../../src/discovery/stages/d0_apply.js");
    const { saveWorkingState, loadWorkingState } = await import("../../src/discovery/stages/d0_working.js");
    const { createDStageHarness } = await import("./d_stage_harness.js");

    const CITED = {
      id: "lem:cited", kind: "lemma", statement: "OLD", depends_on: [],
      status: "cited", source: { cite: "R1983", locator: "Thm 1" },
    };
    const P = {
      qid: "stat_citedreopen", specialization: "v1", cluster: "stat",
      symbols: [{ name: "tau", type: "causal_parameter", def: "E[Y(1)-Y(0)]" }],
      assumptions: [{ id: "ass:overlap", kind: "support", condition: "c", free_symbols: [], standard: { name: "o", cite: "R1983" } }],
      definitions: [{ id: "def:env", name: "U", construction: "U = a", inputs: ["a"] }],
      statements: [CITED], target_estimand: "tau", bibliography: [{ key: "R1983" }],
    };
    const h = await createDStageHarness({ qid: "stat_citedreopen", specialization: "v1", proto: P });
    try {
      const proto = await h.readProto();
      await saveWorkingState(h.ctx(), {
        round: 1,
        solved: { "lem:cited": { proof_tex: "", snapshot: snapshotMember(proto, proto.statements[0]) } },
        resolved_oeqs: {},
        proposals: {
          statements: [{ id: "lem:cited", current: "OLD", proposed: "NEW", reason: "narrow", direction: "narrow" }],
          definitions: [], assumptions: [], coreEdits: [], proofs: [],
        },
      } as never);

      await applyProposedChanges({ ctx: h.ctx() });

      const after = await h.readProto();
      const node = after.statements.find((s: { id: string }) => s.id === "lem:cited")!;
      expect(node.status, "a cited leaf stays cited — schema ties cited <=> source").toBe("cited");
      expect(node.source, "the locator is the ONLY durable copy; losing it forces a re-proof").toBeDefined();

      const w = await loadWorkingState(h.ctx());
      const rec = (w as never as { solved: Record<string, { partial?: boolean }> }).solved["lem:cited"];
      expect(rec?.partial, "`partial` carries the invalidation").toBe(true);
    } finally { await h.dispose(); }
  }, 30000);
});
