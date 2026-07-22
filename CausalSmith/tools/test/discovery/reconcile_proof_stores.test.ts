import { describe, it, expect } from "vitest";
import { computeValidNodes } from "../../src/discovery/stages/d0_working.js";
import { reconcileProofStores } from "../../src/discovery/core/coherence.js";
import type { Core } from "../../src/discovery/core/schema.js";
import type { WorkingState } from "../../src/discovery/stages/d0_working.js";

/** Minimal proto/core pair. `stmts` are the assembled-core statements. */
function makeCore(stmts: Array<Record<string, unknown>>, assumptions: Array<Record<string, unknown>> = []): Core {
  return {
    title: "t",
    assumptions: assumptions as never,
    definitions: [],
    statements: stmts as never,
    bibliography: [],
  } as unknown as Core;
}

function emptyWorking(): WorkingState {
  return { round: 1, solved: {}, resolved_oeqs: {} } as WorkingState;
}

describe("reconcileProofStores", () => {
  it("recovers a proved core node that has no working record", () => {
    // The round-51 shape: a TERMINAL theorem lands in core.json with its proof but
    // never reaches working.solved, so the next round's carry (which reads
    // prev.solved) would drop it entirely.
    const core = makeCore([
      { id: "thm:terminal", kind: "theorem", status: "proved", statement: "S", depends_on: [], proof_tex: "PROOF" },
    ]);
    const working = emptyWorking();

    const recovered = reconcileProofStores(core, core, working);

    expect(recovered).toEqual(["thm:terminal"]);
    expect(working.solved["thm:terminal"].proof_tex).toBe("PROOF");
    expect(working.solved["thm:terminal"].node?.status).toBe("proved");
  });

  it("stores a snapshot the validity computation accepts, so the recovered proof is not re-opened", () => {
    // A snapshot taken against the assembled core rather than the frozen proto would
    // read as permanently stale and force a re-proof every round — a silent loop
    // rather than a loud fault. The two stores are given DIVERGENT text for the
    // assumption the node depends on, so the wrong choice is observable.
    const node = {
      id: "thm:terminal",
      kind: "theorem",
      status: "proved",
      statement: "S",
      depends_on: ["ass:a"],
    };
    const proto = makeCore([node], [{ id: "ass:a", condition: "PROTO-CONDITION" }]);
    const core = makeCore([{ ...node, proof_tex: "PROOF" }], [{ id: "ass:a", condition: "CORE-CONDITION" }]);
    const working = emptyWorking();

    reconcileProofStores(core, proto, working);

    expect(working.solved["thm:terminal"].snapshot.assumptions).toEqual({ "ass:a": "PROTO-CONDITION" });
    expect(computeValidNodes(working, proto).has("thm:terminal")).toBe(true);
  });

  it("leaves already-recorded nodes untouched", () => {
    const core = makeCore([
      { id: "lem:a", kind: "lemma", status: "proved", statement: "S", depends_on: [], proof_tex: "NEW" },
    ]);
    const working = emptyWorking();
    working.solved["lem:a"] = { node: { id: "lem:a" } as never, proof_tex: "ORIGINAL", snapshot: {} as never };

    expect(reconcileProofStores(core, core, working)).toEqual([]);
    expect(working.solved["lem:a"].proof_tex).toBe("ORIGINAL");
  });

  it("ignores core statements that carry no proof", () => {
    // Open questions and unproved targets legitimately have no working record.
    const core = makeCore([
      { id: "oeq:open", kind: "openendedquestion", status: "open", statement: "S", depends_on: [] },
      { id: "lem:cited", kind: "lemma", status: "cited", statement: "S", depends_on: [] },
    ]);
    const working = emptyWorking();

    expect(reconcileProofStores(core, core, working)).toEqual([]);
    expect(Object.keys(working.solved)).toEqual([]);
  });

  it("throws when a resolved OEQ names a theorem present in neither store", () => {
    const core = makeCore([]);
    const working = emptyWorking();
    working.resolved_oeqs = {
      "oeq:bounded-count-diameter": {
        theorem_id: "thm:bounded-count-diameter-obstruction",
        source_fingerprint: "fp",
      },
    };

    expect(() => reconcileProofStores(core, core, working)).toThrow(
      /oeq:bounded-count-diameter->thm:bounded-count-diameter-obstruction/,
    );
  });

  it("accepts a resolved OEQ whose theorem is recovered by the same pass", () => {
    // The real round-51 state: the resolution pointer survived and the theorem was
    // in the core, so the repair must satisfy the invariant rather than trip it.
    const core = makeCore([
      { id: "thm:answer", kind: "theorem", status: "proved", statement: "S", depends_on: [], proof_tex: "P" },
    ]);
    const working = emptyWorking();
    working.resolved_oeqs = { "oeq:q": { theorem_id: "thm:answer", source_fingerprint: "fp" } };

    expect(() => reconcileProofStores(core, core, working)).not.toThrow();
    expect(working.solved["thm:answer"]).toBeDefined();
  });

  it("tolerates the legacy string form of a resolution entry", () => {
    const working = emptyWorking();
    working.resolved_oeqs = { "oeq:q": "thm:missing" } as never;

    expect(() => reconcileProofStores(makeCore([]), makeCore([]), working)).toThrow(/thm:missing/);
  });
});
