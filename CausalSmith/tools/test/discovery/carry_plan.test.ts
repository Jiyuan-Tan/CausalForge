import { describe, it, expect } from "vitest";
import { planCarry } from "../../src/discovery/carry_plan.js";
import type { CarryInputs } from "../../src/discovery/carry_plan.js";
import type { WorkingState, SolvedMember } from "../../src/discovery/stages/d0_working.js";

const agentNode = (id: string, owner?: string): SolvedMember =>
  ({
    proof_tex: "P",
    snapshot: {} as never,
    node: { id, kind: "lemma", status: "proved", statement: "S", depends_on: [] } as never,
    ...(owner ? { owner } : {}),
  }) as SolvedMember;

const protoRec = (): SolvedMember => ({ proof_tex: "P", snapshot: {} as never }) as SolvedMember;

function plan(over: Partial<CarryInputs> & { solved: Record<string, SolvedMember> }) {
  const { solved, ...rest } = over;
  return planCarry({
    prev: { round: 1, solved } as WorkingState,
    protoIds: new Set(),
    validIds: new Set(),
    resolutionTheoremIds: new Set(),
    persistedOeqReplacements: new Map(),
    ...rest,
  });
}

describe("planCarry — agent-authored nodes", () => {
  it("carries a valid agent node", () => {
    const p = plan({ solved: { "lem:a": agentNode("lem:a") }, validIds: new Set(["lem:a"]) });
    expect(p.verdicts.get("lem:a")).toEqual({ fate: "carried", as: "agent-node" });
  });

  it("re-derives a stale agent node rather than dropping its definition", () => {
    // `solved` is the ONLY place an agent-authored statement is defined; dropping the
    // record would delete the statement, not just its proof.
    const p = plan({ solved: { "lem:a": agentNode("lem:a") } });
    expect(p.verdicts.get("lem:a")).toMatchObject({ fate: "re-derive", as: "agent-node" });
  });

  it("treats a stale node that shares a frozen id as a proto member", () => {
    // The proto still defines the statement, so it is not agent-catalog debt.
    const p = plan({ solved: { "lem:a": agentNode("lem:a") }, protoIds: new Set(["lem:a"]) });
    expect(p.verdicts.get("lem:a")).toMatchObject({ fate: "re-derive", as: "proto-member" });
  });
});

describe("planCarry — frozen proto members", () => {
  it("carries a valid proto member", () => {
    const p = plan({
      solved: { "thm:x": protoRec() },
      protoIds: new Set(["thm:x"]),
      validIds: new Set(["thm:x"]),
    });
    expect(p.verdicts.get("thm:x")).toEqual({ fate: "carried", as: "proto-member" });
  });

  it("re-derives a stale proto member", () => {
    const p = plan({ solved: { "thm:x": protoRec() }, protoIds: new Set(["thm:x"]) });
    expect(p.verdicts.get("thm:x")).toMatchObject({ fate: "re-derive", as: "proto-member" });
  });

  it("drops a record that defines no statement and names no frozen node", () => {
    const p = plan({ solved: { "lem:orphan": protoRec() } });
    expect(p.verdicts.get("lem:orphan")).toMatchObject({ fate: "dropped" });
  });
});

describe("planCarry — OEQ answer theorems", () => {
  const solved = { "thm:answer": agentNode("thm:answer", "oeq:q") };
  const resolutionTheoremIds = new Set(["thm:answer"]);

  it("carries the answer when the mapping persisted and the proof is valid", () => {
    const p = plan({
      solved,
      resolutionTheoremIds,
      validIds: new Set(["thm:answer"]),
      persistedOeqReplacements: new Map([["oeq:q", "thm:answer"]]),
    });
    expect(p.verdicts.get("thm:answer")).toEqual({ fate: "carried", as: "oeq-answer" });
  });

  it("uses the authoritative theorem id, not provenance owner, to recognize a persisted answer", () => {
    const noOwner = { "thm:answer": agentNode("thm:answer") };
    const p = plan({
      solved: noOwner,
      resolutionTheoremIds,
      validIds: new Set(["thm:answer"]),
      persistedOeqReplacements: new Map([["oeq:q", "thm:answer"]]),
    });
    expect(p.verdicts.get("thm:answer")).toEqual({ fate: "carried", as: "oeq-answer" });
  });

  it("does not retain an old answer merely because its owner source was remapped", () => {
    const p = plan({
      solved,
      resolutionTheoremIds,
      validIds: new Set(["thm:answer"]),
      persistedOeqReplacements: new Map([["oeq:q", "thm:new-answer"]]),
    });
    expect(p.verdicts.get("thm:answer")).toMatchObject({ fate: "dropped" });
  });

  it("DROPS the answer when the source->answer mapping did not persist", () => {
    // This is the gap that made a finished theorem vanish without a trace: the node is
    // governed only by its mapping, so it is excluded from BOTH the ordinary carry and
    // the stale-recovery path, and previously fell through with no record at all.
    const p = plan({ solved, resolutionTheoremIds, validIds: new Set(["thm:answer"]) });
    const v = p.verdicts.get("thm:answer")!;
    expect(v.fate).toBe("dropped");
    expect(p.explain("thm:answer")).toMatch(/DROPPED/);
    expect(p.explain("thm:answer")).toMatch(/mapping did not persist/);
  });

  it("RE-DERIVES a mapped-but-stale answer under the same id instead of dropping it", () => {
    // The mapping surviving means the QUESTION is unchanged, so this is still its answer
    // — only the proof needs redoing. Dropping it here sent the OEQ back to the frontier
    // to be re-answered under a NEW id, costing a full solve round and churning every
    // downstream reference; and because answer theorems were excluded from BOTH the
    // ordinary carry and stale recovery, the node vanished with its statement definition.
    const p = plan({
      solved,
      resolutionTheoremIds,
      persistedOeqReplacements: new Map([["oeq:q", "thm:answer"]]),
    });
    expect(p.verdicts.get("thm:answer")).toMatchObject({ fate: "re-derive", as: "oeq-answer" });
    expect(p.explain("thm:answer")).toMatch(/re-prove under the same id/);
  });

  it("still DROPS when the fingerprint moved, since the question itself changed", () => {
    // The one case where the old answer genuinely may no longer answer the question.
    const p = plan({ solved, resolutionTheoremIds });
    expect(p.verdicts.get("thm:answer")).toMatchObject({ fate: "dropped" });
    expect(p.explain("thm:answer")).toMatch(/question itself moved/);
  });
});

describe("planCarry — reporting", () => {
  it("groups ids by fate", () => {
    const p = plan({
      solved: {
        "lem:ok": agentNode("lem:ok"),
        "lem:stale": agentNode("lem:stale"),
        "lem:orphan": protoRec(),
      },
      validIds: new Set(["lem:ok"]),
    });
    expect(p.ids("carried")).toEqual(["lem:ok"]);
    expect(p.ids("re-derive")).toEqual(["lem:stale"]);
    expect(p.ids("dropped")).toEqual(["lem:orphan"]);
  });

  it("explains an id it never saw instead of throwing", () => {
    expect(plan({ solved: {} }).explain("lem:ghost")).toMatch(/absent from the previous round/);
  });

  it("returns an empty plan for a first round with no prior state", () => {
    const p = planCarry({
      prev: null,
      protoIds: new Set(),
      validIds: new Set(),
      resolutionTheoremIds: new Set(),
      persistedOeqReplacements: new Map(),
    });
    expect(p.verdicts.size).toBe(0);
  });
});

describe("planCarry — equivalence with the predicates it replaced", () => {
  it("matches the original branch conditions on every combination of their inputs", () => {
    // The extraction must not change which nodes survive. These are the two original
    // `if` conditions from `runStage0Solve`, transcribed verbatim, checked against the
    // plan-driven replacements over all 2^5 input combinations.
    //
    // The frozen-member carry is deliberately absent: its predicate OVERLAPS these two
    // rather than partitioning with them (a node can be both a frozen member and an OEQ
    // answer), so it still reads `validIds` directly. An earlier attempt to route it
    // through the plan silently changed behaviour in exactly that overlap.
    for (const hasNode of [true, false])
      for (const inProto of [true, false])
        for (const valid of [true, false])
          for (const isResThm of [true, false])
            for (const mappingHeld of [true, false]) {
              const id = "n";
              const rec = {
                proof_tex: "P",
                snapshot: {},
                ...(hasNode ? { node: { id, depends_on: [] } } : {}),
                owner: "oeq:q",
              } as never as SolvedMember;
              const p = planCarry({
                prev: { round: 1, solved: { [id]: rec } } as WorkingState,
                protoIds: new Set(inProto ? [id] : []),
                validIds: new Set(valid ? [id] : []),
                resolutionTheoremIds: new Set(isResThm ? [id] : []),
                persistedOeqReplacements: new Map(mappingHeld ? [["oeq:q", id]] : []),
              });
              const v = p.verdicts.get(id)!;
              const label = `node=${hasNode} proto=${inProto} valid=${valid} res=${isResThm} mapped=${mappingHeld}`;

              const origCarryAgent = hasNode && valid && (!isResThm || mappingHeld);
              const newCarryAgent = hasNode && v.fate === "carried" && v.as !== "proto-member";
              expect(newCarryAgent, `agent carry @ ${label}`).toBe(origCarryAgent);

              // `stage0_solve` now accepts BOTH `agent-node` and `oeq-answer` here, so the
              // test must model that or it silently stops describing the real code.
              const origStale = hasNode && !inProto && !valid && !isResThm;
              const newStale =
                hasNode && v.fate === "re-derive" && (v.as === "agent-node" || v.as === "oeq-answer");
              // ONE INTENTIONAL DIVERGENCE from the original predicates: a still-mapped but
              // stale OEQ answer is now RECOVERED under its own id rather than dropped.
              // Everything else must still match exactly.
              // `hasNode` is part of the guard because stale recovery requires a stored
              // statement. (mappingHeld ALSO implies a node in reality — the mapping is only
              // built when `theorem?.node` exists — so the `!hasNode && mappingHeld` cells
              // below are unreachable combinations this exhaustive loop happens to enumerate.)
              const intendedChange = hasNode && isResThm && mappingHeld && !valid;
              if (intendedChange) {
                expect(newStale, `intended recovery @ ${label}`).toBe(true);
                expect(origStale, `original dropped it @ ${label}`).toBe(false);
              } else {
                expect(newStale, `stale recovery @ ${label}`).toBe(origStale);
              }
            }
  });
});
