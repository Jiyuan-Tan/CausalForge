// Do the invariants actually FIRE?
//
// An assertion nobody has seen fail is not evidence — it is an untested claim wearing a
// check's clothing. Several of these guard states the current code no longer reaches
// (that is the point: they are regression guards), so the soak scenarios alone cannot
// demonstrate they work. Each case below feeds the detector a deliberately violating
// input and requires it to report.
//
// This exercises the RUNTIME detector, the same one `commitRound` runs on every real
// round — so passing here means a live run would also have caught the fault.
// Every case is the shape of a fault that actually occurred on 2026-07-19.

import { describe, it, expect } from "vitest";
import { violationsOf } from "./d_stage_invariants.js";
import type { RoundInvariantInput } from "../../src/discovery/core/coherence.js";
import { snapshotMember } from "../../src/discovery/stages/d0_working.js";
import type { Core, CoreStatement } from "../../src/discovery/core/schema.js";
import type { WorkingState } from "../../src/discovery/stages/d0_working.js";

const core = (statements: Array<Record<string, unknown>>, assumptions: Array<Record<string, unknown>> = []): Core =>
  ({ title: "t", assumptions, definitions: [], bibliography: [], statements }) as unknown as Core;

const stmt = (over: Record<string, unknown> = {}): Record<string, unknown> => ({
  id: "thm:x", kind: "theorem", status: "proved", statement: "S", depends_on: [], ...over,
});

const working = (over: Partial<WorkingState> = {}): WorkingState =>
  ({ round: 1, solved: {}, resolved_oeqs: {}, ...over }) as WorkingState;

/** Defaults so each case states only the fields its invariant reads. */
const input = (over: Partial<RoundInvariantInput>): RoundInvariantInput =>
  ({ proto: core([]), core: core([]), after: working(), ...over }) as RoundInvariantInput;

const ids = (i: RoundInvariantInput, code: Parameters<typeof violationsOf>[1]): string[] =>
  violationsOf(i, code).flatMap((v) => v.ids);

describe("store-incoherent", () => {
  it("REPORTS a proved core node with no working record", () => {
    // The morning's silent loss: in core.json with a 4561-char proof, absent from
    // `solved`, therefore deleted on the next round.
    const i = input({ core: core([stmt({ proof_tex: "PROOF" })]) });
    expect(ids(i, "store-incoherent")).toEqual(["core-only:thm:x"]);
  });

  it("REPORTS the REVERSE direction — an agent node carried but absent from core", () => {
    // The check was one-directional and therefore blind to exactly this. On 2026-07-19 two
    // agent-authored lemmas sat in the working cursor with full proofs while absent from
    // the assembled core, and the invariant whose job is store divergence stayed silent.
    // An agent-authored node is defined nowhere else, so it renders nowhere.
    const i = input({
      core: core([]),
      after: working({
        solved: {
          "lem:orphan": {
            proof_tex: "PROOF", snapshot: {} as never,
            node: { id: "lem:orphan", kind: "lemma", statement: "S", depends_on: [], status: "proved" } as never,
          },
        },
      }),
    });
    expect(ids(i, "store-incoherent")).toEqual(["working-only:lem:orphan"]);
  });

  it("does NOT report a proto-member record absent from core", () => {
    // Only agent-authored records are reported: a frozen member is still defined in
    // proto_core.json, so its absence from core is recoverable, not a lost definition.
    const i = input({
      core: core([]),
      after: working({ solved: { "thm:x": { proof_tex: "PROOF", snapshot: {} as never } } }),
    });
    expect(ids(i, "store-incoherent")).toEqual([]);
  });

  it("accepts a coherent pair", () => {
    const i = input({
      core: core([stmt({ proof_tex: "PROOF" })]),
      after: working({ solved: { "thm:x": { proof_tex: "PROOF", snapshot: {} as never } } }),
    });
    expect(ids(i, "store-incoherent")).toEqual([]);
  });

  it("ignores nodes carrying no proof, which legitimately have no record", () => {
    expect(ids(input({ core: core([stmt({ status: "to-prove" })]) }), "store-incoherent")).toEqual([]);
  });
});

describe("dangling-resolution", () => {
  it("REPORTS a resolution naming a theorem in neither store", () => {
    const i = input({
      after: working({ resolved_oeqs: { "oeq:q": { theorem_id: "thm:gone", source_fingerprint: "f" } } }),
    });
    expect(ids(i, "dangling-resolution")).toEqual(["oeq:q->thm:gone"]);
  });

  it("accepts one satisfied by the core alone", () => {
    const i = input({
      core: core([stmt()]),
      after: working({ resolved_oeqs: { "oeq:q": { theorem_id: "thm:x", source_fingerprint: "f" } } }),
    });
    expect(ids(i, "dangling-resolution")).toEqual([]);
  });
});

describe("oeq-answer-churn", () => {
  const proto = core([{ id: "oeq:q", kind: "openendedquestion", status: "to-prove", statement: "S", depends_on: [] }]);
  const res = (tid: string) => ({ "oeq:q": { theorem_id: tid, source_fingerprint: "f" } });

  it("REPORTS a renamed answer while the question is unchanged", () => {
    const i = input({
      proto,
      before: working({ resolved_oeqs: res("thm:a") }),
      after: working({ resolved_oeqs: res("thm:b") }),
    });
    expect(ids(i, "oeq-answer-churn")).toEqual(["oeq:q: thm:a -> thm:b"]);
  });

  it("accepts a stable answer", () => {
    const i = input({
      proto,
      before: working({ resolved_oeqs: res("thm:a") }),
      after: working({ resolved_oeqs: res("thm:a") }),
    });
    expect(ids(i, "oeq-answer-churn")).toEqual([]);
  });

  it("ignores a retracted resolution, which is a different event", () => {
    const i = input({ proto, before: working({ resolved_oeqs: res("thm:a") }), after: working() });
    expect(ids(i, "oeq-answer-churn")).toEqual([]);
  });

  it("ignores a question that left the proto entirely", () => {
    const i = input({
      proto: core([]),
      before: working({ resolved_oeqs: res("thm:a") }),
      after: working({ resolved_oeqs: res("thm:b") }),
    });
    expect(ids(i, "oeq-answer-churn")).toEqual([]);
  });

  it("skips the check on a first round, where there is no prior state", () => {
    const i = input({ proto, after: working({ resolved_oeqs: res("thm:a") }) });
    expect(ids(i, "oeq-answer-churn")).toEqual([]);
  });
});

describe("snapshot-basis", () => {
  // Divergent assumption text is what makes proto-vs-core observable at all.
  const node = stmt({ depends_on: ["ass:a"] }) as unknown as CoreStatement;
  const proto = core([node as never], [{ id: "ass:a", condition: "PROTO" }]);
  const assembled = core([node as never], [{ id: "ass:a", condition: "CORE" }]);

  it("REPORTS a snapshot taken against the assembled core", () => {
    const i = input({
      proto,
      core: assembled,
      after: working({ solved: { "thm:x": { proof_tex: "P", snapshot: snapshotMember(assembled, node) } } }),
    });
    expect(ids(i, "snapshot-basis")).toEqual(["thm:x"]);
  });

  it("uses rec.node as the basis for an AGENT record, not the derived core copy", () => {
    // An agent-authored record's authoritative statement is `rec.node`; the core copy is
    // a derived view that can itself have drifted. Checking the snapshot against core
    // meant validating the derived artifact instead of the source, so an internally
    // CONSISTENT record was reported purely because the core had diverged. (That
    // divergence is real, but it is store-incoherence -- a different invariant reports it.)
    const agent = stmt({ statement: "AGENT CLAIM", depends_on: [] }) as unknown as CoreStatement;
    const drifted = stmt({ statement: "DRIFTED CORE COPY", depends_on: [] }) as unknown as CoreStatement;
    const P = core([agent as never], []);
    const i = input({
      proto: P,
      core: core([drifted as never], []),
      after: working({
        solved: { "thm:x": { proof_tex: "P", snapshot: snapshotMember(P, agent), node: agent as never } },
      }),
    });
    expect(ids(i, "snapshot-basis"), "a self-consistent agent record is not a basis error").toEqual([]);
  });

  it("accepts a snapshot taken against the proto", () => {
    const i = input({
      proto,
      core: assembled,
      after: working({ solved: { "thm:x": { proof_tex: "P", snapshot: snapshotMember(proto, node) } } }),
    });
    expect(ids(i, "snapshot-basis")).toEqual([]);
  });

  it("exempts partials, whose snapshot describes the obligation", () => {
    const i = input({
      proto,
      core: assembled,
      after: working({
        solved: { "thm:x": { proof_tex: "P", snapshot: snapshotMember(assembled, node), partial: true } },
      }),
    });
    expect(ids(i, "snapshot-basis")).toEqual([]);
  });
});

describe("hollow-proof", () => {
  it("REPORTS a node marked proved over an empty proof", () => {
    expect(ids(input({ core: core([stmt({ proof_tex: "   " })]) }), "hollow-proof")).toEqual(["thm:x"]);
  });

  it("accepts a cited node, which needs no proof of ours", () => {
    expect(ids(input({ core: core([stmt({ status: "cited" })]) }), "hollow-proof")).toEqual([]);
  });
});

describe("silent-node-loss", () => {
  const before = working({
    solved: { "lem:a": { proof_tex: "P", snapshot: {} as never, node: stmt({ id: "lem:a" }) as never } },
  });

  it("REPORTS an agent-authored statement that disappeared unexplained", () => {
    // `solved` is the only place such a statement is defined, so this deletes the
    // STATEMENT, not merely its proof.
    expect(ids(input({ before, after: working() }), "silent-node-loss")).toEqual(["lem:a"]);
  });

  it("accepts a loss that was explicitly allowed", () => {
    expect(ids(input({ before, after: working(), allowedLoss: ["lem:a"] }), "silent-node-loss")).toEqual([]);
  });

  it("ignores proto-frozen records, which the proto still defines", () => {
    const protoRec = working({ solved: { "thm:x": { proof_tex: "P", snapshot: {} as never } } });
    expect(ids(input({ before: protoRec, after: working() }), "silent-node-loss")).toEqual([]);
  });
});

describe("dependency-cycle", () => {
  it("REPORTS a mutual dependency, the shape the guardless wiring pass produced", () => {
    const c = core([
      stmt({ id: "lem:a", depends_on: ["lem:b"] }),
      stmt({ id: "lem:b", depends_on: ["lem:a"] }),
    ]);
    expect(ids(input({ core: c }), "dependency-cycle").length).toBeGreaterThan(0);
  });

  it("accepts a chain", () => {
    const c = core([
      stmt({ id: "lem:a", depends_on: ["lem:b"] }),
      stmt({ id: "lem:b", depends_on: [] }),
    ]);
    expect(ids(input({ core: c }), "dependency-cycle")).toEqual([]);
  });

  it("ignores edges pointing outside the statement set", () => {
    expect(ids(input({ core: core([stmt({ depends_on: ["ass:a", "def:b"] })]) }), "dependency-cycle")).toEqual([]);
  });
});
