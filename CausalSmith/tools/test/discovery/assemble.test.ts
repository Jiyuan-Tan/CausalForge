// Construction-level guarantees of the Phase-1 store consolidation (2026-07-30
// migration plan): the published core.json is `assembleCore(proto, working)` — a
// pure render of the two authoritative stores — so each retired cross-store
// check's bad state is now UNREPRESENTABLE or AUTO-RESOLVED. One test per
// retired check, plus the render semantics the migration introduced.
//
// Retired checks covered here (formerly core/coherence.ts + solve/gates.ts):
//   reconcileProofStores (hard)   → "render publishes proofs only from records"
//                                   + normalizeWorkingState throw tests
//   proposal closure (hard)       → "every rendered id comes from proto/working"
//   store-incoherent (warn)       → both directions unrepresentable
//   proved-not-partial (warn)     → derived status: partial never renders proved
//   oeq-source-retired (warn)     → answered sources filtered by the render
//   oeq-source-record-retired     → auto-resolved at the single write boundary

import { describe, it, expect } from "vitest";
import { assembleCore, mergeProseOverlay } from "../../src/discovery/core/assemble.js";
import { normalizeWorkingState } from "../../src/discovery/stages/d0_working.js";
import type { Core } from "../../src/discovery/core/schema.js";
import type { WorkingState } from "../../src/discovery/stages/d0_working.js";

const core = (
  statements: Array<Record<string, unknown>>,
  over: Partial<Record<string, unknown>> = {},
): Core =>
  ({
    qid: "q",
    symbols: [],
    assumptions: [],
    definitions: [],
    statements,
    bibliography: [],
    target_estimand: "tau",
    ...over,
  }) as unknown as Core;

const stmt = (over: Record<string, unknown> = {}): Record<string, unknown> => ({
  id: "thm:x",
  kind: "theorem",
  status: "to-prove",
  statement: "S",
  depends_on: [],
  ...over,
});

const working = (over: Partial<WorkingState> = {}): WorkingState =>
  ({ round: 1, solved: {}, resolved_oeqs: {}, ...over }) as WorkingState;

const snap = (stmtText: string) => ({ stmt: stmtText, depends_on: [], defs: {}, assumptions: {} });

const renderedIds = (c: Core): string[] => c.statements.map((s) => s.id);
const rendered = (c: Core, id: string) => c.statements.find((s) => s.id === id);

describe("assembleCore purity", () => {
  it("does not mutate its inputs and is byte-stable", () => {
    const proto = core([stmt()]);
    const w = working({ solved: { "thm:x": { proof_tex: "P", snapshot: snap("S") } } });
    const protoBefore = JSON.stringify(proto);
    const wBefore = JSON.stringify(w);
    const once = JSON.stringify(assembleCore(proto, w));
    const twice = JSON.stringify(assembleCore(proto, w));
    expect(once).toBe(twice);
    expect(JSON.stringify(proto)).toBe(protoBefore);
    expect(JSON.stringify(w)).toBe(wBefore);
  });
});

describe("retired: reconcileProofStores / store-incoherent (core-only direction)", () => {
  it("a proof can only reach the published core THROUGH a working record", () => {
    // The round-51 shape: a terminal theorem's proof reached core.json without a
    // working record and vanished next round. Now the record IS the only source:
    // with no record the node renders exactly as the frozen proto states it.
    const proto = core([stmt()]);
    const out = assembleCore(proto, working());
    expect(rendered(out, "thm:x")!.status).toBe("to-prove");
    expect(rendered(out, "thm:x")!.proof_tex).toBeUndefined();
  });

  it("a full record's proof renders with derived `proved` status", () => {
    const proto = core([stmt()]);
    const out = assembleCore(proto, working({ solved: { "thm:x": { proof_tex: "PROOF", snapshot: snap("S") } } }));
    expect(rendered(out, "thm:x")!.status).toBe("proved");
    expect(rendered(out, "thm:x")!.proof_tex).toBe("PROOF");
  });
});

describe("retired: store-incoherent (working-only direction)", () => {
  it("a recorded agent node ALWAYS renders — it cannot silently vanish from the paper", () => {
    // 2026-07-19: two agent-authored lemmas sat in the cursor with full proofs
    // while absent from the assembled core. Under the render that state is
    // unrepresentable: the record is the definition, so it publishes.
    const out = assembleCore(
      core([]),
      working({
        solved: {
          "lem:orphan": {
            proof_tex: "PROOF",
            snapshot: snap("S"),
            node: { id: "lem:orphan", kind: "lemma", statement: "S", depends_on: [], status: "proved" } as never,
          },
        },
      }),
    );
    expect(rendered(out, "lem:orphan")).toBeDefined();
    expect(rendered(out, "lem:orphan")!.status).toBe("proved");
  });

  it("EXCEPT shelved debt, which is deliberately unpublished (publication state is data)", () => {
    const out = assembleCore(
      core([]),
      working({
        solved: {
          "lem:debt": {
            proof_tex: "half an argument",
            snapshot: snap("S"),
            node: { id: "lem:debt", kind: "lemma", statement: "S", depends_on: [], status: "to-prove" } as never,
            partial: true,
            shelved: true,
          },
        },
      }),
    );
    expect(rendered(out, "lem:debt")).toBeUndefined();
  });
});

describe("retired: proved-not-partial", () => {
  it("a partial record can never render `proved` — status is derived, not stored twice", () => {
    // The real banked contradiction (exp_saturation_skew_threshold_v1):
    // core.json published `proved` while the cursor said partial. Derivation
    // makes the contradiction unrepresentable: partial ⇒ open target.
    const out = assembleCore(
      core([]),
      working({
        solved: {
          "lem:partial": {
            proof_tex: "best partial bytes",
            snapshot: snap("S"),
            node: { id: "lem:partial", kind: "lemma", statement: "S", depends_on: [], status: "proved" } as never,
            partial: true,
          },
        },
      }),
    );
    const node = rendered(out, "lem:partial")!;
    expect(node.status).toBe("to-prove");
    // Best-partial preservation: the bytes ride along as prior progress.
    expect(node.proof_tex).toBe("best partial bytes");
  });

  it("a partial FROZEN member keeps the proto's open status; its bytes attach as best-partial", () => {
    const proto = core([stmt()]);
    const out = assembleCore(
      proto,
      working({ solved: { "thm:x": { proof_tex: "partial progress", snapshot: snap("S"), partial: true } } }),
    );
    expect(rendered(out, "thm:x")!.status).toBe("to-prove");
    expect(rendered(out, "thm:x")!.proof_tex).toBe("partial progress");
  });
});

describe("retired: proposal closure", () => {
  it("every rendered id comes from the proto or the working state — an uncarried node is unrepresentable", () => {
    const proto = core([stmt(), stmt({ id: "oeq:q", kind: "openendedquestion" })]);
    const w = working({
      solved: {
        "thm:x": { proof_tex: "P", snapshot: snap("S") },
        "lem:added": {
          proof_tex: "P2",
          snapshot: snap("S2"),
          node: { id: "lem:added", kind: "lemma", statement: "S2", depends_on: [], status: "proved" } as never,
        },
        "thm:answer": {
          proof_tex: "P3",
          snapshot: snap("S3"),
          node: { id: "thm:answer", kind: "theorem", statement: "S3", depends_on: [], status: "proved" } as never,
          owner: "oeq:q",
        },
      },
      resolved_oeqs: { "oeq:q": { theorem_id: "thm:answer", source_fingerprint: "fp" } },
    });
    const out = assembleCore(proto, w);
    const carriers = new Set([...proto.statements.map((s) => s.id), ...Object.keys(w.solved)]);
    for (const id of renderedIds(out)) expect(carriers.has(id)).toBe(true);
  });
});

describe("retired: oeq-source-retired", () => {
  it("an answer theorem citing the question it settles renders with neither a self-edge nor a dangling Q id", () => {
    const proto = core([
      stmt({ id: "lem:base", status: "proved", proof_tex: "B" }),
      stmt({ id: "oeq:q", kind: "openendedquestion", statement: "characterize the frontier", depends_on: ["lem:base"] }),
      stmt({ id: "thm:consumer", depends_on: ["oeq:q"] }),
    ]);
    const out = assembleCore(
      proto,
      working({
        solved: {
          "thm:answer": {
            proof_tex: "P",
            snapshot: snap("A"),
            node: { id: "thm:answer", kind: "theorem", statement: "A", depends_on: ["oeq:q"], status: "proved" } as never,
            owner: "oeq:q",
          },
        },
        resolved_oeqs: { "oeq:q": { theorem_id: "thm:answer", source_fingerprint: "fp" } },
      }),
    );
    const ids = new Set(out.statements.map((s) => s.id));
    expect(ids.has("oeq:q")).toBe(false);
    const answer = out.statements.find((s) => s.id === "thm:answer")!;
    // The dropped self-citation inherits the question's own upstream edge.
    expect(answer.depends_on).toEqual(["lem:base"]);
    expect(out.statements.find((s) => s.id === "thm:consumer")!.depends_on).toEqual(["thm:answer"]);
    for (const s of out.statements) for (const d of s.depends_on) expect(ids.has(d), `${s.id} -> ${d}`).toBe(true);
  });
  it("an answered question is filtered out of the render and its answer published", () => {
    // Derived from the healthy stat_reversekl_two_coverage resolution shape.
    const proto = core([
      stmt({ id: "oeq:q", kind: "openendedquestion", statement: "characterize the frontier" }),
      stmt({ id: "thm:consumer", depends_on: ["oeq:q"] }),
    ]);
    const out = assembleCore(
      proto,
      working({
        solved: {
          "thm:answer": {
            proof_tex: "P",
            snapshot: snap("A"),
            node: { id: "thm:answer", kind: "theorem", statement: "A", depends_on: [], status: "proved" } as never,
            owner: "oeq:q",
          },
        },
        resolved_oeqs: { "oeq:q": { theorem_id: "thm:answer", source_fingerprint: "fp" } },
      }),
    );
    expect(rendered(out, "oeq:q")).toBeUndefined();
    expect(rendered(out, "thm:answer")).toBeDefined();
    // Consumers' edges are remapped from the source to its answer.
    expect(rendered(out, "thm:consumer")!.depends_on).toContain("thm:answer");
    expect(rendered(out, "thm:consumer")!.depends_on).not.toContain("oeq:q");
  });
});

describe("retired: oeq-source-record-retired (auto-resolved) + reconcile throw (moved)", () => {
  it("normalizeWorkingState retires a surviving source record at the write boundary", () => {
    const w = working({
      solved: {
        "oeq:q": { proof_tex: "stale", snapshot: snap("q") },
        "thm:answer": {
          proof_tex: "P",
          snapshot: snap("A"),
          node: { id: "thm:answer", kind: "theorem", statement: "A", depends_on: [], status: "proved" } as never,
        },
      },
      resolved_oeqs: { "oeq:q": { theorem_id: "thm:answer", source_fingerprint: "fp" } },
    });
    normalizeWorkingState(w);
    expect(w.solved["oeq:q"]).toBeUndefined();
    expect(w.solved["thm:answer"]).toBeDefined();
  });

  it("throws when a resolution names a theorem the store does not hold (was reconcileProofStores' throw)", () => {
    const w = working({
      resolved_oeqs: { "oeq:q": { theorem_id: "thm:gone", source_fingerprint: "fp" } },
    });
    expect(() => normalizeWorkingState(w)).toThrow(/oeq:q->thm:gone/);
  });

  it("throws on the legacy string form too", () => {
    const w = working({ resolved_oeqs: { "oeq:q": "thm:missing" } as never });
    expect(() => normalizeWorkingState(w)).toThrow(/thm:missing/);
  });
});

describe("render semantics introduced by the migration", () => {
  it("applies the prose overlay at render time (proto is never written)", () => {
    const proto = core([stmt()], { tldr: "old tldr" });
    const overlay = mergeProseOverlay(undefined, {
      tldr: "new tldr",
      statement_notes: [{ id: "thm:x", justification: "why it matters" }],
    });
    const w = working({ prose_overlay: overlay });
    const out = assembleCore(proto, w);
    expect(out.tldr).toBe("new tldr");
    expect(rendered(out, "thm:x")!.justification).toBe("why it matters");
    expect(proto.tldr).toBe("old tldr");
  });

  it("mergeProseOverlay is cumulative per field and per statement note", () => {
    const first = mergeProseOverlay(undefined, {
      tldr: "v1",
      statement_notes: [{ id: "thm:x", justification: "j1", gap: "g1" }],
    });
    const second = mergeProseOverlay(first, {
      statement_notes: [{ id: "thm:x", justification: "j2" }],
    });
    expect(second.tldr).toBe("v1");
    expect(second.statement_notes!["thm:x"]).toEqual({ justification: "j2", gap: "g1" });
  });

  it("filters pruned proto orphans so no render resurrects them", () => {
    const proto = core([stmt(), stmt({ id: "lem:orphan", kind: "lemma" })]);
    const out = assembleCore(proto, working({ pruned_proto_orphans: ["lem:orphan"] }));
    expect(rendered(out, "lem:orphan")).toBeUndefined();
    expect(rendered(out, "thm:x")).toBeDefined();
  });

  it("never publishes `proved` over an empty proof (the hollow-proof construction)", () => {
    const out = assembleCore(
      core([stmt()]),
      working({ solved: { "thm:x": { proof_tex: "   ", snapshot: snap("S") } } }),
    );
    expect(rendered(out, "thm:x")!.status).toBe("to-prove");
  });

  it("preserves `cited` on a full record of a cited frozen member", () => {
    const proto = core([
      stmt({ id: "lem:lit", kind: "lemma", status: "cited", source: { cite: "bibkey", locator: "Thm 1" } }),
    ]);
    const out = assembleCore(
      proto,
      working({ solved: { "lem:lit": { proof_tex: "", snapshot: snap("S") } } }),
    );
    expect(rendered(out, "lem:lit")!.status).toBe("cited");
    // The missing-bib heal (folded into the render) stubs the cited bibkey.
    expect((out.bibliography ?? []).some((b) => b.key === "bibkey")).toBe(true);
  });
});
