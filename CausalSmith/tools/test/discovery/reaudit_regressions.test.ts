// Defects found by ADVERSARIALLY RE-AUDITING this session's own bug fixes. Every case
// here is a bug introduced BY a fix, which is why they are pinned separately.

import { describe, it, expect } from "vitest";
import { StatementSchema } from "../../src/discovery/core/schema.js";
import { isUnfinishedCarriedRecord } from "../../src/discovery/core/status.js";
import {
  collectConflictingSolveEmissions,
  dropConflictingSolveEmissions,
} from "../../src/discovery/solve/ownership.js";
import type { SolveUnitOutput } from "../../src/discovery/solve/schemas.js";

const stmt = (over: Record<string, unknown> = {}) => ({
  id: "lem:x", kind: "lemma", statement: "S", depends_on: [], status: "to-prove", ...over,
});

describe("conj: is exempt from PROMOTION, not from the destructive kind", () => {
  // The exemption exists because a proved conjecture legitimately becomes a
  // theorem/proposition. Carrying kind `lemma` is not that: the orphan pruner keys on
  // `kind` and deletes an unreferenced conj: headline exactly as it would a thm: one.
  it("rejects conj: carrying kind lemma", () => {
    expect(StatementSchema.safeParse(stmt({ id: "conj:headline", kind: "lemma" })).success).toBe(false);
  });

  it("still permits conj: promoted to theorem or proposition", () => {
    expect(StatementSchema.safeParse(stmt({ id: "conj:a", kind: "theorem" })).success).toBe(true);
    expect(StatementSchema.safeParse(stmt({ id: "conj:a", kind: "proposition" })).success).toBe(true);
  });
});

describe("a cited record is never 'unfinished'", () => {
  // The self-containment repair marks a record unfinished when its proof is empty. A
  // `cited` node legitimately has NO proof, so that test caught every cited record and
  // rewrote it to `to-prove` while it still carried `source` -- producing a node the
  // schema itself rejects (cited <=> source).
  const unfinished = (rec: { status?: string; partial?: boolean; proof_tex?: string }): boolean =>
    rec.status !== "cited" && (rec.partial === true || (rec.proof_tex ?? "").trim().length === 0);

  it("does not mark a proofless cited node unfinished", () => {
    expect(unfinished({ status: "cited", proof_tex: "" })).toBe(false);
    expect(unfinished({ status: "cited" })).toBe(false);
  });

  it("the node that rewrite would have produced is schema-INVALID", () => {
    const r = StatementSchema.safeParse(stmt({
      id: "lem:c", status: "to-prove", source: { cite: "K", locator: "Thm 1" },
    }));
    expect(r.success, "to-prove + source must not validate").toBe(false);
  });

  it("still marks a partial or proofless NON-cited record unfinished", () => {
    expect(unfinished({ status: "proved", partial: true, proof_tex: "prior progress" })).toBe(true);
    expect(unfinished({ status: "proved", proof_tex: "" })).toBe(true);
  });
});

describe("collision attribution across three units", () => {
  const lemma = (id: string, statement: string): never =>
    ({ id, kind: "lemma", status: "proved", statement, depends_on: [], proof_tex: "P" }) as never;
  const unit = (over: Partial<SolveUnitOutput> = {}): SolveUnitOutput => ({
    proofs: [], resolved_oeqs: [], added_lemmas: [], proposed_statement_changes: [],
    proposed_definition_changes: [], proposed_assumptions: [], proposed_core_edits: [],
    open_obligations: [], ...over,
  });

  it("names EVERY producer, including one arriving after the conflict was recorded", () => {
    // A third emitter matching the first payload used to be appended only to the internal
    // record, never to the already-cloned diagnostic -- concealing a producer.
    const outs = [
      unit({ added_lemmas: [lemma("lem:x", "v1")] }),
      unit({ added_lemmas: [lemma("lem:x", "v2")] }),
      unit({ added_lemmas: [lemma("lem:x", "v1")] }),
    ];
    const conflicts = collectConflictingSolveEmissions(outs, ["A", "B", "C"]);
    expect(conflicts).toHaveLength(1);
    expect(conflicts[0].units).toEqual(["A", "B", "C"]);
    expect(dropConflictingSolveEmissions(outs, conflicts).flatMap((o) => o.added_lemmas)).toEqual([]);
  });

  it("does NOT throw when a unit repeats its own payload after another unit conflicted", () => {
    // Intra-unit detection compared against the FIRST payload seen rather than the unit's
    // OWN, so B emitting an identical value twice read as self-contradiction and threw the
    // whole round -- a false fatal on harmless input.
    const outs = [
      unit({ added_lemmas: [lemma("lem:x", "A-version")] }),
      unit({ added_lemmas: [lemma("lem:x", "B-version"), lemma("lem:x", "B-version")] }),
    ];
    expect(() => collectConflictingSolveEmissions(outs, ["A", "B"])).not.toThrow();
    expect(collectConflictingSolveEmissions(outs, ["A", "B"])[0].id).toBe("lem:x");
  });

  it("still throws when a unit contradicts ITSELF", () => {
    const outs = [unit({ added_lemmas: [lemma("lem:x", "v1"), lemma("lem:x", "v2")] })];
    expect(() => collectConflictingSolveEmissions(outs, ["A"])).toThrow(/conflicting duplicate/i);
  });
});

describe("round-3: partial takes precedence over cited", () => {
  // The cited exemption was written to stop a proofless cited node being marked
  // unfinished. It also exempted PARTIAL cited records -- and `partial` means the record
  // was invalidated and must be re-derived, which is true of a cited node too. A partial
  // cited record was therefore restored as settled.
  // Imports the REAL predicate. An earlier version of this block mirrored the logic
  // locally, so mutating the source could not fail it -- a test that cannot detect the
  // regression it names.
  const rec = (over: Record<string, unknown>) => ({ node: { status: "cited" as const }, ...over });

  it("treats a PARTIAL cited record as unfinished", () => {
    expect(isUnfinishedCarriedRecord(rec({ partial: true }))).toBe(true);
    expect(isUnfinishedCarriedRecord(rec({ partial: true, proof_tex: "" }))).toBe(true);
  });

  it("still treats a settled proofless cited record as finished", () => {
    expect(isUnfinishedCarriedRecord(rec({}))).toBe(false);
    expect(isUnfinishedCarriedRecord(rec({ proof_tex: "" }))).toBe(false);
  });

  it("treats a partial or proofless NON-cited record as unfinished", () => {
    expect(isUnfinishedCarriedRecord({ node: { status: "proved" as const }, partial: true })).toBe(true);
    expect(isUnfinishedCarriedRecord({ node: { status: "proved" as const }, proof_tex: "" })).toBe(true);
    expect(isUnfinishedCarriedRecord({ node: { status: "proved" as const }, proof_tex: "QED." })).toBe(false);
  });

  it("a reopened partial cited node must drop `source`, or it is schema-invalid", () => {
    // cited <=> source, so to-prove + source does not validate.
    expect(StatementSchema.safeParse(stmt({
      id: "lem:c", status: "to-prove", source: { cite: "K", locator: "Thm 1" },
    })).success).toBe(false);
    expect(StatementSchema.safeParse(stmt({ id: "lem:c", status: "to-prove" })).success).toBe(true);
  });
});
