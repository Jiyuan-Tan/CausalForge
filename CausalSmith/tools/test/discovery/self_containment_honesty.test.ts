// The self-containment repair keeps the core closed when a dependency is referenced but
// not re-emitted. It used to publish the carried node as PROVED unconditionally:
// `solvedStatus` returns "proved" for everything non-cited, so a record flagged `partial`
// (meaning "re-derive; the stored proof is prior partial progress") and a record with an
// EMPTY proof both rendered as established results. Found by static audit 2026-07-20.

import { describe, it, expect } from "vitest";
import { solvedStatus } from "../../src/discovery/core/status.js";

describe("solvedStatus is not a completeness check", () => {
  // Pinning the sharp edge that made the repair unsafe: this helper answers "what status
  // does a SOLVED record get", not "is this record actually finished". Callers holding a
  // possibly-unfinished record must decide that themselves.
  it("returns proved for a node with an empty proof", () => {
    expect(solvedStatus({ id: "lem:x", proof_tex: "" })).toBe("proved");
  });

  it("returns proved for a node with no proof field at all", () => {
    expect(solvedStatus({ id: "lem:x" })).toBe("proved");
  });

  it("preserves cited", () => {
    expect(solvedStatus({ id: "lem:x", status: "cited" })).toBe("cited");
  });
});

describe("the unfinished-record predicate used by the repair", () => {
  // The repair publishes `to-prove` when the carried record is partial or proofless, and
  // only then falls through to solvedStatus. Mirrored here so the rule is pinned
  // independently of the 1700-line function that applies it.
  const unfinished = (rec: { partial?: boolean; proof_tex?: string }): boolean =>
    rec.partial === true || (rec.proof_tex ?? "").trim().length === 0;

  it("treats a partial record as unfinished even with a proof present", () => {
    expect(unfinished({ partial: true, proof_tex: "a long prior-progress proof" })).toBe(true);
  });

  it("treats an empty or whitespace proof as unfinished", () => {
    expect(unfinished({ proof_tex: "" })).toBe(true);
    expect(unfinished({ proof_tex: "   \n " })).toBe(true);
    expect(unfinished({})).toBe(true);
  });

  it("treats a complete carried proof as finished", () => {
    expect(unfinished({ proof_tex: "QED." })).toBe(false);
    expect(unfinished({ partial: false, proof_tex: "QED." })).toBe(false);
  });
});
