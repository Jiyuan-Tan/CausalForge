// Phase 2 (reference-by-revision-hash) round-trip tests: the revision stamped
// on every solver-facing view matches what the apply computes for its legal
// views, so `based_on_revision` collapses the echo view-selection to one
// comparison; unknown/stale hashes skip fail-safe.

import { describe, it, expect } from "vitest";
import { statementRevision, stampRevision, stampCoreStatements, REVISION_PATTERN } from "../../src/discovery/core/revision.js";
import { describeRevisionMismatch } from "../../src/discovery/stages/d0_apply.js";
import { buildReviewPacket } from "../../src/discovery/review_packet.js";
import type { Core, CoreStatement } from "../../src/discovery/core/schema.js";
import type { WorkingState } from "../../src/discovery/stages/d0_working.js";

const node = (over: Partial<CoreStatement> = {}): CoreStatement =>
  ({
    id: "thm:x",
    kind: "theorem",
    statement: "S",
    status: "to-prove",
    depends_on: ["ass:a", "def:d"],
    ...over,
  }) as CoreStatement;

describe("statementRevision", () => {
  it("is deterministic and shaped rev:<sha256>", () => {
    const r = statementRevision(node());
    expect(r).toMatch(REVISION_PATTERN);
    expect(statementRevision(node())).toBe(r);
  });

  it("covers exactly the echo fields: sensitive to claim/status/kind, insensitive to everything else", () => {
    const base = statementRevision(node());
    expect(statementRevision(node({ statement: "S'" }))).not.toBe(base);
    expect(statementRevision(node({ status: "proved" }))).not.toBe(base);
    expect(statementRevision(node({ kind: "lemma" }))).not.toBe(base);
  });

  it("excludes derived/moving fields (audit P23F1): deps wiring, proof bytes, source attestation", () => {
    const base = statementRevision(node());
    // Assembly auto-wires depends_on from proof citations; the packet's wired
    // view and the apply's bare-proto reconstruction must hash identically.
    expect(statementRevision(node({ depends_on: ["def:d", "ass:a", "lem:wired-in"] }))).toBe(base);
    expect(statementRevision({ ...node(), proof_tex: "long proof" } as CoreStatement)).toBe(base);
    expect(statementRevision({ ...node(), source: { cite: "K" } } as never)).toBe(base);
  });
});

describe("describeRevisionMismatch — the three legal views + the open-target form", () => {
  const original = node(); // pre-bundle frozen original
  const overlay = node({ status: "proved" }); // settled working overlay view
  const prior = node({ statement: "S narrowed" }); // post-claim paired node
  const proposed = { id: "thm:x", kind: "theorem" };

  it("accepts the pre-bundle original's revision", () => {
    expect(describeRevisionMismatch(statementRevision(original), proposed, [original, prior], "thm:x")).toBeNull();
  });

  it("accepts the settled-overlay view's revision", () => {
    expect(describeRevisionMismatch(statementRevision(overlay), proposed, [overlay, original], "thm:x")).toBeNull();
  });

  it("accepts the post-claim paired node's revision", () => {
    expect(describeRevisionMismatch(statementRevision(prior), proposed, [original, prior], "thm:x")).toBeNull();
  });

  it("accepts the open-target (dispatch) form of a settled view", () => {
    // A dispatch target is stamped as the re-opened node: status to-prove, source dropped.
    const cited = node({ status: "cited", source: { cite: "K", locator: "Thm 1" } as never });
    const asTarget = { ...cited, status: "to-prove" as const, source: undefined };
    expect(describeRevisionMismatch(statementRevision(asTarget), proposed, [cited], "thm:x")).toBeNull();
  });

  it("rejects an unknown/stale hash with the hash in the message (skip fail-safe)", () => {
    const stale = statementRevision(node({ statement: "an old text" }));
    const why = describeRevisionMismatch(stale, proposed, [original, overlay, prior], "thm:x");
    expect(why).toContain(stale);
    expect(why).toContain("stale edit");
  });

  it("still enforces the kind echo against the matched view", () => {
    const why = describeRevisionMismatch(statementRevision(original), { id: "thm:x", kind: "lemma" }, [original], "thm:x");
    expect(why).toContain("kind must echo");
  });

  it("rejects a payload id that does not match the edit target", () => {
    expect(describeRevisionMismatch(statementRevision(original), { id: "thm:other", kind: "theorem" }, [original], "thm:x"))
      .toContain("does not match the edit target");
  });
});

describe("packet stamping", () => {
  it("every current_typed_core statement carries the revision of its rendered view", () => {
    const core = {
      qid: "q",
      symbols: [],
      assumptions: [],
      definitions: [],
      statements: [node(), node({ id: "lem:y", kind: "lemma", statement: "L", depends_on: [] })],
      bibliography: [],
      target_estimand: "tau",
    } as unknown as Core;
    const working = { round: 1, solved: {}, resolved_oeqs: {} } as unknown as WorkingState;
    const pkt = buildReviewPacket({
      core,
      working,
      proposedStatementChanges: [],
      proposedDefinitionChanges: [],
      proposedAssumptions: [],
      proposedCoreEdits: [],
      provisionalProofs: [],
    });
    const stamped = (pkt.current_typed_core as { statements: Array<CoreStatement & { revision?: string }> }).statements;
    for (const s of stamped) {
      const { revision, ...bare } = s;
      expect(revision).toBe(statementRevision(bare));
    }
    // The input core object is not mutated (stored core.json shapes unchanged).
    expect((core.statements[0] as { revision?: string }).revision).toBeUndefined();
  });

  it("stampRevision/stampCoreStatements agree with statementRevision", () => {
    const s = node();
    expect(stampRevision(s).revision).toBe(statementRevision(s));
    expect(stampCoreStatements({ statements: [s] }).statements[0].revision).toBe(statementRevision(s));
  });
});
