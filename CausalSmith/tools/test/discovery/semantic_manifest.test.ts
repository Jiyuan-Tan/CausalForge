import { readFileSync } from "node:fs";
import { describe, expect, it } from "vitest";
import { CoreSchema } from "../../src/discovery/core/schema.js";
import {
  SemanticManifestSchema,
  validateCoreManifest,
  validateRenderedManifest,
  validateSolveManifest,
  validateWorkingManifest,
} from "../../src/discovery/semantic_manifest.js";
import { memberValid, snapshotMember, type WorkingState } from "../../src/discovery/stages/d0_working.js";

function core() {
  return CoreSchema.parse(JSON.parse(readFileSync(
    new URL("../fixtures/stat_ate_overlap_decay_proto_core.json", import.meta.url),
    "utf8",
  )));
}

describe("D0 semantic manifest", () => {
  it("fails closed on forbidden solve emissions and exact core dependency drift", () => {
    const c = core();
    const id = c.statements[0].id;
    const manifest = SemanticManifestSchema.parse({
      version: 1,
      statements: [{ id, scopes: ["core"], exact_depends_on: c.statements[0].depends_on }],
      forbidden_statements: [{ id: "thm:obsolete-answer", scopes: ["solve", "core"] }],
    });
    expect(() => validateCoreManifest(manifest, "core", c)).not.toThrow();
    expect(() => validateSolveManifest(manifest, [{
      proofs: [], added_lemmas: [],
      resolved_oeqs: [{ source_id: "oeq:x", theorem: {
        id: "thm:obsolete-answer", kind: "theorem", statement: "obsolete",
        depends_on: [], status: "proved", proof_tex: "Proof.",
      } }],
    }])).toThrow(/forbidden statement/);

    const drifted = structuredClone(c);
    drifted.statements[0].depends_on = [];
    expect(() => validateCoreManifest(manifest, "core", drifted)).toThrow(/expected exactly/);
  });

  it("validates working OEQ resolution, dependency snapshots, and rendered literals", () => {
    const c = core();
    const stmt = c.statements[0];
    const manifest = SemanticManifestSchema.parse({
      version: 1,
      statements: [{ id: stmt.id, scopes: ["working"], exact_depends_on: stmt.depends_on }],
      resolved_oeqs: [{ source_id: "oeq:x", theorem_id: "thm:x" }],
      render: { required_literals: ["canonical comparison"], forbidden_literals: ["obsolete lower bound"] },
    });
    const working: WorkingState = {
      round: 1,
      solved: { [stmt.id]: { proof_tex: "Proof.", snapshot: snapshotMember(c, stmt) } },
      resolved_oeqs: { "oeq:x": { theorem_id: "thm:x", source_fingerprint: "f" } },
    };
    expect(() => validateWorkingManifest(manifest, working)).not.toThrow();
    expect(() => validateRenderedManifest(manifest, "The canonical comparison is proved.")).not.toThrow();
    expect(() => validateRenderedManifest(manifest, "An obsolete lower bound.")).toThrow(/missing literal|forbidden literal/);
  });

  it("proof reuse follows the CONTENT basis, not the depends_on edge list", () => {
    const c = core();
    const stmt = c.statements[0];
    const prev: WorkingState = {
      round: 1,
      solved: { [stmt.id]: { proof_tex: "Proof.", snapshot: snapshotMember(c, stmt) } },
    };
    // An edge REMOVED while its referenced content is unchanged is dependency
    // bookkeeping: the statement text and everything the proof was solved against are
    // intact, so the proof stays reusable. (Edge-set comparison previously forced a
    // re-derivation here — "dep change alone triggers re-derivation via snapshot
    // invalidation" cost a run >=3 re-derivations of one byte-identical theorem.)
    const removed = structuredClone(c);
    removed.statements[0].depends_on = removed.statements[0].depends_on.slice(1);
    expect(memberValid(prev, removed, removed.statements[0])).toBe(true);

    // But content leaving the closure with a CHANGED definition still invalidates:
    // the stored snapshot's def map is checked against the current proto by id.
    const edited = structuredClone(c);
    edited.statements[0].depends_on = edited.statements[0].depends_on.filter((d) => d !== "def:estimator");
    edited.definitions.find((d) => d.id === "def:estimator")!.construction = "a DIFFERENT estimator formula";
    expect(memberValid(prev, edited, edited.statements[0])).toBe(false);

    // A reorder or a duplicate is NOT a change and must keep the proof reusable.
    const reordered = structuredClone(c);
    reordered.statements[0].depends_on = [...reordered.statements[0].depends_on].reverse();
    expect(memberValid(prev, reordered, reordered.statements[0])).toBe(true);
    const duped = structuredClone(c);
    duped.statements[0].depends_on = [...duped.statements[0].depends_on, duped.statements[0].depends_on[0]];
    expect(memberValid(prev, duped, duped.statements[0])).toBe(true);
  });
});
