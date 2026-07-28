// Legacy-core soundness of SCOPED symbol invalidation, checked against every real run.
//
// Scoping symbol invalidation by a node's declared `free_symbols` is only safe if a
// node that never declared the field is read as "may use ANY symbol". That is a claim
// about REAL artifacts, not about a fixture: zero of the 1077 statements and zero of the
// 1269 definitions in the 112 real cores under doc/research/{active,_bank} carry
// `free_symbols`, so if the field defaulted to `[]` on parse — or if the scope treated
// absence as emptiness — every one of those runs would carry every proof through a
// symbol re-definition and publish proofs of materially different claims as current.
//
// This test replays that exact scenario on the real (proto_core.json, d0_working.json)
// pairs: stamp the cursor with the basis of its own proto, perturb ONE real symbol's
// `space`, and require every previously-carried proof to reopen.

import { describe, it, expect } from "vitest";
import { existsSync, readFileSync, readdirSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { computeValidNodes, symbolBasis, type WorkingState } from "../../src/discovery/stages/d0_working.js";
import { CoreSchema, DefinitionSchema, StatementSchema, type Core } from "../../src/discovery/core/schema.js";
import { normalizeRawModelJson } from "../../src/discovery/core/latex_serialization.js";

const RESEARCH_ROOT = fileURLToPath(new URL("../../../doc/research", import.meta.url));

function discoveryDirs(): string[] {
  const out: string[] = [];
  const walk = (dir: string): void => {
    for (const e of readdirSync(dir, { withFileTypes: true })) {
      if (!e.isDirectory() || e.name === ".premigration") continue;
      const p = path.join(dir, e.name);
      if (existsSync(path.join(p, "d0_working.json")) && existsSync(path.join(p, "proto_core.json"))) out.push(p);
      walk(p);
    }
  };
  for (const root of ["active", "_bank"]) {
    const dir = path.join(RESEARCH_ROOT, root);
    if (existsSync(dir)) walk(dir);
  }
  return out;
}

function readJson(file: string): Record<string, unknown> | null {
  try {
    return JSON.parse(readFileSync(file, "utf8")) as Record<string, unknown>;
  } catch {
    return null;
  }
}

interface RealRun {
  label: string;
  proto: Core;
  cursor: WorkingState;
}

/** Load a real proto exactly as production does (`core_io.readTypedCore`): normalize the
 *  model's escapes, then run it through `CoreSchema`. Parsing matters — the fail-safe
 *  depends on `free_symbols` surviving that parse as ABSENT, which a raw `JSON.parse`
 *  would give for free and therefore could not test. One banked proto
 *  (stat_ate_overlap_decay_v1) predates a comparator enum and does not parse; it is
 *  skipped rather than smuggled in raw. */
function parseProto(file: string): Core | null {
  try {
    const raw = JSON.parse(normalizeRawModelJson(readFileSync(file, "utf8"))) as { core?: unknown };
    const parsed = CoreSchema.safeParse(raw.core ?? raw);
    return parsed.success ? (parsed.data as Core) : null;
  } catch {
    return null;
  }
}

function realRuns(): RealRun[] {
  const runs: RealRun[] = [];
  for (const dir of discoveryDirs()) {
    const proto = parseProto(path.join(dir, "proto_core.json"));
    const cursor = readJson(path.join(dir, "d0_working.json")) as WorkingState | null;
    if (!proto || !cursor) continue;
    if (proto.symbols.length === 0) continue;
    runs.push({ label: path.basename(path.dirname(dir)), proto, cursor });
  }
  return runs;
}

describe("free_symbols must survive parsing as ABSENT, not as empty", () => {
  // The whole fail-safe rests on this one property. A `.default([])` here — the shape
  // AssumptionSchema uses — would turn every legacy statement into a credible
  // "declared, uses no symbols" and scope every symbol change to nothing.
  it("StatementSchema leaves an undeclared free_symbols undefined", () => {
    const parsed = StatementSchema.parse({
      id: "thm:localized-upper",
      kind: "theorem",
      statement: "the localized and bounded estimator attains the risk bound",
      status: "to-prove",
    });
    expect(parsed.free_symbols).toBeUndefined();
  });

  it("DefinitionSchema leaves an undeclared free_symbols undefined", () => {
    const parsed = DefinitionSchema.parse({
      id: "def:exact-shell",
      name: "exact coverage shell",
      construction: "\\(\\mathcal M(d,C,D,\\eta)\\)",
    });
    expect(parsed.free_symbols).toBeUndefined();
  });

  it("an authored empty declaration survives as [] — a real, distinct declaration", () => {
    expect(
      StatementSchema.parse({
        id: "thm:a", kind: "theorem", statement: "s", status: "to-prove", free_symbols: [],
      }).free_symbols,
    ).toEqual([]);
    expect(
      DefinitionSchema.parse({ id: "def:a", name: "n", construction: "c", free_symbols: [] }).free_symbols,
    ).toEqual([]);
  });
});

describe("scoped symbol invalidation stays sound on every real legacy run", () => {
  const runs = realRuns();

  it("finds a non-trivial corpus (walker-rot canary)", () => {
    // The repo always carries banked runs; an empty list means the layout drifted, not
    // that there is nothing to check.
    expect(runs.length).toBeGreaterThanOrEqual(20);
  });

  it("no real statement or definition declares free_symbols — the case the fail-safe exists for", () => {
    const declaring: string[] = [];
    for (const { label, proto } of runs) {
      for (const s of proto.statements) if (s.free_symbols !== undefined) declaring.push(`${label}/${s.id}`);
      for (const d of proto.definitions ?? []) if (d.free_symbols !== undefined) declaring.push(`${label}/${d.id}`);
    }
    // If this ever fails, the corpus has moved on and the assertions below stop testing
    // the legacy path — they would be testing the scoped path instead.
    expect(declaring).toEqual([]);
  });

  it("a semantic symbol change reopens EVERY carried proof in every run", () => {
    const carriedTotal: number[] = [];
    const leaks: string[] = [];
    for (const { label, proto, cursor } of runs) {
      // The cursors predate `symbol_basis`; stamp the run's own proto as the basis these
      // proofs were solved against, which is what the first post-upgrade round does.
      const prev = { ...cursor, symbol_basis: symbolBasis(proto) } as WorkingState;
      const before = computeValidNodes(prev, proto);
      if (before.size === 0) continue; // nothing carried — no reuse decision to make
      carriedTotal.push(before.size);
      const moved = JSON.parse(JSON.stringify(proto)) as Core;
      moved.symbols[0] = { ...moved.symbols[0], space: `${moved.symbols[0].space ?? ""} [narrowed]` };
      const after = computeValidNodes(prev, moved);
      if (after.size > 0) leaks.push(`${label}: ${after.size}/${before.size} proofs carried through a symbol change`);
    }
    expect(leaks).toEqual([]);
    // Canary: if the corpus stopped carrying proofs the assertion above is vacuous.
    expect(carriedTotal.reduce((a, b) => a + b, 0)).toBeGreaterThan(100);
  });

  it("carries those same proofs when the symbol table is untouched (no mass re-derivation)", () => {
    // The mirror image: over-invalidation is a failure too. A round that changes nothing
    // must reuse everything the pre-scoping pipeline reused.
    const regressions: string[] = [];
    for (const { label, proto, cursor } of runs) {
      const prev = { ...cursor, symbol_basis: symbolBasis(proto) } as WorkingState;
      const withBasis = computeValidNodes(prev, proto);
      const withoutBasis = computeValidNodes({ ...cursor, symbol_basis: undefined } as WorkingState, proto);
      if (withBasis.size !== withoutBasis.size) {
        regressions.push(`${label}: ${withBasis.size} vs ${withoutBasis.size}`);
      }
    }
    expect(regressions).toEqual([]);
  });
});
