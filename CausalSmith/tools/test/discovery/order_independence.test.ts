// Dispatch-unit labels must be decided by CONTENT, never by array position. The label
// decides ownership -- which unit may emit which node -- so if it depends on input order,
// two semantically identical cores grant different write capabilities. `find` returned the
// first headline in SOURCE order. Audit triage 2026-07-20 (class T7).

import { describe, it, expect } from "vitest";
import { groupToProveByComponent } from "../../src/discovery/stages/d0_solve.js";
import type { CoreStatement } from "../../src/discovery/core/schema.js";

const mk = (id: string, kind: string, depends_on: string[] = []): CoreStatement =>
  ({ id, kind, statement: "S", depends_on, status: "to-prove" }) as never;

// One connected component holding TWO theorems: whichever leads must not depend on order.
const alpha = mk("thm:alpha", "theorem", ["lem:shared"]);
const beta = mk("thm:beta", "theorem", ["lem:shared"]);
const shared = mk("lem:shared", "lemma");

const labels = (sts: CoreStatement[]): string[] =>
  groupToProveByComponent(sts).map((u) => u.label).sort();

describe("unit labels do not depend on statement order", () => {
  it("elects the same lead for a reordered core", () => {
    expect(labels([alpha, beta, shared])).toEqual(labels([beta, alpha, shared]));
    expect(labels([shared, beta, alpha])).toEqual(labels([alpha, beta, shared]));
  });

  it("picks the lexically first headline, not the first listed", () => {
    // Deterministic and independent of input order: alpha < beta.
    expect(labels([beta, alpha, shared])).toEqual(["thm:alpha"]);
  });

  it("prefers a headline kind over a lemma wherever the lemma appears", () => {
    for (const arrangement of [[shared, alpha], [alpha, shared]]) {
      expect(labels(arrangement)[0].startsWith("thm:"),
        "a headline must lead its component").toBe(true);
    }
  });
});
