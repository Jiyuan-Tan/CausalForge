import { describe, it, expect } from "vitest";
import { reconcileXrefAdvisories } from "../src/presentation/stage_util.js";

const PAPER = String.raw`
\begin{theoremv}{obj:thm:main}[Main]\label{obj:thm:main} Uses \cref{obj:def:estimator}. \end{theoremv}
\begin{definitionv}{obj:def:estimator}\label{obj:def:estimator} The estimator. \end{definitionv}
`;

describe("reconcileXrefAdvisories (P4 staleness check of P1 advisories)", () => {
  it("marks an advisory resolved when the flagged obj id is now referenced", () => {
    const out = reconcileXrefAdvisories(
      [{ gate: "xref-missing", detail: "thm:main never references \\ref{obj:def:estimator}" }],
      PAPER,
    );
    expect(out).toEqual([
      { advisory: { gate: "xref-missing", detail: "thm:main never references \\ref{obj:def:estimator}" }, resolved: true },
    ]);
  });
  it("keeps an advisory unresolved when the id is only ever a label, never referenced", () => {
    const paper = PAPER.replace("Uses \\cref{obj:def:estimator}. ", "");
    const [r] = reconcileXrefAdvisories(
      [{ gate: "xref-missing", detail: "thm:main never references \\ref{obj:def:estimator}" }],
      paper,
    );
    expect(r.resolved).toBe(false);
  });
  it("returns resolved:null when no obj id is named", () => {
    const [r] = reconcileXrefAdvisories([{ gate: "notation-reviewer", detail: "G_n undefined" }], PAPER);
    expect(r.resolved).toBeNull();
  });
});
