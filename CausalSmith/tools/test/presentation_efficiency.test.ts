import { describe, expect, it } from "vitest";
import {
  applyTargetedReplacements,
  claimUnits,
  proseOnlyReplacements,
  revisionContext,
} from "../src/presentation/stages/p3_gates.js";
import { relevantNotation } from "../src/presentation/stages/p2_draft.js";
import { buildVerificationContract } from "../src/presentation/verification_contract.js";

describe("presentation token-efficiency helpers", () => {
  it("selects only artifact-relevant notation rows", () => {
    const notation = "q_n: schedule\nR_P: regret\nmu: mean";
    const selected = relevantNotation(notation, "The proof controls q_n.");
    expect(selected).toContain("q_n");
    expect(selected).not.toContain("R_P");
  });

  it("splits claim units and applies exact unique patches", () => {
    expect(claimUnits("First claim. Second claim!")).toHaveLength(2);
    expect(applyTargetedReplacements("alpha beta", [{ before: "beta", after: "gamma" }])).toBe("alpha gamma");
    expect(() => applyTargetedReplacements("x x", [{ before: "x", after: "y" }])).toThrow(/non-unique/);
  });

  it("selects relevant paragraphs rather than the whole paper", () => {
    const tex = "Introduction prose.\n\nA rate comparison is overstated.\n\nUnrelated appendix details.";
    expect(revisionContext(tex, ["fix the overstated rate comparison"])).toBe("A rate comparison is overstated.");
  });

  it("salvages prose edges when a revision improperly includes frozen environments", () => {
    const replacements = proseOnlyReplacements([{
      before: "Old prose.\n\n\\begin{definitionv}{d}Old body\\end{definitionv}\n\nSame tail.",
      after: "New prose.\n\n\\begin{definitionv}{d}Rewritten body\\end{definitionv}\n\nSame tail.",
    }]);
    expect(replacements).toEqual([{ before: "Old prose.\n\n", after: "New prose.\n\n" }]);
    expect(applyTargetedReplacements(
      "Old prose.\n\n\\begin{definitionv}{d}Canonical body\\end{definitionv}\n\nSame tail.",
      replacements,
    )).toContain("New prose.\n\n\\begin{definitionv}{d}Canonical body");
  });

  it("deduplicates repeated Lean declarations in the P5 contract", () => {
    const formal = {
      commit: "abc",
      blocks: ["a", "b"].map((obj_id) => ({
        obj_id, alias: null, kind: "theorem", env: "theoremv", title: null,
        body: `statement ${obj_id}`, ref_set: [], lean: { decl: "shared", file: "X.lean" },
        status: "matched", provenance: "from-note", body_hash: `hash-${obj_id}`,
      })),
    };
    const snippets = {
      commit: "abc",
      snippets: Object.fromEntries(["a", "b"].map((id) => [id, {
        decl: "shared", file: "X.lean", line: 1, statement: "theorem shared : True", sorry_free: true, axioms: null,
      }])),
    };
    const contract = buildVerificationContract(formal, snippets);
    expect(Object.keys(contract.declarations)).toHaveLength(1);
    expect(contract.objects[0].lean?.declaration_refs).toEqual(contract.objects[1].lean?.declaration_refs);
  });
});
