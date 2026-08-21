import { describe, expect, it } from "vitest";
import { access, readFile } from "node:fs/promises";
import { join } from "node:path";
import { presentationPrompt, promptContractFiles, VERDICT_ONLY_PROMPTS } from "../src/presentation/prompt_io.js";

const promptDir = join(import.meta.dirname, "..", "src", "presentation", "prompts");
const srcDir = join(import.meta.dirname, "..", "src");

describe("verdict-only contract digest wiring", () => {
  it("every VERDICT_ONLY_PROMPTS member has a template file and a dispatch site", async () => {
    // A phantom set entry silently keeps the full contracts on the real prompt
    // (audit finding: p3_equivalence never existed) — pin both properties.
    const { readdir } = await import("node:fs/promises");
    const walk = async (dir: string): Promise<string[]> => {
      const out: string[] = [];
      for (const e of await readdir(dir, { withFileTypes: true })) {
        const p = join(dir, e.name);
        if (e.isDirectory()) out.push(...await walk(p));
        // prompt_io.ts's own set literal would make the dispatch-site check vacuous.
        else if (e.name.endsWith(".ts") && e.name !== "prompt_io.ts") out.push(await readFile(p, "utf8"));
      }
      return out;
    };
    const sources = (await walk(srcDir)).join("\n");
    for (const name of VERDICT_ONLY_PROMPTS) {
      await expect(access(join(promptDir, `${name}.txt`))).resolves.toBeUndefined();
      expect(sources.includes(`"${name}"`)).toBe(true);
    }
  });

  it("verdict prompts get the digest; authoring prompts keep the full contracts", async () => {
    const digest = (await readFile(join(promptDir, "contract_digest.txt"), "utf8")).trim();
    const audit = await presentationPrompt("proof_audit", {
      obj_id: "x", proof_tex: "p", lean_proof_source: "l", notation_table: "n", paper_path: "f",
    });
    expect(audit).toContain(digest.slice(0, 40));
    expect(audit).not.toContain("GLOBAL READER-FACING PROSE CONTRACT");
    const author = await presentationPrompt("refine_proof", {
      obj_id: "x", proof_tex: "p", lean_proof_source: "l", referenced_defs: "r",
      audit_issues: "a", helper_lemma_envs: "h", informal_derivation: "i", notation_table: "n",
    });
    expect(author).not.toContain(digest.slice(0, 40));
    expect(promptContractFiles("refine_proof")).toEqual(["prose_style_contract", "cross_reference_contract"]);
  });
});
