import { describe, it, expect } from "vitest";
import { readdir, readFile } from "node:fs/promises";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { assertSealableLatexPayload } from "../../src/discovery/core/latex_serialization.js";

const ACTIVE = path.resolve(
  path.dirname(fileURLToPath(import.meta.url)), "..", "..", "..", "doc", "research", "active",
);

/** Every string field repairCoreLatexSerialization treats as LaTeX-bearing —
 * the pipeline's own canonical definition of "can carry TeX". Keep in sync. */
function latexFields(core: any, prefix: string): Array<[string, unknown]> {
  const out: Array<[string, unknown]> = [
    [`${prefix}.target_estimand`, core.target_estimand],
    [`${prefix}.estimand_functional`, core.estimand_functional],
    [`${prefix}.tldr`, core.tldr],
    [`${prefix}.related_work`, core.related_work],
    [`${prefix}.interpretation`, core.interpretation],
    [`${prefix}.technical_internal_limitation`, core.technical_internal_limitation],
    [`${prefix}.honest_scope`, core.honest_scope],
    [`${prefix}.project_justification.gap`, core.project_justification?.gap],
    [`${prefix}.project_justification.niche`, core.project_justification?.niche],
    [`${prefix}.project_justification.fill`, core.project_justification?.fill],
  ];
  for (const s of core.symbols ?? []) {
    for (const k of ["type", "space", "sig", "def", "role"]) out.push([`${prefix}:sym:${s.name}.${k}`, s[k]]);
  }
  for (const a of core.assumptions ?? []) {
    out.push([`${prefix}:${a.id}.condition`, a.condition]);
    out.push([`${prefix}:${a.id}.novel.justification`, a.novel?.justification]);
  }
  for (const d of core.definitions ?? []) {
    out.push([`${prefix}:${d.id}.name`, d.name]);
    out.push([`${prefix}:${d.id}.construction`, d.construction]);
  }
  for (const s of core.statements ?? []) {
    for (const k of ["statement", "proof_tex", "justification", "gap", "consumer"]) {
      out.push([`${prefix}:${s.id}.${k}`, s[k]]);
    }
  }
  for (const b of core.bibliography ?? []) out.push([`${prefix}:bib:${b.key}.citation`, b.citation]);
  return out;
}

describe("seal guard vs real corpus", () => {
  it("accepts every LaTeX-bearing field in the live core/proto corpus", async () => {
    // Opportunistic scan: the corpus only exists in a workspace with active
    // research runs (the public export ships none) — pass vacuously without it.
    let qids: string[];
    try { qids = await readdir(ACTIVE); } catch { return; }
    const failures: string[] = [];
    let fields = 0;
    for (const qid of qids) {
      for (const name of ["core.json", "proto_core.json"]) {
        const file = path.join(ACTIVE, qid, "discovery", name);
        let core: any;
        try { core = JSON.parse(await readFile(file, "utf8")); } catch { continue; }
        for (const [label, value] of latexFields(core, `${qid}/${name}`)) {
          if (typeof value !== "string" || value.length === 0) continue;
          fields += 1;
          try { assertSealableLatexPayload({ field: value }, label); }
          catch (e) { failures.push(`${label}: ${(e as Error).message.split("\n").slice(1, 3).join(" ")}`); }
        }
      }
    }
    console.log(`seal-guard corpus scan: ${fields} field(s) checked`);
    expect(failures).toEqual([]);
  }, 60000);
});
