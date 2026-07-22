/**
 * One-off: re-extract `statement` fields in a bundle's lean_snippets.json using
 * the current lean_extract (fixes snippets captured with an older/buggy
 * extractor). Preserves decl/file/line/sorry_free/axioms/components structure;
 * only the extracted source text is refreshed. Usage:
 *   npx tsx scripts/dev/regen_snippets.ts <bundleDir>
 */
import { readFile, writeFile } from "node:fs/promises";
import { join } from "node:path";
import { extractDeclSnippet, extractHypothesisBinders } from "../../src/presentation/lean_extract.js";

const bundleDir = process.argv[2];
if (!bundleDir) throw new Error("usage: regen_snippets.ts <bundleDir>");

const repoRoot = join(import.meta.dirname, "..", "..");
const crosswalk = JSON.parse(await readFile(join(bundleDir, "presentation_crosswalk.json"), "utf8"));
const leanSubdir: string = crosswalk.lean_subdir;
const snippetsDoc = JSON.parse(await readFile(join(bundleDir, "lean_snippets.json"), "utf8"));
const snippets: Record<string, any> = snippetsDoc.snippets;

const sources = new Map<string, string>();
const src = async (file: string) => {
  const p = join(repoRoot, leanSubdir, file);
  if (!sources.has(p)) sources.set(p, await readFile(p, "utf8"));
  return sources.get(p)!;
};

let changed = 0;
for (const [objId, s] of Object.entries(snippets)) {
  if (s.components) {
    // composite: re-extract each part by matching its label to a decl
    for (const part of s.components) {
      const cw = crosswalk.entries.find((e: any) => e.lean?.decl === part.label);
      if (cw?.lean) {
        const before = part.statement;
        part.statement = extractDeclSnippet(await src(cw.lean.file), cw.lean.decl, cw.lean.line);
        if (part.statement !== before) changed++;
      }
    }
    continue;
  }
  if (s.decl && s.decl !== "(composite)" && s.file) {
    const before = s.statement;
    s.statement = extractDeclSnippet(await src(s.file), s.decl, s.line);
    if (s.statement !== before) {
      changed++;
      console.log(`  refreshed ${objId} (${s.decl})`);
    }
  }
}
await writeFile(join(bundleDir, "lean_snippets.json"), JSON.stringify(snippetsDoc, null, 2) + "\n", "utf8");
console.log(`regen_snippets: ${changed} statement(s) refreshed → ${bundleDir}/lean_snippets.json`);
