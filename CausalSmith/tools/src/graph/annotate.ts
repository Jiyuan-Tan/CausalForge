import { readFile, writeFile } from "node:fs/promises";
import path from "node:path";
import { parseLeanDecls } from "../formalization/crosswalk.js";
import { objIdToNodeId } from "./from_note.js";

/** Classify the declaration-leading lines through which an existing explicit node anchor may
 * legitimately bind: blank lines, line comments, block comments/docstrings, and attributes.
 * This mirrors the extractor's rule that an anchor may sit above a docstring. */
function declarationPreambleLines(lines: string[]): boolean[] {
  let depth = 0;
  return lines.map((line) => {
    const startDepth = depth;
    for (const token of line.match(/\/-|-\//g) ?? []) depth += token === "/-" ? 1 : -1;
    if (depth < 0) depth = 0;
    const trimmed = line.trim();
    return trimmed === "" || startDepth > 0 || trimmed.startsWith("--") ||
      trimmed.startsWith("/-") || trimmed.startsWith("@[");
  });
}

/** Whether the declaration already has an explicit anchor anywhere in its contiguous leading
 * preamble. Checking only the immediately preceding line is wrong when the canonical layout is
 * `@node`, then `/-- docstring -/`, then the declaration. */
function hasLeadingNodeAnnotation(lines: string[], headerIndex: number, preamble: boolean[]): boolean {
  for (let i = headerIndex - 1; i >= 0 && preamble[i]; i--) {
    if (/^\s*--\s*@node:\s*[A-Za-z0-9_:.-]+\s*$/.test(lines[i])) return true;
  }
  return false;
}

/**
 * Seed `-- @node: <id>` comments above every obj_id-bearing decl that lacks one.
 * The link is bootstrapped from the existing name convention (`parseLeanDecls`'s
 * `deriveObjId`); once written it is the authoritative, rename-survivable link the
 * extractor reads. The comment is inserted directly above the decl header line (so
 * it sits between any docstring and the `theorem`/`structure`/… keyword). Returns
 * the number of annotations inserted.
 */
export async function seedAnnotations(leanDir: string): Promise<number> {
  const decls = await parseLeanDecls(leanDir, { includeLemmas: true });
  const byFile = new Map<string, { line: number; id: string }[]>();
  for (const d of decls) {
    if (!d.objId) continue;
    if (!byFile.has(d.file)) byFile.set(d.file, []);
    byFile.get(d.file)!.push({ line: d.line, id: objIdToNodeId(d.objId) });
  }
  let inserted = 0;
  for (const [rel, edits] of byFile) {
    const abs = path.join(leanDir, rel);
    const lines = (await readFile(abs, "utf8")).split(/\r?\n/);
    const preamble = declarationPreambleLines(lines);
    edits.sort((a, b) => b.line - a.line); // bottom-up so earlier line indices stay valid
    let touched = false;
    for (const e of edits) {
      const headerIndex = e.line - 1;
      if (hasLeadingNodeAnnotation(lines, headerIndex, preamble)) continue;
      lines.splice(headerIndex, 0, `-- @node: ${e.id}`);
      // Bottom-up edits never alter the classification needed by an earlier declaration, but keep
      // the arrays aligned so this loop remains correct if two headers are adjacent.
      preamble.splice(headerIndex, 0, true);
      inserted++;
      touched = true;
    }
    if (touched) await writeFile(abs, lines.join("\n"), "utf8");
  }
  return inserted;
}
