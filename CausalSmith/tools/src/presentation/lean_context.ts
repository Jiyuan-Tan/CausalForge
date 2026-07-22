import { readFile } from "node:fs/promises";
import { join } from "node:path";
import { parseLeanDecls } from "../formalization/crosswalk.js";
import { extractDeclSnippet } from "./lean_extract.js";

/** The authoritative Lean context for one declaration: its signature plus the bodies of the
 *  definitions/abbrevs/structures it references. This is the same context the statement equivalence
 *  refiner uses to judge faithfulness — surfaced here so P1 can render a statement DIRECTLY from the Lean
 *  (complete + curated) instead of from a possibly-loose natural-language headline. */
export interface LeanContext {
  /** The decl's statement (signature up to `:=` for a theorem/lemma; the body for a def). */
  statement: string;
  /** One-hop inlined bodies of the def/abbrev/structure names the statement references. */
  referencedDefs: string;
  /** Human pointer: `file: … / declaration: …`. */
  pointer: string;
}

export interface LeanContextIndex {
  contextFor(decl: { decl_name: string; file: string; line?: number }): Promise<LeanContext | null>;
}

/**
 * Build a reusable index over a Lean source tree. `contextFor` returns a decl's signature plus the
 * inlined bodies of the local definitions it references (capped, best-effort). Source files and the
 * def-name index are read once and cached, so calling it per-declaration across a stage is cheap.
 */
export async function buildLeanContextIndex(repoRoot: string, leanSubdir: string): Promise<LeanContextIndex> {
  const leanDir = join(repoRoot, leanSubdir);
  const srcCache = new Map<string, string>();
  const source = async (file: string): Promise<string> => {
    let s = srcCache.get(file);
    if (s === undefined) {
      s = await readFile(join(leanDir, file), "utf8");
      srcCache.set(file, s);
    }
    return s;
  };

  // One-hop index of inlinable referents (a name → where its def/abbrev/structure lives).
  const inlineKinds = new Set(["def", "abbrev", "structure"]);
  const refDeclByName = new Map<string, { file: string; line: number; declKind: string }>();
  try {
    for (const d of await parseLeanDecls(leanDir, {})) {
      if (inlineKinds.has(d.declKind) && !refDeclByName.has(d.name)) {
        refDeclByName.set(d.name, { file: d.file, line: d.line, declKind: d.declKind });
      }
    }
  } catch {
    /* best-effort: a render still has the signature even without inlined defs */
  }

  const unfoldReferencedDefs = async (leanText: string): Promise<string> => {
    const names = new Set(leanText.match(/[A-Za-z_][A-Za-z0-9_']*/g) ?? []);
    const inlined: string[] = [];
    for (const nm of names) {
      if (inlined.length >= 12) break; // cap context size (same bound P3's refiner uses)
      const loc = refDeclByName.get(nm);
      if (!loc) continue;
      try {
        const snip = extractDeclSnippet(await source(loc.file), nm, loc.line);
        if (snip) inlined.push(`-- ${nm} (${loc.declKind}) in ${loc.file}\n${snip}`);
      } catch {
        /* skip a decl whose body can't be extracted */
      }
    }
    return inlined.join("\n\n");
  };

  return {
    async contextFor(decl): Promise<LeanContext | null> {
      try {
        const statement = extractDeclSnippet(await source(decl.file), decl.decl_name, decl.line ?? 0);
        if (!statement || !statement.trim()) return null;
        return {
          statement,
          referencedDefs: await unfoldReferencedDefs(statement),
          pointer: `file: ${decl.file}\ndeclaration: ${decl.decl_name}`,
        };
      } catch {
        return null;
      }
    },
  };
}
