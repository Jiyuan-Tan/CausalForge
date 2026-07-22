import { resolve } from "node:path";
import { readFileSync, writeFileSync } from "node:fs";
import {
  loadLibrary,
  naturalLanguageDoc,
  publishedModulesWithoutShortDescription,
  tier1DeclarationsWithoutNaturalLanguage,
  theoremFilesWithoutCuratedAnchor,
} from "../src/library/schema.js";

/**
 * Regenerate the per-declaration tables in doc/API.md from the docstring-canonical
 * library index (doc/library_index.json). Tables live inside marked regions:
 *
 *     <!-- GEN:Causalean.Graph.DAG -->
 *     | Decl | Signature | Description |
 *     | ...generated... |
 *     <!-- /GEN -->
 *
 * Everything outside the markers (narrative, construction patterns, usage examples) is
 * left untouched. The description column is each decl's docstring first paragraph; the
 * signature is derived from the compiled type. So API.md tables never need hand-editing —
 * edit the docstring and rerun this.
 *
 *   npx tsx bin/library_doc_gen.ts --module Causalean.Graph.DAG   # print one table
 *   npx tsx bin/library_doc_gen.ts --write                        # splice all GEN regions in API.md
 *   npx tsx bin/library_doc_gen.ts --check                        # CI: fail if any region is stale
 *
 * Flags: --root <repoRoot>  --api <path to API.md>
 */

type Entry = { name: string; statement: string; doc?: string | null; source?: string | null; module: string; line: number; kind: string };
type Index = { entries: Entry[]; modules: Record<string, string>; commit: string };

const argv = process.argv.slice(2);
const flag = (n: string): string | undefined => {
  const i = argv.indexOf(n);
  if (i < 0) return undefined;
  const v = argv[i + 1];
  argv.splice(i, 2);
  return v;
};
const bool = (n: string): boolean => {
  const i = argv.indexOf(n);
  if (i < 0) return false;
  argv.splice(i, 1);
  return true;
};

const root = resolve(flag("--root") ?? resolve(import.meta.dirname, "..", "..", ".."));
const apiPath = resolve(flag("--api") ?? resolve(root, "doc", "API.md"));
const oneModule = flag("--module");
const doWrite = bool("--write");
const doCheck = bool("--check");

let idx: Index;
try {
  idx = JSON.parse(readFileSync(resolve(root, "doc", "library_index.json"), "utf8"));
} catch {
  console.error(`No usable index at ${root}/doc/library_index.json (run \`lake exe library_index\`).`);
  process.exit(1);
}

const KINDS = new Set(["theorem", "def", "lemma", "structure", "inductive", "instance", "abbrev"]);
const isAuto = (n: string): boolean =>
  /\.(congr_simp|congr|noConfusion|rec|recAux|casesOn|below|brecOn|sizeOf|eq_def|ext_iff)$|\.go\b|^Causalean\.inst(DecidableEq|Repr|Inhabited|BEq|Hashable)/.test(n);

const ws = (s: string): string => (s || "").replace(/\s+/g, " ").trim();
const esc = (s: string): string => s.replace(/\|/g, "\\|");

// elaborated `statement` -> readable display signature
function topLevelComma(s: string): number {
  let d = 0;
  for (let i = 0; i < s.length; i++) {
    const c = s[i];
    if ("([{".includes(c)) d++;
    else if (")]}".includes(c)) d--;
    else if (c === "," && d === 0) return i;
  }
  return -1;
}
function stripBinders(s: string): string {
  s = s.trim();
  while (s[0] === "{" || s[0] === "[") {
    const open = s[0], close = open === "{" ? "}" : "]";
    let d = 0, end = -1;
    for (let i = 0; i < s.length; i++) {
      if (s[i] === open) d++;
      else if (s[i] === close) { d--; if (d === 0) { end = i; break; } }
    }
    if (end < 0) break;
    let rest = s.slice(end + 1).trim();
    if (rest.startsWith("→")) s = rest.slice(1).trim();
    else break;
  }
  return s;
}
function displaySig(statement: string, name: string): string {
  let s = ws(statement);
  if (s.startsWith("∀")) {
    s = s.slice(1).trim();
    const c = topLevelComma(s);
    return c >= 0 ? ws(s.slice(c + 1)) : s;
  }
  s = stripBinders(s);
  const owner = name.replace(/^Causalean\./, "").split(".").slice(0, -1).join(".");
  if (owner) {
    const re = new RegExp("^Causalean\\." + owner.replace(/[.*+?^${}()|[\]\\]/g, "\\$&") + "\\b[^→]*→\\s*");
    s = s.replace(re, "");
  }
  return ws(s);
}
const firstPara = (doc?: string): string => (doc && doc.trim() ? ws(doc.split(/\n\s*\n/)[0]).replace(/\*\*/g, "") : "");

function genTable(moduleName: string): string {
  const rows = idx.entries
    .filter((e) => e.module === moduleName && KINDS.has(e.kind) && !isAuto(e.name))
    .sort((a, b) => a.line - b.line)
    .map((e) => {
      const nm = e.name.replace(/^Causalean\./, "");
      return `| \`${nm}\` | \`${esc(displaySig(e.statement, e.name))}\` | ${esc(firstPara(naturalLanguageDoc(e) ?? undefined)) || "—"} |`;
    });
  if (!rows.length) return `_(no documented declarations in ${moduleName})_`;
  return ["| Decl | Signature | Description |", "|---|---|---|", ...rows].join("\n");
}

if (oneModule) {
  console.log(genTable(oneModule));
  process.exit(0);
}

// Publishing a regenerated API while a theorem-bearing source file has no curated result makes
// the corresponding library page look complete even though it has no mathematical anchor. This
// is deliberately a hard gate on the write/check paths used by promotion and documentation regen.
const library = loadLibrary(root);
const uncuratedTheoremFiles = theoremFilesWithoutCuratedAnchor(library);
if (uncuratedTheoremFiles.length > 0) {
  console.error(
    `UNCURATED THEOREM FILES (${uncuratedTheoremFiles.length}) — each file with public theorem/lemma declarations needs at least one matching headline_theorems entry before documentation can regenerate:\n  ` +
      uncuratedTheoremFiles.join("\n  "),
  );
  process.exit(1);
}

// Every explorer page needs a short description — both leaf modules backed by a Lean file and
// the intermediate namespace pages a new subtree creates without any file at that path. Do not
// publish a regenerated API that leaves one blank: provide a `/-! -/` module docstring (a
// description merged into the copyright `/- -/` header does NOT register as one) or a
// namespace_intros entry.
const undocumentedModules = publishedModulesWithoutShortDescription(library);
if (undocumentedModules.length > 0) {
  console.error(
    `UNDOCUMENTED PUBLISHED MODULES (${undocumentedModules.length}) — each explorer page needs a \`/-! -/\` module docstring or a matching doc/library_review/<Area>.json namespace_intros entry:\n  ` +
      undocumentedModules.join("\n  "),
  );
  process.exit(1);
}

// Declaration cards use their Lean docstrings as the natural-language layer.
// Publishing any tier-1 card without one would expose the site's missing-NL
// placeholder, so make that a promotion-time failure instead.
const declarationsWithoutNaturalLanguage = tier1DeclarationsWithoutNaturalLanguage(library);
if (declarationsWithoutNaturalLanguage.length > 0) {
  console.error(
    `MISSING NATURAL-LANGUAGE TRANSLATIONS (${declarationsWithoutNaturalLanguage.length}) — each published declaration card needs a non-empty Lean docstring:\n  ` +
      declarationsWithoutNaturalLanguage.join("\n  "),
  );
  process.exit(1);
}

// --write / --check : process GEN regions in API.md
const api = readFileSync(apiPath, "utf8");
const moduleIdent = String.raw`[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*`;
const re = new RegExp(
  String.raw`^(<!-- GEN:(${moduleIdent}) -->)[^\S\r\n]*\r?\n([\s\S]*?)^(<!-- /GEN -->)[^\S\r\n]*$`,
  "gm",
);
let stale = 0, total = 0;
const out = api.replace(re, (_m, open: string, mod: string, inner: string, close: string) => {
  total++;
  const fresh = genTable(mod);
  if (ws(inner) !== ws(fresh)) stale++;
  return `${open}\n${fresh}\n${close}`;
});

if (total === 0) {
  console.error(`No <!-- GEN:<module> --> regions found in ${apiPath}. Add markers around a per-decl table to manage it.`);
  process.exit(doCheck ? 0 : 1);
}
if (doCheck) {
  console.log(`[doc-gen] index @ ${idx.commit.slice(0, 7)} · ${total} GEN region(s) · ${stale} stale`);
  process.exit(stale ? 1 : 0);
}
if (doWrite) {
  writeFileSync(apiPath, out);
  console.log(`[doc-gen] wrote ${apiPath} · ${total} region(s) regenerated (${stale} had changed).`);
  process.exit(0);
}
console.error("specify --module <mod> | --write | --check");
process.exit(1);
