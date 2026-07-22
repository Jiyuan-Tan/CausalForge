import { readFileSync } from "node:fs";
import { MODELS } from "../src/models.js";
import { resolve, join } from "node:path";
import { execSync } from "node:child_process";
import { loadLibrary, isTier1, declArea, type LibDecl } from "../src/library/schema.js";

/**
 * NL docstring sweep: dispatch codex (batched per source file, ≤ FILES_PER_CALL files
 * per call) to (a) write/normalize the first-paragraph NL translation of tier-1 decls
 * per the rubric prompt, and (b) add missing top-of-file module docstrings. Verifies
 * each batch by rebuilding the touched modules.
 *
 * Usage: npx tsx bin/library_nl_sweep.ts --area <Area> [--apply] [--all] [--module-docs-only]
 *   default: dry-run (prints target counts per file)
 *   --apply: dispatch codex batches + lake build verification
 *   --all:   include decls that already have a docstring (normalization pass)
 *   --module-docs-only: skip decl docstrings entirely; only add missing top-of-file
 *     module docstrings (fast pass, larger batches)
 */

const args = process.argv.slice(2);
const areaIdx = args.indexOf("--area");
const area = areaIdx >= 0 ? args[areaIdx + 1] : null;
const apply = args.includes("--apply");
const all = args.includes("--all");
const moduleDocsOnly = args.includes("--module-docs-only");
// --no-verify: skip the per-batch lake build (comment-only edit passes; verify
// once at the end with a full build — useful when lake is contended).
const noVerify = args.includes("--no-verify");
if (!area) {
  console.error("usage: library_nl_sweep --area <Area> [--apply] [--all]");
  process.exit(1);
}

const root = resolve(import.meta.dirname, "..", "..", "..");
const lib = loadLibrary(root);

/** A file needs a module docstring if no `/-!` appears before its first declaration. */
function missingModuleDoc(file: string): boolean {
  let src: string;
  try {
    src = readFileSync(join(root, file), "utf8");
  } catch {
    return false;
  }
  const firstDecl = src.search(
    /^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+|unsafe\s+)*(?:theorem|lemma|def|abbrev|structure|class|inductive|instance|opaque|axiom)\b/m,
  );
  const head = firstDecl >= 0 ? src.slice(0, firstDecl) : src;
  return !head.includes("/-!");
}

const targets = moduleDocsOnly
  ? []
  : lib.entries.filter(
      (e) => declArea(e) === area && isTier1(e, lib.sidecars) && (all || !e.doc?.trim()),
    );
const byFile = new Map<string, LibDecl[]>();
for (const t of targets) byFile.set(t.file, [...(byFile.get(t.file) ?? []), t]);

// Files in this area lacking a module docstring (even with no decl targets).
const areaFiles = [...new Set(
  lib.entries.filter((e) => declArea(e) === area).map((e) => e.file),
)];
const noModDoc = new Set(areaFiles.filter(missingModuleDoc));
for (const f of noModDoc) if (!byFile.has(f)) byFile.set(f, []);

console.log(
  `${targets.length} target decls; ${noModDoc.size} files missing module docstring; ${byFile.size} files total (area ${area})`,
);
for (const [f, ds] of byFile) {
  const tags = [
    ds.length ? ds.map((d) => d.name.split(".").pop()).join(", ") : null,
    noModDoc.has(f) ? "+module-doc" : null,
  ].filter(Boolean);
  console.log(`  ${f}: ${tags.join(" ")}`);
}
if (!apply) process.exit(0);

const FILES_PER_CALL = moduleDocsOnly ? 15 : 6;
const promptTpl = readFileSync(
  resolve(import.meta.dirname, "..", "src", "library", "prompts", "nl_docstring.txt"),
  "utf8",
);
const files = [...byFile.keys()];
for (let i = 0; i < files.length; i += FILES_PER_CALL) {
  const batch = files.slice(i, i + FILES_PER_CALL);
  const lines = batch.flatMap((f) =>
    byFile
      .get(f)!
      .map((d) => `${d.file} : ${d.line} : ${d.name} : ${d.statement.replace(/\s+/g, " ")}`),
  );
  const modDocLines = batch.filter((f) => noModDoc.has(f));
  const prompt = promptTpl
    .replace("{{targets}}", lines.length ? lines.join("\n") : "(none in this batch)")
    .replace("{{module_doc_files}}", modDocLines.length ? modDocLines.join("\n") : "(none in this batch)");
  console.log(
    `codex batch ${i / FILES_PER_CALL + 1}/${Math.ceil(files.length / FILES_PER_CALL)}: ${batch.join(", ")}`,
  );
  execSync(
    `codex exec --full-auto -C ${root} --skip-git-repo-check -c windows.sandbox=unelevated ` +
      `-c model=${MODELS.codexKernel} -c model_reasoning_effort=medium`,
    { input: prompt, stdio: ["pipe", "inherit", "inherit"], timeout: 2400_000 },
  );
  if (!noVerify) {
    const modules = [...new Set(batch.map((f) => f.replace(/\//g, ".").replace(/\.lean$/, "")))];
    console.log(`verifying: lake build ${modules.join(" ")}`);
    execSync(`lake build ${modules.join(" ")}`, { cwd: root, stdio: "inherit", timeout: 2400_000 });
  }
}
console.log("sweep complete — rerun `lake exe library_index` to refresh the index");
