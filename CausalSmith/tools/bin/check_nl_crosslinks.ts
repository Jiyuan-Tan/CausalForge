import { readFileSync, readdirSync } from "node:fs";
import { join, resolve } from "node:path";
import {
  parseNlCrosslinks,
  crosslinkNames,
  linksGoal,
  sourceBinders,
  sourceFieldNames,
} from "../src/shared/nl_crosslinks.js";

/**
 * Lint for NL ↔ Lean crosslink annotations (`[phrase](hyp:name)` /
 * `[phrase](goal)` in docstring first paragraphs — see
 * src/shared/nl_crosslinks.ts for the convention).
 *
 * Usage: npx tsx bin/check_nl_crosslinks.ts [--root <causaleanRoot>] [--strict] [--verbose]
 *
 * Always an ERROR (exit 1):
 *   - a crosslink references a binder name absent from the decl's signature
 *     (drift: hypothesis renamed after the docstring was annotated);
 *   - crosslink markup outside the first paragraph (the NL translation is the
 *     only sanctioned home).
 *
 * Coverage (every hyp-classified binder + the goal linked) is reported as a
 * table; with --strict, HEADLINE theorems with annotations that are
 * incomplete, or headline theorems with no annotations at all, also exit 1 —
 * the gate for post-migration CI and for future Causalean promotions.
 */

const args = process.argv.slice(2);
const rootIdx = args.indexOf("--root");
const root =
  rootIdx >= 0 ? resolve(args[rootIdx + 1]) : resolve(import.meta.dirname, "..", "..", "..");
const strict = args.includes("--strict");
const verbose = args.includes("--verbose");

interface Entry {
  name: string;
  kind: string;
  file: string;
  line: number;
  doc?: string;
  source?: string;
}
const idx = JSON.parse(readFileSync(join(root, "doc", "library_index.json"), "utf8")) as {
  entries: Entry[];
};

// Freshness guard: this lint validates annotations THROUGH the derived index.
// If the Lean sources carry substantially more crosslink markers than the
// index's docstrings, the index is stale (docstrings edited without
// `lake build && lake exe library_index`) and every check below would pass
// VACUOUSLY over pre-edit text (adversarial-audit finding F1, 2026-08-17).
{
  const { execFileSync } = await import("node:child_process");
  let srcCount = 0;
  try {
    const out = execFileSync(
      "grep",
      ["-rc", "--include=*.lean", "](hyp:", join(root, "Causalean")],
      { encoding: "utf8", maxBuffer: 64 * 1024 * 1024 },
    );
    for (const l of out.split("\n")) {
      const n = Number(l.slice(l.lastIndexOf(":") + 1));
      if (Number.isFinite(n)) srcCount += n;
    }
  } catch (err) {
    // grep exits 1 when NO file matches — that is a real count of 0.
    const e = err as { status?: number; stdout?: string };
    if (e.status !== 1) throw err;
  }
  let idxCount = 0;
  for (const e of idx.entries) {
    if (e.name.startsWith("Causalean.") && e.doc) {
      idxCount += (e.doc.match(/\]\(hyp:/g) ?? []).length;
    }
  }
  // Line-based grep counts markers once per line; multi-marker lines make the
  // source count an undercount, so only a SOURCE ≫ INDEX gap signals staleness.
  if (srcCount > idxCount * 1.1 + 50) {
    console.error(
      `STALE INDEX: Causalean sources carry ~${srcCount} \`](hyp:\` marker lines but the ` +
        `index's docstrings only ${idxCount}. Regenerate before linting: ` +
        `lake build && lake exe library_index (then npm run embed:library).`,
    );
    process.exit(1);
  }
}

const headline = new Set<string>();
try {
  for (const f of readdirSync(join(root, "doc", "library_review"))) {
    if (!f.endsWith(".json")) continue;
    const d = JSON.parse(readFileSync(join(root, "doc", "library_review", f), "utf8"));
    for (const n of d.headline_theorems ?? []) headline.add(n);
  }
} catch {
  /* no sidecars: coverage gate simply has no headline set */
}

const errors: string[] = [];
const incomplete: string[] = [];
const unannotatedHeadline: string[] = [];
let annotated = 0;
let fullyCovered = 0;

// Theorems get the full treatment (name validation + hyp/goal coverage);
// structures/classes/defs get name validation only — a structure's crosslinks
// may target its parameter binders or its `where`-block fields, and it has no
// conclusion, so `(goal)` there is an error.
const KINDS = new Set(["theorem", "structure", "class", "def"]);
const decls = idx.entries.filter((e) => KINDS.has(e.kind) && e.name.startsWith("Causalean."));
const theorems = decls.filter((e) => e.kind === "theorem");

for (const e of decls) {
  const doc = e.doc ?? "";
  const paras = doc.trim().split(/\n\s*\n/);
  // Whitespace-collapsed, matching the site's nlOf: a crosslink marker wrapped
  // across a source line must parse the same here as on the rendered page.
  const firstPara = (paras[0] ?? "").replace(/\s+/g, " ");
  const rest = paras.slice(1).join("\n\n");
  const restLinks = parseNlCrosslinks(rest).filter((s) => s.links);
  if (restLinks.length > 0) {
    errors.push(`${e.name} (${e.file}:${e.line}): crosslink markup outside the first paragraph`);
  }
  const names = crosslinkNames(firstPara);
  const hasGoal = linksGoal(firstPara);
  if (names.length === 0 && !hasGoal) {
    if (e.kind === "theorem" && headline.has(e.name)) unannotatedHeadline.push(e.name);
    continue;
  }
  annotated++;
  if (hasGoal && e.kind !== "theorem") {
    errors.push(`${e.name} (${e.file}:${e.line}): (goal) crosslink on a ${e.kind} — no conclusion to link`);
  }
  const binders = e.source ? sourceBinders(e.source) : null;
  if (!binders) {
    // Unparseable signature: can't validate names — surface loudly in verbose,
    // but don't fail; the site falls back to unstructured rendering there too.
    if (verbose) console.log(`  (unparsed signature, names unchecked) ${e.name}`);
    continue;
  }
  const declared = new Set(binders.flatMap((b) => b.names));
  if (e.kind === "structure" || e.kind === "class") {
    for (const f of sourceFieldNames(e.source ?? "")) declared.add(f);
  }
  const unknown = names.filter((n) => !declared.has(n));
  if (unknown.length > 0) {
    errors.push(
      `${e.name} (${e.file}:${e.line}): crosslink names not in signature: ${unknown.join(", ")}`,
    );
  }
  if (e.kind !== "theorem") continue; // coverage gate is theorems-only
  const linked = new Set(names);
  const uncoveredHyps = binders.filter((b) => b.isHyp && !b.names.some((n) => linked.has(n)));
  if (uncoveredHyps.length === 0 && hasGoal) {
    fullyCovered++;
  } else {
    const what = [
      ...uncoveredHyps.map((b) => b.names.join(" ")),
      ...(hasGoal ? [] : ["(goal)"]),
    ];
    incomplete.push(`${e.name}: unlinked ${what.join(", ")}`);
  }
}

console.log(
  `nl-crosslinks: ${decls.length} Causalean decls (${theorems.length} theorems) · ` +
    `${annotated} annotated · ${fullyCovered} theorems fully covered · ` +
    `${incomplete.length} incomplete · ` +
    `${unannotatedHeadline.length}/${headline.size} headline theorems unannotated`,
);
if (verbose && incomplete.length > 0) {
  console.log(`\nIncomplete coverage:\n  ${incomplete.join("\n  ")}`);
}
if (verbose && unannotatedHeadline.length > 0) {
  console.log(`\nUnannotated headline theorems:\n  ${unannotatedHeadline.join("\n  ")}`);
}
if (errors.length > 0) {
  console.error(`\nERRORS (${errors.length}):\n  ${errors.join("\n  ")}`);
  process.exit(1);
}
if (strict && (incomplete.length > 0 || unannotatedHeadline.length > 0)) {
  console.error(
    `\n--strict: ${incomplete.length} theorems with incomplete coverage, ` +
      `${unannotatedHeadline.length} headline theorems unannotated`,
  );
  process.exit(1);
}
