#!/usr/bin/env node
/**
 * C4 — presentation-bundle Lean cache integrity lint.
 *
 * Every published bundle under `doc/presentation/<bundle>/` carries generated
 * caches that describe the paper's Lean content: `paper_library_index.json`
 * (decl-level source/docstring/line — drives the site's Formalization tab),
 * `lean_snippets.json`, and `presentation_crosswalk.json`. They are emitted by
 * P4 and then go stale silently: the extractor exits 0 and writes valid JSON
 * even when it drops declarations or blanks a field.
 *
 * Two checks run:
 *
 *   SNAPSHOT — validate each bundle against the live Lean tree:
 *     stale-source        cached `source` no longer appears in the file it cites
 *     source-misplaced    cached `source` does not start at its recorded line
 *     doc-source-mismatch cached `doc` differs from the leading source doc-comment
 *     misattributed-source  cached `source` opens with a DIFFERENT declaration
 *                         (the extractor's preceding-docstring search stole the
 *                         neighbour's doc block, so `doc` is the wrong text)
 *     stale-snippet       `lean_snippets.json` statement no longer in its file
 *     missing-file        entry cites a `.lean` file that no longer exists
 *     line-past-eof       recorded line is beyond the end of that file
 *     line-zero           no source position recorded (site cannot deep-link)
 *     null-source         populated-by-design field is null
 *     crosswalk-module-gap  a module the crosswalk names is absent from the index
 *                         (the P4 module list is crosswalk-only, so a leaf module
 *                         nothing imports silently drops all of its declarations)
 *     orphan-module      a physical run module contains a public theorem/lemma/def
 *                         but contributes no declarations to the index
 *     dangling-crosswalk-decl  crosswalk anchor resolves to no indexed declaration
 *     foreign-prefix      an indexed declaration was emitted from outside this
 *                         bundle's own Lean module tree
 *
 *   REGRESSION (`--vs <ref>`, default HEAD; `--no-vs` to skip) — diff each
 *   `paper_library_index.json` against the same path at a git ref. This is the
 *   check that catches a bad regeneration BEFORE it is committed:
 *     lost-decl           a declaration present at the ref is gone now
 *     field-nulled        a field that was populated at the ref is now null
 *   Both are hard failures. `gained-decl` is reported once per declaration for
 *   review, never fails.
 *
 * `doc: null` is NOT reported: a declaration with no docstring is legitimate.
 *
 * Usage:
 *   npx tsx tools/bin/check_paper_indexes.ts              # human-readable report
 *   npx tsx tools/bin/check_paper_indexes.ts --json       # machine-readable JSON
 *   npx tsx tools/bin/check_paper_indexes.ts --strict     # exit 1 on any hard failure
 *   npx tsx tools/bin/check_paper_indexes.ts --vs <ref>   # diff against <ref> (default HEAD)
 *   npx tsx tools/bin/check_paper_indexes.ts --no-vs      # snapshot checks only
 *   npx tsx tools/bin/check_paper_indexes.ts --bundle <name>   # restrict (repeatable)
 *
 * Exit code: 0 (report-only) unless `--strict`, where any hard failure yields 1.
 */
import { execFileSync } from "node:child_process";
import { existsSync, readFileSync } from "node:fs";
import { readdir, readFile } from "node:fs/promises";
import path from "node:path";
import process from "node:process";
import { findOrphanPaperModules, SYNTHETIC_COMPANION_RE } from "../src/presentation/paper_index_orphans.js";

/** Severities that fail `--strict`. Everything else is informational. */
const HARD = new Set([
  "lost-decl",
  "field-nulled",
  "stale-source",
  "source-misplaced",
  "doc-source-mismatch",
  "misattributed-source",
  "stale-snippet",
  "missing-file",
  "line-past-eof",
  "line-zero",
  "null-source",
  "null-field",
  "crosswalk-module-gap",
  "orphan-module",
  "dangling-crosswalk-decl",
  "foreign-prefix",
  "unreadable",
]);

/** Fields whose disappearance (populated → null) is a regression. */
const TRACKED_FIELDS = ["source", "doc", "module", "file", "statement", "kind", "line"] as const;

interface Finding {
  severity: string;
  subject: string;
  note: string;
}

interface BundleReport {
  bundle: string;
  leanSubdir: string | null;
  entries: number;
  pinnedCommit: string | null;
  pinDriftCommits: number | null;
  findings: Finding[];
  error?: string;
}

interface DeclEntry {
  name: string;
  module: string | null;
  file: string | null;
  line: number | null;
  kind: string | null;
  statement: string | null;
  source: string | null;
  doc: string | null;
}

interface PaperIndex {
  commit?: string;
  modules?: Record<string, unknown>;
  entries: DeclEntry[];
}

interface CrosswalkEntry {
  obj_id?: string;
  lean?: { file?: string; decl?: string } | null;
}

/** `prefix` itself and its descendants, but never a textual lookalike. */
function isWithinModulePrefix(moduleName: string, prefix: string): boolean {
  return moduleName === prefix || moduleName.startsWith(`${prefix}.`);
}

function findCausalSmithRoot(start: string): string {
  let cur = path.resolve(start);
  for (;;) {
    const lakefile = path.join(cur, "lakefile.toml");
    if (existsSync(lakefile)) {
      try {
        if (/^\s*name\s*=\s*"CausalSmith"/m.test(readFileSync(lakefile, "utf8"))) return cur;
      } catch {
        /* fall through */
      }
    }
    const parent = path.dirname(cur);
    if (parent === cur) throw new Error(`Could not locate CausalSmith package root from ${start}`);
    cur = parent;
  }
}

/** Both extractors cap long slices with a `-- … truncated …` sentinel; drop it before matching. */
const TRUNCATION = /\n[ \t]*-- … \(?truncated[\s\S]*$/;
function untruncate(s: string): string {
  return s.replace(TRUNCATION, "");
}

/** Ignore line-ending whitespace while preserving source line structure. */
function trimLineEnd(line: string): string {
  return line.replace(/\s+$/, "");
}

/** The contents of a leading Lean doc-comment, respecting nested block comments. */
function leadingDocComment(source: string): string | null {
  if (!source.startsWith("/--")) return null;
  let depth = 1;
  let pos = 3;
  while (pos < source.length) {
    if (source.startsWith("/-", pos)) {
      depth += 1;
      pos += 2;
    } else if (source.startsWith("-/", pos)) {
      depth -= 1;
      if (depth === 0) return source.slice(3, pos);
      pos += 2;
    } else {
      pos += 1;
    }
  }
  return null;
}

function normalizeDocText(text: string): string {
  return text.replace(/\s+/g, " ").trim();
}

const DECL_HEAD =
  /^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable |unsafe |partial |scoped |local )*(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque)\s+([A-Za-z_][A-Za-z0-9_'!?.«»]*)/;

/**
 * Leaf name of the first column-0 declaration inside a cached source slice,
 * skipping block comments. `null` when the slice declares nothing recognisable.
 */
function firstDeclaredLeaf(source: string): string | null {
  let depth = 0;
  for (const line of source.split("\n")) {
    const t = line.trim();
    if (depth > 0 || t.startsWith("/-")) {
      depth += (t.match(/\/-/g)?.length ?? 0) - (t.match(/-\//g)?.length ?? 0);
      if (depth < 0) depth = 0;
      continue;
    }
    if (line.length === 0 || line[0] === " " || line[0] === "\t") continue;
    const m = DECL_HEAD.exec(line);
    if (m) return m[1].split(".").pop()!;
  }
  return null;
}

function gitShow(repoRoot: string, ref: string, relPath: string): string | null {
  try {
    return execFileSync("git", ["show", `${ref}:${relPath}`], {
      cwd: repoRoot,
      encoding: "utf8",
      maxBuffer: 64 * 1024 * 1024,
      stdio: ["ignore", "pipe", "ignore"],
    });
  } catch {
    return null; // path absent at that ref (new bundle) — nothing to regress against
  }
}

function gitCountCommitsSince(repoRoot: string, commit: string, relPath: string): number | null {
  try {
    const out = execFileSync("git", ["rev-list", "--count", `${commit}..HEAD`, "--", relPath], {
      cwd: repoRoot,
      encoding: "utf8",
      stdio: ["ignore", "pipe", "ignore"],
    });
    return Number(out.trim());
  } catch {
    return null;
  }
}

async function lintBundle(
  repoRoot: string,
  csRoot: string,
  bundleDir: string,
  opts: { vs: string | null },
): Promise<BundleReport> {
  const bundle = path.basename(bundleDir);
  const rep: BundleReport = {
    bundle,
    leanSubdir: null,
    entries: 0,
    pinnedCommit: null,
    pinDriftCommits: null,
    findings: [],
  };
  const add = (severity: string, subject: string, note: string) =>
    rep.findings.push({ severity, subject, note });

  const indexPath = path.join(bundleDir, "paper_library_index.json");
  if (!existsSync(indexPath)) return { ...rep, error: "no paper_library_index.json" };

  let idx: PaperIndex;
  try {
    idx = JSON.parse(await readFile(indexPath, "utf8"));
  } catch {
    return { ...rep, error: "paper_library_index.json unreadable" };
  }
  if (!Array.isArray(idx.entries)) return { ...rep, error: "paper_library_index.json has no entries array" };
  rep.entries = idx.entries.length;
  rep.pinnedCommit = idx.commit ?? null;

  const cwPath = path.join(bundleDir, "presentation_crosswalk.json");
  let crosswalk: { lean_subdir?: string; entries?: CrosswalkEntry[] } | null = null;
  if (existsSync(cwPath)) {
    try {
      crosswalk = JSON.parse(await readFile(cwPath, "utf8"));
    } catch {
      add("unreadable", "presentation_crosswalk.json", "JSON parse failed");
    }
  }
  const subdir = crosswalk?.lean_subdir ?? null;
  const ownModulePrefix = subdir?.replaceAll("/", ".") ?? null;
  rep.leanSubdir = subdir;
  if (subdir && rep.pinnedCommit) {
    rep.pinDriftCommits = gitCountCommitsSince(
      repoRoot,
      rep.pinnedCommit,
      path.posix.join("CausalSmith", subdir),
    );
  }

  // ---- snapshot: entries against the live tree
  const fileCache = new Map<string, string | null>();
  const textOf = (rel: string): string | null => {
    if (!fileCache.has(rel)) {
      const abs = path.join(csRoot, rel);
      fileCache.set(rel, existsSync(abs) ? readFileSync(abs, "utf8") : null);
    }
    return fileCache.get(rel)!;
  };

  for (const e of idx.entries) {
    if (!e.source) add("null-source", e.name, "no cached source slice");
    if (!e.module) add("null-field", e.name, "module is null");
    else if (ownModulePrefix && !isWithinModulePrefix(e.module, ownModulePrefix))
      add(
        "foreign-prefix",
        e.name,
        `declaring module \`${e.module}\` lies outside bundle prefix \`${ownModulePrefix}\``,
      );
    if (!e.file) {
      add("null-field", e.name, "file is null");
      continue;
    }
    const text = textOf(e.file);
    if (text === null) {
      add("missing-file", e.name, `cites ${e.file}, which does not exist`);
      continue;
    }
    if (e.line === null || e.line === 0) add("line-zero", e.name, `no source position in ${e.file}`);
    else if (e.line !== null && e.line > text.split("\n").length)
      add("line-past-eof", e.name, `line ${e.line} past end of ${e.file}`);
    if (e.source) {
      const source = untruncate(e.source);
      if (!text.includes(source))
        add("stale-source", e.name, `cached source is not in ${e.file} at ${e.line} any more`);
      if (e.line !== null && e.line > 0) {
        const fileLines = text.split("\n");
        const srcLines = source.split("\n");
        const anchored = srcLines.every(
          (line, i) => trimLineEnd(fileLines[e.line! - 1 + i] ?? "") === trimLineEnd(line),
        );
        if (!anchored)
          add("source-misplaced", e.name, `cached source does not start at ${e.file}:${e.line}`);
      }
      const sourceDoc = leadingDocComment(source);
      if (sourceDoc !== null && normalizeDocText(sourceDoc) !== normalizeDocText(e.doc ?? ""))
        add("doc-source-mismatch", e.name, "cached doc differs from the leading source doc-comment");
      const declared = firstDeclaredLeaf(e.source);
      const leaf = e.name.split(".").pop()!;
      if (declared !== null && declared !== leaf && !e.name.endsWith(`.${declared}`))
        add(
          "misattributed-source",
          e.name,
          `cached source/doc actually belongs to \`${declared}\` (neighbouring declaration)`,
        );
    }
  }

  // ---- module coverage: every crosswalk module must be represented.  Do not
  // require every `.lean` file under the run: P4 deliberately imports the
  // crosswalk ∪ prior-index modules, because importing unrelated siblings can
  // change module ownership and erase source metadata.
  const indexedModules = new Set(Object.keys(idx.modules ?? {}));
  const entryModules = new Set(idx.entries.map((e) => e.module).filter((m): m is string => !!m));
  if (subdir) {
    const prefix = subdir.replaceAll("/", ".");
    for (const ce of crosswalk?.entries ?? []) {
      const f = ce.lean?.file;
      if (!f) continue;
      const mod = `${prefix}.${f.slice(0, -".lean".length).replaceAll("/", ".")}`;
      if (!indexedModules.has(mod) && !entryModules.has(mod))
        add("crosswalk-module-gap", mod, `named by crosswalk ${ce.obj_id ?? "?"} but absent from the index`);
    }

    // A brand-new leaf module appears in neither the crosswalk nor a prior
    // index, so P4 never passes it to the extractor. Detect that blind spot
    // from the physical run tree, but spare comment-only/private-only modules.
    const runDir = path.join(csRoot, subdir);
    for (const orphan of await findOrphanPaperModules(runDir, prefix, entryModules)) {
      add(
        "orphan-module",
        orphan.module,
        `${orphan.file} contains a public theorem/lemma/def but contributes zero index entries`,
      );
    }
  }

  // ---- crosswalk anchors must resolve to an indexed declaration
  const byName = new Map(idx.entries.map((e) => [e.name, e]));
  const byLeaf = new Map<string, DeclEntry[]>();
  for (const e of idx.entries) {
    const leaf = e.name.split(".").pop()!;
    byLeaf.set(leaf, [...(byLeaf.get(leaf) ?? []), e]);
  }
  for (const ce of crosswalk?.entries ?? []) {
    const decl = ce.lean?.decl;
    if (!decl) continue;
    if (byName.has(decl)) continue;
    // aux_* anchors record a short (leaf) name rather than the full one
    if ((byLeaf.get(decl.split(".").pop()!) ?? []).length > 0) continue;
    add("dangling-crosswalk-decl", `${ce.obj_id ?? "?"} → ${decl}`, "resolves to no indexed declaration");
  }

  // ---- lean_snippets staleness (P4 owns this file; a finding means "rerun P4")
  const snPath = path.join(bundleDir, "lean_snippets.json");
  if (existsSync(snPath) && subdir) {
    try {
      const sn = JSON.parse(await readFile(snPath, "utf8")) as {
        snippets: Record<string, { decl?: string; file?: string; statement?: string }>;
      };
      for (const [oid, s] of Object.entries(sn.snippets ?? {})) {
        if (!s.statement || !s.file) continue;
        const rel = path.posix.join(subdir, s.file);
        const text = textOf(rel);
        if (text === null) {
          add("missing-file", `lean_snippets:${oid}`, `cites ${rel}, which does not exist`);
          continue;
        }
        if (!text.includes(untruncate(s.statement)))
          add("stale-snippet", `lean_snippets:${oid}`, `cached statement of \`${s.decl}\` is not in ${s.file} any more`);
      }
    } catch {
      add("unreadable", "lean_snippets.json", "JSON parse failed");
    }
  }

  // ---- regression: this file vs the same path at a git ref
  if (opts.vs) {
    const rel = path.relative(repoRoot, indexPath).replaceAll(path.sep, "/");
    const prevRaw = gitShow(repoRoot, opts.vs, rel);
    if (prevRaw !== null) {
      let prev: PaperIndex | null = null;
      try {
        prev = JSON.parse(prevRaw);
      } catch {
        add("unreadable", `${opts.vs}:${rel}`, "JSON parse failed at ref");
      }
      if (prev) {
        const now = new Map(idx.entries.map((e) => [e.name, e]));
        const before = new Map(prev.entries.map((e) => [e.name, e]));
        for (const e of idx.entries) {
          if (!before.has(e.name))
            add("gained-decl", e.name, `not present at ${opts.vs}`);
        }
        for (const p of prev.entries) {
          const cur = now.get(p.name);
          if (!cur) {
            // Lean-generated synthetic companions (`congr_simp`, equation
            // lemmas) have neither source nor a stable authored identity.
            // Older extractor output could give one a borrowed neighbour's
            // source slice or an `add_decl_doc` range, so a repair may now
            // drop it even when the old cache appeared locatable.
            if (SYNTHETIC_COMPANION_RE.test(p.name)) {
              add("dropped-synthetic", p.name, `unlocatable generated entry at ${opts.vs} omitted now`);
              continue;
            }
            // A regeneration must preserve the prior published declaration set.
            // Intentional source removals require an explicit cache migration,
            // rather than silently deleting a Formalization-tab target.
            add("lost-decl", p.name, `present at ${opts.vs}, absent now`);
            continue;
          }
          for (const f of TRACKED_FIELDS) {
            const was = p[f];
            const is = cur[f];
            // A docstring becoming null is an intended repair only when the
            // old cached source demonstrably opened with a different
            // declaration — the historical preceding-doc-comment bug.  Do
            // not exempt ordinary undocumented declarations from regression
            // protection.
            const correctedBorrowedDoc =
              f === "doc" &&
              was !== null &&
              was !== undefined &&
              (is === null || is === undefined) &&
              !!p.source &&
              (() => {
                const declared = firstDeclaredLeaf(p.source!);
                const leaf = p.name.split(".").pop()!;
                const syntheticDocTarget =
                  /\badd_decl_doc\s+(\S+\.(?:congr_simp|eq_def|eq_unfold|eq_\d+))\b/.exec(p.source!)?.[1] ?? null;
                const precedingDecl =
                  declared !== null && declared !== leaf && !p.name.endsWith(`.${declared}`)
                    ? declared
                    : null;
                if (precedingDecl === null && syntheticDocTarget === null) return false;
                // The exemption is deliberately evidence-based: the old text
                // must be exactly the cached docstring of the preceding
                // declaration named by the old source slice.  A merely
                // suspicious range is not enough to waive a regression.
                return prev.entries.some((neighbour) =>
                  neighbour.name !== p.name &&
                  (neighbour.name.split(".").pop() === precedingDecl ||
                    neighbour.name === syntheticDocTarget ||
                    neighbour.name.endsWith(`.${syntheticDocTarget}`)) &&
                  neighbour.doc === was,
                );
              })();
            if (correctedBorrowedDoc)
              add("corrected-borrowed-doc", p.name, `borrowed docstring at ${opts.vs} removed now`);
            else if (was !== null && was !== undefined && (is === null || is === undefined))
              add("field-nulled", p.name, `\`${f}\` was populated at ${opts.vs}, now null`);
            if (f === "line" && was !== 0 && is === 0)
              add("field-nulled", p.name, `\`line\` was ${was} at ${opts.vs}, now 0`);
          }
        }
      }
    }
  }

  return rep;
}

async function main(): Promise<void> {
  const argv = process.argv.slice(2);
  const asJson = argv.includes("--json");
  const strict = argv.includes("--strict");
  const noVs = argv.includes("--no-vs");
  const vsIdx = argv.indexOf("--vs");
  const vs = noVs ? null : vsIdx >= 0 ? (argv[vsIdx + 1] ?? "HEAD") : "HEAD";
  const only = new Set(argv.flatMap((a, i) => (a === "--bundle" ? [argv[i + 1]] : [])).filter(Boolean));

  const csRoot = findCausalSmithRoot(process.cwd());
  const repoRoot = path.dirname(csRoot);
  const presRoot = path.join(csRoot, "doc/presentation");

  const dirs = (await readdir(presRoot, { withFileTypes: true }))
    .filter((d) => d.isDirectory() && (only.size === 0 || only.has(d.name)))
    .map((d) => path.join(presRoot, d.name))
    .sort();

  const reports: BundleReport[] = [];
  for (const d of dirs) reports.push(await lintBundle(repoRoot, csRoot, d, { vs }));

  const hardCount = (r: BundleReport) => r.findings.filter((f) => HARD.has(f.severity)).length;
  const failed = reports.filter((r) => hardCount(r) > 0 || r.error);

  if (asJson) {
    console.log(JSON.stringify(reports, null, 2));
  } else {
    console.log(
      `Presentation-bundle Lean cache integrity — ${reports.length} bundle(s)` +
        (vs ? `, regression-checked against ${vs}\n` : ", snapshot only\n"),
    );
    for (const r of reports) {
      const drift =
        r.pinDriftCommits && r.pinDriftCommits > 0 ? `  [pin ${r.pinnedCommit?.slice(0, 8)} is ${r.pinDriftCommits} commit(s) behind its Lean dir]` : "";
      const head = `${r.bundle}  (${r.entries} decls)${drift}`;
      if (r.error) {
        console.log(`${head}\n  ⚠ ${r.error}`);
        continue;
      }
      if (r.findings.length === 0) {
        console.log(`${head}\n  ✓ clean`);
        continue;
      }
      console.log(head);
      const bySeverity = new Map<string, Finding[]>();
      for (const f of r.findings) bySeverity.set(f.severity, [...(bySeverity.get(f.severity) ?? []), f]);
      for (const [sev, fs] of [...bySeverity].sort()) {
        const mark = HARD.has(sev) ? "✗" : "·";
        console.log(`  ${mark} ${sev} × ${fs.length}`);
        for (const f of fs.slice(0, 5)) console.log(`      ${f.subject} — ${f.note}`);
        if (fs.length > 5) console.log(`      … ${fs.length - 5} more (see --json)`);
      }
    }
    const totals = new Map<string, number>();
    for (const r of reports) for (const f of r.findings) totals.set(f.severity, (totals.get(f.severity) ?? 0) + 1);
    console.log(
      `\nTotals: ${[...totals].sort().map(([k, v]) => `${v} ${k}`).join(", ") || "no findings"}.`,
    );
    if (failed.length > 0)
      console.log(`Hard failures in ${failed.length} bundle(s)${strict ? "" : " (report-only; pass --strict to fail)"}.`);
  }

  if (strict && failed.length > 0) process.exit(1);
}

main().catch((err) => {
  console.error(err);
  process.exit(2);
});
