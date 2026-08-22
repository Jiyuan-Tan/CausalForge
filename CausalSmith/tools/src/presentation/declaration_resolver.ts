import { readFile, realpath } from "node:fs/promises";
import { dirname, isAbsolute, join, relative, resolve, sep } from "node:path";
import { maskLeanCommentsAndStrings } from "../graph/extractor.js";
import { extractDeclSnippet, parseSourceDecls } from "./lean_extract.js";

export interface ResolvedLeanDeclaration {
  /** Canonical path relative to the common workspace root (never `..`). */
  file: string;
  decl: string;
  line: number;
  snippet: string;
  relocated: boolean;
  resolution: "crosswalk" | "library-index" | "export-import" | "run-name-search";
}

const leafOf = (name: string) => name.slice(name.lastIndexOf(".") + 1);
const within = (root: string, target: string) => target === root || !relative(root, target).startsWith(`..${sep}`) && relative(root, target) !== ".." && !isAbsolute(relative(root, target));

async function rootsFor(repoRoot: string): Promise<{ packageRoot: string; workspaceRoot: string; runRoot: string }> {
  const packageRoot = await realpath(repoRoot);
  const parent = await realpath(dirname(packageRoot));
  // PRESENT runs from the CausalSmith package and Causalean is its sibling. Tests may
  // use a one-package fixture; only select the parent when the sibling topology exists.
  let workspaceRoot = packageRoot;
  try {
    await realpath(join(parent, "Causalean"));
    workspaceRoot = parent;
  } catch (e) {
    if ((e as NodeJS.ErrnoException).code !== "ENOENT") throw e;
    /* single-package fixture */
  }
  return { packageRoot, workspaceRoot, runRoot: packageRoot };
}

async function safeRealFile(workspaceRoot: string, candidate: string): Promise<string> {
  const abs = await realpath(candidate);
  if (!within(workspaceRoot, abs)) throw new Error(`P1 declaration path escapes workspace root: ${candidate}`);
  return abs;
}

function canonicalFile(workspaceRoot: string, abs: string): string {
  const rel = relative(workspaceRoot, abs);
  if (!rel || rel === ".." || rel.startsWith(`..${sep}`) || isAbsolute(rel)) {
    throw new Error(`P1 declaration path is not workspace-contained: ${abs}`);
  }
  return rel.split(sep).join("/");
}

function namespaceAtOffset(maskedSource: string, offset: number): string {
  const frames: { kind: "namespace" | "section"; name?: string }[] = [];
  for (const line of maskedSource.slice(0, offset).split(/\r?\n/)) {
    const text = line.trim();
    const ns = /^namespace\s+([A-Za-z_][A-Za-z0-9_.']*)\b/.exec(text);
    if (ns) frames.push({ kind: "namespace", name: ns[1] });
    else if (/^section(?:\s|$)/.test(text)) frames.push({ kind: "section" });
    else if (/^end(?:\s|$)/.test(text)) frames.pop();
  }
  return frames.filter((f) => f.kind === "namespace").map((f) => f.name!).join(".");
}

function explicitExports(source: string, leaf: string): { aliasFq: string; targetFq: string }[] {
  const masked = maskLeanCommentsAndStrings(source);
  const out = new Map<string, { aliasFq: string; targetFq: string }>();
  for (const m of masked.matchAll(/\bexport\s+([A-Za-z_][A-Za-z0-9_.']*)\s*\(([\s\S]*?)\)/g)) {
    if (m[2].match(/[A-Za-z_][A-Za-z0-9_']*/g)?.some((name) => name === leaf) === true) {
      const enclosing = namespaceAtOffset(masked, m.index ?? 0);
      const entry = {
        aliasFq: enclosing ? `${enclosing}.${leaf}` : leaf,
        targetFq: `${m[1]}.${leaf}`,
      };
      out.set(`${entry.aliasFq}\0${entry.targetFq}`, entry);
    }
  }
  return [...out.values()];
}

function declaredFqAt(source: string, line: number, short: string): string | null {
  const masked = maskLeanCommentsAndStrings(source).split(/\r?\n/);
  const frames: { kind: "namespace" | "section"; name?: string }[] = [];
  for (let i = 0; i < Math.min(line, masked.length); i++) {
    const text = masked[i].trim();
    const ns = /^namespace\s+([A-Za-z_][A-Za-z0-9_.']*)\b/.exec(text);
    if (ns) frames.push({ kind: "namespace", name: ns[1] });
    else if (/^section(?:\s|$)/.test(text)) frames.push({ kind: "section" });
    else if (/^end(?:\s|$)/.test(text)) frames.pop();
  }
  if (!parseSourceDecls(source).some((d) => d.line === line && leafOf(d.name) === short)) return null;
  const ns = frames.filter((f) => f.kind === "namespace").map((f) => f.name!).join(".");
  return ns ? `${ns}.${short}` : short;
}

export function fullyQualifiedSourceDecls(source: string): { name: string; line: number; kind: string }[] {
  return parseSourceDecls(source).flatMap((d) => {
    const name = d.name.includes(".") ? d.name : declaredFqAt(source, d.line, d.name);
    return name ? [{ name, line: d.line, kind: d.kind }] : [];
  });
}

type Candidate = { abs: string; file: string; decl: string; line: number; resolution: ResolvedLeanDeclaration["resolution"] };

async function validateUnique(
  workspaceRoot: string,
  requestedFq: string,
  candidates: Candidate[],
  label: string,
): Promise<ResolvedLeanDeclaration | null> {
  const valid: (Candidate & { snippet: string })[] = [];
  const seen = new Set<string>();
  for (const c of candidates) {
    let abs: string;
    try { abs = await safeRealFile(workspaceRoot, c.abs); } catch (e) {
      if ((e as NodeJS.ErrnoException).code === "ENOENT") continue;
      throw e;
    }
    const key = `${abs}\0${c.decl}`;
    if (seen.has(key)) continue;
    seen.add(key);
    const source = await readFile(abs, "utf8");
    const short = leafOf(c.decl);
    const matches = parseSourceDecls(source).filter((d) => leafOf(d.name) === short);
    for (const d of matches) {
      const actualFq = d.name.includes(".") ? d.name : declaredFqAt(source, d.line, short);
      if (actualFq !== c.decl) continue;
      valid.push({ ...c, abs, file: canonicalFile(workspaceRoot, abs), line: d.line, snippet: extractDeclSnippet(source, c.decl, d.line) });
    }
  }
  if (valid.length > 1) {
    throw new Error(`P1 Lean declaration resolution is ambiguous for ${requestedFq} via ${label}: ${valid.map((v) => `${v.file}:${v.decl}:${v.line}`).join(", ")}`);
  }
  const hit = valid[0];
  return hit ? { file: hit.file, decl: hit.decl, line: hit.line, snippet: hit.snippet, relocated: true, resolution: hit.resolution } : null;
}

export async function resolvedLeanAbsolutePath(repoRoot: string, canonicalFile: string): Promise<string> {
  if (isAbsolute(canonicalFile) || canonicalFile.split(/[\\/]/).includes(".."))
    throw new Error(`P1 rejects non-canonical resolved Lean pointer: ${canonicalFile}`);
  const { workspaceRoot } = await rootsFor(repoRoot);
  return safeRealFile(workspaceRoot, resolve(workspaceRoot, canonicalFile));
}

/** Resolve and validate the exact fully-qualified declaration behind a crosswalk pointer.
 * The recorded file may be a thin re-export; leaf-name uniqueness is never authority. */
export async function resolveLeanDeclaration(
  repoRoot: string,
  leanSubdir: string,
  requested: { file: string; decl: string; line: number },
): Promise<ResolvedLeanDeclaration> {
  if (isAbsolute(requested.file) || requested.file.split(/[\\/]/).includes("..")) {
    throw new Error(`P1 rejects non-relative/traversing Lean pointer: ${requested.file}`);
  }
  const { packageRoot, workspaceRoot } = await rootsFor(repoRoot);
  const runDir = resolve(packageRoot, leanSubdir);
  if (!within(packageRoot, runDir)) throw new Error(`P1 lean_subdir escapes package root: ${leanSubdir}`);
  const realRunDir = await realpath(runDir);
  if (!within(packageRoot, realRunDir)) throw new Error(`P1 lean_subdir symlink escapes package root: ${leanSubdir}`);
  const recordedAbs = resolve(runDir, requested.file);
  if (!within(runDir, recordedAbs)) throw new Error(`P1 recorded Lean pointer escapes run root: ${requested.file}`);
  const leaf = leafOf(requested.decl);
  let recordedSource = "";
  try {
    const realRecorded = await safeRealFile(workspaceRoot, recordedAbs);
    if (!within(realRunDir, realRecorded)) {
      throw new Error(`P1 recorded Lean pointer symlink escapes run root: ${requested.file}`);
    }
    recordedSource = await readFile(realRecorded, "utf8");
  }
  catch (e) {
    if ((e as NodeJS.ErrnoException).code !== "ENOENT") throw e;
  }

  const exportsForLeaf = recordedSource ? explicitExports(recordedSource, leaf) : [];
  const authenticatedExports = exportsForLeaf.filter((e) => e.aliasFq === requested.decl);
  if (exportsForLeaf.length > 0 && authenticatedExports.length === 0) {
    throw new Error(
      `P1 re-export alias namespace mismatch for ${requested.decl}: recorded source authenticates ` +
      exportsForLeaf.map((e) => `${e.aliasFq} -> ${e.targetFq}`).join(", "),
    );
  }
  if (authenticatedExports.length > 1) {
    throw new Error(`P1 re-export target is ambiguous for ${requested.decl}: ${authenticatedExports.map((e) => e.targetFq).join(", ")}`);
  }
  if (recordedSource && authenticatedExports.length === 0) {
    const local = await validateUnique(workspaceRoot, requested.decl, [{
      abs: recordedAbs, file: "", decl: requested.decl, line: requested.line, resolution: "crosswalk",
    }], "recorded source");
    if (local) return { ...local, relocated: false, resolution: "crosswalk" };
  }

  const targetFq = authenticatedExports[0]?.targetFq ?? requested.decl;
  const indexPath = join(workspaceRoot, "doc", "library_index.json");
  try {
    const index = JSON.parse(await readFile(indexPath, "utf8")) as { entries?: { name?: string; file?: string; line?: number }[] };
    const rows = (index.entries ?? []).filter((e) => e.name === targetFq && typeof e.file === "string" && Number.isFinite(e.line));
    const hit = await validateUnique(workspaceRoot, targetFq, rows.map((e) => ({
      abs: resolve(workspaceRoot, e.file!), file: "", decl: targetFq, line: e.line!, resolution: "library-index",
    })), "library index");
    if (hit) return hit;
  } catch (e) {
    if (e instanceof SyntaxError || (e as NodeJS.ErrnoException).code === "ENOENT") { /* fallback below */ }
    else throw e;
  }

  if (recordedSource && authenticatedExports.length === 1) {
    const imports = [...maskLeanCommentsAndStrings(recordedSource).matchAll(/^\s*import\s+([A-Za-z0-9_.']+)/gm)].map((m) => m[1]);
    const candidates: Candidate[] = [];
    for (const moduleName of imports) {
      for (const root of [packageRoot, workspaceRoot]) {
        candidates.push({ abs: join(root, ...moduleName.split(".")) + ".lean", file: "", decl: targetFq, line: 1, resolution: "export-import" });
      }
    }
    const hit = await validateUnique(workspaceRoot, targetFq, candidates, "explicit export/import graph");
    if (hit) return hit;
  }

  // Run-local fallback still requires exact FQ identity, never a globally unique leaf.
  const runFiles = new Set<string>();
  for (const pointer of [requested.file]) runFiles.add(resolve(runDir, pointer));
  const hit = await validateUnique(workspaceRoot, requested.decl, [...runFiles].map((abs) => ({
    abs, file: "", decl: requested.decl, line: requested.line, resolution: "run-name-search",
  })), "run declaration search");
  if (hit) return hit;
  throw new Error(`P1 cannot audit ${requested.decl}: ${requested.file}:${requested.line} contains no exact declaration body and no unique authoritative source was resolved`);
}
