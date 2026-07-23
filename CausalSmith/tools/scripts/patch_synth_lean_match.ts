/**
 * One-shot patch: retro-link presentation-synthesized definitions to their existing
 * Lean declarations in every already-emitted accepted-paper bundle, matching the new
 * P4 emit behaviour (see src/presentation/synth_lean_match.ts). For each affected
 * bundle it rewrites presentation_crosswalk.json, lean_snippets.json,
 * formal_layer_web.json, and paper_body.html WITHOUT re-running the full pipeline
 * (no latexmk/codex/lake): snippets are extracted with the real extractor and the
 * paper body drawer is enabled surgically, exactly as tex2html would emit it.
 *
 * Idempotent: a bundle already patched (no presentation-synthesized entry matches)
 * is left byte-for-byte unchanged.
 *
 * Run: cd tools && npx tsx scripts/patch_synth_lean_match.ts [--write]
 * Without --write it is a dry run (reports what would change).
 */
import { readdir, readFile, writeFile } from "node:fs/promises";
import { existsSync } from "node:fs";
import { join } from "node:path";
import { matchSynthDecl, type DeclLoc } from "../src/presentation/synth_lean_match.js";
import { tryExtractDeclSnippet, sorryFree } from "../src/presentation/lean_extract.js";

const REPO_ROOT = join(import.meta.dirname, "..", "..");
const PRESENTATION_DIR = join(REPO_ROOT, "doc", "presentation");
const WRITE = process.argv.includes("--write");

function shortName(qualified: string): string {
  const i = qualified.lastIndexOf(".");
  return i < 0 ? qualified : qualified.slice(i + 1);
}

/** Build shortName → {file (leanSubdir-relative), line, kind} from paper_library_index.json. */
function moduleDeclsFromIndex(indexEntries: { name: string; file: string; line: number; kind: string }[], leanSubdir: string): Map<string, DeclLoc> {
  const prefix = leanSubdir.endsWith("/") ? leanSubdir : leanSubdir + "/";
  const out = new Map<string, DeclLoc>();
  for (const e of indexEntries) {
    const rel = e.file.startsWith(prefix) ? e.file.slice(prefix.length) : e.file;
    const key = shortName(e.name);
    if (!out.has(key)) out.set(key, { file: rel, line: e.line, kind: e.kind });
  }
  return out;
}

/** Enable the Lean drawer on a formal-block div, exactly as tex2html emits it:
 *  swap `data-presentation-only="true"` → `data-objid tabindex`, append the hint. */
function enableDrawer(html: string, objId: string): { html: string; changed: boolean } {
  const startMarker = `<div class="formal-block kind-definition" id="obj-${objId}" data-presentation-only="true">`;
  const start = html.indexOf(startMarker);
  if (start < 0) return { html, changed: false };
  // Find the matching close of this div by depth-counting <div ...> / </div>.
  const openTagEnd = start + startMarker.length;
  let depth = 1;
  const re = /<div\b|<\/div>/g;
  re.lastIndex = openTagEnd;
  let m: RegExpExecArray | null;
  let closeStart = -1;
  while ((m = re.exec(html))) {
    depth += m[0] === "</div>" ? -1 : 1;
    if (depth === 0) { closeStart = m.index; break; }
  }
  if (closeStart < 0) throw new Error(`unbalanced div for ${objId}`);
  const inner = html.slice(openTagEnd, closeStart);
  const newBlock =
    `<div class="formal-block kind-definition" id="obj-${objId}" data-objid="${objId}" tabindex="0">` +
    inner +
    `<span class="lean-hint">⊢ Lean</span></div>`;
  return { html: html.slice(0, start) + newBlock + html.slice(closeStart + "</div>".length), changed: true };
}

let totalBundles = 0;
let patchedBundles = 0;

for (const name of (await readdir(PRESENTATION_DIR)).sort()) {
  const dir = join(PRESENTATION_DIR, name);
  const cwPath = join(dir, "presentation_crosswalk.json");
  if (!existsSync(cwPath) || !existsSync(join(dir, "meta.json"))) continue;
  totalBundles++;

  const crosswalk = JSON.parse(await readFile(cwPath, "utf8")) as {
    commit: string; lean_subdir: string;
    entries: Array<{ obj_id: string; env: string; title?: string | null; lean: { file: string; decl: string; decl_kind: string; line: number } | null; fallback?: string | null; status: string; sorry_free: boolean | null }>;
  };
  const synthEntries = crosswalk.entries.filter((e) => e.status === "presentation-synthesized");
  if (synthEntries.length === 0) continue;

  const indexPath = join(dir, "paper_library_index.json");
  if (!existsSync(indexPath)) { console.log(`[skip] ${name}: no paper_library_index.json`); continue; }
  const index = JSON.parse(await readFile(indexPath, "utf8")) as { entries: { name: string; file: string; line: number; kind: string }[] };
  const moduleDecls = moduleDeclsFromIndex(index.entries, crosswalk.lean_subdir);

  const snippets = JSON.parse(await readFile(join(dir, "lean_snippets.json"), "utf8")) as { commit: string; snippets: Record<string, unknown> };
  const web = JSON.parse(await readFile(join(dir, "formal_layer_web.json"), "utf8")) as { commit: string; groups: Array<{ kind: string; items: Array<{ obj_id: string; label?: string; lean?: { decl?: string } | null }> }> };
  let body = await readFile(join(dir, "paper_body.html"), "utf8");

  const matchedDecls = new Set<string>();
  const linked: string[] = [];
  const srcCache = new Map<string, string>();
  const readSrc = async (rel: string) => {
    if (!srcCache.has(rel)) srcCache.set(rel, await readFile(join(REPO_ROOT, crosswalk.lean_subdir, rel), "utf8").catch(() => ""));
    return srcCache.get(rel)!;
  };

  for (const e of synthEntries) {
    const hit = matchSynthDecl(e.title ?? null, e.obj_id, moduleDecls);
    if (!hit) continue;
    const src = await readSrc(hit.file);
    const snippet = tryExtractDeclSnippet(src, hit.decl, hit.line);
    if (snippet === null) { console.log(`[warn] ${name}: ${e.obj_id} matched ${hit.decl} but snippet not extractable`); continue; }
    const sf = sorryFree(src);
    e.lean = { file: hit.file, decl: hit.decl, decl_kind: hit.decl_kind, line: hit.line };
    e.fallback = null;
    e.status = "matched";
    e.sorry_free = sf;
    (snippets.snippets as Record<string, unknown>)[e.obj_id] = { decl: hit.decl, file: hit.file, line: hit.line, statement: snippet, sorry_free: sf, axioms: null };
    matchedDecls.add(hit.decl);
    linked.push(`${e.obj_id} → ${hit.decl}`);
    const drawer = enableDrawer(body, e.obj_id);
    body = drawer.html;
    if (!drawer.changed) console.log(`[warn] ${name}: ${e.obj_id} body block not found (drawer not enabled)`);
  }

  if (matchedDecls.size === 0) continue;

  // Drop the now-duplicate auxiliary entries/snippets/items for the homed decls.
  const before = crosswalk.entries.length;
  const removedAux: string[] = [];
  crosswalk.entries = crosswalk.entries.filter((e) => {
    if (e.env === "auxiliary" && e.lean && matchedDecls.has(e.lean.decl)) { removedAux.push(e.obj_id); delete (snippets.snippets as Record<string, unknown>)[e.obj_id]; return false; }
    return true;
  });
  // Web aux items carry `lean: null` (the bank crosswalk has no aux row); the decl lives in the
  // graph-node id (`aux_<Decl>` or a bare decl name) mirrored into obj_id — match on that, exactly
  // as the code fix filters auxiliaryNodes(graph) by `n.lean.decl_name`.
  const removedWebItems: string[] = [];
  for (const g of web.groups) {
    if (g.kind !== "auxiliary") continue;
    g.items = g.items.filter((it) => {
      const decl = (it.lean?.decl) || (it.obj_id || "").replace(/^aux_/, "");
      if (matchedDecls.has(decl)) { removedWebItems.push(it.obj_id); return false; }
      return true;
    });
  }

  patchedBundles++;
  console.log(`[patch] ${name}: linked ${linked.length} def(s): ${linked.join(", ")}` +
    (removedAux.length ? `; removed crosswalk aux dup(s): ${removedAux.join(", ")} (${before}→${crosswalk.entries.length} entries)` : "") +
    (removedWebItems.length ? `; removed web aux item(s): ${removedWebItems.join(", ")}` : ""));

  if (WRITE) {
    await writeFile(cwPath, JSON.stringify(crosswalk, null, 2) + "\n", "utf8");
    await writeFile(join(dir, "lean_snippets.json"), JSON.stringify(snippets, null, 2) + "\n", "utf8");
    await writeFile(join(dir, "formal_layer_web.json"), JSON.stringify(web, null, 2) + "\n", "utf8");
    await writeFile(join(dir, "paper_body.html"), body, "utf8");
  }
}

console.log(`\n${WRITE ? "Patched" : "Would patch"} ${patchedBundles}/${totalBundles} bundle(s).${WRITE ? "" : " (dry run — pass --write to apply)"}`);
