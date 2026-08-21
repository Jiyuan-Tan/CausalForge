import { createHash } from "node:crypto";
import { readdir, readFile } from "node:fs/promises";
import { join, relative } from "node:path";
import { writeJsonAtomic } from "./json_io.js";

const MANIFEST = "p2_assembly_manifest.json";

/** Sorted `*.tex` paths under the given run-dir subdirectories (missing dirs → none). */
export async function texFilesUnder(outDir: string, dirs: string[]): Promise<string[]> {
  const paths: string[] = [];
  for (const dir of dirs) {
    const names = await readdir(join(outDir, dir)).catch(() => []);
    paths.push(...names.filter((name) => name.endsWith(".tex")).sort().map((name) => join(outDir, dir, name)));
  }
  return paths;
}

/**
 * sha256 over `(label \0 bytes \0)` per path. `base` relativizes the label (so the
 * digest is location-independent and safe to persist); without it the absolute path
 * is the label (fine for same-process before/after comparison only). Missing files
 * throw unless `missingAsEmpty` — the persisted-manifest use must fail loud.
 */
export async function digestPaths(
  paths: string[],
  opts: { base?: string; missingAsEmpty?: boolean } = {},
): Promise<string> {
  const hash = createHash("sha256");
  for (const path of paths) {
    hash.update(opts.base ? relative(opts.base, path) : path);
    hash.update("\0");
    hash.update(opts.missingAsEmpty ? await readFile(path).catch(() => Buffer.from("")) : await readFile(path));
    hash.update("\0");
  }
  return hash.digest("hex");
}

async function assemblySourceDigest(outDir: string): Promise<string> {
  const paths = [
    join(outDir, "outline.md"),
    join(outDir, "appendix_proofs.tex"),
    ...(await texFilesUnder(outDir, ["sections", "proofs"])),
  ];
  return digestPaths(paths, { base: outDir });
}

/** Record the exact authored inputs consumed by P2's paper.tex assembly. */
export async function recordP2Assembly(outDir: string): Promise<void> {
  await writeJsonAtomic(join(outDir, MANIFEST), { source_digest: await assemblySourceDigest(outDir) });
}

/** Refuse a P4 emit when cached authored inputs changed after the last P2 assembly. */
export async function assertP2AssemblyFresh(outDir: string): Promise<void> {
  const path = join(outDir, MANIFEST);
  const raw = await readFile(path, "utf8").catch((error: NodeJS.ErrnoException) => {
    if (error.code === "ENOENT") return null;
    throw error;
  });
  if (raw === null) {
    throw new Error("P4 blocked: P2 assembly manifest is missing; rerun from P2 before emitting.");
  }
  const saved = JSON.parse(raw) as { source_digest?: string };
  const current = await assemblySourceDigest(outDir);
  if (!saved.source_digest || saved.source_digest !== current) {
    throw new Error("P4 blocked: authored section/proof inputs changed after paper.tex was assembled; rerun from P2 before emitting.");
  }
}
