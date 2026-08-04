import { createHash } from "node:crypto";
import { readdir, readFile } from "node:fs/promises";
import { join, relative } from "node:path";
import { writeJsonAtomic } from "./json_io.js";

const MANIFEST = "p2_assembly_manifest.json";

async function assemblySourcePaths(outDir: string): Promise<string[]> {
  const paths = [join(outDir, "outline.md"), join(outDir, "appendix_proofs.tex")];
  for (const dir of ["sections", "proofs"]) {
    const names = await readdir(join(outDir, dir)).catch(() => []);
    paths.push(...names.filter((name) => name.endsWith(".tex")).sort().map((name) => join(outDir, dir, name)));
  }
  return paths;
}

async function assemblySourceDigest(outDir: string): Promise<string> {
  const hash = createHash("sha256");
  for (const path of await assemblySourcePaths(outDir)) {
    hash.update(relative(outDir, path));
    hash.update("\0");
    hash.update(await readFile(path));
    hash.update("\0");
  }
  return hash.digest("hex");
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
