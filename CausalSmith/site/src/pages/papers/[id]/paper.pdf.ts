import { readFile } from "node:fs/promises";
import { join } from "node:path";
import type { APIRoute } from "astro";
import { loadBundles } from "../../../lib/bundles.js";
import { bundleRoots } from "../../../lib/config.js";

/** Serves each bundle's compiled paper.pdf (the bundle dir lives outside the
 *  site root, so a plain public/ copy can't cover it). */
export async function getStaticPaths() {
  const bundles = await loadBundles(bundleRoots());
  return bundles
    .filter((b) => b.hasPdf)
    .map((b) => ({ params: { id: b.id }, props: { dir: b.dir } }));
}

export const GET: APIRoute = async ({ props }) => {
  const body = await readFile(join((props as { dir: string }).dir, "paper.pdf"));
  return new Response(new Uint8Array(body), {
    headers: { "Content-Type": "application/pdf" },
  });
};
