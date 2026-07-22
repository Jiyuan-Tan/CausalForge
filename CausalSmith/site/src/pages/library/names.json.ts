import type { APIRoute } from "astro";
import { loadLibrary, libraryRoot, declArea, declPagePath, nameMap } from "../../lib/library.js";

/**
 * Slim name → location map for cross-linking Lean identifiers from paper drawers
 * (and anything else) into the library explorer. Keys are full names plus
 * unambiguous short names; values are { a: area, n: full name }.
 */
export const GET: APIRoute = () => {
  const lib = loadLibrary(libraryRoot());
  const out: Record<string, { a: string; n: string }> = {};
  for (const [token, decl] of nameMap(lib)) {
    out[token] = { a: declPagePath(decl, lib), n: decl.name };
  }
  return new Response(JSON.stringify({ commit: lib.commit, names: out }), {
    headers: { "Content-Type": "application/json" },
  });
};
