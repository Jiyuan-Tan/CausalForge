import type { APIRoute } from "astro";
import { loadLibrary, libraryRoot, declArea, declPagePath, isTier1 } from "../../lib/library.js";
import { nlPlain } from "../../lib/docmd.js";

/**
 * Compact search payload over the whole library — fetched lazily by the search box
 * and directly consumable by agents (`GET /library/search.json`).
 * Fields: n=name, k=kind, m=module, a=area, t=tier(1|2), d=NL first paragraph,
 * s=whitespace-collapsed statement, l=line, f=file.
 */
export const GET: APIRoute = () => {
  const lib = loadLibrary(libraryRoot());
  const rows = lib.entries.map((e) => ({
    n: e.name,
    k: e.kind,
    m: e.module,
    a: declPagePath(e, lib),
    t: isTier1(e, lib.sidecars) ? 1 : 2,
    d: nlPlain(e.doc) ?? "",
    s: e.statement.replace(/\s+/g, " "),
    l: e.line,
    f: e.file,
  }));
  return new Response(JSON.stringify({ commit: lib.commit, rows }), {
    headers: { "Content-Type": "application/json" },
  });
};
