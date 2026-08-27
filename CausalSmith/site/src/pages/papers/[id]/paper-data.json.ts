import { loadBundles, type Bundle } from "../../../lib/bundles.js";
import { bundleRoots } from "../../../lib/config.js";

/** Heavy per-statement drawer payload (crosswalk entries + Lean snippets),
 *  split out of the paper page HTML — it is multi-MB and only needed once a
 *  reader clicks a formal block. drawer.ts fetches it lazily (warmed on idle). */
export async function getStaticPaths() {
  const bundles = await loadBundles(bundleRoots());
  return bundles.map((b) => ({ params: { id: b.id }, props: { bundle: b } }));
}

export function GET({ props }: { props: { bundle: Bundle } }) {
  const { bundle } = props;
  return new Response(JSON.stringify({ entries: bundle.entries, snippets: bundle.snippets }), {
    headers: { "Content-Type": "application/json" },
  });
}
