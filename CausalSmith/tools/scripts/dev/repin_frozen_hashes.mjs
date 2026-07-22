// Regenerate frozen_hashes.json from the (hand-amended) formal_layer.tex,
// mirroring p1_plan.ts:150-153. Run from tools/ on node 20.
//   npx tsx scripts/dev/repin_frozen_hashes.mjs <bundle_dir_abs>
import { readFile, writeFile } from "node:fs/promises";
import { join } from "node:path";
import { parseAnchoredEnvs, hashEnvBody } from "../../src/presentation/tex_anchors.ts";

const dir = process.argv[2];
if (!dir) { console.error("usage: repin_frozen_hashes.mjs <bundle_dir_abs>"); process.exit(2); }
const layer = await readFile(join(dir, "formal_layer.tex"), "utf8");
const envs = parseAnchoredEnvs(layer);
const hashes = Object.fromEntries(envs.map((e) => [e.obj_id, hashEnvBody(e.body)]));
await writeFile(join(dir, "frozen_hashes.json"), JSON.stringify(hashes, null, 2) + "\n", "utf8");
console.error(`re-pinned ${envs.length} env hashes: ${envs.map((e) => e.obj_id).join(", ")}`);
