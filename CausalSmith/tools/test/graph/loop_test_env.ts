import { mkdir, writeFile } from "node:fs/promises";
import path from "node:path";
import { promptPath } from "../../src/paths.js";

/**
 * Provision the artifacts the F2.5 reviewer requires inside a temp repo root.
 *
 * The reviewer's `corePath` is the typed `core.json` (the `.md` note is retired
 * upstream of F3 — it only seeds the graph); the reviewer parses it as a `Core`
 * and fails closed if it is missing/unparseable. It also fails closed on a
 * missing/empty reviewer prompt. Tests stub the agent, so the prompt CONTENT is
 * irrelevant — it only has to exist and be non-empty.
 *
 * Returns the `core.json` path to pass as `corePath`.
 */
export async function provisionLoopEnv(dir: string, qid = "q"): Promise<string> {
  const corePath = path.join(dir, "core.json");
  await writeFile(
    corePath,
    JSON.stringify({ qid, symbols: [], assumptions: [], statements: [], target_estimand: "ATE" }),
    "utf8",
  );
  const promptFile = promptPath(dir, "proof_reviewer.txt");
  await mkdir(path.dirname(promptFile), { recursive: true });
  await writeFile(promptFile, "Review each target faithfully against its typed-core statement.\n", "utf8");
  return corePath;
}
