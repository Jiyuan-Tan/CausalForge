#!/usr/bin/env -S npx tsx
import { readFile, writeFile } from "node:fs/promises";
import path from "node:path";
import process from "node:process";
import {
  patchReadmeTokenUsage,
  summarizeTokenUsage,
  writeTokenUsageSummary,
} from "../src/token_usage.js";

async function main(): Promise<void> {
  const args = process.argv.slice(2);
  const value = (flag: string): string | undefined => {
    const i = args.indexOf(flag);
    return i < 0 ? undefined : args[i + 1];
  };
  const runDir = value("--run-dir");
  const tokens = Number(value("--orchestrator-tokens"));
  if (!runDir || !Number.isSafeInteger(tokens) || tokens < 0) {
    throw new Error(
      "Usage: token_usage.ts --run-dir <active-or-banked-run-dir> --orchestrator-tokens <nonnegative integer>",
    );
  }
  const absolute = path.resolve(runDir);
  const summary = await summarizeTokenUsage(absolute, tokens);
  await writeTokenUsageSummary(absolute, summary);

  const statePath = path.join(absolute, "state.json");
  const state = JSON.parse(await readFile(statePath, "utf8"));
  state.token_usage = summary;
  await writeFile(statePath, `${JSON.stringify(state, null, 2)}\n`, "utf8");

  const readmePath = path.join(absolute, "README.md");
  try {
    await patchReadmeTokenUsage(readmePath, summary);
  } catch (err) {
    if ((err as NodeJS.ErrnoException).code !== "ENOENT") throw err;
  }
  console.log(JSON.stringify(summary));
}

main().catch((err) => {
  console.error(err instanceof Error ? err.message : String(err));
  process.exit(1);
});
