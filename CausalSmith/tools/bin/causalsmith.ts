#!/usr/bin/env node
import process from "node:process";
import { fileURLToPath } from "node:url";

export type CausalSmithMode = "research" | "present" | "study";

export function parseCausalSmithCommand(argv: string[]): { mode: CausalSmithMode; args: string[] } {
  const [mode, ...args] = argv;
  if (mode === "research" || mode === "present" || mode === "study") return { mode, args };
  throw new Error(
    "Usage: causalsmith <research|present|study> <args...>\n" +
      "  causalsmith research <qid> <spec> [options...]\n" +
      "  causalsmith present <qid> <spec> [options...]\n" +
      "  causalsmith study <slug> [--resume] [--dry-run]",
  );
}

async function main(argv: string[]): Promise<void> {
  const { mode, args } = parseCausalSmithCommand(argv);
  if (mode === "research") {
    const { runCli } = await import("../src/cli.js");
    await runCli(args);
  } else if (mode === "present") {
    const { runPresentationCli } = await import("../src/presentation/cli.js");
    await runPresentationCli(args);
  } else {
    const { runStudyCli } = await import("../src/cli.js");
    await runStudyCli(args);
  }
}

if (process.argv[1] && fileURLToPath(import.meta.url) === process.argv[1]) {
  main(process.argv.slice(2)).catch((err: unknown) => {
    const message = err instanceof Error ? err.message : String(err);
    console.error(`causalsmith: ${message}`);
    // A deliberate user-facing error carries its own actionable message, so the
    // default output stays clean. An UNEXPECTED throw (a TypeError from some
    // assembly path, say) reduces to a bare line like "Cannot read properties of
    // undefined (reading 'kind')" with no location — and since a D0 round costs
    // ~40 minutes, re-running one purely to obtain a stack is the expensive way to
    // learn where it came from. `CAUSALSMITH_TRACE=1` keeps the stack on the FIRST
    // failure instead.
    if (process.env.CAUSALSMITH_TRACE && err instanceof Error && err.stack) {
      console.error(err.stack);
    }
    process.exitCode = 1;
  });
}
