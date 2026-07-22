// Fixture: exercises spawnWithInactivityTimeout on a command that SUCCEEDS but
// leaves a detached descendant holding the stdout pipe open. Run as a STANDALONE
// node process (see spawn.test.ts) — vitest's worker couples the child `exit`
// event to stdio close, which masks the exit-driven settle this verifies.
//
// argv[2] = the `bash -lc` command to run (defaults to a silent pipe-holder).
// argv[3] = inactivityTimeoutMs (default 10000).
// argv[4] = output file path — the result JSON is written HERE (synchronously),
//           NOT to stdout: a piped stdout can drop bytes when the process exits
//           before it drains, so a file is the only race-free channel.
// argv[5] = maxTotalMs (optional wall-clock cap).
import { writeFileSync } from "node:fs";
import { spawnWithInactivityTimeout } from "../../src/workers/spawn.js";

const cmd = process.argv[2] ?? "sleep 15 & echo done; exit 0";
const inactivityTimeoutMs = Number(process.argv[3] ?? 10_000);
const outPath = process.argv[4];
const maxTotalMs = process.argv[5] ? Number(process.argv[5]) : undefined;

const t = Date.now();
const r = await spawnWithInactivityTimeout("bash", ["-lc", cmd], { inactivityTimeoutMs, maxTotalMs });
writeFileSync(
  outPath,
  JSON.stringify({
    elapsed: Date.now() - t,
    exitCode: r.exitCode,
    killedDueToInactivity: r.killedDueToInactivity,
    killedDueToTotalTimeout: r.killedDueToTotalTimeout ?? false,
    stdout: r.stdout,
  }),
);
process.exit(0);
