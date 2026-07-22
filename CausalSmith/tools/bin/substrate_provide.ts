#!/usr/bin/env -S npx tsx
/**
 * Mark a substrate Note as "provided" — the human (or a future auto-builder)
 * has written the corresponding Lean substrate and is ready to retry the
 * theorems blocked by the original substrate_request.
 *
 * Usage:
 *   tools/bin/substrate_provide.ts --concept "<missing_concept text>" \
 *       --lean-path <path-relative-to-Causalean-root> \
 *       [--verified] [--message "<note text>"]
 *
 *   tools/bin/substrate_provide.ts --note <note_id> \
 *       --lean-path <path-relative-to-Causalean-root> \
 *       [--verified] [--message "<note text>"]
 *
 * Exit codes:
 *   0  success
 *   1  bad usage / missing args
 *   2  could not resolve Note (no match by concept/id)
 *   3  Lean path does not exist (set --force to override)
 */
import { existsSync } from "node:fs";
import { readdir, readFile, writeFile } from "node:fs/promises";
import path from "node:path";
import process from "node:process";
import { findWorkspaceRoot } from "../src/shared/repo_root.js";

interface Args {
  concept?: string;
  noteId?: string;
  leanPath?: string;
  verified: boolean;
  message?: string;
  force: boolean;
}

function parseArgs(argv: string[]): Args {
  const out: Args = { verified: false, force: false };
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === "--concept") { out.concept = argv[++i]; continue; }
    if (a === "--note") { out.noteId = argv[++i]; continue; }
    if (a === "--lean-path") { out.leanPath = argv[++i]; continue; }
    if (a === "--verified") { out.verified = true; continue; }
    if (a === "--force") { out.force = true; continue; }
    if (a === "--message") { out.message = argv[++i]; continue; }
    if (a === "--help" || a === "-h") {
      printUsage();
      process.exit(0);
    }
    process.stderr.write(`substrate_provide: unknown arg '${a}'\n`);
    process.exit(1);
  }
  return out;
}

function printUsage(): void {
  process.stderr.write(
    [
      "substrate_provide: mark a substrate Note as provided",
      "",
      "Usage:",
      "  --concept <text>   |  --note <note_id>     (one is required)",
      "  --lean-path <p>    relative to Causalean repo root  (required)",
      "  [--verified]       assert the new Lean file builds clean",
      "  [--force]          allow nonexistent --lean-path (CI / placeholder)",
      "  [--message <t>]    free-text annotation attached to the marker",
    ].join("\n") + "\n",
  );
}


interface NoteShape {
  note_id: string;
  substrate_concept?: string;
  substrate_provided?: unknown;
  [k: string]: unknown;
}

async function loadAllNoteFiles(notesDir: string): Promise<Array<{ path: string; data: NoteShape }>> {
  const out: Array<{ path: string; data: NoteShape }> = [];
  let names: string[];
  try {
    names = await readdir(notesDir);
  } catch {
    return out;
  }
  for (const n of names) {
    if (!n.endsWith(".json")) continue;
    const p = path.join(notesDir, n);
    try {
      const raw = await readFile(p, "utf8");
      const data = JSON.parse(raw) as NoteShape;
      if (data?.note_id) out.push({ path: p, data });
    } catch {
      // skip unreadable / malformed
    }
  }
  return out;
}

async function main(): Promise<void> {
  const args = parseArgs(process.argv.slice(2));
  if (!args.leanPath) {
    process.stderr.write("substrate_provide: --lean-path is required\n");
    printUsage();
    process.exit(1);
  }
  if (!args.concept && !args.noteId) {
    process.stderr.write("substrate_provide: pass either --concept <text> or --note <id>\n");
    printUsage();
    process.exit(1);
  }

  const repoRoot = findWorkspaceRoot(process.cwd());
  const studyRoot = path.join(repoRoot, "CausalSmith", "doc", "study");
  const notesDir = path.join(studyRoot, "nodes", "note");

  const leanAbs = path.join(repoRoot, args.leanPath);
  if (!existsSync(leanAbs) && !args.force) {
    process.stderr.write(
      `substrate_provide: --lean-path '${args.leanPath}' does not resolve to a file under ${repoRoot}. Re-run with --force to override.\n`,
    );
    process.exit(3);
  }

  const notes = await loadAllNoteFiles(notesDir);
  let match: { path: string; data: NoteShape } | undefined;
  if (args.noteId) {
    match = notes.find((n) => n.data.note_id === args.noteId);
  } else {
    match = notes.find((n) => n.data.substrate_concept === args.concept);
  }
  if (!match) {
    process.stderr.write(
      args.noteId
        ? `substrate_provide: no Note with note_id='${args.noteId}'\n`
        : `substrate_provide: no Note with substrate_concept matching '${args.concept}'\n`,
    );
    process.exit(2);
  }

  const marker = {
    lean_path: args.leanPath,
    provided_at: new Date().toISOString(),
    ...(args.verified ? { verified: true } : { verified: false }),
    ...(args.message ? { note: args.message } : {}),
  };
  match.data.substrate_provided = marker;

  // Atomic write: rename(2) at the end. JSON pretty-print + trailing newline
  // matches every other writer in the graph for diff stability.
  const tmp = `${match.path}.tmp-${process.pid}`;
  await writeFile(tmp, JSON.stringify(match.data, null, 2) + "\n", "utf8");
  const { rename } = await import("node:fs/promises");
  await rename(tmp, match.path);

  process.stdout.write(
    `substrate_provide: stamped Note '${match.data.note_id}' as provided ` +
      `(lean_path=${marker.lean_path}, verified=${marker.verified}).\n`,
  );
  if (Array.isArray(match.data.fulfills_substrate_for) && match.data.fulfills_substrate_for.length > 0) {
    process.stdout.write(
      `  Theorems unblocked for a future --retry-blocked pass: ` +
        `${(match.data.fulfills_substrate_for as string[]).join(", ")}\n`,
    );
  }
}

main().catch((err) => {
  process.stderr.write(`substrate_provide: ${(err as Error).message}\n`);
  process.exit(1);
});
