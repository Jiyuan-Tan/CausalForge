// Permanent, append-only ledger of infrastructure that pipeline runs NEEDED but
// that does not yet exist in Causalean / Mathlib. Two writers:
//   * F1 (stage1) on `needs-new-infrastructure` — records `infrastructure_needed`.
//   * F2 (stage2) on `blocked-missing-architecture` — records `missing_items`.
// Entries are keyed by `qid:spec:source` and REPLACED in place on re-run, so
// repeated runs of the same qid update rather than duplicate. Human-readable so
// a maintainer can scan it, land an item, then re-run the qid.

import fs from "node:fs";
import path from "node:path";
import lockfile from "proper-lockfile";

export interface MissingArchItem {
  id?: string;
  kind: string;
  description: string;
  effort?: string;
}

export interface MissingArchEntry {
  qid: string;
  spec: string;
  /** e.g. "F1 needs-new-infrastructure" | "F2 missing-architecture". */
  source: string;
  /** YYYY-MM-DD; caller supplies (keeps this module clock-free / testable). */
  date: string;
  items: MissingArchItem[];
  /** The .tex claim left unformalized (F1 deferred_conjecture), if any. */
  deferred?: string;
}

const HEADER = `# Missing Architecture Ledger

Auto-maintained by causalsmith. Each block records infrastructure a run NEEDED but
that does not yet exist in Causalean / Mathlib. Pick an item, land it, then re-run
the qid. Blocks are keyed by \`qid:spec:source\` and replaced in place on re-run.
`;

function sleepSync(ms: number): void {
  Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, ms);
}

function lockLedgerSync(lockPath: string): () => void {
  for (let attempt = 0; attempt <= 10; attempt += 1) {
    try {
      return lockfile.lockSync(lockPath, {
        stale: 60_000,
        realpath: false,
      });
    } catch (err) {
      if ((err as NodeJS.ErrnoException).code !== "ELOCKED" || attempt === 10) throw err;
      sleepSync(Math.min(5_000, 100 * 1.5 ** attempt));
    }
  }
  throw new Error(`Could not acquire ledger lock at ${lockPath}`);
}

/** Default ledger location: \`<repoRoot>/doc/research/MISSING_ARCHITECTURE.md\`. */
export function missingArchitectureLedgerPath(repoRoot: string): string {
  return path.join(repoRoot, "doc", "research", "MISSING_ARCHITECTURE.md");
}

function escapeRegExp(s: string): string {
  return s.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
}

function cell(s: string | undefined): string {
  return (s ?? "—").replace(/\|/g, "\\|").replace(/\n/g, " ").trim() || "—";
}

/**
 * Upsert one entry into the ledger. Creates the file (with header) if absent;
 * removes any prior block with the same `qid:spec:source` key before appending
 * the fresh one (idempotent across re-runs).
 */
export function recordMissingArchitecture(
  ledgerPath: string,
  entry: MissingArchEntry,
): void {
  fs.mkdirSync(path.dirname(ledgerPath), { recursive: true });
  const lockPath = `${ledgerPath}.lock`;
  if (!fs.existsSync(lockPath)) fs.writeFileSync(lockPath, "{}\n", { flag: "a" });
  const release = lockLedgerSync(lockPath);
  try {
    // why: concurrent qids upsert shared ledger blocks without lost updates.
    recordMissingArchitectureUnlocked(ledgerPath, entry);
  } finally {
    release();
  }
}

function recordMissingArchitectureUnlocked(
  ledgerPath: string,
  entry: MissingArchEntry,
): void {
  const key = `${entry.qid}:${entry.spec}:${entry.source}`;
  const begin = `<!-- BEGIN ${key} -->`;
  const end = `<!-- END ${key} -->`;

  let body = fs.existsSync(ledgerPath)
    ? fs.readFileSync(ledgerPath, "utf8")
    : HEADER;

  // Strip any existing block for this key.
  const re = new RegExp(
    `\\n*${escapeRegExp(begin)}[\\s\\S]*?${escapeRegExp(end)}\\n*`,
    "g",
  );
  body = body.replace(re, "\n");

  const rows = entry.items
    .map((i) => `| ${cell(i.id)} | ${cell(i.kind)} | ${cell(i.description)} | ${cell(i.effort)} |`)
    .join("\n");

  const block = [
    begin,
    `## ${entry.qid} ${entry.spec} — ${entry.source} (${entry.date})`,
    entry.deferred ? `\n**Deferred:** ${entry.deferred.replace(/\n/g, " ").trim()}\n` : "",
    "| id | kind | description | effort |",
    "|----|------|-------------|--------|",
    rows,
    end,
  ]
    .filter((l) => l !== "")
    .join("\n");

  fs.writeFileSync(ledgerPath, `${body.trimEnd()}\n\n${block}\n`);
}
