/**
 * Shared primitive for failure-bank routing.
 *
 * Two callers today:
 *   - `bin/study_bank.ts`         — study-pipeline run-level quarantine
 *                                   (granularity = `run_id`).
 *   - `bin/bank_entry.ts`         — causalsmith theorem-level banking, including
 *                                   the study-mode `--tier failed` branch
 *                                   (granularity = `bt_id = <qid>_<spec>`).
 *
 * Both perform the same mechanical move + reason-file write: rename a source
 * directory to a destination under a reason-bucketed parent, then drop a
 * `BANK_REASON.md` alongside the moved content. `routeToBank` captures that
 * shape generically; the caller owns reason validation and policy.
 */
import { existsSync } from "node:fs";
import { mkdir, rename, writeFile } from "node:fs/promises";
import path from "node:path";

export interface RouteToBankArgs {
  /** Absolute path of the directory to move. Must exist. */
  srcDir: string;
  /**
   * Absolute path of the destination directory. Must NOT exist. The parent
   * is created with `mkdir -p` semantics; the leaf is moved into place via
   * a single `rename` so callers see an atomic flip (no half-moved state).
   */
  destDir: string;
  /** Reason category (caller-validated taxonomy member). Echoed into BANK_REASON.md. */
  reason: string;
  /** Optional free-form note appended to BANK_REASON.md. */
  note?: string;
  /**
   * Optional identifier echoed in the BANK_REASON.md header. Use `run_id` for
   * study-pipeline run-level routing or `bt_id` for causalsmith theorem-level routing.
   * If omitted, the basename of `destDir` is used.
   */
  identifier?: string;
}

export interface RouteToBankResult {
  /** Absolute path of the moved directory. Identical to `destDir` on success. */
  dest: string;
}

/**
 * Move `srcDir` to `destDir`, creating the parent if needed, and write a
 * `BANK_REASON.md` inside the moved directory.
 *
 * Errors:
 *   - `srcDir` does not exist → throws "Source directory not found: <path>".
 *   - `destDir` already exists → throws "Destination already exists: <path>.
 *     Refusing to overwrite." (mirrors `bank_entry.ts`'s pre-existing safety.)
 */
export async function routeToBank(args: RouteToBankArgs): Promise<RouteToBankResult> {
  const { srcDir, destDir, reason, note, identifier } = args;
  if (!existsSync(srcDir)) {
    throw new Error(`Source directory not found: ${srcDir}`);
  }
  if (existsSync(destDir)) {
    throw new Error(`Destination already exists: ${destDir}. Refusing to overwrite.`);
  }
  await mkdir(path.dirname(destDir), { recursive: true });
  await rename(srcDir, destDir);
  const id = identifier ?? path.basename(destDir);
  const body = [
    `# Banked failed entry: ${id}`,
    ``,
    `- Reason: ${reason}`,
    `- Banked at: ${new Date().toISOString()}`,
    ...(note ? [`- Note: ${note}`] : []),
    ``,
    `Use \`mv ${destDir} ${srcDir}\` to restore.`,
    ``,
  ].join("\n");
  await writeFile(path.join(destDir, "BANK_REASON.md"), body, "utf8");
  return { dest: destDir };
}
