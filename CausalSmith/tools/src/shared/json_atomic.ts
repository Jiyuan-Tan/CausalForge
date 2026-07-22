import { writeFile, rename, rm } from "node:fs/promises";
import process from "node:process";

/**
 * Write `value` as pretty-printed JSON to `target`, atomically.
 *
 * Every canonical D-stage store is written through this: a torn `d0_working.json` or
 * `proto_core.json` costs the run every proof it holds, and a crash mid-write is not
 * a hypothetical on a shared cluster filesystem. Writing to a sibling temp file and
 * renaming makes the replacement atomic, so a reader sees either the old file or the
 * new one and never a truncated prefix.
 *
 * The temp name carries pid and timestamp so two concurrent writers to the same
 * target cannot collide on the scratch file; `rm` in `finally` leaves no debris
 * behind when the write itself throws.
 */
export async function writeJsonAtomic(target: string, value: unknown): Promise<void> {
  const temp = `${target}.tmp-${process.pid}-${Date.now()}`;
  try {
    await writeFile(temp, JSON.stringify(value, null, 2), "utf8");
    await rename(temp, target);
  } finally {
    await rm(temp, { force: true });
  }
}
