import { existsSync, readFileSync, readdirSync } from "node:fs";
import { resolve, join } from "node:path";

/**
 * The real CausalSmith package root (parent of tools/), for integration tests
 * that read actual bank artifacts. Throws if the layout is unexpected.
 */
export function causalSmithRoot(): string {
  const root = resolve(import.meta.dirname, "..", "..");
  const lakefile = join(root, "lakefile.toml");
  if (!existsSync(lakefile) || !/name\s*=\s*"CausalSmith"/.test(readFileSync(lakefile, "utf8"))) {
    throw new Error(`expected CausalSmith package root at ${root}`);
  }
  return root;
}

/**
 * The first accepted bank entry currently on disk, as `{qid, spec}`. Integration tests that load a
 * real banked paper use this instead of a hardcoded qid, so they track whatever paper is banked now
 * and never go stale when the bank is re-curated (a banked paper is removed/renamed). Throws if no
 * accepted entry exists. An accepted entry is a `<qid>_<spec>` directory carrying its state file
 * (the bare `state.json`, or the legacy `<qid>_<spec>_state.json` for un-migrated entries).
 */
export function acceptedBankEntry(): { qid: string; spec: string } {
  const dir = join(causalSmithRoot(), "doc", "research", "_bank", "accepted");
  for (const name of readdirSync(dir).sort()) {
    const m = name.match(/^(.+)_(v\d+)$/);
    if (!m) continue;
    const hasState =
      existsSync(join(dir, name, "state.json")) ||
      existsSync(join(dir, name, `${name}_state.json`));
    if (hasState) return { qid: m[1], spec: m[2] };
  }
  throw new Error(`no accepted bank entry under ${dir}`);
}
