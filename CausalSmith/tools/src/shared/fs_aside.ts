// One implementation of "find a free name beside a file" for the recovery /
// archive CLIs. Three hand-rolled copies existed (`.prevN`, `.invalidated.N`,
// `.pre-recovery.N`), one of them UNBOUNDED — merged 2026-07-31 (dead-code
// sweep, S2). Bounded and fail-loud: an operator directory with hundreds of
// parked artifacts is itself the problem, and silently minting name #1000
// would bury it.
import { access } from "node:fs/promises";

/** ONLY absence (ENOENT) means "free". Any other failure (EACCES, EIO) must
 *  propagate: classifying it as free would let the caller rename/copy ONTO an
 *  existing backup — destroying the very artifact the aside exists to protect
 *  (audit B3). */
const nameIsFree = (file: string): Promise<boolean> =>
  access(file).then(
    () => false,
    (err: NodeJS.ErrnoException) => {
      if (err?.code === "ENOENT") return true;
      throw err;
    },
  );

/** Return `base` if free, else `base.1` … `base.<cap>`; throw past the cap. */
export async function firstFreeName(base: string, cap = 999): Promise<string> {
  if (await nameIsFree(base)) return base;
  for (let n = 1; n <= cap; n++) {
    const candidate = `${base}.${n}`;
    if (await nameIsFree(candidate)) return candidate;
  }
  throw new Error(`no free archive name beside ${base}: ${cap} prior artifacts already parked there.`);
}
