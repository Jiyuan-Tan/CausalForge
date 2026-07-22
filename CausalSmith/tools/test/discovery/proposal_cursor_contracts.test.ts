// Proposal-cursor recovery contracts.
//
// These paths are operator-invoked (reset_proposal_cursor), and every bug here wastes an
// ANGLE rather than a round — the most expensive unit in the D phase, since a lost angle
// re-runs the whole proposal cycle.

import { mkdtemp, rm, writeFile, readFile, access } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import { resolveResumeVersion } from "../../src/discovery/proposal_cursor.js";
import { preserveExistingArchive } from "../../src/discovery/stages/neg1_2.js";

const tmpdirs: string[] = [];
async function tmp(): Promise<string> {
  const d = await mkdtemp(path.join(os.tmpdir(), "cursor-contract-"));
  tmpdirs.push(d);
  return d;
}
afterEach(async () => {
  await Promise.all(tmpdirs.splice(0).map((d) => rm(d, { recursive: true, force: true })));
});

describe("resume version accounts for an authored-but-unreviewed draft", () => {
  const iterations = [
    { angle: 0, version: 1 },
    { angle: 0, version: 2 },
    { angle: 1, version: 1 },
  ];

  it("uses the cursor version when it exceeds the last REVIEWED version", () => {
    // v3 was authored but the reviewer never wrote its row. Deriving from `iterations`
    // alone returns 2, and the producer's `current_version + 1` then re-authors v3 over
    // the existing draft.
    expect(resolveResumeVersion({ angle: 0, iterations, cursorAngle: 0, cursorVersion: 3 })).toBe(3);
  });

  it("ignores the cursor when it points at a different angle", () => {
    expect(resolveResumeVersion({ angle: 0, iterations, cursorAngle: 1, cursorVersion: 9 })).toBe(2);
  });

  it("falls back to the reviewed max when there is no cursor version", () => {
    expect(resolveResumeVersion({ angle: 0, iterations, cursorAngle: 0, cursorVersion: undefined })).toBe(2);
  });

  it("returns 0 for an angle with no history at all", () => {
    expect(resolveResumeVersion({ angle: 2, iterations, cursorAngle: 0, cursorVersion: 1 })).toBe(0);
  });
});

describe("archiving never destroys a previous archive", () => {
  it("parks an incumbent archive aside instead of overwriting it", async () => {
    // Archive names are keyed by angle only, so a second pivot off the same angle used
    // to overwrite the first — and the cursor reset would then restore a draft from a
    // different version than the one it re-seated to.
    const dir = await tmp();
    const target = path.join(dir, "proposal_angle0_rejected.tex");
    await writeFile(target, "FIRST PIVOT DRAFT", "utf8");

    const parked = await preserveExistingArchive(target);
    expect(parked).toBe(`${target}.prev1`);
    expect(await readFile(parked!, "utf8")).toBe("FIRST PIVOT DRAFT");
    await expect(access(target)).rejects.toThrow(); // freed for the new archive

    await writeFile(target, "SECOND PIVOT DRAFT", "utf8");
    const parked2 = await preserveExistingArchive(target);
    expect(parked2).toBe(`${target}.prev2`);
    expect(await readFile(`${target}.prev1`, "utf8")).toBe("FIRST PIVOT DRAFT");
    expect(await readFile(`${target}.prev2`, "utf8")).toBe("SECOND PIVOT DRAFT");
  });

  it("is a no-op when nothing is there", async () => {
    const dir = await tmp();
    expect(await preserveExistingArchive(path.join(dir, "absent.tex"))).toBeNull();
  });
});
