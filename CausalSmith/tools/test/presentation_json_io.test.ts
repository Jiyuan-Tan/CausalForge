import { describe, it, expect, afterEach } from "vitest";
import { mkdtemp, readFile, readdir, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { writeJsonAtomic } from "../src/presentation/json_io.js";

const dirs: string[] = [];
afterEach(async () => {
  await Promise.all(dirs.splice(0).map((dir) => rm(dir, { recursive: true, force: true })));
});

describe("writeJsonAtomic (crash-safe cache persistence)", () => {
  it("writes parseable JSON and replaces an existing file, leaving no temp files", async () => {
    const dir = await mkdtemp(join(tmpdir(), "json-io-"));
    dirs.push(dir);
    const path = join(dir, "cache.json");
    await writeJsonAtomic(path, { a: 1 });
    await writeJsonAtomic(path, { a: 2, b: ["x"] });
    expect(JSON.parse(await readFile(path, "utf8"))).toEqual({ a: 2, b: ["x"] });
    expect(await readdir(dir)).toEqual(["cache.json"]);
  });

  it("survives concurrent writers: the file is always one complete document", async () => {
    const dir = await mkdtemp(join(tmpdir(), "json-io-race-"));
    dirs.push(dir);
    const path = join(dir, "cache.json");
    await Promise.all(
      Array.from({ length: 20 }, (_, i) => writeJsonAtomic(path, { winner: i, pad: "y".repeat(2000) })),
    );
    const parsed = JSON.parse(await readFile(path, "utf8")) as { winner: number; pad: string };
    expect(parsed.pad).toBe("y".repeat(2000));
    expect(parsed.winner).toBeGreaterThanOrEqual(0);
    expect(await readdir(dir)).toEqual(["cache.json"]);
  });
});
