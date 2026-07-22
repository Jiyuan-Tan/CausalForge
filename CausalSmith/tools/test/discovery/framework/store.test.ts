import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, rm, writeFile, mkdir, readFile } from "node:fs/promises";
import path from "node:path";
import os from "node:os";
import { z } from "zod";
import { defineJsonStore } from "../../../src/discovery/framework/store.js";
import type { PipelineContext } from "../../../src/types.js";

const DemoSchema = z.object({ round: z.number(), note: z.string() });

let tmp: string;
let ctx: PipelineContext;

beforeEach(async () => {
  tmp = await mkdtemp(path.join(os.tmpdir(), "store-test-"));
  ctx = { repoRoot: tmp, qid: "demo_qid", specialization: "econometrics", dryRun: false, resume: false } as PipelineContext;
});
afterEach(async () => {
  await rm(tmp, { recursive: true, force: true });
});

const demoStore = defineJsonStore({
  id: "demo",
  resolve: (c) => path.join(c.repoRoot, "sub", "demo.json"),
  schema: DemoSchema,
});

describe("defineJsonStore", () => {
  it("load throws loudly with the resolved path when the file is missing", async () => {
    await expect(demoStore.load(ctx)).rejects.toThrow(/store 'demo'.*missing.*demo\.json/s);
  });

  it("loadOptional returns null for a missing file", async () => {
    expect(await demoStore.loadOptional(ctx)).toBeNull();
  });

  it("load and loadOptional both throw on corrupt JSON — corruption never reads as absence", async () => {
    await mkdir(path.join(tmp, "sub"), { recursive: true });
    await writeFile(path.join(tmp, "sub", "demo.json"), "{ not json", "utf8");
    await expect(demoStore.load(ctx)).rejects.toThrow(/store 'demo'.*not valid JSON/s);
    await expect(demoStore.loadOptional(ctx)).rejects.toThrow(/store 'demo'.*not valid JSON/s);
  });

  it("load throws naming the store when the payload fails schema validation", async () => {
    await mkdir(path.join(tmp, "sub"), { recursive: true });
    await writeFile(path.join(tmp, "sub", "demo.json"), JSON.stringify({ round: "x" }), "utf8");
    await expect(demoStore.load(ctx)).rejects.toThrow(/store 'demo'.*schema/s);
  });

  it("save validates, creates the directory, writes atomically, and round-trips", async () => {
    await demoStore.save(ctx, { round: 3, note: "ok" });
    expect(await demoStore.load(ctx)).toEqual({ round: 3, note: "ok" });
    // pretty-printed like every existing canonical store write
    const raw = await readFile(path.join(tmp, "sub", "demo.json"), "utf8");
    expect(raw).toContain("\n  ");
  });

  it("save rejects a value failing the schema before touching disk", async () => {
    await expect(demoStore.save(ctx, { round: Number.NaN as never, note: 5 as never })).rejects.toThrow(/store 'demo'/);
    expect(await demoStore.loadOptional(ctx)).toBeNull();
  });
});
