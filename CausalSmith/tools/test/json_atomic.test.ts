// `writeJsonAtomic` must be usable as the sole writer of a canonical store.
//
// It is the shared atomic-write helper for every canonical D-stage store, but it used
// to require its destination directory to already exist. `artifactPath`'s docstring
// puts that obligation on writers ("Writers must mkdir the dirname (subfolder)") and
// 24 of its 25 call sites do not honour it — they depend on some earlier stage having
// created `discovery/` first. That dependency is invisible at the call site and only
// shows up as ENOENT on the one path where the store is written first, which is how
// it surfaced: a test calling `saveWorkingState` on a fresh run tree, where every
// sibling test had quietly compensated with a manual `mkdir`.
//
// Ensuring the dirname here makes the contract true by construction instead of by 24
// disciplined call sites, and matches every other store writer in the tree
// (state.ts, log.ts, decision_log.ts, graph/store.ts, ledger_update.ts).

import { describe, it, expect, beforeEach } from "vitest";
import { mkdtemp, readFile, readdir, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { writeJsonAtomic } from "../src/shared/json_atomic.js";

let root: string;

beforeEach(async () => {
  root = await mkdtemp(path.join(os.tmpdir(), "json-atomic-"));
});

describe("writeJsonAtomic", () => {
  it("creates a missing destination directory rather than failing with ENOENT", async () => {
    const target = path.join(root, "doc", "research", "active", "qid", "discovery", "d0_working.json");
    await writeJsonAtomic(target, { round: 2 });
    expect(JSON.parse(await readFile(target, "utf8"))).toEqual({ round: 2 });
  });

  it("overwrites an existing store", async () => {
    const target = path.join(root, "store.json");
    await writeJsonAtomic(target, { v: 1 });
    await writeJsonAtomic(target, { v: 2 });
    expect(JSON.parse(await readFile(target, "utf8"))).toEqual({ v: 2 });
  });

  it("leaves no temp debris beside the target", async () => {
    const target = path.join(root, "nested", "store.json");
    await writeJsonAtomic(target, { ok: true });
    expect(await readdir(path.dirname(target))).toEqual(["store.json"]);
  });

  it("leaves no temp debris when serialization throws", async () => {
    const target = path.join(root, "nested", "store.json");
    await writeFile(path.join(root, "sentinel"), "x");
    const cyclic: Record<string, unknown> = {};
    cyclic.self = cyclic;
    await expect(writeJsonAtomic(target, cyclic)).rejects.toThrow();
    expect(await readdir(path.dirname(target))).toEqual([]);
  });
});
