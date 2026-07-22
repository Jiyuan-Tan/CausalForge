import { mkdtemp, rm, writeFile, utimes } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import { withRunHeartbeatAt } from "../src/shared/run_heartbeat.js";

const dirs: string[] = [];

afterEach(async () => {
  await Promise.all(dirs.splice(0).map((dir) => rm(dir, { recursive: true, force: true })));
});

describe("run heartbeat", () => {
  it("allows concurrent owners of different qids", async () => {
    const logsA = await mkdtemp(join(tmpdir(), "causalsmith-heartbeat-a-"));
    const logsB = await mkdtemp(join(tmpdir(), "causalsmith-heartbeat-b-"));
    dirs.push(logsA, logsB);

    let entered = 0;
    let enteredBoth!: () => void;
    const bothEntered = new Promise<void>((resolve) => { enteredBoth = resolve; });
    let release!: () => void;
    const held = new Promise<void>((resolve) => {
      release = resolve;
    });
    const run = (logs: string, qid: string) =>
      withRunHeartbeatAt(logs, qid, "spec", async () => {
        entered += 1;
        if (entered === 2) enteredBoth();
        await held;
      });

    const first = run(logsA, "qid-a");
    const second = run(logsB, "qid-b");
    await bothEntered;
    expect(entered).toBe(2);

    release();
    await Promise.all([first, second]);
  });

  it("refuses a concurrent owner of the same presentation bundle", async () => {
    const logs = await mkdtemp(join(tmpdir(), "causalsmith-heartbeat-"));
    dirs.push(logs);
    let release!: () => void;
    const held = new Promise<void>((resolve) => {
      release = resolve;
    });
    const first = withRunHeartbeatAt(logs, "paper", "spec", async () => {
      await held;
    });

    await expect(
      withRunHeartbeatAt(logs, "paper", "spec", async () => undefined),
    ).rejects.toMatchObject({ code: "causalsmith_qid_busy" });

    release();
    await first;
  });

  it("never steals an old heartbeat while its PID is still alive", async () => {
    const logs = await mkdtemp(join(tmpdir(), "causalsmith-heartbeat-live-old-"));
    dirs.push(logs);
    const lock = join(logs, ".run.active");
    await writeFile(lock, `${process.pid} spec 2000-01-01T00:00:00.000Z old-owner\n`);
    const old = new Date("2000-01-01T00:00:00.000Z");
    await utimes(lock, old, old);
    await expect(withRunHeartbeatAt(logs, "paper", "spec", async () => undefined))
      .rejects.toMatchObject({ code: "causalsmith_qid_busy" });
  });

  it("reclaims a heartbeat whose PID is dead", async () => {
    const logs = await mkdtemp(join(tmpdir(), "causalsmith-heartbeat-dead-"));
    dirs.push(logs);
    await writeFile(join(logs, ".run.active"), `999999999 spec 2000-01-01T00:00:00.000Z dead-owner\n`);
    let entered = false;
    await withRunHeartbeatAt(logs, "paper", "spec", async () => { entered = true; });
    expect(entered).toBe(true);
  });

  it("allows only one of two simultaneous dead-owner reclaimers", async () => {
    const logs = await mkdtemp(join(tmpdir(), "causalsmith-heartbeat-dead-race-"));
    dirs.push(logs);
    await writeFile(join(logs, ".run.active"), `999999999 spec 2000-01-01T00:00:00.000Z dead-owner\n`);
    let entered = 0;
    let enteredOnce!: () => void;
    const oneEntered = new Promise<void>((resolve) => { enteredOnce = resolve; });
    let rejectedOnce!: (error: unknown) => void;
    const oneRejected = new Promise<unknown>((resolve) => { rejectedOnce = resolve; });
    let release!: () => void;
    const held = new Promise<void>((resolve) => { release = resolve; });
    const run = () => withRunHeartbeatAt(logs, "paper", "spec", async () => {
      entered += 1;
      enteredOnce();
      await held;
    });
    const wrap = (p: Promise<void>) => p.then(
      () => ({ status: "fulfilled" as const }),
      (error: unknown) => { rejectedOnce(error); return { status: "rejected" as const, error }; },
    );
    const first = wrap(run());
    const second = wrap(run());
    await oneEntered;
    expect(await oneRejected).toMatchObject({ code: "causalsmith_qid_busy" });
    expect(entered).toBe(1);
    release();
    const results = await Promise.all([first, second]);
    expect(results.filter((r) => r.status === "rejected")).toHaveLength(1);
  });
});
