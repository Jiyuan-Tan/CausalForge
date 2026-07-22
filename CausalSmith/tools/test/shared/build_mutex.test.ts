// CausalSmith/tools/test/shared/build_mutex.test.ts
import { describe, it, expect } from "vitest";
import { mkdtemp, rm } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { withPromotionLock } from "../../src/shared/build_mutex.js";

describe("withPromotionLock", () => {
  it("serializes concurrent promotions on the same Causalean root", async () => {
    const root = await mkdtemp(path.join(os.tmpdir(), "promlock-"));
    try {
      let active = 0;
      let maxActive = 0;
      const task = () =>
        withPromotionLock(root, async () => {
          active += 1;
          maxActive = Math.max(maxActive, active);
          await new Promise((r) => setTimeout(r, 40));
          active -= 1;
        });
      await Promise.all([task(), task(), task()]);
      // The whole point of the promotion mutex: never two promotions at once.
      expect(maxActive).toBe(1);
      expect(active).toBe(0);
    } finally {
      await rm(root, { recursive: true, force: true });
    }
  });

  it("runs sequentially (each waiter gets the lock in turn, none errors out)", async () => {
    const root = await mkdtemp(path.join(os.tmpdir(), "promlock-"));
    try {
      const order: number[] = [];
      await Promise.all(
        [0, 1, 2, 3].map((i) =>
          withPromotionLock(root, async () => {
            order.push(i);
            await new Promise((r) => setTimeout(r, 10));
          }),
        ),
      );
      // All four acquired the lock (none dropped on retry exhaustion).
      expect(order.sort()).toEqual([0, 1, 2, 3]);
    } finally {
      await rm(root, { recursive: true, force: true });
    }
  });
});
