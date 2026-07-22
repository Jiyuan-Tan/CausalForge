import { describe, it, expect } from "vitest";
import { consumePendingScaffoldRedirect } from "../../src/formalization/dispatcher.js";

const mkArgs = (redirect: string | null) =>
  ({ ctx: {} as never, state: { flags: { scaffold_redirect: redirect } } as never, deps: {} as never });

describe("consumePendingScaffoldRedirect", () => {
  it("no pending redirect → no scaffold call", async () => {
    let called = 0;
    const out = await consumePendingScaffoldRedirect(mkArgs(null), (async () => {
      called += 1;
      return { stage: "2", status: "completed", message: "" } as never;
    }) as never);
    expect(out).toBeNull();
    expect(called).toBe(0);
  });
  it("pending redirect → one scaffold pass, loop proceeds on completion", async () => {
    let called = 0;
    const out = await consumePendingScaffoldRedirect(mkArgs("fix decl X"), (async () => {
      called += 1;
      return { stage: "2", status: "completed", message: "" } as never;
    }) as never);
    expect(out).toBeNull();
    expect(called).toBe(1);
  });
  it("pending redirect + blocked scaffold → fail closed with the F2 result", async () => {
    const blocked = { stage: "2", status: "blocked", message: "no" };
    const out = await consumePendingScaffoldRedirect(mkArgs("fix decl X"), (async () => blocked) as never);
    expect(out).toBe(blocked);
  });
});
