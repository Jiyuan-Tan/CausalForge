import { describe, expect, it } from "vitest";
import { resolveCodexSandboxMode } from "../src/shared/codex.js";

describe("resolveCodexSandboxMode", () => {
  it("keeps workspace-write as the portable default", () => {
    expect(resolveCodexSandboxMode({ env: {} })).toBe("workspace-write");
  });

  it("honors an explicit local-config opt-in", () => {
    expect(
      resolveCodexSandboxMode({ env: {}, configured: "danger-full-access" }),
    ).toBe("danger-full-access");
  });

  it("lets the environment override local configuration", () => {
    expect(
      resolveCodexSandboxMode({
        env: { CAUSALSMITH_CODEX_SANDBOX: "workspace-write" },
        configured: "danger-full-access",
      }),
    ).toBe("workspace-write");
  });

  it("fails closed on an invalid override", () => {
    expect(() =>
      resolveCodexSandboxMode({
        env: { CAUSALSMITH_CODEX_SANDBOX: "read-only" },
      }),
    ).toThrow(/must be workspace-write or danger-full-access/);
  });
});
