import { describe, expect, it } from "vitest";
import { extractResolvedModel, parseStreamJson } from "../../src/workers/claude.js";

describe("parseStreamJson", () => {
  it("collects assistant text blocks", () => {
    const line = JSON.stringify({
      type: "assistant",
      message: { content: [{ type: "text", text: "hello world" }] },
    });
    expect(parseStreamJson(line)).toBe("hello world");
  });

  it("collects the result event's `result` string", () => {
    const line = JSON.stringify({ type: "result", result: "{\"route\":\"user\"}" });
    expect(parseStreamJson(line)).toBe("{\"route\":\"user\"}");
  });

  // Regression: with --json-schema, Claude emits structured payloads via the
  // StructuredOutput tool (not as a text block). Without this branch the
  // intervention judge sees "" and treats valid output as parse_failure.
  it("surfaces StructuredOutput tool_use input as JSON text", () => {
    const line = JSON.stringify({
      type: "assistant",
      message: {
        content: [
          { type: "thinking", thinking: "..." },
          {
            type: "tool_use",
            name: "StructuredOutput",
            input: { route: "stage_neg1", reason: "test" },
          },
        ],
      },
    });
    const parsed = parseStreamJson(line);
    expect(JSON.parse(parsed)).toEqual({ route: "stage_neg1", reason: "test" });
  });

  it("surfaces result.structured_output as JSON text when result string is empty", () => {
    const line = JSON.stringify({
      type: "result",
      result: "",
      structured_output: { route: "user", reason: "fallback" },
    });
    const parsed = parseStreamJson(line);
    expect(JSON.parse(parsed)).toEqual({ route: "user", reason: "fallback" });
  });

  // Regression: the result event's `result` string repeats the final assistant
  // text; collecting both doubled every single-turn reply.
  it("does not duplicate assistant text repeated by the result event", () => {
    const lines = [
      JSON.stringify({
        type: "assistant",
        message: { content: [{ type: "text", text: "final reply body" }] },
      }),
      JSON.stringify({ type: "result", result: "final reply body" }),
    ].join("\n");
    expect(parseStreamJson(lines)).toBe("final reply body");
  });

  it("keeps a result string that adds unseen text", () => {
    const lines = [
      JSON.stringify({
        type: "assistant",
        message: { content: [{ type: "text", text: "intermediate" }] },
      }),
      JSON.stringify({ type: "result", result: "different final" }),
    ].join("\n");
    expect(parseStreamJson(lines)).toBe("intermediate\ndifferent final");
  });

  it("ignores StructuredOutput tool_use without an input object", () => {
    const line = JSON.stringify({
      type: "assistant",
      message: { content: [{ type: "tool_use", name: "StructuredOutput", input: null }] },
    });
    expect(parseStreamJson(line)).toBe("");
  });
});

describe("extractResolvedModel", () => {
  it("prefers the assistant message's served model id over the init event's", () => {
    const lines = [
      JSON.stringify({ type: "system", subtype: "init", model: "claude-opus-4-8" }),
      JSON.stringify({
        type: "assistant",
        message: { model: "claude-opus-4-8-20260115", content: [{ type: "text", text: "hi" }] },
      }),
    ].join("\n");
    expect(extractResolvedModel(lines)).toBe("claude-opus-4-8-20260115");
  });

  it("falls back to the init event when no assistant turn carries a model", () => {
    const lines = [
      "non-json banner",
      JSON.stringify({ type: "system", subtype: "init", model: "claude-opus-4-8" }),
      JSON.stringify({ type: "result", result: "done" }),
    ].join("\n");
    expect(extractResolvedModel(lines)).toBe("claude-opus-4-8");
  });

  it("returns null when the stream carries no model id", () => {
    expect(extractResolvedModel("")).toBeNull();
    expect(extractResolvedModel(JSON.stringify({ type: "result", result: "x" }))).toBeNull();
  });
});
