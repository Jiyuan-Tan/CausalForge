export type DraftRunner = "codex" | "claude";

// why: keep runner validation exports; dead draft execution helpers were removed after repo grep.
export const DRAFT_RUNNERS: readonly DraftRunner[] = ["codex", "claude"];

export function isDraftRunner(value: string): value is DraftRunner {
  return (DRAFT_RUNNERS as readonly string[]).includes(value);
}
