# Codex Project Guide
Before making changes in this repository, read and follow `.claude/CLAUDE.md`.
Treat it as the project guide for proof style, documentation workflow, and
Lean-specific conventions.

Always verify before finishing work in this repository. For Lean changes, use
the Lean LSP/type checker as the default verification path, following
`.claude/CLAUDE.md`. This is a standing project instruction from the user and
counts as explicit permission to verify before reporting completion.

The `.claude` directory also contains project skills/workflows. In particular, for Lean theorem-proving tasks, inspect the relevant files under:

- `.claude/skills/lean4-theorem-proving/`

Use those skill files as local project guidance when they apply. If any
`.claude` instruction conflicts with higher-priority Codex system/developer
instructions, follow the higher-priority instruction and preserve the project intent as closely as possible.

When the inline prompt header identifies the caller as CausalSmith research (any `CausalSmith/tools/src/research/prompts/stage_*.txt` content), treat the inline prompt as authoritative. Do NOT load `.claude/skills/*/SKILL.md` or `.claude/agents/*.md` unless the inline prompt explicitly names that path. CLAUDE.md cues about conditional skills (e.g. `formalization-with-user`) do not apply inside autonomous CausalSmith research stages.
