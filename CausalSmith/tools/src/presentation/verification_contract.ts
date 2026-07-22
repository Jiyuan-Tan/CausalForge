import { createHash } from "node:crypto";
import { FormalLayerSource, type FormalLayerSource as FormalLayer } from "./formal_layer.js";
import { LeanSnippets, type LeanSnippets as SnippetBundle } from "./types.js";

type AuditCache = Record<string, { key?: string; verdict?: string }>;

const sha = (s: string) => createHash("sha256").update(s).digest("hex");

/**
 * Compact, authoritative P5 trust-boundary payload. Repeated Lean component
 * declarations are interned once and paper objects reference them by hash.
 */
export function buildVerificationContract(
  formalRaw: unknown,
  snippetsRaw: unknown,
  statementAudit: AuditCache = {},
  proofAudit: AuditCache = {},
) {
  const formal: FormalLayer = FormalLayerSource.parse(formalRaw);
  const snippets: SnippetBundle = LeanSnippets.parse(snippetsRaw);
  const declarations: Record<string, { label: string; statement: string }> = {};
  const intern = (label: string, statement: string) => {
    const id = sha(`${label}\n${statement}`).slice(0, 16);
    declarations[id] ??= { label, statement };
    return id;
  };
  const objects = formal.blocks.map((block) => {
    const snippet = snippets.snippets[block.obj_id];
    const declRefs: string[] = [];
    if (snippet?.statement) declRefs.push(intern(snippet.decl, snippet.statement));
    for (const component of snippet?.components ?? []) {
      declRefs.push(intern(component.label, component.statement));
    }
    return {
      obj_id: block.obj_id,
      kind: block.kind,
      title: block.title,
      status: block.status,
      paper_statement: block.body,
      paper_statement_hash: block.body_hash,
      external_dependencies: block.cited_dependencies,
      lean: snippet
        ? {
            decl: snippet.decl,
            file: snippet.file,
            sorry_free: snippet.sorry_free,
            declaration_refs: [...new Set(declRefs)],
          }
        : null,
      audits: {
        statement: statementAudit[block.obj_id]?.verdict ?? null,
        statement_key: statementAudit[block.obj_id]?.key ?? null,
        proof: proofAudit[block.obj_id]?.verdict ?? null,
        proof_key: proofAudit[block.obj_id]?.key ?? null,
      },
    };
  });
  return {
    schema: "causalsmith-p5-verification-contract-v1",
    commit: snippets.commit || formal.commit,
    objects,
    declarations,
  };
}
