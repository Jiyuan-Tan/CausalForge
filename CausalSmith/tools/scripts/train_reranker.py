# tools/scripts/train_reranker.py
#
# Phase 2c (retrieval-v2): fine-tune a cross-encoder reranker on Causalean pairs and A/B it
# against the fine-tuned BI-ENCODER's own ranking on HELD-OUT modules (leak-free).
#
# The bi-encoder (Phase 2a/2b) must compress each decl to a single point; the cross-encoder
# attends the query tokens against the decl text jointly and resolves the "several plausibly
# related lemmas — which one" confusions that dominate rank-2-vs-rank-7 errors. It reranks only
# the bi-encoder's top-`pool` candidates, so it earns its keep iff it reorders that pool better.
#
# Training signal (offline, no LLM — derived from the index, TRAIN modules only):
#   query    = a theorem's docstring first paragraph (the NL-description retrieval task)
#   positive = each core ref of that theorem (label 1)                 -> nl_text(ref)
#   negative = hard negatives mined from the FINE-TUNED bi-encoder's top-k for the query,
#              excluding self + gold (label 0) — the decls the bi-encoder confuses for the
#              answer, which is exactly what a reranker must learn to separate.
#
# The held-out eval reranks the bi-encoder's top-`pool` on TEST-module theorems and reports
# hit@3 / recall@10 BEFORE (bi-encoder order) vs AFTER (reranked) — the exact production lift.
#
# Usage: CUDA_VISIBLE_DEVICES=<free gpu> python3 train_reranker.py \
#          --test-modules <dir>/test_modules.json --out <ce_model_dir> \
#          [--bi-model doc/retrieval_model_ft] [--epochs 2] [--batch 32] [--hard-negs 6] [--pool 50]
import os
os.environ.setdefault("HF_HUB_OFFLINE", "1")
os.environ.setdefault("TRANSFORMERS_OFFLINE", "1")
os.environ.setdefault("WANDB_DISABLED", "true")
os.environ.setdefault("WANDB_MODE", "offline")
import json, re, math, argparse, sys
import numpy as np

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))
INDEX = os.path.join(ROOT, "doc", "library_index.json")
BI_MODEL_DEFAULT = "doc/retrieval_model_ft"          # the Phase 2b fine-tuned bi-encoder
# bge-reranker-base (xlm-roberta, ~278M): a purpose-built retrieval reranker. On the held-out
# dependency-proxy gold it lifts the FT bi-encoder's top-50 by hit@3 0.718→0.775, recall@10
# 0.581→0.702 with `--passage nbr`. The lighter cross-encoder/ms-marco-MiniLM-L-6-v2 (web-QA
# relevance) HURT it (0.718→0.501) — the base model + passage richness are the levers, not size.
CE_BASE = "BAAI/bge-reranker-base"
QUERY_PREFIX = "Represent this sentence for searching relevant passages: "  # bge convention (bi-encoder only)
GOLD_KINDS = {"def", "structure", "inductive", "class", "abbrev", "theorem"}


def humanize(name):
    return re.sub(r"([a-z0-9])([A-Z])", r"\1 \2", name.split(".")[-1]).replace("_", " ").strip()


def first_para(doc):
    return (doc or "").split("\n\n")[0].strip()


def nl_text(e):
    return f"{humanize(e['name'])}. {first_para(e.get('doc')) or (e.get('statement') or '')}".strip()


MAX_NEIGHBORS = 16


def build_nbr_ctx(ents):
    present = {e["name"] for e in ents}
    rev = {}
    for e in ents:
        for r in e.get("refs", []) or []:
            if r in present and r != e["name"]:
                rev.setdefault(r, []).append(e["name"])
    return present, rev


def make_passage(e, view, ctx):
    """Passage text for the cross-encoder. `nl` = humanized name + doc; `nbr` additionally
    appends the humanized names of dependency-graph neighbours — the view the bi-encoder wins
    with, so the reranker sees at least as much vocabulary as the recall stage did."""
    if view != "nbr":
        return nl_text(e)
    present, rev = ctx
    head = humanize(e["name"])
    body = first_para(e.get("doc")) or ""
    refs = [r for r in (e.get("refs") or []) if r in present and r != e["name"]]
    revs = [r for r in rev.get(e["name"], []) if r != e["name"]]
    seen, neigh = set(), []
    for r in refs + revs:
        if r in seen:
            continue
        seen.add(r)
        neigh.append(humanize(r))
        if len(neigh) >= MAX_NEIGHBORS:
            break
    tail = (" Related: " + "; ".join(neigh)) if neigh else ""
    return f"{head}. {body}{tail}".strip()


def resolve_dir(model_id):
    cand = model_id if os.path.isabs(model_id) else os.path.join(ROOT, model_id)
    return cand if os.path.isdir(cand) and os.path.exists(os.path.join(cand, "modules.json")) else model_id


def load_bi(path, max_seq=256):
    from sentence_transformers import SentenceTransformer, models
    resolved = resolve_dir(path)
    if os.path.isdir(resolved) and os.path.exists(os.path.join(resolved, "modules.json")):
        return SentenceTransformer(resolved)  # a saved fine-tuned model carries its pooling cfg
    word = models.Transformer(resolved, max_seq_length=max_seq)
    pool = models.Pooling(word.get_word_embedding_dimension(), pooling_mode_cls_token=True, pooling_mode_mean_tokens=False)
    return SentenceTransformer(modules=[word, pool])


def build_gold(ents):
    by = {e["name"]: e for e in ents}
    thms = [e for e in ents if e.get("kind") == "theorem"]
    df = {}
    for T in thms:
        g = {r for r in (T.get("refs") or []) if r in by and r != T["name"]
             and not T["name"].startswith(r + ".") and by[r].get("kind") in GOLD_KINDS}
        for x in g:
            df[x] = df.get(x, 0) + 1
    N = len(thms)
    idf = {d: math.log((N + 1) / (c + 1)) for d, c in df.items()}
    gold = {}
    for T in thms:
        core = [r for r in (T.get("refs") or []) if r in by and r != T["name"] and not T["name"].startswith(r + ".")
                and by[r].get("kind") in GOLD_KINDS and idf.get(r, 1e9) >= 2.3]
        if core and first_para(T.get("doc")):
            gold[T["name"]] = core
    return by, gold


def bi_rank(bi, ents, by, query_thms, pool):
    """For each query theorem, the bi-encoder's top-`pool` candidate names (self excluded)."""
    names = [e["name"] for e in ents]
    row = {n: i for i, n in enumerate(names)}
    corpus = np.asarray(bi.encode([nl_text(e) for e in ents], normalize_embeddings=True,
                                  batch_size=64, show_progress_bar=False), dtype=np.float32)
    qvec = np.asarray(bi.encode([QUERY_PREFIX + first_para(by[t].get("doc")) for t in query_thms],
                                normalize_embeddings=True, batch_size=64, show_progress_bar=False), dtype=np.float32)
    out = {}
    for i, t in enumerate(query_thms):
        sims = corpus @ qvec[i]
        sims[row[t]] = -1e9  # exclude self
        out[t] = [names[j] for j in np.argsort(-sims)[:pool]]
    return out


def metrics(ranked_by_query, gold, query_thms):
    hit3 = rec10 = full10 = 0.0
    for t in query_thms:
        ranked = ranked_by_query[t]
        g = set(gold[t])
        if any(r in g for r in ranked[:3]):
            hit3 += 1
        inter10 = len(g.intersection(ranked[:10]))
        rec10 += inter10 / len(g)
        if inter10 == len(g):
            full10 += 1
    n = len(query_thms)
    return {"n": n, "hit@3": hit3 / n, "recall@10": rec10 / n, "full-recall@10": full10 / n}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--test-modules", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--bi-model", default=BI_MODEL_DEFAULT)
    ap.add_argument("--ce-base", default=CE_BASE)
    ap.add_argument("--epochs", type=int, default=3)
    ap.add_argument("--batch", type=int, default=32)
    ap.add_argument("--max-len", type=int, default=256)
    ap.add_argument("--hard-negs", type=int, default=6)
    ap.add_argument("--pool", type=int, default=50, help="rerank the bi-encoder top-N (recall pool)")
    ap.add_argument("--passage", default="nbr", choices=["nl", "nbr"], help="passage text view fed to the cross-encoder")
    args = ap.parse_args()

    ents = json.load(open(INDEX))["entries"]
    by, gold = build_gold(ents)
    nbr_ctx = build_nbr_ctx(ents)
    passage = lambda e: make_passage(e, args.passage, nbr_ctx)  # noqa: E731
    test_mods = set(json.load(open(args.test_modules)))
    train_thms = [t for t in gold if by[t].get("module") not in test_mods]
    test_thms = [t for t in gold if by[t].get("module") in test_mods]
    print(f"gold theorems: {len(gold)} ({len(train_thms)} train, {len(test_thms)} test)", file=sys.stderr)

    # Bi-encoder: mine hard negatives for TRAIN queries and build the TEST rerank pool.
    bi = load_bi(args.bi_model, max_seq=args.max_len)
    names = [e["name"] for e in ents]
    row = {n: i for i, n in enumerate(names)}
    corpus = np.asarray(bi.encode([nl_text(e) for e in ents], normalize_embeddings=True,
                                  batch_size=64, show_progress_bar=False), dtype=np.float32)

    # ── training examples: positives (label 1) + bi-mined hard negatives (label 0) ──
    from sentence_transformers import InputExample
    qtrain = np.asarray(bi.encode([QUERY_PREFIX + first_para(by[t].get("doc")) for t in train_thms],
                                  normalize_embeddings=True, batch_size=64, show_progress_bar=False), dtype=np.float32)
    examples, n_pos, n_neg = [], 0, 0
    for i, t in enumerate(train_thms):
        q = first_para(by[t].get("doc"))  # plain NL query — the cross-encoder is NOT bge, no prefix
        g = set(gold[t])
        for ref in gold[t]:
            examples.append(InputExample(texts=[q, passage(by[ref])], label=1.0))
            n_pos += 1
        if args.hard_negs > 0:
            sims = corpus @ qtrain[i]
            negs = []
            for j in np.argsort(-sims):
                n = names[j]
                if n == t or n in g:
                    continue
                negs.append(n)
                if len(negs) >= args.hard_negs:
                    break
            for n in negs:
                examples.append(InputExample(texts=[q, passage(by[n])], label=0.0))
                n_neg += 1
    print(f"training examples: {len(examples)} ({n_pos} pos, {n_neg} neg)", file=sys.stderr)

    # ── held-out rerank pool (bi-encoder top-`pool`) + BEFORE metrics ──
    qtest = np.asarray(bi.encode([QUERY_PREFIX + first_para(by[t].get("doc")) for t in test_thms],
                                 normalize_embeddings=True, batch_size=64, show_progress_bar=False), dtype=np.float32)
    pool = {}
    for i, t in enumerate(test_thms):
        sims = corpus @ qtest[i]
        sims[row[t]] = -1e9
        pool[t] = [names[j] for j in np.argsort(-sims)[:args.pool]]
    before = metrics(pool, gold, test_thms)
    print("== BEFORE (fine-tuned bi-encoder order) ==\n" + json.dumps(before), file=sys.stderr)

    # ── train the cross-encoder ──
    from sentence_transformers.cross_encoder import CrossEncoder
    from torch.utils.data import DataLoader
    ce = CrossEncoder(resolve_dir(args.ce_base), num_labels=1, max_length=args.max_len)
    loader = DataLoader(examples, shuffle=True, batch_size=args.batch)
    warmup = int(len(loader) * args.epochs * 0.1)
    ce.fit(train_dataloader=loader, epochs=args.epochs, warmup_steps=warmup, use_amp=True, show_progress_bar=True)
    ce.save(args.out)
    print(f"saved cross-encoder -> {args.out}", file=sys.stderr)

    # ── AFTER: rerank each pool with the cross-encoder ──
    reranked = {}
    for t in test_thms:
        cands = pool[t]
        scores = ce.predict([[first_para(by[t].get("doc")), passage(by[c])] for c in cands],
                            batch_size=64, show_progress_bar=False)
        order = np.argsort(-np.asarray(scores))
        reranked[t] = [cands[j] for j in order]
    after = metrics(reranked, gold, test_thms)
    print("== AFTER (cross-encoder rerank of the top-%d pool) ==" % args.pool, file=sys.stderr)
    print(json.dumps({"pool": args.pool, "before": before, "after": after}, indent=2))


if __name__ == "__main__":
    main()
