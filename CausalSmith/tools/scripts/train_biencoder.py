# tools/scripts/train_biencoder.py
#
# Phase 2 (retrieval-v2): contrastively fine-tune the bge bi-encoder on Causalean pairs
# (build_finetune_data.py), then A/B the fine-tuned encoder against the off-the-shelf model
# on HELD-OUT modules (leak-free) — semantic-only recall on the refs-graph gold.
#
# Query/passage asymmetry mirrors inference: the "a" (query-like) side gets the bge query
# prefix, the "b" (passage) side does not.
#
# Usage: python train_biencoder.py --pairs <dir>/train_pairs.jsonl --test-modules <dir>/test_modules.json \
#                                  --out <model_dir> [--epochs 1] [--batch 64]
import os
os.environ.setdefault("HF_HUB_OFFLINE", "1")
os.environ.setdefault("TRANSFORMERS_OFFLINE", "1")
# Offline cluster: the HF Trainer (used under sentence-transformers .fit) otherwise tries to
# report to Weights & Biases and crashes with "No API key configured".
os.environ.setdefault("WANDB_DISABLED", "true")
os.environ.setdefault("WANDB_MODE", "offline")
os.environ.setdefault("HF_HUB_OFFLINE", "1")
import json, re, math, argparse, sys
import numpy as np

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))
INDEX = os.path.join(ROOT, "doc", "library_index.json")
MODEL = "BAAI/bge-large-en-v1.5"
QUERY_PREFIX = "Represent this sentence for searching relevant passages: "
GOLD_KINDS = {"def", "structure", "inductive", "class", "abbrev", "theorem"}


def humanize(name):
    return re.sub(r"([a-z0-9])([A-Z])", r"\1 \2", name.split(".")[-1]).replace("_", " ").strip()


def first_para(doc):
    return (doc or "").split("\n\n")[0].strip()


def nl_text(e):
    return f"{humanize(e['name'])}. {first_para(e.get('doc')) or (e.get('statement') or '')}".strip()


def load_model(path, max_seq=256):
    from sentence_transformers import SentenceTransformer, models
    word = models.Transformer(path, max_seq_length=max_seq)  # cap seq len — big memory saving, texts mostly fit
    pool = models.Pooling(word.get_word_embedding_dimension(), pooling_mode_cls_token=True, pooling_mode_mean_tokens=False)
    return SentenceTransformer(modules=[word, pool])


def build_gold(ents):
    by = {e["name"]: e for e in ents}
    thms = [e for e in ents if e.get("kind") == "theorem"]
    df = {}
    for T in thms:
        g = {r for r in (T.get("refs") or []) if r in by and r != T["name"] and not T["name"].startswith(r + ".") and by[r].get("kind") in GOLD_KINDS}
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


def eval_model(model, ents, by, gold, test_mods):
    names = [e["name"] for e in ents]
    corpus = model.encode([nl_text(e) for e in ents], normalize_embeddings=True, batch_size=64, show_progress_bar=False)
    corpus = np.asarray(corpus, dtype=np.float32)
    row = {n: i for i, n in enumerate(names)}
    q_thms = [t for t in gold if by[t].get("module") in test_mods]
    qvec = model.encode([QUERY_PREFIX + first_para(by[t].get("doc")) for t in q_thms],
                        normalize_embeddings=True, batch_size=64, show_progress_bar=False)
    qvec = np.asarray(qvec, dtype=np.float32)
    hit3 = rec10 = 0.0
    for i, t in enumerate(q_thms):
        sims = corpus @ qvec[i]
        sims[row[t]] = -1e9  # exclude self
        order = np.argsort(-sims)[:10]
        ranked = [names[j] for j in order]
        g = set(gold[t])
        if any(r in g for r in ranked[:3]):
            hit3 += 1
        rec10 += len(g.intersection(ranked)) / len(g)
    n = len(q_thms)
    return {"n": n, "hit@3": hit3 / n, "recall@10": rec10 / n}


def build_examples(ents, by, gold, test_mods, hard_negs, base_model, InputExample):
    """doc2ref + stmt2doc training examples from TRAIN modules. With hard_negs>0, each doc2ref
    example carries N hard negatives mined by the base model (top non-gold, non-self decls most
    similar to the query) — the signal that most sharpens ranking precision."""
    train_thms = [t for t in gold if by[t].get("module") not in test_mods]
    examples = []
    if hard_negs > 0:
        names = [e["name"] for e in ents]
        corpus = np.asarray(base_model.encode([nl_text(e) for e in ents], normalize_embeddings=True,
                                              batch_size=64, show_progress_bar=False), dtype=np.float32)
        qvec = np.asarray(base_model.encode([QUERY_PREFIX + first_para(by[t].get("doc")) for t in train_thms],
                                            normalize_embeddings=True, batch_size=64, show_progress_bar=False), dtype=np.float32)
        for i, t in enumerate(train_thms):
            g = set(gold[t])
            sims = corpus @ qvec[i]
            negs = []
            for j in np.argsort(-sims):
                n = names[j]
                if n == t or n in g:
                    continue
                negs.append(nl_text(by[n]))
                if len(negs) >= hard_negs:
                    break
            q = QUERY_PREFIX + first_para(by[t].get("doc"))
            for ref in gold[t]:
                examples.append(InputExample(texts=[q, nl_text(by[ref]), *negs]))
    else:
        for t in train_thms:
            q = QUERY_PREFIX + first_para(by[t].get("doc"))
            for ref in gold[t]:
                examples.append(InputExample(texts=[q, nl_text(by[ref])]))
    # stmt2doc cross-view alignment (train modules; in-batch negatives suffice)
    for e in ents:
        if e.get("module") in test_mods:
            continue
        doc = first_para(e.get("doc"))
        stmt = re.sub(r"\s+", " ", (e.get("statement") or "")).strip()
        if doc and stmt:
            examples.append(InputExample(texts=[QUERY_PREFIX + f"{humanize(e['name'])}. {stmt}", f"{humanize(e['name'])}. {doc}"]))
    return examples


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--test-modules", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--epochs", type=int, default=1)
    ap.add_argument("--batch", type=int, default=16)
    ap.add_argument("--seq", type=int, default=256)
    ap.add_argument("--hard-negs", type=int, default=0)
    args = ap.parse_args()

    ents = json.load(open(INDEX))["entries"]
    by, gold = build_gold(ents)
    test_mods = set(json.load(open(args.test_modules)))

    print("== BASELINE (off-the-shelf bge) on held-out modules ==", file=sys.stderr)
    base = load_model(MODEL, max_seq=args.seq)
    base_metrics = eval_model(base, ents, by, gold, test_mods)
    print(json.dumps(base_metrics), file=sys.stderr)

    from sentence_transformers import InputExample, losses
    from torch.utils.data import DataLoader
    examples = build_examples(ents, by, gold, test_mods, args.hard_negs, base, InputExample)
    print(f"training on {len(examples)} examples ({args.epochs} epoch(s), batch {args.batch}, "
          f"seq {args.seq}, hard_negs {args.hard_negs})", file=sys.stderr)
    loader = DataLoader(examples, shuffle=True, batch_size=args.batch)
    loss = losses.MultipleNegativesRankingLoss(base)
    warmup = int(len(loader) * args.epochs * 0.1)
    base.fit(train_objectives=[(loader, loss)], epochs=args.epochs, warmup_steps=warmup,
             use_amp=True, show_progress_bar=True)  # fp16 to halve activation memory
    base.save(args.out)
    print(f"saved fine-tuned model -> {args.out}", file=sys.stderr)

    print("== FINE-TUNED on held-out modules ==", file=sys.stderr)
    ft_metrics = eval_model(base, ents, by, gold, test_mods)
    print(json.dumps({"baseline": base_metrics, "finetuned": ft_metrics}, indent=2))


if __name__ == "__main__":
    main()
