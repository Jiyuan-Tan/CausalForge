#!/usr/bin/env python3
"""Unexecuted exploratory Jiangxi PICC robust/c=0 reanalysis protocol.

The input directory must contain the converted ``survey.tab`` and
``network.tab`` tables.  They are not bundled with this repository; the
authenticated replication download was unavailable in the solve environment.
Randomization follows Zhao (2026), EC.7: independent Bernoulli(1/2), because
the released files omit the original strata.  Deployment uses Zhao's ordinary
inverse on bases whose two-by-two design covariance is positive definite.
"""

from __future__ import annotations

import json
import math
import sys
from dataclasses import dataclass
from math import comb

import numpy as np
import pandas as pd
import torch
from scipy.sparse import coo_matrix, csr_matrix, diags
from scipy.sparse.csgraph import connected_components


torch.set_default_dtype(torch.float64)


@dataclass
class Target:
    ids: np.ndarray
    outcomes: np.ndarray
    own_simple: np.ndarray
    observed_counts: np.ndarray
    friend_sets: list[set[int]]
    m: np.ndarray
    high: int


def clean_inputs(base: str) -> tuple[pd.DataFrame, dict[int, set[int]]]:
    survey = pd.read_csv(f"{base}/survey.tab", sep="\t")
    edges = pd.read_csv(f"{base}/network.tab", sep="\t")
    valid = set(survey.id.astype(int))
    edges = edges[~((edges.network_missname == 1) & edges.network_id.isna())]
    edges = edges[edges.network_id.notna() & (edges.network_id != 99)].copy()
    edges.id = edges.id.astype(int)
    edges.network_id = edges.network_id.astype(int)
    edges = edges[
        edges.id.isin(valid)
        & edges.network_id.isin(valid)
        & (edges.id != edges.network_id)
    ].drop_duplicates(["id", "network_id"])
    by_id = survey.set_index("id")
    first_round = set(by_id[by_id.delay == 0].index.astype(int))
    friends = {
        int(i): set(map(int, group.network_id)) & first_round
        for i, group in edges.groupby("id")
    }
    return survey, friends


def make_target(survey: pd.DataFrame, friends: dict[int, set[int]], high: int) -> Target:
    by_id = survey.set_index("id")
    pool = survey[(survey.delay == 1) & (survey.info_none == 1)].copy()
    pool["m"] = pool.id.map(lambda x: len(friends.get(int(x), set())))
    pool = pool[pool.m >= high].reset_index(drop=True)
    fsets = [friends.get(int(x), set()) for x in pool.id]
    observed_counts = np.array(
        [sum(int(by_id.loc[j, "intensive"] == 1) for j in fs) for fs in fsets],
        dtype=int,
    )
    return Target(
        ids=pool.id.to_numpy(int),
        outcomes=pool.takeup_survey.to_numpy(float),
        own_simple=(pool.intensive.to_numpy() == 0),
        observed_counts=observed_counts,
        friend_sets=fsets,
        m=pool.m.to_numpy(int),
        high=high,
    )


def fold_labels(target: Target, seed: int) -> np.ndarray:
    inverse: dict[int, list[int]] = {}
    for i, friends in enumerate(target.friend_sets):
        for friend in friends:
            inverse.setdefault(friend, []).append(i)
    rows: list[int] = []
    cols: list[int] = []
    for units in inverse.values():
        for i in units:
            for j in units:
                if i != j:
                    rows.append(i)
                    cols.append(j)
    graph = coo_matrix(
        (np.ones(len(rows)), (rows, cols)), shape=(len(target.ids), len(target.ids))
    ).tocsr()
    components, labels = connected_components(graph, directed=False)
    rng = np.random.default_rng(seed)
    component_fold = rng.integers(0, 2, components)
    return component_fold[labels]


def count_probability(m: int, a: int) -> float:
    return comb(m, a) / 2**m if 0 <= a <= m else 0.0


def joint_count_probability(mi: int, mj: int, overlap: int, a: int, b: int) -> float:
    total = 0
    for t in range(overlap + 1):
        if 0 <= a - t <= mi - overlap and 0 <= b - t <= mj - overlap:
            total += comb(overlap, t) * comb(mi - overlap, a - t) * comb(
                mj - overlap, b - t
            )
    return total / 2 ** (mi + mj - overlap)


def design(target: Target, indices: np.ndarray) -> tuple[np.ndarray, csr_matrix]:
    fsets = [target.friend_sets[i] for i in indices]
    m = target.m[indices]
    labels = (target.high, target.high - 1)
    n = len(indices)
    p = np.concatenate(
        [
            np.array([0.5 * count_probability(int(mi), a) for mi in m])
            for a in labels
        ]
    )
    rows: list[int] = []
    cols: list[int] = []
    values: list[float] = []
    for arm_a, _ in enumerate(labels):
        for i in range(n):
            ii = arm_a * n + i
            rows.append(ii)
            cols.append(ii)
            values.append(p[ii] * (1 - p[ii]))
    for i in range(n):
        cov = -p[i] * p[n + i]
        rows.extend([i, n + i])
        cols.extend([n + i, i])
        values.extend([cov, cov])
    for i in range(n):
        for j in range(i + 1, n):
            overlap = len(fsets[i] & fsets[j])
            if overlap == 0:
                continue
            for arm_a, a in enumerate(labels):
                for arm_b, b in enumerate(labels):
                    ii, jj = arm_a * n + i, arm_b * n + j
                    joint = 0.25 * joint_count_probability(
                        int(m[i]), int(m[j]), overlap, a, b
                    )
                    cov = joint - p[ii] * p[jj]
                    if abs(cov) > 1e-16:
                        rows.extend([ii, jj])
                        cols.extend([jj, ii])
                        values.extend([cov, cov])
    omega = coo_matrix((values, (rows, cols)), shape=(2 * n, 2 * n)).tocsr()
    return p, omega


def pilot_moments(target: Target, indices: np.ndarray) -> tuple[float, float, float, float]:
    own = target.own_simple[indices]
    count = target.observed_counts[indices]
    y = target.outcomes[indices]
    y1 = y[own & (count == target.high)]
    y0 = y[own & (count == target.high - 1)]
    mu1 = float(y1.mean()) if len(y1) else 0.0
    mu0 = float(y0.mean()) if len(y0) else 0.0
    var1 = max(mu1 * (1 - mu1), 1e-8)
    var0 = max(mu0 * (1 - mu0), 1e-8)
    return mu1, mu0, var1, var0


def covariance_endpoints(mu1: float, mu0: float) -> tuple[float, float]:
    return max(0.0, mu1 + mu0 - 1.0) - mu1 * mu0, min(mu1, mu0) - mu1 * mu0


def h_value(
    p: np.ndarray,
    omega: csr_matrix,
    moments: tuple[float, float, float, float],
    covariance: float,
) -> float:
    n = len(p) // 2
    inv = 1.0 / p
    a = diags(inv) @ omega @ diags(inv)
    a11 = a[:n, :n]
    a10 = a[:n, n:]
    a00 = a[n:, n:]
    mu1, mu0, var1, var0 = moments
    value = (
        var1 * a11.diagonal().sum()
        + mu1**2 * a11.sum()
        + var0 * a00.diagonal().sum()
        + mu0**2 * a00.sum()
        - 2 * mu1 * mu0 * a10.sum()
        - 2 * covariance * a10.diagonal().sum()
    )
    return float(value / n**2)


def torch_sparse(matrix: csr_matrix) -> torch.Tensor:
    coo = matrix.tocoo()
    indices = torch.tensor(np.vstack([coo.row, coo.col]), dtype=torch.long)
    values = torch.tensor(coo.data)
    return torch.sparse_coo_tensor(indices, values, coo.shape).coalesce()


def optimize_basis(
    p: np.ndarray,
    omega: csr_matrix,
    moments: tuple[float, float, float, float],
    endpoints: tuple[float, float],
    rule: str,
    seeds: tuple[int, ...] = (701, 1701, 2701, 3701),
    steps: int = 500,
) -> tuple[np.ndarray, np.ndarray, dict[str, float]]:
    n = len(p) // 2
    om = torch_sparse(omega)
    pt = torch.tensor(p)
    mu1, mu0, var1, var0 = moments
    hs = [h_value(p, omega, moments, c) for c in endpoints]

    def q_mult(z: torch.Tensor, c: float) -> torch.Tensor:
        z1, z0 = z[:n], z[n:]
        q1 = var1 * z1 + mu1**2 * z1.sum(0, keepdim=True).expand_as(z1)
        q1 = q1 - c * z0 - mu1 * mu0 * z0.sum(0, keepdim=True).expand_as(z0)
        q0 = var0 * z0 + mu0**2 * z0.sum(0, keepdim=True).expand_as(z0)
        q0 = q0 - c * z1 - mu1 * mu0 * z1.sum(0, keepdim=True).expand_as(z1)
        return torch.cat([q1, q0])

    def values(raw_x: torch.Tensor, raw_y: torch.Tensor, cs: tuple[float, ...]):
        x = math.sqrt(n) * raw_x / raw_x.norm()
        y = math.sqrt(n) * raw_y / raw_y.norm()
        zeros = torch.zeros_like(x)
        b = torch.stack([torch.cat([x, zeros]), torch.cat([zeros, y])], dim=1)
        ob = torch.sparse.mm(om, b)
        s = b.T @ ob
        z = ob / pt[:, None]
        gains = []
        for c in cs:
            t = z.T @ q_mult(z, c)
            gains.append(torch.trace(torch.linalg.solve(s, t)) / n**2)
        return x, y, s, torch.stack(gains)

    best = None
    objective_cs = endpoints if rule == "robust" else (0.0,)
    for seed in seeds:
        generator = torch.Generator().manual_seed(seed)
        rx = torch.randn(n, generator=generator, requires_grad=True)
        ry = torch.randn(n, generator=generator, requires_grad=True)
        optimizer = torch.optim.Adam([rx, ry], lr=0.04)
        for _ in range(steps):
            optimizer.zero_grad()
            _, _, s, gains = values(rx, ry, objective_cs)
            eigmin = torch.linalg.eigvalsh(s)[0] / n
            if rule == "robust":
                loss = torch.max(torch.tensor(hs) - gains)
            else:
                loss = -gains[0]
            loss = loss + 1e5 * torch.relu(torch.tensor(1e-8) - eigmin) ** 2
            loss.backward()
            optimizer.step()
        x, y, s, gains = values(rx, ry, objective_cs)
        score = (
            float(torch.max(torch.tensor(hs) - gains).detach())
            if rule == "robust"
            else -float(gains[0].detach())
        )
        if best is None or score < best[0]:
            best = (score, x.detach().numpy(), y.detach().numpy(), float(torch.linalg.eigvalsh(s)[0] / n))
    assert best is not None
    x, y = best[1], best[2]

    def numpy_gain(c: float) -> float:
        b = np.stack([np.r_[x, np.zeros(n)], np.r_[np.zeros(n), y]], axis=1)
        ob = omega @ b
        s = b.T @ ob
        z = ob / p[:, None]
        z1, z0 = z[:n], z[n:]
        q1 = var1 * z1 + mu1**2 * z1.sum(0) - c * z0 - mu1 * mu0 * z0.sum(0)
        q0 = var0 * z0 + mu0**2 * z0.sum(0) - c * z1 - mu1 * mu0 * z1.sum(0)
        t = z.T @ np.r_[q1, q0]
        return float(np.trace(np.linalg.solve(s, t)) / n**2)

    gains_end = [numpy_gain(c) for c in endpoints]
    losses = [h - g for h, g in zip(hs, gains_end)]
    gain0 = numpy_gain(0.0)
    diagnostics = {
        "loss_L": losses[0],
        "loss_U": losses[1],
        "worst_loss": max(losses),
        "gain_0": gain0,
        "regularity": best[3],
        # This is the final heuristic training objective, not a certified
        # upper-minus-lower global-optimality gap.
        "heuristic_objective": (
            max(losses)
            if rule == "robust"
            else max(h_value(p, omega, moments, 0.0) - gain0, 0.0)
        ),
    }
    return x, y, diagnostics


def deploy(
    target: Target,
    indices: np.ndarray,
    p: np.ndarray,
    omega: csr_matrix,
    basis: tuple[np.ndarray, np.ndarray],
    moments: tuple[float, float, float, float],
    endpoints: tuple[float, float],
) -> tuple[float, float]:
    n = len(indices)
    x, y = basis
    b = np.stack([np.r_[x, np.zeros(n)], np.r_[np.zeros(n), y]], axis=1)
    own = target.own_simple[indices]
    count = target.observed_counts[indices]
    outcome = target.outcomes[indices]
    d1 = own & (count == target.high)
    d0 = own & (count == target.high - 1)
    d = np.r_[d1.astype(float), d0.astype(float)]
    signed_observed = np.r_[d1.astype(float) * outcome, -d0.astype(float) * outcome]
    yhat = signed_observed / p
    ht = float(np.sum(yhat) / n)
    s = b.T @ (omega @ b)
    # Zhao's observed outcome stack yhat is already armwise inverse-probability
    # weighted.  Section 3.3 applies the additional Pi^{-1} and the ordinary
    # inverse.  A singular basis is outside this deployment domain.
    gamma = np.linalg.solve(s, b.T @ (omega @ (yhat / p)))
    normalizer = np.array([np.mean(d1 / p[:n]), np.mean(d0 / p[n:])])
    gamma_sn = np.divide(gamma, normalizer, out=np.zeros_like(gamma), where=normalizer > 0)
    estimate = ht - float(gamma_sn @ (b.T @ (d - p) / n))
    mu1, mu0, _, _ = moments
    mean_signed = np.r_[np.full(n, mu1), np.full(n, -mu0)]
    cross = float(gamma_sn @ b.T @ (omega @ (mean_signed / p)))
    quadratic = float(gamma_sn @ s @ gamma_sn)
    variances = [h_value(p, omega, moments, c) - 2 * cross / n**2 + quadratic / n**2 for c in endpoints]
    return estimate, math.sqrt(max(max(variances), 0.0))


def analyze_target(target: Target, seed: int) -> dict[str, object]:
    folds = fold_labels(target, seed)
    fold_records: dict[str, list[dict[str, float]]] = {"robust": [], "c0": []}
    for heldout_fold in (0, 1):
        heldout = np.flatnonzero(folds == heldout_fold)
        training = np.flatnonzero(folds != heldout_fold)
        moments = pilot_moments(target, training)
        endpoints = covariance_endpoints(moments[0], moments[1])
        p, omega = design(target, heldout)
        for rule in ("robust", "c0"):
            x, y, diagnostics = optimize_basis(p, omega, moments, endpoints, rule)
            estimate, se = deploy(target, heldout, p, omega, (x, y), moments, endpoints)
            diagnostics.update({"estimate": estimate, "se": se, "n": float(len(heldout))})
            fold_records[rule].append(diagnostics)
    result: dict[str, object] = {
        "n": len(target.ids),
        "fold_sizes": [int(np.sum(folds == 0)), int(np.sum(folds == 1))],
    }
    for rule, records in fold_records.items():
        weights = np.array([r["n"] for r in records]) / len(target.ids)
        result[rule] = {
            "estimate": float(sum(w * r["estimate"] for w, r in zip(weights, records))),
            "se": float(math.sqrt(sum(w**2 * r["se"] ** 2 for w, r in zip(weights, records)))),
            "loss_L": float(sum(w**2 * r["loss_L"] for w, r in zip(weights, records))),
            "loss_U": float(sum(w**2 * r["loss_U"] for w, r in zip(weights, records))),
            "worst_loss": float(
                max(
                    sum(w**2 * r["loss_L"] for w, r in zip(weights, records)),
                    sum(w**2 * r["loss_U"] for w, r in zip(weights, records)),
                )
            ),
            "heuristic_objective_diagnostic": float(
                sum(w**2 * r["heuristic_objective"] for w, r in zip(weights, records))
            ),
            "minimum_regularity": float(min(r["regularity"] for r in records)),
        }
    return result


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("usage: jiangxi_robust_reanalysis.py DATAVERSE_TABLE_DIRECTORY")
    survey, friends = clean_inputs(sys.argv[1])
    output = {}
    for high, seed, label in ((1, 15, "tau_10"), (2, 42, "tau_21"), (3, 21, "tau_32")):
        output[label] = analyze_target(make_target(survey, friends, high), seed)
        print(json.dumps({label: output[label]}, indent=2), flush=True)
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
