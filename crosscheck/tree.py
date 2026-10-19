#!/usr/bin/env python3
"""Independent mirror of the certificate tree in GyiresCompute/Basic.lean.

Re-implements `checkNode`/`splitCheck` (face closures, facet candidates, centers,
stabilizer-based symmetry reduction) without the polynomial leaf test, checks the
structural conditions, counts the leaf cones, and writes every leaf's ten generator
matrices plus the monomial multiplication tables for `leafcheck.cpp`.

Usage: python3 tree.py OUTPUT_DIR
"""
import itertools
import sys
from array import array
from collections import Counter

NV = 10
FULL = 2**16 - 1
# Same order as Lean's nested flatMap over [0,1,2,3].
PERMS = [list(p) for p in itertools.product(range(4), repeat=4) if len(set(p)) == 4]


def perm_mask(p):
    return sum(1 << (4 * i + p[i]) for i in range(4))


def perm_mat(p):
    return tuple(1 if p[e // 4] == e % 4 else 0 for e in range(16))


def sub_mask(a, b):
    return a & b == a


def perms_in(S):
    return [p for p in PERMS if sub_mask(perm_mask(p), S)]


def closure_of(ps):
    acc = 0
    for p in ps:
        acc |= perm_mask(p)
    return acc


def center_of(ps):
    acc = [0] * 16
    for p in ps:
        for e, v in enumerate(perm_mat(p)):
            acc[e] += v
    return tuple(acc)


ALL_ONES = (1,) * 16
SYMS = [(r, c) for r in PERMS for c in PERMS]


def sym_idx(g, e):
    return 4 * g[0][e // 4] + g[1][e % 4]


def act_mask(g, S):
    return sum(1 << sym_idx(g, e) for e in range(16) if (S >> e) & 1)


def fixes(g, M):
    return all(M[sym_idx(g, e)] == M[e] for e in range(16))


def line_sums_eq(V):
    rows = [sum(V[4 * i:4 * i + 4]) for i in range(4)]
    cols = [sum(V[j::4]) for j in range(4)]
    return len(set(rows + cols)) == 1


def supp_ok(V, S):
    return all((V[e] > 0) == bool((S >> e) & 1) for e in range(16))


def candidates(S):
    return [closure_of(perms_in(S & (FULL ^ (1 << e)))) for e in range(16) if (S >> e) & 1]


def maximals(cands):
    out = []
    for a in cands:
        if not any(sub_mask(a, b) and a != b for b in cands) and a not in out:
            out.append(a)
    return out


def node_ok(pre, S):
    """Structural checks shared by checkNode and splitCheck."""
    ps = perms_in(S)
    S2, V = closure_of(ps), center_of(ps)
    cands = candidates(S2)
    facets = maximals(cands)
    ok = (len(pre) < NV and supp_ok(V, S2) and line_sums_eq(V)
          and all(any(sub_mask(c, f) for f in facets) for c in cands))
    return ok, V, facets


def check_node(fuel, pre, S, G, leaves):
    ps = perms_in(S)
    if len(ps) <= 1:
        leaves.append(pre + [perm_mat(p) for p in ps])
        return len(leaves[-1]) <= NV
    if fuel == 0:
        return False
    ok, V, facets = node_ok(pre, S)
    if not ok:
        return False
    G2 = [g for g in G if fixes(g, V)]
    reps = []
    for f in facets:
        if any(act_mask(g, f) == r for r in reps for g in G2):
            continue
        if not check_node(fuel - 1, pre + [V], f, G2, leaves):
            return False
        reps.append(f)
    return True


def split_check(pre, S, G, reps):
    ok, V, facets = node_ok(pre, S)
    G2 = [g for g in G if fixes(g, V)]
    return (len(perms_in(S)) > 1 and ok
            and all(any(r == f or any(act_mask(g, f) == r for g in G2) for r in reps)
                    for f in facets))


def monos(n, d):
    if n == 0:
        return [[]] if d == 0 else []
    return [[e] + rest for e in range(d, -1, -1) for rest in monos(n - 1, d - e)]


def main(out):
    mask_f = FULL ^ 1
    V0 = center_of(perms_in(mask_f))
    G1 = [g for g in SYMS if fixes(g, V0)]
    # The split used by RequestProject/Cert/Assemble.lean.
    level1 = {65532: [65516, 65500, 65468], 65518: [65516, 65486, 65006],
              65502: [65500, 65498, 65486, 65438, 65246, 64990, 64478]}
    assert split_check([ALL_ONES], mask_f, SYMS, list(level1)), "split_root"
    leaves = []
    for f1, reps in level1.items():
        assert split_check([ALL_ONES, V0], f1, G1, reps), f"split_{f1}"
        c1 = center_of(perms_in(f1))
        G2 = [g for g in G1 if fixes(g, c1)]
        for f2 in reps:
            before = len(leaves)
            assert check_node(14, [ALL_ONES, V0, c1], f2, G2, leaves), f"cert_{f1}_{f2}"
            print(f"cert_{f1}_{f2}: structure OK, {len(leaves) - before} leaf cones")
    shape = Counter((len(gs), sum(gs[-1])) for gs in leaves)
    print(f"total leaf cones: {len(leaves)}; (generators, last generator entry sum): {dict(shape)}")
    buf = array('B')
    for gs in leaves:
        for m in gs:
            buf.extend(m)
    with open(f"{out}/leaves.bin", 'wb') as fh:
        fh.write(buf.tobytes())
    E = {d: monos(NV, d) for d in (1, 2, 4, 8)}
    idx = {d: {tuple(v): i for i, v in enumerate(E[d])} for d in E}
    for a, b, c in ((1, 1, 2), (2, 2, 4), (4, 4, 8)):
        table = array('i', [idx[c][tuple(x + y for x, y in zip(E[a][i], E[b][j]))]
                            for i in range(len(E[a])) for j in range(len(E[b]))])
        with open(f"{out}/T{a}{b}.bin", 'wb') as fh:
            fh.write(table.tobytes())
    assert all(E[1][x] == [int(k == x) for k in range(NV)] for x in range(NV))
    assert all(E[8][k] == [8 if j == 0 else 0 for j in range(NV)] if k == 0 else
               E[8][k] == [7 if j == 0 else int(j == k) for j in range(NV)] for k in range(NV))
    print(f"wrote {len(leaves)} leaves; monomial counts {[len(E[d]) for d in (1, 2, 4, 8)]}")


if __name__ == '__main__':
    main(sys.argv[1])
