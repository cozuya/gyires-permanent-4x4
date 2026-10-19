#!/usr/bin/env python3
"""Generate all full-flag representatives for the exact permanent certificate.

Only Python's standard library is used. The certificate data go to stdout;
counts go to stderr. Matrix entries are printed in row-major order.
"""
from itertools import permutations
from math import gcd
import sys

PERMS = list(permutations(range(4)))
PERM_MASKS = [sum(1 << (4*i + p[i]) for i in range(4)) for p in PERMS]
FULL = (1 << 16) - 1


def components(mask):
    adjacency = [[] for _ in range(8)]
    for i in range(4):
        for j in range(4):
            if mask & (1 << (4*i + j)):
                adjacency[i].append(4+j)
                adjacency[4+j].append(i)
    seen = set()
    count = 0
    for start in range(8):
        if start in seen:
            continue
        count += 1
        stack = [start]
        while stack:
            v = stack.pop()
            if v not in seen:
                seen.add(v)
                stack.extend(adjacency[v])
    return count


# A support is a face support exactly when it is the union of the
# permutation supports contained in it.
faces = {}
centers = {}
for mask in range(1 << 16):
    vertices = [p for p in PERM_MASKS if (p & mask) == p]
    if not vertices:
        continue
    union = 0
    for p in vertices:
        union |= p
    if union != mask:
        continue
    dimension = mask.bit_count() - 8 + components(mask)
    faces[mask] = (dimension, vertices)
    entries = [sum((p >> ij) & 1 for p in vertices) for ij in range(16)]
    divisor = 0
    for value in entries:
        divisor = gcd(divisor, value)
    centers[mask] = [value // divisor for value in entries]
    assert max(centers[mask]) <= 6

expected_face_counts = [24, 240, 978, 1968, 2176, 1392, 528, 120, 16, 1]
face_counts = [sum(d == k for d, _ in faces.values()) for k in range(10)]
assert face_counts == expected_face_counts

# Obtain every facet by setting an entry to zero and then taking the
# union of the surviving permutation supports.
facets = {}
flag_counts = {}
for mask, (dimension, vertices) in sorted(faces.items(), key=lambda kv: kv[1][0]):
    children = set()
    if dimension:
        for ij in range(16):
            if not (mask & (1 << ij)):
                continue
            child = 0
            for p in vertices:
                if not (p & (1 << ij)):
                    child |= p
            if child in faces and faces[child][0] == dimension - 1:
                children.add(child)
        assert children
        flag_counts[mask] = sum(flag_counts[child] for child in children)
    else:
        flag_counts[mask] = 1
    facets[mask] = sorted(children)
assert flag_counts[FULL] == 37656576

# The 576 independent row/column permutations act on support masks.
actions = [
    [1 << (4*r[i] + c[j]) for i in range(4) for j in range(4)]
    for r in PERMS for c in PERMS
]


def transform(mask, action):
    result = 0
    while mask:
        bit = mask & -mask
        mask -= bit
        result |= actions[action][bit.bit_length() - 1]
    return result


# At each step take facet orbits under the stabilizer of the preceding
# chain. This gives one representative of every full-flag orbit.
flags = []


def visit(chain, stabilizer):
    if len(chain) == 10:
        assert len(stabilizer) == 1
        flags.append(chain)
        return
    children = set(facets[chain[-1]])
    done = set()
    for child in sorted(children):
        if child in done:
            continue
        orbit = {transform(child, g) for g in stabilizer}
        assert orbit <= children
        done.update(orbit)
        child_stabilizer = [g for g in stabilizer if transform(child, g) == child]
        visit(chain + [child], child_stabilizer)
    assert done == children


visit([FULL], list(range(576)))
assert len(flags) == 65376
assert len(flags) * 576 == flag_counts[FULL]
print("faces by dimension:", face_counts, file=sys.stderr)
print("maximal flags:", flag_counts[FULL], file=sys.stderr)
print("representatives:", len(flags), file=sys.stderr)
print(len(flags))
for flag in flags:
    print(" ".join(str(x) for mask in flag for x in centers[mask]))
