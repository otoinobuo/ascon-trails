#!/usr/bin/env python3
"""Extend a 4-round characteristic by one round forward and backward, as in Section 2 of the note.

Forward: re-choose the output differences of the last S-box layer (all DDT-compatible choices
are enumerated) to minimise the number of active S-boxes in the next round.
Backward: the input difference of round 0 fixes Sigma^-1 of it uniquely, so the cost of the
preceding round is the number of non-zero columns of that value.

Usage: extend.py <4-round characteristic json> [output json for the 5-round characteristic]
"""
import itertools
import json
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "search"))
import ascon_active as AA  # noqa: E402

t = json.load(open(sys.argv[1]))["trail"]
M = (1 << 64) - 1
rotr = lambda x, s: ((x >> s) | (x << (64 - s))) & M
L = lambda Y: [Y[i] ^ rotr(Y[i], s1) ^ rotr(Y[i], s2) for i, (s1, s2) in enumerate(AA.ROT)]
col = lambda S, j: sum(((S[i] >> j) & 1) << (4 - i) for i in range(5))
nz = lambda X: bin(X[0] | X[1] | X[2] | X[3] | X[4]).count("1")
hexw = lambda V: [f"{v:016x}" for v in V]


def put(cols_vals):
    Y = [0] * 5
    for j, b in cols_vals:
        for i in range(5):
            Y[i] |= ((b >> (4 - i)) & 1) << j
    return Y


# Forward extension
last = len(t) - 1
din = [int(h, 16) for h in t[last]["in"]]
cols = [j for j in range(64) if col(din, j)]
choices = [[b for b in range(1, 32) if AA.DDT[col(din, j)][b]] for j in cols]
best = min(itertools.product(*choices), key=lambda c: nz(L(put(zip(cols, c)))))
Y = put(zip(cols, best))
X = L(Y)
nxt_cols = [j for j in range(64) if col(X, j)]
Ynext = put((j, next(b for b in range(1, 32) if AA.DDT[col(X, j)][b])) for j in nxt_cols)
ext = [dict(r) for r in t[:last]] + [{"in": t[last]["in"], "out": hexw(Y)}, {"in": hexw(X), "out": hexw(Ynext)}]
active, weight = AA.check_trail(ext)
print(f"forward: +{nz(X)} active S-boxes -> {len(ext)} rounds, {active} active, weight {weight}")
if len(sys.argv) > 2:
    json.dump({"trail": ext}, open(sys.argv[2], "w"))


# Backward extension: invert each Sigma_i by iterating it (Sigma_i has finite order)
def inv_row(x, s1, s2):
    f = lambda v: v ^ rotr(v, s1) ^ rotr(v, s2)
    seq, v = [x], f(x)
    while v != x:
        seq.append(v)
        v = f(v)
    return seq[-1]  # f(seq[-1]) = x


X0 = [int(h, 16) for h in t[0]["in"]]
Yprev = [inv_row(X0[i], s1, s2) for i, (s1, s2) in enumerate(AA.ROT)]
assert L(Yprev) == X0
print(f"backward: +{nz(Yprev)} active S-boxes -> {len(t) + 1} rounds, {nz(Yprev) + active - nz(X)} active")
