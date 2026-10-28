#!/usr/bin/env python3
"""Check a characteristic round by round with the designers' reference implementation (pyascon).

For each round r, build an actual state whose active columns take values v with
S(v) xor S(v xor a) = b for the column differences a -> b (other columns random), run one full
round of the reference permutation on the state and on the state xor dX_r, and compare the output
difference with dX_{r+1} (or with Sigma(dY_r) in the last round). The S-box values are taken from
the reference implementation itself, not from our search code.

Usage: verify_trail.py <path to pyascon ascon.py> <characteristic json> [trials per round]
"""
import importlib.util
import json
import random
import sys

spec = importlib.util.spec_from_file_location("ascon_reference", sys.argv[1])
A = importlib.util.module_from_spec(spec)
spec.loader.exec_module(A)
trail = json.load(open(sys.argv[2]))["trail"]
TRIALS = int(sys.argv[3]) if len(sys.argv) > 3 else 20
M = (1 << 64) - 1
C11 = 0xf0 - 11 * 0x10 + 11  # constant used by ascon_permutation(S, rounds=1)
ROT = [(19, 28), (61, 39), (1, 6), (10, 17), (7, 41)]
SPEC_SBOX = [0x04, 0x0b, 0x1f, 0x14, 0x1a, 0x15, 0x09, 0x02, 0x1b, 0x05, 0x08, 0x12, 0x1d, 0x03, 0x06, 0x1c,
             0x1e, 0x13, 0x07, 0x0e, 0x00, 0x0d, 0x11, 0x18, 0x10, 0x0c, 0x01, 0x19, 0x16, 0x0a, 0x0f, 0x17]


def one_round(S):
    S = list(S)
    A.ascon_permutation(S, 1)
    return S


def col(S, j):  # 5-bit value of column j (row 0 = most significant bit)
    return sum(((S[i] >> j) & 1) << (4 - i) for i in range(5))


def setcol(S, j, v):
    for i in range(5):
        S[i] = (S[i] & ~(1 << j) & M) | (((v >> (4 - i)) & 1) << j)


# S-box of the reference implementation: use states whose 64 columns are all equal to v.
# Rotations fix such words, so Sigma(w) = w ^ w ^ w = w; the constant only touches the low
# 8 bits of x2, so column 40 shows S(v) directly.
OS = [col(one_round([M if (v >> (4 - i)) & 1 else 0 for i in range(5)]), 40) for v in range(32)]
print("S-box of the reference implementation equals the specification table:", OS == SPEC_SBOX)

ok_all = True
total = 0
for r, rd in enumerate(trail):
    din = [int(h, 16) for h in rd["in"]]
    dout = [int(h, 16) for h in rd["out"]]
    if r + 1 < len(trail):
        expected = [int(h, 16) for h in trail[r + 1]["in"]]
    else:
        expected = [dout[i] ^ A.rotr(dout[i], s1) ^ A.rotr(dout[i], s2) for i, (s1, s2) in enumerate(ROT)]
    ok = True
    for _ in range(TRIALS):
        S = [random.getrandbits(64) for _ in range(5)]  # S-box layer input (after the constant)
        for j in range(64):
            a, b = col(din, j), col(dout, j)
            if a:
                cands = [v for v in range(32) if OS[v] ^ OS[v ^ a] == b]
                if not cands:
                    sys.exit(f"round {r} col {j}: transition {a:02x}->{b:02x} is impossible")
                setcol(S, j, random.choice(cands))
        P = list(S)
        P[2] ^= C11  # undo the constant so that the round adds it back
        Q = [P[i] ^ din[i] for i in range(5)]
        O1, O2 = one_round(P), one_round(Q)
        if [O1[i] ^ O2[i] for i in range(5)] != expected:
            ok = False
            break
    act = sum(1 for j in range(64) if col(din, j))
    total += act
    ok_all &= ok
    print(f"round {r}: {act} active S-boxes, {'matched in all ' + str(TRIALS) + ' trials' if ok else 'MISMATCH'}")
print("total active S-boxes:", total)
print("all rounds match the reference implementation:", ok_all)
sys.exit(0 if ok_all else 1)
