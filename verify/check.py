#!/usr/bin/env python3
"""One pair of Ascon states that follows the 4-round characteristic with 42 active S-boxes.

No dependencies and no trust in the search code: the Ascon round below is written from
NIST SP 800-232. The script only runs two states through rounds 8..11 of the permutation and
counts, at the input of each S-box layer, the columns where the two states differ.
Expected output: 15, 11, 9, 7 active S-boxes, 42 in total, and an output difference equal to
Sigma(dY_3) of the table in the note.
"""
M = (1 << 64) - 1
ROT = [(19, 28), (61, 39), (1, 6), (10, 17), (7, 41)]

def rr(x, k):
    return ((x >> k) | (x << (64 - k))) & M

def sbox(x):
    x = list(x)
    x[0] ^= x[4]; x[4] ^= x[3]; x[2] ^= x[1]
    t = [(~x[i] & M) & x[(i + 1) % 5] for i in range(5)]
    x = [x[i] ^ t[(i + 1) % 5] for i in range(5)]
    x[1] ^= x[0]; x[0] ^= x[4]; x[3] ^= x[2]; x[2] = ~x[2] & M
    return x

def linear(x):
    return [x[i] ^ rr(x[i], ROT[i][0]) ^ rr(x[i], ROT[i][1]) for i in range(5)]

def active(a, b):
    d = 0
    for u, v in zip(a, b):
        d |= u ^ v
    return bin(d).count("1")

P = [0xa69ddcdf1017bede, 0x84a033cdd3354b73, 0x6bcd5a36901c4381, 0x2638430fac79e91d, 0xa480735de75e0dc8]
D = [0xb9460e2000000000, 0x0000004080000001, 0x39460c6080000000, 0x0000000000000000, 0x0000000000000001]

a, b = P, [p ^ d for p, d in zip(P, D)]
total = 0
for i in range(8, 12):
    n = active(a, b)
    total += n
    print(f"round {i}: {n} active S-boxes")
    c = 0xf0 - i * 0x10 + i
    a = list(a); a[2] ^= c
    b = list(b); b[2] ^= c
    a, b = linear(sbox(a)), linear(sbox(b))
print("total:", total)
print("output difference:", " ".join(f"{u ^ v:016x}" for u, v in zip(a, b)))
# dY_3 of the table in the note; the prediction is Sigma(dY_3), computed here from the table alone
DY3 = [0x0000004000000000, 0x0000104044100440, 0, 0, 0x0000100044100440]
print("matches the characteristic:", linear(DY3) == [u ^ v for u, v in zip(a, b)])
