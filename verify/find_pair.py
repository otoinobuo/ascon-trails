#!/usr/bin/env python3
"""SAT search for a concrete pair of states that follows a characteristic.

Usage: find_pair.py <rounds> <first round index> <characteristic json>
The result is re-checked with a round function written separately from the SAT encoding.
"""
import json,sys,time
from pysat.solvers import Cadical153
R=int(sys.argv[1]); start=int(sys.argv[2]); path=sys.argv[3]
S=[0x04,0x0b,0x1f,0x14,0x1a,0x15,0x09,0x02,0x1b,0x05,0x08,0x12,0x1d,0x03,0x06,0x1c,0x1e,0x13,0x07,0x0e,0x00,0x0d,0x11,0x18,0x10,0x0c,0x01,0x19,0x16,0x0a,0x0f,0x17]
ROT=[(19,28),(61,39),(1,6),(10,17),(7,41)]
d=json.load(open(path)); tr=d['trail'] if isinstance(d,dict) else d
tr=[{k:[int(x,16) for x in t[k]] for k in('in','out')} for t in tr][:R]
assert len(tr)==R
n=0
def new():
    global n; n+=1; return n
X=[[[new() for j in range(64)] for w in range(5)] for r in range(R)]
Y=[[[new() for j in range(64)] for w in range(5)] for r in range(R)]
s=Cadical153(); cl=0
def add(c):
    global cl; s.add_clause(c); cl+=1
def col(words,j): 
    v=0
    for w in range(5): v=(v<<1)|((words[w]>>j)&1)
    return v
for r in range(R):
    c=(0xf0-(start+r)*0x10+(start+r))&0xff
    for j in range(64):
        cb=(c>>j)&1 if j<8 else 0
        inp=[X[r][w][j] for w in range(5)]
        if cb: inp[2]=-inp[2]
        match=lambda v:[(-inp[w] if (v>>(4-w))&1 else inp[w]) for w in range(5)]
        a=col(tr[r]['in'],j); b=col(tr[r]['out'],j)
        for v in range(32):
            m=match(v)
            if a and (S[v]^S[v^a])!=b: add(m)
            if not a: assert b==0
            for w in range(5):
                bit=(S[v]>>(4-w))&1
                add(m+[Y[r][w][j] if bit else -Y[r][w][j]])
    if r<R-1:
        for w,(r1,r2) in enumerate(ROT):
            for j in range(64):
                t,a1,a2,a3=X[r+1][w][j],Y[r][w][j],Y[r][w][(j+r1)%64],Y[r][w][(j+r2)%64]
                for m in range(16):
                    if bin(m).count('1')%2==1:
                        add([(-q if (m>>i)&1 else q) for i,q in enumerate((t,a1,a2,a3))])
print('vars',n,'clauses',cl,flush=True)
t0=time.time(); ok=s.solve(); print('result',ok,'sec',round(time.time()-t0,1),flush=True)
if not ok: sys.exit(0)
mod=set(l for l in s.get_model() if l>0)
state=[sum(1<<j for j in range(64) if X[0][w][j] in mod) for w in range(5)]
print('X0',[f'{x:016x}' for x in state],flush=True)
# Independent re-check, written from the specification, not from the SAT encoding
M=(1<<64)-1
rr=lambda x,k:((x>>k)|(x<<(64-k)))&M
def rnd(x,i):
    x=list(x); x[2]^=(0xf0-i*0x10+i)&0xff
    x[0]^=x[4];x[4]^=x[3];x[2]^=x[1]
    t=[(~x[k]&M)&x[(k+1)%5] for k in range(5)]
    x=[x[k]^t[(k+1)%5] for k in range(5)]
    x[1]^=x[0];x[0]^=x[4];x[3]^=x[2];x[2]=~x[2]&M
    return [x[k]^rr(x[k],ROT[k][0])^rr(x[k],ROT[k][1]) for k in range(5)]
a=state;b=[state[k]^tr[0]['in'][k] for k in range(5)]
good=True
for r in range(R):
    a=rnd(a,start+r);b=rnd(b,start+r);diff=[a[k]^b[k] for k in range(5)]
    if r<R-1: exp=tr[r+1]['in']
    else: exp=[tr[r]['out'][k]^rr(tr[r]['out'][k],ROT[k][0])^rr(tr[r]['out'][k],ROT[k][1]) for k in range(5)]
    print(' round',r,'match',diff==exp); good&=diff==exp
print('ALL ROUNDS FOLLOWED',good)
