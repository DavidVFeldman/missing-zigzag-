def ivec(s,n):
    x=sorted(s); g=[(x[1]-x[0])%n,(x[2]-x[1])%n,(x[0]-x[2])%n]
    return min(tuple(g[i:]+g[:i]) for i in range(3))
def klabel(s,n):
    if len(s)<3: return None
    v=ivec(s,n)
    for k in range(2,n-1):
        if ivec({0,1,k},n)==v: return k
    return None
def enumerate_cycles(n, distinct=False):
    m=n-3; out=[]; seq=[0]*m
    def rec(i,pcs,used):
        if i==m:
            k1=klabel({seq[m-2],seq[m-1],seq[0]},n)
            if k1 is None or k1 in used: return
            u=used|{k1}
            k2=klabel({seq[m-1],seq[0],seq[1]},n)
            if k2 is None or k2 in u: return
            if len(u|{k2})==m: out.append(tuple(seq))
            return
        for c in range(n):
            if distinct and c in pcs: continue
            if i>=2:
                k=klabel({seq[i-2],seq[i-1],c},n)
                if k is None or k in used: continue
                seq[i]=c; rec(i+1,pcs|{c},used|{k})
            else:
                seq[i]=c; rec(i+1,pcs|{c},used)
    for b in range(n):
        seq[1]=b; rec(2,{0,b},frozenset())
    return out
def contour(t,n):
    m=len(t)
    for i in range(m):
        w={t[i],t[(i+1)%m],t[(i+2)%m]}
        if klabel(w,n)==2:
            d1=(t[(i+1)%m]-t[i])%n; d2=(t[(i+2)%m]-t[(i+1)%m])%n
            return "scalar" if (d1==d2 and d1 in(1,n-1)) else "zigzag"
def orbits(sols,n):
    m=n-3; seen=set()
    for t in sols:
        best=None
        for base in [t,tuple(t[(-i)%m] for i in range(m))]:
            for inv in [base,tuple((-x)%n for x in base)]:
                for r in range(m):
                    rot=tuple(inv[(i+r)%m] for i in range(m))
                    c=tuple((x-rot[0])%n for x in rot)
                    if best is None or c<best: best=c
        seen.add(best)
    return len(seen)

print("=== 12TET, all cycles (independent recount) ===")
S=enumerate_cycles(12)
sc=sum(1 for t in S if contour(t,12)=="scalar"); zz=len(S)-sc
print(f"  labeled={len(S)} (paper 1764)  scalar={sc} zigzag={zz}  orbits={orbits(S,12)} (paper 52)")
from collections import Counter
strat=Counter()
for t in S:
    d=[(t[(i+1)%9]-t[i])%12 for i in range(9)]
    strat[sum(1 for x in d if x in (1,11))]+=1
print(f"  strata by #semitone steps S: {dict(sorted(strat.items()))}  (paper 18,36,558,1152 for S=2,3,4,5)")

print("=== 12TET, near-rows (distinct pcs) ===")
D=enumerate_cycles(12,distinct=True)
print(f"  labeled={len(D)} (paper 414)  orbits={orbits(D,12)} (paper 13)")
comp=Counter()
def tclass(s,n):
    best=None
    for t in range(n):
        c=tuple(sorted((x+t)%n for x in s))
        if best is None or c<best: best=c
    return best
for t in D: comp[tclass(set(range(12))-set(t),12)]+=1
print("  omitted-trichord census:")
for s,c in sorted(comp.items(), key=lambda kv:-kv[1]):
    print(f"     {s}: {c}")
print(f"  distinct fraction {len(D)}/{len(S)} = {len(D)/len(S):.4f} (paper 0.2347)")

print("=== Marsden all-trichord rings: are all 192 zigzag? ===")
def ticlass(s,n):
    best=None
    for base in (tuple(s),tuple((-x)%n for x in s)):
        for t in range(n):
            c=tuple(sorted((x+t)%n for x in base))
            if best is None or c<best: best=c
    return best
cnt=0; allzig=True; seq=[0]*12
def rec(i,pcs,used):
    global cnt,allzig
    if i==12:
        c1=ticlass({seq[10],seq[11],seq[0]},12)
        if c1 in used: return
        u=used|{c1}; c2=ticlass({seq[11],seq[0],seq[1]},12)
        if c2 in u: return
        if len(u|{c2})!=12: return
        cnt+=1
        for j in range(12):
            a,b,c=seq[j],seq[(j+1)%12],seq[(j+2)%12]
            if ticlass({a,b,c},12)==ticlass({0,1,2},12):
                d1,d2=(b-a)%12,(c-b)%12
                if d1==d2 and d1 in (1,11): allzig=False
        return
    for c in range(12):
        if c in pcs: continue
        if i>=2:
            cl=ticlass({seq[i-2],seq[i-1],c},12)
            if cl in used: continue
            seq[i]=c; rec(i+1,pcs|{c},used|{cl})
        else:
            seq[i]=c; rec(i+1,pcs|{c},used)
rec(1,{0},frozenset())
print(f"  labeled rings={cnt} (paper 192)  all zigzag: {allzig}")
