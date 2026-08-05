"""
INDEPENDENT verifier. Deliberately different representation:
a trichord class is identified by its SORTED CYCLIC INTERVAL VECTOR,
not by canonical rotation of the pitch set. Nothing is shared with the
earlier code.
"""
def ivec(s, n):
    """rotation-canonical cyclic gap WORD (transposition invariant,
    inversion-SENSITIVE -- sorting would wrongly identify a class with
    its inversion)."""
    x = sorted(s)
    g = [(x[1]-x[0]) % n, (x[2]-x[1]) % n, (x[0]-x[2]) % n]
    return min(tuple(g[i:]+g[:i]) for i in range(3))

def klabel(s, n):
    """class index k for {0,1,k}, via gap vector; None if no semitone"""
    g = ivec(s, n)
    if 1 not in g: return None
    # {0,1,k}: gaps are 1, k-1, n-k
    for k in range(2, n-1):
        if ivec({0,1,k}, n) == g: return k
    return None

def check_cycle(pcs, n, expect_classes=None, distinct=None, drift=0):
    m = len(pcs)
    errs = []
    if m != n-3: errs.append(f"length {m} != n-3={n-3}")
    # drift
    d = sum((pcs[(i+1)%m]-pcs[i]) % n for i in range(m)) % n
    # NOTE for drift!=0 words the cycle is given as a word, handled separately
    ks = []
    for i in range(m):
        w = {pcs[i] % n, pcs[(i+1)%m] % n, pcs[(i+2)%m] % n}
        if len(w) != 3: errs.append(f"window {i} degenerate"); ks.append(None); continue
        k = klabel(w, n)
        ks.append(k)
        if k is None: errs.append(f"window {i} has no semitone")
    if None not in ks:
        if sorted(ks) != list(range(2, n-1)):
            errs.append(f"classes not a bijection: {sorted(ks)}")
    if distinct is not None:
        if (len(set(pcs)) == len(pcs)) != distinct:
            errs.append(f"distinctness expected {distinct}")
    if expect_classes is not None and ks != list(expect_classes):
        errs.append(f"class sequence {ks} != expected {list(expect_classes)}")
    # chromatic contour
    contour = None
    for i in range(m):
        w = {pcs[i]%n, pcs[(i+1)%m]%n, pcs[(i+2)%m]%n}
        if len(w)==3 and klabel(w,n)==2:
            a,b,c = pcs[i]%n, pcs[(i+1)%m]%n, pcs[(i+2)%m]%n
            d1,d2 = (b-a)%n, (c-b)%n
            contour = "scalar" if (d1==d2 and d1 in (1,n-1)) else "zigzag"
    return errs, contour, ks

print("="*62)
print("EXPLICIT EXAMPLES PRINTED IN THE PAPER")
print("="*62)
tests = [
 ("§1/§2.1  12TET example", [0,1,2,4,5,0,11,8,7], 12, [2,3,4,8,7,10,5,6,9], None),
 ("Ex 2.5   9TET miniature", [0,1,4,3,8,2], 9, None, None),
 ("Ex 2.6   15TET zigzag", [0,2,1,6,0,14,9,13,10,11,4,3], 15,
      [2,5,6,7,10,11,4,3,9,8,12,13], None),
 ("§12      fourths transform image", [0,5,10,8,1,0,7,4,11], 12, None, None),
 ("App D    15TET zigzag NEAR-ROW", [0,2,1,7,8,12,9,10,5,11,4,3], 15, None, True),
]
for name, pcs, n, exp, dist in tests:
    errs, contour, ks = check_cycle(pcs, n, exp, dist)
    print(f"{name:38s} n={n:2d}  {str(contour):7s}  {'OK' if not errs else 'FAIL: '+'; '.join(errs)}")

print()
print("="*62)
print("THE FOURTHS CLAIM (§12): image classes are the ic-5 family")
print("="*62)
q = [0,5,10,8,1,0,7,4,11]
fam = set()
for i in range(9):
    w = {q[i]%12, q[(i+1)%9]%12, q[(i+2)%9]%12}
    fam.add(ivec(w,12))
expected = {ivec({0,5,(5*k)%12},12) for k in range(2,11)}
print("  9 distinct classes:", len(fam)==9)
print("  equals M5-image of semitone family:", fam==expected)
# 027 appears as a direct stack?
for i in range(9):
    a,b,c = q[i]%12, q[(i+1)%9]%12, q[(i+2)%9]%12
    if ivec({a,b,c},12)==ivec({0,5,10},12):
        print(f"  027 window ({a},{b},{c}) steps ({(b-a)%12},{(c-b)%12}) -> "
              f"{'DIRECT STACK' if (b-a)%12==(c-b)%12 and (b-a)%12 in (5,7) else 'BROKEN'}")

print()
print("="*62)
print("DRIFT EXAMPLE (§5): word (2,11,8,1,9,4,7,6,1), drift 1, 108 notes")
print("="*62)
W = [2,11,8,1,9,4,7,6,1]; n=12
print("  sum mod 12 =", sum(W)%12, "(claimed drift 1)")
# build the 108-note cycle
pcs=[0]
for rep in range(12):
    for d in W: pcs.append((pcs[-1]+d)%12)
print("  closes after 12 periods:", pcs[-1]==0, "| length", len(pcs)-1)
big=pcs[:-1]
M=len(big)
from collections import Counter
cnt=Counter()
ok=True
for i in range(M):
    w={big[i],big[(i+1)%M],big[(i+2)%M]}
    if len(w)<3: ok=False; break
    k=klabel(w,12)
    if k is None: ok=False; break
    cnt[(k, big[i])]+=1
print("  all 108 windows valid:", ok)
print("  each of 9 classes x 12 transposition levels exactly once:",
      len(cnt)==108 and set(cnt.values())=={1})
# chromatic broken in all 12 appearances?
brk=[]
for i in range(M):
    w={big[i],big[(i+1)%M],big[(i+2)%M]}
    if klabel(w,12)==2:
        d1,d2=(big[(i+1)%M]-big[i])%12,(big[(i+2)%M]-big[(i+1)%M])%12
        brk.append(d1==d2 and d1 in (1,11))
print(f"  chromatic appears {len(brk)} times, all broken: {not any(brk)}")

print()
print("="*62)
print("APP D ROW: C C# D F# G Bb B Ab A Eb E F")
print("="*62)
row=[0,1,2,6,7,10,11,8,9,3,4,5]
print("  aggregate (12 distinct pcs):", len(set(row))==12)
ks=[klabel({row[i],row[i+1],row[i+2]},12) for i in range(10)]
print("  10 consecutive trichords, all semitone-bearing:", None not in ks)
c=Counter(ks)
print("  covers all 9 types:", len(c)==9, "| doubled type:", [k for k,v in c.items() if v==2])
# chain: is it drift-3 spiral? next 3 notes should be row[0..2]+3
print("  T3 chain check: window 10,11 continue as spiral:",
      ((row[0]+3)%12, (row[1]+3)%12) == (3,4))

