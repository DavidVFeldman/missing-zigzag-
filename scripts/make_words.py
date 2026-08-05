import sys
sys.setrecursionlimit(100000)
def edge(n,k,f):
    if f==0: return (1,(k-1)%n)
    if f==1: return (k%n,(n+1-k)%n)
    if f==2: return (n-1,k%n)
    if f==3: return ((k-1)%n,(n-k)%n)
    if f==4: return ((n-k)%n,1)
    return ((n+1-k)%n,n-1)
def circuit(n, forms):   # forms: dict k->f ; returns step word starting at class-2 edge
    m=n-3
    E=[edge(n,k,forms[k]) for k in range(2,n-1)]
    used=[False]*m; used[0]=True
    seq=[0]; cur=E[0][1]
    def cnt(cur,used):
        if all(used): return 1 if cur==E[0][0] else 0
        t=0
        for i in range(m):
            if not used[i] and E[i][0]==cur:
                used[i]=True; t+=cnt(E[i][1],used); used[i]=False
                if t: return t
        return t
    while len(seq)<m:
        for i in range(m):
            if not used[i] and E[i][0]==cur:
                used[i]=True
                if cnt(E[i][1],used): seq.append(i); cur=E[i][1]; break
                used[i]=False
    return [E[i][0] for i in seq], seq, E
def check(n, word):
    m=n-3
    assert len(word)==m
    from functools import lru_cache
    @lru_cache(None)
    def canonT(s):
        best=None
        for t in range(n):
            tup=tuple(sorted((x+t)%n for x in s))
            if best is None or tup<best: best=tup
        return best
    valid={canonT(frozenset((0,1,k))) for k in range(2,n-1)}
    pcs=[0]
    for d in word: pcs.append((pcs[-1]+d)%n)
    if pcs[-1]!=0: return "DRIFT!=0"
    pcs=pcs[:-1]
    seen=set()
    for i in range(m):
        s=frozenset((pcs[i],pcs[(i+1)%m],pcs[(i+2)%m]))
        if len(s)<3: return f"degenerate window {i}"
        c=canonT(s)
        if c not in valid or c in seen: return f"bad/dup class at {i}"
        seen.add(c)
    d0,d1=word[0],word[1]
    zig = not (d0==d1 and d0 in (1,n-1))
    return "OK zigzag" if zig else "OK scalar"

F15={k:f for k,f in zip(range(2,14),[1,4,1,0,2,3,5,4,1,0,2,3])}
F18={k:f for k,f in zip(range(2,17),[1,0,4,1,0,4,1,2,3,4,1,0,4,1,0])}

w15,seq15,E15=circuit(15,F15)
cap15=seq15.index(6)   # class 8 = index 6 (k-2), form VI
print("base15 word (mod 15):",w15,"| cap index:",cap15)
w18,seq18,E18=circuit(18,F18)
i9=seq18.index(7); i10=seq18.index(8)   # classes 9,10 -> indices 7,8
print("base18 word (mod 18):",w18,"| cap steps at:",i9,i10)

def sg(x,n): return x%n
def word_odd(t):
    n=15+6*t; L0=7
    blocks=[]
    for s in range(t):
        L=L0+3*s
        blocks += [sg(-L,n), sg(-1,n), sg(L+2,n), 1, sg(-(L+1),n), sg(L+2,n)]
    blocks += [sg(-(L0+3*t),n)]
    # re-express base word entries in mod-n via signed reps of mod-15
    def lift(v):
        vs = v if v<=7 else v-15
        return sg(vs,n)
    w=[lift(x) for x in w15]
    return n, w[:cap15]+blocks+w[cap15+1:]
def word_even(t):
    n=18+6*t; L0=9
    assert i10==i9+1
    tail=[]
    for s in range(t-1,-1,-1):
        L=L0+3*s
        tail += [sg(L+2,n), sg(-1,n), sg(-L,n), 1, sg(L+1,n), sg(-L,n)]
    mid=[sg(-1,n), sg(L0+3*t,n)]+tail
    def lift(v):
        vs = v if v<=9 else v-18
        return sg(vs,n)
    w=[lift(x) for x in w18]
    return n, w[:i9]+mid+w[i9+2:]

print("\n=== ODD chain: formula verification ===")
for t in range(0,6):
    n,w=word_odd(t)
    print(f"  n={n}: {check(n,w)}")
print("=== EVEN chain: formula verification ===")
for t in range(0,6):
    n,w=word_even(t)
    print(f"  n={n}: {check(n,w)}")
print("\nexample n=27 word:", word_odd(2)[1])

if __name__=="__main__" and "--classes" in sys.argv:
    def kof(a,b,c,n):
        s=frozenset((a,b,c))
        for x in s:
            if (x+1)%n in s:
                z=[y for y in s if y not in (x,(x+1)%n)][0]
                k=(z-x)%n
                if k==n-1: k=2
                if 2<=k<=n-2: return k
    for t in range(0,4):
        for name,(n,w) in [("odd",word_odd(t)),("even",word_even(t))]:
            m=n-3; pcs=[0]
            for d in w: pcs.append((pcs[-1]+d)%n)
            pcs=pcs[:-1]
            ks=[kof(pcs[i],pcs[(i+1)%m],pcs[(i+2)%m],n) for i in range(m)]
            print(f"{name} t={t} n={n}: window classes = {ks}")
