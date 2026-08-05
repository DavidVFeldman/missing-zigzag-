"""Cross-check the Eulerian-counting step by the BEST theorem
(matrix-tree determinant) instead of DFS circuit enumeration."""
from fractions import Fraction
from math import factorial
import itertools, sys

def edge(n,k,f):
    if f==0: return (1,(k-1)%n)
    if f==1: return (k%n,(n+1-k)%n)
    if f==2: return (n-1,k%n)
    if f==3: return ((k-1)%n,(n-k)%n)
    if f==4: return ((n-k)%n,1)
    return ((n+1-k)%n,n-1)

def det_int(M):
    """exact integer determinant via fraction-free Gaussian elimination"""
    M=[row[:] for row in M]; N=len(M); sign=1; prev=1
    for i in range(N-1):
        if M[i][i]==0:
            for r in range(i+1,N):
                if M[r][i]!=0: M[i],M[r]=M[r],M[i]; sign=-sign; break
            else: return 0
        for r in range(i+1,N):
            for c in range(i+1,N):
                M[r][c]=(M[r][c]*M[i][i]-M[r][i]*M[i][c])//prev
        prev=M[i][i]
    return sign*M[N-1][N-1]

def best_count(edges, n):
    """# Eulerian circuits with a fixed distinguished starting edge edges[0]"""
    verts=sorted({a for a,b in edges}|{b for a,b in edges})
    idx={v:i for i,v in enumerate(verts)}
    N=len(verts)
    outd=[0]*N; A=[[0]*N for _ in range(N)]
    for a,b in edges:
        outd[idx[a]]+=1; A[idx[a]][idx[b]]+=1
    # Laplacian for arborescences oriented TOWARD root: L = Dout - A
    L=[[ (outd[i] if i==j else 0) - A[i][j] for j in range(N)] for i in range(N)]
    w=idx[edges[0][0]]
    M=[[L[i][j] for j in range(N) if j!=w] for i in range(N) if i!=w]
    tw=det_int(M)
    prod=1
    for i in range(N): prod*=factorial(outd[i]-1)
    return tw*prod

def dfs_count(edges):
    m=len(edges)
    def rec(cur,used):
        if used==(1<<m)-1: return 1 if cur==edges[0][0] else 0
        t=0
        for i in range(1,m):
            if not (used>>i)&1 and edges[i][0]==cur: t+=rec(edges[i][1],used|(1<<i))
        return t
    return rec(edges[0][1],1)

def plans(n, zig=True):
    """enumerate valid plans: balanced, closed, connected, chromatic type"""
    m=n-3; res=[]
    forms=range(6)
    def rec(i,imb,s,cur):
        if i==m:
            if any(imb.values()) or s%n: return
            E=[edge(n,k+2,cur[k]) for k in range(m)]
            vs={a for a,b in E}|{b for a,b in E}
            adj={v:set() for v in vs}
            for a,b in E: adj[a].add(b); adj[b].add(a)
            st=[E[0][0]]; seen={E[0][0]}
            while st:
                v=st.pop()
                for u in adj[v]:
                    if u not in seen: seen.add(u); st.append(u)
            if seen!=vs: return
            res.append(E); return
        rng=(1,2,3,4) if (i==0 and zig) else ((0,5) if i==0 else forms)
        for f in rng:
            a,b=edge(n,i+2,f)
            im2=dict(imb)
            im2[a]=im2.get(a,0)+1; im2[b]=im2.get(b,0)-1
            im2={k:v for k,v in im2.items() if v!=0}
            rec(i+1,im2,(s+a)%n,cur+[f])
    rec(0,{},0,[])
    return res

for n in [9,15]:
    P=plans(n,zig=True)
    tot_dfs=sum(len(E)*dfs_count(E) for E in P)
    tot_best=sum(len(E)*best_count(E,n) for E in P)
    print(f"n={n}: {len(P)} zigzag plans | DFS total={tot_dfs} | BEST total={tot_best} | agree={tot_dfs==tot_best}")
