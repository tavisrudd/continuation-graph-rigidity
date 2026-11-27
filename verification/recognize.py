"""Certified frame recognition for the field models provided by frame_model.

The mathematical algorithm works over any supplied finite field. This reference
implementation defaults to prime fields and explicit orders 8,9,16,25.
The optional field object supplies q, sub(x,y), div(x,y), power(x,k), with
field elements encoded by range(q) and zero/one encoded by 0/1. Its finite-field
axioms are a supplied premise, as in the mathematical theorem.
Trace recovery follows thm:recognition: the local test of lem:local-trace for
q>=13 and four-clique seeds (lem:seeds) for q=9,11.
"""
from math import isqrt
from frame_model import Field,adjacency,fixed_cliques

def members(mask):
    while mask:
        bit=mask&-mask;mask^=bit;yield bit.bit_length()-1

def closed_common(adj,seed):
    common=(1<<len(adj))-1
    for i in seed:common&=adj[i]
    return common|sum(1<<i for i in seed)

def is_clique(adj,mask):
    return all((adj[i]|(1<<i))&mask==mask for i in members(mask))

def split(adj,v,q):
    """Local trace test (lem:local-trace) at v, for q>=13: the four traces through v, or None."""
    nb=adj[v];rel={u:0 for u in members(nb)}
    for u in rel:
        for w in members(adj[u]&nb):
            if w>u and (adj[u]&adj[w]&nb).bit_count()>=7:rel[u]|=1<<w;rel[w]|=1<<u
    comps=[];left=nb
    while left:
        comp=frontier=left&-left
        while frontier:
            new=0
            for x in members(frontier):new|=rel[x]
            frontier=new&~comp;comp|=frontier
        left&=~comp;comps.append(comp)
    if len(comps)!=4 or any(c.bit_count()!=q-4 or not is_clique(adj,c) for c in comps):return None
    return sorted(c|(1<<v) for c in comps)

def recover_traces(adj,q):
    """Traces meeting two traces through vertex 0 (q>=13), or all traces by four-clique seeds."""
    if q>=13:
        first=split(adj,0,q)
        if first is None:return None
        traces=set(first)
        for v in members(first[0]|first[1]):
            local=split(adj,v,q)
            if local is None:return None
            traces.update(local)
        return sorted(traces)
    traces=set()
    for seed in fixed_cliques(adj,4):
        b=closed_common(adj,seed)
        if b.bit_count()==q-3 and is_clique(adj,b):traces.add(b)
    return sorted(traces)

def verify_transport(adj,q,coordinates, *, field=None):
    f=Field(q) if field is None else field
    if f.q!=q:return False
    expected={(x,y) for x in range(2,q) for y in range(2,q) if x!=y}
    if len(coordinates)!=len(adj) or len(coordinates)!=len(expected) or set(coordinates)!=expected:return False
    if any(a<0 or a>>len(adj) for a in adj):return False
    words=[(x,y,f.div(x,y),f.div(f.sub(x,1),f.sub(y,1))) for x,y in coordinates]
    for i in range(len(adj)):
        if adj[i]>>i&1:return False
        for j in range(i):
            same=any(a==b for a,b in zip(words[i],words[j]))
            if bool(adj[i]>>j&1)!=same or bool(adj[j]>>i&1)!=same:return False
    return True

def recognize(adj, *, field=None):
    """Return (q, coordinate transport) or None. Does not consult source labels."""
    n=len(adj);root=isqrt(1+4*n)
    if root*root!=1+4*n or (5+root)%2:return None
    q=(5+root)//2
    if q<9:return None
    try:f=Field(q) if field is None else field
    except ValueError:return None
    if f.q!=q:return None
    if any(a>>n or a>>i&1 or a.bit_count()!=4*(q-4) for i,a in enumerate(adj)):return None
    if any(bool(adj[i]>>j&1)!=bool(adj[j]>>i&1) for i in range(n) for j in range(i)):return None
    traces=recover_traces(adj,q)
    if traces is None or any(b.bit_count()!=q-3 for b in traces):return None
    disjoint=[sum(1<<j for j,b in enumerate(traces) if i!=j and not a&b) for i,a in enumerate(traces)]
    classes=set()
    for seed in fixed_cliques(disjoint,2):
        c=closed_common(disjoint,seed)
        if c.bit_count()>=q-3 and is_clique(disjoint,c):classes.add(c)
    if len(classes)!=4 or sum(c.bit_count() for c in classes)!=len(traces) or sum(classes)!=(1<<len(traces))-1:return None
    full=(1<<n)-1;completed=[]
    for c in classes:
        part=[traces[j] for j in members(c)]
        if len(part)==q-3:part.append(full&~sum(part))
        if len(part)!=q-2 or sum(part)!=full:return None
        completed.append(part)
    # Index classes over the sorted list of all traces, as for full seed recovery.
    traces=sorted(b for part in completed for b in part)
    if len(set(traces))!=4*(q-2):return None
    index={b:j for j,b in enumerate(traces)}
    classes=sorted(sum(1<<index[b] for b in part) for part in completed)
    parts=[[traces[j] for j in members(c)] for c in classes]
    ids=[]
    for part in parts:
        assignment=[None]*n
        for j,b in enumerate(part):
            for v in members(b):
                if assignment[v] is not None:return None
                assignment[v]=j
        if None in assignment:return None
        ids.append(assignment)
    m=q-2;identity=m
    def missing(first,second):
        ans=[]
        for a in range(m):
            seen={second[v] for v in range(n) if first[v]==a}
            absent=set(range(m))-seen
            if len(absent)!=1:return None
            ans.append(absent.pop())
        return ans if len(set(ans))==m else None
    row_missing_col=missing(ids[0],ids[1]);row_missing_symbol=missing(ids[0],ids[2])
    if row_missing_col is None or row_missing_symbol is None:return None
    col_to_row={c:r for r,c in enumerate(row_missing_col)}
    symbol_to_row={s:r for r,s in enumerate(row_missing_symbol)}
    div=[[None]*(m+1) for _ in range(m+1)]
    for v in range(n):
        a=ids[0][v];b=col_to_row[ids[1][v]];c=symbol_to_row[ids[2][v]]
        if a==b or div[a][b] is not None:return None
        div[a][b]=c
    for a in range(m):div[a][a]=identity;div[a][identity]=a
    div[identity][identity]=identity
    for b in range(m):
        absent=set(range(m))-{div[a][b] for a in range(m) if a!=b}
        if len(absent)!=1:return None
        div[identity][b]=absent.pop()
    if any(None in row for row in div):return None
    inv=div[identity]
    powers=None;order=q-1
    for t in range(m):
        trial=[identity]
        for _ in range(order-1):trial.append(div[trial[-1]][inv[t]])
        if len(set(trial))!=order or div[trial[-1]][inv[t]]!=identity:continue
        if all(div[trial[i]][trial[j]]==trial[(i-j)%order] for i in range(order) for j in range(order)):
            powers=trial;break
    if powers is None:return None
    for w in range(2,q):
        wp=[f.power(w,i) for i in range(order)]
        if len(set(wp))!=order:continue
        labels=dict(zip(powers,wp))
        coordinates=[(labels[ids[0][v]],labels[col_to_row[ids[1][v]]]) for v in range(n)]
        values={};valid=True
        for v,(x,y) in enumerate(coordinates):
            z=f.div(f.sub(x,1),f.sub(y,1));c=ids[3][v]
            if c in values and values[c]!=z:valid=False;break
            values[c]=z
        if valid and len(set(values.values()))==m:
            # For a frame graph every image passing the fourth-partition
            # test is an isomorphism, so one pairwise check decides.
            return (q,coordinates) if verify_transport(adj,q,coordinates,field=f) else None
    return None
