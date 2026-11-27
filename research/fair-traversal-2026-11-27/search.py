import json
import itertools
import math
import time
from pathlib import Path
import numpy as np
from scipy.optimize import milp, linprog, Bounds, LinearConstraint
from scipy.sparse import coo_array
from sympy import Matrix, Rational

ROOT = Path(__file__).resolve().parent


def gp(q, k):
    n = 2*q
    edges = {tuple(sorted((i, (i+1)%q))) for i in range(q)}
    edges |= {tuple(sorted((q+i, q+(i+k)%q))) for i in range(q)}
    edges |= {(i, q+i) for i in range(q)}
    rot = [(i+1)%q for i in range(q)] + [q+(i+1)%q for i in range(q)]
    swap = [q+(k*i)%q for i in range(q)] + [(k*i)%q for i in range(q)]
    assert k*k%q in (1, q-1)
    return n, sorted(edges), [rot, swap]


def edge_orbits(n, edges, generators):
    pos = {e:i for i,e in enumerate(edges)}
    parent = list(range(len(edges)))
    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a
    def union(a,b):
        a,b = find(a),find(b)
        if a != b: parent[b] = a
    for g in generators:
        assert sorted(g) == list(range(n))
        for i,(u,v) in enumerate(edges):
            union(i,pos[tuple(sorted((g[u],g[v])))])
    roots = sorted({find(i) for i in range(len(edges))})
    classes = {r:i for i,r in enumerate(roots)}
    return np.array([classes[find(i)] for i in range(len(edges))],dtype=int)


def johnson(v,k,intersections):
    subsets = list(itertools.combinations(range(v),k))
    sets = list(map(set,subsets))
    n = len(subsets)
    edges = [(i,j) for i in range(n) for j in range(i+1,n)
             if len(sets[i]&sets[j]) in intersections]
    orbit = np.array([sorted(intersections).index(len(sets[i]&sets[j])) for i,j in edges])
    return n,edges,orbit


class Oracle:
    def __init__(self,n,edges,orbit):
        self.n,self.edges,self.orbit=n,edges,orbit
        self.t=int(max(orbit))+1
        self.m=len(edges)
        ex=edges+[(v,n) for v in range(n)]
        self.ex=ex
        self.M=len(ex)
        M=self.M
        rows=[];cols=[];vals=[];lo=[];hi=[]
        def row(coeff,l,u):
            r=len(lo)
            for c,a in coeff.items():
                rows.append(r);cols.append(c);vals.append(a)
            lo.append(l);hi.append(u)
        for v in range(n+1):
            row({j:1 for j,e in enumerate(ex) if v in e},2,2)
        for v in range(n):
            co={}
            for j,(a,b) in enumerate(ex):
                if v==a:
                    co[M+2*j]=-1;co[M+2*j+1]=1
                elif v==b:
                    co[M+2*j]=1;co[M+2*j+1]=-1
            row(co,1,1)
        for j in range(M):
            row({M+2*j:1,j:-n},-np.inf,0)
            row({M+2*j+1:1,j:-n},-np.inf,0)
        A=coo_array((np.array(vals,dtype=float),(np.array(rows,dtype=np.int32),np.array(cols,dtype=np.int32))),shape=(len(lo),3*M)).tocsc()
        self.constraint=LinearConstraint(A,np.array(lo),np.array(hi))
        self.bounds=Bounds(np.zeros(3*M),np.r_[np.ones(M),np.full(2*M,n)])
        self.integrality=np.r_[np.ones(M),np.zeros(2*M)]
        self.q=(n-1)*np.bincount(orbit,minlength=self.t)/self.m

    def solve(self,w,limit=4):
        objective=np.zeros(3*self.M)
        objective[:self.m]=np.array(w)[self.orbit]
        res=milp(objective,integrality=self.integrality,bounds=self.bounds,
                 constraints=self.constraint,options={'time_limit':limit,'mip_rel_gap':0})
        if res.x is None:
            return {'status':int(res.status),'message':res.message}
        chosen=[i for i in range(self.m) if res.x[i]>.5]
        adj=[[] for _ in range(self.n)]
        for i in chosen:
            u,v=self.edges[i];adj[u].append(v);adj[v].append(u)
        ends=[v for v in range(self.n) if len(adj[v])==1]
        if len(chosen)!=self.n-1 or len(ends)!=2 or any(len(a) not in (1,2) for a in adj):
            raise AssertionError('invalid integer edge solution')
        path=[ends[0]]
        while len(path)<self.n:
            nx=[v for v in adj[path[-1]] if len(path)==1 or v!=path[-2]]
            assert len(nx)==1 and nx[0] not in path
            path.append(nx[0])
        assert len(set(path))==self.n
        counts=np.bincount(self.orbit[chosen],minlength=self.t)
        return {'status':int(res.status),'counts':counts.tolist(),'path':path,
                'objective':float(np.dot(w,counts)),
                'dual_bound':float(res.mip_dual_bound) if hasattr(res,'mip_dual_bound') else None}

    def exact_support(self,support):
        """Validate paths/counts, then solve their balancing weights over Q."""
        pos={e:i for i,e in enumerate(self.edges)}
        counts=[]
        for _,path,claimed in support:
            if sorted(path)!=list(range(self.n)):
                return {'verified':False,'reason':'not_a_vertex_permutation'}
            try:
                edge_ids=[pos[tuple(sorted(e))] for e in zip(path,path[1:])]
            except KeyError:
                return {'verified':False,'reason':'nonedge_in_path'}
            actual=np.bincount(self.orbit[edge_ids],minlength=self.t).tolist()
            if actual!=claimed:
                return {'verified':False,'reason':'count_mismatch'}
            counts.append(actual)
        sizes=np.bincount(self.orbit,minlength=self.t).tolist()
        target=[Rational((self.n-1)*s,self.m) for s in sizes]
        A=Matrix(counts).T.col_join(Matrix([[1]*len(counts)]))
        b=Matrix(target+[Rational(1)])
        try:
            weights,parameters=A.gauss_jordan_solve(b)
        except ValueError:
            return {'verified':False,'reason':'no_exact_solution'}
        if len(parameters):
            return {'verified':False,'reason':'dependent_support'}
        if any(w<0 for w in weights) or A*weights!=b:
            return {'verified':False,'reason':'negative_or_invalid_weights'}
        return {'verified':True,'weights':[str(w) for w in weights],
                'target':[str(x) for x in target],'orbit_sizes':sizes}

    def column_generation(self,limit=4,rounds=35):
        first=self.solve(np.zeros(self.t),limit)
        if 'counts' not in first:return {'result':'no_path_found','oracle':first}
        cols=[first['counts']];paths=[first['path']]
        for step in range(rounds):
            C=np.array(cols).T
            primal=linprog(np.zeros(len(cols)),A_eq=np.vstack([C,np.ones(len(cols))]),
                           b_eq=np.r_[self.q,1],bounds=(0,None),method='highs')
            if primal.success:
                support=[(float(p),paths[i],cols[i]) for i,p in enumerate(primal.x) if p>1e-8]
                exact=self.exact_support(support)
                return {'result':'feasible_exact' if exact['verified'] else 'feasible_numerically',
                        'iterations':step,'target':self.q.tolist(),'support':support,'exact':exact}
            D=C.T-self.q
            dual=linprog(np.r_[np.zeros(self.t),-1.0],
                         A_ub=np.c_[-D,np.ones(len(cols))],b_ub=np.zeros(len(cols)),
                         bounds=[(-1,1)]*self.t+[(None,None)],method='highs')
            assert dual.success
            w=dual.x[:-1]
            p=self.solve(w,limit)
            if 'counts' not in p:
                return {'result':'oracle_timeout_without_path','iterations':step,'oracle':p}
            gap=float(np.dot(w,np.array(p['counts'])-self.q))
            if gap>1e-7 and p['status']==0:
                return {'result':'POTENTIAL_OBSTRUCTION','iterations':step,'weight':w.tolist(),
                        'target':self.q.tolist(),'gap':gap,'oracle':p}
            if p['counts'] in cols:
                return {'result':'oracle_stalled','iterations':step,'gap':gap,'oracle':p,'weight':w.tolist()}
            cols.append(p['counts']);paths.append(p['path'])
        return {'result':'round_limit','iterations':rounds}


def emit(data):
    text=json.dumps(data)
    print(text,flush=True)
    with (ROOT/'results.jsonl').open('a') as f:f.write(text+'\n')


def main():
    tests=[(5,2),(8,3),(10,3),(12,5),(13,5),(16,7),(17,4),(20,9),(24,5),(24,7),(24,11),(25,7),(26,5),(28,13),(29,12),(30,11),(30,13),(32,15)]
    for q,k in tests:
        if k*k%q not in (1,q-1):continue
        n,edges,gens=gp(q,k)
        orbit=np.array([int(v==u+q) for u,v in edges])
        start=time.time()
        o=Oracle(n,edges,orbit)
        p=o.solve([0,-1],limit=3)
        target=(2*q-1)/3
        result='feasible_explicitly' if 'counts' in p and p['counts'][1]>=target else 'undetermined'
        if p.get('status')==0 and p.get('counts',[0,0])[1]<target:result='POTENTIAL_OBSTRUCTION'
        emit({'family':'GP','q':q,'k':k,'vertices':n,'result':result,'spoke_target':target,'oracle':p,'seconds':round(time.time()-start,2)})
    complements=[(8,3),(10,3),(12,5),(13,5),(16,7)]
    for q,k in complements:
        n,E,gens=gp(q,k);old=set(E)
        edges=[(a,b) for a in range(n) for b in range(a+1,n) if (a,b) not in old]
        orbit=edge_orbits(n,edges,gens)
        tag=f'complement_GP_{q}_{k}'
        (ROOT/(tag+'.json')).write_text(json.dumps({'n':n,'edges':edges,'orbit':orbit.tolist(),'generators':gens}))
        start=time.time();res=Oracle(n,edges,orbit).column_generation(limit=3,rounds=35)
        emit({'family':'complement_GP','q':q,'k':k,'vertices':n,'orbits':int(max(orbit)+1),'seconds':round(time.time()-start,2),**res})
    for v,k,inter in [(7,3,{0,1}),(7,3,{0,2}),(7,3,{1,2}),(8,3,{0,1}),(8,3,{0,2}),(8,4,{0,1,2}),(8,4,{0,1,3}),(8,4,{0,2,3})]:
        n,edges,orbit=johnson(v,k,inter)
        tag=f'Johnson_{v}_{k}_'+''.join(map(str,sorted(inter)))
        (ROOT/(tag+'.json')).write_text(json.dumps({'n':n,'edges':edges,'orbit':orbit.tolist(),'subsets':list(itertools.combinations(range(v),k))}))
        start=time.time();res=Oracle(n,edges,orbit).column_generation(limit=3,rounds=25)
        emit({'family':'Johnson_union','v':v,'k':k,'intersections':sorted(inter),'vertices':n,'seconds':round(time.time()-start,2),**res})


if __name__=='__main__':main()
