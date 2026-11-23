"""Exact multioutput synthesis on subcubes, with gate-elimination lower bounds."""
import argparse
import itertools
import json
from pathlib import Path
from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Solver

MATCHINGS = [[(i, 3 + (i+k)%3) for i in range(3)] for k in range(3)]
def tables(cube):
    free = [i for i, bit in enumerate(cube) if bit=='*']
    rows = range(1<<len(free))
    inputs = [sum(((row>>i)&1)<<row for row in rows) for i in range(len(free))]
    full = (1<<len(rows))-1
    xs=[inputs[free.index(i)] if i in free else (full if bit=='1' else 0) for i,bit in enumerate(cube)]
    outputs=[(xs[a]&xs[b])|(xs[c]&xs[d])|(xs[e]&xs[f]) for (a,b),(c,d),(e,f) in MATCHINGS]
    targets=list(dict.fromkeys(x for x in outputs if x not in inputs+[0,full]))
    return inputs,targets

class Instance:
    def __init__(self,cube,size,last=None,first_free=False,allow_dead=False,support_prune=True):
        ins,outs=tables(cube)
        self.cube=cube
        self.size=size
        self.n=n=len(ins)
        self.inputs=ins
        self.targets=outs
        self.pool=IDPool()
        self.cnf=CNF()
        self.top=[]; self.low=[]; self.op=[]
        self.sel=[]
        self.values=[]
        self.full=(1<<(1<<n))-1
        for j in range(n,n+size):
            top=self.choices(('top',j),range(j)); low=self.choices(('low',j),range(j))
            ops=self.choices(('op',j),['and','or','not'])
            self.op.append(ops);self.top.append(top);self.low.append(low)
            for a in range(j):
                self.add(-top[a],-ops['not'],low[a])
                self.add(-top[a],ops['not'],*[low[b] for b in range(a)])
            if j>n+int(first_free):
                pt=self.top[-2]; pl=self.low[-2]
                for a in range(j):
                    self.add(-top[a],*[pt[b] for b in pt if b<=a])
                    if a in pt:
                        for b in range(a+1):
                            self.add(-top[a],-pt[a],-low[b],*[pl[c] for c in range(b+1)])
        for i,want in enumerate(outs):
            dep=sum(any(((want>>r)^(want>>(r^(1<<b))))&1 for r in range(1<<n)) for b in range(n))
            self.sel.append(self.choices(('out',i),range(n+(max(0,dep-2) if support_prune else 0),n+size)))
        for j in range(n,n+size):
            outs_here=[d[j] for d in self.sel if j in d]
            for a,b in itertools.combinations(outs_here,2):self.add(-a,-b)
            uses=[port[j] for i in range(j-n+1,size) for port in (self.top[i],self.low[i])]
            if not allow_dead:self.add(*outs_here,*uses)
        if last is not None:
            self.add(self.sel[last].get(n+size-1,False))
        for row in range(1<<n):
            vals=[bool((table>>row)&1) for table in ins]
            for i in range(size):
                a=self.var('a',i,row);b=self.var('b',i,row);y=self.var('y',i,row)
                self.select_value(self.top[i],vals,a)
                self.select_value(self.low[i],vals,b)
                self.gate_truth(self.op[i],a,b,y)
                vals.append(y)
            self.values.append(vals)
            for i,sel in enumerate(self.sel):
                for j,s in sel.items():self.add(-s,vals[j] if (outs[i]>>row)&1 else -vals[j])
    def var(self,*key):return self.pool.id(key)
    def add(self,*lits):
        if any(x is True for x in lits):return
        self.cnf.append([x for x in lits if x is not False])
    def choices(self,key,domain):
        d={v:self.var(*key,v) for v in domain}
        self.add(*d.values())
        for a,b in itertools.combinations(d.values(),2):self.add(-a,-b)
        return d
    def select_value(self,port,vals,out):
        for j,s in port.items():
            v=vals[j]
            if type(v) is bool:self.add(-s,out if v else -out)
            else:
                self.add(-s,-v,out);self.add(-s,v,-out)
    def gate_truth(self,op,a,b,y):
        for name,clauses in [('and',[[-a,-b,y],[a,-y],[b,-y]]),('or',[[a,b,-y],[-a,y],[-b,y]]),('not',[[a,y],[-a,-y]])]:
            for c in clauses:self.add(-op[name],*c)
    def bound(self,lits,k,atleast):
        if (atleast and k<=0) or (not atleast and k>=len(lits)):return
        if (atleast and k>len(lits)) or (not atleast and k<0):self.add();return
        f=CardEnc.atleast if atleast else CardEnc.atmost
        self.cnf.extend(f(lits,bound=k,vpool=self.pool,encoding=EncType.seqcounter).clauses)
    def restrict(self,subcube,minimum):
        # 0, 1 are constant marks. Unknown wires carry neither mark.
        free=[i for i,x in enumerate(self.cube) if x=='*']
        zeros=[subcube[i]=='0' for i in free];ones=[subcube[i]=='1' for i in free]
        kept=[]
        for i in range(self.size):
            z=[];o=[]
            for p,port in enumerate([self.top[i],self.low[i]]):
                a=self.var(subcube,'z',i,p); b=self.var(subcube,'o',i,p)
                self.select_value(port,zeros,a);self.select_value(port,ones,b);z.append(a);o.append(b)
            op=self.op[i]; cz=self.var(subcube,'cz',i);co=self.var(subcube,'co',i)
            for t in ['and','or','not']:
                # Forced constants suffice for the maximum number of surviving gates.
                # The bound is sound even if other simplifications are missed.
                if t=='not':
                    self.add(-op[t],-z[0],co);self.add(-op[t],-o[0],cz)
                else:
                    some,all_,v,w=(z,o,cz,co) if t=='and' else (o,z,co,cz)
                    for mark in some:self.add(-op[t],-mark,v)
                    self.add(-op[t],-all_[0],-all_[1],w)
            k=self.var(subcube,'kept',i);kept.append(k)
            for mark in z+o:self.add(-k,-mark)
            zeros.append(cz);ones.append(co)
        self.bound(kept,minimum,True)
    def solve(self,name,proof=None):
        with Solver(name=name,bootstrap_with=self.cnf.clauses,with_proof=bool(proof)) as s:
            if not s.solve():
                if proof:
                    Path(proof).write_text('\n'.join(s.get_proof())+'\n')
                    self.cnf.to_file(proof+'.cnf')
                return None
            model={v for v in s.get_model() if v>0}
            chosen=lambda d: next(v for v,p in d.items() if p in model)
            gates=[(chosen(op),chosen(top),chosen(low)) for op,top,low in zip(self.op,self.top,self.low)]
            outs=[chosen(d) for d in self.sel]
            vals=self.inputs.copy()
            for op,a,b in gates:
                vals.append(vals[a]&vals[b] if op=='and' else vals[a]|vals[b] if op=='or' else self.full^vals[a])
            assert [vals[j] for j in outs]==self.targets
            return gates,outs
def lower_tables(cube):
    ins,outs=tables(cube)
    if not outs:return 0
    def deps(v):return sum(any(((v>>r)^(v>>(r^(1<<b))))&1 for r in range(1<<len(ins))) for b in range(len(ins)))
    return max(len(outs),max(deps(t)-1 for t in outs))
def subcubes(cube,free):
    for spots in itertools.combinations([i for i,b in enumerate(cube) if b=='*'],cube.count('*')-free):
        for bits in itertools.product('01',repeat=len(spots)):
            xs=list(cube)
            for i,v in zip(spots,bits):xs[i]=v
            yield ''.join(xs)
def signature(cube):
    # Simultaneous affine index changes and side exchange preserve all three outputs up to relabeling.
    shapes=[]
    for a,b,s,swap in itertools.product(range(3),range(3),[1,2],[False,True]):
        u=cube[3:] if swap else cube[:3];v=cube[:3] if swap else cube[3:]
        shapes.append(''.join(u[(s*i+a)%3] for i in range(3))+''.join(v[(s*i+b)%3] for i in range(3)))
    return min(shapes)
def bounds_table(path):
    cache={}
    for free in [2,3,4]:
        for sub in sorted({signature(c) for c in subcubes('******',free)}):
            ins,outs=tables(sub); lower=lower_tables(sub)
            if outs:
                for size in range(lower,16):
                    p=Instance(sub,size)
                    witness=p.solve('cadical300')
                    if witness is not None:break
                else:raise ValueError(sub)
                lower=size
            cache[sub]=lower
            print(sub,lower,flush=True)
            path.write_text(json.dumps(cache,indent=2))


def add_sensitivity(p,reads):
    for v in range(p.n):
        mask=1<<v
        for row in range(1<<p.n):
            if row&mask:continue
            mate=row|mask
            if all(((o>>row)^(o>>mate))&1==0 for o in p.targets):continue
            passes=[]
            for i in range(p.size):
                k=p.var('sens',v,row,i);passes.append(k)
                p.add(-k,reads[i,v])
                a=p.values[row][p.n+i];b=p.values[mate][p.n+i]
                p.add(-k,a,b);p.add(-k,-a,-b)
            p.add(*passes)



def main_case(kind,cache):
    p=Instance('******',14,None,first_free=True)
    read={}
    for i in range(14):
        for v in range(6+i):
            r=p.var('reads',i,v)
            a=p.top[i][v];b=p.low[i][v]
            p.add(-a,r);p.add(-b,r);p.add(-r,a,b)
            read[i,v]=r
    for v in range(6):
        uses=[read[i,v] for i in range(14)]
        p.bound(uses,2,False)
        p.add(*uses)
        for i in range(14):
            for j in range(14):
                if i!=j:p.add(-read[i,v],-read[j,v],p.op[i]['and'])
            # For a first binary gate on two inputs, the value of the other input
            # can disable it while at least one target still depends on v.
            for w in range(6):
                if w!=v:
                    p.add(-read[i,v],-read[i,w],*[read[j,v] for j in range(14) if j!=i])
    for j in range(14):
        for i in range(j):
            # An AND/OR with both a wire and its direct AND/OR child is an alias.
            for v in range(6+i):
                p.add(-read[j,6+i],-read[j,v],-read[i,v],p.op[i]['not'])
    for i in range(14):
        for j in range(i):
            for v in range(6):
                for a in range(6):
                    for b in range(6):
                        if v!=a and v!=b:
                            p.add(-read[i,v],-read[i,a],-read[j,v],-read[j,b])
    # Select the indicated gate first, then sort the remaining gates.
    
    if kind=='not':
        p.add(p.op[0]['not']);p.add(p.top[0][0])
        for i in range(p.size):
            for a,b in itertools.combinations(range(6),2):
                p.add(-read[i,a],-read[i,b])
    else:
        a,b={'same':(0,1),'cross':(0,3)}[kind]
        p.add(p.op[0]['and']);p.add(p.low[0][a]);p.add(p.top[0][b])
    
    add_sensitivity(p,read)
    for sub,m in [('0*****',9),('1*****',12)]:
        for v in range(6):
            s=list('******');s[v]=sub[0];p.restrict(''.join(s),m)
    
    for sub in subcubes('******',4):
        p.restrict(sub,cache[signature(sub)])
    return p
