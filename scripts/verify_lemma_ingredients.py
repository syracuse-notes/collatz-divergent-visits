"""L5: a single non-periodic T-orbit has few values in [Y,2Y).
Checks (finite; the proof is in the note):
 (1) Terras bijection: x mod 2^k -> first k parities is a bijection (k<=14).
 (2) exact probabilities over all 2^k parity vectors vs the Chernoff / Doob bounds used.
 (3) the chain/up-crossing accounting on real orbits: every visit is either in Stay(Y),
     or among the last k visits of its chain; every chain boundary has an up-crossing z in
     [Y',1.5Y') that lies in Stay'(Y') or Climb(Y').
 (4) optimise gamma."""
import math, random
from fractions import Fraction as F
def T(x): return x//2 if x%2==0 else (3*x+1)//2
# (1)
for k in range(1,15):
    seen=set()
    for r in range(2**k):
        x=r+2**k*7; v=[]
        for _ in range(k): v.append(x&1); x=T(x)
        seen.add(tuple(v))
    assert len(seen)==2**k
print('(1) Terras bijection ok for k<=14')
# (2) exact distribution of S_k via DP on (#odd) counts
L3,L2=math.log(1.5),math.log(2)
def M(t): return (1.5**t+2**-t)/2
for k in [10,20,30]:
    # DP over paths tracking min and max is expensive; S_k tail exact, min/max via DP over j with barrier
    b=2.0
    # Pr[S_k >= -b]
    p=sum(math.comb(k,j) for j in range(k+1) if j*L3-(k-j)*L2>=-b)/2**k
    ch=min(math.exp(t*b)*M(t)**k for t in [i/100 for i in range(1,100)])
    # Pr[max_{s<=k} S_s >= b] exact via DP on j (odd count) at each s with absorbing
    dist={0:1.0}; hit=0.0
    for s in range(1,k+1):
        nd={}
        for j,pr in dist.items():
            for dj in (0,1):
                jj=j+dj; val=jj*L3-(s-jj)*L2
                if val>=b: hit+=pr/2
                else: nd[jj]=nd.get(jj,0)+pr/2
        dist=nd
    print('(2) k=%d  Pr[S_k>=-2]=%.4g <= Chernoff %.4g ; Pr[max S>=2]=%.4g <= Doob e^-2=%.4g'%(k,p,ch,hit,math.exp(-b)))
    assert p<=ch+1e-12 and hit<=math.exp(-b)+1e-12
# (3) accounting on real orbits
def check_orbit(n,e,eps):
    Y=2**e; Yp=Y**(1-eps); k=int(math.log2(Y)); kp=int(math.log2(0.5*Yp))
    orb=[n]
    while orb[-1]!=1: orb.append(T(orb[-1]))
    orb=orb[:-1]  # pre-periodic part: all values distinct
    assert len(set(orb))==len(orb)
    def stay(x,lo,steps):
        for _ in range(steps):
            x=T(x)
            if x<lo: return False
        return True
    def climb(z):
        x=z
        for _ in range(kp):
            x=T(x)
            if x>=Y: return True
            if x<Yp: return False
        return False
    visits=[t for t,x in enumerate(orb) if Y<=x<2*Y]
    if len(visits)<2: return None
    chains=[[visits[0]]]
    zs=[]
    for a,b in zip(visits,visits[1:]):
        dips=[u for u in range(a+1,b) if orb[u]<Yp]
        if dips:
            u=dips[-1]; z=orb[u+1]
            assert Yp<=z<1.5*Yp
            assert stay(z,Yp,kp) or climb(z), ('z not rare',n,z)
            zs.append(z); chains.append([b])
        else: chains[-1].append(b)
    nonstay=0
    for ch in chains:
        for t in ch:
            if ch[-1]-t>=k:
                assert stay(orb[t],Yp,k)
            elif not stay(orb[t],Yp,k): nonstay+=1
    assert nonstay<=k*len(chains)
    return len(visits),len(chains),len(zs)
random.seed(1); tot=[0,0,0]; cases=0
for _ in range(3000):
    n=random.randrange(10**11,10**12)|1
    for e in [20,24,28,32]:
        r=check_orbit(n,e,0.2)
        if r: cases+=1; tot=[a+b for a,b in zip(tot,r)]
print('(3) accounting ok on %d (orbit,block) cases with >=2 visits; visits=%d chains=%d upcrossings=%d'%(cases,*tot))
# (4) gamma
best=(0,)
for i in range(1,200):
    th=i/200; d=-math.log2(M(th))
    for j in range(1,200):
        eps=j/1000
        g=min(d-th*eps,1-(1-eps)*(1-d),2*eps)
        if g>best[0]: best=(g,th,eps)
print('(4) best gamma=%.4f at theta=%.3f eps=%.3f'%best)
print('NOTE: finite checks of the inequalities/accounting only; not a proof of L5.')
