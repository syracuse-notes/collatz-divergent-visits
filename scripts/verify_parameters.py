"""Instantiate the kernel-checked integer theorem L5M.L5_main with explicit parameters and
evaluate its bound exactly (integer arithmetic). Y=2^e, Yp=2^(e-ceil(e/50)), k=e, m1=1,
k'=e'-1, m2=2, (u,w)=(3,2), t0/t1 = least j meeting the hypotheses ht0/ht1.
Output: log2(bound)/e. Finite illustration of the asymptotic step (which is proved by hand)."""
import math
def least_j(lhs, mult):
    j=0
    while lhs > mult*3**j: j+=1
    return j
u,w=3,2
for e in [100,200,500,1000,2000,4000]:
    ep=e-math.ceil(e/50); Y=2**e; Yp=2**ep; k=e; m1=1; kp=ep-1; m2=2
    assert Y<=2**k*m1 and Yp//2+1<=2**kp*m2 and 2*k<=3*Yp+1 and 2*kp<=3*Yp+1
    t0=least_j(Yp*2**k, 4*Y); t1=least_j(Yp*2**kp, 3*Yp)
    S=(m1*(u+w)**k*w**t0)//(u**t0*w**k)
    C=(m2*2**kp*3*Yp)//Y
    P=(m2*(u+w)**kp*w**t1)//(u**t1*w**kp)
    tot=S+k*(C+P+1)
    print('e=%5d  log2(S)/e=%.4f  log2(k*C)/e=%.4f  log2(k*P)/e=%.4f  log2(total)/e=%.4f  (<1 means o(Y))'%(
        e, math.log2(S)/e, math.log2(max(k*C,1))/e, math.log2(max(k*P,1))/e, math.log2(tot)/e))
