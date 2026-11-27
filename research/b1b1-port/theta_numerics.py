import math, sys
from array import array

def sieve_mu(N):
    mu = [1]*(N+1)
    primes=[]
    iscomp=bytearray(N+1)
    mu[0]=0
    for i in range(2,N+1):
        if not iscomp[i]:
            primes.append(i); mu[i]=-1
            for j in range(i*i,N+1,i):
                iscomp[j]=1
        for p in primes:
            if i*p>N: break
            iscomp[i*p]=1
            if i%p==0:
                mu[i*p]=0
                break
            else:
                mu[i*p]=-mu[i]
    return mu

def sieve_lam(N):
    lam = [0.0]*(N+1)
    spf = list(range(N+1))
    for i in range(2,int(N**0.5)+1):
        if spf[i]==i:
            for j in range(i*i,N+1,i):
                if spf[j]==j: spf[j]=i
    for m in range(2,N+1):
        p=spf[m]; k=m; e=0
        while k%p==0: k//=p; e+=1
        if k==1: lam[m]=math.log(p)
    return lam

def run(n):
    U = math.isqrt(int(n**(1/16)))+0
    # careful integer floors
    U = int(n**0.0625)
    while (U+1)**16 <= n: U+=1
    while U**16 > n: U-=1
    B1 = math.isqrt(math.isqrt(n))
    while (B1+1)**4 <= n: B1+=1
    while B1**4 > n: B1-=1
    mu = sieve_mu(B1)
    lam = sieve_lam(n)
    # c(a) = sum_{d|a, d>U} mu(d)
    c=[0]*(B1+1)
    for d in range(U+1,B1+1):
        if mu[d]!=0:
            for a in range(d,B1+1,d):
                c[a]+=mu[d]
    tau=[0.0]*(n+1)
    for a in range(U+1,B1+1):
        if c[a]==0: continue
        ca=c[a]
        for r in range(U+1, n//a+1):
            if lam[r]!=0.0:
                tau[a*r]+=ca*lam[r]
    D=sum(tau[m]*tau[n-m] for m in range(n+1))
    theta=sum(c[a]/a for a in range(U+1,B1+1))
    mass=sum(tau)
    L2=sum(t*t for t in tau)
    return dict(n=n,U=U,B1=B1,theta=theta,D=D,D_over_n=D/n,mass=mass,mass_over_n=mass/n,L2=L2,L2_over_n=L2/n)

for n in [10**4, 10**5, 10**6, 10**7]:
    r=run(n)
    print({k:(round(v,6) if isinstance(v,float) else v) for k,v in r.items()})
