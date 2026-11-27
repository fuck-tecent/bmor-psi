import math, cmath
N = 20000
# sieve Lambda
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
tot = sum(l*l for l in lam)   # = int_0^1 |V|^2
print("N =", N, " sum Lambda^2 =", round(tot,1))
def V(theta):
    # sum_h lam[h] exp(2 pi i theta h)
    s = 0j
    two_pi = 2*math.pi
    for h in range(2,N+1):
        if lam[h]:
            s += lam[h]*cmath.exp(1j*two_pi*theta*h)
    return s
for delta in [0.3,0.1,0.03,0.01,0.003,0.001]:
    M = 300
    acc = 0.0
    for j in range(-M, M+1):
        th = delta*j/M
        acc += abs(V(th))**2
    integral = acc*(2*delta/M)
    print(f"delta={delta:8.4f}  delta*N={delta*N:9.1f}  int/|V|^2 = {integral/tot:8.5f}")
