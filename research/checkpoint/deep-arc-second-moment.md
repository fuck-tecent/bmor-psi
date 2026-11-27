# 深次弧上保留了多少二阶矩？ / Second-moment mass outside the wide arcs

取研究台的素数对数权和普通区间 $[0,1]$。对所有充分大的整数 $n$，立方根截断的宽主弧之外仍保留全圆二阶矩的一个固定正比例。分母上限扩大到研究台使用的 $\lfloor\sqrt n/\lfloor\log_2(n+2)\rfloor^4\rfloor$ 后，弧外二阶矩仍至少为常数倍的 $n\log\log n$。这两个下界说明，对积分逐点取绝对值会损失有符号估计所需的抵消。

Let $e(x)=\exp(2\pi i x)$ and $S_n(t)=\sum_{p\le n}(\log p)e(pt)$, with the sum over primes. Write $B_n(D,H)$ for the part of $[0,1]$ outside every closed interval of radius $H/(rn)$ about a reduced fraction $b/r$ with $1\le r\le D$ and $0\le b\le r$. Set $\ell=\lfloor\log_2(n+2)\rfloor$. The following bounds hold for every sufficiently large integer $n$, with absolute implied constants.

| Denominator cutoff $D$ | Width parameter $H$ | Bound on $\int_{B_n(D,H)} \lvert S_n(t)\rvert^2\,dt$ |
| --- | --- | --- |
| $\lfloor n^{1/3}\rfloor$ | $256D\ell^2$ | $\asymp n\log n$ |
| $\lfloor\sqrt n/\ell^4\rfloor$ | $256D\ell^2$ | $\gg n\log\log n$ |

These are the masks called **wideArcs** and **sqrtArcs** in the catalogue. Since $\lvert S_n(t)^2e(-nt)\rvert=\lvert S_n(t)\rvert^2$, an upper bound obtained by integrating this absolute value cannot give an $o(n)$ bound on either complement. The signed integral can still have cancellation.

## A lower bound for each denominator scale

Put $L=\lfloor\sqrt n/4\rfloor$. Suppose $128\le D<L$ and $LH\le n/2$. We prove

$$
\int_{B_n(D,H)} |S_n(t)|^2\,dt
\ \ge\ \frac{n}{6144}\left\lfloor\log_2(L/D)\right\rfloor
$$

for all sufficiently large $n$, uniformly in these choices of $D$ and $H\ge0$. Here $D$ is an integer. Each complete dyadic block $(T,2T]$ with $T=2^jD$ and $2T\le L$ contributes at least $n/6144$.

**1. Disjoint windows inside the complement.** Take all squarefree $q$ with $D<q\le L$ and all $1\le a<q$ coprime to $q$. Use the one-sided window $a/q+[0,1/(6n)]$. Every window lies inside $[0,1]$ because $1/q>1/(6n)$. Any two distinct reduced centers are at distance at least $1/L^2$, so the windows are jointly disjoint across all denominator blocks. For a removed center $b/r$ we have $r\le D<q$ and $|ar-bq|\ge1$. Uniformly for $0\le h\le1/(6n)$,

$$
qr\,|a/q+h-b/r|\ \ge\ 1-qr/(6n)
\ \ge\ 1-L^2/(6n)\ >\ 1/2\ \ge\ qH/n.
$$

Thus even the endpoints lie outside every removed interval.

**2. Energy at one squarefree denominator.** Write $\theta(n)=\sum_{p\le n}\log p$. In our shift range $\Re S_n(h)\ge\theta(n)/2$ because $0\le2\pi ph\le\pi/3$. The sum over reduced numerators satisfies

$$
\sum_{(a,q)=1\bmod q}S_n(a/q+h)
=\mu(q)\left(S_n(h)-\sum_{p\mid q}p\log p\,e(ph)\right).
$$

Indeed the Ramanujan sum $c_q(p)=\sum_{(a,q)=1\bmod q}e(ap/q)$ is multiplicative in squarefree $q$ by the Chinese remainder theorem. At a prime factor $s$ its value is $-1$ if $s\nmid p$ and $s-1$ if $s=p$. All prime divisors of $q$ occur in $S_n$ since $q\le L\le n$. The prime-divisor sum subtracted from $S_n(h)$ has absolute value at most $q\sum_{p\mid q}\log p\le q\log q$. The prime number theorem gives $\theta(n)\ge n/2$ eventually and $L\log L\le n/8$ eventually. Hence the absolute value of the sum over numerators is at least $n/8$, uniformly in $q$ and $h$. Cauchy–Schwarz and $\varphi(q)\le q$ yield

$$
\sum_{(a,q)=1\bmod q}|S_n(a/q+h)|^2\ge \frac{n^2}{64q}.
$$

Integrating over $0\le h\le1/(6n)$ yields at least $n/(384q)$ on the windows of this denominator.

**3. Count squarefree denominators and sum the blocks.** In $(T,2T]$, at most $\sum_{2\le d\le\sqrt{2T}}(T/d^2+1)$ integers are divisible by a square $d^2$ with $d\ge2$. Since $\sum_{d\ge2}d^{-2}\le1/4+\int_2^\infty x^{-2}dx=3/4$ and $\sqrt{2T}\le T/8$ for $T\ge128$, at least $T/8$ denominators are squarefree. Each has $q\le2T$. Their total contribution is at least $(T/8)n/(768T)=n/6144$. The joint disjointness in step 1 allows all $\lfloor\log_2(L/D)\rfloor$ complete blocks to be included in the same integral.

## Applying the two catalogue cutoffs

For $D=\lfloor n^{1/3}\rfloor$ we have $LH/n=O(n^{-1/6}\ell^2)=o(1)$ and $\log_2(L/D)=\tfrac16\log_2 n+O(1)$. Parseval gives the matching upper bound on the full circle,

$$
\int_0^1 |S_n(t)|^2\,dt=\sum_{p\le n}(\log p)^2
\le(\log n)\theta(n)\ll n\log n.
$$

For $D=\lfloor\sqrt n/\ell^4\rfloor$ we have $LH/n=O(\ell^{-2})$ and $\log_2(L/D)=4\log_2\ell+O(1)$. This yields the second row of the table. Matching its lower bound with an upper bound would require a further estimate.

## Lean proofs accompanying the calculation

The window lemmas prove separation from the published arc set and pairwise disjointness for arbitrary real shifts. The energy lemmas prove the pointwise Cauchy–Schwarz estimate and integrate it to obtain $n/(384q)$ from the lower bound on the sum over numerators. The complete single-file proof combines these lemmas with the Ramanujan-sum evaluation, the squarefree count and disjoint-window summation. It proves both rows of the table, including the square-root cutoff result as a separate theorem. [Full proof in PR #2520](https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/2520). [Window proofs](DeepArcWindows.lean) · [Energy proofs](ResidueEnergy.lean)

Both files can be checked from the repository's **lean** directory.

```sh
lake env lean --trust=0 ../research/checkpoint/DeepArcWindows.lean
lake env lean --trust=0 ../research/checkpoint/ResidueEnergy.lean
```

## Related work

PR #2495 proposes a fourth-moment obstruction using squarefree denominators. PR #2508 supplies a Lean refutation of the fourth-moment claim. Here the exponent two makes each complete denominator block contribute the same lower bound, so the number of blocks determines the logarithm. Harper and Soundararajan obtain a related minor-arc mean-square lower bound for the von Mangoldt exponential sum with their own cutoff and widths. The argument above uses the prime-only weight and the two masks as published in this project. [Project fourth-moment argument](https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/2495) · [Submitted Lean refutation](https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/2508) · [Harper and Soundararajan, §6, after (26)](https://arxiv.org/pdf/1602.01984#page=16)
