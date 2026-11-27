# A residue-class obstruction to Beaumont's central prediction

`L-goldbach-beaumont-central-local-prediction` requires the predictor for two adjacent even targets to be at least $M=X/\log^2 X$ at every even integer in $[X,2X]$. On a positive-density subset, the mean of the actual counts is at most $(495/512+o(1))M$. This gives a positive lower bound for the mean-square error of **every** such predictor.

在 $[X,65X/64]$ 中取模 30 余 26 的偶数。对每个目标 $n$，分别计算 $n$ 和 $n+2$ 有多少个有序素数表示，其中第一项落在目标的中央三分之一区间。两者相加后的平均值仍低于题目规定的统一预测下限。这个偏差出现在正比例的整数上，因而均方误差无法任意缩小。它指出了局部预测条件需要修改；相邻偶数是否同时缺少中央表示仍是独立问题。

## Count the ordered pairs

Use the frozen definitions $H(m)=\#\{(p,q):p,q\text{ prime},\ p+q=m,\ m\le3p\le2m\}$ and $R(n)=H(n)+H(n+2)$. Put $\delta=1/64$ and let

$$
A_X=\{n\in[X,(1+\delta)X]\cap\mathbb N:n\equiv26\pmod{30}\}.
$$

Then $A_X$ lies in the task's set of even targets and $|A_X|=\delta X/30+O(1)$. Both primes in a central representation lie between one and two thirds of their sum. For large $X$ they exceed 5 and belong to reduced classes modulo 30. The possibilities are

| Shift $s$ | $(p\bmod 30,q\bmod 30)$ for $p+q=n+s$ |
| --- | --- |
| $0$ | $(7,19),(13,13),(19,7)$ |
| $2$ | $(11,17),(17,11),(29,29)$ |

Each ordered prime pair contributes to at most one $n$ for a fixed shift, including when the two classes coincide.

Write $\pi_a(t)$ for the number of primes at most $t$ in a reduced class $a$ modulo 30. Uniformly for $X/4\le t\le2X$,

$$
\pi_a(t)=\frac{t}{8\log X}+o(X/\log X).
$$

Indeed the fixed-modulus prime number theorem gives $\pi_a(t)\sim t/(8\log t)$. Its relative error tends uniformly to zero on this interval since the lower endpoint tends to infinity, and $\log t=\log X+O(1)$. There are only eight classes. Thus the number of primes of one such class in any subinterval is its length divided by $8\log X$, with an additive $o(X/\log X)$ uniform in both endpoints. Endpoint rounding contributes at most $O(1)$. The pinned Mathlib provides this input as [`Nat.isEquivalent_card_prime_modEq`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/NumberTheory/LSeries/WeakPNT.lean#L164-L168).

Fix a row and one ordered class pair. Every admissible $p$ lies between $(X+s)/3$ and $2((1+\delta)X+s)/3$, an interval of length $(1+2\delta)X/3+O(1)$. For each such $p$, every admissible $q$ lies in $[X+s-p,(1+\delta)X+s-p]$, of length $\delta X$. All these intervals lie within $[X/4,2X]$ for large $X$. Applying the uniform bound first to $q$ and then to $p$ gives

$$
\sum_{n\in A_X} R(n)\ \le
6\left(\frac{(1+2\delta)X}{3\cdot8\log X}+o(X/\log X)\right)
 \left(\frac{\delta X}{8\log X}+o(X/\log X)\right).
$$

Dividing by $|A_X|M$ yields an upper bound of $15(1+2\delta)/16+o(1)=495/512+o(1)$. This estimate sums over targets, so it requires no conjecture about a fixed pair of primes.

## Contradiction with the frozen quantifiers

For all sufficiently large integer $X$, we have $|A_X|\ge\delta X/60$ and the average of $R$ on $A_X$ is at most $63M/64$. For any admissible $b$ (including one chosen separately for this $X$), the sum of $b(n)-R(n)$ on $A_X$ is at least $|A_X|M/64$. By Cauchy–Schwarz, the full error satisfies

$$
\sum_{n\in E(X)}(R(n)-b(n))^2
\ \ge\ \frac1{|A_X|}\left(\sum_{n\in A_X}(b(n)-R(n))\right)^2
\ \ge\ \frac{\delta}{60\cdot64^2}XM^2.
$$

Taking $\varepsilon=\delta/(120\cdot64^2)>0$ contradicts the claimed upper bound for all sufficiently large $X$. The existing conditional transfer to a bound on double misses therefore needs a different input.

The [Lean arithmetic certificate](BeaumontCentralPredictionArithmetic.lean) checks the ordered residue pairs, integer interval endpoints, rational constants, and the implication from a mean deficit to a square-error lower bound over an ordered ring in Lean 4.36. It also gives an exact parametrization of the target set along $X=1920K$. The application of the prime number theorem to the moving intervals and the assembly of these estimates for the frozen statement are given above in prose.
