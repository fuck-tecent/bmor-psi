# 同一轮模上的哥德巴赫表示数 / Goldbach counts on a fixed wheel

## 中文

令素数权 $w(p)=\log p$，在非素数处置零，记 $R(t)=\sum_{p=0}^{t}w(p)w(t-p)$。给定充分大的偶数 $N$，事先指定偶平方自由模数 $2\le W\le N^{1/12}$，例如固定 $W=30$。以下各窗口均用这个模数。设

$$
 U_W(N)=\{a\bmod W:(a,W)=(N-a,W)=1\},\qquad
 D_W(N)=\frac{W|U_W(N)|}{\varphi(W)^2}.
$$

由中国剩余定理，$D_W(N)=\prod_{p\mid W}p\nu_p/(p-1)^2$，其中 $p\mid N$ 时 $\nu_p=p-1$，否则 $\nu_p=p-2$。因为 $2\mid N$，所有因子都为正。$D_W(N+hW)=D_W(N)$ 精确成立。这个因子仅计入轮模内的素数，两条命题均无需用它近似完整奇异级数。

**可由 GRH 导出的粗平均。** 若 $N^2\le H^3$ 且 $WH\le N$，则

$$
 \sum_{0\le h<H}R(N+hW)\ \ge\ \tfrac1{16}NH D_W(N).
$$

这里的 $N$ 可以事先指定。取 $H=\lceil N^{2/3}\rceil$ 即可使参数范围对所有充分大的 $N$ 非空。证明只用既有 GRH 算术级数估计。它给既约类的 $\psi(x;W,a)$ 误差 $O(\sqrt N\log^2 N)$，对 $N/4-1\le x\le 2N$ 一致。去除真素数幂仍是这个误差，因为所有 $p^k\le2N,\ k\ge2$ 的总对数权为 $O(\sqrt N\log^2 N)$。于是对于每个 $a\in U_W(N)$，在 $N/4<p\le N/2$ 且 $p\equiv a\pmod W$ 的素数对数权至少为 $N/(8\varphi(W))$，其中 $\varphi(W)\le N^{1/12}$ 使误差被主项吸收。固定这样的 $p$，其补数 $N-p+hW$ 是一个既约类在左开右闭区间 $(N-p-W,\,N-p+(H-1)W]$ 内的全部整数。区间长 $HW$，相应的素数对数权至少为 $HW/(2\varphi(W))$，因为 $HW/\varphi(W)\ge H\ge N^{2/3}$。将两端下界相乘，再对 $|U_W(N)|$ 个互不相交的左端类求和，得到 $1/16$。这里给出了条件数学证明，目录条目待 Lean 形式化。[本站 GRH 算术级数与窗口输入](https://github.com/CGandGameEngineLearner/goldbach-proofs/blob/main/research/gaps.json)

**开放的两点目标。** 在同一 GRH 假设下，求一个绝对常数 $c>0$，使所有上述 $N,W$ 都满足

$$
 R(N)+R(N+W)\ \ge\ cN D_W(N).
$$

它在加性组合上的内容可以直接检验。设 $E_{\delta,W}=\{t\ge4:t\text{ 为偶数},\ R(t)<\delta t D_W(t)\}$，并定义 $E-W=\{n:n+W\in E\}$。两点目标排除 $N\in E_{c/3,W}\cap(E_{c/3,W}-W)$，因为 $D_W(N+W)=D_W(N)$ 且 $2N+W\le3N$。反过来，只要对某一统一的 $\delta>0$ 排除这项交叠，就得到两点下界，取 $c=\delta$ 即可。即使固定 $W=30$，稀疏集合 $\{2^{2^j},\,2^{2^j}+30:j\ge3\}$ 在 $X$ 以内只有 $O(\log\log X)$ 个元素，却含有无穷多对间距 30 的点。这说明仅有例外数上界无法推出所需的无交叠性质。这个集合只用于检验推理，并非素数的反例。

即使两点目标成立，仍可能 $R(N)=0$ 而 $R(N+W)>0$。要解决单点问题，还须排除这种孤立的例外。

在已有研究中，Cully-Hugill 和 Dudek 在 RH 下证明每个 $(x,x+9696\log^2 x]$ 含一个哥德巴赫数。它允许从整个区间中选择目标。Alsetri 与 Shao 的定理 1.1 和 1.2 表明，一个素数子集的全局相对下密度可以任意接近 1 而其和集仍漏掉正比例的偶数。若在每个既约类中的相对下密度均至少为同一个 $\delta>1/2$，则几乎所有偶数都有表示。这里的权使用全体真素数，要求每个指定的二点集合有统一的表示权下界。上述文献为间隔和局部密度提供背景，两点下界是本提案提出的目标。[短区间定理](https://arxiv.org/abs/2206.00433) · [密度定理](https://arxiv.org/html/2405.18576v2#S1)

## English

Give every prime its logarithmic weight and set the weight of each nonprime to zero. Write $R(t)$ for the resulting ordered binary convolution. For every sufficiently large even $N$, prescribe an even squarefree wheel $2\le W\le N^{1/12}$. A fixed wheel such as 30 is allowed. The definitions above give $D_W(N)>0$ and $D_W(N+hW)=D_W(N)$ exactly. Only primes dividing $W$ enter this factor.

**Coarse mean from GRH.** For every $H$ with $N^2\le H^3$ and $WH\le N$, the sum over $0\le h<H$ is at least $NH D_W(N)/16$. To see this, apply the GRH progression estimate to prime logarithmic weights, removing proper powers at a total cost $O(\sqrt N\log^2 N)$ per endpoint. In each admissible left class the primes in $(N/4,N/2]$ supply at least $N/(8\varphi(W))$. For each such prime $p$, its complements form exactly one reduced class in $(N-p-W,N-p+(H-1)W]$, supplying at least $HW/(2\varphi(W))$. The two errors are absorbed uniformly because $\varphi(W)\le N^{1/12}$ and $HW/\varphi(W)\ge N^{2/3}$. Multiplication followed by summation over the disjoint left classes gives the claim. The proof is conditional on GRH and awaits formalization.

**Open two-target estimate.** Seek an absolute $c>0$ for which $R(N)+R(N+W)\ge cN D_W(N)$ for every admissible $N,W$, under GRH. Equivalently up to a change of constant, the low-count set $E_{\delta,W}$ defined above must avoid its translate by $W$ at each admissible $N$. Indeed two deficiencies at threshold $c/3$ contradict the bound. Conversely a single nondeficient target gives the bound with $c=\delta$. A set of size $O(\log\log X)$ up to $X$ can still contain infinitely many prescribed-gap pairs, as the example with $W=30$ shows. The two-target estimate allows an isolated zero at $N$. To reach the single target one must still rule out such an isolated exception.

The RH theorem of Cully-Hugill and Dudek finds a Goldbach number anywhere in a logarithmically short interval. Alsetri and Shao obtain representations of almost all even integers from prime subsets having relative lower density uniformly above one half in every reduced class. Global relative density alone can approach one while a positive proportion of even integers is missed. These results use different quantifiers from a uniform lower bound for the two prescribed targets with the full prime weight. [Short intervals](https://arxiv.org/abs/2206.00433) · [Density theorems](https://arxiv.org/html/2405.18576v2#S1)
