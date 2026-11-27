# 筛过小素因子后，哪些补数是真素数？

固定一个偶数 $N$。陈氏定理对充分大的 $N$ 给出 $p+P_2=N$，其中 $P_2$ 至多有两个素因子，按重数计。若直接在这组表示上要求至少一个补数的素因子个数为奇数，得到的就是一个真素数对。为了把这一步分成两个可以各自研究的问题，下面保留一个更宽的候选集。[陈氏双重筛的定量结果，吴杰](https://arxiv.org/abs/0709.3764)

在中央窗口 $N<3p<2N$ 取素数 $p$，令 $m=N-p>1$。所有素因子 $r\mid m$ 都满足 $r^5>N$ 时保留 $p$。将这些 $p$ 组成的集合记为 $C_N$。记 $M=|C_N|$，$T_3$ 为其中恰有三个素因子的补数个数，$P$ 为其中素数补数的个数。令 $L=\sum_{p\in C_N}(-1)^{\Omega(N-p)}$，其中 $\Omega$ 按重数计数，四个量的每一项都用权 1。

### 两个估计怎样接上

保留下来的 $m$ 满足 $1\le\Omega(m)\le4$，因为五个允许的素因子相乘已经超过 $N$。所以有精确恒等式

$$2P=M-L-2T_3.$$

下列三个估计都针对**每一个**充分大的偶数，常数与 $N$ 无关。

| 目录任务 | 数学目标 | 着手之处 |
|---|---|---|
| `rough-fifth-mass` | $M\ge cN/(\log N)^2$，某个 $c>0$ | 把 $N-p$ 按小素因子筛去。使用维数一线性筛时应核对中央窗口、整除 $N$ 的素数、模数平均余项。 |
| `rough-fifth-triples` | $10T_3\le3M$ | 把 $m$ 写成排序后的素数乘积 $a b d$，按 $a,b$ 的大小分段估计 $N-abd$ 为素数的次数。排序使每个 $m$ 恰计一次。 |
| `rough-fifth-liouville` | $L\le (2/5-\eta)M$，某个 $0<\eta<2/5$ | 在同一窗口控制反射的刘维尔函数和。只需上界，可先研究平方自由补数上的莫比乌斯函数和。 |
| `rough-fifth-bridge` | 用上述有限恒等式提取真素数对 | 对四种可能的 $\Omega$ 值分别计数。 |

三个估计同时成立时，$2P\ge M-(2/5-\eta)M-3M/5=\eta M$。当 $N\ge9$ 时，两端都大于 $N/3$，每个有序素数对的对数权至少为 $(\log N)^2/4$。因此站内的完整卷积 $R(N)$ 至少为 $c\eta N/8$，这接到目录中的 `dyadic-correlation-floor`。从充分大偶数推广到全部偶数，还要覆盖阈值以下的区间。

### 可以先做的两项工作

**去除重复素因子。** 这对应第五条目录任务 **rough-fifth-square-error**。设 $z\ge1$ 为整数且 $z^5\le N$。记 $D$ 为 $C_N$ 中补数含素数平方因子的项数。每个这样的补数是某个 $r^2$ 的倍数，$r>z$。由于 $p\mapsto N-p$ 是单射，

$$D\le\sum_{z<r\le\sqrt N}\left\lfloor\frac N{r^2}\right\rfloor
 \le N\sum_{r>z}\left(\frac1{r-1}-\frac1r\right)=N/z.$$

这里求和可以取所有整数 $r$。令 $z=\lfloor N^{1/5}\rfloor$，得 $D=O(N^{4/5})$。这同时控制三因子计数中的重复因子，并给出 $\left|L-\sum_{p\in C_N}\mu(N-p)\right|\le D$。一旦有了上述质量下界，代换的误差就是 $o(M)$。莫比乌斯扭曲的研究因此有一个具体入口。Huang–Li 在普通分布估计和莫比乌斯扭曲的分布估计上给出了一个条件性哥德巴赫定理。把他们的输入用于此处仍需处理本路线的截断与固定平移。[Huang–Li](https://arxiv.org/abs/2005.03811)

**校准三因子预算。** 在素因子分解的连续密度模型中，令 $u,v,1-u-v$ 为按升序排列的三个素因子的对数除以 $\log N$。将局部密度和中央窗口的长度提出后，三因子项的体积为

$$\int_{1/5}^{1/3}\int_u^{(1-u)/2}\frac{dv\,du}{u v(1-u-v)}
=\int_1^3\frac{\log t}{1+t}\,dt \simeq 0.40609.$$

第二式用 $t=1/u-2$。维数一线性筛在水平趋近 $1/2$ 时的下筛系数，用同一归一化为 $4\log(3/2)\simeq1.62186$。四分之一的下筛预算约为 $0.40547$，略小于三因子的模型体积。选取 $3/10$ 将预算增加到约 $0.48656$。这给出了选择候选常数的依据。要完成 `rough-fifth-triples`，必须在每个 $N$ 上给出与 $M$ 相容的真实上界。比例也可经评审调整，一般地 $T_3\le bM$ 要配合 $L\le(1-2b-\eta)M$。

**有限核对。** $N=116$ 时 $(M,T_3,L)=(9,3,-1)$，三因子预算失效。$N=242$ 时取值为 $(15,2,7)$，有符号预算失效。两项命题都明确保留了“充分大”的限定。遍历 $1{,}000\le N\le20{,}000$ 的全部 9,501 个偶数，得到 $T_3/M$ 的最大值 $16/69$，出现在 $N=3{,}104$，而 $L/M$ 的最大值 $6/17$ 出现在另一个偶数 $N=1{,}412$。这些计算不能给出适用于任意大偶数的阈值。[整数计数脚本](experiments/rough_fifth_counts.py)

在上述归一化下，下筛系数来自 $5e^{-\gamma} f(5/2)$。可以从文献中 $2\le s\le4$ 的公式直接代入。两条有限命题另附可独立编译的证明。[线性筛函数，式 (2.5)](https://www.cambridge.org/core/journals/mathematical-proceedings-of-the-cambridge-philosophical-society/article/weighted-sieves-with-switching/986429394BA969687D48224E177E2F1C) · [奇偶计数证明](reference-proofs/L_goldbach_rough_fifth_bridge.lean) · [平方因子误差证明](reference-proofs/L_goldbach_rough_fifth_square_error.lean)

### English summary

For each fixed even $N$, take central primes $p$ with $N<3p<2N$ such that every prime factor of $N-p>1$ exceeds $N^{1/5}$. Give each candidate weight one. On this support the only odd values of $\Omega(N-p)$ are one and three. The Liouville sum $L$ detects their combined mass. Counting the triple products separately recovers the prime count by $2P=M-L-2T_3$. Either estimate can be investigated before the other is available.

The proposed targets bound triple products by three tenths of the common candidate count and the signed sum by $(2/5-\eta)M$. Together with a lower sieve bound for $M$, they imply the existing dyadic correlation floor. The square-divisor bound above reduces both investigations to distinct factors at a cost of $O(N^{4/5})$. The integral calibrates the trial constants in a model. The analytic estimates for the actual shifted primes remain to be established.
