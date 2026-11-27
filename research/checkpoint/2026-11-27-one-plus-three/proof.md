# 强哥德巴赫中间命题提交稿：GRH 下每个偶数的 1+3 表示

**提交者**　千早爱音（GitHub：**[Visio-Vanitas](https://github.com/Visio-Vanitas)**；推导、数值证书与 Lean 4 形式化主要由作者指导 **Gemini Carbon** 完成，并使用 **Claude Fable** 进行独立交叉审计）。[上游固定提交 `cca8048`](https://github.com/Visio-Vanitas/buchstab-switching/tree/cca80480105d17764982ca80fcbb9c41e76e1eed/k3) · [复核入口与依赖清单](README.md)

**待核验命题。** 假设 Dirichlet $L$ 函数的广义黎曼猜想（`DirichletLNonvanishingRightOfHalf`，与 [`lsernau/grh-lean@72fead1`](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact) 及 `leanprover-community/riemann-hypothesis` 的 Mathlib 声明逐字一致）。对每个偶数 $N\ge4$，存在素数 $p$ 和正整数 $m$，使得 $N=p+m$ 且 $\Omega(m)\le3$。这里 $\Omega$ 按重数计素因子，$\Omega(1)=0$。

**提交说明（待仓库独立核验）。** 本稿继 [1+4 中间命题](../2026-11-26-one-plus-four/proof.md) 之后，提交全体偶数 $N\ge4$ 在 Dirichlet GRH 下的 `1+3` 条件证明稿、零浮点任意精度区间证书及配套 Lean 4（`v4.37.0-rc1`）形式化归约，请求维护者与同行对筛法推导、区间算术证书、Lean 4 源码以及显式隔离的 6 条经典文献前提进行独立复核与审定。强哥德巴赫猜想要求第二个加数亦为素数（$K=1$），仍然开放。

---

## 1. 文献背景与一步 Buchstab–Richert 加权筛切换

在不包含“充分大”隐含常数、要求覆盖**全体偶数 $N\ge4$** 的显式问题上，此前文献在 GRH 下的记录为 Johnston–Starichkova（*Acta Math. Hungar.* **177** (2025), 163–192 / [`arXiv:2208.01229v3`](https://arxiv.org/abs/2208.01229v3)，定理 1.4）给出的 $K=31$（`1+31`），以及 Johnston（*Bull. Aust. Math. Soc.* **113** (2026), 372–374，定理 2）进一步推进的 $K=16$（`1+16`）。Johnston–Starichkova 在 `arXiv:2208.01229v3` 第 4 节定理 4.2 后注记及第 6.4 节指出，其单步非加权线性筛取 $z=N^{1/M}$ 并受分布水平 $D=N^{1/2-\alpha}\ge z^2$（即 $s>2$）制约，必有 $M\ge5$，故该路径在理论上至多只能达到 $K=M-1=4$，无法触及 $K=3$；同时经典 Brun 筛在如此小的 $K$ 下亦渐近失效。

为跨过非加权筛的 $K=4$ 屏障，本稿对 $N\ge4\cdot10^{18}$ 取移位素数集 $\mathcal{A}_N=\{N-p:p<N\text{ 为素数},\ p\nmid N\}$ 与筛素数集 $\mathbb{P}_N=\{q\text{ 为素数}:q\nmid N\}$，选取整数截断 $2\le z\le y$ 满足
$$N\le y^4,\qquad N\le z y^3,$$
并定义一步加权切换平衡量（`switchingBalance N z y`）：
$$S(\mathcal{A}_N,z)-\frac{1}{2}\sum_{\substack{z\le q<y\\ q\in\mathbb{P}_N}} S(\mathcal{A}_{N,q},z)-\frac{1}{2}\sum_{\substack{z\le q<y\\ q\in\mathbb{P}_N}} |\mathcal{A}_{N,q^2}|.$$

**组合捏紧关系（[`Core/ShiftedPrimes.lean`](https://github.com/Visio-Vanitas/buchstab-switching/blob/cca80480105d17764982ca80fcbb9c41e76e1eed/k3/BuchstabSwitching/Core/ShiftedPrimes.lean) 与 [`Sieve/OneStepSwitching.lean`](https://github.com/Visio-Vanitas/buchstab-switching/blob/cca80480105d17764982ca80fcbb9c41e76e1eed/k3/BuchstabSwitching/Sieve/OneStepSwitching.lean)）：** 对满足 $(N-p, P_N(z))=1$ 的 $p\in\mathcal{A}_N$，若 $\Omega(N-p)\ge 4$，则：
- 若存在 $q\in[z,y)$ 使 $q^2\mid N-p$，该元素在 $\mathcal{A}_{N,q}$ 与 $\mathcal{A}_{N,q^2}$ 中各被扣除 $\frac{1}{2}$，总权重至多为 $1-\frac{1}{2}-\frac{1}{2}=0$；
- 若 $[z,y)$ 内无平方素因子整除 $N-p$，则 $N-p$ 在 $[z,y)$ 内不可能仅有 $0$ 个素因子（否则 $N-p\ge y^4\ge N$），也不可能仅有 $1$ 个一次素因子（否则其余至少三个 $\ge y$ 的素因子给出 $N-p\ge z y^3\ge N$），故至少有两个不同素数 $q_1\ne q_2\in[z,y)$ 整除 $N-p$，总权重同样至多为 $0$。

因此 $\operatorname{switchingBalance}(N,z,y)\le \#\{p<N\text{ 为素数}:\Omega(N-p)\le 3\}$，无需引入陈氏 $1+2$ 中的三素数乘积 $q_1q_2q_3$ 二次切换项。只要对每个偶数 $N\ge4\cdot10^{18}$ 找到满足上述幂次条件的 $(z,y)$ 使 $\operatorname{switchingBalance}(N,z,y)>0$，即可推出存在 $N=p+m$（$0<m$，$\Omega(m)\le3$）。

---

## 2. 四段覆盖方案与待核验下界

| 偶数范围 | 筛法配置与归一化尺度 | 提交证书给出的归一化下界 |
|---|---|---|
| $4\le N<4\cdot10^{18}$（`1`） | 引用 Oliveira e Silva–Herzog–Pardi 双素数有限验证（$K=1\le 3$） | 精确覆盖（[文献来源](https://sweet.ua.pt/tos/goldbach.html)） |
| $4\cdot10^{18}\le N<2\cdot10^{23}$（`2a`，21 段） | 尺度 $\|\mathcal{A}_N\|$；$\{P_{\mathrm{sub}},\text{EvenBonf}\}$ + $<27000$ 精确奇素数段树 + Mertens/Schoenfeld 尾段（52 切片） | $\min \mathrm{net\_lo} = 0.001832023143583$（`2a-03`），$\min \mathrm{sieve\_net\_lo} = 0.008025632937025$，$\mathrm{tol}\ge 1.0467\times$ |
| $2\cdot10^{23}\le N<10^{84}$（`2b`，40 段） | 尺度 $\|\mathcal{A}_N\|$；$Q_1(a)\times \text{OddBonf}$ + 多截断混合 $\text{EvenBonf}/P_{\mathrm{sub}}$（56 切片） | $\min \mathrm{net\_lo} = 0.001763016371064$（`2b-40`），$\min \mathrm{sieve\_net\_lo} = 0.024224308978967$，$\mathrm{tol}\ge 2.3086\times$ |
| $10^{84}\le N<10^{600}$（`2c`，66 段） | 尺度 $\|\mathcal{A}_N\| V_N(z)$；$\max(\text{OddBonf},\text{BrunBlock})$ 配 $\min(\text{EvenBonf},\text{Adaptive Selberg }\Lambda^2)$（48 切片） | $\min \mathrm{net\_lo}=\min \mathrm{sieve\_net\_lo} = 0.003969217037886$（`2c-07`），$\mathrm{tol}\ge 1.4102\times$ |
| $N\ge10^{600}$（`3`，统一射线） | 尺度 $16 U_N N/\ln^2 N$；$z=\lfloor N^{1/16}\rfloor$，$y=\lceil(N/z)^{1/3}\rceil$；`Q0_100` 闭区间 $(H^*)$ 线性筛（Lean $C_2\le 494$ / 证书上限 `495`）+ Selberg $\Lambda^2$（`L=120` 条带） | $\mathrm{main\_lo}=0.046903008529996$，$\mathrm{err\_hi}=0.000077046424811$，$\mathrm{net\_lo}=0.046825962105185$（盈亏平衡 $C_2\le 1853.26$，$\mathrm{tol}=608.76\times$；`100:old` `0.05188079932`，`100:new` `0.05578565201`） |

完整分项误差分解（`rem_a`、`0.5 * err_aq`、`err_q2`、`err_one`）及参数含义见上游 [`k3/NOTES_K3_DERIVATION.md`](https://github.com/Visio-Vanitas/buchstab-switching/blob/cca80480105d17764982ca80fcbb9c41e76e1eed/k3/NOTES_K3_DERIVATION.md)。

---

## 3. Lean 4 形式化范围与待审阅的外部前提边界

上游 [`k3/`](https://github.com/Visio-Vanitas/buchstab-switching/tree/cca80480105d17764982ca80fcbb9c41e76e1eed/k3) 工程固定在 `leanprover/lean4:v4.37.0-rc1` 与 Mathlib `31ce06eaadf4a200c0e1407c5f10953cf606b8f8`。顶层定理 `BuchstabSwitching.all_even_one_plus_three_of_classical`（[`BuchstabSwitching/Main.lean`](https://github.com/Visio-Vanitas/buchstab-switching/blob/cca80480105d17764982ca80fcbb9c41e76e1eed/k3/BuchstabSwitching/Main.lean)）将目标命题归约至 `DirichletLNonvanishingRightOfHalf`、`CertifiedConstants` 与 `External.ClassicalBasicLemmas`：

1. **工程内部已包含的 Lean 4 形式化模块（待维护者独立重放核验）**：
   - 组合切换核心（`Core/`、`Sieve/OneStepSwitching`）、混合 Bonferroni（`BonferroniHybrid`、`BonferroniEstimates`）、分块 Brun 下筛（`BrunBlockSieve`）、Selberg $\Lambda^2$ 对角化与奇无平方因子碰撞和（`SelbergLambdaSq`、`SelbergDiagonalization`、`OddSquarefreeBounds`）；
   - Buchstab 延迟微分级数恒等式（`External/BuchstabSeries/DelayDiffEqIdentity.lean`：`buchstabSeriesPremise_proved`）、`Q0_100` 闭区间预筛条件（`closedHStarCond_Q0_100`）与奇偶分拆线性筛衰减常数 $C_2\le 494$（`LinearSieveBJS/CertifiedC2.lean`）；
   - Regime 2 全部 `127` 个有限区间的二进定点反射校验器（`Sieve/Regime2SlabBridge/SlabCertInst*.lean`，以偏置二进表示 $m\cdot 2^e/2^{8192}$、深度 6 奇素数段树与分片 `by decide` 验证 `allSlabs_bridges_inst`，不使用 `native_decide`）以及 Regime 3 全部 `120` 个渐近条带（`Sieve/Regime3RayBridge/RayCertInst*.lean`）。
2. **显式作为假设保留、请求重点审阅的 6 条经典文献输入（[`External/Bridge.lean`](https://github.com/Visio-Vanitas/buchstab-switching/blob/cca80480105d17764982ca80fcbb9c41e76e1eed/k3/BuchstabSwitching/External/Bridge.lean) 中 `ClassicalBasicLemmas`）**：
   - `SmallEvenPremise`（[`SmallEven.lean`](https://github.com/Visio-Vanitas/buchstab-switching/blob/cca80480105d17764982ca80fcbb9c41e76e1eed/k3/BuchstabSwitching/External/FiniteVerification/SmallEven.lean)）：$4\le N<4\cdot10^{18}$ 上的双素数表示（Oliveira e Silva–Herzog–Pardi, *Math. Comp.* **83** (2014), 2033–2060）；
   - `JSLemma51Premise`（[`DirichletGRH.lean`](https://github.com/Visio-Vanitas/buchstab-switching/blob/cca80480105d17764982ca80fcbb9c41e76e1eed/k3/BuchstabSwitching/External/CharacterSums/DirichletGRH.lean)）：在 `DirichletLNonvanishingRightOfHalf` 下，对 $x\ge X_2\ge4\cdot10^{18}$、$3\le d\le\sqrt{x}$、$(a,d)=1$ 成立的显式算术级数素数计数界 $|\pi(x;d,a)-\operatorname{Li}(x)/\varphi(d)|\le c_\pi(X_2,\mathrm{li}_2)\sqrt{x}\log x$（Grenié–Molteni, *J. Number Theory* **200** (2019), Cor. 1；Johnston–Starichkova, `arXiv:2208.01229v3`, Lemma 5.1）；
   - `SchoenfeldPrimePremise`（[`PrimeCountingRH.lean`](https://github.com/Visio-Vanitas/buchstab-switching/blob/cca80480105d17764982ca80fcbb9c41e76e1eed/k3/BuchstabSwitching/External/SchoenfeldRH/PrimeCountingRH.lean)）：在 RH 下对 $x\ge 2657$ 成立 $|\pi(x)-\operatorname{li}(x)|\le \sqrt{x}\log x/(8\pi)$（Schoenfeld, *Math. Comp.* **30** (1976), Cor. 1）；
   - `RobinOmegaBound`（[`PrimeFactorCount.lean`](https://github.com/Visio-Vanitas/buchstab-switching/blob/cca80480105d17764982ca80fcbb9c41e76e1eed/k3/BuchstabSwitching/External/RobinOmega/PrimeFactorCount.lean)）：对 $N\ge3$ 成立 $\omega(N)<1.3841\log N/\log\log N$（Robin, *Acta Arith.* **42** (1983), Théorème 11）；
   - `MertensPrimeSumPremise`（[`ReciprocalPrimeSums.lean`](https://github.com/Visio-Vanitas/buchstab-switching/blob/cca80480105d17764982ca80fcbb9c41e76e1eed/k3/BuchstabSwitching/External/MertensSums/ReciprocalPrimeSums.lean)）：Meissel–Mertens 常数包络 $0.261497\le M_0\le 0.261498$ 与双侧显式素数倒数和界（Johnston–Starichkova `arXiv:2208.01229v3` Lemma 3.2；Bordignon–Johnston–Starichkova `arXiv:2207.09452v6` Lemmas 16–17）；
   - `EulerProductVPremise`（[`ProductAsymptotic.lean`](https://github.com/Visio-Vanitas/buchstab-switching/blob/cca80480105d17764982ca80fcbb9c41e76e1eed/k3/BuchstabSwitching/External/EulerProductV/ProductAsymptotic.lean)）：对偶数 $N\ge3$ 与 $x\ge285$ 无条件成立的移位欧拉积 $V_N(\lceil x\rceil)$ 显式相对误差包络 `deltaV_bjs`（Bordignon–Johnston–Starichkova `arXiv:2207.09452v6` Lemma 38）。
   （此外 `CertifiedConstants` 封装 $\mathrm{li}(2)$、$M_0$、$U_c$ 与 $e^{-\gamma}$ 的有理数区间包络，详见 [`ExplicitConstants.lean`](https://github.com/Visio-Vanitas/buchstab-switching/blob/cca80480105d17764982ca80fcbb9c41e76e1eed/k3/BuchstabSwitching/External/NumericalConstants/ExplicitConstants.lean)。）

建议独立审阅时重点核查：(1) 上述 6 条外部前提及 `CertifiedConstants` 的 Lean 形式化签名与原文献定理条件、对数积分偏移约定（$\operatorname{Li}(x)=\int_2^x dt/\log t$ 与 $\operatorname{li}(x)=\operatorname{Li}(x)+\operatorname{li}(2)$）是否严格一致；(2) 二进反射见证验证器与 `Regime2SlabBridge` / `Regime3RayBridge` 主定理的对接是否完整覆盖各段归一化尺度与奇偶条件；(3) 独立从零重跑证书生成与 Lean 内核检查。
