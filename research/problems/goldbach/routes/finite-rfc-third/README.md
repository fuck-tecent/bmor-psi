# 小偶数覆盖第三批 · Finite-range coverage III

令 \(C=4\cdot10^{18}\)、\(X(a)=\exp(\exp a)\)、\(T=X(32.7)\)。\(G_r(n)\) 要求 \(n=p+s\)，其中 \(p\) 为素数、\(s\ge2\)，且 \(s\) 的素因子按重数不超过 \(r\)。RFC1 要在 \(4\le n<X(50)\) 的全部偶数上得到 \(G_1\)，并在 \(C<n\le T\) 的全部偶数上得到 \(G_2\)。已发表的计算验证包含端点 \(C\)。[RFC1](../../../../RFC1-小偶数上的Goldbach.md) · [Oliveira e Silva、Herzog、Pardi](https://doi.org/10.1090/S0025-5718-2013-02787-1)

## Prime pair certificates

F01–F03 对应 FR-9001、FR-9002。对 \(C-4095\le p<C+32768\) 的大素数锚点，将 \(p-1\) 的完整分解和 Lucas 底数写成 CSV。候选最初由素数筛和整数因数分解产生。复核只用模幂、因子乘积、最大公因数与从 2 开始的归纳。CSV 有 4350 个非基例节点和 858 个锚点。每行是 \(p,a,q_1,\ldots,q_k\)，素因子 \(q_j\) 按重数列出。逐个以 \(\ell\mid p-1\) 检查 \(\gcd(a^{(p-1)/\ell}-1,p)=1\)。Mathlib 的 Lucas 判据只需要该模幂不等于 1。[Lucas 表](lucas.csv) · [Mathlib 判据](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/NumberTheory/LucasPrimality.lean)

对 \(n=C+130,C+132,\ldots,C+32768\)，从最大的 \(p<n\) 开始倒查，至多回退 28 个锚点，检验较小余数 \(q=n-p\) 的素性。相邻锚点间的偏移 \(t=n-p_i\) 可用 FR-7017 的平移见证语义一次核验。证书使用 767 个不同的大素数，\(q\le1499\)。首尾两对为 \((C+69,61)\)、\((C+32701,67)\)。回放生成的 16,320 行 \(n,p,q\) 使用十进制和 LF，SHA-256 为 5d510f2aeac701bce09653cdc8796a07791622f76904636cbebd46c00aaa4870。FR-8001 覆盖 \(C+2\) 至 \(C+128\)，两块相接后的下一个偶数是 \(C+32770\)。[FR-7017](https://www.movan.tech/goldbach/?lemma=L-goldbach-finite-witness-translate-bitset) · [FR-8001](https://www.movan.tech/goldbach/?lemma=L-goldbach-finite-post-boundary-prime-block)

在仓库根目录运行标准库 Python 3。可加上 --pairs PATH 写出供 Lean 消费的见证表。[回放](replay.py)

~~~sh
python3 -B research/problems/goldbach/routes/finite-rfc-third/replay.py
~~~

## Rough remainder wheel

F04–F07 对应 FR-9003 至 FR-9006。模 \(W=30030\) 的十二个基类由 FR-8002 覆盖。对每类保留十六个同余的素数。它们分别在从 17 到 73 的十五个素模上有互不相同的余数。最大发现值为 \(B=19\,495\,926\,503\)。对于给定偶数 \(n\ge B+2\)，先取满足 \((n-b,W)=1\) 的基类。每个额外素数至多消去该类的一个候选，剩下的候选给出 \(2\le n-p\) 且每个素因子至少为 79。通过投影纤维大小合并该表，所需枚举范围为模 \(W\) 的 15,015 个偶余类。候选表的 SHA-256 为 d57127f950d88c642bba0788c71d8c462343550505ce7330899c74cc8b328355。[候选表](wheel.csv) · [FR-8002](https://www.movan.tech/goldbach/?lemma=L-goldbach-finite-wheel-unit-base)

对 \(22\le n<B+2<11^{11}\)，FR-7006 的模 210 见证给 11 粗余项。\(4\le n\le20\) 的九个素数对在 RFC1 列出。回放核对 \(e^{19/5}<45<11\log79\) 和 \(e^5<297/2<34\log79\)。结合 \(79^{\Omega(n-p)}\le n-p<n\)，得到两个原型的 \(G_{10}\)、\(G_{33}\) 候选定理。FR-9006 要求同一个 \(p\) 同时满足两条因子数界。[回放](replay.py) · [粗度到因子数](https://www.movan.tech/goldbach/?lemma=L-goldbach-finite-rough-factor-power)

## Fixed major arcs

F08–F15 使用同一子域 \(D_*=\{n:C<n<X(19/5),\ 30\mid n\}\)。对 \(Q=105\)、\(1\le q\le Q\) 和每个既约分子 \(a\) 取圆周半宽 \(h_q=Q/(qn)\)。Farey 分离给任意不同圆周中心之间的距离至少 \(1/(qs)\)，而 \(Q(q+s)<n\) 保证两弧互斥。模一的两个半弧借周期性合成中心 \(0/1\) 的一个对称积分。对其它中心直接用 \(\alpha=a/q+\beta\)。[Farey 间隙归约](https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/2509) · [既有分离引理](https://www.movan.tech/goldbach/?lemma=L-goldbach-arc-disjoint)

记 \(e(x)=e^{2\pi i x}\)、\(V_n(\beta)=\sum_{k=1}^n e(k\beta)\)、\(M_q(\beta)=\mu(q)V_n(\beta)/\varphi(q)\) 和 \(S_n(\alpha)=\sum_{k=1}^n \Lambda(k)e(k\alpha)\)。令 \(A,A_0\) 分别为 \(S_n^2,M_q^2\) 乘 \(e(-n\alpha)\) 后在各弧积分的实部总和。令 \(U,V\) 分别为 \(\lvert S_n-M_q\rvert^2,\lvert M_q\rvert^2\) 的各弧积分和。

- **FR-9007–9010。** 以 \(t=n\beta\) 缩放。相位的弦长给归一化 \(V_n\) 对 \(e(t/2)\operatorname{sinc}(\pi t)\) 的误差 \(2\pi|t|/n\)。对平方和平方模积分，误差均至多 \(4\pi (Q/q)^2/n\)。截断核 \(K_q=\int_{-Q/q}^{Q/q}\operatorname{sinc}^2(\pi t)\,dt\) 在 \(0\) 和 \(1\) 之间，且 \(K_q\ge1-2q/(9Q)\)。模型按既约分子求和后的系数为 \(\mu(q)^2c_q(-n)/\varphi(q)^2\)。\(q\mid30\) 的贡献至少 \(26/7\)，其余负项总损失小于 \(201/1000\)。能量表使用 \(\sum_{q\le105}\mu(q)^2/\varphi(q)\)。回放核对两个有理数表和 \(236336/n\) 的离散误差，给出模型目标 \(A_0/n>7/2\)、\(V/n<6\)。[回放](replay.py) · [Ramanujan 和的 CRT](https://www.movan.tech/goldbach/?lemma=L-goldbach-ram-crt)
- **FR-9011–9013。** 对单位类 \(a\bmod q\)，以 \(D_m=\psi(m;q,a)-m/\varphi(q)\) 作 Abel 求和。先用 \(m(\log(8\cdot10^9)+1)\) 控制 \(m<8\cdot10^9\)，再用 BMOR 的 \(\lvert D_m\rvert\le m/(840\log m)\) 对余下前缀求和。中段截至 \(6\cdot10^{14}\) 时用 \(\log m>22\)，其后用 \(\log m>34\)，端点 \(m=n\) 用 \(\log n>42\)。前两段贡献合计小于 \(n/10^9\)（对 \(|\beta|\le Q/n\)）。尾段保留 \(\pi|\beta|n^2/(840\cdot34)\)。\(q=1,2\) 都从模 4 的两条单位类推得，素数幂用非单位 Mangoldt 质量另计。[BMOR 定理 1.1](https://arxiv.org/abs/1802.00085)
- **FR-9012–9013。** 对每个 \(\beta\) 将单位类误差零延拓到所有剩余类。完整加法 Parseval 给误差平方和的因子 \(q\)，限制既约分子仍有同一上界。非单位质量至多 \(3\log n\)，用平方和范数的三角不等式加回。取 \(c_q=2\)（\(q=1,2\)）或 \(1\)（\(q\ge3\)），\(\alpha_q=c_q/(840\cdot42)+10^{-8}\)、\(\delta_q=c_q105(22/7)/(840\cdot34q)\)。用 \(u=|\beta|/h_q\) 积分，\(q\) 项对 \(U/n\) 的贡献上界为 \(210\varphi(q)(\alpha_q^2+\alpha_q\delta_q+\delta_q^2/3)\)。有理数总和小于 \(3/40\)，约为 0.073310599。最大的三项来自 \(q=1,2,3\)。[回放](replay.py) · [BMOR 原任务](https://www.movan.tech/goldbach/?lemma=L-goldbach-fixed-ap-bmor-psi)
- **FR-9014–9015。** 展开平方，用 Cauchy–Schwarz 得 \(A\ge A_0-2\sqrt{UV}-U\)。取 \(U/n\le1/10\)，即 \(A/n>37/20\)。FR-9015 显式挑战同一子域同一弧宽的真实补弧损失 \(\le9n/5\)。若得到这条界，扣掉 FR-7019 的素数幂预算后仍有超过 \(n(1/20-10^{-5})\) 的正余量。还需要兑现 FR-9013 的 BMOR 输入。F13 沿用现有 BMOR ID，核对 \(q\le105\) 的表和低零点证书。F15 的正性组合沿用 FR-7021 和满圆系数恒等式。[显式幂预算](https://www.movan.tech/goldbach/?lemma=L-goldbach-finite-power-contamination-budget) · [正余量组合](https://www.movan.tech/goldbach/?lemma=L-goldbach-finite-band-fixed-loss-bridge)
- **FR-9022。** F12 的带符号备选项从单位类复权 \(F\) 出发。对每个 \(d\mid q\)，用 \(F_d(y)=\sum_{r\equiv y\bmod d}F(r)\) 表示纤维质量。对既约分子的平方和乘 \(e(-na/q)\) 后恰等于 \(\sum_{d\mid q}d\mu(q/d)\sum_y F_d(y)F_d(n-y)\)。这条恒等式保留符号、复相位和 \(d=1\) 项，允许将 \(d>1\) 的项接到第三章的部分反射。实际积分还乘共同的 \(e(-n\beta)\)，并需补入非单位项及其交叉项。[素幂 Ramanujan 和](https://www.movan.tech/goldbach/?lemma=L-goldbach-ram-prime-power)

## Weighted sieve and Chen counts

**F16–F20。** 采用千早爱音（Visio-Vanitas）原稿的加权筛。令 \(A\) 为 \(p\le n\) 的素数中 \(p\nmid n\) 且 \(n-p\) 无小于 \(z\) 的素因子者。FR-9016 用整数权 \(2w\)，从和中精确扣除 \(p=n-1\) 的贡献。FR-9023 在这个底集上写出一次和平方整除的两组实际计数，并剔除整除 \(n\) 的筛素数。FR-9017 在同一权重上将支持判据推广到 \(r\) 个因子，条件是 \(y^{r+1}\ge n\)、\(zy^r\ge n\)。F17–F18 沿用现有的 58 段证书和换段审阅，需逐段兑现各筛不等式及带平方整除的同归一化误差。FR-9018 按 \(r=2\) 冻结为显式挑战，仅要求 \(D_*\)。可先按 \(r=3\) 实算。区间内的 \(G_2\) 需要相应 \(r=2\) 正余量。[1+4 原稿及审查](../../../../checkpoint/2026-11-26-one-plus-four/proof.md) · [作者权重形式化](https://github.com/Visio-Vanitas/buchstab-switching/blob/a5c1fa9cee34de526915481f93cadeb1ea16014b/lean/AllEvenOnePlusFour/AllEvenOnePlusFour/Weights.lean)

**F21–F22。** FR-9019 对齐 BJS 定理 3 的无权计数。BJS §10 在从定理 3 推出推论 4 时另扣余项 1 和素数平方。FR-9020 将不同素因子的余项用 \(r<v\) 唯一归类，切开 \(r^3\le n\) 和 \(r^3>n\)。若 \(r\mid n\)，则素性迫使 \(p=r\)，坏模数计数至多为 \(\omega(n)\)。在好模数上用 FR-9021 计算多项式 \(v(n-rv)\) 的局部根数，包括 \(r\equiv0\bmod\ell\) 与 \(n\equiv0\bmod\ell\)。对实际筛计数，还保留 \(v=\ell\) 或 \(n-rv=\ell\) 的有限例外。平方项沿用已有 FR-8006、FR-8007。定理 3 在 \(n>T\) 的端点严格开，应用于 \(I_{654}\) 时也保持这一点。[BJS 定理 3 和 §10](https://arxiv.org/html/2207.09452v6#S10) · [平方损失](https://www.movan.tech/goldbach/?lemma=L-goldbach-finite-chen-square-numeric-loss)

**F23。** 对同一个 \(n\) 在实际无权计数中排除不同因子半素数耗尽净计数的可能。FR-9020 保留 \(p=n-rv\) 为素数。BJS 文献下界本身数值较小，直接要求半素数数目小于该数值需要额外论证。可先比较 \(n^{1/3}<r<v\le n/r\) 的贡献与同权重的实际总下界。这是 RFC1 中原 \(D_h-J_h\) 挑战的相同奇偶性输入。若调整计数权重，还需另得该权重的下界。[RFC1 的挑战与权重](../../../../RFC1-小偶数上的Goldbach.md)

**F24。** FR-7001–7003、FR-7015–7016 仍负责双对数网格和已证范围交接。\(I_{75}\) 按 \(C,C+128,C+32768\) 切，\(I_{654}\) 保留 \(T\) 的严格分界，最后一带排除 \(X(50)\)。充分大偶数的定理必须给出不超过 \(2\lceil X(50)/2\rceil\) 的显式起点才能与主目标拼接。Lean 证明验收后再将相应范围计入 \(G_r\)。[RFC1 的覆盖表](../../../../RFC1-小偶数上的Goldbach.md)
