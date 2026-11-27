# 二进反射与 Levent GRH 零点公式

[中文研究路线](https://www.movan.tech/goldbach/?lang=zh#route=dyadic-reflection) · [English research route](https://www.movan.tech/goldbach/?lang=en#route=dyadic-reflection)

固定偶数 $N$，取严格大于 $N$ 的最小二次幂 $M=2^K$。对 $q=2^k<M$，记 $D_q(r)$ 为模 $2q$ 的两个子类 $r,r+q$ 的对数素数权之差。反射将模 $q$ 的 $r$ 送到 $\rho=(N-r)\bmod q$，并按 $(N-r)\bmod 2q$ 是否小于 $q$ 决定子类的符号 $\sigma_q(r)$。逐层贡献为

$$C_q(N)=\frac qM\sum_{r<q}\sigma_q(r)D_q(r)D_q(\rho).$$

把各层贡献与 $(\sum_{p\leq N}\log p)^2/M$ 相加，得到 $\sum_{p+q=N}\log p\log q$，其中两变量遍历有序素数对。对于偶数 $N$，$C_1(N)\geq0$。严格的 $M>N$ 保证 $N$ 本身为二次幂时顶层也完整。

## 已冻结的输入

| 草案 | 任务 | 交付及用途 |
| --- | --- | --- |
| AD1 | DR-0001、DR-0002 | 在任意实权上证明进位恒等式和卷积的望远镜展开。复用 `L-goldbach-coset-sum-reflection` 的纤维反射。 |
| AD2 | DR-0003、DR-0004 | 用 $1+q$ 的特征值 $-1$ 筛出本原特征。半差 Parseval 的因子为 $2/\varphi(2q)$，最低一层为模 4。现有 OC-0055 筛的是 $\chi(-1)=-1$。 |
| G01 | DR-0005、DR-0006 | 对保留 $x,N-x$ 两者均为单位的部分反射证明平方投影和正负维数。在任意特征子集上得到 Hermitian 收缩界，供换权和零点替换。 |
| G02 | DR-0007、DR-0008 | 证明反射与素幂约化的纤维平均交换。导子 1 和 $p$ 同属最低块，其上不同层的矩阵元为零。 |
| G03 | DR-0009 | 证明稳定子要求非零矩阵元的特征比从 $m/\gcd(m,N)$ 诱导，并限制每行的支撑；包含商模 1。 |
| G04 | DR-0010、DR-0011 | 对互素模数乘上归一化矩阵元。在素模计算交叉 Jacobi 相位及目标为零的对角项。复用 CW-8001、CW-8002 的实二次特例作检验。 |
| G05 | DR-0012 | 用实际单位质量的本原特征二次型恢复奇余类部分。归一化向量为 $W_N(\bar\chi)/\sqrt{\varphi(m)}$，回到 $C_q$ 的权为 $m/M$。 |
| G06 | DR-0013 | 计算真素数权在偶余类上的唯一可能贡献。模 $2q$ 下 $N\equiv 4$、$N\equiv 4+q$ 分别取正、负号。层权求和后的成本小于 $(\log 2)^2$。 |
| G07 | DR-0014 | 在 $m\mid2N$ 时由乘 $N-1$ 对角化。对二次幂目标，顶层本原特征取得 $-\chi(-1)$，其余层取得 $\chi(-1)$；可对 OC-0005 的中心窗权使用。 |
| G08 | DR-0015 | 在整数纤维上应用 Cauchy–Schwarz，再在单位群上用 Parseval，得到适用于任意特征子集的因子 $1+\lfloor N/m\rfloor$。 |
| G09 | DR-0016 | 在实际反射二次型中从真素数权换为 $\Lambda$。以已收录的 `L-goldbach-power-index-count` 和逐整数范数控制两项混合损失。 |
| AD4 | DR-0017 | 给定真素数扭曲和界，求和至 $q\leq Q$，其中 $2Q\leq N$。代入 $Q=N/\log^6(2N)$ 后得到 $O(N/\log^2(2N))$ 的误差。 |
| G13 | DR-0018 | 对一批任意选定的二幂层保留权 $m/M$，用两项几何和汇总混合项与替换向量的平方。 |
| G12 | DR-0019 | 取 $u=N+1/2$、$T=N$，将逐特征余项和低零点界转换为归一化向量误差。零点计重数，要求 $|\operatorname{Im}\rho|<T$，覆盖 $N<m\leq2N$。 |

## 文献接口与剩余估计

- AD3 使用 #2829 的 `GoldbachGRHPrimeError.twisted_prime_interval`，取区间 $[0,N]$、模数 $2q\leq N$ 和非主特征。两条裙边的冻结声明已在平台登记。#2829 提供带显式 GRH 前提的 Lean 结论，生产目前暂停 GRH 核验。DR-0017 把所需扭曲界写成前件，允许在 Mathlib 环境先完成粗层归约。 [#2829 的源码](https://github.com/CGandGameEngineLearner/goldbach-proofs/blob/cfde193e18afc4e0ffac53868d514142e908cd36/research/goldbach-skirts/LowSkirtGRHSingle.lean#L8704)
- G10 对接 Levent 的 `GlobalTheory.ExplicitFormula.truncated_explicit_formula`。对本原且非主的特征，$u=N+1/2$ 消去整数端点权，$T=N$ 允许模数直到 $2N$。原定理及其依赖需要移植到本站的 Lean 版本。DR-0019 复用它所给的逐特征余项。 [固定提交中的显式公式](https://github.com/leanprover-community/riemann-hypothesis/blob/fcb6eac7534875d32d68030967e2deae6d686151/src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedExplicitFormula.lean#L607)
- G11 复用 #2829 的 `uniform_dirichlet_zero_slice`。取窗中心 0，以 `analyticOrderNatAt` 计重数。对模数大于 1 的本原特征，`regularizedL` 等于原 $L$ 函数。零线给 $|\rho|\geq1/2$，中心实零也包含在余项内。 [带重数的单位窗估计](https://github.com/CGandGameEngineLearner/goldbach-proofs/blob/cfde193e18afc4e0ffac53868d514142e908cd36/research/goldbach-skirts/LowSkirtGRHSingle.lean#L2818)
- G14 的正负投影由 DR-0005 与 DR-0009 给出的不变空间构造。在 $N=10,m=8$ 的奇余类上，反射固定 1、5，交换 3、7，两个符号都出现。二次幂目标可用 DR-0014 直接按符号分组。 [特征乘法换元的来源](https://github.com/leanprover-community/riemann-hypothesis/blob/fcb6eac7534875d32d68030967e2deae6d686151/src/Development/AbelianVarietyTheory/Proofs/FoundationProofs/DirichletCharFiniteFourierTransformProperties.lean#L85)

G15 和 AD5 要求在每个充分大的偶数 $N$ 上，让真实细层零点向量的带符号和保留固定正余量。该双变量估计沿用原父题。其到 AD6 的合成使用同一个 $N$、相同的真素数权和阈值。DR-0016 在每层乘上 $m/M$，对 $q>N/\log^6(2N)$ 的 $O(\log\log N)$ 层求和。DR-0018 代入 DR-0019 的统一向量误差后得到 $o(N)$，该误差预算对细层的实际符号没有假设。与粗层误差合并后，仍需细层留下线性正余量，才能得到充分大偶数的结论。 [逐点父题](https://www.movan.tech/goldbach/?lemma=L-goldbach-binary-pointwise-positivity) · [二次幂中心窗父题](https://www.movan.tech/goldbach/?lemma=L-goldbach-dyadic-central-prime-mass)
