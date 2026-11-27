# 从局部 Θ 见证到 abc · From local theta witnesses to abc

父题 **JA-0065** 是有理数上的 abc 猜想。对每个 $\varepsilon>0$ 要找到一个 $C_\varepsilon$，对全部互素正整数 $a,b$ 都有 $\log(a+b)\le(1+\varepsilon)\log\operatorname{rad}(ab(a+b))+C_\varepsilon$。研究台同时设有两个中间终点，分别是有界重数族的局部 Szpiro 型界 JA-0055，以及对全部三元组采用一个固定指数的弱 abc 界 JA-0059。[任务目录](problems.json)

研究起点是 Edison Mai 的双语稿《Kirti Joshi 并未证出推论 3.12 和 abc 猜想》（本地审计文本版本 97c322dcd6d2e3f9777a7ee1c24758701f701fdc），特别是有限处体积下界及相邻 Θ 值的两节。下文给出可重做的反例数据、定义和归约。原始比较取 Joshi III v4 的 Theorem 9.11.1 和 Corollary 9.11.1.1，原始 Θ 级数取 Joshi II。LANA 的形式化规格可用于核对后续结果所需的输入。[Joshi II](https://arxiv.org/abs/2303.01662) · [Joshi III v4](https://arxiv.org/abs/2401.13508v4) · [Joshi IV](https://arxiv.org/abs/2403.10430) · [LANA 固定版本](https://github.com/LANA-Project/iut4-sec1/tree/a7551d2f575b7e462cf9e82c587d9c6308e7b15c)

| 任务 / Tasks | 交付的数学输入 / Mathematical input |
| --- | --- |
| JA-0001–0008 | 核对印出的符号、两个 5 进处、张量平衡与 Haar 归一。 Audit the sign, the two places over five, tensor balancing and Haar normalization. |
| JA-0009–0017 | 证明缩放对数等距，求实际双边级数与相邻比值的赋值。 Establish the scaled-log isometry and compute valuations of the bilateral series and adjacent ratios. |
| JA-0018–0028 | 在 29 进域算三个喷射，恢复三维商格，量出高重数族的缺额。 Compute three 29-adic jets, recover the three-dimensional quotient and measure the deep-family deficit. |
| JA-0029–0039 | 计算整层取迹、取整损失、Fourier 零化子和次数加权总误差。 Compute whole-lattice traces, rounding, Fourier annihilators and the degree-weighted loss. |
| JA-0040–0045 | 核对标记运输、有限层 Kummer 类、给定陪集测试与 Haar 占比。 Check marked transport, finite-level Kummer classes, prescribed coset tests and Haar density. |
| JA-0046–0056 | 对同一包络消元，比较两种见证系数，检验 Frey 局部 Szpiro 族。 Eliminate the common hull volume, compare witness coefficients and test a local Szpiro family. |
| JA-0057–0066 | 连接无穷处高度与根基，分别冻结固定指数及全部 ε 的目标。 Relate archimedean height to the radical and distinguish the fixed exponent from the full ε-family. |

## 为什么需要新包络

设坏处非空，各处的 $a_w=|q_w^{1/(2\ell)}|$ 都在 $(0,1)$ 内。印出推论右端 $-\sum_w\log a_w$ 严格为正，左端 $-|V|/m$ 对任一实数对数体积 $V$ 都非正。另一个独立检验使用 $k=\mathbb Q(\sqrt[3]{2})$、$J=\sqrt[3]{2}/5$。模 5 有 $X^3-2=(X-3)(X^2+3X+4)$，两个处的剩余次数为 1、2，约化节点的切线为 $y=0,-x$。把标量 5 放入两个不同张量槽得到同一格 $5M$，原带权赋值却分别为 $1/5$、$1/25$。修订以有限 étale 代数 $T$ 的整闭包为基准，取 $\mu(\mathcal O_T)=1$ 及 $\nu=(\dim T)^{-1}\log\mu$。张量乘法行列式固定各槽的次数权重。

## 三个局部见证与它们的适用范围

对奇素数取 $p^*=p$，对 2 取 $p^*=4$。缩放坐标为 $\tau_p(x)=\log_p(1+p^*x)/p^*$。在同一个带标记域内，Joshi II 的双边级数在 $u=r^j\zeta$ 的唯一主导指标为 $-1$。先计算 $\xi_j=\theta_M(\zeta)/\theta_M(r^j\zeta)$，再对相邻值取商，可恢复一次幂的范数。把商送入实际的 Kummer 像时，需验证主单位 $1+p^*(\xi_j/\xi_{j-1})$ 在指定标签中可取得。

取 $\pi^{14}=29$、$\ell=7$，令 $W=\pi\mathcal O$、$L_0=\pi^4\mathcal O$。$W/L_0$ 的坐标是 $\pi,\pi^2,\pi^3$。十四个根分支的像共线，指数为 $29^2$。JA-0022–0024 从双边级数和对数计算 $\tau(\pi),\tau(\xi_2),\tau(u_2)$ 的坐标，其中 $u_2=\xi_2/\xi_1$。按行写下后为 $(1,0,0)$、$(0,1+\zeta^2,0)$、$(1,0,\zeta^2)$。JA-0028 将这三点和 $L_0$ 提升回整个一次幂格。改取 $r_t=29^t\pi,\ t\ge1$ 时，$r_t^4\mathcal O\subseteq29r_t\mathcal O$。模 $29r_t\mathcal O$ 剩下十四个方向，三个任意见证的缺额至少为 $29^{11}$。

这里有三个需要分别定义的几何对象，分别是实际允许的 Kummer 像、它的加法生成子群、逐分量理想包络。JA-0042 的前提要求三个见证来自**同一个标签**。要将局部计算用于 III，仍需从 III 的允许映射构造三个成员资格，并证明上界量的正是所得包络。单点的迹还可能消失。整层迹的指数 $\lfloor(n+d)/e\rfloor$ 来自逆不同理想，消去 $d$ 后的取整代价每处小于一层。JA-0032 保留了一个固定 337 处的检验。在 $q=337^{42N+30},\ e=7,\ d=6$ 的三槽逐元组模型中，整格下界超过旧上界 $(9N+2)\log337$。

## 指定 Fourier 测试与全局误差

对实际可测加法子群 $C$，先证 $L_0\subseteq C$。在 $G=W/L_0$ 上取 $H=(C\cap W)/L_0$。则 $|H^\perp|=[W:C\cap W]$，在 $\nu(W)=-Q_p$ 的归一化下得到 $\nu(C)\ge -Q_p-\log|H^\perp|/\dim T$。可测区域也可用相对占比 $\rho>0$ 支付 $-\log\rho/\dim T$。JA-0044 覆盖任意有限阿贝尔商，JA-0045 在指定的循环商上给出 Parseval 占比公式。若借用 Levent 工程的 Θ 提升，还要把实际允许像的指示函数送入可用的测试空间，在同一 Haar 归一化下控制其 Fourier 系数。这个匹配是独立的几何输入。[Heisenberg 平移的条件与公式](https://github.com/leanprover-community/riemann-hypothesis/blob/fcb6eac7534875d32d68030967e2deae6d686151/src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ThetaKernelSplitPlacesEqJetClassicalThetaStatement.lean#L1335) · [Rallis 范数公式的条件](https://github.com/leanprover-community/riemann-hypothesis/blob/fcb6eac7534875d32d68030967e2deae6d686151/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/ThetaLiftPeterssonNormEqRallisIntegral.lean#L972)

在线性下界和平方上界都作用于同一 $R$ 时，令 $b=(\ell+1)/4$、$A=\ell(\ell+1)/12$。由 $-bQ-\delta\le R\le-AQ+U$ 得

$$
  \frac{2\ell Q}{6}\le k_\ell(U+\delta),\qquad
  k_\ell=\frac{4\ell}{(\ell-3)(\ell+1)} .
$$

JA-0055 可先在奇坏处重数至多为 $M$ 的族上证明判别式的局部对数和至多为 $2M\sum_{p\in S}\log p$。JA-0060 则逐项列明升级到 Frey 高度所需的同一包络比较、无穷处误差和根基预算。JA-0061 要对每个辅助素数 $\ell\ge7$ 取得统一于**所有三元组**的上界。单点输入 JA-0066 固定 $\ell=7$。JA-0064 由此推出指数 $15/8$。允许按 $\varepsilon$ 先选 $\ell$ 并固定常数，再使用 $c_4$ 高度比较，才得到 JA-0063 通往父题的归约。高重数坏处的补偿、上界对实际包络的适用性和统一的高度估计均需新的证明。

## Working from the English task queue

Independent starting points include the sign test JA-0001, the local log dominance estimate JA-0009, the fixed 29-adic residue pivots JA-0019, the trace-ideal exponent JA-0029 and the Frey discriminant JA-0052. JA-0028 uses the actual theta and logarithm series and states the residue-lifting hypothesis explicitly. JA-0042 specifies the further membership evidence needed at a common ATS label.

The sufficient reduction JA-0063 uses JA-0061, JA-0062 and JA-0058. It first fixes an auxiliary prime depending on ε, then uses one constant for every coprime positive triple. JA-0059 asks only for one fixed exponent. To obtain either estimate from ATS, contributions at finite and infinite places must be controlled on the same marked hull, with a global bound in terms of the full radical.

## 逻辑强度与待验证的桥 / Logical strength and missing bridges

令 $H=\tfrac12\log(16(a^2+ab+b^2))$。JA-0061 与完整 abc 等价。正向使用 JA-0063。反向固定 $\ell$，对 abc 取 $\varepsilon=k_\ell>0$，并用 $H\le\log(a+b)+\log4$。JA-0066 只要求 $\ell=7$ 的高度界，依同样的高度比较，它与固定指数 $15/8$ 的 abc 界等价。JA-0064 只使用这个单点输入和 JA-0058，因此可独立接到 JA-0059。

Let $H=\tfrac12\log(16(a^2+ab+b^2))$. JA-0061 is equivalent to full abc. For the forward direction, use JA-0063. For the converse at a fixed $\ell$, apply abc with $\varepsilon=k_\ell>0$ and use $H\le\log(a+b)+\log4$. JA-0066 asks for the height bound at $\ell=7$. The same height comparison makes it equivalent to the abc bound with fixed exponent $15/8$. JA-0064 uses this one input and JA-0058, and gives a route to JA-0059.

第一座桥须在实际 ATS/Kummer 数据上选定一个标签和一个允许像，构造三个 Θ 见证的成员资格，再调用 JA-0042。应先在 $\ell=7,p=29$ 的模型检查这些成员资格，同时用 JA-0027 的深层秩亏测试构造的适用范围。第二座桥须在实际 Frey 家族定义同一个标记包络，用两条体积界估计它，并对高度和取整误差证明统一的根基预算。JA-0060 的实值函数消元可用于最后一步。

For the first bridge, fix a label and an allowed image in the actual ATS/Kummer data. Construct the three theta memberships, then apply JA-0042. Start with the model at $\ell=7,p=29$. Use the rank deficit in JA-0027 to test where this construction applies. For the second bridge, define one marked hull for the actual Frey family. Prove both volume bounds for that hull and a uniform radical budget for the height and rounding losses. Use the elimination in JA-0060 once these inputs are available.
