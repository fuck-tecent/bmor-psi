# 差二的素数相关 · Twin primes at gap two

父题 **TP-0054** 要求对任意自然数 $B$，找到 $p>B$，使 $p$ 和 $p+2$ 都是素数。分站把 SeungJu Lee 的固定偶差分析和 Levent Alpöge 工程中的移线、显式公式与 Θ 提升方法用于这一指定平移。拆分依据包括《彻底证明孪生素数猜想的分析》与《进一步扩张 Theta 提升以证明更多数论猜想的分析》。每个编号在目录中都有独立的 Lean 声明和双语提示。[任务目录](problems.json) · [Lee 的固定偶差论文](https://arxiv.org/abs/2610.32672) · [固定版本的 RH 与 Dirichlet 声明](https://github.com/leanprover-community/riemann-hypothesis/blob/fcb6eac7534875d32d68030967e2deae6d686151/src/Main.lean#L43)

| 任务 / Tasks | 交付的数学输入 / Mathematical input |
| --- | --- |
| TP-0001–0006 | 计数窄窗中的高次幂并抽取真素数对。 Count proper powers and extract a genuine prime pair in a narrow window. |
| TP-0007–0017 | 隔离频带并精确计算两个实际时间矩之差。 Isolate the gap-two band and compute the difference of two actual time moments. |
| TP-0018–0026 | 求正对角常数，保留零点重数与相位，比较差一和差二。 Compute the diagonal, retain multiplicities and phases, and compare gaps one and two. |
| TP-0027–0039 | 求短除数主项，把长除数换成余因子，在同一尺度合并。 Evaluate short divisors, switch long divisors to cofactors and recombine at the same scale. |
| TP-0040–0043 | 用长度 1、2、3 的窗口消掉平方对角。 Cancel the squared diagonal using windows of lengths one, two and three. |
| TP-0044–0054 | 计算局部掩码、指定平移的 Fourier 相位与带符号能量。 Compute local masks, the Fourier phase for the prescribed shift and its signed energy. |

## 窄窗中究竟要超过多少污染

令 $W_X=\{n:X<n<51X/50\}$，令 $M_X=X^{-1}\sum_{n\in W_X}\Lambda(n)\Lambda(n+2)$。在同一个和中只保留至少一端为合数的项，得到 $E_X$。Mangoldt 权的支撑意味着每个坏项至少一端是高次素数幂。候选幂有 $O(\sqrt X\log X)$ 个，每个可在两端各出现一次。TP-0002 的预算是 $E_X\le C e_X$，其中 $e_X=\log^3(2+X)/\sqrt X$。

TP-0006 的两个输入是 TP-0002 和 TP-0005。先从第一个输入取 $C$，再在任意起点以外取 $M_X>C e_X$ 的尺度。严格正的差值给出一个真素数对。这个判据允许 $M_X$ 随尺度衰减。双时间矩使用的光滑权支撑在同一窄窗，TP-0015 通过权的一致上界将余量送回 $M_X$。

## 两个时间矩与零点余量

TP-0013 固定具体光滑函数、$T=2\pi X$ 和同一个 Dirichlet 多项式。取 $b$ 为支撑在 $[-1/40,1/40]$ 的偶凸起函数，用卷积 $b*b$ 在 $0,\pm1/5$ 的平移组成 $H$。对 $X\ge1000$，$X\log(1+2/n)$ 落在以 2 为中心、半径 $1/20$ 的开区间。差一和至少三的整数间距避开该边带。两个非负时间权的差因此精确提取差二。

Lee 从一致的 ζ 比值猜想导出主项。本台把实际双矩的单侧余量单列为 TP-0014。RH 可将非平凡零点放在新线 $9/16$ 左方。走双 Mellin 微分均值路线时，误差除以 $T$ 后的幂次为 $\vartheta-7/8+\varepsilon$。TP-0017 核算该阈值，一致微分均值仍是独立的解析输入。[Lee 的 Fourier、Mellin 推导](https://arxiv.org/abs/2610.32672) · [Levent 工程的截断显式公式](https://github.com/leanprover-community/riemann-hypothesis/blob/fcb6eac7534875d32d68030967e2deae6d686151/src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedExplicitFormula.lean)

TP-0025 使用 ζ 在 $1/2+i\gamma$ 的实际零点阶 $m$，在 $|\gamma-t|\le\log^2(2+T)$ 截尾。平方有 $m^2$ 个有序配对，扣掉 $m$ 个自配对后，同高异编号仍有 $m(m-1)$ 项。任务要求在无界尺度证明 $d_2+R_2(X)>\kappa>0$。TP-0026 须把该量接到实际双矩，计入对角主项、截尾和极点误差。差一对照也有正谱对角，但算术侧的偶数一端只能是二的幂。这个对照检验所用估计能否分辨指定间距。

## 长除数、跳跃与 Θ 测试

TP-0039 使用 TP-0035、TP-0038 与 TP-0002。在 $D=\lfloor X^{1/3}\rfloor$ 切开 $p+2$ 的除数，短段极限 $2C_2/50$ 中的 $1/50$ 来自硬截断窗长。短段可走 Bombieri–Vinogradov 平均。TP-0030 另在显式 Dirichlet GRH 前提下追踪单模数误差。长段需要保住 $\mu(d)$ 与 $md-2$ 素性之间的符号。若 $p+2=rs$ 是两个不同素数的积，四个除数项恰好抵消。

TP-0041 用补零的 Mangoldt 序列得到 $F_X(3)-2F_X(2)+F_X(1)=2C_2(X)$，其中 $C_2(X)$ 是有限差二相关和。TP-0043 寻求的超平方根增益须覆盖对角误差、差一贡献和高次幂污染。前段的 $C_2$ 则是 Euler 乘积常数。

TP-0053 使用 TP-0052。将窄窗的素数对数权补零到 $\mathbb Z/(2X+5)$，则指定字符相位的实部乘以 Fourier 能量，求和后恰是模数乘以差二内积。补零排除了从末端回绕形成的配对。TP-0052 要求该指定能量在无界尺度严格为正。走自守路线时，需在同一模型、同一 Haar 归一化下为 $b_X$ 与 $n\mapsto b_X(n+2)$ 构造两个测试，证明算术匹配的误差界，再在两个 Rallis 值之差中保住符号。Levent 工程的 Heisenberg 展开和 Petersson 范数公式列出了各自的相容条件。[Heisenberg 平移展开](https://github.com/leanprover-community/riemann-hypothesis/blob/fcb6eac7534875d32d68030967e2deae6d686151/src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ThetaKernelSplitPlacesEqJetClassicalThetaStatement.lean#L1335) · [Rallis 公式及前提](https://github.com/leanprover-community/riemann-hypothesis/blob/fcb6eac7534875d32d68030967e2deae6d686151/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/ThetaLiftPeterssonNormEqRallisIntegral.lean#L972)

## Working from the English task queue

For an independent start, TP-0001 bounds proper powers, TP-0008 isolates the frequency of a gap of two, TP-0020 counts repeated-zero labels and TP-0045 computes the local mask at a prime.

Three explicit reductions reach TP-0054. TP-0006 subtracts the proper-power contribution on an unbounded sequence. TP-0039 adds the short-divisor limit to a strict signed lower bound for long divisors before removing proper powers. TP-0053 uses signed Parseval and zero padding to turn positive prescribed energy into two actual primes. A spectral proof still needs a construction of the prescribed tests and control of their mixed term at the same gap and scale. The Lean statements include the RH or Dirichlet GRH hypotheses wherever the reduction uses them.

## 逻辑强度与领取 / Logical strength and task selection

TP-0052 与 TP-0054 等价。补零消掉回绕后，能量为正当且仅当窗口含有孪生素数。反向给定任意足够大的孪生对 $p,p+2$，取 $X=p-1$。当 $p>151$ 时，$50(p+2)<51X$，两端都落在窗口内。自守路线若要推进，须构造匹配同一算术序列的两支测试，并控制两支比较误差及其差的符号。

TP-0052 is equivalent to TP-0054. Zero padding removes wraparound, so the energy is positive precisely when a twin pair lies in the window. For the converse, take a sufficiently large twin pair $p,p+2$ and set $X=p-1$. If $p>151$, then $50(p+2)<51X$ and both primes lie in the window. An automorphic approach needs two tests for the same arithmetic sequence and control of their comparison errors and the sign of their difference.

TP-0035 是已知工具的形式化里程碑。Bombieri–Vinogradov 在 $D=\lfloor X^{1/3}floor$ 控制加权进程误差，定量素数定理给出无条件 Möbius 矩，再经绝对收敛的卷积识别硬截断极限。TP-0034 的 RH 版本不能直接作为无条件输入。TP-0026 则要在 RH 和 TP-0025 的条件下验证实际谱与双矩的比较。这两题须显式领取。TP-0001 可复用主站的有限计数 L-goldbach-power-index-count。TP-0047、0049 保留为组合路线中的引用，分别由一般形式 QP-0050、0042 特化。

TP-0035 is a formalization milestone. Bombieri–Vinogradov controls the weighted progression error at $D=\lfloor X^{1/3}floor$. The quantitative prime number theorem supplies unconditional Möbius moments. An absolutely convergent convolution then gives the cutoff limit. TP-0034 gives the version under RH. TP-0026 compares the actual spectrum with the moments under RH and TP-0025. Both tasks require explicit selection. For TP-0001, reuse the finite count L-goldbach-power-index-count. In the reduction, TP-0047 and TP-0049 are references to special cases of QP-0050 and QP-0042.
