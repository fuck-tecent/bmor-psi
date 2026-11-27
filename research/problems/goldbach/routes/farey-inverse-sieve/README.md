# Farey 分母对与逆元筛

固定偶数 \(n\ge64\)，取整数中心窗 \(I=[\lceil n/3\rceil,\lfloor2n/3\rfloor]\)。阶数 \(n-1\) 的 Farey 序列升到阶数 \(n\) 时，既约分数 \(a/n\) 插入一对相邻分数之间。若左分母为 \(u\)，则右分母为 \(n-u\)，且 \(au\equiv1\bmod n\)。反过来，由 \(u\) 的标准逆元 \(a\) 可恢复两侧分子和行列式。Athreya–Cheung 把 Farey 相邻分母归一化成 BCZ 首返映射的周期轨道。本路线固定其中的一条插入层，再研究实际分母及其逆元标记。固定连续函数的轨道等分布本身允许这条层没有双素数点。[Athreya–Cheung，定理 1.1](https://arxiv.org/abs/1206.6597) · [#2509 的相邻格与分母构造](https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/2509)

对分子窗 \(J\subseteq[0,n-1]\)，令 \(A_d(J)\) 计数满足下列条件的 \(u\in I\)。要求 \(u\) 与 \(n\) 互素，\(u^{-1}\) 的标准代表落在 \(J\)，且 \(d\mid u(n-u)\)。可用 \(\lfloor3a/n\rfloor=0,1,2\) 将全窗拆成三个整数区间。对与 \(n\) 互素的平方自由数 \(d\)，每个素因子给出 \(0,n\bmod p\) 两个根。全分子窗的主项是
\[
|I|\,\frac{\varphi(n)}n\,\frac{2^{\omega(d)}}d.
\]
逐根用 Möbius 反演和 CRT 给出 \(2^{\omega(d)}\tau(n)\) 的余项。这个估计是衡量分窗方法的对照。逆元窗使用的多项式同余和完全 Fourier 求和直接作用于同一个 \(n\)。

分窗时写 \(u=b+dt\)，设 \(0\le b\le h<n\)，其中 \(h\) 是分母区间上端。取 \(s,c\in[0,n-1]\) 使 \(ds\equiv b\) 且 \(dc\equiv1\bmod n\)。由于 \(ds=b+kn\) 且 \(0\le k<d\)，有 \(d(t+s)=u+kn<dn\)。平移后的真实窗口落在单个标准周期，且 \(a(t+s)\equiv c\bmod n\)。每根使用一个模双曲线矩形。计数误差至多为矩形余项 \(E\) 加一，后一项来自进程长度取整。代入矩形界 \(E\ll_\varepsilon n^{1/2+\varepsilon}\) 后，利用 \(\sum_{d\le D}2^{\omega(d)}\le D(1+\log D)\) 可在 \(D=\lfloor n^{1/4}\rfloor\) 取得 \(O_\varepsilon(n^{3/4+\varepsilon})\) 的绝对余项和，其中对单矩形先取较小的指数误差。[Shparlinski，§3.1 定理 13 及式 (10)](https://arxiv.org/abs/1103.2879)

取固定 \(U\ge 8\)，用整数筛点 \(z_0=\lfloor n^{1/U}\rfloor\)、\(z_1=\lfloor n^{1/3}\rfloor\)、\(z_2=\lfloor\sqrt n\rfloor\)。全窗幸存数 \(S(z)\) 取 \(u\) 与 \(n\) 互素、\(\minFac(u(n-u))>z\) 的分母数，\(V(z)\) 取 \(|I|\varphi(n)/n\) 乘上 \(p\le z,\ p\nmid n\) 的各个 \(1-2/p\)。大于 \(z_2\) 的坏素数至多有一个。与 TH-0072 所用的局部因子比较可得
\[
V(z_2)\ge\tfrac23 |I|\,M(z_2)^2,\qquad
V(z_0)\le 2\big(M(z_0)/M(z_2)\big)^2 V(z_2)
\]
其中 \(M(z)=\prod_{p\le z,\ p\ {\rm prime}}(1-1/p)\)。Mertens 乘积估计给出终筛主项的 \(n/(\log n)^2\) 尺度及 \(O(U^2)\) 的两筛点比。配合全窗 CRT 余项和二维筛基本引理，目标是对每个充分大的固定 \(U\) 得 \(S(z_0)\ge V(z_0)-V(z_2)/8\)。[Friedlander–Iwaniec，*Opera de Cribro*](https://doi.org/10.1090/coll/057)

令 \(L_i\) 计全窗最小素因子落在 \((z_{i-1},z_i]\) 的点。由同一个最小素因子唯一归类，\(S(z_2)=S(z_0)-L_1-L_2\)。三个挑战估计若在同一尺度均成立，则 \(S(z_2)\ge V(z_2)/8>0\)。初筛和中段分别对所有充分大的固定 \(U\) 给出阈值，可选同一个 \(U\) 再取所有阈值的最大值。两侧分母均大于 \(\sqrt n\)，故终筛幸存者给出真素数对。沿用 TH-0011、TH-0012 加回对角项，并用原 \(\mathrm{log\mbox{-}correlation\mbox{-}iff}\) 对接大偶数表示。原全称目标还包含有限范围。

中段挑战控制满足两侧粗糙性条件的真实最小素因子和，低水平分窗余项只覆盖其中能够放入该水平的部分。末段挑战把命中侧写成 \(pq\)，其中 \(p\le q\) 均为素数，保留另一侧没有小于 \(p\) 的素因子。两侧的逆元条件分别是 \(apq\equiv1,-1\bmod n\)。平方项 \(p=q\) 对每个方向至多 \(\lfloor\sqrt n\rfloor\) 项，剩下的是两个不同素因子与另一分母的同时分布。三项挑战预算严格合成正余量。每项单独通过只给相应的初筛或损失估计。

## Frozen tasks and reuse

Every published statement fixes the same target integer before counting residues or prime factors. The full-window calculation removes the numerator tag. The rectangle calculation retains it and allows a genuine subinterval. All estimates in the final comparison must hold for the same numerator window.

| Draft | Task ID suffix or reused input | Work |
| --- | --- | --- |
| HD1 | farey-insertion-inverse, farey-inverse-full-weight | Construct the new numerator from the left denominator and recover the two neighbours. Sum over the inverse fibres and use the accepted diagonal correction TH-0012. |
| HD2 | farey-coprime-progression-count, farey-full-sieve-remainder | Add the coprimality mask to the accepted two-root and CRT counts TH-0030 and TH-0031. Get an interval error for each divisor, then sum over the roots. |
| HD3 | farey-hyperbola-shift, farey-hyperbola-rectangles, farey-hyperbola-sieve-transfer, farey-sieve-root-total | Produce one canonical rectangle per root. Apply the composite-modulus literature bound and sum the root-weighted discrepancies. |
| HD4 | farey-sieve-terminal-floor, farey-sieve-cutoff-ratio | Account for prime factors above the terminal cutoff and compare two sieve products. Reuse the finite Euler-product bounds. |
| HD5 | farey-initial-sieve-lower | Formalize the dimension-two lower-bound sieve with its error stated on the terminal scale. This opt-in task requires analytic infrastructure. |
| HD6 | farey-first-hit-middle | Open challenge for the entire middle band. It retains the least-factor restriction on both sides. |
| HD7 | farey-late-first-hit-factor-switch, farey-late-prime-square-loss | Compute the two semiprime sums with the same inverse labels and bound their square terms. |
| HD8 | farey-first-hit-late | Open challenge for the late band. The rough cofactor restriction applies to the opposite denominator. |
| HD8 input | farey-cube-sqrt-density-ratio | Determine the limiting ratio of the two sieve volumes for the same even target. |
| HD9 | farey-terminal-survivors, accepted log-correlation-iff | Prove the exact terminal sieve identity. The first-hit partition and budget addition give the conditional combination above. |

The finite checks covered 12,151 insertions, 1,257 progression examples including 67 shifts ending at the last residue, and 675 inverse-labelled sieve windows. The window checks included 238 prime-square hits. The asymptotic rectangle estimate, lower-bound sieve and first-hit inequalities are Lean tasks.

### 末段筛主项的比值 · Late cutoff ratio

设 $z=\lfloor n^{1/3}\rfloor$、$y=\lfloor\sqrt n\rfloor$。从 $V_n(y)/V_n(z)$ 中消去公共因子，留下 $z<p\le y$ 且 $p\nmid n$ 上的乘积。Mertens 素数倒数和公式给出这段的倒数和趋于 $\log(3/2)$。其中整除 $n$ 的素因子个数有一致上界，删去它们的误差趋于零。于是 $V_n(z)/V_n(y)\to 9/4$，HD-8015 右侧除以 $V_n(y)$ 后趋于 $7/4$。左侧仍需在每个充分大的偶数上控制另一分母满足粗糙条件的首次命中数。

For the same even target, cancel the common local factors below the cube root. The reciprocal sum of the primes between the two cutoffs tends to $\log(3/2)$. The number of primes in this band dividing the target is uniformly bounded, and the sum of squared reciprocals tends to zero. The terminal product relative to the cube-root product therefore tends to $4/9$. This determines the limiting allowance for HD-8015. Bounding the actual late first-hit count on that scale remains open.
