# 第三批的因子线与深弧系数 / Factor lines and deep-arc coefficients

## 第三带的二点能量

固定正整数因子 $a,b$ 与目标 $n$，令 $g=(a,b)$。仅 $g\mid n$ 的纤维有整数解。取一组 Bézout 系数 $aA+bB=g$，令 $x=(n/g)A, y=(n/g)B, h=b/g, k=a/g$。在盒 $[l,r]\times[u,v]$ 内，参数 $i$ 同时满足

$$
\max\{\lceil(l-x)/h\rceil,\lceil(y-v)/k\rceil\}\le i\le
\min\{\lfloor(r-x)/h\rfloor,\lfloor(y-u)/k\rfloor\}.
$$

FW-9001 在这个整数区间精确求和，允许空区间和每个点不同的权。FW-9002 在 $r,s>U$、$ar+bs=n$ 的真实纤维保留两个截断 Möbius 除数和及两个 Mangoldt 权。两点行列式的绝对值为 $(n/g)|i-j|$。取行列式上界 $H$，每个点至多有 $2\lfloor Hg/n\rfloor$ 个不同邻点。因此近对角贡献以逐纤维真实平方权之和为界。举例，$a=6,b=10,n=100$ 时每个非零行列式至少为 50，所有 $H<50$ 的近对角非对角和都为零。远壳、纤维间的总损失以及宽弧扣除仍需各自的算术估计。[既有第三带与纤维分解](https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/2495)

## 给同一偶数的整行系数一个有限模型

固定 $n$ 的素数权、截断和宽弧遮罩，取 $W=[n,2n]\cap2\mathbb Z$。对每个 $m\in W$ 用同一组 $K=(n+1)^6$ 个等宽中点采样，记得到的实深弧系数为 $a_m$。FW-9003 把可能跨界的闭格数控制在 $4\sum_{q\le Q_1}(q+1)$。FW-9004 用这一计数和光滑格上的导数界控制整行的绝对平方误差，并核验均匀概率权的平方预算。

具体地，在光滑格上，被积函数的振幅至多 $O(n^2\log^2(2n))$，导数至多 $O(n^3\log^2(2n))$。中点误差对每个 $m\le2n$ 一致。跨界格合计长度至多 $O(n^{2/3}/K)$。平方后对至多 $n+1$ 项求和，足以争取误差半径 $1/n$。模型的均值与 $a_n$ 之间仍须在每个充分大的偶数取得单侧比较。将模型计算精度提高，仍需算术输入来确定该差的符号。这个逐点估计沿用原反尖峰挑战。共享误差球、最优权与移动二阶矩分别见已有工作。[共享误差](https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/2634) · [最优权](https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/2507) · [移动二阶矩](https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/2840)

## 第一章其他交接项

- Round 8 的 2A/2B 推导仍需同一份完整参数表、互素条件、零频消去及全区间误差预算。六个核对点合并为一份文献交接。
- 中心窗一阶、二阶矩、上界筛与正密度结果复用 TH-0023–0029。由这些平均结果恢复给定偶数的正性仍需逐点传递。
- Θ 路线的下一项算术输入是同一真实素数权的正负局部测试、归一化及其误差。原谱假设 R 已退出。第三带远壳的指数也须由真实系数确定。[第二批路线](https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/2495)

## English

FW-9001 transports a weighted box to the Bézout interval, including empty fibers. FW-9002 retains the actual squared arithmetic weights and the determinant cutoff on band three. The far shells still require cancellation at the same target. FW-9003 counts cells crossing the fixed wide-arc mask. FW-9004 uses the midpoint rule on a common grid for the entire even row and checks the square budget of the uniform weights. Comparing that finite model's mean with its value at the target remains the open arithmetic step. The Round 8 handoff needs the full parameter ranges and summed errors. The density and theta inputs retain the scopes of their original statements.
