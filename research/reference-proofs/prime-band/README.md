## 大素数项的次弧积分可以删去哪段频率

设 **$n$** 是目标偶数。仓库给整数 $p$ 赋予权重 $h_n(p)$：若 $p$ 为素数且 $p^3>n$，权重为自然对数 $\log p$，其余取零。把主弧分母上限记为 $Q=\lfloor\log_2(n+2)\rfloor^2$。对满足 $0\le p,r\le n$ 的一对索引，它在大素数项的次弧积分中的整数频率是 $p+r-n$。（[目标命题](../../gaps.json)，[积分展开](BandPairs.lean)）

令 $L=1+\lfloor\log_2(n+2)\rfloor$，$K=\lfloor n/L^4\rfloor$。在 $n>2Q^2$ 时，主弧互不重叠。把满足 $0<|p+r-n|\le K$ 的项在次弧上的贡献之和记为 $R(n)$，则有

$$
|R(n)|\le 4\log(4)\,n\,\frac{(1+2\log L)^2}{L}.
$$

**可以从原命题中删去这一整段非零频率。** 当 $n$ 增大时，$K$ 趋于无穷，$R(n)/n$ 趋于零。保留 $p+r=n$ 和 $|p+r-n|>K$ 的项后，“对每个 $\varepsilon>0$，对所有充分大的偶数，实部至少为 $-\varepsilon n$”与登记的目标命题等价。剩余频率的下界仍待证明。（[误差界和等价定理](BandReduction.lean)）

### 证明的三个环节

1. 将互不重叠的主弧按既约分母求和。分母为一的弧在单位区间两端各占一部分，周期性将它们合成完整的一条弧。仓库已核验所需的不相交条件和截断参数最终满足该条件的事实。（[弧积分](BandGeometry.lean)，[不相交引理](https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/153)，[尺度引理](https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/196)）
2. 求次弧指示函数的整数傅里叶系数。按频率与分母的公因子展开拉马努金和，对一段频率求绝对值之和，得到只含两个调和和因子的平均上界。（[算术估计](BandArithmetic.lean)，[完整傅里叶系数](BandMask.lean)）
3. 固定第一个索引 $p$ 后，每个正的绝对频率至多对应两个 $r$。用切比雪夫函数控制所有素数权重的总和，再将频率平均上界代入，得到上式。（[素数对估计](BandPairs.lean)，[Mathlib 的切比雪夫上界](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/NumberTheory/Chebyshev.lean#L190)）

### 剩余高频需要控制哪个量

对整数 $k\ge0$，令 $A_n(k)$ 为满足 $|p+r-n|=k$ 的所有有序对的权重 $h_n(p)h_n(r)$ 之和，其中 $0\le p,r\le n$。对分母 $q$，记 $c_q(k)$ 为拉马努金和。令 $D_n$ 为零频贡献，即 $A_n(0)$ 乘以次弧在单位区间内的长度。对整数 $K\le t\le n$，定义**带符号的前缀和**

$$
S_n(t)=\sum_{K<k\le t}A_n(k)\sum_{q=1}^Q c_q(k)
    \sin\!\left(\frac{2\pi kQ}{qn}\right).
$$

在 $n>2Q^2$ 时，删去小频带后剩余的积分实部恰好为 $D_n-H_n$，其中

$$
H_n=\frac1\pi\left(\frac{S_n(n)}{n}
     +\sum_{K<k<n}\left(\frac1k-\frac1{k+1}\right)S_n(k)\right).
$$

因此目录中的高高项下界等价于如下估计：对每个 $\varepsilon>0$，对所有充分大的偶数 $n$，有 $H_n\le D_n+\varepsilon n$。这里的 $D_n$ 包含满足 $p+r=n$ 的实际素数对权重；用一个简单的常数替代它需要另行证明。不同位置的前缀和可以有不同的符号，此公式保留了它们各自的权重。（[频率重排、分部求和与等价定理](TailPrefixes.lean)）

### 本地复核

在仓库根目录执行以下命令。检查程序从当前目录清单逐字读取目标命题并比对摘要，为两个既有输入读取已核验的固定版本，随后编译各证明模块。最后一步直接读取目录中 `L-goldbach-bulk-prefix-equivalence` 的完整声明，用等价定理逐字对接该类型，并对所有模块做 Lean 内核重检。（[复核程序](check.py)）

```sh
(cd lean && lake exe cache get)
python3 research/reference-proofs/prime-band/check.py
```
