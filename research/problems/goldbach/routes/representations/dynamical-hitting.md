# 两步素数路径与轨道命中 / Two-step prime paths and orbit hitting

这是既有 representations 路线内的探索。起点为《哥德巴赫猜想的动力系统版本》及英文笔记 *Dynamical Formulations of the Goldbach Conjecture* 第 2–7 节。原笔记给出等价编码。下面的有限图、平方根步长窗口及其估计是据此提出的任务。

For even endpoints in [X,2X], H counts first primes p in [⌊√X⌋,2⌊√X⌋] with n−p prime. The predicted mean scale is √X/(log X)². The moment tasks aim first for a positive proportion of rich endpoints. Coverage of almost every endpoint needs a sharper error estimate. A single missed endpoint remains compatible with either conclusion.

| 分组 | 可检验的产出 |
|---|---|
| 轨道窗口 | 有限窗口匹配加上两侧各一次命中，限制出有限个平移候选，进而判定混合轨道极限。 |
| 模图与整数图 | 构造所有模数可达的反例，精确分离进位和无进位路径，估计折回的路径数。 |
| 矩与算术输入 | 第一矩来自长短两个素数区间。第二矩需要不同小素数平移的共同邻点筛界及位移权重的平均。 |
| 覆盖与稳定性 | 用矩估计推出一批拥有许多见证的偶数，进而容忍删除部分步长。密度趋一另需控制漏点。 |

可以优先攻共同邻点筛界、位移因子均值和窗口漏点密度，当前积分以任务台为准。下列命题均等待参与者提交 Lean 证明。全体偶数的逐点命中沿用既有最终任务。

- `L-goldbach-dyn-window-trap` — 混合柱集把平移时间锁进有限区间 / Trap mixed-cylinder hitting times in a finite interval
- `L-goldbach-dyn-closure-rigidity` — 有限窗口可匹配的混合极限必为原轨道点 / Recover mixed orbit limits from finite-window matches
- `L-goldbach-dyn-modular-mirage` — 所有模数两步可达仍可漏掉指定整数 / Construct a target missed despite reachability at every modulus
- `L-goldbach-dyn-carry-split` — 模图的两步路径精确分成无进位与进位两层 / Split modular two-step paths into two exact carry layers
- `L-goldbach-dyn-carry-reflection` — 把进位层反射成低端整数的路径计数 / Reflect wrapped paths into a low-end integer count
- `L-goldbach-dyn-carry-edge-budget` — 用高端步长数限制伪命中的重数 / Bound wrapped multiplicity by the smaller upper tail
- `L-goldbach-dyn-surplus-certificate` — 模路径数超过伪命中预算时恢复整数命中 / Certify an integer hit from a modular surplus
- `L-goldbach-dyn-incidence-first` — 将两步路径的一阶矩换成逐个小素数求和 / Double-count first arrivals by their small prime step
- `L-goldbach-dyn-interior-box` — 用一个完整素数矩形给路径总量下界 / Embed an interior prime rectangle into the path count
- `L-goldbach-dyn-first-mass` — 平方根步长窗口内的一阶矩下界 / Lower-bound total arrivals with a square-root-scale first prime
- `L-goldbach-dyn-factorial-collisions` — 把碰撞矩分解成不同小素数对的共同终点 / Resolve factorial collisions into shared endpoints
- `L-goldbach-dyn-shift-sieve` — 统一控制两个小素数平移的共同邻点 / Sieve the shared neighbors of two distinct small primes
- `L-goldbach-dyn-shift-factor-mean` — 控制小素数对的位移奇异因子均值 / Bound the mean singular weight over small prime pairs
- `L-goldbach-dyn-path-second-moment` — 平方根步长窗口内的路径二阶矩 / Bound the square-root-window path second moment
- `L-goldbach-dyn-many-rich-targets` — 正比例的偶数拥有许多小步长表示 / Find a positive proportion of endpoints with many witnesses
- `L-goldbach-dyn-thin-window-exceptions` — 探索猜想：平方根步长窗口的漏点密度趋零 / Conjecture: vanishing density of missed square-root-window targets
- `L-goldbach-dyn-deletion-loss` — 删除大步长后有多少富终点会完全失去路径 / Bound rich endpoints destroyed by deleting long steps
- `L-goldbach-dyn-robust-arrivals` — 探索猜想：删去一批大素数步长后仍有正比例命中 / Conjecture: positive coverage survives adversarial long-step deletions
- `L-goldbach-dyn-exception-energy` — 用局部预测的均方误差约束漏点数 / Charge each missed endpoint to local prediction error

## 短窗覆盖 / Local coverage

把平方根素数步长的覆盖定位到每个长度约 X^(3/4) 的子窗。两矩合用可在每窗得到正比例富终点；漏点密度趋零仍需下尾估计。

Localize square-root prime steps to every block of length about X^(3/4). Together the moments give positive rich-target density in each block; vanishing miss density still needs lower-tail control.

- `L-goldbach-dyn-block-first-mass` — 每个四分之三次幂短窗中的素数路径总量下界 / Lower-bound prime arrivals in every three-quarter-power block
- `L-goldbach-dyn-block-collision-budget` — 每个四分之三次幂短窗中的共同终点碰撞预算 / Bound common-endpoint collisions in every three-quarter-power block

## 可对照文献的短窗目标 / Short-window benchmarks

两个待证目标都把一个素数加数留在平方根带 [⌊√X⌋, 2⌊√X⌋]。检索截至 2026-11-27。对照 [Li v8 定理 6、7](https://arxiv.org/html/2308.04458v8#S7)、[Grimmelt 定理 1](https://arxiv.org/abs/1910.05187) 和 [Halupczok 定理 5](https://arxiv.org/html/1212.4406)。Halupczok 要求平均窗长 R 不超过受限加数窗长 Y 的同阶量，并对两个窗的端点相对位置有要求。取小素数窗 Y ≍ √X 时，平方根带与目标窗相隔约 X，端点条件不成立；交换加数后，在大素数上取由目标窗决定的短区间也达不到其 Y ≫ X^(7/12+ε) 的要求。已知短窗素数下界无法在这两道题的超短尺度逐窗使用。已有 X^(3/4) 窗矩估计允许更短的子窗完全漏掉。

- `L-goldbach-dyn-short-restricted-power-saving` — 同一 13/225 窗长下，要求平方根加数约束和漏点幂次节省。取 X=y 并放开加数即推出 Li 定理 6 的密度结论。它还控制每个合法窗的漏点，铺窗后将父题的全区间漏点数压到 O(X^(1−δ)+X^(13/225))。切入口是带局部算术因子的正主项与一次逐窗均方估计。
- `L-goldbach-dyn-ultrashort-restricted-hit` — 同一 26/1075 窗长下，要求至少一个由平方根带素数参与的表示。取 X=y 并放开加数即推出 Li 定理 7 的存在结论。它排除同尺度全漏，且铺窗可得到 Ω(X^(1−26/1075)) 个不同命中。要得到父题的密度结论，还需控制剩余漏点。切入口是对带短窗权的素数二元卷积直接建立正下界。

Both targets are open and retain the square-root constraint. With X=y and that constraint dropped, their conclusions recover Li's Theorems 6 and 7 respectively. The first controls every comparable window at exponent 13/225 and gives a power saving in the exception count. The second rules out wholly missed windows at the shorter exponent 26/1075. The literature comparison establishes the stated improvements over these baselines; priority for the exact restricted statements remains subject to further literature review.
