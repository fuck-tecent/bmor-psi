# Beaumont 框架的工具命题 / Tools for Beaumont’s framework

来源为 Herbert A. Beaumont, *Toward a Geometric–Dynamical Reformulation of the Goldbach Partition Function* (2026), §§4–9。本文档提出有限圆周模型来检验原稿所需的几何素性判据、同步命中和误差回收。

一条整数速度为 a 的离散圆周轨道通过反复累加 a 产生。素模数下每个非零步长遍历全圆。这个判据用到了模数本身；独立于整数标签的素性模型仍待构造。对于反向运动，法向位移是两个速度的和。无混叠区间和半单位误差界分别处理精确共振和近共振。同步反例检查两条边际轨道各自均匀时，共同命中仍能失败。

工作猜想只要求在三个相邻偶数中至少命中一个，且第一步长在中央区间。它会排除连续三个漏点，允许单个偶数仍无表示。计算可帮助排查模型，领取任务的交付物为对冻结声明的 Lean 证明或证伪。原猜想终点继续沿用既有任务。

These tasks separate transitivity, synchronization, and arithmetic recovery. The local three-target conjecture permits missed individual targets. Density only ensures hitting an open target; exact recovery needs a separate separation estimate.

- `L-goldbach-beaumont-primitive-cycle` — 用圆周有限步长的传递性检测素性 / Detect primes by transitivity of every nonzero circular step
- `L-goldbach-beaumont-cycle-fiber` — 定量计算圆周步长的返回重数 / Count returns for a step on a finite circle
- `L-goldbach-beaumont-resonance-window` — 在无混叠窗口中从碰撞恢复精确和 / Recover an exact sum from a collision in an alias-free window
- `L-goldbach-beaumont-near-hit-window` — 有安全边距时把近共振转为邻近整数和 / Transfer near resonance to a nearby integer sum with a safety margin
- `L-goldbach-beaumont-marginal-obstruction` — 证伪：两个粒子各自遍历全圆仍可能永不相遇 / Refute collision from two individually uniform marginals
- `L-goldbach-beaumont-quotient-obstruction` — 证伪：固定模数的相位标签不足以辨认素数 / Refute primality detection from a single fixed modular phase
- `L-goldbach-beaumont-dense-open-hit` — 把稠密轨道用于可命中的开靶区 / Transfer dense-orbit information to an open target
- `L-goldbach-beaumont-dense-exact-obstruction` — 证伪：稠密和闭包命中不能推出精确命中 / Refute exact hitting from density and closure alone
- `L-goldbach-beaumont-three-target-window` — 探索猜想：中心步长在三个相邻偶数中至少命中一个 / Conjecture: a central step hits one of three consecutive even targets
- `L-goldbach-beaumont-perturbed-clock-gap` — 半单位误差预算下整数标签唯一 / Recover the unique integer label with half-unit error margins
- `L-goldbach-beaumont-central-gap-density` — 相邻两个偶数都缺中央表示的起点密度趋零 / Vanishing density of adjacent central misses
- `L-goldbach-beaumont-central-imbalance-budget` — 相邻靶区共享的表示重数下界 / Lower-bound multiplicity shared by adjacent targets
- `L-goldbach-beaumont-central-local-prediction` — 猜想：相邻中央命中的局部主项具有低均方误差 / Conjecture: low mean-square error for adjacent central arrivals
- `L-goldbach-beaumont-central-prediction-transfer` — 用已证能量引理把局部预测转成双漏密度上界 / Transfer a local prediction to a double-miss bound
- `L-goldbach-beaumont-one-sided-hole-cluster` — 猜想：平方根长度短窗中的中央漏点不会聚集 / Conjecture: central misses do not cluster in square-root intervals
- `L-goldbach-beaumont-alternate-normal-shift` — 猜想：正比例的连续三靶都具有中央表示 / Conjecture: a positive proportion of adjacent triples all have central hits
- `L-goldbach-beaumont-scaled-deletion-survival` — 猜想：中央命中对删除长步长稳定 / Conjecture: central coverage survives long-step deletion
