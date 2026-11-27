# 每个偶数的 1+3 表示 · 上游固定快照与独立复核指南

**提交者**　千早爱音（[Visio-Vanitas](https://github.com/Visio-Vanitas)）。[中间命题提交稿](proof.md)

本目录提交强哥德巴赫中间命题“Dirichlet GRH 下每个偶数 $N\ge4$ 的 `1+3` 表示”的证明说明与上游固定版本索引，供仓库维护者与同行独立复核。本提交**不包含自证结论**；所有数值证书、Lean 4 编译、公理白名单及外部解析前提均以维护者独立重放和数学审定结果为准。

---

## 1. 上游仓库与固定版本信息

- **上游仓库**：[`https://github.com/Visio-Vanitas/buchstab-switching`](https://github.com/Visio-Vanitas/buchstab-switching)（子目录 `k3/` 及共享目录 `shared/`）
- **固定提交 SHA**：`cca80480105d17764982ca80fcbb9c41e76e1eed`
- **Lean 工具链与依赖锁**：
  - [`k3/lean-toolchain`](https://github.com/Visio-Vanitas/buchstab-switching/blob/cca80480105d17764982ca80fcbb9c41e76e1eed/k3/lean-toolchain)：`leanprover/lean4:v4.37.0-rc1`
  - [`k3/lake-manifest.json`](https://github.com/Visio-Vanitas/buchstab-switching/blob/cca80480105d17764982ca80fcbb9c41e76e1eed/k3/lake-manifest.json)：Mathlib `31ce06eaadf4a200c0e1407c5f10953cf606b8f8`
- **GRH 声明对齐目标**：[`k3/BuchstabSwitching/External/CharacterSums/DirichletGRH.lean`](https://github.com/Visio-Vanitas/buchstab-switching/blob/cca80480105d17764982ca80fcbb9c41e76e1eed/k3/BuchstabSwitching/External/CharacterSums/DirichletGRH.lean) 中的 `DirichletLNonvanishingRightOfHalf` 与 [`lsernau/grh-lean@72fead102f663d5c7a407964a13dc0cf9d977207`](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Statements.lean) 逐字对应。

### 关键存档文件 SHA-256（以 `git clone -c core.autocrlf=false` 检出为准）

| 相对路径 | SHA-256 | 说明 |
|---|---|---|
| `k3/scripts/data/certified_slabs.json` | `52708e3888902dc5cf9b64479bde4536c1e5c92ecca05f223175d1750e3e78f6` | 127 个有限区间与 $10^{600}$ 射线的证书数据 |
| `k3/scripts/data/certified_bounds.txt` | `a64e1ce4a19716bd0be91615d2d84031313a494d5b09bc9d78ff24ef89eb2127` | 逐段归一化主项、误差与净余量文本记录 |
| `k3/BuchstabSwitching/Certificates/Data.lean` | `19a5a75259c348335e2f667662d5399745cf4719a6c3293390336e0f1f6e7ab4` | 分母 `DENOM = 10^10` 的 Lean 整数证书表 |
| `shared/data/linear_sieve_inputs/cn_rows_all.json` | `b931b6798c2c9f35cba30ead4c54c668d544b79c9a1989aa705352d55d09b906` | 线性筛精确有理数常数表（含 `100:old`、`100:new`） |
| `shared/data/linear_sieve_inputs/logs/hstar.log` | `9db0e31b2ff56e623eb512ab7f058bc5e247a4ba0fbe6e9cfce04e0839ce4eb4` | 预筛扫描参考日志 |

*注记*：`certified_slabs.json` 中 `main_lo`、`err_hi`、`net_lo` 各自从 90 位十进制精度独立向外截断至 15 位小数字符串，因此个别区间字符串差 `main_lo - err_hi` 与 `net_lo` 在末位可能相差 $1\text{ ulp}$（$10^{-15}$）；`Data.lean`（分母 $10^{10}$）内满足精确整数关系 `0 < net_num ≤ main_num - err_num`。

---

## 2. 供维护者独立执行的复核命令（POSIX shell）

```sh
git clone -c core.autocrlf=false https://github.com/Visio-Vanitas/buchstab-switching.git
cd buchstab-switching
git fetch origin cca80480105d17764982ca80fcbb9c41e76e1eed
git checkout --detach FETCH_HEAD

# 1. 快速检查（AST 零浮点扫描、Decimal Inexact/Rounded 陷阱、闭区间 (H*)、127 段与 Data.lean 一致性）
cd k3
python3 -I scripts/quick_verify.py

# 2. 从零重新生成区间证书与二进反射见证并比对工作树差异（可选，完整重算约数分钟）
python3 -I scripts/certify_omega_le_3.py
python3 -I scripts/generate_lean_data.py
python3 -I -m scripts.sieve_cert.slab_witness_export
git diff --exit-code

# 3. Lean 4 独立编译与标准公理白名单检查（已做二进 Dyadic 分片，单进程峰值内存 < 500 MB）
lake exe cache get
lake build BuchstabSwitching
lake env lean AxiomsCheckK3.lean
lake env lean BuchstabSwitching/Sieve/AxiomsAudit.lean

# 4. Comparator 独立内核导出核验（需环境已安装 comparator / leanchecker / nanoda_bin）
bash comparator/run_comparator.sh
```

---

## 3. 主要源码核查索引

| 核查模块 | 上游路径 |
|---|---|
| 顶层条件定理 `all_even_one_plus_three_of_classical` | `k3/BuchstabSwitching/Main.lean` |
| 6 条经典文献前提汇总 `ClassicalBasicLemmas` | `k3/BuchstabSwitching/External/Bridge.lean` |
| 外部前提逐项定义与文献说明 | `k3/BuchstabSwitching/External/README.md` |
| 一步切换组合捏紧与平衡不等式 | `k3/BuchstabSwitching/Core/ShiftedPrimes.lean`、`k3/BuchstabSwitching/Sieve/OneStepSwitching.lean` |
| Regime 2（127 段）筛法桥与二进 `Dyadic` 反射验证器 | `k3/BuchstabSwitching/Sieve/Regime2SlabBridge/` |
| Regime 3（$N\ge10^{600}$）闭区间 $(H^*)$、$C_2\le494$ 与射线桥 | `k3/BuchstabSwitching/Sieve/LinearSieveBJS/`、`k3/BuchstabSwitching/Sieve/Regime3RayBridge/` |
| 独立 Comparator 挑战目标声明 | `k3/comparator/ChallengeK3Reduction.lean`、`k3/comparator/reduction-export-targets.txt` |
| 数学推导与二进反射架构文档 | `k3/NOTES_K3_DERIVATION.md`、`k3/BLUEPRINT.md` |
