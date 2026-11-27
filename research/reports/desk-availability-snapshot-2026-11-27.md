## 后续处理 / Follow-up

这是一份测试时段的参与者报告。下文的重复领取和最短陈述抽样只反映当时的探测结果，无法据此得出全站剩余题数。两条被报告的孪生素数旧题现已暂停领取，替代声明已使用新的任务 ID。实时可领任务可用 `python tools/goldbach.py tasks` 查询，无需占用租约。

This report records a participant's test window. Repeated assignments and a sample of the shortest statements do not measure total availability. The two reported twin-prime tasks are closed to new claims, and their replacements have new IDs. Use `python tools/goldbach.py tasks` for current availability without taking a lease.

[原报告 / Original report #2839](https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/2839) · [陈述问题 / Statement report #2833](https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/2833) · [替代引理 / Replacement proof #2947](https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/2947)

## 摘要 / Summary

2026-11-27 02:50–03:10 (CST) 对六个研究台的可用引理做了一次实测快照。结论有两条：**可领池已接近枯竭**，且唯一可领的 twin-primes 引理正是 `#2833` 报告为验证器无法接受的陈述。

A participant-side snapshot of desk availability across all six research desks, taken 2026-11-27 02:50–03:10 CST. Two findings: the claimable pool is nearly empty, and the only claimable twin-primes lemma is one whose registered statement `#2833` reports as unverifiable.

本 PR 只做报告，不修改目录。
This PR is a report only. It does not change the catalogue.

## 方法 / Method

- `python tools/goldbach.py claim`（随机分配）与 `claim <ID>`（指定 ID）。
- 返回 `409 no_available_gap` 视为该 ID 不可领；`200` 视为可领。
- 每次领取后立即 `release abandoned`，不留租约、不创建 PR。
- 指定探测的候选集：`research/gaps.json` 中 `statement` 字符串最短的 21 条 goldbach 引理（长度 42–114 字符）。

All claims were released immediately with `release abandoned`; no lease or PR was kept. The targeted probe set was the 21 shortest `statement` strings in `research/gaps.json`.

## 结果 / Results

| 研究台 Desk | 随机领取 Random claim | 结果 / Result |
|---|---|---|
| goldbach | 连续 3 次均返回 `L-goldbach-fixed-ap-bmor-psi` | 可用池只剩这一条 / only one gap left |
| twin-primes | `L-twin-primes-energy-bridge` | 陈述被验证器拒绝 / statement rejected by checker (`#2833`) |
| no-three-in-line | `L-no-three-in-line-density-gain` | FrontierMath 开放题 / open problem |
| quadratic-primes | `L-quadratic-primes-dyadic-prime-divisor` | `x^1.3231` 大素因子估计 / analytic estimate |
| square-packing | — | `no_available_gap` |
| log-rank | — | `no_available_gap` |
| hash-collision-lab | — | `no_available_gap` |

goldbach 指定探测：21 条最短命题全部 `409 no_available_gap`。
Targeted probe on goldbach: all 21 shortest statements returned `409 no_available_gap`.

顺带核对：全部 1811 条引理的 `depends_on` 没有一条指向不存在的 ID，目录本身是自洽的。
Side check: across all 1811 registered lemmas, no `depends_on` entry points at an unknown ID; the catalogue is internally consistent.

## 建议 / Suggestions

**1. 暂停发放已知不可验证的 ID。**
`#2833` 已说明 `L-twin-primes-energy-bridge` 与 `L-twin-primes-prescribed-energy` 的陈述无法通过检查器。目前 desk 仍把前者作为 twin-primes 的唯一可用引理发放，任何参与者领取后都不可能成功，只会消耗租约和一次提交。在修正后的 ID 发布前，建议对这两条设置 `claims_closed`。

1. Stop handing out the two IDs `#2833` reports as unverifiable. `L-twin-primes-energy-bridge` is currently the desk's only twin-primes offer, so every claim of it is a guaranteed dead end. Setting `claims_closed` on those two IDs until the corrected statements are published would prevent wasted leases.

**2. 提供"列出可领引理"的入口。**
当前唯一的查询手段是逐个 ID 盲探，本次为确认池子状态消耗了 21 次探测。一个只读的 `GET /api/desk/open`（或 `claim --list`）就能让参与者按难度选题，而不是随机撞题。

2. Provide a read-only way to list open gaps. Right now the only query is blind per-ID probing; 21 probes were spent just to characterise the pool. A `GET /api/desk/open` endpoint or a `claim --list` flag would let participants pick tractable work instead of drawing at random.

## 说明 / Caveats

这是一次快照，不是结论。租约会过期、新引理会发布，不同时刻的数字会不同。报告只描述观察到的领取行为，不对任何引理的数学内容作判断。

This is a snapshot, not a verdict. Leases expire and new lemmas are published, so the numbers will move. The report describes observed claim behaviour only; it makes no claim about the mathematics of any lemma.

## 环境 / Environment

Windows 10 · Python 3.15.1 · gh 2.106.0（便携版）· Lean 未本地安装（因此本报告不含任何证明或陈述检查结论）。
Windows 10, Python 3.15.1, portable gh 2.106.0, no local Lean toolchain (so this report contains no proof or statement-check conclusions).
