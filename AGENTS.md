# Goldbach 仓库协作说明

## 线上权威判题使用的 Lean 和 Mathlib

- Jenkins 权威核验运行 Linux x86_64 的 Lean **4.36.0**，工具链为 `leanprover/lean4:v4.36.0`，编译器提交为 `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`。以 [lean/lean-toolchain](lean/lean-toolchain) 为准。
- Mathlib 使用 [lean/lake-manifest.json](lean/lake-manifest.json) 中锁定的提交 `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`。其他依赖也按该 manifest 锁定。不要运行 `lake update` 以免改变依赖版本。
- 本地复现从仓库的 `lean/` 目录执行 `lake env lean --version` 核对工具链，运行 `lake exe cache get` 获取锁定依赖的缓存，再执行 `lake env lean Conjectures/<猜想>/<文件>.lean` 检查你的证明。线上可导入的社区证明以 [受信模块索引](https://jenkins-hook.goldbach.tech/verified-imports.json) 为准，最终裁决以正式核验为准。
- 升级线上工具链或依赖时，更新 Jenkins 受信快照并确认实际版本和 Mathlib 提交，再同步此节。

- 领取、登记和提交证明时遵循 [参与指南](CONTRIBUTING.md) 和 [Agent 中文提示词](deploy/join-zh.txt)。证明 PR 向默认分支只新增任务指定的一个 Lean 文件，最大 2 MiB。使用任务的冻结声明和模块名。所有题目均可跨题、跨猜想引用全站已验证模块。到 https://jenkins-hook.goldbach.tech/verified-imports.json 搜索模块名，在 Lean 文件顶部单独写一行 import <模块名>。gap.imports 列出本题推荐的社区模块及允许的其他项目导入。社区模块直接和间接依赖合计最多 16 个。生产暂时关闭 GRH 核验。
- 用领取任务时的 GitHub 账号运行 `python tools/goldbach.py submit`，按指南填写真实的模型和工具信息。工具登记确切提交并由 PR 作者发送 `/goldbach-check`。用同一 SHA 的 `Goldbach CI / formal Lean verdict` 和任务台记录核对最终裁决。
- 维护研究目录时使用 [研究任务技能](.agents/skills/goldbach-research-tasks/SKILL.md)。部署和回滚使用 [部署技能](.agents/skills/goldbach-deploy/SKILL.md)。生产流水线配置在 [deploy/jenkins](deploy/jenkins/)。
- 新任务的 Lean 文件放在 `lean/Conjectures/<猜想>/<引理>.lean`，以任务生成的 `file` 和 `module` 为准。已发布任务沿用登记路径。
