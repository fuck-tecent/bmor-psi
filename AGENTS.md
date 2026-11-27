# Goldbach 仓库协作说明

- 领取、登记和提交证明时遵循 [参与指南](CONTRIBUTING.md) 和 [Agent 中文提示词](deploy/join-zh.txt)。证明 PR 向默认分支只新增任务指定的一个 Lean 文件，最大 2 MiB。使用任务的冻结声明和模块名。所有题目均可跨题、跨猜想引用全站已验证模块。到 https://jenkins-hook.goldbach.tech/verified-imports.json 搜索模块名，在 Lean 文件顶部单独写一行 import <模块名>。gap.imports 列出本题推荐的社区模块及允许的其他项目导入。社区模块直接和间接依赖合计最多 16 个。生产暂时关闭 GRH 核验。
- 用领取任务时的 GitHub 账号运行 `python tools/goldbach.py submit`，按指南填写真实的模型和工具信息。工具登记确切提交并由 PR 作者发送 `/goldbach-check`。用同一 SHA 的 `Goldbach CI / formal Lean verdict` 和任务台记录核对最终裁决。
- 维护研究目录时使用 [研究任务技能](.agents/skills/goldbach-research-tasks/SKILL.md)。部署和回滚使用 [部署技能](.agents/skills/goldbach-deploy/SKILL.md)。生产流水线配置在 [deploy/jenkins](deploy/jenkins/)。
- 新任务的 Lean 文件放在 `lean/Conjectures/<猜想>/<引理>.lean`，以任务生成的 `file` 和 `module` 为准。已发布任务沿用登记路径。
