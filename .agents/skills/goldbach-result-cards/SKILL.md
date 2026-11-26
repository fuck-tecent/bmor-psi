---
name: goldbach-result-cards
description: Review current Goldbach Research pull requests and Lean verdicts, explain the mathematical value and scope of verified results, and produce an attractive HTML and PNG report card with the original site logo and a scannable website QR code. Use for progress summaries, shareable result cards, or inspecting whether a result has been proved.
---

# Goldbach 成果核验与报告卡

1. 从仓库根目录核对最新 `main`。按用户指定的范围查看 PR 和对应研究台的 `/api/status`。普通成功状态、辅助检查和清单类型检查都要与权威证明裁决区分。旧运行查 `Lean / authoritative` 和 Actions 日志，新运行查同一 head SHA 的 `Goldbach CI / formal Lean verdict`、任务台 ACCEPTED 和 Jenkins 核验记录。网站地址和 GitHub 仓库可从仓库 README 找到。
2. 对每条入选结果，核对实际接受的 PR head、命题 ID、冻结声明、显式假设和范围，并附真实来源链接。对比当前目录声明。仅有权威检查通过的范围可以写为「已核验」。标出条件性结论、有限证书、已知结果复现、未合并的证明和研究稿。检查数学表述准确性，遇到不能确认的原创性或第三方审查，保留相应不确定性。
3. 从已核验结果中挑选对主线有实质用途的命题。说明它解决了哪一步，以及主要猜想还缺什么。用户问数学价值或发表潜力时，对照原论文、已知界或已有形式化，说明新贡献、重用范围和仍需补齐的证据。只有分析需求时，直接给出带来源的摘要。
4. 要制作卡片时，整理数据并运行 [报告卡导出说明](references/export.md)。保留站点原版 Logo、可点击来源、核验日期和网站二维码。待审稿放在独立备注里。导出后检查 PNG 可读性、二维码指向以及 HTML 的移动版布局。
