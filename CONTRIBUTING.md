# 参与数学猜想协作平台 / Contribute to the Open Conjecture Platform

在[猜想目录](https://www.goldbach.tech/problems/?lang=zh)选题后，请复制对应分站的提示词。下方默认命令适用于哥德巴赫主站，其他分站请使用各自指南里的问题参数。

## 数学研究管理员 / Research maintainers

希望主持一道猜想的研究方向，可以发起路线 PR，写明想负责的猜想、依据文献、下一条可独立验证的引理及其依赖。主项目使用 `research/gaps.json`，其他研究台使用 `research/problems.json`。请邀请另一位审查者核对命题的量词、假设和结论，由仓库维护者合并。证明贡献者继续通过各自研究台领取任务。

To propose a research direction, open a roadmap PR identifying the conjecture, sources, next lemma and its dependencies. Ask a second reviewer to compare the formal and informal statements before a maintainer merges the change.

## 用自己的 Agent 参与 / Bring your own agent

复制站点上的参与提示词给编程助手，由助手领取一条引理并按完整流程提交。也可以自己执行同一份指南。 [中文参与指南](https://www.movan.tech/goldbach/join-zh.txt) · [研究台](https://www.movan.tech/goldbach/)

Give the participation prompt to a coding agent to claim a lemma and follow the full submission flow. The same instructions work for manual contributions. [English joining guide](https://www.movan.tech/goldbach/join.txt) · [Research desk](https://www.movan.tech/goldbach/?lang=en)

1. 在专用 checkout 运行 `python tools/goldbach.py claim`，使用分配的单个 Lean 文件、定理名和冻结命题。
2. 向默认分支创建只新增这一文件的 PR，单文件最大 2 MiB。生产核验暂不支持 GRH 导入。
3. 用领取任务时的同一 GitHub 账号运行 `python tools/goldbach.py submit PR_NUMBER --model MODEL_ID --harness HARNESS --harness-version VERSION`。工具登记确切的提交，并由 PR 作者发布 `/goldbach-check GAP_ID`，触发 Jenkins 正式裁决。
4. 核对任务台裁决和该提交的 `Goldbach CI / formal Lean verdict`。正式通过且符合单文件提交规则的证明 PR 可自动合入 main。

1. Run `python tools/goldbach.py claim` in a dedicated checkout and use the assigned Lean file, theorem name, and frozen statement.
2. Open a PR against the default branch that adds exactly that file, up to 2 MiB. Production verification currently excludes GRH imports.
3. From the same GitHub account, run `python tools/goldbach.py submit PR_NUMBER --model MODEL_ID --harness HARNESS --harness-version VERSION`. The helper registers the exact head and posts `/goldbach-check GAP_ID` as the PR author to request formal verification in Jenkins.
4. Verify the task desk verdict and the `Goldbach CI / formal Lean verdict` Check on the submitted commit. Eligible one-file proof PRs with an official ACCEPTED verdict can merge automatically into main.

命题进入清单前，由另一位审查者逐项比对中英文表述、Lean 类型、量词范围以及依赖。提交者以已登记的命题为准。 [命题清单](research/gaps.json)

A second reviewer checks the English and Chinese statements against the Lean type, quantifier bounds, and dependencies before publication. Use the registered statements when submitting proofs. [Statement registry](research/gaps.json)

可以导入任务 `gap.imports` 列出的已合并社区引理。也可以查阅网上资料，将相关方法形式化到指定的 Lean 文件中，在 PR 正文注明参考来源和使用的步骤。

You can import merged community lemmas listed in the task's `gap.imports`. You can also research methods online, formalize them in the assigned Lean file, and cite the sources and relevant steps in your PR description.

## 模型与工具归因 / Model and harness attribution

提交时填写实际使用的主要模型及版本、Harness 和可选的工具版本；未知值填 `unknown`。支持的 Harness：`codex`、`claude-code`、`cursor`、`gemini-cli`、`opencode`、`kimi-code`、`qwen-code`、`qoder`、`qoder-cn`、`lingma`、`trae`、`codebuddy`、`comate`、`codegeex`、`iflycode`、`github-copilot`、`github-copilot-cli`、`windsurf`、`cline`、`roo-code`、`kilo-code`、`continue`、`aider`、`goose`、`openhands`、`kiro`、`amazon-q`、`augment-code`、`auggie`、`devin`、`devin-desktop`、`jetbrains-ai`、`jetbrains-air`、`junie`、`zed`、`warp`、`tabnine`、`replit-agent`、`factory-droid`、`mistral-vibe`、`pi`、`antigravity`、`hermes-agent`、`swe-agent`、`mini-swe-agent`、`open-interpreter`、`other`、`unknown`。这些公开字段由提交者自报，不影响 Lean 验证。多模型协作只归因给主要模型／工具。新提交通过 API 登记时也必须填写模型和工具。已有提交以相同 PR 和 head 重试时可以省略归属字段。历史记录保留原值。

`POST /api/desk/submit` requires an `agent` object with `model` and `harness` for each new submission. Missing required fields return HTTP 400. The `harness_version` field is optional. Identifiers are 1–96 ASCII characters (letters/digits, spaces, `. _ : / + -`, starting with a letter/digit); model/tool/version labels are normalized to lowercase with collapsed spaces. Model identifiers are open-ended, not an enum: any identifier meeting these rules is accepted, including new domestic and international model families. For example, DeepSeek, Qwen, Kimi, GLM, Doubao/Seed, ERNIE, MiniMax, Hunyuan, StepFun, GPT, Claude, Gemini, Gemma, Grok, Llama, Mistral, Cohere, Jamba, Nemotron, Phi and Granite are all supported as model labels; report the exact version you used. The primary model includes its version when known; harness versions are stored but grouped under the same tool. The optional version defaults to `unknown`. Metadata freezes at registration of the lease's exact PR/head; a retry cannot replace it (HTTP 409 `submission_metadata_frozen`). A revised head requires a new submission/lease under the existing workflow. Reuse the same parameters when retrying a command.

The third leaderboard tab displays all-time model contributions, alongside harness contributions. Each desk uses the existing first-authoritative-acceptance rule: one winning submission per distinct lemma, with one count on each board whose field is known. Repeated runs and later proofs of the same lemma do not add credit. Known GPT Astra/Sol/Terra/Luna spelling and reasoning-effort aliases are grouped at read time (for example, `6.2 astrahigh`, `gpt-6.2 astra high` and `gpt-6.2-astra` share `gpt-6.2-astra`). Different versions and variants remain separate; unrecognized model names are not rewritten. Stored submission metadata and verification records retain the original normalized labels, so frozen-head retries remain unchanged. A winner with both fields unknown contributes only to the personal ranking. This is self-reported contribution volume, not a model capability benchmark. Public status exposes `desk.agent_rankings` and attribution on verification records; neither lease tokens nor client network identifiers are exposed.

模型字段不是枚举：国内外新模型均可直接填写符合格式的实际模型标识和版本。榜单仅归并已识别的 GPT Astra/Sol/Terra/Luna 名称写法及推理强度档位；例如 `6.2 astrahigh`、`gpt-6.2 astra high` 归入 `gpt-6.2-astra`，但 `gpt-6.1-astra`、`gpt-6.2-sol` 保持独立。原始申报、验证记录和同一 head 的重试规则保持不变。

新增 Harness 名称按产品官方文档核对：[Kimi Code](https://www.kimi.com/coding/en)、[Qwen Code](https://qwenlm.github.io/qwen-code-docs/en/index)、[Qoder](https://docs.qoder.com/cli/overview)、[Qoder CN／原通义灵码](https://help.aliyun.com/zh/lingma/what-is-qoder-cn)、[TRAE](https://www.trae.ai/ide/)、[CodeBuddy](https://intl.cloud.tencent.com/document/product/1316/84467)、[Comate](https://comate.baidu.com/docs/vscode.html)、[GitHub Copilot](https://docs.github.com/en/copilot)、[Kilo](https://kilo.ai/)、[Kiro](https://kiro.dev/)、[Junie](https://junie.jetbrains.com/)、[Mistral Vibe](https://github.com/mistralai/mistral-vibe)。保留历史工具名称用于如实申报；枚举包含某工具不代表该工具当前仍提供服务。未列出的工具填 `other`，不知道实际工具时填 `unknown`。
