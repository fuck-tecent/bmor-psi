# 新任务的研究目录

从本次约定开始，新任务在 `research/problems/<研究台>/routes/<路线>/tasks/<任务 ID>.json` 编辑。每条路线的元数据放在同级的 `route.json`。文件夹使用稳定的英文 slug。研究台名称沿用 goldbach、quadratic-primes、log-rank、no-three-in-line、square-packing 和 hash-collision-lab。

## 新建一条路线

例如新建 Goldbach 路线时可用以下结构，名称仅为示例。

```text
goldbach/routes/signed-window/
  route.json
  tasks/
    L-goldbach-window-example.json
```

```json
{
  "id": "signed-window",
  "title": {"zh": "有符号窗口", "en": "Signed windows"},
  "description": {"zh": "比较移位与原目标的误差。", "en": "Compare the shifted and original targets."},
  "feeds": ["minor-truncation"]
}
```

沿用主站已有路线时，只需在 route.json 写入对应的 id。分站新路线使用双语 title、description；接入既有分站路线时以其固定 route_id 作为目录名和 id，填写 existing_stage_en（原阶段完整英文标题）。任务文件沿用同研究台的完整目录记录，包括 id、file、module、statement、双语 plain_statement 和 brief、program、imports、source 等字段。任务的 track 从目录名生成。复用同一研究台的引理时在 depends_on 中引用其 ID。Lean 文件和模块沿用原签名约定。

设置 `challenge_only: true` 后，开放题只接受按 ID 的新领取。需要连按 ID 的新领取也停止时，同时设置 `claims_closed: true`。这两个目录字段不参与声明哈希，已有租约可按原流程续租、提交和验证。

## 提交和核验

新任务的 Lean 文件按猜想放在 `lean/Conjectures/<猜想>/<引理>.lean`。例如 `L-goldbach-window-example` 对应 `Conjectures.Goldbach.WindowExample`，顶层定理采用同名声明。生成器从研究台 slug 和任务 ID 派生 `file`、`module`，新任务 JSON 可以省略这两个字段。路线变更保留模块路径。已有任务沿用登记路径。

1. 添加源文件后运行 `python research/build_catalogue.py --write`。一并提交源文件与更新的兼容清单。网站、领取工具及权威检查器继续读取现有清单。
2. 运行 `python research/build_catalogue.py` 检查生成结果，再运行 `python -B -m unittest research.test_catalogue research.test_route_sources`。目录 CI 还会用固定版本 Lean 检查生成的声明。
3. PR 正文按研究台和路线列出新增 ID、父题及尚缺的证明。合并后按发布流程核对线上声明哈希。
4. 老任务保持原位置。若两个新 PR 同时更新兼容清单，合并时先保留主分支的清单和双方的分目录源文件，再运行生成命令。若 PR 同时含旧格式任务，应先保留这些任务的清单变更。
