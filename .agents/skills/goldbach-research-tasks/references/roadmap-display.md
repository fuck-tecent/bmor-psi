# 新版路线图指南

## 挂载任务

从仓库根目录编辑 `research/problems/<desk>/routes/<route-id>/route.json`，每条新任务写到同级 `tasks/<lemma-id>.json`。目录名、`route.json.id` 和已确定的路线 ID 保持一致。新路线提供中英文 `title` 和 `description`。任务的中英文 `plain_statement` 用作列表或面板中的标题，`brief` 补充证明切入口。将任务间依赖写进 `depends_on`。

| 页面 | 前端如何分组 | 维护动作 |
| --- | --- | --- |
| 强哥德巴赫首页的「研究地图」 | 读取 `gaps.json` 的 `tracks`，按任务的 `track` 分组，用 `feeds` 连路线 | 用现有稳定 ID 接入已有路线。新路线提供指向同台已有路线的 `feeds`，没有下游时填空数组。连线应无环。主线方向变化时同步更新 `research/ROADMAP.md`，核对中英文入口。 |
| 研究分站的「研究路线」及地图 | 读取该题 `problems.json` 的 `roadmap`。阶段的 `tasks[].id` 决定面板、地图分组和任务详情绑定 | 接入已有阶段时填准确的 `existing_stage_en`，沿用该阶段稳定的 `route_id`。新阶段由源文件生成。任务只挂在一个阶段。 |

运行下面的命令，并将分目录源文件与有变更的生成清单一起提交。调整已有路线的标题或说明时，先查它由旧清单还是分目录源文件维护，在相应来源修改。移动已发布任务前，核对旧链接和任务租约。

```sh
python research/build_catalogue.py --write
python research/build_catalogue.py
python -B -m unittest research.test_catalogue research.test_route_sources
```

## 页面验收

在预览或部署后的页面用 `lang=zh` 和 `lang=en` 各检查一次。主站从 `/?lang=zh#lemmas` 进入地图，路线可用 `/?lang=zh#route=<route-id>` 直达。分站从 `/problems/<desk>/?lang=zh#roadmap` 打开路线面板，也可用 `#track-<route-id>` 跳到该面板再展开。复制任务直达链接时使用该面板生成的链接。

1. 在地图或路线面板找到预期的双语标题。确认新增任务都在正确路线，且没有落到「未分路线的命题」或主站的未分轨任务组。主站抽查 `feeds` 的方向，分站抽查同一任务能从地图筛选及路线面板找到。
2. 点开新任务，确认详情显示正确的 ID、命题、证明状态和领取入口。挑战题的开放状态和领取方式应符合 `challenge_only`、`claims_closed`。在窄屏检查路线列表与详情可操作。
3. 从对应研究台的 `/api/status` 对照任务 ID、`route_id`、冻结声明和 `proved` 状态。若 API 或页面还是旧数据，先核对 `/health` 的 `catalogue_revision` 和浏览器刷新后的结果。CI 状态不能用来替代运营中的目录快照。

示例可用二次型素数研究台的 [高频估计推广阶段](https://www.goldbach.tech/problems/quadratic-primes/?lang=zh#track-high-mode-extension)。在 PR 里留下对应的主站或分站入口与抽查任务 ID，方便维护者复核。
