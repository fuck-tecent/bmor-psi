# 研究清单自动发布

AI 从最新 main 开分支，为目录变更提交 PR。项目所有者或授权的数学任务发布者在 GitHub 审核并合并。ECS 定时器每五分钟按 main 第一父链顺序检查变更，要求每个目录提交对应由获授权账号合并的 PR，并有该 SHA 的 `Goldbach CI / catalogue release` 成功记录。建议用 squash merge。目录通过直接推送或多 PR 打包时若无法对应单一合并提交，发布停下供人工核对。服务器只从 Git 读取两个目录数据文件。服务代码及工作流的运维更新仍走部署技能。

在 `goldbach-catalogue.service` 的服务器 drop-in 中设置 `GOLDBACH_CATALOGUE_CI=jenkins`，并设置 `GOLDBACH_CATALOGUE_MERGER_IDS`，填入以空格分隔的 GitHub 数字用户 ID，随后执行 `systemctl daemon-reload`。项目所有者默认有权限。该名单独立于网站发布名单。

## 首次启用

在此功能 PR 合并之后，按部署技能从已审提交发布 server.py、zh.html、en.html、publish_catalogue.py。核对线上基线：选择已经在生产处理过的最后一个目录提交，或之后尚未引入目录变化的 main 提交。用完整 SHA 初始化。初始化会复制现网两份 JSON；历史页面从首次自动发布开始计数。

```sh
install -d -m 0755 /opt/goldbach-catalogues
python3 /opt/goldbach-web/publish_catalogue.py --bootstrap "$LIVE_BASE_SHA"
install -m 0644 deploy/goldbach-catalogue.service deploy/goldbach-catalogue.timer /etc/systemd/system/
systemctl daemon-reload
systemctl enable --now goldbach-catalogue.timer
```

加载器一次解析 current 指向的不可变版本。新版本目录完整落盘后，发布器原子切换链接、仅重启 goldbach-web，并从生产 health 核对 catalogue_revision；失败时切回原版本。若线上清单与 Git 基线不同，三方合并保留现网差异；有冲突时在切换前退出。核验 API 和服务记录无需部署令牌。对批量发布检查各台 api/catalogue-status 和新题详情；公开变更记录入口为 research-changes?lang=zh。

## 发布社区引理导入

更新任务的 `imports` 时，从已合并的提交准备一份新的 Jenkins 受信基线，其中包含对应目录和已合并的引理源文件。Lean 工具链、Mathlib 锁定版本和已构建的项目模块兼容时，可复用现有缓存。切换前用新基线检查允许列表、依赖闭包和一份实际调用引理的证明，并核对依赖清单中的源文件哈希。保留旧基线，在正式核验空闲时切换 `GOLDBACH_TRUSTED_BASE`，然后核对生产目录接口返回的 `imports` 与 Jenkins 一致。冻结的任务声明仍用 Mathlib 检查。

自动合并服务从 Jenkins 的正式 ACCEPTED 记录和已送达裁决中读取候选，使用 GitHub App 的 Contents 写权限精确匹配 PR head 后 squash 合并。该服务把已核验的 Lean 源文件加入下一份受信快照，原子切换 `/opt/goldbach-ci/proof-bases/current`，然后重试下一批。初始化时把已核对的受信基线放入该目录，再将 current 指向它，设置 Jenkins 的 `GOLDBACH_TRUSTED_BASE` 解析该链接。维护者发布新任务目录时暂停合并服务，更新同一个链接，使用的基线须包含已出版的证明。保留旧快照直至所有引用该快照的任务退出。通过 `goldbach-ci-proof-merge.timer` 控制自动合并，日志写入对应 systemd 服务。新增导入权限仍由研究目录维护者在任务的 `imports` 字段里配置。

合并工作器在证明进入受信基线后，检查目录中尚未登记的直接依赖。只有源码与 GitHub main 完全一致的模块才可以登记。工作器使用目录生成器更新 `imports`，按批次创建待审核的目录 PR，需要 GitHub App 的 Contents 和 Pull requests 写权限。已有待审核 PR 时等待合并，再处理积累的依赖。目录发布后会显示新增推荐。全题库共享引用权限由 Jenkins 受信快照的 verified-imports.json 管理，新证明与索引随同一快照原子发布。历史回填使用 seed_verified_imports.py，对齐正式任务台裁决、主分支 Git blob 与快照源码。运行 seed 前暂停合并定时器并等待当前工作器退出。

Jenkins 在 `/var/cache/goldbach-lean-deps` 复用社区依赖的 `.olean`。缓存键包含固定工具链、Mathlib 锁文件、受信依赖的构建产物、模块源码和其传递依赖。并行任务使用同一缓存键时只编译一次。提交的证明每次独立编译并进行 Lean 内核核验。

合并工作器会同步生产任务台报告的目录版本。只同步已进入 main、且获同一个 GitHub App 的正式目录发布检查通过的提交。若该提交需要更换 Lean 工具链、锁文件或核验器，需先准备相应的 Jenkins 受信基线。

## 故障处理

查看 journalctl -u goldbach-catalogue.service，区分身份不符、CI 待完成、清单合并冲突和重载失败。网络错误由下一轮定时器重试。需要人工回滚时先停止 timer 和发布服务，核对旧版本后原子切回 current，重启 goldbach-web 并核对 health。恢复 timer 前在 Git 上创建并审核修复 PR；若队列头仍是有冲突或未获授权的提交，须由管理员明确核对并协调基线。历史记录属于正在提供服务的快照。

## 启用可核验拆题

先部署带 reduce 模式的 CheckLemma 并按锁定版本重建受信 checklemma，更新受信快照的 outside-guard.mjs、Jenkins controller（含 assemble.py）、合并服务脚本、网站发布器允许列表与 Desk 运行文件（含 reductions.py），供各研究台的开放任务拆分使用。任务源文件上的 reductions 控制正式反驳资格。已有 SQLite 库会在启动时增量迁移。研究台和 CI 共用原正式裁决签名配置。使用原有 GOLDBACH_TRUSTED_BASE、GOLDBACH_DESK_URL 和 GOLDBACH_DESK_SECRET_FILE。配置正式 Desk 的 site runner 每轮从所有分站获取一套就绪的拆法，在原有并发配额内核验；暂缺已合并源文件时会轮询重试。父题的冻结声明、组合 Lean 源码、依赖哈希和各方 PR 可从任务详情及 /api/catalogue-status 复核。

在备有锁定 Lean、Mathlib、PEqualNP.Defs 和 checklemma 的开发 checkout 中，通过下列命令重放两套拆法、正式反驳和父题核验。测试使用独立的本地 HTTPS Desk 和临时数据库。

```sh
GOLDBACH_TEST_LEAN=1 python3 -B -m unittest -v deploy.test_cut_refute
```
