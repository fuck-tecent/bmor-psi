---
name: goldbach-deploy
description: Deploy or update the Goldbach Open Conjecture Platform, verify the deployed version, or roll back a release. Use for website and task-catalogue updates, Jenkins, GitHub App or webhook changes, and service or nginx configuration updates. Read the deployment plan without changing production when asked only for advice.
---

# Goldbach 项目部署

日常网站更新经有发布权限的维护者合并 PR 到 `main` 后，Jenkins 核验确切提交并由 GitHub App 回写 `Goldbach CI / site release`，服务器定时器检查结果并发布。发布权限由服务器按 GitHub 用户 ID 核对。开发者用自己的 GitHub 账号开 PR。用公开健康接口的 `site_revision` 核对线上实际版本。[自动发布、安装与故障处理](../../../deploy/site-release.md)

从仓库根目录运行命令。部署步骤和按变更类型选择的检查见 [发布与回滚](references/release.md)。服务配置、依赖、凭据文件位置和双入口架构见仓库的 [部署文档](../../../deploy/README.md)。

- **网站更新**：在 PR 里列出可见效果和测试。新增 JS、CSS 或图片要检查应用资源路由和两种入口下的路径。上线后确认提交对应的 CI 通过、健康接口显示预期版本，并实际打开页面。
- **任务清单**：对照 `research/gaps.json` 和 `research/problems.json`，确认新增 ID 唯一，已发布命题及其哈希按预期保留。先核验确切提交的 `Goldbach CI / catalogue release`，再部署相应清单并重启服务。逐个核对受影响研究台的公开任务。
- **工作流、代理或凭据**：Jenkins 流水线和控制服务使用 `deploy/jenkins/` 的配置。nginx 改动仅涉及项目专属虚拟主机或子路径，配置通过 `nginx -t` 后平滑重载。systemd 单元或 drop-in 修改后执行 `daemon-reload`。现有业务、生产数据库和站点凭据都在发布文件清单之外。

使用开发者自己的授权账号与服务器权限。只有获准更新生产时才运行生产命令。凭据通过 systemd 或各自的凭据存储提供。Git、提交描述、日志、截图和命令输出只记录必要的版本与验证结果。部署完成时给出提交 SHA、实际更新文件、线上验证结果和适用的回滚备份位置。
