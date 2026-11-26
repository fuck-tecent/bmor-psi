# 发布与回滚

## 选择发布文件

| 发布内容 | 来源与目的地 | 核验 |
| --- | --- | --- |
| 网站模板、静态资源和 Python 模块 | `deploy/` 下需要发布的运行文件 → `/opt/goldbach-web/` | 主入口和子路径入口都能加载相关页面、样式、脚本与图片 |
| 研究任务 | `research/gaps.json` 或 `research/problems.json` → `/opt/goldbach-web/` 同名文件 | 核对受影响问题的任务 ID、命题和公开状态 |
| Jenkins、Lean 和 checker | `deploy/jenkins/`、`lean/`、`tools/` 中的 Git 文件 | 查看目标提交对应的 GitHub Check 与 Jenkins 构建结果 |
| nginx 及 systemd | 逐项对照 `deploy/nginx/`、`deploy/goldbach-web.service` 与对应 drop-in | 代理配置先过 `nginx -t`，服务单元变更先执行 `systemctl daemon-reload` |

在仓库查看 `git status --short`、`git diff --check` 和目标提交差异。只暂存本次文件，用 `git diff --cached --name-status` 核对范围。Python 认证测试可运行 `python -B -m unittest deploy.test_zhihu deploy.test_github_identity`，研究清单可运行 `python -B -m unittest research.test_catalogue`。对改动的 JS 运行 `node --check`。Lean 类型检查以本次目标提交对应的 `Goldbach CI / catalogue release` 结果为准。验证生成的命题通过类型检查与证明已获得权威核验是不同结果。

## 更新正在运行的网站

从已授权的入口登录服务器。先核对服务的运行目录、当前版本和实际文件。按提交 SHA 获取发布文件，避免从浏览器下载或从工作区复制其他未提交内容。服务器直连 GitHub 失败时，可从受信本地仓库导出包含目标提交及所需历史的 Git bundle，通过已授权的 SSH 连接传输后在服务器核对提交 SHA。共享工作副本分叉时保留它，使用单独的发布工作副本。

下面的 Linux 示例只发布 `site.css`。替换示例 SHA。多文件更新时先备份所有将被替换的文件，记录本次新增文件，准备好整组新文件后再切换。服务模块、任务清单、系统配置分别处理。

```sh
set -eu
release='<reviewed-commit-sha>'
app=/opt/goldbach-web
backup=$(mktemp -d)
git cat-file -e "${release}^{commit}"
git show "${release}:deploy/site.css" > "$backup/site.css.new"
cp -p "$app/site.css" "$backup/site.css"
install -m 0644 "$backup/site.css.new" "$app/site.css.next"
mv "$app/site.css.next" "$app/site.css"
cmp "$app/site.css" "$backup/site.css.new"
printf 'Rollback backup: %s\n' "$backup"
```

静态资源由应用按请求读取。Python 模块、启动时读取的任务清单、地区数据或凭据更新后，重启 `goldbach-web` 并检查 `systemctl is-active goldbach-web`。仅在代理配置发生变化且 `nginx -t` 通过时运行 `systemctl reload nginx`。备份权限保持私有。生产 SQLite、OAuth 会话、管理员记录、证书私钥、签名密钥与统计密钥由运维独立管理。需要迁移数据时使用 SQLite 一致性备份并考虑写入窗口及数据库兼容性。

## 公网验收

```sh
curl -fsS --retry 5 --retry-delay 1 https://www.goldbach.tech/health
curl -fsS --retry 5 --retry-delay 1 https://www.movan.tech/goldbach/health
curl -fsS https://www.goldbach.tech/api/status -o /dev/null
curl -fsS https://www.movan.tech/goldbach/api/status -o /dev/null
```

再检查这次变更的可见效果。页面用浏览器打开中英文入口及适用分站。任务台对照 `/problems/<slug>/api/status` 返回的任务。更换讨论群时对照图片中的截止日期、两种入口的图片以及浮窗是否能展开。OAuth 用已登记的主域名，通过授权测试账号或隔离数据核对权限。裁决回传以确切提交的 `Goldbach CI / formal Lean verdict` 和任务台公开记录为准。

## 回滚

如果验证失败，保留必要的非敏感错误信息。把本次备份的文件逐个恢复到原位，并按改动类型重启项目服务或验证后重载 nginx。只在已确认没有调用方时移除本次新增的资源。再次运行公网验收。服务文件回滚和 Git 回滚分别处理，已发布的修正使用新的 revert 或修复提交。生产 SQLite 有新写入时，恢复旧数据库前先确认数据影响和恢复方案。
