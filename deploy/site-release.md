# 网站自动发布

开发者创建 PR，仓库所有者或获授权的网站维护者合并到 `main`。Jenkins 验证合并后的确切提交，GitHub App 回写 `Goldbach CI / site release`。服务端每三分钟拉取公开仓库并检查合并人和测试结果。符合条件时只发布检查范围内的应用模块、模板及静态资源。任务清单按 [任务发布流程](catalogue-release.md) 发布。nginx、systemd、凭据和发布器自身由服务器维护者单独更新。

## 开发者操作

1. 创建分支并开 PR，说明改动和验收方式。尽量用 GitHub 的 squash merge 将一次发布合为单个 main 提交。
2. 合并后查看同一 SHA 的 `Goldbach CI / site release` 检查。通过后等待服务器轮询。
3. 打开两个入口的健康接口，确认 `site_revision` 是本次发布提交或其后续发布提交。访问改动页面确认效果。

```sh
curl -fsS https://www.goldbach.tech/health
curl -fsS https://www.movan.tech/goldbach/health
```

## 服务器首次安装

由已有服务器维护者执行。从已审核提交安装，先比对网站正在运行的文件与选定的完整 `LIVE_BASE_SHA`。该 SHA 应在 main 的第一父提交链上。已有的任务发布器应处于已配置状态。在网站发布服务的 systemd drop-in 中设置 `GOLDBACH_SITE_CI=jenkins`。

```sh
install -d -m 0755 /usr/local/libexec/goldbach
install -d -m 0700 /opt/goldbach-site-releases
install -m 0644 deploy/publish_site.py /usr/local/libexec/goldbach/publish_site.py
install -m 0644 deploy/goldbach-site-release.service deploy/goldbach-site-release.timer /etc/systemd/system/
install -d -m 0755 /etc/systemd/system/goldbach-catalogue.service.d
install -m 0644 deploy/goldbach-catalogue-release-lock.conf /etc/systemd/system/goldbach-catalogue.service.d/release-lock.conf
flock -w 90 /opt/goldbach-catalogues/site-release.lock /usr/bin/python3 /usr/local/libexec/goldbach/publish_site.py --bootstrap "$LIVE_BASE_SHA"
systemctl daemon-reload
systemctl enable --now goldbach-site-release.timer
```

## 排障和回滚

用 `journalctl -u goldbach-site-release.service` 查合并授权、CI、文件差异与健康检查。网络或 CI 未完成时定时重试。遇到直接提交、未经授权的账号合并或运行文件有差异时，由维护者核对并处理队列头。恢复前保留现场，核实改动和发布基线。每个批次先备份受影响的线上文件，再发布并重启服务。双域名健康检查不通过时恢复备份。发布器与任务清单共用锁，避免同时切换。

网站发布授权通过 `goldbach-site-release.service` 的服务器 drop-in 设置。将 `GOLDBACH_SITE_RELEASE_MERGER_IDS` 设置为经核实的 GitHub 数字用户 ID，以空格分隔，并执行 `systemctl daemon-reload`。协作者还需要仓库的合并权限。撤销授权时从相同名单移除 ID 并重载。仓库所有者默认拥有网站发布权限。

手动回滚时停止发布定时器，等正在执行的发布结束，按日志中的快照和待发布文件清单恢复指定文件及版本标记，再重启并检查两个域名。对已经上线的变更优先通过经过审核的 revert PR 发布修复。备份在服务器保留，按维护周期清理。
