# 导出核验报告卡

在仓库外或被 Git 忽略的输出目录准备 UTF-8 JSON。顶层字段为 `title`、`date`、`summary`、`cards` 及可选的 `note`。每个卡片包含 `track`、`title`、`scope`、`body` 和 `sources`。每条来源包含 `label` 和 `url`。在标题或正文里直接写 Unicode 数学符号。所有文字由脚本转义。第一项作为视觉焦点，其他项在桌面双栏排布。HTTPS 网站二维码由脚本从目标 URL 直接生成，包含标准静区，旁边保留可读域名。

安装本机渲染依赖：`python -m pip install playwright "qrcode[pil]"`。可用已有的 Chrome 或 Edge，也可用 `python -m playwright install chromium` 安装浏览器。在仓库根目录运行：

```sh
python .agents/skills/goldbach-result-cards/scripts/render.py results.json /path/to/output/goldbach-results
```

如果使用已安装的 Edge 或 Chrome，在命令末尾加 `--channel msedge` 或 `--channel chrome`。

输出同名 `.html` 和 `.png`。HTML 自带 Logo、二维码和样式，可直接分享。默认二维码指向 `https://www.goldbach.tech/`。如报告只涉及某个分站，用 `--url` 指定已核实的研究台 HTTPS 地址。审查输出图片中中文是否完整、公式是否被截断、二维码是否清楚。至少用手机扫码或独立的二维码解码器验证一次完整 PNG，核对解码地址与卡片所写地址一致。卡片内容是已选成果快照，后续更新应重新核对 PR 当前 head 和权威裁决。
