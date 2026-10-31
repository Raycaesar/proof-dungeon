# 第十批：全仓库国际化审计与正文补译（2026-11-01）

## 范围与版本校验

以 `Raycaesar/proof-dungeon` 当时的 `main` 为基准；主要源文件的本地 Git blob SHA 已与 GitHub 一一核对：

- `index.html`：`ef47f992d4a0a84346f50f6f2c0d1f9edbc44dff`
- `src/js/app.js`：`b70d15d66e4e3a1437ed01d4a7512fdb7d829c43`
- `src/i18n/zh-CN.js`：`6715934d6753b9c77c71266b874333125700245c`
- `src/i18n/catalog.js`：`3609db3749519d6bfac454d07aee7ae970c85f12`
- `src/i18n/books.zh-CN.js`：`f8f85b0ba6532496ee97aa2d2784ea025563cf30`

审查包括入口 HTML、CSS、主 JS、三份语言资源、测试脚本、构建/校验脚本及项目文档。原始许可证、日英词库和游戏核心规则不变。

## 已定位的问题

1. 原有 `L1(ja, en)` 在简体中文模式下依据日文假名正则式决定是否选择英文。若已翻译的中文模板中插入了日文字符串，会把**整段中文**误当成日文，回退为英文。现在 `__T` 记录最近 128 次中文索引输出的来源，`L1` 识别来自索引的中文文字，不再仅因其中有假名而选英文。
2. 报告中的 “How truth values are decided” 对应索引 `1992`，“Assignment” 真值规则表对应 `1989`，“No more dead-end notices” 对应 `1912/1913`。这些中文译文已存在于当前仓库，因此如果仍显示对应英文，须检查**实际所用语言**和**网页/脚本缓存或部署版本**；不能仅凭看到英文认定这几条没有翻译。本轮提供针对这些精确条目的运行路径测试。
3. 除 3,202 条索引外，`app.js` 中另有 **19 个正文小节**采用 `L1(String.raw`，不经过索引。先前 `kripke` 已翻译 8 节；本批将 `transl` 4 节和 `selfref` 7 节迁入 `src/i18n/books.zh-CN.js`，共 19 / 19 节；保留原有 `<!--pg-->` 分页和 MathJax 数学分隔符。
4. `index.html` 的入口脚本、CSS 附加 `?v=2026-11-01-10`，促使浏览器及静态站点缓存加载新的版本。不影响本地相对路径或 GitHub Pages。

## 改动文件

- `src/js/app.js`：国际化来源识别补丁；不修改证明逻辑与关卡。
- `src/i18n/books.zh-CN.js`：新添 11 节非索引书库正文完整中文译文。
- `index.html`：仅对资源 URL 添加版本查询参数。
- `tests/smoke_locale_routing.cjs`：检查中英日语言路径、报告的三处内容及动态日文插值。
- `tests/smoke_unindexed_books.cjs`：检查全部 19 节非索引书库正文、分页、基本 HTML 与数学公式分隔符。
- 本文与中文 README／翻译状态文件。

## 验证方式

```bash
node --check src/js/app.js
node --check src/i18n/books.zh-CN.js
python3 scripts/check_translations.py
python3 tests/smoke_index_zh_batch09.py
python3 tests/smoke_markup_zh.py
for file in tests/*.cjs; do node "$file"; done
```

以上静态测试与 Node VM 渲染函数测试均已通过。**尚未通过完整浏览器运行/逐关手工检查**，尤其是公式排版与动态引导弹窗；需要在 `python3 -m http.server 8000` 的页面上检查。若依旧看到英文，请先点击右上角语言按钮确认是“简中”，再在浏览器中执行 Ctrl+Shift+R 强制刷新，并确认 GitHub Pages 正在提供本次版本。

## 范围说明

索引 `3,202 / 3,202` 以及源程序中已识别的全部 `19 / 19` 个原生日英书库正文小节已有中文资源。这不是对任意游戏状态下所有可见字符的形式证明：源程序存在英文代码、Lean 语法、参考书目原文、备用英语 UI 模板和专有名称，后续仍需在三语下按 119 关逐关检查动态提示。静态扫描不能替代浏览器端到端测试。
