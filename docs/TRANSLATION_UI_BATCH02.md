# 第二批本地化变更说明

- 累积中文模板：1411 / 3202 条（本批 +844）；三语保留。
- 本次重点：主界面、地图、首领关卡、反例和证明操作、帮助、回放、部分教程。
- 中文仅作为 `ZH_CN` 独立覆盖层，原始 `catalog.js` 中的日文与英文不修改。
- 上一批书库正文 8 小节及其独立 JS 文件一并包含。
- `app.js` 保持原游戏逻辑，未拆改证明引擎。
- 动态占位符（如 `⟦0⟧`）与 HTML 结构均已测试。
- 未翻译的英文或日文仍然可能出现在长篇剧情、教程与书库中。

## 覆盖方式

下载此 ZIP 到 `~/code`，从 `~/code` 运行 `unzip -o proof-dungeon-zh-CN-ui-batch-02-cumulative.zip`。
压缩包内部以 `proof-dungeon/` 开头；解压会覆盖本地仓库中相同路径的文件。

## 验证

```sh
cd ~/code/proof-dungeon
python3 scripts/check_translations.py
node tests/smoke_i18n.cjs
node tests/smoke_books_zh.cjs
python3 tests/smoke_markup_zh.py
node --check src/js/app.js
```

通过后使用 `python3 -m http.server 8000` 进行浏览器本地交互测试，再 commit/push。
