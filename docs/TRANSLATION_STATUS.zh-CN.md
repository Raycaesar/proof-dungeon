# 简体中文翻译进度 · 第四批（2026-10-31）

- 词条总数：3,202。
- 第一轮：332；书库第一批：+243；界面第二批：+844；第三批：+406；**第四批：+288**。
- **累计中文词条：2,105 / 3,202（65.7%）；剩余 1,097 条**。
- 本批完整覆盖原索引 **1000—1287**：迷宫故事线中的命题逻辑、直觉主义逻辑、谓词逻辑、集合与等号、代数与函数、自然数、归纳法、公理独立性、终章剧情及主要对话。
- 原文和英文保留在 `catalog.js`，中文覆盖在 `zh-CN.js`。未翻译的条目继续按原程序机制回退为英语或日语。
- 《Kripke 模型之书》8 段译文位于 `src/i18n/books.zh-CN.js`，本批没有修改它。
- 本批只修改中文文本资源和进度文档；无须清除本地存档，也不更改证明检查器、关卡、公式或 HTML 模板。
- **进度数字是词条覆盖率，并非书库全篇字数或整个游戏的汉化百分比**；教程中仍有未译长 HTML 模板。

## 自查命令

```bash
python3 scripts/check_translations.py
node tests/smoke_i18n.cjs
node tests/smoke_books_zh.cjs
python3 tests/smoke_markup_zh.py
node --check src/i18n/zh-CN.js
node tests/smoke_story_zh.cjs
```

需要在本地浏览器进一步确认页面渲染和关卡互动。
