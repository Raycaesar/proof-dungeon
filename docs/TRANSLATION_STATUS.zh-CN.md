# 简体中文翻译进度 · 第六批（2026-10-31）

- 索引文本总数：**3,202**。
- 第五批累计：**2,374** 条。
- 第六批新增：**192** 条，连续编号 **2158—2349**。
- **累计：2,566 / 3,202（80.1%），剩余 636 条**。
- 翻译内容：反模型的计算和释义、直觉主义模型、量词交换、偏序、群、归纳法、理论无矛盾性与独立性、反例结果弹窗以及项目致谢。
- `src/i18n/catalog.js` 原日文和英文仍然完整保留，简体中文以 `src/i18n/zh-CN.js` 独立覆盖，默认显示中文。
- `src/i18n/books.zh-CN.js` 中之前的书库译文保持不变。
- **未修改游戏逻辑、关卡和存档。**
- 后续优先翻译未覆盖的索引范围 404—716、762—999、2350 之后及其他长篇帮助与故事文本。

说明：覆盖率只统计索引条目数量，不代表全篇字数或所有未索引书库的实际翻译程度。

## 检查

```bash
python3 scripts/check_translations.py
node tests/smoke_i18n.cjs
node tests/smoke_books_zh.cjs
python3 tests/smoke_markup_zh.py
node tests/smoke_story_zh.cjs
node tests/smoke_tutorial_zh.cjs
node tests/smoke_countermodels_zh.cjs
node --check src/i18n/zh-CN.js
```

完整浏览器逐关测试仍建议在发布前进行。
