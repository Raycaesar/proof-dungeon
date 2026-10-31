# 第七批：剩余教程与关卡提示（2026-10-31）

- 基于 `Raycaesar/proof-dungeon` 第六批版本（原 `src/i18n/zh-CN.js` Git blob：`a28126104486e9340916111b5b49d9ac256b5de0`）。
- 新增 **253** 条简体中文译文，完整覆盖此前未翻译的 **404—716** 范围；原本已存在的条目保持不变。
- 累计 **2,819 / 3,202 条（88.0%）**，尚余 **383** 条索引文本。注意：这只是索引条目覆盖率，不包括未索引长篇内容的完成情况。
- 涵盖自然数顺序与皮亚诺公理、命题逻辑反例、一阶量词推理、反模型、偏序和幺半群、集合运算、三段论、对角线论证、群论、格利文科与黑田翻译，以及公理独立性。
- 保留原始日文和英文词库 `src/i18n/catalog.js`，不修改 `src/js/app.js`、证明引擎、关卡数据或存档格式。
- 修改了 `tests/smoke_countermodels_zh.cjs` 中仅适用于第六批的译文总数断言；新增 `tests/smoke_hints_zh_batch07.cjs` 检查全部 253 条译文的占位符出现次数、交叉引用和 HTML 标签；完整索引见 `docs/TRANSLATION_BATCH07_IDS.txt`。
- 下一批可翻译 **762—999** 范围剩余 136 条及其他零散条目，并全面核查未索引的书库和动态文本。

## 在项目根目录测试

```bash
python3 scripts/check_translations.py
node tests/smoke_i18n.cjs
node tests/smoke_books_zh.cjs
python3 tests/smoke_markup_zh.py
node tests/smoke_story_zh.cjs
node tests/smoke_tutorial_zh.cjs
node tests/smoke_countermodels_zh.cjs
node tests/smoke_hints_zh_batch07.cjs
node --check src/i18n/zh-CN.js
```

静态检查通过后仍建议用真实浏览器抽查关卡交互，特别是量词、集合展开和反例面板。
