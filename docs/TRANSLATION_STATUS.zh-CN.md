# 简体中文翻译进度 · 第五批（2026-10-31）

- 索引词条总数：**3,202**。
- 第四批完成时：**2,105** 条。
- 本批新增：**269** 条，主要补齐教程中的早期关卡提示。
- **累计：2,374 / 3,202（74.1%）；剩余 828 条**。
- 本批新增索引范围：17—402，其中未添加原有已译条目；实际索引见 `docs/TRANSLATION_BATCH05.md`。
- 重点：蕴涵、析取、否定、归谬法、直觉主义 Kripke 模型、全称和存在量词、等号、集合与数学归纳法，兼顾群论及乘法。
- 日文、英文仍完整保存在 `src/i18n/catalog.js` 中，简体中文作为独立覆盖层。
- 本批没有修改证明引擎、关卡数据或原始日英词库，也没有改动存档格式。
- `src/i18n/books.zh-CN.js` 中已有的书库汉化保持不变。本批侧重关卡正文，未翻译的其他书库/帮助长文本仍需下一批处理。
- 翻译覆盖率按索引条目计算，**不代表游戏内全部字数的完成比例**。

## 测试

```bash
python3 scripts/check_translations.py
node tests/smoke_i18n.cjs
node tests/smoke_books_zh.cjs
python3 tests/smoke_markup_zh.py
node tests/smoke_story_zh.cjs
node tests/smoke_tutorial_zh.cjs
node --check src/i18n/zh-CN.js
```

建议使用浏览器对抽样关卡的弹窗、Kripke 模型提示和归纳法操作进行人工检查。
