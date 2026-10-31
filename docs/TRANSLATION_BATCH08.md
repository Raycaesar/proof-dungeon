# 第八批：教程、证明操作、楼层叙事与帮助表（2026-10-31）

基于 `Raycaesar/proof-dungeon` 第七批提交，并与上传至该仓库的中文词库核对基线。

- **本批新增 136 条**：补齐 **762—999** 之间全部此前未翻译的索引条目。包含 **953** 号长篇操作指南与 978—999 号楼层叙事。
- **累计 2,955 / 3,202 条（92.3%）**；索引中还有 **247** 条待译，另外还需扫描未索引正文。
- 内容涵盖 ∀I、∃I、→I、=E、RAA、⊥E 等推理操作，固有变元条件、等式改写和引理、归纳法、证明树标签、死路提示、反例与数学模型结果、楼层开场剧情与操作对照表。
- 只修改中文覆盖层和翻译文档；原日文/英文词库、游戏引擎、关卡数据与存档保持不变。
- 更新第七批测试中对累计译文数写死的断言，改为下限检查；新增第八批专用测试。

对应 ID 列表见 `TRANSLATION_BATCH08_IDS.txt`。

## 测试

```bash
python3 scripts/check_translations.py
node tests/smoke_i18n.cjs
node tests/smoke_books_zh.cjs
node tests/smoke_story_zh.cjs
node tests/smoke_tutorial_zh.cjs
node tests/smoke_countermodels_zh.cjs
node tests/smoke_hints_zh_batch07.cjs
node tests/smoke_hints_zh_batch08.cjs
python3 tests/smoke_markup_zh.py
node --check src/i18n/zh-CN.js
```

这些是静态回归检查；仍建议用浏览器抽查日英中三语切换、Lean 帮助页、楼层开场叙事和证明树交互。下一批可继续完成索引中剩余的 247 条并扫描未索引长篇正文。
