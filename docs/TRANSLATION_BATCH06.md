# 第六批：反模型解析与结尾操作界面

本批以第五批版本为基准，翻译了 **192 条连续条目（2158—2349）**。其中大多数说明只有日文原文，原来在简体中文模式下无法回退到英文。

## 翻译范围

- 2158—2196：命题逻辑反例、直觉主义 Kripke 模型与哥德尔—达米特逻辑。
- 2197—2222：谓词逻辑、固有变元条件、空真、量词交换和关系结构。
- 2223—2266：偏序与预序、极大元、代数结构、群论、归纳法与有限模型。
- 2267—2291：无矛盾性、群论与算术公理的独立性模型。
- 2292—2349：反例解释、证明回放按钮、制作人员和授权信息、结构与 Kripke 反模型结果弹窗。

## 技术原则

- 只覆盖 `src/i18n/zh-CN.js`，不修改 `src/i18n/catalog.js` 中的日文、英文。
- 不改动 `src/js/app.js`、任何关卡数据、推理引擎或存档接口。
- 逐条核验所有 `⟦n⟧` 占位符的出现次数、`{{...}}` 交叉引用和原有 HTML 元素及属性。
- 原翻译授权声明与 `LICENSE` 保留。

## 进度

第五批 2,374 条；第六批新增 192 条；累计 **2,566 / 3,202（80.1%）**；剩余 **636 条**。按词条计数，不代表已经翻译了 80.1% 的文字量。未索引正文仍需进一步扫描。

## 测试

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

建议抽查游戏中反例结算画面、Kripke 模型说明、群论和数学归纳法关卡。下一批优先解决 404—716 的连续教程与剩余长篇帮助文本。
