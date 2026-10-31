# Proof Dungeon：自然演繹の迷宮

**[▶ ブラウザで遊ぶ](https://kihara-logic.github.io/proof-dungeon/)**

自然演繹による証明の組み立てと、反例による「証明できないこと」の確認を、迷宮のパズルとして体験するブラウザゲームです。

手持ちの鍵（仮定）を使って扉（証明の目標）を開けると、その操作がそのまま自然演繹の証明図になります。証明できない扉は、真理値の割り当て・クリプキモデル・有限の構造を作って、反例で示します。最後には、公理から命題もその否定も導けない「決まらない扉」にたどり着きます。

## 迷宮の構成

本編の 17 の層に、隠し層 2 つと寄り道 3 つを加えた、全 22 層・119 ステージです。層は、前の層をクリアすると順に開きます（「制限なしモード」ですべて開きます）。

| 部 | 層 | 内容 |
|---|---|---|
| 第一部　命題論理 | 第 1〜6 層 | ∧・→・∨・⊥・¬ の推論規則、背理法の魔法（古典論理）、真理値の割り当てによる反証 |
| | 隠し層 H1 | 術なしの論理（直観主義論理）とクリプキモデル |
| 第二部　述語論理と集合 | 第 7〜11 層 | ∀・∃ の推論規則、古典述語論理、構造による反証、集合の演算と範囲を限った量化子 |
| | 隠し層 H2 | 二重否定翻訳（グリヴェンコ・黒田） |
| 第三部　等号と数学の理論 | 第 12〜17 層 | 等号と関数、順序と群、補題（カット）、自然数と数学的帰納法、公理から証明できないことの反例、自己言及・無矛盾性・独立性 |
| | 寄り道 S1〜S3 | 掛け算の法則、自然数の順序とペアノの公理 |

各層の最後には、扉が「証明できる」か「反例がある」かを見極める鑑定の部屋や、ボスのステージがあります。

## 主な特徴

- **証明図**：操作するたびに、自然演繹の証明図が組み上がります。クリア後は、一手ずつの再生や、操作と推論規則の対応表で振り返れます。クリアした証明は保存され、いつでも見返せます。
- **反例**：真理値の割り当て（石盤）、クリプキモデル（時の塔）、有限の構造（模型の街）を作って、推論が成り立たないことを示します。反例が完成すると、決め手になった住人や表の欄を示し、作った反例の意味を解説します。
- **定理カード**：証明した定理は定理カード（全 15 枚）になり、後のステージで仮定の鍵として使えます。
- **書庫**：各層の書庫に、推論規則と数学の内容を解説した書物（全 28 冊）があります。参考文献も付いています。
- **証明項と Lean**：「証明項を表示」で証明を λ 項として、「Lean モード」で定理証明支援系 Lean 4 のコードとして見られます。
- **式の入力**：補題や項は、記号ボタンのほか、TeX のコマンド（`\forall`、`\to` など）でも入力できます。
- **ストーリー**：迷宮を進む物語と結末があります（設定でオフにもできます）。冒険の記録から、語り・碑文・問答帳・結末を読み返せます。
- **言語**：日本語と英語に対応しています。
- **アクセシビリティ**：キーボードで操作でき、読み上げソフト向けの名前を付けています。OS の「動きを減らす」設定（prefers-reduced-motion）に合わせて、演出の動きを控えます。

## 遊び方

ブラウザで `index.html` を開くだけで遊べます（インストールは不要です）。画面右上の「遊び方」と「チュートリアル」で、操作の説明を見られます。

クリアの記録・定理カード・証明の途中経過は、遊んでいるブラウザの中に保存されます。

## クレジット

制作: 木原貴行, Claude Opus 5.5 (Anthropic)

**着想を得た作品**

- [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4)（Kevin Buzzard、Jon Eugster ほか）――ペアノ算術をゲームとして証明していく構成と、証明した定理を再利用する仕組みを参考にしました。
- [The Incredible Proof Machine](https://incredible.pm/)（Joachim Breitner）――自然演繹を、手で触れて遊べるものにした先駆けです。

**自然演繹について**

G. Gentzen (1935), D. Prawitz (1965), D. van Dalen, *Logic and Structure*（ゲーム内の書庫の参考文献を参照）

**使っているもの**

- 書体：Zen Old Mincho、BIZ UDPGothic、STIX Two Text（SIL Open Font License 1.1、Google Fonts 経由）
- 数式の表示：MathJax 3（Apache License 2.0）
- Lean モードで書き出すコードは、Lean 4（Apache License 2.0）で検査できます。

## ライセンス

- **ソフトウェア**（HTML・CSS・JavaScript のコード）：[MIT License](LICENSE)
- **文章**（物語、書庫の書物、問答帳、各ステージの説明・ヒント、チュートリアルの文など。日本語版・英語版とも）：[CC BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/)

詳しくは [LICENSE](LICENSE) を参照してください。MathJax とフォントは、それぞれ元のライセンスに従います。

---

# Proof Dungeon: The Labyrinth of Natural Deduction

**[▶ Play in your browser](https://kihara-logic.github.io/proof-dungeon/)**

A browser game in which you build proofs in natural deduction and show, with counterexamples, what cannot be proved — as puzzles in a labyrinth. Using the keys you hold (assumptions) to open doors (goals), your moves become a natural deduction proof tree. Doors that cannot be opened are shown with counterexamples: truth assignments, Kripke models and finite structures. At the end you reach "undecided doors" — statements whose truth and falsity both fail to follow from the axioms.

- **22 levels, 119 stages**: 17 main levels (propositional logic → predicate logic and sets → equality and mathematical theories), 2 hidden levels (intuitionistic logic and Kripke models; double-negation translations) and 3 side paths (multiplication; the order of the natural numbers and the Peano axioms).
- Proof trees with step-by-step replay; saved proofs; counterexamples with their decisive features explained; 15 theorem cards; 28 books in the library; proof terms and Lean 4 code; symbol buttons and TeX input; a story with an ending; Japanese and English.
- Just open `index.html` in a browser. Progress is saved in your browser.

Created by: Takayuki Kihara, Claude Opus 5.5 (Anthropic). Inspired by the [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4) (Kevin Buzzard, Jon Eugster et al.) and [The Incredible Proof Machine](https://incredible.pm/) (Joachim Breitner). Fonts: Zen Old Mincho, BIZ UDPGothic, STIX Two Text (SIL OFL 1.1). Math rendering: MathJax 3 (Apache License 2.0).

License: the software (HTML, CSS and JavaScript) is under the [MIT License](LICENSE); the written content (story, library books, Q&A notebook, lessons, hints and tutorial texts, in both languages) is under [CC BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/). See [LICENSE](LICENSE) for details.
