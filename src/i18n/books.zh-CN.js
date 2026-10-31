/*
 * Chinese translations of library pages originally embedded as raw bilingual
 * templates in app.js. Each key is a book ID, then a section ID.
 * The functions receive only the original book rendering helpers.
 * Original narrative / exposition: © 2026 Takayuki Kihara, CC BY-NC-SA 4.0.
 */
const BOOK_ZH_CN = Object.freeze({
  transl: Object.freeze({
    glivenko: ({ KEY }) => String.raw`
      ${KEY(String.raw`命题逻辑中的格利文科定理：\(\vdash_{\mathrm{c}} A \iff \vdash_{\mathrm{i}} \neg\neg A\)`)}
      <p>\(\vdash_{\mathrm{c}}\) 表示在包含反证法的<b>古典逻辑</b>中可证，\(\vdash_{\mathrm{i}}\) 表示在不采用反证法的<b>直觉主义逻辑</b>中可证。格利文科定理（1929）表明：古典逻辑可证的命题公式，只要在整个公式前添加双重否定，就成为直觉主义逻辑的定理。故事中把反证法称为“魔法书中的法术”，把添加双重否定称为“披上斗篷”。</p>
      <p>翻译室的 H2-1 至 H2-3 展示了这一方法。H2-1 的译式 \(\neg\neg(P\lor\neg P)\)，正是第 4 层首领关卡 4-5 中的公式。</p>
      <!--pg-->
      <p>从右向左的方向很直接：如果直觉主义逻辑证明了 \(\neg\neg A\)，那么古典逻辑可以利用反证法推出 \(A\)。</p>
      <p>从左向右的证明思路是：逐步考察古典逻辑的证明，说明将每一步结论加上双重否定之后，相应推理仍能在直觉主义逻辑中实现。所用到的性质包括：</p>
      ${KEY(String.raw`\(\neg\neg(A\to B)\leftrightarrow(\neg\neg A\to\neg\neg B)\)`,String.raw`\(\neg\neg(A\land B)\leftrightarrow(\neg\neg A\land\neg\neg B)\)`,String.raw`\(\neg\neg\neg\neg A\to\neg\neg A\)`)}
      <p>尤其是最后一项，使原证明中通过反证法从 \(\neg A\) 导出矛盾、再得出 \(A\) 的步骤，也能够在添加双重否定后的推导中得到处理。</p>`,
    fail: ({ KEY }) => String.raw`
      ${KEY(String.raw`虽然 \(\vdash_{\mathrm{c}}\forall x(P(x)\lor\neg P(x))\)，但 \(\nvdash_{\mathrm{i}}\neg\neg\forall x(P(x)\lor\neg P(x))\)`)}
      <p>对于含量词的公式，仅在整个公式外面添加双重否定是不够的（H2-4）。一个反例是具有无限上升世界链的 Kripke 模型，也就是游戏里的“时间之塔”。</p>
      <p>在一阶直觉主义 Kripke 模型中，每个世界有自己的论域，未来世界的论域可以扩大。\(\forall x A(x)\) 在一个世界被强制，要求从该世界出发的每个未来世界中的每个个体都满足 \(A\)；\(\exists x A(x)\) 被强制则要求当前世界已有一个满足 \(A\) 的个体。</p>
      ${KEY(String.raw`世界 \(n\) 的论域是 \(\{0,1,\dots,n\}\)`,String.raw`\(P(k)\) 自世界 \(k+1\) 起被强制`)}
      <p>在世界 \(n\) 中，新出现的个体 \(n\) 既不满足 \(P(n)\)，也不满足 \(\neg P(n)\)：前者要到下一世界才被强制，因此后者也无法被强制。于是任何世界都不强制 \(\forall x(P(x)\lor\neg P(x))\)，每个世界都强制它的否定，因而世界 0 不强制其双重否定。由可靠性定理，所讨论的翻译式在直觉主义逻辑中不可证。</p>
      <!--pg-->
      <p><b>为什么需要无限反模型？</b> 对于有限世界的 Kripke 模型，从任意世界都能到达一个极大世界；在那里公式的真值按古典方式确定。所以每个古典有效式 \(A\) 都在这些极大世界中被强制，从而 \(\neg A\) 在任何世界都不被强制，\(\neg\neg A\) 则处处被强制。</p>
      <p><b>失效的规则</b>：在上述模型中，每个个体都满足 \(\neg\neg(P(x)\lor\neg P(x))\)，因为这一实例本身是直觉主义逻辑的定理；但 \(\neg\neg\forall x(P(x)\lor\neg P(x))\) 仍未得到强制。因此以下“双重否定移位”在直觉主义逻辑中一般无效：</p>
      ${KEY(String.raw`\(\forall x\,\neg\neg B(x)\to\neg\neg\forall x\,B(x)\)`)}`,
    kuroda: ({ KEY, bkTable }) => String.raw`
      <p>黑田成胜（1951）的翻译除了在整个公式前添加双重否定，还要在每个全称量词内部立即添加双重否定。将 \(A\) 中每个 \(\forall x\) 改为 \(\forall x\neg\neg\)，得到 \(A^*\)，再定义：</p>
      ${KEY(String.raw`\(A^{\mathrm K}=\neg\neg A^*\)`,String.raw`\(\vdash_{\mathrm c}A\iff\vdash_{\mathrm i}A^{\mathrm K}\)`)}
      <p>例如，\(\forall x(P(x)\lor\neg P(x))\) 被译为 \(\neg\neg\forall x\neg\neg(P(x)\lor\neg P(x))\)，它在直觉主义逻辑中可证（H2-5）。全称量词内部的双重否定克服了上一节的障碍。</p>
      <!--pg-->
      <p><b>哥德尔—根岑否定翻译</b>是另一种经典方案，它在原子公式、析取及存在量词处引入否定：</p>
      ${bkTable(["公式","译式"],[[String.raw`\(P\)（原子公式）`,String.raw`\(\neg\neg P\)`],[String.raw`\(A\land B\)`,String.raw`\(A^N\land B^N\)`],[String.raw`\(A\to B\)`,String.raw`\(A^N\to B^N\)`],[String.raw`\(A\lor B\)`,String.raw`\(\neg(\neg A^N\land\neg B^N)\)`],[String.raw`\(\forall x A\)`,String.raw`\(\forall x A^N\)`],[String.raw`\(\exists x A\)`,String.raw`\(\neg\forall x\neg A^N\)`]])}
      <p>在这一翻译下，\(\Gamma\vdash_{\mathrm c}A\) 与 \(\Gamma^N\vdash_{\mathrm i}A^N\) 相对应（哥德尔，1933；根岑同期也得到了这一翻译）。将原子公式变为稳定的双重否定形式，并用否定改写析取、存在量词，使翻译后的公式在直觉主义证明中具有相应性质。</p>`,
    embed: () => String.raw`
      <p>通过否定翻译，古典逻辑中的证明可以转换为直觉主义逻辑中对相应译式的证明。因此，古典逻辑可以通过这种翻译<b>嵌入</b>直觉主义逻辑。</p>
      <p>特别地，\(\bot\) 的译式仍是 \(\bot\)。若一个经典理论可以推出矛盾，对应的直觉主义翻译理论也能推出矛盾。在算术中，这一思想联系了佩亚诺算术与海廷算术的相容性。</p>
      <p>古典逻辑与直觉主义逻辑之间有精确的翻译关系。故事中的“使用魔法书的人”与“禁止施展法术的人”，就体现了两种不同的推理规则体系。</p>`
  }),
  selfref: Object.freeze({
    barber: ({ KEY }) => String.raw`
      ${KEY(String.raw`\(\vdash\neg\exists y\,\forall x\,(K(y,x)\leftrightarrow\neg K(x,x))\)`)}
      <p>在 17-1 中，\(\leftrightarrow\) 写成两个蕴涵的合取。若真存在这样的制钥匠 \(a\)，将 \(a\) 自身代入 \(x\)，便得到 \(K(a,a)\leftrightarrow\neg K(a,a)\)，产生矛盾。这里甚至不需要使用古典反证法。</p>
      <p>第 9-1 关的规则只有一个方向的蕴涵，因此可以存在这样的制钥匠，并且能够推出 \(K(p,p)\)。</p>
      <!--pg-->
      <p><b>罗素悖论</b>：设 \(R=\{x\mid x\notin x\}\)，即所有不以自身为成员的集合所组成的集合。于是 \(R\in R\leftrightarrow R\notin R\)，导致矛盾。这与把 17-1 中的 \(K(y,x)\) 解释为 \(x\in y\) 具有相同的形式。</p>
      <p>任意条件都能定义集合的朴素集合观念会导致矛盾。ZF 等公理化集合论通过公理约束集合的形成方式。</p>`,
    diag: ({ KEY }) => String.raw`
      ${KEY(String.raw`\(\vdash\forall y\,\exists x\,\neg(D(y,x)\leftrightarrow\neg D(x,x))\)`)}
      <p>在 17-2 中，见证者就是判定机器 \(y\) 自身。将所有机器对各输入的回答排成表，再把对角线上的每个回答取反，就得到一列与任何机器的回答都不同的结果：它在输入 \(y\) 处必定不同于机器 \(y\) 的回答。</p>
      <p><b>康托尔的对角线论证</b>：不存在从自然数到自然数幂集的满射 \(f\)。若 \(S=\{n\mid n\notin f(n)\}\) 等于 \(f(m)\)，则得到 \(m\in S\leftrightarrow m\notin f(m)=S\)，矛盾。把 \(D(y,x)\) 解释为“\(x\in f(y)\)”即可看出与 17-2 的对应。</p>
      <!--pg-->
      <p><b>停机问题</b>（图灵，1936）：不存在一个程序 \(H\)，能够对任意程序 \(p\) 和输入 \(x\) 总是正确判定 \(p(x)\) 是否停机。</p>
      <p>否则，可构造程序 \(D\)：当 \(H\) 判断 \(p(p)\) 会停机时，它便无限循环；否则它立即停机。将 \(D\) 自身输入 \(D\)，就会得到“停机当且仅当不停机”的矛盾。</p>`,
    decide: ({ KEY }) => String.raw`
      <p><b>命题逻辑</b>的可证性是可判定的。若出现 \(n\) 个原子命题，逐一检查 \(2^n\) 种真值赋值即可。直觉主义命题逻辑的可证性也可判定，例如通过有限 Kripke 模型与终止的证明搜索；因此，游戏在第 6 层之前可以报告死路（见《可靠性与完全性之书》）。</p>
      ${KEY("一阶逻辑不存在对任意输入都能终止的通用可证性判定算法","丘奇与图灵，1936")}
      <p>依照长度依次枚举所有候选证明，凡是可证的公式终究会找到证明。但若公式不可证，枚举过程未必能在有限时间内确认这一点。反例也可能只能存在于无限结构中。例如，满足“每个元素都有严格更小元素”的非空线性序必然是无限的。</p>`,
    check: () => String.raw`
      <p>给定一份形式证明，可以机械地逐条检查推理规则是否正确，即<b>证明检验是可判定的</b>。游戏中的“检查通过”以及 Lean 一类证明助手，都执行这样的验证。把证明视为 λ 项时，这与类型检查相联系（见《蕴涵之书·下卷》）。</p>
      <p>既然可以检查证明，就可以把所有候选证明按长度枚举并逐一检验，从而最终找到每一个可证公式的证明。一阶逻辑的有效式因此构成<b>递归可枚举</b>集合，也称<b>半可判定</b>。</p>
      <p>但不存在一种通用算法，能对任意一阶公式都在有限时间内给出“可证”或“不可证”的正确答案。对于不可证公式，枚举证明的过程可能永远继续。</p>
      <p>这种不可判定性涉及形式问题本身，而非人和机器之间的能力差别。人的证明同样需要符合规则；游戏中无法制造出能识别所有不可打开之门的机器，正是对此性质的表现。</p>`,
    consis: ({ KEY }) => String.raw`
      ${KEY("如果某个结构满足理论 \\(T\\) 的全部公理，那么 \\(T\\) 无法证明矛盾 \\(\\bot\\)")}
      <p>这是可靠性定理的直接推论（17-3）。反过来，每个相容的一阶理论都有模型，这是哥德尔完全性定理的一个结果；该模型可能无限。</p>
      <!--pg-->
      ${KEY(String.raw`如果一个使 \(A\) 为真、另一个使 \(A\) 为假的结构都满足 \(T\)`,String.raw`那么 \(T\nvdash A\) 且 \(T\nvdash\neg A\)`)}
      <p>此时称 \(A\) 相对于 \(T\)<b>独立</b>（17-4、17-5）。著名例子包括平行公设相对于欧氏几何其余公理的独立性、选择公理相对于 ZF 的独立性，以及连续统假设相对于 ZFC 的独立性（哥德尔，1938；科恩，1963）。</p>`,
    godel: ({ KEY }) => String.raw`
      ${KEY("第一不完全性定理：设 \\(T\\) 为公理可有效枚举、包含足够算术且相容的理论", "则存在一个算术语句，\\(T\\) 既不能证明它，也不能证明它的否定", "第二不完全性定理：满足相应可表达性与可导性条件的 \\(T\\) 不能证明自身的相容性")}
      <p>第一不完全性定理由哥德尔（1931）证明。罗瑟（1936）进一步把不可反驳性所需的假设从较强的 ω-相容性减弱为相容性。</p>
      <!--pg-->
      <p><b>基本思路</b>：利用哥德尔编号给公式与证明编码，并用算术公式 \(\mathrm{Prov}_T(n)\) 表示“编码为 \(n\) 的公式在 \(T\) 中可证”。利用对角线引理构造语句 \(G\)，使得（\(\ulcorner G\urcorner\) 是 \(G\) 的编码）：</p>
      ${KEY(String.raw`\(T\vdash G\leftrightarrow\neg\mathrm{Prov}_T(\ulcorner G\urcorner)\)`)}
      <p>\(G\) 可以理解为表达“我在 \(T\) 中不可证”。若 \(T\) 相容，则 \(T\) 不证明 \(G\)。在标准自然数模型中，\(G\) 因而为真。</p>
      <p>不过，要证明哥德尔原始构造的 \(G\) 也不可被反驳，需要更强的 ω-相容性。罗瑟改用另一个语句，通过对证明长度的比较，仅从相容性就能得到两侧都不可证的结论。</p>
      <!--pg-->
      <p>第二不完全性定理利用在理论内部对证明及相容性作算术化表述：如果 \(T\) 能证明符合标准定义的自身相容性语句，那么在适当可导性条件下它也会证明某个哥德尔语句，发生矛盾。证明中需要仔细处理 \(\mathrm{Prov}_T\) 满足的可导性条件。</p>
      <p>更强的理论有时可以证明较弱理论的相容性，例如 ZFC 可以证明皮亚诺算术的相容性。增加公理也可能判定原来独立的语句，但充分强的、有效公理化的相容理论仍会遇到新的独立语句：这对应游戏中“无法裁定的门”。</p>`,
    more: ({ bkRefs }) => String.raw`
      <details><summary>完全性与不完全性</summary><p>名称相近，但含义不同。哥德尔完全性定理（1930）断言：一阶逻辑中，在所有结构里有效的公式均可证明。不完全性定理讨论的是包含算术的特定理论中存在既无法证明也无法反驳的语句。</p></details>
      <details><summary>第二不完全性定理与证明谓词的选择</summary><p>第二定理中的“自身相容性”依赖于选用何种证明谓词 \(\mathrm{Prov}_T\) 来表达 \(\neg\mathrm{Prov}_T(\ulcorner0=1\urcorner)\)。标准证明谓词满足适当的可导性条件，其他人为构造的证明谓词未必满足；因此必须明确相容性语句所采用的编码和条件。相关讨论可参考 Hilbert–Bernays、Löb 及后来的证明逻辑研究。</p></details>
      <details><summary>参考文献</summary>${bkRefs(["godel31","rosser36","turing","church","cantor91","godel30","godel38","cohen63","smullyan","hilbertbernays39","lob55","feferman60","arai90","kurahashi20","kurahashi19"])}</details>`
  }),
  kripke: Object.freeze({
    def: ({ KEY }) => String.raw`
      <p>对于不采用反证法的逻辑（直觉主义命题逻辑），我们使用一种有别于经典真值赋值的语义学。</p>
      ${KEY(String.raw`克里普克模型 \(\mathcal{K}=(W,\le,V)\)`)}
      <ul class="help-list"><li>\(W\)：非空集合，其中的元素称为<b>世界</b>，可以理解为不同的知识状态。</li><li>\(\le\)：\(W\) 上的偏序关系（具有反身性、传递性和反对称性）。\(w\le v\) 表示世界 \(v\) 是 \(w\) 的一个未来状态。</li><li>\(V\)：赋值函数，将每个世界 \(w\) 对应到在那里已成立的原子命题集合 \(V(w)\)。</li></ul>
      <!--pg-->
      <p>赋值函数须满足<b>单调性</b>：</p>
      ${KEY(String.raw`\(w\le v\;\Longrightarrow\;V(w)\subseteq V(v)\)`)}
      <p>它表示一个已经确立的原子命题，在未来世界中仍然成立。</p>
      <p>这里也可以使用前序关系代替偏序关系：以下论证不依赖反对称性。</p>`,
    force: ({ KEY, bkTable }) => String.raw`
      <p>用 \(w\Vdash A\) 表示公式 \(A\) 在世界 \(w\) 中成立，称为“\(w\) 强制 \(A\)”。这一关系按照公式的构造递归定义。</p>
      ${bkTable(["公式",String.raw`\(w\Vdash\cdots\) 的定义`],[[String.raw`\(p\)（原子命题）`,String.raw`\(p\in V(w)\)`],[String.raw`\(A\land B\)`,String.raw`\(w\Vdash A\) 且 \(w\Vdash B\)`],[String.raw`\(A\lor B\)`,String.raw`\(w\Vdash A\) 或 \(w\Vdash B\)`],[String.raw`\(A\to B\)`,String.raw`对所有 \(v\ge w\)，若 \(v\Vdash A\)，则 \(v\Vdash B\)`],[String.raw`\(\bot\)`,"永不成立"]])}
      <p>由于 \(\neg A\) 是 \(A\to\bot\) 的缩写，可以得到：</p>
      ${KEY(String.raw`\(w\Vdash\neg A\iff\forall v\ge w\;(v\nVdash A)\)`)}
      <!--pg-->
      ${KEY("要点：只有蕴涵与否定需要考察全部未来世界")}
      <p>“知道 \(A\) 蕴涵 \(B\)”意味着：无论是在当前还是以后的世界，只要 \(A\) 获得证实，\(B\) 也必须获得证实。</p>
      <p>“知道 \(\neg A\)”意味着：未来任何世界都不会证实 \(A\)。这比“目前尚不知道 \(A\)”强得多。</p>`,
    persist: ({ KEY }) => String.raw`
      ${KEY(String.raw`<b>持久性引理</b> 若 \(w\Vdash A\) 且 \(w\le v\)，则 \(v\Vdash A\)。`)}
      <p><b>证明</b>：对公式 \(A\) 的结构进行归纳。</p>
      <ul class="help-list"><li>原子命题：结论直接来自 \(V\) 的单调性。</li><li>合取与析取：直接应用归纳假设。</li><li>矛盾 \(\bot\)：没有世界强制 \(\bot\)，因而蕴涵真空成立。</li><li>蕴涵 \(A\to B\)：任取 \(u\ge v\)。由传递性有 \(u\ge w\)。因为 \(w\Vdash A\to B\)，所以 \(u\Vdash A\) 蕴涵 \(u\Vdash B\)。这就证明了 \(v\Vdash A\to B\)。\(\square\)</li></ul>
      <p>蕴涵的语义定义需要量化所有未来世界，持久性引理才能成立。</p>`,
    sound: ({ KEY }) => String.raw`
      <p>若在任意克里普克模型的任意世界 \(w\) 中，只要 \(w\) 强制 \(\Gamma\) 中所有公式就必然强制 \(A\)，便称 \(A\) 是 \(\Gamma\) 的<b>克里普克语义后承</b>，记作 \(\Gamma\models_K A\)。</p>
      ${KEY(String.raw`<b>可靠性定理</b> 若 \(\Gamma\vdash A\) 在不使用反证法的自然演绎中可证，则 \(\Gamma\models_K A\)。`)}
      <!--pg-->
      <p><b>证明要点</b>：对证明树进行归纳，逐条验证推理规则保持语义有效性。</p>
      <p>对 \(\to\mathrm{I}\)，假设 \(\Gamma,A\models_K B\) 且 \(w\Vdash\Gamma\)。任取 \(v\ge w\) 并假定 \(v\Vdash A\)。由持久性引理可知 \(v\Vdash\Gamma\)，于是 \(v\Vdash B\)，从而 \(w\Vdash A\to B\)。</p>
      <p>对 \(\to\mathrm{E}\)，在蕴涵的语义定义中取 \(v=w\) 即得结论；对 \(\lor\mathrm{E}\)，按照 \(w\Vdash A\) 或 \(w\Vdash B\) 分类讨论；对 \(\bot\mathrm{E}\)，其前提永不成立，因此结论真空成立。</p>
      <!--pg-->
      ${KEY(String.raw`<b>推论</b> 如果存在世界强制 \(\Gamma\) 却不强制 \(A\)，那么不用反证法就无法从 \(\Gamma\) 证明 \(A\)。`)}
      <p>反证法（RAA）不具有这一语义下的可靠性。下面的模型中，某个世界强制 \(\neg\neg p\)，却不强制 \(p\)。</p>`,
    ex: ({ KEY }) => String.raw`
      ${KEY(String.raw`\(W=\{w_0,w_1\},\quad w_0\le w_1,\quad V(w_0)=\emptyset,\quad V(w_1)=\{p\}\)`)}
      <ul class="help-list"><li>在 \(w_0\) 中，\(p\) 尚未成立；但在其未来 \(w_1\) 中 \(p\) 成立，因此 \(w_0\nVdash\neg p\)。故 <b>\(w_0\nVdash p\lor\neg p\)</b>：排中律在这里失效。</li><li>在 \(w_0\) 和 \(w_1\) 中都不成立 \(\neg p\)，因此 \(w_0\Vdash\neg\neg p\)；但 \(w_0\nVdash p\)。故 <b>\(w_0\nVdash\neg\neg p\to p\)</b>：双重否定消去失效。</li><li>令 \(q\) 在所有世界中均不成立。此时没有世界强制 \(p\to q\)，于是 \(w_0\Vdash (p\to q)\to p\)，而 \(w_0\nVdash p\)。所以<b>皮尔士律</b>在 \(w_0\) 失效。</li></ul>
      <!--pg-->
      <p>再考虑一个分叉模型：\(w_0\le w_1\)、\(w_0\le w_2\)，其中 \(V(w_0)=\emptyset\)、\(V(w_1)=\{p\}\)、\(V(w_2)=\{q\}\)。</p>
      <p>任何世界都不同时强制 \(p\) 和 \(q\)，因此 \(w_0\Vdash\neg(p\land q)\)。但是，由 \(w_1\Vdash p\) 可知 \(w_0\nVdash\neg p\)；由 \(w_2\Vdash q\) 可知 \(w_0\nVdash\neg q\)。</p>
      ${KEY(String.raw`所以，在不使用反证法的系统中，\(\neg(p\land q)\nvdash\neg p\lor\neg q\)。`)}`, 
    complete: ({ KEY }) => String.raw`
      ${KEY(String.raw`<b>完全性定理</b>（Kripke，1965）若 \(\Gamma\models_K A\)，则不用反证法也能证明 \(\Gamma\vdash A\)。`)}
      <p>结合可靠性定理可知：直觉主义逻辑中的可证明性，恰好对应于在所有克里普克模型中的有效性。</p>
      <!--pg-->
      <p><b>证明思路（典范模型）</b>：设 \(\Gamma\nvdash A\)，构造使全部 \(\Gamma\) 成立而 \(A\) 不成立的反模型。</p>
      <ul class="help-list"><li>世界：由<b>素理论</b>组成，即在演绎下封闭、相容，并具有析取性质（若 \(B\lor C\) 属于理论，则 \(B\) 或 \(C\) 属于理论）的公式集合。</li><li>关系 \(\le\)：理论之间的包含关系 \(\subseteq\)；\(V(w)\) 为世界 \(w\) 所包含的原子命题集合。</li><li><b>真值引理</b>：\(w\Vdash B\iff B\in w\)。</li></ul>
      <p>由 Lindenbaum 型扩张引理，若 \(\Gamma\nvdash A\)，就存在包含 \(\Gamma\) 却不包含 \(A\) 的素理论；它正是所需的反例世界。</p>
      <!--pg-->
      ${KEY("有限模型性质：有反例时，可在有限世界模型中找到反例")}
      <p>对命题逻辑来说，若公式存在反模型，就存在一个有限反模型。因此，直觉主义命题逻辑的可证明性是可判定的。</p>`,
    rel: ({ KEY }) => String.raw`
      ${KEY("只有一个世界的克里普克模型等价于一个经典真值赋值")}
      <p>模型只有一个世界时，“所有未来世界”就是当前这个世界，所以蕴涵与否定的定义恰好与经典真值表一致。</p>
      <p>因此，所有克里普克有效式都是经典有效式；反方向不成立，排中律就是反例。</p>
      <!--pg-->
      <p>克里普克语义最初用于研究模态逻辑。Gödel（1933）以及 McKinsey–Tarski（1948）等工作建立了直觉主义逻辑向模态逻辑 S4 的翻译。它按公式结构递归进行：原子命题 \(p\) 译成 \(\Box p\)，蕴涵 \(A\to B\) 译成 \(\Box(A'\to B')\)，而合取、析取直接连接各部分的译文。直觉主义命题逻辑的克里普克框架由反身、传递的可达关系刻画，与 S4 的框架条件相对应。</p>`,
    game: ({ bkTable }) => String.raw`
      ${bkTable(["数学概念","游戏机制"],[[String.raw`世界 \(w\in W\)`,"塔楼中的一层"],[String.raw`\(w\le v\)`,"向上的楼梯：越往上表示越靠后的未来"],[String.raw`\(V(w)\)`,"该楼层亮起的灯"],[String.raw`\(w\Vdash A\)`,String.raw`在该楼层中，公式 \(A\) 亮起`]])}
      <p>在构造反例的关卡中，只要找到一个楼层，使所有假设都亮起而目标没有亮起，就可由可靠性定理断定：不使用反证法时，无法从这些假设证明目标。</p>`
  })
});
