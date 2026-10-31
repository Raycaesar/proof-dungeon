/*
 * Chinese translations of library pages originally embedded as raw bilingual
 * templates in app.js. Each key is a book ID, then a section ID.
 * The functions receive only the original book rendering helpers.
 * Original narrative / exposition: © 2026 Takayuki Kihara, CC BY-NC-SA 4.0.
 */
const BOOK_ZH_CN = Object.freeze({
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
