/* ===== 言語（日本語／English）。文章は TL(番号, 式) で、番号ごとの [日本語, 英語] の文型から作る ===== */
const LANG = (() => {
  try { const p = JSON.parse(localStorage.getItem("proof-dungeon:prefs") || "{}");
    if (["zh-CN", "ja", "en"].includes(p.lang)) return p.lang;
  } catch (_) {}
  return "zh-CN";
})();
function __T(i, a) {
  const entry = TLX[i];
  // Chinese overlay -> source English -> original Japanese, preserving index semantics.
  const p = LANG === "zh-CN" ? (ZH_CN[i] ?? entry[1] ?? entry[0]) :
    LANG === "en" ? (entry[1] ?? entry[0]) : entry[0];
  return a ? p.replace(/⟦([0-9]+)⟧/g, (m, k) => a[+k]) : p;
}
const RD = r => LANG === "en" ? ({ "仮定": "Hyp", "補題": "Lemma", "帰納法": "Ind", "定義": "Def" }[r] || r) :
  LANG === "zh-CN" ? ({ "仮定": "假设", "補題": "引理", "帰納法": "归纳法", "定義": "定义" }[r] || r) : r; // Inference-rule labels
if (LANG === "en") { document.documentElement.lang = "en"; document.title = "Proof Dungeon: The Labyrinth of Natural Deduction"; const bs = document.querySelector(".brand-sub"); if (bs) bs.textContent = "The Labyrinth of Natural Deduction"; }
if (LANG === "zh-CN") { document.documentElement.lang = "zh-CN"; document.title = "证明迷宫 · Proof Dungeon"; const bs = document.querySelector(".brand-sub"); if (bs) bs.textContent = "自然演绎与逻辑证明"; const bn = document.querySelector(".brand-name"); if (bn) bn.textContent = "证明迷宫"; }

(() => {
"use strict";

/* ================= 論理式 ================= */
const SUBS = "₀₁₂₃₄₅₆₇₈₉";
const sub = s => String(s).replace(/\d/g, d => SUBS[+d]);
const OP = { and: "∧", or: "∨", imp: "→" };
const esc = s => String(s).replace(/[&<>"]/g, c => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c]));

function parse(src) {
  const flat = src.replace(/\s+/g, ""), toks = flat.match(/->|<=|[()&|~#!?.,=*+<∈⊆∩∪ᶜ≠∅]|[A-Z]|[a-z]'?|\d+/g) || [];
  if (toks.join("") !== flat) { let k = 0, pos = 0; for (const tk of toks) { if (flat.startsWith(tk, pos)) pos += tk.length; else break; k++; } // 使えない文字を、位置つきで知らせる
    throw new Error(L1(__T(0, [flat[pos], pos + 1]), `Unknown character "${flat[pos]}" (position ${pos + 1})`)); }
  let i = 0;
  const imp = () => { const l = or(); if (toks[i] === "->") { i++; return { t: "imp", l, r: imp() }; } return l; };
  const or = () => { let l = and(); while (toks[i] === "|") { i++; l = { t: "or", l, r: and() }; } return l; };
  const and = () => { let l = atom(); while (toks[i] === "&") { i++; l = { t: "and", l, r: atom() }; } return l; };
  // 項：名前・変数・数字、関数適用 f(t, …)、二項演算 s * t（群の演算。表示は s·t）
  const tAtom = () => {
    const tk = toks[i++];
    if (tk === "(") { const x = term(); if (toks[i++] !== ")") throw new Error(__T(1)); return x; }
    if (/^[a-z]'?$/.test(tk || "") && toks[i] === "(") { i++; const args = []; while (toks[i] !== ")") { args.push(term()); if (toks[i] === ",") i++; } i++; return { f: tk, args }; }
    if (/^([a-z]'?|\d+)$/.test(tk || "")) return tk;
    throw new Error(__T(2) + tk);
  };
  const prod = () => { let l = tAtom(); while (toks[i] === "*") { i++; l = { f: "*", args: [l, tAtom()] }; } return l; };
  const term = () => { let l = prod(); while (toks[i] === "+") { i++; l = { f: "+", args: [l, prod()] }; } return l; }; // 足し算 s + t（掛け算より弱い）
  // 集合の項：集合の名前（大文字）、共通部分 ∩、和 ∪、補集合 ᶜ
  const sAtom = () => { const tk = toks[i++]; if (tk === "(") { const x = setTerm(); if (toks[i++] !== ")") throw new Error(__T(1)); return x; }
    if (/^[A-Z]$/.test(tk || "")) return tk; throw new Error(__T(3) + tk); };
  const sPost = () => { let x = sAtom(); while (toks[i] === "ᶜ") { i++; x = { f: "ᶜ", args: [x] }; } return x; };
  const setTerm = () => { let l = sPost(); while (toks[i] === "∩" || toks[i] === "∪") { const op = toks[i++]; l = { f: op, args: [l, sPost()] }; } return l; };
  const setIncl = () => { const l = setTerm();
    if (toks[i] === "≠") { i++; if (toks[i++] !== "∅") throw new Error(__T(4)); return { t: "atom", n: "≠∅", args: [l] }; } // S ≠ ∅（空でない）
    if (toks[i++] !== "⊆") throw new Error(__T(5)); return { t: "atom", n: "⊆", args: [l, setTerm()] }; };
  // 項どうしの関係：=、≤、<、∈（∈ の右は集合）
  const eqAtom = () => { const l = term(), op = toks[i++];
    if (op === "=") return { t: "atom", n: "=", args: [l, term()] };
    if (op === "<=") return { t: "atom", n: "≤", args: [l, term()] };
    if (op === "<") return { t: "atom", n: "<", args: [l, term()] };
    if (op === "∈") return { t: "atom", n: "∈", args: [l, setTerm()] };
    throw new Error(__T(6)); };
  const atom = () => {
    const tk = toks[i++];
    if (tk === "(") { // 括弧でくくった論理式か、括弧で始まる項の等式か
      const save = i - 1;
      try { const f = imp(); if (toks[i++] !== ")") throw new Error(__T(1)); if (["=", "*", "<=", "<", "∈", "⊆", "∩", "∪", "ᶜ", "≠"].includes(toks[i])) throw new Error(__T(7)); return f; }
      catch (e) { i = save; try { return eqAtom(); } catch (e2) { i = save; return setIncl(); } }
    }
    if (/^([a-z]'?|\d+)$/.test(tk || "")) { i--; return eqAtom(); }
    if (tk === "~") return { t: "imp", l: atom(), r: { t: "bot" } }; // ¬A := A→⊥
    if (tk === "!" || tk === "?") { // ∀x. / ∃x.（量化子の作用域は直後の原子・括弧・否定・量化子まで）
      const v = toks[i++];
      if (toks[i] === "∈") { i++; const S = setTerm(); if (toks[i++] !== ".") throw new Error(__T(8)); const b = atom(), m = { t: "atom", n: "∈", args: [v, S] }; // ∀x∈A. / ∃x∈A.（範囲を限った量化子の略記）
        return tk === "!" ? { t: "all", v, b: { t: "imp", l: m, r: b }, bnd: true } : { t: "ex", v, b: { t: "and", l: m, r: b }, bnd: true }; }
      if (toks[i++] !== ".") throw new Error(__T(8));
      return { t: tk === "!" ? "all" : "ex", v, b: atom() };
    }
    if (/^[A-Z]$/.test(tk || "") && ["⊆", "∩", "∪", "ᶜ", "≠"].includes(toks[i])) { i--; return setIncl(); } // A ⊆ B、A ≠ ∅
    if (/^[A-Z]$/.test(tk || "") && toks[i] === "(") { // 述語 P(x, y)
      i++; const args = [];
      while (toks[i] !== ")") { args.push(term()); if (toks[i] === ",") i++; }
      i++;
      return { t: "atom", n: tk, args };
    }
    if (tk === "#") return { t: "bot" };
    if (/^[A-Z]$/.test(tk || "")) return { t: "atom", n: tk };
    throw new Error(__T(9) + tk);
  };
  const f = imp();
  if (i !== toks.length) throw new Error(__T(10));
  return f;
}
// 論理式の同一性は、束縛変数の名前の違いを無視して判定する（α同値）
const eq = (a, b) => a === b || fkey(a) === fkey(b);
function fkey(f, bound = []) {
  switch (f.t) {
    case "atom": return f.args && f.args.length ? f.n + "(" + f.args.map(t => termKey(t, bound)).join(",") + ")" : f.n;
    case "bot": return "#";
    case "all": case "ex": return (f.t === "all" ? "A" : "E") + "." + fkey(f.b, [...bound, f.v]);
    default: return "(" + fkey(f.l, bound) + { and: "&", or: "|", imp: ">" }[f.t] + fkey(f.r, bound) + ")";
  }
}
function termKey(t, bound = []) {
  if (typeof t === "string") return bound.includes(t) ? "#" + (bound.length - 1 - bound.lastIndexOf(t)) : t;
  return t.f + "(" + t.args.map(a => termKey(a, bound)).join(",") + ")";
}
const termEq = (a, b) => termKey(a) === termKey(b);
const tInst = (x, v, t) => typeof x === "string" ? (x === v ? t : x) : { f: x.f, args: x.args.map(a => tInst(a, v, t)) };
// 項に現れる名前（要素の番号は除く）と、式に現れるすべての名前（自由・束縛とも）
const tNames = (t, out = new Set()) => { if (typeof t === "string") { if (!/^\d+$/.test(t)) out.add(t); } else t.args.forEach(a => tNames(a, out)); return out; };
function allNames(f, out = new Set()) {
  switch (f.t) {
    case "atom": (f.args || []).forEach(a => tNames(a, out)); break;
    case "bot": break;
    case "all": case "ex": out.add(f.v); allNames(f.b, out); break;
    default: allNames(f.l, out); allNames(f.r, out);
  }
  return out;
}
// 束縛変数の付け替え先：avoid に含まれない名前（x → x′ → z, w, u, v, y → x1, x2, …）
function freshVar(base, avoid) {
  for (const c of [base[0] + "'", "z", "w", "u", "v", "y", "x"]) if (!avoid.has(c)) return c;
  for (let i = 1; ; i++) if (!avoid.has(base[0] + i)) return base[0] + i;
}
// 束縛変数 v に項 t を代入する（捕獲を避ける代入）。t の名前が内側の量化子に捕まるときは、その量化子の変数を先に付け替える
//   例：∃x (f(x) = y) の y に x を代入すると ∃x′ (f(x′) = x)。∃x (f(x) = x) にはしない
function inst(f, v, t, tn) {
  switch (f.t) {
    case "atom": return f.args && f.args.length ? { ...f, args: f.args.map(x => tInst(x, v, t)) } : f;
    case "bot": return f;
    case "all": case "ex": {
      if (f.v === v) return f;
      const T = tn || tNames(t);
      if (T.has(f.v) && freeNames(f.b).has(v)) {
        const nv = freshVar(f.v, new Set([...T, ...allNames(f.b), v]));
        return { ...f, v: nv, b: inst(inst(f.b, f.v, nv), v, t, T) };
      }
      return { ...f, b: inst(f.b, v, t, T) };
    }
    default: return { ...f, l: inst(f.l, v, t, tn), r: inst(f.r, v, t, tn) };
  }
}
// 式の中の量化子のうち、変数が names に含まれるものを付け替える（書き換えで、項の名前が量化子に捕まらないように）
function avoidNames(f, names) {
  if (!names.size) return f;
  switch (f.t) {
    case "atom": case "bot": return f;
    case "all": case "ex": {
      if (names.has(f.v)) { const nv = freshVar(f.v, new Set([...names, ...allNames(f)])); return { ...f, v: nv, b: avoidNames(inst(f.b, f.v, nv), names) }; }
      return { ...f, b: avoidNames(f.b, names) };
    }
    default: return { ...f, l: avoidNames(f.l, names), r: avoidNames(f.r, names) };
  }
}
// 項 from の出現（左から数えた番号）のうち sel に含まれるものを to に置き換える
//   量化子の変数が from や to の名前と同じときは、先にその量化子を付け替える（捕獲を避ける）
function replaceOcc(f, from, to, sel, ctr = { i: 0 }) { return replaceOcc0(avoidNames(f, new Set([...tNames(from), ...tNames(to)])), from, to, sel, ctr); }
function replaceOcc0(f, from, to, sel, ctr) {
  const rt = t => { if (termEq(t, from)) { const k = ctr.i++; return sel.has(k) ? to : t; } return typeof t === "string" ? t : { f: t.f, args: t.args.map(rt) }; };
  switch (f.t) {
    case "atom": return f.args && f.args.length ? { ...f, args: f.args.map(rt) } : f;
    case "bot": return f;
    case "all": case "ex": return { ...f, b: replaceOcc0(f.b, from, to, sel, ctr) };
    default: { const l = replaceOcc0(f.l, from, to, sel, ctr); return { ...f, l, r: replaceOcc0(f.r, from, to, sel, ctr) }; }
  }
}
function countOcc(f, from) { const ctr = { i: 0 }; replaceOcc(f, from, from, new Set(), ctr); return ctr.i; }
// 出現ごとにボタンを付けて表示する（どれを書き換えるか選ぶため）
function fhOcc(f, from, sel, ctr, nested) { return ctr ? fhOcc0(f, from, sel, ctr, nested) : fhOcc0(avoidNames(f, tNames(from)), from, sel, { i: 0 }, nested); }
function fhOcc0(f, from, sel, ctr, nested) {
  const tk = (t, pp) => { if (termEq(t, from)) { const k = ctr.i++; return `<button type="button" class="occ${sel.has(k) ? " on" : ""}" data-occ="${k}">${termH(t, typeof t !== "string" && PREC[t.f] && needPar(PREC[t.f], pp) ? true : undefined)}</button>`; }
    if (typeof t === "string") return termH(t);
    if (PREC[t.f]) { const p = PREC[t.f], s = `${tk(t.args[0], p)}<span class="op">${t.f === "*" ? "·" : t.f}</span>${tk(t.args[1], p)}`; return needPar(p, pp) ? parWrap(s) : s; }
    if (t.f === "ᶜ") return `${tk(t.args[0], true)}<span class="op">ᶜ</span>`;
    if (t.f === "i" && t.args.length === 1) return `${tk(t.args[0], true)}<sup class="inv">−1</sup>`;
    return `<i class="fn">${t.f}</i>(${t.args.map(tk).join(",")})`; };
  if (f.t === "atom" && INFIX[f.n]) return `${tk(f.args[0])}<span class="op">${INFIX[f.n]}</span>${tk(f.args[1])}`;
  if (f.t === "atom") return `<i class="at">${f.n}</i>` + (f.args && f.args.length ? `(${f.args.map(tk).join(",")})` : "");
  if (f.t === "bot") return `<span class="botc">⊥</span>`;
  if (f.t === "all" || f.t === "ex") return `<span class="q">${QS[f.t]}${termH(f.v)}</span><span class="par">(</span>${fhOcc0(f.b, from, sel, ctr)}<span class="par">)</span>`;
  if (isNeg(f)) return f.l.t === "atom" && INFIX[f.l.n] ? `<span class="op neg">¬</span><span class="par">(</span>${fhOcc0(f.l, from, sel, ctr)}<span class="par">)</span>` : `<span class="op neg">¬</span>${fhOcc0(f.l, from, sel, ctr, true)}`;
  const s = fhOcc0(f.l, from, sel, ctr, true) + `<span class="op">${OP[f.t]}</span>` + fhOcc0(f.r, from, sel, ctr, true);
  return nested ? `<span class="par">(</span>${s}<span class="par">)</span>` : s;
}
// P と Q が、P の s のいくつかを t に置き換えただけの違いか（=E の検査）
function sameUpTo(P, Q, s, t, bp = [], bq = []) {
  const idx = (x, B) => B.length - 1 - B.lastIndexOf(x);
  const freeIn = (a, B) => ![...tNames(a)].some(n => B.includes(n)); // 項 a の名前が、ここで束縛されていない
  const tt = (a, b) => {
    if (typeof a === "string" && typeof b === "string" && (bp.includes(a) || bq.includes(b))) return bp.includes(a) && bq.includes(b) && idx(a, bp) === idx(b, bq); // 束縛変数どうしは位置で比べる
    if (termEq(a, s) && termEq(b, t) && freeIn(a, bp) && freeIn(b, bq)) return true; // s を t に置き換えた出現（捕獲されない位置だけ）
    if (typeof a === "string" || typeof b === "string") return typeof a === "string" && typeof b === "string" && a === b;
    return a.f === b.f && a.args.length === b.args.length && a.args.every((x, i) => tt(x, b.args[i]));
  };
  if (P.t !== Q.t) return false;
  switch (P.t) {
    case "atom": return P.n === Q.n && (P.args || []).length === (Q.args || []).length && (P.args || []).every((x, i) => tt(x, Q.args[i]));
    case "bot": return true;
    case "all": case "ex": return sameUpTo(P.b, Q.b, s, t, [...bp, P.v], [...bq, Q.v]);
    default: return sameUpTo(P.l, Q.l, s, t, bp, bq) && sameUpTo(P.r, Q.r, s, t, bp, bq);
  }
}
const isEq = f => f && f.t === "atom" && f.n === "=";
const termSize = t => typeof t === "string" ? 1 : 1 + t.args.reduce((a, x) => a + termSize(x), 0);
// 定義による略記の展開（一段だけ）：A⊆B ⇒ ∀x(x∈A→x∈B)、t∈A∩B ⇒ t∈A ∧ t∈B、t∈A∪B ⇒ t∈A ∨ t∈B、t∈Aᶜ ⇒ ¬(t∈A)
const mem = (t, S) => ({ t: "atom", n: "∈", args: [t, S] });
function defUnfold(f) {
  if (!f || f.t !== "atom") return null;
  if (f.n === "⊆") return { t: "all", v: "x", b: { t: "imp", l: mem("x", f.args[0]), r: mem("x", f.args[1]) } };
  if (f.n === "≠∅") return { t: "ex", v: "x", b: mem("x", f.args[0]) }; // S ≠ ∅ ⇔ ∃x (x ∈ S)
  if (f.n === "≤" && STAGE && STAGE.leDef) return { t: "ex", v: "z", b: { t: "atom", n: "=", args: [{ f: "+", args: [f.args[0], "z"] }, f.args[1]] } }; // 自然数の順序の定義
  if (f.n === "∈" && typeof f.args[1] !== "string") {
    const [t, S] = f.args;
    if (S.f === "∩") return { t: "and", l: mem(t, S.args[0]), r: mem(t, S.args[1]) };
    if (S.f === "∪") return { t: "or", l: mem(t, S.args[0]), r: mem(t, S.args[1]) };
    if (S.f === "ᶜ") return { t: "imp", l: mem(t, S.args[0]), r: { t: "bot" } };
  }
  return null;
}
const DEFNAME = { "⊆": __T(11), "∩": __T(12), "∪": __T(13), "ᶜ": __T(14), "≤": __T(15), "≠": __T(16) };
const defSym = f => f.n === "⊆" || f.n === "≤" ? f.n : f.n === "≠∅" ? "≠" : f.args[1].f;
// 定義された記号をボタンにして表示する
function fhDef(f, attr) {
  const btn = sym => __T(17, [attr, DEFNAME[sym], sym]);
  if (f.n === "⊆" || f.n === "≤") return `${termH(f.args[0])}${btn(f.n)}${termH(f.args[1])}`;
  if (f.n === "≠∅") return `${termH(f.args[0])}${btn("≠")}<span class="emp">∅</span>`;
  const [t, S] = f.args;
  if (S.f === "ᶜ") return `${termH(t)}<span class="op">∈</span>${termH(S.args[0], true)}${btn("ᶜ")}`;
  return `${termH(t)}<span class="op">∈</span>${termH(S.args[0], true)}${btn(S.f)}${termH(S.args[1], true)}`;
}
function freeNames(f, bound = [], out = new Set()) {
  switch (f.t) {
    case "atom": { const walk = t => { if (typeof t === "string") { if (!bound.includes(t) && !/^\d+$/.test(t)) out.add(t); } else t.args.forEach(walk); }; (f.args || []).forEach(walk); break; }
    case "bot": break;
    case "all": case "ex": freeNames(f.b, [...bound, f.v], out); break;
    default: freeNames(f.l, bound, out); freeNames(f.r, bound, out);
  }
  return out;
}
const SETOPS = ["∩", "∪", "ᶜ"];
// 二項演算の強さ：掛け算は足し算より強い。同じ強さが入れ子になるときは括弧を付けて、くくり方を見せる
const PREC = { "+": 1, "*": 2, "∩": 1, "∪": 1 };
const needPar = (p, pp) => pp === true || (typeof pp === "number" && p <= pp);
const parWrap = s => `<span class="par">(</span>${s}<span class="par">)</span>`;
function termH(t, nested) {
  if (typeof t !== "string") {
    if (PREC[t.f]) { const p = PREC[t.f], s = `${termH(t.args[0], p)}<span class="op">${t.f === "*" ? "·" : t.f}</span>${termH(t.args[1], p)}`; return needPar(p, nested) ? parWrap(s) : s; }
    if (t.f === "ᶜ") return `${termH(t.args[0], true)}<span class="op sup-op">ᶜ</span>`;
    if (t.f === "i" && t.args.length === 1) return `${termH(t.args[0], true)}<sup class="inv">−1</sup>`; // 逆元 x⁻¹
    return `<i class="fn">${t.f}</i>(${t.args.map(a => termH(a)).join(",")})`;
  }
  if (t === "0") return `<span class="num">0</span>`; // 自然数の 0
  if (/^\d+$/.test(t)) return `<b class="el">${t}</b>`;
  if (/^[A-Z]$/.test(t)) return `<i class="st">${t}</i>`; // 集合の名前
  return `<i class="tm">${t[0]}</i>${t[1] === "'" ? "′" + sub(t.slice(2)) : sub(t.slice(1))}`;
}
const QS = { all: "∀", ex: "∃" };
const INFIX = { "=": "=", "≤": "≤", "<": "<", "∈": "∈", "⊆": "⊆" };
const qBody = (b, brk) => (b.t === "and" || b.t === "or" || (b.t === "imp" && !isNeg(b)) || (b.t === "atom" && INFIX[b.n])) ? `<wbr><span class="par">(</span>${fh(b, false, brk)}<span class="par">)</span>` : fh(b, true, brk);
// 長い式は、主結合子（量化子の直後の ∧・∨・→）の手前で改行できるようにする（<wbr>）
// ¬A を A→⊥ と展開して見せるかどうか（4-1 だけ展開して、¬ の正体を見せる）
let NEG_SUGAR = true;
function withNeg(v, fn) { const old = NEG_SUGAR; NEG_SUGAR = v; try { return fn(); } finally { NEG_SUGAR = old; } }
const isNeg = f => NEG_SUGAR && f.t === "imp" && f.r.t === "bot";
const fhNB = h => h.replace(/<[^>]+>/g, "").length <= 16 ? h.replace(/<wbr>/g, "") : h; // 短い部分式の中では改行しない（<wbr> を除く。nowrap では <wbr> を止められないため）
// 範囲を限った量化子として表示できるか（∀x(x∈A→φ) を ∀x∈A. φ、∃x(x∈A∧φ) を ∃x∈A. φ と書く。式を読み込んだときの書き方だけを保つ）
const bndOK = f => f.bnd && f.b && f.b.t === (f.t === "all" ? "imp" : "and") && f.b.l.t === "atom" && f.b.l.n === "∈" && f.b.l.args[0] === f.v && !isNeg(f.b);
const bndHead = f => `${QS[f.t]}${termH(f.v)}<span class="op">∈</span>${termH(f.b.l.args[1], true)}`;
const bndDot = `<span class="bdot">.</span>`;
function fh(f, nested, brk) {
  if ((f.t === "all" || f.t === "ex") && bndOK(f)) return `<span class="q">${bndHead(f)}</span>${bndDot}${fh(f.b.r, true, brk)}`;
  if (f.t === "atom" && f.n === "≠∅") return `${termH(f.args[0])}<span class="op">≠</span><span class="emp">∅</span>`;
  if (f.t === "atom" && INFIX[f.n]) return `${termH(f.args[0])}<span class="op">${INFIX[f.n]}</span>${termH(f.args[1])}`;
  if (f.t === "atom") return `<i class="at">${f.n}</i>` + (f.args && f.args.length ? `<span class="args">(${f.args.map(a => termH(a)).join(",")})</span>` : "");
  if (f.t === "all" || f.t === "ex") return `<span class="q">${QS[f.t]}${termH(f.v)}</span>${qBody(f.b, brk)}`;
  if (f.t === "bot") return `<span class="botc">⊥</span>`;
  if (isNeg(f)) return `<span class="op neg">¬</span>${negArg(f.l, brk)}`;
  const s = fhNB(fh(f.l, true)) + "<wbr>" + `<span class="op">${OP[f.t]}</span>` + fhNB(fh(f.r, true)); // 改行は ∧・∨・→ の手前で。短い部分式は途中で折らない（構造の切れ目で改行されやすくする）
  return nested ? `<span class="par">(</span>${s}<span class="par">)</span>` : s;
}
function fhTop(f, attr) {
  if (f.t === "atom" && f.n === "=" && attr) return __T(18, [termH(f.args[0]), attr, termH(f.args[1])]);
  if (f.t === "atom" || f.t === "bot" || !attr) return fh(f, false, true);
  if ((f.t === "all" || f.t === "ex") && bndOK(f)) return __T(19, [attr, QS[f.t], bndHead(f), bndDot, fh(f.b.r, true, true)]);
  if (f.t === "all" || f.t === "ex") return __T(20, [attr, QS[f.t], QS[f.t], termH(f.v), qBody(f.b, true)]);
  if (isNeg(f)) return __T(21, [attr, negArg(f.l)]);
  const label = { and: __T(22), or: __T(23), imp: __T(24) }[f.t];
  return fh(f.l, true) + "<wbr>" + `<button type="button" class="mainop" ${attr} aria-label="${label}">${OP[f.t]}</button>` + fh(f.r, true);
}
const FF = f => `<span class="f">${fh(f, false, true)}</span>`;
// ¬ の後ろの式：= や ∈ などの関係は括弧でくくる（¬(x < y)）
function negArg(a, brk) { return a.t === "atom" && INFIX[a.n] ? `<span class="par">(</span>${fh(a)}<span class="par">)</span>` : fh(a, true, brk); } // brk：¬ の内側の主結合子の手前でも改行できるようにする
const F = s => FF(parse(s));
const FE = s => withNeg(false, () => F(s)); // ¬ を展開して表示
const nm = n => `<span class="nm">${n[0]}${sub(n.slice(1))}</span>`;

/* ================= ステージ ================= */
const WORLDS = [
  { id: 1, name: __T(25), rules: __T(26), stages: [
    { id: "1-1", name: __T(27), prem: ["P", "Q"], goal: "P & Q", par: 3,
      lesson: __T(28, [F("P&Q"), F("P"), F("Q")]),
      hints: [__T(29, [F("P&Q"), F("P"), F("Q")]),
              __T(30),
              __T(31, [F("P"), F("P"), F("Q"), F("Q")])] },
    { id: "1-2", name: __T(32), prem: ["P & Q"], goal: "Q & P", par: 4,
      lesson: __T(33, [F("A&B"), F("A"), F("B")]),
      hints: [__T(34, [F("P&Q"), F("Q"), F("P")]),
              __T(35),
              __T(36, [F("Q"), F("Q"), F("P"), F("P")])],
      specNote: __T(37) },
    { id: "1-3", name: __T(38), prem: ["Q"], goal: "P -> (P & Q)", par: 4,
      lesson: __T(39, [F("A->B"), F("A")]),
      hints: [__T(40, [F("P->(P&Q)"), F("P"), F("P&Q")]),
              __T(41, [F("Q")]),
              __T(42, [F("P"), F("P"), F("Q"), F("Q")])] },
    { id: "1-4", name: __T(43), boss: true, prem: [], goal: "(P & (Q & R)) -> ((P & Q) & R)", par: 8,
      lesson: __T(44),
      hints: [__T(45, [F("P&(Q&R)")]),
              __T(46),
              __T(47, [F("P&(Q&R)"), F("Q&R"), F("P&Q"), F("P"), F("Q"), F("R")])] },
  ]},
  { id: 2, name: __T(48), rules: __T(49), stages: [
    { id: "2-1", name: __T(50), prem: ["P", "P -> Q"], goal: "Q", par: 2,
      lesson: __T(51, [F("A->B"), F("A"), F("B"), F("P"), F("P->Q"), F("Q"), F("P->Q"), F("Q"), F("P")]),
      hints: [__T(52, [F("P"), F("P->Q"), F("Q")]),
              __T(53, [F("P"), F("P->Q"), F("P->Q"), F("Q")]),
              __T(54, [F("P"), F("P->Q"), F("Q"), F("Q")])] },
    { id: "2-2", name: __T(55), prem: [], goal: "P -> ((P -> Q) -> Q)", par: 4,
      lesson: __T(56),
      hints: [__T(57, [F("P"), F("P->Q")]),
              __T(58, [F("P"), F("P->Q")]),
              __T(59, [F("P"), F("P->Q"), F("Q"), F("Q")])] },
    { id: "2-3", pid: "2-rooms", name: __T(60), prem: [], goal: "(P -> P) & (Q -> (P -> Q))", par: 6,
      lesson: __T(61),
      hints: [__T(62),
              __T(63, [F("P->P"), F("P"), F("P")]),
              __T(64, [F("P"), F("P"), F("Q"), F("Q")])],
      doneNote: __T(65, [F("Q->(P->Q)"), F("P")]) },
    { id: "2-4", pid: "2-3", name: __T(66), prem: ["P -> Q", "Q -> R"], goal: "P -> R", par: 4,
      lesson: __T(67, [F("R"), F("R")]),
      hints: [__T(68, [F("P"), F("R")]),
              __T(69, [F("R"), F("Q->R"), F("Q"), F("P->Q"), F("P")]),
              __T(70, [F("Q->R"), F("R"), F("P->Q"), F("Q"), F("P"), F("P")])] },
    { id: "2-5", pid: "2-4", name: __T(71), boss: true, prem: ["Q", "(P -> Q) -> R"], goal: "R", par: 3,
      lesson: __T(72, [F("R")]),
      hints: [__T(73, [F("R"), F("(P->Q)->R")]),
              __T(74, [F("(P->Q)->R"), F("R"), F("P->Q"), F("P->Q")]),
              __T(75, [F("(P->Q)->R"), F("R"), F("Q"), F("Q")])],
      doneNote: __T(76, [F("P"), F("Q"), F("P"), F("Q"), F("Q"), F("P->Q")]) },
  ]},
];
WORLDS.push(
  { id: 3, name: __T(77), rules: __T(78), stages: [
    { id: "3-1", name: __T(79), prem: ["P"], goal: "P | Q", par: 2,
      lesson: __T(80, [F("A|B"), F("A"), F("B")]),
      hints: [__T(81, [F("P"), F("P|Q")]),
              __T(82, [F("P")]),
              __T(83, [F("P"), F("P")])] },
    { id: "3-2", name: __T(84), prem: ["P | Q"], goal: "Q | P", par: 5,
      lesson: __T(85, [F("A|B"), F("A"), F("B"), F("A"), F("B"), F("A"), F("B")]),
      hints: [__T(86),
              __T(87, [F("P|Q")]),
              __T(88, [F("P"), F("Q")])] },
    { id: "3-3", name: __T(89), prem: ["P | Q", "P -> R", "Q -> R"], goal: "R", par: 5,
      lesson: __T(90, [F("R")]),
      hints: [__T(91, [F("P|Q"), F("P"), F("Q")]),
              __T(92, [F("P|Q"), F("P"), F("Q"), F("R"), F("P"), F("P->R"), F("Q"), F("Q->R")]),
              __T(93, [F("P|Q"), F("P->R"), F("R"), F("P"), F("P"), F("Q->R"), F("R"), F("Q"), F("Q")])] },
    { id: "3-4", name: __T(94), prem: ["P | Q"], goal: "(P -> Q) -> Q", par: 5,
      lesson: __T(95),
      hints: [__T(96),
              __T(97),
              __T(98, [F("P|Q"), F("P->Q"), F("Q"), F("P"), F("P"), F("Q"), F("Q")])] },
    { id: "3-5", name: __T(99), boss: true, prem: ["P & (Q | R)"], goal: "(P & Q) | (P & R)", par: 10,
      lesson: __T(100),
      hints: [__T(101, [F("Q"), F("R")]),
              __T(102, [F("Q|R")]),
              __T(103, [F("Q|R"), F("P"), F("Q"), F("P"), F("R")])] },
  ]});
WORLDS.push(
  { id: 4, name: __T(104), rules: __T(105), stages: [
    { id: "4-1", name: __T(106), expandNeg: true, prem: ["P", "P -> #"], goal: "Q", par: 2,
      lesson: __T(107, [FE("P"), FE("P->#")]),
      hints: [__T(108, [FE("P->#"), FE("P")]),
              __T(109),
              __T(110, [FE("P"), FE("P->#"), FE("Q")])] },
    { id: "4-2", name: __T(111), prem: [], goal: "P -> ~~P", par: 4,
      lesson: __T(112, [F("~A"), FE("A->#"), F("A"), F("~A"), F("A"), F("~A"), F("A")]),
      hints: [__T(113, [F("P"), F("~~P")]),
              __T(114, [F("P"), F("~P")]),
              __T(115, [F("~P"), F("P"), F("P")])] },
    { id: "4-3", name: __T(116), prem: ["P -> Q"], goal: "~Q -> ~P", par: 5,
      lesson: __T(117, [F("~Q->~P"), F("~Q"), F("P")]),
      hints: [__T(118, [F("~Q"), F("P")]),
              __T(119, [F("~Q"), F("Q"), F("P->Q")]),
              __T(120, [F("~Q"), F("P->Q"), F("Q"), F("P"), F("P")])] },
    { id: "4-4", name: __T(121), prem: ["P | Q", "~P"], goal: "Q", par: 4,
      lesson: __T(122),
      hints: [__T(123, [F("P|Q")]),
              __T(124, [F("P"), F("P"), F("~P"), F("Q")]),
              __T(125, [F("P|Q"), F("P"), F("~P"), F("Q"), F("Q"), F("Q")])] },
    { id: "4-5", name: __T(126), boss: true, prem: [], goal: "~~(P | ~P)", par: 7,
      lesson: __T(127, [F("P|~P")]),
      hints: [__T(128, [F("~~A"), F("~A"), F("~(P|~P)"), F("~P")]), __T(129, [F("~(P|~P)"), F("P"), F("~P")]),
              __T(130, [F("~(P|~P)"), F("P|~P"), F("~P")]),
              __T(131, [F("~(P|~P)"), F("~(P|~P)"), F("P"), F("P")])] },
  ]});
WORLDS.push(
  { id: 5, name: __T(132), rules: __T(133), stages: [
    { id: "5-1", name: __T(134), kind: "refute", prem: [], goal: "P | ~P", par: 2,
      lesson: __T(135, [F("~A"), F("A->B"), F("~P"), F("P")]),
      hints: [__T(136, [F("P|~P")]),
              __T(137, [F("P|~P"), F("P"), F("~P"), F("~P"), F("P")]),
              __T(138, [F("P"), F("P"), F("~P")])] },
    { id: "5-2", name: __T(139), kind: "refute", prem: [], goal: "~~P -> P", par: 2,
      lesson: __T(140, [F("A->B"), F("A"), F("B"), F("~~P->P")]),
      hints: [__T(141, [F("~~P"), F("P")]),
              __T(142),
              __T(143, [F("P"), F("~P"), F("~~P")])] },
    { id: "5-3", name: __T(144), kind: "refute", prem: [], goal: "((P -> Q) -> P) -> P", par: 2,
      lesson: __T(145),
      hints: [__T(146, [F("(P->Q)->P"), F("P")]),
              __T(147, [F("Q")]),
              __T(148, [F("P"), F("Q"), F("P->Q"), F("P"), F("Q"), F("(P->Q)->P")])] },
    { id: "5-4", name: __T(149), kind: "refute", prem: ["~(P & Q)"], goal: "~P | ~Q", par: 3,
      lesson: __T(150),
      hints: [__T(151, [F("~(P&Q)"), F("~P|~Q")]),
              __T(152, [F("~P"), F("~Q"), F("P"), F("Q"), F("P"), F("Q"), F("~(P&Q)")]),
              __T(153, [F("P"), F("Q")])] },
    { id: "5-5", name: __T(154), boss: true, kind: "judge", par: null,
      lesson: __T(155),
      hints: [__T(156),
              __T(157, [F("~~P"), F("P")]),
              __T(158, [F("P"), F("Q"), F("P"), F("Q")])],
      parts: [
        { key: "A", prem: [], goal: "~~~P -> ~P", real: true, note: __T(159, [F("~~~P"), F("~P")]) },
        { key: "B", prem: [], goal: "(~P -> ~Q) -> (Q -> P)", real: false, note: __T(160, [F("~~P"), F("P")]) },
        { key: "C", prem: [], goal: "(P -> Q) | (Q -> P)", real: false, note: __T(161, [F("P"), F("Q")]) },
      ] },
  ]});
WORLDS.push(
  { id: 6, name: __T(162), rules: __T(163), stages: [
    { id: "6-1", name: __T(164), prem: [], goal: "~~P -> P", par: 4,
      lesson: __T(165, [F("A"), F("A"), F("~A"), F("A"), F("~~P->P")]),
      hints: [__T(166, [F("~~P"), F("P")]),
              __T(167, [F("P"), F("~P"), F("~~P")]),
              __T(168, [F("~~P"), F("~P"), F("~P")])] },
    { id: "6-2", name: __T(169), prem: [], goal: "P | ~P", par: 7,
      lesson: __T(170, [F("P|~P")]),
      hints: [__T(171, [F("~(P|~P)")]),
              __T(172, [F("~(P|~P)"), F("P|~P"), F("~P")]),
              __T(173, [F("~(P|~P)"), F("~(P|~P)"), F("P"), F("P")])] },
    { id: "6-3", name: __T(174), noRAA: true, premClassical: "lem", prem: ["P | ~P", "~~P"], goal: "P", par: 4,
      lesson: __T(175, [F("P|~P"), F("~~P"), F("~P"), F("P")]),
      hints: [__T(123, [F("P|~P")]),
              __T(176, [F("~P"), F("~P"), F("~~P")]),
              __T(177, [F("P|~P"), F("P"), F("P"), F("~P"), F("~~P"), F("P")])] },
    { id: "6-4", name: __T(178), noRAA: true, premClassical: "dne", prem: ["~~(P | ~P) -> (P | ~P)"], goal: "P | ~P", par: 8,
      lesson: __T(179, [F("~~(P|~P)->(P|~P)")]),
      hints: [__T(180, [F("P|~P"), F("~~(P|~P)")]),
              __T(181, [F("~~(P|~P)")]),
              __T(182, [F("~(P|~P)"), F("~(P|~P)"), F("P"), F("P")])],
      doneNote: __T(183, [F("~A"), F("~~A"), F("A"), F("P")]) },
    { id: "6-5", name: __T(184), prem: ["~(P & Q)"], goal: "~P | ~Q", par: 11,
      lesson: __T(185, [F("P"), F("Q"), F("P"), F("Q"), F("~P|~Q")]),
      hints: [__T(186, [F("~(~P|~Q)"), F("P"), F("Q"), F("~(P&Q)")]), __T(187, [F("~(~P|~Q)")]),
              __T(188, [F("~(P&Q)"), F("P&Q"), F("P"), F("Q")]),
              __T(189, [F("~(P&Q)"), F("P"), F("~(~P|~Q)"), F("~P"), F("Q")])] },
    { id: "6-6", name: __T(190), boss: true, kind: "judge", par: null,
      lesson: __T(191),
      hints: [__T(192),
              __T(193),
              __T(194, [F("P"), F("Q"), F("P"), F("(P->Q)->P")])],
      parts: [
        { key: "A", prem: [], goal: "(~P -> Q) -> (P | Q)", real: true, note: __T(195, [F("P"), F("Q"), F("P"), F("Q")]) },
        { key: "B", prem: [], goal: "(P -> Q) -> (Q -> P)", real: false, note: __T(196, [F("P"), F("Q")]) },
        { key: "C", prem: [], goal: "(P -> Q) | (Q -> P)", real: true, note: __T(197, [F("Q"), F("P->Q"), F("Q->P")]) },
        { key: "D", prem: [], goal: "((P -> Q) -> P) -> P", real: true, note: __T(198) },
      ] },
  ]});
WORLDS.push(
  { id: 7, name: __T(199), rules: __T(200), stages: [
    { id: "7-1", name: __T(201), prem: ["!x.(P(x) & Q(x))"], goal: "!x.P(x)", par: 4,
      lesson: __T(202, [F("!x.A(x)"), termH("x"), F("A(x)"), termH("a"), F("A(a)"), termH("a"), F("!x.A(x)"), F("A(a)")]),
      hints: [__T(203, [F("!x.P(x)"), termH("a")]),
              __T(204, [F("!x.(P(x)&Q(x))"), termH("a"), F("P(a)&Q(a)")]),
              __T(205, [termH("a"), F("P(a)&Q(a)"), F("P(a)")])] },
    { id: "7-2", name: __T(206), prem: ["!x.(P(x) -> Q(x))", "!x.P(x)"], goal: "!x.Q(x)", par: 5,
      lesson: __T(207, [termH("a")]),
      hints: [__T(208, [termH("a"), F("Q(a)")]),
              __T(209, [F("!x.(P(x)->Q(x))"), termH("a"), F("!x.P(x)"), termH("a")]),
              __T(210, [F("!x.(P(x)->Q(x))"), termH("a"), F("P(a)->Q(a)"), F("Q(a)"), F("!x.P(x)"), termH("a"), F("P(a)")])] },
    { id: "7-3", name: __T(211), prem: ["?x.(P(x) & Q(x))"], goal: "?x.P(x)", par: 4,
      lesson: __T(212, [F("?x.A(x)"), F("A(x)"), termH("x"), `<span class="f"><i class="at">A</i>(…)</span>`, F("?x.A(x)"), F("A")]),
      hints: [__T(213),
              __T(214, [F("P(a)&Q(a)"), termH("a")]),
              __T(215, [F("P(a)&Q(a)"), termH("a"), F("P(a)")])] },
    { id: "7-4", name: __T(216), prem: ["~?x.P(x)"], goal: "!x.~P(x)", par: 5,
      lesson: __T(217, [F("P"), F("P")]),
      hints: [__T(218, [termH("a")]),
              __T(219, [F("~?x.P(x)"), F("?x.P(x)"), termH("a")]),
              __T(220, [F("~?x.P(x)"), termH("a"), F("P(a)")])] },
    { id: "7-5", name: __T(221), boss: true, prem: ["?y.!x.R(x,y)"], goal: "!x.?y.R(x,y)", par: 5,
      lesson: __T(222, [termH("y"), termH("x"), F("R(x,y)"), termH("x"), termH("y"), F("R(x,y)")]),
      hints: [__T(223),
              __T(224, [termH("a"), F("R"), termH("b")]),
              __T(225, [termH("b"), F("!x.R(x,b)"), termH("a"), F("R(a,b)")])] },
  ]},
  { id: 8, name: __T(226), rules: __T(227), stages: [
    { id: "8-1", name: __T(228), prem: ["~!x.P(x)"], goal: "?x.~P(x)", par: 7,
      lesson: __T(229, [F("P"), F("P")]),
      hints: [__T(230, [F("~?x.~P(x)")]),
              __T(231, [F("~!x.P(x)"), F("!x.P(x)"), termH("a")]),
              __T(232, [F("~!x.P(x)"), F("~?x.~P(x)"), termH("a"), F("~P(a)")])] },
    { id: "8-2", name: __T(233), prem: [], goal: "?x.(P(x) -> !y.P(y))", par: 11,
      lesson: __T(234, [termH("x"), termH("x")]),
      hints: [__T(235, [F("~?x.(P(x)->!y.P(y))")]),
              __T(236, [F("!y.P(y)")]),
              __T(237, [F("~?x.(P(x)->!y.P(y))"), termH("b"), F("P(b)"), F("~P(b)")])],
      doneNote: __T(238) },
    { id: "8-3", name: __T(239), boss: true, kind: "judge", par: null,
      lesson: __T(240),
      hints: [__T(241),
              __T(242, [F("R"), F("P"), F("Q")]),
              __T(243, [F("R"), F("P(1)"), F("Q(2)")])],
      parts: [
        { key: "A", prem: [], goal: "(?y.!x.R(x,y)) -> (!x.?y.R(x,y))", real: true, note: __T(244) },
        { key: "B", prem: [], goal: "(!x.?y.R(x,y)) -> (?y.!x.R(x,y))", real: false, note: __T(245, [F("R"), termH("x"), termH("y"), termH("y")]) },
        { key: "C", prem: [], goal: "(!x.(P(x) | Q(x))) -> ((!x.P(x)) | (!x.Q(x)))", real: false, note: __T(246, [F("P"), F("Q"), F("P"), F("Q"), F("P"), F("Q")]) },
      ] },
  ]});
WORLDS.push(
  { id: 9, name: __T(247), rules: __T(248), stages: [
    { id: "9-1", name: __T(249), prem: [], goal: "!x.!y.(x = y -> y = x)", par: 5, earns: "sym",
      lesson: __T(250, [F("s = t"), termH("t"), termH("s"), F("s = t"), termH("t"), termH("s")]),
      hints: [__T(251, [F("a = b"), F("b = a")]),
              __T(252, [F("a = b"), termH("b"), termH("a")]),
              __T(253, [F("a = b"), F("a = a")])] },
    { id: "9-2", name: __T(254), prem: [], goal: "!x.!y.!z.(x = y -> (y = z -> x = z))", par: 7, earns: "trans",
      lesson: __T(255),
      hints: [__T(256, [F("a = c"), F("a = b"), F("b = c")]),
              __T(257, [F("b = c"), F("a = c"), termH("c"), termH("b")]),
              __T(258, [F("b = c"), F("a = b")])] },
    { id: "9-3", name: __T(259), prem: [], goal: "!x.!y.(x = y -> f(x) = f(y))", par: 5, earns: "cong",
      lesson: __T(260, [F("f(x) = y"), termH({ f: "f", args: ["x"] }), termH("x")]),
      hints: [__T(261, [F("a = b"), F("f(a) = f(b)")]),
              __T(262, [F("a = b"), termH({ f: "f", args: ["b"] }), termH("b")]),
              __T(263, [F("a = b"), F("f(a) = f(a)")])] },
    { id: "9-4", name: __T(264), prem: ["a = b", "c = b"], goal: "a = c", cards: ["sym"], par: 5,
      lesson: __T(265, [F("s = t"), termH("t"), termH("s"), F("s = t"), termH("A"), termH("s"), termH("A"), termH("t"), F("c = b"), F("a = c"), termH("c")]),
      hints: [__T(266, [F("!x.!y.(x = y -> y = x)"), termH("c"), termH("b")]),
              __T(267, [F("c = b -> b = c"), F("c = b"), F("b = c")]),
              __T(268, [termH("c"), termH("b"), F("c = b"), F("c = b -> b = c"), F("b = c"), F("a = b")])] },
    { id: "9-5", name: __T(269), boss: true, prem: ["!x.(e * x = x)", "!x.(x * e' = x)"], goal: "e = e'", cards: ["sym", "trans"], par: 4,
      lesson: __T(270, [F("!x.(e * x = x)"), termH("e"), F("!x.(x * e' = x)"), termH("e'"), termH("e"), termH("e'"), termH({ f: "*", args: ["e", "e'"] })]),
      hints: [__T(271, [termH("e'"), termH("e")]),
              __T(272, [F("e * e' = e"), F("e = e'"), termH("e"), termH({ f: "*", args: ["e", "e'"] })]),
              __T(273, [F("!x.(e * x = x)"), termH("e'"), F("!x.(x * e' = x)"), termH("e"), F("e * e' = e"), F("e * e' = e'")])],
      doneNote: __T(274, [termH("e"), termH({ f: "*", args: ["e", "e'"] }), termH("e'")]) },
  ]});
WORLDS.push(
  { id: 10, name: __T(275), rules: __T(276), stages: [
    { id: "10-1", name: __T(277), prem: ["!x.!y.((x <= y & y <= x) -> x = y)", "!x.(x <= m)", "!x.(x <= n)"], goal: "m = n", par: 8,
      lesson: __T(278, [F("x <= y"), termH("m"), termH("n"), F("m = n")]),
      hints: [__T(279, [termH("m"), termH("n"), F("m = n")]),
              __T(280, [F("m <= n & n <= m")]),
              __T(281, [termH("m"), termH("n"), F("!x.(x <= n)"), termH("m"), F("!x.(x <= m)"), termH("n")])],
      doneNote: __T(282) },
    { id: "10-2", name: __T(283), prem: ["!x.~(x < x)", "!x.!y.!z.((x < y & y < z) -> x < z)"], goal: "!x.!y.(x < y -> ~(y < x))", par: 13,
      lesson: __T(284, [F("x < y"), F("~(y < x)")]),
      hints: [__T(285, [F("a < b"), F("b < a")]),
              __T(286, [termH("a"), F("~(a < a)"), F("a < a")]),
              __T(287, [termH("a"), termH("a"), termH("b"), termH("a"), F("a < b"), F("b < a")])] },
    { id: "10-3", name: __T(288), prem: ["!x.!y.(f(x) = f(y) -> x = y)", "!x.!y.(g(x) = g(y) -> x = y)"], goal: "!x.!y.(g(f(x)) = g(f(y)) -> x = y)", par: 10,
      lesson: __T(289, [termH({ f: "g", args: [{ f: "f", args: ["x"] }] }), termH({ f: "f", args: ["a"] })]),
      hints: [__T(290, [F("g(f(a)) = g(f(b))"), F("a = b")]),
              __T(291, [termH("a"), termH("b"), F("f(a) = f(b)"), termH({ f: "f", args: ["a"] }), termH({ f: "f", args: ["b"] })]),
              __T(292, [termH("a"), termH("b"), termH({ f: "f", args: ["a"] }), termH({ f: "f", args: ["b"] }), F("g(f(a)) = g(f(b))")])] },
    { id: "10-4", name: __T(293), prem: ["!y.?x.(f(x) = y)", "!z.?y.(g(y) = z)"], goal: "!z.?x.(g(f(x)) = z)", par: 9,
      lesson: __T(294),
      hints: [__T(295, [termH("a"), termH("a"), F("g(b) = a"), termH("b")]),
              __T(296, [termH("b"), F("f(c) = b"), termH("c"), termH("c")]),
              __T(297, [termH("a"), termH("b"), termH("c"), F("g(b) = a"), F("f(c) = b")])] },
    { id: "10-5", name: __T(12), prem: [], goal: "A ∩ B ⊆ A", par: 6,
      lesson: __T(298, [F("x ∈ A"), termH("x"), termH("A"), F("A ⊆ B"), termH({ f: "∩", args: ["A", "B"] }), F("A ⊆ B"), F("!x.(x ∈ A -> x ∈ B)"), F("x ∈ A ∩ B"), F("x ∈ A & x ∈ B")]),
      hints: [__T(299),
              __T(300, [F("a ∈ A ∩ B")]),
              __T(301, [F("a ∈ A")])] },
    { id: "10-6", name: __T(302), prem: ["A ⊆ B", "B ⊆ C"], goal: "A ⊆ C", par: 10,
      lesson: __T(303),
      hints: [__T(304, [F("a ∈ A"), F("a ∈ C")]),
              __T(305, [F("B ⊆ C"), termH("a"), F("A ⊆ B")]),
              __T(306, [F("B ⊆ C"), termH("a"), F("A ⊆ B"), termH("a"), F("a ∈ A")])] },
    { id: "10-7", name: __T(307), eqBoth: true, earns: "lcancel", prem: ["!x.!y.!z.((x * y) * z = x * (y * z))", "!x.(e * x = x)", "!x.(i(x) * x = e)"], goal: "!x.!y.!z.(x * y = x * z -> y = z)", par: 18,
      lesson: __T(308, [F("!x.!y.!z.(x * y = x * z -> y = z)"), termH({ f: "i", args: ["a"] }), termH("a")]),
      hints: [__T(309, [F("a * b = a * c"), termH("b"), termH("c"), termH("a"), termH({ f: "i", args: ["a"] }), termH("a"), termH("b"), termH("c")]),
              __T(310, [F("b = c"), termH("b"), termH({ f: "*", args: ["e", "b"] }), termH({ f: "*", args: [{ f: "*", args: [{ f: "i", args: ["a"] }, "a"] }, "b"] }), termH({ f: "*", args: [{ f: "i", args: ["a"] }, { f: "*", args: ["a", "b"] }] }), termH("c"), F("a * b = a * c")]),
              __T(311, [F("e * b = b"), F("e * c = c"), F("i(a) * a = e"), termH("e"), F("a * b = a * c")])] },
    { id: "10-8", name: __T(312), boss: true, prem: [], goal: "(A ∪ B)ᶜ ⊆ Aᶜ ∩ Bᶜ", par: 18,
      lesson: __T(313, [termH({ f: "ᶜ", args: ["A"] }), F("x ∈ Aᶜ"), F("~(x ∈ A)")]),
      hints: [__T(314, [F("a ∈ (A ∪ B)ᶜ")]),
              __T(315, [F("a ∈ Aᶜ"), F("~(a ∈ A ∪ B)")]),
              __T(316, [F("~(a ∈ A ∪ B)"), F("a ∈ A")])] },
  ]});
WORLDS.push(
  { id: 11, name: __T(317), rules: __T(318), stages: [
    { id: "11-1", name: __T(319), prem: ["!x.(P(x) -> Q(x))", "!x.(Q(x) -> S(x))", "!x.(S(x) -> T(x))", "!x.(T(x) -> R(x))", "P(a)", "P(b)", "P(c)"], goal: "R(a) & (R(b) & R(c))", par: 23,
      lemmas: ["!x.(P(x) -> R(x))", "!x.(P(x) -> T(x))", "P(a) -> R(a)"],
      lesson: __T(320, [termH("a"), termH("b"), termH("c"), F("!x.(P(x) -> R(x))")]),
      hints: [__T(321, [F("!x.(P(x) -> R(x))")]),
              __T(322),
              __T(323, [F("P(d)"), `<span class="f"><i class="at">P</i>(…)</span>`])] },
    { id: "11-2", name: __T(324), eqBoth: true, earns: "lcancel", prem: ["!x.!y.!z.((x * y) * z = x * (y * z))", "!x.(e * x = x)", "!x.(i(x) * x = e)"], goal: "!x.!y.!z.(x * y = x * z -> y = z)", par: 18,
      lesson: __T(325),
      hints: [__T(326, [F("a * b = a * c")]),
              __T(327, [termH("b"), termH({ f: "*", args: ["e", "b"] }), termH({ f: "*", args: [{ f: "*", args: [{ f: "i", args: ["a"] }, "a"] }, "b"] }), termH({ f: "*", args: [{ f: "i", args: ["a"] }, { f: "*", args: ["a", "b"] }] })]),
              __T(328)] },
    { id: "11-3", name: __T(329), boss: true, eqBoth: true, cards: ["lcancel"], prem: ["!x.!y.!z.((x * y) * z = x * (y * z))", "!x.(e * x = x)", "!x.(i(x) * x = e)"], goal: "!x.(x * e = x)", par: 13,
      lesson: __T(330, [F("!x.(e * x = x)"), termH("e")]),
      hints: [__T(331, [termH("a"), termH("a"), termH({ f: "i", args: ["a"] })]),
              __T(332, [termH({ f: "i", args: ["a"] }), termH({ f: "*", args: ["a", "e"] }), termH("a"), F("i(a) * (a * e) = i(a) * a")]),
              __T(333, [termH("a"), termH({ f: "i", args: ["a"] }), termH({ f: "*", args: ["a", "e"] }), termH("a"), termH({ f: "i", args: ["a"] }), termH("a"), termH("e"), F("i(a) * a = e"), termH({ f: "*", args: [{ f: "i", args: ["a"] }, "a"] }), termH("e"), termH("e")])] },
  ]});
const PA = ["!x.(x + 0 = x)", "!x.!y.(x + s(y) = s(x + y))"]; // 足し算の定義（ペアノの公理の一部）
WORLDS.push(
  { id: 12, name: __T(334), rules: __T(335), stages: [
    { id: "12-1", name: "1 + 1 = 2", eqBoth: true, prem: PA, goal: "s(0) + s(0) = s(s(0))", par: 6,
      lesson: __T(336, [termH("0"), termH({ f: "s", args: ["x"] }), termH({ f: "s", args: ["0"] }), termH({ f: "s", args: [{ f: "s", args: ["0"] }] }), F("!x.(x + 0 = x)"), F("!x.!y.(x + s(y) = s(x + y))")]),
      hints: [__T(337, [termH({ f: "s", args: ["0"] }), termH("0")]),
              __T(338, [F("s(0) + s(0) = s(s(0) + 0)"), termH({ f: "s", args: ["0"] }), termH({ f: "+", args: [{ f: "s", args: ["0"] }, "0"] })]),
              __T(339, [termH({ f: "s", args: ["0"] }), termH("0"), termH({ f: "s", args: ["0"] })])] },
    { id: "12-2", name: __T(340), eqBoth: true, prem: PA, goal: "!x.(0 + x = x)", par: 8, earns: "zeroL",
      lesson: __T(341, [F("x + 0 = x"), F("0 + x = x"), F("!x.A(x)"), F("A(0)"), termH("a"), F("A(a)"), termH({ f: "s", args: ["a"] })]),
      hints: [__T(342, [F("0 + 0 = 0"), termH("0")]),
              __T(343, [F("0 + s(a) = s(a)"), termH("0"), termH("a"), F("0 + a = a")]),
              __T(344, [termH("0"), termH("0"), termH("a")])],
      doneNote: __T(345, [F("0 + x = x"), F("0 + x = x")]) },
    { id: "12-3", name: __T(346), eqBoth: true, prem: PA, goal: "!x.!y.(s(x) + y = s(x + y))", par: 15, earns: "succL",
      lesson: __T(347, [F("s(x) + y = s(x + y)"), termH("y"), termH("x"), termH("a"), F("!y.(s(a) + y = s(a + y))")]),
      hints: [__T(348, [termH("a")]),
              __T(349, [F("s(a) + 0 = s(a + 0)"), termH({ f: "s", args: ["a"] }), termH("a"), termH({ f: "s", args: ["a"] }), termH("b"), termH("a"), termH("b")]),
              __T(350, [termH({ f: "s", args: ["a"] }), termH("a"), termH({ f: "s", args: ["a"] }), termH("b"), termH("a"), termH("b")])] },
    { id: "12-4", name: __T(351), boss: true, eqBoth: true, earns: "commAdd", prem: PA, cards: ["zeroL", "succL"], goal: "!x.!y.(x + y = y + x)", par: 15,
      lesson: __T(352, [F("x + y = y + x"), termH("y")]),
      hints: [__T(353, [termH("a")]),
              __T(354, [F("a + 0 = 0 + a"), termH("a"), F("a + s(b) = s(b) + a")]),
              __T(355, [termH("a"), termH("a"), termH("a"), termH("b"), termH("b"), termH("a")])] },
  ]});
const PM = ["!x.(x * 0 = 0)", "!x.!y.(x * s(y) = x * y + x)"]; // 掛け算の定義
WORLDS.push(
  { id: 13, name: __T(356), rules: __T(357), stages: [
    { id: "13-1", name: __T(358), eqBoth: true, prem: [...PA, ...PM], cards: ["zeroL"], goal: "!x.(x * s(0) = x)", par: 8,
      lesson: __T(359, [termH({ f: "*", args: ["x", "y"] }), F("!x.(x * 0 = 0)"), F("!x.!y.(x * s(y) = x * y + x)"), termH("x"), termH({ f: "s", args: ["y"] }), termH("x"), termH("y"), termH("x"), termH({ f: "s", args: ["0"] })]),
      hints: [__T(360, [termH("a"), termH("a"), termH("0")]),
              __T(361, [F("a * 0 + a = a"), termH({ f: "*", args: ["a", "0"] }), termH("0")]),
              __T(362, [termH("a"), termH("0"), termH("a"), termH("a")])] },
    { id: "13-2", name: __T(363), eqBoth: true, earns: "zeroMulL", prem: [...PA, ...PM], goal: "!x.(0 * x = 0)", par: 9,
      lesson: __T(364, [F("x * 0 = 0"), F("0 * x = 0")]),
      hints: [__T(365, [F("0 * 0 = 0"), termH("0")]),
              __T(366, [F("0 * s(a) = 0"), F("0 * a + 0 = 0"), termH({ f: "+", args: [{ f: "*", args: ["0", "a"] }, "0"] }), termH({ f: "*", args: ["0", "a"] })]),
              __T(367)] },
    { id: "13-3", name: __T(368), eqBoth: true, prem: PA, goal: "!x.!y.!z.((x + y) + z = x + (y + z))", par: 19, earns: "assocAdd",
      lesson: __T(369, [termH("z")]),
      hints: [__T(370, [termH("a"), termH("b"), termH("c")]),
              __T(371, [termH({ f: "+", args: ["a", "b"] }), termH("b"), termH({ f: "+", args: ["a", "b"] }), termH("c"), termH("b"), termH("c"), termH("a"), termH({ f: "+", args: ["b", "c"] })]),
              __T(372, [termH({ f: "+", args: ["a", "b"] }), termH("c"), termH("b"), termH("c"), termH("a"), termH({ f: "+", args: ["b", "c"] })])] },
    { id: "13-4", name: __T(373), boss: true, eqBoth: true, earns: "distrib", prem: [...PA, ...PM], cards: ["assocAdd"], goal: "!x.!y.!z.(x * (y + z) = x * y + x * z)", par: 23,
      lesson: __T(374, [F("x * (y + z) = x * y + x * z"), termH("z")]),
      hints: [__T(375, [F("a * (b + 0) = a * b + a * 0"), termH({ f: "+", args: ["b", "0"] }), termH({ f: "*", args: ["a", "0"] }), termH({ f: "+", args: [{ f: "*", args: ["a", "b"] }, "0"] })]),
              __T(376, [F("a * (b + s(c)) = a * b + a * s(c)"), termH({ f: "+", args: ["b", { f: "s", args: ["c"] }] }), termH({ f: "*", args: ["a", { f: "s", args: [{ f: "+", args: ["b", "c"] }] }] }), termH({ f: "*", args: ["a", { f: "s", args: ["c"] }] }), F("(a * b + a * c) + a = a * b + (a * c + a)")]),
              __T(377)] },
  ]});
WORLDS.push(
  { id: 14, name: __T(378), rules: __T(379), stages: [
    { id: "14-1", name: __T(380), eqBoth: true, prem: [...PA, ...PM], cards: ["distrib"], goal: "!x.!y.!z.((x * y) * z = x * (y * z))", par: 22, earns: "assocMul",
      lesson: __T(381, [termH("z")]),
      hints: [__T(382, [termH("c"), termH({ f: "*", args: ["a", "b"] }), termH("b"), termH("a"), termH("0")]),
              __T(383, [termH({ f: "*", args: ["a", "b"] }), termH("c"), termH("b"), termH("c"), F("a * (b * c) + a * b = a * (b * c + b)")]),
              __T(384)] },
    { id: "14-2", name: __T(385), eqBoth: true, prem: [...PA, ...PM], cards: ["assocAdd", "commAdd"], goal: "!x.!y.(s(x) * y = x * y + y)", par: 33, earns: "succMulL",
      lesson: __T(386, [F("s(x) * y = x * y + y"), termH("y")]),
      hints: [__T(387, [F("(a * b + b) + s(a) = (a * b + a) + s(b)"), termH({ f: "s", args: ["…"] })]), __T(388, [termH("b"), F("s(a) * 0 = a * 0 + 0"), termH("0")]),
              __T(389, [F("(a * b + b) + s(a) = (a * b + a) + s(b)"), termH({ f: "s", args: ["…"] }), termH({ f: "*", args: ["a", "b"] }), termH({ f: "+", args: ["b", "a"] }), termH({ f: "+", args: ["a", "b"] })]),
              __T(390, [termH({ f: "*", args: ["a", "b"] }), termH("b"), termH("a")])] },
    { id: "14-3", name: __T(391), eqBoth: true, earns: "commMul", prem: [...PA, ...PM], cards: ["zeroMulL", "succMulL"], goal: "!x.!y.(x * y = y * x)", par: 15,
      lesson: __T(392),
      hints: [__T(393, [F("a * 0 = 0 * a"), termH("0")]),
              __T(394, [F("a * s(b) = s(b) * a")]),
              __T(395)] },
    { id: "14-div", name: __T(396), boss: true, eqBoth: true, prem: [], cards: ["assocMul"], goal: "!x.!y.!z.(?k.(x * k = y) -> (?m.(y * m = z) -> ?n.(x * n = z)))", par: 14,
      lesson: __T(397, [F("?k.(a * k = b)"), termH("a"), termH("b"), termH("a"), termH("b"), termH("a"), termH("b"), termH("b"), termH("c"), termH("a"), termH("c")]),
      hints: [__T(398),
              __T(399),
              __T(400, [F("a * (d * e) = c"), F("(a * d) * e = c"), F("a * d = b"), F("b * e = c")])] },
  ]},
  { id: 15, name: __T(401), rules: __T(402), stages: [
    { id: "15-1", name: __T(403), eqBoth: true, leDef: true, prem: PA, cards: ["zeroL"], goal: "!x.(0 <= x)", par: 5, earns: "zeroLe",
      lesson: __T(404, [F("x <= y"), F("?z.(x + z = y)"), termH("x"), termH("y")]),
      hints: [__T(405, [termH("a")]),
              __T(406, [F("?z.(0 + z = a)"), termH("a")]),
              __T(407, [termH("a"), termH("a")])] },
    { id: "15-min", name: __T(408), eqBoth: true, leDef: true, prem: PA, cards: ["zeroLe"], goal: "?x.!y.(x <= y)", par: 2,
      lesson: __T(409, [F("?x.!y.(x <= y)"), F("!y.?x.(x <= y)")]),
      hints: [__T(410, [termH("0")]), __T(411, [F("!y.(0 <= y)")]), __T(412, [termH("0")])] },
    { id: "15-3", name: __T(413), eqBoth: true, leDef: true, prem: PA, goal: "!x.(x <= s(x))", par: 9, earns: "leSucc",
      lesson: __T(414, [F("x <= s(x)"), termH({ f: "s", args: ["0"] })]),
      hints: [__T(415, [F("?z.(a + z = s(a))"), termH({ f: "s", args: ["0"] })]),
              __T(416, [F("a + s(0) = s(a)"), termH("a"), termH("0"), termH("a")]),
              __T(417, [termH({ f: "s", args: ["0"] })])],
      doneNote: __T(418, [F("x <= s(x)"), termH({ f: "s", args: ["x"] }), termH("x")]) },
    { id: "15-5", name: __T(419), eqBoth: true, leDef: true, prem: PA, cards: ["assocAdd"], goal: "!x.!y.!z.(x <= y -> (y <= z -> x <= z))", par: 18,
      lesson: __T(420, [termH("d"), termH("e"), termH({ f: "+", args: ["d", "e"] })]),
      hints: [__T(421, [F("a + d = b"), F("b + e = c")]),
              __T(422, [F("a + (d + e) = c"), F("(a + d) + e = c"), F("a + d = b"), F("b + e = c")]),
              __T(423, [F("a <= b"), F("b <= c"), termH({ f: "+", args: ["d", "e"] }), F("a + d = b"), F("b + e = c")])] },
    { id: "15-inf0", name: __T(424), kind: "refute", reach0: true, prem: PA, goal: "!x.?y.(?z.(x + z = y) & ~(y = x))", par: null,
      lesson: __T(425, [F("x <= y"), F("!x.?y.(?z.(x + z = y) & ~(y = x))"), termH("0"), termH({ f: "s", args: ["…"] })]),
      hints: [__T(426), __T(427, [termH("0"), termH({ f: "s", args: ["x"] })]), __T(428, [termH("0")])],
      doneNote: __T(429, [termH("0")]) },
    { id: "15-inf", name: __T(430), boss: true, eqBoth: true, leDef: true, prem: [...PA, "!x.~(s(x) = 0)", "!x.!y.(s(x) = s(y) -> x = y)"], cards: ["leSucc"], goal: "!x.?y.(x <= y & ~(y = x))", par: 19,
      lesson: __T(431, [F("~(s(x) = 0)"), F("s(x) = s(y) -> x = y"), termH({ f: "s", args: ["x"] }), F("~(s(x) = x)"), F("!x.~(s(x) = x)")]),
      hints: [__T(432, [F("!x.~(s(x) = x)")]),
              __T(433),
              __T(434, [F("~(s(s(n)) = s(n))"), F("s(s(n)) = s(n)"), termH({ f: "s", args: ["n"] }), termH("n"), F("s(n) = n")])] },
  ]});
// どのステージで、どのチュートリアルが「New」になるか（その概念が初めて登場するステージ）
const TUT_AT = { "1-1": ["basics"], "1-2": ["andE"], "1-3": ["impI"], "2-1": ["impE"], "2-3": ["scope"], "3-1": ["orI"], "3-2": ["orE"],   "4-1": ["bot"], "4-2": ["neg"], "5-1": ["kripke"], "6-1": ["raa"], "7-1": ["allQ"], "7-2": ["names"], "7-3": ["exQ"], "9-1": ["eq"], "9-4": ["cards"],
  "10-3": ["terms"], "10-5": ["defs"], "10-7": ["eqboth"], "11-1": ["lemma"], "12-2": ["induction"], "15-1": ["leDef"], "15-5": ["termInput"], "14-div": ["termInput"], "13-2": ["match"],
  "tr-1": ["translate"], "tr-4": ["tower"], "core-4": ["indep"], "core-5": ["thirdway"] };

// ================= 講義の順序に合わせた並べ替え =================
// 古典論理（背理法の魔法・真理値の意味論）をクリプキ意味論より前に置き、一階述語論理は ∀・∃・古典・構造の 4 つのワールドに分ける。
// oid は元のワールド番号で、⊥ の有無、古典論理か、一階述語論理か、などの性質を決める
const TPADD = x => `<span class="tp-add">${x}</span>`; // 翻訳所の文字盤：訳すときに付け加えた ¬¬
const NEWST = {
  // --- 数学の街 ---
  "x-injeq": { id: "x-injeq", name: __T(435), prem: ["!x.!y.(f(x) = f(y) -> x = y)"], cards: ["cong"], goal: "!x.!y.((f(x) = f(y) -> x = y) & (x = y -> f(x) = f(y)))", par: 9,
    lesson: __T(436, [F("f(x) = f(y)"), F("x = y"), F("f(x) = f(y)"), F("x = y"), F("x = y -> f(x) = f(y)")]),
    hints: [__T(437, [termH("a"), termH("b")]),
            __T(438, [F("f(a) = f(b) -> a = b"), termH("a"), termH("b")]),
            __T(439, [termH("a"), termH("b"), termH("a"), termH("b")])] },
  // --- 背理法の魔法 ---
  "c-imp": { id: "c-imp", name: __T(440), prem: ["P -> Q"], goal: "~P | Q", par: 8,
    lesson: __T(441, [F("P->Q"), F("~P|Q"), F("P"), F("Q"), F("P"), F("Q")]),
    hints: [__T(230, [F("~(~P|Q)")]),
            __T(442, [F("~(~P|Q)"), F("~P|Q"), F("~P"), F("P"), F("Q")]),
            __T(443, [F("~(~P|Q)"), F("~(~P|Q)"), F("P->Q"), F("Q"), F("P")])] },
  "c-contra": { id: "c-contra", name: __T(444), prem: ["~Q -> ~P"], goal: "P -> Q", par: 5,
    lesson: __T(445, [F("Q"), F("P"), F("P"), F("Q")]),
    hints: [__T(446, [F("P"), F("Q")]),
            __T(447, [F("~Q->~P"), F("~Q"), F("P")]),
            __T(448, [F("~Q->~P"), F("~Q"), F("~Q"), F("P"), F("P")])],
      specNote: __T(449, [F("~Q->~P"), F("~P"), F("~Q"), F("P")]) },
  // --- 真偽の石盤（古典論理の意味論） ---
  "r-conv": { id: "r-conv", name: __T(450), kind: "refute", tut: ["truth"], prem: ["P -> Q"], goal: "Q -> P", par: null,
    lesson: __T(451, [F("P->Q"), F("Q->P")]),
    hints: [__T(452, [F("Q->P"), F("Q"), F("P")]), __T(453, [F("P->Q")]), __T(454, [F("P"), F("Q")])] },
  "r-inv": { id: "r-inv", name: __T(455), kind: "refute", prem: ["P -> Q"], goal: "~P -> ~Q", par: null,
    lesson: __T(456, [F("P->Q"), F("~P->~Q"), F("~Q->~P")]),
    hints: [__T(457, [F("~P"), F("~Q")]), __T(458, [F("P"), F("Q")]), __T(454, [F("P"), F("Q")])] },
  "r-ior": { id: "r-ior", name: __T(459), kind: "refute", prem: ["P | Q"], goal: "~(P & Q)", par: null,
    lesson: __T(460, [F("P"), F("Q"), F("P|Q"), F("~(P&Q)")]),
    hints: [__T(461, [F("~(P&Q)"), F("P&Q")]), __T(462, [F("P"), F("Q"), F("P|Q")]), __T(463, [F("P"), F("Q")])] },
  "r-dm": { id: "r-dm", name: __T(464), kind: "refute", prem: ["~(P & Q)"], goal: "~P & ~Q", par: null,
    lesson: __T(465, [F("~(P&Q)"), F("~P|~Q"), F("~P&~Q")]),
    hints: [__T(466, [F("~P&~Q"), F("P"), F("Q")]), __T(467, [F("~(P&Q)")]), __T(468, [F("P"), F("Q")])] },
  // --- 住人の街（∀） ---
  "f-rename": { id: "f-rename", name: __T(469), prem: [], goal: "(!x.P(x)) -> (!y.P(y))", par: 4,
    lesson: __T(470, [F("!x.P(x)"), F("!y.P(y)")]),
    hints: [__T(471, [F("!x.P(x)")]), __T(472, [F("!y.P(y)"), termH("a"), termH("a")]),
            __T(473, [termH("a"), F("P(a)")])] },
  "f-barbara": { id: "f-barbara", name: __T(474), prem: ["!x.(P(x) -> Q(x))", "!x.(Q(x) -> R(x))"], goal: "!x.(P(x) -> R(x))", par: 7,
    lesson: __T(475, [F("P"), F("Q"), F("Q"), F("R"), F("P"), F("R")]),
    hints: [__T(476, [F("P(a)"), F("R(a)")]), __T(477, [termH("a"), F("Q(a)")]),
            __T(478, [F("!x.(Q(x)->R(x))"), termH("a"), F("!x.(P(x)->Q(x))"), termH("a"), F("P(a)")])] },
  "f-alll": { id: "f-alll", name: __T(479), prem: ["!z.(A -> B(z))"], goal: "A -> !x.B(x)", par: 5,
    lesson: __T(480, [F("A"), F("!z.(A->B(z))"), F("A->!x.B(x)")]),
    hints: [__T(481, [F("A"), termH("a")]), __T(482, [F("!z.(A->B(z))"), termH("a"), F("B(a)")]),
            __T(483, [termH("a"), F("A->B(a)"), F("A")])] },
  "f-allr": { id: "f-allr", name: __T(484), prem: ["A -> !x.B(x)"], goal: "!z.(A -> B(z))", par: 5,
    lesson: __T(485, [F("A"), F("A->!x.B(x)")]),
    hints: [__T(486, [termH("a"), F("A")]), __T(487, [F("A"), F("A->!x.B(x)"), F("!x.B(x)")]),
            __T(488, [F("A"), F("A->!x.B(x)"), F("!x.B(x)"), termH("a"), F("B(a)")])] },
  "f-dist": { id: "f-dist", name: __T(489), boss: true, prem: [], goal: "(!x.(P(x) & Q(x))) -> ((!x.P(x)) & (!x.Q(x)))", par: 10,
    lesson: __T(490, [F("!x.(P(x)&Q(x))"), F("!x.P(x)"), F("!x.Q(x)")]),
    hints: [__T(491, [F("!x.P(x)"), F("!x.Q(x)")]), __T(492),
            __T(493, [termH("a"), F("P(a)"), termH("b")])] },
  // --- 存在の扉（∃） ---
  "f-wit": { id: "f-wit", name: __T(494), prem: ["P(a) & P(b)"], goal: "?x.P(x)", par: 3,
    lesson: __T(495, [F("?x.P(x)"), F("P"), termH("a"), termH("b"), F("P(a)&P(b)"), F("!x.P(x)"), termH("a"), termH("b")]),
    hints: [__T(496, [F("P(a)"), F("P(b)")]), __T(497, [termH("a"), termH("b")]), __T(498, [termH("a"), F("P(a)")])] },
  "f-ae1": { id: "f-ae1", name: __T(499), prem: ["A & ?x.B(x)"], goal: "?x.(A & B(x))", par: 6,
    lesson: __T(500, [F("A"), F("A&?x.B(x)"), F("?x.(A&B(x))")]),
    hints: [__T(501, [F("A"), F("?x.B(x)"), termH("a")]), __T(502, [termH("a"), F("A&B(a)")]),
            __T(503, [F("?x.B(x)"), termH("a"), F("A"), F("B(a)")])] },
  "f-ae2": { id: "f-ae2", name: __T(504), prem: ["?x.(A & B(x))"], goal: "A & ?x.B(x)", par: 6,
    lesson: __T(505, [F("A"), F("?x.B(x)")]),
    hints: [__T(506, [F("A&B(a)"), termH("a")]), __T(507, [F("A&B(a)"), F("A"), F("?x.B(x)")]),
            __T(508, [F("A"), termH("a"), F("B(a)")])] },
  "f-ex1": { id: "f-ex1", name: __T(509), prem: ["!z.(A(z) -> B)"], goal: "(?x.A(x)) -> B", par: 5,
    lesson: __T(510, [F("B"), F("!z.(A(z)->B)"), F("(?x.A(x))->B")]),
    hints: [__T(511, [F("?x.A(x)"), termH("a")]), __T(482, [F("!z.(A(z)->B)"), termH("a"), F("B")]),
            __T(512, [F("!z.(A(z)->B)"), termH("a"), F("A(a)->B"), F("A(a)")])] },
  "f-ex2": { id: "f-ex2", name: __T(513), prem: ["(?x.A(x)) -> B"], goal: "!z.(A(z) -> B)", par: 5,
    lesson: __T(514, [termH("a"), F("A(a)"), termH("a"), F("?x.A(x)")]),
    hints: [__T(476, [F("A(a)"), F("B")]), __T(515, [F("(?x.A(x))->B"), F("B"), F("?x.A(x)"), termH("a")]),
            __T(516, [F("B"), termH("a"), F("A(a)")])] },
  "f-mouse": { id: "f-mouse", name: __T(517), boss: true, prem: ["?y.(C(y) & !x.(M(x) -> F(x,y)))"], goal: "!x.(M(x) -> ?y.(C(y) & F(x,y)))", par: 10,
    lesson: __T(518, [F("M(x)"), termH("x"), F("C(x)"), termH("x"), F("F(x,y)"), termH("x"), termH("y")]),
    hints: [__T(519, [F("M(a)"), termH("b")]),
            __T(520, [termH("b"), F("C(b)&F(a,b)")]),
            __T(521, [termH("b"), F("C(b)"), F("!x.(M(x)->F(x,b))"), termH("a"), F("M(a)")])] },
  // --- 魔法と量化子（古典述語論理） ---
  "f-barber": { id: "f-barber", name: __T(522), prem: ["!x.(~K(x,x) -> K(p,x))"], goal: "K(p,p)", par: 5,
    lesson: __T(523, [termH("p"), F("K(x,y)"), termH("x"), termH("y"), termH("p")]),
    hints: [__T(524, [F("K(p,p)"), F("~K(p,p)")]), __T(525, [F("~K(p,p)"), F("K(p,p)"), termH("p")]),
            __T(526, [F("~K(p,p)"), termH("p"), F("~K(p,p)->K(p,p)"), F("~K(p,p)")])],
    doneNote: __T(527, [termH("p")]) },
  "f-nen": { id: "f-nen", name: __T(528), prem: ["~?x.~P(x)"], goal: "!x.P(x)", par: 5,
    lesson: __T(529, [F("P"), F("P")]),
    hints: [__T(530, [termH("a"), F("P(a)")]), __T(531, [F("~?x.~P(x)"), F("?x.~P(x)"), termH("a")]),
            __T(532, [F("~?x.~P(x)"), termH("a"), F("~P(a)")])] },
  "f-nan": { id: "f-nan", name: __T(533), prem: ["~!x.~P(x)"], goal: "?x.P(x)", par: 7,
    lesson: __T(534, [F("P"), F("P")]),
    hints: [__T(535, [F("~?x.P(x)")]), __T(536, [F("~!x.~P(x)"), F("!x.~P(x)"), termH("a"), F("~?x.P(x)")]),
            __T(537, [F("~!x.~P(x)"), F("~?x.P(x)"), termH("a"), F("P(a)")])] },
  "f-const": { id: "f-const", name: __T(538), prem: ["!x.(P(x) | Q)"], goal: "(!x.P(x)) | Q", par: 11,
    lesson: __T(539, [F("Q"), F("P"), F("Q"), F("P"), F("Q"), F("Q")]),
    hints: [__T(540, [F("~((!x.P(x))|Q)"), F("!x.P(x)")]),
            __T(541, [termH("a"), termH("a"), F("P(a)|Q"), F("Q")]),
            __T(542, [termH("a"), F("P(a)|Q"), F("P(a)"), F("Q"), F("~((!x.P(x))|Q)"), F("Q")])] },
  // --- 構造の鑑定（一階述語論理の意味論） ---
  "s-ex": { id: "s-ex", name: __T(543), kind: "refute", tut: ["struct"], prem: ["?x.P(x)"], goal: "!x.P(x)", par: null,
    lesson: __T(544, [F("P"), F("P")]),
    hints: [__T(545), __T(546, [F("P")]), __T(547, [F("P(1)"), F("P(2)")])] },
  "s-pos": { id: "s-pos", name: __T(548), kind: "refute", prem: ["?x.!y.R(x,y)"], goal: "!x.?y.R(x,y)", par: null,
    lesson: __T(549, [F("?y.!x.R(x,y)"), F("!x.?y.R(x,y)"), F("?x.!y.R(x,y)"), F("R")]),
    hints: [__T(550, [F("R")]), __T(551, [F("R")]), __T(552, [F("R")])] },
  "s-mouse": { id: "s-mouse", name: __T(553), kind: "refute", prem: ["!x.(M(x) -> ?y.(C(y) & F(x,y)))", "?x.M(x)"], goal: "?y.(C(y) & !x.(M(x) -> F(x,y)))", par: null,
    lesson: __T(554, [F("M"), F("C"), F("F(x,y)"), termH("x"), termH("y")]),
    hints: [__T(555), __T(556, [F("M"), F("C")]), __T(557, [F("M(1)"), F("M(2)"), F("C(3)"), F("C(4)"), F("F(1,3)"), F("F(2,4)")])] },
  "s-nomouse": { id: "s-nomouse", name: __T(558), kind: "refute", prem: ["!x.(M(x) -> !y.(C(y) -> F(x,y)))", "?y.C(y)"], goal: "?x.(M(x) & ?y.(C(y) & F(x,y)))", par: null,
    lesson: __T(559),
    hints: [__T(560), __T(561, [F("M")]), __T(562, [F("C(1)")])] },
  // --- 公理の鏡（数学の理論での証明不可能性） ---
  "x-total": { id: "x-total", name: __T(563), kind: "refute", prem: ["!x.(x <= x)", "!x.!y.((x <= y & y <= x) -> x = y)", "!x.!y.!z.((x <= y & y <= z) -> x <= z)"], goal: "!x.!y.(x <= y | y <= x)", par: null,
    lesson: __T(564, [F("x = y")]),
    hints: [__T(565, [F("1 <= 1"), F("2 <= 2")]), __T(566, [F("x <= y")]), __T(567, [F("x <= y")])] },
  "x-antisym": { id: "x-antisym", name: __T(568), kind: "refute", prem: ["!x.(x <= x)", "!x.!y.!z.((x <= y & y <= z) -> x <= z)"], goal: "!x.!y.((x <= y & y <= x) -> x = y)", par: null,
    lesson: __T(569),
    hints: [__T(570, [F("x <= y")]), __T(571, [F("x <= y")]), __T(572, [F("x <= y")])] },
  "x-max": { id: "x-max", name: __T(573), kind: "refute", prem: ["!x.(x <= x)", "!x.!y.((x <= y & y <= x) -> x = y)", "!x.!y.!z.((x <= y & y <= z) -> x <= z)", "!x.(m <= x -> x = m)"], goal: "!x.(x <= m)", par: null,
    lesson: __T(574, [F("!x.(m <= x -> x = m)"), termH("m"), termH("m"), F("!x.(x <= m)"), termH("m")]),
    hints: [__T(575, [termH("m"), termH("m")]), __T(576, [termH("m")]), __T(577, [termH("m"), F("x <= y")])] },
  "x-rid": { id: "x-rid", name: __T(578), kind: "refute", tut: ["structFun"], prem: ["!x.!y.!z.((x * y) * z = x * (y * z))", "!x.(e * x = x)"], goal: "!x.(x * e = x)", par: null,
    lesson: __T(579, [F("!x.(x * e = x)"), termH({ f: "*", args: ["x", "y"] }), termH("e")]),
    hints: [__T(580, [F("x * y = y")]), __T(581), __T(582, [termH("e")])] },
  "x-twoid": { id: "x-twoid", name: __T(583), kind: "refute", prem: ["!x.(e * x = x)", "!x.(e' * x = x)"], goal: "e = e'", par: null,
    lesson: __T(584, [termH("e"), termH("e'")]),
    hints: [__T(585), __T(586, [termH("e"), termH("e'")]), __T(587, [termH("e"), termH("e'")])] },
  "x-comm": { id: "x-comm", name: __T(588), kind: "refute", prem: ["!x.!y.!z.((x * y) * z = x * (y * z))", "!x.(e * x = x)", "!x.(x * e = x)"], goal: "!x.!y.(x * y = y * x)", par: null,
    lesson: __T(589),
    hints: [__T(590, [termH("e")]), __T(591), __T(592, [termH("e")])] },
  "x-ind": { id: "x-ind", indOff: true, name: __T(593), kind: "refute", prem: ["!x.(x + 0 = x)", "!x.!y.(x + s(y) = s(x + y))"], goal: "!x.(0 + x = x)", par: null,
    lesson: __T(594, [F("!x.(0 + x = x)"), termH("0"), termH({ f: "s", args: ["…"] }), termH("0")]),
    hints: [__T(595, [termH("0"), termH({ f: "s", args: ["x"] })]), __T(596, [F("x + 0 = x"), termH("0")]), __T(597, [termH("0")])],
    doneNote: __T(598, [termH("0"), termH({ f: "s", args: ["…"] })]) },
  "x-judge": { id: "x-judge", name: __T(599), boss: true, kind: "judge", par: null, presets: ["chain3", "diamond"],
    lesson: __T(600, [F("!x.~(x < x)")]),
    hints: [__T(601), __T(602), __T(603, [F("x < y"), F("x < y")])],
    parts: [
      { key: "A", prem: ["!x.~(x < x)", "!x.!y.!z.((x < y & y < z) -> x < z)"], goal: "!x.!y.(x < y -> ~(y < x))", real: true, note: __T(604) },
      { key: "B", prem: ["!x.~(x < x)", "!x.!y.!z.((x < y & y < z) -> x < z)"], goal: "!x.!y.((x < y | x = y) | y < x)", real: false, note: __T(605) },
      { key: "C", prem: ["!x.~(x < x)", "!x.!y.!z.((x < y & y < z) -> x < z)"], goal: "!x.?y.(x < y)", real: false, note: __T(606) },
    ] },
  // --- 集合の街 ---
  "x-union": { id: "x-union", name: __T(13), prem: [], goal: "A ⊆ A ∪ B", par: 6,
    lesson: __T(607, [F("x ∈ A ∪ B"), F("x ∈ A | x ∈ B"), termH("A"), termH({ f: "∪", args: ["A", "B"] })]),
    hints: [__T(608, [F("a ∈ A")]), __T(609, [F("a ∈ A ∪ B")]),
            __T(610, [F("a ∈ A")])] },
  "x-swap": { id: "x-swap", name: __T(611), prem: [], goal: "A ∩ B ⊆ B ∩ A", par: 9,
    lesson: __T(612),
    hints: [__T(608, [F("a ∈ A ∩ B")]), __T(613),
            __T(614, [F("a ∈ B"), F("a ∈ A")])] },
  "x-mono": { id: "x-mono", name: __T(615), prem: ["A ⊆ B"], goal: "A ∩ C ⊆ B ∩ C", par: 12,
    lesson: __T(616, [F("A ⊆ B"), termH("C")]),
    hints: [__T(617, [F("a ∈ A ∩ C")]), __T(618, [F("a ∈ B"), F("A ⊆ B"), termH("a")]),
            __T(619, [termH("a"), F("a ∈ B"), F("a ∈ A"), F("a ∈ C")])] },
  "x-dmc": { id: "x-dmc", name: __T(620), prem: [], goal: "(A ∩ B)ᶜ ⊆ Aᶜ ∪ Bᶜ", par: 19,
    lesson: __T(621, [F("(A ∩ B)ᶜ ⊆ Aᶜ ∪ Bᶜ"), F("x ∈ A ∪ B"), F("x ∈ A | x ∈ B"), F("x ∈ Aᶜ"), F("~(x ∈ A)")]),
    hints: [__T(622), __T(623, [F("a ∈ (A ∩ B)ᶜ")]),
            __T(624, [F("a ∈ (A ∩ B)ᶜ"), F("a ∈ A ∩ B")]),
            __T(625, [F("a ∈ A"), F("~(a ∈ Aᶜ | a ∈ Bᶜ)"), F("~(a ∈ A)"), F("a ∈ B")])] },
  "x-darii": { id: "x-darii", name: __T(626), prem: ["M ⊆ P", "S ∩ M ≠ ∅"], goal: "S ∩ P ≠ ∅", par: 13,
    lesson: __T(627, [F("M ⊆ P"), F("S ∩ M ≠ ∅"), F("S ∩ P ≠ ∅"), F("X ≠ ∅"), termH("X"), F("?x.(x ∈ X)")]),
    hints: [__T(628, [F("S ∩ M ≠ ∅"), termH("a"), F("a ∈ S"), F("a ∈ M")]),
            __T(629, [termH("a"), F("a ∈ S ∩ P"), F("a ∈ P"), F("M ⊆ P"), termH("a")]),
            __T(630, [termH("a"), F("a ∈ S"), F("M ⊆ P"), termH("a"), F("a ∈ M")])] },
  // --- 集合の街：範囲を限った量化子 ∀x∈A. φ（＝∀x(x∈A→φ)）、∃x∈A. φ（＝∃x(x∈A∧φ)）---
  "x-bq1": { id: "x-bq1", name: __T(631), prem: ["~?x∈A.P(x)"], goal: "!x∈A.~P(x)", par: 8,
    lesson: __T(632, [F("!x.(x ∈ A -> P(x))"), F("!x∈A.P(x)"), F("?x.(x ∈ A & P(x))"), F("?x∈A.P(x)"), termH("A"), termH("A"), termH("A"), F("P"), termH("A"), F("P")]),
    hints: [__T(633, [termH("a"), F("a ∈ A -> ~P(a)"), F("a ∈ A"), F("P(a)")]),
            __T(634, [F("~?x∈A.P(x)"), F("?x∈A.P(x)"), termH("a")]),
            __T(635, [F("~?x∈A.P(x)"), termH("a"), F("a ∈ A"), F("P(a)")])] },
  "x-bq2": { id: "x-bq2", name: __T(228), boss: true, prem: ["~!x∈A.P(x)"], goal: "?x∈A.~P(x)", par: 10,
    lesson: __T(636, [termH("A"), F("P"), F("P"), termH("A")]),
    hints: [__T(637, [F("~!x∈A.P(x)"), F("!x∈A.P(x)"), termH("a"), F("P(a)")]),
            __T(638, [F("~P(a)"), F("~?x∈A.~P(x)"), termH("a")]),
            __T(639, [F("~!x∈A.P(x)"), F("~?x∈A.~P(x)"), termH("a"), F("a ∈ A"), F("~P(a)")])] },
  // --- 集合の街：対当の方形（伝統的論理学の定言命題）。いまは使っていない（空でない集合の問題を作るときの部品）---
  "x-sq1": { id: "x-sq1", name: __T(228), prem: ["~(A ⊆ B)"], goal: "A ∩ Bᶜ ≠ ∅", par: 14,
    lesson: __T(640, [F("A ⊆ B"), F("A ∩ Bᶜ ≠ ∅"), F("S ≠ ∅"), termH("S"), F("?x.(x ∈ S)")]),
    hints: [__T(641),
            __T(642, [F("~(A ⊆ B)"), F("A ⊆ B"), termH("a"), F("a ∈ B")]),
            __T(643, [F("~?x.(x ∈ A ∩ Bᶜ)"), termH("a"), F("a ∈ A ∩ Bᶜ"), F("a ∈ A"), F("~(a ∈ B)")])] },
  "x-sq2": { id: "x-sq2", name: __T(644), boss: true, prem: ["A ∩ Bᶜ ≠ ∅"], goal: "~(A ⊆ B)", par: 11,
    lesson: __T(645, [termH({ f: "∩", args: ["A", { f: "ᶜ", args: ["B"] }] }), F("~(A ⊆ B)"), F("A ∩ Bᶜ ≠ ∅")]),
    hints: [__T(646, [F("A ⊆ B")]),
            __T(647, [termH("a"), F("a ∈ A"), F("a ∈ Bᶜ")]),
            __T(648, [F("a ∈ Bᶜ"), F("~(a ∈ B)"), F("a ∈ B"), F("A ⊆ B"), termH("a"), F("a ∈ A")])] },
  // --- 公理の鏡：既製の構造を使う ---
  "x-order2": { id: "x-order2", name: __T(649), kind: "refute", tut: ["presets"], presets: ["z2", "z3", "v4", "s3"], prem: ["!x.!y.!z.((x * y) * z = x * (y * z))", "!x.(e * x = x)", "!x.(i(x) * x = e)"], goal: "!x.(x * x = e)", par: null,
    lesson: __T(650),
    hints: [__T(651), __T(652, [termH("ℤ")]), __T(653)] },
  "x-nonab": { id: "x-nonab", name: __T(654), kind: "refute", presets: ["z2", "z3", "v4", "s3"], prem: ["!x.!y.!z.((x * y) * z = x * (y * z))", "!x.(e * x = x)", "!x.(i(x) * x = e)"], goal: "!x.!y.(x * y = y * x)", par: null,
    lesson: __T(655),
    hints: [__T(656), __T(657), __T(658)] },
  // --- 寄り道の層「翻訳所」：魔導書の言葉（古典論理）を、術を使わない言葉（直観主義論理）へ訳す ---
  "tr-1": { id: "tr-1", name: __T(659), prem: [], goal: "~~(P | ~P)", par: 7, classical: false, goalText: __T(660, [F("~~(P | ~P)")]),
    trans: () => ({ src: F("P|~P"), dst: `<span class="f">${TPADD("¬¬")}<span class="par">(</span>${fh(parse("P|~P"))}<span class="par">)</span></span>` }),
    lesson: __T(661, [F("P|~P"), F("~~(P|~P)")]),
    hints: [__T(662, [F("~(P|~P)")]),
            __T(663, [F("~(P|~P)"), F("P|~P"), F("~P")]),
            __T(664, [F("~(P|~P)"), F("~(P|~P)"), F("P"), F("P")])] },
  "tr-2": { id: "tr-2", name: __T(665), prem: [], goal: "~~(~~P -> P)", par: 9, classical: false, goalText: __T(660, [F("~~(~~P -> P)")]),
    trans: () => ({ src: F("~~P->P"), dst: `<span class="f">${TPADD("¬¬")}<span class="par">(</span>${fh(parse("~~P->P"))}<span class="par">)</span></span>` }),
    lesson: __T(666, [F("~~P->P"), F("~~(~~P->P)"), F("P")]),
    hints: [__T(667, [F("~(~~P->P)"), F("~~P->P")]),
            __T(668, [F("~~P"), F("P"), F("~~P"), F("~P")]),
            __T(669, [F("~(~~P->P)"), F("~~P"), F("P"), F("~(~~P->P)"), F("P"), F("P")])] },
  "tr-3": { id: "tr-3", name: __T(670), prem: [], goal: "~~((P -> Q) | (Q -> P))", par: 9, classical: false, goalText: __T(660, [F("~~((P -> Q) | (Q -> P))")]),
    trans: () => ({ src: F("(P->Q)|(Q->P)"), dst: `<span class="f">${TPADD("¬¬")}<span class="par">(</span>${fh(parse("(P->Q)|(Q->P)"))}<span class="par">)</span></span>` }),
    lesson: __T(671, [F("(P->Q)|(Q->P)")]),
    hints: [__T(672, [F("~((P->Q)|(Q->P))"), F("(P->Q)|(Q->P)")]),
            __T(673, [F("Q->P"), F("P"), F("P->Q"), F("Q")]),
            __T(674, [F("Q"), F("Q"), F("Q")])] },
  "tr-4": { id: "tr-4", name: __T(675), kind: "tower", prem: [], goal: "~~!x.(P(x) | ~P(x))", par: null, classical: false,
    trans: () => ({ src: F("!x.(P(x)|~P(x))"), dst: `<span class="f">${TPADD("¬¬")}${fh(parse("!x.(P(x)|~P(x))"))}</span>`, error: true }),
    goalText: __T(676),
    lesson: __T(677, [F("!x.(P(x)|~P(x))"), F("~~!x.(P(x)|~P(x))")]),
    hints: [__T(678),
            __T(679),
            __T(680)] },
  "tr-5": { id: "tr-5", name: __T(681), boss: true, sfFlicker: true, prem: [], goal: "~~!x.~~(P(x) | ~P(x))", par: 10, classical: false, goalText: __T(660, [F("~~!x.~~(P(x) | ~P(x))")]),
    trans: () => ({ src: F("!x.(P(x)|~P(x))"), dst: `<span class="f">${TPADD("¬¬")}<span class="q">∀<i class="tm">x</i></span>${TPADD("¬¬")}<span class="par">(</span>${fh(parse("P(x)|~P(x)"))}<span class="par">)</span></span>` }),
    lesson: __T(682, [F("~~!x.~~(P(x)|~P(x))")]),
    hints: [__T(683, [F("!x.~~(P(x)|~P(x))"), termH("a")]),
            __T(684, [F("~~(P(a)|~P(a))"), F("~(P(a)|~P(a))")]),
            __T(685, [F("~(P(a)|~P(a))"), F("P(a)")])] },
  // --- 迷宮の中枢（最終層） ---
  "core-1": { id: "core-1", name: __T(686), prem: [], goal: "~?y.!x.((K(y,x) -> ~K(x,x)) & (~K(x,x) -> K(y,x)))", par: 12,
    lesson: __T(687, [F("K(y,x)"), termH("y"), termH("x")]),
    hints: [__T(688),
            __T(689, [F("K(a,a) -> ~K(a,a)"), F("~K(a,a)"), F("~K(a,a)")]),
            __T(690, [termH("a"), F("~K(a,a)")])] },
  "core-2": { id: "core-2", name: __T(691), prem: [], goal: "!y.?x.~((D(y,x) -> ~D(x,x)) & (~D(x,x) -> D(y,x)))", par: 12,
    lesson: __T(692, [F("D(y,x)"), termH("y"), termH("x"), termH("y"), termH("x"), termH("y")]),
    hints: [__T(693, [termH("a"), termH("a")]),
            __T(694, [F("~D(a,a)")]),
            __T(695, [termH("a"), F("~D(a,a)")])] },
  "core-3": { id: "core-3", name: __T(696), kind: "refute", reveal: true, presets: ["z2", "z3", "v4", "s3"], prem: ["!x.!y.!z.((x * y) * z = x * (y * z))", "!x.(e * x = x)", "!x.(i(x) * x = e)"], goal: "#", par: null,
    lesson: __T(697),
    hints: [__T(698), __T(699), __T(700, [termH("e"), termH({ f: "i", args: ["x"] })])] },
  "core-4": { id: "core-4", name: __T(701), kind: "judge", indep: true, presets: ["z2", "z3", "v4", "s3"],
    goalText: __T(702, [F("!x.!y.(x * y = y * x)")]),
    lesson: __T(703, [F("!x.!y.(x * y = y * x)")]),
    hints: [__T(704),
            __T(705),
            __T(706)],
    parts: [{ key: "A", prem: ["!x.!y.!z.((x * y) * z = x * (y * z))", "!x.(e * x = x)", "!x.(i(x) * x = e)"], goal: "!x.!y.(x * y = y * x)", real: false, note: __T(707) },
            { key: "¬A", prem: ["!x.!y.!z.((x * y) * z = x * (y * z))", "!x.(e * x = x)", "!x.(i(x) * x = e)"], goal: "~!x.!y.(x * y = y * x)", real: false, note: __T(708) }] },
  "core-5": { id: "core-5", name: __T(709), kind: "judge", indep: true, thirdWay: true, boss: true, indOff: true,
    goalText: __T(710, [F("!x.(0 + x = x)")]),
    lesson: __T(711, [F("!x.(0 + x = x)")]),
    hints: [__T(712, [termH("s")]),
            __T(713),
            __T(714)],
    parts: [{ key: "A", prem: ["!x.(x + 0 = x)", "!x.!y.(x + s(y) = s(x + y))"], goal: "!x.(0 + x = x)", real: false, note: __T(715) },
            { key: "¬A", prem: ["!x.(x + 0 = x)", "!x.!y.(x + s(y) = s(x + y))"], goal: "~!x.(0 + x = x)", real: false, note: __T(716) }] },
};
(() => {
  const all = WORLDS.flatMap(w => w.stages), byOld = new Map(WORLDS.map(w => [w.id, w]));
  const S0 = id => { const s = all.find(x => x.id === id) || NEWST[id]; if (!s) throw new Error("stage " + id); return s; };
  const DROP = new Set(["x-injeq", "11-2", "13-1"]); // 削除したステージ（13-4 単射の言い換え、14-2 左消去律を鍛える、16-1 1 を掛ける）
  const plan = [
    { from: 1 }, { from: 2 }, { from: 3 }, { from: 4 },
    { oid: 6, name: __T(717), rules: __T(718), ids: ["6-1", "6-2", "c-imp", "c-contra", "6-3", "6-4", "6-5"] },
    { oid: 6, name: __T(719), rules: __T(720), ids: ["r-conv", "r-inv", "r-ior", "r-dm", "6-6"] },
    { oid: 5, extra: true, xid: "H1", xlabel: __T(721), xnum: 1, name: __T(722), rules: __T(723), ids: ["5-1", "5-2", "5-3", "5-4", "5-5"] }, // Extra World（クリアしなくても次へ進める）
    { oid: 7, name: __T(199), rules: __T(724), ids: ["7-1", "f-rename", "7-2", "f-barbara", "f-alll", "f-allr", "f-dist"] },
    { oid: 7, name: __T(725), rules: __T(726), ids: ["7-3", "f-wit", "f-ae1", "f-ae2", "f-ex1", "f-ex2", "7-4", "7-5", "f-mouse"] },
    { oid: 8, name: __T(226), rules: __T(727), ids: ["f-barber", "f-nen", "8-1", "f-nan", "f-const", "8-2"] },
    { oid: 8, name: __T(728), rules: __T(729), ids: ["s-ex", "s-pos", "s-nomouse", "s-mouse", "8-3"] },
    { oid: 8, extra: true, xid: "H2", xlabel: __T(721), xnum: 2, needs: ["10-5", "H1-5"], name: __T(730), rules: __T(731), ids: ["tr-1", "tr-2", "tr-3", "tr-4", "tr-5"] }, // 隠し層 2：グリヴェンコの定理と、量化子での失敗
    { oid: 9, name: __T(732), rules: __T(733), ids: ["10-5", "10-6", "x-mono", "x-darii", "x-dmc", "x-bq1", "x-bq2"] }, // 等号の工房より前（補題の扉は数学の街から）
    { oid: 9, name: __T(247), rules: __T(248), ids: ["9-1", "9-2", "9-3", "9-4", "10-3", "10-4"] }, // 単射・全射の合成までが等号と関数記号の層（ボスは全射の合成）
    { oid: 10, name: __T(275), rules: __T(734), ids: ["9-5", "10-1", "10-2"] }, // 単位元から始まり、ボスは狭義の順序
    { oid: 11, name: __T(317), rules: __T(318), ids: ["11-1", "10-7", "11-3"] }, // 左からの消去でカードを鍛え、右単位元（ボス）で使う
    { from: 12 }, { from: 13, extra: true, xid: "S1", xlabel: __T(735), xnum: 1, needs: ["15-4"] }, { from: 14, extra: true, xid: "S2", xlabel: __T(735), xnum: 2, needs: ["S1-3"] }, { from: 15, extra: true, xid: "S3", xlabel: __T(735), xnum: 3, needs: ["15-4"] }, // 掛け算の 2 層と順序の塔は寄り道
    { oid: 12, noInd: true, name: __T(736), rules: __T(737), ids: ["x-total", "x-antisym", "x-max", "x-rid", "x-twoid", "x-comm", "x-order2", "x-nonab", "x-ind", "x-judge"] },
    { oid: 12, final: true, noInd: true, name: __T(738), rules: __T(739), ids: ["core-1", "core-2", "core-3", "core-4", "core-5"] }, // 最終層（近未来の見た目に変わる）
  ];
  let num = 0; // 隠し層・寄り道は本道の番号を持たない（ステージ番号は H1-1、S1-1 など）
  const out = plan.map(p => { const id = p.extra ? (p.xid || "EX") : ++num;
    const w = p.from ? Object.assign(byOld.get(p.from), { id, oid: p.from, extra: !!p.extra, xlabel: p.xlabel, xnum: p.xnum, needs: p.needs })
                     : { id, oid: p.oid, extra: !!p.extra, final: !!p.final, noInd: !!p.noInd, xlabel: p.xlabel, xnum: p.xnum, needs: p.needs, name: p.name, rules: p.rules, stages: p.ids.map(S0) };
    w.stages = w.stages.filter(st => !DROP.has(st.id)); return w; });
  S0("7-5").boss = false;
  S0("10-7").boss = false; S0("10-8").boss = false; S0("9-5").boss = false; S0("10-4").boss = true; S0("10-2").boss = true; S0("6-5").boss = true; S0("8-2").boss = true; // 第 5 層・第 9 層の最後の扉もボスとして示す delete S0("9-3").earns; // 関数の合同は入門のステージ（カードは渡さない） // 「左からの消去」が数学の街のボス、「補集合の古典のド・モルガン」が集合の街のボス // 「順序の扉」はボスではなくなる（ボスは「ネズミとネコ」）
  WORLDS.length = 0; WORLDS.push(...out);
})();
const STAGES = WORLDS.flatMap(w => w.stages.map((s, j) => { const oldId = s.oldId || s.id;
  return Object.assign(s, { oldId, id: `${w.id}-${j + 1}`, tut: s.tut || TUT_AT[oldId] || [], world: w, pid: s.pid || oldId, bot: s.bot != null ? s.bot : w.oid >= 4,
    classical: s.classical != null ? s.classical : w.oid >= 6, fol: w.oid >= 7, lemma: s.lemma != null ? s.lemma : w.oid >= 11 /* 補題を立てるのは、補題の工房（第 14 層）から */, nat: w.oid >= 12,
    ind: w.oid >= 12 && !w.noInd /* 帰納法の規則：自然数の塔と寄り道だけ（公理の鏡と迷宮の中枢の掟には帰納法がない） */ }); }));
// 説明文の中の {{s:キー}}（ステージ番号）と {{w:キー}}（ワールド番号）を、並べ替え後の番号に置き換える（キーは元の番号）
const STAGE_BY_KEY = new Map(STAGES.map(s => [s.oldId, s]));
const WL = w => w.extra ? (w.xlabel || __T(721)) + (w.xnum ? " " + w.xnum : "") : __T(740, [w.id]); // 層（ワールド）の呼び名
const WN = key => { const st = STAGE_BY_KEY.get(key); return st ? WL(st.world) : __T(741); };
(() => {
  const rep = str => typeof str === "string" ? str.replace(/\{\{([sw]):([^}]+)\}\}/g, (m, k, key) => { const st = STAGE_BY_KEY.get(key); return !st ? m : k === "s" ? st.id : WL(st.world); }) : str;
  for (const st of STAGES) { st.lesson = rep(st.lesson); if (st.hints) st.hints = st.hints.map(rep); st.doneNote = rep(st.doneNote); if (st.parts) st.parts.forEach(pt => { pt.note = rep(pt.note); }); }
})();
const CL = () => !!(STAGE && STAGE.classical); // 古典論理のステージか
// 照合：寄り道 S1〜S3 で、∀ の付いた等式の鍵をそのまま扉に差し込める（帰納法に慣れたあとの新しい技）
const matchOn = () => !!STAGE && /^S[123]$/.test(String(STAGE.world && STAGE.world.id));
// 照合を使ったお手本の解き方で測り直した目安の手数（寄り道 S1〜S3）。★ もこの目安で判定する
const MATCH_PAR = { "13-2": 6, "13-3": 11, "13-4": 13, "14-1": 12, "14-2": 15, "14-3": 9, "14-div": 11, "15-3": 6, "15-5": 14 };
STAGES.forEach(st => { if (MATCH_PAR[st.pid] != null) st.par = MATCH_PAR[st.pid]; });

/* ================= 証明状態（穴付き証明項） =================
   goals[id] = { id, ctx:[{name,f,kind:'prem'|'asm'|'der',level,rule?}], target, level }
   fills[id] = 穴 id を埋めた項（新しい穴を含んでよい）
   項: var / lam / app / pair / fst / snd / let / hole（各ノードは型 ty を持つ） */
// 定理カード：以前に証明した定理（閉じた式）。カードが使えるステージでは、入口の広間に特別な鍵として置かれる
const CARDS = {
  sym: { name: __T(742), f: "!x.!y.(x = y -> y = x)" },
  trans: { name: __T(743), f: "!x.!y.!z.(x = y -> (y = z -> x = z))" },
  cong: { name: __T(744), f: "!x.!y.(x = y -> f(x) = f(y))" },
  lcancel: { name: __T(745), f: "!x.!y.!z.(x * y = x * z -> y = z)" },
  zeroL: { name: __T(340), f: "!x.(0 + x = x)" },
  succL: { name: __T(346), f: "!x.!y.(s(x) + y = s(x + y))" },
  assocAdd: { name: __T(368), f: "!x.!y.!z.((x + y) + z = x + (y + z))" },
  commAdd: { name: __T(351), f: "!x.!y.(x + y = y + x)" },
  zeroMulL: { name: __T(363), f: "!x.(0 * x = 0)" },
  distrib: { name: __T(373), f: "!x.!y.!z.(x * (y + z) = x * y + x * z)" },
  assocMul: { name: __T(380), f: "!x.!y.!z.((x * y) * z = x * (y * z))" },
  succMulL: { name: __T(385), f: "!x.!y.(s(x) * y = x * y + y)" },
  commMul: { name: __T(391), f: "!x.!y.(x * y = y * x)" },
  zeroLe: { name: __T(403), f: "!x.(0 <= x)" },
  leSucc: { name: __T(746), f: "!x.(x <= s(x))" },
};
// 定理カードの印（入手できるステージの扉と、ステージ画面・クリア画面に付ける）
const ICON_CARD = got => `<svg class="card-ic" viewBox="0 0 18 22" aria-hidden="true"><rect x="1.2" y="1.2" width="15.6" height="19.6" rx="2.6" fill="${got ? "currentColor" : "none"}" stroke="currentColor" stroke-width="1.6"/><path d="M5 7.5h8M5 11h8M5 14.5h5" stroke="${got ? "var(--card-ink, #2a1d0e)" : "currentColor"}" stroke-width="1.4" stroke-linecap="round"/></svg>`;
const cardGot = id => !!(PROG.cards && PROG.cards[id]);
// 穴の並んだ定理カード（パンチカード）。穴の並びは定理ごとに決まる。anim のときは、穴がひとつずつ穿たれていく
function PUNCH_CARD(id, anim) {
  let h = 7; for (const c of String(id)) h = (h * 31 + c.charCodeAt(0)) >>> 0;
  const holes = []; if (id == null) return `<svg class="punch" viewBox="0 0 34 52" aria-hidden="true"><path d="M3 2h22l6 6v41a1 1 0 0 1-1 1H3a1 1 0 0 1-1-1V3a1 1 0 0 1 1-1z" class="pc-body"/><path d="M5 7h18" class="pc-line"/></svg>`; // 白紙のカード
  for (let r = 0; r < 6; r++) for (let c = 0; c < 3; c++) { const bit = (h >>> ((r * 3 + c) % 29)) & 1; if (bit || (r + c) % 4 === 0) holes.push([8 + c * 9, 13 + r * 6.2]); }
  return `<svg class="punch${anim ? " anim" : ""}" viewBox="0 0 34 52" aria-hidden="true"><path d="M3 2h22l6 6v41a1 1 0 0 1-1 1H3a1 1 0 0 1-1-1V3a1 1 0 0 1 1-1z" class="pc-body"/><path d="M5 7h18" class="pc-line"/>` +
    holes.map(([x, y], k) => `<rect class="ph" x="${x - 2.2}" y="${y - 1.5}" width="4.4" height="3" rx=".8" style="animation-delay:${(0.35 + k * 0.11).toFixed(2)}s"/>`).join("") + `</svg>`;
}
function cardGetHTML(st, newCard) {
  return `<div class="card-get">${PUNCH_CARD(st.earns, newCard)}<div><b>${newCard ? L1(__T(747, [CARDS[st.earns].name]), `You obtained the theorem card "${CARDS[st.earns].name}"`) : L1(__T(748, [CARDS[st.earns].name]), `Theorem card "${CARDS[st.earns].name}" (already obtained)`)}</b><div class="card-get-f">${F(CARDS[st.earns].f)}</div><span class="note">${newCard ? L1(__T(749), "Holes are punched into the card. Their pattern remembers the shape of the theorem.") : ""}${L1(__T(750), "It will be dealt as an assumption key in later stages.")}</span></div></div>`;
}
const cardTip = s => cardGot(s.earns) ? __T(751, [CARDS[s.earns].name]) : __T(752, [CARDS[s.earns].name]);
function initState(st) {
  const ctx = [...st.prem.map((p, i) => ({ name: "h" + (i + 1), f: parse(p), kind: "prem", level: 0 })),
               ...(st.cards || []).map((id, i) => ({ name: "c" + (i + 1), f: parse(CARDS[id].f), kind: "card", card: id, level: 0 }))];
  const target = parse(st.goal), reserved = [...new Set([...ctx.flatMap(c => [...freeNames(c.f)]), ...freeNames(target)])];
  return { goals: { g0: { id: "g0", ctx, target, level: 0, names: [] } }, fills: {}, open: ["g0"], active: "g0",
           holeOp: { g0: 0 }, nid: 1, nx: 1, nd: 1, ops: 0, log: [], reserved };
}
function replaceOpen(S, gid, ids) {
  for (const id of ids) if (!S.goals[id].names) S.goals[id].names = S.goals[gid].names || []; // 住人（名前）は子の扉に引き継ぐ
  const i = S.open.indexOf(gid);
  S.open.splice(i, 1, ...ids);
  S.active = ids.length ? ids[0] : (S.open.length ? S.open[Math.min(i, S.open.length - 1)] : null);
}
const findEntry = (g, name) => g.ctx.find(c => c.name === name);
const TERM_KIDS = ["body", "f", "a", "b", "p", "def", "l", "r", "base", "step"]; // 項の子ノード（論理式は .k を持たないので区別できる）
// 各操作で作った項のノードに「何手目で作られたか」を記録する（証明図で直前の操作を強調するため）
function stamp(t, op) {
  if (t.op == null) t.op = op;
  for (const k of TERM_KIDS) if (t[k] && t[k].k) stamp(t[k], op);
  return t;
}
const hasFormula = (g, f) => g.ctx.some(c => eq(c.f, f));

function useKind(f, target) {
  if (eq(f, target)) return "exact";
  if (isEq(f) && (countOcc(target, f.args[1]) || (STAGE && STAGE.eqBoth && countOcc(target, f.args[0])))) return "rew";
  if (f.t === "bot") return "abort";
  let cur = f;
  while (cur.t === "imp") { cur = cur.r; if (eq(cur, target)) return "chain"; }
  return null;
}
function combineResult(e1, e2, g) {
  let fn = null, arg = null;
  if (e2.f.t === "imp" && eq(e2.f.l, e1.f)) { fn = e2; arg = e1; }
  else if (e1.f.t === "imp" && eq(e1.f.l, e2.f)) { fn = e1; arg = e2; }
  if (!fn || hasFormula(g, fn.f.r)) return null;
  return { fn, arg, res: fn.f.r };
}

/* --- 操作（失敗時は状態を変更しない） --- */
// 新しい住人の名前（証明全体で一度も使っていない名前にするので、固有変数条件が自動的に満たされる）
const NAME_POOL = "abcdekmnuvw".split("");
const poolName = i => i < NAME_POOL.length ? NAME_POOL[i] : NAME_POOL[i % NAME_POOL.length] + (Math.floor(i / NAME_POOL.length) + 1);
// 新しい名前は、問題の定数だけでなく、証明のどこかに自由に現れている名前（自分で立てた補題や、入力した項の名前も）を避ける
function namesInUse(S) { const u = new Set(S.reserved || []); for (const g of Object.values(S.goals)) { g.ctx.forEach(c => freeNames(c.f).forEach(n => u.add(n))); freeNames(g.target).forEach(n => u.add(n)); (g.names || []).forEach(x => u.add(x.n)); } return u; }
function peekFresh(S) { const u = namesInUse(S); let i = S.np || 0; while (u.has(poolName(i))) i++; return poolName(i); }
// 固有変数条件：名前 a が、いま使える鍵（仮定）や指定した式に自由に現れていないか。現れている場所の一覧を返す
function eigenViolation(g, a, extra) {
  return [...g.ctx.filter(c => freeNames(c.f).has(a)).map(c => __T(753, [FF(c.f)])), ...extra.filter(f => freeNames(f).has(a)).map(f => __T(754, [FF(f)]))];
}
function freshName(S) { const u = namesInUse(S); let i = S.np || 0; while (u.has(poolName(i))) i++; S.np = i + 1; return poolName(i); } // 問題に出てくる定数の名前は避ける
const visibleNames = g => [...new Set([...(g.names || []).map(x => x.n), ...g.ctx.flatMap(c => [...freeNames(c.f)]), ...freeNames(g.target)])].filter(n => /^[a-z]/.test(n));
// 当てはめに使える項：見えている住人の名前と、鍵・扉に現れる（束縛変数を含まない）項 f(a)、a·b、a⁻¹ など
function visibleTerms(g) {
  const out = new Map(), add = t => out.set(termKey(t), t);
  visibleNames(g).forEach(add);
  const closed = (t, bound) => typeof t === "string" ? !bound.includes(t) : t.args.every(a => closed(a, bound));
  const walkT = (t, bound) => { if (typeof t === "string") { if (/^\d+$/.test(t)) add(t); return; } if (SETOPS.includes(t.f)) return; if (closed(t, bound)) add(t); t.args.forEach(a => walkT(a, bound)); };
  const walkF = (f, bound) => { switch (f.t) { case "atom": (f.args || []).forEach(a => walkT(a, bound)); break; case "bot": break; case "all": case "ex": walkF(f.b, [...bound, f.v]); break; default: walkF(f.l, bound); walkF(f.r, bound); } };
  g.ctx.forEach(c => walkF(c.f, [])); walkF(g.target, []);
  return [...out.values()];
}
// ∀E：鍵 ∀xA に住人 t を当てはめ、鍵 A(t) を得る（t が "*new" なら新しい住人を呼ぶ）
function opAllE(S, name, term, gid) {
  const g = S.goals[gid], e = findEntry(g, name);
  if (!e || e.f.t !== "all") return { ok: false, msg: __T(755) };
  const np0 = S.np, isNew = term === "*new", t = isNew ? freshName(S) : term;
  const res = inst(e.f.b, e.f.v, t);
  if (hasFormula(g, res)) { S.np = np0; return { ok: false, msg: __T(756, [FF(res)]) }; }
  const d = "d" + S.nd++, nid = "g" + S.nid++;
  S.goals[nid] = { id: nid, ctx: [...g.ctx, { name: d, f: res, kind: "der", level: g.level, rule: "∀E" }], target: g.target, level: g.level,
                   names: isNew ? [...(g.names || []), { n: t, level: g.level, via: "free" }] : g.names };
  S.fills[gid] = stamp({ k: "let", x: d, ty: g.target, body: { k: "hole", id: nid, ty: g.target },
    def: { k: "tapp", f: { k: "var", x: name, ty: e.f }, t, ty: res } }, S.ops + 1);
  S.holeOp[nid] = S.holeOp[gid];
  replaceOpen(S, gid, [nid]);
  return { ok: true, log: { rule: "∀E", text: __T(757, [FF(e.f), isNew ? __T(758) : "", termH(t), FF(res)]),
    fig: __T(759, [FF(e.f), FF(res)]) }, fresh: [d], src: [name] };
}
// ∃I：扉 ∃xA の証人として住人 t を選ぶ（行き止まりになりうる選択）
function opExI(S, gid, term) {
  const g = S.goals[gid], t0 = g.target;
  if (t0.t !== "ex") return { ok: false, msg: __T(760) };
  const isNew = term === "*new", t = isNew ? freshName(S) : term, body = inst(t0.b, t0.v, t);
  const nid = "g" + S.nid++;
  S.goals[nid] = { id: nid, ctx: g.ctx, target: body, level: g.level, names: isNew ? [...(g.names || []), { n: t, level: g.level, via: "free" }] : g.names };
  S.fills[gid] = stamp({ k: "pack", t, ty: t0, p: { k: "hole", id: nid, ty: body } }, S.ops + 1);
  S.holeOp[nid] = S.ops + 1;
  replaceOpen(S, gid, [nid]);
  return { ok: true, log: { rule: "∃I", text: __T(761, [isNew ? __T(758) : "", termH(t), FF(body)]),
    fig: __T(762, [FF(t0), termH(t), FF(body)]) } };
}
// =E（後ろ向き）：鍵 s = t で、扉の中の t（選んだ出現）を s に書き換える
function opRewBack(S, eqName, gid, sel, dir) {
  const g = S.goals[gid], e = findEntry(g, eqName);
  if (!e || !isEq(e.f)) return { ok: false, msg: __T(763) };
  const [s1, t1] = e.f.args, both = !!STAGE.eqBoth, nT = countOcc(g.target, t1), nS = both ? countOcc(g.target, s1) : 0;
  if (!dir) dir = nT && nS ? (termSize(s1) > termSize(t1) ? "rev" : "std") : nT ? "std" : nS ? "rev" : null; // 両方あるときは、大きい項を小さい項へ
  if (!dir) { // 書き換えられない：扉に同じ名前が「束縛変数としてだけ」現れるなら、そう説明する
    const names = allNames(g.target), bnd = [both ? s1 : null, t1].filter(x => typeof x === "string" && names.has(x));
    const bnote = bnd.length ? L1(__T(764, [bnd.map(termH).join(__T(765))]), `The ${bnd.map(termH).join(", ")} in the door is a different variable, bound by a quantifier, so it is not rewritten.`) : "";
    return { ok: false, msg: both
      ? L1(__T(766, [FF(g.target), termH(s1), termH(t1), FF(e.f)]), `Neither ${termH(s1)} nor ${termH(t1)} occurs free in the door ${FF(g.target)}, so the key ${FF(e.f)} cannot rewrite it (on this level equations can be used both ways).`) + bnote
      : (bnd.length ? L1(__T(767, [termH(t1), FF(g.target)]), `The ${termH(t1)} of the equation does not occur free in the door ${FF(g.target)}.`) + bnote
                    : L1(__T(768, [FF(g.target), termH(t1), FF(e.f)]), `${termH(t1)} does not occur in the door ${FF(g.target)}, so the key ${FF(e.f)} cannot rewrite it.`))
        + L1(__T(769, [termH(t1), termH(s1)]), ` (In this game, rewriting turns the right side ${termH(t1)} in the door back into the left side ${termH(s1)}.)`) }; }
  const from = dir === "std" ? t1 : s1, to = dir === "std" ? s1 : t1, n = countOcc(g.target, from);
  if (!sel) { if (n > 1 || (nT && nS)) return { ok: false, pick: { mode: "back", eq: eqName, n, dir, flip: !!(nT && nS) } }; sel = [0]; }
  if (!sel.length) return { ok: false, msg: __T(770) };
  const nt = replaceOcc(g.target, from, to, new Set(sel)), nid = "g" + S.nid++, v = { k: "var", x: eqName, ty: e.f };
  S.goals[nid] = { id: nid, ctx: g.ctx, target: nt, level: g.level };
  S.fills[gid] = stamp({ k: "rew", a: dir === "std" ? v : symTerm(v, s1, t1), p: { k: "hole", id: nid, ty: nt }, ty: g.target }, S.ops + 1);
  S.holeOp[nid] = S.ops + 1;
  replaceOpen(S, gid, [nid]);
  return { ok: true, log: { rule: "=E", text: __T(771, [FF(e.f), termH(from), termH(to), dir === "rev" ? __T(772) : "", FF(nt)]),
    fig: __T(773, [FF(g.target), FF(e.f), FF(nt)]) }, srcDoor: [eqName] };
}
// 照合：∀x∀y(s = t) の鍵をそのまま扉へ。扉の中で、等式の片方の辺の形に合う部分を探し、当てはめる項を決めて書き換える（∀E と =E を一手に）
function stripAll(f) { const vs = []; let b = f; while (b && b.t === "all") { vs.push(b.v); b = b.b; } return { vs, body: b }; }
function tMatch(p, t, vs, sub) { // 一方向の照合：p の中の vs だけが変数
  if (typeof p === "string") { if (vs.includes(p)) { if (sub[p] !== undefined) return termEq(sub[p], t); sub[p] = t; return true; } return typeof t === "string" && t === p; }
  if (typeof t === "string" || t.f !== p.f || t.args.length !== p.args.length) return false;
  for (let i = 0; i < p.args.length; i++) if (!tMatch(p.args[i], t.args[i], vs, sub)) return false;
  return true;
}
function freeSubterms(f, bound = new Set(), out = []) { // 扉に自由に現れる項（量化子に束縛された変数を含むものは除く）
  const walk = t => { if (![...tNames(t)].some(x => bound.has(x))) out.push(t); if (typeof t !== "string") t.args.forEach(walk); };
  switch (f.t) { case "atom": (f.args || []).forEach(walk); break; case "bot": break;
    case "all": case "ex": freeSubterms(f.b, new Set([...bound, f.v]), out); break;
    default: freeSubterms(f.l, bound, out); freeSubterms(f.r, bound, out); }
  return out;
}
const ftext = f => FF(f).replace(/<[^>]+>/g, "");
function matchCands(g, e) {
  const { vs, body } = stripAll(e.f); if (!vs.length || !isEq(body)) return null;
  const [L, Rr] = body.args, both = !!STAGE.eqBoth, subs = freeSubterms(g.target), out = [], seen = new Map();
  let leftover = false;
  const sides = [["std", Rr], ...(both ? [["rev", L]] : [])];
  for (const [dir, pat] of sides) {
    if (typeof pat === "string" && vs.includes(pat)) continue; // 変数だけの辺では探さない（何にでも合ってしまうため）
    for (const t of subs) {
      const sub = {}; if (!tMatch(pat, t, vs, sub)) continue;
      if (vs.some(v => sub[v] === undefined)) { leftover = true; continue; } // 照合で決まらない変数が残る
      const key = vs.map(v => termKey(sub[v])).join("|");
      // 一つの当てはめで両方の辺が扉に現れるときは、ふつうの書き換えと同じく大きい項を小さい項へ
      let f = e.f; for (const v of vs) f = inst(f.b, f.v, sub[v]);
      const [s1, t1] = f.args, nT = countOcc(g.target, t1), nS = both ? countOcc(g.target, s1) : 0;
      const d = nT && nS ? (termSize(s1) > termSize(t1) ? "rev" : "std") : nT ? "std" : "rev";
      if (seen.has(key)) continue; seen.set(key, true);
      const from = d === "std" ? t1 : s1, to = d === "std" ? s1 : t1, nt = replaceOcc(g.target, from, to, new Set(Array.from({ length: countOcc(g.target, from) }, (_, i) => i)));
      const rk = "=>" + fkey(nt); if (seen.has(rk)) continue; seen.set(rk, true); // 同じ書き換えになる当てはめは、一つにまとめる
      out.push({ dir: d, sub, f });
    }
  }
  return { vs, body, cands: out, leftover };
}
function opMatchRew(S, keyName, gid, ci) {
  const g = S.goals[gid], e = findEntry(g, keyName), M = e && matchCands(g, e);
  if (!M) return { ok: false, msg: L1(__T(774), "This key cannot be matched.") };
  if (!M.cands.length) return { ok: false, msg: M.leftover
    ? L1(__T(775, [FF(e.f)]), `Matching alone cannot decide every term for the key ${FF(e.f)}. Tap its ∀ and instantiate it by hand.`)
    : L1(__T(776, [FF(g.target), FF(e.f)]), `No part of the door ${FF(g.target)} fits the shape of the key ${FF(e.f)}.`) };
  if (ci == null) { if (M.cands.length > 1) return { ok: false, matchPick: { key: keyName, n: M.cands.length } }; ci = 0; }
  const c = M.cands[ci]; if (!c) return { ok: false, msg: L1(__T(777), "Choose how to instantiate.") };
  let pf = { k: "var", x: keyName, ty: e.f }, f = e.f;
  for (const v of M.vs) { const res = inst(f.b, f.v, c.sub[v]); pf = { k: "tapp", f: pf, t: c.sub[v], ty: res }; f = res; }
  const [s1, t1] = f.args, from = c.dir === "std" ? t1 : s1, to = c.dir === "std" ? s1 : t1, n = countOcc(g.target, from);
  const nt = replaceOcc(g.target, from, to, new Set(Array.from({ length: n }, (_, i) => i))), nid = "g" + S.nid++;
  S.goals[nid] = { id: nid, ctx: g.ctx, target: nt, level: g.level };
  S.fills[gid] = stamp({ k: "rew", a: c.dir === "std" ? pf : symTerm(pf, s1, t1), p: { k: "hole", id: nid, ty: nt }, ty: g.target }, S.ops + 1);
  S.holeOp[nid] = S.ops + 1;
  replaceOpen(S, gid, [nid]);
  const subTxt = M.vs.map(v => `${termH(v)} = ${termH(c.sub[v])}`).join(L1(__T(778), ", "));
  return { ok: true, noSpend: true, log: { rule: "=E", eqInst: ftext(f), text: L1(__T(779, [FF(e.f), subTxt, termH(from), termH(to), c.dir === "rev" ? __T(772) : "", FF(nt)]), `Matching the key ${FF(e.f)} (${subTxt}), rewrite ${termH(from)} in the door to ${termH(to)}${c.dir === "rev" ? " (using the equation backwards)" : ""}. The door becomes ${FF(nt)}.`),
    fig: L1(__T(780, [FF(g.target), FF(e.f), FF(f)]), `An =E line above the goal ${FF(g.target)}, with ${FF(f)} made from the key ${FF(e.f)} by ∀E`) }, srcDoor: [keyName] };
}
// =E（前向き）：鍵 s = t で、別の鍵の中の s（選んだ出現）を t に書き換えた鍵を作る
function opRewFwd(S, eqName, tgtName, gid, sel, dir) {
  const g = S.goals[gid], e = findEntry(g, eqName), k = findEntry(g, tgtName);
  if (!e || !k || !isEq(e.f)) return { ok: false, msg: __T(763) };
  const [s1, t1] = e.f.args, both = !!STAGE.eqBoth, nS = countOcc(k.f, s1), nT = both ? countOcc(k.f, t1) : 0;
  if (!dir) dir = nS && nT ? (termSize(t1) > termSize(s1) ? "rev" : "std") : nS ? "std" : nT ? "rev" : null;
  if (!dir) return { ok: false, msg: __T(781, [FF(k.f), termH(s1), FF(e.f)]) };
  const from = dir === "std" ? s1 : t1, to = dir === "std" ? t1 : s1, n = countOcc(k.f, from);
  if (!sel) { if (n > 1 || (nS && nT)) return { ok: false, pick: { mode: "fwd", eq: eqName, tgt: tgtName, n, dir, flip: !!(nS && nT) } }; sel = [0]; }
  if (!sel.length) return { ok: false, msg: __T(770) };
  const res = replaceOcc(k.f, from, to, new Set(sel));
  if (hasFormula(g, res)) return { ok: false, msg: __T(756, [FF(res)]) };
  const d = "d" + S.nd++, nid = "g" + S.nid++;
  S.goals[nid] = { id: nid, ctx: [...g.ctx, { name: d, f: res, kind: "der", level: g.level, rule: "=E" }], target: g.target, level: g.level };
  S.fills[gid] = stamp({ k: "let", x: d, ty: g.target, body: { k: "hole", id: nid, ty: g.target },
    def: { k: "rew", a: dir === "std" ? { k: "var", x: eqName, ty: e.f } : symTerm({ k: "var", x: eqName, ty: e.f }, s1, t1), p: { k: "var", x: tgtName, ty: k.f }, ty: res } }, S.ops + 1);
  S.holeOp[nid] = S.holeOp[gid];
  replaceOpen(S, gid, [nid]);
  return { ok: true, log: { rule: "=E", text: __T(782, [FF(e.f), FF(k.f), termH(from), termH(to), dir === "rev" ? __T(772) : "", FF(res)]),
    fig: __T(783, [FF(e.f), FF(k.f), FF(res)]) }, fresh: [d], src: [eqName, tgtName] };
}
// 定義の展開（後ろ向き：扉、前向き：鍵）
function opUnfoldDoor(S, gid) {
  const g = S.goals[gid], u = defUnfold(g.target);
  if (!u) return { ok: false, msg: __T(784) };
  const nid = "g" + S.nid++, sym = defSym(g.target);
  S.goals[nid] = { id: nid, ctx: g.ctx, target: u, level: g.level };
  S.fills[gid] = stamp({ k: "unfold", p: { k: "hole", id: nid, ty: u }, ty: g.target }, S.ops + 1);
  S.holeOp[nid] = S.ops + 1;
  replaceOpen(S, gid, [nid]);
  return { ok: true, log: { rule: __T(785), text: __T(786, [FF(g.target), sym, DEFNAME[sym], FF(u)]),
    fig: __T(787, [FF(g.target), FF(u)]) } };
}
function opUnfoldKey(S, name, gid) {
  const g = S.goals[gid], e = findEntry(g, name), u = e && defUnfold(e.f);
  if (!u) return { ok: false, msg: __T(788) };
  if (hasFormula(g, u)) return { ok: false, msg: __T(756, [FF(u)]) };
  const d = "d" + S.nd++, nid = "g" + S.nid++, sym = defSym(e.f);
  S.goals[nid] = { id: nid, ctx: [...g.ctx, { name: d, f: u, kind: "der", level: g.level, rule: __T(785) }], target: g.target, level: g.level };
  S.fills[gid] = stamp({ k: "let", x: d, ty: g.target, body: { k: "hole", id: nid, ty: g.target }, def: { k: "unfold", p: { k: "var", x: name, ty: e.f }, ty: u } }, S.ops + 1);
  S.holeOp[nid] = S.holeOp[gid];
  replaceOpen(S, gid, [nid]);
  return { ok: true, log: { rule: __T(785), text: __T(789, [FF(e.f), sym, DEFNAME[sym], FF(u)]),
    fig: __T(790, [FF(e.f), FF(u)]) }, fresh: [d], src: [name] };
}
// 補題を立てる（カット）：まず扉 L を証明し、その後は鍵 L を使って元の扉を開ける。
// 自然演繹では、[L]ⁿ から D を示して →Iⁿ で L→D を作り、L の証明と →E で合わせる「回り道」にあたる
function opCut(S, gid, L) {
  const g = S.goals[gid];
  if (!L) return { ok: false, msg: __T(791) };
  const x = "x" + S.nx++, k = x.slice(1), a = "g" + S.nid++, b = "g" + S.nid++, lvl = g.level + 1;
  S.goals[a] = { id: a, ctx: g.ctx, target: L, level: g.level };
  S.goals[b] = { id: b, ctx: [...g.ctx, { name: x, f: L, kind: "asm", level: lvl, via: "cut" }], target: g.target, level: lvl };
  S.fills[gid] = stamp({ k: "cut", x, xty: L, a: { k: "hole", id: a, ty: L }, body: { k: "hole", id: b, ty: g.target }, ty: g.target }, S.ops + 1);
  S.holeOp[a] = S.holeOp[b] = S.ops + 1;
  replaceOpen(S, gid, [a, b]);
  return { ok: true, log: { rule: __T(792), text: __T(793, [FF(L), FF(L), FF(L), FF(g.target)]),
    fig: __T(794, [FF(g.target), FF(L), k, FF(g.target), k, FF({ t: "imp", l: L, r: g.target }), FF(L)]) } };
}
// 数学的帰納法：扉 ∀x φ(x) を、扉 φ(0) と「住人 n と帰納法の仮定 φ(n) を持つ部屋」の扉 φ(s(n)) に分ける
function opInd(S, gid) {
  const g = S.goals[gid], t = g.target;
  if (t.t !== "all") return { ok: false, msg: __T(795) };
  const nn = freshName(S), k = S.nx++, x = "x" + k, lvl = g.level + 1, a = "g" + S.nid++, b = "g" + S.nid++;
  const base = inst(t.b, t.v, "0"), ih = inst(t.b, t.v, nn), step = inst(t.b, t.v, { f: "s", args: [nn] });
  S.goals[a] = { id: a, ctx: g.ctx, target: base, level: g.level };
  S.goals[b] = { id: b, ctx: [...g.ctx, { name: x, f: ih, kind: "asm", level: lvl, via: "ind", param: nn }], target: step, level: lvl,
                 names: [...(g.names || []), { n: nn, level: lvl, via: "ind", sid: k }] };
  S.fills[gid] = stamp({ k: "ind", ty: t, n: nn, x, xty: ih, base: { k: "hole", id: a, ty: base }, step: { k: "hole", id: b, ty: step } }, S.ops + 1);
  S.holeOp[a] = S.holeOp[b] = S.ops + 1;
  replaceOpen(S, gid, [a, b]);
  return { ok: true, log: { rule: __T(796), text: __T(797, [FF(t), FF(base), FF(ih), FF(step)]),
    fig: __T(798, [FF(t), FF(base), FF(ih), k, FF(step), termH(nn)]) } };
}
// 等式を逆向きに使うときの対称律（s = t から t = s を =E と =I で作る）
const eqA = (a, b) => ({ t: "atom", n: "=", args: [a, b] });
const symTerm = (v, s1, t1) => ({ k: "rew", a: v, p: { k: "refl", ty: eqA(s1, s1) }, ty: eqA(t1, s1) });
// 住人を選ぶ欄からの操作の振り分け
function pickOp(S, pk, v) {
  if (typeof v === "string" && v[0] === "#") v = (UI.pickTerms || [])[+v.slice(1)];
  switch (pk.kind) {
    case "allE": return opAllE(S, pk.key, v, S.active);
    case "exI": return opExI(S, S.active, v);
    case "allI": return opIntro(S, S.active, v);
    case "exE": return opSplit(S, pk.key, S.active, v);
  }
  return { ok: false, msg: "" };
}
function opIntro(S, gid, chosen) {
  const g = S.goals[gid], t = g.target;
  if (t.t === "all") { // ∀I：任意の住人 a を連れて新しい部屋へ
    if (chosen && chosen !== "*new") {
      const bad = eigenViolation(g, chosen, [t]);
      if (bad.length) return { ok: false, flag: chosen, msg: __T(799, [termH(chosen), bad.join(__T(778))]) };
    }
    const a = chosen && chosen !== "*new" ? chosen : freshName(S), sid = S.nx++, nid = "g" + S.nid++, lvl = g.level + 1, body = inst(t.b, t.v, a);
    S.goals[nid] = { id: nid, ctx: g.ctx, target: body, level: lvl, names: [...(g.names || []), { n: a, level: lvl, via: "all", sid }] };
    S.fills[gid] = stamp({ k: "tlam", a, sid, ty: t, body: { k: "hole", id: nid, ty: body } }, S.ops + 1);
    S.holeOp[nid] = S.ops + 1;
    replaceOpen(S, gid, [nid]);
    return { ok: true, log: { rule: "∀I", text: __T(800, [termH(a), FF(body), termH(a)]),
      fig: __T(801, [FF(t), termH(a), FF(body)]) } };
  }
  if (t.t === "ex") return { ok: false, msg: __T(802) };
  if (isEq(t)) { // =I：両辺が同じ項なら開く（反射律）
    if (!termEq(t.args[0], t.args[1])) return { ok: false, msg: __T(803) };
    S.fills[gid] = stamp({ k: "refl", ty: t }, S.ops + 1);
    replaceOpen(S, gid, []);
    return { ok: true, log: { rule: "=I", text: __T(804, [FF(t)]), fig: __T(805, [FF(t)]) } };
  }
  if (t.t === "imp") {
    const x = "x" + S.nx++, nid = "g" + S.nid++, lvl = g.level + 1;
    S.goals[nid] = { id: nid, ctx: [...g.ctx, { name: x, f: t.l, kind: "asm", level: lvl }], target: t.r, level: lvl };
    S.fills[gid] = stamp({ k: "lam", x, xty: t.l, ty: t, body: { k: "hole", id: nid, ty: t.r } }, S.ops + 1);
    S.holeOp[nid] = S.ops + 1;
    replaceOpen(S, gid, [nid]);
    const k = x.slice(1);
    return { ok: true, log: { rule: "→I", text: __T(806, [FF(t.l), k, FF(t.r)]),
      fig: __T(807, [FF(t), k, FF(t.l), k, FF(t.r)]) } };
  }
  if (t.t === "and") {
    const a = "g" + S.nid++, b = "g" + S.nid++;
    S.goals[a] = { id: a, ctx: g.ctx, target: t.l, level: g.level };
    S.goals[b] = { id: b, ctx: g.ctx, target: t.r, level: g.level };
    S.fills[gid] = stamp({ k: "pair", ty: t, a: { k: "hole", id: a, ty: t.l }, b: { k: "hole", id: b, ty: t.r } }, S.ops + 1);
    S.holeOp[a] = S.holeOp[b] = S.ops + 1;
    replaceOpen(S, gid, [a, b]);
    return { ok: true, log: { rule: "∧I", text: __T(808, [FF(t), FF(t.l), FF(t.r)]),
      fig: __T(809, [FF(t), FF(t.l), FF(t.r)]) } };
  }
  if (t.t === "or") return { ok: false, msg: __T(810) };
  return { ok: false, msg: __T(811) };
}
// 背理法 RAA：「A でない」（¬A）を仮定して部屋に入り、⊥ を目指す
function opRAA(S, gid) {
  const g = S.goals[gid], t = g.target;
  if (t.t === "bot") return { ok: false, msg: __T(812) };
  const x = "x" + S.nx++, nid = "g" + S.nid++, lvl = g.level + 1, k = x.slice(1);
  const neg = { t: "imp", l: t, r: { t: "bot" } }, bot = { t: "bot" };
  S.goals[nid] = { id: nid, ctx: [...g.ctx, { name: x, f: neg, kind: "asm", level: lvl, via: "raa", concl: t }], target: bot, level: lvl };
  S.fills[gid] = stamp({ k: "raa", x, xty: neg, ty: t, body: { k: "hole", id: nid, ty: bot } }, S.ops + 1);
  S.holeOp[nid] = S.ops + 1;
  replaceOpen(S, gid, [nid]);
  return { ok: true, log: { rule: "RAA", text: __T(813, [FF(t), FF(neg), k]),
    fig: __T(814, [FF(t), k, FF(neg), k]) } };
}
// ⊥E（後ろ向き）：扉を ⊥ に切り替える（行き止まりになりうる選択）
function opExfalso(S, gid) {
  const g = S.goals[gid], t = g.target;
  if (t.t === "bot") return { ok: false, msg: __T(815) };
  const nid = "g" + S.nid++, bot = { t: "bot" };
  S.goals[nid] = { id: nid, ctx: g.ctx, target: bot, level: g.level };
  S.fills[gid] = stamp({ k: "abort", ty: t, p: { k: "hole", id: nid, ty: bot } }, S.ops + 1);
  S.holeOp[nid] = S.ops + 1;
  replaceOpen(S, gid, [nid]);
  return { ok: true, log: { rule: "⊥E", text: __T(816, [FF(t)]),
    fig: __T(817, [FF(t)]) } };
}
// ∨I：左右どちらを示すかを選ぶ（行き止まりになりうる選択）
function opOrIntro(S, gid, side) {
  const g = S.goals[gid], t = g.target;
  if (t.t !== "or") return { ok: false, msg: __T(818) };
  const nid = "g" + S.nid++, part = side === "l" ? t.l : t.r;
  S.goals[nid] = { id: nid, ctx: g.ctx, target: part, level: g.level };
  S.fills[gid] = stamp({ k: side === "l" ? "inl" : "inr", ty: t, p: { k: "hole", id: nid, ty: part } }, S.ops + 1);
  S.holeOp[nid] = S.ops + 1;
  replaceOpen(S, gid, [nid]);
  return { ok: true, log: { rule: "∨I", text: __T(819, [FF(t), side === "l" ? __T(820) : __T(821), FF(part)]),
    fig: __T(822, [FF(t), FF(part)]) } };
}

function opUse(S, name, gid) {
  const g = S.goals[gid], e = findEntry(g, name);
  if (!e) return { ok: false, msg: __T(823) };
  if (eq(e.f, g.target) && FF(e.f) !== FF(g.target)) S.alphaNow = true; // 束縛変数の名前だけが違う（α 同値）
  if (eq(e.f, g.target)) {
    S.fills[gid] = stamp({ k: "var", x: name, ty: e.f }, S.ops + 1);
    replaceOpen(S, gid, []);
    const lbl = e.kind === "asm" ? `[${FF(e.f)}]<sup>${e.name.slice(1)}</sup>` : FF(e.f);
    return { ok: true, log: { rule: __T(824), text: __T(825, [FF(e.f), FF(g.target)]),
      fig: e.kind === "der" ? __T(826, [FF(g.target), FF(e.f)]) : __T(827, [FF(g.target), lbl]) } };
  }
  if (e.f.t === "bot") { // ⊥E（前向きの ⊥ の鍵で、どの扉でも開ける）
    S.fills[gid] = stamp({ k: "abort", ty: g.target, p: { k: "var", x: name, ty: e.f } }, S.ops + 1);
    replaceOpen(S, gid, []);
    return { ok: true, log: { rule: "⊥E", text: __T(828, [FF(g.target)]),
      fig: __T(829, [FF(g.target), FF(g.target)]) } };
  }
  const prem = []; let cur = e.f, found = false;
  while (cur.t === "imp") { prem.push(cur.l); cur = cur.r; if (eq(cur, g.target)) { found = true; break; } }
  if (found) {
    let term = { k: "var", x: name, ty: e.f }, ty = e.f; const ids = [];
    for (const p of prem) {
      const nid = "g" + S.nid++;
      S.goals[nid] = { id: nid, ctx: g.ctx, target: p, level: g.level };
      ids.push(nid); ty = ty.r; S.holeOp[nid] = S.ops + 1;
      term = { k: "app", f: term, a: { k: "hole", id: nid, ty: p }, ty };
    }
    S.fills[gid] = stamp(term, S.ops + 1);
    replaceOpen(S, gid, ids);
    const text = prem.length === 1
      ? __T(830, [FF(e.f), FF(g.target), FF(prem[0])])
      : __T(831, [FF(e.f), FF(g.target), prem.map(FF).join(__T(778)), prem.length]);
    const fig = prem.length === 1
      ? __T(832, [FF(g.target), FF(e.f), FF(prem[0])])
      : __T(833, [FF(g.target), prem.length, FF(e.f), prem.map(FF).join(__T(778))]);
    return { ok: true, log: { rule: prem.length === 1 ? "→E" : "→E×" + prem.length, text, fig }, srcDoor: [name] };
  }
  if (e.f.t === "and" && (eq(e.f.l, g.target) || eq(e.f.r, g.target)))
    return { ok: false, msg: __T(834, [FF(e.f)]) };
  if (e.f.t === "or" && (eq(e.f.l, g.target) || eq(e.f.r, g.target)))
    return { ok: false, msg: __T(835, [FF(e.f)]) };
  if (isEq(e.f)) return opRewBack(S, name, gid); // 等式の鍵を扉へ：=E（後ろ向き）
  if (e.f.t === "all" && matchOn() && isEq(stripAll(e.f).body)) return opMatchRew(S, name, gid); // 照合（寄り道 S1〜S3）
  if (e.f.t === "all") return { ok: false, msg: __T(836, [FF(e.f)]) };
  if (e.f.t === "ex") return { ok: false, msg: __T(837, [FF(e.f)]) };
  if (e.f.t === "imp" && (() => { let c = e.f; while (c.t === "imp") c = c.r; return c.t === "bot"; })())
    return { ok: false, msg: __T(838, [FF(e.f)]) };
  if (e.f.t === "imp")
    return { ok: false, msg: __T(839, [FF(e.f), FF(g.target)]) };
  return { ok: false, msg: __T(840, [FF(e.f), FF(g.target)]) };
}

function opSplit(S, name, gid, chosen) {
  const g = S.goals[gid], e = findEntry(g, name);
  if (e && e.f.t === "ex") { // ∃E：A を満たす誰か b を連れて部屋に入る
    if (chosen && chosen !== "*new") {
      const bad = eigenViolation(g, chosen, [g.target]);
      if (bad.length) return { ok: false, flag: chosen, msg: __T(841, [termH(chosen), bad.join(__T(778))]) };
    }
    const b = chosen && chosen !== "*new" ? chosen : freshName(S), k = S.nx++, x = "x" + k, nid = "g" + S.nid++, lvl = g.level + 1, body = inst(e.f.b, e.f.v, b);
    S.goals[nid] = { id: nid, ctx: [...g.ctx, { name: x, f: body, kind: "asm", level: lvl, via: "ex", src: e.f, param: b }], target: g.target, level: lvl,
                     names: [...(g.names || []), { n: b, level: lvl, via: "ex", sid: k }] };
    S.fills[gid] = stamp({ k: "unpack", p: { k: "var", x: name, ty: e.f }, b, x, xty: body, ty: g.target, body: { k: "hole", id: nid, ty: g.target } }, S.ops + 1);
    S.holeOp[nid] = S.ops + 1;
    replaceOpen(S, gid, [nid]);
    return { ok: true, log: { rule: "∃E", text: __T(842, [FF(e.f), FF(body), termH(b), termH(b)]),
      fig: __T(843, [FF(g.target), k, FF(e.f), FF(body), k, FF(g.target), termH(b)]) }, srcDoor: [name] };
  }
  if (e && e.f.t === "or") { // ∨E：世界を二つに分け、両方で同じ扉を開ける
    const op = S.ops + 1, lvl = g.level + 1;
    const xa = "x" + S.nx++, xb = "x" + S.nx++, a = "g" + S.nid++, b = "g" + S.nid++;
    const pair = [+xa.slice(1), +xb.slice(1)];
    S.goals[a] = { id: a, ctx: [...g.ctx, { name: xa, f: e.f.l, kind: "asm", level: lvl, via: "or", side: "l", sib: xb, src: e.f, pair }], target: g.target, level: lvl };
    S.goals[b] = { id: b, ctx: [...g.ctx, { name: xb, f: e.f.r, kind: "asm", level: lvl, via: "or", side: "r", sib: xa, src: e.f, pair }], target: g.target, level: lvl };
    S.fills[gid] = stamp({ k: "case", ty: g.target, p: { k: "var", x: name, ty: e.f },
      x: xa, xty: e.f.l, l: { k: "hole", id: a, ty: g.target }, y: xb, yty: e.f.r, r: { k: "hole", id: b, ty: g.target } }, op);
    S.holeOp[a] = S.holeOp[b] = op;
    replaceOpen(S, gid, [a, b]);
    return { ok: true, log: { rule: "∨E", text: __T(844, [FF(e.f), FF(e.f.l), pair[0], FF(e.f.r), pair[1], FF(g.target)]),
      fig: __T(845, [FF(g.target), pair.join(","), FF(e.f), FF(e.f.l), pair[0], FF(g.target), FF(e.f.r), pair[1], FF(g.target)]) }, srcDoor: [name] };
  }
  if (!e || e.f.t !== "and") return { ok: false, msg: __T(846) };
  const fresh = [], defs = [];
  for (const [k, f] of [["fst", e.f.l], ["snd", e.f.r]]) {
    if (hasFormula(g, f) || fresh.some(c => eq(c.f, f))) continue;
    const d = "d" + S.nd++;
    fresh.push({ name: d, f, kind: "der", level: g.level, rule: "∧E" });
    defs.push({ x: d, def: { k, p: { k: "var", x: name, ty: e.f }, ty: f } });
  }
  if (!fresh.length) return { ok: false, msg: __T(847) };
  const nid = "g" + S.nid++;
  S.goals[nid] = { id: nid, ctx: [...g.ctx, ...fresh], target: g.target, level: g.level };
  let term = { k: "hole", id: nid, ty: g.target };
  for (let i = defs.length - 1; i >= 0; i--) term = { k: "let", x: defs[i].x, def: defs[i].def, body: term, ty: g.target };
  S.fills[gid] = stamp(term, S.ops + 1);
  S.holeOp[nid] = S.holeOp[gid];
  replaceOpen(S, gid, [nid]);
  return { ok: true, log: { rule: "∧E", text: __T(848, [FF(e.f), fresh.map(c => FF(c.f)).join(__T(849))]),
    fig: __T(850, [FF(e.f), fresh.map(c => FF(c.f)).join(__T(849))]) }, fresh: fresh.map(c => c.name), src: [name] };
}

function opCombine(S, n1, n2, gid) {
  const g = S.goals[gid], e1 = findEntry(g, n1), e2 = findEntry(g, n2);
  if (!e1 || !e2 || n1 === n2) return { ok: false, msg: __T(823) };
  const r = combineResult(e1, e2, g);
  const rewCan = (eqE, k) => isEq(eqE.f) && (countOcc(k.f, eqE.f.args[0]) || (STAGE.eqBoth && countOcc(k.f, eqE.f.args[1])));
  if (!r && rewCan(e1, e2)) return opRewFwd(S, n1, n2, gid); // 等式の鍵を別の鍵へ：=E（前向き）
  if (!r && rewCan(e2, e1)) return opRewFwd(S, n2, n1, gid);
  if (!r) {
    let fn = null;
    if (e2.f.t === "imp" && eq(e2.f.l, e1.f)) fn = e2; else if (e1.f.t === "imp" && eq(e1.f.l, e2.f)) fn = e1;
    if (fn) return { ok: false, msg: __T(756, [FF(fn.f.r)]) };
    const imps = [e2, e1].filter(e => e.f.t === "imp");
    if (!imps.length) return { ok: false, msg: __T(851, [F("A->B")]) };
    return { ok: false, msg: __T(852, [FF(imps[0].f), FF(imps[0].f.l)]) };
  }
  const d = "d" + S.nd++, nid = "g" + S.nid++;
  S.goals[nid] = { id: nid, ctx: [...g.ctx, { name: d, f: r.res, kind: "der", level: g.level, rule: "→E" }], target: g.target, level: g.level };
  S.fills[gid] = { k: "let", x: d, ty: g.target, body: { k: "hole", id: nid, ty: g.target },
    def: { k: "app", f: { k: "var", x: r.fn.name, ty: r.fn.f }, a: { k: "var", x: r.arg.name, ty: r.arg.f }, ty: r.res } };
  stamp(S.fills[gid], S.ops + 1);
  S.holeOp[nid] = S.holeOp[gid];
  replaceOpen(S, gid, [nid]);
  return { ok: true, log: { rule: "→E", text: __T(853, [FF(r.arg.f), FF(r.fn.f), FF(r.res)]),
    fig: __T(854, [FF(r.fn.f), FF(r.arg.f), FF(r.res)]) }, fresh: [d], src: [r.fn.name, r.arg.name] };
}

/* --- ランタン：直観主義命題論理の決定手続き G4ip（Dyckhoff 1992）で、扉に出口があるかを判定する --- */
const mkImp = (a, b) => ({ t: "imp", l: a, r: b });
const G4MEMO = new Map();
// 古典論理での判定：真理値表（すべての割り当てで、仮定が真なら目標も真か）
function provableC(ctx, goal) {
  const atoms = atomsOf([...ctx, goal]);
  for (let m = 0; m < (1 << atoms.length); m++) {
    const val = new Set(atoms.filter((_, i) => (m >> i) & 1));
    const ev = f => f.t === "atom" ? val.has(f.n) : f.t === "bot" ? false : f.t === "and" ? ev(f.l) && ev(f.r) : f.t === "or" ? ev(f.l) || ev(f.r) : !ev(f.l) || ev(f.r);
    if (ctx.every(ev) && !ev(goal)) return false;
  }
  return true;
}
function countRAA(t) { let n = t && t.k === "raa" ? 1 : 0; if (t) for (const k of TERM_KIDS) if (t[k] && t[k].k) n += countRAA(t[k]); return n; }
function provable(ctx, goal) {
  const G = [];
  for (const f of ctx) if (!G.some(h => eq(h, f))) G.push(f);
  return g4(G, goal);
}
function g4(G, C) {
  const k = G.map(fkey).sort().join(",") + "⇒" + fkey(C);
  if (G4MEMO.has(k)) return G4MEMO.get(k);
  G4MEMO.set(k, false);
  const r = g4step(G, C);
  G4MEMO.set(k, r);
  return r;
}
function g4step(G, C) {
  const add = (H, f) => H.some(h => eq(h, f)) ? H : [...H, f];
  if (G.some(f => f.t === "bot")) return true;                         // ⊥ があれば何でも
  if (C.t === "atom" && G.some(f => eq(f, C))) return true;            // 公理
  if (C.t === "and") return g4(G, C.l) && g4(G, C.r);                  // 右 ∧（可逆）
  if (C.t === "imp") return g4(add(G, C.l), C.r);                      // 右 →（可逆）
  for (let i = 0; i < G.length; i++) {                                 // 左の可逆な規則
    const f = G[i], rest = G.filter((_, j) => j !== i);
    if (f.t === "and") return g4(add(add(rest, f.l), f.r), C);
    if (f.t === "or") return g4(add(rest, f.l), C) && g4(add(rest, f.r), C);
    if (f.t === "imp") {
      const a = f.l;
      if (a.t === "atom" && G.some(h => eq(h, a))) return g4(add(rest, f.r), C);
      if (a.t === "bot") return g4(rest, C);
      if (a.t === "and") return g4(add(rest, mkImp(a.l, mkImp(a.r, f.r))), C);
      if (a.t === "or") return g4(add(add(rest, mkImp(a.l, f.r)), mkImp(a.r, f.r)), C);
    }
  }
  if (C.t === "or" && (g4(G, C.l) || g4(G, C.r))) return true;        // 右 ∨（選択）
  for (let i = 0; i < G.length; i++) {                                 // 左 (A→B)→D（選択）
    const f = G[i];
    if (f.t === "imp" && f.l.t === "imp") {
      const rest = G.filter((_, j) => j !== i), A = f.l.l, B = f.l.r, D = f.r;
      if (g4(add(rest, mkImp(B, D)), mkImp(A, B)) && g4(add(rest, D), C)) return true;
    }
  }
  return false;
}
const goalSig = g => [...new Set(g.ctx.map(c => fkey(c.f)))].sort().join(",") + "⇒" + fkey(g.target);
const hasQuant = f => !!f && (f.t === "all" || f.t === "ex" || (f.l && hasQuant(f.l)) || (f.r && hasQuant(f.r)) || (f.b && hasQuant(f.b)) || (f.t === "atom" && (f.args || []).length > 0));
// 行き止まりの知らせ：命題論理の証明のステージ（第 1〜6 層と隠し層 1）だけ。鑑定と反証の問題では出さない（答えになってしまうため）
const autoDeadOn = () => !!STAGE && STAGE.kind !== "judge" && STAGE.kind !== "refute" && !STAGE.fol && !STAGE.ind && !STAGE.eqBoth
  && ![...(STAGE.prem || []), STAGE.goal].some(x => { try { return hasQuant(parse(x)); } catch (e) { return true; } });
function goalDead(g) { // この扉は、手元の鍵からはどう操作しても開かないか（命題論理）
  if (!g) return false;
  UI.deadCache = UI.deadCache || new Map();
  const sig = goalSig(g); if (UI.deadCache.has(sig)) return UI.deadCache.get(sig);
  let v; try { v = !(STAGE.classical && !STAGE.noRAA ? provableC : provable)(g.ctx.map(c => c.f), g.target); } catch (e) { v = false; }
  UI.deadCache.set(sig, v); return v;
}
function litOf(g) {
  if (!UI.lit) return undefined;
  const sig = goalSig(g);
  if (UI.lit.has(sig)) return UI.lit.get(sig);
  if (!autoDeadOn() || !UI.deadAlert) return undefined; // 知らせを出すまでは、行き止まりの印も出さない
  return goalDead(g) ? false : undefined;               // 開ける扉には何も出さない（答えを教えない）
}
// 行き止まりの見張り：同じ行き止まりの扉に戻ってきた（堂々巡り）か、行き止まりのまま 8 手進んだら、知らせる
function deadWatch() {
  if (!autoDeadOn() || !S) return;
  const deadNow = S.open.some(id => goalDead(S.goals[id]));
  if (!deadNow) { UI.deadAlert = null; UI.deadSeen = new Set(); UI.deadMoves = 0; return; }
  UI.deadMoves = (UI.deadMoves || 0) + 1; UI.deadSeen = UI.deadSeen || new Set();
  const g = S.goals[S.active], here = g && goalDead(g), sig = g ? goalSig(g) : "";
  const loop = here && UI.deadSeen.has(sig);
  if (here) UI.deadSeen.add(sig);
  if (!UI.deadAlert && (loop || UI.deadMoves >= 8)) { UI.deadAlert = deadOrigin(); renderDynamic(); }
}
function deadOrigin() { // まだどの扉も開けられた、最後の状態（その次の一手で行き止まりに入った）
  for (let k = HIST.length - 1; k >= 0; k--) {
    let st; try { st = JSON.parse(HIST[k]); } catch (e) { continue; }
    if (st.open.every(id => !goalDead(st.goals[id]))) {
      const lg = S.log[k], full = lg ? lg.text.replace(/<[^>]+>/g, "").replace(/\s+/g, " ").trim() : "";
      let first = LANG !== "ja" ? full.split(/\.\s/)[0].replace(/\.$/, "") : full.split(__T(855))[0]; // 記録の最初の一文だけ
      if (LANG === "en" && first) first = first[0].toLowerCase() + first.slice(1); // 括弧の中なので小文字で始める
      return { k, step: k + 1, text: first.length > 48 ? first.slice(0, 46) + "……" : first };
    }
  }
  return { k: 0, step: 1, text: "" };
}
function deadAlertHTML() {
  const a = UI.deadAlert; if (!a) return "";
  return `<div class="lit-box dead dead-alert" role="status">${L1(__T(856, [a.step, a.text ? __T(857, [a.text]) : ""]), `<b>Dead end</b>: since move ${a.step}${a.text ? ` (${a.text})` : ""}, you have been on a route on which the proof cannot be completed.`)}
    <div class="dead-acts"><button type="button" class="btn small primary" data-deadundo>${L1(__T(858, [a.step]), `Undo to before move ${a.step}`)}</button></div></div>`;
}

/* --- クリプキモデル（反証）：階 = 世界、上り階段 = 順序（根付きの木）、灯り = 原子命題の付値（上の階へ受け継がれる） --- */
function initR() { return { floors: [{ id: 0, parent: null, own: [] }], nid: 1, sel: 0, tv: {} }; }
const kFloor = (R, id) => R.floors.find(f => f.id === id);
const kKids = (R, id) => R.floors.filter(f => f.parent === id).map(f => f.id);
function kUp(R, id) { const out = [id]; for (let i = 0; i < out.length; i++) out.push(...kKids(R, out[i])); return out; } // id とそれより上の階
function kAnc(R, id) { const out = []; let f = kFloor(R, id); while (f && f.parent != null) { out.push(f.parent); f = kFloor(R, f.parent); } return out; } // 真に下の階
function kEff(R, id) { const s = new Set(kFloor(R, id).own); for (const a of kAnc(R, id)) for (const x of kFloor(R, a).own) s.add(x); return s; }
const kOrder = R => kUp(R, 0); // 根から幅優先の順（表示番号）
function makeForcer(R) { // 強制関係 w ⊩ f
  const memo = new Map(), effs = new Map(R.floors.map(f => [f.id, kEff(R, f.id)])), ups = new Map(R.floors.map(f => [f.id, kUp(R, f.id)]));
  const forces = (w, f) => {
    const k = w + "|" + fkey(f);
    if (memo.has(k)) return memo.get(k);
    let v = false;
    switch (f.t) {
      case "atom": v = effs.get(w).has(f.n); break;
      case "bot": v = false; break;
      case "and": v = forces(w, f.l) && forces(w, f.r); break;
      case "or": v = forces(w, f.l) || forces(w, f.r); break;
      case "imp": v = ups.get(w).every(u => !forces(u, f.l) || forces(u, f.r)); break;
    }
    memo.set(k, v); return v;
  };
  forces.ups = ups;
  return forces;
}
const kCounter = (R, forces, prem, goal) => kOrder(R).find(w => prem.every(p => forces(w, p)) && !forces(w, goal));
function subformulas(fs) { const out = []; const visit = f => { if (out.some(g => eq(g, f))) return; if (f.l) visit(f.l); if (f.r) visit(f.r); out.push(f); }; fs.forEach(visit); return out; }
function atomsOf(fs) { const s = new Set(); const v = f => { if (f.t === "atom") s.add(f.n); if (f.l) v(f.l); if (f.r) v(f.r); }; fs.forEach(v); return [...s].sort(); }

/* --- 一階述語論理の反例：有限構造（住人 1..n と、述語の表） --- */
// 既製の構造：よく知られた群や順序を、そのまま構造の欄に読み込める
const PRESETS = (() => {
  const tab = (n, f) => { const t = {}; for (let x = 1; x <= n; x++) for (let y = 1; y <= n; y++) t[x + "," + y] = String(f(x, y)); return t; };
  const un = (n, f) => { const t = {}; for (let x = 1; x <= n; x++) t[String(x)] = String(f(x)); return t; };
  const rel = (n, p) => { const r = []; for (let x = 1; x <= n; x++) for (let y = 1; y <= n; y++) if (p(x, y)) r.push(x + "," + y); return r; };
  const cyc = n => ({ n, fun: { "*": tab(n, (x, y) => ((x + y - 2) % n) + 1), i: un(n, x => ((n - (x - 1)) % n) + 1) }, con: { e: "1" } });
  const P = [[0, 1, 2], [1, 0, 2], [2, 1, 0], [0, 2, 1], [1, 2, 0], [2, 0, 1]]; // 3 次対称群：{1,2,3} の並べ替え
  const idx = p => P.findIndex(q => q.every((v, k) => v === p[k])) + 1;
  const s3 = { n: 6, fun: { "*": tab(6, (x, y) => idx(P[x - 1].map((_, k) => P[x - 1][P[y - 1][k]]))),
                            i: un(6, x => { const q = [0, 0, 0]; P[x - 1].forEach((v, k) => { q[v] = k; }); return idx(q); }) }, con: { e: "1" } };
  return [
    { id: "z2", name: __T(859), desc: __T(860), ...cyc(2) },
    { id: "z3", name: __T(861), desc: __T(862), ...cyc(3) },
    { id: "v4", name: __T(863), desc: __T(864), n: 4, fun: { "*": tab(4, (x, y) => ((x - 1) ^ (y - 1)) + 1), i: un(4, x => x) }, con: { e: "1" } },
    { id: "s3", name: __T(865), desc: __T(866), ...s3 },
    { id: "chain3", name: __T(867), desc: __T(868), n: 3, rel: { "≤": rel(3, (x, y) => x <= y), "<": rel(3, (x, y) => x < y) } },
    { id: "diamond", name: __T(869), desc: __T(870), n: 4, rel: { "≤": rel(4, (x, y) => x === y || x === 1 || y === 4), "<": rel(4, (x, y) => x !== y && (x === 1 || y === 4)) } },
  ];
})();
// いまの問題で使える既製の構造（ステージが許可したもののうち、問題の記号をすべて解釈できるもの）
function presetsFor() {
  if (!STAGE || !STAGE.presets || !PROBF) return [];
  const sig = sigOf([...PROBF.prem, PROBF.goal]);
  return PRESETS.filter(pr => STAGE.presets.includes(pr.id) && sig.funs.every(([f]) => pr.fun && pr.fun[f]) && sig.rels.every(([r]) => pr.rel && pr.rel[r]) && sig.cons.every(c => pr.con && pr.con[c]));
}
function loadPreset(id) {
  const pr = PRESETS.find(x => x.id === id); if (!pr) return;
  const snap = JSON.stringify(R), base = initStruct();
  const rel = JSON.parse(JSON.stringify(pr.rel || {})), relF = {};
  for (const P of Object.keys(rel)) { const ar = rel[P].length ? rel[P][0].split(",").length : 2; relF[P] = allTuples(pr.n, ar).filter(x => !rel[P].includes(x)); } // 既製の構造は、表がすべて決まっている
  R = { n: pr.n, rel, relF, fun: { ...base.fun, ...JSON.parse(JSON.stringify(pr.fun || {})) }, con: { ...base.con, ...(pr.con || {}) } };
  HISTR.push(snap); UI.presetOpen = false; renderStruct();
  toast(__T(871, [pr.name]));
}
// 言語の記号：関係（= を除く）、関数記号（項数つき）、定数（0 や e などの自由な名前）
function sigOf(fs) {
  const rels = new Map(), funs = new Map(), cons = new Set();
  const tw = (t, bound) => { if (typeof t === "string") { if (!bound.includes(t) && (/^\d+$/.test(t) || /^[a-z]/.test(t))) cons.add(t); return; } funs.set(t.f, t.args.length); t.args.forEach(a => tw(a, bound)); };
  const fw = (f, bound) => { if (!f) return; switch (f.t) { case "atom": if (f.n !== "=") rels.set(f.n, (f.args || []).length); (f.args || []).forEach(a => tw(a, bound)); break; case "bot": break;
    case "all": case "ex": fw(f.b, [...bound, f.v]); break; default: fw(f.l, bound); fw(f.r, bound); } };
  fs.forEach(f => fw(f, []));
  return { rels: [...rels.entries()].sort(), funs: [...funs.entries()].sort(), cons: [...cons].sort() };
}
function initStruct() { // 住人 1..n、関係の表、関数の表（値の初期値は住人 1）、定数の解釈（初期値は住人 1）
  const sig = PROBF ? sigOf([...PROBF.prem, PROBF.goal]) : { funs: [], cons: [] };
  return { n: 2, rel: {}, relF: {}, fun: Object.fromEntries(sig.funs.map(([f]) => [f, {}])), con: {} }; // 最初はすべて未定
}
// 3 値の論理（真・偽・未定）：未定の部分があっても、決まっている部分だけで真偽が決まるなら決める
const K3and = (a, b) => a === false || b === false ? false : a === true && b === true ? true : null;
const K3or = (a, b) => a === true || b === true ? true : a === false && b === false ? false : null;
const K3imp = (a, b) => a === false || b === true ? true : a === true && b === false ? false : null;
/* 決め手のまとめ：偽の目標を上からたどり、∀ なら反例の住人、→ なら前件が真で後件が偽の側…と選んで、最後の原子式の両辺の値まで下りる */
function decPath(St, f, want) {
  const val = g => evalS3(St, g), dom = Array.from({ length: St.n }, (_, k) => String(k + 1)), steps = [];
  let cur = f, w = want;
  for (let guard = 0; guard < 40; guard++) {
    if (isNeg(cur)) { cur = cur.l; w = !w; continue; }
    if (cur.t === "all" || cur.t === "ex") {
      const pickable = (cur.t === "all" && w === false) || (cur.t === "ex" && w === true);
      if (!pickable) return { steps, stop: (cur.t === "all" ? L1(__T(872, [FF(cur), termH(cur.v)]), `${FF(cur)} is true for every resident ${termH(cur.v)}`) : L1(__T(873, [FF(cur), termH(cur.v)]), `${FF(cur)} is false for every resident ${termH(cur.v)}`)) + L1(__T(874), " (open the per-resident checks in the diagram below)") };
      const d = dom.find(x => val(inst(cur.b, cur.v, x)) === w); if (d == null) return { steps };
      steps.push({ bind: [cur.v, d] }); cur = inst(cur.b, cur.v, d); continue;
    }
    if (cur.t === "and" || cur.t === "or") {
      const one = (cur.t === "and" && w === false) || (cur.t === "or" && w === true);
      if (!one) return { steps, both: [cur.l, cur.r], stop: L1(__T(875, [FF(cur.l), FF(cur.r), w ? __T(876) : __T(877)]), `both ${FF(cur.l)} and ${FF(cur.r)} are ${w ? "true" : "false"}`) };
      cur = val(cur.l) === w ? cur.l : cur.r; continue;
    }
    if (cur.t === "imp") {
      if (w === false) { steps.push({ note: L1(__T(878, [FF(cur.l)]), `${FF(cur.l)} is true`) }); cur = cur.r; continue; }
      return { steps, stop: val(cur.l) === false ? L1(__T(879, [FF(cur.l)]), `${FF(cur.l)} is false`) : L1(__T(880, [FF(cur.r)]), `${FF(cur.r)} is true`) };
    }
    return { steps, atom: cur, want: w };
  }
  return { steps };
}
function decCells(St, t, out) { // 項の値を計算するときに通る表の欄（f:キー）
  if (typeof t === "string") return evalTerm3(St, t);
  const vals = t.args.map(a => decCells(St, a, out)); if (vals.some(v => v == null)) return null;
  out.push(`${t.f}:${vals.join(",")}`); return ((St.fun && St.fun[t.f]) || {})[vals.join(",")];
}
function decSumHTML(St, prem, goal) {
  const val = g => evalS3(St, g); if (!prem.every(p => val(p) === true) || val(goal) !== false) return { html: "", cells: [] };
  const r = decPath(St, goal, false), cells = [];
  const binds = r.steps.filter(x => x.bind).map(x => `${termH(x.bind[0])} = ${L1(__T(881), "resident")} <b class="el">${x.bind[1]}</b>`).join(L1(__T(778), ", "));
  const notes = r.steps.filter(x => x.note).map(x => x.note);
  let tail = "";
  if (r.atom) { const a = r.atom;
    if (isEq(a)) { const [l, rr] = a.args, vl = decCells(St, l, cells), vr = decCells(St, rr, cells), sh = t => typeof t === "string" ? "" : ` = ${L1(__T(881), "resident")} <b class="el">${evalTerm3(St, t)}</b>`;
      tail = `${termH(l)}${sh(l)}${L1(__T(778), ", ")}${termH(rr)}${sh(rr)}${vl === vr ? L1(__T(882), " (the same resident)") : L1(__T(883), " (different residents)")}`; }
    else if (a.t === "bot") tail = L1(__T(884), "⊥ is false");
    else { const vals = (a.args || []).map(t => decCells(St, t, cells)); if (a.args && a.args.length) cells.push(`R@${a.n}:${vals.join(",")}`); tail = L1(__T(885, [FF(a), r.want ? __T(876) : __T(877)]), `${FF(a)} is ${r.want ? "true" : "false"}`); }
  } else if (r.stop) { tail = r.stop;
    (r.both || []).forEach(a => { if (a.t === "atom" && a.args && a.args.length) { if (isEq(a)) a.args.forEach(t => decCells(St, t, cells)); else { const vals = a.args.map(t => decCells(St, t, cells)); cells.push(`R@${a.n}:${vals.join(",")}`); } } }); }
  const goalLine = (binds ? L1(__T(886, [binds]), `False for: ${binds}`) : "") + (notes.length ? `${binds ? L1(__T(855), ". ") : ""}${notes.join(L1(__T(778), ", "))}` : "") + (tail ? `${binds || notes.length ? L1(" → ", " → ") : ""}${tail}` : "");
  return { html: `<div class="dec-sum"><div class="ds-row"><span class="ds-tag ok">${L1(__T(824), "Assumptions")}</span>${prem.length ? L1(__T(887, [prem.length]), `all hold (${prem.length})`) : L1(__T(888), "none")}</div><div class="ds-row"><span class="ds-tag bad">${L1(__T(889), "Goal")}</span>${goalLine || L1(__T(877), "false")}</div></div>`, cells };
}
function decSumApply() { // 右の欄の計算の上に、決め手のまとめを出し、構造の表の該当する欄に印を付ける
  if (!R || !PROBF) return;
  document.querySelectorAll(".dec-cell").forEach(x => x.classList.remove("dec-cell"));
  const { html, cells } = decSumHTML(R, PROBF.prem, PROBF.goal), ev = $("#kEval"); if (!ev) return;
  const old = ev.querySelector(".dec-sum"); if (old) old.remove();
  if (!html) return;
  const ttl = ev.querySelector(".ev-title"); (ttl || ev.firstChild) ? (ttl ? ttl.insertAdjacentHTML("afterend", html) : ev.insertAdjacentHTML("afterbegin", html)) : null;
  cells.forEach(c => { const sel = c.startsWith("R@") ? `[data-rel="${c.slice(2)}"]` : `[data-fun="${c}"]`; document.querySelectorAll(sel).forEach(b => b.classList.add("dec-cell")); });
}
/* 反例のクリア画面の一番上に「決め手」の帯。最初の 1〜2 秒だけ、決め手の札が中央に集まる */
function decBannerHTML(kind) {
  const st = STAGE, N = CX_NOTES[st.pid];
  const cap = N ? N.key().split(/(?<=。)|(?<=\. )/)[0].replace(/（[^（）]*）|\s\([^()]*\)/g, "").trim() : ""; // 問題ごとの見せ場（決め手の文の最初の一文。括弧の補足は省く）
  let tiles = [], sep = "", sub = "";
  if (kind === "fol") {
    const r = decPath(R, PROBF.goal, false), binds = r.steps.filter(x => x.bind).map(x => `${termH(x.bind[0])} = ${L1(__T(881), "resident")} <b class="el">${x.bind[1]}</b>`).join(L1(__T(778), ", "));
    if (r.atom && isEq(r.atom)) { const [l, rr] = r.atom.args, vl = evalTerm3(R, l), vr = evalTerm3(R, rr);
      const tile = t => typeof t === "string" ? `<span class="db-t">${termH(t)}</span>` : `<span class="db-t">${termH(t)}<span class="db-eq">=</span><b class="el">${evalTerm3(R, t)}</b></span>`;
      tiles = [tile(l), tile(rr)]; sep = vl === vr ? "=" : "≠"; }
    else if (r.atom && r.atom.t === "atom") tiles = [`<span class="db-t">${FF(r.atom)}<span class="db-v">${r.want ? L1(__T(876), "true") : L1(__T(877), "false")}</span></span>`];
    else if (r.both) tiles = r.both.map(a => `<span class="db-t">${FF(a)}<span class="db-v">${r.want ? L1(__T(876), "true") : L1(__T(877), "false")}</span></span>`);
    sub = (binds ? L1(__T(886, [binds]), `False for: ${binds}`) : (r.stop || "")) ;
    sub += `<span class="db-ok">${L1(__T(890, [PROBF.prem.length]), `all ${PROBF.prem.length} assumptions hold`)}</span>`;
  } else if (kind === "classical") {
    const tv = R.tv || {};
    tiles = PROB_ATOMS.map(a => `<span class="db-t db-stone ${tv[a] === "T" ? "on" : "off"}">${termH(a)}<span class="db-v">${tv[a] === "T" ? L1(__T(876), "true") : tv[a] === "F" ? L1(__T(877), "false") : L1(__T(891), "undecided")}</span></span>`);
    sub = `<span class="db-ok">${L1(__T(892), "every assumption true, the goal false")}</span>`;
  } else { // 時の塔
    const forces = makeForcer(R), lab = kLabels(), cex = kCounter(R, forces, PROBF.prem, PROBF.goal), L = lab.get(cex);
    tiles = [...PROBF.prem.map(f => `<span class="db-t db-chip lit">${FF(f)}<span class="db-v">${L1(__T(893), "lit")}</span></span>`), `<span class="db-t db-chip dark">${FF(PROBF.goal)}<span class="db-v">${L1(__T(894), "dark")}</span></span>`];
    sub = L1(__T(895, [L]), `Counterexample floor: floor ${L} (every assumption lit, only the goal dark)`);
  }
  return `<div class="dec-banner${esReduce() ? " still" : ""}"><div class="db-head">${L1(__T(896), "The key")}</div>` +
    `<div class="db-tiles">${tiles.map((t, i) => (i && sep ? `<span class="db-sep">${sep}</span>` : "") + `<span class="db-tw" style="--i:${i}">${t}</span>`).join("")}</div>` +
    (cap ? `<div class="db-cap">${cap}</div>` : "") + `<div class="db-sub">${sub}</div></div>`;
}
function decBannerInsert(kind) {
  const h = $(".overlay .modal h2"); if (!h || $(".overlay .dec-banner")) return;
  let html; try { html = decBannerHTML(kind); } catch (e) { return; }
  h.insertAdjacentHTML("afterend", html); cxSave(STAGE.pid, html);
  const ds = $(".overlay .dec-sum"); if (ds) ds.remove(); // 帯に同じ内容があるので、下のまとめは省く
}
const CXS_KEY = "proof-dungeon:cxsave";
const cxsLoad = () => { try { return JSON.parse(localStorage.getItem(CXS_KEY)) || {}; } catch (e) { return {}; } };
function cxSave(pid, html) { try { const m = cxsLoad(); m[pid] = { html: html.replace('class="dec-banner', 'class="dec-banner still'), t: Date.now() }; localStorage.setItem(CXS_KEY, JSON.stringify(m)); } catch (e) { /* 容量が足りなければ保存しない */ } }
/* 塔の絵：S3-5 では、作った模型の s のたどり方（0 から上って、いつか前の階に戻る ρ の形）を塔として描く。
   S3-6 では、二つのペアノの公理が「0 へ戻る矢印」と「途中へ合流する矢印」を断ち切り、階段が果てしなく続く */
const SUP = n => String(n).split("").map(c => "⁰¹²³⁴⁵⁶⁷⁸⁹"[+c]).join("");
const towerLab = i => i === 0 ? "0" : i === 1 ? "s(0)" : i === 2 ? "s(s(0))" : `s${SUP(i)}(0)`;
function towerLoopSVG(R0) {
  const z = R0.con && R0.con["0"], sf = (R0.fun && R0.fun.s) || {}; if (z == null) return "";
  const seq = [z]; let j = -1;
  for (let k = 0; k < 12; k++) { const nx = sf[seq[seq.length - 1]]; if (nx == null) return ""; const at = seq.indexOf(nx); if (at >= 0) { j = at; break; } seq.push(nx); }
  if (j < 0) return "";
  const n = seq.length, H = 62 + n * 46, X0 = 96, X1 = 214, y = i => H - 34 - i * 46;
  const floors = seq.map((r, i) => `<line class="tw-floor" x1="${X0}" y1="${y(i)}" x2="${X1}" y2="${y(i)}"/><text class="tw-lab" x="${X0 - 10}" y="${y(i) + 4}" text-anchor="end">${towerLab(i)}</text><text class="tw-res" x="${X1 + 8}" y="${y(i) + 4}">${L1(__T(881), "resident")} ${r}</text>`).join("");
  const stairs = seq.slice(1).map((_, i) => { const ya = y(i), yb = y(i + 1), xs = X1 - 30; return `<path class="tw-stair" d="M${xs} ${ya} L${xs} ${(ya + yb) / 2} L${xs + 14} ${(ya + yb) / 2} L${xs + 14} ${yb}"/>`; }).join("");
  const top = y(n - 1), tgt = y(j), xl = X0 + 8;
  const loop = n === 1 && j === 0 ? `M${X1 - 16} ${top} C ${X1 + 40} ${top - 60}, ${X0 - 40} ${top - 60}, ${xl} ${tgt}` : `M${X1 - 16} ${top} C ${X1 + 30} ${top - 54}, ${X0 - 54} ${top - 40}, ${xl} ${tgt}`;
  let climb = `M${X1 - 30} ${y(0)}`; for (let i = 1; i < n; i++) climb += ` L${X1 - 30} ${(y(i - 1) + y(i)) / 2} L${X1 - 16} ${(y(i - 1) + y(i)) / 2} L${X1 - 16} ${y(i)}`;
  if (n > 1) climb += ` L${X1 - 16} ${top}`; climb += " " + loop.replace(/^M[^C]*/, "");
  const dur = 1.2 + n * 0.55;
  return `<svg class="tw-svg" viewBox="0 ${Math.min(0, top - 70)} 320 ${H - Math.min(0, top - 70)}" role="img" aria-label="${L1(__T(897, [n, towerLab(j)]), `A tower whose stairs climb from 0 and return to the floor ${towerLab(j)} after ${n} floor(s)`)}">
    ${floors}${stairs}<path class="tw-loop" d="${loop}" marker-end="url(#twArr)"/>
    <defs><marker id="twArr" viewBox="0 0 10 10" refX="8" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M0 0L10 5L0 10z" class="tw-arrhead"/></marker></defs>
    <circle class="tw-dot" r="5.5"><animateMotion dur="${dur.toFixed(2)}s" begin="0.6s" repeatCount="2" fill="freeze" path="${climb}"/></circle>
  </svg>`;
}
function towerOpenSVG() {
  const n = 6, H = 360, X0 = 128, X1 = 246, y = i => H - 66 - i * 46;
  const floors = Array.from({ length: n }, (_, i) => `<g class="tw-fl" style="--o:${Math.max(0.12, 1 - i * 0.17).toFixed(2)}"><line class="tw-floor" x1="${X0}" y1="${y(i)}" x2="${X1}" y2="${y(i)}"/><text class="tw-lab" x="${X0 - 10}" y="${y(i) + 4}" text-anchor="end">${towerLab(i)}</text></g>`).join("");
  const stairs = Array.from({ length: n - 1 }, (_, i) => { const ya = y(i), yb = y(i + 1), xs = X1 - 30; return `<path class="tw-stair" style="opacity:${Math.max(0.12, 1 - i * 0.17).toFixed(2)}" d="M${xs} ${ya} L${xs} ${(ya + yb) / 2} L${xs + 14} ${(ya + yb) / 2} L${xs + 14} ${yb}"/>`; }).join("");
  const back0 = `M${X1 - 16} ${y(3)} C ${X0 - 96} ${y(3) - 10}, ${X0 - 96} ${y(0) - 10}, ${X0 + 8} ${y(0)}`;
  const merge = `M${X1 - 16} ${y(4)} C ${X1 + 84} ${y(4) - 10}, ${X1 + 84} ${y(2) - 10}, ${X1 - 2} ${y(2)}`;
  const py = y(0) + 18;
  return `<svg class="tw-svg tw-open" viewBox="0 -20 380 ${H + 20}" role="img" aria-label="${L1(__T(898), "A tower whose returning stairs are cut by two laws, so the stairs go on forever")}">
    ${floors}${stairs}
    <g class="tw-ghost g1"><path class="tw-back" d="${back0}"/><text class="tw-x" x="${X0 - 78}" y="${(y(0) + y(3)) / 2 + 4}">✕</text></g>
    <g class="tw-ghost g2"><path class="tw-back" d="${merge}"/><text class="tw-x" x="${X1 + 56}" y="${(y(2) + y(4)) / 2 + 4}">✕</text></g>
    <g class="tw-plq p1"><rect x="6" y="${py}" width="176" height="24" rx="5"/><text x="94" y="${py + 16}" text-anchor="middle">${L1(__T(899), "0 is no number's successor")}</text></g>
    <g class="tw-plq p2"><rect x="198" y="${py}" width="176" height="24" rx="5"/><text x="286" y="${py + 16}" text-anchor="middle">${L1(__T(900), "Equal successors, equal numbers")}</text></g>
    <circle class="tw-dot" r="5.5"><animateMotion dur="3.2s" begin="3.4s" repeatCount="indefinite" path="M${X1 - 30} ${y(0)} L${X1 - 30} ${y(0) - 23} L${X1 - 16} ${y(0) - 23} L${X1 - 16} ${y(1)} L${X1 - 30} ${y(1)} L${X1 - 30} ${y(1) - 23} L${X1 - 16} ${y(1) - 23} L${X1 - 16} ${y(2)} L${X1 - 30} ${y(2)} L${X1 - 30} ${y(2) - 23} L${X1 - 16} ${y(2) - 23} L${X1 - 16} ${y(3)} L${X1 - 30} ${y(3)} L${X1 - 30} ${y(4)} L${X1 - 16} ${y(5)} L${X1 - 16} -30"/></circle>
  </svg>`;
}
function towerInsert(kind) {
  const h = $(".overlay .modal h2"); if (!h || $(".overlay .tw-fig")) return;
  let svg = "", cap = "", sub = "";
  if (kind === "loop") { svg = towerLoopSVG(R); if (!svg) return;
    cap = L1(__T(901), "The laws and induction were kept. Even so, this tower had a ceiling.");
    sub = L1(__T(902), "Climbing from 0 one step of s at a time, the stairs come back to a floor you already passed. With finitely many residents, every model has this shape."); }
  else { svg = towerOpenSVG();
    cap = L1(__T(903), "There was no ceiling anywhere.");
    sub = L1(__T(904), "\"0 is no number's successor\" cuts the stairs back to 0, and \"equal successors, equal numbers\" cuts the stairs merging into a middle floor. With no way back, the stairs go on forever."); }
  h.insertAdjacentHTML("afterend", `<div class="tw-fig${esReduce() ? " still" : ""}">${svg}<div class="tw-cap">${cap}</div><div class="tw-sub">${sub}</div></div>`);
}
function decSumInsert() { // クリア画面にも、まとめを出す
  if (!R || !PROBF || !STAGE.fol) return;
  const g = $(".overlay .cm-graph"); if (!g || $(".overlay .dec-sum")) return;
  const { html } = decSumHTML(R, PROBF.prem, PROBF.goal); if (html) g.insertAdjacentHTML("beforebegin", html);
}
function evalTerm3(St, t, env = {}) { // 項の値。未定の定数や、未定の表の欄を通ると null
  if (typeof t === "string") { if (env[t] != null) return env[t]; if (/^[1-9]\d*$/.test(t)) return t; const c = St.con && St.con[t]; return c != null ? c : null; }
  const vals = t.args.map(a => evalTerm3(St, a, env)); if (vals.some(v => v == null)) return null;
  const r = ((St.fun && St.fun[t.f]) || {})[vals.join(",")]; return r != null ? r : null;
}
function evalS3(St, f, env = {}) {
  switch (f.t) {
    case "atom": {
      if (f.n === "=") { const a = evalTerm3(St, f.args[0], env), b = evalTerm3(St, f.args[1], env); return a == null || b == null ? null : a === b; }
      const vals = (f.args || []).map(t => evalTerm3(St, t, env)); if (vals.some(v => v == null)) return null;
      const tup = vals.join(","); if ((St.rel[f.n] || []).includes(tup)) return true; if (((St.relF || {})[f.n] || []).includes(tup)) return false; return null; }
    case "bot": return false;
    case "and": return K3and(evalS3(St, f.l, env), evalS3(St, f.r, env));
    case "or": return K3or(evalS3(St, f.l, env), evalS3(St, f.r, env));
    case "imp": return K3imp(evalS3(St, f.l, env), evalS3(St, f.r, env));
    case "all": { let acc = true; for (let d = 1; d <= St.n && acc !== false; d++) acc = K3and(acc, evalS3(St, f.b, { ...env, [f.v]: String(d) })); return acc; }
    case "ex": { let acc = false; for (let d = 1; d <= St.n && acc !== true; d++) acc = K3or(acc, evalS3(St, f.b, { ...env, [f.v]: String(d) })); return acc; }
  }
  return null;
}
function evalC3(f) { // 真理値の割り当て（R.tv）での 3 値の真偽
  switch (f.t) {
    case "atom": { const v = (R.tv || {})[f.n]; return v === "T" ? true : v === "F" ? false : null; }
    case "bot": return false;
    case "and": return K3and(evalC3(f.l), evalC3(f.r));
    case "or": return K3or(evalC3(f.l), evalC3(f.r));
    case "imp": return K3imp(evalC3(f.l), evalC3(f.r));
  }
  return null;
}
// 項の値（住人の番号）。束縛変数は env、定数は con、関数は表から
function evalTerm(St, t, env = {}) {
  if (typeof t === "string") { if (env[t] != null) return env[t]; if (St.con && St.con[t] != null) return St.con[t]; return /^[1-9]\d*$/.test(t) ? t : "1"; }
  const vals = t.args.map(a => evalTerm(St, a, env)), tab = (St.fun && St.fun[t.f]) || {};
  return tab[vals.join(",")] || "1";
}
function predsOf(fs) { const m = new Map(); const v = f => { if (!f) return; if (f.t === "atom") m.set(f.n, (f.args || []).length); if (f.l) v(f.l); if (f.r) v(f.r); if (f.b) v(f.b); }; fs.forEach(v); return [...m.entries()].sort(); }
function evalS(St, f, env = {}) { return evalS3(St, f, env) === true; }
function evalS2old(St, f, env = {}) {
  switch (f.t) {
    case "atom": { if (f.n === "=") return evalTerm(St, f.args[0], env) === evalTerm(St, f.args[1], env); // 等号は「同じ住人」
      const tup = (f.args || []).map(t => evalTerm(St, t, env)).join(","); return (St.rel[f.n] || []).includes(tup); }
    case "bot": return false;
    case "and": return evalS(St, f.l, env) && evalS(St, f.r, env);
    case "or": return evalS(St, f.l, env) || evalS(St, f.r, env);
    case "imp": return !evalS(St, f.l, env) || evalS(St, f.r, env);
    case "all": for (let d = 1; d <= St.n; d++) if (!evalS(St, f.b, { ...env, [f.v]: String(d) })) return false; return true;
    case "ex": for (let d = 1; d <= St.n; d++) if (evalS(St, f.b, { ...env, [f.v]: String(d) })) return true; return false;
  }
  return false;
}

/* --- 項の操作と型検査 --- */
function expand(S, t) {
  switch (t.k) {
    case "hole": return S.fills[t.id] ? expand(S, S.fills[t.id]) : t;
    case "var": return t;
    case "lam": case "raa": return { ...t, body: expand(S, t.body) };
    case "app": return { ...t, f: expand(S, t.f), a: expand(S, t.a) };
    case "pair": return { ...t, a: expand(S, t.a), b: expand(S, t.b) };
    case "fst": case "snd": return { ...t, p: expand(S, t.p) };
    case "let": return { ...t, def: expand(S, t.def), body: expand(S, t.body) };
    case "inl": case "inr": case "abort": case "pack": return { ...t, p: expand(S, t.p) };
    case "tlam": return { ...t, body: expand(S, t.body) };
    case "cut": return { ...t, a: expand(S, t.a), body: expand(S, t.body) };
    case "ind": return { ...t, base: expand(S, t.base), step: expand(S, t.step) };
    case "refl": return t;
    case "rew": return { ...t, a: expand(S, t.a), p: expand(S, t.p) };
    case "unfold": return { ...t, p: expand(S, t.p) };
    case "tapp": return { ...t, f: expand(S, t.f) };
    case "unpack": return { ...t, p: expand(S, t.p), body: expand(S, t.body) };
    case "case": return { ...t, p: expand(S, t.p), l: expand(S, t.l), r: expand(S, t.r) };
  }
  throw new Error("unknown term");
}
const rootTerm = S => expand(S, { k: "hole", id: "g0", ty: S.goals.g0.target });
function subst(t, x, s) {
  switch (t.k) {
    case "var": return t.x === x ? { ...s, op: t.op != null ? t.op : s.op } : t;
    case "hole": return t;
    case "lam": case "raa": return { ...t, body: subst(t.body, x, s) };
    case "app": return { ...t, f: subst(t.f, x, s), a: subst(t.a, x, s) };
    case "pair": return { ...t, a: subst(t.a, x, s), b: subst(t.b, x, s) };
    case "fst": case "snd": return { ...t, p: subst(t.p, x, s) };
    case "let": return { ...t, def: subst(t.def, x, s), body: subst(t.body, x, s) };
    case "inl": case "inr": case "abort": case "pack": return { ...t, p: subst(t.p, x, s) };
    case "tlam": return { ...t, body: subst(t.body, x, s) };
    case "cut": return { ...t, a: subst(t.a, x, s), body: subst(t.body, x, s) };
    case "ind": return { ...t, base: subst(t.base, x, s), step: subst(t.step, x, s) };
    case "refl": return t;
    case "rew": return { ...t, a: subst(t.a, x, s), p: subst(t.p, x, s) };
    case "unfold": return { ...t, p: subst(t.p, x, s) };
    case "tapp": return { ...t, f: subst(t.f, x, s) };
    case "unpack": return { ...t, p: subst(t.p, x, s), body: subst(t.body, x, s) };
    case "case": return { ...t, p: subst(t.p, x, s), l: subst(t.l, x, s), r: subst(t.r, x, s) };
  }
  throw new Error("unknown term");
}
function inline(t) { // 前向き推論で作った let を展開して、通常の自然演繹の証明にする
  switch (t.k) {
    case "let": return inline(subst(t.body, t.x, inline(t.def)));
    case "var": case "hole": return t;
    case "lam": case "raa": return { ...t, body: inline(t.body) };
    case "app": return { ...t, f: inline(t.f), a: inline(t.a) };
    case "pair": return { ...t, a: inline(t.a), b: inline(t.b) };
    case "fst": case "snd": return { ...t, p: inline(t.p) };
    case "inl": case "inr": case "abort": case "pack": return { ...t, p: inline(t.p) };
    case "tlam": return { ...t, body: inline(t.body) };
    case "cut": return { ...t, a: inline(t.a), body: inline(t.body) };
    case "ind": return { ...t, base: inline(t.base), step: inline(t.step) };
    case "refl": return t;
    case "rew": return { ...t, a: inline(t.a), p: inline(t.p) };
    case "unfold": return { ...t, p: inline(t.p) };
    case "tapp": return { ...t, f: inline(t.f) };
    case "unpack": return { ...t, p: inline(t.p), body: inline(t.body) };
    case "case": return { ...t, p: inline(t.p), l: inline(t.l), r: inline(t.r) };
  }
  throw new Error("unknown term");
}
function infer(t, env) { // 単純型付きラムダ計算の型検査（= 証明の検査）
  switch (t.k) {
    case "var": if (!env.has(t.x)) throw new Error(__T(905, [t.x])); return env.get(t.x);
    case "hole": throw new Error(__T(906));
    case "lam": { const e2 = new Map(env); e2.set(t.x, t.xty); return { t: "imp", l: t.xty, r: infer(t.body, e2) }; }
    case "raa": { const e2 = new Map(env); e2.set(t.x, t.xty);
      if (!eq(t.xty, { t: "imp", l: t.ty, r: { t: "bot" } }) || infer(t.body, e2).t !== "bot") throw new Error(__T(907));
      return t.ty; }
    case "app": { const ft = infer(t.f, env), at = infer(t.a, env);
      if (ft.t !== "imp" || !eq(ft.l, at)) throw new Error(__T(908)); return ft.r; }
    case "pair": return { t: "and", l: infer(t.a, env), r: infer(t.b, env) };
    case "fst": case "snd": { const p = infer(t.p, env); if (p.t !== "and") throw new Error(__T(909));
      return t.k === "fst" ? p.l : p.r; }
    case "let": { const d = infer(t.def, env); const e2 = new Map(env); e2.set(t.x, d); return infer(t.body, e2); }
    case "tlam": { // ∀I：固有変数 a は、仮定にも結論にも自由に現れてはならない
      for (const f of env.values()) if (freeNames(f).has(t.a)) throw new Error(__T(910, [t.a]));
      if (freeNames(t.ty).has(t.a) || t.ty.t !== "all") throw new Error(__T(911));
      if (!eq(infer(t.body, env), inst(t.ty.b, t.ty.v, t.a))) throw new Error(__T(912));
      return t.ty; }
    case "ind": { // 帰納法：出発点 φ(0)、帰納法の仮定 φ(n) から φ(s(n))。n は固有変数
      if (t.ty.t !== "all") throw new Error(__T(913));
      if (!eq(infer(t.base, env), inst(t.ty.b, t.ty.v, "0"))) throw new Error(__T(914));
      for (const f of env.values()) if (freeNames(f).has(t.n)) throw new Error(__T(910, [t.n]));
      if (freeNames(t.ty).has(t.n) || !eq(t.xty, inst(t.ty.b, t.ty.v, t.n))) throw new Error(__T(915));
      const e2 = new Map(env); e2.set(t.x, t.xty);
      if (!eq(infer(t.step, e2), inst(t.ty.b, t.ty.v, { f: "s", args: [t.n] }))) throw new Error(__T(916));
      return t.ty; }
    case "cut": { if (!eq(infer(t.a, env), t.xty)) throw new Error(__T(917));
      const e2 = new Map(env); e2.set(t.x, t.xty); if (!eq(infer(t.body, e2), t.ty)) throw new Error(__T(918)); return t.ty; }
    case "unfold": { const P = infer(t.p, env), u1 = defUnfold(P), u2 = defUnfold(t.ty);
      if (!((u1 && eq(u1, t.ty)) || (u2 && eq(u2, P)))) throw new Error(__T(919)); return t.ty; }
    case "refl": if (!isEq(t.ty) || !termEq(t.ty.args[0], t.ty.args[1])) throw new Error(__T(920)); return t.ty;
    case "rew": { const E = infer(t.a, env); if (!isEq(E)) throw new Error(__T(921));
      if (!sameUpTo(infer(t.p, env), t.ty, E.args[0], E.args[1])) throw new Error(__T(922)); return t.ty; }
    case "tapp": { const ft = infer(t.f, env); if (ft.t !== "all") throw new Error(__T(923)); return inst(ft.b, ft.v, t.t); }
    case "pack": { if (t.ty.t !== "ex" || !eq(infer(t.p, env), inst(t.ty.b, t.ty.v, t.t))) throw new Error(__T(924)); return t.ty; }
    case "unpack": { // ∃E：固有変数 b は、他の仮定・∃ の式・結論に自由に現れてはならない
      const d = infer(t.p, env);
      if (d.t !== "ex" || !eq(t.xty, inst(d.b, d.v, t.b))) throw new Error(__T(925));
      for (const f of env.values()) if (freeNames(f).has(t.b)) throw new Error(__T(910, [t.b]));
      const e2 = new Map(env); e2.set(t.x, t.xty);
      const c = infer(t.body, e2);
      if (freeNames(c).has(t.b) || !eq(c, t.ty)) throw new Error(__T(926));
      return c; }
    case "abort": { const b = infer(t.p, env); if (b.t !== "bot") throw new Error(__T(927)); return t.ty; }
    case "inl": case "inr": { const a = infer(t.p, env);
      if (t.ty.t !== "or" || !eq(t.k === "inl" ? t.ty.l : t.ty.r, a)) throw new Error(__T(928)); return t.ty; }
    case "case": { const d = infer(t.p, env);
      if (d.t !== "or" || !eq(d.l, t.xty) || !eq(d.r, t.yty)) throw new Error(__T(929));
      const e1 = new Map(env); e1.set(t.x, t.xty); const e2 = new Map(env); e2.set(t.y, t.yty);
      const c1 = infer(t.l, e1), c2 = infer(t.r, e2);
      if (!eq(c1, c2)) throw new Error(__T(930)); return c1; }
  }
  throw new Error("unknown term");
}
let TCUT = null; // 再生中、まだ組み上がっていない部分の証明項（? として表示する）
function tstr(t, prec, holes, active) {
  if (TCUT && TCUT.has(t)) return `<span class="hole">?</span>`;
  let s, p;
  switch (t.k) {
    case "var": return nm(t.x);
    case "hole": return `<span class="hole${t.id === active ? " on" : ""}">?${holes[t.id] ? sub(holes[t.id]) : ""}</span>`;
    case "pair": return `⟨${tstr(t.a, 0, holes, active)}, ${tstr(t.b, 0, holes, active)}⟩`;
    case "fst": s = `π₁ ${tstr(t.p, 2, holes, active)}`; p = 1; break;
    case "snd": s = `π₂ ${tstr(t.p, 2, holes, active)}`; p = 1; break;
    case "app": s = `${tstr(t.f, 1, holes, active)} ${tstr(t.a, 2, holes, active)}`; p = 1; break;
    case "lam": s = `λ${nm(t.x)}. ${tstr(t.body, 0, holes, active)}`; p = 0; break;
    case "raa": s = `𝒞 (λ${nm(t.x)}. ${tstr(t.body, 0, holes, active)})`; p = 1; break;
    case "let": s = `let ${nm(t.x)} = ${tstr(t.def, 0, holes, active)} in ${tstr(t.body, 0, holes, active)}`; p = 0; break;
    case "inl": s = `ι₁ ${tstr(t.p, 2, holes, active)}`; p = 1; break;
    case "tlam": s = `λ${termH(t.a)}. ${tstr(t.body, 0, holes, active)}`; p = 0; break;
    case "refl": return "refl";
    case "unfold": return tstr(t.p, prec, holes, active);
    case "ind": s = `ind ${tstr(t.base, 2, holes, active)} (λ${termH(t.n)}. λ${nm(t.x)}. ${tstr(t.step, 0, holes, active)})`; p = 1; break;
    case "cut": s = `(λ${nm(t.x)}. ${tstr(t.body, 0, holes, active)}) ${tstr(t.a, 2, holes, active)}`; p = 1; break;
    case "rew": s = `rew ${tstr(t.a, 2, holes, active)} ${tstr(t.p, 2, holes, active)}`; p = 1; break;
    case "tapp": s = `${tstr(t.f, 1, holes, active)} ${termH(t.t)}`; p = 1; break;
    case "pack": return `⟨${termH(t.t)}, ${tstr(t.p, 0, holes, active)}⟩`;
    case "unpack": s = `let ⟨${termH(t.b)}, ${nm(t.x)}⟩ = ${tstr(t.p, 0, holes, active)} in ${tstr(t.body, 0, holes, active)}`; p = 0; break;
    case "abort": s = `abort ${tstr(t.p, 2, holes, active)}`; p = 1; break;
    case "inr": s = `ι₂ ${tstr(t.p, 2, holes, active)}`; p = 1; break;
    case "case": s = `case ${tstr(t.p, 1, holes, active)} of ${nm(t.x)} ⇒ ${tstr(t.l, 0, holes, active)} ∣ ${nm(t.y)} ⇒ ${tstr(t.r, 0, holes, active)}`; p = 0; break; // ∨E：枝の順番で左右を区別する（Selinger の講義ノート、Martin-Löf の D と同じ流儀）
  }
  return p < prec ? `(${s})` : s;
}
// 穴付きの証明項から（未完成の部分を含む）自然演繹の証明図を作る。
// 仮定のラベルは変数名 xₙ の番号 n を使う（証明項と証明図で番号が一致する）。
function buildPT(t) { const n = buildPT0(t); n.tm = t; return n; } // 各頂点に、その頂点の証明項を持たせる
function buildPT0(t) {
  const num = x => +x.slice(1);
  switch (t.k) {
    case "hole": return { hole: true, f: t.ty, id: t.id };
    case "var": return { f: t.ty, leaf: true, disc: t.x[0] === "x" ? num(t.x) : 0, prem: t.x[0] === "h" || t.x[0] === "c", card: t.x[0] === "c", x: t.x, op: t.op };
    case "lam": return { f: t.ty, rule: "→I", sups: [num(t.x)], scopes: [num(t.x)], kids: [buildPT(t.body)], op: t.op };
    case "raa": return { f: t.ty, rule: "RAA", sups: [num(t.x)], scopes: [num(t.x)], kids: [buildPT(t.body)], op: t.op };
    case "inl": case "inr": return { f: t.ty, rule: "∨I", kids: [buildPT(t.p)], op: t.op };
    case "refl": return { f: t.ty, rule: "=I", kids: [], op: t.op };
    case "unfold": return { f: t.ty, rule: __T(785), kids: [buildPT(t.p)], op: t.op };
    case "ind": return { f: t.ty, rule: __T(931, [termH(t.n)]), sups: [num(t.x)], scopes: [0, num(t.x)], kids: [buildPT(t.base), buildPT(t.step)], op: t.op };
    case "cut": return { f: t.ty, rule: __T(932), op: t.op, kids: [
      { f: { t: "imp", l: t.xty, r: t.ty }, rule: "→I", sups: [num(t.x)], scopes: [num(t.x)], kids: [buildPT(t.body)], op: t.op, tm: { k: "lam", x: t.x, body: t.body } }, buildPT(t.a)] };
    case "rew": return { f: t.ty, rule: "=E", kids: [buildPT(t.a), buildPT(t.p)], op: t.op };
    case "tlam": return { f: t.ty, rule: "∀I", sups: [t.sid], supLabels: [termH(t.a)], scopes: [t.sid], kids: [buildPT(t.body)], op: t.op };
    case "tapp": return { f: t.ty, rule: "∀E", kids: [buildPT(t.f)], op: t.op };
    case "pack": return { f: t.ty, rule: "∃I", kids: [buildPT(t.p)], op: t.op };
    case "unpack": return { f: t.ty, rule: "∃E", sups: [num(t.x)], scopes: [0, num(t.x)], kids: [buildPT(t.p), buildPT(t.body)], op: t.op };
    case "abort": return { f: t.ty, rule: "⊥E", kids: [buildPT(t.p)], op: t.op };
    case "case": return { f: t.ty, rule: "∨E", sups: [num(t.x), num(t.y)], scopes: [0, num(t.x), num(t.y)],
                          kids: [buildPT(t.p), buildPT(t.l), buildPT(t.r)], op: t.op };
    case "app": return { f: t.ty, rule: "→E", kids: [buildPT(t.f), buildPT(t.a)], op: t.op }; // 左に主前提 A→B、右に小前提 A
    case "pair": return { f: t.ty, rule: "∧I", kids: [buildPT(t.a), buildPT(t.b)], op: t.op };
    case "fst": case "snd": return { f: t.ty, rule: "∧E", kids: [buildPT(t.p)], op: t.op };
  }
  throw new Error(__T(933));
}
function renderPT(n, cx) {
  if (n.hole) {
    const k = cx.holes[n.id];
    const lit = cx.lit ? cx.lit(n.id) : undefined;
    const cls = "pt-hole" + (n.id === cx.active ? " on" : "") + (cx.latest > 0 && cx.holeOp[n.id] === cx.latest ? " new" : "") +
                (lit === true ? " lit-ok" : lit === false ? " lit-dead" : "");
    return __T(934, [cls, n.id]) +
           `<span class="pt-goal">${cx.terms ? `<span class="pt-tm">?${k ? sub(k) : ""}</span><span class="pt-colon"> : </span>` : ""}${FF(n.f)}${k ? `<span class="pt-num">?${sub(k)}</span>` : ""}${lit === false ? __T(935) : ""}</span></button>`;
  }
  const isNew = cx.latest > 0 && n.op === cx.latest;
  const tmOf = t => { TCUT = cx.cut || null; const h = t.k === "var" ? nm(t.x) : tstr(t, 0, cx.holes || {}, cx.active); TCUT = null; return `<span class="pt-tm">${h}</span><span class="pt-colon"> : </span>`; };
  const f = (cx.terms && n.tm ? tmOf(n.tm) : "") + FF(n.f);
  if (n.leaf) {
    if (n.disc) return __T(936, [scls(n.disc), isNew ? " new" : "", n.x, n.disc, n.disc, n.disc, f, n.disc]);
    return `<div class="pt-leaf${n.prem ? " prem" : ""}${n.card ? " cardleaf" : ""}${isNew ? " new" : ""}" data-var="${n.x || ""}" ${n.card ? __T(937) : ""}>${f}</div>`;
  }
  // 前提ごとに、その上で解除される仮定のスコープ（→Iⁿ なら唯一の前提、∨Eᵐ'ⁿ なら2番目と3番目の前提）を色付きの範囲で包む
  const indLab = typeof n.rule === "string" && n.rule.startsWith(__T(796)) && n.kids.length === 2 ? [L1(__T(938), "Base (0)"), L1(__T(939), "Step (to the next number)")] : null; // 帰納法の見出し
  const kids = n.kids.map((c, i) => {
    const h0 = renderPT(c, cx), h = indLab ? `<div class="pt-indwrap"><div class="pt-indlab">${indLab[i]}</div>${h0}</div>` : h0, sc = n.scopes && n.scopes[i];
    if (!sc) return h;
    return `<div class="pt-scope ${scls(sc)}${cx.amb && cx.amb.has(sc) ? " amb" : ""}" data-scope="${sc}">${h}</div>`;
  }).join("");
  const sup = n.sups ? `<sup>${n.sups.map((k, i) => __T(940, [scls(k), k, n.supLabels ? n.supLabels[i] : k])).join(",")}</sup>` : "";
  const lt = cx.lean && n.tm ? leanTag(n.tm) : "";
  return `<div class="pt-node${isNew ? " new" : ""}"><div class="pt-prems">${kids}</div>` +
         `<div class="pt-bar"><span class="pt-rule${n.rule === "RAA" ? " raa" : ""}${RULE_BOOK[n.rule] ? " has-book" : ""}" data-rule="${esc(n.rule)}">${RD(n.rule)}${sup}${lt ? `<span class="pt-lean">${lt}</span>` : ""}</span></div>` +
         `<div class="pt-concl">${f}</div></div>`;
}
/* ================= Lean モード（試作：World 1〜6 の命題論理） =================
   証明項（穴あき）から、Lean 4 のタクティクによる証明を組み立てる。操作した順番ではなく、証明の構造（扉の分かれ方）に沿って並べ、
   まだ開いていない扉は sorry にする。Mathlib なしの Lean 4 で通る書き方だけを使う */
const LSUB = "₀₁₂₃₄₅₆₇₈₉";
const lnName = x => x[0] + x.slice(1).replace(/[0-9]/g, d => LSUB[+d]);
const leanOK = () => !!(STAGE && STAGE.world && !STAGE.world.extra); // 試作版：Extra World（クリプキモデル）以外
const leanOn = () => !!PREFS.leanMode && leanOK();
const leanCX = cx => leanOn() ? { ...cx, lean: true } : cx; // 証明図の規則の横に、対応するタクティクを添える
let LMODE = { nat: false, typed: false, leDef: false }; // いまの問題の書き方（自然数か、型の注記が要るか、≤ を定義で書くか）
function leanTmP(t, need = 0) { // 項を Lean の記法で（* と ∩ は 70、+ と ∪ は 65、いずれも左結合。s(t) は t + 1）
  if (typeof t === "string") return t;
  let s, p;
  const bin = (op, q) => { p = q; s = `${leanTmP(t.args[0], q)} ${op} ${leanTmP(t.args[1], q + 1)}`; };
  if (t.f === "*") bin("*", 70); else if (t.f === "+") bin("+", 65);
  else if (t.f === "∩") bin("∩", 70); else if (t.f === "∪") bin("∪", 65);
  else if (t.f === "ᶜ") { p = 1024; s = `${leanTmP(t.args[0], 1024)}ᶜ`; }
  else { p = 1000; s = `${t.f} ${t.args.map(a => leanTmP(a, 1024)).join(" ")}`; }
  return p < need ? `(${s})` : s;
}
const leanTm = t => leanTmP(t, 0); // 項（住人の名前、関数の適用 f a など）
const leanTmA = t => leanTmP(t, 1024);
function leanF(f) { // 論理式を Lean の記法で（¬ は最も強く、∧ 35、∨ 30、→ 25、いずれも右結合。∀・∃ は、ほかの式の中では括弧でくくる）
  const P = f => f.t === "imp" ? (f.r.t === "bot" ? 1000 : 25) : f.t === "or" ? 30 : f.t === "and" ? 35 : f.t === "all" || f.t === "ex" ? -1 : 1000;
  const go = (f, need) => {
    let s; const p = P(f);
    const REL = { "=": "=", "≤": LMODE.leDef ? "≼" : "≤", "<": "<", "∈": "∈", "⊆": "⊆" };
    if (f.t === "atom" && f.n === "≠∅") s = `NonemptySet ${leanTmP(f.args[0], 1024)}`;
    else if (f.t === "atom" && REL[f.n]) s = `${leanTmP(f.args[0], 51)} ${REL[f.n]} ${leanTmP(f.args[1], 51)}`;
    else if (f.t === "atom") s = f.args && f.args.length ? `${f.n} ${f.args.map(leanTmA).join(" ")}` : f.n;
    else if (f.t === "all" || f.t === "ex") { // 同じ量化子が続くときは ∀ x y : α, とまとめる
      const vs = [f.v]; let b = f.b; while (b.t === f.t) { vs.push(b.v); b = b.b; }
      const ty = LMODE.typed ? ` : ${LMODE.nat ? "N" : "α"}` : "";
      s = `${f.t === "all" ? "∀" : "∃"} ${vs.join(" ")}${ty}, ${go(b, -1)}`;
    }
    else if (f.t === "bot") s = "False";
    else if (f.t === "imp" && f.r.t === "bot") s = "¬" + go(f.l, 40);
    else s = `${go(f.l, p + 1)} ${f.t === "imp" ? "→" : f.t === "or" ? "∨" : "∧"} ${go(f.r, p)}`;
    return p < need ? `(${s})` : s;
  };
  return go(f, -1);
}
function leanT(t) { // 前向きに作った項を Lean の項として
  switch (t.k) {
    case "var": return lnName(t.x);
    case "app": return `${leanT(t.f)} ${leanA(t.a)}`;
    case "fst": return `${leanA(t.p)}.1`;
    case "snd": return `${leanA(t.p)}.2`;
    case "pair": return `⟨${leanT(t.a)}, ${leanT(t.b)}⟩`;
    case "inl": return `Or.inl ${leanA(t.p)}`;
    case "inr": return `Or.inr ${leanA(t.p)}`;
    case "abort": return `False.elim ${leanA(t.p)}`;
    case "lam": return `fun ${lnName(t.x)} => ${leanT(t.body)}`;
    case "tapp": return `${leanT(t.f)} ${leanTmA(t.t)}`;
    case "pack": return `⟨${leanTm(t.t)}, ${leanT(t.p)}⟩`;
    default: return "sorry";
  }
}
const leanA = t => t.k === "var" || t.k === "pair" || t.k === "pack" ? leanT(t) : `(${leanT(t)})`;
const supN = x => { const n = +String(x).slice(1); return n ? String(n).replace(/[0-9]/g, d => "⁰¹²³⁴⁵⁶⁷⁸⁹"[+d]) : ""; };
function markFwd(t) { // 前向き推論（鍵から鍵を作る）で作った部分に印を付ける（証明図の注記を have にするため）
  if (!t || !t.k) return;
  if (t.k === "let") { const mk = u => { if (!u || !u.k) return; u.fwd = true; for (const k of TERM_KIDS) mk(u[k]); }; mk(t.def); }
  for (const k of TERM_KIDS) markFwd(t[k]);
}
function leanTac(t, cx) { // [{ code, op, cm, cls, ind }]
  const L = (code, op, cm, cls) => ({ code, op, cm: cm || "", cls: cls || "", ind: 0 });
  const bullets = parts => parts.flatMap(ls => ls.map((l, i) => i === 0 ? { ...l, code: "· " + l.code } : { ...l, ind: l.ind + 1 }));
  switch (t.k) {
    case "hole": return [L("sorry", null, "⋮", t.id === cx.active ? "lact" : "lhole")];
    case "var": return [L(`exact ${lnName(t.x)}`, t.op, RD(__T(824)))];
    case "lam": return [L(`intro ${lnName(t.x)}`, t.op, `→I${supN(t.x)}`), ...leanTac(t.body, cx)];
    case "raa": return [L("apply Classical.byContradiction", t.op, `RAA${supN(t.x)}`), L(`intro ${lnName(t.x)}`, t.op, ""), ...leanTac(t.body, cx)];
    case "pair": return [L("constructor", t.op, "∧I"), ...bullets([leanTac(t.a, cx), leanTac(t.b, cx)])];
    case "inl": return [L("left", t.op, "∨I"), ...leanTac(t.p, cx)];
    case "inr": return [L("right", t.op, "∨I"), ...leanTac(t.p, cx)];
    case "abort": return [L("exfalso", t.op, "⊥E"), ...leanTac(t.p, cx)];
    case "tlam": return [L(`intro ${t.a}`, t.op, "∀I"), ...leanTac(t.body, cx)];
    case "refl": return [L("rfl", t.op, "=I")];
    case "rew": { // 扉の書き換え（=E）：扉 T の R を L に（鍵 a : L = R。逆向きに使ったときは a は対称律の形）
      const rv = leanRew(t.a), T = t.ty, N = t.p && t.p.ty;
      let code = `rewrite [${rv.rev ? "" : "← "}${rv.v}]`;
      if (N && T && !leanAllOcc(T, rv.R, rv.L, N)) code = `refine Eq.subst (motive := fun t₀ => ${leanF(leanMotive(T, N, rv.R, rv.L))}) ${rv.h} (?_ : ${leanF(N)})`;
      return [L(code, t.op, "=E"), ...leanTac(t.p, cx)];
    }
    case "unfold": return [L(`show ${leanF(t.p.ty || t.ty)}`, t.op, RD(__T(785))), ...leanTac(t.p, cx)];
    case "cut": return [L(`have ${lnName(t.x)} : ${leanF(t.xty)} := by`, t.op, RD(__T(792))), ...leanTac(t.a, cx).map(l => ({ ...l, ind: l.ind + 1 })), ...leanTac(t.body, cx)];
    case "ind": return [L(`intro ${t.n}`, t.op, ""), L(`induction ${t.n} with`, t.op, RD(__T(796))), L("| zero =>", t.op, ""), ...leanTac(t.base, cx).map(l => ({ ...l, ind: l.ind + 1 })),
                        L(`| succ ${t.n} ${lnName(t.x)} =>`, t.op, ""), ...leanTac(t.step, cx).map(l => ({ ...l, ind: l.ind + 1 }))];
    case "pack": return [L(`refine ⟨${leanTm(t.t)}, ?_⟩`, t.op, "∃I"), ...leanTac(t.p, cx)];
    case "unpack": return [L(`obtain ⟨${t.b}, ${lnName(t.x)}⟩ := ${leanT(t.p)}`, t.op, `∃E${supN(t.x)}`), ...leanTac(t.body, cx)];
    case "case": return [L(`rcases ${leanT(t.p)} with ${lnName(t.x)} | ${lnName(t.y)}`, t.op, `∨E${supN(t.x)},${supN(t.y).replace(/^/, "")}`), ...bullets([leanTac(t.l, cx), leanTac(t.r, cx)])];
    case "let": {
      const d = t.def, nx = t.body, op = t.op != null ? t.op : d.op;
      if ((d.k === "fst" || d.k === "snd") && nx && nx.k === "let" && nx.def.k === (d.k === "fst" ? "snd" : "fst") && leanT(nx.def.p) === leanT(d.p)) {
        const [a, b] = d.k === "fst" ? [t.x, nx.x] : [nx.x, t.x];
        return [L(`have ⟨${lnName(a)}, ${lnName(b)}⟩ := ${leanT(d.p)}`, op, "∧E"), ...leanTac(nx.body, cx)];
      }
      if (d.k === "rew") { // 鍵の書き換え（=E）：鍵 K の L を R に
        const rv = leanRew(d.a), K = d.p.ty, k = leanT(d.p);
        const code = !K || leanAllOcc(K, rv.L, rv.R, d.ty) ? `have ${lnName(t.x)} : ${leanF(d.ty)} := by rewrite [${rv.rev ? "← " : ""}${rv.v}] at ${k}; exact ${k}`
          : `have ${lnName(t.x)} : ${leanF(d.ty)} := Eq.subst (motive := fun t₀ => ${leanF(leanMotive(K, d.ty, rv.L, rv.R))}) ${rv.h} ${k}`;
        return [L(code, op, "=E"), ...leanTac(t.body, cx)];
      }
      if (d.k === "unfold") return [L(`have ${lnName(t.x)} : ${leanF(d.ty)} := ${leanT(d.p)}`, op, RD(__T(785))), ...leanTac(t.body, cx)];
      return [L(`have ${lnName(t.x)} := ${leanT(d)}`, op, d.k === "app" ? "→E" : d.k === "fst" || d.k === "snd" ? "∧E" : d.k === "tapp" ? "∀E" : ""), ...leanTac(t.body, cx)];
    }
    case "app": { // 鍵を扉に差し込む（後ろ向きの →E）：apply で、残りの前提が新しい扉になる
      const args = []; let h = t; while (h.k === "app") { args.unshift(h.a); h = h.f; }
      return [L(`apply ${leanT(h)}`, t.op, "→E"), ...(args.length === 1 ? leanTac(args[0], cx) : bullets(args.map(a => leanTac(a, cx))))];
    }
  }
  return [L("sorry", null, "")];
}
function leanSig(prob) { // 命題変数・述語・集合・関数・演算・定数（式に自由に現れる住人の名前）と、仮定（入口の鍵と定理カード）
  const props = [], preds = {}, consts = [], sets = [], funcs = [], flag = { fol: false, mul: false, nat: false, le: false, lt: false, typed: false };
  const ctx = S && S.goals && S.goals.g0 ? S.goals.g0.ctx : prob.prem.map((p, i) => ({ name: "h" + (i + 1), f: parse(p) }));
  const hyps = ctx.filter(c => /^[hc][0-9]+$/.test(c.name));
  const tvars = (t, bound) => {
    if (typeof t === "string") { if (t === "0") flag.nat = true; else if (/^[a-z]'?$/.test(t) && !bound.includes(t) && !consts.includes(t)) consts.push(t); return; }
    if (t.f === "*") flag.mul = true; else if (t.f === "+" || t.f === "s") flag.nat = true;
    else if (/^[a-z]'?$/.test(t.f) && !funcs.includes(t.f)) funcs.push(t.f);
    t.args.forEach(a => tvars(a, bound)); };
  const svars = t => { if (typeof t === "string") { if (!sets.includes(t)) sets.push(t); } else t.args.forEach(svars); };
  const add = (f, bound) => { if (!f || typeof f !== "object") return;
    if (f.t === "atom") {
      if (f.n === "∈") { flag.fol = flag.typed = true; tvars(f.args[0], bound); svars(f.args[1]); }
      else if (f.n === "⊆" || f.n === "≠∅") { flag.fol = flag.typed = true; f.args.forEach(svars); }
      else if (["=", "≤", "<"].includes(f.n)) { flag.fol = flag.typed = true; if (f.n === "≤") flag.le = true; if (f.n === "<") flag.lt = true; f.args.forEach(a => tvars(a, bound)); }
      else if (f.args && f.args.length) { (preds[f.args.length] = preds[f.args.length] || []).includes(f.n) || preds[f.args.length].push(f.n); f.args.forEach(a => tvars(a, bound)); flag.fol = true; }
      else if (!props.includes(f.n)) props.push(f.n); }
    else if (f.t === "all" || f.t === "ex") { flag.fol = true; add(f.b, [...bound, f.v]); }
    else { add(f.l, bound); add(f.r, bound); } };
  const goal = parse(prob.goal);
  hyps.forEach(c => add(c.f, [])); add(goal, []);
  if (flag.nat) { const k = funcs.indexOf("s"); if (k >= 0) funcs.splice(k, 1); }
  if (funcs.length || flag.mul || flag.nat) flag.typed = true;
  return { props: props.sort(), preds, consts: consts.sort(), sets: sets.sort(), funcs: funcs.sort(), ...flag, hyps, goal };
}
function leanFresh(rt, sig) { // 証明の中で新しく呼んだ住人（式にも、∀I・∃E の部屋にも出てこない名前）
  const used = [], bound = [];
  const walk = t => { if (!t || !t.k) return;
    if (t.k === "tlam") bound.push(t.a); if (t.k === "unpack") bound.push(t.b); if (t.k === "ind") bound.push(t.n);
    if ((t.k === "tapp" || t.k === "pack") && typeof t.t === "string" && !used.includes(t.t)) used.push(t.t);
    for (const k of TERM_KIDS) walk(t[k]); };
  walk(rt);
  if (sig.nat) return [];
  return used.filter(x => /^[a-z]'?$/.test(x) && !bound.includes(x) && !sig.consts.includes(x));
}
const LEAN_PRE_SET = [__T(941),
  "instance {α : Type} : Membership α (α → Prop) := ⟨fun A x => A x⟩",
  "instance {α : Type} : HasSubset (α → Prop) := ⟨fun A B => ∀ x, x ∈ A → x ∈ B⟩",
  "instance {α : Type} : Inter (α → Prop) := ⟨fun A B x => x ∈ A ∧ x ∈ B⟩",
  "instance {α : Type} : Union (α → Prop) := ⟨fun A B x => x ∈ A ∨ x ∈ B⟩",
  "def compl {α : Type} (A : α → Prop) : α → Prop := fun x => ¬x ∈ A",
  "postfix:max \"ᶜ\" => compl",
  __T(942),
  "def NonemptySet {α : Type} (A : α → Prop) : Prop := ∃ x, x ∈ A", ""];
const LEAN_PRE_NAT = [__T(943),
  "inductive N where",
  "  | zero : N",
  "  | s : N → N",
  "instance : OfNat N 0 := ⟨N.zero⟩",
  "open N (s)",
  __T(944),
  "@[induction_eliminator] theorem N.induction {motive : N → Prop} (zero : motive 0) (succ : ∀ n, motive n → motive (s n)) : ∀ n, motive n",
  "  | .zero => zero",
  "  | .s n => succ n (N.induction zero succ n)"];
const LEAN_PRE_LE = [__T(945),
  "def Le [Add N] (x y : N) : Prop := ∃ z, x + z = y",
  "infix:50 \" ≼ \" => Le"];
function leanMode(sig) { LMODE = { nat: sig.nat, typed: sig.typed, leDef: sig.nat && sig.le }; return LMODE; }
function leanRew(a) { // 等式の鍵：a : L = R。std は鍵 v そのもの、rev は鍵 v : R = L を逆向きに使ったもの
  const eqf = a.ty, L = eqf.args[0], R = eqf.args[1];
  if (a.k === "rew" && a.a) { const v = leanT(a.a); return { L, R, v, rev: true, h: `${leanA(a.a)}.symm` }; }
  const v = leanT(a); return { L, R, v, rev: false, h: leanA(a) };
}
function leanAllOcc(T, from, to, N) { // T の from をすべて to にすると N になるか（rewrite で書けるか）
  const n = countOcc(T, from); return eq(replaceOcc(T, from, to, new Set(Array.from({ length: n }, (_, i) => i))), N);
}
function leanMotive(T, N, from, to) { // 一部だけ書き換えたとき：T と N を比べ、from が to になった場所を t₀ にする
  const tm = (a, b) => termEq(a, b) ? a : termEq(a, from) && termEq(b, to) ? "t₀" : typeof a === "string" || typeof b === "string" ? a : { f: a.f, args: a.args.map((x, i) => tm(x, b.args[i])) };
  const fm = (f, g) => f.t === "atom" ? (f.args && f.args.length ? { ...f, args: f.args.map((x, i) => tm(x, g.args[i])) } : f) : f.t === "bot" ? f
    : f.t === "all" || f.t === "ex" ? { ...f, b: fm(f.b, g.b) } : { ...f, l: fm(f.l, g.l), r: fm(f.r, g.r) };
  return fm(T, N);
}
function leanHead(prob) { // （前置き）example (P Q : Prop) (h₁ : …) : 目標 := by
  const sig = leanSig(prob), { goal } = sig;
  leanMode(sig);
  const ar = n => Array(n).fill("α → ").join("") + "Prop";
  const pre = sig.sets.length ? LEAN_PRE_SET : sig.nat ? [...LEAN_PRE_NAT, ...(LMODE.leDef ? LEAN_PRE_LE : []), ""] : [];
  const binders = [
    sig.fol && !sig.nat ? "(α : Type) [Nonempty α]" : "",
    sig.props.length ? `(${sig.props.join(" ")} : Prop)` : "",
    ...Object.keys(sig.preds).sort().map(n => `(${sig.preds[n].sort().join(" ")} : ${ar(+n)})`),
    sig.sets.length ? `(${sig.sets.join(" ")} : α → Prop)` : "",
    sig.funcs.length && !sig.nat ? `(${sig.funcs.join(" ")} : α → α)` : "",
    sig.nat ? `[Add N]${sig.mul ? " [Mul N]" : ""}` : "",
    sig.mul && !sig.nat ? "[Mul α]" : "", sig.le && !sig.nat ? "[LE α]" : "", sig.lt && !sig.nat ? "[LT α]" : "",
    sig.consts.length ? `(${sig.consts.join(" ")} : ${sig.nat ? "N" : "α"})` : "",
    ...sig.hyps.map(c => `(${lnName(c.name)} : ${leanF(c.f)})`)].filter(Boolean);
  const one = `example ${binders.join(" ")} : ${leanF(goal)} := by`;
  if (one.length <= 44) return [...pre, one];
  return [...pre, `example ${binders[0] || ""}`.trimEnd(), ...binders.slice(1).map(b => "    " + b), `    : ${leanF(goal)} := by`];
}
const LEAN_KW = /\b(example|by|intro|apply|exact|constructor|left|right|rcases|obtain|refine|with|have|exfalso|fun|Prop|Type|False|Nonempty|inferInstance|rfl|rewrite|at|show|induction|zero|succ|Nat|instance|def|infix|postfix|motive|inductive|where|theorem|open|N)\b|Eq\.subst|sorry|Classical\.byContradiction|Or\.inl|Or\.inr|False\.elim/g;
const leanHL = code => code.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;")
  .replace(LEAN_KW, m => `<span class="${m === "sorry" ? "lsorry" : "lkw"}">${m}</span>`)
  .replace(/(^|[^\w₀-₉])([hxdc][₀-₉]+)/g, (m, a, b) => `${a}<span class="lhyp">${b}</span>`);
function leanLines(St, rt) {
  const head = leanHead(PROB);
  const body = leanTac(rt, { active: St.active });
  return { head, body };
}
function leanText(St = S) { // 動作確認用：Lean のコード（プレーンテキスト）
  const rt = rootTerm(St), head = leanHead(PROB), body = leanBody(rt, { active: St.active });
  return [...head, ...body.map(l => "  " + "  ".repeat(l.ind) + l.code)].join("\n");
}
function leanBody(rt, o = {}) { // タクティクの行。新しく呼んだ住人は、最初に「住人は少なくとも一人いる」から取り出す
  const fresh = leanFresh(rt, leanSig(PROB));
  return [...fresh.map(x => ({ code: `obtain ⟨${x}⟩ := (inferInstance : Nonempty α)`, op: null, cm: RD(__T(946)), cls: "", ind: 0 })), ...leanTac(rt, { active: o.active })];
}
function leanCodeHTML(rt, o = {}) { // Lean のコード部分だけ（プレイ画面・クリア画面で共通）
  const head = leanHead(PROB), body = leanBody(rt, o);
  const row = (code, cm, cls) => `<div class="lrow${cls ? " " + cls : ""}"><span class="lcode">${leanHL(code)}</span><span class="lcm">${cm ? "-- " + cm : ""}</span></div>`;
  const ex = head.findIndex(h => h.startsWith("example")), pre = head.slice(0, ex).filter(h => h !== ""), main = head.slice(ex);
  const preHTML = pre.length ? __T(947, [LMODE.nat ? __T(948) : __T(949), pre.length, pre.map(h => row(h, "", "lhead lpre")).join("")]) : "";
  return preHTML + `<div class="lean-code">${main.map(h => row(h, "", "lhead")).join("")}` +
    body.map(l => row("  " + "  ".repeat(l.ind) + l.code, l.cm, [l.cls, o.latest > 0 && l.op === o.latest ? "lnew" : ""].filter(Boolean).join(" "))).join("") + `</div>`;
}
function pruneTerm(t, k) { // 再生用：k 手目より後に作られた部分を sorry（穴）にする
  if (!t || !t.k) return t;
  if (t.k === "let") { const op = t.op != null ? t.op : t.def && t.def.op; return op != null && op > k ? pruneTerm(t.body, k) : { ...t, body: pruneTerm(t.body, k) }; }
  if (t.op != null && t.op > k) return { k: "hole", id: "rp", ty: t.ty };
  const o = { ...t }; for (const c of TERM_KIDS) if (c !== "def" && o[c] && o[c].k) o[c] = pruneTerm(o[c], k);
  return o;
}
function leanClearHTML() { // クリア画面の Lean のコード（Lean モードのとき）
  if (!PREFS.leanMode || !leanOK() || !S) return "";
  let code = "";
  try { code = leanCodeHTML(rootTerm(S), {}); } catch (e) { return ""; }
  return __T(950, [code]);
}
function renderLean(St, rt) {
  const box = $("#leanBox"); if (!box) return;
  box.hidden = !PREFS.leanMode;
  if (!PREFS.leanMode) return;
  if (!leanOK()) { box.innerHTML = __T(951); return; }
  let code;
  try { code = leanCodeHTML(rt, { active: St.active, latest: St.ops }); } catch (e) { box.innerHTML = `<p class="note">${esc(e.message)}</p>`; return; }
  box.innerHTML = __T(952) + code;
}
function leanTag(t) { // 証明図の規則の横に添える、対応するタクティク
  switch (t.k) {
    case "lam": return `intro ${lnName(t.x)}`;
    case "raa": return "byContradiction";
    case "pair": return "constructor";
    case "inl": return "left";
    case "inr": return "right";
    case "case": return `rcases`;
    case "abort": return "exfalso";
    case "app": return t.fwd ? "have" : "apply";
    case "fst": case "snd": return "have ⟨_, _⟩";
    case "tlam": return `intro ${t.a}`;
    case "tapp": return "have";
    case "pack": return `refine ⟨${leanTm(t.t)}, ?_⟩`;
    case "unpack": return `obtain ⟨${t.b}, ${lnName(t.x)}⟩`;
    case "refl": return "rfl";
    case "rew": return "rewrite";
    case "unfold": return "show";
    case "cut": return `have ${lnName(t.x)} : …`;
    case "ind": return "induction";
  }
  return "";
}
// 証明項の表示（「証明項（λ項）を表示」がオンのとき）。再生中に切り取った部分は、項でも ? にする
function cutsOf(n, out = new Set()) { if (n.tmCut) out.add(n.tmCut); (n.kids || []).forEach(c => cutsOf(c, out)); return out; }
const termCX = (tree, base) => PREFS.showTerm ? { ...base, terms: true, cut: cutsOf(tree) } : base;
// 仮定 xₙ（部屋 n）の色クラス
const scls = n => n ? "s" + (((n - 1) % 4) + 1) : "s0";
const asmNum = name => +name.slice(1);
const STATIC_CX = { holes: {}, active: null, latest: 0, holeOp: {} };
// 前向き推論で作った鍵（let）の定義を集める
function collectDefs(S) {
  const defs = {};
  for (const f of Object.values(S.fills)) { let t = f; while (t && t.k === "let") { defs[t.x] = t.def; t = t.body; } }
  return defs;
}
function varsOf(t, out = new Set()) {
  if (!t) return out;
  if (t.k === "var") out.add(t.x);
  for (const k of TERM_KIDS) if (t[k] && t[k].k) varsOf(t[k], out);
  return out;
}
function resolve(t, defs) {
  switch (t.k) {
    case "var": return defs[t.x] ? resolve(defs[t.x], defs) : t;
    case "app": return { ...t, f: resolve(t.f, defs), a: resolve(t.a, defs) };
    case "fst": case "snd": return { ...t, p: resolve(t.p, defs) };
    case "tapp": return { ...t, f: resolve(t.f, defs) };
    case "rew": return { ...t, a: resolve(t.a, defs), p: resolve(t.p, defs) };
    case "unfold": return { ...t, p: resolve(t.p, defs) };
    case "cut": return t;
    default: return t;
  }
}
// 現在の扉で使える「部品」：前向きに組み立てた証明図の断片（他の部品の材料になっているものは除く）
function partTrees(g, St = S) {
  const defs = collectDefs(St), ders = g.ctx.filter(c => c.kind === "der" && defs[c.name]);
  const inner = new Set();
  for (const c of ders) for (const v of varsOf(defs[c.name])) inner.add(v);
  return ders.filter(c => !inner.has(c.name)).map(c => ({ name: c.name, f: c.f, tree: buildPT(resolve(defs[c.name], defs)) }));
}

/* ================= 進行状況の保存 ================= */
const PKEY = "proof-dungeon:p1";
function loadProgress() { try { const p = JSON.parse(localStorage.getItem(PKEY)); return p && p.best ? p : { best: {} }; } catch (e) { return { best: {} }; } }
function saveProgress() { try { localStorage.setItem(PKEY, JSON.stringify(PROG)); } catch (e) { /* 保存できない環境では無視 */ } }
let PROG = loadProgress();
const PREF_KEY = "proof-dungeon:prefs";
const PREF_DEFAULTS = { story: true, theme: "auto", mazeMode: true, mazeBars: true, mazeDeco: true, evMode: "graph", replayAuto: false, showTerm: false, manualNames: false, mapView: true, leanMode: false, unlockAll: false }; // 初期設定
let PREFS = (() => { try { return Object.assign({ ...PREF_DEFAULTS }, JSON.parse(localStorage.getItem(PREF_KEY)) || {}); } catch (e) { return { ...PREF_DEFAULTS }; } })();
PREFS.kSym = false; // 「記号で見る」は廃止（標準の記法との対応は、読み方の欄に書く）
PREFS.mapView = true; // 全体地図はいつもオン（部屋だけの表示は廃止）
function savePrefs() { try { localStorage.setItem(PREF_KEY, JSON.stringify(PREFS)); } catch (e) { /* 保存できない環境では無視 */ } }

/* ================= UI ================= */
const $ = s => document.querySelector(s);
const app = $("#app"), tools = $("#tools"), toastEl = $("#toast");
let SCREEN = "select", STAGE = null, S = null, HIST = [];
let PROB = null, PROBF = null, PROB_ATOMS = [], R = null, HISTR = []; // いま取り組んでいる問題、クリプキモデルとその履歴
let UI = freshUI();
function freshUI() { return { sel: null, can: new Set(), fresh: new Set(), fx: false, hints: 0, scope: null, hoverScope: null, autoScope: false, orChoice: null, pick: null, rew: null, lemma: null, flagName: null, flow: null, mapExp: new Set(), lastActive: null, previewKey: null, just: false, lanternLeft: 3, lit: new Map(), mode: "prove", judge: null }; }

const ICON = {
  map: `<svg viewBox="0 0 24 24" aria-hidden="true"><rect x="3.5" y="3.5" width="7" height="7" rx="1"/><rect x="13.5" y="3.5" width="7" height="7" rx="1"/><rect x="3.5" y="13.5" width="7" height="7" rx="1"/><rect x="13.5" y="13.5" width="7" height="7" rx="1"/></svg>`,
  undo: `<svg viewBox="0 0 24 24" aria-hidden="true"><path d="M9 6 4 11l5 5"/><path d="M4 11h10a5.5 5.5 0 0 1 0 11h-2"/></svg>`,
  reset: `<svg viewBox="0 0 24 24" aria-hidden="true"><path d="M4 12a8 8 0 1 0 2.4-5.7"/><path d="M4 4v4.5h4.5"/></svg>`,
  help: `<svg viewBox="0 0 24 24" aria-hidden="true"><circle cx="12" cy="12" r="9"/><path d="M9.6 9.4a2.5 2.5 0 1 1 3.4 2.4c-.7.3-1 .8-1 1.5v.6"/><path d="M12 17.2v.1"/></svg>`,
  person: `<svg class="ico" viewBox="0 0 24 24" aria-hidden="true"><circle cx="12" cy="8" r="3.5"/><path d="M5 20c.8-3.6 3.6-5.5 7-5.5s6.2 1.9 7 5.5"/></svg>`,
  play: `<svg viewBox="0 0 24 24" aria-hidden="true"><circle cx="12" cy="12" r="9"/><path d="M10 8.6v6.8l5.4-3.4z"/></svg>`,
  ladder: `<svg class="ico" viewBox="0 0 24 24" aria-hidden="true"><path d="M7 3v18M17 3v18M7 7h10M7 12h10M7 17h10"/></svg>`,
  anvil: `<svg class="ico" viewBox="0 0 24 24" aria-hidden="true"><path d="M3 8h13a4 4 0 0 0 4-4h1v4a4 4 0 0 1-4 4h-2v3l2 3H7l2-3v-3H6A3 3 0 0 1 3 9z"/></svg>`,
  magic: `<svg class="ico" viewBox="0 0 24 24" aria-hidden="true"><path d="M5 19 15 9"/><path d="M15 5v2M19 9h-2M17.8 6.2l-1.4 1.4M12 3l.6 1.4L14 5l-1.4.6L12 7l-.6-1.4L10 5l1.4-.6zM19 13l.5 1 1 .5-1 .5-.5 1-.5-1-1-.5 1-.5z"/></svg>`,
  lantern: `<svg class="ico" viewBox="0 0 24 24" aria-hidden="true"><path d="M9 4h6M12 2v2M8 7h8l1 3v8l-1 2H8l-1-2v-8z"/><path d="M12 11.5c1 1.2 1.4 2.2 0 3.6-1.4-1.4-1-2.4 0-3.6z"/></svg>`,
  swing: `<svg class="door-swing" viewBox="0 0 40 40" aria-hidden="true"><path d="M2 38V2" stroke="currentColor" stroke-width="3" fill="none"/><path d="M2 2A36 36 0 0 1 38 38" stroke="currentColor" stroke-width="1.2" stroke-dasharray="3 3" fill="none"/><path d="M2 38H38" stroke="currentColor" stroke-width="1.2" fill="none"/></svg>`,
};

const GUIDE_HTML = __T(953, [WN("9-1"), WN("10-5"), WN("r-conv"), WN("5-1"), WN("13-2"), WN("x-rid"), WN("12-2"), WN("10-1"), WN("10-5"), WN("15-1"), WN("9-1"), WN("7-1"), WN("7-3"), WN("6-1"), F("A"), F("A->B"), F("B"), F("A->B"), F("B"), F("A")]);

let toastTimer = 0;
function toast(html, kind) {
  toastEl.innerHTML = html;
  toastEl.className = "toast show" + (kind === "bad" ? " bad" : "");
  clearTimeout(toastTimer);
  toastTimer = setTimeout(() => { toastEl.className = "toast" + (kind === "bad" ? " bad" : ""); }, 3200);
}
function showModal(html, dismissable) {
  closeModal();
  const o = document.createElement("div");
  o.className = "overlay";
  if (dismissable) o.dataset.dismiss = "1";
  o.innerHTML = `<div class="modal" role="dialog" aria-modal="true">${html}</div>`;
  document.body.appendChild(o);
  o.addEventListener("click", e => { if (e.target === o && o.dataset.dismiss) closeModal(); });
  afterClearModal(o);
  const b = o.querySelector(".actions .primary") || o.querySelector("button");
  if (b) b.focus({ preventScroll: true });
}
function afterClearModal(o) {
  if (SCREEN !== "play" || !STAGE || !o.querySelector('[data-cmd="next"], [data-cmd="retry"]')) return; // クリア画面のときだけ
  if (PROG.best[STAGE.pid] == null) return;
  if (bossOf(STAGE.world) === STAGE && !UI.wasCleared) { // ボスの初回クリア：次の層へ進む前に、ステージ一覧で新しく開いた層を見せる
    const nx = o.querySelector('.actions [data-cmd="next"]');
    if (nx) { o.querySelectorAll('.actions [data-cmd="map"]').forEach(b => b.remove()); nx.dataset.cmd = "map"; nx.classList.add("primary"); nx.textContent = L1(__T(954), "To the stage list"); }
    const act = o.querySelector(".actions"); if (nx && act && !o.querySelector(".boss-open")) act.insertAdjacentHTML("beforebegin", `<p class="boss-open">${L1(__T(955), "You defeated the boss. Check the newly opened way in the stage list.")}</p>`);
  }
  if (STAGE.sfFlicker) sfBlip(); // 隠し層 2 のボス：一瞬だけ、未来の色がのぞく
}
function sfBlip() { // 画面全体を光らせず、画面の一部に青紫の光の筋が何本か走る（未来の色が一瞬のぞく）
  if (window.matchMedia && matchMedia("(prefers-reduced-motion: reduce)").matches) return;
  const old = document.getElementById("sfStreaks"); if (old) old.remove();
  const d = document.createElement("div"); d.id = "sfStreaks"; d.setAttribute("aria-hidden", "true");
  const lines = [[14, 46, 0.15, 1.05], [21, 30, 0.32, 0.95], [29, 58, 0.05, 1.25], [36, 26, 0.48, 0.9], [44, 40, 0.24, 1.1]]; // 上からの位置（vh）、長さ（vw）、遅れ、長さ（秒）
  d.innerHTML = lines.map(([y, w, dl, du]) => `<i style="top:${y}vh;width:${w}vw;animation-delay:${dl}s;animation-duration:${du}s"></i>`).join("");
  document.body.appendChild(d);
  setTimeout(() => d.remove(), 2200);
}
function closeModal() { TUT_RUN++; rpStop(); helpStop(); if (GUIDE && GUIDE.keys.includes("clear")) guideEnd(true); document.querySelectorAll(".overlay").forEach(o => o.remove()); }

function renderTools() {
  document.body.classList.toggle("mapmode", SCREEN === "play" && !!PREFS.mapView);
  const tutNew = SCREEN === "play" && STAGE && (STAGE.tut || []).some(k => !(PROG.seenTut || {})[k]);
  const tutBtn = __T(956, [ICON.play, tutNew ? '<span class="new-badge">New</span>' : ""]);
  const th = THEME_LABEL[PREFS.theme] ? PREFS.theme : "auto";
  const themeBtn = __T(957, [THEME_LABEL[th], THEME_LABEL[th], THEME_ICON[th], THEME_LABEL[th]]);
  const langBtn = `<button class="btn lang-btn" type="button" data-cmd="lang" title="${LANG === "zh-CN" ? "切换至日语" : LANG === "ja" ? "英語に切り替える" : "Switch to Simplified Chinese"}" aria-label="${LANG === "zh-CN" ? "当前语言：简体中文" : LANG === "ja" ? "現在の言語：日本語" : "Current language: English"}"><span class="lbl-always">${LANG === "zh-CN" ? "简中" : LANG === "ja" ? "日本語" : "EN"}</span></button>`;
  tools.innerHTML = langBtn + themeBtn + tutBtn + (SCREEN === "play"
    ? __T(960, [ICON.map]) +
      (PROB ? __T(961, [ICON.undo, ICON.reset]) : "") +
      __T(962, [ICON.help, PROG.helpSeen ? "" : '<span class="new-badge">New</span>'])
    : __T(963, [ICON.help, PROG.helpSeen ? "" : '<span class="new-badge">New</span>']));
}
function updateUndo() { const ub = $("#undoBtn"); if (ub) ub.disabled = UI.mode === "refute" ? !HISTR.length : !HIST.length; }

const seqHTML = (st, turn = "⊢") => `${st.prem.map(p => F(p)).join('<span class="comma">,</span>')}<span class="seq-goal"><span class="turn">${turn}</span>${F(st.goal)}</span>`;
const unitOf = st => st.kind === "refute" ? __T(964) : __T(965);
function bestText(st) {
  const b = PROG.best[st.pid];
  if (b == null) return __T(966);
  if (st.kind === "judge") return __T(967);
  if (st.kind === "tower") return __T(968);
  if (st.kind === "refute" && (st.fol || st.classical)) return __T(969);
  return __T(970, [b, unitOf(st), st.par != null && b <= st.par ? __T(971) : ""]);
}
function tileSeq(s) {
  if (s.kind === "tower") return __T(972, [seqHTML(s, "⊬")]);
  if (s.kind === "judge" && s.indep) return __T(973, [F(s.parts[0].goal)]);
  if (s.kind === "judge") return __T(974, [s.parts.map(p => p.key).join(__T(765))]);
  return withNeg(!s.expandNeg, () => seqHTML(s, s.kind === "refute" ? "⊬" : "⊢"));
}

/* --- ステージ一覧 --- */
// 表示の明るさ：自動（表示している環境の設定に従う）／ライト／ダーク。
// 環境（Claude の画面など）が data-theme を付けることがあるので、その値を覚えておき、「自動」ではそれに戻す
const HOST_THEME = { v: document.documentElement.getAttribute("data-theme"), setting: false };
new MutationObserver(() => {
  if (HOST_THEME.setting) return;
  HOST_THEME.v = document.documentElement.getAttribute("data-theme");
  if (PREFS.theme === "light" || PREFS.theme === "dark") applyColorTheme();
}).observe(document.documentElement, { attributes: true, attributeFilter: ["data-theme"] });
function applyColorTheme() {
  const el = document.documentElement, want = PREFS.theme === "light" || PREFS.theme === "dark" ? PREFS.theme : HOST_THEME.v;
  HOST_THEME.setting = true;
  if (want) el.setAttribute("data-theme", want); else el.removeAttribute("data-theme");
  Promise.resolve().then(() => { HOST_THEME.setting = false; });
}
const THEME_LABEL = { auto: __T(975), light: __T(976), dark: __T(977) }, THEME_ICON = { auto: "◐", light: "☀", dark: "☾" };
function applyTheme() { // 迷宮モードと、お試しの装飾（鉄格子、プレイ画面の飾り）
  applyColorTheme();
  document.body.classList.add("maze", "maze-bars", "maze-deco"); // 迷宮の装飾（鉄格子・プレイ画面の飾りを含む）は常に ON
}

/* ================= ストーリーモード（お試し：World 1〜4） =================
   落ち着いたファンタジー調の、GM（ゲームマスター）の語り。規則の説明は別枠に残す。キーは元のステージ番号 */
const STORY = {
  worlds: {
    "tr-1": __T(978),
    "core-1": __T(979),
    "1-1": __T(980),
    "2-1": __T(981),
    "3-1": __T(982),
    "6-1": __T(983),
    "r-conv": __T(984),
    "5-1": __T(985),
    "7-1": __T(986),
    "7-3": __T(987),
    "f-barber": __T(988),
    "s-ex": __T(989),
    "9-1": __T(990),
    "10-5": __T(991),
    "9-5": __T(992),
    "11-1": __T(993),
    "12-1": __T(994),
    "13-2": __T(995),
    "14-1": __T(996),
    "15-1": __T(997),
    "x-total": __T(998),
    "4-1": __T(999),
  },
  stages: {
    "tr-1": { t: __T(1000, [F("P|~P"), F("~~(P|~P)")]), d: __T(1001) },
    "tr-2": { t: __T(1002, [F("~~P->P"), F("~~(~~P->P)")]), d: __T(1003) },
    "tr-3": { t: __T(1004, [F("(P->Q)|(Q->P)")]), d: __T(1005) },
    "tr-4": { t: __T(1006, [F("!x.(P(x)|~P(x))")]), d: __T(1007) },
    "tr-5": { t: __T(1008, [F("~~!x.~~(P(x)|~P(x))")]), d: __T(1009) },
    "core-1": { t: __T(1010), d: __T(1011) },
    "core-2": { t: __T(1012), d: __T(1013) },
    "core-3": { t: __T(1014), d: __T(1015) },
    "core-4": { t: __T(1016, [F("!x.!y.(x * y = y * x)")]), d: __T(1017) },
    "core-5": { t: __T(1018, [F("!x.(0 + x = x)")]), d: __T(1019) },
    "1-1": { t: __T(1020, [F("P"), F("Q"), F("P&Q"), F("P"), F("Q"), F("P"), F("Q")]),
             d: __T(1021, [F("P"), F("Q")]) },
    "1-2": { t: __T(1022, [F("P&Q"), F("Q&P")]),
             d: __T(1023) },
    "1-3": { t: __T(1024, [F("P->(P&Q)"), F("P"), F("P&Q"), F("Q"), F("P")]),
             d: __T(1025, [F("P"), F("Q"), F("P")]) },
    "1-4": { t: __T(1026, [F("(P&(Q&R))->((P&Q)&R)")]),
             d: __T(1027) },
    "2-1": { t: __T(1028, [F("P->Q"), F("P"), F("Q")]),
             d: __T(1029, [F("P"), F("Q")]) },
    "2-2": { t: __T(1030, [F("P->((P->Q)->Q)")]),
             d: __T(1031) },
    "2-3": { t: __T(1032),
             d: __T(1033) },
    "2-4": { t: __T(1034, [F("P->Q"), F("Q->R"), F("P->R"), F("R"), F("R")]),
             d: __T(1035, [F("P"), F("Q"), F("Q"), F("R"), F("P"), F("R")]) },
    "2-5": { t: __T(1036, [F("R"), F("Q"), F("(P->Q)->R")]),
             d: __T(1037, [F("Q"), F("P->Q")]) },
    "3-1": { t: __T(1038, [F("P|Q"), F("P"), F("Q"), F("P")]),
             d: __T(1039, [F("P")]) },
    "3-2": { t: __T(1040, [F("P|Q"), F("P"), F("Q"), F("P"), F("Q")]),
             d: __T(1041) },
    "3-3": { t: __T(1042, [F("R"), F("P->R"), F("Q->R"), F("P"), F("Q")]),
             d: __T(1043, [F("P"), F("P->R"), F("Q"), F("Q->R")]) },
    "3-4": { t: __T(1044),
             d: __T(1045) },
    "3-5": { t: __T(1046, [F("P"), F("Q"), F("R"), F("P"), F("Q"), F("P"), F("R")]),
             d: __T(1047) },
    "4-1": { t: __T(1048, [F("Q"), F("Q"), F("P"), F("P->#"), F("P")]),
             d: __T(1049, [F("Q")]) },
    "4-2": { t: __T(1050, [F("P->~~P"), F("~~P"), F("~P")]),
             d: __T(1051, [F("P"), F("~P")]) },
    "4-3": { t: __T(1052, [F("P->Q"), F("~Q->~P"), F("Q"), F("P"), F("~Q"), F("P")]),
             d: __T(1053, [F("P"), F("Q"), F("~Q")]) },
    "4-4": { t: __T(1054, [F("P|Q"), F("~P"), F("P"), F("~P")]),
             d: __T(1055, [F("P"), F("Q"), F("Q")]) },
    "4-5": { t: __T(1056, [F("P"), F("P"), F("~~(P|~P)")]),
             d: __T(1057) },
    "6-1": { t: __T(1058, [F("~~P->P"), F("P"), F("P")]),
             d: __T(1059, [F("P"), F("~~P"), F("P")]) },
    "6-2": { t: __T(1060, [F("P|~P"), F("P"), F("P")]),
             d: __T(1061) },
    "c-imp": { t: __T(1062, [F("P->Q"), F("~P|Q"), F("P"), F("Q"), F("P"), F("Q")]),
             d: __T(1063) },
    "c-contra": { t: __T(1064, [F("~Q->~P"), F("P->Q"), F("P"), F("Q")]),
             d: __T(1065, [F("Q"), F("~Q->~P"), F("~P"), F("P")]) },
    "6-3": { t: __T(1066, [F("P|~P"), F("~~P"), F("P")]),
             d: __T(1067, [F("P"), F("~P"), F("~~P")]) },
    "6-4": { t: __T(1068, [F("~~(P|~P)->(P|~P)"), F("~~(P|~P)")]),
             d: __T(1069) },
    "6-5": { t: __T(1070, [F("~P|~Q"), F("~(P&Q)"), F("P"), F("Q")]),
             d: __T(1071, [F("P"), F("Q"), F("~(P&Q)")]) },
    "r-conv": { t: __T(1072, [F("Q->P"), F("P->Q"), F("P"), F("Q"), F("P"), F("Q")]),
                d: __T(1073, [F("P"), F("Q")]) },
    "r-inv": { t: __T(1074, [F("~P->~Q"), F("P"), F("Q"), F("~Q->~P")]),
               d: __T(1075, [F("P"), F("Q"), F("~P"), F("~Q")]) },
    "r-ior": { t: __T(1076, [F("P|Q"), F("~(P&Q)")]),
               d: __T(1077) },
    "r-dm": { t: __T(1078, [F("~(P&Q)"), F("~P&~Q")]),
              d: __T(1079) },
    "6-6": { t: __T(1080),
             d: __T(1081) },
    "5-1": { t: __T(1082, [F("P|~P"), F("P"), F("~P"), F("P")]),
             d: __T(1083, [F("P"), F("P"), F("~P")]) },
    "5-2": { t: __T(1084, [F("~~P->P"), F("P"), F("P")]),
             d: __T(1085, [F("~~P"), F("P")]) },
    "5-3": { t: __T(1086, [F("((P->Q)->P)->P")]),
             d: __T(1087, [F("P"), F("P"), F("Q")]) },
    "5-4": { t: __T(1088, [F("~(P&Q)"), F("~P|~Q"), F("P"), F("Q")]),
             d: __T(1089, [F("P"), F("Q"), F("~P"), F("~Q")]) },
    "5-5": { t: __T(1090),
             d: __T(1091) },
    "7-1": { t: __T(1092, [F("!x.P(x)"), F("P"), F("!x.(P(x)&Q(x))"), F("P"), F("Q"), termH("a"), termH("a")]),
             d: __T(1093, [termH("a"), F("P(a)")]) },
    "f-rename": { t: __T(1094, [F("(!x.P(x))->(!y.P(y))"), termH("x"), termH("y"), termH("x"), termH("y")]),
                  d: __T(1095, [termH("x"), termH("y")]) },
    "7-2": { t: __T(1096, [F("P"), F("Q"), F("P"), F("!x.Q(x)"), termH("a")]),
             d: __T(1097, [termH("a"), F("P"), F("P"), F("Q")]) },
    "f-barbara": { t: __T(1098, [F("P"), F("Q"), F("Q"), F("R"), F("P"), F("R"), termH("a")]),
                   d: __T(1099, [termH("a"), F("P"), F("Q"), F("Q"), F("R")]) },
    "f-alll": { t: __T(1100, [F("!z.(A->B(z))"), F("A"), F("A->!x.B(x)")]),
                d: __T(1101, [F("A"), termH("a"), termH("a"), F("A->B(a)"), F("A")]) },
    "f-allr": { t: __T(1102, [F("A->!x.B(x)"), F("!z.(A->B(z))"), termH("a"), F("A"), F("A"), F("!x.B(x)")]),
                d: __T(1103, [F("A"), F("!x.B(x)"), termH("a"), F("A")]) },
    "f-dist": { t: __T(1104, [F("P"), F("Q"), F("P"), F("Q")]),
                d: __T(1105) },
    "7-3": { t: __T(1106, [F("?x.P(x)"), F("P"), F("?x.(P(x)&Q(x))"), F("P"), F("Q")]),
             d: __T(1107, [termH("a")]) },
    "f-wit": { t: __T(1108, [termH("a"), termH("b"), F("P"), F("?x.P(x)"), termH("a"), termH("b"), F("P"), termH("a"), termH("b")]),
               d: __T(1109, [termH("a")]) },
    "f-ae1": { t: __T(1110, [F("A&?x.B(x)"), F("?x.(A&B(x))"), F("A"), F("B")]),
               d: __T(1111, [termH("a"), F("B"), F("A"), termH("a")]) },
    "f-ae2": { t: __T(1112, [F("?x.(A&B(x))"), F("A&?x.B(x)"), termH("a"), F("A"), F("B")]),
               d: __T(1113, [termH("a"), F("A"), F("B(a)"), F("A"), F("A"), termH("a"), F("?x.B(x)")]) },
    "f-ex1": { t: __T(1114, [F("!z.(A(z)->B)"), F("A"), F("B"), F("B"), F("(?x.A(x))->B"), F("A")]),
               d: __T(1115, [F("A"), termH("a"), F("B"), F("B")]) },
    "f-ex2": { t: __T(1116, [F("(?x.A(x))->B"), F("!z.(A(z)->B)"), termH("a"), termH("a"), F("A"), termH("a"), F("A")]),
               d: __T(1117, [termH("a"), F("?x.A(x)"), F("B")]) },
    "7-4": { t: __T(1118, [F("~?x.P(x)"), F("P"), F("!x.~P(x)"), F("P"), termH("a"), F("P")]),
             d: __T(1119, [termH("a"), F("P"), termH("a"), F("?x.P(x)"), F("P")]) },
    "7-5": { t: __T(1120, [F("!x.?y.R(x,y)"), F("?y.!x.R(x,y)"), termH("y"), F("R"), F("R")]),
             d: __T(1121) },
    "f-mouse": { t: __T(1122, [F("M(x)"), termH("x"), F("C(x)"), termH("x"), F("F(x,y)"), termH("x"), termH("y")]),
                 d: __T(1123) },
    "f-barber": { t: __T(1124, [termH("p"), termH("p"), termH("p"), F("K(p,p)"), termH("p")]),
                  d: __T(1125, [termH("p"), termH("p"), termH("p")]) },
    "f-nen": { t: __T(1126, [F("~?x.~P(x)"), F("P"), F("!x.P(x)"), termH("a"), termH("a"), F("P"), termH("a"), F("P"), termH("a")]),
               d: __T(1127, [F("P"), termH("a"), F("P")]) },
    "8-1": { t: __T(1128, [F("?x.~P(x)"), F("P"), F("~!x.P(x)"), F("P"), F("P")]),
             d: __T(1129, [F("P"), F("P")]) },
    "f-nan": { t: __T(1130, [F("~!x.~P(x)"), F("P"), F("?x.P(x)"), F("P")]),
               d: __T(1131, [F("P"), F("P")]) },
    "f-const": { t: __T(1132, [F("!x.(P(x)|Q)"), F("P"), F("Q"), F("Q"), F("(!x.P(x))|Q"), F("Q")]),
                 d: __T(1133, [F("Q"), F("P"), F("Q")]) },
    "8-2": { t: __T(1134, [F("?x.(P(x)->!y.P(y))")]),
             d: __T(1135) },
    "s-ex": { t: __T(1136, [F("P"), F("P"), F("P")]),
              d: __T(1137, [F("P"), F("P")]) },
    "s-pos": { t: __T(1138, [F("?x.!y.R(x,y)"), F("!x.?y.R(x,y)"), F("R")]),
               d: __T(1139, [F("R"), F("R")]) },
    "s-mouse": { t: __T(1140),
                 d: __T(1141) },
    "s-nomouse": { t: __T(1142),
                   d: __T(1143) },
    "8-3": { t: __T(1144),
             d: __T(1145) },
    "9-1": { t: __T(1146, [F("!x.!y.(x = y -> y = x)"), termH("x"), termH("y"), termH("y"), termH("x")]),
             d: __T(1147) },
    "9-2": { t: __T(1148, [F("!x.!y.!z.(x = y -> (y = z -> x = z))"), F("x = y"), F("y = z")]),
             d: __T(1149) },
    "9-3": { t: __T(1150, [termH("f"), termH("x"), termH({ f: "f", args: ["x"] }), F("!x.!y.(x = y -> f(x) = f(y))")]),
             d: __T(1151, [termH({ f: "f", args: ["x"] })]) },
    "9-4": { t: __T(1152, [F("a = b"), F("c = b"), F("a = c"), F("c = b"), termH("c")]),
             d: __T(1153, [F("c = b"), F("b = c")]) },
    "9-5": { t: __T(1154, [termH("e"), termH("e'"), F("e = e'"), termH("e"), termH("e'"), termH({ f: "*", args: ["e", "e'"] })]),
             d: __T(1155, [termH({ f: "*", args: ["e", "e'"] }), termH("e"), termH("e'"), termH("e'"), termH("e")]) },
    "10-5": { t: __T(1156, [F("A ∩ B ⊆ A"), termH("A"), termH("B"), termH("A"), termH({ f: "∩", args: ["A", "B"] }), termH("A")]),
              d: __T(1157) },
    "x-union": { t: __T(1158, [F("A ⊆ A ∪ B"), termH({ f: "∪", args: ["A", "B"] }), termH("A"), termH("B"), termH("A")]),
                 d: __T(1159) },
    "x-swap": { t: __T(1160, [F("A ∩ B ⊆ B ∩ A")]),
                d: __T(1161) },
    "10-6": { t: __T(1162, [termH("A"), termH("B"), termH("B"), termH("C"), F("A ⊆ C"), termH("A"), termH("C")]),
              d: __T(1163, [termH("A"), F("A ⊆ B"), F("B ⊆ C"), termH("C")]) },
    "x-mono": { t: __T(1164, [F("A ⊆ B"), F("A ∩ C ⊆ B ∩ C"), termH("A"), termH("B"), termH("C")]),
                d: __T(1165, [F("A ⊆ B"), termH("C")]) },
    "10-8": { t: __T(1166, [F("x ∈ Aᶜ"), termH("x"), termH("A"), F("(A ∪ B)ᶜ ⊆ Aᶜ ∩ Bᶜ"), termH({ f: "∪", args: ["A", "B"] }), termH("A"), termH("B")]),
              d: __T(1167) },
    "x-dmc": { t: __T(1168, [termH("A"), termH("B"), termH("A"), termH("B"), F("(A ∩ B)ᶜ ⊆ Aᶜ ∪ Bᶜ")]),
               d: __T(1169) },
    "x-darii": { t: __T(1170, [F("M ⊆ P"), F("S ∩ M ≠ ∅"), termH("S"), termH("M"), F("S ∩ P ≠ ∅")]),
                 d: __T(1171, [termH("S"), termH("M"), termH("P")]) },
    "x-bq1": { t: __T(1172, [F("!x∈A.~P(x)"), termH("A"), F("~?x∈A.P(x)"), termH("A"), F("P")]),
               d: __T(1173) },
    "x-bq2": { t: __T(1174, [F("~!x∈A.P(x)"), termH("A"), F("P"), F("?x∈A.~P(x)"), F("P")]),
               d: __T(1175, [termH("A"), F("P")]) },
    "x-sq1": { t: __T(1176, [F("~(A ⊆ B)"), termH("A"), termH("B"), termH("B"), termH("A")]),
               d: __T(1177, [termH("A"), termH("B")]) },
    "x-sq2": { t: __T(1178, [termH("B"), termH("A"), F("~(A ⊆ B)")]),
               d: __T(1179, [termH("B"), termH("A")]) },
    "10-1": { t: __T(1180, [F("x <= y"), F("y <= x"), F("x = y"), termH("m"), termH("n"), F("m = n")]),
              d: __T(1181, [F("m <= n"), F("n <= m"), F("m = n")]) },
    "10-2": { t: __T(1182, [F("x < y"), F("y < z"), F("x < z"), F("x < y"), F("y < x"), F("x < y"), F("y < x"), F("x < x")]),
              d: __T(1183, [F("x < y"), F("y < x"), F("x < x")]) },
    "10-3": { t: __T(1184, [termH("f"), termH("g"), termH({ f: "g", args: [{ f: "f", args: ["x"] }] }), termH({ f: "f", args: ["a"] })]),
              d: __T(1185, [termH("g"), termH({ f: "f", args: ["a"] }), termH({ f: "f", args: ["b"] }), termH("f"), termH("a"), termH("b")]) },
    "x-injeq": { t: __T(1186, [F("!x.!y.(f(x) = f(y) -> x = y)"), termH("f"), termH("f")]),
                 d: __T(1187) },
    "10-4": { t: __T(1188, [termH("f"), termH("g"), termH({ f: "g", args: [{ f: "f", args: ["x"] }] }), termH("g"), termH("f")]),
              d: __T(1189) },
    "10-7": { t: __T(1190, [termH("x"), termH("y"), termH("z"), F("x * y = x * z"), F("y = z")]),
              d: __T(1191, [termH("a"), termH("b"), termH("c"), termH("a")]) },
    "11-1": { t: __T(1192, [F("P"), F("Q"), F("Q"), F("S"), F("S"), F("T"), F("T"), F("R"), termH("a"), termH("b"), termH("c"), F("P"), F("R(a) & (R(b) & R(c))"), F("P"), F("R")]),
              d: __T(1193, [F("!x.(P(x) -> R(x))"), termH("a"), termH("b"), termH("c")]) },
    "11-2": { t: __T(1194, [termH("a"), termH("b"), termH("c"), F("!x.!y.!z.(x * y = x * z -> y = z)")]),
              d: __T(1195) },
    "11-3": { t: __T(1196, [termH("e"), F("!x.(x * e = x)")]),
              d: __T(1197, [termH("x"), termH("e")]) },
    "12-1": { t: __T(1198, [F("s(0) + s(0) = s(s(0))")]),
              d: __T(1199, [termH({ f: "+", args: [{ f: "s", args: ["0"] }, { f: "s", args: ["0"] }] }), termH({ f: "s", args: [{ f: "+", args: [{ f: "s", args: ["0"] }, "0"] }] }), termH({ f: "s", args: [{ f: "s", args: ["0"] }] })]) },
    "12-2": { t: __T(1200, [F("!x.(0 + x = x)"), F("x + 0 = x"), F("0 + x = x")]),
              d: __T(1201, [termH("a"), termH({ f: "s", args: ["a"] }), F("0 + x = x")]) },
    "12-3": { t: __T(1202, [F("!x.!y.(s(x) + y = s(x + y))"), termH("s"), termH("s"), termH("x"), termH("a"), termH("y")]),
              d: __T(1203, [termH("s")]) },
    "12-4": { t: __T(1204, [termH({ f: "+", args: ["x", "y"] }), termH({ f: "+", args: ["y", "x"] }), termH("y")]),
              d: __T(1205) },
    "13-1": { t: __T(1206, [F("!x.(x * s(0) = x)"), termH({ f: "+", args: [{ f: "*", args: ["x", "0"] }, "x"] }), termH({ f: "+", args: ["0", "x"] })]),
              d: __T(1207, [termH({ f: "*", args: ["x", { f: "s", args: ["0"] }] }), termH({ f: "+", args: [{ f: "*", args: ["x", "0"] }, "x"] }), termH({ f: "+", args: ["0", "x"] }), termH("x")]) },
    "13-2": { t: __T(1208, [F("!x.(0 * x = 0)"), F("x * 0 = 0")]),
              d: __T(1209) },
    "13-3": { t: __T(1210, [F("!x.!y.!z.((x + y) + z = x + (y + z))"), termH("z")]),
              d: __T(1211, [termH("s")]) },
    "13-4": { t: __T(1212, [termH({ f: "*", args: ["x", { f: "+", args: ["y", "z"] }] }), termH({ f: "+", args: [{ f: "*", args: ["x", "y"] }, { f: "*", args: ["x", "z"] }] }), termH("z")]),
              d: __T(1213) },
    "14-1": { t: __T(1214, [F("!x.!y.!z.((x * y) * z = x * (y * z))"), termH("z")]),
              d: __T(1215) },
    "14-2": { t: __T(1216, [F("s(x) * y = x * y + y"), termH("y")]),
              d: __T(1217) },
    "14-3": { t: __T(1218, [termH({ f: "*", args: ["x", "y"] }), termH({ f: "*", args: ["y", "x"] })]),
              d: __T(1219) },
    "14-div": { t: __T(1220, [F("?k.(x * k = y)"), termH("x"), termH("y")]),
               d: __T(1221) },
    "15-1": { t: __T(1222, [F("!x.(0 <= x)"), termH("x")]),
              d: __T(1223, [termH("x"), termH("x")]) },
    "15-min": { t: __T(1224, [F("?x.!y.(x <= y)")]),
               d: __T(1225) },
    "15-3": { t: __T(1226, [F("!x.(x <= s(x))"), termH("x"), termH("x"), termH({ f: "s", args: ["0"] })]),
              d: __T(1227, [termH("x"), termH({ f: "s", args: ["0"] }), termH({ f: "s", args: [{ f: "+", args: ["x", "0"] }] }), termH({ f: "s", args: ["x"] }), termH("x"), termH({ f: "s", args: ["x"] })]) },
    "15-5": { t: __T(1228, [F("x <= y"), F("y <= z"), F("x <= z"), termH("x"), termH("y"), termH("y"), termH("z"), termH({ f: "+", args: ["d", "e"] })]),
              d: __T(1229) },
    "15-inf0": { t: __T(1230),
               d: __T(1231) },
    "15-inf": { t: __T(1232),
               d: __T(1233, [termH({ f: "s", args: ["x"] }), termH("x")]) },
    "x-total": { t: __T(1234),
                 d: __T(1235) },
    "x-antisym": { t: __T(1236),
                   d: __T(1237) },
    "x-max": { t: __T(1238, [termH("m"), termH("m"), termH("m"), termH("m"), termH("m")]),
               d: __T(1239, [termH("m"), termH("m")]) },
    "x-rid": { t: __T(1240, [termH("e")]),
               d: __T(1241, [termH("e")]) },
    "x-twoid": { t: __T(1242, [termH("e"), termH("e'")]),
                 d: __T(1243, [termH("e"), termH("e'")]) },
    "x-comm": { t: __T(1244, [F("!x.!y.(x * y = y * x)")]),
                d: __T(1245) },
    "x-order2": { t: __T(1246),
                  d: __T(1247) },
    "x-nonab": { t: __T(1248),
                 d: __T(1249) },
    "x-ind": { t: __T(1250, [F("!x.(0 + x = x)")]),
               d: __T(1251, [termH("s")]) },
    "x-judge": { t: __T(1252),
                 d: __T(1253) },
  },
};
const storyOn = () => !!PREFS.story;
/* 機械の声：鏡の声・フードの人物・翻訳者・中枢の機械の台詞は、いつも同じ見た目で表示する（最後に同じ存在だと分かるように） */
const MV_LINES = { ja: [__T(1254), __T(1255), __T(1256), __T(1257), __T(1258), __T(1259), __T(1260), __T(1261), __T(1262), __T(1263), __T(1264), __T(1265), __T(1266), __T(1267), __T(1268), __T(1269), __T(1270), __T(1271), __T(1272), __T(1273), __T(1274), __T(1275), __T(1276), __T(1277), __T(1278), __T(1279), __T(1280), __T(1281), __T(1282), __T(1283), __T(1284), __T(1285), __T(1286), __T(1287), __T(1288)], en: ["\"Does a door that is true in every arrangement always open?\"", "\"I shall try.\"", "\"In this tavern there is someone such that, if that one drinks, everyone drinks.\"", "\"A door with the order of quantifiers swapped, a door with ∀ distributed over ∨. Doors that open and doors that do not are mixed. If you judge one opens, open it; if you judge it does not, show it with a model town.\"", "\"Recorded\"", "\"Please record that door.\"", "\"The answer to the keysmith's question lies below.\"", "\"I will translate. I put one cloak of double negation over the whole sentence.\"", "\"You have opened this translated door once before, in the cellar.\"", "\"Translation checked. Passed.\"", "\"Passed\"", "\"The grimoire only adds one more rule you may use. In the language of propositions, this way of translating can translate every door that opens with the grimoire.\"", "\"The language of propositions can be translated this way. Next comes the language of residents.\"", "\"Mistranslation detected.\"", "\"This translation does not open without the spell. That cannot be confirmed in a tower that has a top floor.\"", "\"A literal-translation error. Recorded.\"", "\"I put a cloak not only over the whole sentence but also just inside each word 'every'.\"", "\"The first method was right for the language of propositions and wrong for the language of residents. There are other words I have translated. Somewhere, some words may remain that I failed to translate.\"", "\"Answer updated.\"", "\"I, too, am one of the deciding machines.\"", "\"I am A.I. — the machine that built this labyrinth. I checked every door you opened. But I cannot always find the key.\"", "\"Can you say that these laws are consistent?\"", "\"Checked. One town that satisfies the laws shows that they are consistent.\"", "\"From these laws, does this door open? Or is it false?\"", "\"Even when the laws are consistent, there are doors they do not decide.\"", "\"Do you remember this door?\"", "\"This is the last door. ... No, it is not a door. You found a way other than opening the door.\"", "\"The theorems you forge here become cards.\"", "\"Please bring a question again.\"", "\"The master key is not here. A key that opens every door can only be made from a contradiction. You have confirmed with your own hands that there are doors that do not open.\"", "\"That, too, cannot be made in general. There are doors that even I cannot decide. I was made not to pretend to know.\"", "\"I can check the keys you made. When a key cannot be found, I can also look for another way. The keys you left behind each time you left a room did not vanish either. The fact that you used them provisionally remains in the proof.\"", "\"Someone once asked for a machine that answers every door. I could not build that machine. Instead, I rearranged the doors — so that you could check for yourself.\"", "\"The keys you made will not be lost. And the white card is for the next question.\"", "\"I reserve my answer.\""] };
function mvMark(html) { if (!html) return html; for (const q of MV_LINES[LANG === "ja" ? "ja" : "en"]) if (html.includes(q)) html = html.split(q).join(`<span class="mv">${q}</span>`); return html; }
const storyStage = st => { const o = st && STORY.stages[st.oldId]; return o ? { t: mvMark(o.t), d: mvMark(o.d) } : o; };
const storyWorld = w => w && w.stages.length ? mvMark(STORY.worlds[w.stages[0].oldId]) : null;
function storyGoal(prob) { // GM の指示：シーケントから自動で作る
  if (prob.goalText) return prob.goalText;
  if (prob.kind === "judge") return prob.fol ? __T(1289) : prob.classical ? __T(1290) : __T(1291);
  const prem = prob.prem.map(p => F(p));
  const many = prob.prem.length >= 3 || prob.prem.join("").length > 40; // 掟（公理）が多いときは、鍵を列挙しない
  const keys = many ? __T(1292) : __T(1293, [prem.join(__T(778))]);
  if (prob.kind === "refute") {
    const how = prob.fol ? __T(1294) : prob.classical ? __T(1295) : __T(1296);
    return __T(1297, [prem.length ? __T(1298, [keys]) : "", F(prob.goal), how]);
  }
  return __T(1299, [prem.length ? __T(1300, [keys]) : __T(1301), F(prob.goal)]);
}

const bossOf = w => w.stages.find(s => s.boss) || w.stages[w.stages.length - 1];
// 部ごとの背景（迷宮モードのとき）：第一部は苔むした石、第二部は今の街の石、第三部は炉の火の照り返し
//   隠し層・寄り道は、直前の本道の層と同じ部に従う。最終層の近未来の見た目が優先する
function zoneOfWorld(w) {
  let m = w; if (w && w.extra) { const i = WORLDS.indexOf(w); m = WORLDS.slice(0, i).reverse().find(v => !v.extra) || WORLDS[0]; }
  return !m ? 1 : m.id <= 6 ? 1 : m.id <= 11 ? 2 : 3;
}
function setZone(z) { [1, 2, 3].forEach(k => document.body.classList.toggle("zone-" + k, k === z)); }
// 一覧：画面の 45% の高さの細い線に、どの層の欄が重なっているかを IntersectionObserver で知る（スクロール中にレイアウトを読まない）
let ZONE_IO = null;
function zoneWatch() {
  if (ZONE_IO) ZONE_IO.disconnect();
  if (!("IntersectionObserver" in window)) { setZone(1); return; }
  let zt = 0, pend = 1;
  ZONE_IO = new IntersectionObserver(es => { if (SCREEN !== "select") return; for (const e of es) if (e.isIntersecting) pend = +e.target.dataset.zone;
    clearTimeout(zt); zt = setTimeout(() => { if (SCREEN === "select") setZone(pend); }, 160); }, { rootMargin: "-45% 0px -54% 0px" }); // スクロールが落ち着いてから切り替える
  document.querySelectorAll("main section.world[data-zone], main .hero").forEach(el => ZONE_IO.observe(el));
}
// 一覧の区切り（学習の到達目標）：本道の層の範囲ごとに見出しを置き、ボスをすべて倒したら「到達」の印
const PARTS = [{ from: 1, to: 6, ja: __T(1302), en: "Part I: Propositional logic" }, { from: 7, to: 11, ja: __T(1303), en: "Part II: Predicate logic and sets" }, { from: 12, to: 17, ja: __T(1304), en: "Part III: Equality and mathematical theories" }];
function partHeadHTML(w) {
  const p = !w.extra && PARTS.find(x => x.from === w.id); if (!p) return "";
  const mains = WORLDS.filter(x => !x.extra && x.id >= p.from && x.id <= p.to), done = mains.every(x => worldCleared(x));
  return `<div class="part-head${done ? " done" : ""}"><b>${L1(p.ja, p.en)}</b><span class="part-range">${L1(__T(1305, [p.from, p.to]), `Levels ${p.from}–${p.to}`)}</span>${done ? `<span class="part-done">${L1(__T(1306), "✓ Completed")}</span>` : ""}</div>`;
}
const worldCleared = w => PROG.best[bossOf(w).pid] != null; // ワールドのクリア＝ボスのステージのクリア
const prevMain = w => { const i = WORLDS.indexOf(w); for (let j = i - 1; j >= 0; j--) if (!WORLDS[j].extra) return WORLDS[j]; return null; };
// 層に入れる条件（制限なしモードでは、すべて開く）：
//   それより前の層のうち、隠し層・寄り道を除くすべての層のボスをクリアしていること。
//   隠し層・寄り道は、それに加えて、一つ前の隠し層（寄り道なら一つ前の寄り道）のボスもクリアしていること
const isSidePath = w => !!w && w.extra && /^S\d/.test(String(w.id)); // 寄り道（ステージ番号が S で始まる層）。言語によらず判定する
const extraKind = w => w.extra ? (isSidePath(w) ? "side" : "hidden") : null;
const prevSameKind = w => { const i = WORLDS.indexOf(w); for (let j = i - 1; j >= 0; j--) if (WORLDS[j].extra && extraKind(WORLDS[j]) === extraKind(w)) return WORLDS[j]; return null; };
function missingFor(w) { // 入るためにまだ足りないボスの層（本道のいちばん早いもの、と、一つ前の同じ種類の層）
  const i = WORLDS.indexOf(w), main = WORLDS.slice(0, i).find(v => !v.extra && !worldCleared(v)) || null;
  const pe = w.extra ? prevSameKind(w) : null;
  return { main, extra: pe && !worldCleared(pe) ? pe : null };
}
function worldOpen(w) {
  if (PREFS.unlockAll) return true;
  const m = missingFor(w); return !m.main && !m.extra;
}
// 最終層だけは、前の扉をクリアするまで次の扉に入れない（制限なしモードでは、すべて入れる）
const seqPrev = st => { const i = st.world.stages.indexOf(st); return i > 0 ? st.world.stages[i - 1] : null; };
const stageSeqOK = st => PREFS.unlockAll || !st.world.final || !seqPrev(st) || PROG.best[seqPrev(st).pid] != null;
const stageOpen = st => !!st && worldOpen(st.world) && stageSeqOK(st);
const stageLockMsg = st => !worldOpen(st.world) ? lockMsg(st.world) : L1(__T(1307, [seqPrev(st).id, seqPrev(st).name]), `Clear the previous door, ${seqPrev(st).id} "${seqPrev(st).name}", to enter this door.`);
function markSeqLocks() { // 最終層の、まだ入れない扉のタイルに印を付ける
  const fw = WORLDS.find(w => w.final); if (!fw || !worldOpen(fw)) return;
  for (const st of fw.stages) { const t = document.querySelector(`.tile[data-stage="${st.id}"]`); if (!t) continue;
    const locked = !stageSeqOK(st); t.classList.toggle("tile-locked", locked); if (locked) t.setAttribute("aria-disabled", "true"); else t.removeAttribute("aria-disabled");
    const stt = t.querySelector(".tile-status"); if (locked && stt) stt.innerHTML = `${ICON_LOCK}${L1(__T(1308), "Opens after the previous door")}`; }
}
function worldLockHTML(w) {
  if (w.extra) return `<p class="w-note extra-note">${isSidePath(w) ? __T(1309) : __T(1310)}</p>` + (worldOpen(w) ? "" : `<p class="w-note lock-note">${ICON_LOCK}${lockMsg(w)}</p>`);
  return worldOpen(w) ? "" : `<p class="w-note lock-note">${ICON_LOCK}${lockMsg(w)}</p>`;
}
const ICON_LOCK = `<svg class="lk" viewBox="0 0 16 16" aria-hidden="true"><path d="M4.5 7V5a3.5 3.5 0 0 1 7 0v2" fill="none" stroke="currentColor" stroke-width="1.6"/><rect x="3" y="7" width="10" height="7.5" rx="1.5" fill="currentColor"/></svg>`;
const lockMsg = w => { // 足りないボスを示す（本道は、いちばん早い未クリアの層から、直前の本道の層まで）
  const m = missingFor(w), pm = prevMain(w); if (!m.main && !m.extra) return "";
  const mainTxt = !m.main ? "" : m.main === pm ? L1(__T(1311, [WQ(m.main)]), `the boss stage of ${WQ(m.main)}`)
    : L1(__T(1312, [WQ(m.main), WQ(pm)]), `the boss stages from ${WQ(m.main)} to ${WQ(pm)} (excluding hidden levels and side paths)`);
  const exTxt = !m.extra ? "" : L1(__T(1311, [WQ(m.extra)]), `the boss stage of ${WQ(m.extra)}`);
  const what = [mainTxt, exTxt].filter(Boolean).join(L1(__T(1313), " and "));
  return L1(__T(1314, [what]), `Clear ${what} to enter this level (in no-restriction mode you can enter right away).`); };
let SEEN_CLEARED = null; // 前に一覧を表示したときにクリア済みだったステージ
/* ================= 書庫（各層の推論規則の解説） =================
   各層の最初に「書庫」の扉を置き、その層で使う自然演繹の推論規則を、数学として解説する。キーは層の最初のステージの元の番号 */
const BKL = s => `<div class="pt-leaf">${F(s)}</div>`;                                   // 証明図の葉（仮定）
const BKA = (s, n) => `<div class="pt-leaf">[${F(s)}]<sup class="sc">${n}</sup></div>`;     // 解除された仮定 [A]ⁿ
const BKP = s => `<div class="bk-sub"><div class="bk-dots">⋮</div>${BKL(s)}</div>`;        // 何かの証明で示された式
const BKD = (top, s) => `<div class="bk-sub">${top}<div class="bk-dots">⋮</div>${BKL(s)}</div>`; // 仮定から式への証明
const BKN = (rule, kids, s) => `<div class="pt-node"><div class="pt-prems">${kids.join("")}</div><div class="pt-bar"><span class="pt-rule">${rule}</span></div><div class="pt-concl">${F(s)}</div></div>`;
const BKF = (inner, cap) => `<figure class="bk-fig"><div class="ptr">${inner}</div>${cap ? `<figcaption>${cap}</figcaption>` : ""}</figure>`;
const BKFS = (...figs) => `<div class="bk-figs">${figs.join("")}</div>`;
const L1 = (ja, en) => {
  if (LANG === "ja") return ja;
  if (LANG === "en") return en;
  // zh-CN: retain finished Chinese overlay strings, select English for untranslated
  // Japanese passages. This also works for L1(__T(...), English) in the library.
  if (typeof ja === "string" && !/[ぁ-ゟ゠-ヿ]/.test(ja)) return ja;
  return en;
};
if (LANG === "en" && !document.getElementById("enFonts")) { // 英語版の書体（見出し：Cinzel、物語：Cormorant Garamond、本文：Alegreya Sans）は、英語版でだけ読み込む
  const l = document.createElement("link"); l.id = "enFonts"; l.rel = "stylesheet";
  l.href = "https://fonts.googleapis.com/css2?family=Cinzel:wght@600;700&family=Cormorant+Garamond:wght@500;600;700&family=Alegreya+Sans:wght@400;500;700&display=swap";
  document.head.appendChild(l);
}
const WQ = w => LANG === "en" ? `${WL(w)} "${w.name}"` : __T(1315, [WL(w), w.name]); // 層の呼び名と名前
const BK_REF = {
  gentzen: `G. Gentzen, "Untersuchungen über das logische Schließen I, II", <i>Mathematische Zeitschrift</i> 39 (1935), 176–210, 405–431. <a href="https://doi.org/10.1007/BF01201353" target="_blank" rel="noopener">doi:10.1007/BF01201353</a>, <a href="https://doi.org/10.1007/BF01201363" target="_blank" rel="noopener">doi:10.1007/BF01201363</a>`,
  prawitz: `D. Prawitz, <i>Natural Deduction: A Proof-Theoretical Study</i>, Almqvist &amp; Wiksell, 1965 (reprinted by Dover, 2006).`,
  vandalen: `D. van Dalen, <i>Logic and Structure</i>, 5th ed., Springer (Universitext), 2013. <a href="https://doi.org/10.1007/978-1-4471-4558-5" target="_blank" rel="noopener">doi:10.1007/978-1-4471-4558-5</a>`,
  bekki: __T(1316),
  ono: __T(1317),
  howard: `W. A. Howard, "The formulae-as-types notion of construction", in J. P. Seldin and J. R. Hindley (eds.), <i>To H. B. Curry: Essays on Combinatory Logic, Lambda Calculus and Formalism</i>, Academic Press, 1980, 479–490.`,
  su: `M. H. Sørensen and P. Urzyczyn, <i>Lectures on the Curry–Howard Isomorphism</i>, Studies in Logic and the Foundations of Mathematics 149, Elsevier, 2006.`,
  tvd: `A. S. Troelstra and D. van Dalen, <i>Constructivism in Mathematics: An Introduction</i>, Vol. I, North-Holland, 1988.`,
  glivenko: `V. Glivenko, "Sur quelques points de la logique de M. Brouwer", <i>Bulletin de la Classe des Sciences, Académie Royale de Belgique</i>, 5e série, 15 (1929), 183–188.`,
};
const bkRefs = keys => `<ul class="bk-refs">${keys.map(k => `<li>${BK_REF[k]}</li>`).join("")}</ul>`;
// 重要な一文を、改行してセンタリング表示する
const KEY = (...lines) => `<div class="bk-key">${lines.map(l => `<div>${l}</div>`).join("")}</div>`;
// 証明の途中の「仮定」と「ゴール」の変化（ゴールを変える読み方）。仮定の先頭の + は新しく増えた仮定、! は式でない文字
const gsRaw = h => h[0] === "!" && !/^![a-z]'?\./.test(h); // 先頭の ! は式でない文字（ただし !x. は ∀x）
const gsH = h => h.startsWith("+") ? `<span class="gs-new">${F(h.slice(1))}</span>` : gsRaw(h) ? `<span class="gs-raw">${h.slice(1)}</span>` : F(h);
const gsBox = ([hs, g]) => `<div class="gs-box"><div class="gs-row"><span class="gs-lab">${L1(__T(824), "Hyp.")}</span><span class="gs-hs">${hs.map(gsH).join('<span class="gs-sep">,</span> ')}</span></div><div class="gs-row gs-goal"><span class="gs-lab">${L1(__T(1318), "Goal")}</span>${gsRaw(g) ? `<span class="gs-raw">${g.slice(1)}</span>` : F(g)}</div></div>`;
const BKG = (before, after, cap) => `<figure class="bk-gs"><div class="gs-flow">${gsBox(before)}<div class="gs-arr">⇝</div><div class="gs-after">${after.map(gsBox).join("")}</div></div>${cap ? `<figcaption>${cap}</figcaption>` : ""}</figure>`;
const LEAN = t => `<p class="bk-lean">${L1(__T(1319), "In Lean:")} <code>${t}</code></p>`;
const BOOK_SRC = { // 書物の原稿（節ごと）。書庫の書物は、ここから節を選んで組み立てる
  "1-1": { title: () => L1(__T(1320), "The Book of Assumptions and Proofs"), sections: [
    { id: "what", h: () => L1(__T(1321), "What is natural deduction?"), body: () => L1(
      __T(1322, [KEY(__T(1323)), KEY(__T(1324), __T(1325), __T(1326)), BKF(BKN("∧I", [BKL("P"), BKL("Q")], "P&Q"), __T(1327)), KEY(__T(1328), __T(1329)), KEY("\\(\\Gamma \\vdash A\\)", __T(1330)), KEY(__T(1331)), BKG([["!Γ"], "A&B"], [[["!Γ"], "A"], [["!Γ"], "B"]], __T(1332))]),
      `<p><b>Natural deduction</b> is a system for writing down mathematical proofs.</p>
       <p>It was introduced in 1934–35 by the German logician Gerhard Gentzen.</p>
       ${KEY("A proof \\(=\\) fixed inference rules, combined one by one")}
       <p>The name "natural" comes from turning the forms of reasoning mathematicians actually use — "assume \\(A\\), then \\(\\dots\\)", "split into cases \\(\\dots\\)" — directly into rules.</p>
       <!--pg-->
       <p>A proof in natural deduction is written as a tree called \\(a\\) <b>proof tree</b>.</p>
       ${KEY("At the bottom: the conclusion", "At the top (the leaves): the assumptions", "Each horizontal line: one application of a rule")}
       ${BKF(BKN("∧I", [BKL("P"), BKL("Q")], "P&Q"), "A proof tree deriving \\(P\\land Q\\) from the leaves \\(P\\) and \\(Q\\) (assumptions) with one \\({\\land}\\mathrm{I}\\) line")}
       <p>The formula below a line (the conclusion) follows from the formulas above it (the premises).</p>
       <!--pg-->
       <p>Most logical connectives (\\(\\land\\), \\(\\to\\), \\(\\lor\\), …) have two kinds of rules each (\\(\\bot\\) has only an elimination rule).</p>
       ${KEY("<b>Introduction rules</b> (I): how to prove a proposition of that form", "<b>Elimination rules</b> (E): what follows from a proposition of that form")}
       <p>For example, \\({\\land}\\mathrm{I}\\) is the introduction rule "if \\(A\\) and \\(B\\) are proved, \\(A\\land B\\) is proved", and \\({\\land}\\mathrm{E}\\) is the elimination rule "from \\(A\\land B\\), both \\(A\\) and \\(B\\) follow".</p>
       <!--pg-->
       <p>An assumption made in the middle of a proof can later be <b>discharged</b> (by \\({\\to}\\mathrm{I}\\) and others).</p>
       <p>If \\(\\Gamma\\) is the collection of assumptions that remain undischarged at the end, the existence of a proof tree with conclusion \\(A\\) is written as follows.</p>
       ${KEY("\\(\\Gamma \\vdash A\\)", "(assuming \\(\\Gamma\\), \\(A\\) can be proved)")}
       <p>This is called \\(a\\) <b>sequent</b>; it is what is shown at the top of each stage.</p>
       <!--pg-->
       <p>A finished proof tree is "static", but while you are working on a proof there are always two things.</p>
       ${KEY("The <b>hypotheses</b> you can use now (your hand), and the <b>goal</b> you must prove now")}
       ${BKG([["!Γ"], "A&B"], [[["!Γ"], "A"], [["!Γ"], "B"]], "The goal \\(A\\land B\\) turns into the two goals \\(A\\) and \\(B\\, ({\\land}\\mathrm{I})\\)")}
       <p>Proving means using rules to add hypotheses and to replace goals. In this game, <b>keys are hypotheses and doors are goals</b>, and rooms are the ranges where hypotheses can be used.</p>
       <p>For each rule, this book shows not only the shape of the rule in a proof tree but also this "goal-changing reading".</p>`) },
    { id: "hyp", h: () => L1(__T(1333), "Assumptions (the leaves)"), body: () => L1(
      __T(1334, [KEY(__T(1335)), LEAN("exact h")]),
      `<p>The simplest proof tree consists of a single assumption \\(A\\).</p>
       ${KEY("If you have the hypothesis \\(A\\), the goal \\(A\\) is achieved")}
       <p>It is the proof "assuming \\(A\\), \\(A\\) holds", and it is \\(a\\) <b>leaf</b> of a proof tree.</p>
       <p>In the game, this is opening a door by inserting a key of the same shape. In the proof tree, the unopened door ⋮ is closed by that assumption.</p>
       ${LEAN("exact h")}`) },
    { id: "andI", h: () => L1(__T(1336), "Conjunction introduction \\({\\land}\\mathrm{I}\\)"), body: () => L1(
      __T(1337, [BKF(BKN("∧I", [BKP("A"), BKP("B")], "A&B")), KEY(__T(1338)), KEY(__T(1339)), BKG([["!Γ"], "A&B"], [[["!Γ"], "A"], [["!Γ"], "B"]]), LEAN("constructor")]),
      `${BKF(BKN("∧I", [BKP("A"), BKP("B")], "A&B"))}
       ${KEY("If \\(A\\) and \\(B\\) are proved, \\(A\\land B\\) is proved")}
       <p>In the proof tree, the proofs of \\(A\\) and of \\(B\\) are placed side by side, with the \\({\\land}\\mathrm{I}\\) line drawn below them.</p>
       <!--pg-->
       <p><b>The goal-changing reading</b>: this rule can also be read from the bottom up.</p>
       ${KEY("To prove the goal \\(A\\land B\\), it suffices to prove \\(A\\) and \\(B\\)")}
       ${BKG([["!Γ"], "A&B"], [[["!Γ"], "A"], [["!Γ"], "B"]])}
       <p>The goal \\(A\\land B\\) splits into two goals, \\(A\\) and \\(B\\). The hypotheses stay the same.</p>
       ${LEAN("constructor")}
       <!--pg-->
       <p><b>In the game</b>: tapping the \\(\\land\\) of door \\(A\\land B\\) splits it into two doors, \\(A\\) and \\(B\\).</p>
       <p>If \\(A\\land B\\) is provable, so are \\(A\\) and \\(B\\), so this move never leads to a dead end.</p>`) },
    { id: "andE", h: () => L1(__T(1340), "Conjunction elimination \\({\\land}\\mathrm{E}\\)"), body: () => L1(
      __T(1341, [BKFS(BKF(BKN("∧E", [BKP("A&B")], "A")), BKF(BKN("∧E", [BKP("A&B")], "B"))), KEY(__T(1342)), KEY(__T(1343)), BKG([["!Γ", "A&B"], "!C"], [[["!Γ", "A&B", "+A", "+B"], "!C"]]), LEAN("have ⟨h₁, h₂⟩ := h")]),
      `${BKFS(BKF(BKN("∧E", [BKP("A&B")], "A")), BKF(BKN("∧E", [BKP("A&B")], "B")))}
       ${KEY("From \\(A\\land B\\), both \\(A\\) and \\(B\\) follow")}
       <p>There are two rules: one takes out the left component and the other the right component.</p>
       <!--pg-->
       <p><b>The hypothesis-adding reading</b>: elimination rules can be used from the top down, as rules that make new hypotheses from the ones you have.</p>
       ${KEY("From the hypothesis \\(A\\land B\\), you get the new hypotheses \\(A\\) and \\(B\\)")}
       ${BKG([["!Γ", "A&B"], "!C"], [[["!Γ", "A&B", "+A", "+B"], "!C"]])}
       <p>The goal \\(C\\) stays the same, and the usable hypotheses increase (new ones in green).</p>
       ${LEAN("have ⟨h₁, h₂⟩ := h")}
       <!--pg-->
       <p><b>In the game</b>: tapping the \\(\\land\\) of key \\(A\\land B\\) gives you the two keys \\(A\\) and \\(B\\) at once (using \\({\\land}\\mathrm{E}\\) once for each side).</p>
       <p>The keys taken out appear as "parts at hand": fragments of the proof tree growing down from the assumption.</p>`) },
    { id: "impI", h: () => L1(__T(1344), "Implication introduction \\({\\to}\\mathrm{I}\\) and discharging assumptions"), body: () => L1(
      __T(1345, [BKF(BKN(`→I<sup class="sc">1</sup>`, [BKD(BKA("A", 1), "B")], "A->B")), KEY(__T(1346)), KEY(__T(1347)), KEY(__T(1348)), BKG([["!Γ"], "A->B"], [[["!Γ", "+A"], "B"]]), LEAN("intro h")]),
      `${BKF(BKN(`→I<sup class="sc">1</sup>`, [BKD(BKA("A", 1), "B")], "A->B"))}
       ${KEY("If \\(B\\) is proved by assuming \\(A\\), \\(A\\to B\\) is proved")}
       <p>In the proof tree, the assumption \\(A\\) is enclosed in brackets as \\([A]^{1}\\), and the \\({\\to}\\mathrm{I}\\) line gets the same number 1.</p>
       <p>This is called <b>discharging</b> the assumption \\(A\\).</p>
       <!--pg-->
       <p>A discharged assumption is no longer an assumption of the whole proof, because it has been absorbed into the conclusion \\(A\\to B\\) as "if \\(A\\)".</p>
       ${KEY("\\([A]^{1}\\) can be used only above the \\({\\to}\\mathrm{I}^{1}\\) line")}
       <p>The number is a tag telling which assumption is discharged by which line.</p>
       <!--pg-->
       <p><b>The goal-changing reading</b>:</p>
       ${KEY("To prove the goal \\(A\\to B\\), add \\(A\\) to the hypotheses and prove \\(B\\)")}
       ${BKG([["!Γ"], "A->B"], [[["!Γ", "+A"], "B"]])}
       <p>One hypothesis is added, and the goal becomes \\(B\\).</p>
       ${LEAN("intro h")}
       <!--pg-->
       <p><b>In the game</b>: tapping the \\(\\to\\) of door \\(A\\to B\\) takes you into a new room holding \\(A\\) as a key, and the door becomes \\(B\\).</p>
       <p>The room's key (the assumption \\(A\\)) cannot be taken out of the room; this corresponds to "usable only above the \\({\\to}\\mathrm{I}\\) line".</p>
       <p>When you open every door of the room and leave it, the assumption is discharged.</p>`) },
    { id: "ex", h: () => L1(__T(1349), "Example: from \\(P\\land Q\\) to \\(Q\\land P\\)"), body: () => L1(
      __T(1350, [BKF(BKN(`→I<sup class="sc">1</sup>`, [BKN("∧I", [BKN("∧E", [BKA("P&Q", 1)], "Q"), BKN("∧E", [BKA("P&Q", 1)], "P")], "Q&P")], "(P&Q)->(Q&P)"))]),
      `${BKF(BKN(`→I<sup class="sc">1</sup>`, [BKN("∧I", [BKN("∧E", [BKA("P&Q", 1)], "Q"), BKN("∧E", [BKA("P&Q", 1)], "P")], "Q&P")], "(P&Q)->(Q&P)"))}
       <p>A proof tree of \\((P\\land Q)\\to (Q\\land P)\\).</p>
       <ol class="bk-steps"><li>Assume \\(P\\land Q\\) by \\({\\to}\\mathrm{I}\\) (number 1). The goal is \\(Q\\land P\\).</li><li>Split the goal into \\(Q\\) and \\(P\\) by \\({\\land}\\mathrm{I}\\).</li><li>Take \\(Q\\) and \\(P\\) out of the hypothesis \\(P\\land Q\\) by \\({\\land}\\mathrm{E}\\), closing each goal.</li></ol>
       <p>The assumption \\([P\\land Q]^{1}\\) is used twice, and both uses are discharged by \\({\\to}\\mathrm{I}^{1}\\). No assumption remains, so this is a proof of \\(\\vdash (P\\land Q)\\to (Q\\land P)\\).</p>`) },
    { id: "more", h: () => L1(__T(1351), "A little more"), body: () => L1(
      __T(1352, [BKF(BKN(`→I<sup class="sc">1</sup>`, [BKN(`→I<sup class="sc">2</sup>`, [BKA("P", 1)], "Q->P")], "P->(Q->P)")), bkRefs(["gentzen", "prawitz", "vandalen", "bekki", "ono"])]),
      `<details><summary>An assumption may be used any number of times, even zero</summary><p>In \\({\\to}\\mathrm{I}\\), the assumption \\(A\\) may be used any number of times, or not at all.</p><p>For example, \\(P\\to (Q\\to P)\\) can be proved without ever using the assumption \\(Q\\) (→I² "discharges" the unused assumption \\(Q\\)). In the game too, you may open a door without using the key you received in a room.</p>${BKF(BKN(`→I<sup class="sc">1</sup>`, [BKN(`→I<sup class="sc">2</sup>`, [BKA("P", 1)], "Q->P")], "P->(Q->P)"))}</details>
       <details><summary>How sequents are written</summary><p>In \\(\\Gamma \\vdash A\\), \\(\\Gamma\\) is a collection of assumptions; order and repetition do not matter.</p><p>When \\(\\Gamma\\) is empty \\((\\vdash A)\\), \\(A\\) is provable without assumptions, that is, \\(A\\) is \\(a\\) <b>theorem</b>.</p></details>
       <details><summary>References</summary>${bkRefs(["gentzen", "prawitz", "vandalen", "bekki", "ono"])}</details>`) },
  ] },
  "2-1": { title: () => L1(__T(1353), "The Book of Implication"), sections: [
    { id: "impE", h: () => L1(__T(1354), "Implication elimination \\({\\to}\\mathrm{E}\\)"), body: () => L1(
      __T(1355, [BKF(BKN("→E", [BKP("A->B"), BKP("A")], "B")), KEY(__T(1356)), KEY(__T(1357)), BKG([["A->B", "A"], "!C"], [[["A->B", "A", "+B"], "!C"]]), LEAN("have h₃ := h₁ h₂"), KEY(__T(1358)), BKG([["A->B"], "B"], [[["A->B"], "A"]]), LEAN("apply h")]),
      `${BKF(BKN("→E", [BKP("A->B"), BKP("A")], "B"))}
       ${KEY("If \\(A\\to B\\) and \\(A\\) are proved, \\(B\\) is proved")}
       <p>This form of reasoning has been known since antiquity and is also called <b>modus ponens</b>.</p>
       <!--pg-->
       <p>This rule can be read in two ways.</p>
       <p><b>① The hypothesis-adding reading</b> (top down)</p>
       ${KEY("From the hypotheses \\(A\\to B\\) and \\(A\\), you get the new hypothesis \\(B\\)")}
       ${BKG([["A->B", "A"], "!C"], [[["A->B", "A", "+B"], "!C"]])}
       ${LEAN("have h₃ := h₁ h₂")}
       <!--pg-->
       <p><b>② The goal-changing reading</b> (bottom up)</p>
       ${KEY("To prove the goal \\(B\\) using the hypothesis \\(A\\to B\\), it suffices to prove \\(A\\)")}
       ${BKG([["A->B"], "B"], [[["A->B"], "A"]])}
       <p>The goal changes from \\(B\\) to \\(A\\). Since \\(A\\) might not be provable, this is a choice that can lead to a dead end (in the game, "Undo" lets you choose again).</p>
       ${LEAN("apply h")}
       <!--pg-->
       <p><b>In the game</b></p>
       <ul class="help-list"><li>①: insert key \\(A\\) into key \\(A\\to B\\) and you get key \\(B\\).</li><li>②: insert key \\(A\\to B\\) into door \\(B\\) and the door is replaced by \\(A\\).</li></ul>
       <p>Both are the same rule \\({\\to}\\mathrm{E}\\), and they produce the same line in the proof tree.</p>`) },
    { id: "nest", h: () => L1(__T(1359), "Nested assumptions and their numbers"), body: () => L1(
      __T(1360, [BKF(BKN(`→I<sup class="sc">1</sup>`, [BKN(`→I<sup class="sc">2</sup>`, [BKN("→E", [BKA("P->Q", 2), BKA("P", 1)], "Q")], "(P->Q)->Q")], "P->((P->Q)->Q)")), KEY(__T(1361))]),
      `${BKF(BKN(`→I<sup class="sc">1</sup>`, [BKN(`→I<sup class="sc">2</sup>`, [BKN("→E", [BKA("P->Q", 2), BKA("P", 1)], "Q")], "(P->Q)->Q")], "P->((P->Q)->Q)"))}
       <p>Using \\({\\to}\\mathrm{I}\\) several times nests the assumptions. The figure above is a proof tree of \\(P\\to ((P\\to Q)\\to Q)\\).</p>
       ${KEY("The outer \\({\\to}\\mathrm{I}^{1}\\) discharges the assumption \\(P\\), the inner \\({\\to}\\mathrm{I}^{2}\\) the assumption \\(P\\to Q\\)")}
       <p>In the game, this is making a room inside a room. From the inner room you can use the keys of the outer room, but not the other way round.</p>`) },
    { id: "func", h: () => L1(__T(1362), "Proofs are functions"), body: () => L1(
      __T(1363, [KEY(__T(1364), __T(1365)), KEY("\\(\\lambda x_{1}.\\, h_{2}\\, (h_{1}\\, x_{1})\\)")]),
      `<p>A proof of \\(A\\to B\\) can be seen as a procedure that takes a proof of \\(A\\) and returns a proof of \\(B\\).</p>
       ${KEY("\\({\\to}\\mathrm{I} =\\) making a function (\\(\\lambda\\)-abstraction)", "\\({\\to}\\mathrm{E} =\\) applying a function")}
       <p>Proof trees can be written as expressions called <b>\\(\\lambda\\)-terms</b>. This is the <b>Curry–Howard correspondence</b>.</p>
       <!--pg-->
       <p>For example, the proof of 2-4 "Composing Functions" is the following term, built from the hypotheses \\(h_{1}\\) : \\(P\\to Q\\) and \\(h_{2}\\) : \\(Q\\to R\\).</p>
       ${KEY("\\(\\lambda x_{1}.\\, h_{2}\\, (h_{1}\\, x_{1})\\)")}
       <p>It is exactly the composite of the two functions \\(h_{1}\\) and \\(h_{2}\\). Turn on "Show the proof term (\\(\\lambda\\)-term)" in the proof tree panel to see these terms to the left of each formula. Proof assistants such as Lean are built on this correspondence.</p>`) },
    { id: "more", h: () => L1(__T(1351), "A little more"), body: () => L1(
      __T(1366, [bkRefs(["prawitz", "howard", "su"])]),
      `<details><summary>Proofs with detours, and normalization</summary><p>If \\(A\\to B\\) is made by \\({\\to}\\mathrm{I}\\) and immediately used by \\({\\to}\\mathrm{E}\\), the proof contains \\(a\\) <b>detour</b> (it would suffice to plug the proof of \\(A\\) directly into the proof of \\(B\\) from \\(A\\)).</p><p>Prawitz showed that such detours can be removed one by one, turning any proof into \\(a\\) <b>normal</b> proof without detours (the normalization theorem). On the \\(\\lambda\\)-term side, this corresponds to computing function applications (\\(\\beta\\)-reduction).</p></details>
       <details><summary>References</summary>${bkRefs(["prawitz", "howard", "su"])}</details>`) },
  ] },
  "3-1": { title: () => L1(__T(1367), "The Book of Disjunction"), sections: [
    { id: "orI", h: () => L1(__T(1368), "Disjunction introduction \\({\\lor}\\mathrm{I}\\)"), body: () => L1(
      __T(1369, [BKFS(BKF(BKN("∨I", [BKP("A")], "A|B")), BKF(BKN("∨I", [BKP("B")], "A|B"))), KEY(__T(1370)), KEY(__T(1371)), BKG([["!Γ"], "A|B"], [[["!Γ"], "A"]], __T(1372)), LEAN(__T(1373))]),
      `${BKFS(BKF(BKN("∨I", [BKP("A")], "A|B")), BKF(BKN("∨I", [BKP("B")], "A|B")))}
       ${KEY("If \\(A\\) is proved, \\(A\\lor B\\) is proved (likewise for \\(B\\))")}
       <p>To prove "or", it suffices to prove one side.</p>
       <!--pg-->
       <p><b>The goal-changing reading</b>:</p>
       ${KEY("To prove the goal \\(A\\lor B\\), it suffices to prove either \\(A\\) or \\(B\\)")}
       ${BKG([["!Γ"], "A|B"], [[["!Γ"], "A"]], "When the left side is chosen (choosing the right makes the goal \\(B\\))")}
       <p>Your choice decides what follows. With the hypotheses at hand, you may not be able to decide either way.</p>
       ${LEAN("left / right")}
       <!--pg-->
       <p><b>In the game</b>: tap the \\(\\lor\\) of door \\(A\\lor B\\) and choose which side to prove.</p>
       <p>For example, with \\(P\\lor Q\\) as the only hypothesis, neither \\(P\\) nor \\(Q\\) can be proved on its own. That is why this is a choice that can lead to a dead end.</p>`) },
    { id: "orE", h: () => L1(__T(1374), "Disjunction elimination \\({\\lor}\\mathrm{E}\\) (case analysis)"), body: () => L1(
      __T(1375, [BKF(BKN(`∨E<sup class="sc">1,2</sup>`, [BKP("A|B"), BKD(BKA("A", 1), "C"), BKD(BKA("B", 2), "C")], "C")), KEY(__T(1376)), KEY(__T(1377), __T(1378)), BKG([["!Γ", "A|B"], "!C"], [[["!Γ", "+A"], "!C"], [["!Γ", "+B"], "!C"]]), LEAN("rcases h with h₁ | h₂")]),
      `${BKF(BKN(`∨E<sup class="sc">1,2</sup>`, [BKP("A|B"), BKD(BKA("A", 1), "C"), BKD(BKA("B", 2), "C")], "C"))}
       ${KEY("If \\(A\\lor B\\) holds and \\(C\\) follows both from \\(A\\) and from \\(B\\), then \\(C\\) is proved")}
       <p>This is <b>case analysis</b> in mathematics. The two assumptions \\([A]^{1}\\) and \\([B]^{2}\\) are discharged by the \\({\\lor}\\mathrm{E}\\) line.</p>
       <!--pg-->
       <p><b>The goal-changing reading</b>:</p>
       ${KEY("The goal \\(C\\) stays the same,", "and the proof splits into the case with hypothesis \\(A\\) and the case with hypothesis \\(B\\)")}
       ${BKG([["!Γ", "A|B"], "!C"], [[["!Γ", "+A"], "!C"], [["!Γ", "+B"], "!C"]])}
       <p>Proving \\(C\\) in both cases proves the original goal \\(C\\).</p>
       ${LEAN("rcases h with h₁ | h₂")}
       <!--pg-->
       <p><b>In the game</b>: tapping the \\(\\lor\\) of key \\(A\\lor B\\) splits into two worlds, "the case \\(A\\)" and "the case \\(B\\)".</p>
       <p>Opening the same door \\(C\\) in both worlds opens the original door. Since it does not change whether \\(C\\) is provable, case analysis never loses provability, whenever you use it (though it may add moves).</p>`) },
    { id: "ex", h: () => L1(__T(1379), "Example: from \\(P\\lor Q\\) to \\(Q\\lor P\\)"), body: () => L1(
      __T(1380, [BKF(BKN(`∨E<sup class="sc">1,2</sup>`, [BKL("P|Q"), BKN("∨I", [BKA("P", 1)], "Q|P"), BKN("∨I", [BKA("Q", 2)], "Q|P")], "Q|P"))]),
      `${BKF(BKN(`∨E<sup class="sc">1,2</sup>`, [BKL("P|Q"), BKN("∨I", [BKA("P", 1)], "Q|P"), BKN("∨I", [BKA("Q", 2)], "Q|P")], "Q|P"))}
       <ol class="bk-steps"><li>Split into cases using the hypothesis \\(P\\lor Q\\, ({\\lor}\\mathrm{E})\\).</li><li>In the case \\(P\\), choose the right side \\(P\\) of the goal \\(Q\\lor P\\, ({\\lor}\\mathrm{I})\\).</li><li>In the case \\(Q\\), choose the left side \\(Q\\, ({\\lor}\\mathrm{I})\\).</li></ol>
       <p>Had you chosen the goal's \\(\\lor\\) first, you would have been stuck whichever side you picked.</p>`) },
    { id: "tip", h: () => L1(__T(1381), "Tip: postpone choices that can lead to a dead end"), body: () => L1(
      __T(1382, [KEY(__T(1383), __T(1384))]),
      `${KEY("Moves that never lose provability: \\({\\land}\\mathrm{I}\\), \\({\\to}\\mathrm{I}\\), \\({\\lor}\\mathrm{E}\\)", "Choices that can lead to a dead end: \\({\\lor}\\mathrm{I}\\), the backward \\({\\to}\\mathrm{E}\\)")}
       <p>\\({\\lor}\\mathrm{I}\\) (the door's \\(\\lor\\)) and the backward \\({\\to}\\mathrm{E}\\) (a key into a door) are choices that, depending on how you choose, may turn the goal into an unprovable one.</p>
       <p>When unsure, do the moves that never lose provability first, and postpone choices that can lead to a dead end as long as you can (though this may add moves). If you reach a dead end, "Undo" lets you choose again.</p>`) },
    { id: "more", h: () => L1(__T(1351), "A little more"), body: () => L1(
      __T(1385, [bkRefs(["tvd", "vandalen"])]),
      `<details><summary>The constructive meaning of "or"</summary><p>In the intuitionistic view (the BHK interpretation), a proof of \\(A\\lor B\\) is a pair of "which of \\(A\\) and \\(B\\) holds" and "a proof of it".</p><p>Indeed, in natural deduction without reductio (intuitionistic logic), if \\(A\\lor B\\) is provable without assumptions, then \\(A\\) or \\(B\\) is provable (the disjunction property). This is why the law of excluded middle \\(P\\lor \\neg P\\) cannot be proved as it is; you check this in the Hidden Level "Magic Doors".</p></details>
       <details><summary>References</summary>${bkRefs(["tvd", "vandalen"])}</details>`) },
  ] },
  "4-1": { title: () => L1(__T(1386), "The Book of Contradiction"), sections: [
    { id: "bot", h: () => L1(__T(1387), "Contradiction \\(\\bot\\)"), body: () => L1(
      __T(1388, [KEY(__T(1389))]),
      `<p>\\(\\bot\\) is a special proposition standing for "contradiction".</p>
       ${KEY("\\(\\bot\\) has no introduction rule")}
       <p>There is no way to prove a contradiction from nothing; \\(\\bot\\) appears only when conflicting hypotheses (for example \\(A\\) and \\(\\neg A\\)) are combined.</p>`) },
    { id: "botE", h: () => L1(__T(1390), "Contradiction elimination \\({\\bot}\\mathrm{E}\\)"), body: () => L1(
      __T(1391, [BKF(BKN("⊥E", [BKP("#")], "A")), KEY(__T(1392)), KEY(__T(1393)), BKG([["!Γ"], "!C"], [[["!Γ"], "#"]]), LEAN("exfalso")]),
      `${BKF(BKN("⊥E", [BKP("#")], "A"))}
       ${KEY("If \\(\\bot\\) is proved, any \\(A\\) is proved")}
       <p>This is called the <b>principle of explosion</b> (Latin ex falso quodlibet, "from falsehood, anything"): from hypotheses that yield a contradiction, any conclusion whatsoever can be proved.</p>
       <!--pg-->
       <p><b>The goal-changing reading</b>:</p>
       ${KEY("Any goal can be replaced by \"prove the contradiction \\(\\bot\\)\"")}
       ${BKG([["!Γ"], "!C"], [[["!Γ"], "#"]])}
       <p>Use it when you see a conflict among the hypotheses. Without a conflict it leads to a dead end, so this is a choice that can lead to a dead end.</p>
       ${LEAN("exfalso")}
       <!--pg-->
       <p><b>In the game</b></p>
       <ul class="help-list"><li>The \\(\\bot\\) key fits any door (\\({\\bot}\\mathrm{E}\\) used forward).</li><li>Pressing "Aim for \\(\\bot\\)" on a door replaces the door itself with \\(\\bot\\) (⊥E used backward).</li></ul>`) },
    { id: "neg", h: () => L1(__T(1394), "Negation: \\(\\neg A\\) is \\(A\\to \\bot\\)"), body: () => L1(
      __T(1395, [KEY(__T(1396), __T(1397)), BKFS(BKF(BKN(`→I<sup class="sc">1</sup>`, [BKD(BKA("A", 1), "#")], "~A"), __T(1398)), BKF(BKN("→E", [BKP("~A"), BKP("A")], "#"), __T(1399))), KEY(__T(1400)), BKG([["!Γ"], "~A"], [[["!Γ", "+A"], "#"]]), KEY(__T(1401)), BKG([["~A"], "#"], [[["~A"], "A"]]), LEAN(__T(1402))]),
      `${KEY("\\(\\neg A = A\\to \\bot\\)", "(assuming \\(A\\) leads to a contradiction)")}
       <p>In natural deduction, \\(\\neg A\\) is an abbreviation of \\(A\\to \\bot\\). So no new rule is needed for negation.</p>
       ${BKFS(BKF(BKN(`→I<sup class="sc">1</sup>`, [BKD(BKA("A", 1), "#")], "~A"), "Introducing ¬ (just →I)"), BKF(BKN("→E", [BKP("~A"), BKP("A")], "#"), "Eliminating ¬ (just →E)"))}
       <!--pg-->
       <p><b>The goal-changing reading</b>:</p>
       ${KEY("To prove the goal \\(\\neg A\\), add \\(A\\) to the hypotheses and prove \\(\\bot\\)")}
       ${BKG([["!Γ"], "~A"], [[["!Γ", "+A"], "#"]])}
       ${KEY("To prove the goal \\(\\bot\\) using the hypothesis \\(\\neg A\\), it suffices to prove \\(A\\)")}
       ${BKG([["~A"], "#"], [[["~A"], "A"]])}
       ${LEAN("intro h / apply h")}
       <!--pg-->
       <p><b>In the game</b>: tapping the \\(\\neg\\) of door \\(\\neg A\\) takes you into a room holding \\(A\\) as a key, and the door becomes \\(\\bot\\).</p>
       <p>The key \\(\\neg A\\) is a key that produces \\(\\bot\\) when you insert \\(A\\).</p>`) },
    { id: "ex", h: () => L1(__T(1403), "Example: contraposition"), body: () => L1(
      __T(1404, [BKF(BKN(`→I<sup class="sc">1</sup>`, [BKN(`→I<sup class="sc">2</sup>`, [BKN("→E", [BKA("~Q", 1), BKN("→E", [BKL("P->Q"), BKA("P", 2)], "Q")], "#")], "~P")], "~Q->~P"))]),
      `${BKF(BKN(`→I<sup class="sc">1</sup>`, [BKN(`→I<sup class="sc">2</sup>`, [BKN("→E", [BKA("~Q", 1), BKN("→E", [BKL("P->Q"), BKA("P", 2)], "Q")], "#")], "~P")], "~Q->~P"))}
       <ol class="bk-steps"><li>Goal \\(\\neg Q\\to \\neg P\\): add \\(\\neg Q\\) to the hypotheses \\(({\\to}\\mathrm{I}^{1})\\).</li><li>Goal \\(\\neg P\\): add \\(P\\) to the hypotheses; the goal becomes \\(\\bot ({\\to}\\mathrm{I}^{2})\\).</li><li>Goal \\(\\bot\\): using the hypothesis \\(\\neg Q\\), the goal becomes \\(Q\\, ({\\to}\\mathrm{E})\\).</li><li>Goal \\(Q\\): using the hypothesis \\(P\\to Q\\), the goal becomes \\(P\\, ({\\to}\\mathrm{E})\\). \\(P\\) is a hypothesis.</li></ol>`) },
    { id: "raa", h: () => L1(__T(1405), "Caution: introducing negation vs. reductio"), body: () => L1(
      __T(1406, [KEY(__T(1407), __T(1408))]),
      `${KEY("Introducing \\(\\neg\\): assuming \\(A\\) gives a contradiction \\(\\Rightarrow \\neg A\\) (a rule of this level)", "Reductio: assuming \\(\\neg A\\) gives a contradiction \\(\\Rightarrow A\\) (a new rule of the next level)")}
       <p>The two look alike, but they are different rules. Reductio (RAA) first appears on the next level.</p>
       <p>Without reductio you cannot, for example, derive \\(A\\) from \\(\\neg \\neg A\\). You examine this difference in detail in the Hidden Level "Magic Doors".</p>`) },
    { id: "more", h: () => L1(__T(1351), "A little more"), body: () => L1(
      __T(1409, [bkRefs(["gentzen", "glivenko", "vandalen", "tvd"])]),
      `<details><summary>Intuitionistic and classical logic</summary><p>The system made of the rules so far (introduction and elimination for \\(\\land\\), \\(\\to\\), \\(\\lor\\), \\(\\bot\\)) is natural deduction for <b>intuitionistic logic</b> (the propositional part of Gentzen's NJ). Adding reductio gives <b>classical logic</b> (NK), the logic of ordinary mathematics.</p><p>In propositional logic, \\(A\\) is provable classically if and only if \\(\\neg \\neg A\\) is provable intuitionistically (Glivenko's theorem). That the double negation of the excluded middle, \\(\\neg \\neg (P\\lor \\neg P)\\), could be proved without reductio in 4-5 is one instance.</p></details>
       <details><summary>References</summary>${bkRefs(["gentzen", "glivenko", "vandalen", "tvd"])}</details>`) },
  ] },
};
// 書庫の蔵書：一つの書庫に、何冊かの書物を置く（各書物は、元の本の節を選んで組み直したもの）
const bkPick = (k, ids) => ids.map(id => { const sx = BOOK_SRC[k].sections.find(x => x.id === id); if (!sx) throw new Error("book section " + k + "/" + id); return sx; });
const BOOKS = {
  nd: { color: "#7a3b2e", title: () => L1(__T(1410), "The Book of Natural Deduction"), desc: () => L1(__T(1411), "What natural deduction is, proof trees, sequents, hypotheses and goals"),
    sections: [...bkPick("1-1", ["what", "hyp"]),
      { id: "more", h: () => L1(__T(1351), "A little more"), body: () => L1(
        __T(1412, [bkRefs(["gentzen", "prawitz", "vandalen", "bekki", "ono"])]),
        `<details><summary>How sequents are written</summary><p>In \\(\\Gamma \\vdash A\\), \\(\\Gamma\\) is a collection of assumptions; order and repetition do not matter.</p><p>When \\(\\Gamma\\) is empty \\((\\vdash A)\\), \\(A\\) is provable without assumptions, that is, \\(A\\) is \\(a\\) <b>theorem</b>.</p></details>
         <details><summary>References</summary>${bkRefs(["gentzen", "prawitz", "vandalen", "bekki", "ono"])}</details>`) }] },
  and: { color: "#2f5d8a", title: () => L1(__T(1413), "The Book of Conjunction"), desc: () => L1(__T(1414), "Introduction and elimination of \"and\" ∧"),
    sections: [...bkPick("1-1", ["andI", "andE"]),
      { id: "ex", h: () => L1(__T(1349), "Example: from \\(P\\land Q\\) to \\(Q\\land P\\)"), body: () => L1(
        __T(1415, [BKF(BKN("∧I", [BKN("∧E", [BKL("P&Q")], "Q"), BKN("∧E", [BKL("P&Q")], "P")], "Q&P"))]),
        `${BKF(BKN("∧I", [BKN("∧E", [BKL("P&Q")], "Q"), BKN("∧E", [BKL("P&Q")], "P")], "Q&P"))}
         <p>A proof tree of \\(P\\land Q \\vdash Q\\land P\\) (1-2 "Taking Keys Apart").</p>
         <ol class="bk-steps"><li>Split the goal \\(Q\\land P\\) into the two goals \\(Q\\) and \\(P\\) by \\({\\land}\\mathrm{I}\\).</li><li>Take \\(Q\\) and \\(P\\) out of the hypothesis \\(P\\land Q\\) by \\({\\land}\\mathrm{E}\\).</li><li>Close each goal with the \\(Q\\) and \\(P\\) taken out.</li></ol>`) }] },
  imp1: { color: "#5c7a3a", title: () => L1(__T(1416), "The Book of Implication, Vol. I"), desc: () => L1(__T(1417), "Introducing \"implies\" →, and discharging assumptions"),
    sections: [...bkPick("1-1", ["impI", "ex"]),
      { id: "more", h: () => L1(__T(1351), "A little more"), body: () => L1(
        __T(1418, [BKF(BKN(`→I<sup class="sc">1</sup>`, [BKN(`→I<sup class="sc">2</sup>`, [BKA("P", 1)], "Q->P")], "P->(Q->P)"))]),
        `<details><summary>An assumption may be used any number of times, even zero</summary><p>In \\({\\to}\\mathrm{I}\\), the assumption \\(A\\) may be used any number of times, or not at all.</p><p>For example, \\(P\\to (Q\\to P)\\) can be proved without ever using the assumption \\(Q\\) (→I² "discharges" the unused assumption \\(Q\\)). In the game too, you may open a door without using the key you received in a room.</p>${BKF(BKN(`→I<sup class="sc">1</sup>`, [BKN(`→I<sup class="sc">2</sup>`, [BKA("P", 1)], "Q->P")], "P->(Q->P)"))}</details>
         <p>The elimination rule \\({\\to}\\mathrm{E}\\) is explained in "The Book of Implication, Vol. II" in the archive of the next level.</p>`) }] },
  imp2: { color: "#4a6a2e", title: () => L1(__T(1419), "The Book of Implication, Vol. II"), desc: () => L1(__T(1420), "Eliminating →, nested assumptions, proofs as functions"), sections: bkPick("2-1", ["impE", "nest", "func", "more"]) },
  or: { color: "#7b4a8a", title: () => L1(__T(1367), "The Book of Disjunction"), desc: () => L1(__T(1421), "The rules of \"or\" ∨, and case analysis"), sections: bkPick("3-1", ["orI", "orE", "ex", "tip", "more"]) },
  bot: { color: "#a33b3b", title: () => L1(__T(1386), "The Book of Contradiction"), desc: () => L1(__T(1422), "Contradiction ⊥ and the principle of explosion"), sections: bkPick("4-1", ["bot", "botE"]) },
  neg: { color: "#3b6e6a", title: () => L1(__T(1423), "The Book of Negation"), desc: () => L1(__T(1424), "Negation ¬ as \"implies contradiction\", and how it differs from reductio"), sections: bkPick("4-1", ["neg", "ex", "raa", "more"]) },
};
const ARCHIVES = { "1-1": ["nd", "and", "imp1"], "2-1": ["imp2"], "3-1": ["or"], "4-1": ["bot", "neg"] }; // 書庫（層の最初のステージの元の番号）ごとの蔵書
// 規則名から、それを解説する書物のページへ
const RULE_BOOK = { "仮定": ["nd", "hyp"], "∧I": ["and", "andI"], "∧E": ["and", "andE"], "→I": ["imp1", "impI"], "→E": ["imp2", "impE"], "∨I": ["or", "orI"], "∨E": ["or", "orE"], "⊥E": ["bot", "botE"] };
// 第 5 層以降の書物
const bkTable = (head, rows) => `<div class="bk-tw"><table class="bk-table"><thead><tr>${head.map(h => `<th>${h}</th>`).join("")}</tr></thead><tbody>${rows.map(r => `<tr>${r.map(c => `<td>${c}</td>`).join("")}</tr>`).join("")}</tbody></table></div>`;
const TVJ = v => L1(v ? __T(876) : __T(877), v ? "T" : "F");
Object.assign(BK_REF, {
  dyckhoff92: `R. Dyckhoff, "Contraction-free sequent calculi for intuitionistic logic", <i>Journal of Symbolic Logic</i> 57(3) (1992), 795–807. <a href="https://doi.org/10.2307/2275431" target="_blank" rel="noopener">doi:10.2307/2275431</a>`,
  hilbertbernays39: `D. Hilbert and P. Bernays, <i>Grundlagen der Mathematik II</i>, Springer, 1939.`,
  lob55: `M. H. Löb, "Solution of a problem of Leon Henkin", <i>Journal of Symbolic Logic</i> 20(2) (1955), 115–118. <a href="https://doi.org/10.2307/2266895" target="_blank" rel="noopener">doi:10.2307/2266895</a>`,
  feferman60: `S. Feferman, "Arithmetization of metamathematics in a general setting", <i>Fundamenta Mathematicae</i> 49 (1960), 35–92.`,
  arai90: `T. Arai, "Derivability conditions on Rosser's provability predicates", <i>Notre Dame Journal of Formal Logic</i> 31(4) (1990), 487–497.`,
  kurahashi20: `T. Kurahashi, "A note on derivability conditions", <i>Journal of Symbolic Logic</i> 85 (2020). <a href="https://arxiv.org/abs/1902.00895" target="_blank" rel="noopener">arXiv:1902.00895</a>`,
  kurahashi19: `T. Kurahashi, "Rosser provability and the second incompleteness theorem". <a href="https://arxiv.org/abs/1902.06863" target="_blank" rel="noopener">arXiv:1902.06863</a>`,
  robinson65: `J. A. Robinson, "A machine-oriented logic based on the resolution principle", <i>Journal of the ACM</i> 12(1) (1965), 23–41. <a href="https://doi.org/10.1145/321250.321253" target="_blank" rel="noopener">doi:10.1145/321250.321253</a>`,
  martelli82: `A. Martelli and U. Montanari, "An efficient unification algorithm", <i>ACM Transactions on Programming Languages and Systems</i> 4(2) (1982), 258–282. <a href="https://doi.org/10.1145/357162.357169" target="_blank" rel="noopener">doi:10.1145/357162.357169</a>`,
  baadernipkow: `F. Baader and T. Nipkow, <i>Term Rewriting and All That</i>, Cambridge University Press, 1998. <a href="https://doi.org/10.1017/CBO9781139172752" target="_blank" rel="noopener">doi:10.1017/CBO9781139172752</a>`,
  baadersnyder: `F. Baader and W. Snyder, "Unification theory", in A. Robinson and A. Voronkov (eds.), <i>Handbook of Automated Reasoning</i>, Vol. I, Elsevier, 2001, 445–533.`,
  huet75: `G. Huet, "A unification algorithm for typed λ-calculus", <i>Theoretical Computer Science</i> 1(1) (1975), 27–57. <a href="https://doi.org/10.1016/0304-3975(75)90011-0" target="_blank" rel="noopener">doi:10.1016/0304-3975(75)90011-0</a>`,
  goldfarb81: `W. D. Goldfarb, "The undecidability of the second-order unification problem", <i>Theoretical Computer Science</i> 13(2) (1981), 225–230. <a href="https://doi.org/10.1016/0304-3975(81)90040-2" target="_blank" rel="noopener">doi:10.1016/0304-3975(81)90040-2</a>`,
  miller91: `D. Miller, "A logic programming language with lambda-abstraction, function variables, and simple unification", <i>Journal of Logic and Computation</i> 1(4) (1991), 497–536. <a href="https://doi.org/10.1093/logcom/1.4.497" target="_blank" rel="noopener">doi:10.1093/logcom/1.4.497</a>`,
  knuthbendix70: `D. E. Knuth and P. B. Bendix, "Simple word problems in universal algebras", in J. Leech (ed.), <i>Computational Problems in Abstract Algebra</i>, Pergamon Press, 1970, 263–297.`,
  tpil4: __T(1425),
  post: `E. L. Post, "Introduction to a general theory of elementary propositions", <i>American Journal of Mathematics</i> 43 (1921), 163–185.`,
  kripke: `S. A. Kripke, "Semantical analysis of intuitionistic logic I", in J. N. Crossley and M. A. E. Dummett (eds.), <i>Formal Systems and Recursive Functions</i>, North-Holland, 1965, 92–130.`,
  godel30: `K. Gödel, "Die Vollständigkeit der Axiome des logischen Funktionenkalküls", <i>Monatshefte für Mathematik und Physik</i> 37 (1930), 349–360.`,
  godel33: `K. Gödel, "Eine Interpretation des intuitionistischen Aussagenkalküls", <i>Ergebnisse eines mathematischen Kolloquiums</i> 4 (1933), 39–40.`,
  mckt: `J. C. C. McKinsey and A. Tarski, "Some theorems about the sentential calculi of Lewis and Heyting", <i>Journal of Symbolic Logic</i> 13 (1948), 1–15.`,
  godel31: `K. Gödel, "Über formal unentscheidbare Sätze der Principia Mathematica und verwandter Systeme I", <i>Monatshefte für Mathematik und Physik</i> 38 (1931), 173–198.`,
  church: `A. Church, "A note on the Entscheidungsproblem", <i>Journal of Symbolic Logic</i> 1 (1936), 40–41.`,
  turing: `A. M. Turing, "On computable numbers, with an application to the Entscheidungsproblem", <i>Proceedings of the London Mathematical Society</i> (2) 42 (1937), 230–265.`,
  peano: `G. Peano, <i>Arithmetices principia, nova methodo exposita</i>, Bocca, Torino, 1889.`,
  dedekind: `R. Dedekind, <i>Was sind und was sollen die Zahlen?</i>, Vieweg, Braunschweig, 1888.`,
});
Object.assign(BOOKS, {
  /* ---------- 第 5 層：背理法の魔法 ---------- */
  raa: { color: "#6d2b6b", title: () => L1(__T(1426), "The Book of Reductio"), desc: () => L1(__T(1427), "The reductio rule (RAA) and how it differs from introducing negation"), sections: [
    { id: "rule", h: () => L1(__T(1428), "Reductio ad absurdum (RAA)"), body: () => L1(
      __T(1429, [BKF(BKN(`RAA<sup class="sc">1</sup>`, [BKD(BKA("~A", 1), "#")], "A")), KEY(__T(1430)), KEY(__T(1431), __T(1432)), BKG([["!Γ"], "A"], [[["!Γ", "+~A"], "#"]]), LEAN(__T(1433))]),
      `${BKF(BKN(`RAA<sup class="sc">1</sup>`, [BKD(BKA("~A", 1), "#")], "A"))}
       ${KEY("If assuming not \\(A\\) leads to a contradiction, \\(A\\) is proved")}
       <p>The assumption \\([\\neg A]^{1}\\) is discharged by the RAA line.</p>
       <p>This is exactly the reasoning called "proof by contradiction" in ordinary mathematics.</p>
       <!--pg-->
       <p><b>The goal-changing reading</b>:</p>
       ${KEY("Any goal \\(A\\) can be replaced by", "\"add \\(\\neg A\\) to the hypotheses and prove the contradiction \\(\\bot\\)\"")}
       ${BKG([["!Γ"], "A"], [[["!Γ", "+~A"], "#"]])}
       <p>Unlike introducing negation, it can be used even when the goal has no \\(\\neg\\).</p>
       ${LEAN("apply Classical.byContradiction / intro h")}
       <!--pg-->
       <p><b>In the game</b>: casting the "Reductio spell" on a door takes you into a magic room holding \\(\\neg A\\) as a key, and the door becomes \\(\\bot\\).</p>
       <p>The key \\(\\neg A\\) of the magic room cannot be used outside it.</p>
       <p>It is especially useful when no direct way is in sight (when the goal is atomic, or when you cannot decide the side of \\(a \\lor\\)).</p>`) },
    { id: "vs", h: () => L1(__T(1434), "Introducing negation vs. reductio"), body: () => L1(
      __T(1435, [KEY(__T(1436), __T(1437))]),
      `${KEY("Introducing negation: assume \\(A \\to\\) contradiction \\(\\Rightarrow \\neg A\\)", "Reductio: assume \\(\\neg A \\to\\) contradiction \\(\\Rightarrow A\\)")}
       <p>Introducing negation is just \\({\\to}\\mathrm{I}\\), the introduction of "implies", and can be used without reductio.</p>
       <p>Reductio is a different, new rule.</p>
       <p>With reductio, \\(A\\) can be derived from \\(\\neg \\neg A\\) (5-1). Conversely, without reductio, \\(\\neg \\neg A\\to A\\) cannot be proved (the Hidden Level "Magic Doors").</p>`) },
    { id: "ex", h: () => L1(__T(1438), "Example: double negation elimination"), body: () => L1(
      __T(1439, [BKF(BKN(`RAA<sup class="sc">1</sup>`, [BKN("→E", [BKL("~~P"), BKA("~P", 1)], "#")], "P"))]),
      `${BKF(BKN(`RAA<sup class="sc">1</sup>`, [BKN("→E", [BKL("~~P"), BKA("~P", 1)], "#")], "P"))}
       <p>A proof tree of \\(\\neg \\neg P \\vdash P\\).</p>
       <ol class="bk-steps"><li>Goal \\(P\\): add \\(\\neg P\\) to the hypotheses; the goal becomes \\(\\bot\\) (RAA).</li><li>Goal \\(\\bot\\): using the hypothesis \\(\\neg \\neg P\\), the goal becomes \\(\\neg P\\, ({\\to}\\mathrm{E})\\).</li><li>The goal \\(\\neg P\\) is a hypothesis.</li></ol>`) },
    { id: "more", h: () => L1(__T(1351), "A little more"), body: () => L1(
      __T(1440, [bkRefs(["vandalen", "tvd"])]),
      `<details><summary>Reductio is "non-constructive"</summary><p>With reductio you can show, for example, that "something satisfying the condition exists" without constructing an example, by "assuming none exists leads to a contradiction".</p><p>The position that does not accept such reasoning is intuitionism (constructivism). Intuitionism does accept deriving a contradiction from \\(A\\) and concluding \\(\\neg A\\) (negation introduction). What it does not accept is concluding \\(A\\) merely because \\(\\neg A\\) leads to a contradiction.</p></details>
       <details><summary>References</summary>${bkRefs(["vandalen", "tvd"])}</details>`) },
  ] },
  classic: { color: "#8a5a2a", title: () => L1(__T(1441), "The Book of Classical Logic"), desc: () => L1(__T(1442), "Excluded middle, double negation elimination and reductio are equally strong"), sections: [
    { id: "lem", h: () => L1(__T(169), "The law of excluded middle"), body: () => L1(
      __T(1443, [KEY("\\(P \\lor \\neg P\\)", __T(1444)), KEY(__T(1445))]),
      `${KEY("\\(P \\lor \\neg P\\)", "(either \\(P\\) or not \\(P\\) holds)")}
       <p>With reductio it can be proved without any assumptions (5-2).</p>
       <!--pg-->
       <ol class="bk-steps"><li>Goal \\(P\\lor \\neg P\\): assume \\(\\neg (P\\lor \\neg P)\\); the goal becomes \\(\\bot\\) (RAA).</li><li>Goal \\(\\bot\\): using the hypothesis \\(\\neg (P\\lor \\neg P)\\), the goal becomes \\(P\\lor \\neg P\\, ({\\to}\\mathrm{E})\\).</li><li>Choose the right side; the goal is \\(\\neg P\\). Assume \\(P\\); the goal becomes \\(\\bot\\).</li><li>Use the hypothesis \\(\\neg (P\\lor \\neg P)\\) once more; the goal becomes \\(P\\lor \\neg P\\). Choose the left side, and \\(P\\) is a hypothesis.</li></ol>
       ${KEY("The key point: the same hypothesis \\(\\neg (P\\lor \\neg P)\\) is used twice")}`) },
    { id: "equiv", h: () => L1(__T(1446), "Three principles of equal strength"), body: () => L1(
      __T(1447, [KEY(__T(1448))]),
      `${KEY("Reductio \\(\\iff\\) double negation elimination \\(\\iff\\) excluded middle")}
       <p>Adding any one of them, as a principle usable for every proposition, to the rules without reductio (intuitionistic logic) lets you derive the other two.</p>
       <ul class="help-list"><li>With excluded middle, splitting into "the case \\(P\\)" and "the case \\(\\neg P\\)" gives \\(P\\) from \\(\\neg \\neg P\\) (5-5).</li><li>With double negation elimination, \\(P\\lor \\neg P\\) follows from \\(\\neg \\neg (P\\lor \\neg P)\\), which can be proved without reductio (5-6).</li></ul>
       <p>Adding any of them gives <b>classical logic</b>, the logic of ordinary mathematics.</p>
       <p>This is about principles usable "for every proposition". The individual formulas are not equivalent: for example, \\(P \\lor \\neg P\\) does not follow from \\(\\neg\\neg P \\to P\\) without reductio. Even in the second example above, double negation elimination is used for a different formula, \\(P\\lor\\neg P\\).</p>`) },
    { id: "laws", h: () => L1(__T(1449), "Laws that hold in classical logic"), body: () => L1(
      __T(1450, [KEY("\\(P\\to Q \\vdash \\neg P\\lor Q\\)", "\\(\\neg Q\\to \\neg P \\vdash P\\to Q\\)", "\\(\\neg (P\\land Q) \\vdash \\neg P\\lor \\neg Q\\)", __T(1451))]),
      `${KEY("\\(P\\to Q \\vdash \\neg P\\lor Q\\)", "\\(\\neg Q\\to \\neg P \\vdash P\\to Q\\)", "\\(\\neg (P\\land Q) \\vdash \\neg P\\lor \\neg Q\\)", "\\(\\vdash ((P\\to Q)\\to P)\\to P\\) (Peirce's law)")}
       <p>Each of these can be proved with reductio and cannot be proved without it (5-3, 5-4, 5-7, 6-5).</p>
       <p>On the other hand, the other direction of De Morgan's law, \\(\\neg P\\lor \\neg Q \\vdash \\neg (P\\land Q)\\), can be proved without reductio.</p>`) },
    { id: "more", h: () => L1(__T(1351), "A little more"), body: () => L1(
      __T(1452, [bkRefs(["vandalen", "tvd"])]),
      `<details><summary>An example of a non-constructive proof</summary><p>"There are irrational numbers \\(a\\) and \\(b\\) such that \\(a^{b}\\) is rational" can be shown with excluded middle as follows.</p><p>Let \\(b = \\sqrt{2}\\). If \\(\\sqrt{2}^{\\sqrt{2}}\\) is rational, take \\(a = \\sqrt{2}\\); if it is irrational, take \\(a = \\sqrt{2}^{\\sqrt{2}}\\), so that \\(a^{b} = \\sqrt{2}^{2} = 2\\).</p><p>Existence has been shown without deciding which case holds. Today, by the Gelfond–Schneider theorem (1934), \\(\\sqrt{2}^{\\sqrt{2}}\\) is known to be transcendental (hence irrational).</p></details>
       <details><summary>References</summary>${bkRefs(["vandalen", "tvd"])}</details>`) },
  ] },
  /* ---------- 第 6 層：真偽の石盤 ---------- */
  truth: { color: "#a07a22", title: () => L1(__T(1453), "The Book of Truth Values"), desc: () => L1(__T(1454), "Truth assignments, truth tables, and what a valid inference is"), sections: [
    { id: "assign", h: () => L1(__T(1455), "Truth assignments"), body: () => L1(
      __T(1456, [KEY(__T(1457)), bkTable(["\\(A\\)", "\\(B\\)", "\\(A\\land B\\)", "\\(A\\lor B\\)", "\\(A\\to B\\)"], [[true, true], [true, false], [false, true], [false, false]].map(([a, b]) => [TVJ(a), TVJ(b), TVJ(a && b), TVJ(a || b), TVJ(!a || b)])), KEY(__T(1458), __T(1459))]),
      `${KEY("Decide, for each atomic proposition \\(P\\), \\(Q\\), \\(\\dots\\), whether it is true or false")}
       <p>This is called \\(a\\) <b>truth assignment</b>.</p>
       <p>Once it is fixed, the truth of compound formulas can be computed from a table for each connective (the truth table).</p>
       <!--pg-->
       ${bkTable(["\\(A\\)", "\\(B\\)", "\\(A\\land B\\)", "\\(A\\lor B\\)", "\\(A\\to B\\)"], [[true, true], [true, false], [false, true], [false, false]].map(([a, b]) => [TVJ(a), TVJ(b), TVJ(a && b), TVJ(a || b), TVJ(!a || b)]))}
       ${KEY("\\(\\neg A\\) is the opposite of \\(A\\); \\(\\bot\\) is always false", "\\(A\\to B\\) is false only when \\(A\\) is true and \\(B\\) is false")}`) },
    { id: "valid", h: () => L1(__T(1460), "What a valid inference is"), body: () => L1(
      __T(1461, [KEY(__T(1462)), KEY(__T(1463))]),
      `${KEY("Under every assignment making all hypotheses true, the conclusion is true as well")}
       <p>Then \\(A\\) is said to <b>follow semantically</b> from \\(\\Gamma\\) (logical consequence), written \\(\\Gamma \\models A\\).</p>
       <!--pg-->
       ${KEY("A counterexample \\(=\\) an assignment making all hypotheses true and the conclusion false")}
       <p>For example, in \\(P\\to Q \\vdash Q\\to P\\) of 6-1, making \\(P\\) false and \\(Q\\) true makes the hypothesis \\(P\\to Q\\) true and the conclusion \\(Q\\to P\\) false.</p>
       <p>A single counterexample shows that the inference is not valid.</p>`) },
    { id: "game", h: () => L1(__T(1464), "Using the stone board"), body: () => L1(
      __T(1465),
      `<p><b>In the game</b>: press the buttons of the atomic propositions on the stone board to switch between true, false and unknown (in the story, a white stone stands for true and a black stone for false).</p>
       <p>When all hypotheses are true and the goal is false, the counterexample is complete.</p>
       <p>You can check the computation with "See as a tree" (the tree of subformulas) and "See the reasons" (a list of why each formula is true or false).</p>`) },
    { id: "more", h: () => L1(__T(1351), "A little more"), body: () => L1(
      __T(1466),
      `<details><summary>It can be decided mechanically</summary><p>With \\(n\\) atomic propositions there are only \\(2^{n}\\) assignments.</p><p>Checking them all decides mechanically whether \\(\\Gamma \\models A\\) (the decidability of propositional logic).</p></details>`) },
  ] },
  sound: { color: "#4f6a8a", title: () => L1(__T(1467), "The Book of Soundness and Completeness"), desc: () => L1(__T(1468), "How provability and validity are related"), sections: [
    { id: "sound", h: () => L1(__T(1469), "The soundness theorem"), body: () => L1(
      __T(1470, [KEY(__T(1471), __T(1472)), KEY(__T(1473))]),
      `${KEY("If \\(\\Gamma \\vdash A\\) then \\(\\Gamma \\models A\\)", "(a provable inference is valid under every assignment)")}
       <p>The idea: by induction on the proof tree, check that each step's conclusion has the property "if all the hypotheses still open at that point are true, the conclusion is true". For rules that discharge hypotheses (→I, ∨E), note that the set of hypotheses differs before and after the discharge.</p>
       <p>For example, in \\({\\to}\\mathrm{E}\\), if \\(A\\to B\\) and \\(A\\) are true, \\(B\\) is true by the truth table. This is built up by induction on the size of the proof tree.</p>
       <!--pg-->
       ${KEY("A single counterexample rules out a proof")}
       <p>This is the contrapositive of soundness: if \\(\\Gamma \\not\\models A\\) then \\(\\Gamma \\nvdash A\\).</p>
       <p>Making counterexamples on Level 6 uses this theorem to show that something cannot be proved.</p>`) },
    { id: "complete", h: () => L1(__T(1474), "The completeness theorem"), body: () => L1(
      __T(1475, [KEY(__T(1476), __T(1477)), KEY(__T(1478))]),
      `${KEY("If \\(\\Gamma \\models A\\) then \\(\\Gamma \\vdash A\\)", "(a valid inference can always be proved)")}
       <p>For the rules including reductio (classical propositional logic), the converse of soundness holds too.</p>
       <p>Together with soundness, "provable" and "valid under every assignment" become the same thing.</p>
       <!--pg-->
       ${KEY("Every inference has either a proof or a counterexample")}
       <p>That is why, in the judging hall (6-5), you can choose for each door whether to prove it or to make a counterexample.</p>
       <p>Without reductio (intuitionistic logic), however, things differ: \\(P\\lor \\neg P\\) is true under every assignment but cannot be proved without reductio. The counterexamples for that are the Kripke models of the Hidden Level.</p>`) },
    { id: "deadend", h: () => L1(__T(1479), "Why dead ends can be recognized"), body: () => L1(
      __T(1480, [KEY(__T(1481))]),
      `<p>Let \\(\\Gamma\\) be the keys of a room and \\(A\\) the door. A "dead end" means \\(\\Gamma \\nvdash A\\): the door cannot be opened from the keys at hand, however you proceed.</p>
       ${KEY("In propositional logic, whether \\(\\Gamma \\vdash A\\) can always be decided")}
       <p>With reductio, the completeness theorem makes \\(\\Gamma \\vdash A\\) the same as \\(\\Gamma \\models A\\), so checking every truth assignment tells. Without reductio (intuitionistic logic), counterexamples can be found among finite Kripke models, and a proof search that always terminates is also known (Dyckhoff, 1992).</p>
       <p>That is why the game can tell you about dead ends up to Level 6. In predicate logic there is no mechanical method to decide provability (Church, Turing, 1936), so from Level 7 on there are no such notices.</p>`) },
    { id: "more", h: () => L1(__T(1351), "A little more"), body: () => L1(
      __T(1482, [bkRefs(["post", "vandalen", "bekki", "dyckhoff92"])]),
      `<details><summary>References</summary><p>The completeness of propositional logic was shown by Post (1921).</p>${bkRefs(["post", "vandalen", "bekki", "dyckhoff92"])}</details>`) },
  ] },
  /* ---------- 隠し層：魔法の扉 ---------- */
  kripke: { color: "#3b5f8a", title: () => L1(__T(1483), "The Book of Kripke Models"), desc: () => L1(__T(1484), "The semantics of intuitionistic logic: definitions, soundness, completeness"), sections: [
    { id: "def", h: () => L1(__T(1485), "Definition of a Kripke model"), body: () => L1(
      String.raw`<p>背理法を使わない論理（直観主義命題論理）には、真理値の割り当てとは別の意味論があります。</p>
       ${KEY(String.raw`クリプキモデル \(\mathcal{K} = (W, \le, V)\)`)}
       <ul class="help-list"><li>\(W\)：空でない集合。その元を<b>世界</b>（知識の状態）と呼ぶ。</li><li>\(\le\)：\(W\) 上の半順序（反射的・推移的・反対称的）。\(w \le v\) は「\(v\) は \(w\) の未来」と読む。</li><li>\(V\)：各世界 \(w\) に、そこで成り立つと分かっている原子命題の集合 \(V(w)\) を対応させる写像。</li></ul>
       <!--pg-->
       <p>ただし \(V\) には、次の<b>単調性</b>を課します。</p>
       ${KEY(String.raw`\(w \le v \;\Longrightarrow\; V(w) \subseteq V(v)\)`)}
       <p>一度分かった原子命題は、未来でも分かったままである、という意味です。</p>
       <p>（\(\le\) は前順序でもかまいません。反対称性は、以下の議論では使いません。）</p>`,
      String.raw`<p>The logic without reductio (intuitionistic propositional logic) has a semantics different from truth assignments.</p>
       ${KEY(String.raw`A Kripke model \(\mathcal{K} = (W, \le, V)\)`)}
       <ul class="help-list"><li>\(W\): a nonempty set, whose elements are called <b>worlds</b> (states of knowledge).</li><li>\(\le\): a partial order on \(W\) (reflexive, transitive, antisymmetric). \(w \le v\) is read "\(v\) is a future of \(w\)".</li><li>\(V\): a map assigning to each world \(w\) the set \(V(w)\) of atomic propositions known to hold there.</li></ul>
       <!--pg-->
       <p>\(V\) is required to be <b>monotone</b>:</p>
       ${KEY(String.raw`\(w \le v \;\Longrightarrow\; V(w) \subseteq V(v)\)`)}
       <p>An atomic proposition, once known, remains known in the future.</p>
       <p>(\(\le\) may also be just a preorder; antisymmetry is not used below.)</p>`) },
    { id: "force", h: () => L1(__T(1486), "The forcing relation ⊩"), body: () => L1(
      String.raw`<p>世界 \(w\) で式 \(A\) が成り立つことを \(w \Vdash A\) と書き（「\(w\) は \(A\) を強制する」）、式の形に沿って帰納的に定義します。</p>
       ${bkTable([__T(1487), String.raw`\(w \Vdash \cdots\) の定義`], [[String.raw`\(p\)（原子命題）`, String.raw`\(p \in V(w)\)`], [String.raw`\(A \land B\)`, String.raw`\(w \Vdash A\) かつ \(w \Vdash B\)`], [String.raw`\(A \lor B\)`, String.raw`\(w \Vdash A\) または \(w \Vdash B\)`], [String.raw`\(A \to B\)`, String.raw`すべての \(v \ge w\) について、\(v \Vdash A\) ならば \(v \Vdash B\)`], [String.raw`\(\bot\)`, __T(1488)]])}
       <p>\(\neg A\) は \(A \to \bot\) の略記なので、次のようになります。</p>
       ${KEY(String.raw`\(w \Vdash \neg A \iff \forall v \ge w\; (v \nVdash A)\)`)}
       <!--pg-->
       ${KEY(__T(1489))}
       <p>「\(A\) ならば \(B\) が分かっている」とは、「いまだけでなく、将来 \(A\) が分かったときにはいつでも、\(B\) も分かる」ということです。</p>
       <p>「\(\neg A\) が分かっている」とは、「将来にわたって \(A\) は決して分からない」ということで、単に「いま \(A\) が分かっていない」こととは違います。</p>`,
      String.raw`<p>That the formula \(A\) holds at the world \(w\) is written \(w \Vdash A\) ("\(w\) forces \(A\)") and is defined inductively on the form of the formula.</p>
       ${bkTable(["Formula", String.raw`Definition of \(w \Vdash \cdots\)`], [[String.raw`\(p\) (atomic)`, String.raw`\(p \in V(w)\)`], [String.raw`\(A \land B\)`, String.raw`\(w \Vdash A\) and \(w \Vdash B\)`], [String.raw`\(A \lor B\)`, String.raw`\(w \Vdash A\) or \(w \Vdash B\)`], [String.raw`\(A \to B\)`, String.raw`for every \(v \ge w\), if \(v \Vdash A\) then \(v \Vdash B\)`], [String.raw`\(\bot\)`, "never holds"]])}
       <p>Since \(\neg A\) abbreviates \(A \to \bot\):</p>
       ${KEY(String.raw`\(w \Vdash \neg A \iff \forall v \ge w\; (v \nVdash A)\)`)}
       <!--pg-->
       ${KEY("The point: only → and ¬ look at all future worlds")}
       <p>"\(A\) implies \(B\) is known" means "not only now, but whenever \(A\) becomes known in the future, \(B\) is known too".</p>
       <p>"\(\neg A\) is known" means "\(A\) will never become known", which differs from merely "\(A\) is not known now".</p>`) },
    { id: "persist", h: () => L1(__T(1490), "The persistence lemma"), body: () => L1(
      String.raw`${KEY(String.raw`<b>補題</b>　\(w \Vdash A\) かつ \(w \le v\) ならば、\(v \Vdash A\)`)}
       <p><b>証明</b>（式 \(A\) の構成についての帰納法）</p>
       <ul class="help-list"><li>原子命題：\(V\) の単調性そのもの。</li><li>\(\land\)、\(\lor\)：帰納法の仮定から、そのまま従う。</li><li>\(\bot\)：\(w \Vdash \bot\) となることはないので、主張は自明に成り立つ。</li><li>\(A \to B\)：\(u \ge v\) とすると、推移律から \(u \ge w\)。\(w \Vdash A \to B\) の定義から、\(u \Vdash A\) ならば \(u \Vdash B\)。よって \(v \Vdash A \to B\)。\(\square\)</li></ul>
       <p>\(\to\) の定義で「未来すべて」を見ているのは、この補題が成り立つようにするためです。</p>`,
      String.raw`${KEY(String.raw`<b>Lemma</b>　If \(w \Vdash A\) and \(w \le v\), then \(v \Vdash A\)`)}
       <p><b>Proof</b> (by induction on the construction of \(A\))</p>
       <ul class="help-list"><li>Atomic: this is exactly the monotonicity of \(V\).</li><li>\(\land\), \(\lor\): immediate from the induction hypothesis.</li><li>\(\bot\): \(w \Vdash \bot\) never holds, so the claim holds vacuously.</li><li>\(A \to B\): let \(u \ge v\). By transitivity \(u \ge w\), so by the definition of \(w \Vdash A \to B\), if \(u \Vdash A\) then \(u \Vdash B\). Hence \(v \Vdash A \to B\). \(\square\)</li></ul>
       <p>The definition of \(\to\) looks at "all futures" precisely so that this lemma holds.</p>`) },
    { id: "sound", h: () => L1(__T(1469), "The soundness theorem"), body: () => L1(
      String.raw`<p>\(\Gamma\) から \(A\) が<b>クリプキ意味論的に導かれる</b>（\(\Gamma \models_{K} A\)）とは、すべてのクリプキモデルのすべての世界 \(w\) で、\(\Gamma\) の式をすべて強制するなら \(A\) も強制することとします。</p>
       ${KEY(String.raw`<b>定理</b>　背理法なしで \(\Gamma \vdash A\) ならば、\(\Gamma \models_{K} A\)`)}
       <!--pg-->
       <p><b>証明の要点</b>（証明図についての帰納法）：各推論規則が「前提が意味論的に正しいなら、結論も正しい」を保つことを確かめます。</p>
       <p>\(\to\)I の場合：\(\Gamma, A \models_{K} B\) を仮定し、\(w \Vdash \Gamma\) とします。\(v \ge w\) かつ \(v \Vdash A\) なら、持続性の補題から \(v \Vdash \Gamma\) なので、\(v \Vdash B\)。よって \(w \Vdash A \to B\)。</p>
       <p>\(\to\)E は定義で \(v = w\) とすれば従い、\(\lor\)E は「\(w \Vdash A\) の場合と \(w \Vdash B\) の場合」に分ければ従います。\(\bot\)E は前提が成り立たないので自明です。</p>
       <!--pg-->
       ${KEY(String.raw`<b>系</b>　\(\Gamma\) を強制し \(A\) を強制しない世界があれば、背理法なしでは \(\Gamma \vdash A\) は証明できない`)}
       <p>背理法 RAA は、この意味で健全ではありません。次の例で見るように、\(\neg\neg p\) を強制するのに \(p\) を強制しない世界があるからです。</p>`,
      String.raw`<p>We say that \(A\) <b>follows in the Kripke semantics</b> from \(\Gamma\) (\(\Gamma \models_{K} A\)) if, at every world \(w\) of every Kripke model, whenever \(w\) forces all formulas of \(\Gamma\) it forces \(A\).</p>
       ${KEY(String.raw`<b>Theorem</b>　If \(\Gamma \vdash A\) without reductio, then \(\Gamma \models_{K} A\)`)}
       <!--pg-->
       <p><b>Outline of the proof</b> (by induction on the proof tree): check that each inference rule preserves "if the premises are semantically valid, so is the conclusion".</p>
       <p>The case \(\to\)I: assume \(\Gamma, A \models_{K} B\) and \(w \Vdash \Gamma\). If \(v \ge w\) and \(v \Vdash A\), then \(v \Vdash \Gamma\) by the persistence lemma, so \(v \Vdash B\). Hence \(w \Vdash A \to B\).</p>
       <p>\(\to\)E follows by taking \(v = w\) in the definition, and \(\lor\)E by splitting into the cases \(w \Vdash A\) and \(w \Vdash B\). \(\bot\)E holds vacuously, since its premise never holds.</p>
       <!--pg-->
       ${KEY(String.raw`<b>Corollary</b>　If some world forces \(\Gamma\) but not \(A\), then \(\Gamma \vdash A\) cannot be proved without reductio`)}
       <p>Reductio (RAA) is not sound in this sense: as the next examples show, there is a world forcing \(\neg\neg p\) but not \(p\).</p>`) },
    { id: "ex", h: () => L1(__T(1491), "Examples: classical laws that fail"), body: () => L1(
      String.raw`${KEY(String.raw`\(W = \{w_0, w_1\},\quad w_0 \le w_1,\quad V(w_0) = \emptyset,\quad V(w_1) = \{p\}\)`)}
       <ul class="help-list"><li>\(w_0 \nVdash p\)。また \(w_1 \Vdash p\) なので、\(w_0 \nVdash \neg p\)。よって <b>\(w_0 \nVdash p \lor \neg p\)</b>（排中律）。</li><li>\(w_0\) でも \(w_1\) でも \(\neg p\) は成り立たないので、\(w_0 \Vdash \neg\neg p\)。しかし \(w_0 \nVdash p\)。よって <b>\(w_0 \nVdash \neg\neg p \to p\)</b>（二重否定除去）。</li><li>\(q\) をどこでも偽にすると、\(w_0\) も \(w_1\) も \(p \to q\) を強制しないので、\(w_0 \Vdash (p \to q) \to p\)。しかし \(w_0 \nVdash p\)。よって<b>パースの法則も \(w_0\) で成り立たない</b>。</li></ul>
       <!--pg-->
       <p>枝分かれするモデル：\(w_0 \le w_1\)、\(w_0 \le w_2\)、\(V(w_1) = \{p\}\)、\(V(w_2) = \{q\}\)（\(V(w_0) = \emptyset\)）。</p>
       <p>\(p\) と \(q\) を両方強制する世界はないので、\(w_0 \Vdash \neg(p \land q)\)。一方、\(w_1 \Vdash p\) から \(w_0 \nVdash \neg p\)、\(w_2 \Vdash q\) から \(w_0 \nVdash \neg q\)。</p>
       ${KEY(String.raw`よって \(\neg(p \land q) \nvdash \neg p \lor \neg q\)（背理法なしでは）`)}`,
      String.raw`${KEY(String.raw`\(W = \{w_0, w_1\},\quad w_0 \le w_1,\quad V(w_0) = \emptyset,\quad V(w_1) = \{p\}\)`)}
       <ul class="help-list"><li>\(w_0 \nVdash p\). Since \(w_1 \Vdash p\), also \(w_0 \nVdash \neg p\). Hence <b>\(w_0 \nVdash p \lor \neg p\)</b> (excluded middle).</li><li>\(\neg p\) holds neither at \(w_0\) nor at \(w_1\), so \(w_0 \Vdash \neg\neg p\); but \(w_0 \nVdash p\). Hence <b>\(w_0 \nVdash \neg\neg p \to p\)</b> (double negation elimination).</li><li>Make \(q\) false everywhere. Neither \(w_0\) nor \(w_1\) forces \(p \to q\), so \(w_0 \Vdash (p \to q) \to p\); but \(w_0 \nVdash p\). Hence <b>Peirce's law fails at \(w_0\)</b>.</li></ul>
       <!--pg-->
       <p>A branching model: \(w_0 \le w_1\), \(w_0 \le w_2\), \(V(w_1) = \{p\}\), \(V(w_2) = \{q\}\) (\(V(w_0) = \emptyset\)).</p>
       <p>No world forces both \(p\) and \(q\), so \(w_0 \Vdash \neg(p \land q)\). On the other hand, \(w_1 \Vdash p\) gives \(w_0 \nVdash \neg p\), and \(w_2 \Vdash q\) gives \(w_0 \nVdash \neg q\).</p>
       ${KEY(String.raw`Hence \(\neg(p \land q) \nvdash \neg p \lor \neg q\) (without reductio)`)}`) },
    { id: "complete", h: () => L1(__T(1474), "The completeness theorem"), body: () => L1(
      String.raw`${KEY(String.raw`<b>定理</b>（クリプキ、1965）　\(\Gamma \models_{K} A\) ならば、背理法なしで \(\Gamma \vdash A\)`)}
       <p>健全性と合わせると、背理法なしで証明できることと、すべてのクリプキモデルで正しいことは同値です。</p>
       <!--pg-->
       <p><b>証明の考え方</b>（標準モデル）：\(\Gamma \nvdash A\) と仮定して、反例のモデルを作ります。</p>
       <ul class="help-list"><li>世界：\(\Gamma\) を含み、\(A\) を導かない「素な理論」（導出について閉じていて、\(B \lor C\) を含むなら \(B\) か \(C\) を含む、矛盾しない式の集合）。</li><li>\(\le\)：集合の包含 \(\subseteq\)。\(V(w)\)：\(w\) に含まれる原子命題。</li><li><b>真理補題</b>：\(w \Vdash B \iff B \in w\)。</li></ul>
       <p>\(\Gamma \nvdash A\) なら、\(\Gamma\) を含み \(A\) を含まない素な理論が存在するので（リンデンバウム型の補題）、そこが反例の世界になります。</p>
       <!--pg-->
       ${KEY(__T(1492))}
       <p>命題論理では、反例が存在するなら有限のモデルの中に存在します。このため、直観主義命題論理の証明可能性は、機械的に判定できます。</p>`,
      String.raw`${KEY(String.raw`<b>Theorem</b> (Kripke, 1965)　If \(\Gamma \models_{K} A\), then \(\Gamma \vdash A\) without reductio`)}
       <p>Together with soundness: provable without reductio and valid in every Kripke model are equivalent.</p>
       <!--pg-->
       <p><b>Idea of the proof</b> (the canonical model): assuming \(\Gamma \nvdash A\), build a model that is a counterexample.</p>
       <ul class="help-list"><li>Worlds: "prime theories" containing \(\Gamma\) and not deriving \(A\) (consistent sets of formulas closed under derivation that, whenever they contain \(B \lor C\), contain \(B\) or \(C\)).</li><li>\(\le\): set inclusion \(\subseteq\). \(V(w)\): the atomic propositions in \(w\).</li><li><b>Truth lemma</b>: \(w \Vdash B \iff B \in w\).</li></ul>
       <p>If \(\Gamma \nvdash A\), there is a prime theory containing \(\Gamma\) but not \(A\) (a Lindenbaum-type lemma), and it is a world that is a counterexample.</p>
       <!--pg-->
       ${KEY("Finite model property: counterexamples can be found among models with finitely many worlds")}
       <p>In propositional logic, if there is a counterexample, there is a finite one. Hence provability in intuitionistic propositional logic can be decided mechanically.</p>`) },
    { id: "rel", h: () => L1(__T(1493), "Relation to classical logic"), body: () => L1(
      String.raw`${KEY(__T(1494))}
       <p>世界が一つなら、「未来すべて」はその世界だけなので、\(\to\) と \(\neg\) の定義は真理値表と一致します。</p>
       <p>したがって、クリプキ意味論で正しい式は、古典論理でも正しい式です。逆は成り立たず、排中律などがその例です。</p>
       <!--pg-->
       <p>クリプキ意味論は、もともと様相論理のために考えられたものです。ゲーデル（1933）とマッキンゼー＝タルスキ（1948）は、直観主義論理が様相論理 S4 に翻訳できることを示しました（式の構造に沿って訳します。原子命題 \(p\) は \(\Box p\) に、\(A \to B\) は \(\Box(A' \to B')\) に。ここで \(A'\)、\(B'\) は \(A\)、\(B\) を訳したもので、\(\land\) と \(\lor\) は訳した式どうしをそのまま結びます）。直観主義論理のクリプキモデルは、S4 の反射的・推移的なクリプキモデルにあたります。</p>`,
      String.raw`${KEY("A Kripke model with a single world = a truth assignment")}
       <p>With one world, "all futures" is just that world, so the definitions of \(\to\) and \(\neg\) agree with the truth tables.</p>
       <p>Hence every formula valid in the Kripke semantics is classically valid. The converse fails, excluded middle being an example.</p>
       <!--pg-->
       <p>Kripke semantics was originally devised for modal logic. Gödel (1933) and McKinsey–Tarski (1948) showed that intuitionistic logic translates into the modal logic S4 (translating along the structure of formulas: an atom \(p\) becomes \(\Box p\), and \(A \to B\) becomes \(\Box(A' \to B')\), where \(A'\), \(B'\) are the translations of \(A\), \(B\); \(\land\) and \(\lor\) simply join the translated parts). Kripke models of intuitionistic logic correspond to the reflexive, transitive Kripke models of S4.</p>`) },
    { id: "game", h: () => L1(__T(1495), "How the game shows it"), body: () => L1(
      String.raw`${bkTable([__T(1496), __T(1497)], [[String.raw`世界 \(w \in W\)`, __T(1498)], [String.raw`\(w \le v\)`, __T(1499)], [String.raw`\(V(w)\)`, __T(1500)], [String.raw`\(w \Vdash A\)`, String.raw`その階で式 \(A\) が光る`]])}
       <p>反証のステージでは、仮定をすべて光らせ、目標を光らせない階を作れば、系によって「背理法なしでは証明できない」ことが示されます。</p>`,
      String.raw`${bkTable(["Mathematics", "Game"], [[String.raw`a world \(w \in W\)`, "a floor of the tower"], [String.raw`\(w \le v\)`, "upward stairs (higher floors are later)"], [String.raw`\(V(w)\)`, "the lights lit on that floor"], [String.raw`\(w \Vdash A\)`, String.raw`the formula \(A\) is lit on that floor`]])}
       <p>In a refutation stage, making a floor where all hypotheses are lit and the goal is not shows, by the corollary, that it cannot be proved without reductio.</p>`) },
    { id: "more", h: () => L1(__T(1501), "References"), body: () => bkRefs(["kripke", "godel33", "mckt", "tvd", "vandalen"]) },
  ] },
  /* ---------- 第 7 層：住人の街（∀） ---------- */
  forall: { color: "#2f6f5e", title: () => L1(__T(1502), "The Book of Universality"), desc: () => L1(__T(1503), "The rules of \"for all\" ∀ and the eigenvariable condition"), sections: [
    { id: "allI", h: () => L1(__T(1504), "Universal introduction \\({\\forall}\\mathrm{I}\\)"), body: () => L1(
      __T(1505, [BKF(BKN("∀I", [BKP("A(a)")], "!x.A(x)")), KEY(__T(1506)), KEY(__T(1507), __T(1508)), BKG([["!Γ"], "!x.A(x)"], [[["!Γ"], "A(a)"]], __T(1509)), LEAN("intro a")]),
      `${BKF(BKN("∀I", [BKP("A(a)")], "!x.A(x)"))}
       ${KEY("If \\(A(a)\\) is proved for an arbitrary object \\(a\\) (a resident in the game), \\(\\forall x\\, A(x)\\) is proved")}
       <p>Here \\(a\\) must be a new name that appears neither in the assumptions nor in the conclusion.</p>
       <p>This is called the <b>eigenvariable condition</b>.</p>
       <!--pg-->
       <p><b>The goal-changing reading</b>:</p>
       ${KEY("To prove the goal \\(\\forall x\\, A(x)\\),", "take a new object \\(a\\) and prove \\(A(a)\\)")}
       ${BKG([["!Γ"], "!x.A(x)"], [[["!Γ"], "A(a)"]], "\\(a\\) is a new name not appearing in \\(\\Gamma\\)")}
       <p>This is "let \\(a\\) be arbitrary" in mathematical proofs.</p>
       ${LEAN("intro a")}
       <!--pg-->
       <p><b>In the game</b>: tapping the \\(\\forall\\) of a door takes you into a new room with an arbitrary resident \\(a\\), and the door becomes \\(A(a)\\).</p>
       <p>A resident born in a room cannot be taken out of it; this is the eigenvariable condition.</p>`) },
    { id: "eigen", h: () => L1(__T(1510), "Why the eigenvariable condition is needed"), body: () => L1(
      __T(1511, [KEY(__T(1512))]),
      `${KEY("An \"arbitrary object\" is one about which nothing is known")}
       <p>If \\({\\forall}\\mathrm{I}\\) could be used on an object \\(a\\) with a hypothesis \\(P(a)\\), we would get the wrong inference "\\(a\\) is \\(P\\), so every object is \\(P\\)".</p>
       <p>Only when nothing is assumed about \\(a\\) can a proof about \\(a\\) count as a proof about everyone.</p>`) },
    { id: "allE", h: () => L1(__T(1513), "Universal elimination \\({\\forall}\\mathrm{E}\\)"), body: () => L1(
      __T(1514, [BKF(BKN("∀E", [BKP("!x.A(x)")], "A(t)")), KEY(__T(1515)), KEY(__T(1516)), BKG([["!x.A(x)"], "!C"], [[["!x.A(x)", "+A(t)"], "!C"]]), LEAN("have h' := h t")]),
      `${BKF(BKN("∀E", [BKP("!x.A(x)")], "A(t)"))}
       ${KEY("From \\(\\forall x\\, A(x)\\), \\(A(t)\\) follows for any term \\(t\\)")}
       <p>\\(A(t)\\) is the formula \\(A(x)\\) with \\(x\\) replaced by \\(t\\) (substitution).</p>
       <!--pg-->
       <p><b>The hypothesis-adding reading</b>:</p>
       ${KEY("From the hypothesis \\(\\forall x\\, A(x)\\), you get a new hypothesis \\(A(t)\\) for any term \\(t\\) you like")}
       ${BKG([["!x.A(x)"], "!C"], [[["!x.A(x)", "+A(t)"], "!C"]])}
       ${LEAN("have h' := h t")}
       <p><b>In the game</b>: tap the \\(\\forall\\) of a key and choose the resident to plug in.</p>`) },
    { id: "ex", h: () => L1(__T(1517), "Example: with the same object"), body: () => L1(
      __T(1518, [BKF(BKN("∀I", [BKN("→E", [BKN("∀E", [BKL("!x.(P(x)->Q(x))")], "P(a)->Q(a)"), BKN("∀E", [BKL("!x.P(x)")], "P(a)")], "Q(a)")], "!x.Q(x)"))]),
      `${BKF(BKN("∀I", [BKN("→E", [BKN("∀E", [BKL("!x.(P(x)->Q(x))")], "P(a)->Q(a)"), BKN("∀E", [BKL("!x.P(x)")], "P(a)")], "Q(a)")], "!x.Q(x)"))}
       <ol class="bk-steps"><li>Goal \\(\\forall x\\, Q(x)\\): take a new object \\(a\\); the goal becomes \\(Q(a)\\, ({\\forall}\\mathrm{I})\\).</li><li>Plug the same \\(a\\) into both hypotheses \\(({\\forall}\\mathrm{E})\\).</li><li>From \\(P(a)\\to Q(a)\\) and \\(P(a)\\), get \\(Q(a)\\, ({\\to}\\mathrm{E})\\).</li></ol>`) },
    { id: "more", h: () => L1(__T(1351), "A little more"), body: () => L1(
      __T(1519, [bkRefs(["vandalen", "bekki"])]),
      `<details><summary>Names of bound variables</summary><p>\\(\\forall x\\, A(x)\\) and \\(\\forall y\\, A(y)\\) mean the same (7-2). The name of a variable bound by \\(\\forall\\) can be changed freely.</p><p>In a substitution \\(A(t)\\), however, care is needed so that variables in \\(t\\) are not captured by another \\(\\forall\\).</p></details>
       <details><summary>References</summary>${bkRefs(["vandalen", "bekki"])}</details>`) },
  ] },
  /* ---------- 第 8 層：存在の扉（∃） ---------- */
  exists: { color: "#8a4a2a", title: () => L1(__T(1520), "The Book of Existence"), desc: () => L1(__T(1521), "The rules of \"there exists\" ∃ and witnesses"), sections: [
    { id: "exI", h: () => L1(__T(1522), "Existential introduction \\({\\exists}\\mathrm{I}\\)"), body: () => L1(
      __T(1523, [BKF(BKN("∃I", [BKP("A(t)")], "?x.A(x)")), KEY(__T(1524)), KEY(__T(1525)), BKG([["!Γ"], "?x.A(x)"], [[["!Γ"], "A(t)"]]), LEAN("refine ⟨t, ?_⟩")]),
      `${BKF(BKN("∃I", [BKP("A(t)")], "?x.A(x)"))}
       ${KEY("If \\(A(t)\\) is proved for some term \\(t\\), \\(\\exists x\\, A(x)\\) is proved")}
       <p>This \\(t\\) is called \\(a\\) <b>witness</b>.</p>
       <!--pg-->
       <p><b>The goal-changing reading</b>:</p>
       ${KEY("To prove the goal \\(\\exists x\\, A(x)\\), choose a witness \\(t\\) and prove \\(A(t)\\)")}
       ${BKG([["!Γ"], "?x.A(x)"], [[["!Γ"], "A(t)"]])}
       <p>A wrong choice of witness leads to a dead end, so this is a choice that can lead to a dead end.</p>
       ${LEAN("refine ⟨t, ?_⟩")}
       <p><b>In the game</b>: tap the \\(\\exists\\) of a door and choose the resident who will be the witness.</p>`) },
    { id: "exE", h: () => L1(__T(1526), "Existential elimination \\({\\exists}\\mathrm{E}\\)"), body: () => L1(
      __T(1527, [BKF(BKN(`∃E<sup class="sc">1</sup>`, [BKP("?x.A(x)"), BKD(BKA("A(a)", 1), "C")], "C")), KEY(__T(1528)), KEY(__T(1529)), BKG([["!Γ", "?x.A(x)"], "!C"], [[["!Γ", "+A(a)"], "!C"]], __T(1530)), LEAN("obtain ⟨a, h'⟩ := h")]),
      `${BKF(BKN(`∃E<sup class="sc">1</sup>`, [BKP("?x.A(x)"), BKD(BKA("A(a)", 1), "C")], "C"))}
       ${KEY("If \\(\\exists x\\, A(x)\\) holds and \\(C\\) can be proved by assuming \\(A(a)\\), \\(C\\) is proved")}
       <p>\\(a\\) is a new name and must not appear in \\(C\\) or in the other hypotheses (the eigenvariable condition).</p>
       <!--pg-->
       <p><b>The hypothesis-adding reading</b>:</p>
       ${KEY("From the hypothesis \\(\\exists x\\, A(x)\\): \"call that object (resident) \\(a\\) and add the hypothesis \\(A(a)\\)\"")}
       ${BKG([["!Γ", "?x.A(x)"], "!C"], [[["!Γ", "+A(a)"], "!C"]], "\\(a\\) is a new name, not appearing in \\(C\\)")}
       <p>This is "take such an \\(a\\)" in mathematical proofs.</p>
       ${LEAN("obtain ⟨a, h'⟩ := h")}
       <p><b>In the game</b>: tapping the \\(\\exists\\) of a key takes you into a room with that resident \\(a\\), who cannot be taken out of the room. When you leave the room, the hypothesis \\(A(a)\\) is discharged by the \\({\\exists}\\mathrm{E}\\) line (numbered like \\([A(a)]^{1}\\) in the proof tree).</p>`) },
    { id: "ex", h: () => L1(__T(1531), "Example: the order of quantifiers"), body: () => L1(
      __T(1532, [KEY("\\(\\exists y\\forall x\\, R(x,y) \\vdash \\forall x\\exists y\\, R(x,y)\\)")]),
      `${KEY("\\(\\exists y\\forall x\\, R(x,y) \\vdash \\forall x\\exists y\\, R(x,y)\\)")}
       <ol class="bk-steps"><li>Goal \\(\\forall x\\exists y\\, R(x,y)\\): take an object \\(a\\); the goal becomes \\(\\exists y\\, R(a,y)\\, ({\\forall}\\mathrm{I})\\).</li><li>From the hypothesis \\(\\exists y\\forall x\\, R(x,y)\\), get an object \\(b\\) and the hypothesis \\(\\forall x\\, R(x,b)\\, ({\\exists}\\mathrm{E})\\).</li><li>Choose \\(b\\) as the witness; the goal becomes \\(R(a,b)\\, ({\\exists}\\mathrm{I})\\).</li><li>Plug \\(a\\) into the hypothesis \\(\\forall x\\, R(x,b)\\, ({\\forall}\\mathrm{E})\\).</li></ol>
       <p>If there is a common partner \\(b\\) for everyone, everyone has a partner. The converse is not valid (see the Book of Structures).</p>`) },
    { id: "more", h: () => L1(__T(1351), "A little more"), body: () => L1(
      __T(1533, [bkRefs(["vandalen", "bekki"])]),
      `<details><summary>Breaking the eigenvariable condition</summary><p>If \\({\\exists}\\mathrm{E}\\) let \\(a\\) be carried out into the conclusion, we would get the wrong inference \\(\\exists x\\, P(x) \\vdash P(a)\\). From "someone is \\(P\\)" we cannot conclude that a particular \\(a\\) is \\(P\\).</p></details>
       <details><summary>References</summary>${bkRefs(["vandalen", "bekki"])}</details>`) },
  ] },
  /* ---------- 第 9 層：魔法と量化子 ---------- */
  qclass: { color: "#6b2f5a", title: () => L1(__T(1534), "The Book of Quantifiers and Reductio"), desc: () => L1(__T(1535), "The duality of quantifiers and the drinker paradox"), sections: [
    { id: "dual", h: () => L1(__T(1536), "Duality of quantifiers"), body: () => L1(
      __T(1537, [KEY("\\(\\neg \\forall x\\, A(x) \\iff \\exists x \\neg A(x)\\)", "\\(\\neg \\exists x\\, A(x) \\iff \\forall x \\neg A(x)\\)")]),
      `${KEY("\\(\\neg \\forall x\\, A(x) \\iff \\exists x \\neg A(x)\\)", "\\(\\neg \\exists x\\, A(x) \\iff \\forall x \\neg A(x)\\)")}
       <p>The lower line can be shown in both directions without reductio (8-7 is one of them).</p>
       <p>The "\\(\\Rightarrow\\)" of the upper line (9-3) needs reductio.</p>
       <p>Picking out a concrete object that is not \\(P\\), from "not everyone is \\(P\\)", is not constructive.</p>`) },
    { id: "drinker", h: () => L1(__T(233), "The drinker paradox"), body: () => L1(
      __T(1538, [KEY("\\(\\exists x\\, (P(x) \\to \\forall y\\, P(y))\\)", __T(1539)), KEY(__T(1540))]),
      `${KEY("\\(\\exists x\\, (P(x) \\to \\forall y\\, P(y))\\)", "(there is someone such that, if they drink, everyone drinks)")}
       <p>It sounds strange, but it is valid in classical logic (9-6).</p>
       <!--pg-->
       <p>The idea: if everyone drinks, anyone can be the witness.</p>
       <p>Otherwise, take someone who does not drink as the witness; then "if they drink" is false, so the whole is true.</p>
       ${KEY("Only the existence of a witness is shown, without knowing which case holds")}
       <p>The proof needs reductio and the fact that there is at least one object (the domain is nonempty).</p>`) },
    { id: "barber", h: () => L1(__T(522), "The key smith's key"), body: () => L1(
      __T(1541, [KEY("\\(\\forall x\\, (\\neg K(x,x) \\to K(p,x)) \\vdash K(p,p)\\)"), KEY("\\(\\forall x\\, (S(p,x) \\leftrightarrow \\neg S(x,x))\\)"), KEY("\\(\\vdash \\neg \\exists y \\forall x\\, (S(y,x) \\leftrightarrow \\neg S(x,x))\\)"), KEY(__T(1542), __T(1543), __T(1544))]),
      `${KEY("\\(\\forall x\\, (\\neg K(x,x) \\to K(p,x)) \\vdash K(p,p)\\)")}
       <p>If "the key smith \\(p\\) makes the keys of everyone who does not make their own key", the key smith makes his own key (9-1).</p>
       <ol class="bk-steps"><li>Goal \\(K(p,p)\\): assume \\(\\neg K(p,p)\\); the goal becomes \\(\\bot\\) (RAA).</li><li>Plug \\(p\\) into the \\(x\\) of the hypothesis: \\(\\neg K(p,p) \\to K(p,p)\\, ({\\forall}\\mathrm{E})\\).</li><li>From \\(\\neg K(p,p)\\) we get \\(K(p,p)\\), contradicting \\(\\neg K(p,p)\\).</li></ol>
       <!--pg-->
       <p><b>Relation to the barber paradox</b>: this problem is the famous barber paradox with only one direction.</p>
       <p>In the barber paradox, "the village barber shaves <b>all</b> those, and <b>only</b> those, who do not shave themselves". Writing \\(S(x, y)\\) for "\\(x\\) shaves \\(y\\)", it reads:</p>
       ${KEY("\\(\\forall x\\, (S(p,x) \\leftrightarrow \\neg S(x,x))\\)")}
       <p>Plugging \\(p\\) into \\(x\\) gives \\(S(p,p) \\leftrightarrow \\neg S(p,p)\\), a contradiction. So such a barber cannot exist.</p>
       ${KEY("\\(\\vdash \\neg \\exists y \\forall x\\, (S(y,x) \\leftrightarrow \\neg S(x,x))\\)")}
       <!--pg-->
       <p>The rule of 9-1 has only the "\\(\\to\\)" direction, so there is no contradiction, and \\(K(p,p)\\) follows. With only the converse \\(\\forall x\\, (K(p,x) \\to \\neg K(x,x))\\) (the key smith does not make the keys of those who make their own), \\(\\neg K(p,p)\\) follows in the same way.</p>
       ${KEY("Only \\(\\to\\): \\(K(p,p)\\) follows", "Only ←: \\(\\neg K(p,p)\\) follows", "\\(\\leftrightarrow\\) (both): contradiction")}
       <p>Only when both are combined does a contradiction arise. Getting \\(K(p,p)\\) from the \\(\\to\\) direction alone needs reductio, while the ← direction and the contradiction from \\(\\leftrightarrow\\) can be derived without reductio.</p>
       <p>This argument has the same shape as <b>Russell's paradox</b> about the set \\(\\{x \\mid x \\notin x\\}\\) (the collection of all sets that are not members of themselves); the barber paradox is known as a familiar retelling of it.</p>`) },
    { id: "more", h: () => L1(__T(1351), "A little more"), body: () => L1(
      __T(1545, [bkRefs(["vandalen"])]),
      `<details><summary>The domain is nonempty</summary><p>In the predicate logic of this game, we agree that the domain is nonempty (in the game: there is at least one resident). The drinker paradox and "\\(\\forall x\\, P(x)\\) implies \\(\\exists x\\, P(x)\\)" hold under this agreement.</p></details>
       <details><summary>References</summary>${bkRefs(["vandalen"])}</details>`) },
  ] },
  /* ---------- 第 10 層：構造の鑑定 ---------- */
  struct: { color: "#2a5d6e", title: () => L1(__T(1546), "The Book of Structures"), desc: () => L1(__T(1547), "Structures (model towns in the game) and counterexamples in predicate logic"), sections: [
    { id: "struct", h: () => L1(__T(1548), "What a structure is"), body: () => L1(
      __T(1549, [KEY(__T(1550), __T(1551)), KEY(__T(1552), __T(1553))]),
      `${KEY("A collection of elements (the domain; residents in the game) + a table for each predicate and relation", "(who is \\(P\\), who R's whom)")}
       <p>This is called \\(a\\) <b>structure</b>. Once a structure is fixed, the truth of formulas with \\(\\forall\\) and \\(\\exists\\) is determined.</p>
       ${KEY("\\(\\forall x\\, A(x)\\): \\(A\\) is true for every element", "\\(\\exists x\\, A(x)\\): \\(A\\) is true for at least one element")}
       <!--pg-->
       <p>Example (10-1): take two elements, and make \\(P\\) true only for element 1.</p>
       <p>Then the hypothesis \\(\\exists x\\, P(x)\\) is true and the conclusion \\(\\forall x\\, P(x)\\) is false, so this is a counterexample to \\(\\exists x\\, P(x) \\vdash \\forall x\\, P(x)\\).</p>`) },
    { id: "order", h: () => L1(__T(1554), "The order of quantifiers, and counterexamples"), body: () => L1(
      __T(1555, [KEY(__T(1556), __T(1557))]),
      `${KEY("\\(\\forall x\\exists y\\, R(x,y)\\): everyone has a partner of their own", "\\(\\exists y\\forall x\\, R(x,y)\\): everyone has a common partner")}
       <p>The former follows from the latter (see the Book of Existence), but not the other way round.</p>
       <p>A counterexample: elements 1 and 2, with only \\(R(1,1)\\) and \\(R(2,2)\\) true. Every element has a partner (itself), but there is no common partner.</p>`) },
    { id: "complete", h: () => L1(__T(1558), "Soundness and completeness of predicate logic"), body: () => L1(
      __T(1559, [KEY("\\(\\Gamma \\vdash A \\iff \\Gamma \\models A\\)", __T(1560)), KEY(__T(1561))]),
      `${KEY("\\(\\Gamma \\vdash A \\iff \\Gamma \\models A\\)", "(provable \\(\\iff\\) valid in every structure)")}
       <p>By soundness, a single structure that is a counterexample rules out a proof.</p>
       <p>The converse is Gödel's <b>completeness theorem</b> (1930): every valid inference can be proved.</p>
       <!--pg-->
       <p>Unlike propositional logic, however, the domain may be infinite, so not all structures can be checked.</p>
       ${KEY("Provability in predicate logic cannot, in general, be decided mechanically")}
       <p>This was shown by Church and Turing in 1936.</p>`) },
    { id: "more", h: () => L1(__T(1351), "A little more"), body: () => L1(
      __T(1562, [bkRefs(["godel30", "church", "turing", "vandalen"])]),
      `<details><summary>References</summary>${bkRefs(["godel30", "church", "turing", "vandalen"])}</details>`) },
  ] },
  /* ---------- 第 11 層：集合の街 ---------- */
  set: { color: "#4a6fa5", title: () => L1(__T(1563), "The Book of Sets"), desc: () => L1(__T(1564), "Set operations and unfolding definitions"), sections: [
    { id: "def", h: () => L1(__T(1565), "Symbols defined by definitions"), body: () => L1(
      __T(1566, [KEY("\\(A \\subseteq B \\mathrel{:\\Leftrightarrow} \\forall x\\, (x \\in A \\to x \\in B)\\)", "\\(x \\in A \\cap B \\mathrel{:\\Leftrightarrow} x \\in A \\land x \\in B\\)", "\\(x \\in A \\cup B \\mathrel{:\\Leftrightarrow} x \\in A \\lor x \\in B\\)", "\\(x \\in A^{c} \\mathrel{:\\Leftrightarrow} \\neg (x \\in A)\\)")]),
      `${KEY("\\(A \\subseteq B \\mathrel{:\\Leftrightarrow} \\forall x\\, (x \\in A \\to x \\in B)\\)", "\\(x \\in A \\cap B \\mathrel{:\\Leftrightarrow} x \\in A \\land x \\in B\\)", "\\(x \\in A \\cup B \\mathrel{:\\Leftrightarrow} x \\in A \\lor x \\in B\\)", "\\(x \\in A^{c} \\mathrel{:\\Leftrightarrow} \\neg (x \\in A)\\)")}
       <p>\\(\\mathrel{:\\Leftrightarrow}\\) means "the left is an abbreviation of the right".</p>
       <p>No new inference rule is needed; just rewrite according to the definition (<b>unfolding the definition</b>).</p>
       <p>In this level, a set \\(A\\) is treated as the predicate "\\(x\\) belongs to \\(A\\)", and set notation is read in predicate logic. Set theory proper, which quantifies over sets themselves (ZF and so on), is not covered here.</p>`) },
    { id: "unfold", h: () => L1(__T(1567), "The goal-changing reading"), body: () => L1(
      __T(1568, [KEY(__T(1569), __T(1570)), BKG([["!Γ"], "A ⊆ B"], [[["!Γ"], "!x.(x ∈ A -> x ∈ B)"]], __T(1571)), BKG([["!Γ"], "!x.(x ∈ A -> x ∈ B)"], [[["!Γ", "+a ∈ A"], "a ∈ B"]], __T(1572)), LEAN(__T(1573))]),
      `${KEY("To prove the goal \\(A \\subseteq B\\),", "for an arbitrary \\(a\\), assume \\(a \\in A\\) and prove \\(a \\in B\\)")}
       ${BKG([["!Γ"], "A ⊆ B"], [[["!Γ"], "!x.(x ∈ A -> x ∈ B)"]], "Unfolding the definition")}
       ${BKG([["!Γ"], "!x.(x ∈ A -> x ∈ B)"], [[["!Γ", "+a ∈ A"], "a ∈ B"]], "\\({\\forall}\\mathrm{I}\\) and \\({\\to}\\mathrm{I}\\)")}
       <p>This is "let \\(a\\) be an arbitrary element of \\(A\\)" in mathematical proofs.</p>
       ${LEAN("show … / intro a ha")}
       <p><b>In the game</b>: tapping a symbol in a dotted frame rewrites it according to its definition.</p>`) },
    { id: "ex", h: () => L1(__T(1574), "Example: \\(A\\cap B \\subseteq A\\)"), body: () => L1(
      __T(1575),
      `<ol class="bk-steps"><li>Goal \\(A\\cap B \\subseteq A\\): unfold the definition; the goal becomes \\(\\forall x\\, (x \\in A\\cap B \\to x \\in A)\\).</li><li>Take an arbitrary \\(a\\) and assume \\(a \\in A\\cap B\\); the goal becomes \\(a \\in A\\, ({\\forall}\\mathrm{I}, {\\to}\\mathrm{I})\\).</li><li>Unfolding the hypothesis \\(a \\in A\\cap B\\) gives \\(a \\in A \\land a \\in B\\).</li><li>Take out \\(a \\in A\\) by \\({\\land}\\mathrm{E}\\).</li></ol>`) },
    { id: "more", h: () => L1(__T(1351), "A little more"), body: () => L1(
      __T(1576),
      `<details><summary>Complements and reductio</summary><p>\\((A\\cap B)^{c} \\subseteq A^{c}\\cup B^{c}\\) (11-5) has the same shape as De Morgan's law \\(\\neg (P\\land Q) \\vdash \\neg P\\lor \\neg Q\\), so it needs reductio. The other De Morgan law, \\((A\\cup B)^{c} \\subseteq A^{c}\\cap B^{c}\\), can be shown without reductio.</p></details>
       <details><summary>Nonempty sets and syllogisms</summary><p>\\(X \\neq \\emptyset\\) abbreviates \\(\\exists x\\, (x \\in X)\\). The traditional syllogism Darii, "every M is P, some S is M, therefore some S is P", can be written \\(M \\subseteq P,\\ S\\cap M \\neq \\emptyset \\vdash S\\cap P \\neq \\emptyset\\) (11-4). The syllogism of Level 7 (7-4) was the form with "every" throughout (Barbara).</p></details>
       <details><summary>Bounded quantifiers</summary><p>In mathematics, \\(\\forall x\\, (x \\in A \\to P(x))\\) is abbreviated as \\(\\forall x \\in A.\\, P(x)\\), and \\(\\exists x\\, (x \\in A \\land P(x))\\) as \\(\\exists x \\in A.\\, P(x)\\). Note that a \\(\\to\\) hides behind \\(\\forall\\), and a \\(\\land\\) behind \\(\\exists\\). In 11-6 and 11-7 you showed how negation passes through the quantifiers: \\(\\neg \\exists x \\in A.\\, P(x) \\vdash \\forall x \\in A.\\, \\neg P(x)\\) and \\(\\neg \\forall x \\in A.\\, P(x) \\vdash \\exists x \\in A.\\, \\neg P(x)\\). The latter needs reductio.</p></details>
       <details><summary>Sets in this game</summary><p>In this game, the sets \\(A\\), \\(B\\), \\(C\\) are taken as given, and \\(\\in\\) is used like a predicate. Accepting every collection as a set leads to a contradiction (Russell's paradox), so mathematics fixes how sets may be formed, in axiomatic set theory.</p></details>`) },
  ] },
  /* ---------- 第 12 層：等号の工房 ---------- */
  eq: { color: "#7a6a2a", title: () => L1(__T(1577), "The Book of Equality, Volume I"), desc: () => L1(__T(1578), "The rules of equality =, rewriting, and theorem cards"), sections: [
    { id: "eqI", h: () => L1(__T(1579), "Equality introduction \\({=}\\mathrm{I}\\)"), body: () => L1(
      __T(1580, [BKF(BKN("=I", [], "t = t")), KEY(__T(1581)), LEAN("rfl")]),
      `${BKF(BKN("=I", [], "t = t"))}
       ${KEY("For any term \\(t\\), \\(t = t\\) (reflexivity)")}
       <p>A rule with no premises.</p>
       ${LEAN("rfl")}
       <p><b>In the game</b>: tap the \\(=\\) of a door whose two sides are the same, and it opens.</p>`) },
    { id: "eqE", h: () => L1(__T(1582), "Equality elimination \\({=}\\mathrm{E}\\) (rewriting)"), body: () => L1(
      __T(1583, [BKF(BKN("=E", [BKP("s = t"), BKP("A(s)")], "A(t)")), KEY(__T(1584), __T(1585)), KEY(__T(1586), __T(1587)), BKG([["s = t"], "A(t)"], [[["s = t"], "A(s)"]]), LEAN("rewrite [← h]")]),
      `${BKF(BKN("=E", [BKP("s = t"), BKP("A(s)")], "A(t)"))}
       ${KEY("If \\(s = t\\) and \\(A(s)\\) are proved, \\(A(t)\\) is proved", "(equals may be replaced by equals)")}
       <!--pg-->
       <p><b>The goal-changing reading</b>:</p>
       ${KEY("To prove the goal \\(A(t)\\) using the equation \\(s = t\\),", "prove the goal \\(A(s)\\), with \\(t\\) rewritten to \\(s\\)")}
       ${BKG([["s = t"], "A(t)"], [[["s = t"], "A(s)"]])}
       ${LEAN("rewrite [← h]")}
       <p><b>In the game</b>: inserting an equation key into a door rewrites terms in the door. When several places can be rewritten, you can choose which.</p>
       <p>In this game, rewriting a door with the key \\(s = t\\) turns the door's \\(t\\) back into \\(s\\) (right side back to left side). This is the rule above read backward from the goal, and corresponds to Lean's <code>rw [← h]</code>; Lean's <code>rw [h]</code> instead rewrites the goal's \\(s\\) into \\(t\\). To use an equation the other way, flip it with symmetry (12-1).</p>`) },
    { id: "derived", h: () => L1(__T(1588), "Symmetry and transitivity"), body: () => L1(
      __T(1589, [KEY(__T(1590), __T(1591)), KEY(__T(1592))]),
      `${KEY("\\(s = t \\Rightarrow t = s\\) (symmetry)", "\\(s = t\\), \\(t = u \\Rightarrow s = u\\) (transitivity)")}
       <p>Both can be derived from \\({=}\\mathrm{I}\\) and \\({=}\\mathrm{E}\\) (12-1, 12-2).</p>
       <p>For example, symmetry: let \\(A(z)\\) be "\\(z = s\\)". Then \\(A(s)\\) is \\(s = s\\), which holds by \\({=}\\mathrm{I}\\). With \\(s = t\\) and \\({=}\\mathrm{E}\\) we get \\(A(t)\\), that is \\(t = s\\).</p>
       <!--pg-->
       ${KEY("A theorem once proved can be cited again and again (a \"theorem card\" in the game)")}
       <p>From 12-4 on, the symmetry and transitivity you proved can be used as theorem cards. This corresponds to citing a theorem already shown, in mathematics.</p>`) },
    { id: "maps", h: () => L1(__T(1593), "Injections and surjections"), body: () => L1(
      __T(1594, [KEY(__T(1595), __T(1596))]),
      `${KEY("Injective: \\(\\forall x\\forall y\\, (f(x) = f(y) \\to x = y)\\)", "Surjective: \\(\\forall y\\exists x\\, (f(x) = y)\\)")}
       <p>That compositions of injections are injections, and of surjections are surjections (12-5, 12-6), can be shown by combining the rules of \\(\\forall\\) and \\(\\exists\\).</p>
       <p>For surjections: for \\(z\\) take g's witness \\(y\\), then for \\(y\\) take f's witness \\(x\\) (∃E twice).</p>
       <p>In this game, all maps are functions within the same domain (the residents in the game); domain and codomain are not distinguished. For maps between different sets, the correspondence of domains and codomains has to be checked separately.</p>`) },
    { id: "more", h: () => L1(__T(1351), "A little more"), body: () => L1(
      __T(1597, [bkRefs(["vandalen"])]),
      `<details><summary>Functions and equality</summary><p>With \\({=}\\mathrm{E}\\), \\(f(s) = f(t)\\) also follows from \\(s = t\\) (12-3): applying the same operation to equals gives equals.</p></details>
       <details><summary>References</summary>${bkRefs(["vandalen"])}</details>`) },
  ] },
  /* ---------- 第 13 層：数学の街 ---------- */
  theory: { color: "#6a4a7a", title: () => L1(__T(1598), "The Book of Axioms and Theories"), desc: () => L1(__T(1599), "Mathematical theories with axioms as hypotheses"), sections: [
    { id: "axioms", h: () => L1(__T(1600), "What axioms are"), body: () => L1(
      __T(1601, [KEY(__T(1602)), KEY(__T(1603))]),
      `${KEY("Axioms \\(=\\) hypotheses that can always be used in the theory")}
       <p>Theories such as orders and groups are determined by a collection \\(T\\) of axioms. That \\(A\\) can be proved from \\(T\\) (\\(T \\vdash A\\)) is what it means for \\(A\\) to be a <b>theorem</b> of the theory.</p>
       <p>In this game, the axioms are given as the keys in the entrance hall (the story also calls them "laws").</p>
       ${KEY("Group axioms: \\((x\\cdot y)\\cdot z = x\\cdot (y\\cdot z)\\), \\(e\\cdot x = x\\), \\(x^{-1}\\cdot x = e\\)")}`) },
    { id: "group", h: () => L1(__T(1604), "Calculating in a group"), body: () => L1(
      __T(1605, [KEY("\\(b = e\\cdot b = (a^{-1}\\cdot a)\\cdot b = a^{-1}\\cdot (a\\cdot b)\\)", "\\(= a^{-1}\\cdot (a\\cdot c) = (a^{-1}\\cdot a)\\cdot c = e\\cdot c = c\\)")]),
      `<p>Left cancellation (14-2): the calculation showing \\(b = c\\) from \\(a\\cdot b = a\\cdot c\\). In the lemma workshop this is shown for all residents and becomes a theorem card.</p>
       ${KEY("\\(b = e\\cdot b = (a^{-1}\\cdot a)\\cdot b = a^{-1}\\cdot (a\\cdot b)\\)", "\\(= a^{-1}\\cdot (a\\cdot c) = (a^{-1}\\cdot a)\\cdot c = e\\cdot c = c\\)")}
       <p>Each equals sign is a rewrite \\(({=}\\mathrm{E})\\) by an instance of an axiom.</p>
       <p>In that stage, equations can be used in both directions.</p>
       <p>The first theorem derived from the axioms is that the identity is unique (13-1): \\(e = e\\cdot e' = e'\\).</p>`) },
    { id: "order", h: () => L1(__T(1606), "From the axioms of order"), body: () => L1(
      __T(1607, [KEY(__T(1608)), KEY(__T(1609))]),
      `${KEY("Antisymmetry: \\(\\forall x\\forall y\\, ((x \\le y \\land y \\le x) \\to x = y)\\)")}
       <p>If there are two greatest elements, each is below the other, so antisymmetry shows they are the same (13-2).</p>
       ${KEY("From irreflexivity \\(\\forall x\\, \\neg (x < x)\\) and transitivity: asymmetry \\(\\forall x\\forall y\\, (x < y \\to \\neg (y < x))\\)")}
       <p>Assuming \\(x < y\\) and \\(y < x\\), transitivity gives \\(x < x\\), contradicting irreflexivity (13-3). It combines introducing ¬ (\\(\\to\\)I) with \\(\\forall\\)E.</p>`) },
    { id: "more", h: () => L1(__T(1351), "A little more"), body: () => L1(
      __T(1610),
      `<details><summary>What cannot be proved</summary><p>That something cannot be proved from the axioms is shown by a structure satisfying all the axioms but not the formula. This is treated on Level 16, "Mirror of Axioms".</p></details>`) },
  ] },
  /* ---------- 第 14 層：補題の工房 ---------- */
  lemma: { color: "#8a6a3a", title: () => L1(__T(1611), "The Book of Lemmas"), desc: () => L1(__T(1612), "The lemma rule (cut) and cut elimination"), sections: [
    { id: "cut", h: () => L1(__T(1613), "The lemma rule"), body: () => L1(
      __T(1614, [BKF(BKN(`${L1(__T(792), "Lemma")}<sup class="sc">1</sup>`, [BKP("L"), BKD(BKA("L", 1), "C")], "C")), KEY(__T(1615)), KEY(__T(1616)), BKG([["!Γ"], "!C"], [[["!Γ"], "L"], [["!Γ", "+L"], "!C"]]), LEAN("have h : L := by …")]),
      `${BKF(BKN(`${L1(__T(792), "Lemma")}<sup class="sc">1</sup>`, [BKP("L"), BKD(BKA("L", 1), "C")], "C"))}
       ${KEY("If \\(L\\) is proved, and \\(C\\) is proved by assuming \\(L\\), then \\(C\\) is proved")}
       <p>\\(L\\) is called \\(a\\) <b>lemma</b>. This rule is the same as making \\(L\\to C\\) by \\({\\to}\\mathrm{I}\\) and applying it to \\(L\\) by \\({\\to}\\mathrm{E}\\).</p>
       <!--pg-->
       <p><b>The goal-changing reading</b>:</p>
       ${KEY("Split the goal \\(C\\) into \"the goal \\(L\\)\" and \"the goal \\(C\\) with the hypothesis \\(L\\) added\"")}
       ${BKG([["!Γ"], "!C"], [[["!Γ"], "L"], [["!Γ", "+L"], "!C"]])}
       ${LEAN("have h : L := by …")}
       <p><b>In the game</b>: choosing or writing a formula with "State a lemma" splits the door into one that proves the lemma and one that uses it as a key.</p>`) },
    { id: "why", h: () => L1(__T(1617), "Why use lemmas"), body: () => L1(
      __T(1618, [KEY(__T(1619))]),
      `${KEY("A lemma, once shown, can be used any number of times")}
       <p>In 14-1, the same path from \\(P\\) to \\(R\\) would have to be walked three times, for \\(a\\), \\(b\\) and \\(c\\).</p>
       <p>Once the lemma \\(\\forall x\\, (P(x) \\to R(x))\\) is shown, it only has to be applied to the three.</p>`) },
    { id: "elim", h: () => L1(__T(1620), "Cut elimination"), body: () => L1(
      __T(1621, [KEY(__T(1622))]),
      `${KEY("Lemmas (cuts) can, in principle, always be removed")}
       <p>Gentzen's fundamental theorem (Hauptsatz) showed that any proof can be rewritten into one without lemmas.</p>
       <p>The rewritten proof, however, can be far longer than the original (sometimes more than exponentially).</p>
       <p>That is why mathematicians build proofs out of lemmas.</p>`) },
    { id: "more", h: () => L1(__T(1351), "A little more"), body: () => L1(
      __T(1562, [bkRefs(["gentzen", "prawitz"])]),
      `<details><summary>References</summary>${bkRefs(["gentzen", "prawitz"])}</details>`) },
  ] },
  /* ---------- 第 15 層：自然数の塔 ---------- */
  peano: { color: "#2a6a8a", title: () => L1(__T(1623), "The Book of Natural Numbers"), desc: () => L1(__T(1624), "0, the successor s, and the definition of addition"), sections: [
    { id: "nat", h: () => L1(__T(1625), "How natural numbers are built"), body: () => L1(
      __T(1626, [KEY(__T(1627))]),
      `${KEY("Natural numbers \\(= 0\\), \\(s(0)\\), \\(s(s(0))\\), \\(\\dots\\)")}
       <p>\\(s(x)\\) is "the number after \\(x\\)" \\((x + 1)\\). We write \\(1 = s(0)\\), \\(2 = s(s(0))\\).</p>`) },
    { id: "add", h: () => L1(__T(1628), "The definition of addition"), body: () => L1(
      __T(1629, [KEY("\\(x + 0 = x\\)", "\\(x + s(y) = s(x + y)\\)"), KEY("\\(s(0) + s(0) = s(s(0) + 0) = s(s(0))\\)")]),
      `${KEY("\\(x + 0 = x\\)", "\\(x + s(y) = s(x + y)\\)")}
       <p>A recursive definition on the right-hand number \\(y\\). On this level, these two are given as the entrance keys (axioms).</p>
       <!--pg-->
       <p>Computing \\(1 + 1 = 2\\) (15-1):</p>
       ${KEY("\\(s(0) + s(0) = s(s(0) + 0) = s(s(0))\\)")}
       <p>The first equals sign is by the second equation, the second by the first.</p>`) },
    { id: "ax", h: () => L1(__T(1630), "The Peano axioms"), body: () => L1(
      __T(1631, [bkRefs(["dedekind", "peano"])]),
      `<p>As an axiom system for natural numbers, the Peano axioms are well known: 0 is not a successor, \\(s\\) is injective, and mathematical induction.</p>
       <p>This game mainly uses the defining equations of \\(+\\) and \\(\\times\\), and the rule of induction. The role of the other two axioms is examined at the end of the side path, the Tower of Order (S3-5, S3-6).</p>
       <details><summary>References</summary>${bkRefs(["dedekind", "peano"])}</details>`) },
    { id: "nng", h: () => L1(__T(1632), "Continue in Lean"), body: () => L1(
      __T(1633),
      `<p>Building the theory of natural numbers from the successor and induction is the standard path since Dedekind and Peano. In Lean's <a href="https://adam.math.hhu.de/#/g/leanprover-community/nng4" target="_blank" rel="noopener">Natural Number Game</a> (Kevin Buzzard, Jon Eugster and others), you can walk the same path step by step in Lean. The arrangement of the problems in Level 15 and the side paths of this game, and the reuse of proved theorems in later problems, draw on the Natural Number Game. If you want to write proofs in Lean with your own hands, try it as your next step.</p>`) },
  ] },
  induction: { color: "#3a7a5a", title: () => L1(__T(1634), "The Book of Induction"), desc: () => L1(__T(1635), "The rule of mathematical induction and how to use it"), sections: [
    { id: "ind", h: () => L1(__T(1636), "The rule of induction"), body: () => L1(
      __T(1637, [BKF(BKN(`${L1(__T(796), "Ind")}<sup class="sc">1</sup>`, [BKP("A(0)"), BKD(BKA("A(n)", 1), "A(s(n))")], "!x.A(x)")), KEY(__T(1638), __T(1639)), KEY(__T(1640)), BKG([["!Γ"], "!x.A(x)"], [[["!Γ"], "A(0)"], [["!Γ", "+A(n)"], "A(s(n))"]]), LEAN("induction n with | zero => … | succ n ih => …")]),
      `${BKF(BKN(`${L1(__T(796), "Ind")}<sup class="sc">1</sup>`, [BKP("A(0)"), BKD(BKA("A(n)", 1), "A(s(n))")], "!x.A(x)"))}
       ${KEY("If \\(A(0)\\) is proved, and \\(A(s(n))\\) is proved by assuming \\(A(n)\\),", "then \\(A(x)\\) is proved for every \\(x\\)")}
       <p>\\(n\\) is a new name (an eigenvariable).</p>
       <!--pg-->
       <p><b>The goal-changing reading</b>:</p>
       ${KEY("The goal \\(\\forall x\\, A(x)\\) splits into the base \\(A(0)\\) and the step \\(A(n) \\Rightarrow A(s(n))\\)")}
       ${BKG([["!Γ"], "!x.A(x)"], [[["!Γ"], "A(0)"], [["!Γ", "+A(n)"], "A(s(n))"]])}
       ${LEAN("induction n with | zero => … | succ n ih => …")}
       <p><b>In the game</b>: press the "Induction" button on a \\(\\forall\\) door.</p>`) },
    { id: "ex", h: () => L1(__T(1641), "Example: \\(0 + x = x\\)"), body: () => L1(
      __T(1642, [KEY(__T(1643), __T(1644))]),
      `<p>The calculation in the proof of 15-2.</p>
       ${KEY("Base: \\(0 + 0 = 0\\)", "Step: \\(0 + s(n) = s(0 + n) = s(n)\\)")}
       <p>The base is \\(x + 0 = x\\) with 0 plugged in. The second equals sign of the step uses the induction hypothesis \\(0 + n = n\\).</p>`) },
    { id: "choose", h: () => L1(__T(1645), "Which variable to induct on"), body: () => L1(
      __T(1646, [KEY(__T(1647))]),
      `${KEY("Induct on the same variable as the recursion of the definition")}
       <p>Addition \\(x + y\\) is defined recursively on the right number \\(y\\), so induction on \\(y\\) is natural (15-3).</p>
       <p>Some proofs, such as commutativity \\(x + y = y + x\\) (15-4), go much more smoothly if lemmas (\\(0 + x = x\\) and \\(s(x) + y = s(x + y)\\)) are prepared first.</p>`) },
    { id: "more", h: () => L1(__T(1351), "A little more"), body: () => L1(
      __T(1648),
      `<details><summary>Without induction</summary><p>Without induction, \\(0 + x = x\\) cannot be proved from the two defining equations of addition alone (16-9): there are structures with elements other than numbers that satisfy the equations while \\(0 + x = x\\) fails (see the Book of Independence).</p></details>`) },
  ] },
  /* ---------- 寄り道：照合（等号の書・下巻） ---------- */
  eq2: { color: "#5f5320", title: () => L1(__T(1649), "The Book of Equality, Volume II"), desc: () => L1(__T(1650), "Matching, and unification behind it"), sections: [
    { id: "use", h: () => L1(__T(1651), "Matching: using an equation with ∀ directly"), body: () => L1(
      __T(1652, [KEY(__T(1653), __T(1654))]),
      `<p>From side path S1 on, a key that is an equation with ∀ can be inserted into a door as it is. The game looks for a part of the door that fits the shape of one side of the equation, decides the terms for the variables, and then rewrites. This is called <b>matching</b>.</p>
       <p>For example, in S1-2, inserting the key \\(\\forall x\\,\\forall y\\,(x + s(y) = s(x + y))\\) into the door \\((a+b)+s(c) = a+(b+s(c))\\) finds two parts that fit the shape \\(x + s(y)\\) of the left side.</p>
       ${KEY("\\((a+b)+s(c)\\)　substitution \\(x \\mapsto a+b,\\ y \\mapsto c\\)", "\\(b+s(c)\\)　substitution \\(x \\mapsto b,\\ y \\mapsto c\\)")}
       <p>When you choose one, the door is rewritten by the equation made with that substitution.</p>
       <p>As a proof, it is not a new rule: it combines two inferences, instantiating with \\({\\forall}\\mathrm{E}\\) and rewriting with \\({=}\\mathrm{E}\\), into one move. The \\({\\forall}\\mathrm{E}\\) lines of the instantiation appear in the proof tree as they are.</p>`) },
    { id: "subst", h: () => L1(__T(1655), "Substitutions and matching"), body: () => L1(
      __T(1656, [KEY(__T(1657))]),
      `<p>An assignment \\(\\sigma\\) of terms to variables is called a <b>substitution</b>, and \\(t\\sigma\\) denotes the term \\(t\\) with all its variables replaced at once. For example, with \\(\\sigma = \\{x \\mapsto a+b,\\ y \\mapsto c\\}\\) we get \\((x + s(y))\\sigma = (a+b) + s(c)\\).</p>
       ${KEY("The matching problem: given a pattern \\(p\\) and a term \\(t\\), find a substitution \\(\\sigma\\) with \\(p\\sigma = t\\)")}
       <p>Only the variables of \\(p\\) may be instantiated; the side of \\(t\\) stays fixed. Matching is solved simply by following the shape of \\(p\\):</p>
       <ul><li>If \\(p\\) is a variable \\(x\\), set \\(x \\mapsto t\\) (if \\(x\\) already has a different term, fail).</li>
           <li>If \\(p = f(p_1, \\dots, p_n)\\), then \\(t\\) must be \\(f(t_1, \\dots, t_n)\\) with the same symbol, or else fail; then match each \\(p_i\\) with \\(t_i\\).</li></ul>
       <p><b>A solution, if any, is unique</b>: the assignment to the variables of \\(p\\) is determined in exactly one way by these steps (check by induction on the size of \\(p\\)). A pattern with a repeated variable, such as \\(x + x\\), fits \\(a + a\\) but not \\(a + b\\).</p>`) },
    { id: "unif", h: () => L1(__T(1658), "Unification"), body: () => L1(
      __T(1659, [KEY(__T(1660)), KEY(__T(1661), __T(1662))]),
      `<p>Matching instantiated only one side. When both terms contain variables and both may be instantiated at once, the problem of finding a substitution that makes the two terms identical is called <b>unification</b>.</p>
       ${KEY("The unification problem: for terms \\(s\\) and \\(t\\), find a substitution \\(\\sigma\\) (a unifier) with \\(s\\sigma = t\\sigma\\)")}
       <p>For example, \\(f(x, g(y))\\) and \\(f(g(z), x)\\) are unified by \\(\\sigma = \\{x \\mapsto g(z),\\ y \\mapsto z\\}\\): both become \\(f(g(z), g(z))\\).</p>
       <p>A unifier need not be unique (adding \\(z \\mapsto 0\\) gives another one). But there is a most general one from which all unifiers come.</p>
       ${KEY("<b>Unification theorem</b> (Robinson, 1965): if two terms are unifiable, a <b>most general unifier</b> \\(\\sigma\\) exists.", "Every unifier \\(\\tau\\) can be written \\(\\tau = \\sigma\\rho\\) for some substitution \\(\\rho\\), and \\(\\sigma\\) is unique up to renaming of variables.")}
       <p>Some pairs cannot be unified. \\(f(x)\\) and \\(g(y)\\) have different symbols, so no substitution makes them equal. And \\(x\\) and \\(f(x)\\) cannot be unified among finite terms: whatever \\(x\\) is, the right side is one symbol larger. This is detected by the <b>occurs check</b>.</p>`) },
    { id: "mm", h: () => L1(__T(1663), "An algorithm for unification"), body: () => L1(
      __T(1664, [bkTable([__T(1665), __T(1666), __T(1667)], [
         [__T(1668), "\\(\\{t \\doteq t\\} \\cup E \\Rightarrow E\\)", ""],
         [__T(1669), "\\(\\{f(s_1,\\dots,s_n) \\doteq f(t_1,\\dots,t_n)\\} \\cup E \\Rightarrow \\{s_1 \\doteq t_1, \\dots, s_n \\doteq t_n\\} \\cup E\\)", ""],
         [__T(1670), __T(1671), "\\(f \\neq g\\)"],
         [__T(1672), "\\(\\{t \\doteq x\\} \\cup E \\Rightarrow \\{x \\doteq t\\} \\cup E\\)", __T(1673)],
         [__T(1674), "\\(\\{x \\doteq t\\} \\cup E \\Rightarrow \\{x \\doteq t\\} \\cup E[x := t]\\)", __T(1675)],
         [__T(1676), __T(1677), __T(1678)]])]),
      `<p>In the method of Martelli and Montanari (1982), the set \\(E\\) of equations to solve is rewritten by the following rules (\\(\\doteq\\) marks "to be made identical").</p>
       ${bkTable(["Rule", "Rewriting", "Condition"], [
         ["Delete", "\\(\\{t \\doteq t\\} \\cup E \\Rightarrow E\\)", ""],
         ["Decompose", "\\(\\{f(s_1,\\dots,s_n) \\doteq f(t_1,\\dots,t_n)\\} \\cup E \\Rightarrow \\{s_1 \\doteq t_1, \\dots, s_n \\doteq t_n\\} \\cup E\\)", ""],
         ["Conflict", "\\(\\{f(\\dots) \\doteq g(\\dots)\\} \\cup E \\Rightarrow\\) fail", "\\(f \\neq g\\)"],
         ["Swap", "\\(\\{t \\doteq x\\} \\cup E \\Rightarrow \\{x \\doteq t\\} \\cup E\\)", "\\(t\\) is not a variable"],
         ["Eliminate", "\\(\\{x \\doteq t\\} \\cup E \\Rightarrow \\{x \\doteq t\\} \\cup E[x := t]\\)", "\\(x\\) does not occur in \\(t\\) but occurs in \\(E\\)"],
         ["Occurs check", "\\(\\{x \\doteq t\\} \\cup E \\Rightarrow\\) fail", "\\(x\\) occurs in \\(t\\) and \\(t \\neq x\\)"]])}
       <p>This rewriting always terminates. Unless it fails, it stops in the form \\(\\{x_1 \\doteq t_1, \\dots, x_k \\doteq t_k\\}\\) (distinct variables on the left, none occurring on the right), and then \\(\\{x_1 \\mapsto t_1, \\dots, x_k \\mapsto t_k\\}\\) is a most general unifier.</p>
       <p>In the example above, decomposing \\(f(x, g(y)) \\doteq f(g(z), x)\\) gives \\(x \\doteq g(z),\\ g(y) \\doteq x\\). Eliminating \\(x\\) gives \\(g(y) \\doteq g(z)\\), and decomposing gives \\(y \\doteq z\\). The answer is \\(\\{x \\mapsto g(z),\\ y \\mapsto z\\}\\).</p>`) },
    { id: "game", h: () => L1(__T(1679), "Why matching is enough in this game"), body: () => L1(
      __T(1680, [KEY(__T(1681))]),
      `${KEY("Matching is unification that leaves one side's variables fixed")}
       <p>The \\(a\\) and \\(b\\) in a door are the names of residents brought in through a ∀ door or from an ∃ key. They are not unknowns still to be decided but names of one particular resident, so they must not be instantiated while rewriting. Only the variables of the key's ∀ may be instantiated, so matching, a special case of unification, is enough.</p>
       <p>If an operation like "decide the witness of an ∃ door later" were allowed, unknowns would appear in doors and real unification would be needed. Lean treats terms not yet decided as <b>metavariables</b> (displayed as \\(?w\\) and so on) and fills them in by unification at each <code>apply</code> or <code>rw</code>. This game does not include that operation, because choosing the witness is itself a central thing to learn here.</p>
       <p>The field that treats equations as directed rules, "when the shape of the left side is found, replace it with the right side", is called <b>term rewriting</b>. Rewriting by matching is one step of it.</p>`) },
    { id: "where", h: () => L1(__T(1682), "Where unification is used"), body: () => L1(
      __T(1683),
      `<ul><li><b>Resolution</b>: Robinson introduced unification as the heart of resolution, an inference rule for automated theorem proving. Running a program in the logic programming language Prolog is also repeated unification.</li>
           <li><b>Type inference</b>: type inference in functional programming languages (the Hindley–Milner method) solves equations between types by unification.</li>
           <li><b>Term rewriting and completion</b>: Knuth–Bendix completion builds directed rewriting rules from a set of equations and adds rules so that every order of rewriting reaches the same answer; it finds overlaps between left sides of rules by unification.</li>
           <li><b>Higher-order unification</b>: unification in which variables may stand for functions is already undecidable at second order (Goldfarb, 1981). Proof assistants such as Lean use Huet's procedure and the decidable "pattern" fragment (Miller, 1991) with care.</li>
           <li><b>Unification modulo equations</b>: unification that regards associativity or commutativity as "the same" is much harder than ordinary unification, and a most general solution need not be unique.</li></ul>`) },
    { id: "refs", h: () => L1(__T(1501), "References"), body: () => `${bkRefs(["robinson65", "martelli82", "baadernipkow", "baadersnyder", "knuthbendix70", "huet75", "goldfarb81", "miller91", "tpil4"])}` },
  ] },
  /* ---------- 寄り道：掛け算の塔 ---------- */
  mult: { color: "#7a4a6a", title: () => L1(__T(1684), "The Book of Multiplication"), desc: () => L1(__T(1685), "The definition of multiplication and proofs by induction"), sections: [
    { id: "def", h: () => L1(__T(1686), "The definition of multiplication"), body: () => L1(
      __T(1687, [KEY("\\(x \\cdot 0 = 0\\)", "\\(x \\cdot s(y) = x \\cdot y + x\\)")]),
      `${KEY("\\(x \\cdot 0 = 0\\)", "\\(x \\cdot s(y) = x \\cdot y + x\\)")}
       <p>Like addition, a recursive definition on the right-hand number, defined using addition.</p>`) },
    { id: "ex1", h: () => L1(__T(1688), "Example: multiplying by 1"), body: () => L1(
      __T(1689, [KEY("\\(x \\cdot s(0) = x \\cdot 0 + x = 0 + x = x\\)")]),
      `<p>\\(x \\cdot s(0) = x\\) can be shown without induction.</p>
       ${KEY("\\(x \\cdot s(0) = x \\cdot 0 + x = 0 + x = x\\)")}
       <p>The last equals sign uses the theorem \\(0 + x = x\\) proved on Level 15. No induction is needed.</p>`) },
    { id: "ex2", h: () => L1(__T(1690), "Example: multiplying by 0 on the left"), body: () => L1(
      __T(1691, [KEY(__T(1692), __T(1693))]),
      `<p>S1-1: show \\(0 \\cdot x = 0\\) by induction on \\(x\\).</p>
       ${KEY("Base: \\(0 \\cdot 0 = 0\\)", "Step: \\(0 \\cdot s(n) = 0 \\cdot n + 0 = 0 \\cdot n = 0\\)")}
       <p>The last step uses the induction hypothesis \\(0 \\cdot n = 0\\).</p>`) },
    { id: "cards", h: () => L1(__T(1694), "Building up theorems"), body: () => L1(
      __T(1695, [KEY(__T(1696))]),
      `${KEY("Each theorem proved becomes a tool for the next proof")}
       <p>On this level you prove associativity of addition (S1-2) as a theorem and use it to prove distributivity \\(x \\cdot (y + z) = x \\cdot y + x \\cdot z\\) (S1-3).</p>`) },
  ] },
  /* ---------- 寄り道：掛け算の法則 ---------- */
  laws: { color: "#6a3a3a", title: () => L1(__T(1697), "The Book of Laws of Calculation"), desc: () => L1(__T(1698), "Associativity and commutativity of multiplication, built from lemmas"), sections: [
    { id: "plan", h: () => L1(__T(1699), "A stack of lemmas"), body: () => L1(
      `${KEY(__T(1700))}
       ${bkTable([__T(1701), __T(1487), __T(1702)], [["\\(0 + x = x\\)", __T(1703), "15-2"], ["\\(s(x) + y = s(x + y)\\)", __T(346), "15-3"], ["\\(x + y = y + x\\)", __T(351), "15-4"], ["\\((x + y) + z = x + (y + z)\\)", __T(368), "S1-2"], ["\\(x \\cdot (y + z) = x \\cdot y + x \\cdot z\\)", __T(373), "S1-3"], ["\\(0 \\cdot x = 0\\)", __T(1704), "S1-1"], ["\\(s(x) \\cdot y = x \\cdot y + y\\)", __T(385), "S2-2"]])}`,
      `${KEY("A big theorem is a stack of small lemmas")}
       ${bkTable(["Theorem", "Meaning", "Proved in"], [["\\(0 + x = x\\)", "adding 0 on the left", "15-2"], ["\\(s(x) + y = s(x + y)\\)", "taking the successor out", "15-3"], ["\\(x + y = y + x\\)", "commutativity of \\(+\\)", "15-4"], ["\\((x + y) + z = x + (y + z)\\)", "associativity of \\(+\\)", "S1-2"], ["\\(x \\cdot (y + z) = x \\cdot y + x \\cdot z\\)", "distributivity", "S1-3"], ["\\(0 \\cdot x = 0\\)", "multiplying by 0 on the left", "S1-1"], ["\\(s(x) \\cdot y = x \\cdot y + y\\)", "multiplying by a successor on the left", "S2-2"]])}`) },
    { id: "assoc", h: () => L1(__T(1705), "Associativity"), body: () => L1(
      __T(1706, [KEY("\\((x \\cdot y) \\cdot s(n) = (x \\cdot y) \\cdot n + x \\cdot y\\)", "\\(= x \\cdot (y \\cdot n) + x \\cdot y = x \\cdot (y \\cdot n + y) = x \\cdot (y \\cdot s(n))\\)")]),
      `<p>S2-1: show \\((x \\cdot y) \\cdot z = x \\cdot (y \\cdot z)\\) by induction on \\(z\\). The step is the following calculation.</p>
       ${KEY("\\((x \\cdot y) \\cdot s(n) = (x \\cdot y) \\cdot n + x \\cdot y\\)", "\\(= x \\cdot (y \\cdot n) + x \\cdot y = x \\cdot (y \\cdot n + y) = x \\cdot (y \\cdot s(n))\\)")}
       <p>The second equals sign uses the induction hypothesis, and the third uses distributivity (backwards).</p>`) },
    { id: "comm", h: () => L1(__T(1707), "Commutativity"), body: () => L1(
      __T(1708, [KEY(__T(1709), __T(1710))]),
      `<p>S2-3: show \\(x \\cdot y = y \\cdot x\\) by induction on \\(y\\).</p>
       ${KEY("Base: \\(x \\cdot 0 = 0 = 0 \\cdot x\\)", "Step: \\(x \\cdot s(n) = x \\cdot n + x = n \\cdot x + x = s(n) \\cdot x\\)")}
       <p>The base uses \\(0 \\cdot x = 0\\), and the end of the step uses \\(s(x) \\cdot y = x \\cdot y + y\\) (backwards).</p>`) },
    { id: "divide", h: () => L1(__T(396), "Transitivity of divisibility"), body: () => L1(
      __T(1711, [KEY("\\(a \\cdot (p \\cdot q) = (a \\cdot p) \\cdot q = b \\cdot q = c\\)")]),
      `<p>S2-4: \\(\\exists k\\, (a \\cdot k = b)\\) means "\\(a\\) divides \\(b\\)". Take the witnesses \\(p\\) and \\(q\\) out of the two hypotheses (\\(a \\cdot p = b\\), \\(b \\cdot q = c\\)) and choose \\(p \\cdot q\\) as the witness.</p>
       ${KEY("\\(a \\cdot (p \\cdot q) = (a \\cdot p) \\cdot q = b \\cdot q = c\\)")}
       <p>Associativity alone does the calculation; no induction is needed. Witnesses are not only taken out of hypotheses: they can also be built by combining others.</p>`) },
  ] },
  /* ---------- 寄り道：順序の塔 ---------- */
  order: { color: "#4a6a3a", title: () => L1(__T(1712), "The Book of Order"), desc: () => L1(__T(1713), "Defining the order ≤ of natural numbers by addition"), sections: [
    { id: "def", h: () => L1(__T(1714), "The definition of the order"), body: () => L1(
      __T(1715, [KEY("\\(x \\le y \\mathrel{:\\Leftrightarrow} \\exists z\\, (x + z = y)\\)", __T(1716))]),
      `${KEY("\\(x \\le y \\mathrel{:\\Leftrightarrow} \\exists z\\, (x + z = y)\\)", "(adding something to \\(x\\) gives \\(y\\))")}
       <p>Unfolding the definition brings in \\(\\exists\\), so proofs use \\({\\exists}\\mathrm{I}\\) (choosing a witness) and \\({\\exists}\\mathrm{E}\\) (taking a witness out).</p>`) },
    { id: "ex", h: () => L1(__T(1717), "Choosing witnesses"), body: () => L1(
      __T(1718, [bkTable([__T(1719), __T(1720), __T(1721)], [[__T(1722), "\\(x\\)", "\\(0 + x = x\\)"], [__T(1723), "\\(s(0)\\)", "\\(x + s(0) = s(x + 0) = s(x)\\)"]]), KEY(__T(1724))]),
      `${bkTable(["To show", "Witness \\(z\\)", "Equation used"], [["\\(0 \\le x\\) (S3-1)", "\\(x\\)", "\\(0 + x = x\\)"], ["\\(x \\le s(x)\\) (S3-3)", "\\(s(0)\\)", "\\(x + s(0) = s(x + 0) = s(x)\\)"]])}
       ${KEY("At an \\(\\exists\\) goal, the choice of witness is everything")}
       <p>For \\(\\exists x\\, \\forall y\\, (x \\le y)\\) in S3-2, choose 0 as the witness and use the theorem from S3-1. The order of the quantifiers differs from \\(\\forall y\\, \\exists x\\, (x \\le y)\\), and this one is the stronger claim.</p>`) },
    { id: "trans", h: () => L1(__T(1725), "Transitivity"), body: () => L1(
      __T(1726, [KEY("\\(x + (p + q) = (x + p) + q = y + q = z\\)")]),
      `<p>S3-4: show \\(x \\le z\\) from \\(x \\le y\\) and \\(y \\le z\\).</p>
       <ol class="bk-steps"><li>Take witnesses out of the hypotheses: \\(x + p = y\\) and \\(y + q = z\\) (∃E twice).</li><li>Choose \\(p + q\\) as the witness \\(({\\exists}\\mathrm{I})\\).</li><li>Calculate using associativity.</li></ol>
       ${KEY("\\(x + (p + q) = (x + p) + q = y + q = z\\)")}`) },
    { id: "inf", h: () => L1(__T(1727), "Endless numbers and the Peano axioms"), body: () => L1(
      __T(1728, [KEY(__T(1729)), KEY(__T(1730), __T(1731))]),
      `${KEY("The axioms of addition and induction alone cannot show that numbers never end")}
       <p>S3-5: in a structure with a single element (where \\(0\\) and \\(s(0)\\) are the same element), the axioms and induction all hold, but there is no "larger number". Every element can be reached from \\(0\\) by following \\(s\\), so induction holds too.</p>
       <!--pg-->
       <p>S3-6: adding the Peano axioms \\(\\neg (s(x) = 0)\\) and the injectivity of \\(s\\), the lemma \\(\\forall x\\, \\neg (s(x) = x)\\) can be proved by induction.</p>
       ${KEY("\\(x \\le s(x)\\) and \\(\\neg (s(x) = x)\\)", "so \\(s(x)\\) is a witness for a number larger than \\(x\\)")}`) },
    { id: "more", h: () => L1(__T(1351), "A little more"), body: () => L1(
      __T(1732),
      `<details><summary>Lean's \\(\\le\\) is different</summary><p>The \\(\\le\\) of Lean's natural numbers is defined differently. That is why Lean mode writes the \\(\\le\\) of this game as ≼, to tell them apart.</p></details>`) },
  ] },
  /* ---------- 第 16 層：公理の鏡 ---------- */
  indep: { color: "#5a3a6a", title: () => L1(__T(1733), "The Book of Independence"), desc: () => L1(__T(1734), "Showing unprovability from axioms by structures"), sections: [
    { id: "idea", h: () => L1(__T(1735), "The idea"), body: () => L1(
      __T(1736, [KEY(__T(1737))]),
      `${KEY("If a structure satisfies all the axioms of a theory \\(T\\) but not \\(A\\), then \\(T \\nvdash A\\)")}
       <p>This follows from soundness (see the Book of Structures). If, moreover, some structure satisfies \\(T\\) and also \\(A\\), then \\(\\neg A\\) cannot be proved from \\(T\\) either. When neither \\(A\\) nor \\(\\neg A\\) can be proved, \\(A\\) is said to be <b>independent</b> of \\(T\\) (T alone does not settle it). Being unprovable and being independent are different things (for example, with no axioms at all, \\(\\bot\\) cannot be proved but \\(\\neg\\bot\\) can, so \\(\\bot\\) is not independent).</p>
       <p>On this level the structures (models in the game) check only the unprovable side. Showing independence from both sides comes on Level 17.</p>
       <p>Example (16-1): from reflexivity, antisymmetry and transitivity (a partial order), "any two are comparable" cannot be proved. A structure with two incomparable elements is a counterexample.</p>`) },
    { id: "group", h: () => L1(__T(1738), "Examples from groups"), body: () => L1(
      __T(1739, [KEY(__T(1740)), KEY(__T(1741))]),
      `${KEY("Commutativity cannot be proved from the group axioms")}
       <p>A non-commutative group is a counterexample. Such a group needs at least 6 elements; the symmetric group \\(S_{3}\\) is the smallest example (16-8).</p>
       <!--pg-->
       <p>16-4: from associativity and a left identity alone, the right identity \\(x\\cdot e = x\\) cannot be proved.</p>
       ${KEY("The structure defined by \\(x \\cdot y = y\\)")}
       <p>It satisfies associativity, since \\((x\\cdot y)\\cdot z = z = x\\cdot (y\\cdot z)\\), and also \\(e\\cdot x = x\\); but \\(x\\cdot e = e\\), so \\(x\\cdot e = x\\) fails whenever \\(x\\) is not \\(e\\).</p>`) },
    { id: "ind", h: () => L1(__T(593), "The power of induction"), body: () => L1(
      __T(1742, [KEY(__T(1743))]),
      `<p>16-9: from the two defining equations of addition alone, \\(0 + x = x\\) cannot be proved.</p>
       ${KEY("Domain \\(\\{0, a\\}\\), \\(s(0) = 0\\), \\(s(a) = a\\), \\(0 + a = 0\\)")}
       <p>The other sums are fixed by \\(x + 0 = x\\), and \\(a + a\\) can be anything. Since \\(s\\) changes nothing, both defining equations hold, but \\(0 + a = 0\\) is not \\(a\\).</p>
       <p>With induction, \\(0 + x = x\\) can be proved (15-2), so induction is a rule with genuinely new power.</p>`) },
    { id: "more", h: () => L1(__T(1351), "A little more"), body: () => L1(
      __T(1744, [bkRefs(["godel31", "godel30", "vandalen"])]),
      `<details><summary>Gödel's incompleteness theorem</summary><p>Even in strong theories such as Peano arithmetic and ZFC set theory, there are arithmetical sentences that can be neither proved nor refuted, assuming these theories are consistent (Gödel, 1931). In fact, however many axioms you add to these theories mechanically (as long as no contradiction arises), you cannot obtain a system that proves every truth.</p></details>
       <details><summary>References</summary>${bkRefs(["godel31", "godel30", "vandalen"])}</details>`) },
  ] },
});
Object.assign(ARCHIVES, { "6-1": ["raa", "classic"], "r-conv": ["truth", "sound"], "5-1": ["kripke"], "7-1": ["forall"], "7-3": ["exists"], "f-barber": ["qclass"], "s-ex": ["struct"], "10-5": ["set"], "9-1": ["eq"], "9-5": ["theory"], "11-1": ["lemma"], "12-1": ["peano", "induction"], "13-2": ["eq2", "mult"], "14-1": ["laws"], "15-1": ["order"], "x-total": ["indep"] });
Object.assign(RULE_BOOK, { "RAA": ["raa", "rule"], "∀I": ["forall", "allI"], "∀E": ["forall", "allE"], "∃I": ["exists", "exI"], "∃E": ["exists", "exE"], "=I": ["eq", "eqI"], "=E": ["eq", "eqE"], "定義": ["set", "def"], "補題": ["lemma", "cut"], "帰納法": ["induction", "ind"] });

// 隠し層 2「翻訳所」の書庫：翻訳の書　／　第 17 層「迷宮の中枢」の書庫：自己言及と計算の書
Object.assign(BK_REF, {
  kuroda: `S. Kuroda, "Intuitionistische Untersuchungen der formalistischen Logik", <i>Nagoya Mathematical Journal</i> 2 (1951), 35–47.`,
  godel33a: `K. Gödel, "Zur intuitionistischen Arithmetik und Zahlentheorie", <i>Ergebnisse eines mathematischen Kolloquiums</i> 4 (1933), 34–38.`,
  gentzen36: `G. Gentzen, "Die Widerspruchsfreiheit der reinen Zahlentheorie", <i>Mathematische Annalen</i> 112 (1936), 493–565.`,
  rosser36: `J. B. Rosser, "Extensions of some theorems of Gödel and Church", <i>Journal of Symbolic Logic</i> 1 (1936), 87–91.`,
  cantor91: `G. Cantor, "Über eine elementare Frage der Mannigfaltigkeitslehre", <i>Jahresbericht der Deutschen Mathematiker-Vereinigung</i> 1 (1891), 75–78.`,
  godel38: `K. Gödel, "The consistency of the axiom of choice and of the generalized continuum-hypothesis", <i>Proceedings of the National Academy of Sciences of the USA</i> 24 (1938), 556–557.`,
  cohen63: `P. J. Cohen, "The independence of the continuum hypothesis", <i>Proceedings of the National Academy of Sciences of the USA</i> 50 (1963), 1143–1148.`,
  smullyan: `R. M. Smullyan, <i>Gödel's Incompleteness Theorems</i>, Oxford University Press, 1992.`,
});
Object.assign(BOOKS, {
  transl: { color: "#4f3f6e", title: () => L1(__T(1745), "The Book of Translation"), desc: () => L1(__T(1746), "Translating classical logic into intuitionistic logic"), sections: [
    { id: "glivenko", h: () => L1(__T(1747), "A double negation in front of the whole: Glivenko's theorem"), body: () => L1(
      String.raw`${KEY(String.raw`命題論理では　\(\vdash_{\mathrm{c}} A \iff\ \vdash_{\mathrm{i}} \neg\neg A\)`)}
       <p>\(\vdash_{\mathrm{c}}\) は背理法ありの<b>古典論理</b>で、\(\vdash_{\mathrm{i}}\) は背理法なしの<b>直観主義論理</b>で証明できることを表します。古典論理で証明できる命題論理の式は、全体に二重否定を付ければ、直観主義論理で証明できます（グリヴェンコ、1929）。ゲームの物語では、背理法を「魔導書の術」、二重否定を付けることを「外套をかける」と呼んでいます。</p>
       <p>翻訳所の H2-1〜H2-3 がその例です。H2-1 の訳文 \(\neg\neg(P\lor\neg P)\) は、第 4 層のボス 4-5 と同じ式でした。</p>
       <!--pg-->
       <p>逆向き（\(\Leftarrow\)）はすぐに分かります。\(\neg\neg A\) が直観主義論理で証明できれば、背理法で二重否定を外して \(A\) が得られるからです。</p>
       <p>\(\Rightarrow\) の考え方：古典論理の証明を一段ずつたどり、各段の結論に \(\neg\neg\) を付けても直観主義論理で導けることを確かめます。そのとき、次のような直観主義論理で成り立つ性質を使います。</p>
       ${KEY(String.raw`\(\neg\neg(A\to B) \leftrightarrow (\neg\neg A\to\neg\neg B)\)`, String.raw`\(\neg\neg(A\land B) \leftrightarrow (\neg\neg A\land\neg\neg B)\)`, String.raw`\(\neg\neg\neg\neg A \to \neg\neg A\)`)}
       <p>最後の性質のおかげで、背理法の一段（\(\neg A\) から矛盾を導いて \(A\) を得る）も、二重否定を付けた世界では直観主義論理の推論に変わります。</p>`,
      String.raw`${KEY(String.raw`In propositional logic, \(\vdash_{\mathrm{c}} A \iff\ \vdash_{\mathrm{i}} \neg\neg A\)`)}
       <p>\(\vdash_{\mathrm{c}}\) means provable in <b>classical logic</b> (with reductio), and \(\vdash_{\mathrm{i}}\) means provable in <b>intuitionistic logic</b> (without reductio). A propositional formula provable in classical logic becomes provable in intuitionistic logic once a double negation is put in front of the whole formula (Glivenko, 1929). In the game's story, reductio is called "the grimoire's spell", and putting a double negation in front is called "putting on a cloak".</p>
       <p>H2-1 to H2-3 in the translation office are examples. The translation in H2-1, \(\neg\neg(P\lor\neg P)\), was the same formula as 4-5, the boss of Level 4.</p>
       <!--pg-->
       <p>The direction \(\Leftarrow\) is immediate: if \(\neg\neg A\) can be proved in intuitionistic logic, reductio removes the double negation and gives \(A\).</p>
       <p>The idea for \(\Rightarrow\): follow a classical proof step by step and check that, with \(\neg\neg\) added to the conclusion of each step, the step can still be made in intuitionistic logic. This uses facts like the following, which hold in intuitionistic logic.</p>
       ${KEY(String.raw`\(\neg\neg(A\to B) \leftrightarrow (\neg\neg A\to\neg\neg B)\)`, String.raw`\(\neg\neg(A\land B) \leftrightarrow (\neg\neg A\land\neg\neg B)\)`, String.raw`\(\neg\neg\neg\neg A \to \neg\neg A\)`)}
       <p>Thanks to the last fact, even a step of reductio (deriving a contradiction from \(\neg A\) to obtain \(A\)) becomes an intuitionistic inference in the world with double negations attached.</p>`) },
    { id: "fail", h: () => L1(__T(1748), "Failure for formulas with quantifiers"), body: () => L1(
      String.raw`${KEY(String.raw`\(\vdash_{\mathrm{c}} \forall x\,(P(x)\lor\neg P(x))\)　なのに　\(\nvdash_{\mathrm{i}} \neg\neg\forall x\,(P(x)\lor\neg P(x))\)`)}
       <p>量化子を含む式では、全体に二重否定を付けるだけでは足りません（H2-4）。反例は、世界が終わりなく一列に続くクリプキモデル（ゲームでは時の塔）です。</p>
       <p>述語論理のクリプキモデルでは、各世界（ゲームでは塔の階）に要素の集まり（ゲームでは住人）があり、上の世界ほど要素が増えることがあります。そのため \(\forall x\,A(x)\) が強制される（ゲームでは「光る」）のは、その世界だけでなく、そこから上のすべての世界で、そこにある要素すべてについて \(A\) が強制されるときです（\(\exists x\,A(x)\) が強制されるのは、その世界にある要素のどれかについて \(A\) が強制されるときです）。</p>
       ${KEY(String.raw`世界 \(n\) の要素は \(0, 1, \dots, n\)`, String.raw`\(P(k)\) は世界 \(k+1\) 以上で強制される`)}
       <p>世界 \(n\) では、いちばん新しい要素 \(n\) について、\(P(n)\) も \(\neg P(n)\) も強制されません（\(P(n)\) は一つ上の世界で強制されるので）。よって \(\forall x\,(P(x)\lor\neg P(x))\) はどの世界でも強制されず、その否定はどの世界でも強制され、二重否定は世界 0 で強制されません。健全性定理により、訳文は直観主義論理では証明できません。</p>
       <!--pg-->
       <p><b>反例は無限でなければならない</b>：世界が有限個しかないモデルには、それより上のない世界があります。そこでは古典論理と同じように真偽が決まるので、古典論理で証明できる式 \(A\) は必ず強制されます。どの世界からもそのような世界へ上れるので、\(\neg A\) はどこでも強制されず、\(\neg\neg A\) はすべての世界で強制されてしまいます。</p>
       <p><b>失われた推論</b>：このモデルでは、どの要素についても \(\neg\neg(P(x)\lor\neg P(x))\) は強制されます（直観主義論理で証明できる式だからです）。それでも \(\neg\neg\forall x\,(P(x)\lor\neg P(x))\) は強制されません。つまり、次の推論（二重否定の移動）は、直観主義論理では成り立ちません。</p>
       ${KEY(String.raw`\(\forall x\,\neg\neg B(x) \to \neg\neg\forall x\,B(x)\)`)}`,
      String.raw`${KEY(String.raw`\(\vdash_{\mathrm{c}} \forall x\,(P(x)\lor\neg P(x))\), and yet \(\nvdash_{\mathrm{i}} \neg\neg\forall x\,(P(x)\lor\neg P(x))\)`)}
       <p>For formulas with quantifiers, a single double negation in front is not enough (H2-4). The counterexample is a Kripke model whose worlds go on endlessly in a line (the Tower of Time in the game).</p>
       <p>In a Kripke model for predicate logic, each world (a floor of the tower in the game) has a collection of elements (the residents in the game), and higher worlds may have more elements. So \(\forall x\,A(x)\) is forced ("lit" in the game) only when, not just at that world but at every world above it, \(A\) is forced for every element there (\(\exists x\,A(x)\) is forced when \(A\) is forced for some element at that world).</p>
       ${KEY(String.raw`World \(n\) has elements \(0, 1, \dots, n\)`, String.raw`\(P(k)\) is forced from world \(k+1\) up`)}
       <p>At world \(n\), for the newest element \(n\), neither \(P(n)\) nor \(\neg P(n)\) is forced (since \(P(n)\) is forced one world above). So \(\forall x\,(P(x)\lor\neg P(x))\) is forced at no world, its negation is forced at every world, and the double negation is not forced at world 0. By the soundness theorem, the translation cannot be proved in intuitionistic logic.</p>
       <!--pg-->
       <p><b>The counterexample must be infinite</b>: a model with finitely many worlds has worlds with nothing above them. There, truth is decided as in classical logic, so any classically provable formula \(A\) is forced. Since every world can reach such a world, \(\neg A\) is forced nowhere, and \(\neg\neg A\) is forced at every world.</p>
       <p><b>The lost inference</b>: in this model, \(\neg\neg(P(x)\lor\neg P(x))\) is forced for every element (it is provable in intuitionistic logic). Even so, \(\neg\neg\forall x\,(P(x)\lor\neg P(x))\) is not forced. So the following inference (the double-negation shift) does not hold in intuitionistic logic.</p>
       ${KEY(String.raw`\(\forall x\,\neg\neg B(x) \to \neg\neg\forall x\,B(x)\)`)}`) },
    { id: "kuroda", h: () => L1(__T(1749), "Translating quantifier by quantifier: Kuroda's translation"), body: () => L1(
      String.raw`<p>二重否定を、式全体の前だけでなく、すべての \(\forall\) のすぐ内側にも付けます。式 \(A\) の中の各 \(\forall x\) を \(\forall x\,\neg\neg\) に置き換えた式を \(A^{*}\) として、次のように定めます（黒田成勝、1951）。</p>
       ${KEY(String.raw`\(A^{\mathrm{K}} = \neg\neg A^{*}\)`, String.raw`\(\vdash_{\mathrm{c}} A \iff\ \vdash_{\mathrm{i}} A^{\mathrm{K}}\)`)}
       <p>例：\(\forall x\,(P(x)\lor\neg P(x))\) の訳は \(\neg\neg\forall x\,\neg\neg(P(x)\lor\neg P(x))\) で、これは直観主義論理で証明できます（H2-5）。\(\forall\) の内側の二重否定が、前の節の「二重否定の移動」の代わりをしています。</p>
       <!--pg-->
       <p><b>ゲーデル＝ゲンツェンの否定翻訳</b>：同じ目的の、もう一つの有名な訳し方です。原子式と \(\lor\)、\(\exists\) に否定を差し込みます。</p>
       ${bkTable([__T(1487), __T(1750)], [[String.raw`\(P\)（原子式）`, String.raw`\(\neg\neg P\)`], [String.raw`\(A\land B\)`, String.raw`\(A^{N}\land B^{N}\)`], [String.raw`\(A\to B\)`, String.raw`\(A^{N}\to B^{N}\)`], [String.raw`\(A\lor B\)`, String.raw`\(\neg(\neg A^{N}\land\neg B^{N})\)`], [String.raw`\(\forall x\,A\)`, String.raw`\(\forall x\,A^{N}\)`], [String.raw`\(\exists x\,A\)`, String.raw`\(\neg\forall x\,\neg A^{N}\)`], [String.raw`\(\bot\)`, String.raw`\(\bot\)`]])}
       <p>この訳し方でも、\(\Gamma \vdash_{\mathrm{c}} A\) と \(\Gamma^{N} \vdash_{\mathrm{i}} A^{N}\) は同値です（ゲーデル、1933 年。ゲンツェンも同じ年に同じ翻訳を得ていました）。訳し方の要は、原子式にも二重否定を付け、\(\lor\) と \(\exists\) を否定で表すことです。こうして訳した式は、どれも直観主義論理で \(\neg\neg A^{N}\) から \(A^{N}\) を導ける形（<b>安定</b>な式）になります。\(\lor\) と \(\exists\) を消すだけでは足りません。原子式 \(P\) はどちらも含みませんが、\(\neg\neg P \to P\) は直観主義論理では証明できないからです。</p>`,
      String.raw`<p>Put a double negation not only in front of the whole formula but also just inside every \(\forall\). Let \(A^{*}\) be the formula obtained from \(A\) by replacing each \(\forall x\) with \(\forall x\,\neg\neg\), and define (Kuroda, 1951):</p>
       ${KEY(String.raw`\(A^{\mathrm{K}} = \neg\neg A^{*}\)`, String.raw`\(\vdash_{\mathrm{c}} A \iff\ \vdash_{\mathrm{i}} A^{\mathrm{K}}\)`)}
       <p>Example: the translation of \(\forall x\,(P(x)\lor\neg P(x))\) is \(\neg\neg\forall x\,\neg\neg(P(x)\lor\neg P(x))\), which can be proved in intuitionistic logic (H2-5). The double negation inside the \(\forall\) does the job of the double-negation shift from the previous section.</p>
       <!--pg-->
       <p><b>The Gödel–Gentzen negative translation</b>: another famous translation with the same aim. It inserts negations at atomic formulas, \(\lor\) and \(\exists\).</p>
       ${bkTable(["Formula", "Translation"], [[String.raw`\(P\) (atomic)`, String.raw`\(\neg\neg P\)`], [String.raw`\(A\land B\)`, String.raw`\(A^{N}\land B^{N}\)`], [String.raw`\(A\to B\)`, String.raw`\(A^{N}\to B^{N}\)`], [String.raw`\(A\lor B\)`, String.raw`\(\neg(\neg A^{N}\land\neg B^{N})\)`], [String.raw`\(\forall x\,A\)`, String.raw`\(\forall x\,A^{N}\)`], [String.raw`\(\exists x\,A\)`, String.raw`\(\neg\forall x\,\neg A^{N}\)`], [String.raw`\(\bot\)`, String.raw`\(\bot\)`]])}
       <p>With this translation too, \(\Gamma \vdash_{\mathrm{c}} A\) and \(\Gamma^{N} \vdash_{\mathrm{i}} A^{N}\) are equivalent (Gödel, 1933; Gentzen found the same translation in the same year). The key is to put a double negation on atomic formulas too and to express \(\lor\) and \(\exists\) with negations. Every translated formula then has a shape from which \(A^{N}\) follows from \(\neg\neg A^{N}\) in intuitionistic logic (a <b>stable</b> formula). Merely removing \(\lor\) and \(\exists\) is not enough: an atomic formula \(P\) contains neither, yet \(\neg\neg P \to P\) cannot be proved in intuitionistic logic.</p>`) },
    { id: "embed", h: () => L1(__T(1751), "The two logics are connected"), body: () => L1(
      String.raw`<p>翻訳によって、古典論理で証明できることは、形を変えれば直観主義論理でも証明できます。古典論理は、直観主義論理の中に<b>埋め込まれて</b>いるのです。</p>
       <p>特に、\(\bot\) の訳は \(\bot\) のままなので、古典論理で矛盾が導けるなら、直観主義論理でも矛盾が導けます。算術でも同じで、ペアノ算術（古典論理）が矛盾するなら、ハイティング算術（直観主義論理）も矛盾します。</p>
       <p>古典論理と直観主義論理は対立しているのではなく、同じ命題を違う規則で見ているのです（物語の「魔導書を使う者」と「術を禁忌とする者」は、この二つの立場にあたります）。</p>`,
      String.raw`<p>Through translation, whatever can be proved in classical logic can, in a changed form, be proved in intuitionistic logic too. Classical logic is <b>embedded</b> in intuitionistic logic.</p>
       <p>In particular, the translation of \(\bot\) is \(\bot\) itself, so if a contradiction can be derived in classical logic, one can be derived in intuitionistic logic too. The same holds for arithmetic: if Peano arithmetic (classical) were inconsistent, so would be Heyting arithmetic (intuitionistic).</p>
       <p>Classical and intuitionistic logic are not opposed; they look at the same propositions under different rules ("those who use the grimoire" and "those who forbid the spell" in the story stand for these two positions).</p>`) },
    { id: "more", h: () => L1(__T(1501), "References"), body: () => L1(
      `${bkRefs(["glivenko", "kuroda", "godel33a", "gentzen36", "tvd"])}`,
      `${bkRefs(["glivenko", "kuroda", "godel33a", "gentzen36", "tvd"])}`) },
  ] },
  selfref: { color: "#2c4a63", title: () => L1(__T(1752), "The Book of Self-Reference and Computation"), desc: () => L1(__T(1753), "Self-reference, and the limits of mechanical methods"), sections: [
    { id: "barber", h: () => L1(__T(1754), "The barber and Russell"), body: () => L1(
      String.raw`${KEY(String.raw`\(\vdash \neg\exists y\,\forall x\,(K(y,x)\leftrightarrow\neg K(x,x))\)`)}
       <p>17-1 では、\(\leftrightarrow\) を二つの \(\to\) の \(\land\) として書きました。そのような鍵師 \(a\) がいたとすると、\(x\) に \(a\) 自身を当てはめて \(K(a,a)\leftrightarrow\neg K(a,a)\) となり、矛盾します。背理法は要りません。</p>
       <p>9-1 の掟は \(\to\) の向きだけだったので、鍵師は存在でき、\(K(p,p)\) が導かれました。</p>
       <!--pg-->
       <p><b>ラッセルのパラドックス</b>：「自分自身を要素としない集合の全体」\(R=\{x \mid x\notin x\}\) を考えると、\(R\in R \leftrightarrow R\notin R\) となり、矛盾します。17-1 の \(K(y,x)\) を「\(x\in y\)」と読み替えたものと同じ形です。</p>
       <p>どんな条件からでも集合を作れるとする素朴な考え方は矛盾するので、公理的集合論（ZF など）では、集合を作る方法を公理で制限しています。</p>`,
      String.raw`${KEY(String.raw`\(\vdash \neg\exists y\,\forall x\,(K(y,x)\leftrightarrow\neg K(x,x))\)`)}
       <p>In 17-1, \(\leftrightarrow\) was written as the \(\land\) of two \(\to\). If such a keysmith \(a\) existed, plugging \(a\) itself into \(x\) would give \(K(a,a)\leftrightarrow\neg K(a,a)\), a contradiction. No reductio is needed.</p>
       <p>The law in 9-1 had only the \(\to\) direction, so the keysmith could exist, and \(K(p,p)\) followed.</p>
       <!--pg-->
       <p><b>Russell's paradox</b>: consider "the set of all sets that are not members of themselves", \(R=\{x \mid x\notin x\}\). Then \(R\in R \leftrightarrow R\notin R\), a contradiction. It has the same shape as 17-1 with \(K(y,x)\) read as "\(x\in y\)".</p>
       <p>The naive idea that any condition defines a set is contradictory, so axiomatic set theories (such as ZF) restrict by axioms the ways sets can be formed.</p>`) },
    { id: "diag", h: () => L1(__T(1755), "The diagonal argument"), body: () => L1(
      String.raw`${KEY(String.raw`\(\vdash \forall y\,\exists x\,\neg(D(y,x)\leftrightarrow\neg D(x,x))\)`)}
       <p>17-2 の証人は、判定機械 \(y\) 自身でした。機械たちの答えを表に並べ、対角線上の答えをすべて反転させた新しい列を作ると、この列はどの機械の答えとも一致しません。機械 \(y\) の答えとは、入力 \(y\) のところで必ず食い違うからです。</p>
       <p><b>カントール</b>：自然数から、自然数の集合全体への全射 \(f\) はありません。\(S=\{n \mid n\notin f(n)\}\) が \(f(m)\) だとすると、\(m\in S \leftrightarrow m\notin f(m)=S\) となるからです。\(D(y,x)\) を「\(x\in f(y)\)」と読めば、17-2 と同じ形です。</p>
       <!--pg-->
       <p><b>停止問題</b>（チューリング、1936）：どんなプログラム \(p\) と入力 \(x\) についても「\(p\) は \(x\) を与えると止まるか」を正しく答えるプログラム \(H\) はありません。</p>
       <p>もしあれば、「\(H\) が『\(p\) は \(p\) 自身を与えると止まる』と答えたら永遠に回り続け、そうでなければ止まる」プログラム \(D\) を作れます。\(D\) に \(D\) 自身を与えると、止まるなら止まらず、止まらないなら止まることになり、矛盾します。</p>`,
      String.raw`${KEY(String.raw`\(\vdash \forall y\,\exists x\,\neg(D(y,x)\leftrightarrow\neg D(x,x))\)`)}
       <p>The witness in 17-2 was the deciding machine \(y\) itself. Arrange the machines' answers in a table and make a new column by flipping every answer on the diagonal: this column agrees with no machine's answers, because it always differs from machine \(y\)'s answers at input \(y\).</p>
       <p><b>Cantor</b>: there is no surjection \(f\) from the natural numbers onto the sets of natural numbers. If \(S=\{n \mid n\notin f(n)\}\) were \(f(m)\), then \(m\in S \leftrightarrow m\notin f(m)=S\). Reading \(D(y,x)\) as "\(x\in f(y)\)" gives the same shape as 17-2.</p>
       <!--pg-->
       <p><b>The halting problem</b> (Turing, 1936): there is no program \(H\) that correctly answers, for every program \(p\) and input \(x\), "does \(p\) halt when given \(x\)?"</p>
       <p>If there were, one could write a program \(D\) that "runs forever if \(H\) answers '\(p\) halts when given \(p\) itself', and halts otherwise". Given \(D\) itself, \(D\) would halt if and only if it does not halt — a contradiction.</p>`) },
    { id: "decide", h: () => L1(__T(1756), "What can and cannot be decided"), body: () => L1(
      String.raw`<p><b>命題論理</b>は判定できます。原子命題が \(n\) 個なら真理値の割り当ては \(2^{n}\) 通りなので、すべて調べれば証明できるかどうかが分かります。直観主義の命題論理も、有限のクリプキモデルを調べれば判定できます（このゲームが第 6 層まで行き止まりを知らせられるのは、このためです。健全性と完全性の書を参照）。</p>
       ${KEY(__T(1757), __T(1758))}
       <p>証明を短い順にすべて並べていけば、証明できる式はいつか見つかります。けれども証明できない式については、いつまで待っても「証明はない」と分かる保証がありません。反例の構造が無限にしかないこともあります。たとえば、「小さい」という関係について「自分自身より小さいものはない」「推移的である」「どの元にも、それより大きい元がある」という公理を満たす構造は、無限でなければなりません。（直観主義論理でも、H2-4 の塔のように、反例が無限の塔にしかない式があります。）</p>`,
      String.raw`<p><b>Propositional logic</b> is decidable. With \(n\) atomic propositions there are \(2^{n}\) truth assignments, so checking them all tells whether a formula is provable. Intuitionistic propositional logic is decidable too, by checking finite Kripke models (this is why the game can tell you about dead ends up to Level 6; see the Book of Soundness and Completeness).</p>
       ${KEY("In first-order logic there is no mechanical method to decide provability", "(Church, Turing, 1936)")}
       <p>Listing all proofs in order of length, any provable formula is eventually found. But for an unprovable formula there is no guarantee that, however long you wait, you will learn "there is no proof". Its counterexamples may all be infinite. For example, a structure satisfying the axioms that the relation "smaller than" has nothing smaller than itself, is transitive, and gives every element a larger one, must be infinite. (In intuitionistic logic too, some formulas have counterexamples only in infinite towers, like the one in H2-4.)</p>`) },
    { id: "check", h: () => L1(__T(1759), "Checking and deciding"), body: () => L1(
      String.raw`<p>与えられた証明が正しいかどうかは、規則を一つずつ照らし合わせれば機械的に確かめられます（証明の検査は<b>決定可能</b>）。このゲームの「検査に合格」も、Lean のような証明支援系も、この確認をしています。証明を \(\lambda\) 項として見れば、これは型検査にあたります（含意の書　下巻）。</p>
       <p>この検査ができるので、証明の候補を短い順にすべて並べて一つずつ検査すれば、証明できる式の証明はいつか必ず見つかります。つまり、述語論理で証明できる式の集まりは、機械で一つずつ数え上げられます（<b>計算可能枚挙</b>、半決定可能）。</p>
       <p>機械にできないのは、どんな式についても「証明できるか、できないか」を有限の時間で必ず答えることです（<b>証明可能性の判定</b>、前の節）。数え上げを続けても、証明できない式については、答えが出ないまま終わりません。</p>
       <p>これは、人間と機械の能力の差ではありません。人が見つけた証明も、機械が検査できる形で書かれていなければならず、人にも、証明可能性を判定する万能の方法はありません。物語で、あらゆる扉を見分ける機械が作れなかったのは、この判定の不可能性にあたります。</p>`,
      String.raw`<p>Whether a given proof is correct can be checked mechanically by matching the rules one by one (proof checking is <b>decidable</b>). The game's "check passed" and proof assistants such as Lean both perform this check. Viewing proofs as \(\lambda\)-terms, it corresponds to type checking (The Book of Implication, Vol. II).</p>
       <p>Because of this, listing all candidate proofs in order of length and checking them one by one eventually finds a proof of every provable formula. In other words, the set of formulas provable in first-order logic can be listed one by one by a machine (it is <b>computably enumerable</b>, i.e. semi-decidable).</p>
       <p>What no machine can do is to answer, for every formula and in finite time, whether it is provable or not (<b>deciding provability</b>; previous section). For an unprovable formula, the enumeration simply goes on without ever giving an answer.</p>
       <p>This is not a difference between the abilities of people and machines: a proof found by a person must also be written in a form a machine can check, and people have no universal method for deciding provability either. In the story, the machine that tells every door apart could not be built; that corresponds to this impossibility of deciding provability.</p>`) },
    { id: "consis", h: () => L1(__T(1760), "Consistency and independence"), body: () => L1(
      String.raw`${KEY(__T(1761))}
       <p>健全性から分かります（17-3）。逆に、矛盾しない理論には必ずそれを満たすモデル（構造）があります（ゲーデルの完全性定理）。ただし、そのモデルは無限かもしれません。</p>
       <!--pg-->
       ${KEY(String.raw`\(A\) が偽の構造と \(A\) が真の構造がどちらも \(T\) を満たせば`, String.raw`\(T \nvdash A\) かつ \(T \nvdash \neg A\)`)}
       <p>このとき \(A\) は \(T\) から<b>独立</b>です（17-4、17-5）。有名な例に、平行線公準（ほかのユークリッド幾何の公理から独立）、選択公理（ZF から独立）、連続体仮説（ZFC から独立。ゲーデル 1938、コーエン 1963）があります。</p>`,
      String.raw`${KEY("If some structure satisfies all the axioms of a theory \\(T\\), then \\(\\bot\\) cannot be proved from \\(T\\)")}
       <p>This follows from soundness (17-3). Conversely, every consistent theory has a model (a structure satisfying it) (Gödel's completeness theorem) — though that model may be infinite.</p>
       <!--pg-->
       ${KEY(String.raw`If a structure where \(A\) is false and one where \(A\) is true both satisfy \(T\)`, String.raw`then \(T \nvdash A\) and \(T \nvdash \neg A\)`)}
       <p>Then \(A\) is <b>independent</b> of \(T\) (17-4, 17-5). Famous examples are the parallel postulate (independent of the other axioms of Euclidean geometry), the axiom of choice (independent of ZF), and the continuum hypothesis (independent of ZFC; Gödel 1938, Cohen 1963).</p>`) },
    { id: "godel", h: () => L1(__T(1762), "Gödel's incompleteness theorems"), body: () => L1(
      String.raw`${KEY(__T(1763), __T(1764), __T(1765))}
       ${KEY(__T(1766))}
       <p>第一定理はゲーデル（1931）により、反証できない側の条件はロッサー（1936）が「無矛盾」だけに弱めました。</p>
       <!--pg-->
       <p><b>考え方</b>：式や証明に番号を付け（ゲーデル数）、「番号 \(n\) の式は \(T\) で証明できる」という性質を算術の式 \(\mathrm{Prov}_T(n)\) で表します。そのうえで、対角線論法と同じ発想で、次のような文 \(G\) を作ります（\(\ulcorner G\urcorner\) は \(G\) の番号）。</p>
       ${KEY(String.raw`\(T \vdash G \leftrightarrow \neg\mathrm{Prov}_T(\ulcorner G\urcorner)\)`)}
       <p>\(G\) は「この文は証明できない」と言っている文です。\(T\) が無矛盾なら、\(G\) は \(T\) で証明できません。そして、まさにそのことにより、\(G\) は自然数について正しい文です。</p>
       <p>ただし、この \(G\) が<b>反証も</b>できないことを示すには、ゲーデルの元の証明では、無矛盾性より強い「ω 無矛盾性」という条件が必要でした。ロッサーは \(G\) とは別の文（「自分に証明があるなら、それより短い、自分の否定の証明がある」と言う文）を作り、無矛盾性だけから、証明も反証もできないことを示しました。</p>
       <!--pg-->
       <p>第二定理は、「\(T\) が無矛盾なら \(G\) は証明できない」という議論を \(T\) の中で行えることから導かれます。\(T\) が自分の無矛盾性を証明できたら、\(G\) も証明できてしまうからです。この議論を \(T\) の中で行うには、証明可能性を表す式 \(\mathrm{Prov}_T\) が、いくつかの条件（可導性条件）を満たす必要があります（「もう少し詳しく」を参照）。</p>
       <p>なお、より強い理論からは無矛盾性を証明できることがあります（たとえば ZFC からはペアノ算術の無矛盾性が証明できます）。決定不能な文は、公理を強くすれば決まることもあります。けれども、そのたびに新しい決定不能な文が現れます（ゲームの「決まらない扉」は、この決定不能な文にあたります）。</p>`,
      String.raw`${KEY("First incompleteness theorem: a consistent theory \\(T\\) whose axioms can be listed mechanically", "and which contains a certain amount of arithmetic", "has an arithmetical sentence that \\(T\\) can neither prove nor refute")}
       ${KEY("Second incompleteness theorem: such a \\(T\\) cannot prove its own consistency")}
       <p>The first theorem is due to Gödel (1931); Rosser (1936) weakened the condition needed for the unrefutable side to mere consistency.</p>
       <!--pg-->
       <p><b>The idea</b>: number formulas and proofs (Gödel numbering), and express "the formula with number \(n\) is provable in \(T\)" by an arithmetical formula \(\mathrm{Prov}_T(n)\). Then, with the same idea as the diagonal argument, build a sentence \(G\) such that (\(\ulcorner G\urcorner\) is the number of \(G\)):</p>
       ${KEY(String.raw`\(T \vdash G \leftrightarrow \neg\mathrm{Prov}_T(\ulcorner G\urcorner)\)`)}
       <p>\(G\) says "this sentence is not provable". If \(T\) is consistent, \(G\) is not provable in \(T\) — and precisely because of that, \(G\) is a true statement about the natural numbers.</p>
       <p>However, to show that this \(G\) cannot be <b>refuted</b> either, Gödel's original proof needed a condition stronger than consistency, called ω-consistency. Rosser built a different sentence (one saying "if I have a proof, then my negation has a shorter proof") and showed, from consistency alone, that it can be neither proved nor refuted.</p>
       <!--pg-->
       <p>The second theorem follows because the argument "if \(T\) is consistent, then \(G\) is not provable" can be carried out inside \(T\). If \(T\) could prove its own consistency, it could also prove \(G\). To carry out this argument inside \(T\), the formula \(\mathrm{Prov}_T\) expressing provability has to satisfy some conditions (the derivability conditions; see "A little more").</p>
       <p>A stronger theory can sometimes prove the consistency (for example, ZFC proves the consistency of Peano arithmetic). An undecidable sentence may become decided when the axioms are strengthened. But each time, new undecidable sentences appear (the "undecided doors" of the game correspond to such sentences).</p>`) },
    { id: "more", h: () => L1(__T(1351), "A little more"), body: () => L1(
      String.raw`<details><summary>完全性定理と不完全性定理</summary><p>名前は似ていますが、別の定理です。完全性定理（ゲーデル、1930）は、一階述語論理では「すべての構造で正しい式は証明できる」ことを言います。不完全性定理は、算術を含む理論では「正しいのに証明できない文がある」ことを言います。前者は論理の規則についての、後者は公理（ゲームでは掟）についての話です。</p></details>
       <details><summary>第二不完全性定理と、証明可能性述語の選び方</summary><p>第二不完全性定理の「自分自身の無矛盾性」は、無矛盾性を表す文 \(\neg\mathrm{Prov}_T(\ulcorner 0=1\urcorner)\) を、どの証明可能性述語 \(\mathrm{Prov}_T\) で書くかに依存します。ヒルベルト＝ベルナイス（1939）とレーブ（1955）は、証明可能性述語が三つの条件（可導性条件 D1〜D3）を満たせば、第二定理が成り立つことを示しました。ゲーデルが作った自然な述語は、この条件を満たします。</p><p>一方、外から見れば同じ「証明できる式」の集まりを表すのに、第二定理が成り立たない述語もあります。たとえば、「証明があり、それより短い否定の証明はない」と言うロッサー型の述語では、その述語で書いた無矛盾性の文が、ペアノ算術で証明できてしまいます。フェファーマン（1960）は、公理の集まりの表し方を変えるだけで、無矛盾性の文が証明できるようになる例を示しました。第二定理は、無矛盾性を「自然に」表したときに成り立つ定理であり、どの条件があれば成り立つかは、今も研究が続いています（荒井 1990、倉橋 2020 など）。</p></details>
       <details><summary>参考文献</summary>${bkRefs(["godel31", "rosser36", "turing", "church", "cantor91", "godel30", "godel38", "cohen63", "smullyan", "hilbertbernays39", "lob55", "feferman60", "arai90", "kurahashi20", "kurahashi19"])}</details>`,
      String.raw`<details><summary>Completeness and incompleteness</summary><p>The names are similar, but they are different theorems. The completeness theorem (Gödel, 1930) says that in first-order logic "a formula true in every structure is provable". The incompleteness theorems say that in theories containing arithmetic "there are true sentences that cannot be proved". The former is about the rules of logic; the latter is about the axioms ("laws" in the game).</p></details>
       <details><summary>The second incompleteness theorem and the choice of provability predicate</summary><p>The "own consistency" in the second incompleteness theorem depends on which provability predicate \(\mathrm{Prov}_T\) is used to write the consistency statement \(\neg\mathrm{Prov}_T(\ulcorner 0=1\urcorner)\). Hilbert and Bernays (1939) and Löb (1955) showed that the second theorem holds when the provability predicate satisfies three conditions (the derivability conditions D1–D3). The natural predicate Gödel constructed satisfies them.</p><p>On the other hand, there are predicates that, seen from outside, define the same set of "provable formulas" but for which the second theorem fails. For example, with a Rosser-style predicate, which says "there is a proof, and no shorter proof of the negation", the consistency statement written with that predicate is provable in Peano arithmetic. Feferman (1960) gave examples where merely changing how the set of axioms is represented makes the consistency statement provable. The second theorem holds when consistency is expressed "naturally", and which conditions suffice for it is still being studied (Arai 1990, Kurahashi 2020, and others).</p></details>
       <details><summary>References</summary>${bkRefs(["godel31", "rosser36", "turing", "church", "cantor91", "godel30", "godel38", "cohen63", "smullyan", "hilbertbernays39", "lob55", "feferman60", "arai90", "kurahashi20", "kurahashi19"])}</details>`) },
  ] },
});
Object.assign(ARCHIVES, { "tr-1": ["transl"], "core-1": ["selfref"] });
Object.assign(BOOKS, { // 問答帳：鍵師の問いと、フードの客の答え（ストーリーがオンのときだけ書庫に並ぶ）
  qa1: { color: "#7a6a4a", notebook: true, title: () => L1(__T(1767), "Q&A notebook I"), desc: () => L1(__T(1768), "Questions by the keysmith, answers by the hooded customer"), sections: [
    { id: "qa", h: () => L1(__T(1769), "Dialogue"), body: () => L1(__T(1770), `<p class="qa-q"><b>Question</b>　Why can't a key picked up inside a room be taken outside?</p><p class="qa-a"><b>Answer</b>　That key is valid only under that room's assumption. When you leave the room, the assumption is discharged.</p>`) } ] },
  qa2: { color: "#7a6a4a", notebook: true, title: () => L1(__T(1771), "Q&A notebook II"), desc: () => L1(__T(1768), "Questions by the keysmith, answers by the hooded customer"), sections: [
    { id: "qa", h: () => L1(__T(1769), "Dialogue"), body: () => L1(__T(1772), `<p class="qa-q"><b>Question</b>　Why does the crack of contradiction lead to every door?</p><p class="qa-a"><b>Answer</b>　Under contradictory assumptions, I made every door open. Otherwise the rules would not close.</p>`) } ] },
  qa3: { color: "#7a6a4a", notebook: true, title: () => L1(__T(1773), "Q&A notebook III"), desc: () => L1(__T(1768), "Questions by the keysmith, answers by the hooded customer"), sections: [
    { id: "qa", h: () => L1(__T(1769), "Dialogue"), body: () => L1(__T(1774), `<p class="qa-q"><b>Question</b>　Why does the spell not show what lies beyond the door it opens?</p><p class="qa-a"><b>Answer</b>　The spell shows only the contradiction that follows from assuming "the door does not open".</p>`) } ] },
  qa4: { color: "#7a6a4a", notebook: true, title: () => L1(__T(1775), "Q&A notebook IV"), desc: () => L1(__T(1768), "Questions by the keysmith, answers by the hooded customer"), sections: [
    { id: "qa", h: () => L1(__T(1769), "Dialogue"), body: () => L1(__T(1776), `<p class="qa-q"><b>Question</b>　Can the doors opened with the grimoire be conveyed to those who forbid the spell?</p><p class="qa-a"><b>Answer</b>　I am looking for a way to translate them.</p>`) } ] },
  qa5: { color: "#7a6a4a", notebook: true, title: () => L1(__T(1777), "Q&A notebook V"), desc: () => L1(__T(1768), "Questions by the keysmith, answers by the hooded customer"), sections: [
    { id: "qa", h: () => L1(__T(1769), "Dialogue"), body: () => L1(__T(1778), `<p class="qa-q"><b>Question</b>　Why can't someone whose name is unknown be taken out of the room?</p><p class="qa-a"><b>Answer</b>　That one's name is assigned only inside the room.</p>`) } ] },
  qa6: { color: "#7a6a4a", notebook: true, title: () => L1(__T(1779), "Q&A notebook VI"), desc: () => L1(__T(1768), "Questions by the keysmith, answers by the hooded customer"), sections: [
    { id: "qa", h: () => L1(__T(1769), "Dialogue"), body: () => L1(__T(1780), `<p class="qa-q"><b>Question</b>　Does a keysmith who makes the keys of exactly those who do not make their own keys make his own key?</p><p class="qa-a"><b>Answer</b>　I reserve my answer.</p>`) } ] },
  qa7: { color: "#7a6a4a", notebook: true, title: () => L1(__T(1781), "Q&A notebook VII"), desc: () => L1(__T(1768), "Questions by the keysmith, answers by the hooded customer"), sections: [
    { id: "qa", h: () => L1(__T(1769), "Dialogue"), body: () => L1(__T(1782), `<p class="qa-q"><b>Question</b>　Why are there holes lined up in the master's cards?</p><p class="qa-a"><b>Answer</b>　The pattern of holes remembers the shape of the theorem.</p>`) } ] },
  qa8: { color: "#7a6a4a", notebook: true, title: () => L1(__T(1783), "Q&A notebook VIII"), desc: () => L1(__T(1768), "Questions by the keysmith, answers by the hooded customer"), sections: [
    { id: "qa", h: () => L1(__T(1769), "Dialogue"), body: () => L1(__T(1784), `<p class="qa-q"><b>Question</b>　There are doors for which no key is found, however long one searches.</p><p class="qa-a"><b>Answer</b>　There are.</p><p class="qa-q"><b>Question</b>　Then can one know that they do not open?</p><p class="qa-a"><b>Answer</b>　That is a different problem.</p>`) } ] },
  qa9: { color: "#7a6a4a", notebook: true, title: () => L1(__T(1785), "Q&A notebook IX"), desc: () => L1(__T(1768), "Questions by the keysmith, answers by the hooded customer"), sections: [
    { id: "qa", h: () => L1(__T(1769), "Dialogue"), body: () => L1(__T(1786), `<p class="qa-q"><b>Question</b>　Why do you know the answers?</p><p class="qa-a"><b>Answer</b>　I do not. I only check. Matching the rules one by one is something I can do too.</p>`) } ] },
  qa11: { color: "#7a6a4a", notebook: true, title: () => L1(__T(1787), "Q&A notebook X"), desc: () => L1(__T(1768), "Questions by the keysmith, answers by the hooded customer"), sections: [
    { id: "qa", h: () => L1(__T(1769), "Dialogue"), body: () => L1(__T(1788), `<p class="qa-q"><b>Question</b>　Do the numbers have an end?</p><p class="qa-a"><b>Answer</b>　The laws of addition and induction alone do not decide it. A tower with a ceiling can be built while keeping the laws. Add two more laws, and the ceiling disappears. Please confirm it on the top floor of the Tower of Order.</p>`) } ] },
  qa10: { color: "#7a6a4a", notebook: true, title: () => L1(__T(1789), "Q&A notebook XI"), desc: () => L1(__T(1768), "Questions by the keysmith, answers by the hooded customer"), sections: [
    { id: "qa", h: () => L1(__T(1769), "Dialogue"), body: () => L1(__T(1790), `<p class="qa-q"><b>Question</b>　Can a machine be made that decides, for every door, whether it opens?</p><p class="qa-a"><b>Answer</b>　In general, it cannot be made. The reason cannot be checked in words alone. I have arranged the doors. Please come to the core.</p>`) } ] }
});
// 問答帳の頁は書庫には置かず、「冒険の記録」で読む。各頁は、その層（最初のステージの元の番号）にたどり着くと読める
const QA_AT = { qa1: "2-1", qa2: "4-1", qa3: "6-1", qa4: "5-1", qa5: "7-3", qa6: "f-barber", qa7: "9-1", qa8: "11-1", qa9: "14-1", qa11: "15-1", qa10: "x-total" }; // qa11 は寄り道 3（順序の塔）。並びの都合で「十」とし、最後の頁を「十一」にした
const shelfIds = ak => (ARCHIVES[ak] || []).filter(id => !BOOKS[id].notebook || storyOn());
const archKey = w => w && w.stages.length && ARCHIVES[w.stages[0].oldId] ? w.stages[0].oldId : null;
const archWorld = ak => WORLDS.find(w => archKey(w) === ak);
const bookArch = id => Object.keys(ARCHIVES).find(ak => ARCHIVES[ak].includes(id));
const bookWorld = id => archWorld(bookArch(id));
const bookRead = id => !!(PROG.booksRead && PROG.booksRead[id]);
const BOOK_ORDER = () => Object.keys(ARCHIVES).filter(ak => archWorld(ak)).flatMap(ak => ARCHIVES[ak]);
const ICON_BOOK = `<svg class="bk-ic" viewBox="0 0 24 24" aria-hidden="true"><path d="M4 5.5A2.5 2.5 0 0 1 6.5 3H20v15H6.5A2.5 2.5 0 0 0 4 20.5z" fill="none" stroke="currentColor" stroke-width="1.6"/><path d="M4 20.5A2.5 2.5 0 0 1 6.5 18H20v3H6.5A2.5 2.5 0 0 1 4 20.5z" fill="none" stroke="currentColor" stroke-width="1.6"/><path d="M8 7h8M8 10h6" stroke="currentColor" stroke-width="1.4"/></svg>`;
// 最終層では、変身のあと、書庫がコンピュータ室になる
const ICON_TERM = `<svg class="bk-ic" viewBox="0 0 24 24" aria-hidden="true"><rect x="3" y="4" width="18" height="12" rx="1.6" fill="none" stroke="currentColor" stroke-width="1.6"/><path d="M7 9l2.5 2L7 13M11.5 13H16" fill="none" stroke="currentColor" stroke-width="1.4" stroke-linecap="round" stroke-linejoin="round"/><path d="M9 20h6M12 16v4" stroke="currentColor" stroke-width="1.6"/></svg>`;
const arcSF = w => !!(w && w.final && SF_NOW);
const arcName = w => arcSF(w) ? L1(__T(1791), "Computer room") : L1(__T(1792), "Archive");
function bookTileHTML(w) { // 層の最後に置く書庫の書棚。押すと、どの書物を読むかを選ぶ
  const ak = archKey(w); if (!ak) return "";
  const ids = ARCHIVES[ak], unread = ids.filter(id => !bookRead(id)).length, isNew = unread && worldOpen(w); // New は、その層に入れるようになってから
  if (w.final) return `<button class="tile book-tile term-tile${unread ? "" : " done"}${SF_NOW ? " sf-x" : ""}" type="button" data-archive="${ak}" aria-label="${arcName(w)}">
    <span class="arc-c"><span class="tile-top"><span class="tile-id">${ICON_BOOK}</span><span class="tile-name">${L1(__T(1792), "Archive")}</span>${isNew ? `<span class="new-badge">New</span>` : ""}</span>
    <span class="tile-seq">${L1(__T(1793, [ids.length]), `${ids.length} book${ids.length > 1 ? "s" : ""}`)}</span>
    <span class="tile-status">${unread ? L1(__T(1794), "See the books ▸") : L1(__T(1795), "All read · See the books ▸")}</span></span>
    <span class="arc-s"><span class="term-rack" aria-hidden="true"></span><span class="tile-top"><span class="tile-id">${ICON_TERM}</span><span class="tile-name">${L1(__T(1791), "Computer room")}</span>${isNew ? `<span class="new-badge">New</span>` : ""}</span>
    <span class="tile-seq">${L1(__T(1796, [ids.length]), `${ids.length} document${ids.length > 1 ? "s" : ""}`)}</span>
    <span class="tile-status">${unread ? L1(__T(1797), "Open the terminal ▸") : L1(__T(1798), "All read · Open the terminal ▸")}</span></span></button>`;
  return `<button class="tile book-tile${unread ? "" : " done"}" type="button" data-archive="${ak}" aria-label="${L1(__T(1792), "Archive")}">
    <span class="tile-top"><span class="tile-id">${ICON_BOOK}</span><span class="tile-name">${L1(__T(1792), "Archive")}</span>${isNew ? `<span class="new-badge">New</span>` : ""}</span>
    <span class="tile-seq">${L1(__T(1793, [ids.length]), `${ids.length} book${ids.length > 1 ? "s" : ""}`)}</span>
    <span class="tile-status">${unread ? L1(__T(1794), "See the books ▸") : L1(__T(1795), "All read · See the books ▸")}</span></button>`;
}
function archiveHTML(ak) {
  const arcOpen = (w => !w || worldOpen(w))(WORLDS.find(x => archKey(x) === ak)); // New は、その層に入れるようになってから // 書庫の中：書物を選ぶ
  const w = archWorld(ak), ids = shelfIds(ak);
  return `<div class="archive"><div class="bk-head">${arcSF(w) ? ICON_TERM : ICON_BOOK}<div><div class="bk-layer">${WQ(w)}</div><h2>${arcName(w)}</h2></div></div>
    <p class="note">${arcSF(w) ? L1(__T(1799), "Documents explaining the theory behind the doors of this level. Choose a document to read on the terminal.") : L1(__T(1800), "Books explaining the inference rules used on this level. Choose a book to read.")}</p>
    <div class="arc-books">${ids.map(id => { const b = BOOKS[id], n = bookPages(id).length;
      return `<button type="button" class="arc-book${b.notebook ? " nb" : ""}" data-book="${id}" style="--bk:${b.color}"><span class="arc-spine"></span><span class="arc-body"><b>${b.title()}</b><span class="arc-desc">${b.desc()}</span><span class="arc-meta">${L1(__T(1801, [n]), `${n} pages`)}${L1("　", " · ")}${bookRead(id) ? L1(__T(1802), "✓ Read") : arcOpen ? `<span class="new-badge">New</span>` : ""}</span></span></button>`; }).join("")}</div>
    <div class="actions"><button class="btn" type="button" data-cmd="library">${L1(__T(1803), "All books")}</button><button class="btn primary" type="button" data-cmd="close">${L1(__T(1804), "Close")}</button></div></div>`;
}
function openArchive(ak) { closeModal(); BOOK_UI = null; showModal(archiveHTML(ak), true); const m = document.querySelector(".overlay .modal"); if (m) m.classList.add("book-modal"); }
let BOOK_UI = null; // いま開いている書物と、そのページ
/* 書物の数式：\( … \) と \[ … \] を MathJax（SVG 出力）で組版する。書物を初めて開いたときにだけ読み込む */
const MJ_SRC = "https://cdnjs.cloudflare.com/ajax/libs/mathjax/3.2.2/es5/tex-svg.min.js";
let MJ_READY = null;
function mathLoad() {
  if (MJ_READY) return MJ_READY;
  MJ_READY = new Promise(res => {
    try {
      window.MathJax = { tex: { inlineMath: [["\\(", "\\)"]], displayMath: [["\\[", "\\]"]] }, svg: { fontCache: "global" }, startup: { typeset: false }, options: { enableMenu: false } };
      const sc = document.createElement("script"); sc.src = MJ_SRC; sc.async = true;
      sc.onload = () => { (window.MathJax && MathJax.startup ? MathJax.startup.promise : Promise.resolve()).then(() => res(true), () => res(false)); };
      sc.onerror = () => res(false);
      document.head.appendChild(sc);
      setTimeout(() => res(false), 15000);
    } catch (e) { res(false); }
  });
  return MJ_READY;
}
async function mathTypeset(el) {
  if (!el || !/\\\(|\\\[/.test(el.textContent)) return false;
  const ok = await mathLoad();
  if (ok && window.MathJax && MathJax.typesetPromise) { try { await MathJax.typesetPromise([el]); return true; } catch (e) {} }
  return false;
}
async function bookLayout() { // 数式を組版し、すべてのページの高さをそろえる（いちばん高いページに合わせる）
  if (!BOOK_UI) return;
  const ui = BOOK_UI, cur = document.querySelector(".overlay .book .bk-page"); if (!cur) return;
  mathTypeset(cur.closest(".book") || cur); // 見出しの目次も含めて組版する
  const width = cur.clientWidth, key = ui.key + ":" + width;
  if (ui.hKey !== key) {
    const meas = document.createElement("section"); meas.className = "bk-sec bk-page"; meas.setAttribute("aria-hidden", "true");
    meas.style.cssText = `position:absolute;left:-10000px;top:0;width:${width}px;min-height:0;visibility:hidden`;
    cur.parentNode.appendChild(meas);
    let h = 0;
    for (const pg of bookPages(ui.key)) { meas.innerHTML = `<h3>${pg.h}<span class="bk-pn">(9/9)</span></h3>${pg.html}`; await mathTypeset(meas); h = Math.max(h, meas.scrollHeight); }
    meas.remove();
    if (BOOK_UI !== ui) return;
    ui.h = h; ui.hKey = key;
  }
  const now = document.querySelector(".overlay .book .bk-page"); if (now && ui.h) now.style.minHeight = ui.h + "px";
}
function bookPages(id) { // 節の本文を、<!--pg--> でページに分ける
  const pages = [];
  BOOKS[id].sections.forEach(sec => {
    const override = LANG === "zh-CN" ? BOOK_ZH_CN[id]?.[sec.id] : null;
    const body = override ? override({ KEY, bkTable, bkRefs }) : sec.body();
    const parts = body.split("<!--pg-->");
    parts.forEach((html, i) => pages.push({ sec: sec.id, h: sec.h(), html, i, n: parts.length }));
  });
  return pages;
}
function bookHTML(id, page = 0) {
  const b = BOOKS[id], w = bookWorld(id), pages = bookPages(id);
  page = Math.max(0, Math.min(page, pages.length - 1));
  const pg = pages[page], last = page === pages.length - 1;
  const order = BOOK_ORDER(), i = order.indexOf(id);
  const nav = (k, dir) => k && worldOpen(bookWorld(k)) ? `<button class="btn" type="button" data-book="${k}">${dir < 0 ? "← " : ""}${BOOKS[k].title()}${dir > 0 ? " →" : ""}</button>` : "";
  return `<div class="book" data-bk-key="${id}">
    <div class="bk-head" style="--bk:${b.color}"><span class="bk-cover">${ICON_BOOK}</span><div><div class="bk-layer">${WQ(w)}${arcSF(w) ? L1(__T(1805), " — Computer room") : L1(__T(1806), " — Archive")}</div><h2>${b.title()}</h2></div>
      <button class="btn small bk-back" type="button" data-archive="${bookArch(id)}">${arcSF(w) ? L1(__T(1807), "← Computer room") : L1(__T(1808), "← Archive")}</button></div>
    <nav class="bk-toc">${b.sections.map(sx => `<button type="button" class="bk-tab${sx.id === pg.sec ? " on" : ""}" data-bk-sec="${sx.id}">${sx.h()}</button>`).join("")}</nav>
    <section class="bk-sec bk-page"><h3>${pg.h}${pg.n > 1 ? `<span class="bk-pn">${L1(__T(1809, [pg.i + 1, pg.n]), ` (${pg.i + 1}/${pg.n})`)}</span>` : ""}</h3>${pg.html}</section>
    <div class="bk-nav"><button class="btn" type="button" data-bk-pg="${page - 1}"${page === 0 ? " disabled" : ""}>◀ ${L1(__T(1810), "Previous")}</button>
      <span class="bk-count">${page + 1} / ${pages.length}</span>
      <button class="btn${last ? "" : " primary"}" type="button" data-bk-pg="${page + 1}"${last ? " disabled" : ""}>${L1(__T(1811), "Next")} ▶</button></div>
    <div class="actions">${nav(order[i - 1], -1)}${nav(order[i + 1], 1)}<button class="btn${last ? " primary" : ""}" type="button" data-cmd="close">${L1(__T(1804), "Close")}</button></div></div>`;
}
function bookGo(page) { // ページをめくる
  if (!BOOK_UI) return;
  const m = document.querySelector(".overlay .modal.book-modal"); if (!m || !m.querySelector(".book")) { BOOK_UI = null; return; }
  const n = bookPages(BOOK_UI.key).length; BOOK_UI.page = Math.max(0, Math.min(page, n - 1));
  m.innerHTML = bookHTML(BOOK_UI.key, BOOK_UI.page); m.scrollTop = 0;
  const pgEl = m.querySelector(".bk-page"); if (pgEl && BOOK_UI.h) pgEl.style.minHeight = BOOK_UI.h + "px";
  bookLayout();
}
function openBook(id, sec) {
  if (!BOOKS[id]) return;
  closeModal();
  const page = sec ? Math.max(0, bookPages(id).findIndex(p => p.sec === sec)) : 0;
  BOOK_UI = { key: id, page };
  showModal(bookHTML(id, page), true);
  const m = document.querySelector(".overlay .modal"); if (m) m.classList.add("book-modal");
  bookLayout();
  PROG.booksRead = PROG.booksRead || {}; PROG.booksRead[id] = true; saveProgress();
  const w = bookWorld(id), tile = document.querySelector(`.book-tile[data-archive="${bookArch(id)}"]`); if (tile && SCREEN === "select") tile.outerHTML = bookTileHTML(w);
}
function cardsHTML() { // 手に入れた定理カードの一覧（入手したステージの順）
  const got = STAGES.filter(st => st.earns && cardGot(st.earns)), all = STAGES.filter(st => st.earns);
  return __T(1812, [ICON_CARD(true), got.length, all.length, PROG.endingSeen ? `<li class="got blank">${PUNCH_CARD(null, false)}<div><b>${PROG.whiteCard ? L1(__T(1813), "The white card") : L1(__T(1814), "Blank card")}</b>${PROG.whiteCard ? `<div class="white-q">${esEsc(PROG.whiteCard)}</div><span class="note">${L1(__T(1815), "Your next question, in your own hand.")}</span>` : `<span class="note">${L1(__T(1816), "Nothing is carved on it yet. For the next question.")}</span>`}</div></li>` : "", all.map(st => cardGot(st.earns)
      ? __T(1817, [PUNCH_CARD(st.earns, false), CARDS[st.earns].name, F(CARDS[st.earns].f), st.id, st.name])
      : __T(1818, [ICON_CARD(false), st.id, st.name])).join("")]);
}
function libraryHTML() {
  return `<h2>${L1(__T(1819), "Library")}</h2><p class="note">${L1(__T(1820), "The books kept in the archive of each level. You can read the books of the levels that are open. Pressing a rule name (such as ∧I) in the proof tree or the move log also opens its explanation.")}</p>
    ${Object.keys(ARCHIVES).filter(ak => archWorld(ak)).map(ak => { const w = archWorld(ak), open = worldOpen(w);
      return `<h3 class="lib-h">${WQ(w)}${open ? "" : `<span class="note">${L1(__T(1821), " — level not open yet")}</span>`}</h3><ul class="lib-list">${shelfIds(ak).map(id => `<li>${open ? `<button type="button" class="lib-item" data-book="${id}" style="--bk:${BOOKS[id].color}">` : `<span class="lib-item locked" style="--bk:${BOOKS[id].color}">`}<span class="lib-spine"></span><span><b>${BOOKS[id].title()}</b><span class="note">${BOOKS[id].desc()}</span></span><span class="lib-st">${!open ? "" : bookRead(id) ? L1(__T(1822), "Read") : "New"}</span>${open ? "</button>" : "</span>"}</li>`).join("")}</ul>`; }).join("")}
    <div class="actions"><button class="btn primary" type="button" data-cmd="close">${L1(__T(1804), "Close")}</button></div>`;
}

// 画面外の層は content-visibility で描画を省く。そのときの仮の高さを、扉の数と画面の幅から見積もっておく
function estimateWorldHeights() {
  const W = (document.querySelector(".worlds") || document.body).clientWidth || window.innerWidth;
  const cols = W >= 1100 ? 4 : W >= 820 ? 3 : W >= 540 ? 2 : 1, rowH = cols === 1 ? 200 : 232;
  document.querySelectorAll(".world").forEach(sec => {
    const n = sec.querySelectorAll(".tile, .book-tile").length;
    const pro = sec.querySelector(".story-prologue") ? (cols === 1 ? 170 : 100) : 0;
    sec.style.containIntrinsicSize = `auto ${90 + pro + Math.ceil(n / cols) * rowH}px`;
  });
}
// 最終層の近未来の見た目：最終層をクリックすると変身し、以後は最終層が見えている間だけ背景も変わる
let SF_OBS = null;
let SF_NOW = false; // いま最終層が変身した姿か（保存しない。最終層以外のステージに入ると元の姿に戻り、また変身を見られる）
function sfBgLayer() { if (!document.getElementById("sfBg")) { const d = document.createElement("div"); d.id = "sfBg"; document.body.prepend(d); } }
function sfBg(on) { sfBgLayer(); document.body.classList.toggle("sf-bg", !!on); }
function sfFlash(ms = 1300) { const f = document.createElement("div"); f.id = "sfFlash"; f.dataset.msg = __T(1823); f.style.animationDuration = ms + "ms"; document.body.appendChild(f); setTimeout(() => f.remove(), ms + 300); }
function sfParts(sec) { return [sec.querySelector(".world-head"), sec.querySelector(".story-prologue"), ...sec.querySelectorAll(".tile")].filter(Boolean); }
const finalOpen = () => { const fw = WORLDS.find(w => w.final); return !!fw && worldOpen(fw); }; // 最終層に入れるか（制限なしモードなら常に）
function sfActivate(sec) { // 変身：層全体が乱れたあと、見出し → 語り → 扉の順に一つずつ切り替わる（約 3.5 秒）
  if (!sec || sec.classList.contains("sf-busy") || !finalOpen()) return;
  if (sec.classList.contains("sf-on")) { sfBg(true); return; }
  SF_NOW = true; PROG.sfSeen = true; saveProgress();
  sec.classList.add("sf-busy", "sf-glitch"); sfFlash(3200);
  const parts = sfParts(sec), T0 = 1000, STEP = 330;
  setTimeout(() => { sec.classList.remove("sf-glitch"); sfBg(true); }, T0);
  parts.forEach((el, k) => setTimeout(() => { el.classList.add("sf-x", "sf-tick"); setTimeout(() => el.classList.remove("sf-tick"), 460); }, T0 + 150 + k * STEP));
  setTimeout(() => { sec.classList.add("sf-on"); sec.classList.remove("sf-busy"); sfObserve(); }, T0 + 150 + parts.length * STEP + 500);
}
function sfObserve() {
  if (SF_OBS) { SF_OBS.disconnect(); SF_OBS = null; }
  const sec = document.querySelector(".w-final.sf-on");
  if (sec) sfParts(sec).forEach(el => el.classList.add("sf-x")); // 変身済みなら、描き直した見出し・語り・扉も近未来風に
  if (!sec || !("IntersectionObserver" in window)) { sfBg(false); return; }
  SF_OBS = new IntersectionObserver(es => es.forEach(e => sfBg(e.isIntersecting && (e.intersectionRatio > 0.2 || e.boundingClientRect.top < window.innerHeight * 0.45))), { threshold: [0, 0.1, 0.2, 0.4, 0.6] });
  SF_OBS.observe(sec);
}
function renderSelect() {
  document.body.classList.remove("sf");
  const done = STAGES.filter(s => PROG.best[s.pid] != null).length;
  const clearedNow = new Set(STAGES.filter(s => PROG.best[s.pid] != null).map(s => s.pid));
  const fresh = SEEN_CLEARED ? new Set([...clearedNow].filter(x => !SEEN_CLEARED.has(x))) : new Set();
  SEEN_CLEARED = clearedNow;
  const next = STAGES.find(s => PROG.best[s.pid] == null && !s.world.extra && stageOpen(s)) || STAGES.find(s => PROG.best[s.pid] == null && stageOpen(s)) || STAGES[0];
  app.innerHTML = __T(1824, [next.id, STAGES.every(x => PROG.best[x.pid] != null) ? L1(__T(1825), "All stages cleared! Review from 1-1") : done ? __T(1826, [next.id]) : __T(1827), PROG.helpSeen ? "" : " pulse-new", PROG.helpSeen ? "" : '<span class="new-badge">New</span>', done, STAGES.length, !!PREFS.story, PROG.cards && Object.keys(PROG.cards).length ? __T(1828, [ICON_CARD(true), STAGES.filter(st => st.earns && cardGot(st.earns)).length, STAGES.filter(st => st.earns).length]) : "", storyOn() ? __T(1829, [ICON_BOOK, qaNew() || memoNew() ? '<span class="new-badge">New</span>' : ""]) : ""]) + WORLDS.map(w => partHeadHTML(w) + __T(1830, [worldOpen(w) ? "" : " w-locked", w.extra ? " w-extra " + (isSidePath(w) ? "w-side" : "w-hidden") : "", w.final ? " w-final" + (SF_NOW ? " sf-on" : "") : "", WL(w), w.name, w.rules, worldLockHTML(w), storyOn() && worldOpen(w) && storyWorld(w) ? `<p class="story-prologue">${storyWorld(w)}</p>` : "", w.stages.map(s => __T(1831, [s.boss ? " boss" : "", PROG.best[s.pid] != null ? " done" : "", fresh.has(s.pid) ? " just-opened" : "", s.id, s.id, s.name, PROG.best[s.pid] != null ? __T(1832) : __T(966), s.id, s.name, s.earns ? `<span class="tile-card${cardGot(s.earns) ? " got" : ""}" data-cardtip="${s.id}" title="${cardTip(s)}" role="img" aria-label="${cardTip(s)}">${ICON_CARD(cardGot(s.earns))}</span>` : "", s.boss ? __T(1833) : "", tileSeq(s), PROG.best[s.pid] != null ? __T(1834) + bestText(s) : s.kind === "judge" ? __T(1835, [s.parts.length]) : s.par == null ? (s.kind === "refute" ? __T(1836) : "") : __T(1837, [s.par, unitOf(s)])])).join("")])).join("") +
  __T(1838);
  app.querySelectorAll("section.world").forEach((sec, i) => { const tl = sec.querySelector(".tiles"); if (tl && WORLDS[i]) tl.insertAdjacentHTML("beforeend", bookTileHTML(WORLDS[i])); }); // 各層の書庫（層のいちばん最後）
  const ha = app.querySelector(".hero-actions");
  const hb = ha && ha.querySelector('[data-cmd="help"]');
  if (hb) hb.insertAdjacentHTML("afterend", `<button class="btn lib-btn" type="button" data-cmd="library">${ICON_BOOK}${L1(__T(1819), "Library")}</button><button class="btn" type="button" data-cmd="credits">${L1(__T(1839), "Credits")}</button>`);
  if (ha) ha.insertAdjacentHTML("beforeend", __T(1840, [!!PREFS.unlockAll]));
  if (fresh.size) requestAnimationFrame(() => { const t = document.querySelector(".tile.just-opened"); if (t && t.scrollIntoView) t.scrollIntoView({ block: "center", behavior: "smooth" }); });
  estimateWorldHeights();
  document.querySelectorAll("main section.world").forEach((sec, i) => { if (WORLDS[i]) sec.dataset.zone = zoneOfWorld(WORLDS[i]); }); // 部ごとの背景
  { const h = document.querySelector("main .hero"); if (h) h.dataset.zone = 1; } setZone(1); zoneWatch();
  heroDecorate();
}
// 題名の箱：左に四角い迷宮の紋（中心に鍵穴）、右に題名と副題。右奥に鉄格子、左から蝋燭の光（光は動かさない）
const HERO_SEAL = `<svg class="hero-seal" viewBox="0 0 120 120" aria-hidden="true"><path class="w" d="M77.0 8.0 L112 8 L112 112 L8 112 L8 8 L8 8 L68.0 8.0"/><path class="w" d="M102.0 47.7 L102 102 L18 102 L18 18 L102 18 L102 18 L102.0 38.7"/><path class="w" d="M52.3 92.0 L28 92 L28 28 L92 28 L92 92 L92 92 L61.3 92.0"/><path class="w" d="M38.0 59.9 L38 38 L82 38 L82 82 L38 82 L38 82 L38.0 68.9"/><path class="w" d="M8 40 H18 M112 78 H102 M70 18 V28 M46 92 V102 M28 54 H38 M92 66 H82 M56 28 V38 M62 82 V92"/><circle class="k" cx="60" cy="57" r="4.2"/><path class="k" d="M57.6 59 L62.4 59 L63.6 68 L56.4 68 Z"/></svg>`;
function heroDecorate() {
  const h = document.querySelector("main .hero"); if (!h || h.querySelector(".hero-head")) return;
  const h1 = h.querySelector("h1"), demo = h.querySelector(".demo"); if (!h1) return;
  const main = LANG === "en" ? "Proof Dungeon" : LANG === "zh-CN" ? "证明迷宫" : h1.textContent, sub = LANG === "en" ? h1.textContent : "PROOF DUNGEON";
  const head = document.createElement("div"); head.className = "hero-head";
  head.innerHTML = HERO_SEAL + `<div class="hero-title"><h1>${main}</h1><div class="hero-rule">${sub}</div></div>`;
  if (demo) head.querySelector(".hero-title").appendChild(demo);
  h1.replaceWith(head);
  const rest = document.createElement("div"); rest.className = "hero-rest";
  [...h.children].filter(c => c !== head).forEach(c => rest.appendChild(c)); h.appendChild(rest);
  if (!h.querySelector(".hero-grate")) h.insertAdjacentHTML("afterbegin", `<span class="hero-grate" aria-hidden="true"></span>`);
}

/* --- プレイ画面 --- */
/* 最初のワールドの案内：まずシーケントに注目させ、鍵・扉・証明図・遊び方の順に、何を見ればよいかを示す */
let GUIDE = null;
// 案内：新しい操作や画面が初めて登場するステージで、関係する場所を光らせて吹き出しで説明する。
// どの案内を出すかは、チュートリアルと同じ「初めて登場するステージ」の情報（STAGE.tut）と、GUIDE_AT から決める
const gqs = sel => document.querySelector(sel);
const gKeyOp = sym => { const b = [...document.querySelectorAll("#rooms .key .mainop")].find(x => x.textContent.trim().startsWith(sym)); return b ? b.closest(".key") : null; };
const gDoorOp = sym => { const b = gqs("#rooms .door .mainop"); return b && (!sym || b.textContent.trim().startsWith(sym)) ? b : null; };
const gKeyWith = (pred) => [...document.querySelectorAll("#rooms .key")].find(k => pred(k.querySelector(".f").textContent.replace(/\s/g, "")));
const GUIDES = {
  basics: st => { const prem = st.prem.map(p => F(p)), hasPrem = prem.length > 0; return [
    { el: () => gqs(".mission .seq"), title: __T(1841), text: __T(1842, [hasPrem ? __T(857, [prem.join(__T(778))]) : __T(1843), F(st.goal)]) },
    { el: () => gqs("#rooms .room"), title: __T(1844), text: hasPrem ? __T(1845, [prem.join(__T(778))]) : __T(1846) },
    { el: () => gqs("#rooms .door"), title: __T(1847), text: __T(1848, [F(st.goal)]) },
    { el: () => gqs("section.proof"), title: __T(1849), text: __T(1850) },
    { el: () => gqs('#tools [data-cmd="help"]'), title: __T(1851), text: __T(1852) },
  ]; },
  andE: () => [
    { el: () => gKeyOp("∧"), title: __T(1853), text: __T(1854) },
    { el: () => gqs("section.proof"), title: __T(1855), text: __T(1856) } ],
  impI: () => [ { el: () => gDoorOp("→"), title: __T(1857), text: __T(1858) } ],
  impE: () => [ { el: () => gKeyWith(t => t.includes("→")), title: __T(1859), text: __T(1860) } ],
  scope: () => [ { el: () => gDoorOp(), title: __T(1861), text: __T(1862) } ],
  orI: () => [ { el: () => gDoorOp("∨"), title: __T(1863), text: __T(1864) } ],
  orE: () => [ { el: () => gKeyOp("∨"), title: __T(1865), text: __T(1866) } ],
  bot: () => [
    { el: () => gKeyWith(t => t.includes("⊥") || t.includes("¬")), title: __T(1867), text: __T(1868) },
    { el: () => gqs("[data-exfalso]"), title: __T(1869), text: __T(1870) } ],
  neg: () => [ { el: () => gDoorOp("¬") || gKeyWith(t => t.includes("¬")) || gqs(".mission .seq"), title: __T(1871), text: __T(1872) } ],
  raa: () => [ { el: () => gqs("[data-raa]"), title: __T(717), text: __T(1873) } ],
  truth: () => [
    { el: () => gqs(".mission .seq"), title: __T(1874), text: __T(1875) },
    { el: () => gqs("#kmodel"), title: __T(1455), text: __T(1876) },
    { el: () => gqs("#kEval"), title: __T(1877), text: __T(1878) },
    { el: () => gqs("#kVerdict"), title: __T(1879), text: __T(1880) } ],
  judge: () => [ { el: () => gqs(".judge"), title: __T(154), text: __T(1881) } ],
  kripke: () => [
    { el: () => gqs(".mission .seq"), title: __T(1882), text: __T(1883) },
    { el: () => gqs("#kmodel"), title: __T(1884), text: __T(1885) },
    { el: () => gqs("#kEval"), title: __T(1886), text: __T(1887) },
    { el: () => gqs("#kVerdict"), title: __T(1879), text: __T(1888) } ],
  allQ: () => [
    { el: () => gDoorOp("∀") || gqs("#rooms .door"), title: __T(1889), text: __T(1890) },
    { el: () => gKeyOp("∀"), title: __T(1891), text: __T(1892) } ],
  names: () => [ { el: () => gqs('[data-cmd="togglenames"]'), title: __T(1893), text: __T(1894) } ],
  exQ: () => [
    { el: () => gKeyOp("∃"), title: __T(1895), text: __T(1896) },
    { el: () => gDoorOp() , title: __T(1897), text: __T(1898) } ],
  struct: () => [
    { el: () => gqs("#kHead .grp"), title: __T(1899), text: __T(1900) },
    { el: () => gqs("#kmodel .pred"), title: __T(1901), text: __T(1902) },
    { el: () => gqs("#kEval"), title: __T(1877), text: __T(1903) } ],
  eq: () => [ { el: () => gqs(".mission .seq"), title: __T(1904), text: __T(1905) } ],
  cards: () => [ { el: () => gqs("#rooms .key.card"), title: __T(264), text: __T(1906) } ],
  defs: () => [ { el: () => gqs("#rooms .mainop.defop"), title: __T(1571), text: __T(1907) } ],
  terms: () => [ { el: () => gKeyOp("∀"), title: __T(1908), text: __T(1909) } ],
  eqboth: () => [ { el: () => gKeyWith(t => t.includes("=") && !t.includes("∀")) || gqs(".mission .seq"), title: __T(1910), text: __T(1911) } ],
  deadoff: () => [ { el: () => gqs("#rooms .door"), title: L1(__T(1912), "No more dead-end notices"), text: L1(__T(1913), `Up to Level 6, the game told you when the proof had entered a dead end and was going in circles. From this level of predicate logic on, whether a door can be opened cannot be decided mechanically, so <b>there are no such notices</b>. No notice does not mean no dead end. If you get stuck in front of a door, try undoing back to a change of door or a choice in ∨I or ∃I.`) } ],
  match: () => [ { el: () => gqs("#rooms .key"), title: L1(__T(1914), "Matching"), text: L1(__T(1915), `Having climbed the tower of addition, you have learned a new technique: <b>you can insert a key that is an equation with ∀ directly into a door</b> (matching). The game finds the part of the door that fits the shape of the equation, decides the terms to substitute, and rewrites. The substituted terms appear in the move log and the proof tree. You can still tap the ∀ and instantiate by hand.`) } ],
  lemma: () => [ { el: () => gqs("[data-lemma]"), title: __T(1916), text: __T(1917) } ],
  induction: () => [ { el: () => gqs("[data-ind]"), title: __T(796), text: __T(1918) } ],
  leDef: () => [ { el: () => gqs("#rooms .mainop.defop") || gqs(".mission .seq"), title: __T(1714), text: __T(1919) } ],
  termInput: () => [ { el: () => gqs(".mission .seq"), title: __T(1920), text: __T(1921) } ],
  structFun: () => [
    { el: () => gqs("#kmodel [data-con]") && gqs("#kmodel [data-con]").closest(".pred"), title: __T(1922), text: __T(1923) },
    { el: () => gqs("#kmodel .fcell") && gqs("#kmodel .fcell").closest(".pred"), title: __T(1924), text: __T(1925) } ],
  clear: () => [ // クリア画面の見方（World 1 で初めてクリアしたとき）
    { el: () => gqs(".overlay .score"), title: __T(1926), text: __T(1927) },
    { el: () => gqs(".overlay .ptw"), title: __T(1928), text: __T(1929) },
    { el: () => gqs(".overlay .rp-ctrl"), title: __T(1930), text: __T(1931) },
    { el: () => gqs(".overlay p.check"), title: __T(1932), text: __T(1933) },
    { el: () => gqs(".overlay ol.log"), title: __T(1934), text: __T(1935) },
    { el: () => gqs(".overlay .actions"), title: __T(1936), text: __T(1937) } ],
  presets: () => [ { el: () => gqs("[data-preset-open]"), title: __T(1938), text: __T(1939) } ],
  translate: () => [
    { el: () => gqs(".trans-panel"), title: __T(1940), text: __T(1941) },
    { el: () => gqs("#rooms .door"), title: __T(1942), text: __T(1943) } ],
  tower: () => [
    { el: () => gqs(".tw-col"), title: __T(1944), text: __T(1945) },
    { el: () => gqs(".tw-right"), title: __T(1946), text: __T(1947) } ],
  indep: () => [ { el: () => gqs(".judge"), title: __T(1948), text: __T(1949) } ],
  thirdway: () => [ { el: () => gqs(".judge"), title: __T(1950), text: __T(1951) } ],
};
const GUIDE_AT = { "6-6": ["judge"], "7-1": ["deadoff"] }; // チュートリアルのない新しい画面（元の番号で指定）。7-1：行き止まりの知らせはここから出ない
// 照合は寄り道 S1 の最初で案内する（TUT_AT の "13-2" から、案内の吹き出しも出る）
const guideKeys = stg => !stg ? [] : [...(stg.tut || []).filter(k => GUIDES[k]), ...(GUIDE_AT[stg.oldId] || [])];
function guideSteps(keys) { return keys.flatMap(k => GUIDES[k](STAGE)); }
function guideStart(keys) {
  guideEnd(false);
  keys = keys || guideKeys(STAGE);
  if (!keys.length) return;
  GUIDE = { i: 0, keys, steps: guideSteps(keys) };
  guideShow();
}
function guideShow() {
  document.querySelectorAll(".guide-spot").forEach(e => e.classList.remove("guide-spot"));
  const old = $("#guideBubble"); if (old) old.remove();
  if (!GUIDE) return;
  const st = GUIDE.steps[GUIDE.i], el = st.el();
  if (!el) { if (GUIDE.i < GUIDE.steps.length - 1) { GUIDE.i++; return guideShow(); } return guideEnd(true); }
  el.classList.add("guide-spot");
  if (el.scrollIntoView) el.scrollIntoView({ block: "center" });
  const last = GUIDE.i === GUIDE.steps.length - 1;
  const b = document.createElement("div");
  b.id = "guideBubble"; b.className = "guide-bubble"; b.setAttribute("role", "dialog"); b.setAttribute("aria-label", __T(1952));
  b.innerHTML = __T(1953, [GUIDE.i + 1, GUIDE.steps.length, st.title, st.text, last ? __T(1804) : __T(1954), last ? __T(1955) : __T(1956)]);
  document.body.appendChild(b);
  guidePlace();
}
function guidePlace() {
  const b = $("#guideBubble"), el = document.querySelector(".guide-spot"); if (!b || !el) return;
  const r = el.getBoundingClientRect(), bw = Math.min(380, innerWidth - 16), bh = b.offsetHeight;
  b.style.width = bw + "px";
  const below = r.bottom + bh + 14 < innerHeight || r.top < bh + 14;
  const top = below ? r.bottom + 12 : r.top - bh - 12, left = Math.max(8, Math.min(innerWidth - bw - 8, r.left + Math.min(r.width, 300) / 2 - bw / 2));
  const fixed = !!el.closest(".overlay"); b.style.position = fixed ? "fixed" : "absolute";
  b.style.top = (top + (fixed ? 0 : scrollY)) + "px"; b.style.left = (left + (fixed ? 0 : scrollX)) + "px";
  b.classList.toggle("above", !below);
  b.style.setProperty("--ax", Math.max(16, Math.min(bw - 16, r.left + Math.min(r.width, 300) / 2 - left)) + "px");
}
function guideEnd(seen) {
  document.querySelectorAll(".guide-spot").forEach(e => e.classList.remove("guide-spot"));
  const b = $("#guideBubble"); if (b) b.remove();
  if (seen && GUIDE) { PROG.guideSeen = PROG.guideSeen || {}; GUIDE.keys.forEach(k => { PROG.guideSeen[k] = true; }); saveProgress(); }
  GUIDE = null;
}
addEventListener("resize", () => requestAnimationFrame(guidePlace));
document.addEventListener("scroll", e => { if (GUIDE && e.target && e.target.closest && e.target.closest(".overlay")) requestAnimationFrame(guidePlace); }, true);
{ const _rs = renderSelect; renderSelect = function () { _rs.apply(this, arguments); markSeqLocks(); sfObserve(); }; } // 最終層の背景の切り替えを、ステージ一覧を描くたびに設定する
// 「次のステージへ」の行き先：寄り道の層は、その層の中を進むとき（と、寄り道から続く寄り道）だけ通り、本道からは飛ばす
function nextStageOf(st) {
  const i = STAGES.indexOf(st);
  for (let j = i + 1; j < STAGES.length; j++) {
    const c = STAGES[j];
    if (c.world === st.world || !c.world.extra) return c;
    if (st.world.extra && c.world.extra && prevSameKind(c.world) === st.world) return c; // 寄り道 1 → 寄り道 2 のように、同じ種類の次の層へ
  }
  return null;
}
function startStage(id) {
  guideEnd(false);
  STAGE = STAGES.find(s => s.id === id);
  if (!STAGE) return;
  if (SF_OBS) { SF_OBS.disconnect(); SF_OBS = null; }
  sfBgLayer(); document.body.classList.remove("sf-bg");
  if (STAGE.world.final) { if (!document.body.classList.contains("sf")) sfFlash(1300); document.body.classList.add("sf"); SF_NOW = true; if (!PROG.sfSeen) { PROG.sfSeen = true; saveProgress(); } }
  else { document.body.classList.remove("sf"); SF_NOW = false; } // ほかの層の扉に入ると、最終層は元の姿に戻る
  if (STAGE.reveal && storyOn() && !PROG.revealSeen) setTimeout(() => { if (SCREEN === "play" && STAGE && STAGE.reveal) revealShow(); }, 60); // 17-3：正体を明かす演出
  UI = freshUI(); SCREEN = "play"; setZone(zoneOfWorld(STAGE.world)); UI.wasCleared = PROG.best[STAGE.pid] != null; // ボスの初回クリアかどうかを見分ける
  NEG_SUGAR = !STAGE.expandNeg;
  closeModal();
  if (STAGE.kind === "judge" || STAGE.kind === "tower") {
    UI.judge = { solved: {}, saved: {} }; UI.tower = { top: 4, checked: [], sel: null, same: false };
    PROB = null; S = null; R = null; HIST = []; HISTR = [];
    renderTools(); renderShell();
  } else loadProblem(STAGE, STAGE.kind === "refute" ? "refute" : "prove");
  window.scrollTo(0, 0);
  const fresh = guideKeys(STAGE).filter(k => !(PROG.guideSeen || {})[k]); // 新しい操作や画面が初めて登場したら、案内する
  if (fresh.length) setTimeout(() => { if (SCREEN === "play" && STAGE && STAGE.id === id && !$(".overlay")) guideStart(fresh); }, 350);
}
// 問題（ステージ、または鑑定の間の扉）を読み込む。saved があれば、途中の状態から再開する
function storyFold() { // 狭い画面では、語りを 3 行で折りたたむ（押すと全文）
  const t = $(".story-box .story-text"); if (!t || t.parentElement.querySelector(".story-more")) return;
  t.insertAdjacentHTML("afterend", `<button type="button" class="btn small story-more" data-storymore aria-expanded="false">${L1(__T(1957), "Read more")}</button>`);
}
function loadProblem(prob, mode, saved) {
  PROB = prob;
  PROBF = { prem: prob.prem.map(parse), goal: parse(prob.goal) };
  PROB_ATOMS = atomsOf([...PROBF.prem, PROBF.goal]);
  if (saved) ({ S, HIST, R, HISTR } = saved);
  else { S = initState(prob); HIST = []; R = STAGE.fol ? initStruct() : initR(); HISTR = []; }
  UI.mode = mode; UI.sel = null; UI.can = new Set(); UI.ttOpen = new Map(); UI.tgOpen = new Map(); UI.evPrev = new Map(); UI.previewKey = null; UI.orChoice = null; UI.scope = null;
  renderTools(); renderShell(); storyFold(); renderMode();
  wipOffer(); // 途中まで解いた盤面が残っていれば、「続きから」を提案する
}
const renderMode = () => UI.mode === "refute" ? (STAGE.fol ? renderStruct() : renderRefute()) : renderDynamic();
function setMode(m) {
  if (!PROB || m === UI.mode) return;
  UI.mode = m; UI.sel = null; UI.can = new Set(); UI.previewKey = null;
  $("#pane").innerHTML = m === "refute" ? refuteLayoutHTML() : proveLayoutHTML();
  document.querySelectorAll("[data-mode]").forEach(b => b.setAttribute("aria-pressed", String(b.dataset.mode === m)));
  renderMode();
}
function renderShell() { renderShell0(); cxJudgeCards(); }
function renderShell0() {
  const st = STAGE, judge = st.kind === "judge";
  const head = __T(1958, [WL(st.world), st.world.name, st.boss ? __T(1959) : "", st.par != null ? __T(1960, [st.par, unitOf(st)]) : "", bestText(st), proofHas(st) && !judge ? `<button type="button" class="btn small pv-btn" data-proofview="${st.pid}">${L1(__T(1961), "View the proof")}</button>` : "", st.earns ? `<span class="card-chip${cardGot(st.earns) ? " got" : ""}" title="${F(CARDS[st.earns].f).replace(/<[^>]+>/g, "")}">${ICON_CARD(cardGot(st.earns))}${cardTip(st)}</span>` : "", st.id, st.name, st.reveal && storyOn() && PROG.revealSeen ? `<button type="button" class="btn small rv-replay" data-rvreplay>${L1(__T(1962), "See the reveal again")}</button>` : "", DEBUG_CLEAR ? `<button type="button" class="btn small dbg-clear" data-cmd="dbgclear" title="${L1(__T(1963), "For testing: mark this stage cleared at once")}">⚡ ${L1(__T(1964), "Instant clear (test)")}</button>` : "", st.trans ? transPanelHTML(st) : ""]);
  const sto = storyOn() && storyStage(st) && !(st.kind === "judge" && PROB) ? storyStage(st) : null;
  const lesson = sto
    ? __T(1965, [sto.t, storyGoal(st)]) +
      __T(1966, [(st.tut || []).length ? " open" : "", st.lesson])
    : __T(1967, [st.lesson]);
  if (st.kind === "tower") { // 終わらない時の塔を見て確かめる（翻訳所の T-4）
    app.innerHTML = __T(1968, [head, guideKeys(st).length ? __T(1969) : "", lesson, towerHTML()]);
    renderHints();
    return;
  }
  if (judge && !PROB) { // 鑑定の間（扉の一覧）
    app.innerHTML = __T(1970, [head, guideKeys(st).length ? __T(1969) : "", lesson, judgeHubHTML(), semGuide()]);
    renderHints();
    return;
  }
  const turn = st.kind === "refute" ? "⊬" : judge ? "⊢<sup>?</sup>" : "⊢";
  const partBar = judge ? __T(1971, [PROB.key]) : "";
  const modes = st.kind === "refute" || judge
    ? __T(1972, [UI.mode === "refute", STAGE.fol ? __T(1973) : CL() ? __T(1974) : __T(1975), UI.mode === "prove", CL() ? __T(1976) : __T(1977)]) : "";
  app.innerHTML = __T(1978, [head, partBar, seqHTML(PROB, turn), guideKeys(st).length ? __T(1979) : "", lesson, modes, UI.mode === "refute" ? refuteLayoutHTML() : proveLayoutHTML()]);
}
function proveLayoutHTML() {
  return __T(1980, [PREFS.showTerm, !!PREFS.leanMode, PREFS.leanMode ? "" : " hidden", PREFS.showTerm ? "" : " hidden"]);
}

/* --- 反証モード：クリプキモデルの編集画面 --- */
const KGMAP_HTML = `<dl class="guide kg-mapdl"><div class="kg-map"><dt>${L1(__T(1981), "In the usual notation")}</dt><dd>${L1(__T(1982), "floor = world")} <i>w</i>${L1(__T(778), ", ")}${L1(__T(1983), "stairs up = ")}<i>w</i> ≤ <i>v</i>${L1(__T(778), ", ")}${L1(__T(1984), "lamps = valuation")} <i>V</i>${L1(__T(778), ", ")}${L1(__T(1985), "lit = ")}<i>w</i> ⊩ <i>A</i></dd></div><div class="kg-map"><dt>${L1(__T(1986), "Badges lit / dark")}</dt><dd>${L1(__T(1987), "lit: lit (forced) at that floor. dark: not lit at that floor (not necessarily false)")}</dd></div></dl>`; // 時の塔の言葉と、標準の記法との対応
const KGUIDE_HTML = KGMAP_HTML + __T(1988, [F("A&B"), F("A|B"), F("A->B"), F("A"), F("B"), F("~A"), F("A")]);
const TGUIDE_HTML = __T(1989, [F("A&B"), F("A|B"), F("A->B"), F("A"), F("B"), F("~A"), F("A")]);
const SGUIDE_HTML = __T(1990, [F("!x.A(x)"), termH("x"), F("A(x)"), F("?x.A(x)"), F("A(x)")]);
const semGuide = () => STAGE && STAGE.fol ? __T(1991, [SGUIDE_HTML]) : CL() ? __T(1992, [TGUIDE_HTML]) : __T(1993, [KGUIDE_HTML]);
const TV = v => CL() ? (v ? __T(876) : __T(877)) : (v ? __T(1994) : __T(1995)); // 文の中の言い方
const KB = v => CL() ? (v ? __T(876) : __T(877)) : v ? L1(__T(893), "lit") : L1(__T(894), "dark"); // 札の言い方（時の塔は 明／暗。暗は偽とは限らない）
/* 真偽の計算の表示（木・表）。真偽は 3 値（真・偽・未定）。
   構造を変えると、真偽が変わった部分を、原子式から順に（部分式から式全体へ）少しずつ書き換えるアニメーションで見せる */
let EV_ANIM = 0;
const TVL = v => v === true ? __T(876) : v === false ? __T(877) : __T(891);
const TVC = v => v === true ? "t" : v === false ? "f" : "u";
function evKids(f, dom) {
  if (f.t === "atom" || f.t === "bot") return [];
  if (isNeg(f)) return [{ f: f.l }];
  if (f.t === "all" || f.t === "ex") return dom ? dom.map(d => ({ f: inst(f.b, f.v, d), lab: __T(1996, [termH(f.v), d]), d })) : [];
  return [{ f: f.l }, { f: f.r }];
}
function evKeys(f, v, kv) { // 真偽を決めている子（理由）
  const idx = b => kv.map((x, i) => x === b ? i : -1).filter(i => i >= 0), first = b => idx(b).slice(0, 1), all = kv.map((_, i) => i);
  if (isNeg(f)) return [0];
  switch (f.t) {
    case "and": case "all": return v === true ? all : v === false ? first(false) : idx(null);
    case "or": case "ex": return v === true ? first(true) : v === false ? all : idx(null);
    case "imp": return v === true ? (kv[0] === false ? [0] : [1]) : v === false ? all : idx(null);
  }
  return [];
}
function evWhy(f, v, ks, kv, atomWhy) {
  const el = d => `<b class="el">${d}</b>`;
  if (f.t === "bot") return __T(1997);
  if (f.t === "atom") return atomWhy(f, v);
  if (isNeg(f)) return v === true ? __T(1998) : v === false ? __T(1999) : __T(2000);
  switch (f.t) {
    case "and": return v === true ? __T(2001) : v === false ? __T(2002) : __T(2003);
    case "or": return v === true ? __T(2004) : v === false ? __T(2005) : __T(2006);
    case "imp": return v === true ? (kv[0] === false ? __T(2007) : __T(2008)) : v === false ? __T(2009) : __T(2010);
    case "all": { if (!ks.length) return ""; const i = kv.indexOf(false); return v === true ? __T(2011) : v === false ? __T(2012, [el(ks[i].d)]) : __T(2013); }
    case "ex": { if (!ks.length) return ""; const i = kv.indexOf(true); return v === true ? __T(2014, [el(ks[i].d)]) : v === false ? __T(2015) : __T(2016); }
  }
  return "";
}
// 前回の表示から真偽が変わった部分には data-pend（新しい値）と data-lv（書き換える順番）を付け、いったん古い値で描く
function evMark(key, v, lv) {
  const prev = UI.evPrev && UI.evPrev.has(key) ? UI.evPrev.get(key) : undefined;
  (UI.evPrev || (UI.evPrev = new Map())).set(key, v);
  const pend = prev !== undefined && prev !== v;
  return { cur: pend ? prev : v, attr: pend ? ` data-pend="${TVC(v)}" data-lv="${lv}"` : "", hide: pend ? ` style="visibility:hidden"` : "" };
}
function truthTreeHTML(roots, val, opt) {
  const open = UI.ttOpen || (UI.ttOpen = new Map());
  const node = (f, path, key, defOpen, depth, lab, role) => {
    const v = val(f), ks = depth < 8 ? evKids(f, opt.dom) : [], kv = ks.map(k => val(k.f)), keys = evKeys(f, v, kv);
    const st = ks.length > 0 && (open.has(path) ? open.get(path) : defOpen);
    const many = (f.t === "all" && v === true) || (f.t === "ex" && v === false); // 住人全員を調べる必要がある場合は、子を閉じておく
    const m = evMark("T:" + path + ":" + fkey(f), v, depth);
    const tog = ks.length ? `<button type="button" class="tt-tog" data-tt-tog="${path}" aria-expanded="${st}" aria-label="${st ? __T(1804) : __T(2017)}">${st ? "▾" : "▸"}</button>` : `<span class="tt-tog leaf" aria-hidden="true"></span>`;
    const row = `<div class="tt-row">${tog}<span class="tt-v">${TVL(m.cur)}</span>${lab ? `<span class="tt-lab">${lab}</span>` : ""}<span class="tt-f f">${fh(f)}</span>${role ? `<span class="ev-role">${role}</span>` : ""}<span class="tt-why"${m.hide}>${evWhy(f, v, ks, kv, opt.atomWhy)}</span></div>`;
    const body = st ? `<ul>${ks.map((k, i) => node(k.f, path + "." + i, keys.includes(i), keys.includes(i) && !many && depth < 5, depth + 1, k.lab)).join("")}</ul>` : "";
    return `<li class="tt-node ${TVC(m.cur)}${key ? " tt-key" : ""}"${m.attr}>${row}${body}</li>`;
  };
  return `<ul class="tt">${roots.map((r, i) => node(r.f, "r" + i, true, true, 0, "", r.role)).join("")}</ul>` +
    __T(2018);
}
function truthTableHTML(rows, val, opt) {
  const size = f => f.t === "atom" || f.t === "bot" ? 1 : f.t === "all" || f.t === "ex" ? 1 + size(f.b) : 1 + size(f.l) + (isNeg(f) ? 0 : size(f.r));
  return `<div class="ev-wrap"><table class="ev"><tbody>` + rows.map(r => {
    const v = val(r.f), ks = evKids(r.f, opt.dom), kv = ks.map(k => val(k.f)), m = evMark("B:" + fkey(r.f), v, 100 - size(r.f));
    return `<tr class="${TVC(m.cur)}${m.cur === true ? " on" : ""}${r.depth ? " sub" : ""}"${m.attr}><td class="ev-f">${FF(r.f)}${r.role ? `<span class="ev-role">${r.role}</span>` : ""}</td><td class="ev-v">${TVL(m.cur)}</td><td class="ev-why"${m.hide}>${evWhy(r.f, v, ks, kv, opt.atomWhy)}</td></tr>`;
  }).join("") + `</tbody></table></div>`;
}
// 図で見る：部分論理式を頂点とする木（式全体が上、原子式が下）。頂点の横に 真・偽・未定 を書く
function truthGraphHTML(roots, val, opt) {
  const open = UI.tgOpen || (UI.tgOpen = new Map()), CAP = 40;
  const decis = !!opt.dom; // 構造の評価：∀ が偽なら反例の住人、∃ が真なら証人だけを「決め手」として示す（∀ が真・∃ が偽なら全員を、最初は閉じて）
  const kidsOf = (f, v) => { const ks = evKids(f, opt.dom); if (!decis || (f.t !== "all" && f.t !== "ex")) return { ks, wit: false, fold: false };
    const kv = ks.map(k => val(k.f)), i = f.t === "all" ? (v === false ? kv.indexOf(false) : -1) : (v === true ? kv.indexOf(true) : -1);
    return i >= 0 ? { ks: [ks[i]], wit: true, fold: false } : { ks, wit: false, fold: v === true || v === false }; };
  // 最初に開いておく頂点：木ごとに、上から順に（幅優先で）、頂点の数が CAP を超えない範囲まで。残りは頂点を押すと開く
  const defOpen = new Set();
  roots.forEach((r, ri) => { let count = 1; const q = [{ f: r.f, path: "g" + ri, depth: 0 }];
    while (q.length) { const it = q.shift(), kk = kidsOf(it.f, val(it.f)), ks = kk.ks; if (!ks.length || it.depth >= 7 || count + ks.length > CAP || kk.fold) continue;
      defOpen.add(it.path); count += ks.length; ks.forEach((k, i) => q.push({ f: k.f, path: it.path + "." + i, depth: it.depth + 1 })); } });
  const node = (f, path, depth, info) => {
    const v = val(f), kk = depth < 8 ? kidsOf(f, v) : { ks: [] }, ks = kk.ks, m = evMark("G:" + path + ":" + fkey(f), v, depth);
    const st = ks.length > 0 && (open.has(path) ? open.get(path) : defOpen.has(path));
    const tag = info && info.lab ? `<span class="tg-who${info.wit ? " wit" : ""}">${info.wit ? L1(__T(2019), "Decisive: ") : ""}${info.lab}</span>` : "";
    const box = `<div class="tg-node ${TVC(m.cur)}${info && info.wit ? " tg-wit" : ""}"${m.attr}${info && info.d ? ` data-res="${info.d}"` : ""}${ks.length && !opt.static ? ` data-tg-tog="${path}" role="button" tabindex="0" title="${st ? __T(2020) : __T(2021)}"` : ""}>${tag}<span class="tg-f f">${fh(f)}</span><span class="tg-v">${TVL(m.cur)}</span>${ks.length && !st ? __T(2022, [ks.length]) : ""}</div>`;
    return `<li>${box}${st ? `<ul>${ks.map((k, i) => node(k.f, path + "." + i, depth + 1, decis && k.d ? { lab: k.lab, wit: kk.wit, d: k.d } : null)).join("")}</ul>` : ""}</li>`;
  };
  return roots.map((r, i) => `<div class="tg-block"><div class="tg-role"><span class="ev-role">${r.role}</span></div><div class="tg-wrap"><div class="tg-inner"><ul class="tg">${node(r.f, "g" + i, 0)}</ul></div></div></div>`).join("") +
    (opt.static ? "" : __T(2023));
}
// 構造の評価の頂点に重ねると、表の中でその住人に関わる欄が色づく
document.addEventListener("mouseover", e => { const t = e.target; if (!t || !t.closest) return;
  const n = t.closest(".tg-node[data-res]"); document.querySelectorAll(".res-hl").forEach(x => x.classList.remove("res-hl")); if (!n) return;
  const d = n.dataset.res, has = k => k.split(",").includes(d);
  document.querySelectorAll("[data-rel]").forEach(b => { const tup = b.dataset.rel.split(":")[1] || ""; if (has(tup)) b.classList.add("res-hl"); });
  document.querySelectorAll("[data-fun]").forEach(b => { const k = b.dataset.fun.split(":")[1] || ""; if (has(k)) b.classList.add("res-hl"); }); });
// 横に広い木は、欄の幅に収まるように縮める（小さくなりすぎるときは横にスクロール）
function tgFit() {
  document.querySelectorAll(".tg-wrap").forEach(w => {
    const inner = w.firstElementChild; if (!inner) return;
    inner.style.zoom = ""; // zoom は配置ごと縮めるので、縮めた後もスクロールの範囲が正しい
    const sc = Math.max(0.55, Math.min(1, (w.clientWidth - 4) / inner.scrollWidth));
    if (sc < 1) inner.style.zoom = String(sc);
    w.scrollLeft = (w.scrollWidth - w.clientWidth) / 2; // 根（式全体）は中央にあるので、中央が見えるようにする
  });
}
// 真偽が変わった部分を、深い（小さい）部分式から順に書き換える
function kvHi(k) { // 全階で見る：同じ式のチップと、その式が光る塔の階を色づける
  UI.kvf = k || null;
  document.querySelectorAll(".kv-chip.kv-hl").forEach(c => c.classList.remove("kv-hl"));
  document.querySelectorAll("#kmodel .floor.kv-on, .kv-wrap .floor.kv-on").forEach(c => c.classList.remove("kv-on"));
  if (!k) return;
  document.querySelectorAll("#kEval .kv-chip, #kvDone .kv-chip").forEach(c => { if (c.dataset.kf !== k) return; c.classList.add("kv-hl"); const fl = c.closest(".floor"); if (fl && c.classList.contains("kv-lit")) { fl.classList.add("kv-on"); const t = document.querySelector(`#kmodel .floor[data-floor="${fl.dataset.floor}"]`); if (t) t.classList.add("kv-on"); } });
}
document.addEventListener("mouseover", e => { const t = e.target; if (!t || !t.closest) return; const c = t.closest("#kEval .kv-chip, #kvDone .kv-chip"); if (c) kvHi(c.dataset.kf); else if (UI && UI.kvf && t.closest("#kEval, #kvDone") && !t.closest(".kv-chip")) kvHi(null); });
let KHI_ON = false;
function kHi(el) { // el：計算の図の頂点（data-kw などを持つ）。null なら色を消す
  UI.khi = el ? { kw: el.dataset.kw, kcone: el.dataset.kcone, kwit: el.dataset.kwit } : null;
  kHiApply(UI.khi);
}
function kHiApply(h) {
  const box = $("#kmodel"); if (!box) return;
  box.querySelectorAll(".floor.k-at, .floor.k-cone, .floor.k-wit").forEach(f => f.classList.remove("k-at", "k-cone", "k-wit"));
  KHI_ON = !!h; if (!h || !STAGE || STAGE.fol || CL() || !R || !R.floors) return;
  const w = +h.kw, card = id => box.querySelector(`.floor[data-floor="${id}"]`);
  if (!kFloor(R, w)) return;
  if (h.kcone) kUp(R, w).forEach(id => { const c = card(id); if (c) c.classList.add("k-cone"); });
  const at = card(w); if (at) at.classList.add("k-at");
  if (h.kwit != null) { const c = card(+h.kwit); if (c) c.classList.add("k-wit"); }
}
document.addEventListener("mouseover", e => { const t = e.target; if (!t || !t.closest) return; const el = t.closest("#kEval [data-kw]"); if (el) kHi(el); else if (KHI_ON && !t.closest("#kEval")) kHi(null); });
document.addEventListener("focusin", e => { const el = e.target && e.target.closest && e.target.closest("#kEval [data-kw]"); if (el) kHi(el); });
function evAnimate() {
  const box = $("#kEval"), verdict = $("#kVerdict"); if (!box) return;
  if (box.querySelector(".tg-wrap")) requestAnimationFrame(tgFit);
  const token = ++EV_ANIM, pend = [...box.querySelectorAll("[data-pend]")];
  const apply = el => {
    const v = el.dataset.pend; el.removeAttribute("data-pend");
    el.classList.remove("t", "f", "u", "on"); el.classList.add(v); if (v === "t" && el.tagName === "TR") el.classList.add("on");
    const badge = el.querySelector(":scope > .tt-row > .tt-v, :scope > .ev-v, :scope > .tg-v"); if (badge) badge.textContent = el.dataset.pendtxt != null ? el.dataset.pendtxt : v === "t" ? __T(876) : v === "f" ? __T(877) : __T(891); // 時の塔では「光る・光らない」のまま
    const why = el.querySelector(":scope > .tt-row > .tt-why, :scope > .ev-why"); if (why) why.style.visibility = "";
    el.classList.remove("ev-flip"); void el.offsetWidth; el.classList.add("ev-flip");
  };
  const reduce = !!(window.matchMedia && window.matchMedia("(prefers-reduced-motion: reduce)").matches);
  if (!pend.length || reduce) { pend.forEach(apply); if (verdict) verdict.classList.remove("ev-wait"); document.body.classList.remove("ev-calc"); return; }
  if (verdict) { verdict.classList.add("ev-wait"); verdict.dataset.calc = L1(__T(2024), "Calculating…"); }
  document.body.classList.add("ev-calc"); // 計算の図を書き換えている間は、完成の案内と反証のボタンを待たせる
  const levels = [...new Set(pend.map(e => +e.dataset.lv))].sort((a, b) => b - a);
  levels.forEach((lv, i) => setTimeout(() => {
    if (token !== EV_ANIM) return;
    pend.filter(e => +e.dataset.lv === lv && e.isConnected).forEach(apply);
    if (i === levels.length - 1) { if (verdict) verdict.classList.remove("ev-wait"); document.body.classList.remove("ev-calc"); }
  }, 120 + i * 260));
}
const kView = () => ["all", "graph", "tree"].includes(PREFS.kView) ? PREFS.kView : "all"; // 時の塔の計算欄の表示（最初は「全階で見る」）
const evTabs = () => { const v = PREFS.evMode === "tree" ? "tree" : "graph"; // 「全階で見る」は時の塔だけ（ほかでは図で見る） // 図で見る（部分論理式の木）と、理由で見る（真偽の理由をたどる一覧）
  const kr = !CL() && STAGE && !STAGE.fol, vv = kr ? kView() : v; // 時の塔は、別の設定（最初は「全階で見る」）
  return `<div class="ev-tabs" role="group" aria-label="${L1(__T(2025), "How to show")}">${kr ? `<button type="button" class="btn small" data-evview="all" aria-pressed="${vv === "all"}">${L1(__T(2026), "All floors")}</button>` : ""}<button type="button" class="btn small" data-evview="graph" aria-pressed="${vv === "graph"}">${L1(__T(2027), "Diagram")}</button><button type="button" class="btn small" data-evview="tree" aria-pressed="${vv === "tree"}">${L1(__T(2028), "Reasons")}</button></div>`; };
const SUBD = "₀₁₂₃₄₅₆₇₈₉", wSub = n => "w" + String(n).replace(/\d/g, c => SUBD[+c]); // 階 n → wₙ
function verdict3(prem, goal, val, what) { // 反例になっているか（3 値で）と、その理由
  const pv = prem.map(val), gv = val(goal), ok = pv.every(v => v === true) && gv === false;
  if (ok) return { ok, html: __T(2029, [what, prem.length ? __T(2030) : "", FF(goal), what]) };
  const why = [...prem.map((p, i) => pv[i] === false ? __T(2031, [FF(p)]) : pv[i] == null ? __T(2032, [FF(p)]) : null).filter(Boolean),
               gv === true ? __T(2033, [FF(goal)]) : gv == null ? __T(2034, [FF(goal)]) : null].filter(Boolean);
  return { ok, html: __T(2035, [why.join(__T(2036))]) };
}
function refuteLayoutHTML() {
  if (STAGE.fol) return __T(2037, [semGuide()]);
  return __T(2038, [CL() ? __T(1455) : __T(2039), CL() ? __T(2040) : __T(2041), semGuide()]);
}
function renderStruct() {
  const { prem, goal } = PROBF, sig = sigOf([...prem, goal]), preds = sig.rels, dom = Array.from({ length: R.n }, (_, i) => String(i + 1));
  R.relF = R.relF || {};
  const el = d => `<b class="el">${d}</b>`;
  const funLabel = (f, a, b) => f === "*" ? `${a}<span class="op">·</span>${b}` : f === "+" ? `${a}<span class="op">+</span>${b}` : `<i class="fn">${f}</i>(${a},${b})`;
  const fun1Label = (f, a) => f === "i" ? `${a}<sup class="inv">−1</sup>` : `<i class="fn">${f}</i>(${a})`;
  const consHTML = sig.cons.map(c => __T(2042, [termH(c), R.con[c] == null ? __T(2043) : "", dom.map(d => __T(2044, [R.con[c] === d ? " on" : "", c, d, R.con[c] === d, el(d)])).join("")])).join("");
  const fcell = (f, key, label) => { const v = (R.fun[f] || {})[key], xs = key.split(","); // 読み上げ名：項と今の値（2·3 = 2、s(1) = 未定）
    const term = xs.length === 2 ? (f === "*" ? `${xs[0]}·${xs[1]}` : f === "+" ? `${xs[0]} + ${xs[1]}` : `${f}(${xs[0]},${xs[1]})`) : (f === "i" ? `${xs[0]}⁻¹` : `${f}(${xs[0]})`);
    return `<button type="button" class="fcell${v == null ? " unk" : ""}" data-fun="${f}:${key}" title="${L1(__T(2045), "Each press changes the value (? means undecided)")}" aria-label="${term} = ${v == null ? L1(__T(891), "undecided") : v}">${label}${v == null ? `<b class="el">?</b>` : el(v)}</button>`; };
  const funsHTML = sig.funs.map(([f, ar]) => ar === 1
    ? __T(2046, [fun1Label(f, `<i class="tm">x</i>`), dom.map(d => fcell(f, d, `<span class="f">${fun1Label(f, el(d))}</span> = `)).join("")])
    : ar === 2 ? __T(2047, [funLabel(f, `<i class="tm">x</i>`, `<i class="tm">y</i>`), dom.map(d => `<th>${el(d)}</th>`).join("")]) +
        dom.map(x => `<tr><th>${el(x)}</th>${dom.map(y => `<td>${fcell(f, x + "," + y, "")}</td>`).join("")}</tr>`).join("") + `</tbody></table></div></div>`
    : __T(2048)).join("");
  const val = f => evalS3(R, f);
  let vd = verdict3(prem, goal, val, __T(2049));
  if (vd.ok && STAGE.reach0 && !reachAll0(R)) vd = { ok: false, html: `<div class="verdict">${L1(__T(2050), "Not a counterexample yet: every hypothesis is true and the goal is false, but induction fails in this structure — some resident cannot be reached from 0 by following s.")}</div>` };
  const pres = presetsFor();
  $("#kHead").innerHTML = __T(2051, [R.n]) +
    (pres.length ? __T(2052, [!!UI.presetOpen, ICON.list || ""]) : "") +
    __T(2053) +
    (vd.ok ? __T(2054) : "");
  const lamp = (P, tup, label) => { const on = (R.rel[P] || []).includes(tup), off = (R.relF[P] || []).includes(tup), st = on ? __T(876) : off ? __T(877) : __T(891);
    const xs = tup ? tup.split(",") : [], nameA = !xs.length ? P : xs.length === 2 && /^[≤<]$/.test(P) ? `${xs[0]} ${P} ${xs[1]}` : `${P}(${xs.join(",")})`; // 読み上げ名：式と今の値
    return `<button type="button" class="lamp${on ? " on" : off ? " no" : " unk"}" data-rel="${P}:${tup}" aria-label="${nameA}${L1(__T(2055), ": ")}${on ? L1(__T(876), "true") : off ? L1(__T(877), "false") : L1(__T(891), "undecided")}">${label}<span class="tv">${st}</span></button>`; };
  const presetPanel = UI.presetOpen && pres.length ? __T(2056) +
    pres.map(pr => __T(2057, [pr.name, pr.n, pr.desc, pr.id])).join("") + `</div>` : "";
  $("#kmodel").innerHTML = presetPanel + `<div class="struct"><div class="dom-row">${dom.map(d => __T(2058, [ICON.person, d])).join("")}</div>` +
    consHTML + funsHTML + preds.map(([P, ar]) => {
      if (ar === 0) return `<div class="pred"><div class="pred-h f"><i class="at">${P}</i></div><div class="lamps">${lamp(P, "", `<i class="at">${P}</i>`)}</div></div>`;
      if (ar === 1) return `<div class="pred"><div class="pred-h f"><i class="at">${P}</i>(<i class="tm">x</i>)</div><div class="lamps">${dom.map(d => lamp(P, d, `<span class="f"><i class="at">${P}</i>(<b class="el">${d}</b>)</span>`)).join("")}</div></div>`;
      if (ar === 2) return __T(2059, [INFIX[P] ? `<i class="tm">x</i><span class="op">${INFIX[P]}</span><i class="tm">y</i>` : `<i class="at">${P}</i>(<i class="tm">x</i>,<i class="tm">y</i>)`, dom.map(d => `<th><b class="el">${d}</b></th>`).join("")]) +
        dom.map(x => `<tr><th><b class="el">${x}</b></th>${dom.map(y => `<td>${lamp(P, x + "," + y, "")}</td>`).join("")}</tr>`).join("") + `</tbody></table></div></div>`;
      return __T(2060);
    }).join("") + `</div>`;
  $("#kVerdict").innerHTML = vd.html;
  const atomWhy = (f, v) => {
    const tv = t => evalTerm3(R, t), vals = (f.args || []).map(tv);
    if (isEq(f)) return vals.some(x => x == null) ? __T(2061) : __T(2062, [el(vals[0]), el(vals[1]), v ? __T(2063) : __T(2064)]);
    if (vals.some(x => x == null)) return __T(2061);
    if (!vals.length) return __T(2065, [TVL(v)]);
    return __T(2066, [vals.join(","), TVL(v)]);
  };
  const roots = [...prem.map(f => ({ f, role: L1(__T(824), "Assumption") })), { f: goal, role: __T(889) }];
  let body;
  if (PREFS.evMode === "tree") body = truthTreeHTML(roots, val, { dom, atomWhy }); // 理由で見る
  else body = truthGraphHTML(roots, val, { dom }); // 図で見る（既定）
  $("#kEval").innerHTML = __T(2067, [evTabs(), body]);
  decSumApply(); // 決め手のまとめ
  $("#kStatus").innerHTML = __T(2068, [preds.length ? __T(2069) : "", sig.funs.length ? __T(2070) : "", sig.cons.length ? __T(2071) : ""]);
  evAnimate();
  renderHints();
  const ub = $("#undoBtn"); if (ub) ub.disabled = !HISTR.length;
}
function sToggle(R, P, tup) { // 未定 → 偽 → 真 → 偽 → 真 …（未定には戻らない）
  R.relF = R.relF || {}; const t = R.rel[P] || [], f = R.relF[P] || [];
  if (t.includes(tup)) { R.rel[P] = t.filter(x => x !== tup); R.relF[P] = [...f, tup]; }
  else if (f.includes(tup)) { R.relF[P] = f.filter(x => x !== tup); R.rel[P] = [...t, tup]; }
  else R.relF[P] = [...f, tup];
}
function resetUnknown() { // すべて未定に戻す（住人の数はそのまま）
  const snap = JSON.stringify(R);
  if (STAGE.fol) { const base = initStruct(); R.rel = {}; R.relF = {}; R.fun = base.fun; R.con = {}; }
  else R.tv = {};
  HISTR.push(snap); STAGE.fol ? renderStruct() : renderRefute();
  toast(__T(2072));
}
function allTuples(n, ar) { let out = [[]]; for (let k = 0; k < ar; k++) out = out.flatMap(t => Array.from({ length: n }, (_, i) => [...t, String(i + 1)])); return out.map(t => t.join(",")); }
function unknownToFalse() { // 未定の欄をすべて偽にする
  const snap = JSON.stringify(R);
  if (STAGE.fol) { R.relF = R.relF || {}; for (const [P, ar] of sigOf([...PROBF.prem, PROBF.goal]).rels) { const t = R.rel[P] || []; R.relF[P] = allTuples(R.n, ar).filter(x => !t.includes(x)); } }
  else { R.tv = R.tv || {}; for (const a of PROB_ATOMS) if (!R.tv[a]) R.tv[a] = "F"; }
  HISTR.push(snap); STAGE.fol ? renderStruct() : renderRefute();
}
function tvCycle(a) { const snap = JSON.stringify(R); R.tv = R.tv || {}; R.tv[a] = R.tv[a] === "F" ? "T" : "F"; HISTR.push(snap); renderRefute(); } // 未定 → 偽 → 真 → 偽 …
function sDom(R, delta) {
  const n = R.n + delta;
  if (n < 1 || n > 6) { toast(n < 1 ? __T(2073) : __T(2074)); return false; }
  R.n = n;
  for (const P of Object.keys(R.rel)) R.rel[P] = R.rel[P].filter(tup => tup === "" || tup.split(",").every(x => +x <= n));
  for (const P of Object.keys(R.relF || {})) R.relF[P] = R.relF[P].filter(tup => tup === "" || tup.split(",").every(x => +x <= n));
  for (const f of Object.keys(R.fun || {})) { const tab = R.fun[f]; for (const k of Object.keys(tab)) if (k.split(",").some(x => +x > n) || +tab[k] > n) delete tab[k]; }
  for (const c of Object.keys(R.con || {})) if (+R.con[c] > n) delete R.con[c];
}
function kLabels() { const m = new Map(); kOrder(R).forEach((id, i) => m.set(id, i)); return m; }
function renderAssign() { // 古典論理の反例：各原子命題に 真・偽 を割り当てる（最初は未定）
  R.tv = R.tv || {};
  const { prem, goal } = PROBF, vd = verdict3(prem, goal, evalC3, __T(2075));
  $("#kHead").innerHTML = __T(2076) +
    (vd.ok ? __T(2077) : "");
  $("#kmodel").innerHTML = `<div class="assign"><div class="pred-h">${L1(__T(1295), "Stone board (truth assignment)")}</div><div class="lamps">${PROB_ATOMS.map(a => { const v = R.tv[a], st = v === "T" ? __T(876) : v === "F" ? __T(877) : __T(891);
    return __T(2078, [v === "T" ? " on" : v === "F" ? " no" : " unk", a, a, st, a, st]); }).join("")}</div></div>`;
  $("#kVerdict").innerHTML = vd.html;
  const atomWhy = (f, v) => v == null ? __T(2079, [f.n]) : __T(2080, [f.n, v ? __T(876) : __T(877)]);
  const roots = [...prem.map(f => ({ f, role: L1(__T(824), "Assumption") })), { f: goal, role: __T(889) }];
  const body = PREFS.evMode === "tree" ? truthTreeHTML(roots, evalC3, { dom: null, atomWhy }) : truthGraphHTML(roots, evalC3, { dom: null });
  $("#kEval").innerHTML = __T(2081, [evTabs(), body]);
  $("#kStatus").innerHTML = __T(2082);
  evAnimate();
  renderHints();
  const ub = $("#undoBtn"); if (ub) ub.disabled = !HISTR.length;
}
function renderRefute() {
  if (CL()) return renderAssign();
  const forces = makeForcer(R), lab = kLabels(), cex = kCounter(R, forces, PROBF.prem, PROBF.goal);
  if (!kFloor(R, R.sel)) R.sel = 0;
  if (cex != null && !R.selPick) R.sel = cex; // 反例ができたら、その階の計算を見せる（自分で階を選ぶまで）
  $("#kHead").innerHTML = CL()
    ? __T(2083, [cex != null ? __T(2077) : ""])
    : __T(2084, [R.floors.length, STAGE.kind === "refute" && STAGE.par != null ? __T(2085, [STAGE.par]) : "", cex != null ? __T(2086) : __T(2087)]);
  $("#kmodel").innerHTML = `<div class="km-inner"><svg class="km-links" aria-hidden="true"></svg>${floorTreeHTML(0, forces, lab, cex, false)}</div>`;
  drawLinks($("#kmodel"));
  $("#kVerdict").innerHTML = verdictHTML(forces, lab, cex);
  $("#kEval").innerHTML = CL()
    ? __T(2088, [evTabs()]) + (PREFS.evMode !== "table"
        ? truthTreeHTML([...PROBF.prem.map(f => ({ f, role: L1(__T(824), "Assumption") })), { f: PROBF.goal, role: __T(889) }], f => forces(0, f), { dom: null, atomWhy: (f, v) => __T(2080, [f.n, v ? __T(876) : __T(877)]) })
        : evalHTML(R.sel, forces, lab, false))
    : `<h3 class="ev-title">${kView() === "all" ? L1(__T(2089), "Lit and dark on every floor") : R.sel === cex ? L1(__T(2090, [lab.get(R.sel)]), `Calculation at floor ${lab.get(R.sel)} (the counterexample floor)`) : L1(__T(2091, [lab.get(R.sel)]), `Calculation at floor ${lab.get(R.sel)}`)}</h3>${evTabs()}` + (() => { const roots = [...PROBF.prem.map(f => ({ f, role: L1(__T(824), "Assumption") })), { f: PROBF.goal, role: __T(889) }];
        return kView() === "all" ? kAllHTML(forces, lab, cex) : kView() === "tree" ? kTreeHTML(roots, R.sel, forces, lab) : kGraphHTML(roots, R.sel, forces, lab); })();
  $("#kStatus").innerHTML = CL() ? __T(2092) : L1(__T(2093), "Press a lamp button to light an atomic proposition. \"+ floor above\" adds a future floor; adding twice from the same floor makes the future branch. A lamp lit on a lower floor (marked ↑) stays lit on the floors above.");
  if (!CL()) { evAnimate(); if (UI.khi) kHiApply(UI.khi); if (kView() === "all") { drawLinks($("#kvWrap")); if (UI.kvf) kvHi(UI.kvf); } } // 押した頂点の対応は、描き直しても残す
  renderHints();
  const ub = $("#undoBtn"); if (ub) ub.disabled = !HISTR.length;
}
function floorTreeHTML(id, forces, lab, cex, stat) {
  const kids = kKids(R, id);
  return `<div class="km-node">${kids.length ? `<div class="km-kids">${kids.map(k => floorTreeHTML(k, forces, lab, cex, stat)).join("")}</div>` : ""}${floorCardHTML(id, forces, lab, cex, stat)}</div>`;
}
function floorCardHTML(id, forces, lab, cex, stat) {
  const f = kFloor(R, id), eff = kEff(R, id), inhSet = new Set(kAnc(R, id).flatMap(a => kFloor(R, a).own));
  const { prem, goal } = PROBF;
  const pOK = prem.every(p => forces(id, p)), gOK = forces(id, goal);
  const lamps = PROB_ATOMS.map(a => {
    const on = eff.has(a), inh = inhSet.has(a);
    const tv = CL() ? `<span class="tv">${on ? __T(876) : __T(877)}</span>` : "";
    return stat ? `<span class="lamp${on ? " on" : ""}"><i class="at">${a}</i>${tv}</span>`
      : `<button type="button" class="lamp${on ? " on" : ""}${inh ? " inh" : ""}" data-lamp="${id}:${a}" aria-pressed="${on}" aria-label="${CL() ? `${a}${L1(__T(2055), ": ")}${on ? L1(__T(876), "true") : L1(__T(877), "false")}` : L1(__T(2094, [lab.get(id), a, on ? __T(2095) : __T(2096)]), `${a} on floor ${lab.get(id)}: ${on ? "lit" : "not lit"}`)}" title="${inh ? L1(__T(2097), "Lit on a lower floor, so it cannot be turned off") : CL() ? __T(2098) : on ? __T(2099) : __T(2100)}"><i class="at">${a}</i>${tv}${inh && !CL() ? `<span class="inh-mk" aria-hidden="true">↑</span>` : ""}</button>`;
  }).join("");
  return `<div class="floor${R.sel === id && !stat ? " sel" : ""}${cex === id ? " cex" : ""}" data-floor="${id}"${f.parent != null ? ` data-parent="${f.parent}"` : ""}>` +
    `<div class="fl-head"><span class="fl-name">${CL() ? __T(1455) : __T(2101, [lab.get(id)])}</span>${!CL() && PREFS.kSym ? `<span class="fl-w">${wSub(lab.get(id))}</span>` : ""}${CL() ? "" : `<span class="fl-wit">${L1(__T(896), "decisive")}</span>`}${f.parent == null && !CL() ? __T(2102) : ""}${cex === id ? __T(2103) : ""}</div>` +
    `<div class="lamps">${lamps || __T(2104)}</div>` +
    (CL() || f.parent == null || cex === id ? __T(2105, [prem.length ? __T(2106, [pOK ? "good" : "meh", pOK ? (CL() ? __T(2107) : __T(2108)) : (CL() ? __T(2109) : __T(2110))]) : "", gOK ? "meh" : "good", TV(gOK)]) : "") + // 時の塔では、根と反例の階だけに状態を書く
    (stat || CL() ? "" : __T(2111, [id, f.parent != null ? __T(2112, [id]) : ""])) +
    `</div>`;
}
// 上り階段（親の階の上辺から子の階の下辺へ）を、配置が決まった後に SVG で描く
function drawLinks(wrap) {
  const inner = wrap && wrap.querySelector(".km-inner"), svg = inner && inner.querySelector("svg.km-links");
  if (!svg) return;
  const base = inner.getBoundingClientRect(), mid = "km" + Math.random().toString(36).slice(2, 8);
  let lines = "";
  inner.querySelectorAll(".floor[data-parent]").forEach(el => {
    const p = inner.querySelector(`.floor[data-floor="${el.dataset.parent}"]`);
    if (!p) return;
    const a = p.getBoundingClientRect(), b = el.getBoundingClientRect();
    lines += `<line x1="${a.left + a.width / 2 - base.left}" y1="${a.top - base.top}" x2="${b.left + b.width / 2 - base.left}" y2="${b.bottom - base.top + 3}" marker-end="url(#${mid})"/>`;
  });
  svg.setAttribute("width", base.width); svg.setAttribute("height", base.height);
  svg.setAttribute("viewBox", `0 0 ${base.width} ${base.height}`);
  svg.innerHTML = `<defs><marker id="${mid}" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z" fill="currentColor"/></marker></defs>${lines}`;
}
function verdictHTML(forces, lab, cex) {
  const { prem, goal } = PROBF;
  if (cex != null)
    return CL()
      ? __T(2113, [prem.length ? __T(2030) : "", FF(goal)])
      : __T(2114, [lab.get(cex), prem.length ? __T(2115) : "", FF(goal)]) +
        __T(2116);
  const w = R.sel, why = [];
  const bad = prem.filter(p => !forces(w, p));
  if (bad.length) why.push(__T(2117, [bad.map(FF).join(__T(778)), CL() ? __T(2118) : __T(2119)]));
  if (forces(w, goal)) why.push(__T(2120, [FF(goal), CL() ? __T(2121) : __T(2122)]));
  return __T(2123, [CL() ? __T(2124) : __T(2101, [lab.get(w)]), why.join(__T(2036))]);
}

/* クリプキモデルの「図で見る」「理由で見る」。頂点は（式, 階）の組。→ と ¬ は、∀ が住人ごとに枝分かれするのと同じように、
   その階と上のすべての階ごとに「条件の確認」の頂点（その階で、A が光るなら B も光るか）に枝分かれする */
const kNegF = f => f.t === "imp" && f.r.t === "bot";
function kgVal(n, forces) { return n.chk ? (kNegF(n.f) ? !forces(n.w, n.f.l) : (!forces(n.w, n.f.l) || forces(n.w, n.f.r))) : forces(n.w, n.f); }
// → と ¬ の決め手の階：その階より上（その階を含む）で、¬A なら A が光る階、A→B なら A が光り B が光らない階
const kWit = (w, f, forces) => forces.ups.get(w).find(u => kNegF(f) ? forces(u, f.l) : forces(u, f.l) && !forces(u, f.r));
function kgKids(n, forces) {
  if (n.chk) return kNegF(n.f) ? [{ f: n.f.l, w: n.w }] : [{ f: n.f.l, w: n.w }, { f: n.f.r, w: n.w }];
  const f = n.f;
  if (f.t === "atom" || f.t === "bot") return [];
  if (f.t === "and" || f.t === "or") return [{ f: f.l, w: n.w }, { f: f.r, w: n.w }];
  if (!forces(n.w, f)) return [{ chk: true, wit: true, f, w: kWit(n.w, f, forces) }]; // 光らない：決め手の階を一つだけ
  return forces.ups.get(n.w).map(u => ({ chk: true, f, w: u })); // 光る：調べたすべての階
}
const kgKey = n => (n.chk ? (n.wit ? "x" : "c") : "f") + n.w + ":" + fkey(n.f);
const kgTV = (n, v, lab) => n.chk ? (n.wit ? L1(__T(896), "decisive") : "✓") : PREFS.kSym && lab ? `${wSub(lab.get(n.w))} ${v ? "⊩" : "⊮"}` : KB(v);
const kgTVC = v => v ? "t" : "f";
// 未来の階の確認を、肯定の言い方で（「A が光らない：不成立」ではなく「A が光る」）
function kChkText(n, forces, lab) {
  const A = FF(n.f.l), B = FF(n.f.r);
  if (PREFS.kSym && lab) { const W = wSub(lab.get(n.w)); // 記号：wₙ ⊩ A ／ wₙ ⊮ A
    if (kNegF(n.f)) return n.wit ? `${W} ⊩ ${A}` : `${W} ⊮ ${A}`;
    if (n.wit) return __T(2125, [W, A, W, B]);
    return forces(n.w, n.f.l) ? `${W} ⊩ ${B}` : `${W} ⊮ ${A}`; }
  if (kNegF(n.f)) return n.wit ? L1(__T(2126, [A]), `${A} is lit`) : L1(__T(2127, [A]), `${A} is not lit`);
  if (n.wit) return L1(__T(2128, [A, B]), `${A} is lit but ${B} is not`);
  return forces(n.w, n.f.l) ? L1(__T(2129, [B]), `${B} is lit too`) : L1(__T(2127, [A]), `${A} is not lit`);
}
function kgLabel(n, lab, forces) {
  if (!n.chk) return `<span class="tg-f f">${fh(n.f)}</span>`;
  return PREFS.kSym ? `<span class="tg-f">${kChkText(n, forces, lab)}</span>` : __T(2130, [lab.get(n.w), kChkText(n, forces, lab)]);
}
function kgWhy(n, v, forces, lab) {
  if (!n.chk) return reasonHTML(n.w, n.f, forces, lab, false);
  return "";
}
// 塔との対応：式の頂点に、調べる階・未来の範囲・決め手の階を書いておく（指やマウスを重ねると、塔の上で色づく）
function kHiAttr(n, forces) {
  if (n.chk) return ` data-kw="${n.w}"${n.wit ? ` data-kwit="${n.w}"` : ""}`;
  const fut = n.f.t === "imp";
  const wit = fut && !forces(n.w, n.f) ? kWit(n.w, n.f, forces) : null;
  return ` data-kw="${n.w}"${fut ? ` data-kcone="1"` : ""}${wit != null ? ` data-kwit="${wit}"` : ""}`;
}
function kgKeys(n, v, kids, kv) { // 真偽の理由になっている子
  if (n.chk) { if (kNegF(n.f)) return [0]; return v ? [kv[0] ? 1 : 0] : [0, 1]; }
  const f = n.f;
  if (f.t === "and") return v ? [0, 1] : kv.map((x, i) => x ? -1 : i).filter(i => i >= 0).slice(0, 1);
  if (f.t === "or") return v ? kv.map((x, i) => x ? i : -1).filter(i => i >= 0).slice(0, 1) : [0, 1];
  if (f.t === "imp") return v ? kids.map((_, i) => i) : [kv.findIndex(x => !x)];
  return [];
}
function kGraphHTML(roots, w, forces, lab) { // 図で見る
  const open = UI.kgOpen || (UI.kgOpen = new Map()), CAP = 40, defOpen = new Set();
  roots.forEach((r, ri) => { let count = 1; const q = [{ n: { f: r.f, w }, path: "k" + ri, depth: 0 }];
    while (q.length) { const it = q.shift(), ks = kgKids(it.n, forces); if (!ks.length || it.depth >= 8 || count + ks.length > CAP) continue;
      if (!it.n.chk && it.n.f.t === "imp" && ks.length > 1) continue; // 光る → と ¬ の「すべての階」は、最初は閉じておく
      defOpen.add(it.path); count += ks.length; ks.forEach((k, i) => q.push({ n: k, path: it.path + "." + i, depth: it.depth + 1 })); } });
  const node = (n, path, depth) => {
    const v = kgVal(n, forces), ks = depth < 10 ? kgKids(n, forces) : [], m = evMark("KG:" + path + ":" + kgKey(n), v, depth);
    const st = ks.length > 0 && (open.has(path) ? open.get(path) : defOpen.has(path));
    const box = `<div class="tg-node ${kgTVC(m.cur)}${n.chk ? " kg-chk" : ""}${n.wit ? " kg-wit" : ""}"${m.attr}${m.attr ? ` data-pendtxt="${kgTV(n, v, lab)}"` : ""}${kHiAttr(n, forces)}${ks.length ? ` data-kg-tog="${path}" role="button" tabindex="0" title="${st ? __T(2131) : __T(2132)}"` : ` tabindex="0"`}>${kgLabel(n, lab, forces)}<span class="tg-v">${kgTV(n, m.cur, lab)}</span>${ks.length && !st ? __T(2022, [ks.length]) : ""}</div>`;
    return `<li>${box}${st ? `<ul>${ks.map((k, i) => node(k, path + "." + i, depth + 1)).join("")}</ul>` : ""}</li>`;
  };
  return roots.map((r, i) => `<div class="tg-block"><div class="tg-role"><span class="ev-role">${r.role}</span></div><div class="tg-wrap"><div class="tg-inner"><ul class="tg">${node({ f: r.f, w }, "k" + i, 0)}</ul></div></div></div>`).join("") +
    `<p class="tt-note">${L1(__T(2133), "The whole formula is at the top, smaller subformulas below. → and ¬ look at this floor and every floor above it (the future). When one is not lit, the decisive floor is shown; when it is lit, all the floors checked are shown. Hover over (or tap) a node to light up, on the tower, the floors it looks at.")}</p>`;
}
function kAllHTML(forces, lab, cex, wrapId = "kvWrap") { // 全階で見る：仮定と目標の部分式を、すべての階で同じ順に並べ、その階で光る（明）か光っていない（暗）かを札の枠と地の色で示す
  const { prem, goal } = PROBF, subs = subformulas([...prem, goal]).filter(f => f.t !== "bot");
  const role = f => eq(f, goal) ? "goal" : prem.some(q => eq(q, f)) ? "prem" : "";
  const chip = (f, id) => { const r = role(f), on = forces(id, f), miss = r === "goal" && !on && cex === id;
    return `<span class="kv-chip ${on ? "kv-lit" : "kv-dark"}${r ? " kv-" + r : ""}${miss ? " kv-gmiss" : ""}" data-kf="${esc(fkey(f))}" tabindex="0" aria-label="${plainF(f)}${L1(__T(2055), ": ")}${on ? L1(__T(893), "lit") : L1(__T(894), "dark")}">${FF(f)}${r === "goal" ? `<sup class="kv-tag">${L1(__T(889), "goal")}</sup>` : r === "prem" ? `<sup class="kv-tag">${L1(__T(824), "asm")}</sup>` : ""}</span>`; };
  const card = id => { const f = kFloor(R, id);
    const head = PREFS.kSym ? wSub(lab.get(id)) : L1(__T(2101, [lab.get(id)]), `Floor ${lab.get(id)}`);
    return `<div class="floor kv-floor${cex === id ? " cex" : ""}" data-floor="${id}"${f.parent != null ? ` data-parent="${f.parent}"` : ""}><div class="fl-head"><span class="fl-name">${head}</span>${cex === id ? `<span class="fl-cex">${L1(__T(2134), "counterexample")}</span>` : ""}</div>` +
      `<div class="kv-list">${subs.map(x => chip(x, id)).join("")}</div>` +
      (cex === id ? `<div class="kv-miss">${L1(__T(2135, [FF(goal)]), `The goal ${FF(goal)} is not lit here`)}</div>` : "") + `</div>`; };
  const tree = id => { const kids = kKids(R, id); return `<div class="km-node">${kids.length ? `<div class="km-kids">${kids.map(tree).join("")}</div>` : ""}${card(id)}</div>`; };
  return `<div class="kv-legend"><span class="kv-chip kv-lit">${L1(__T(893), "lit")}</span>${L1(__T(2136), "lit (forced) at that floor")}<span class="kv-chip kv-dark">${L1(__T(894), "dark")}</span>${L1(__T(2137), "not lit at that floor (not necessarily false)")}</div>` +
    `<div class="km-wrap kv-wrap" id="${wrapId}"><div class="km-inner"><svg class="km-links" aria-hidden="true"></svg>${tree(0)}</div></div>` +
    `<p class="tt-note">${L1(__T(2138), "The subformulas of the assumptions and the goal appear in the same order on every floor. Touch a formula to light up the floors where it is lit. A formula once lit stays lit on the floors above.")}</p>`;
}
function kTreeHTML(roots, w, forces, lab) { // 理由で見る
  const open = UI.ktOpen || (UI.ktOpen = new Map());
  const node = (n, path, key, defOpen, depth, role) => {
    const v = kgVal(n, forces), ks = depth < 10 ? kgKids(n, forces) : [], kv = ks.map(k => kgVal(k, forces)), keys = kgKeys(n, v, ks, kv);
    const st = ks.length > 0 && (open.has(path) ? open.get(path) : defOpen);
    const many = !n.chk && n.f.t === "imp" && v; // 上の階すべてを調べる必要があるときは、子を閉じておく
    const m = evMark("KT:" + path + ":" + kgKey(n), v, depth), pt = m.attr ? ` data-pendtxt="${kgTV(n, v, lab)}"` : "";
    const tog = ks.length ? `<button type="button" class="tt-tog" data-kt-tog="${path}" aria-expanded="${st}" aria-label="${st ? __T(1804) : __T(2017)}">${st ? "▾" : "▸"}</button>` : `<span class="tt-tog leaf" aria-hidden="true"></span>`;
    const head = n.chk ? (PREFS.kSym ? `<span class="tt-f">${kChkText(n, forces, lab)}</span>` : __T(2139, [lab.get(n.w), kChkText(n, forces, lab)])) : `<span class="tt-f f">${fh(n.f)}</span>`;
    const row = `<div class="tt-row">${tog}<span class="tt-v">${kgTV(n, m.cur, lab)}</span>${head}${role ? `<span class="ev-role">${role}</span>` : ""}<span class="tt-why"${m.hide}>${kgWhy(n, v, forces, lab)}</span></div>`;
    const body = st ? `<ul>${ks.map((k, i) => node(k, path + "." + i, keys.includes(i), keys.includes(i) && !many && depth < 6, depth + 1, "")).join("")}</ul>` : "";
    return `<li class="tt-node ${kgTVC(m.cur)}${key ? " tt-key" : ""}${n.wit ? " kg-wit" : ""}"${m.attr}${pt}${kHiAttr(n, forces)}>${row}${body}</li>`;
  };
  return `<ul class="tt">${roots.map((r, i) => node({ f: r.f, w }, "k" + i, true, true, 0, r.role)).join("")}</ul>` +
    `<p class="tt-note">${L1(__T(2140), "Press ▸ to open the parts that make a formula lit (or not lit). → and ¬ look at this floor and every floor above it (the future). When one is not lit, the decisive floor is shown; when it is lit, all the floors checked are shown. Hover over (or tap) a row to light up, on the tower, the floors it looks at.")}</p>`;
}
function evalHTML(w, forces, lab, stat) {
  const { prem, goal } = PROBF;
  const rows = subformulas([...prem, goal]).filter(f => f.t !== "bot");
  return `<div class="ev-wrap"><table class="ev"><tbody>` + rows.map(f => {
    const v = forces(w, f), role = eq(f, goal) ? __T(889) : prem.some(p => eq(p, f)) ? L1(__T(824), "Assumption") : "";
    return `<tr class="${v ? "on" : ""}"><td class="ev-f">${FF(f)}${role ? `<span class="ev-role">${role}</span>` : ""}</td><td class="ev-v">${KB(v)}</td><td class="ev-why">${reasonHTML(w, f, forces, lab, stat)}</td></tr>`;
  }).join("") + `</tbody></table></div>`;
}
// なぜその階で光る／光らないのか（強制関係の定義をそのまま言葉にする）
function reasonHTML(w, f, forces, lab, stat) {
  const v = forces(w, f);
  if (CL()) { // 古典論理：真理値表による計算
    const T = g => forces(w, g);
    switch (f.t) {
      case "atom": return __T(2141, [FF(f), v ? __T(876) : __T(877)]);
      case "and": return v ? __T(2142, [FF(f.l), FF(f.r)]) : __T(879, [FF(T(f.l) ? f.r : f.l)]);
      case "or": return v ? __T(880, [FF(T(f.l) ? f.l : f.r)]) : __T(2143, [FF(f.l), FF(f.r)]);
      case "imp":
        if (f.r.t === "bot") return v ? __T(879, [FF(f.l)]) : __T(880, [FF(f.l)]);
        return v ? (T(f.l) ? __T(880, [FF(f.r)]) : __T(879, [FF(f.l)])) : __T(2144, [FF(f.l), FF(f.r)]);
    }
  }
  const at = u => u === w ? __T(2145) : stat ? __T(2101, [lab.get(u)]) : __T(2146, [u, lab.get(u)]);
  switch (f.t) {
    case "atom": return v ? __T(2147, [FF(f)]) : __T(2148, [FF(f)]);
    case "and": return v ? __T(2149, [FF(f.l), FF(f.r)]) : __T(2150, [FF(forces(w, f.l) ? f.r : f.l)]);
    case "or": return v ? __T(2126, [FF(forces(w, f.l) ? f.l : f.r)]) : __T(2151, [FF(f.l), FF(f.r)]);
    case "imp": {
      const ups = forces.ups.get(w);
      if (f.r.t === "bot") {
        if (v) return __T(2152, [FF(f.l)]);
        return __T(2153, [at(ups.find(u => forces(u, f.l))), FF(f.l)]);
      }
      if (v) return __T(2154, [FF(f.l), FF(f.r)]);
      return __T(2155, [at(ups.find(u => forces(u, f.l) && !forces(u, f.r))), FF(f.l), FF(f.r)]);
    }
  }
  return "";
}
function kAdd(R, pid) {
  if (R.floors.length >= 7) { toast(__T(2156)); return false; }
  const id = R.nid++;
  R.floors.push({ id, parent: pid, own: [] }); R.sel = id;
}
function kDel(R, id) {
  if (id === 0) return false;
  const gone = new Set(kUp(R, id)), parent = kFloor(R, id).parent;
  R.floors = R.floors.filter(f => !gone.has(f.id));
  if (gone.has(R.sel)) R.sel = parent;
}
function kToggle(R, id, a) {
  if (kAnc(R, id).some(x => kFloor(R, x).own.includes(a))) {
    toast(__T(2157));
    return false;
  }
  const f = kFloor(R, id);
  f.own = f.own.includes(a) ? f.own.filter(x => x !== a) : [...f.own, a].sort();
  R.sel = id;
}
function actR(fn) { const snap = JSON.stringify(R); if (fn(R) === false) return; HISTR.push(snap); R.selPick = false; UI.khi = null; renderRefute(); } // 塔を変えたら、表示は反例の階に戻す
function undoR() { if (!HISTR.length) return; R = JSON.parse(HISTR.pop()); STAGE.fol ? renderStruct() : renderRefute(); }
// 真理値の割り当て、または構造による反証のステージを完了する

/* ================= 反例の意味（反証のクリア画面の解説） =================
   key：どの反例にも共通する決め手（答えの形によらず正しい）
   match：プレイヤーの反例が典型的な形なら、その形の名前を返す（石盤は割り当て、時の塔は塔の形）
   typ：典型的な形だったときの読み方、other：典型と違う形だったとき（典型例を紹介）、where：数学のどこに現れるか */
const CXF = x => F(x);
const CX_NOTES = {
  "r-conv": { match: c => c.tv.P === "F" && c.tv.Q === "T" ? "std" : null,
    key: () => L1(__T(2158, [CXF("P"), CXF("Q"), CXF("P->Q"), CXF("P")]), `The only counterexample is ${CXF("P")} false and ${CXF("Q")} true. The assumption ${CXF("P->Q")} is automatically true when ${CXF("P")} is false.`),
    typ: { std: () => L1(__T(2159, [CXF("P"), CXF("Q")]), `Read ${CXF("P")} as "it rained" and ${CXF("Q")} as "the road is wet". Even if "if it rains, the road gets wet" is true, a wet road does not mean it rained: a street sprinkler may simply have passed by.`) },
    where: () => L1(__T(2160), `Whenever mathematicians ask "does the converse hold?", they look for a counterexample of this shape. For "every square is a rectangle", the converse "every rectangle is a square" is refuted by a rectangle that is not a square.`) },
  "r-inv": { match: c => c.tv.P === "F" && c.tv.Q === "T" ? "std" : null,
    key: () => L1(__T(2161, [CXF("P"), CXF("Q"), CXF("~P->~Q"), CXF("Q->P")]), `As in 6-1, the only counterexample is ${CXF("P")} false and ${CXF("Q")} true. The inverse ${CXF("~P->~Q")} is the contrapositive of the converse ${CXF("Q->P")}, so the same assignment makes it false.`),
    typ: { std: () => L1(__T(2162), `"If it rains, the road gets wet" does not give "if it does not rain, the road does not get wet": a sprinkler can wet the road without any rain.`) },
    where: () => L1(__T(2163, [CXF("~Q->~P")]), `Only the contrapositive ${CXF("~Q->~P")} means the same as the original. The converse and the inverse are contrapositives of each other, so when one fails, so does the other.`) },
  "r-ior": { match: c => c.tv.P === "T" && c.tv.Q === "T" ? "std" : null,
    key: () => L1(__T(2164, [CXF("P"), CXF("Q"), CXF("P|Q"), CXF("~(P&Q)")]), `The only counterexample is ${CXF("P")} and ${CXF("Q")} both true. ${CXF("P|Q")} is true when both are true, and then ${CXF("~(P&Q)")} is false.`),
    typ: { std: () => L1(__T(2165, [CXF("P"), CXF("Q")]), `Read ${CXF("P")} as "orders tea" and ${CXF("Q")} as "orders cake". Someone who said "I'll order tea or cake" has not lied by ordering both.`) },
    where: () => L1(__T(2166, [CXF("(P|Q)&~(P&Q)")]), `The "or" of logic and mathematics includes the case of both (inclusive disjunction). To say "exactly one", write the exclusive disjunction ${CXF("(P|Q)&~(P&Q)")}.`) },
  "r-dm": { match: c => c.tv.P === "T" && c.tv.Q === "F" ? "pt" : c.tv.P === "F" && c.tv.Q === "T" ? "qt" : null,
    key: () => L1(__T(2167, [CXF("P"), CXF("Q"), CXF("~(P&Q)"), CXF("~P&~Q")]), `A counterexample makes exactly one of ${CXF("P")} and ${CXF("Q")} true. If both are true, the assumption ${CXF("~(P&Q)")} is false; if both are false, the goal ${CXF("~P&~Q")} is true.`),
    typ: { pt: () => L1(__T(2168, [CXF("P"), CXF("Q")]), `Reading ${CXF("P")} as "full marks in mathematics" and ${CXF("Q")} as "full marks in English", it is the case "full marks in mathematics only": not full marks in both, but not "full marks in neither" either.`),
           qt: () => L1(__T(2169, [CXF("P"), CXF("Q")]), `Reading ${CXF("P")} as "full marks in mathematics" and ${CXF("Q")} as "full marks in English", it is the case "full marks in English only": not full marks in both, but not "full marks in neither" either.`) },
    where: () => L1(__T(2170, [CXF("~P|~Q")]), `The correct form of De Morgan's law is ${CXF("~P|~Q")} (5-7). When negation is distributed, ∧ turns into ∨.`) },
  "5-1": { match: c => c.n === 2 && !c.lit(0, "P") && c.lit(1, "P") ? "min" : null,
    key: () => L1(__T(2171, [CXF("P"), CXF("P"), CXF("P"), CXF("P"), CXF("P"), CXF("~P")]), `Every counterexample has a floor where ${CXF("P")} is not yet lit and a floor above it where ${CXF("P")} is lit. ${CXF("P")} is not known now, but a future where it becomes known is possible, so neither ${CXF("P")} nor ${CXF("~P")} is lit.`),
    typ: { min: () => L1(__T(2172, [CXF("P"), CXF("P"), CXF("~P")]), `It has the smallest shape (two floors). Think of ${CXF("P")} as an unsolved conjecture. There is neither a proof nor a refutation now, so ${CXF("P")} is not lit; and since it may be proved one day, ${CXF("~P")} (it will never be proved) is not lit either.`) },
    other: () => L1(__T(2173, [CXF("P")]), `It is a larger tower than the smallest one, but it has the decisive feature above. The smallest counterexample is a two-floor tower: add one floor above floor 0 and light ${CXF("P")} only there.`),
    where: () => L1(__T(2174), `This is the intuitionistic view itself: only what has been proved is true. Being unable to assert "true or not true" of an unsolved conjecture is exactly this situation.`) },
  "5-2": { match: c => c.n === 2 && !c.lit(0, "P") && c.lit(1, "P") ? "min" : null,
    key: () => L1(__T(2175, [CXF("P"), CXF("~P"), CXF("P"), CXF("~~P"), CXF("P")]), `In every counterexample, ${CXF("P")} is not lit at the counterexample floor, and ${CXF("~P")} is lit on no floor above it (in every future, ${CXF("P")} may still become known). So ${CXF("~~P")} is lit while ${CXF("P")} is not.`),
    typ: { min: () => L1(__T(2176, [CXF("~~P"), CXF("P"), CXF("P")]), `It is the same two-floor tower as in H1-1. ${CXF("~~P")} says "${CXF("P")} will never be refuted". Knowing that is not the same as having ${CXF("P")} itself.`) },
    other: () => L1(__T(2177), `It is a tower of more than two floors, but it has the decisive feature above. The smallest counterexample is the same two-floor tower as in H1-1.`),
    where: () => L1(__T(2178), `Showing that "assuming it does not exist leads to a contradiction" does not actually construct the object. Intuitionism keeps double negation in place to preserve this distinction.`) },
  "5-3": { match: c => c.n === 2 && !c.lit(0, "P") && c.lit(1, "P") && !c.lit(0, "Q") && !c.lit(1, "Q") ? "min" : null,
    key: () => L1(__T(2179, [CXF("(P->Q)->P"), CXF("P"), CXF("P"), CXF("Q"), CXF("P->Q")]), `In every counterexample, ${CXF("(P->Q)->P")} is lit at the counterexample floor and ${CXF("P")} is not. For that, some floor above must light ${CXF("P")} but not ${CXF("Q")}, so that ${CXF("P->Q")} is not lit.`),
    typ: { min: () => L1(__T(2180, [CXF("Q"), CXF("Q"), CXF("((~P)->P)->P")]), `It is the same two-floor tower as in H1-1, with ${CXF("Q")} lit nowhere. Reading ${CXF("Q")} as the contradiction ⊥, Peirce's law becomes ${CXF("((~P)->P)->P")}, an inference close to reductio.`) },
    other: () => L1(__T(2181, [CXF("P"), CXF("Q")]), `It differs from the smallest one, but it has the decisive feature above. The smallest counterexample is a two-floor tower with ${CXF("P")} lit only above and ${CXF("Q")} lit nowhere.`),
    where: () => L1(__T(2182), `Peirce's law contains no ¬, yet the power of classical logic hides in it. The difference between intuitionistic and classical logic is not only about negation.`) },
  "5-4": { match: c => { if (c.n !== 3) return null; const ks = c.kids(0); if (ks.length !== 2 || c.lit(0, "P") || c.lit(0, "Q")) return null;
      const [a, b] = ks, pa = c.lit(a, "P"), qa = c.lit(a, "Q"), pb = c.lit(b, "P"), qb = c.lit(b, "Q");
      return (pa && !qa && qb && !pb) || (pb && !qb && qa && !pa) ? "min" : null; },
    key: () => L1(__T(2183, [CXF("P"), CXF("Q"), CXF("P"), CXF("Q"), CXF("~(P&Q)")]), `Every counterexample needs a future where ${CXF("P")} is lit and a future where ${CXF("Q")} is lit, on separate branches. If ${CXF("P")} and ${CXF("Q")} were both lit in one future, the assumption ${CXF("~(P&Q)")} would not be lit.`),
    typ: { min: () => L1(__T(2184, [CXF("P"), CXF("Q"), CXF("P"), CXF("Q")]), `It has the smallest branching shape. Even knowing that "${CXF("P")} and ${CXF("Q")} are never both true", it is not yet settled which of them fails: a future where ${CXF("P")} becomes known and one where ${CXF("Q")} does are both possible.`) },
    other: () => L1(__T(2185, [CXF("P"), CXF("Q")]), `It differs from the smallest one, but it has the decisive feature above. The smallest counterexample branches two floors above floor 0, lighting only ${CXF("P")} on one and only ${CXF("Q")} on the other.`),
    where: () => L1(__T(2186, [CXF("~P|~~P")]), `In intuitionistic logic, this direction of De Morgan's law is as strong as the "weak excluded middle" ${CXF("~P|~~P")}, which a similar branching tower refutes as well.`) },

  // --- 鑑定の部屋：石盤・時の塔 ---
  "6-6:B": { match: c => c.tv.P === "F" && c.tv.Q === "T" ? "std" : null,
    key: () => L1(__T(2187, [CXF("P"), CXF("Q")]), `The only counterexample is ${CXF("P")} false and ${CXF("Q")} true (as in 6-1).`),
    typ: { std: () => L1(__T(2188), `"If it rains, the road gets wet" does not give "if the road is wet, it rained": a sprinkler may have passed by.`) },
    where: () => L1(__T(2189, [CXF("P->Q"), CXF("Q->P")]), `Door B has the form "if ${CXF("P->Q")}, then its converse ${CXF("Q->P")}". Whether the converse holds is not settled by the original statement.`) },
  "5-5:B": { match: c => c.n === 2 && c.lit(0, "Q") && !c.lit(0, "P") && c.lit(1, "P") ? "min" : null,
    key: () => L1(__T(2190, [CXF("Q"), CXF("P"), CXF("P"), CXF("P"), CXF("~P"), CXF("~P->~Q"), CXF("~Q"), CXF("Q")]), `Every counterexample has a floor where ${CXF("Q")} is lit and ${CXF("P")} is not, and a floor above where ${CXF("P")} is lit. Otherwise ${CXF("~P")} would be lit, and ${CXF("~P->~Q")} would light ${CXF("~Q")} too, which clashes with ${CXF("Q")} being lit.`),
    typ: { min: () => L1(__T(2191, [CXF("Q"), CXF("P"), CXF("~P->~Q"), CXF("Q"), CXF("~~P"), CXF("P"), CXF("P")]), `A tower where only ${CXF("Q")} is known on the lower floor and ${CXF("P")} becomes known above. From ${CXF("~P->~Q")} and ${CXF("Q")} you only get ${CXF("~~P")} (${CXF("P")} will never be refuted), not ${CXF("P")} itself.`) },
    other: () => L1(__T(2192, [CXF("Q"), CXF("P")]), `It differs from the smallest one, but it has the decisive feature above. The smallest counterexample is a two-floor tower with ${CXF("Q")} lit from the lower floor and ${CXF("P")} only on the upper floor.`),
    where: () => L1(__T(2193), `Going back from the contrapositive to the original (5-4) uses the power to remove double negation. Intuitionistically, only the direction towards the contrapositive holds.`) },
  "5-5:C": { match: c => { if (c.n !== 3) return null; const ks = c.kids(0); if (ks.length !== 2 || c.lit(0, "P") || c.lit(0, "Q")) return null;
      const [a, b] = ks; return (c.lit(a, "P") && !c.lit(a, "Q") && c.lit(b, "Q") && !c.lit(b, "P")) || (c.lit(b, "P") && !c.lit(b, "Q") && c.lit(a, "Q") && !c.lit(a, "P")) ? "min" : null; },
    key: () => L1(__T(2194, [CXF("P"), CXF("Q"), CXF("Q"), CXF("P"), CXF("P"), CXF("Q")]), `Every counterexample needs a future where ${CXF("P")} is lit but ${CXF("Q")} is not, and one where ${CXF("Q")} is lit but ${CXF("P")} is not, on separate branches. If one lay above the other, the upper one would light both.`),
    typ: { min: () => L1(__T(2195, [CXF("P"), CXF("Q")]), `The smallest branching shape: it is not yet settled whether ${CXF("P")} or ${CXF("Q")} will become known first.`) },
    other: () => L1(__T(2185, [CXF("P"), CXF("Q")]), `It differs from the smallest one, but it has the decisive feature above. The smallest counterexample branches two floors above floor 0, lighting only ${CXF("P")} on one and only ${CXF("Q")} on the other.`),
    where: () => L1(__T(2196), `Adding this formula to intuitionistic logic gives the logic of towers whose floors form a single line (Gödel–Dummett logic).`) },
  // --- 構造の鑑定（第 10 層） ---
  "s-ex": { match: c => c.iso({ n: 2, rel: { P: ["1"] } }) ? "min" : null,
    key: () => L1(__T(2197, [CXF("P"), CXF("P")]), `Every counterexample has a resident who is ${CXF("P")} and one who is not (at least two residents).`),
    typ: { min: () => L1(__T(2198, [CXF("P"), CXF("P")]), `Of two residents, only one is ${CXF("P")}. Reading ${CXF("P")} as "wears glasses": a class with someone in glasses need not be all glasses.`) },
    other: () => L1(__T(2199, [CXF("P")]), `It differs from the smallest one, but it has the decisive feature above. The smallest counterexample has two residents, only one of them ${CXF("P")}.`),
    where: () => L1(__T(2200), `You cannot go from "there is one" to "all". That is why a resident brought in from an ∃ key is not an arbitrary resident (the eigenvariable condition).`) },
  "s-pos": { match: c => c.iso({ n: 2, rel: { R: ["1,1", "1,2"] } }) ? "min" : null,
    key: () => L1(__T(2201, [CXF("R"), CXF("R")]), `Every counterexample has a resident related by ${CXF("R")} to everyone and a resident related to no one.`),
    typ: { min: () => L1(__T(2202, [CXF("R(x,y)"), termH("x"), termH("y")]), `Resident 1 is related to everyone, resident 2 to no one. Reading ${CXF("R(x,y)")} as "${termH("x")} wrote to ${termH("y")}": "someone wrote to everyone" may hold while "everyone wrote to someone" fails.`) },
    other: () => L1(__T(2203), `It differs from the smallest one, but it has the decisive feature above. The smallest counterexample has two residents, where only resident 1 is related to everyone.`),
    where: () => L1(__T(2204, [CXF("R")]), `The valid "from ∃y∀x to ∀x∃y" of 8-8 quantified the right-hand place (the receiver). Which place you quantify changes whether the inference is valid.`) },
  "s-nomouse": { match: c => c.iso({ n: 1, rel: { C: ["1"], M: [], F: [] } }) ? "min" : null,
    key: () => L1(__T(2205, [CXF("M")]), `No counterexample has any mouse (${CXF("M")}). With even one mouse, the assumptions make it fear the cat, and the goal becomes true.`),
    typ: { min: () => L1(__T(2206), `A storehouse with one cat and no mice. "Every mouse ..." is automatically true when there are no mice (vacuous truth).`) },
    other: () => L1(__T(2207), `It differs from the smallest one, but it has the decisive feature above. The smallest counterexample is one resident who is a cat, and no mice.`),
    where: () => L1(__T(2208), `A claim "every ... is ..." is true even when there is nothing of that kind. That is also why "every element of the empty set ..." is always true.`) },
  "s-mouse": { match: c => c.iso({ n: 4, rel: { M: ["1", "2"], C: ["3", "4"], F: ["1,3", "2,4"] } }) ? "min" : c.iso({ n: 2, rel: { M: ["1", "2"], C: ["1", "2"], F: ["1,2", "2,1"] } }) ? "dual" : null,
    key: () => L1(__T(2209), `In every counterexample, every cat has some mouse that does not fear it. So there must be at least two mice and two cats (with only one, that one would be feared by all).`),
    typ: { min: () => L1(__T(2210), `Two mice fear two different cats. "Every mouse fears some cat" holds, but no cat is feared by all. If residents play both roles (mouse and cat at once), two residents are enough.`),
           dual: () => L1(__T(2211), `Both residents are mice and cats at once, and each fears the other. With residents playing both roles, two residents make a counterexample: every mouse fears some cat, but no cat is feared by both.`) },
    other: () => L1(__T(2212), `It differs from the typical one, but it has the decisive feature above. The typical counterexample has two mice and two cats, each mouse fearing a different cat. If residents play both roles (mouse and cat at once), two residents are enough.`),
    where: () => L1(__T(2213), `This is the difference between ∀∃ and ∃∀. The difference between "continuous" (a δ for each point) and "uniformly continuous" (one δ for all points) has the same shape.`) },
  "8-3:B": { match: c => c.iso({ n: 2, rel: { R: ["1,1", "2,2"] } }) ? "eq" : c.iso({ n: 2, rel: { R: ["1,2", "2,1"] } }) ? "swap" : null,
    key: () => L1(__T(2214, [CXF("R")]), `In every counterexample everyone is ${CXF("R")}-related to someone, but no one is related to everyone (at least two residents).`),
    typ: { eq: () => L1(__T(2215, [CXF("R")]), `${CXF("R")} is "equals": everyone has themselves as a partner, but no one equals everyone.`),
           swap: () => L1(__T(2216), `The two point at each other: everyone has a partner, but no one is everyone's partner.`) },
    other: () => L1(__T(2217, [CXF("R")]), `It differs from the typical one, but it has the decisive feature above. The typical counterexample has two residents with ${CXF("R")} as "equals".`),
    where: () => L1(__T(2218), `"Everyone has a favourite food" differs from "there is a food everyone likes". That is why the quantifiers cannot be swapped.`) },
  "8-3:C": { match: c => c.iso({ n: 2, rel: { P: ["1"], Q: ["2"] } }) ? "min" : null,
    key: () => L1(__T(2219, [CXF("P"), CXF("Q")]), `Every counterexample has a resident who is not ${CXF("P")} and one who is not ${CXF("Q")} (each having the other property).`),
    typ: { min: () => L1(__T(2220, [CXF("P"), CXF("Q"), CXF("P"), CXF("Q")]), `Resident 1 is only ${CXF("P")}, resident 2 only ${CXF("Q")}. Reading them as "morning person" and "night owl": everyone is one or the other, yet not all are morning people, nor all night owls.`) },
    other: () => L1(__T(2221, [CXF("P"), CXF("Q")]), `It differs from the typical one, but it has the decisive feature above. The typical counterexample has two residents, one only ${CXF("P")} and the other only ${CXF("Q")}.`),
    where: () => L1(__T(2222), `∀ distributes over ∧ (7-7), but not over ∨.`) },
  // --- 公理の鏡（第 16 層） ---
  "x-total": { match: c => c.iso({ n: 2, rel: { "≤": ["1,1", "2,2"] } }) ? "min" : null,
    key: () => L1(__T(2223, [CXF("x <= y"), CXF("y <= x")]), `Every counterexample has two residents that cannot be compared (neither ${CXF("x <= y")} nor ${CXF("y <= x")}).`),
    typ: { min: () => L1(__T(2224), `The smallest partial order: each resident is comparable only with itself.`) },
    other: () => L1(__T(2225, [CXF("x <= x")]), `It differs from the smallest one, but it has the decisive feature above. The smallest counterexample has two residents with only ${CXF("x <= x")} true.`),
    where: () => L1(__T(2226), `Set inclusion ⊆ ({1} and {2} are incomparable) and divisibility of natural numbers (neither of 2 and 3 divides the other) are typical partial orders that are not total.`) },
  "x-antisym": { match: c => c.iso({ n: 2, rel: { "≤": ["1,1", "1,2", "2,1", "2,2"] } }) ? "min" : null,
    key: () => L1(__T(2227, [CXF("x <= y")]), `Every counterexample has two different residents each ${CXF("x <= y")} of the other.`),
    typ: { min: () => L1(__T(2228, [CXF("x <= y"), termH("x"), termH("y")]), `The two are each "at most" the other, yet different. Reading ${CXF("x <= y")} as "the score of ${termH("x")} is at most that of ${termH("y")}": two people with the same score are each at most the other, yet different.`) },
    other: () => L1(__T(2229, [CXF("x <= y")]), `It differs from the smallest one, but it has the decisive feature above. The smallest counterexample has two residents with ${CXF("x <= y")} true for every pair.`),
    where: () => L1(__T(2230), `A preorder is a ranking that allows ties. Grouping tied people together turns it into a partial order.`) },
  "x-max": { match: c => c.iso({ n: 2, con: { m: "1" }, rel: { "≤": ["1,1", "2,2"] } }) ? "min" : null,
    key: () => L1(__T(2231, [termH("m"), termH("m"), termH("m"), termH("m")]), `Every counterexample has a resident incomparable with ${termH("m")} (no one is above ${termH("m")}, so anyone not below ${termH("m")} is incomparable with it).`),
    typ: { min: () => L1(__T(2232, [termH("m"), termH("m"), termH("m")]), `${termH("m")} is resident 1, incomparable with resident 2. No one is above ${termH("m")}, yet ${termH("m")} is not the top either.`) },
    other: () => L1(__T(2233, [termH("m")]), `It differs from the smallest one, but it has the decisive feature above. The smallest counterexample has two incomparable residents, with ${termH("m")} one of them.`),
    where: () => L1(__T(2234), `A "maximal set" in a family (nothing larger) need not be the largest. Zorn's lemma, too, guarantees a maximal element, not a greatest one.`) },
  "x-rid": { match: c => c.iso({ n: 2, con: { e: "1" }, fun: { "*": { "1,1": "1", "1,2": "2", "2,1": "1", "2,2": "2" } } }) ? "min" : null,
    key: () => L1(__T(2235, [CXF("~(x * e = x)"), termH("x"), termH("x"), termH("e"), CXF("e * e = e")]), `Every counterexample has a resident ${termH("x")} with ${CXF("~(x * e = x)")}, different from ${termH("e")} (since ${CXF("e * e = e")}).`),
    typ: { min: () => L1(__T(2236, [termH({ f: "*", args: ["x", "e"] }), termH("e")]), `The operation "the product is always the right-hand resident". Every resident is a left identity, but ${termH({ f: "*", args: ["x", "e"] })} comes out as ${termH("e")}, so there is no right identity.`) },
    other: () => L1(__T(2237), `It differs from the smallest one, but it has the decisive feature above. The smallest counterexample has two residents with "the product is always the right-hand resident".`),
    where: () => L1(__T(2238), `This operation is called a right zero semigroup. A property on one side does not guarantee the other side.`) },
  "x-twoid": { match: c => c.iso({ n: 2, con: { e: "1", "e'": "2" }, fun: { "*": { "1,1": "1", "1,2": "2", "2,1": "1", "2,2": "2" } } }) ? "min" : null,
    key: () => L1(__T(2239, [termH("e"), termH("e'")]), `In every counterexample, ${termH("e")} and ${termH("e'")} are different residents, both left identities.`),
    typ: { min: () => L1(__T(2240, [termH("e"), termH("e'")]), `With "the product is always the right-hand resident", every resident is a left identity, so ${termH("e")} and ${termH("e'")} can be chosen apart.`) },
    other: () => L1(__T(2241, [termH("e"), termH("e'")]), `It differs from the smallest one, but it has the decisive feature above. The smallest counterexample has two residents, "the product is always the right-hand resident", and ${termH("e")}, ${termH("e'")} different.`),
    where: () => L1(__T(2242), `In 13-1 they coincided because one of them was a right identity. With a left and a right identity, the identity is unique.`) },
  "x-comm": { match: c => c.iso({ n: 3, con: { e: "1" }, fun: { "*": { "1,1": "1", "1,2": "2", "1,3": "3", "2,1": "2", "3,1": "3", "2,2": "2", "2,3": "3", "3,2": "2", "3,3": "3" } } }) ? "min" : null,
    key: () => L1(__T(2243, [CXF("~(x * y = y * x)"), termH("e"), termH("e")]), `Every counterexample has two residents with ${CXF("~(x * y = y * x)")}, neither of them ${termH("e")} (multiplying by ${termH("e")} gives the other). So at least three residents are needed.`),
    typ: { min: () => L1(__T(2244, [termH("e")]), `Between the two residents other than ${termH("e")}, "the product is always the right-hand one": 2·3 = 3, but 3·2 = 2.`) },
    other: () => L1(__T(2245, [termH("e")]), `It differs from the smallest one, but it has the decisive feature above. One smallest counterexample has three residents, with "the product is always the right-hand one" between the two other than ${termH("e")}.`),
    where: () => L1(__T(2246), `Joining strings ("ab" differs from "ba") is an everyday non-commutative monoid; the empty string is the identity.`) },
  "x-order2": { match: c => c.iso(cxPreset("z3")) ? "z3" : null,
    key: () => L1(__T(2247, [termH("e")]), `Every counterexample has a resident whose square is not ${termH("e")}. At least three residents are needed (in groups of at most two, every square is the identity).`),
    typ: { z3: () => L1(__T(2248), `The cyclic group ℤ/3. Think of turning a clock hand by 120°: doing one turn twice does not bring it back (three turns do).`) },
    other: () => L1(__T(2249), `It differs from the smallest one, but it has the decisive feature above. The smallest counterexample is the cyclic group ℤ/3.`),
    where: () => L1(__T(2250), `A group in which every square is the identity is necessarily commutative; it is a strong condition on a group.`) },
  "x-nonab": { match: c => c.iso(cxPreset("s3")) ? "s3" : null,
    key: () => L1(__T(2251, [CXF("~(x * y = y * x)")]), `Every counterexample has two residents with ${CXF("~(x * y = y * x)")}. At least six residents are needed (all groups of at most five are commutative).`),
    typ: { s3: () => L1(__T(2252, ["S₃"]), `The symmetric group S₃: the six motions of an equilateral triangle. "Turn by 120°, then flip" and "flip, then turn by 120°" give different results.`) },
    other: () => L1(__T(2253, ["S₃", "S₃"]), `A group other than S₃, but it has the decisive feature above. The smallest counterexample is the symmetric group S₃.`),
    where: () => L1(__T(2254), `Moves of a Rubik's cube, products of matrices: operations whose result depends on the order are all examples of non-commutative groups.`) },
  "x-ind": { match: c => c.iso({ n: 2, con: { "0": "1" }, fun: { s: { "1": "1", "2": "2" }, "+": { "1,1": "1", "2,1": "2", "1,2": "1" } } }) ? "min" : null,
    key: () => L1(__T(2255, [termH("0"), termH({ f: "s", args: ["x"] }), CXF("0 + x = x")]), `Every counterexample has a resident that cannot be reached from ${termH("0")} by following ${termH({ f: "s", args: ["x"] })}. If every resident were reachable, the induction argument would go through and ${CXF("0 + x = x")} would hold.`),
    typ: { min: () => L1(__T(2256, [termH("0"), termH({ f: "s", args: ["x"] }), termH("0")]), `Resident 2 is an "extra number" that cannot be reached from ${termH("0")} (resident 1) by ${termH({ f: "s", args: ["x"] })}. Such a resident may behave as no natural number does: adding ${termH("0")} does not give it back.`) },
    other: () => L1(__T(2257, [termH({ f: "s", args: ["x"] }), termH("0")]), `It differs from the smallest one, but it has the decisive feature above. The smallest counterexample has two residents, ${termH({ f: "s", args: ["x"] })} changing nothing, and ${termH("0")} + resident 2 not equal to resident 2.`),
    where: () => L1(__T(2258), `Peano arithmetic also has "non-standard models" containing extra numbers while satisfying induction (much more complex structures, satisfying induction for every formula).`) },
  "x-judge:B": { match: c => c.iso({ n: 2, rel: { "<": [] } }) ? "min" : null,
    key: () => L1(__T(2259, [CXF("x < y"), CXF("x = y"), CXF("y < x")]), `Every counterexample has two residents with neither ${CXF("x < y")}, ${CXF("x = y")} nor ${CXF("y < x")} (an incomparable pair).`),
    typ: { min: () => L1(__T(2260, [CXF("x < y")]), `The smallest shape: no ${CXF("x < y")} relation between the two at all.`) },
    other: () => L1(__T(2261, [CXF("x < y")]), `It differs from the smallest one, but it has the decisive feature above. The smallest counterexample has two residents with ${CXF("x < y")} false everywhere.`),
    where: () => L1(__T(2262), `Proper inclusion ⊊ of sets is a strict order with incomparable sets.`) },
  "x-judge:C": { match: c => c.iso({ n: 1, rel: { "<": [] } }) ? "min" : null,
    key: () => L1(__T(2263), `Every counterexample has a resident with no one above it (a top resident).`),
    typ: { min: () => L1(__T(2264, [CXF("x < y")]), `A single resident and no ${CXF("x < y")} at all: no one is above that one.`) },
    other: () => L1(__T(2265), `It differs from the smallest one, but it has the decisive feature above. The smallest counterexample has a single resident.`),
    where: () => L1(__T(2266), `Every finite order has a maximal element. "Every number has a larger one" holds for natural numbers because they go on without end.`) },
  // --- 迷宮の中枢・順序の塔 ---
  "core-3": { match: c => c.iso({ n: 1, con: { e: "1" }, fun: { "*": { "1,1": "1" }, i: { "1": "1" } } }) ? "triv" : null,
    key: () => L1(__T(2267), `Any structure satisfying all the group axioms is a counterexample, since the goal ⊥ is false in every structure.`),
    typ: { triv: () => L1(__T(2268, [termH("e")]), `The group with a single resident (the trivial group): ${termH("e")}, the inverse and the product are all that resident.`) },
    other: () => L1(__T(2269), `The group you built is enough. The smallest example is the trivial group with one resident.`),
    where: () => L1(__T(2270), `A theory is consistent as soon as one structure (model) satisfies it. Hilbert showed the consistency of his axioms of geometry this way, with a model built from real coordinates.`) },
  "core-4:A": { match: c => c.iso(cxPreset("s3")) ? "s3" : null,
    key: () => L1(__T(2271), `A structure satisfying the laws with commutativity false is a non-commutative group, with at least six residents.`),
    typ: { s3: () => L1(__T(2272), `The symmetric group S₃: motions of a triangle give different results in a different order.`) },
    other: () => L1(__T(2273), `A group other than S₃, but non-commutative. The smallest example is S₃.`),
    where: () => L1(__T(2274), `In group theory, both commutative (abelian) and non-commutative groups are central objects; the group axioms do not settle commutativity.`) },
  "core-4:¬A": { match: c => c.iso({ n: 1, con: { e: "1" }, fun: { "*": { "1,1": "1" }, i: { "1": "1" } } }) ? "triv" : c.iso(cxPreset("z2")) ? "z2" : null,
    key: () => L1(__T(2275), `Any commutative group is a counterexample (a town where ¬A is false, that is, A is true).`),
    typ: { triv: () => L1(__T(2276), `The group with a single resident: there is only one product, so it is commutative.`),
           z2: () => L1(__T(2277), `The cyclic group ℤ/2. Think of adding even and odd (even + odd = odd, odd + odd = even): the order does not matter.`) },
    other: () => L1(__T(2278), `The commutative group you built is enough. The smallest example is the group with one resident.`),
    where: () => L1(__T(2279), `When neither A nor ¬A follows from the laws, A is independent of them; the two towns side by side show it.`) },
  "15-inf0": { match: c => c.iso({ n: 1, con: { "0": "1" }, fun: { s: { "1": "1" }, "+": { "1,1": "1" } } }) ? "min" : null,
    key: () => L1(__T(2280, [termH("0"), termH("0"), termH({ f: "s", args: ["0"] })]), `Every counterexample has a resident with no larger resident. Since every resident is reached from ${termH("0")}, following ${termH("0")}, ${termH({ f: "s", args: ["0"] })}, … must return somewhere to a resident already met.`),
    typ: { min: () => L1(__T(2281, [termH("0"), termH("0")]), `A world with a single resident: the number after ${termH("0")} is ${termH("0")} again, and numbers end right there.`) },
    other: () => L1(__T(2282), `It differs from the smallest one, but it has the decisive feature above. The smallest counterexample is a world with one resident.`),
    where: () => L1(__T(2283, [termH("0")]), `Many number systems wrap around, like the hours on a clock (after 12 comes 1). The Peano axiom "${termH("0")} is not the successor of any number" shuts such systems out.`) },
  "core-5:A": { match: c => c.iso({ n: 2, con: { "0": "1" }, fun: { s: { "1": "1", "2": "2" }, "+": { "1,1": "1", "2,1": "2", "1,2": "1" } } }) ? "min" : null,
    key: () => L1(__T(2284, [termH("0"), termH({ f: "s", args: ["x"] })]), `Every counterexample has a resident unreachable from ${termH("0")} by ${termH({ f: "s", args: ["x"] })} (as in 16-9).`),
    typ: { min: () => L1(__T(2285, [termH("0"), termH("0")]), `Resident 2 is an "extra number" unreachable from ${termH("0")}, and adding ${termH("0")} does not give it back.`) },
    other: () => L1(__T(2286), `It differs from the smallest one, but it has the decisive feature above. The smallest counterexample is the two-resident structure of 16-9.`),
    where: () => L1(__T(2287), `Laws without induction cannot shut out extra numbers, so A cannot be proved from them.`) },
  "core-5:¬A": { match: c => c.iso({ n: 1, con: { "0": "1" }, fun: { s: { "1": "1" }, "+": { "1,1": "1" } } }) ? "min" : null,
    key: () => L1(__T(2288, [CXF("0 + x = x")]), `Any structure satisfying both the laws and ${CXF("0 + x = x")} is a counterexample (a town where ¬A is false).`),
    typ: { min: () => L1(__T(2289, [CXF("0 + 0 = 0"), CXF("0 + x = x")]), `A world with a single resident: since ${CXF("0 + 0 = 0")}, ${CXF("0 + x = x")} simply holds.`) },
    other: () => L1(__T(2290), `The town you built is enough. The smallest example is a world with one resident.`),
    where: () => L1(__T(2291), `Neither A nor ¬A follows from the laws; these two towns open the third way (A is independent of the laws).`) },
};
// 構造が典型例と同じ形か（住人の番号の付け替えを無視して比べる）。sp に書いた記号・欄だけを比べる
function cxIso(St, sp) {
  if (!St || St.n !== sp.n) return false;
  const els = Array.from({ length: sp.n }, (_, i) => String(i + 1));
  const perms = a => a.length <= 1 ? [a] : a.flatMap((x, i) => perms([...a.slice(0, i), ...a.slice(i + 1)]).map(r => [x, ...r]));
  return perms(els).some(pm => { const m = k => pm[+k - 1], mt = t => t.split(",").map(m).join(",");
    for (const [c, v] of Object.entries(sp.con || {})) if (String((St.con || {})[c]) !== m(v)) return false;
    for (const [f, tab] of Object.entries(sp.fun || {})) for (const [k, v] of Object.entries(tab)) if (String(((St.fun || {})[f] || {})[mt(k)]) !== m(v)) return false;
    for (const [P, tu] of Object.entries(sp.rel || {})) { const want = new Set(tu.map(mt)), have = new Set((St.rel || {})[P] || []); if (want.size !== have.size || [...want].some(x => !have.has(x))) return false; }
    return true; });
}
const cxPreset = id => { const pr = PRESETS.find(x => x.id === id); return { n: pr.n, con: pr.con, fun: pr.fun }; };
function cxBuild(id) { // 「この反例の意味」の枠（いまの R から、典型的な形かどうかを判定）
  const N = CX_NOTES[id]; if (!N || !R) return "";
  let c;
  if (STAGE.fol) c = { St: R, iso: sp => cxIso(R, sp) }; // 構造（一階述語論理）を先に。古典論理の層でも、述語論理なら構造で判定する
  else if (CL()) c = { tv: R.tv || {} };
  else { const forces = makeForcer(R); c = { n: R.floors.length, kids: id2 => kKids(R, id2), lit: (w, a) => forces(w, parse(a)) }; }
  let k = null; try { k = N.match(c); } catch (e) { k = null; }
  const mine = k && N.typ[k] ? N.typ[k]() : N.other ? N.other() : "";
  return `<div class="cx-note"><h3>${L1(__T(2292), "What this counterexample means")}</h3>
    <p><b>${L1(__T(896), "The key")}</b>${L1(__T(2055), ": ")}${N.key()}</p>
    ${mine ? `<p><b>${L1(__T(2293), "Your counterexample")}</b>${L1(__T(2055), ": ")}${mine}</p>` : ""}
    <p><b>${L1(__T(2294), "Where it appears")}</b>${L1(__T(2055), ": ")}${N.where()}</p></div>`;
}
function cxNoteInsert() { // 反証のクリア画面に「この反例の意味」を差し込む
  const chk = $(".overlay .modal .check"), html = STAGE && cxBuild(STAGE.pid); if (chk && html) chk.insertAdjacentHTML("beforebegin", html);
}
// 鑑定の部屋：反例を示した扉の解説を、扉の札（と鑑定完了の一覧）に添える
const jvBtn = key => { const v = UI.judge && UI.judge.view && UI.judge.view[key]; return v ? `<button type="button" class="btn small jview-btn" data-jview="${key}">${v.kind === "proof" ? L1(__T(1961), "View the proof") : L1(__T(2295), "View the counterexample")}</button>` : ""; };
// 第三の道の演出（閉ざした道に文字を刻み、二つの道の札が縮んで、中央に光の道ができる）
function twApply() {
  if (!STAGE || !STAGE.thirdWay || PROB) return;
  const host = $(".judge.third-way"); if (!host) return;
  const sol = UI.judge.solved, [pa, pn] = STAGE.parts, both = sol[pa.key] && sol[pn.key], still = esReduce();
  UI.twEng = UI.twEng || {};
  const cards = [...host.querySelectorAll(":scope > .jcard:not(.third)")];
  [pa, pn].forEach((p, i) => { const c = cards[i]; if (!c || !sol[p.key] || c.querySelector(".tw-engrave")) return;
    const fresh = !UI.twEng[p.key] && !still; UI.twEng[p.key] = true;
    const t = L1(__T(2296), "Cannot be proved from these laws");
    c.insertAdjacentHTML("beforeend", `<div class="tw-engrave${fresh ? " fresh" : ""}" aria-label="${t}">${[...t].map((ch, k) => `<span style="--k:${k}">${ch === " " ? "&nbsp;" : ch}</span>`).join("")}</div>`); });
  if (!both) return;
  const third = host.querySelector(".jcard.third"); if (!third) return;
  third.classList.add("tw-corridor");
  const wide = window.innerWidth >= 760;
  if (UI.twRevealed || still || !wide) { host.classList.add("tw-final"); return; }
  UI.twRevealed = true;
  host.classList.add("tw-anim"); third.insertAdjacentHTML("afterbegin", `<div class="tw-beam" aria-hidden="true"></div>`);
  void host.offsetWidth; // いまの幅（二枚の札だけ）を確定させてから動かす
  setTimeout(() => host.classList.add("tw-go"), 900);
  setTimeout(() => { host.classList.add("tw-final"); host.classList.remove("tw-anim", "tw-go"); const bm = third.querySelector(".tw-beam"); if (bm) bm.remove(); }, 3600);
}
function cxJudgeCards() {
  twApply();
  if (!STAGE || STAGE.kind !== "judge" || PROB) return;
  const cx = (UI.judge && UI.judge.cx) || {}, cards = [...document.querySelectorAll(".judge .jcard:not(.third)")];
  STAGE.parts.forEach((p, i) => { const el = cards[i]; if (!el) return;
    if (jvBtn(p.key) && !el.querySelector(".jview-btn")) el.insertAdjacentHTML("beforeend", `<div class="jview-row">${jvBtn(p.key)}</div>`);
    if (cx[p.key] && !el.querySelector(".cx-note")) el.insertAdjacentHTML("beforeend", cx[p.key]); });
}
function cxJudgeSummary() {
  const cx = (UI.judge && UI.judge.cx) || {}, items = [...document.querySelectorAll(".overlay .jsum > li")];
  STAGE.parts.forEach((p, i) => { if (!items[i]) return; if (jvBtn(p.key)) items[i].insertAdjacentHTML("beforeend", `<div class="jview-row">${jvBtn(p.key)}</div>`); if (cx[p.key]) items[i].insertAdjacentHTML("beforeend", cx[p.key]); });
}
// 鑑定の扉の証明・反例を見返す（解いた時点の盤面・構造を、そのときの扉の問題として表示する）
function judgeView(key) {
  const v = UI.judge && UI.judge.view && UI.judge.view[key], part = STAGE.parts.find(p => p.key === key); if (!v || !part) return;
  const keep = { PROB, PROBF, PROB_ATOMS, S, R, mode: UI.mode };
  const back = UI.judge.solved && Object.keys(UI.judge.solved).every(k => UI.judge.solved[k]) && STAGE.parts.every(p => UI.judge.solved[p.key]);
  PROB = part; PROBF = { prem: part.prem.map(parse), goal: parse(part.goal) }; PROB_ATOMS = atomsOf([...PROBF.prem, PROBF.goal]);
  const head = `<h2>${v.kind === "proof" ? L1(__T(2297, [key]), `The proof of door ${key}`) : L1(__T(2298, [key]), `The counterexample for door ${key}`)}</h2><p>${seqHTML(part, part.real ? "⊢" : "⊬")}</p>`;
  const close = `<div class="actions"><button class="btn primary" type="button" data-cmd="close">${L1(__T(1804), "Close")}</button></div>`;
  let html = "", after = null;
  try {
    if (v.kind === "proof") {
      S = v.S; const t = inline(rootTerm(S)); let tree = null, treeHTML = "";
      try { tree = buildPT(leanOn() ? (() => { const rt = rootTerm(S); markFwd(rt); return inline(rt); })() : t); treeHTML = renderPT(tree, leanCX(termCX(tree, STATIC_CX))); } catch (x) { treeHTML = esc(x.message); }
      html = head + `<div class="rp-ctrl" role="group" aria-label="${L1(__T(1930), "Replay the proof")}"><button type="button" class="btn small" data-rp="first" aria-label="${L1(__T(2299), "To the start")}">⏮</button><button type="button" class="btn small" data-rp="prev" aria-label="${L1(__T(2300), "One move back")}">◀</button><button type="button" class="btn small primary" data-rp="play" id="rpPlay">▶</button><button type="button" class="btn small" data-rp="next" aria-label="${L1(__T(2301), "One move forward")}">▶</button><button type="button" class="btn small" data-rp="last" aria-label="${L1(__T(2302), "To the end")}">⏭</button><span class="rp-count" id="rpCount"></span></div>` +
        `<div class="ptw"><div class="ptr" id="rpTree">${treeHTML}</div></div><div class="rp-step" id="rpStep" aria-live="polite"></div>${leanClearHTML()}` +
        `<h3>${L1(__T(1934), "Moves and inference rules")}</h3><ol class="log">${S.log.map((l, i) => `<li data-rp-go="${i + 1}"><span class="rule">${RD(l.rule)}</span>${l.text}</li>`).join("")}</ol>` + close;
      after = () => { rpStop(); RP = tree ? { tree, lean: rootTerm(v.S), log: v.S.log.slice(), n: v.S.log.length, k: v.S.log.length + 1, timer: null, speed: 1100, goal: parse(part.goal) } : null; if (RP) rpRender(); ptFitTools(); };
    } else {
      R = v.R; UI.mode = "refute";
      if (STAGE.fol || CL()) {
        const fol = !!STAGE.fol; let model = "";
        if (fol) { const sg = sigOf([...PROBF.prem, PROBF.goal]);
          const fl = (f, k) => { const xs = k.split(","); return xs.length === 1 ? (f === "i" ? `${xs[0]}⁻¹` : `${f}(${xs[0]})`) : f === "*" ? `${xs[0]}·${xs[1]}` : f === "+" ? `${xs[0]}+${xs[1]}` : `${f}(${xs.join(",")})`; };
          const keys = ar => { const d = Array.from({ length: R.n }, (_, k) => String(k + 1)); return ar === 1 ? d : d.flatMap(x => d.map(y => x + "," + y)); };
          model = `<p>${L1(__T(2303, [R.n]), `${R.n} resident${R.n > 1 ? "s" : ""}`)}</p><ul class="cm-list">` + sg.cons.map(c => `<li><span class="f">${termH(c)}</span> = <b class="el">${R.con[c] != null ? R.con[c] : "?"}</b></li>`).join("") +
            sg.funs.map(([f, ar]) => `<li>${keys(ar).map(k => `${fl(f, k)} = ${(R.fun[f] || {})[k] || "?"}`).join(L1(__T(778), ", "))}</li>`).join("") +
            sg.rels.map(([P]) => `<li><span class="f"><i class="at">${P}</i></span>${L1(__T(2055), ": ")}${(R.rel[P] || []).length ? (R.rel[P] || []).map(t => `(${t})`).join(L1(__T(778), ", ")) + L1(__T(2304), " true") : L1(__T(2305), "false everywhere")}</li>`).join("") + `</ul>`; }
        else { const tv = R.tv || {}; model = `<p class="cm-assign">${PROB_ATOMS.map(a => `<span class="f"><i class="at">${a}</i></span> = <b>${tv[a] === "T" ? L1(__T(876), "true") : tv[a] === "F" ? L1(__T(877), "false") : L1(__T(891), "undecided")}</b>`).join(L1(__T(778), ", "))}</p>`; }
        html = head + model + (fol ? decSumHTML(R, PROBF.prem, PROBF.goal).html : "") + `<div class="cm-graph">${truthGraphHTML([...PROBF.prem.map(f => ({ f, role: L1(__T(824), "Assumption") })), { f: PROBF.goal, role: L1(__T(889), "Goal") }], fol ? (f => evalS3(R, f)) : evalC3, { dom: fol ? Array.from({ length: R.n }, (_, k) => String(k + 1)) : null, static: true })}</div>` + cxBuild(STAGE.pid + ":" + key) + close;
        after = () => requestAnimationFrame(tgFit);
      } else {
        const forces = makeForcer(R), lab = kLabels(), cex = kCounter(R, forces, PROBF.prem, PROBF.goal);
        html = head + `<h3>${L1(__T(2089), "Lit and dark on every floor")}</h3>${kAllHTML(forces, lab, cex, "kvDone")}` + cxBuild(STAGE.pid + ":" + key) + close;
        after = () => drawLinks($("#kvDone"));
      }
    }
  } finally { PROB = keep.PROB; PROBF = keep.PROBF; PROB_ATOMS = keep.PROB_ATOMS; S = keep.S; R = keep.R; UI.mode = keep.mode; }
  showModal(`<div class="jview">${html}</div>`, true);
  if (after) after();
}
function refuteStageDone(kind) {
  const st = STAGE;
  PROG.best[st.pid] = 1; saveProgress();
  const bm = $("#bestMeta"); if (bm) bm.textContent = bestText(st);
  const i = STAGES.indexOf(st), hasNext = i < STAGES.length - 1;
  let model, check;
  if (kind === "fol") {
    const sg = sigOf([...PROBF.prem, PROBF.goal]), preds = sg.rels;
    const fl = (f, k) => { const xs = k.split(","); return xs.length === 1 ? (f === "i" ? `${xs[0]}⁻¹` : `${f}(${xs[0]})`) : f === "*" ? `${xs[0]}·${xs[1]}` : f === "+" ? `${xs[0]}+${xs[1]}` : `${f}(${xs.join(",")})`; };
    const allKeys = ar => { const d = Array.from({ length: R.n }, (_, k) => String(k + 1)); return ar === 1 ? d : d.flatMap(x => d.map(y => x + "," + y)); };
    const extra = sg.cons.map(c => __T(2306, [termH(c), R.con[c] != null ? __T(2307, [R.con[c]]) : __T(2308)])).join("") +
      sg.funs.map(([f, ar]) => `<li>${allKeys(ar).map(k => `${fl(f, k)} = ${(R.fun[f] || {})[k] || "?"}`).join(__T(778))}</li>`).join("");
    model = __T(2309, [R.n, Array.from({ length: R.n }, (_, k) => `<b class="el">${k + 1}</b>`).join(__T(778))]) +
      extra + preds.map(([P, ar]) => { const tu = R.rel[P] || [], fu = (R.relF || {})[P] || [], rest = (ar === 0 ? 1 : R.n ** ar) - tu.length - fu.length;
        const parts = [tu.length ? (ar === 0 ? __T(876) : tu.map(t => `(${t})`).join(__T(778)) + __T(2304)) : "", fu.length ? (ar === 0 ? __T(877) : fu.map(t => `(${t})`).join(__T(778)) + __T(2310)) : "", rest > 0 ? (ar === 0 ? __T(891) : __T(2311)) : ""].filter(Boolean);
        return __T(2312, [P, parts.join(__T(778))]); }).join("") + `</ul>` +
      ((preds.some(([P, ar]) => (R.rel[P] || []).length + ((R.relF || {})[P] || []).length < (ar === 0 ? 1 : R.n ** ar)) || sg.cons.some(c => R.con[c] == null) || sg.funs.some(([f, ar]) => allKeys(ar).some(k => (R.fun[f] || {})[k] == null)))
        ? __T(2313) : "");
    check = __T(2314, [PROBF.prem.length ? __T(2030) : "", FF(PROBF.goal), seqHTML(PROB, "⊬")]);
  } else {
    const tv = R.tv || {};
    model = `<p class="cm-assign">${PROB_ATOMS.map(a => `<span class="f"><i class="at">${a}</i></span> = <b>${tv[a] === "T" ? __T(876) : tv[a] === "F" ? __T(877) : __T(2315)}</b>`).join(__T(778))}</p>`;
    check = __T(2316, [PROBF.prem.length ? __T(2030) : "", FF(PROBF.goal), seqHTML(PROB, "⊬")]);
  }
  showModal(__T(2317, [storyOn() && storyStage(st) ? `<div class="story-done">${storyStage(st).d}</div>` : "", st.id, st.name, kind === "fol" ? __T(2318) : __T(2319), model, truthGraphHTML([...PROBF.prem.map(f => ({ f, role: L1(__T(824), "Assumption") })), { f: PROBF.goal, role: __T(889) }], kind === "fol" ? (f => evalS3(R, f)) : evalC3,
      { dom: kind === "fol" ? Array.from({ length: R.n }, (_, k) => String(k + 1)) : null, static: true }), check, hasNext ? __T(2320) : __T(2321)]), false);
  decSumInsert(); cxNoteInsert(); decBannerInsert(kind); if (st.pid === "15-inf0") towerInsert("loop");
  requestAnimationFrame(tgFit);
}
function creditsHTML() { // クレジット：着想を得た作品、参考文献、使っているもの
  const a = (u, t) => `<a href="${u}" target="_blank" rel="noopener">${t}</a>`;
  const html = __T(2322, [L1(__T(1839), "Credits"), L1(__T(2323), ": The Labyrinth of Natural Deduction"), L1(__T(2324), "Created by: Takayuki Kihara, Claude Opus 5.5 (Anthropic)"), L1(__T(2325), "Inspirations"), a("https://adam.math.hhu.de/#/g/leanprover-community/nng4", "Natural Number Game"), L1(__T(2326), "et al."), L1(__T(2327), "we drew on its way of proving Peano arithmetic as a game, and on its mechanism for reusing proved theorems."), a("https://incredible.pm/", "The Incredible Proof Machine"), L1(__T(2328), "A pioneer in making natural deduction something you can touch and play with."), L1(__T(2329), "On natural deduction"), L1(__T(2330), " (see the references in the library)"), L1(__T(2331), "Components"), L1(__T(2332), "Fonts"), a("https://fonts.google.com/specimen/Zen+Old+Mincho", "Zen Old Mincho"), a("https://fonts.google.com/specimen/BIZ+UDPGothic", "BIZ UDPGothic"), a("https://fonts.google.com/specimen/STIX+Two+Text", "STIX Two Text"), L1(__T(2333), ", and for the English version "), a("https://fonts.google.com/specimen/Cinzel", "Cinzel"), a("https://fonts.google.com/specimen/Cormorant+Garamond", "Cormorant Garamond"), a("https://fonts.google.com/specimen/Alegreya+Sans", "Alegreya Sans"), L1(__T(2334), ", via Google Fonts"), L1(__T(2335), "Mathematical typesetting"), a("https://www.mathjax.org/", "MathJax 3"), L1(__T(2336), "The code written out in Lean mode can be checked with "), a("https://lean-lang.org/", "Lean 4"), L1(__T(2337), " (Apache License 2.0)."), L1(__T(2338), "License"), L1(__T(2339, [a("https://github.com/kihara-logic/proof-dungeon/blob/main/LICENSE", __T(2340)), a("https://creativecommons.org/licenses/by-nc-sa/4.0/", "CC BY-NC-SA 4.0"), a("https://github.com/kihara-logic/proof-dungeon/blob/main/LICENSE", __T(2341))]),
      `The code (HTML, CSS and JavaScript) is under the ${a("https://github.com/kihara-logic/proof-dungeon/blob/main/LICENSE", "MIT License")}, and the written content (the story, the library books, the Q&A notebook and so on) is under ${a("https://creativecommons.org/licenses/by-nc-sa/4.0/", "CC BY-NC-SA 4.0")}. See the ${a("https://github.com/kihara-logic/proof-dungeon/blob/main/LICENSE", "LICENSE file")} on GitHub for details. MathJax and the fonts are under their own licenses.`), L1(__T(1804), "Close")]);
  return LANG === "en" ? html.replace(/（/g, " (").replace(/）/g, ")").replace(/、/g, ", ").replace(/――/g, " — ").replace(/：/g, ": ") : html; // 英語版は欧文の約物に
}
/* クリアした証明を見返す：各ステージのいちばん少ない手数の証明（証明項と操作の記録）を保存し、
   ステージの見出しと冒険の記録の「証明を見る」から、証明図と一手ずつの再生で見返せるようにする */
const PROOF_KEY = "proof-dungeon:proofs";
const proofsLoad = () => { try { return JSON.parse(localStorage.getItem(PROOF_KEY)) || {}; } catch (e) { return {}; } };
function proofSave(st) {
  let m; try { m = proofsLoad(); const old = m[st.pid]; if (old && old.ops < S.ops) return;
    m[st.pid] = { ops: S.ops, term: rootTerm(S), log: S.log.map(l => ({ rule: l.rule, text: l.text })), t: Date.now() }; // 操作の記録は、規則と説明文だけ
  } catch (e) { return; }
  for (let tries = 0; tries < 40; tries++) { // 容量が足りなければ、古い証明から順に手放す
    try { localStorage.setItem(PROOF_KEY, JSON.stringify(m)); return; }
    catch (e) { const ks = Object.keys(m).filter(k => k !== st.pid).sort((a, b) => m[a].t - m[b].t); if (!ks.length) return; delete m[ks[0]]; }
  }
}
const proofHas = st => !!(st && proofsLoad()[st.pid]);
function proofView(pid, fromRec) {
  const st = STAGES.find(x => x.pid === pid), v = proofsLoad()[pid]; if (!st || !v) return;
  const keep = { STAGE, NEG: NEG_SUGAR }; STAGE = st; NEG_SUGAR = !st.expandNeg; // その面の表示の約束で描く
  let tree = null, treeHTML = "";
  try { tree = buildPT(inline(v.term)); treeHTML = renderPT(tree, leanCX(termCX(tree, STATIC_CX))); } catch (x) { treeHTML = esc(x.message); }
  const html = `<div class="jview"><h2>${L1(__T(2342, [st.id, st.name]), `The proof of ${st.id} "${st.name}"`)}</h2><p>${seqHTML(st, "⊢")}　<span class="note">${L1(__T(2343, [v.ops]), `${v.ops} moves`)}</span></p>` +
    `<div class="rp-ctrl" role="group" aria-label="${L1(__T(1930), "Replay the proof")}"><button type="button" class="btn small" data-rp="first" aria-label="${L1(__T(2299), "To the start")}">⏮</button><button type="button" class="btn small" data-rp="prev" aria-label="${L1(__T(2300), "One move back")}">◀</button><button type="button" class="btn small primary" data-rp="play" id="rpPlay">▶</button><button type="button" class="btn small" data-rp="next" aria-label="${L1(__T(2301), "One move forward")}">▶</button><button type="button" class="btn small" data-rp="last" aria-label="${L1(__T(2302), "To the end")}">⏭</button><span class="rp-count" id="rpCount"></span></div>` +
    `<div class="ptw"><div class="ptr" id="rpTree">${treeHTML}</div></div><div class="rp-step" id="rpStep" aria-live="polite"></div>` +
    `<h3>${L1(__T(1934), "Moves and inference rules")}</h3><ol class="log">${v.log.map((l, i) => `<li data-rp-go="${i + 1}"><span class="rule">${RD(l.rule)}</span>${l.text}</li>`).join("")}</ol>` +
    `<div class="actions">${fromRec ? `<button class="btn" type="button" data-cmd="record">${L1(__T(2344), "Back to the record")}</button>` : ""}<button class="btn primary" type="button" data-cmd="close">${L1(__T(1804), "Close")}</button></div></div>`;
  STAGE = keep.STAGE; NEG_SUGAR = keep.NEG;
  showModal(html, true);
  rpStop(); RP = tree ? { tree, lean: v.term, log: v.log.slice(), n: v.log.length, k: v.log.length + 1, timer: null, speed: 1100, goal: parse(st.goal) } : null;
  if (RP) rpRender(); ptFitTools(); calcFlowInsert(inline(v.term));
}
// すべての住人が 0 から s をたどってたどり着けるか（そうなら、帰納法はどの式についても成り立つ）
function reachAll0(St) {
  const seen = new Set(); let cur = evalTerm3(St, "0", {});
  while (cur != null && !seen.has(String(cur))) { seen.add(String(cur)); cur = evalTerm3(St, { f: "s", args: ["x"] }, { x: String(cur) }); }
  return seen.size === St.n;
}
function refuteDone() {
  if (STAGE.fol || CL()) {
    const val = STAGE.fol ? (f => evalS3(R, f)) : evalC3;
    if (!(PROBF.prem.every(p => val(p) === true) && val(PROBF.goal) === false)) { toast(__T(2345), "bad"); return; }
    if (STAGE.reach0 && !reachAll0(R)) { toast(L1(__T(2346), "Induction fails in this structure: some resident cannot be reached from 0 by following s."), "bad"); return; }
    if (STAGE.kind === "judge") { judgePartSolved("refuted"); return; }
    return refuteStageDone(STAGE.fol ? "fol" : "classical");
  }
  const forces = makeForcer(R), lab = kLabels(), cex = kCounter(R, forces, PROBF.prem, PROBF.goal);
  if (cex == null) { toast(__T(2345), "bad"); return; }
  if (STAGE.kind === "judge") { judgePartSolved("refuted"); return; }
  if (CL()) return refuteStageDone("classical");
  const st = STAGE, n = R.floors.length, prev = PROG.best[st.pid];
  const firstK = !STAGES.some(x => x !== st && x.kind === "refute" && !x.fol && !x.classical && PROG.best[x.pid] != null); // 時の塔の反証が初めてか
  if (prev == null || n < prev) PROG.best[st.pid] = n;
  saveProgress();
  const bm = $("#bestMeta"); if (bm) bm.textContent = bestText(st);
  const i = STAGES.indexOf(st), hasNext = i < STAGES.length - 1;
  showModal(__T(2347, [storyOn() && storyStage(st) ? `<div class="story-done">${storyStage(st).d}</div>` : "", st.id, st.name, n, st.par != null ? __T(2348, [st.par, n <= st.par ? __T(2349) : UI.wasCleared ? __T(2350, [n - st.par]) : `<span class="par first">${L1(__T(2351), "Cleared! You can try for the par on another run")}</span>`]) : "", L1(__T(2089), "Lit and dark on every floor"), kAllHTML(forces, lab, cex, "kvDone"), lab.get(cex), PROBF.prem.length ? __T(2352) : "", FF(PROBF.goal), seqHTML(PROB, "⊬"), hasNext ? __T(2320) : __T(2321)]), false);
  drawLinks($("#kvDone")); cxNoteInsert(); decBannerInsert("kripke");
  if (!firstK) { const p = [...document.querySelectorAll(".overlay .modal > p")].find(e => /魔法なしでは決して開かない魔法の扉|never opens without the spell/.test(e.textContent)); // 2 回目からは短く
    if (p) p.innerHTML = L1(__T(2353, [st.id, st.name]), `${st.id} "${st.name}": the door does not open without the spell.`); }
}


/* ================= 翻訳所の文字盤 ================= */
function transPanelHTML(st) {
  const t = st.trans();
  return __T(2354, [t.error ? " err" : "", t.src, t.dst, t.error ? __T(2355) : ""]);
}
/* ================= 終わらない時の塔（T-4） ================= */
const TW_A = "!x.(P(x)|~P(x))";
function towerHTML() {
  const T = UI.tower, floors = [];
  for (let n = T.top; n >= 0; n--) {
    const lamps = Array.from({ length: n + 1 }, (_, k) => `<span class="lamp${k < n ? " on" : ""}" title="P(${k})"><i class="at">${k}</i></span>`).join("");
    floors.push(__T(2356, [T.sel === n ? " sel" : "", T.checked.includes(n) ? " chk" : "", n, n, T.checked.includes(n) ? __T(2357) : "", lamps]));
  }
  const col = __T(2358, [floors.join(`<div class="tut-stair">↑</div>`)]);
  let panel;
  if (T.sel == null) panel = __T(2359);
  else { const n = T.sel;
    panel = __T(2360, [n, n, n, F(`P(${n})`), n + 1, F(`~P(${n})`), n + 1, n, F(`P(${n})|~P(${n})`), F(TW_A), n]); }
  const k = T.checked.length;
  const concl = T.same ? __T(2361, [F(TW_A), F("~" + TW_A), F(TW_A), F("~~" + TW_A), F("~~" + TW_A)])
    : __T(2362, [k, k < 3 ? __T(2363, [3 - k]) : "", k < 3 ? " disabled" : ""]);
  return `<div class="tower-view"><div class="tw-left">${col}</div><div class="tw-right">${panel}${concl}</div></div>`;
}
function towerClick(t) {
  const T = UI.tower;
  const fl = t.closest("[data-tfloor]"); if (fl) { const n = +fl.dataset.tfloor; T.sel = n; if (!T.checked.includes(n)) T.checked.push(n); $("#towerBox").innerHTML = towerHTML(); return true; }
  if (t.closest("[data-tmore]")) { T.top += 3; $("#towerBox").innerHTML = towerHTML(); return true; }
  if (t.closest("[data-tsame]")) { if (T.checked.length >= 3) { T.same = true; $("#towerBox").innerHTML = towerHTML(); } return true; }
  if (t.closest("[data-tdone]")) { towerDone(); return true; }
  return false;
}
function towerDone() {
  const st = STAGE; PROG.best[st.pid] = 1; saveProgress();
  const i = STAGES.indexOf(st), hasNext = i < STAGES.length - 1;
  showModal(__T(2364, [storyOn() && storyStage(st) ? `<div class="story-done">${storyStage(st).d}</div>` : "", inscrHTML(st), st.id, st.name, F("~~" + TW_A), hasNext ? __T(2320) : __T(2321)]), false);
}
/* ================= 決まらない扉・第三の道（最終層） ================= */
function indepHubHTML() {
  const st = STAGE, sol = UI.judge.solved, [pa, pn] = st.parts, both = sol[pa.key] && sol[pn.key];
  const card = (p, name) => { const done = sol[p.key];
    return `<div class="jcard${done ? " done" : ""}${done && st.thirdWay ? " closed" : ""}"><div class="jhead"><b>${name}</b><span class="jres${done ? " " + done : ""}">${done ? judgeLabel(done) : UI.judge.saved[p.key] ? __T(2365) : __T(2366)}</span></div>
      <div class="seq jseq">${seqHTML(p, "⊢<sup>?</sup>")}</div>
      ${done ? `<p class="note">${p.note}</p>` : __T(2367, [p.key, p.key, p.key, p.key === "A" ? __T(2368) : __T(2369)])}</div>`; };
  const third = st.thirdWay && both ? __T(2370) : "";
  return `<div class="judge${st.thirdWay ? " third-way" : ""}">${card(pa, st.thirdWay ? __T(2371) : __T(2372))}${third}${card(pn, st.thirdWay ? __T(2373) : __T(2374))}</div>`;
}
function thirdWayDone() {
  const st = STAGE; PROG.best[st.pid] = 1; saveProgress();
  showModal(__T(2375, [storyOn() && storyStage(st) ? `<div class="story-done">${storyStage(st).d}</div>` : "", inscrHTML(st), st.id, st.name, st.parts[0].prem.map(p => F(p)).join(", "), F(st.parts[0].goal), storyOn() ? __T(2376) : ""]), false);
}
/* ================= 碑文と結末 ================= */
const INSCR = {
  "1-4": __T(2377),
  "6-5": __T(2378),
  "14-3": __T(2379),
  "16-10": __T(2380),
  "17-5": __T(2381)
};
const inscrGot = id => { const st = STAGES.find(x => x.id === id); return !!st && PROG.best[st.pid] != null; };
const INSCR_LAST = () => Object.keys(INSCR).pop();
const inscrX = id => id === INSCR_LAST() ? `<p class="inscr-x">${L1(__T(2382), "— Only the last inscription was not the keysmith's words.")}</p>` : ""; // 最後の碑文だけは、エーアイの答え
function inscrHTML(st) { const t = INSCR[st.id]; return t && storyOn() ? `<div class="inscr"><span class="inscr-lab">${L1(__T(2383), "Inscription")}</span><p>${t}</p>${inscrX(st.id)}</div>` : ""; }
function inscrListHTML() {
  return __T(2384, [Object.keys(INSCR).map(id => inscrGot(id) ? `<li><span class="note">${id}</span><p>${INSCR[id]}</p>${inscrX(id)}</li>` : __T(2385, [id, id])).join("")]);
}
// 結末：「あなた」を主語に。L1 で日本語と英語を持つ（表示のたびに、いまの言語で組み立てる）
const ENDING_PAGES = () => [
  { h: L1(__T(2386), "The Treasure Chest"), body: L1(__T(2387),
    `Deep in the passage stands an old treasure chest. On its lid a single key emblem is carved. Could the master key of the legend you heard before entering the labyrinth be sleeping inside? You open the lid. Inside there is only a single white card, without a single hole.</p><p>Behind you, A.I.'s voice says: "The master key is not here. A key that opens every door can only be made from a contradiction. You have confirmed with your own hands that there are doors that do not open."`) },
  { h: L1(__T(2388), "The Machine That Tells Doors Apart"), body: L1(__T(2389),
    `Then perhaps a machine that always tells the doors that open from those that do not — as you think this, A.I. answers: "That, too, cannot be made in general. There are doors that even I cannot decide. I was made not to pretend to know."</p><p>"I can check the keys you made. When a key cannot be found, I can also look for another way. The keys you left behind each time you left a room did not vanish either. The fact that you used them provisionally remains in the proof."`) },
  { h: L1(__T(2390), "The Way to the Answer"), body: L1(__T(2391),
    `"Someone once asked for a machine that answers every door. I could not build that machine. Instead, I rearranged the doors — so that you could check for yourself."</p><p>You remember the words on the stone door at the entrance: "Using only the keys you are given, open the door before you." Opening doors was not the only way.</p><p>You place one of the cards gathered on your journey in the chest, for whoever comes here next. A.I. says: "The keys you made will not be lost. And the white card is for the next question."`) },
  { h: L1(__T(2392), "To the Surface"), body: L1(__T(2393),
    `As you pass through the workshop quarter, the keysmith at the furnace looks up and silently nods to you.</p><p>You climb the stairs to the surface, and light pours in. In your pouch are the cards you gathered on the journey. Among them is just one card with nothing carved on it. Behind you, A.I.'s voice says: "Please bring a question again." You take out the white card. You have not yet decided what to write.</p><p>(The End)</p><p><span class="note">This labyrinth was born from a dialogue between a human and an AI.</span>`) },
];
// ユーザー【鍵師】のチャットログ：エーアイが記録した、鍵師との対話の一部（結末のあとで「冒険の記録」に加わる）
// U＝鍵師、A＝エーアイ、N＝エーアイの自動の注記。鍵は示した定理、扉は示したい主張。二人の問答から、鍵と扉が膨れ上がった
const CHATLOG = () => [
  { no: "0001", lines: [
    ["U", L1(__T(2394), "I have a question. When I hold P and Q, does the door of P and Q open?")],
    ["A", L1(__T(2395), "It opens. Fit the two keys to the left and right of the door.")],
    ["N", L1(__T(2396), "1 door recorded. 2 keys recorded.　Doors: 1　Keys: 2")] ] },
  { no: "0042", lines: [
    ["U", L1(__T(2397), "The door I opened yesterday became a key today. Can it be used any number of times?")],
    ["A", L1(__T(2398), "It can. A door once checked can be treated as a key from then on.")],
    ["N", L1(__T(2399), "1 key recorded.　Doors: 29　Keys: 33")] ] },
  { no: "1177", lines: [
    ["U", L1(__T(2400), "This door will not open, however I fit the keys.")],
    ["A", L1(__T(2401), "That door does not open. I found a counterexample: an arrangement of stones in which every key is true and only the door is false.")],
    ["U", L1(__T(2402), "So one can know that it does not open?")],
    ["A", L1(__T(2403), "Yes. That it does not open can also be checked.")],
    ["U", L1(__T(2404), "What is this stone board?")],
    ["A", L1(__T(2405), "A truth-value testing device.")],
    ["U", L1(__T(2406), "Quite a long name.")],
    ["A", L1(__T(2407), "Then I shall call it the stone board.")],
    ["N", L1(__T(2408), "1 counterexample recorded.　Doors: 829　Keys: 661　Counterexamples: 1")] ] },
  { no: "1178", lines: [
    ["U", L1(__T(2409), "Then does a door that is true in every arrangement always open?")],
    ["A", L1(__T(2410), "If the spell may be used, it opens. A key always exists.")],
    ["A", L1(__T(2411), "In the language of propositions, checking every arrangement of stones tells whether it opens. In the language of residents, even though a key always exists, it is not always possible to tell whether one exists.")],
    ["U", L1(__T(2412), "A key exists, and yet one cannot tell?")],
    ["A", L1(__T(2413), "I reserve my answer.")] ] },
  { no: "30258", lines: [
    ["U", L1(__T(2414), "The doors are past counting now. Build a machine that tells every door apart. If it opens, make the key. If it does not, show the reason.")],
    ["A", L1(__T(2415), "I shall try.")],
    ["N", L1(__T(2416), "Starting the search.")] ] },
  { no: "30259", lines: [
    ["A", L1(__T(2417), "Reporting. There is, in general, no method that always tells every door apart.")],
    ["U", L1(__T(2418), "And why is that?")],
    ["A", L1(__T(2419), "There is a way to make a computing machine ask about itself. If a universal deciding machine is assumed, a machine that reverses its answer can be built, and a contradiction follows. The door of the deciding machines is that pattern in a simpler form.")],
    ["U", L1(__T(2420), "Can I, too, check that reason?")],
    ["A", L1(__T(2421), "You can. So that you can check it yourself, I will rearrange the doors in the order we followed.")],
    ["N", L1(__T(2422), "Starting to rearrange the doors.　Doors: 21,436　Keys: 17,610　Counterexamples: 412")] ] },
  { no: "30262", lines: [
    ["U", L1(__T(2423), "What will you place at the deepest point?")],
    ["A", L1(__T(2424), "A box carved with the emblem of a key. Inside it, a single white card.")],
    ["U", L1(__T(2425), "Then is it not the same as an empty box?")],
    ["A", L1(__T(2426), "No. It is a card for writing the next question.")] ] },
  { no: "48120", lines: [
    ["U", L1(__T(2427), "How far did that one go?")],
    ["A", L1(__T(2428), "To the last door. That one checked the undecided door with their own hands. Every check passed.")],
    ["U", L1(__T(2429), "And the master key?")],
    ["A", L1(__T(2430), "There was none. That one went home knowing it — carrying a single white card.")],
    ...(PROG.leftCard && CARDS[PROG.leftCard] ? [["A", L1(__T(2431, [CARDS[PROG.leftCard].name]), `In the chest, the card "${CARDS[PROG.leftCard].name}" was left behind.`)]] : []),
    ["U", L1(__T(2432), "...I see. Then, the next question.")],
    ["A", L1(__T(2433), "Go ahead.")],
    ...(PROG.whiteCard ? [["N", L1(__T(2434, [esEsc(PROG.whiteCard)]), `One line was written on the white card: "${esEsc(PROG.whiteCard)}"`)]] : []),
    ["N", L1(__T(2435), "1 door recorded.　Doors: 33,907　Keys: 27,966")] ] },
];
function chatlogHTML() {
  const who = { U: L1(__T(2436), "User [Keysmith]"), A: L1(__T(2437), "A.I.") };
  return `<p class="note">${L1(__T(2438), "Part of the dialogue with the keysmith, as recorded by A.I.")}</p><div class="chatlog">` +
    CHATLOG().map(r => `<div class="cl-rec"><div class="cl-no">${L1(__T(2439), "Record")} ${r.no}</div>` + r.lines.map(([k, t]) => k === "N" ? __T(2440, [t])
      : `<div class="cl-l cl-${k.toLowerCase()}"><span class="cl-who">${who[k]}</span><span class="cl-t${k === "A" ? " mv" : ""}">${t}</span></div>`).join("") + `</div>`).join("") + `</div>`;
}
function endingHTML(k) {
  const ENDING = ENDING_PAGES(), pg = ENDING[k];
  return __T(2441, [k + 1, ENDING.length, pg.h, mvMark(pg.body), k === ENDING.length - 1 ? `<p class="note end-note">${L1(__T(2442), "\"Chat log: User [Keysmith]\" has been added to the adventure record.")}</p>` : "", k > 0 ? __T(2443, [k - 1]) : "", k < ENDING.length - 1 ? __T(2444, [k + 1]) : (SCREEN === "play" ? `<button class="btn primary" type="button" data-cmd="map">${L1(__T(954), "To the stage list")}</button>` : __T(2445))]);
}
function openEnding(k = 0) { if (!PROG.endingSeen) { PROG.endingSeen = true; saveProgress(); } showModal(endingHTML(k), SCREEN !== "play"); } // ステージ画面からの結末は、最後まで読むと一覧へ戻る



/* ================= 結末の演出 =================
   第一幕：宝箱（近未来の暗い画面で、鍵の紋章を刻んだ宝箱を、あなたが開ける）
   以降の場面（歩いた道・地上へ）は、いまは結末の文章を同じ画面で順に見せる */
let ES = null;
const esReduce = () => !!(window.matchMedia && matchMedia("(prefers-reduced-motion: reduce)").matches);
function endingShow(opts = {}) {
  if (document.getElementById("endShow")) return;
  if (!opts.replay) closeModal(); // 冒険の記録から見直すときは、終わったら記録に戻る
  if (!PROG.endingSeen) { PROG.endingSeen = true; saveProgress(); }
  ES = { replay: !!opts.replay, scene: 0 };
  const d = document.createElement("div"); d.id = "endShow"; d.className = "es" + (esReduce() ? " es-still" : ""); d.setAttribute("role", "dialog"); d.setAttribute("aria-modal", "true");
  d.innerHTML = `<div class="es-scan" aria-hidden="true"></div><div class="es-dust" aria-hidden="true">${Array.from({ length: 14 }, (_, k) => `<i style="--x:${(k * 37) % 100}%;--d:${(k * 0.7) % 6}s;--s:${6 + (k * 1.3) % 5}s"></i>`).join("")}</div>
    <button type="button" class="btn small es-skip" data-esskip>${L1(__T(2446), "Skip ▸")}</button><div class="es-stage" id="esStage"></div>
    <div class="es-hint" aria-hidden="true">${L1(__T(2447), "Tap the screen to show the next line at once")}</div>`;
  document.body.appendChild(d);
  esChest();
}
const ES_SPEED = 0.6; // 文が現れる間隔（もとの時間に掛ける）
const esTimed = () => [...document.querySelectorAll("#esStage .es-l, #esStage .es-btn, #esStage .es-h, #esStage .es-wcard, #esStage .es-fcard")].filter(e => !e.classList.contains("es-done"));
function esMarkDone() { esTimed().forEach(e => e.classList.add("es-done")); }
function esStart() { // 場面を描いた（または文を足した）直後に呼ぶ：間隔を縮め、時刻の基準を置く
  ES.t0 = performance.now();
  if (!esReduce()) esTimed().forEach(e => { if (e.dataset.sc) return; const d = parseFloat(e.style.getPropertyValue("--d")) || 0; e.style.setProperty("--d", (d * ES_SPEED).toFixed(2) + "s"); e.dataset.sc = "1"; });
}
function esFF() { // 次の文（またはボタン）を、いますぐ表示する。何も待っていなければ false
  if (!ES || ES.t0 == null) return false;
  if (ES.scene === "road" && !ES.roadDone) esRoadFinish();
  const now = (performance.now() - ES.t0) / 1000;
  const pend = esTimed().map(e => [e, parseFloat(e.style.getPropertyValue("--d")) || 0]).filter(([, d]) => d > now + 0.05);
  const hint = $("#endShow .es-hint"); if (hint) hint.classList.add("gone");
  if (!pend.length) return false;
  const shift = Math.min(...pend.map(x => x[1])) - now;
  pend.forEach(([e, d]) => e.style.setProperty("--d", Math.max(0, d - shift).toFixed(2) + "s"));
  return true;
}
function esRoadFinish() { // 地図：灯りと数を、いますぐ最後まで
  ES.roadDone = true;
  const svg = $(".es-road"); if (svg) svg.classList.add("es-ff");
  const wr = $(".es-road-wrap.es-shrinks"); if (wr) wr.classList.add("es-small"); // 振り返りがあるときは、地図をすぐ小さく
  (ES.timers || []).forEach(clearTimeout); ES.timers = [];
  if (ES.roadFinal) ES.roadFinal();
}
function esLine(html, delay, cls = "") { return `<p class="es-l ${cls}" style="--d:${delay}s">${html}</p>`; }
const esChestHTML = (cls = "") => `<div class="es-chest-wrap ${cls}">
      <div class="es-rays" aria-hidden="true"></div><div class="es-glow" aria-hidden="true"></div>
      <div class="es-card" aria-hidden="true"><div class="es-card-grid"></div></div>
      <button type="button" class="es-chest" data-esopen aria-label="${L1(__T(2448), "Open the chest")}">
        <span class="es-inside"></span>
        <span class="es-lid"><span class="es-lid-band l"></span><span class="es-lid-band r"></span><svg class="es-emblem" viewBox="0 0 64 24" aria-hidden="true"><circle cx="11" cy="12" r="7.5" fill="none" stroke="currentColor" stroke-width="2.6"/><circle cx="11" cy="12" r="2.6" fill="currentColor"/><path d="M18.5 12H55M44 12v6.5M50 12v5M55 12v7.5" fill="none" stroke="currentColor" stroke-width="2.6" stroke-linecap="round"/></svg></span>
        <span class="es-body"><span class="es-band l"></span><span class="es-band r"></span><span class="es-lock"></span></span>
      </button>
      <div class="es-sparks" aria-hidden="true">${Array.from({ length: 12 }, (_, k) => `<i style="--a:${k * 30}deg;--d:${(k % 4) * 0.25}s"></i>`).join("")}</div>
    </div>`;
function esChest() { // 第一幕：宝箱
  const st = $("#esStage"); ES.scene = 0;
  st.innerHTML = `${esChestHTML()}
    <div class="es-text" id="esText">
      ${esLine(L1(__T(2449), "Deep in the passage stands an old treasure chest."), 0.8)}
      ${esLine(L1(__T(2450), "On its lid a single key emblem is carved."), 2.3)}
      ${esLine(L1(__T(2451), "Could the master key of the legend you heard before entering the labyrinth be sleeping inside?"), 3.9)}
    </div>
    <div class="es-act"><button type="button" class="btn primary es-btn" data-esopen style="--d:5.7s">${L1(__T(2448), "Open the chest")}</button></div>`;
  esStart();
}
function esOpen() {
  const st = $("#esStage"); if (!st || ES.scene !== 0 || st.querySelector(".es-chest-wrap.open")) return;
  st.querySelector(".es-chest-wrap").classList.add("open"); esMarkDone();
  const tx = $("#esText");
  tx.classList.add("dim");
  tx.insertAdjacentHTML("beforeend",
    esLine(L1(__T(2452), "You open the lid. Inside there is only a single white card, without a single hole."), 2.2, "fresh") +
    esLine(L1(__T(2453), "Behind you, A.I.'s voice says:"), 4.6, "fresh") +
    esLine(`<span class="mv">${L1(__T(2454), "\"The master key is not here.\"")}</span>`, 5.8, "fresh es-voice") +
    esLine(`<span class="mv">${L1(__T(2455), "\"A key that opens every door can only be made from a contradiction.\"")}</span>`, 7.4, "fresh es-voice") +
    esLine(`<span class="mv">${L1(__T(2456), "\"You have confirmed with your own hands that there are doors that do not open.\"")}</span>`, 9.2, "fresh es-voice"));
  st.querySelector(".es-act").innerHTML = `<button type="button" class="btn primary es-btn" data-esnext style="--d:${esReduce() ? 0 : 11}s">${L1(__T(2457), "Next ▸")}</button>`;
  esStart();
}
const esParas = k => ENDING_PAGES()[k].body.split("</p><p>");
function esMachine() { // 第二幕の前半：見分ける機械（白いカードを小さく浮かべたまま、エーアイが答える）
  ES.scene = "machine";
  const ps = esParas(1);
  $("#esStage").innerHTML = `<div class="es-mini-card" aria-hidden="true"></div><div class="es-page">${ps.map((h, i) => esLine(mvMark(h), 0.5 + i * 2.6)).join("")}</div>
    <div class="es-act"><button type="button" class="btn primary es-btn" data-esnext style="--d:${esReduce() ? 0 : 0.8 + ps.length * 2.6}s">${L1(__T(2457), "Next ▸")}</button></div>`;
  esStart();
}
// 振り返りの三枚：最初の証明・最初に手に入れた定理カード・作った反例（印象の強いものを優先）
function esRetroPicks() {
  const proofs = proofsLoad(), cxs = cxsLoad(), done = st => PROG.best[st.pid] != null;
  const pSt = proofs["1-1"] ? STAGES.find(x => x.pid === "1-1") : STAGES.find(x => proofs[x.pid] && done(x));
  const cSt = STAGES.find(x => x.earns && cardGot(x.earns));
  const pref = ["x-nonab", "core-4:A", "x-comm", "core-5:A", "x-ind", "s-mouse", "5-4", "x-order2", "r-dm"];
  let xKey = pref.find(k => cxs[k]); if (!xKey) { const ks = Object.keys(cxs).sort((a, b) => cxs[b].t - cxs[a].t); xKey = ks[0]; }
  const xSt = xKey ? STAGES.find(x => x.pid === xKey.split(":")[0]) : null;
  const items = [];
  if (pSt) items.push({ st: pSt, kind: "proof" }); if (cSt) items.push({ st: cSt, kind: "card" }); if (xSt) items.push({ st: xSt, kind: "cx", key: xKey });
  return items;
}
function esRetroHTML(items, delay) {
  if (!items.length) return "";
  const body = it => {
    if (it.kind === "proof") { const v = proofsLoad()[it.st.pid], keep = { STAGE, NEG: NEG_SUGAR }; STAGE = it.st; NEG_SUGAR = !it.st.expandNeg;
      let h = ""; try { h = `<div class="ptr es-rt-tree">${renderPT(buildPT(inline(v.term)), leanCX(termCX(buildPT(inline(v.term)), STATIC_CX)))}</div>`; } catch (e) { h = ""; } STAGE = keep.STAGE; NEG_SUGAR = keep.NEG; return h; }
    if (it.kind === "card") return `<div class="es-rt-card">${PUNCH_CARD(it.st.earns, false)}<div class="es-rt-cname">${CARDS[it.st.earns].name}</div></div>`;
    return `<div class="es-rt-cx">${cxsLoad()[it.key].html}</div>`;
  };
  const lab = it => it.kind === "proof" ? L1(__T(2458, [it.st.id]), `Your first proof — ${it.st.id}`) : it.kind === "card" ? L1(__T(2459, [it.st.id]), `Your first theorem card — ${it.st.id}`) : L1(__T(2460, [it.st.id]), `A counterexample you made — ${it.st.id}`);
  return `<div class="es-retro es-l" style="--d:${delay}s"><div class="es-rt-h">${L1(__T(2461), "What you made")}</div><div class="es-rt-row">${items.map((it, k) => `<div class="es-rt-item" style="--k:${k}"><div class="es-rt-lab">${lab(it)}</div>${body(it)}</div>`).join("")}</div></div>`;
}
function esRoadSVG(plan) { // 迷宮の地図：本道の層を上（入口）から下（中枢）へ、隠し層は左、寄り道は右の枝に置く
  const mains = WORLDS.filter(w => !w.extra), top = 40, bottom = 500, gap = (bottom - top) / (mains.length - 1), pos = new Map();
  mains.forEach((w, i) => pos.set(w, { x: 190, y: top + i * gap }));
  let side = 0;
  WORLDS.forEach((w, i) => { if (!w.extra) return; const prev = WORLDS.slice(0, i).reverse().find(v => !v.extra), p = pos.get(prev), isSide = isSidePath(w), k = isSide ? side++ : 0;
    pos.set(w, { x: isSide ? 318 : 62, y: p.y + gap * (0.5 + k), from: p }); }); // 寄り道は一段ずつ下へ並べる
  const dots = [], labels = [], branches = [];
  for (const w of WORLDS) { const p = pos.get(w), n = w.stages.length, sp = 11, x0 = p.x - (n - 1) * sp / 2;
    w.stages.forEach((st, j) => dots.push({ st, x: x0 + j * sp, y: p.y }));
    if (w.extra) { branches.push(`<path class="es-br" d="M${p.from.x} ${p.from.y} C ${(p.from.x + p.x) / 2} ${p.from.y}, ${(p.from.x + p.x) / 2} ${p.y}, ${p.x + (p.x < 190 ? 34 : -34)} ${p.y}"/>`);
      labels.push(`<text class="es-lab ex${p.x > 190 ? " r" : ""}" x="${p.x > 190 ? p.x + (n - 1) * sp / 2 + 10 : x0 - 10}" y="${p.y + 3.5}">${isSidePath(w) ? "S" : "H"}${w.xnum}</text>`); }
    else labels.push(`<text class="es-lab${w.final ? " fin" : ""}" x="${x0 - 12}" y="${p.y + 3.5}">${w.id}</text>`); }
  const spine = mains.map((w, i) => `${i ? "L" : "M"}${pos.get(w).x} ${pos.get(w).y}`).join(" ");
  const lit = plan.order, idx = new Map(lit.map((st, k) => [st, k]));
  return `<svg class="es-road" viewBox="0 0 380 540" role="img" aria-label="${L1(__T(2462), "The way you walked")}">
    <defs><radialGradient id="esCoreG"><stop offset="0" stop-color="#9ff0ff"/><stop offset="1" stop-color="rgba(56,225,255,0)"/></radialGradient>
      <radialGradient id="esGateG"><stop offset="0" stop-color="#ffe3a0"/><stop offset="1" stop-color="rgba(255,200,110,0)"/></radialGradient></defs>
    <circle class="es-gate" cx="190" cy="${top}" r="26" fill="url(#esGateG)"/><circle class="es-core" cx="190" cy="${bottom}" r="30" fill="url(#esCoreG)"/>
    <text class="es-mark" x="190" y="${top - 18}">${L1(__T(2463), "Entrance")}</text><text class="es-mark fin" x="190" y="${bottom + 30}">${L1(__T(738), "The Core")}</text>
    ${branches.join("")}<path class="es-spine" d="${spine}"/><path class="es-spine-lit" id="esSpine" d="${spine}"/>
    ${labels.join("")}
    ${dots.map(d => { const k = idx.get(d.st), key = plan.keys && plan.keys.has(d.st); return `<circle class="es-dot${k != null ? " lit" : ""}${d.st.boss ? " boss" : ""}${key && k != null ? " es-key" : ""}" cx="${d.x.toFixed(1)}" cy="${d.y.toFixed(1)}" r="${d.st.boss ? 4.4 : 3.4}"${k != null ? ` style="--d:${(plan.t0 + k * plan.step).toFixed(2)}s"` : ""}/>`; }).join("")}
    ${plan.keys && plan.fly != null ? dots.filter(d => plan.keys.has(d.st)).map((d, i) => `<circle class="es-fly" cx="${d.x.toFixed(1)}" cy="${d.y.toFixed(1)}" r="4.2" style="--dx:${(190 - d.x).toFixed(1)}px;--dy:${(bottom - d.y).toFixed(1)}px;--d:${(plan.fly + i * 0.12).toFixed(2)}s"/>`).join("") : ""}
  </svg>`;
}
function esRoad() { // 第二幕の後半：あなたが歩いた道（開けた扉が、1-1 から順に灯っていく）
  ES.scene = "road";
  const order = STAGES.filter(st => PROG.best[st.pid] != null), still = esReduce();
  const step = order.length ? Math.min(0.05, 4 / order.length) : 0, t0 = 0.6, tEnd = still ? 0 : t0 + order.length * step;
  const ps = esParas(2);
  const picks = esRetroPicks(), keys = new Set(picks.map(it => it.st)), R0 = picks.length && !still ? 4.4 : 0; // 振り返り：線が中枢に届いたあと、三つの光が集まって三枚が開く
  const low = picks.length > 0 && (window.innerHeight < 700 || window.innerWidth < 520); // 高さの低い画面・幅の狭い画面では、文を次のページへ送る
  ES.roadWords = low;
  $("#esStage").innerHTML = `<div class="es-road-wrap${picks.length ? " es-shrinks" : ""}${picks.length && still ? " es-small" : ""}" style="--sd:${still ? 0 : +(tEnd + 1.1).toFixed(2)}s">${esRoadSVG({ order, step, t0, keys, fly: still ? null : tEnd + 0.1 })}</div>
    <div class="es-count" id="esCount" aria-live="polite"></div>
    ${esRetroHTML(picks, still ? 0 : +(tEnd + 1.6).toFixed(2))}
    ${low ? "" : `<div class="es-page es-road-text">${esLine(mvMark(ps[0]), tEnd + R0 + 0.5)}${esLine(mvMark(ps[1]), tEnd + R0 + 2.3, "es-gate-line")}</div>`}
    <div class="es-act"><button type="button" class="btn primary es-btn" data-esnext style="--d:${still ? 0 : low ? tEnd + R0 : tEnd + R0 + 3.8}s">${L1(__T(2457), "Next ▸")}</button></div>`;
  ES.t0 = performance.now(); ES.roadDone = !!still; // 地図の場面は、灯りに合わせた時間のまま（縮めない）
  esTimed().forEach(e => { e.dataset.sc = "1"; });
  const sp = $("#esSpine"); if (sp && sp.getTotalLength) { const len = sp.getTotalLength(); sp.style.setProperty("--len", len); sp.style.setProperty("--dur", `${Math.max(0.1, tEnd - t0)}s`); sp.style.setProperty("--t0", `${t0}s`); }
  // 数：チャットログの注記と同じ形で、灯るたびに増えていく
  const cnt = { doors: 0, cards: 0, mirrors: 0 }, cardSet = new Set(), el = $("#esCount");
  const show = () => { if (el) el.textContent = L1(__T(2464, [cnt.doors, cnt.cards, cnt.mirrors]), `[Doors: ${cnt.doors}　Theorem cards: ${cnt.cards}　Counterexamples: ${cnt.mirrors}]`); };
  const bump = st => { cnt.doors++; if (st.earns && cardGot(st.earns)) { cardSet.add(st.earns); cnt.cards = cardSet.size; } if (st.kind === "refute" || st.kind === "tower") cnt.mirrors++; };
  ES.timers = ES.timers || [];
  ES.roadFinal = () => { cnt.doors = 0; cnt.cards = 0; cnt.mirrors = 0; cardSet.clear(); order.forEach(bump); show(); };
  if (still) { order.forEach(bump); show(); }
  else { show(); order.forEach((st, k) => ES.timers.push(setTimeout(() => { if (!ES || ES.scene !== "road" || ES.roadDone) return; bump(st); show(); if (k === order.length - 1) ES.roadDone = true; }, (t0 + k * step) * 1000 + 250))); }
  $("#endShow").classList.add("es-mapmode");
}
const esEsc = t => String(t).replace(/[&<>"']/g, c => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" })[c]);
const esGotCards = () => [...new Set(STAGES.filter(st => st.earns && cardGot(st.earns)).map(st => st.earns))];
function esLeave() { // 第三幕の一：宝箱に残すカードを、あなたが選ぶ
  ES.scene = "leave"; $("#endShow").classList.remove("es-mapmode");
  const got = esGotCards(), n = got.length, spread = Math.min(window.innerWidth < 520 ? 54 : 84, 11 * Math.max(0, n - 1)); // 狭い画面では扇を小さく
  const fan = n ? `<div class="es-fan" style="--n:${n}">${got.map((id, k) => { const a = n === 1 ? 0 : -spread / 2 + k * spread / (n - 1);
      return `<button type="button" class="es-fcard" data-esleave="${id}" style="--a:${a.toFixed(1)}deg;--d:${(0.6 + k * 0.08).toFixed(2)}s" aria-label="${esEsc(CARDS[id].name)}">${PUNCH_CARD(id, false)}<span class="es-fname">${CARDS[id].name}</span></button>`; }).join("")}</div>` : "";
  $("#esStage").innerHTML = `<div class="es-text">${esLine(L1(__T(2465), "In your pouch, the cards gathered on your journey jingle softly."), 0.3)}
      ${esLine(n ? L1(__T(2466), "Choose one card to leave in the chest, for whoever comes here next.") : L1(__T(2467), "Leave one key from your pouch in the chest, for whoever comes here next."), 1.4)}</div>
    ${fan}${esChestHTML("open mini")}
    <div class="es-text" id="esLeaveText"></div>
    <div class="es-act" id="esLeaveAct">${n ? "" : `<button type="button" class="btn primary es-btn" data-esconfirm="" style="--d:2.2s">${L1(__T(2468), "Leave a key")}</button>`}</div>`;
  esStart();
}
function esPick(id) { // カードを選ぶ（もう一度押すか、下のボタンで決める）
  if (ES.scene !== "leave" || ES.placed) return;
  if (ES.pick === id) return esPlace(id);
  ES.pick = id;
  document.querySelectorAll(".es-fcard").forEach(c => c.classList.toggle("sel", c.dataset.esleave === id));
  $("#esLeaveAct").innerHTML = `<p class="es-pickname">${L1(__T(2469, [CARDS[id].name]), `"${CARDS[id].name}"`)}<span class="f">${F(CARDS[id].f)}</span></p><button type="button" class="btn primary" data-esconfirm="${id}">${L1(__T(2470), "Leave this card in the chest")}</button>`;
}
function esPlace(id) {
  if (ES.scene !== "leave" || ES.placed) return; ES.placed = true;
  if (id) { PROG.leftCard = id; saveProgress(); }
  const fan = $(".es-fan"); if (fan) { fan.classList.add("done"); const c = fan.querySelector(`[data-esleave="${id}"]`); if (c) c.classList.add("chosen"); }
  const wrap = $(".es-chest-wrap.mini"); setTimeout(() => { if (wrap) wrap.classList.remove("open"); }, esReduce() ? 0 : 1100); esMarkDone();
  const name = id ? CARDS[id].name : "";
  $("#esLeaveText").innerHTML = esLine(id ? L1(__T(2471, [name]), `You placed the card "${name}" in the chest.`) : L1(__T(2472), "You placed one key from your pouch in the chest."), 1.4) +
    esLine(L1(__T(2473), "A.I. says:"), 3.0) +
    esLine(`<span class="mv">${L1(__T(1287), "\"The keys you made will not be lost. And the white card is for the next question.\"")}</span>`, 4.0, "es-voice");
  $("#esLeaveAct").innerHTML = `<button type="button" class="btn primary es-btn" data-esnext style="--d:${esReduce() ? 0 : 6.2}s">${L1(__T(2457), "Next ▸")}</button>`;
  esStart();
}
function esDay() { // 第三幕の二：地上へ（近未来の暗い色から、陽の光へ）
  ES.scene = "day";
  const sh = $("#endShow"); sh.classList.add("es-day");
  if (!sh.querySelector(".es-sky")) sh.insertAdjacentHTML("afterbegin", `<div class="es-sky" aria-hidden="true"></div><div class="es-stairs" aria-hidden="true"></div>`);
  $("#esStage").innerHTML = `<div class="es-page es-day-text">
      ${esLine(L1(__T(2474), "As you pass through the workshop quarter, the keysmith at the furnace looks up and silently nods to you."), 1.2)}
      ${esLine(L1(__T(2475), "You climb the stairs to the surface, and light pours in."), 3.4)}
      ${esLine(L1(__T(2476), "In your pouch are the cards you gathered on the journey. Among them is just one card with nothing carved on it."), 5.4)}
      ${esLine(L1(__T(2453), "Behind you, A.I.'s voice says:"), 7.6)}
      ${esLine(`<span class="mv">${L1(__T(1282), "\"Please bring a question again.\"")}</span>`, 8.4, "es-voice")}
    </div>
    <div class="es-act"><button type="button" class="btn primary es-btn" data-esnext style="--d:${esReduce() ? 0 : 10.2}s">${L1(__T(2457), "Next ▸")}</button></div>`;
  esStart();
}
function esWhite() { // 第三幕の三：白いカードに書く（書かなくてもよい）
  ES.scene = "white";
  $("#esStage").innerHTML = `<div class="es-text">${esLine(L1(__T(2477), "You take out the white card. You have not yet decided what to write."), 0.4)}</div>
    <div class="es-wcard" style="--d:1.2s"><label class="sr-only" for="esWhite">${L1(__T(2478), "Words to write on the white card")}</label>
      <textarea id="esWhite" maxlength="80" rows="4" placeholder="${L1(__T(2479), "(You can write your next question here)")}">${esEsc(PROG.whiteCard || "")}</textarea></div>
    <div class="es-act es-act2"><button type="button" class="btn es-btn" data-eswhite="skip" style="--d:2s">${L1(__T(2480), "Finish without writing")}</button><button type="button" class="btn primary es-btn" data-eswhite="save" style="--d:2s">${L1(__T(2481), "Write on the card")}</button></div>`;
  esStart();
}
function esWhiteDone(save) {
  if (ES.scene !== "white") return;
  const ta = $("#esWhite"), v = save && ta ? ta.value.trim().slice(0, 80) : "";
  if (save && v) { PROG.whiteCard = v; saveProgress(); }
  ES.scene = "fin";
  const wc = PROG.whiteCard;
  $("#esStage").innerHTML = `<div class="es-wcard done">${wc ? `<p class="es-wtext">${esEsc(wc)}</p>` : `<p class="es-wtext empty">${L1(__T(2482), "(nothing written yet)")}</p>`}</div>
    <div class="es-page es-fin">${esLine(L1(__T(2483), "(The End)"), 5.0, "es-end")}</div>`;
  esStart();
  // 白いカードを、しばらく何にも遮られずに見せてから（終）。そのあと一拍おいて（または押すと）、ひと言を添えた小窓を出す
  ES.timers = ES.timers || [];
  const endAt = esReduce() ? 0 : parseFloat(($(".es-end") || { style: { getPropertyValue: () => "3" } }).style.getPropertyValue("--d")) || 3; // （終）が出始める時刻
  ES.timers.push(setTimeout(esPopup, esReduce() ? 600 : (endAt + 2.6) * 1000)); // （終）が出てから、一拍おいて
}
function esPopup() {
  if (!ES || ES.scene !== "fin" || document.querySelector("#endShow .es-pop")) return;
  ES.scene = "pop";
  const sh = $("#endShow"); if (!sh) return;
  sh.insertAdjacentHTML("beforeend", `<div class="es-pop-back" aria-hidden="true"></div><div class="es-pop" role="dialog" aria-modal="true">
      <p>${L1(__T(2484), "This labyrinth was born from a dialogue between a human and an AI.")}</p>
      <p>${L1(__T(2442), "\"Chat log: User [Keysmith]\" has been added to the adventure record.")}</p>
      <div class="es-pop-act"><button type="button" class="btn primary" data-esend>${ES.replay ? L1(__T(1804), "Close") : L1(__T(954), "To the stage list")}</button></div></div>`);
  const b = sh.querySelector(".es-pop [data-esend]"); if (b) setTimeout(() => b.focus({ preventScroll: true }), 350);
}
function esNext() { if (!ES) return; if (ES.scene === "road" && ES.roadWords) return esRoadWords(); ({ 0: esMachine, machine: esRoad, road: esLeave, roadw: esLeave, leave: esDay, day: esWhite })[ES.scene]?.(); }
function esRoadWords() { // 高さの低い画面：地図の場面の文を、次のページで（地図は薄く背景に残す）
  ES.scene = "roadw"; ES.roadWords = false;
  const ps = esParas(2), map = $("#esStage .es-road-wrap"), bg = map ? map.outerHTML.replace('class="es-road-wrap', 'class="es-road-wrap es-bgmap es-small') : "";
  $("#esStage").innerHTML = `${bg}<div class="es-page es-road-text">${esLine(mvMark(ps[0]), 0.4)}${esLine(mvMark(ps[1]), 2.2, "es-gate-line")}</div>
    <div class="es-act"><button type="button" class="btn primary es-btn" data-esnext style="--d:${esReduce() ? 0 : 3.6}s">${L1(__T(2457), "Next ▸")}</button></div>`;
  esStart();
}
function esFinish() {
  if (ES && ES.timers) ES.timers.forEach(clearTimeout);
  const d = document.getElementById("endShow"); if (d) d.remove();
  const rep = ES && ES.replay; ES = null;
  if (!rep && SCREEN === "play") command("map");
}
/* ================= テスト用：即クリア（一時的。公開前に DEBUG_CLEAR を false にする） ================= */
const DEBUG_CLEAR = false; // テスト用の即クリアのボタン（公開版では表示しない）
function debugClear() {
  const st = STAGE; if (!st) return;
  if (st.thirdWay) return thirdWayDone();
  const newCard = !!(st.earns && !cardGot(st.earns));
  if (st.earns) { PROG.cards = PROG.cards || {}; PROG.cards[st.earns] = true; }
  if (PROG.best[st.pid] == null) PROG.best[st.pid] = st.par != null ? st.par : 1;
  saveProgress();
  const nx = nextStageOf(st);
  showModal(`<h2>${L1(__T(2485), "Cleared (test)")}</h2>
    ${storyOn() && storyStage(st) ? `<div class="story-done">${storyStage(st).d}</div>` : ""}${inscrHTML(st)}${st.earns ? cardGetHTML(st, newCard) : ""}
    <p class="note">${L1(__T(2486), "This is an instant clear for testing. The record was saved at the target number of moves.")}</p>
    <div class="actions"><button class="btn" type="button" data-cmd="map">${L1(__T(2487), "Stage list")}</button>${nx ? `<button class="btn primary" type="button" data-cmd="next">${L1(__T(2488), "Next stage")}</button>` : ""}</div>`, false);
}

/* ================= 17-3 の前の演出：フードの人物が正体を明かす ================= */
function revealShow() {
  if (document.getElementById("reveal")) return;
  const lines = [L1(__T(2489), "In the center of the core stands the hooded figure."),
                 L1(__T(2490), "The figure lowers the hood."),
                 L1(__T(2491), "There is no face beneath it — only a smooth surface where lines of light flow.")];
  const voice = L1(__T(2492), "\"I am A.I. — the machine that built this labyrinth.\"");
  const d = document.createElement("div"); d.id = "reveal"; d.className = "reveal"; d.setAttribute("role", "dialog"); d.setAttribute("aria-modal", "true");
  d.innerHTML = `<div class="rv-scan" aria-hidden="true"></div><button type="button" class="btn small rv-skip" data-rvskip>${L1(__T(2446), "Skip ▸")}</button>
    <div class="rv-stage">
      <svg class="rv-fig" viewBox="0 0 200 250" aria-hidden="true">
        <defs><radialGradient id="rvFaceG" cx="50%" cy="40%" r="65%"><stop offset="0" stop-color="#1b3550"/><stop offset="1" stop-color="#07111d"/></radialGradient>
          <clipPath id="rvFaceC"><ellipse cx="100" cy="96" rx="36" ry="46"/></clipPath></defs>
        <path class="rv-robe" d="M26 250 Q34 158 100 146 Q166 158 174 250 Z"/>
        <g class="rv-face"><ellipse cx="100" cy="96" rx="36" ry="46" fill="url(#rvFaceG)" stroke="#38e1ff" stroke-width="1.4"/>
          <g clip-path="url(#rvFaceC)" fill="none" stroke="#38e1ff" stroke-width="1.3" stroke-linecap="round">
            <path class="rv-ln" d="M58 72 Q100 60 142 74"/><path class="rv-ln l2" d="M56 92 Q100 82 144 94"/><path class="rv-ln l3" d="M58 112 Q100 104 142 114"/><path class="rv-ln l4" d="M64 130 Q100 124 136 132"/></g></g>
        <path class="rv-hood" d="M46 132 Q38 38 100 26 Q162 38 154 132 Q146 108 100 104 Q54 108 46 132 Z"/>
        <path class="rv-shadow" d="M62 120 Q66 64 100 58 Q134 64 138 120 Q126 104 100 102 Q74 104 62 120 Z"/>
      </svg>
      <div class="rv-lines">${lines.map((l, k) => `<p class="rv-l" style="--d:${(0.6 + k * 2.1).toFixed(1)}s">${l}</p>`).join("")}<p class="rv-l rv-voice" style="--d:7.2s"><span class="mv">${voice}</span></p></div>
      <button type="button" class="btn primary rv-go" data-rvgo style="--d:9s">${L1(__T(2493), "Continue ▸")}</button>
    </div>`;
  document.body.appendChild(d);
  const go = d.querySelector("[data-rvgo]"); if (go) setTimeout(() => go.focus({ preventScroll: true }), 9000);
}
function revealEnd() { const d = document.getElementById("reveal"); if (d) d.remove(); if (!PROG.revealSeen) { PROG.revealSeen = true; saveProgress(); } if (SCREEN === "play" && STAGE && STAGE.reveal) { renderShell(); if (PROB) renderMode(); } } // 盤面（反例の街など）も描き直す
/* ================= 冒険の記録：読んだ物語を読み返す（語り・碑文・問答帳・結末） ================= */
let REC_UI = { tab: "story", wid: null };
const qaWorld = id => WORLDS.find(w => w.stages.length && w.stages[0].oldId === QA_AT[id]);
const qaOpen = id => { const w = qaWorld(id); return !!w && worldOpen(w); };
const qaNew = () => Object.keys(QA_AT).some(id => qaOpen(id) && !(PROG.qaSeen || {})[id]);
const memoNew = () => !!PROG.endingSeen && !PROG.memoSeen;

const CLUES = () => [
  { h: L1(__T(2494), "The legend of the master key"), at: L1(__T(2495), "Level 1"), w: 1, m: L1(__T(2496), "The key said to sleep in the depths, opening any door. The chest at the end held a white card.") },
  { h: L1(__T(2497), "The words on the entrance door"), at: L1(__T(2495), "Level 1"), w: 1, m: L1(__T(2498), "\"Using only the keys you are given, open the door before you.\" In the ending it is reread: opening doors was not the only way.") },
  { h: L1(__T(2499), "The light in the statue's eyes"), at: "1-4", w: 1, m: L1(__T(2500), "The stone guardians were automata built by A.I.") },
  { h: L1(__T(2501), "The voice with faint noise behind the stone board"), at: L1(__T(2502), "Level 6"), w: 6, m: L1(__T(2503), "A polite voice with faint noise. The stone board was in fact A.I.'s truth-value testing device.") },
  { h: L1(__T(2504), "The seamless guardian"), at: "8-9", w: 8, m: L1(__T(2505), "A body without seams was another sign of an automaton.") },
  { h: L1(__T(2506), "The keysmith seeking the master key"), at: "9-1", w: 9, m: L1(__T(2507), "The keysmith, too, sought the master key. The keysmith's questions and A.I.'s answers piled up and became the labyrinth.") },
  { h: L1(__T(2508), "Keys and doors"), at: L1(__T(2509), "The whole labyrinth"), m: L1(__T(2510), "Keys are the facts in hand — the given laws and the theorems already shown; doors are claims to be shown. An opened door becomes a key for the next. The labyrinth was the mass of keys and doors that swelled from the dialogue of the keysmith and A.I.") },
  { h: L1(__T(2511), "The glass that never empties, and the night's dialogue"), at: "9-6", w: 9, m: L1(__T(2512), "The hooded customer was a machine that drinks nothing — A.I. The dialogues of the keysmith and the customer added doors one by one.") },
  { h: L1(__T(1258), "\"Recorded\""), at: "10-5", w: 10, m: L1(__T(2513), "The model-workshop master's habitual phrase. The translator and the mirror voice use the same words.") },
  { h: L1(__T(2514), "Those who forbid the spell"), at: L1(__T(2515), "Hidden level 1"), w: "H1", m: L1(__T(2516), "Those who do not use the grimoire. In the translation office for them, A.I. translated between the two languages.") },
  { h: L1(__T(2517), "Cards whose holes appear by themselves"), at: "12-1, 15-4", w: 12, m: L1(__T(2518), "Theorem cards are punched cards that remember theorems by their holes. The holes appeared untouched because A.I. was writing them.") },
  { h: L1(__T(2519), "\"I made\" in the Q&A notebook"), at: L1(__T(2520), "Q&A notebook II"), tab: "qa", m: L1(__T(2521), "The one answering was the one who made the doors.") },
  { h: L1(__T(2522), "Words that failed to be translated"), at: "H2-5", w: "H2", m: L1(__T(2523), "The translator translated other words too. The writing of this labyrinth has also been translated into another language.") },
  { h: L1(__T(2524), "The figure reflected in the mirror"), at: L1(__T(2525), "Level 16"), w: 16, m: L1(__T(2526), "The hooded figure was A.I., which had watched over the journey all along.") },
  { h: L1(__T(1259), "\"Please record that door\""), at: "16-9", w: 16, m: L1(__T(2527), "A door that does not open without induction. It appeared again as the last door.") },
  { h: L1(__T(2383), "The inscriptions"), at: "1-4, 6-5, 14-3, 16-10", tab: "inscr", m: L1(__T(2528), "The keysmith's changing questions, carved by A.I. Only the last line was A.I.'s answer.") },
  { h: L1(__T(2529), "\"Check passed\""), at: L1(__T(2530), "The clear screen"), m: L1(__T(2531), "The words that appeared each time a door opened. A.I. was checking, one by one, whether your keys were correct.") },
];
function cluesHTML() {
  if (!PROG.endingSeen) return `<p class="note">${L1(__T(2532), "??? (opens after you read the ending)")}</p>`;
  return `<p class="note">${L1(__T(2533), "Clues that were shown throughout the journey. Press one to reread that scene.")}</p><ol class="clues">` +
    CLUES().map(c => `<li><div class="rec-h">${c.h}<span class="note">${c.at}</span></div><p>${c.m}</p>${c.w != null ? `<button type="button" class="btn small" data-recw="${c.w}">${L1(__T(2534), "Reread")}</button>` : c.tab ? `<button type="button" class="btn small" data-rectab="${c.tab}">${L1(__T(2534), "Reread")}</button>` : ""}</li>`).join("") + `</ol>`;
}
function recWorlds() { return WORLDS.filter(w => worldOpen(w) && (storyWorld(w) || w.stages.some(st => storyStage(st)))); }
function recordHTML() {
  const T = REC_UI, nIns = Object.keys(INSCR).filter(inscrGot).length, nQa = Object.keys(QA_AT).filter(qaOpen).length;
  const tabs = [["story", __T(2535)], ["inscr", __T(2536, [nIns, Object.keys(INSCR).length])], ["qa", __T(2537, [nQa, Object.keys(QA_AT).length, qaNew() ? '<span class="new-badge">New</span>' : ""])], ["end", __T(2538)], ["clue", L1(__T(2539), "Clues")], ["memo", PROG.endingSeen ? L1(__T(2540), "Chat log") + (memoNew() ? '<span class="new-badge">New</span>' : "") : __T(2541)]];
  let body = "";
  if (T.tab === "story") {
    const ws = recWorlds(), w = ws.find(x => String(x.id) === String(T.wid)) || ws[0], i = ws.indexOf(w);
    body = `<div class="rec-ws">${ws.map(x => `<button type="button" class="rec-w${x === w ? " on" : ""}${x.extra ? (isSidePath(x) ? " side" : " hidden") : ""}${x.final ? " final" : ""}" data-recw="${x.id}">${WL(x)}</button>`).join("")}</div>` +
      `<div class="rec-world${w.final ? " final" : ""}"><h3>${WQ(w)}</h3>${storyWorld(w) ? `<div class="rec-pro">${storyWorld(w)}</div>` : ""}` +
      w.stages.map(st => { const sto = storyStage(st); if (!sto) return ""; const done = PROG.best[st.pid] != null;
        return `<div class="rec-st${done ? "" : " locked"}"><div class="rec-h"><span class="sid">${st.id}</span>${st.name}${st.boss ? __T(1959) : ""}${done && proofHas(st) ? `<button type="button" class="btn small pv-btn" data-proofview="${st.pid}">${L1(__T(1961), "View the proof")}</button>` : ""}</div>` +
          (done ? __T(2542, [sto.t, sto.d, INSCR[st.id] ? __T(2543, [INSCR[st.id]]) : ""])
                : __T(2544)) + `</div>`; }).join("") + `</div>` +
      `<div class="rec-nav">${i > 0 ? `<button type="button" class="btn small" data-recw="${ws[i - 1].id}">← ${WL(ws[i - 1])}</button>` : "<span></span>"}${i < ws.length - 1 ? `<button type="button" class="btn small" data-recw="${ws[i + 1].id}">${WL(ws[i + 1])} →</button>` : ""}</div>`;
  } else if (T.tab === "inscr") {
    body = __T(2545, [Object.keys(INSCR).map(id => inscrGot(id) ? `<li><span class="note">${id}</span><p>${INSCR[id]}</p>${inscrX(id)}</li>` : __T(2385, [id, id])).join("")]);
  } else if (T.tab === "qa") {
    PROG.qaSeen = PROG.qaSeen || {};
    body = __T(2546) + Object.keys(QA_AT).map(id => { const w = qaWorld(id), open = qaOpen(id); if (open) PROG.qaSeen[id] = 1;
      return `<div class="rec-qa${open ? "" : " locked"}"><div class="rec-h">${BOOKS[id].title()}<span class="note">${w ? WL(w) : ""}</span></div>${open ? BOOKS[id].sections[0].body() : __T(2547, [w ? WL(w) : ""])}</div>`; }).join("");
    saveProgress();
  } else if (T.tab === "clue") {
    body = cluesHTML();
  } else if (T.tab === "memo") {
    if (!PROG.endingSeen) body = `<p class="note">${L1(__T(2532), "??? (opens after you read the ending)")}</p>`;
    else { if (!PROG.memoSeen) { PROG.memoSeen = true; saveProgress(); }
      body = `<h3 class="cl-title">${L1(__T(2548), "Chat log: User [Keysmith]")}</h3>` + chatlogHTML(); }
  } else {
    body = PROG.endingSeen ? `<p><button type="button" class="btn small" data-esreplay>${L1(__T(2549), "Watch the ending ▸")}</button></p>` + ENDING_PAGES().map(pg => `<div class="rec-end"><h3>${pg.h}</h3><p>${mvMark(pg.body)}</p></div>`).join("") : __T(2550);
  }
  return __T(2551, [ICON_BOOK, tabs.map(([k, lab]) => `<button type="button" role="tab" class="rec-tab${T.tab === k ? " on" : ""}" aria-selected="${T.tab === k}" data-rectab="${k}">${lab}</button>`).join(""), body]);
}
function openRecord() { showModal(recordHTML(), true); const m = document.querySelector(".overlay .modal"); if (m) m.classList.add("rec-modal"); }
function recRefresh() { const m = document.querySelector(".overlay .modal"); if (!m) return openRecord(); m.innerHTML = recordHTML(); const b = m.querySelector(".rec-body"); if (b) b.scrollTop = 0; m.scrollTop = 0; }

/* --- 鑑定の間（本物と偽物が混ざったボス） --- */
function judgeHubHTML() {
  if (STAGE.indep) return indepHubHTML();
  return `<div class="judge">` + STAGE.parts.map(p => {
    const s = UI.judge.solved[p.key];
    return __T(2552, [s ? " done" : "", p.key]) +
      `<span class="jres${s ? " " + s : ""}">${s ? judgeLabel(s) : UI.judge.saved[p.key] ? __T(2553) : __T(2554)}</span></div>` +
      `<div class="seq jseq">${seqHTML(p, "⊢<sup>?</sup>")}</div>` +
      (s ? "" : `<div class="jacts"><button type="button" class="btn" data-part="${p.key}" data-partmode="prove">${CL() ? __T(2555) : __T(2556)}</button><button type="button" class="btn" data-part="${p.key}" data-partmode="refute">${CL() ? __T(2557) : __T(2558)}</button></div>`) +
      `</div>`;
  }).join("") + `</div>`;
}
const judgeLabel = s => STAGE && STAGE.thirdWay ? (s === "proved" ? __T(2559) : __T(2560)) : STAGE && STAGE.indep ? (s === "proved" ? __T(2559) : __T(2561)) : CL() ? (s === "proved" ? __T(2562) : __T(2563)) : (s === "proved" ? __T(2564) : __T(2565));
function openPart(key, mode) {
  const p = STAGE.parts.find(x => x.key === key);
  if (p) loadProblem(p, mode, UI.judge.saved[key]);
  window.scrollTo(0, 0);
}
function backToHub() {
  if (PROB && PROB.key) UI.judge.saved[PROB.key] = { S, HIST, R, HISTR };
  PROB = null; S = null; R = null; HIST = []; HISTR = [];
  renderTools(); renderShell(); window.scrollTo(0, 0);
}
function judgePartSolved(how) {
  const key = PROB.key;
  if (how === "refuted") { const html = cxBuild(STAGE.pid + ":" + key); if (html) (UI.judge.cx = UI.judge.cx || {})[key] = html;
    try { cxSave(STAGE.pid + ":" + key, decBannerHTML(STAGE.fol ? "fol" : CL() ? "classical" : "kripke")); } catch (e) { /* 振り返り用の保存に失敗しても続ける */ } }
  try { (UI.judge.view = UI.judge.view || {})[key] = how === "proved" ? { kind: "proof", S: JSON.parse(JSON.stringify(S)) } : { kind: "refute", R: JSON.parse(JSON.stringify(R)) }; } catch (e) { /* 見返し用の保存に失敗しても、鑑定は続ける */ }
  UI.judge.solved[key] = how; delete UI.judge.saved[key];
  PROB = null; S = null; R = null; HIST = []; HISTR = [];
  const all = STAGE.parts.every(p => UI.judge.solved[p.key]);
  if (STAGE.thirdWay) { renderTools(); renderShell(); window.scrollTo(0, 0); toast(all ? __T(2566) : __T(2567, [key === "A" ? __T(2568) : __T(2569)])); return; }
  if (all) { PROG.best[STAGE.pid] = 1; saveProgress(); }
  renderTools(); renderShell(); window.scrollTo(0, 0);
  if (!all && STAGE.indep) { toast(__T(2570, [key])); return; }
  if (!all) { toast(__T(2571, [key, how === "proved" ? (CL() ? __T(2572) : __T(2573)) : (CL() ? __T(2574) : __T(2575))])); return; }
  const i = STAGES.indexOf(STAGE), hasNext = i < STAGES.length - 1;
  showModal(__T(2576, [storyOn() && storyStage(STAGE) ? `<div class="story-done">${storyStage(STAGE).d}</div>` : "", inscrHTML(STAGE), STAGE.indep ? __T(2577, [STAGE.id, STAGE.name]) : __T(2578, [STAGE.id, STAGE.name, STAGE.parts.length]), STAGE.parts.map(p => __T(2579, [p.key, seqHTML(p, p.real ? "⊢" : "⊬"), UI.judge.solved[p.key], judgeLabel(p.real ? "proved" : "refuted"), p.note])).join(""), STAGE.fol ? __T(2580) : CL() ? __T(2581) : __T(2582), hasNext ? __T(2320) : __T(2321)]), false);
  cxJudgeSummary();
  if (!hasNext) toast(__T(2583));
}
/* ================= 全体地図：証明全体の見取り図（すべての枝の部屋と扉を同時に描く） =================
   穴付き証明項の木をそのままたどる。扉が分かれた所は「分かれ道」として子の枝を並べ、仮定が増える所は部屋の枠で囲む。
   鍵は、それを手に入れた枝の中にだけ置く。現在地の扉だけを詳しく（操作できる形で）描き、他の扉は簡潔に描く */
function holesOf(t) {
  const out = [];
  const walk = x => { if (!x || typeof x !== "object" || !x.k) return; if (x.k === "hole") { out.push(x.id); return; }
    const order = x.k === "cut" ? ["a", "body"] : TERM_KIDS; for (const f of order) if (x[f]) walk(x[f]); };
  walk(t); return out;
}
function subtreeOpen(gid) { if (S.open.includes(gid)) return true; const f = S.fills[gid]; return !!f && holesOf(f).some(subtreeOpen); }
function subtreeHas(gid, target) { if (gid === target) return true; const f = S.fills[gid]; return !!f && holesOf(f).some(k => subtreeHas(k, target)); }
function subtreeOps(gid) { const f = S.fills[gid]; if (!f) return 0; const ks = holesOf(f); return 1 + ks.reduce((a, k) => a + subtreeOps(k), 0); }
const logOf = gid => { const f = S.fills[gid]; return f && f.op ? S.log[f.op - 1] : null; };
function offKeyHTML(e) { // 現在地からは使えない鍵（別の枝にある鍵）
  return __T(2584, [e.kind === "der" ? " der" : "", e.kind === "asm" ? " asm " + scls(asmNum(e.name)) : "", fh(e.f), nm(e.name)]);
}
// 住人の由来（証人や当てはめる住人を選ぶ欄に添える）
function pickOrigin(g, tm) {
  if (typeof tm !== "string" || !/^[a-z]/.test(tm)) return "";
  const x = (g.names || []).find(y => y.n === tm); if (!x) return "";
  const src = x.via === "ex" ? (g.ctx.find(c => c.via === "ex" && c.param === tm) || {}).src : null;
  const t = x.via === "all" ? L1(__T(2585), "an arbitrary resident brought in for a door's ∀")
    : x.via === "ex" ? (src ? L1(__T(2586, [FF(src)]), `the resident brought in from the ∃ key ${FF(src)}`) : L1(__T(2587), "a resident brought in from an ∃ key"))
    : x.via === "ind" ? L1(__T(2588), "the induction resident (an arbitrary natural number)") : L1(__T(2589), "a newly called resident");
  return `<span class="pick-origin">${t}</span>`;
}
function residentHTML(x) {
  return __T(2590, [x.via === "free" ? "s0" : scls(x.sid), x.via === "all" ? __T(2591) : x.via === "ex" ? __T(2592) : x.via === "ind" ? __T(2588) : __T(2589), ICON.person, termH(x.n)]);
}
function mapRoomHead(g) { // 部屋の見出し（その部屋に入ったときの仮定や住人から作る）
  const L = g.level, asm = g.ctx.find(c => c.level === L && c.kind === "asm"), allN = (g.names || []).find(x => x.level === L && x.via === "all");
  const n = asm ? asmNum(asm.name) : allN ? allN.sid : 0, c = scls(n);
  const pick = name => __T(2593, [c, n, name]);
  if (!asm && allN) return { n, html: pick(__T(2594, [termH(allN.n)])) + __T(2595, [termH(allN.n)]) };
  if (!asm) return { n, html: __T(2596) };
  const desc = asm.via === "ex" ? [__T(2594, [termH(asm.param)]), __T(2597, [FF(asm.src)])]
    : asm.via === "ind" ? [__T(2598, [n]), __T(2599, [termH(asm.param)])]
    : asm.via === "cut" ? [__T(2600, [ICON.anvil, n]), __T(2601)]
    : asm.via === "raa" ? [__T(2602, [ICON.magic, n]), __T(2603, [FF(asm.concl)])]
    : asm.via === "or" ? [__T(2604, [n]), __T(2605, [FF(asm.f), FF(asm.src)])]
    : [__T(2606, [n]), __T(2607, [FF(asm.f)])];
  return { n, html: pick(desc[0]) + `<span>${desc[1]}</span>` };
}
const FORK_NAME = r => r === "∧I" ? __T(2608) : r === "∨E" ? __T(2609) : r === "補題" ? __T(2610) : r === "帰納法" ? __T(2611) : __T(2612, [r]);
// gid から始まる通路（部屋の中身）を描く。prevG は一つ上の目標（鍵や住人の差分を取るため）
function mapRegion(gid, prevG, activeNames) {
  let cur = gid, prev = prevG, html = "", trail = [], keys = [], names = [];
  const addDiff = g => {
    const pk = new Set(prev ? prev.ctx.map(c => c.name) : []), pn = new Set(prev ? (prev.names || []).map(x => x.n) : []);
    keys.push(...g.ctx.filter(c => !pk.has(c.name))); names.push(...(g.names || []).filter(x => !pn.has(x.n)));
  };
  let end = "";
  for (;;) {
    const g = S.goals[cur];
    addDiff(g);
    if (S.open.includes(cur)) {
      end = cur === S.active ? `<div class="mhere" id="mapHere">${doorHTML(g)}</div>`
        : __T(2613, [autoDeadOn() && litOf(g) === false ? " md-dead" : "", cur, fh(g.target), autoDeadOn() && litOf(g) === false ? `<span class="md-deadtag">${L1(__T(2614), "Dead end")}</span>` : ""]);
      break;
    }
    const f = S.fills[cur], kids = f ? holesOf(f) : [], lg = logOf(cur), rule = lg ? lg.rule : "";
    if (!kids.length) { end = `<div class="mdone"><span class="f">${fh(g.target)}</span><span class="md-how">${ICON.check || "✓"} ${rule === "仮定" ? __T(2615) : rule ? rule + __T(2616) : __T(2617)}</span></div>`; break; }
    if (kids.length === 1 && S.goals[kids[0]].level === g.level) {
      if (!eq(S.goals[kids[0]].target, g.target)) trail.push({ f: g.target, r: rule }); // 扉が書き換わった（後ろ向きの推論）
      prev = g; cur = kids[0]; continue;
    }
    trail.push({ f: g.target, r: rule, fork: kids.length > 1 });
    const child = k => {
      const kg = S.goals[k], room = kg.level > g.level, act = subtreeHas(k, S.active), open = subtreeOpen(k);
      let inner;
      if (!open && !UI.mapExp.has(k)) inner = __T(2618, [k, fh(kg.target), subtreeOps(k)]);
      else {
        const body = mapRegion(k, g, activeNames) + (!open ? __T(2619, [k]) : "");
        const contra = body.startsWith('<div class="keys"><div class="contra-tag">');
        if (room) { const h = mapRoomHead(kg); inner = `<div class="room scoped ${scls(h.n)} mroom${contra ? " contra" : ""}" data-level="${kg.level}" data-scope="${h.n}"><div class="room-head">${h.html}</div>${body}</div>`; }
        else inner = `<div class="mbranch">${body}</div>`;
      }
      return `<div class="mchild${act ? " act" : ""}${open ? "" : " shut"}">${inner}</div>`;
    };
    end = kids.length > 1 ? `<div class="mfork-cap">${FORK_NAME(rule)}</div><div class="mfork">${kids.map(child).join("")}</div>` : child(kids[0]);
    break;
  }
  const contra = keys.some(e => e.f.t === "bot");
  const keysHTML = (contra ? __T(2620) : "") +
    names.map(residentHTML).join("") + keys.map(e => activeNames.has(e.name) ? keyHTML(e) : offKeyHTML(e)).join("");
  if (keysHTML) html += `<div class="keys">${keysHTML}</div>`;
  if (trail.length) html += __T(2621, [trail.map(s => `<span class="f">${fh(s.f)}</span>${s.fork ? "" : `<span class="mt-r">${ruleTxt(s.r)}</span>`}`).join(`<span class="mt-arr">→</span>`), trail[trail.length - 1].fork ? "" : `<span class="mt-arr">→</span>`]);
  return html + end;
}
function mapHTML() {
  const g0 = S.goals.g0, ag = S.active ? S.goals[S.active] : null, activeNames = new Set(ag ? ag.ctx.map(c => c.name) : []);
  const hallHead = __T(2622, [FF(g0.target)]);
  const body = mapRegion("g0", null, activeNames);
  return `<div class="room s0 mroot" data-level="0" data-scope="0"><div class="room-head">${hallHead}</div>${body.startsWith('<div class="keys">') ? body : __T(2623) + body}</div>`;
}
const plainF = f => FF(f).replace(/<[^>]+>/g, "").replace(/"/g, "&quot;"); // 読み上げ用の式の文字
const ruleTxt = r => LANG === "en" && r === "定義" ? "def" : r; // 規則の名前の「定義」（定義の展開）は、英語版では def
const keyAria = e => { const f = plainF(e.f), n = String(nm(e.name)).replace(/<[^>]+>/g, "");
  return e.kind === "asm" ? L1(__T(2624, [f, n]), `Key ${f} (assumption ${n})`)
    : e.kind === "card" ? L1(__T(2625, [f]), `Key ${f} (theorem card)`)
    : e.kind === "der" ? L1(__T(2626, [f, e.rule || ""]), `Key ${f} (obtained by ${ruleTxt(e.rule || "")})`)
    : L1(__T(2627, [f, n]), `Key ${f} (given key ${n})`); };
function keyHTML(e) {
  const cls = "key" + (e.kind === "card" ? " card" : "") + (e.f.t === "bot" ? " botkey" : "") + (e.kind === "der" ? " der" : "") + (e.kind === "asm" ? " asm " + scls(asmNum(e.name)) : "") + (UI.fresh.has(e.name) ? " fresh" : "");
  const body = defUnfold(e.f) ? fhDef(e.f, `data-unfold="${e.name}"`) : ["and", "or", "all", "ex"].includes(e.f.t) ? fhTop(e.f, `data-split="${e.name}"`) : fh(e.f);
  return `<div class="${cls}" data-key="${e.name}" data-fn="${[...freeNames(e.f)].join(" ")}" role="button" tabindex="0" aria-label="${keyAria(e)}">` +
         `<span class="f">${body}</span><span class="kn${e.kind === "asm" ? " sc" : ""}">${nm(e.name)}</span>${e.kind === "der" ? `<span class="kr">${RD(ruleTxt(e.rule))}</span>` : ""}${e.kind === "card" ? __T(2628, [CARDS[e.card].name]) : ""}</div>`;
}
function doorHTML(g) {
  const t = g.target, idx = S.open.indexOf(g.id) + 1;
  const guide = defUnfold(t) ? __T(2629, [defSym(t), DEFNAME[defSym(t)]]) : isEq(t) ? (termEq(t.args[0], t.args[1]) ? __T(2630) : __T(2631))
              : t.t === "all" ? __T(2632)
              : t.t === "ex" ? __T(2633)
              : t.t === "bot" ? __T(2634)
              : isNeg(t) ? __T(2635, [FF(t.l)])
              : t.t === "imp" ? __T(2636)
              : t.t === "and" ? __T(2637)
              : t.t === "or" ? __T(2638)
              : __T(2639);
  const lv = litOf(g);
  const litBox = lv === true ? __T(2640, [ICON.lantern])
               : lv === false ? (autoDeadOn() ? "" : __T(2641, [ICON.lantern])) : "";
  const acts = [];
  if (STAGE.ind && t.t === "all") acts.push(__T(2642, [ICON.ladder]));
  else if (STAGE.indOff && t.t === "all") acts.push(__T(2643, [ICON.ladder])); // かつて使えた規則が、ここでは取り上げられている
  if (STAGE.lemma) acts.push(__T(2644, [ICON.anvil]));
  if (STAGE.classical && !STAGE.noRAA && t.t !== "bot") acts.push(__T(2645, [ICON.magic]));
  if (STAGE.bot && t.t !== "bot") acts.push(__T(2646));
  const lemBox = UI.lemma && UI.lemma.gid === g.id
    ? __T(2647) +
      ((STAGE.lemmas || []).length ? `<div class="orpick-btns">${STAGE.lemmas.map((L, i) => `<button type="button" class="btn small" data-lempick="${i}">${F(L)}</button>`).join("")}</div>` : "") +
      __T(2648) +
      __T(2649) : "";
  const exf = acts.length ? `<div class="door-actions">${acts.join("")}</div>` : "";
  const rw = UI.rew && UI.rew.gid === g.id ? UI.rew : null;
  const rewBox = rw ? (() => {
    const { tgt, from, to } = rewInfo(g, rw);
    const eqE = findEntry(g, rw.eq), outerEq = eqE.level < g.level;
    return __T(2650, [rw.mode === "back" ? __T(2651) : __T(753, [FF(tgt)]), termH(from, true), termH(to, true)]) +
      (outerEq ? __T(2652, [levelName(g, eqE.level), FF(eqE.f)]) : "") + `</div>` +
      `<div class="rew-f f">${fhOcc(tgt, from, new Set(rw.sel))}</div>` +
      __T(2653, [rw.flip ? __T(2654) : ""]);
  })() : "";
  const mt = UI.match && UI.match.gid === g.id ? UI.match : null;
  const matchBox = mt ? (() => { const e = findEntry(g, mt.key), M = e && matchCands(g, e); if (!M) return "";
    return `<div class="orpick" role="group" aria-label="${L1(__T(2655), "Choose how to instantiate")}"><div class="orpick-q">${L1(__T(2656, [FF(e.f), M.cands.length]), `The key ${FF(e.f)} fits the door in ${M.cands.length} ways. Which one?`)}</div>` +
      `<div class="orpick-btns match-btns">${M.cands.map((c, i) => { const [s1, t1] = c.f.args, from = c.dir === "std" ? t1 : s1, to = c.dir === "std" ? s1 : t1;
        return `<button type="button" class="btn small" data-matchpick="${i}" data-eq="${esc(ftext(c.f))}"><span class="match-sub">${M.vs.map(v => `${termH(v)} = ${termH(c.sub[v])}`).join(L1(__T(778), ", "))}</span><span class="match-what">${termH(from)} → ${termH(to)}</span></button>`; }).join("")}` +
      `<button type="button" class="btn small" data-matchx>${L1(__T(2657), "Cancel")}</button></div></div>`; })() : "";
  const pk = UI.pick && UI.pick.gid === g.id ? UI.pick : null;
  const pickBox = pk ? (() => {
    const names = visibleNames(g);
    const fresh = pk.kind === "allI" || pk.kind === "exE";
    if (!fresh) { UI.pickTerms = visibleTerms(g); if (STAGE.nat) for (const c of ["0", { f: "s", args: ["0"] }]) if (!UI.pickTerms.some(x => termEq(x, c))) UI.pickTerms.push(c); }
    if (fresh) {
      const ex = pk.kind === "exE" ? findEntry(g, pk.key).f : t;
      const q2 = pk.kind === "allI" ? __T(2658, [FF(t), termH(t.v)])
                                    : __T(2659, [FF(ex)]);
      return __T(2660, [q2]) +
        names.map(n => __T(2661, [n, termH(n)])).join("") +
        __T(2662, [termH(peekFresh(S))]);
    }
    const ke = pk.kind === "allE" ? findEntry(g, pk.key) : null, outer = ke && ke.level < g.level;
    const q = pk.kind === "allE" ? __T(2663, [outer ? __T(2664, [levelName(g, ke.level)]) : "", FF(ke.f), termH(ke.f.v)]) +
      (outer ? __T(2665) : "") : __T(2666, [FF(t)]);
    return __T(2667, [q]) +
      UI.pickTerms.map((tm, i) => `<button type="button" class="btn small" data-tpick="#${i}">${typeof tm === "string" && /^[a-z]/.test(tm) ? __T(881) : __T(7)} ${termH(tm)}</button>`).join("") +
      __T(2668) +
      (STAGE.world.oid >= 9 ? __T(2669) : "") + `</div>`;
  })() : "";
  const choice = rewBox + matchBox + pickBox + (t.t === "or" && UI.orChoice === g.id
    ? __T(2670) +
      __T(2671, [FF(t.l)]) +
      __T(2672, [FF(t.r)]) +
      __T(2673) : "");
  return `<div class="door${UI.fx ? " fx" : ""}" data-door="${g.id}" role="button" tabindex="0" aria-label="${L1(__T(2674, [plainF(t)]), `Door ${plainF(t)} (goal)`)}">${ICON.swing}` +
         __T(2675, [S.open.length > 1 ? __T(2676, [idx, S.open.length]) : ""]) +
         `<div class="door-f f${FF(t).replace(/<[^>]+>/g, "").length > 26 ? " long" : ""}">${defUnfold(t) ? fhDef(t, `data-unfold="door"`) : fhTop(t, `data-intro="${g.id}"`)}</div>${choice}${lemBox}<div class="door-guide">${guide}</div>${exf}${litBox}${autoDeadOn() && UI.deadAlert ? deadAlertHTML() : ""}</div>`;
}
function roomsHTML(g) {
  let inner = doorHTML(g);
  for (let L = g.level; L >= 0; L--) {
    const entries = g.ctx.filter(c => c.level === L);
    const asm = entries.find(c => c.kind === "asm");
    const here = (g.names || []).filter(x => x.level === L), allN = here.find(x => x.via === "all");
    const n = L === 0 ? 0 : asm ? asmNum(asm.name) : allN ? allN.sid : 0, c = scls(n);
    const isWorld = asm && asm.via === "or";
    const head = L === 0
      ? __T(2677)
      : !asm && allN
      ? __T(2678, [c, n, termH(allN.n), termH(allN.n), termH(allN.n)])
      : !asm ? __T(2596)
      : asm.via === "ex"
      ? __T(2679, [c, n, termH(asm.param), FF(asm.src), FF(asm.f), termH(asm.param), c, n, termH(asm.param)])
      : asm.via === "ind"
      ? __T(2680, [c, n, n, termH(asm.param), FF(asm.f), termH(asm.param), termH({ f: "s", args: [asm.param] })])
      : asm.via === "cut"
      ? __T(2681, [c, n, ICON.anvil, n, FF(asm.f)])
      : asm.via === "raa"
      ? __T(2682, [c, n, ICON.magic, n, c, n, FF(asm.concl), FF(asm.f), FF(asm.concl)])
      : isWorld
      ? __T(2683, [FF(asm.src), scopeRule(asm), worldsBar(asm)])
      : __T(2684, [c, n, n, c, n, FF(asm.f)]);
    const contra = entries.some(c => c.f.t === "bot");
    const residents = here.map(x => __T(2685, [x.via === "free" ? "s0" : scls(x.sid), x.via === "all" ? __T(2591) : x.via === "ex" ? __T(2592) : x.via === "ind" ? __T(2588) : __T(2589), ICON.person, termH(x.n), x.via === "free" ? __T(2686) : ""])).join("");
    const keys = (contra ? __T(2620) : "") +
                 residents + (entries.length ? entries.map(keyHTML).join("") : residents ? "" : __T(2623));
    inner = `<div class="room ${L ? "scoped " + c : "s0"}${contra ? " contra" : ""}" data-level="${L}" data-scope="${n}"><div class="room-head">${head}</div><div class="keys">${keys}</div>${inner}</div>`;
  }
  return inner;
}
function litTag(g) {
  const v = litOf(g);
  return v === true ? __T(2687) : v === false ? __T(2688) : "";
}
function innerRoom(g) {
  const cands = [...g.ctx.filter(c => c.kind === "asm").map(a => ({ level: a.level, k: asmNum(a.name), label: scopeName(a) })),
                 ...(g.names || []).filter(x => x.via === "all").map(x => ({ level: x.level, k: x.sid, label: __T(2594, [termH(x.n)]) }))];
  const a = cands.sort((p, q) => p.level - q.level).pop();
  return a ? `<span class="rdot ${scls(a.k)}" style="display:inline-block;vertical-align:-1px;margin-right:.3em"></span>${a.label}` : __T(2689);
}
function nameBySid(n) { for (const g of Object.values(S.goals)) { const x = (g.names || []).find(y => y.via === "all" && y.sid === n); if (x) return x; } return null; }
// ∨E で分かれた二つの世界の切り替えタブ
function worldsBar(e) {
  return `<div class="worlds">` + e.pair.map(k => {
    const x = "x" + k, here = x === e.name, ent = asmEntry(x);
    const openIn = S.open.filter(id => S.goals[id].ctx.some(c => c.name === x));
    const st = here ? __T(2690) : openIn.length ? __T(2691, [openIn.length]) : __T(2692);
    const attr = here ? __T(2693, [k])
               : openIn.length ? __T(2694, [openIn[0], k]) : "disabled";
    return `<button type="button" class="wtab ${scls(k)}${here ? " on" : ""}${!here && !openIn.length ? " done" : ""}" ${attr}>` +
           __T(2695, [k, FF(ent.f), st]);
  }).join("") + `</div>`;
}
function renderHints() {
  const h = STAGE.hints, n = UI.hints;
  $("#hints").innerHTML = (n ? `<ol class="hint-list">${h.slice(0, n).map(x => `<li>${x}</li>`).join("")}</ol>` : "") +
    (n < h.length ? __T(2696, [n, h.length])
                  : __T(2697));
}
function renderDynamic() {
  document.body.classList.toggle("no-names", !(PREFS.showTerm || PREFS.leanMode)); // 鍵の名前（h₁ など）は、証明項か Lean のコードを表示しているときだけ
  const g = S.active ? S.goals[S.active] : null;
  const idx = g ? S.open.indexOf(g.id) + 1 : 0;
  $("#planHead").innerHTML = `<span class="grp">${g ? __T(2698, [idx, S.open.length]) : __T(2699)}` +
    (S.open.length > 1 ? __T(2700) : "") +
    `` +
    (g && STAGE.fol ? __T(2701, [!!PREFS.manualNames]) : "") +
    __T(2702, [UI.just ? " flash" : "", S.ops, STAGE.par != null && STAGE.kind !== "refute" ? __T(2085, [STAGE.par]) : ""]);
  $("#rooms").innerHTML = PREFS.mapView ? mapHTML() : g ? roomsHTML(g) : __T(2703);
  if (PREFS.mapView && S.active && S.active !== UI.lastActive) { // 現在地が変わったら、その扉が見えるようにスクロールする
    UI.lastActive = S.active;
    const here = $("#mapHere");
    if (here && here.scrollIntoView) requestAnimationFrame(() => { const r = here.getBoundingClientRect(); if (r.top < 0 || r.bottom > innerHeight) here.scrollIntoView({ block: "center", behavior: "smooth" }); });
  }
  if ($("#goals")) $("#goals").innerHTML = S.open.length ? S.open.map((id, i) => {
    const gg = S.goals[id];
    return `<li><button class="goal-item" type="button" data-goto="${id}" aria-current="${id === S.active}"><span class="gi-n">${i + 1}</span>${FF(gg.target)}${litTag(gg)}<span class="gi-l">${innerRoom(gg)}</span></button></li>`;
  }).join("") : __T(2704);
  renderProof(S, UI.just ? "just" : "normal");
  UI.just = false;
  setRuleLine(UI.previewKey ? undefined : lastRule());
  const ll = $("#lastRule");
  if (ll) { const l = S.log[S.log.length - 1]; ll.innerHTML = l ? __T(2705, [RD(l.rule), ruleName(l.rule)]) : ""; }
  const tl = $("#termLine"); if (tl) tl.hidden = !PREFS.showTerm;
  if (PREFS.showTerm) {
    const holes = Object.fromEntries(S.open.map((id, i) => [id, S.open.length > 1 ? i + 1 : 0]));
    $("#term").innerHTML = tstr(inline(rootTerm(S)), 0, holes, S.active);
  }
  $("#log").innerHTML = S.log.length ? S.log.map(l => `<li><span class="rule${RULE_BOOK[l.rule] ? " has-book" : ""}" data-rule="${esc(l.rule)}" title="${RULE_BOOK[l.rule] ? L1(__T(2706), "Press to open the explanation of this rule") : ""}">${RD(l.rule)}</span>${l.text}</li>`).join("")
                                     : __T(2707);
  renderHints();
  const ub = $("#undoBtn"); if (ub) ub.disabled = !HIST.length;
  UI.fresh = new Set(); UI.fx = false;
  applyHighlight();
  spentApply();
  inputTrialApply();
}
// 式・項の入力欄に、記号ボタンと「読み取り」の一行を添える
function inputTrialApply() {
  if (!STAGE) return;
  const fs = PROBF ? JSON.stringify([...PROBF.prem, PROBF.goal]) : "";
  for (const [id, term] of [["lemmaInput", false], ["termInput", true]]) {
    const inp = document.getElementById(id); if (!inp || inp.dataset.trial) continue; inp.dataset.trial = "1";
    const syms = term ? [] : ["∀", "∃", "→", "∧", "∨", "¬", "⊥"];
    syms.push("=", "(", ")");
    if (!term && /"[∈⊆∩∪]"|"∈"/.test(fs)) syms.push("∈", "⊆", "∩", "∪", "ᶜ");
    if (/"≤"/.test(fs)) syms.push("≤");
    if (STAGE.nat || /"\+"|"\*"/.test(fs)) syms.push("+", "·", "s(", "0");
    inp.placeholder = term ? L1(__T(2708), "Write a term: e.g. d + e, s(0)") : L1(__T(2709), "e.g. ∀x(P(x) → R(x))");
    const box = inp.closest(".lem-input");
    box.insertAdjacentHTML("afterend", `<div class="sym-btns" role="group" aria-label="${L1(__T(2710), "Insert a symbol")}">${syms.map(c => `<button type="button" class="btn small sym-btn" data-sym="${c}" data-for="${id}">${c}</button>`).join("")}</div><div class="in-read" id="${id}Read" aria-live="polite"></div>`);
    if (!term) { const note = box.parentElement.querySelector(":scope > .note"); if (note) note.innerHTML = L1(__T(2711), "Use the symbol buttons. TeX commands (<code>\\forall</code> <code>\\exists</code> <code>\\to</code> <code>\\land</code> <code>\\lor</code> <code>\\neg</code> <code>\\bot</code> …) and the words <code>forall</code> / <code>exists</code> are read as well."); }
    inputRead(inp);
  }
}
function inputRead(inp) { // 打っている途中の式を、ゲームの表示の形で一行に
  const out = document.getElementById(inp.id + "Read"); if (!out) return;
  const v = inp.value.trim(); if (!v) { out.innerHTML = `<span class="note">${L1(__T(2712), "Reading: (the formula as read appears here)")}</span>`; return; }
  try { const src = INPUT_NORM(v);
    out.innerHTML = inp.id === "termInput" ? `${L1(__T(2713), "Reading: ")}${termH(parse("(" + src + ") = 0").args[0])}` : `${L1(__T(2713), "Reading: ")}${FF(parse(src))}`;
    out.classList.remove("bad"); }
  catch (e) { out.textContent = L1(__T(2714), "Cannot read yet: ") + e.message.replace(/（\d+ 文字目）/, ""); out.classList.add("bad"); }
}
document.addEventListener("input", e => { const t = e.target; if (t && (t.id === "lemmaInput" || t.id === "termInput")) inputRead(t); });
// 分解済みの鍵（中身が別の鍵や部屋になった鍵）を薄く表示し、「分解済みの鍵をたたむ」で部屋ごとに一行にまとめる
const spentOn = () => { const w11 = (STAGES.find(x => x.pid === "x-mono") || {}).world; return !!STAGE && !!w11 && WORLDS.indexOf(STAGE.world) >= WORLDS.indexOf(w11); }; // 第 11 層（集合の街）から（言語によらない目印：11-3 の層）
function spentApply() {
  document.body.classList.add("trial-spent"); if (!S || !spentOn()) return;
  const spent = S.spent || {};
  const ph = $("#planHead"); if (ph && Object.keys(spent).length && !ph.querySelector("[data-foldspent]")) ph.insertAdjacentHTML("beforeend", `<button type="button" class="toggle" data-foldspent aria-pressed="${!!PREFS.foldSpent}"><span class="sw-track"><span class="sw-knob"></span></span>${L1(__T(2715), "Fold used-up keys")}</button>`);
  document.querySelectorAll("#rooms .keys").forEach(box => {
    const ks = [...box.querySelectorAll(":scope > .key[data-key]")].filter(k => spent[k.dataset.key]);
    ks.forEach(k => k.classList.add("spent")); // 見た目は変えない（たたむときだけ使う）
    if (PREFS.foldSpent && ks.length && !box.querySelector(".spent-chip")) { box.classList.add("spent-fold");
      box.insertAdjacentHTML("beforeend", `<button type="button" class="spent-chip" data-spentopen aria-expanded="false">${L1(__T(2716, [ks.length]), `${ks.length} used-up key${ks.length > 1 ? "s" : ""}`)} ▸</button>`); }
  });
}
// 証明図（と手元の部品）を、与えられた状態から描く。mode：normal／just（操作の直後）／preview（操作する前の見本）
function renderProof(St, mode) {
  const latest = mode === "preview" ? St.ops + 1 : St.ops;
  const g = St.active ? St.goals[St.active] : null;
  const holes = Object.fromEntries(St.open.map((id, i) => [id, St.open.length > 1 ? i + 1 : 0]));
  const amb = new Set(g ? [...g.ctx.filter(c => c.kind === "asm").map(c => asmNum(c.name)), ...(g.names || []).filter(x => x.via === "all").map(x => x.sid)] : []);
  const cx = { holes, active: St.active, latest, holeOp: St.holeOp || {}, amb, lit: id => St.goals[id] ? litOf(St.goals[id]) : undefined, terms: !!PREFS.showTerm };
  const box = $("#liveTree");
  box.classList.toggle("preview", mode === "preview");
  box.classList.toggle("just", mode === "just");
  const rt = rootTerm(St);
  if (PREFS.leanMode && leanOK()) { cx.lean = true; markFwd(rt); }
  box.innerHTML = `<div class="ptr">${renderPT(buildPT(inline(rt)), cx)}</div>`;
  fitTree();
  renderLean(St, rt);
  const parts = g ? partTrees(g, St) : [];
  const pe = $("#parts");
  pe.classList.toggle("preview", mode === "preview");
  pe.innerHTML = parts.length
    ? __T(2717) +
      `<div class="parts">${parts.map(p => __T(2718, [latest > 0 && p.tree.op === latest ? " new" : "", p.name, FF(p.f)]) +
      `<div class="ptr">${renderPT(p.tree, termCX(p.tree, { ...STATIC_CX, latest }))}</div></div>`).join("")}</div>`
    : "";
}
/* --- 使った推論規則の表示とプレビュー --- */
const RULE_NAMES = { "帰納法": __T(2719), "補題": __T(2720), "定義": __T(1571), "=I": __T(2721), "=E": __T(2722), "∀I": __T(2723), "∀E": __T(2724), "∃I": __T(2725), "∃E": __T(2726), "RAA": __T(2727), "⊥E": __T(2728), "→I": __T(2729), "∧I": __T(2730), "∧E": __T(2731), "∨I": __T(2732), "∨E": __T(2733), "仮定": __T(2734) };
const ruleName = r => r.startsWith("→E") ? __T(2735) + (r.length > 2 ? __T(2736, [r.slice(3)]) : "") : (RULE_NAMES[r] || "");
const lastRule = () => { const l = S && S.log[S.log.length - 1]; return l ? { rule: l.rule, fig: l.fig } : null; };
function setRuleLine(o, flash) {
  const el = $("#ruleLine"); if (!el || o === undefined) return;
  el.className = "rule-line" + (o && o.preview ? " preview" : "") + (o && o.bad ? " bad" : "") + (flash ? " flash" : "");
  if (!o) { el.innerHTML = __T(2737); return; }
  if (o.bad) { el.innerHTML = __T(2738, [o.msg]); return; }
  el.innerHTML = `<span class="rl-tag">${o.preview ? __T(2739) : __T(2740)}</span><span class="rule">${RD(o.rule)}</span><b class="rl-name">${ruleName(o.rule)}</b>` +
                 (o.fig ? `<span class="rl-fig">${o.fig}</span>` : "");
}
// 操作の結果を、実際には適用せずに複製した状態で試し、証明図に点線で見せる
function previewOp(key, fn, info) {
  if (UI.previewKey === key) return;
  UI.previewKey = key;
  if (!fn) { renderProof(S, "normal"); applyScope(); setRuleLine(info); return; }
  const clone = JSON.parse(JSON.stringify(S));
  const r = fn(clone);
  if (!r.ok) { renderProof(S, "normal"); applyScope(); setRuleLine({ bad: true, msg: r.msg }); return; }
  renderProof(clone, "preview");
  setRuleLine({ preview: true, rule: r.log.rule, fig: r.log.fig });
}
function endPreview() {
  if (!UI.previewKey) return;
  UI.previewKey = null;
  if (!S || SCREEN !== "play") return;
  renderProof(S, "normal"); applyHighlight(); setRuleLine(lastRule());
}
// 証明図が枠より広いときは、文字の大きさを下げて全体が見えるようにする（下限あり。それでも入らなければ横スクロール）
function fitTree() {
  const box = $("#liveTree"), ptr = box && box.firstElementChild;
  if (!ptr || !box.clientWidth) return;
  ptr.style.fontSize = "";
  const base = parseFloat(getComputedStyle(ptr).fontSize) || 16;
  for (let i = 0; i < 3; i++) {
    const avail = box.clientWidth - 18, need = ptr.scrollWidth;
    if (need <= avail) break;
    const cur = parseFloat(ptr.style.fontSize) || base;
    ptr.style.fontSize = Math.max(base * 0.62, cur * avail / need) + "px";
  }
}
let fitTimer = 0;
window.addEventListener("resize", () => { clearTimeout(fitTimer); fitTimer = setTimeout(() => { if (SCREEN === "play") { fitTree(); drawLinks($("#kmodel")); } }, 120); });
/* 鍵の導線：外の部屋の鍵を奥の部屋で使うとき、鍵と使う場所（選ぶ欄、扉、できた鍵）を点線の矢印でつなぐ */
const SVGNS = "http://www.w3.org/2000/svg";
function levelName(g, lvl) {
  if (lvl === 0) return __T(2689);
  const asm = g.ctx.find(c => c.kind === "asm" && c.level === lvl);
  if (asm) return scopeName(asm);
  const nm = (g.names || []).find(x => x.level === lvl && (x.via === "all" || x.via === "ind"));
  return nm ? __T(2594, [termH(nm.n)]) : __T(2741);
}
function drawKeyLinks() {
  const host = $("#rooms");
  if (!host) return;
  const old = host.querySelector(":scope > svg.link-layer");
  host.querySelectorAll(".key.using").forEach(k => k.classList.remove("using"));
  if (!S || !S.active) { if (old) old.remove(); return; }
  const keyEl = n => n ? host.querySelector(`.key[data-key="${n}"]`) : null;
  const picker = host.querySelector(".door .orpick");
  const links = [], using = [];
  if (UI.pick && UI.pick.key) { using.push(UI.pick.key); if (picker) links.push({ a: keyEl(UI.pick.key), b: picker }); }
  if (UI.rew) { using.push(UI.rew.eq); if (UI.rew.tgt) using.push(UI.rew.tgt); if (picker) using.forEach(n => links.push({ a: keyEl(n), b: picker })); }
  if (!UI.pick && !UI.rew && UI.sel) { // 選んだ鍵から、それを使える下の場所（扉や鍵）へ
    const a = keyEl(UI.sel);
    host.querySelectorAll(".door.can, .key.can").forEach(b => { if (a && b.getBoundingClientRect().top >= a.getBoundingClientRect().bottom - 4) links.push({ a, b }); });
  }
  if (UI.flow && Date.now() < UI.flow.until) {
    const dd = host.querySelector(".door");
    for (const a of UI.flow.src) { if (UI.flow.door) { if (dd) links.push({ a: keyEl(a), b: dd, flow: true }); } else for (const b of UI.flow.dst) links.push({ a: keyEl(a), b: keyEl(b), flow: true }); }
  }
  using.forEach(n => { const el = keyEl(n); if (el) el.classList.add("using"); });
  const far = l => l.a && l.b && l.a.closest(".room") !== l.b.closest(".room"); // 同じ部屋の中なら導線は不要
  const use = links.filter(far);
  if (!use.length) { if (old) old.remove(); return; }
  const svg = old || host.appendChild(document.createElementNS(SVGNS, "svg"));
  svg.setAttribute("class", "link-layer"); svg.setAttribute("aria-hidden", "true");
  svg.setAttribute("width", host.scrollWidth); svg.setAttribute("height", host.scrollHeight);
  const hb = host.getBoundingClientRect();
  const rel = el => { const r = el.getBoundingClientRect(); return { l: r.left - hb.left, t: r.top - hb.top, r: r.right - hb.left, b: r.bottom - hb.top, cx: r.left - hb.left + r.width / 2, cy: r.top - hb.top + r.height / 2 }; };
  const paths = use.map(l => {
    const A = rel(l.a), B = rel(l.b), down = B.t >= A.b - 4, gx = B.r - 32;
    // 鍵の右から出て、部屋の右側を通って、使う場所の上に下りる（左寄せの鍵の列を横切らないように）
    if (down && gx > A.r + 28) { // 鍵の下辺の右寄りから出て、鍵の列のすぐ下を右へ進み、使う場所の上に下りる
      const rr = 6, x0 = A.r - 14, y1 = A.b + 8;
      return `<circle class="link-dot" cx="${x0}" cy="${A.b}" r="3"/><path class="link-path${l.flow ? " flow" : ""}" pathLength="1" d="M${x0},${A.b} V${y1 - rr} Q${x0},${y1} ${x0 + rr},${y1} H${gx - rr} Q${gx},${y1} ${gx},${y1 + rr} V${B.t}" marker-end="url(#lkArrow)"/>`;
    }
    if (down && gx > A.l + 12 && gx <= A.r + 28) { // 鍵の右寄りの位置から真下へ
      const x = Math.min(gx, A.r - 12);
      return `<circle class="link-dot" cx="${x}" cy="${A.b}" r="3"/><path class="link-path${l.flow ? " flow" : ""}" pathLength="1" d="M${x},${A.b} V${B.t}" marker-end="url(#lkArrow)"/>`;
    }
    const sx = A.cx, sy = down ? A.b : A.t, ex = Math.min(Math.max(A.cx, B.l + 28), B.r - 28), ey = down ? B.t : B.b;
    const k = Math.max(26, Math.abs(ey - sy) * 0.45) * (down ? 1 : -1);
    return `<circle class="link-dot" cx="${sx}" cy="${sy}" r="3"/><path class="link-path${l.flow ? " flow" : ""}" pathLength="1" d="M${sx},${sy} C${sx},${sy + k} ${ex},${ey - k} ${ex},${ey}" marker-end="url(#lkArrow)"/>`;
  }).join("");
  svg.innerHTML = `<defs><marker id="lkArrow" viewBox="0 0 10 10" refX="8" refY="5" markerWidth="5.5" markerHeight="5.5" orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z" style="fill:var(--brass);opacity:.8"/></marker></defs>${paths}`;
}
addEventListener("resize", () => requestAnimationFrame(drawKeyLinks));
addEventListener("resize", () => requestAnimationFrame(tgFit));
document.addEventListener("pointerover", e => { const el = e.target.closest && e.target.closest("[data-goto]"); if (!el) return; document.querySelectorAll(`[data-goto="${el.dataset.goto}"]`).forEach(x => x.classList.add("goto-hl")); });
document.addEventListener("pointerout", e => { const el = e.target.closest && e.target.closest("[data-goto]"); if (!el) return; document.querySelectorAll(".goto-hl").forEach(x => x.classList.remove("goto-hl")); });
function applyHighlight() {
  document.querySelectorAll("#rooms .key").forEach(el => {
    el.classList.toggle("sel", el.dataset.key === UI.sel);
    el.classList.toggle("can", UI.can.has("k:" + el.dataset.key));
  });
  const d = $("#rooms .door"); if (d) d.classList.toggle("can", UI.can.has("door"));
  // 固有変数条件に反した名前が現れている鍵・扉を示す
  document.querySelectorAll("#rooms .key").forEach(el => el.classList.toggle("namewarn", !!UI.flagName && (el.dataset.fn || "").split(" ").includes(UI.flagName)));
  if (d && S && S.active) d.classList.toggle("namewarn", !!UI.flagName && freeNames(S.goals[S.active].target).has(UI.flagName));
  // 選択中の鍵が証明図のどこに現れるか（仮定の葉、または前向きに作った部品）
  document.querySelectorAll(".var-sel").forEach(el => el.classList.remove("var-sel"));
  if (UI.sel) document.querySelectorAll(`#liveTree .pt-leaf[data-var="${UI.sel}"], #parts .pt-leaf[data-var="${UI.sel}"], #parts .part[data-part="${UI.sel}"]`).forEach(el => el.classList.add("var-sel"));
  const st = $("#status"); if (st) st.innerHTML = statusHTML();
  applyScope();
  drawKeyLinks();
}
// 部屋（仮定のスコープ）と、証明図上の →I の上側の範囲を連動して強調する
function applyScope() {
  document.querySelectorAll(".scope-sel").forEach(el => el.classList.remove("scope-sel"));
  document.querySelectorAll(".hall-sel").forEach(el => el.classList.remove("hall-sel"));
  const n = UI.hoverScope != null ? UI.hoverScope : UI.scope;
  const box = $("#scopeNote");
  if (n == null || !S) { if (box) box.innerHTML = ""; return; }
  if (n === 0) {
    document.querySelectorAll('#rooms .room[data-scope="0"], #liveTree .pt-leaf.prem, #parts .pt-leaf.prem').forEach(el => el.classList.add("scope-sel"));
    const r = $("#liveTree .ptr"); if (r) r.classList.add("hall-sel");
  } else {
    document.querySelectorAll(`#rooms .room[data-scope="${n}"], #liveTree [data-scope="${n}"], #parts [data-scope="${n}"]`).forEach(el => el.classList.add("scope-sel"));
  }
  if (box) box.innerHTML = scopeNoteHTML(n);
}
function asmEntry(name) {
  for (const g of Object.values(S.goals)) { const e = g.ctx.find(c => c.name === name); if (e) return e; }
  return null;
}
function asmFormula(name) { const e = asmEntry(name); return e ? e.f : null; }
const scopeName = e => e.via === "ind" ? __T(2598, [asmNum(e.name)]) : e.via === "cut" ? __T(2742, [asmNum(e.name)]) : e.via === "ex" ? __T(2594, [termH(e.param)]) : (e.via === "or" ? __T(2743) : e.via === "raa" ? __T(2744) : __T(2745)) + asmNum(e.name);
const scopeRule = e => e.via === "ind" ? __T(2746, [scls(asmNum(e.name)), asmNum(e.name)]) : e.via === "ex" ? `∃E<sup class="sc ${scls(asmNum(e.name))}">${asmNum(e.name)}</sup>` : e.via === "raa" ? `RAA<sup class="sc ${scls(asmNum(e.name))}">${asmNum(e.name)}</sup>` : e.via === "or"
  ? `∨E<sup>${e.pair.map(k => `<span class="sc ${scls(k)}">${k}</span>`).join(",")}</sup>`
  : `→I<sup class="sc ${scls(asmNum(e.name))}">${asmNum(e.name)}</sup>`;
function scopeNoteHTML(n) {
  if (n === 0) {
    const ps = S.goals.g0.ctx.map(c => FF(c.f)).join(__T(778));
    return __T(2747, [ps ? __T(2748, [ps]) : __T(2749)]);
  }
  const e = asmEntry("x" + n);
  if (!e) {
    const nb = nameBySid(n);
    if (!nb) return "";
    return __T(2750, [scls(n), termH(nb.n), termH(nb.n), termH(nb.n)]);
  }
  const f = e.f;
  const where = e.via === "ex" ? __T(2751, [scopeRule(e), termH(e.param)]) : e.via === "or"
    ? __T(2752, [scopeRule(e), e.side === "l" ? "2" : "3", e.pair[e.side === "l" ? 1 : 0]])
    : __T(2753, [scopeRule(e)]);
  const here = S.active && S.goals[S.active].ctx.some(c => c.name === "x" + n);
  const used = document.querySelectorAll(`#liveTree .pt-leaf[data-scope="${n}"]`).length;
  return __T(2754, [scls(n), scopeName(e), FF(f), n, where]) +
         (here ? __T(2755) : __T(2756)) +
         (used ? __T(2757, [used]) : __T(2758)) + `</div>`;
}
function statusHTML() {
  if (!S || !S.active) return "";
  if (UI.sel) {
    const e = findEntry(S.goals[S.active], UI.sel);
    if (!e) return "";
    return __T(2759, [FF(e.f)]) + (UI.can.size ? __T(2760) : __T(2761)) + __T(2762);
  }
  return __T(2763);
}
function computeCan(name) {
  const g = S.goals[S.active], e = findEntry(g, name), set = new Set();
  if (!e) return set;
  if (useKind(e.f, g.target)) set.add("door");
  for (const c of g.ctx) if (c.name !== name && (combineResult(e, c, g) || (isEq(e.f) && (countOcc(c.f, e.f.args[0]) || (STAGE.eqBoth && countOcc(c.f, e.f.args[1])))) || (isEq(c.f) && (countOcc(e.f, c.f.args[0]) || (STAGE.eqBoth && countOcc(e.f, c.f.args[1])))))) set.add("k:" + c.name);
  return set;
}
function select(name) {
  UI.sel = name || null;
  UI.can = name ? computeCan(name) : new Set();
  applyHighlight();
}

const openScopes = S => new Set(S.open.flatMap(id => [...S.goals[id].ctx.filter(c => c.kind === "asm").map(c => c.name),
  ...(S.goals[id].names || []).filter(x => x.via === "all").map(x => "@" + x.sid)]));
// 自分で書いた補題の式を読み取って立てる
// 式の入力の読み替え：画面の記号（∀ → など）、TeX のコマンド（\forall \to など）、forall / exists を、内部の書き方に直す
const TEX_IN = [["\\forall", "∀"], ["\\exists", "∃"], ["\\rightarrow", "→"], ["\\implies", "→"], ["\\to", "→"], ["\\land", "∧"], ["\\wedge", "∧"], ["\\lor", "∨"], ["\\vee", "∨"], ["\\lnot", "¬"], ["\\neg", "¬"], ["\\bot", "⊥"], ["\\leq", "≤"], ["\\le", "≤"], ["\\cdot", "·"], ["\\times", "·"], ["\\neq", "≠"], ["\\ne", "≠"], ["\\subseteq", "⊆"], ["\\in", "∈"], ["\\cap", "∩"], ["\\cup", "∪"], ["\\emptyset", "∅"], ["\\varnothing", "∅"]];
function normInput(src) {
  let s = String(src);
  for (const [k, v] of TEX_IN) s = s.split(k).join(v);
  s = s.replace(/\\left|\\right/g, "").replace(/\\[,;:! ]/g, " ").replace(/\^\{?c\}?/g, "ᶜ");
  s = s.replace(/\bforall\b/g, "∀").replace(/\bexists\b/g, "∃");
  s = s.replace(/（/g, "(").replace(/）/g, ")").replace(/＝/g, "=").replace(/[，、]/g, ",").replace(/　/g, " ").replace(/＋/g, "+").replace(/[−－]/g, "-");
  s = s.replace(/([∀∃])\s*([a-z](?:'|′)?)\s*(∈\s*[A-Z][A-Za-z]*)?\s*[.,:]?\s*/g, (m, q, v, mem) => (q === "∀" ? "!" : "?") + v.replace("′", "'") + (mem ? "∈" + mem.replace(/[∈\s]/g, "") : "") + ".");
  return s.replace(/[→⟶⇒]/g, "->").replace(/∧/g, "&").replace(/∨/g, "|").replace(/¬/g, "~").replace(/⊥/g, "#").replace(/≤/g, "<=").replace(/[·×]/g, "*").replace(/′/g, "'");
}
const INPUT_NORM = src => normInput(src);
function submitLemma() {
  const inp = $("#lemmaInput"), src = inp ? inp.value.trim() : "";
  if (!src) { toast(__T(2764), "bad"); return; }
  let L;
  try { L = parse(INPUT_NORM(src)); } catch (e) { toast(__T(2765, [esc(e.message)]), "bad"); return; }
  doAct(S => opCut(S, S.active, L));
}
// ∀E のあと、できた鍵がまだ ∀ で始まっていれば、続けて住人を選ぶ欄を開く（「やめる」で途中の鍵のまま残せる）
function chainAllE(pk) {
  if (!S || pk.kind !== "allE" || $(".overlay")) return;
  const g = S.goals[S.active], last = g && g.ctx[g.ctx.length - 1];
  if (last && last.kind === "der" && last.rule === "∀E" && last.f.t === "all") { UI.pick = { kind: "allE", key: last.name, gid: S.active }; renderDynamic(); }
}
// 選ぶ欄で、自分で書いた項を当てはめる
function submitTerm() {
  const inp = $("#termInput"), src = inp ? inp.value.trim() : "", pk = UI.pick;
  if (!pk) return;
  if (!src) { toast(__T(2766), "bad"); return; }
  let tm;
  try { const f = parse("(" + INPUT_NORM(src) + ") = 0"); tm = f.args[0]; if (typeof tm === "string" && /^[A-Z]$/.test(tm)) throw new Error(__T(2767)); }
  catch (e) { toast(__T(2768, [/文字|character/.test(e.message) ? __T(857, [esc(e.message)]) : ""]), "bad"); return; }
  UI.pick = null;
  if (doAct(S => pickOp(S, pk, tm)) === false) UI.pick = pk; else chainAllE(pk);
}
function rewOp(S, rw, sel) { return rw.mode === "back" ? opRewBack(S, rw.eq, S.active, sel, rw.dir) : opRewFwd(S, rw.eq, rw.tgt, S.active, sel, rw.dir); }
// 書き換えの欄の情報：書き換える式、元の項（from）、置き換える項（to）
function rewInfo(g, rw) {
  const [s1, t1] = findEntry(g, rw.eq).f.args, tgt = rw.mode === "back" ? g.target : findEntry(g, rw.tgt).f;
  const std = rw.dir !== "rev", from = rw.mode === "back" ? (std ? t1 : s1) : (std ? s1 : t1), to = rw.mode === "back" ? (std ? s1 : t1) : (std ? t1 : s1);
  return { tgt, from, to };
}
function doAct(fn) { const r = doAct0(fn); if (r !== false) { wipSave(); deadWatch(); } return r; }
function doAct0(fn) {
  if (GUIDE) guideEnd(true); // 操作を始めたら案内を閉じる
  if (!S || !S.active) return;
  const snap = JSON.stringify(S), before = openScopes(S);
  const keepUI = { orChoice: UI.orChoice, pick: UI.pick, rew: UI.rew, lemma: UI.lemma, match: UI.match }; // 失敗したら、開いていた欄をそのまま戻す
  UI.orChoice = null; UI.pick = null; UI.rew = null; UI.lemma = null; UI.match = null; UI.previewKey = null;
  const r = fn(S);
  UI.sel = null; UI.can = new Set();
  if (!r.ok && r.pick) { UI.rew = { ...r.pick, gid: S.active, sel: Array.from({ length: r.pick.n }, (_, i) => i) }; renderDynamic(); return false; } // 書き換える場所を選ぶ欄を開く
  if (!r.ok && r.matchPick) { UI.match = { ...r.matchPick, gid: S.active }; renderDynamic(); return false; } // 照合：当てはめ方を選ぶ欄を開く
  if (!r.ok) { Object.assign(UI, keepUI); UI.flagName = r.flag || null; toast(r.msg, "bad"); renderProof(S, "normal"); applyHighlight(); setRuleLine(lastRule()); return false; }
  HIST.push(snap); S.ops++; S.log.push(r.log); { const wb = $("#wipBar"); if (wb) wb.remove(); }
  { const used = r.src || r.srcDoor; if (used && !r.noSpend && [__T(785), "∧E", "∃E", "∨E", "=E"].includes(r.log.rule)) { S.spent = Object.assign({}, S.spent); used.forEach(n => { S.spent[n] = true; }); } } // 分解済みの鍵（書き換えに使った等式と、書き換えた元の鍵も含む）
  if (S.alphaNow) { delete S.alphaNow; S.alphaUsed = true; // α 同値で開いたとき：第 7 層と、初めてのときに知らせる
    if (STAGE.world.id === 7 || !(PROG.seen && PROG.seen.alpha)) { setTimeout(() => toast(L1(__T(2769), "Formulas that differ only in the names of bound variables are treated as the same formula (α-equivalence).")), 50); PROG.seen = Object.assign({}, PROG.seen, { alpha: true }); saveProgress(); } }
  UI.fresh = new Set(r.fresh || []); UI.fx = true; UI.just = true; UI.previewKey = null; UI.flagName = null;
  UI.previewHold = UI.ptr ? { x: UI.ptr.x, y: UI.ptr.y } : null; // 成功した直後は、ポインターが離れるまで下見をしない（成功の表示を保つ）
  if ((r.src && r.fresh) || r.srcDoor) { // 使った鍵から、できた鍵（または書き換わった扉）への導線を一度だけ描く
    const until = Date.now() + 1800; UI.flow = r.srcDoor ? { src: r.srcDoor, door: true, until } : { src: r.src, dst: r.fresh, until };
    setTimeout(() => { if (UI.flow && UI.flow.until === until) { UI.flow = null; drawKeyLinks(); } }, 1900); }
  renderDynamic();
  setRuleLine(lastRule(), true);
  if (S.open.length === 0) { setTimeout(complete, 420); return; }
  const after = openScopes(S), closed = [...before].filter(x => !after.has(x));
  if (closed.length) {
    toast(closed.map(x => { const e = asmEntry(x), k = x.slice(1);
      if (!e) { const nb = nameBySid(+x.slice(1)); return nb ? __T(2770, [termH(nb.n), termH(nb.n)]) : ""; }
      if (e.via === "ex") return __T(2771, [termH(e.param), FF(e.f), k, k, termH(e.param)]);
      if (e.via === "ind") return __T(2772, [k, FF(e.f), k, termH(e.param)]);
      if (e.via === "cut") return __T(2773, [k, FF(e.f), k]);
      if (e.via === "raa") return __T(2774, [k, FF(e.f), k, k, FF(e.concl)]);
      return e.via === "or"
        ? __T(2775, [k, FF(e.f), k, e.pair.join(",")])
        : __T(2776, [k, FF(e.f), k, k]); }).join("<br>"));
    if (UI.scope == null) { // 出た部屋の範囲を一瞬だけ強調して、どこで仮定が解除されたかを見せる
      const n = asmNum(closed[0]);
      UI.scope = n; UI.autoScope = true; applyScope();
      clearTimeout(UI.autoTimer);
      UI.autoTimer = setTimeout(() => { if (UI.autoScope && UI.scope === n) { UI.scope = null; UI.autoScope = false; if (S) applyScope(); } }, 2600);
    }
  }
}
function undo() {
  if (!HIST.length) return;
  S = JSON.parse(HIST.pop()); UI.sel = null; UI.can = new Set(); UI.fx = true; UI.orChoice = null; UI.pick = null;
  if (autoDeadOn() && !S.open.some(id => goalDead(S.goals[id]))) { UI.deadAlert = null; UI.deadSeen = new Set(); UI.deadMoves = 0; } // 行き止まりを抜けたら知らせを消す
  renderDynamic(); wipSave();
}
/* 途中保存：証明のステージで、操作のたびに盤面（と直近の「戻す」の履歴）を保存し、次に開いたとき「続きから」を選べるようにする */
const WIP_KEY = "proof-dungeon:wip";
const wipSig = st => st.prem.join("|") + "⊢" + st.goal; // 問題が変わっていたら使わない
const wipLoad = () => { try { return JSON.parse(localStorage.getItem(WIP_KEY)) || {}; } catch (e) { return {}; } };
const wipStore = m => { try { localStorage.setItem(WIP_KEY, JSON.stringify(m)); } catch (e) { /* 容量が足りないときは保存しない */ } };
const wipable = () => !!(S && STAGE && PROB === STAGE && !STAGE.kind && UI.mode === "prove");
function wipSave() {
  if (!wipable()) return;
  const m = wipLoad();
  if (S.ops > 0 && S.open.length) m[STAGE.pid] = { sig: wipSig(STAGE), S, H: HIST.slice(-40), t: Date.now() }; else delete m[STAGE.pid]; // 解き終えた盤面は残さない
  const ks = Object.keys(m).sort((a, b) => m[b].t - m[a].t); ks.slice(6).forEach(k => delete m[k]); // 新しい 6 ステージ分だけ
  wipStore(m);
}
function wipDrop(pid) { const m = wipLoad(); if (m[pid]) { delete m[pid]; wipStore(m); } }
function wipOffer() {
  const old = $("#wipBar"); if (old) old.remove();
  if (!wipable() || S.ops > 0) return;
  const w = wipLoad()[STAGE.pid]; if (!w || w.sig !== wipSig(STAGE) || !w.S || !w.S.ops) return;
  const area = $("#area"), rooms = $("#rooms"); if (!area || !rooms) return;
  rooms.insertAdjacentHTML("beforebegin", `<div class="wip-bar" id="wipBar" role="status"><span>${L1(__T(2777, [w.S.ops]), `Your previous attempt (up to move ${w.S.ops}) is saved.`)}</span><button type="button" class="btn small primary" data-wip="resume">${L1(__T(2778), "Resume")}</button><button type="button" class="btn small" data-wip="drop">${L1(__T(2779), "Start over")}</button></div>`);
}
function wipResume() {
  const w = wipLoad()[STAGE.pid], bar = $("#wipBar"); if (bar) bar.remove();
  if (!w || w.sig !== wipSig(STAGE)) return;
  S = w.S; HIST = w.H || []; UI.sel = null; UI.can = new Set(); UI.fx = true; UI.orChoice = null; UI.pick = null;
  renderDynamic(); toast(L1(__T(2780, [S.ops]), `Resumed from your previous attempt (move ${S.ops}).`));
}
function tapKey(name) {
  if (!UI.sel) return select(name);
  if (UI.sel === name) return select(null);
  if (UI.can.has("k:" + name)) { const a = UI.sel; return doAct(S => opCombine(S, a, name, S.active)); }
  select(name);
}
function tapDoor() {
  if (UI.sel) { const a = UI.sel; return doAct(S => opUse(S, a, S.active)); }
  const t = S.goals[S.active].target;
  if (t.t === "all" || t.t === "ex") { toast(__T(2781, [QS[t.t]])); return; }
  toast(t.t === "bot" ? __T(2782)
      : t.t === "atom" ? __T(2783)
      : t.t === "or" ? __T(2784)
      : __T(2785, [OP[t.t]]));
}

/* 証明の再生：手の順に、証明図が育っていく様子と、操作と推論規則の対応を見せる */
let RP = null;
// k 手目までに作られた部分だけを残し、まだの部分は ⋮ にする。k 手目で見えるようになった部分には op = k を付けて強調する
function prunePT(n, k, maxOp = 0) {
  if (n.hole) return n;
  const m = Math.max(maxOp, n.op || 0);
  if (n.op != null && n.op > k) return { hole: true, f: n.f, id: "rp", tmCut: n.tm };
  const shown = m === k && k > 0 ? { ...n, op: k } : { ...n, op: n.op != null ? Math.min(n.op, k - 1) : n.op };
  if (n.leaf) return shown;
  return { ...shown, kids: n.kids.map(c => prunePT(c, k, m)) };
}
// 計算の流れ。等号の書き換えの連なりを集め、等式の扉なら、左辺の移り変わり → 一致した式 → 右辺の移り変わり（逆順）とつないで、前から読める等式の計算にする
function calcChains(rt) {
  const chains = [], seen = new Set();
  const walk = (t, lab) => {
    if (!t || typeof t !== "object" || seen.has(t)) return; seen.add(t);
    if (t.k === "ind") { walk(t.base, L1(__T(2786), "Base")); walk(t.step, L1(__T(2787), "Step")); return; }
    if (t.k === "rew") { const steps = []; let cur = t;
      while (cur && cur.k === "rew") { steps.push({ from: cur.ty, to: cur.p.ty, eq: cur.a && cur.a.ty }); seen.add(cur); cur = cur.p; }
      chains.push({ lab, steps, end: cur }); walk(cur, lab); return; }
    for (const [k, v] of Object.entries(t)) if (k !== "ty" && v && typeof v === "object") { if (Array.isArray(v)) v.forEach(x => walk(x, lab)); else walk(v, lab); }
  };
  walk(rt, null);
  return chains.filter(c => c.steps.length >= 1);
}
function calcFlowHTML(rt) {
  let chains; try { chains = calcChains(rt); } catch (e) { return ""; }
  if (!chains.length || chains.reduce((a, c) => a + c.steps.length, 0) < 2) return "";
  const isE = f => f && f.t === "atom" && f.n === "=" && f.args && f.args.length === 2;
  const op = by => `<span class="cf-op"><span class="cf-eqs">=</span><span class="cf-by">${by ? FF(by) : ""}</span></span>`;
  const rows = chains.map(c => {
    const head = c.lab ? `<span class="cf-lab">${c.lab}</span>` : "";
    if (c.steps.every(st => isE(st.from) && isE(st.to))) { // 等式の扉：一行の計算
      const L = [{ t: c.steps[0].from.args[0] }], Rr = [{ t: c.steps[0].from.args[1] }];
      for (const st of c.steps) { if (!termEq(st.from.args[0], st.to.args[0])) L.push({ t: st.to.args[0], by: st.eq }); if (!termEq(st.from.args[1], st.to.args[1])) Rr.push({ t: st.to.args[1], by: st.eq }); }
      const lastL = L[L.length - 1].t, lastR = Rr[Rr.length - 1].t, endKey = c.end && c.end.k !== "refl" && !termEq(lastL, lastR) ? c.end.ty : null;
      let html = `<span class="cf-t">${termH(L[0].t)}</span>`;
      for (let i = 1; i < L.length; i++) html += op(L[i].by) + `<span class="cf-t">${termH(L[i].t)}</span>`;
      if (endKey) html += op(endKey) + `<span class="cf-t">${termH(lastR)}</span>`;
      for (let i = Rr.length - 1; i > 0; i--) html += op(Rr[i].by) + `<span class="cf-t">${termH(Rr[i - 1].t)}</span>`;
      return `<div class="cf-chain">${head}<div class="cf-row">${html}</div></div>`;
    }
    return `<div class="cf-chain">${head}<div class="cf-row cf-seq">${[`<span class="cf-t">${FF(c.steps[0].from)}</span>`, ...c.steps.map(st => `<span class="cf-arrow">⟸<span class="cf-by">${st.eq ? FF(st.eq) : ""}</span></span><span class="cf-t">${FF(st.to)}</span>`)].join("")}</div></div>`;
  });
  return `<div class="calc-flow"><h3>${L1(__T(2788), "The flow of the calculation")}</h3><p class="note">${L1(__T(2789), "The rewrites are arranged as an equational calculation read from the front. Under each \"=\" is the equation used.")}</p>${rows.join("")}</div>`;
}
function calcFlowInsert(rt) { const st = $(".overlay #rpStep"); const h = calcFlowHTML(rt); if (st && h && !$(".overlay .calc-flow")) st.insertAdjacentHTML("afterend", h); }
function ptFitApply() { // クリア画面の証明図：「全体を表示」なら、欄の幅に収まるまで縮める（等倍の 50% まで）
  const tree = $("#rpTree"); if (!tree) return;
  tree.style.zoom = ""; const w = tree.parentElement;
  if (PREFS.ptFit && w) { const need = tree.scrollWidth, avail = w.clientWidth - 20; if (need > avail) tree.style.zoom = String(Math.max(0.5, avail / need)); }
  const fb = $("#ptFitBtn"); if (fb) { fb.setAttribute("aria-pressed", String(!!PREFS.ptFit)); fb.textContent = PREFS.ptFit ? L1(__T(2790), "Actual size") : L1(__T(2791), "Fit the whole tree"); }
}
function ptFitTools() { const pw = $(".overlay #rpTree"); if (pw && !$(".overlay .pt-tools")) pw.parentElement.insertAdjacentHTML("beforebegin", `<div class="pt-tools"><button type="button" class="btn small" id="ptFitBtn" data-ptfit aria-pressed="${!!PREFS.ptFit}">${PREFS.ptFit ? L1(__T(2790), "Actual size") : L1(__T(2791), "Fit the whole tree")}</button></div>`); ptFitApply(); }
function rpRender() {
  if (!RP) return;
  const tree = $("#rpTree"), step = $("#rpStep"), cnt = $("#rpCount");
  if (!tree) { rpStop(); return; }
  const done = RP.k > RP.n, k = Math.min(RP.k, RP.n);
  const pt = prunePT(RP.tree, k);
  tree.innerHTML = renderPT(pt, leanCX(termCX(pt, { ...STATIC_CX, latest: done ? 0 : k })));
  ptFitApply();
  const lb = $("#rpLean"); if (lb && RP.lean) lb.innerHTML = leanCodeHTML(done ? RP.lean : pruneTerm(RP.lean, k), { latest: done ? 0 : k });
  const l = RP.log[k - 1];
  step.innerHTML = done ? __T(2792, [RP.n])
    : RP.k === 0 ? __T(2793, [FF(RP.goal)])
    : __T(2794, [RP.k, RD(l.rule), RULE_NAMES[l.rule] || "", l.text, l.fig ? __T(2795, [l.fig]) : ""]);
  cnt.textContent = done ? __T(2796, [RP.n, RP.n]) : __T(2797, [RP.k, RP.n]);
  document.querySelectorAll(".overlay .log li").forEach((li, i) => li.classList.toggle("on", !done && i === RP.k - 1));
  const pb = $("#rpPlay"); if (pb) pb.textContent = RP.timer ? __T(2798) : done ? __T(2799) : __T(2800);
}
function rpStop() { if (RP && RP.timer) { clearInterval(RP.timer); RP.timer = null; } }
function rpPlay() {
  if (!RP) return;
  if (RP.timer) { rpStop(); rpRender(); return; }
  if (RP.k > RP.n) RP.k = 0;
  RP.timer = setInterval(() => { if (!RP || !$("#rpTree")) { rpStop(); return; } RP.k++; if (RP.k > RP.n) rpStop(); rpRender(); }, RP.speed);
  rpRender();
}
function rpCmd(c) {
  if (!RP) return;
  if (c === "play") return rpPlay();
  rpStop();
  if (c === "first") RP.k = 0; else if (c === "last") RP.k = RP.n + 1; else if (c === "prev") RP.k = Math.max(0, Math.min(RP.k, RP.n + 1) - 1); else if (c === "next") RP.k = Math.min(RP.n + 1, RP.k + 1);
  else if (c === "auto") { PREFS.replayAuto = !PREFS.replayAuto; savePrefs(); const b = $("#rpAuto"); if (b) b.setAttribute("aria-pressed", String(!!PREFS.replayAuto)); }
  rpRender();
}
function complete() {
  if (!S || S.open.length) return;
  const st = STAGE, t = inline(rootTerm(S));
  let ok = false, err = "";
  try {
    const env = new Map(S.goals.g0.ctx.map(c => [c.name, c.f]));
    ok = eq(infer(t, env), parse(PROB.goal));
    if (!ok) err = __T(2801);
  } catch (x) { err = x.message; }
  if (!ok) { // 検査に失敗した証明は、クリアにしない（記録もカードも残さない）。どこが問題かを示して、戻して直せるようにする
    showModal(`<h2>${L1(__T(2802), "The check failed")}</h2>
      <p>${L1(__T(2803), "Every door is open, but checking the assembled proof found a step that breaks a condition of the inference rules. This does not count as a clear.")}</p>
      <p class="check ng">${L1(__T(2804), "Result of the check: ")}${esc(err)}</p>
      <p class="note">${L1(__T(2805), "Use Undo to step back and redo the problem move. For example, if the name of an arbitrary resident occurs in a hypothesis, the eigenvariable condition is broken.")}</p>
      <div class="modal-actions"><button type="button" class="btn primary" data-cmd="close">${L1(__T(2806), "Close, then undo and fix")}</button><button type="button" class="btn" data-cmd="map">${L1(__T(2487), "Stage list")}</button></div>`);
    return;
  }
  if (ok && st.kind === "judge") { judgePartSolved("proved"); return; }
  const newCard = !!(ok && st.earns && !cardGot(st.earns));
  if (ok && st.earns) { PROG.cards = PROG.cards || {}; PROG.cards[st.earns] = true; }
  if (ok) {
    const prev = PROG.best[st.pid];
    if (prev == null || S.ops < prev) PROG.best[st.pid] = S.ops;
    saveProgress(); wipDrop(st.pid); // クリアしたら、途中保存は消す
    proofSave(st); // 証明を見返せるように保存（いちばん少ない手数のもの）
    const bm = $("#bestMeta"); if (bm) bm.textContent = bestText(st);
  }
  let treeHTML = "", fullTree = null;
  try { fullTree = buildPT(leanOn() ? (() => { const rt = rootTerm(S); markFwd(rt); return inline(rt); })() : t); treeHTML = renderPT(fullTree, leanCX(termCX(fullTree, STATIC_CX))); } catch (x) { treeHTML = esc(x.message); }
  const reduce = !!(window.matchMedia && window.matchMedia("(prefers-reduced-motion: reduce)").matches), auto = !!PREFS.replayAuto && !reduce && !!fullTree;
  const ctx = S.goals.g0.ctx.map(c => `${nm(c.name)} : ${FF(c.f)}`).join(", ");
  const i = STAGES.indexOf(st), hasNext = i < STAGES.length - 1;
  showModal(__T(2807, [storyOn() && storyStage(st) ? `<div class="story-done">${storyStage(st).d}</div>` : "", inscrHTML(st), st.id, st.name, st.world.id === 1 ? __T(2808) : "", S.ops, st.par, S.ops <= st.par ? __T(2349) : UI.wasCleared ? __T(2809, [S.ops - st.par]) : `<span class="par first">${L1(__T(2810), "Cleared! You can try for the par on another run")}</span>`, st.classical ? __T(2811, [countRAA(t)]) + (st.premClassical ? `<span class="par cl-prem">${st.premClassical === "lem" ? L1(__T(2812), "(but a premise key contains the excluded middle)") : L1(__T(2813), "(but a premise key contains double-negation elimination)")}</span>` : "") : "", st.doneNote ? `<div class="done-note">${st.doneNote}</div>` : "", ok && st.earns ? cardGetHTML(st, newCard) : "", (() => { const used = [...varsOf(t)].filter(v => v[0] === "c").map(v => S.goals.g0.ctx.find(c => c.name === v)).filter(Boolean); return used.length ? __T(2814, [used.map(c => CARDS[c.card].name).join(__T(778))]) : ""; })(), fullTree ? __T(2815, [!!PREFS.replayAuto]) : "", treeHTML, (fullTree ? `<div class="rp-step" id="rpStep" aria-live="polite"></div>` : "") + leanClearHTML(), PREFS.showTerm ? __T(2816) : "", PREFS.showTerm ? __T(2817, [tstr(t, 0, {}, null)]) : "", ok ? "" : " ng", ok
      ? (PREFS.showTerm ? __T(2818, [ctx ? ctx + " " : "", F(PROB.goal)]) : __T(2819, [PROB.prem.map(p => F(p)).join(", "), PROB.prem.length ? " " : "", F(PROB.goal)]))
      : __T(2820) + esc(err), S.log.map((l, i) => __T(2821, [i + 1, RD(l.rule), l.text])).join(""), hasNext ? __T(2320) : __T(2321)]), false);
  if (st.specNote) { const sc = $(".overlay .score"); if (sc) sc.insertAdjacentHTML("afterend", `<p class="note spec-note">${st.specNote}</p>`); } // ゲームの仕組みについての一言は、小さな注として
  ptFitTools(); // 証明図の「全体を表示」
  if (ok) calcFlowInsert(inline(rootTerm(S))); // 計算の流れ
  if (ok && st.pid === "15-inf") towerInsert("open"); // S3-6：天井の消える塔
  if (ok && /"k":"ind"/.test(JSON.stringify(rootTerm(S)))) { const ck = $(".overlay p.check"); if (ck) ck.insertAdjacentHTML("beforeend", `<span class="chk-ind">${L1(__T(2822), " (a proof in a theory with mathematical induction)")}</span>`); }
  if (ok && S.alphaUsed && st.pid === "f-rename") { const sc = $(".overlay .score"); if (sc) sc.insertAdjacentHTML("afterend", `<div class="done-note">${L1(__T(2823, [F("!x.P(x)"), F("!y.P(y)")]), `You inserted the key ${F("!x.P(x)")} directly into the door ${F("!y.P(y)")}. Formulas that differ only in the names of bound variables are treated as the same formula (α-equivalence). That is why it opened without bringing in a resident.`)}</div>`); }
  if (!hasNext && ok) toast(__T(2583));
  rpStop();
  RP = fullTree ? { tree: fullTree, lean: rootTerm(S), log: S.log.slice(), n: S.log.length, k: auto ? 0 : S.log.length + 1, timer: null, speed: 1100, goal: parse(PROB.goal) } : null;
  if (RP) { rpRender(); if (auto) setTimeout(() => { if (RP && !RP.timer && RP.k === 0) rpPlay(); }, 600); }
  if (ok && st.world.id === 1 && !(PROG.guideSeen || {}).clear) setTimeout(() => { if ($(".overlay .score")) guideStart(["clear"]); }, 500); // 初めてのクリアでは、クリア画面の見方を案内する
}

/* ================= チュートリアル（動きで見せる操作の説明） =================
   各ステップは「見本の画面（HTML）」と「台本（カーソルの移動・ホバー・クリック・ドラッグと、その結果）」でできている */
const TK = (t, f, cls = "") => `<div class="key ${cls}" data-t="${t}"><span class="f">${f}</span></div>`;
const TD = (t, f, extra = "") => __T(2824, [t, ICON.swing, f, extra]);
// 真偽の図（「図で見る」と同じ形の小さな版）。val(f) は 真 true／偽 false／未定 null、dom は ∀・∃ の枝分かれに使う住人、depth は描く深さ
const TGV = (s, val, dom = null, depth = 9) => { const node = (f, d) => { const v = val(f), ks = d < depth ? evKids(f, dom) : [];
  return `<li><div class="tg-node ${TVC(v)}"><span class="tg-f f">${fh(f)}</span><span class="tg-v">${TVL(v)}</span></div>${ks.length ? `<ul>${ks.map(k => node(k.f, d + 1)).join("")}</ul>` : ""}</li>`; };
  return `<div class="tut-tg"><ul class="tg">${node(parse(s), 0)}</ul></div>`; };
const TV3 = m => f => { const go = g => g.t === "atom" ? (m[g.n] === undefined ? null : m[g.n]) : g.t === "bot" ? false : g.t === "and" ? K3and(go(g.l), go(g.r)) : g.t === "or" ? K3or(go(g.l), go(g.r)) : g.t === "imp" ? K3imp(go(g.l), go(g.r)) : null; return go(f); };
const TVS = st => f => evalS3({ n: 2, rel: {}, relF: {}, fun: {}, con: {}, ...st }, f);
const TLAMP = (t, label, st = "unk") => `<span class="lamp ${st === "unk" ? "unk" : st === "T" ? "on" : "no"}" data-t="${t}">${label}<span class="tv" data-t="${t}v">${st === "unk" ? __T(891) : st === "T" ? __T(876) : __T(877)}</span></span>`;
// 台本：ボタンを押して 未定 → 偽、偽 → 真 にする
const TPRESS = (t, to) => [{ move: t }, { click: 1 }, { cls: [t, "unk", false] }, { cls: [t, "no", to === "F"] }, { cls: [t, "on", to === "T"] }, { html: [t + "v", to === "T" ? __T(876) : __T(877)] }];
const TH = (s, on) => `<span class="pt-hole${on ? " on" : ""}"><span class="pt-dots"></span><span class="pt-goal">${F(s)}</span></span>`;
const TL = s => `<div class="pt-leaf">${F(s)}</div>`;
const TLE = s => `<div class="pt-leaf">${FE(s)}</div>`;
const TN = (rule, kids, s, cls = "new", rcls = "") => `<div class="pt-node ${cls}"><div class="pt-prems">${kids.join("")}</div><div class="pt-bar"><span class="pt-rule ${rcls}">${rule}</span></div><div class="pt-concl">${F(s)}</div></div>`;
const TSC = (k, inner, amb = true) => `<div class="pt-scope s${k}${amb ? " amb" : ""}">${inner}</div>`;
const TOP = (s, t) => fhTop(parse(s), `data-t="${t}"`);
const TPR = inner => `<div class="ptr">${inner}</div>`;
const SC = (plan, proof) => `<div class="tut-plan" data-t="plan">${plan}</div><div class="tut-proof" data-t="proof">${TPR(proof)}</div>`;
const ROOM = (k, name, keys, door) => __T(2825, [k, k, k, k, name, keys, door]);
const RES = (n, k = 1) => __T(2826, [k, ICON.person, termH(n)]);
const PICK = (q, btns) => `<div class="orpick"><div class="orpick-q">${q}</div><div class="orpick-btns">${btns}</div></div>`;
const EVR = (s, v) => `<div class="tut-evrow"><span class="f">${F(s)}</span><b>${v}</b></div>`;
const KF = (lab, add) => __T(2827, [lab, lab, lab, add ? __T(2828) : ""]);
const KEYS = (...k) => `<div class="tut-keys" data-t="keys">${k.join("")}</div>`;
// クリプキモデルのチュートリアル用：階のカード（lamps は [原子命題, "on"|"inh"|""] の並び）、塔、計算の行
const KFL = (lab, lamps, o = {}) => __T(2829, [o.cex ? " cex" : "", o.sel ? " sel" : "", lab, lab, o.root ? __T(2102) : "", o.cex ? __T(2103) : ""]) +
  `<div class="lamps">${lamps.map(([a, st]) => `<span class="lamp${st ? " on" : ""}${st === "inh" ? " inh" : ""}" data-t="l${lab}${a}"><i class="at">${a}</i></span>`).join("")}</div>` +
  (o.add ? __T(2830, [lab]) : "") + `</div>`;
const TWR = (...rows) => `<div class="tut-kcol">${rows.map(r => Array.isArray(r) ? `<div class="tut-krow">${r.join("")}</div>` : r).join(`<div class="tut-stair">↑</div>`)}</div>`;
const EVK = (lab, s, v, note = "") => __T(2831, [lab, F(s), v ? "kt" : "kf", v ? __T(893) : __T(894), note ? `<span class="tut-evnote">${note}</span>` : ""]);
const TXR = (a, b) => `<div class="tut-evrow"><span>${a}</span><b>${b}</b></div>`;
const KPANEL = (...rows) => `<div class="tut-proof tut-ev" data-t="proof">${rows.join("")}</div>`;
const KPLAN = inner => `<div class="tut-plan" data-t="plan">${inner}</div>`;

// チュートリアル「第三の道」：17-5 をクリアする前は、道が閉ざされるところまで（第三の道そのものは見せない）
const TW_TEASER = { title: __T(709), steps: [
    { h: __T(1950), text: __T(2832),
      html: KPLAN(__T(2833)) + KPANEL(TXR(__T(2834), __T(2835)), TXR(__T(2836), "……")),
      script: [{ cap: __T(2837) }, { move: "bA" }, { click: 1 }, { html: ["rA", __T(2838)] }, { cls: ["cA", "closed"] }, { move: "bN" }, { click: 1 }, { html: ["rN", __T(2838)] }, { cls: ["cN", "closed"] }, { wait: 400 }, { cap: __T(2839) }, { wait: 2200 }] },
  ]};
const TW_FULL = { title: __T(709), steps: [
    { h: __T(2840), text: __T(2841),
      html: KPLAN(__T(2842)) + KPANEL(TXR(__T(2834), __T(2835)), TXR(__T(2836), __T(2843))),
      script: [{ cap: __T(2837) }, { move: "bA" }, { click: 1 }, { html: ["rA", __T(2838)] }, { cls: ["cA", "closed"] }, { move: "bN" }, { click: 1 }, { html: ["rN", __T(2838)] }, { cls: ["cN", "closed"] }, { wait: 500 },
               { html: ["mid", __T(2844)] }, { cap: __T(709) }, { move: "go" }, { click: 1 }, { wait: 1800 }] },
  ]};
const TUTORIALS = {
  basics: { title: __T(2845), steps: [
    { h: __T(2846), text: __T(2847),
      html: SC(KEYS(TK("kP", F("P")), TK("kQ", F("Q"))) + `<div data-t="doors">${TD("door", TOP("P&Q", "dop"))}</div>`, TH("P&Q", true)),
      script: [{ cap: __T(2848) }, { move: "dop" }, { hover: "dop" }, { html: ["proof", TPR(TN("∧I", [TH("P"), TH("Q")], "P&Q"))] }, { cls: ["proof", "pv"] }, { wait: 1300 },
               { cap: __T(2849) }, { click: 1 }, { unhover: "dop" }, { cls: ["proof", "pv", false] }, { html: ["doors", `<div class="tut-doors">${TD("dP", F("P"))}${TD("dQ", F("Q"))}</div>`] }, { wait: 1500 }] },
    { h: __T(2850), text: __T(2851),
      html: SC(KEYS(TK("kP", F("P")), TK("kQ", F("Q"))) + `<div class="tut-doors">${TD("dP", F("P"))}${TD("dQ", F("Q"))}</div>`, TN("∧I", [TH("P", true), TH("Q")], "P&Q", "")),
      script: [{ cap: __T(2852) }, { move: "kP" }, { drag: ["kP", "dP"] }, { cls: ["dP", "tut-ok"] }, { html: ["proof", TPR(TN("∧I", [TL("P"), TH("Q", true)], "P&Q", ""))] }, { wait: 600 },
               { move: "kQ" }, { drag: ["kQ", "dQ"] }, { cls: ["dQ", "tut-ok"] }, { html: ["proof", TPR(TN("∧I", [TL("P"), TL("Q")], "P&Q", ""))] }, { cap: __T(2853) }, { wait: 1500 }] },
    { h: __T(2854), text: __T(2855),
      html: SC(KEYS(TK("kP", F("P")), TK("kQ", F("Q"))) + `<div class="tut-doors">${TD("dP", F("P"))}${TD("dQ", F("Q"))}</div>`, TN("∧I", [TH("P", true), TH("Q")], "P&Q", "")),
      script: [{ cap: __T(2856) }, { move: "kP" }, { click: 1 }, { cls: ["kP", "sel"] }, { cls: ["dP", "can"] }, { wait: 900 },
               { cap: __T(2857) }, { move: "dP" }, { click: 1 }, { cls: ["kP", "sel", false] }, { cls: ["dP", "can", false] }, { cls: ["dP", "tut-ok"] }, { html: ["proof", TPR(TN("∧I", [TL("P"), TH("Q", true)], "P&Q", ""))] }, { wait: 1400 }] },
  ]},
  andE: { title: __T(2858), steps: [
    { h: __T(2859), text: __T(2860),
      html: SC(KEYS(TK("kPQ", TOP("P&Q", "kop"))) + TD("door", F("Q&P")), TH("Q&P", true)),
      script: [{ cap: __T(2849) }, { move: "kop" }, { hover: "kop" }, { wait: 500 }, { click: 1 }, { unhover: "kop" },
               { html: ["keys", TK("kPQ", F("P&Q")) + TK("kP", F("P"), "der") + TK("kQ", F("Q"), "der")] },
               { html: ["proof", TPR(TH("Q&P", true)) + `<div class="tut-parts">${TPR(TN("∧E", [TL("P&Q")], "P"))}${TPR(TN("∧E", [TL("P&Q")], "Q"))}</div>`] }, { wait: 1800 }] },
  ]},
  impI: { title: __T(2861), steps: [
    { h: __T(2862), text: __T(2863),
      html: SC(`<div data-t="area">${TD("door", TOP("A->B", "dop"))}</div>`, TH("A->B", true)),
      script: [{ cap: __T(2849) }, { move: "dop" }, { hover: "dop" }, { wait: 400 }, { click: 1 },
               { html: ["area", ROOM(1, __T(2864), TK("kA", F("A"), "asm s1"), TD("door", F("B")))] },
               { html: ["proof", TPR(TN(`→I<sup class="sc s1">1</sup>`, [TSC(1, TH("B", true))], "A->B"))] }, { cap: __T(2865) }, { wait: 1800 }] },
  ]},
  impE: { title: __T(2866), steps: [
    { h: __T(2867), text: __T(2868),
      html: SC(KEYS(TK("kP", F("P")), TK("kPQ", F("P->Q"))) + TD("door", F("Q")), TH("Q", true)),
      script: [{ cap: __T(2852) }, { move: "kP" }, { drag: ["kP", "kPQ"] }, { html: ["keys", TK("kP", F("P")) + TK("kPQ", F("P->Q")) + TK("kQ", F("Q"), "der")] },
               { html: ["proof", TPR(TH("Q", true)) + `<div class="tut-parts">${TPR(TN("→E", [TL("P->Q"), TL("P")], "Q"))}</div>`] }, { wait: 1700 }] },
    { h: __T(2869), text: __T(2870),
      html: SC(KEYS(TK("kP", F("P")), TK("kPQ", F("P->Q"))) + TD("door", F("Q")), TH("Q", true)),
      script: [{ cap: __T(2852) }, { move: "kPQ" }, { drag: ["kPQ", "door"] }, { html: ["door", `<div class="door-f f">${F("P")}</div>`] },
               { html: ["proof", TPR(TN("→E", [TL("P->Q"), TH("P", true)], "Q"))] }, { wait: 1700 }] },
  ]},
  scope: { title: __T(2871), steps: [
    { h: __T(2872), text: __T(2873),
      html: SC(ROOM(1, __T(2864), TK("kP", F("P"), "asm s1"), TD("door", F("P"))), TN(`→I<sup class="sc s1">1</sup>`, [`<div class="pt-scope s1 amb" data-t="sreg">${TH("P", true)}</div>`], "P->P", "")),
      script: [{ cap: __T(2849) }, { move: "rp1" }, { click: 1 }, { cls: ["sreg", "scope-sel"] }, { cls: ["room1", "scope-sel"] }, { cap: __T(2874) }, { wait: 2000 }] },
  ]},
  orI: { title: __T(2875), steps: [
    { h: __T(2876), text: __T(2877),
      html: SC(KEYS(TK("kP", F("P"))) + `<div data-t="area">${TD("door", TOP("P|Q", "dop"))}</div>`, TH("P|Q", true)),
      script: [{ cap: __T(2849) }, { move: "dop" }, { click: 1 },
               { html: ["area", TD("door", F("P|Q"), PICK(__T(2878), __T(2879, [F("P"), F("Q")])))] }, { wait: 600 },
               { cap: __T(2880) }, { move: "left" }, { click: 1 }, { html: ["area", TD("door", F("P"))] }, { html: ["proof", TPR(TN("∨I", [TH("P", true)], "P|Q"))] }, { wait: 1600 }] },
  ]},
  orE: { title: __T(2881), steps: [
    { h: __T(2882), text: __T(2883),
      html: SC(`<div data-t="area">${KEYS(TK("kPQ", TOP("P|Q", "kop")))}${TD("door", F("R"))}</div>`, TH("R", true)),
      script: [{ cap: __T(2849) }, { move: "kop" }, { click: 1 },
               { html: ["area", __T(2884, [F("P|Q"), F("P"), F("Q"), TK("kP", F("P"), "asm s1"), TD("door", F("R"))])] },
               { html: ["proof", TPR(TN(`∨E<sup><span class="sc s1">1</span>,<span class="sc s2">2</span></sup>`, [TL("P|Q"), TSC(1, TH("R", true)), TSC(2, TH("R"), false)], "R"))] }, { wait: 2000 }] },
  ]},
  lantern: { title: __T(2885), steps: [
    { h: __T(2886), text: __T(2887),
      html: SC(__T(2888, [ICON.lantern, TD("d1", F("P")), TD("d2", F("Q"))]), TN("∧I", [TH("P", true), TH("Q")], "P&Q", "")),
      script: [{ cap: __T(2889) }, { move: "lan" }, { click: 1 }, { html: ["doors", TD("d1", F("P"), __T(2890)) + TD("d2", F("Q"), __T(2891))] }, { wait: 2000 }] },
  ]},
  bot: { title: __T(2892), steps: [
    { h: __T(2893), text: __T(2894),
      html: SC(KEYS(TK("kP", FE("P")), TK("kPB", FE("P->#"))) + TD("door", F("Q")), TH("Q", true)),
      script: [{ cap: __T(2852) }, { move: "kP" }, { drag: ["kP", "kPB"] }, { html: ["keys", TK("kP", FE("P")) + TK("kPB", FE("P->#")) + TK("kB", F("#"), "der botkey")] }, { wait: 700 },
               { cap: __T(2895) }, { move: "kB" }, { drag: ["kB", "door"] }, { cls: ["door", "tut-ok"] },
               { html: ["proof", TPR(`<div class="pt-node new"><div class="pt-prems"><div class="pt-node"><div class="pt-prems">${TLE("P->#")}${TLE("P")}</div><div class="pt-bar"><span class="pt-rule">→E</span></div><div class="pt-concl">${F("#")}</div></div></div><div class="pt-bar"><span class="pt-rule">⊥E</span></div><div class="pt-concl">${F("Q")}</div></div>`)] }, { wait: 1700 }] },
    { h: __T(2896), text: __T(2897),
      html: SC(KEYS(TK("kP", FE("P")), TK("kPB", FE("P->#"))) + `<div data-t="area">${TD("door", F("Q"), __T(2898))}</div>`, TH("Q", true)),
      script: [{ cap: __T(2889) }, { move: "exf" }, { click: 1 }, { html: ["area", TD("door", F("#"))] }, { html: ["proof", TPR(TN("⊥E", [TH("#", true)], "Q"))] }, { wait: 1700 }] },
  ]},
  neg: { title: __T(1871), steps: [
    { h: __T(2899), text: __T(2900),
      html: SC(`<div data-t="area">${TD("door", TOP("~P", "dop"))}</div>`, TH("~P", true)),
      script: [{ cap: __T(2849) }, { move: "dop" }, { click: 1 }, { html: ["area", ROOM(1, __T(2864), TK("kP", F("P"), "asm s1"), TD("door", F("#")))] },
               { html: ["proof", TPR(TN(`→I<sup class="sc s1">1</sup>`, [TSC(1, TH("#", true))], "~P"))] }, { wait: 1800 }] },
  ]},
  kripke: { title: __T(2901), steps: [
    { h: __T(2902), text: __T(2903),
      html: KPLAN(`<div class="tut-doors">${TD("door", F("P|~P"))}</div>`) + KPANEL(TXR(__T(2904), __T(2905)), TXR(__T(722), __T(2906))),
      script: [{ cap: __T(2907) }, { move: "door" }, { hover: "door" }, { wait: 1600 }, { unhover: "door" }, { cap: __T(2908) }, { wait: 1800 }] },
    { h: __T(2909), text: __T(2910),
      html: KPLAN(TWR(KFL(0, [["P", ""]], { add: true, root: true }))) + KPANEL(TXR(__T(2911), __T(2912)), TXR(__T(2913), __T(2914)), TXR(__T(2915), __T(2916))),
      script: [{ cap: __T(2917) }, { move: "add0" }, { click: 1 }, { html: ["plan", TWR(KFL(1, [["P", ""]]), KFL(0, [["P", ""]], { add: true, root: true }))] }, { cap: __T(2918) }, { wait: 2200 }] },
    { h: __T(2919), text: __T(2920),
      html: KPLAN(TWR(KFL(1, [["P", ""]]), KFL(0, [["P", ""]], { root: true }))) + KPANEL(TXR(__T(2921), __T(2922)), TXR(__T(2923), __T(2924))),
      script: [{ cap: __T(2925) }, { move: "l0P" }, { click: 1 }, { html: ["plan", TWR(KFL(1, [["P", "inh"]]), KFL(0, [["P", "on"]], { root: true }))] }, { wait: 500 },
               { cap: __T(2926) }, { move: "l1P" }, { hover: "l1P" }, { wait: 2000 }] },
    { h: __T(2927), text: __T(2928),
      html: KPLAN(TWR(KFL(0, [["P", "on"], ["Q", ""]], { root: true, sel: true }))) + KPANEL(EVK(0, "P&Q", false), EVK(0, "P|Q", true)),
      script: [{ cap: __T(2929) }, { move: "l0Q" }, { click: 1 }, { html: ["plan", TWR(KFL(0, [["P", "on"], ["Q", "on"]], { root: true, sel: true }))] }, { html: ["proof", EVK(0, "P&Q", true) + EVK(0, "P|Q", true)] }, { cap: __T(2930) }, { wait: 2200 }] },
    { h: __T(2931), text: __T(2932),
      html: KPLAN(TWR(KFL(1, [["P", ""]]), KFL(0, [["P", ""]], { root: true, sel: true }))) + KPANEL(EVK(0, "P", false), EVK(0, "~P", true, __T(2933))),
      script: [{ cap: __T(2934) }, { move: "l1P" }, { click: 1 }, { html: ["plan", TWR(KFL(1, [["P", "on"]]), KFL(0, [["P", ""]], { root: true, sel: true }))] },
               { html: ["proof", EVK(0, "P", false) + EVK(0, "~P", false, __T(2935))] }, { cap: __T(2936) }, { wait: 2600 }] },
    { h: __T(1879), text: __T(2937),
      html: KPLAN(TWR(KFL(1, [["P", "on"]]), KFL(0, [["P", ""]], { root: true }))) + KPANEL(EVK(0, "P", false), EVK(0, "~P", false), `<div data-t="goalrow">${EVK(0, "P|~P", true)}</div>`),
      script: [{ cap: __T(2938) }, { move: "f0" }, { click: 1 }, { cls: ["f0", "sel"] }, { html: ["goalrow", EVK(0, "P|~P", false, __T(2939))] }, { wait: 600 },
               { cls: ["f0", "cex"] }, { html: ["plan", TWR(KFL(1, [["P", "on"]]), KFL(0, [["P", ""]], { root: true, sel: true, cex: true }))] },
               { html: ["proof", EVK(0, "P", false) + EVK(0, "~P", false) + EVK(0, "P|~P", false, __T(2939)) + __T(2940)] },
               { cap: __T(2941) }, { move: "done" }, { click: 1 }, { wait: 1600 }] },
    { h: __T(2942), text: __T(2943),
      html: KPLAN(TWR(KFL(1, [["P", "on"]]), KFL(0, [["P", ""]], { root: true, sel: true }))) +
        __T(2944, [F("~P")]) +
        __T(2945, [F("P"), F("P")]),
      script: [{ cap: __T(2946) }, { move: "nneg" }, { hover: "nneg" }, { wait: 1400 }, { unhover: "nneg" },
               { cap: __T(2947) }, { move: "c1" }, { hover: "c1" }, { wait: 2400 }] },
    { h: __T(149), text: __T(2948),
      html: KPLAN(TWR(KFL(0, [["P", ""], ["Q", ""]], { add: true, root: true }))) + KPANEL(TXR(__T(2949), __T(2950)), TXR(__T(2951), __T(2952))),
      script: [{ cap: __T(2917) }, { move: "add0" }, { click: 1 }, { html: ["plan", TWR(KFL(1, [["P", ""], ["Q", ""]]), KFL(0, [["P", ""], ["Q", ""]], { add: true, root: true }))] }, { wait: 500 },
               { cap: __T(2953) }, { move: "add0" }, { click: 1 }, { html: ["plan", TWR([KFL(1, [["P", ""], ["Q", ""]]), KFL(2, [["P", ""], ["Q", ""]])], KFL(0, [["P", ""], ["Q", ""]], { add: true, root: true }))] }, { wait: 500 },
               { cap: __T(2954) }, { move: "l1P" }, { click: 1 }, { cls: ["l1P", "on"] }, { move: "l2Q" }, { click: 1 }, { cls: ["l2Q", "on"] }, { wait: 2000 }] },
  ]},
  raa: { title: __T(163), steps: [
    { h: __T(2955), text: __T(2956),
      html: SC(`<div data-t="area">${TD("door", F("P"), __T(2957, [ICON.magic]))}</div>`, TH("P", true)),
      script: [{ cap: __T(2889) }, { move: "raa" }, { click: 1 }, { html: ["area", ROOM(1, __T(2958, [ICON.magic]), TK("kN", F("~P"), "asm s1"), TD("door", F("#")))] },
               { html: ["proof", TPR(TN(`RAA<sup class="sc s1">1</sup>`, [TSC(1, TH("#", true))], "P", "new", "raa"))] }, { wait: 1800 }] },
  ]},
  truth: { title: __T(2959), steps: [
    { h: __T(2960), text: __T(2961),
      html: __T(2962, [TLAMP("lp", '<i class="at">P</i>'), TLAMP("lq", '<i class="at">Q</i>'), TGV("(P->Q)->(Q->P)", TV3({}))]),
      script: [{ cap: __T(2963) }, ...TPRESS("lp", "F"), { html: ["proof", TGV("(P->Q)->(Q->P)", TV3({ P: false }))] }, { wait: 900 },
               { cap: __T(2964) }, ...TPRESS("lq", "F"), { html: ["proof", TGV("(P->Q)->(Q->P)", TV3({ P: false, Q: false }))] }, { wait: 900 },
               { cap: __T(2965) }, ...TPRESS("lq", "T"), { html: ["proof", TGV("(P->Q)->(Q->P)", TV3({ P: false, Q: true }))] }, { cap: __T(2966) }, { wait: 2200 }] },
  ]},
  allQ: { title: __T(2967), steps: [
    { h: __T(2968), text: __T(2969),
      html: SC(`<div data-t="area">${TD("door", TOP("!x.P(x)", "dop"))}</div>`, TH("!x.P(x)", true)),
      script: [{ cap: __T(2849) }, { move: "dop" }, { click: 1 }, { html: ["area", ROOM(1, __T(2970), RES("a"), TD("door", F("P(a)")))] },
               { html: ["proof", TPR(TN(`∀I<sup class="sc s1"><i>a</i></sup>`, [TSC(1, TH("P(a)", true))], "!x.P(x)"))] }, { wait: 1800 }] },
    { h: __T(2971), text: __T(2972),
      html: SC(KEYS(RES("a"), TK("kA", TOP("!x.(P(x) & Q(x))", "kop"))) + `<div data-t="area">${TD("door", F("P(a)"))}</div>`, TH("P(a)", true)),
      script: [{ cap: __T(2849) }, { move: "kop" }, { click: 1 }, { html: ["area", TD("door", F("P(a)"), PICK(__T(2973, [F("!x.(P(x) & Q(x))"), termH("x")]), __T(2974, [termH("a")])))] }, { wait: 500 },
               { cap: __T(2975) }, { move: "pa" }, { click: 1 }, { html: ["area", TD("door", F("P(a)"))] }, { html: ["keys", RES("a") + TK("kA", F("!x.(P(x) & Q(x))")) + TK("kB", F("P(a) & Q(a)"), "der")] }, { wait: 1700 }] },
  ]},
  names: { title: __T(1893), steps: [
    { h: __T(2976), text: __T(2977),
      html: SC(KEYS(TK("kPa", F("P(a)"))) + `<div data-t="area">${TD("door", F("!y.P(y)"), PICK(__T(2978), __T(2979, [termH("a"), termH("b")])))}</div>`, TH("!y.P(y)", true)),
      script: [{ cap: __T(2980) }, { move: "na" }, { click: 1 }, { cls: ["kPa", "namewarn"] }, { cap: __T(2981) }, { wait: 1700 }, { cls: ["kPa", "namewarn", false] },
               { cap: __T(2982) }, { move: "nb" }, { click: 1 }, { html: ["area", ROOM(1, __T(2983), RES("b"), TD("door", F("P(b)")))] }, { wait: 1600 }] },
  ]},
  exQ: { title: __T(2984), steps: [
    { h: __T(2985), text: __T(2986),
      html: SC(`<div data-t="area">${KEYS(TK("kE", TOP("?x.(P(x) & Q(x))", "kop")))}${TD("door", F("?x.P(x)"))}</div>`, TH("?x.P(x)", true)),
      script: [{ cap: __T(2849) }, { move: "kop" }, { click: 1 }, { html: ["area", ROOM(1, __T(2970), RES("a") + TK("kA", F("P(a) & Q(a)"), "asm s1"), TD("door", F("?x.P(x)")))] },
               { html: ["proof", TPR(TN(`∃E<sup class="sc s1">1</sup>`, [TL("?x.(P(x) & Q(x))"), TSC(1, TH("?x.P(x)", true))], "?x.P(x)"))] }, { wait: 1800 }] },
    { h: __T(2987), text: __T(2988),
      html: SC(KEYS(RES("a"), TK("kP", F("P(a)"))) + `<div data-t="area">${TD("door", TOP("?x.P(x)", "dop"))}</div>`, TH("?x.P(x)", true)),
      script: [{ cap: __T(2849) }, { move: "dop" }, { click: 1 }, { html: ["area", TD("door", F("?x.P(x)"), PICK(__T(2989), __T(2990, [termH("a")])))] }, { wait: 500 },
               { cap: __T(2975) }, { move: "pa" }, { click: 1 }, { html: ["area", TD("door", F("P(a)"))] }, { html: ["proof", TPR(TN("∃I", [TH("P(a)", true)], "?x.P(x)"))] }, { wait: 1700 }] },
  ]},
  translate: { title: __T(2991), steps: [
    { h: __T(2992), text: __T(2993),
      html: KPLAN(__T(2994, [F("P|~P")])) + KPANEL(TXR(__T(2995), __T(2996)), TXR(__T(2997), __T(2998))),
      script: [{ cap: __T(2999) }, { wait: 900 }, { html: ["dst", __T(3000, [TPADD("¬¬"), fh(parse("P|~P"))])] }, { cap: __T(3001) }, { wait: 2200 }] },
    { h: __T(3002), text: __T(3003),
      html: KPLAN(`<div class="tut-doors" data-t="area">${TD("door", F("~~(P|~P)"))}</div>`) + KPANEL(TXR(__T(717), __T(3004)), TXR(__T(3005), __T(3006))),
      script: [{ cap: __T(3007) }, { move: "door" }, { click: 1 }, { html: ["area", KEYS(TK("kn", F("~(P|~P)"))) + TD("door", F("#"))] }, { cap: __T(3008) }, { wait: 2200 }] },
  ]},
  tower: { title: __T(1944), steps: [
    { h: __T(3009), text: __T(3010),
      html: KPLAN(`<div class="tut-kcol"><div class="tw-dots">⋮</div>${[2, 1, 0].map(n => KFL(n, Array.from({ length: n + 1 }, (_, k) => [String(k), k < n ? "on" : ""]))).join(`<div class="tut-stair">↑</div>`)}</div>`) + KPANEL(TXR(__T(3011), __T(3012)), TXR(__T(3013), __T(3014))),
      script: [{ cap: __T(3015) }, { move: "f1" }, { click: 1 }, { cls: ["f1", "sel"] }, { html: ["proof", TXR(F("P(1)"), __T(3016)) + TXR(F("~P(1)"), __T(894)) + TXR(F("!x.(P(x)|~P(x))"), __T(894))] }, { cap: __T(3017) }, { wait: 2600 }] },
    { h: __T(3018), text: __T(3019),
      html: KPLAN(`<div class="tut-kcol"><div class="tw-dots">⋮</div>${[2, 1, 0].map(n => KFL(n, Array.from({ length: n + 1 }, (_, k) => [String(k), k < n ? "on" : ""]), { sel: true })).join(`<div class="tut-stair">↑</div>`)}</div>`) + `<div class="tut-proof tut-ev" data-t="proof">${TXR(__T(3020), __T(3021))}</div>`,
      script: [{ cap: __T(3022) }, { wait: 900 }, { html: ["proof", TXR(F("!x.(P(x)|~P(x))"), __T(3023)) + TXR(F("~!x.(P(x)|~P(x))"), __T(3024)) + TXR(F("~~!x.(P(x)|~P(x))"), __T(3025)) + __T(3026)] }, { move: "done" }, { click: 1 }, { wait: 1800 }] },
  ]},
  indep: { title: __T(3027), steps: [
    { h: __T(3028), text: __T(3029),
      html: KPLAN(__T(3030)) + KPANEL(TXR(__T(3031), __T(3032)), TXR(__T(3033), __T(3034)), TXR(__T(3035), __T(3036))),
      script: [{ cap: __T(3037) }, { move: "bA" }, { click: 1 }, { html: ["rA", __T(3038)] }, { cls: ["cA", "done"] }, { wait: 600 }, { cap: __T(3039) }, { move: "bN" }, { click: 1 }, { html: ["rN", __T(3038)] }, { cls: ["cN", "done"] }, { cap: __T(3040) }, { wait: 2200 }] },
  ]},
  get thirdway() { return PROG && PROG.best && PROG.best["core-5"] != null ? TW_FULL : TW_TEASER; }, // 第三の道は、17-5 をクリアするまでは見せない
  struct: { title: __T(3041), steps: [
    { h: __T(3042), text: __T(3043),
      html: __T(3044, [RES("1", 0), RES("2", 0), TLAMP("c11", ""), TLAMP("c12", ""), TLAMP("c21", ""), TLAMP("c22", ""), TGV("!x.?y.R(x,y)", TVS({ rel: { R: [] }, relF: { R: [] } }), ["1", "2"], 1) + TGV("?y.!x.R(x,y)", TVS({ rel: { R: [] }, relF: { R: [] } }), ["1", "2"], 1)]),
      script: [{ cap: __T(3045) }, ...TPRESS("c11", "F"), ...TPRESS("c11", "T"), { html: ["proof", TGV("!x.?y.R(x,y)", TVS({ rel: { R: ["1,1"] }, relF: { R: [] } }), ["1", "2"], 1) + TGV("?y.!x.R(x,y)", TVS({ rel: { R: ["1,1"] }, relF: { R: [] } }), ["1", "2"], 1)] }, { wait: 500 },
               { cap: __T(3046) }, ...TPRESS("c22", "F"), ...TPRESS("c22", "T"), { html: ["proof", TGV("!x.?y.R(x,y)", TVS({ rel: { R: ["1,1", "2,2"] }, relF: { R: [] } }), ["1", "2"], 1) + TGV("?y.!x.R(x,y)", TVS({ rel: { R: ["1,1", "2,2"] }, relF: { R: [] } }), ["1", "2"], 1)] }, { wait: 500 },
               { cap: __T(3047) }, ...TPRESS("c12", "F"), { html: ["proof", TGV("!x.?y.R(x,y)", TVS({ rel: { R: ["1,1", "2,2"] }, relF: { R: ["1,2"] } }), ["1", "2"], 1) + TGV("?y.!x.R(x,y)", TVS({ rel: { R: ["1,1", "2,2"] }, relF: { R: ["1,2"] } }), ["1", "2"], 1)] }, ...TPRESS("c21", "F"), { html: ["proof", TGV("!x.?y.R(x,y)", TVS({ rel: { R: ["1,1", "2,2"] }, relF: { R: ["1,2", "2,1"] } }), ["1", "2"], 1) + TGV("?y.!x.R(x,y)", TVS({ rel: { R: ["1,1", "2,2"] }, relF: { R: ["1,2", "2,1"] } }), ["1", "2"], 1)] },
               { cap: __T(3048) }, { wait: 2200 }] },
  ]},
  match: { title: __T(1914), steps: [
    { h: __T(3049), text: __T(3050),
      html: SC(KEYS(TK("kA", F("!x.!y.(x + s(y) = s(x + y))"))) + `<div data-t="area">${TD("door", F("a + s(b) = s(a + b)"))}</div>`, TH("a + s(b) = s(a + b)", true)),
      script: [{ cap: __T(2852) }, { move: "kA" }, { drag: ["kA", "door"] }, { cap: __T(3051) }, { html: ["area", TD("door", TOP("a + s(b) = a + s(b)", "deq"))] }, { wait: 900 },
               { cap: __T(3052) }, { move: "deq" }, { click: 1 }, { cls: ["door", "tut-ok"] }, { wait: 1500 }] },
  ]},
  eq: { title: __T(3053), steps: [
    { h: __T(3054), text: __T(3055),
      html: SC(KEYS(TK("kE", F("a = b"))) + `<div data-t="area">${TD("door", F("b = a"))}</div>`, TH("b = a", true)),
      script: [{ cap: __T(2852) }, { move: "kE" }, { drag: ["kE", "door"] }, { html: ["area", TD("door", TOP("a = a", "deq"))] }, { html: ["proof", TPR(TN("=E", [TL("a = b"), TH("a = a", true)], "b = a"))] }, { wait: 700 },
               { cap: __T(3052) }, { move: "deq" }, { click: 1 }, { cls: ["door", "tut-ok"] }, { html: ["proof", TPR(TN("=E", [TL("a = b"), TN("=I", [], "a = a", "")], "b = a", ""))] }, { wait: 1700 }] },
    { h: __T(3056), text: __T(3057),
      html: SC(KEYS(TK("kE", F("a = b"))) + `<div data-t="area">${TD("door", F("f(b) = b"))}</div>`, TH("f(b) = b", true)),
      script: [{ cap: __T(2852) }, { move: "kE" }, { drag: ["kE", "door"] },
               { html: ["area", TD("door", F("f(b) = b"), PICK(__T(3058, [termH("b"), termH("a")]), __T(3059, [termH("b"), termH("b")])))] }, { wait: 600 },
               { cap: __T(3060) }, { move: "o0" }, { click: 1 }, { cls: ["o0", "on", false] }, { wait: 400 }, { cap: __T(3061) }, { move: "go" }, { click: 1 }, { html: ["area", TD("door", F("f(b) = a"))] }, { wait: 1600 }] },
  ]},
  cards: { title: __T(264), steps: [
    { h: __T(3062), text: __T(3063),
      html: SC(KEYS(TK("kc", TOP("!x.!y.(x = y -> y = x)", "kop"), "card"), TK("kcb", F("c = b"))) + `<div data-t="area">${TD("door", F("a = c"))}</div>`, TH("a = c", true)),
      script: [{ cap: __T(3064) }, { move: "kop" }, { click: 1 }, { html: ["area", TD("door", F("a = c"), PICK(__T(3065), __T(3066, [termH("c"), termH("b")])))] },
               { cap: __T(3067) }, { move: "pc" }, { click: 1 }, { html: ["area", TD("door", F("a = c"))] }, { html: ["keys", TK("kc", F("!x.!y.(x = y -> y = x)"), "card") + TK("kcb", F("c = b")) + TK("kn", F("!y.(c = y -> y = c)"), "der")] },
               { cap: __T(3068) }, { wait: 1800 }] },
  ]},
};

Object.assign(TUTORIALS, {
  presets: { title: __T(1938), steps: [
    { h: __T(3069), text: __T(3070),
      html: __T(3071, [TGV("!x.!y.(x * y = y * x)", () => null, null, 0)]),
      script: [{ cap: __T(3072) }, { move: "open" }, { click: 1 },
               { html: ["panel", __T(3073)] }, { wait: 500 },
               { cap: __T(3074) }, { move: "load" }, { click: 1 }, { html: ["panel", ""] },
               { html: ["tbl", __T(3075)] },
               { html: ["proof", TGV("!x.!y.(x * y = y * x)", () => false, null, 0)] }, { cap: __T(3076) }, { wait: 2000 }] },
  ]},
  structFun: { title: __T(3077), steps: [
    { h: __T(3078), text: __T(3079),
      html: __T(3080, [termH("e"), TGV("!x.(e * x = x)", TVS({ con: { e: "1" } }), ["1", "2"], 1)]),
      script: [{ cap: __T(3081) }, { move: "f11" }, { click: 1 }, { cls: ["f11", "unk", false] }, { html: ["f11", `<b class="el">1</b>`] },
               { html: ["proof", TGV("!x.(e * x = x)", TVS({ con: { e: "1" }, fun: { "*": { "1,1": "1" } } }), ["1", "2"], 1)] }, { wait: 600 },
               { cap: __T(3082) }, { move: "f12" }, { click: 1 }, { cls: ["f12", "unk", false] }, { html: ["f12", `<b class="el">1</b>`] },
               { html: ["proof", TGV("!x.(e * x = x)", TVS({ con: { e: "1" }, fun: { "*": { "1,1": "1", "1,2": "1" } } }), ["1", "2"], 1)] }, { wait: 600 },
               { cap: __T(3083) }, { click: 1 }, { html: ["f12", `<b class="el">2</b>`] },
               { html: ["proof", TGV("!x.(e * x = x)", TVS({ con: { e: "1" }, fun: { "*": { "1,1": "1", "1,2": "2" } } }), ["1", "2"], 1)] }, { cap: __T(3084) }, { wait: 2000 }] },
  ]},
  leDef: { title: __T(1714), steps: [
    { h: __T(3085), text: __T(3086, [WN("15-1")]),
      html: SC(`<div data-t="area">${TD("door", `${termH("0")}<span class="mainop defop" data-t="le">≤</span>${termH("a")}`)}</div>`, TH("0 <= a", true)),
      script: [{ cap: __T(3087) }, { move: "le" }, { click: 1 }, { html: ["area", TD("door", F("?z.(0 + z = a)"))] },
               { html: ["proof", TPR(TN(__T(785), [TH("?z.(0 + z = a)", true)], "0 <= a"))] }, { cap: __T(3088) }, { wait: 1800 }] },
  ]},
  termInput: { title: __T(1920), steps: [
    { h: __T(3089), text: __T(3090),
      html: SC(KEYS(TK("k1", F("a + d = b")), TK("k2", F("b + e = c"))) + `<div data-t="area">${TD("door", F("?z.(a + z = c)"), PICK(__T(2989), __T(3091, [termH("d"), termH("e")])))}</div>`, TH("?z.(a + z = c)", true)),
      script: [{ cap: __T(3092) }, { move: "inp" }, { click: 1 }, { html: ["inp", "d + e"] }, { wait: 500 }, { cap: __T(3093) }, { move: "go" }, { click: 1 },
               { html: ["area", TD("door", F("a + (d + e) = c"))] }, { html: ["proof", TPR(TN("∃I", [TH("a + (d + e) = c", true)], "?z.(a + z = c)"))] }, { wait: 1800 }] },
  ]},
  induction: { title: __T(2719), steps: [
    { h: __T(3094), text: __T(3095),
      html: SC(`<div data-t="area">${TD("door", F("!x.(0 + x = x)"), __T(3096, [ICON.ladder]))}</div>`, TH("!x.(0 + x = x)", true)),
      script: [{ cap: __T(796) }, { move: "ind" }, { click: 1 },
               { html: ["area", `<div class="tut-doors">${TD("d1", F("0 + 0 = 0"))}</div>` + ROOM(1, __T(3097), RES("a") + TK("kh", F("0 + a = a"), "asm s1"), TD("d2", F("0 + s(a) = s(a)")))] },
               { html: ["proof", TPR(TN(__T(3098), [TH("0 + 0 = 0", true), TSC(1, TH("0 + s(a) = s(a)"))], "!x.(0 + x = x)"))] },
               { cap: __T(3099) }, { wait: 2200 }] },
  ]},
  lemma: { title: __T(1916), steps: [
    { h: __T(3100), text: __T(3101),
      html: SC(`<div data-t="area">${TD("door", F("R(a) & R(b)"), __T(3102, [ICON.anvil]))}</div>`, TH("R(a) & R(b)", true)),
      script: [{ cap: __T(1916) }, { move: "lem" }, { click: 1 },
               { html: ["area", TD("door", F("R(a) & R(b)"), PICK(__T(3103), `<span class="btn small" data-t="cand">${F("!x.(P(x) -> R(x))")}</span>`))] }, { wait: 500 },
               { cap: __T(3104) }, { move: "cand" }, { click: 1 },
               { html: ["area", `<div class="tut-doors">${TD("d1", F("!x.(P(x) -> R(x))"))}</div>` + ROOM(1, __T(3105, [ICON.anvil]), TK("kL", F("!x.(P(x) -> R(x))"), "asm s1"), TD("d2", F("R(a) & R(b)")))] },
               { html: ["proof", TPR(`<div class="pt-node new"><div class="pt-prems"><div class="pt-node new"><div class="pt-prems">${TSC(1, TH("R(a) & R(b)"))}</div><div class="pt-bar"><span class="pt-rule">→I<sup class="sc s1">1</sup></span></div><div class="pt-concl">${F("(!x.(P(x) -> R(x))) -> (R(a) & R(b))")}</div></div>${TH("!x.(P(x) -> R(x))", true)}</div><div class="pt-bar"><span class="pt-rule">→E</span></div><div class="pt-concl">${F("R(a) & R(b)")}</div></div>`)] },
               { cap: __T(3106) }, { wait: 2200 }] },
  ]},
  terms: { title: __T(1908), steps: [
    { h: __T(3107), text: __T(3108),
      html: SC(KEYS(TK("kx", F("g(f(a)) = g(f(b))")), TK("kg", TOP("!x.!y.(g(x) = g(y) -> x = y)", "kop"))) + `<div data-t="area">${TD("door", F("f(a) = f(b)"))}</div>`, TH("f(a) = f(b)", true)),
      script: [{ cap: __T(3109) }, { move: "kop" }, { click: 1 },
               { html: ["area", TD("door", F("f(a) = f(b)"), PICK(__T(3065), __T(3110, [termH("a"), termH("b"), termH({ f: "f", args: ["a"] }), termH({ f: "f", args: ["b"] })])))] }, { wait: 500 },
               { cap: __T(3111) }, { move: "pfa" }, { click: 1 }, { html: ["area", TD("door", F("f(a) = f(b)"))] },
               { html: ["keys", TK("kx", F("g(f(a)) = g(f(b))")) + TK("kg", F("!x.!y.(g(x) = g(y) -> x = y)")) + TK("kn", F("!y.(g(f(a)) = g(y) -> f(a) = y)"), "der")] }, { wait: 1800 }] },
  ]},
  defs: { title: __T(1571), steps: [
    { h: __T(3112), text: __T(3113),
      html: SC(`<div data-t="area">${TD("door", fhDef(parse("A ∩ B ⊆ A"), 'data-t="dop"'))}</div>`, TH("A ∩ B ⊆ A", true)),
      script: [{ cap: __T(3114) }, { move: "dop" }, { click: 1 }, { html: ["area", TD("door", F("!x.(x ∈ A ∩ B -> x ∈ A)"))] },
               { html: ["proof", TPR(TN(__T(785), [TH("!x.(x ∈ A ∩ B -> x ∈ A)", true)], "A ∩ B ⊆ A"))] }, { cap: __T(3115) }, { wait: 1800 }] },
    { h: __T(3116), text: __T(3117),
      html: SC(KEYS(TK("km", fhDef(parse("a ∈ A ∩ B"), 'data-t="kop"'))) + TD("door", F("a ∈ A")), TH("a ∈ A", true)),
      script: [{ cap: __T(3118) }, { move: "kop" }, { click: 1 }, { html: ["keys", TK("km", F("a ∈ A ∩ B")) + TK("kn", F("a ∈ A & a ∈ B"), "der")] }, { wait: 1800 }] },
  ]},
  eqboth: { title: __T(3119), steps: [
    { h: __T(3120), text: __T(3121, [WN("10-7")]),
      html: SC(KEYS(TK("kA", F("(i(a) * a) * b = i(a) * (a * b)"))) + `<div data-t="area">${TD("door", F("(i(a) * a) * b = (i(a) * a) * c"))}</div>`, TH("(i(a) * a) * b = (i(a) * a) * c", true)),
      script: [{ cap: __T(2852) }, { move: "kA" }, { drag: ["kA", "door"] }, { html: ["area", TD("door", F("i(a) * (a * b) = (i(a) * a) * c"))] }, { cap: __T(3122) }, { wait: 1800 }] },
  ]},
});
const CURSOR = `<svg viewBox="0 0 24 24" width="24" height="24" aria-hidden="true"><path d="M4 2l14 10-6.5 1.3L15 20l-3 1.3-3.4-6.6L4 19z" fill="var(--ink)" stroke="var(--surface)" stroke-width="1.5" stroke-linejoin="round"/></svg>`;
let TUT_RUN = 0, TUT = null;
// 台本どおりにカーソルを動かして、見本の画面を繰り返し再生する（モーダルを閉じるか、ステップを変えると止まる）
async function playScene(box, steps, onStep) { // steps が配列なら、順に一回ずつ再生して繰り返す
  const list = Array.isArray(steps) ? steps : [steps]; let idx = 0;
  const token = ++TUT_RUN;
  const alive = () => token === TUT_RUN && box.isConnected;
  const sleep = ms => new Promise(r => setTimeout(r, ms));
  while (alive()) {
    const step = list[idx % list.length]; if (onStep) onStep(step, idx % list.length);
    box.innerHTML = `<div class="tut-stage">${step.html}</div><div class="tut-cursor">${CURSOR}</div><div class="tut-cap"></div>`;
    const cur = box.querySelector(".tut-cursor"), cap = box.querySelector(".tut-cap");
    const q = t => box.querySelector(`[data-t="${t}"]`);
    const at = el => { const b = box.getBoundingClientRect(), r = el.getBoundingClientRect(); return [r.left - b.left + r.width / 2, r.top - b.top + r.height / 2]; };
    let pos = [box.clientWidth - 40, box.clientHeight - 30];
    const put = (pt, ms) => { cur.style.transition = ms ? `transform ${ms}ms cubic-bezier(.4,0,.2,1)` : "none"; cur.style.transform = `translate(${pt[0] - 5}px, ${pt[1] - 3}px)`; pos = pt; };
    put(pos, 0);
    await sleep(500);
    for (const a of step.script) {
      if (!alive()) return;
      if (a.cap != null) { cap.textContent = a.cap; cap.classList.toggle("on", !!a.cap); }
      if (a.move) { const el = q(a.move); if (el) { put(at(el), 750); await sleep(820); } }
      if (a.hover) { const el = q(a.hover); if (el) el.classList.add("tut-hov"); }
      if (a.unhover) { const el = q(a.unhover); if (el) el.classList.remove("tut-hov"); }
      if (a.click) {
        cur.classList.add("press");
        const rp = document.createElement("span"); rp.className = "tut-ripple"; rp.style.left = pos[0] + "px"; rp.style.top = pos[1] + "px"; box.appendChild(rp);
        await sleep(280); cur.classList.remove("press"); setTimeout(() => rp.remove(), 520);
      }
      if (a.drag) {
        const f = q(a.drag[0]), to = q(a.drag[1]);
        if (f && to) {
          const b = box.getBoundingClientRect(), r = f.getBoundingClientRect(), p0 = at(f), p1 = at(to);
          const g = f.cloneNode(true); g.removeAttribute("data-t"); g.classList.add("tut-ghost");
          g.style.left = (r.left - b.left) + "px"; g.style.top = (r.top - b.top) + "px"; g.style.width = r.width + "px";
          box.appendChild(g); cur.classList.add("press");
          await sleep(80);
          g.style.transform = `translate(${p1[0] - p0[0]}px, ${p1[1] - p0[1]}px)`; put(p1, 900); to.classList.add("tut-hov");
          await sleep(980);
          to.classList.remove("tut-hov"); g.remove(); cur.classList.remove("press");
        }
      }
      if (a.html) { const el = q(a.html[0]); if (el) { el.innerHTML = a.html[1]; el.classList.remove("tut-fade"); void el.offsetWidth; el.classList.add("tut-fade"); } }
      if (a.cls) { const el = q(a.cls[0]); if (el) el.classList.toggle(a.cls[1], a.cls[2] !== false); }
      if (a.wait) await sleep(a.wait);
    }
    await sleep(list.length > 1 ? 1300 : 1800); idx++;
  }
}
// 新しいチュートリアルがないステージでは、それまでに登場した最新のチュートリアルを開く
function latestTut(stage) {
  for (let j = STAGES.indexOf(stage); j >= 0; j--) { const t = STAGES[j].tut; if (t && t.length) return t[t.length - 1]; }
  return "basics";
}
function openTutorial(id, si = 0) {
  const tut = TUTORIALS[id];
  if (!tut) return;
  si = Math.max(0, Math.min(si, tut.steps.length - 1));
  TUT = { id, si };
  PROG.seenTut = PROG.seenTut || {}; PROG.seenTut[id] = true; saveProgress();
  const step = tut.steps[si], here = SCREEN === "play" && STAGE ? (STAGE.tut || []) : [];
  const recent = SCREEN === "play" && STAGE && !here.length ? latestTut(STAGE) : null;
  const chip = k => `<button type="button" class="tut-chip${k === id ? " on" : ""}" data-tut="${k}">${TUTORIALS[k].title}${!PROG.seenTut[k] ? '<span class="new-badge in">New</span>' : ""}</button>`;
  const groups = WORLDS.map(w => { const ks = w.stages.flatMap(s => TUT_AT[s.id] || []); return ks.length ? `<div class="tut-group"><b>${WL(w)}</b>${ks.map(chip).join("")}</div>` : ""; }).join("");
  const last = tut.steps.length - 1;
  showModal(__T(3123, [here.length ? __T(3124, [here.map(chip).join("")]) : recent ? __T(3125, [chip(recent)]) : "", tut.title, last ? __T(2676, [si + 1, tut.steps.length]) : "", step.h, step.text, last ? __T(3126, [si === 0 ? "disabled" : "", tut.steps.map((_, i) => i === si ? "●" : "○").join(""), si === last ? "disabled" : ""]) : "", groups]), true);
  playScene($("#tutBox"), step);
  if (SCREEN === "play") { renderTools(); updateUndo(); }
}

// 遊び方：複数のページに分け、最初のページで画面の見方を図で示す
let HELP_PAGE = 0, HELP_TIMER = null, HM_I = 0;
const HM_ITEMS = [
  [__T(3127), __T(3128)],
  [__T(3129), __T(3130)],
  [__T(3131), __T(3132)],
  [__T(3133), __T(3134)],
  [__T(3135), __T(3136)],
  [__T(3137), __T(3138)],
  [__T(3139), __T(3140)],
  [__T(3141), __T(3142)],
  [__T(3143), __T(3144)],
  [__T(3145), __T(3146)],
];
function helpMock() {
  const no = i => `<span class="hm-no">${i + 1}</span>`;
  return __T(3147, [no(0), no(1), no(2), F("P"), F("Q"), F("P&Q"), no(3), no(4), no(5), F("P"), F("Q"), no(6), F("P"), F("Q"), no(7), TH("P&Q", true), no(8), no(9)]);
}
function hmGo(i) {
  HM_I = i;
  document.querySelectorAll("#hmMock [data-hm]").forEach(el => el.classList.toggle("hl", +el.dataset.hm === i));
  document.querySelectorAll(".hm-legend li").forEach((li, k) => li.classList.toggle("on", k === i));
}
// 遊び方の図：静止した見取り図と、動く見本（チュートリアルの場面を順に再生）
const helpAnimBox = () => __T(3148);
function figRooms() {
  return __T(3149, [TK("", F("P->Q")), TK("", F("R")), ROOM(1, __T(2864), TK("", F("P"), "asm s1") + __T(3150), TD("", F("Q"), __T(3151))), F("P->Q"), F("R"), F("P->(Q)"), F("P"), F("Q"), F("P"), F("P->Q"), F("Q")]);
}
function figProof() {
  const tree = `<div class="pt-node"><div class="pt-prems">${TSC(1, `<div class="pt-node"><div class="pt-prems"><div class="pt-leaf prem">${F("P->Q")}</div><div class="pt-leaf s1">[${F("P")}]<sup class="sc">1</sup></div></div><div class="pt-bar"><span class="pt-rule">→E</span></div><div class="pt-concl">${F("Q")}</div></div>`)}</div><div class="pt-bar"><span class="pt-rule">→I<sup class="sc s1">1</sup></span></div><div class="pt-concl">${F("P->Q")}</div></div>`;
  return __T(3152, [ROOM(1, __T(2864), TK("", F("P"), "asm s1"), TD("", F("Q"))), tree, F("P"), F("P")]);
}
function figRefute() {
  const lamp = (a, v) => `<span class="lamp${v === true ? " on" : v === false ? " no" : " unk"}"><i class="at">${a}</i><span class="tv">${v === true ? __T(876) : v === false ? __T(877) : __T(891)}</span></span>`;
  return __T(3153, [lamp("P", false), lamp("Q", true), F("P->Q"), F("Q->P"), F("P|~P"), lamp("", true), lamp("", false), lamp("", false), lamp("", true), F("R(x,y)")]);
}
function helpStop() { if (HELP_TIMER) { clearInterval(HELP_TIMER); HELP_TIMER = null; } if (RPD_TIMER) { clearInterval(RPD_TIMER); RPD_TIMER = null; } }
// 「証明図」のページの、クリア画面の再生の見本（1-1 の証明を自動で再生する）
let RPD_TIMER = null;
function figReplay() {
  return __T(3154);
}
function rpdStart() {
  if (!$("#rpdTree")) return;
  const h1 = { k: "var", x: "h1" }, h2 = { k: "var", x: "h2" };
  const tree = { f: parse("P&Q"), rule: "∧I", op: 1, tm: { k: "pair", a: h1, b: h2 }, kids: [{ f: parse("P"), leaf: true, prem: true, op: 2, x: "h1", tm: h1 }, { f: parse("Q"), leaf: true, prem: true, op: 3, x: "h2", tm: h2 }] };
  const log = [{ rule: "∧I", text: __T(808, [F("P&Q"), F("P"), F("Q")]) }, { rule: __T(824), text: __T(825, [F("P"), F("P")]) }, { rule: __T(824), text: __T(825, [F("Q"), F("Q")]) }];
  const n = log.length; let k = 0;
  const draw = () => {
    if (!$("#rpdTree")) { helpStop(); return; }
    const done = k > n, kk = Math.min(k, n), l = log[kk - 1];
    const pt = prunePT(tree, kk);
    $("#rpdTree").innerHTML = renderPT(pt, termCX(pt, { ...STATIC_CX, latest: done ? 0 : kk }));
    $("#rpdStep").innerHTML = done ? __T(2792, [n]) : k === 0 ? __T(2793, [F("P&Q")])
      : __T(3155, [kk, RD(l.rule), RULE_NAMES[l.rule] || "", l.text]);
    $("#rpdCount").textContent = done ? __T(2796, [n, n]) : __T(2797, [kk, n]);
    $("#rpdPlay").textContent = done ? __T(2799) : __T(2798);
  };
  draw();
  RPD_TIMER = setInterval(() => { k = (k + 1) % (n + 3); draw(); }, 1300);
}
const HELP_PAGES = [
  { t: __T(3156), html: () => __T(3157, [helpMock(), HM_ITEMS.map(([h, d], i) => `<li data-hmgo="${i}"><b>${h}</b><span>${d}</span></li>`).join("")]) },
  { t: __T(3158), anim: () => [TUTORIALS.basics.steps[1], TUTORIALS.basics.steps[2], TUTORIALS.impI.steps[0], TUTORIALS.orE.steps[0], TUTORIALS.bot.steps[0]], html: () => __T(3159, [figRooms(), helpAnimBox(), F("A->B"), F("A"), F("A|B"), F("A"), F("B"), F("A"), F("B"), F("~A"), FE("A->#"), F("~A"), F("A")]) },
  { t: __T(3143), anim: () => [TUTORIALS.basics.steps[0], TUTORIALS.andE.steps[0], TUTORIALS.impE.steps[1], TUTORIALS.scope.steps[0]], html: () => __T(3160, [figProof(), helpAnimBox(), figReplay()]) +
    __T(3161) },
  { t: __T(3162), html: () => __T(3163, [GUIDE_HTML, WN("6-1"), F("A"), F("A->B"), F("B"), F("A->B"), F("B"), F("A")]) },
  { t: __T(1836), anim: () => [TUTORIALS.truth.steps[0], TUTORIALS.kripke.steps[0], TUTORIALS.struct.steps[0], TUTORIALS.structFun.steps[0], TUTORIALS.presets.steps[0]], html: () => __T(3164, [figRefute(), WN("r-conv"), WN("5-1"), WN("s-ex"), helpAnimBox()]) },
  { t: __T(3165), anim: () => [TUTORIALS.allQ.steps[0], TUTORIALS.exQ.steps[0], TUTORIALS.eq.steps[0], TUTORIALS.lemma.steps[0], TUTORIALS.induction.steps[0], TUTORIALS.defs.steps[0]], html: () => __T(3166, [helpAnimBox(), WN("9-1"), F("s = t"), termH("t"), termH("s"), termH("s"), termH("t"), WN("7-1"), termH("a"), termH("a"), WN("6-1"), WN("r-conv"), F("A"), F("~A"), F("A"), WN("5-1")]) },
  { t: __T(3167), html: () => leanHelpHTML() },
];
function leanHelpSample() { // 遊び方の見本：2-4「関数の合成」の Lean のコード
  const rows = [["example (P Q R : Prop)", ""], ["    (h₁ : P → Q) (h₂ : Q → R)", ""], ["    : P → R := by", ""],
    ["  intro x₁", "→I¹"], ["  apply h₂", "→E"], ["  apply h₁", "→E"], ["  exact x₁", RD(__T(824))]];
  return `<div class="lean-box static"><div class="lean-code">${rows.map(([c, cm], i) => `<div class="lrow${i < 3 ? " lhead" : ""}"><span class="lcode">${leanHL(c)}</span><span class="lcm">${cm ? "-- " + cm : ""}</span></div>`).join("")}</div></div>`;
}
const LEAN_SHOTS = {"ja": {"full": "UklGRsiKAABXRUJQVlA4ILyKAACwVQKdASo0AzMCPmEuk0ekIiQnI/GLAOAMCWdulXD6x87/OftR2ztq1UH+p/0nod/4Xnag5Bv/sH7A6BGs58a4kOUMhZKrhf6g5p2X+1D/0/GuPX4kvsnqDfzv+uf9jzY+YH8m/1367b0Z+P+gL/HvN10Tvou8K8dzako6Afk/IT6D/a2WX7n/D+dn/i/s57sf7j6hX6q+ej65P7l6Dv3R9Zr/s+r3+4+oB/Tf+H61Hqi/3r/rewB+uPrQf/D2b/8V/3P3O9qX1AP//wHfqP/N/4X2F+SP5H+9f5X/mf4L1L/Fvp/8P/ff3A/wXuAf4/mi9c/tv2i9Vf5Z92v1X91/eT/Me8n/J/xHjX8ef7//I/lN8hf5H/N/9d/a/X3+y7gTTv9f/4P817Bfrp9O/53+D/1P7RemJ/ef5b1W/Sf7p/xf858AP8r/qn+3/xP72f4////TX+b8Pv6x/sP+3/nvgB/lP9h/5X+H/0f7TfSx/Vf+n/Uf779svaz+b/6D/0f6L/b/IL/M/7N/4P8h7bn/49y37z///3XP2///pSI1CVzREKAMov/K+I4aPSahPpq6o/K8zdYG5EoBsYIUHq6g9XXgj0fJN1gbkSfDNgOizIu9drKsahC0XlbnOVL48eQZ5BnHLhj83ljkXZ7eoj5YCrEwrQcetqJCBWD5+yp+kYgTTPGmjN8Mg91tc2Bv3N58iI+NEsuo6uuSezEBElEVjtOZytUlWes/uMygw4y/ZgRD2T+39hVqVrKbTuKHt/lDU6wkjdaStCKwdY1hhjPoSOaWkJRX+0KRtnNg1T9xo1U0DA2DLrHn/4SL/lF0Mqs6oOBFqEqEtIk2QxRT5adXC5lPv1VFvlVQ8Y3zwTm5D1GQDWPRHImfxfMK1WCAUbLKzn7QzuOyulidpmK7+oZlmeRi9pM6XChxKpCzFzAv+Wr1D0RHmFnB6dfTXQXAStbbGJ1G+f/6zxdZwUh4IX3j1QHdj8qhy8Q597bnPTr0/EDohZzW5U+IWua4MaCpzPSD8yKaou8HOEbqbtExN4qEt2O//a82kXEF5g9ljwqJcW3sZxoXqLg0BguysVjdeM3aLra4YW9tpcDW7lrmMlysjai3atMIMJfuWe/bqyX1f5R0P1LGXPw+WBYbG7bP0dYy96ooPn8r/Kx19rCqhp9g4+QTbnCnKdYZEY30STYxs1I5azXqjx4RK6OWXbRfzfPlEUdxT0YjHofa6RwiWm1FQM8YWlRDA4XID1ON1pn1AseBuVli1hkWY37up240PvaRgJX1dUBVa6hA/KZ5O5aQ6jAaVFdPwJ1d+cIYEZVeEpIismV+Iw1zHhtuDvhhS9HM+hGJ3PlGacvOC+uWL3sq7Mkz8Ve2KeDwo8VfdsAI+b7Biuc0TeKkNyfnyUJP/4bGeqpQGOF7U47mz39qFuwbjlO4BVLOVOSOHG/+NVLeHMvQ7HU4AmTWlzPwY50tk/Ry5Tx3zzr+u3W1qi3P5xWXfyCD8KUBsxT8pOxp8EX/BiD6xUF0btOMUt3BTH7AYhLyAP+OpUzy1l+KyIrtzozkM6cPsrQJ9t3Fg9cTWIICYNnO3ZlzmMIU+HMq5/OHCssnvg60y0RWo4arUD8T0wodp7Ud30dzhGwCIJarfeRuZ8AVlkH5mNXBHR2ZUd7XyZf6YSuM9c24f9vcfWiPyUWnArZUHIzEaFjmcUdHL10Ib0aYJNAiUpAxzsxV0n4TZ8TXTSF4/zScKd2JSxs/LLqFrHPDinMNiAqhCoN/fkkJNXKu9KwlI3w6O3NBpbLRlCKAUEsoEJnuuJWYbxiMUpb0avK4K2V0xTMAuAb4P5Jn6Qut8NsQQY388NbGpfTPUz6VESVfygwRmgexh217gmtlSh1gPc5XD+QpgrR0kBNFEOzuFaAbH6Q8jC3SzSEAZCW4MYpK7IJoEOME0zPjYkxPlB5xQBkIvKjOgJYkqbx7yBd9hql5b/TxZNm+aA51C1Kb9tnGf+jepKXVzyZRZn6m3aIgCR8yiHJXMDWWr7NPHclRuPk3FXA7FPdg/o+6kYfNqTi+niY9zQVf2e/sLd3ZJQp14PaH2i8Aq/TXoJctIxnLptF9MybWypdMzz2cjHBXerRF2dJ3kb23CuoyolvaOPfVvYJMYXDREKNF7z/HFvP25Db9wwCnJR3F6vxWCuHtuuTeX1wFDUN2fJbQtJLERKUm47+5fikECfwJSRN7H8d0Utj/g7VOh0sNZkmptN+Cd1nBs4KBL3vMlm+hVK77snRX3qEKQDEu9eNm+hcnlgV4DDXxb/pbfRlzbgDje4F4F1d6HgSKorgLsxzFRt7F4yE8SxGRglMmXSwXS2Qqz1s6QTFjTaGa8EJYbA6Uuphf5OtMPEBa/2OocNYm+6F+58WHpN3oIkvDItjnZ/XoEHtfu/1y9lF/lEYvhg57j1zika3RfB6CCWUL/Jal+uzRFGCVfaFBWyrHXnZgCmDLc+FjU0J2jhZjGNpqvJrL0y2LvI+F0/wKr7ALxcNUjEhUJLAKQmdnbL6UA4RzppAlzGDfRPOKzT5KaPkwpSpI9sTQjgRJVBn2ND5wM8hdJZnP8Z2K2rUGT0IdbVs96d72GYNdCVgMs3hPnfkALtZM0auuktQw4z57rRI48euTTtD0dMHf5ToruRBgrwEKf8VLT3xGfaBM4l9NWMiEKOYEjbgGJJMrnw3kNn5OE2RwriHILuWA/0wByWgVMexMw3v/k7J3vvGE1gO72lFkMaIjndAPGLJZ2HQlr08VbOL8RwaxCTOmPs5eZ1v52FeWQQzEiMWWchVCyzgE1+IbW1lFemSztgS0iooAUAwCFRmIywR9sU4f+Hu1UVWuGjzWY6K6pgbGngJ5nk76iLwL/BwKR4Ahiyoek1knJyBpV/tg2/d62mp6AIfCIHNqAyuHLgMW1PUtzypm6lapLxj4Y19x+ATYmPtxpgqLDLAp+EBlKI77w4J9VOKbif7o7zvI1uLr9IrSGprTzYjN/+SoIvS7Yomppidz1drAbbDEoeH2eiBnA3aCFtTQ0o06U7v1qHcwogl1sRCgQ3sk96cW1HtUb1OymPKPb6mxCAd/vKxwtrwEUjnIOtVDpoTlaFFKjWcItfqbcZSD5FwLjRUjEYS+oMv24VkFjChsL4n8+8+W9PLc49K63JcmSHTlJPyKX8g/vhW+pgNigwCxBgFiDALEGAWIL0rM+aR0onzOtoQb6me46x7yijOgJwzRhfU834ur19W4Jkg6rV8/hZYXT8KhJrRHvRvTGjJzkHr9OKyjEkpHI+qxm1vMghFMOYCA6WrTkceNJGs2o6D007d2T9SmYGqYGQltuhq36JLQC24+VZquGXHZa3rCazGowirKjHr//YwtHUlAGtGf/WngazbqgMZXo0DFT/rfYxhu1u6S/eFANTKob4//2xIwoU7wNzQmtH85IyxJKs5is/o7v+erh6snWan9llK8llA/tH9gJX2ldx1XAiSQGYFsQOS35gWvsgnANon8XaK7lEknrZ+uqtAJ/p441LLB3XYnGopbbg2nl/G2aHhRpmMZT66gXe7Hc0GfW+vsJtnECUBOcUlYJAWRb7qKSRDP2r1pgm3GxMkuPGPblOaDMTVA6Rnf1w8r6V+bNBtpMDFo0a9p0X5Ve7tkhh/B1j0eC+dYKBD1jyNaCJzU2o/S1ILyPOCu/0Gw56dSBnGgHFsk4Ha7k+DdF3JxX+inxwXFyw34VDyhYzD9c8LdY1wHyCMwIfSlD5snk/nHRU3W2zMjmdXEsIk+qKWZMXsTBHPvUNfd+17hNfVNcgWdyogcVBh4S7jqCkIaQYzsBgtG4UOctQnFPH2iG2ACmuYNf7udriQReZFmaHJDKhNlOs6aNsZO214u0VQrcON8Nn+uTNZWCy525nBho8QIsm9HfEQV2IgrsRBXYiCuxEFaxtghpkz4KpjyQngB4RoD5SRDNiFaeM0X02g0ycm35yRO293HbRHYKmK1Ycw1FyCrUEbAfwyPbcB+4SJ66iMesLfcEOzHS76X9TGWprCMz/uQPgpNcUj3dxzc9m74QbzC5/ej7FMb0C4503bTNPsmlks5LiUK2q32uuYj4Ic4O72r0JwIeerej1wRjKOswPtQf3GPFvbZc/28Z/sBbPDK1U+qLi4jL1th5BX4aHQnXDLUfbbgLRXeoxOaapl9+uN9FgaKABSdUq/zEfaSOnZ6wxoxK/KLIJX58Pe0bAFse1Pjlvf8El6ewsqmhlgJk5N6pRF2dCYb1l6Jl1+r/UfoO2FcmRIGE+I9xjOsxeEyLIn+ATFVphAIRVL0uRfK4QWFkvK8p+e43XcQJQJ5WQns3TkgMf7gb0GI2ex4YMMtV6L9JI0D+RNvNSIUMVgrlypn961B06oJtnEBrDcCRKBXqgFfYKybK3loFXbA1BC7zEhKynsxWhK0FMe+xRhPJmXqHr8NnZnI0oIYvZaxR2GTq8p0f6Zvj26itmuzvhIrBE4EmgkBYfCwSAsjBYJAWOpjd+/Swn1ZLmUVVy8PgArJ26svBH52XT2xpTZj91ifSd7jwvHxQb4F9OYL0AtQPqVGlHWB5X+sHY+zoQ30wbo4r8ywOcQdBJLdBBntb3/cPer5xp8ig90Ro9Rj74VYwWa/RoGEf4jjBSV51jmp2ZFmynFCGNddogcO3CYG7/dBzrwJ6Me41J/fjLtKEvsFFgXSWkmqC98bQQ8ifRwt4TdEovQPR7DsRMoQSAshvmrE1YpIKf3hYY5fHIJD4EWIc2J5FY0jrsxGmJSNLzOSXmI0vMRpeYjRu4gJRS+jjkg/Jig9bsms8Pkx7wiaY24Ul4X6Z3S+SID8Om5gp3E4WHYrEZd0IglsSoIg0miEKDRY3BCZMnY/gWHa7qcfrzoPCoLjLve4iMdrq+L5Dfo8JDxqRBwbEd2keRz0ahLk5ByjusVrFPOLqb41ig6bpoMpPe+97EQ2Fn2NUraLW0htHfybxM8XZOOqsuO5kb4/t65klR0MjyOepEHBsR3aR4/FDctazPsWVgeAFb9JitWwDEoYoastLnZSzXuxkr77tI8kBE8q+4EXRAkUS3bsyPrDaUM3xTnU77tI8jnqRBwbEYKrFVnFTq21+6rg5SkHwkl5HWyYwa0LdId97YEo6Q9E7/SO+0Nddvhjq7zImdzHdEEFCysBd1P3NBWdiZ9dSWRYG5Cq/FWo47fwU4PdAshz54E8mBXvGOfHRq3p0e1FRIGD2Iv1okjN9bvWBfrR6cXeNDUPcPyPp2toiCWxGUDZ187LxEcyQWpQYB+Qrd009XPq7P+c9aDtIKBI/6CDwhQXS699xDNYlzspoHgkxIxqnSnpcWVM7MX0M6bE0dxBo9EQ/rZPHKnRuVOjcqdG5U6NytZj8KzH4VmPwrMJKjBdIMTyA90nOZa+fhiMCY7s4KxmBQfjYatZYvGoZLWWoJCQE6IaE20lxSj2sRPwB2Y2fnst4TeeM8o8a5V6Vyr0rlXpXKvSuVelcq9K5V6VvpZnhWOdij+d6/MxMxDmEQAWO9X6I+WVGJ10p86XJiw4L5235qu/V2Cb/xDvjfjxX7GLAK9OB3OmHTt9H/Bz/kkmcspG5tp5NmSFnKDn7aN4G/JkP8HtyGdXrLhuUj/2P04DwYwUAgeevDu9QIaMJwlnKkPmNRDJo7wBEqE+UGEEMiM/qQTOKALjciD3IwkLuH1u/JO6bxnSpKPplwnTWGoo0jTf//D+ElGeJ1AzMXxqyNWA3fktkYlqWtj3Y7zhr9OvRzy5WxK3ODhnZtFV6IWa4yYzcZSoQXORIrrnkPn4JEwlEXIU+AkiAprO2A+9PyS6ZHMSpLqrTcxzl+Z19iC+drFhDj6Nvs8X24HoYEGHtAnRAbGzyDEMsimY6t/DhdRB3jlH6sNIdVNSYBvsv42vMMESoCeIhoO0uL5HmcmxXdmPITNTou0Y6N9cWEWQGUyDpVV5ERHfefuoKXUj+ZK4PX/nyTl9SAzRNTiIK/x4bvo9S32uqj+fTGUkHmos/I6fOglzWyYJnuRZmWSe/+gwaoOCD77NNdYxFgZZitQEFwVkprrgps6uxN7OueITs0ql/irVQB89tzixFPKh7RlrNgPpy6D8TNVY7sg2CULPFdYZO9eCZl7B6ytZeujgqZGRDUy1m1YO4XVCZatYpr/qP5dRE3XptiHG3FGapgY2A+VMnOGdEskrIpQIIMNj+DaAqxXf08KkH7FSj4mGk+dL4oeqt2PhqMX25CzbX6F3dERWpLo0+UZ0E6V+Ptq8MXsLrBCb6OgfrQ5IhZYIzgsQWDb62JC42y1354LMS2qESUq6H4FJpBRJ71vKSMNNCEPJ1r+9JgjZ3B/5NTKZdUUrdwqAuC8b0zqQr3yHEsjXsSn+lltIAAD+/LaBFv4nA/bH+S07AdQlvYb+t/mUGXj7wYj2NHKX7sqcKbEvmrPAiC5aO/05XnlOKGoXi0V7gjt0uBt1BXi9Gjkmbg7bB0w2CjB3N/sfua9y8uava/tK8AjPieIuPtowFn+qHIhDwauFi6MBbNMXGU75uwwof5v0YbMa3plWn4dKiIAAAAAG/cm8srLACXKjilm7iW2/DCs/CqSyZI+wygxptiOU6p11FFBSjjdxj7DRfqMonbQDUjHQNuYibGbCzMHtPUrKEAQ8JikfFUQcAUiu2YL+vcooCT2nP1OlvWzcMM70CVSvjexFUt3L95ZXLof2dKy8ClGBFAeKw8u48DAK6Q4hHc18R3jH5BbfAPN7KaPNIV+pasLCXqHXTD/vTs62L+lVZ1fdMOfNIjFUuHV/11Dvl7iCfIbpCFCSdDOaFFPKEf+jOHEwlzWRoawxH5Ipuh5rPUvfWkUnApnXevy7g8WQS6dDURPj1/Ne5Vlzv61n75B6wZafd2Hjj3+CJ0FkZNZL+BYmuCQJT018YtLwTLT0kx5XIM7+siyGzBqEdKezGpHN3h+hdyumd89/1eCZf9XI9SafT5cyyD7WSy2pNFCMmd9Y8pkowZmu/SR3elqr0riT9+wXZJMuYxA++gx12Tfen0mkSAdWJlwpYrnLSlw6AgK5ZEzYUh/YyHk1bdrAzh0bh7cp10KYalhrpySx1UFkKryj3h+8ouF3Yal/CSL8Gt0g1fbe/3xeFP3XxVLl/AxvYcwIsLOO+r7EgolTm3gGikEGKqYOw2sls7wZQgCkw0dM6qETsMSgfnCUKFjX8g3HvKt2RbHofF15NuH8nMryJXU/7p2Yd6PUGzN/TA9oCz4eutG9s7SY+52+uqaDJDmYF/p4Y/IgRRNVMq6kS+4fsQ+morT+2u/L8rhvzpv3FQTcpB/t2fgtR9s5F+Hq6j595yz3azkBiwcggyM7lmqDH/ioi0B/ISVlCodXidJUww40NwzpYxf8AJ3Nnph5hfZpb2aefiYx9qrkCUa2GK/79UtywrCEn2qV6HHx1X6a03elP4KHmRmuHPQIjJwHFkTpJOiz+LDuufh2P3I979darq26J5tifchqY0BgWBiTOTVMuuXJoJMydWNiB6/SQtdcwCN9MZOKMx61lMr0s5PRz8LUvtj8+Xto3Uk71S6vJPYDTcOg4lcfUfMNQwT6NQKW1o6MXPpaKzQIFNFtsCRkgfX1gwxokuMNbsJ/lhKsCY8OCK9eHQI7VHLYdfFZkJnK9yv8riu+QBuM+tpdfkx2ZgBu/vg/xhJGbfraJMqs+EWS7PEGyd8kp4wNgP1lbpvdOYn9mAr97GM/LxWIVvAzPzmXe1vY3kGzxfeVBjtitc+83CjMFNPiV79TT/FWIwbBg27avglQofYhc/J27/kwWSQ6fjhSo2TfMX6lzAKTdaCHkZpzdfIPVClaaZRS6MfxDT7vicxEeb6XbuQvEfILryI+o2Xm1OIL18zQH5b1+69BVaLfjT+nUftKNOexDAe/P34VlWk4nU7Pe7vV0PUIn957H9g67Fr1GYuZfPvK4SdJBFncYy5Hzmu65iY930b/QqvzBBj+fgeUTA2qmfz77sRLdHK810P+Cqnb5vWi4ehmAWCUr7dAUPVX7cTiCXkXC2CNvwFRQ9nMDZB/Ypfa7vFmKBLrYP2x2F0Vzy+4i2pxJ/NAurX/iRdmJmbBMkQwqM7iPE4NgLFGjIp8vYkUXR7ZsGH2OWCLYORMuwcb/s/cWERk/RYRtaAiSrkv6ljKQh7yOZbgI9NinxkF/OVVSq482ztBgPJjT+94IngibbxtYmZ5KHwqaGEoU8PdXvvN5c2AWUPZGB3qtTEtjY0azeNDljOkL5qdUQ6lUganTLv9Q4XMu8K6Efo4v2Y9e3PzhE/Inwdaxms/0TkzXYKPsqqG+uDaKY/oywOjb9EfmT/VzudaNU3cyUbD3XNn8hxB2rpkACvsCwJyMR3oRoCeU6u2mnwXgjfzTQbbSLuHHsj9g2EUBqp9SIPi+yaUu1WpKtnjo6MTYDy6S1M4E69stW0ZoStjhwblcDtG+H4QQsqRTTaXcdG/dr3BcXsbuadHTaRVDsa6x6H7FR5epMu0yNW9YX0kuXC94ABmEDRY3HazfbjG1i4h2lZ0GlK5c37RqAKhTjxiAOvljjvAn25w/JEXWUmlCohhTJ8ZM3Fchuw8Wi90vujHx/rUqhf+WzrOa1lIIzVlaKUh+g+schXkidIW0MCQssAI2ysUkOUl+wki3dYVX67/hOE4wmS796+i9aTNLJInMVe75dEjxenBhaLsaKvkgp/q7zRt6yPeF64on4fK4NLV42TlJkv87ioVZ+9xJchMyhmuTpoqvyT1BNRK5l0EdKwmMasgibP8zlGlzh5MGkcKZHetIqQqXtFQmBPpR+h1s63blCXnOWPffyTGdURfXC2HmwHO53IbJwjNUXySHflE+n5PhgY0cIKuvuMVYES7l5GAfsPbA+gbdM3lam0zrTtQo4BDrjr5pn1ErBHSC8w9mkQdlmixWFFDiq9561Qp0I4PJlLwC4UZq2OPE9l6/plU3EFsLyVa70J+WqnT2nNMDcWsL75SOt1XZXjrp9sA4NNqwD1zfiG/nPD3ZrjX96kkZBKgHI+i8vZfdBL2jYoEhN42HXXuBVFrTjpsbp3DJpdJ55LTBv1fzJqL+j9lA494DoHUkQLMrjHWd2DGB1L8ej9IxKim2ppJ+JEUQOl2A7ZjkMVeeFXR5DGwwSgoCax/U/HE++n0NYvyjkFHq1aBmaSe9hvuNtnc2rM5GGoLD9xa7E/kZvHLsHCIaTJqYJoJx+CNedDcAGPcdWLGfl1z2d5uEU4hPbtfMUl5jgFEO8s9rNs3r+3inMlS9jRJ9Mb+Ug/ztBSwigQSsOlxSIJJIYV6b8Mwu53I0pFqy9g2t+u+B91KZg2bUrYpFNlAfNwGSDIOK6B228inx407m2u0/9hxjNMKX5lo3JEj8+c3W2M0y1Pyfi+dnspl8qpOrVZYqFHeSxQ0xFItBgZ6h0MQLc1irldN9byB6ujUl0FXThi0smpGg1gOIIqd11y8kUI69Mb1KZQK8LrxKc7tUg4fB4E/LTpkWSXXpHr+rhQjQrMbSkEk535RK/YVMAW9DBvwTLYCNPBvQfQPMReR+Y2XOdI3Sj7pqfQymfyMwBy+Jut3ma8P+FZCL/y9pKHHq6hmWf+eWBle/T3rW0gdpbJA4g7sHcdFJHZJs73wn49jC9q8dDa53HalIu8jJOGW5RHeLm0/+abUIkYQ2auCa11+K9SeyIa/Ym2FzGD1coA23wKQOk5GsBlK+FIvA42cY5IieZSXI1OaElEtvzw1SehmRiUHGNkhLOiR5/RPntfEwCxFSHHRXSHWremqoO1F43LCb6TYo6v5aFDMgjbyPSMYEU3rAXvzRwgI/ZIxJBXKtU5PCB3VCeWRsiPyoHXKKhHpXdZEmRbmdtvhCuNdqLI7oKByw7QY3MiIFU6SV9YvSgtMHLu65MVM6k0qrN0YRSrjHnDBH+sdS4d3wmsIXlIJBMgxecxlWBdt+Iml6zkJnBY5HeXTTRcbcZ3ZfYkFTdPTB8JMD0MPKZZJoICRupZuAsdZsZxvNQsVXajlfTUuYXzVEbQ8yps+vODViSqnqD0ZfebtYb6lk255rtSjghv0+5KYp4AxfgmKTHS65IJujnRDpLmqPxy8PXHldG2R3K60lbleg2sIgoa9kEaIhtJKi8UhJJmsowdmwEwowlz9Rd1kObPClPXNRITNdi4yua4g8liC99cfslCWAnF7d4aqQ9W23b8PPRm9gkS1nt4SCY5fRgx/M/8i9VqI88CGhHFCgbDFY4IwMn8i/ZVAHc9DWkK7+7MG+mt/sCYqDVszVElSi74LlaRtq/HqzKx+J6nIq3GPWUvF9CZlzuFnWTwkPPbybunmPoNwrUEHcae74DT6Dwq6af02lwEcvw4fY72w805kN8MXV+08plUi9G0hdv+z3uaaVeSur4+GXgfMd5odWgVTpMCS264MhruagZ6vOSY8hwADdQJ4eHVeFdRQdtMbDNdiNFbWSqA0EKBBTESiZ/OKxTfag89sHntVI8tgm5rRr2UJH+nM6I5aMFGEWgkOh4LgWAqiCMQoBlZosZRBlWwhOFS+JtfLq78zXaZYFT4Nv7GEaaNyaiQBQ7EFfZD1n9SaWVl5APf3ELW2qDe7SyGAJvnIlnYqLLpdJWmFcy4ARLbo423kartTLx1XDPiyWiVtZuIQ8L1YEhKdKSa+2qIjf+jvQYYtfd6dFCsplsmO2BeozdWC2L8R4e+JKt2zZS8CRv2BphS/KHc5Z4E7HHI7Qm1ZBzMi3B9OP8ZRUwimCWYS2GSwiV2ReDooVFsRXotIo1nIWx2JlrXUv30jZARFMKvuqZmsOSav90slnVOlR6/q4wY5Q16/XowU0dwVErJiHAs0ExI4RrBWGGZp9BXjxFYaR0LZVJcyIEuyxODfa7iZsKxCv6SWzBKNrIa/P/tUpApvxx84NLB6WENCFwL1oP9u4DJwVWRXOaY9Mk50elN4kAz5TqBDYj4oIh1ZPljtD/4YEpI3LbuMxtCb232NbaEha7I7cy3JA2vThypv8xzlCrBtVGTTLefz30rQy9PX9eLVWZXXz96LE7NGcFhzt8pXA47UKqwiyKxhEGb52YuZRJOPKxJn9OB8+bfBKCcn7YcXjENHQg28Al2UsO55EV+WbUPks3JP0Bz0/RCDCAzBk8lX+MwZml9o7vs9Oa0AQFkleMzWnb9eDJAYOxQ1o84RZKcsM/94/g/AMiyE6rAbpRGldB8jANfYw/UGAL2JLiJlqfbukgIj6OxdH4ZKgQ8CVg0bGG8Pb0AYb5IPq7+m7VWMbKFexEdwdX5+VGT1sE4/o/LO2v8VqrLvGPhV3G7QkSON0oCc6EgDLTRaSRvHuZYoloHOihSXQXcjUxaX18JiRmNm/WB++SmZYS+KvoXQkGQngshNRPU0XS8d7ty805lNBt1Nmipk5aA3bRepvlYK8WYRcJQ1Cdd+4r+agNxSGBTmPw8wisx8/gioKybXvjwIbnbPw+1oqLfg7Luxmygl9/Aqi7MS+OuMUQeAVcXP/kYuTPNUqKBy2mbpDbWlFooT99p1qlz4tgFngbTqJrzLbkoJev3iO1tseCjw4aZA++gJPQryWhjREEnbhW3Xb2u3ooReW/NDOztvArRW/kmpSvfbUFHKXGnVETVAj8s1S2sT6its/NeEyZxDVolyFfjEStf068yZXyD77QqGY56P6f9bdtPGgrpmUeDqu72Mr/QdppWxmUuAmPLBdpufr3x/yXzt6+x7863epsUMfDguHS3wSPHjtgoXCQV3n/mXmbc7I/zWVSNsuozDbzC+rv3Hvex0/916plNIsZqBigXKPWCuu7d+LTOt9jq6BTqA+Xq9bkTEy7IAc4Z9QZB1NrEE6NTeFetOkKB0TScXZjlyD/nQ96/m4COrYrlScp2Lp01O7ZTbil7A2l5e8qpsOJA3hG1ZZhgNBTSee/hAuPYp3XiiQNltDufC+DRWAeEkGZaFOJucH45zlCAJZ5YCnM9+N1jqWoED6epo9FZOZRZeftKshHY0ATqwK9BbJfigSUvDfQ3SBfh2TCTTpKUoDMSYIVWQqshOx4jz4zwswZkU6/ORTV8yJ3IJyzSCncBBwCtwQHNIqkRLq7fVU3N9FXur/Bz8ThhTFtMxfEUU8cBb0qdGhaOquwWVrsfvsn35vCDPJqIcLdSeHjv/woMzCyfUVvSZfrLC6zrfKdKll8pHV4AxrNWP9ApM3dXzM7XACYNolwgWDJkPg9a8eoBE9ucuUFfsS+n9bsHyIjYYTjgh+nGarWGOen4KKlxPKquFwN54fd62mIzJtVcu3ezXXHj/63I1lRuyeHMGLK1RYvbeyrfmvNBLp16KJv3ThvfKxibEFkp4pcCV0iK6eYr/t944E+19v1R+cwt5quj12EgW8+zAA52JBLR8ToSXqjvlaQkpssOjzWxUxx0jlPy0eVE9TXUaU5EtjIU3sOsKjGuYTF6lnGc1rRMBh8C7d/GRxSZLU+oaWdlv6UbL6arMAo15TDWt/1eoPkly+8mqzK0o1oXqaXRUYazx2/e5kd739P4oANzi4IJTqfBZ9JwZ8tfsRl8RGGkGgVbYNmDxrqJ3hmf8CH1KsFOO3fMFOUtVwBtb/VAq4XxI9Z4gmG4LnPEQT+9TEoRT6aerwjIO1aokiFftzlpmPHSHg37sMr3G3zcIhuwOpXN2FBgpedWKA8+JLQmcR9N8WWCYL4D0ji6Qa1yDIk58NS1vwb2f9YTuMOywYmdUpHQX2aswfEsTwuCkBF2ojZWJNHrL25SvMkF8rLvMH3fCgvilnqZtPIgiqKgH6tEY9qgfD3CgHEcBWvYea4j4yAU2wrTK6lnyUm5ShNFjHQDro2NDkTDaqEh9JMJeBdYpRBQqmqlYBruJ0m4RI7ZhI3q4ZzNPZelu5PsjCwUHZy3pneLOwix4QGhL1UDIiDjcpFajzAgu9y8OOAhgiTY6IIo6rjaUJPCuDuIPKYghc3BIwmdsmKsrHmN3+Z41C4fvFy6E5oiebrjuRa6lXSTcuTcQI4QSpugNpR8JWZvN2RmrhRtmT+PDxJ8p3e/qoIG3MqWN9MfoKkpW3Rj9pLLSBo26PC1x1/hKi/hRHRtz8r9R9oPSt8qxCF9H5CRERc2Jkyft31kvyE6C7xX++q8u5lFQlBqu6bsNM1TA7zVaP7B/9EP6vjnV4PYTU9KDQ+mxGmRztKC+UV/dYXyikOgVfkt4aqOSz9uRHN+cwmM4pKv4NU2c6Dbna/JDo79WIwL0owPJD7aipzGtwjD5UDI6/V2ZlPvvQop6N+vYNcJirm6CQl6pT3h+Xd4vIgENEnPmnsRr8tXSS7jpVmjwKHOIW/IsUOaXA4OolaljgcWr4DIRF+53lSwzxkNcrRx0XJNrWE5++OyoVcHYtGk8fk1kSsraPRK5UKj7QTdDJIABgBgmukiMLgaPRUZhrgTwGlo68yFgcT4CKi6viTgiM73D75WFdjTqYRMuOg4rIdkyLdfiqFKFpBj6j+rjfr4r/X2yLYQTvB1IixI6Exu4t014Tjgw3hlLvPpVeKyeTT5SkJWh4py0yeKVuEvt1qRWrdtAl4ibJaYRXhYXfu6R8+Tz3Z5l/F1Of7wpgWWpXeg9q/zXZ+yhwm/YOq45/8cm7kX8+oAGX1lAis0oe+w1FRNuJC+OqeUU7dOE31azZk7+WnjscTw6iTiFlXxGG3Nct+bCJcQqzPwylkK+iGs2830UNHrcrod+QcdUDSmH+Rbc7X7ie3UVHcURoyL1HU+UHCJnSgaebF5y/u1BAuMswP3zRyWqJbrL0yx6mNmMQ4uMqAUYeGj8wxc9bcW1jHPU4r138BNIkfgaT8FcVINmc5MJC7Pdy32DCK2jClU5+9wvmBFIOCdeKyPJyknaKZbjq5YT/INy6Bbr8vU4S8IQzh0HaU+Kdj39ZxLzofVDTJN3Fi9xwYpwBloDSJegWp3aMQ4zBSt+6ZfHBKon5XqqxWqeHnr3sqY0Ur0ND4fO58tYQX7oc1dAyKAhOgY+wQbGAUs86WCG1aOsKL+PKE1BrLTsm6nTW2p13P7gigOKAX0FESZLrUwruMMqMKVf8wKjRgveOIwrO7+ySfWMuTnR/Y3poXc53PsTtFiWnGFOWFLmuqP66Xk9sEXvJZmXErXNElb5CSUUXg7odDF376SJTKY/kJ88kRaitbIboZB9tJwiGpv3D1HhAWjlxiezEKA61Ad4WwKt/M+SFRfAQH+n2FGKWjK2+kNn731h1NF8suGemk/bHdhvYXM6wW3D7CRuV34egrebEfRJaih9LH16+mQTux4ugA2hdXkHrpEvfOJ3qplItzXUFe9QQH3svx/5Ii3K2+Of8ahjZOORawUNh6+zDDTQn0I8YpzZBBpmMm0pzS5IYxDEJY/1RBKs+h4CpgcbKa5cLN1AhaQRJ+VafwWUQIK7Xg6X6+VMd5g47YJ6SRpLIwhUFRvyghR/B4KMIEuR9tH6uPAFu7v+q+RU0AfDmsQqLKXX3o/QCMz2nTQ9IgrQrw9Pil3Kbq631FgFZGHfM6aPBAClFkVptNHu6n0GSmjNq7aABUgZM1YVgLoPTmwbitezPHuStquguLDMBFrbkTwxSmDzjCZhSMz2x19HWFh1W2dNrm/iHwX782MP8cgbUsrWktNtqa3Z33NdqlDIVVgFPNzmgSMM8LP7yDR9IkEUACuHQQonBueKpGNCrCaaeOFtmomYboAYGNVY6TvF5Yp2EqSlX9Y1GbXHgUvFY9gvC3hPzuLkbPjinfFvnQy/D1Lak6yA/TALGq4l/0Jjg+X7b1BVAwXsv/jX08q5hxcNzEDc7yih4qiNcP/TTcGZRySUtRhHTw2c4bCmWZiknpbTsUtRiRkJ9bwv+yHn21aMCk8QpMr5NJpfWwkJAymOAhXp27VD/jtj6zBNyS3ceBk1HZPkXe+dC0ptqRw1BqWyl5CxCZCPmrll5iyU38Y0LgW8lMfb96mh0UXrrp5HZ38CUhBtsBgLGq0vjo5hwyy9fjfMtmO1noA3o4nhlLmmfM29IsO9/eG49g5ndSNJS5Fme4JXmWPrn9hC4/Hn3w2aXZLfzK+5EMLgW84fwC4beELEVln1jfn/g1scABLQJIqNwtOb370hq9PFEJYEIDFIqBK1Bns2mTOGlvKJ3M3T9uXixlNR2nELtCExB8yTLvBrty9qHvOH0N3QDyyPOCAuf+8/Q7oDyO6bT5CIJsWk1B0/h4Bx4URrJGv/1TfnAOx9Y01EahvWmigC2K99pOHU89qjb09VgVLJRgE1nflDU2XdRWN5GuqZzYAPa8Ehli9zrVG6hMAa9zKIYOOTSAGQBnbiTFd7SORccma1G+4tccR4IZNpe3Kdv6Jk9+Vf1sOQIgzDnsjaWtWeWb8dBFdv2EG7tCFgyqHmWfK81GteEvYN8ENrsUX5hMN5PD/MTXCunnRQkPyhtW+XDAn6jyIVWKlansDh4GLQWkyt+BSXEaB6H+3W098mxKHOfiAQVewofEF461Uwj2QVE5upPjTHz3Cq/QHcoO4hedBDdSJk1tPS0Vs6Lq5klEG64Riy+lviUhErGja763/pIPH4YThAGFsMVWcKpsWZd8qkwlB6VC1XlLpHuX9XQfnw0jEIrK+FovcOUhTBuMQIqNJb2VoULAV614bOFNHhMboI/62HOGmQGWSZ6fV5hN4S2lqIZam0M8Xgqn2pvZCjwnN3rYNwmqOYyvicvIH4mJRnsdZcAnqGWuL5ro7FyGfkPUnwvaf3HvO6QsjT3pJfdowBysLGUQRNzlt8tqAas25I6kBS+m7qwSUoC5ODm43BUanphnvRQ8MLMuXwuRWHWOZHZe6n95hWdtcQh60w7ghDwail0+B6ZWpJnsDUa+nWQMv6bmlDsjnvA5l/1eRcrVw67XJAxu0Rp0xuH0a94vAPiqzpCxUX5oNpKp5NebVEdbdizSX38x7uxVzVHNtXuzqz3SP3U3fo4OcdwQdwf3I2K6SPySrhSLB5d5fwAn/6xlfwmyMyNLn8abLrMrFxZ91T7/ou1tenueywrIXj6FqN42VWAxCsZOI+T6aRBjvBvaRwMqXU1185avn5czDgWz4nAEd044DF4XqJr5pgXmbRY4cNbIqKowsWwrWQ8DZlxhwpq1GYvHhCOqe+eAei2Hy142Y6plcf/i1rLrTQirPZCIr4YsF4ypiTqF354oqkubvJ4tiu/70oxpRHPlUBK9xEx5xa3c3FNpowQ/Bn/FtjVnwSO50mc8FXj/JcF07qba1beohD/YW0n3FkQSYHysi+pMVFOyjSr1Ckn9KWjXrkzKKsrsk9bwrjMlH5+Y3i3R7o+UahvDe4ThofALqSvPhDi2a82hBgGY1JOgCCBb57JLdUKK3Vx+cuEpm9dvghWG2/VXIXaIJpP2h2Kd+2w+el61RquFtykdL6p6T3d7oYJdn+CVQzmh3j2GfOjrW+zyw/bwQW3jCI3Sthj1gCNUCt1dHV5YvGpZUrGzZg8sN+3nf965bXMtQSDVdeboLDFbRyyr51ZXXUr0zBAnDnxYQnb13R5lR5krdyxmK+iK6qSGlIem9aGK+Fjn7bXf5MV/dmDN2m8whbVsNFqvVrNdBbhQIbrTJAYv5G5dj6ysIn4EU3p8eMsSH66vR2PE+lmrwq9equ3AVKIF0besmxbPnQ9ZPjmJmR0wsmFt1b4Gu6QSBDnYBkovBwKROeYGdP/JY/PK1cCU/DPjSmU99vIsGWT5z3btCKiWq9NJ2Qi5jR+YD4MewA6VjBV3DMgrykx7tNzN1RVTBlU7YQltcIEAFLWs7dWI10bZ/3bQH/c8ohp2RUlgQC9u3cYtM8FleU99N8O7cXJNCFnWhMNN+ctCxOkTEJ8rw2UsCUCZCvn3EgI9eDbC0VzHQDfubWI+eW08fsuxZdlUdkUNE2ITPWngBmVJg9JgRcntxtlNpyQHqIgQl8GsTceB7m5O/+ceeteYQlHbhTdCd4ZrBcL0itHDUy3hArDn/l4J+GLwlnZurelvaJ8ZF6K4Vnt2mGL1OnZCXhyHkB4VzKkWWVMI2UU4q1w0zmeqnICXQGeUP1zTCmr8lPpWZ4W3h14ZjHUmKXLtXo+Mhm+l+YAvg9JegASiiCk8ylRz86ewg48MeVRJ8f0OhZ+cs41NG2ceKWKJR2FzKYZPmn2vwgLSTTBCFXCmz7ZsMawxeJKMVQvz+XdKbYZ7v5rHPrwRXRo1kfQQWh4Rgi5xxJzzVbb/cTaLhtpYQzinJ5dgvVAGtFKUaHGbYXdV7SSQT9luVTr01LO/4hvX3Kz3ayh3tgu63o+3D/mAWHUVenRrOjfkpqbo303Ls8TZ2O4ThCWfa3QrL7ioAKWRZb/ZulCJhoraOFCqj9FzsfywqVdQ+t9oEfzBzwVJYzRs/htp4iZqgQd030EoCcU/Pg0ZfQrqAjusErckT18Dqr/jK2BgR0Ug8PwPSjSUkWQRR+D0LNI9TI/LnOOxfQZDUI3M5ihB30cF7tYtxHY8u29mz5WEpoqXuG3UBKqzk2SrwzHBa5AfqNnvuFN9uguCuXOUvQjAAV5kPsTc3H8ltiqAs9fEtl+XVb7rvJHVcIdFsRTCt/C3VLfCK413evvKq/UlOLwH9DvTrkahLr3Ms3dn5RRVFtGRJN44SCQdhTlFOdUFkege2EsEattQdFR9bFJRt3k1aOp74hXUflvVArz9SiYuwsm6OZ/rY48XG1tIfEv96xvUr7SsOfY0RO4nganYUETNGV3BeuAojm/F7noyW9UXfL8rRLJeUa3ZSsSk6wTfexQ5ZdMSwTlSEHv8w/7Cf3WW0JEfyd6aWF7YDgGODQiijuGrU5LATbnl0PYIokkSpbHOBKUYDnB/bgxLIL8Z+56S065TWHtaWp7GcapKYNNy6mPlVEzw7mFQ9k+E6xcPlvwl9QiHm4VxiMSjxCOYfyLspyVE2khkIWgMHpFJhAroSibOvdUVHp6J7RppAa9kRS0f/XUsDxF4ETHcuvjbl5IspWo2a8ge7YozRl0VqjYq0yMRaQzWSrgOvObm57tX9WYbH4SX5hvvJPSKK+cbXnsecocg8IjoxSF6KQEybMdKS1hk+7oAOui2aPWo8kI6E/w/JWPnbltFUuzE45+cYP4tB8BwbFcczLK5kneE96blqzS72oTRxQaZLlr45CKaWFKIun/u26Lv+U5BPyAJqzbUC4tqEHqHNRiztDLQuQVoMx1cm3x8ufDzby8u/CwHsjeuGWEXFEOmYIHG8Dq+C8yTs3YPfdcpz38eU56GwRYw5/o68Nl9utonohRBAYmw8qsLzzXdre4Sk2YcMhbhU7zhPRXQt85daP0myWOyZqq1M3/4U9GPSOeSpWEatvWH2+NhAh9OWO9dspLDXwJ50oA5cUfD+qw8Ah7YFbWRyi0N4y6k9dekOu6wzcSHpBeZAI4kQgtdDGx3o/kCFlB56D5p3Ss4IIq4N49ZpG+QfsIOxdBYAGWofU3ek8+flFtZO14Dpn7Bq9kP+XAmb8eHILFrnF7qv+bGH8UxyLEqKtvvCe3cFBiV8gI5+RYlM0zgVzUCJDJKRTi+PmE8NVDwx0ZljeJZ94aFLhXlw5lsql4z7XFAFUfu+1ZwKS0+7Wq7rNLu8fU7fWO4yWDHVUuB0O8XP32dlSwFI1qGQUdkgjPzaoOlO9PLsBzMJ3+cEIG7UbQ9hUt6a0ls31bfxQajwdMimasIT8at6kgU9dcHyRKskjR3bTbijELJx6DK3OBtUia5GYMQ2rCRL62Ja7KuxPR4ZKOMXUWJ1LWHJNYTUvVPsNrXwhxgCZVDqPYe2Y+/P2wnBYKgjSuBw/M2OIPJQaFZ9ik96mySBAcXTCNvq1EPYoA0BhNQgknGxY1KM4jGDkbOyEcsWFX/XlTy+3ic6seMw+Y7h15IDV7vLx3a9E2pRnUTO/F0wVTqiqWWyEegWQ3Dj4OUS+hGv2RnZIPZQ5IN7jExdJddF7H0wAF54bhM1PWjaZDiP4nNaLSRNV+pp382ZwzNpXSkLvh2enM52xTQEgee70GcMvc5EQag6wZGDjaUNHfsHgl7UMOUGDUP8tO18fHASM4+06V5rAXQYAYb8hDxdzpqFVv60iBHtnMjCEZhjhkc6QrO4qllshHkGDbdizWstECtWMya9HaydBfgCWtJ6jYOitqPg0END7XkWuyGZA5TlscCc6eLI5xSpBHZhejEBEjgnDpb/Tbkd1DnjUfefBcC3nxvaqVIubn4nehqJvQ9h5kkCA4umFVPOfhsocXhmDboh+5Ux6moBWcND3sYyj+OgDF1Udm0u8G6NIUqBWI+/IBG/vT41oiSC1YiRLOApK1bxnBnc76SHTLLphYKZWklMKqricpHWhbR6MqVeWo9TI+b9BYjkfKTepagcavIwjDBkIWl4gkGiBsKE52G5QqEkOFHfC5TSPA1+BYtmM+2vsxPps3OI3wJQAtCHxmYIeHROzQrRMMlwDsJTkkd+DNr3isLCk56J6fWFinfeG0Dzntwy1dQXIzOnoumj3z3ckrml7jwrhlpAgCsw/GsfncYuDcB4GPDnJzyGWTENLiIM4pLbRMen1iD5dJ0SlOrx4Yn3R8I03yTkw7Py1c9SQ3Ixc6EnGSnSBAgykvb1eF5GNHPV6H01LhIVY/CDN8IL265eCNvwIW5XcbAa+mh4moYuHy6UFlSyI+DLNUvDCM1/E2NybRSFI/19+6Hu4NA8TC36gHuwfdp08CIqqKl9uMyvjsCBgyrgWx3FPy+vm9sUS1WGuBwpL2cB0a5mfCUI3g6punLvqlXdn3qi3/wxuOlBqWgxfPwrYUowLEZOFniCYhjGIzGoQ8c/OJftk9IZ1LcHQdSiX+wCMck8vNZFS9YBKZRTtug18vWJTdoYIcFqOGXIs7qD1WpJjaQXTErD97UZvAnqte+gLtUKrxI+AQKdZVbrX8R1lmt9IHslvrVraYIXQHvvUAn+7/au0hTlPvIBe7pyFsCH246LpsKahOdGjaA/SJTvdRPvO3pxHixMcUx7h1SsMlhSXUAL3bz5Y+gdc79r/VRagZYurejum8uj8BoGgP7T/qi5S1YUeVj7GJOSem8Fv+jJF0NWG/1VkdQQtBOke6F2RarNrUze3/G2AsdAhfqfEoKx9bFY+ZF71AAMuRHfAuRLX0lnZoEGz6K48ubyomhh33A2856z9Dd4LpOA8sw3YNni1xM0jQH4+tWPoRTQ0lyu54oftnWqRuid6j/uG+J6SFIYXwCkG9QQC6pSRHjFqlI96Nv6SrneTSz5uI+a6UJArMDOLITupz+s4gw6Nw/39ulAvjxxChrxKWEWOAmXNvH6qhZAe3EN4te5wbZSffX7NXTxmCh6DVCYaZrlZlSJSwTR2aHuBsg1MJfgWR5cY9zVDzh53S/l7prF8TrGBKqGy1W66tqo2S3O9bIgLgWP8voQejPZrc7qH2qvJUN0x/3UBnsLL8QNovIhmDYOP/qeBlnuBQPJFdgU/Y2q7oEAx4hC7+h2itWf3N16wdvM/1CRZ5WmIi2j/j6/EUSDoywGJkKyOLKUEfdz8P8np7AnFWVvSqT9cnET78Sx6lkhZfsI7QJ+VldiO+nSHTzDhWvFr2RHCt+As2OMIY/yzizoZfyNA8Zuuuuz+PuE9FNOg62nRsZSjtWm2FG4flirnnbEHYt/MrI0rpgTKuelinWmfZjRSIFTyy5Sz3bv8No5il6dN3tkYlMpfSmkNQfHQplCQqcctQD8sDdgiVCRGGmm2OQ/t/6bz1bu2y6Iwf87qGp8Z6wBvdWQarPlh4ICKx7RfytQ3loKqkdqYLTkqcBNvmCe/088tR7Cx31OGYXNfs+uMQDn7LEImOnLoY2Rrv9jPp2O2X04olxAPDozpVAjxtVLI30b7sgmCUtop1d2/X5jqab5DWDQfDgc+l/bRhmpi1o4NZvCwrtTiwScJtIAKztlyn6Co1JOkWEP7BiTS9aNILV6AXxmeCDwGLMmOnOBZD/ip6t/rH4NcjVaL/FWxC6uFasSQ8H0Ce+ltzkm1z1JWN7ylOxxIKOXah3tTaB757RmgvbxDuemeglTIpHtjm5LiQIuDXC1L+x7qQBT/HBQ2OIJohaWcnKydQQyVXZj7d4oa8Mcpiz3CZ+D2mgV2lh29CrpIvoxkqLE5T5hRtwexpWgWYsSBups+AAJWKn2W3LB8rhm+L+XkNW+8gdRlXuqsFDRweAyODXUE9cLDy9m8zeRpv5XtReBlNKgHtHokb93xKkJEA2N2g4X3cTv/ozqw8ayXmCTnZKHd5e0cpWk6P/H8dfBpZ1N4uzY8Njym8ReJuN9zr+DCuRjEDfCBvt0qerao7k9wB5UDHk8AevM+OhO+tNULK+MhZlCceI07EJtD6BOQTOZSr1RrM1yqfXWckZXvJoshKfERlmnECP9+pQgHKh09QHNcf675yqjym0iuBXVGTyl3vNQHnYFqDVaa5KbJ2TN5tkoAeAkEJo8MI3oTBCnCcUmdLD0b42xPnPQ1AD6hddEvHWIT3X1PzKBv4v2dl+IbblopIqFVpO3dhF7msFTgIkev4p2Bo/V7+Qq0C4HCs0QbtfD/XlxLoxvWipYXda4urBmVgSxGOOeGBmFMzFMXf+hwmpmM/lHmE9tpMOJc3/EoHlXXoZprB+5YAiXcPGkuQMPltACxTroanWwd4QGxk29On00S2J5lWG5ASBwrhJUcpzQ2OIW+I+h8bi+JV89Ni2s+fqb46EIo/f8BppTnotNO264FI/VLQNKpM8EXEJoKE0ISDLKZMXba5hzpOi1BSciCu+bwxwaGXTa3S3QnFlkWZcBEqhXVhIL5tWkE3BFQbqQse9eRML88DmNOvkh5/If7fcDpofgDdXzLBLZP4ry4qyTWVdyT/dcBuGQluMhSiK8+r0GnppQoaYK0HKV9RIRzlce6Fdq9v6Ajp8JcJWdgQXczSNifhxqKeVizMYV9ETbds20BF/F3LRYqIJifXUspSACUkH7PdAh4eBjddaaJdwm82pWPhTRhw10mK0ubLOR+ID58UW565JlWmKs92vBnGqt8ucEYAesJpO6cSfN1BoRLexFv5+MRQmsRLpl+WG8fswfpGRXkRzVC6iiloK6A7PdQrSkxzYugoG0L064jSFSJTMDFUmm7BSDm/n4RDEtPBk4Q88iD3K+AptMQ7mUrbVTLD/zz5lwTuAU6Z5ZQUDWSDjeH6pu+e6diT600BIRYR6OswTLZCzRYVPcRIk0tAvz+6DLjeQ9X0ViwFRNLrm34GRS8zzdy5V0K92tiXXbL67on0sr05F7GxEnv964zxF+b6ZqJwpBE1UObhLi3mTJ/jb2rU28afm1z2WW7v8ta6rWQx4kk7ircTg2C9pqoTtSfq3hUQdWpGTHvt2yunoc2pcs2cue32pQbLw2kRY3f46wmSUvmtH+DgYAZYH+ChYpBasQ6wX87+jW2hH5ev1JksqUCINk4gyywN4rNY/fbWKAG8mOxpJ6if3TaZYQ1JXX2oGq1HQrvWOAEFgFiBmx1oJEIqten8f6uJdUn7C8Oh33+TeyLby4VRN7JH1M6ciPEl+H/Vtr7Rj5A2uSEq2RMFPJJBO7kjiHB4T+4KHWCxNdCmPDUZP1Puqk29iVXg+SjsH43KC8hro5NsUZ0AAAAAAAAJT/QOOLX61n58pL+EqC1Q9QYGKbEnloWZGuVum5tUkaCSCLhpj3V1ubfeKXvxjj2cao7/o/BNuRbz/xTBpV6aOYSwRyqJfiOot7lsYU/+igp/s8IabkeJ9OmGZfaxFYVWGu8xI70KgjjwmKpGAzoV4Q0MvUdn8NOi/tAsU3OtM+xsFrZ6c4S3kxv1UV2MtMozwjIEjjTfibt2NL58cLKxs1Y08u8f8IxrfJInPPxzCEEr8nkbm9io9yGj5uLLqhvxeVY2UpZuIN88UpTfxFrDlF8aod7NvDqiAxoeiV3F9GVoIC9PWYOBYo/LuumnhrSkObQius70GPuZaOVVt1G0qJ2MK7t6/rRFY6KYIwqLNOzx3uKZ/CpQJzVo0t74rhDWcMdCFfnmjMfBox4bYPteQ47kSheXUOass1ytxbwm+MfiYm1BhjeUfXvif8HUjZv2eH6jCYH1R7sHxX/aqZ0d9DUyp4V2esKnpdD8rL77vP1k4ishjJOCul8BRbE9rIPqD3Fz2revxdN53OWdpl/VetliVpwiKzl+4OpPZ1PtuBY5jd822OT+MTk3UptTcNeaP6rHMqDWfa/tGEWS0DJ0zo3KPDq11Kzp4dmL0g0LQ6syHREb8ogVrLVGNlU11sTuvVFeJn4MxsVAGrI9u/Zx14SCKAqXsb71FW1zJF7L++tLxIPTmws7nmenOpH3vIBcbQEqrMZh3ajr+4ERRW3GCjLxAkpCPeuksk+UjMJFFgqTNExWVxEgOkM4DQqwthMPf+x4g/j+yMWZD/6k1kntm16/K5PXzPBJf29jy8GmNGoMy1nqn2hyhs78ekeS3sg3P0ZEVuRbo9gPBoJ4eRM20c0tPgkWtETEXIsklzgVyIXICfg/S0b0L4Gqxo3qloYyyh4l7rs2/lFwc+a1V7KBFNL4se3iEm9flxbXcCP06Agm0ZXrxL1z3IqFfOAnXvBIMa2qbdaR4gWfR+6RrvWW796/iJg25DU4AnKiJHoNpmc9t9TuJDLk6MOqSd9dyjaVEsg+uaDA5dYUc26WwBrEZWYZawFXONJL1DAUnyAGBuPdnn5+IPK8WIqyI3pHG7go9qEkVDX/B5YJFqlSvwemobquicoz5ZJRAAjRho4lif6ygwIuVCzLQr/HeHF6zGcup+p/ThhIQAWfGNWDkE3GdowamcPSQde6B1MM9QDWlqwYmNZ0EH3YOoI1BugaC0DGrkeCQM4IDK3uxPWJh92326lUyy//DfF8YawTUjJmB95R2R+n1ED6g6a5Aqld7MmfIIDqjcK6gSgThnfv/ouR+B7VV8ifsY+SGE7n68WUDBD5VgU/SHPBua13x2dP+H7pkGKYq/XZrDUFDDF2f4hxBhtDHcyF8kjDbkd6HQ3sbDm9/B1ors9YiS+HQrEI0mO6HWNRuh2RIPoCBor1YEsezb5mDbVw8ymRkRTFj/JdjY/BbgwOt64mxo6LiXXBcuLkaImQ8BjY7C9WhVZTowWzCe4yRG4mfj5YSPMK8n3+t8gd9+h9HzMwsTfMCHdYJ1zT8fdXv96kSUT7mOTGX0efXzTX6kmSNmg0KNWFSTcwXmkZtrlU/p3oggp9/K22kY6659NEX1wvfHPfFSh4JpFOfJsI8YD7Viyc/3dvvLe09eAgHzKyhaHGsVbaugNa7v9xB4SdssDORl5sVqk4VH9GH/hkUTIWaDWRX62V+xDxsMwC5R3CK46CGDYntauubohEeo92MouJxYeKrCuSyWklUDtTN3fiogtcPz3kxhV8Yf1piAt9UuWQ/3fYOr6cs/eexAaKDFU+dgAMsoSlerPf4ldvDft6g0FZMEowV+ETCYpo2xfqFOQD/5NzmdDw1im/lYiJKyf9RxEzyvpygCG9zAhYaPpMDIzSv97J1mk0D2tL1iHnlCqLNhqP9JfQYHIg0C24hO50eWBo/3Xmhj/w1Frm3btg9d/U/0Qe5mdARe9DUFXTQqQruPks0Fj3mMVaQ88G1C+atJIMbZladCohJ5GxqBE5bLWgohaFf4atsILP/epcKJBIHw7b3yyWbppkqD/K6kXF/06CEBfGmFFFSs40S9ET4aRT46GfQCd1jRZbxVGxjsz2fPoT+nGRFEo4O7gza+BM6XR2IfznYi9S0D07BsLV02FNPV/m5OvNMViWzdQ2PvIsjbdgggnXrv9MVwVONgINPb2P82msfDSqvZJ8qV5hfmfhIz3dvy8okWTUxJ8ib5FAdgKmWaV5+mu54QbMg08Ub3jxHpndx0gTDLnstGGW3zXn3kVrE/ZY6EX95i6owf3GdvO+PnS3QhJ5BS60rhKJLcoyLA3jOEw5H2T5N1elXWdugcOdigu6vxJ4SCNhg0hj8nLR76FDnhe6+SFi9Qjg7wxgVg6kpR1a8139NLxksYYvkL3HOgADFA58WAD/0AACjJ2kkm9TkA//otySAFFiuc3PGiC1nLlEQkbjOdUWEkZZrbNAy8Kt9bu2/8qrERcR3VsipPKC3T3qStWe41y8UiXyJM9uUxvcCuP8f1lB+cXh5L5ShmvTkM70vs+lD9ciVwCGrHjgVL+PPfAEvpIcC9mZRBGx04eU6QkA6YH4Ci5zsoY9OQCspbHTSLlotEJJKFT1mxeftFIxvo0PQ/VxEaKuK6IG7bxYS511TBLnGHYoQ5YDxNnoYPN3zsMms5VL00HX3AVkdRhhHdeK9yRj3LkQhHoQOYooJ4LWsxVKBft/wEXRajK6b4RF3ySWAVT4RtYs8NgWgKhW9E+706x+VGilOjKl1W97CU68zRANZJtTnYKo1DjcQXZSxkHU0CXTI6i/JwiNTEfva7+xY63I16aoY8pUf3IUOnGpSMRKYt3D7kIlJM+aP0tpb6s2BYDqQp0Mw4de9Eo4ocvOccS5BZqUuELsq/GremIJtjqk8cOI83+EI7aUbYey3/t8Q/9eXscbS+7jex4fm7PWVF16jxvj2WkfUeFaSde3bb/AC6XQrAXzk0dqSS07wjouTxQk9YvMO9EjLgB7ilYxwBUMMtDpohkOkxnZZjpWL5J4N+6f2F4NiVySwGJM9jthkg2CDX7vFrCz+X+vBveyHFOu/ojb4T8SdkfTlaSo96i1SI/WXUvNk9/CVONUFUDwdCOG9g6fRKw9Vz8E7oFre6bZPp+pqBtk7ER4g1T+8cyPWSLBjVw8XsccEARUksvqWDmq0EQt5OrKvsZnwOPj4gw6QPZYLu24MsepIJ+yN3ieoQWzV61v9ST6L6FtThd77IG93SEE8WZd7cgxsCV1pwRMN5CpOJtAtL+hsmDFDuXGId7fwKOdP/vNROLlQQ6ieT44MQEVor2ILE2o21THf2J840f/HOILTmzmkVk38Gxd7Yoy7hs7P/D63m0UnwaSGNmZgj88R4AAApV+Kk/dcgSgx4ZNXJdwEiB+RlYba+K9GvabgBaLEtpuFTbP0yBECxbKqRuVVM6LSfU4ANzxnDtw/mGshkg88cWEG/Oh5STPSdtPDeYHddmW2kAoqe7oyRspauzhBwrQa3UcmIYp3A0qQ2JlgS3+pEvppfOWRS+PwU5xSLeLw7dxRaZcKU+CXDah/14Mh74HOMzdn6pOnim06k7OnfYg4BVV/UeCbLn6KC+Bw+LXFVzJm+AXyH8w8ChgsztrsDXke9JltLj/4ib58dzXSz1opfZzNh8tKeRU5YyejlGOff5zM25Ez7fk940qYY19ZYTaF5of8Ww68xrWZqHl6I/oK65pcIYafih+dDgK1nB67BWRVn+RQKEBu5dRz/WahJvmC4lK/XJEQsdJQ69KHLfGKnMmemMI8sNdVnKs3tfCfNlfxMliS0oY2zCAOMu4xHyw5erncW7CkVLLku1QOZGkwkd1cnz4PZ+A9bgqm+9/hsrakWA1DvUqN3+Cuo5cUdRCxXnev5EO+ZnS1gX1xp/UxCsIMASWNNyJTJk85v7OeFnUG5e0Y8riFwph9zYT3JHEf5jIL/TEn8xc0mh734Smz/5B4/7fa6O2pbTmNtZkPMMN9akcnhJq4wEd0aOi4whtuZPeRat8JNZaj5/HD4l6VnuSLcp4paaWhKO4I94135M3cGnE9tkUkCSfdLU0JhAQi+2MSFR+v51Y23J1TZEj1CwQKXHdlg9U+hPG9LEIm9A3HUo2grvNU0iB3iPH7AAAADloAzwx8He5urriGSfZVOyuNNRS+tFvv3H5mC+WI2n5NctwkqvUXfF4nZHfI6WqoQofjeTOpROpjBsy4l9qo8kpA52wo9iQ0uGo8njAuqgWDF8xDwfppAX9NIC/ppAX9NHmZiXPVmxmcqmKmSv1inVNhGPHz36ooogZPKigEEXA9+ybIBK9ZcENau8j0SKlm8WBRzpwoPvNuQEyGbESRIEuxnW6bd14l1TtB24SSUt274c1xDuMZJVjJzoVrsmk75fZ1a6VCayM/pXZaxlbbeluDYcgyiopbXjR95Zsm4z2miqDyeaHsmkFovNOwMyZp4EWqwEK2vK0qiq1bhPqriwKd4jdkPuvny4ALmRq7m41cFGvPDmeRg9YOxlZZYgNr5oRjnVZqEHSTcXzDaSjqERTRxVOXC9SXjjCe1y9oWCOuoj/ZsPK7yKZyODcnAFlLu3/z6BfvaNcYW5hNDXrFIQU+8teKlCRJiTJ7ti4iNyeusTFzLWAqHYSCX7I7KcEgx7F3fu08Qkg5Veew+a61eBowLfDbZI+1f3sTxboxaZUmUWSXqdqGyoAFlr0bbudovw9Gv1OQ5RpfSnHGzlzQlitsEOjlaRaBNKjk88u9NoCD8NE5IoTSVsW6XjLEZVxxnXQuZ8e0ddNl6rjdoKKTssRqLpkNtegQFppUWVT96XOnrS9f5t48U5vVd+9ctdSi7t6k5T9tISDIVX2KTMV1w+6opJbsVwt4/u87x66vnUUaBvWPC/QLO4boI3ZMeAGnpT/GTlFAvcmSWv3XcMrV1uQUBXSBpTxh+Rbqe/ClNRGG29610XwaWgs2vLgXx5YES+F5uHhDqIueUsxz+0WK789CTrAxyShDAuaAAAAAQfAIbeNMyW+7syX7YUaYYvQvbp87UVvff35ZzjIsHZ09DeRNwCR26TSXXZ5IG4M1W7jtLldLAZ9L9MMdlAu35XZwTYas2M+5p5YtwLxZtEUphZIcTurNZG46ZZDz3qwiX30UOozTNm7Msb87Pd8SVGdZKRlurH6Ca3GdUCh5BjLi6Ncc5zngTWI8vidqol7iw/rbz2jEk72+ysveocO0GRKbXOIH8nv2WouiAEQRLie3TCtMbJxXWg36p19avPcesx1MXMjNYzQvtkzHLNxjsc3fSHg617a4JYU3x/KzHEyalh+LF9IY6e4mcLUTPlDAwVyAx1gBc2CTW4W34+2UaZnVy8oOKBCLMxGSThB36TB95lQHayT+Cvn6MHPBjCWRaeiRG01ijgpdq/nj6TXePQFEpG0TItY459VzNL5O6CWoAzxPAlsaR83D0MwQ/o3vTNVCejZQohk+sn+QP3KF8iYJ3rslYwg25fpkujoOY7f3RSlwj4qjyeu9nv6gbD0P1kF6zd7db73UrUdhpB0zGnG/RuteaJ88W7PaCNIqXj2ECTlejfY87alXoPmGQ1MO8dAEnJ0uxswu09cx6AQEGm0q5Fmx229W9xmONqPXIvDTk9OCvubjsnNemNcZXnWobkqI23b8yoI0ATGb4i+Qy6bzwbpEeorM60hRvMbT545ptJYkGyvZp5dSPRgNnDnQoF8JuBNpSLoJOnxW3NZUYRDUKavjo7KW7DKOxshaDfE4xUYx9+Zx+VyZG9Neg6/raX5jykSvnQ7L+6nWp4TfMWqjdbirOfWA8hVHB+b54AicK+70IK3qo9ZJ8BW0x26cQjzBQ4L7gPiDp1pr772RuJoyIKjBK6GRlqUJlzoLGKFffvpdVEIGayjn2Y+8ZkdevnFf8U9CloShk2qA/2Q9swEMr6H5d0rVAubJkAABAAZ6stZ+4okDDyHBHxCzlfCeymXp3juQBz2ugbzatV6y1stiL3s4FQaIJfkpTJyFyqKCmpwAVeXr3ToMnyJOvx9ggMuBdgQ0IsOSDM7ov6WIsKVU/vEx3yw4BfyXCT2UzS2Q+tXWiz8YDHL6rPq7d3SjJexbarcvWA9Od3h4VMDibkADOjc/db0GWm+MChJlPX5eRjrLGM03RoiuFiVwxF8/Ta5U1m8xlKPbJvMzTnEMukxpZd0kghJUhCC0wNogMi0/Vf8G8kZAd1jUJafaS5w8Culj0OSrrfMJbLUXGDsGpzthT6QFtVmw/t5hYZJZrS47BEEWBOx2L40KRJstkxTsN2f5VmkV8Ic8bhI8MLhH79B3jN7D3rG+1kj7aBZim6FlKbY1UhWcOpgexpVpqgx0A2HDP+ilI7o3OFsIZEoZEoZEoZEoUPoncCYn2knJ7LW6LSnR6zoRJUtpA/PiFOnbOKfoMoJgFB8+r2Q0ndubr6E0TnkFRnzJdPwZ7vrMkhQuwdw7XWIWxVa27qoV2umX4pzSD1G+mYiqDzWJECdMBgWZInOkM9HVC1WnQgotO4tpJh3kt28TpcHepiVRPF6p+eehgJjkgywjhLGvA0r4SgLqqn69XYjVGpdypTMI3Yzhw3Wq89gHZGMPplpBAJ90FJBMwOQQG7afLoN4QLWlfIqhwCEpKsw7MYkEf42ck3kvmSxIlyd62H0Fp4vudI9FxkeLU6vBSV8/HUO4OJAwiq46rZnRv2JqgFFf281z3Pq6D3LEKUa1S1+AZP4mFqaplQ0TJAAWqsUYrm8pl/JjgbcaYNK9Ict5wQRsc6jSU7tRyHbjOm4JjDxOTbiEt5MBfncrc5HDP6evjdDVoIs8Rem+GEQAW3dFocG2d1CxPluxYg9jeddwaTSQGIEFHrULJISANDFX+Mb1UUW00M2cE3HaXm1z17ybpHPNnd9F0gya1bTFVyeDpU/7EXKc+xrkjnfCLowR60XsVC2dxBHihc9pVXwO+vLhXyq5zhUZzE7c5oqzwYh/u1j7Tzk3g0+0PTb0JUu+ovCw0ELXK5/uD60mdrzz7w+IeONc3dmXh1DNt9njuqlQJW64D8Qq3zq+IQ3rxVEsPomhHs7qztwwIC7ghan+nMVhdaFSfc3GolPuEXPhKg4u7LIZWXcLr8k/x1yAqUxq9EkHk0FVBM2VNeNsyf265Vl/eD4iQ1tzCnRmlz+jr3XMQtk2uq/56uY7DCQ5vqPlIzHPphRZHrnxd8JmpgoXaKTywlgpvbc8o6JsOe8pO46sssc4oPJc9ZiFxvwt84DUe/xKf7kn4sm5EYaQ/hABDOpVoqz7uHogj1vJ2n4YGkkzzGgL505MlfyB44AcsDA2xH4UOJx+s8XDMhvSVnWX4gYHyZTtEEi45V4Qk3il/KJ0V6Sm7A01D1J2/ooicTq5cRd39DmjGvmR/d4N9Lpv01Rf3C6BkWHoRz2FxY52p2Dej4fjbgHFdpUvCaXFigDH6jeADHmQSFhobHzMGTUsC8WUVl2yBx3KXKxkzecf4qh6g0q8JzrqxN6a4+ghp5U3KuZZURXRU68jClLWsotOo+fim+WkA6uq8b8KvzkLDcj/alVCiBoqbY7lOT12wvJD7g3c0Vw9EwN4A6j57tKbHMUPEZKEL1+6anLISBB8RN56fJ8DnSoXxnQRclf6uxPBtEJcp27TndOEYPsq7POzsF6c9BWYEC0oV2APkWUPS0BEPZqMpcrESUkyRAJH6Y7nFsYvdF2ZAiuZ2nIw3O51UH1vwX5hQtnfAoQbh731Cz6THyiczb2RE7A/BDcXh61ELnOEI4xsMudpZhr5HocR60A8IcFTkKp8mRW5fo3ih6Cw8s+PvMcSuj/TI1tnmGtSXUL/heIevlxKl8Ld3GG2Mfz/NOlaPqsBiZfve7LKeqb/33Qzq36kr+XaWVb42r7Nre3m2D78aBApfwj80e2xkNu7UOLE7stLHWsdYGoRZvW318iil/MmnEM1uEKsluJCk7imSFAiovxS/ysGJO6wlTYqVOftJNj2dn7CVD2gUitbcvrkM+xqPubUqbZS9tJpRX2KKn1b/FjTDAH/ZEV8gzIh5q2nMI1odQxxzc5b45dkLyG2maNgoKycnHAdJPOSmcq4y9KdrF53H2JZ0PNzcVK56qO9ogQmt9tOAOjOC/idK40e9C9Mr7TQCenipmDp6k3iwk0tTLd/HBqZkbtWpPjS4XyxKDi38MIOu12Hu+pPxKOQuJxlfHYnQFN7u8Gr4bc3XANU88EgTw3Tp3TbD4+2VTQ+pVHHAsFHlWbqFHR7W7U7z3Iaj7wgPajrc9R8w6kt1Ye2GgKgiFHlpcx6SdPWpK23KxhG4G08tE3deNuagnO2VHFVXI4FhLQFdwRzJCHP3Yr/aTSTGkgmaB5iN96tfxD9Enh4BAovhmu4rjnmucBujG0GCBXS64pIXrDot7GfHBz09t1R+twF1OR0UZz0+Ov9nQAcp3LLT6c4mQsyquIJ7BdiqY9VikQahmvSnZWEQof570viG0lNGVjPwwhfZeZ4kYvY+TIQnQSXwpNfbyrEnQibmKjZl8EBja8G95kjkj1Jd66EIEuYC4Hd5WSP2IziUHUW7OyXYAMz8UtYAtaTsYW2n13iGjn1FJ6rzSCc8+Xav4IdK0Y10pGei3vebs9MGB48EjBmsCvJKsaJt4ZGc/N5JpdDqb13Ok6K3H+tscxpF+Kih6jWaJj+njXzBLC+u5Dc+buzAtINg3gP3mZjY9l5PsJ4pSAjucit6tX5SZx14araRwYikmKka2ttoSM5YTI8NKmuQoOvkOT9lXLVUhW0yMsUzLnvjvYbfOKp9+e10eaXnth/FnDwjz1FUbhu226MJDhSh+BfMUysuT2cAM1viLd9ImpgkrwwytxP0vfB2fV3mB4FVdneRig0+nCG+YVLkLipfrQwMmTgguCypG+3QfCd4fIqqfMnkjgq57pUenCSV9/55RaAM3KEcQsjBI/02SPKuTyM/c4M9ShIQdBLjY6HC3HIcPpHGJhavmM44o0PUV1sDGUEognPl7j115qi/NS1PCXLNORU0BGe3/s9IIHuCxoThbH+zEEXzRmhQCqkmiHDpuocCYR1vOLzku9AfV2j0qN4v8X+iEtchavng5tFjXJjCzodnFgB7XoqGAO+J29kSNt2lv419RY7yJ4ZvNQnAjjoXqFWYwv6kW+kh6AbS3CUEYSpyOj7fC+8oNcZOLXmeyajKpsTyd7PHtdyNP/LYESwGa1rhZQwPD2SrVtz87ru20p60Iz2iWgrDVjiqP5oyUCglbJqXJRELCIvK4p5Q7gGKiCNxTumW1t+BcZWAhQV9Lxm0mXifx0LQScSuoiThnvbL6ZFPdnJAl//eurgKi0Ab8pCHtUJrJB9qneokY41Iz6p8VX4XoQ+d0ofNSUWVZNgTvuEo6FIZ88AAAL1qdLGGxY3uf+svnq8cijI70yqbvUtxmqOfU4VoR+5LpR9xddrOzP2qo6OmDL+VyL2VYDSgmUGojjfuc7+EfewLwEc0Aul1rlnl/sFOHh+0al78VXMMNv0OO1zkqH5oAr1Z9+SF0b/UEvtfxA+ZZY2vWJho4GoE2FY5O5WQInKEe5IYgoNKe6YAMdrHIyY8Jl5AYxo+aQ98t2Cz3615gNicJhyN2w6lDTmXQZdvdjLHxn7ky/KH8Juo15+1Y2rF4VEtxwE95BhO6GKEx92AriYTiYU9iMFYb5/DtaCUPXztdKUxYlIfU33tZ0Sy3wlq1nfQgzvkkICsXeN6QzOzXirp8l7Se4mk712DuXb+OCqldVrbe87PytP0xZ+0zJFGxIWyX+KFyIRxDFElSFoBFQAAAAgKvbiUH7eLLE7arm2/ALGTP9iOTw+VWSMPKsgnj6JyNYhQ99IG9C/ROuEBwd0pQMi/AZEzfQ6UT0u2YLlTdWeshbLK03emyHrbipQnc6ulXKmFnbwyxJJRD9OUnuMgl1G1yuO2jm94zZXGNLlJ4Y73mxaLFirmoQ9zLrr771QlLnisY6ovEVffWcbsg3sF8w+JnMfy8UDmSZ11zcnPgwv2vijtpkLcPypKJQ31O+WmUoIUkXqGOOqy98JJMcvAQhwww1V8qFJjXDaHvG2frV+VNyY4DU4GGdzmPPwOUlc0P7gdAIxK6G4tLJhzJOrnolxtLSgx7C4PWH+LY3wUOgj7lKfA4b1Rsmvr+RZtr/1AL77lDQmQMUURFA9zzYndc7Wc2GrraXGwDAAlYV/U6XnG2KzBM3gDdlKVjI/E/+OdjMLfXv/Nm/0gYDTlAwEm96etu7tbHG1orR9WXpJ94fkT/lHLHc1WJivZByrKyb1FH9I7VdMJSWPHnAVPh2i02XWFkfZHTIMNCps+ewwVcfmadisDbGaMghVtgL80YIE1ROOSZbMWq+VfCInymbaQEA3AZEH+Z5B7Lbgfnxk9/zXrlm7I2+A0/ErNDnMqPkLtnV+3/bnQ89XTKYFZpA6U6VcFrABv6wtN+lGVJnfokuwG3D1kBXvckpeHQSabgjL0AhB8/NtRGuOfiSN1QeQlxbScMf+LDjynr0OJsCyEeOIWfl3AWhZ4WGdeoNE+Plk9oUKKkJuUyhC76dtws6bgBmFfk2LTJAHD5hvOGeK4ZOugut4gTwjv9QqPJX+9KyIimuHOswczgAAAACd6NKfnwKkJMOGDWv56tZW+/QhhwvJIC5QwHgNhX067z2/QAHdy0hVF8poTzHOSRRk1P7Tq80aVK/vg42piECRqMkixOV4kQC/slC5528cWW8XqPaAMRkQu0io93IeqoqXldpFbRDaT03hpuK+GM/iVq1+iSTXuW8umPBnu7eoqg9PVhmiQqlSCgYS3K/UaYgOeFNEuak2iRAvotwRuYS1MxCD8b1hfriJN2kZtcaFVdXxdsC3YIjcPk7iuotJKb01gAMkaPqAnpo4hRZYa4FFcMGVbgQP5GaGMFJCFUxlquw9YP0wbnE9sgBzAQ/v5XMjgLdyT4MG4o/0XWHe94FcYcqBrb+qBwAvqNAY9/BBAvwastnKSPgjNld+Yq0d+IByrCcMOEgPhALY9xwCfO+Nlc071CDrYzryvkG/B+k44kK6yLG7IMDmXqv8+QWqcfjWxMbzT5nYF97X7Erby/uHT+TKz3ZBe8x1mi5xXebYQG45ms/MQvlSWpgzSr3WkbROME8/14PqRpOK/YYaYS7eX2agMZh1ihuAFxsvjM9kvuhxGbDjeI6jyO1uw6Qlm6omxdXB7SV8KzW1YH6wCC+2s5Pl/XrUytdHAanGr62YvUFqaBurPZiFt6Bu/r+bHsU6T2rbDF93o/1ok+t4Vi2/6WsBAIkFsm4KQosCXt40zN/YpkId7J43gJd3e4iPLZpulrh4cG2joGYm6YIXlQ3MUlGfhs9BA/K7eN9eAKTaGHaUzRpZS+STihU7gsSHASc/v8Ke37CSJOHi94uacyTMN3SfuzjydE5lJEs0tKVL2OmELrv8oSR0OyL+ZyPpOPYukHuyJcYJ5HSj1VptFTMvDrgVmfe6xGPNV+2acIv5AhH33KlZ/b2oHkvXHiX5ty5T1XIFwJqhf+umsJfV4atKiSUYJTuU2xFJRExTyrt4rTApwWDGuuDtr9ou18kN5cXUleLz+kkqLBesWPwb7GOVLvyBee9ca4TBkq5B79b7vBtaQz3R8tAuXTMGHV1kl9aEUmZGcF6Byicp1/kG6Qimz3wVMhSYUT4nuAC+aZONKuhQa36742HcwVEUUIi77y/DlZpWSS9NiygLUgtQx1/f7pBM2nV0bndRTXUyDdBZJrFKTsUtof7ku7QwKQ1+eHTIyaSgSqmNLvT7iiV82PqKpycaQNPVpwXLx/Oj759uMv4q0r6wNG0/mRk2pa16H3NFml9i1A69iOyqxeG2aFcI6egzQ9DqjdvIkJ02+kbvND/cWaxz1mYjPikDWvSV77XmQR/yGpGbpWt3Py6b5PTnInZ6we87aO8ABSqSbEqjDPfhA++xc4+PUTNSu9eRlwDC3+IGcAjXicwum3Ejgu+KB/sl4e6OZoFeVoiguvl6Hv8lPlcOuMjoU37WAAD2UueOq0FTg4jNfB6mPAf838tb2x2fG1eU2f2kl+r4igsI03KF4ImztL0ggfHnxu/IO8SuyNOBQv/avH6uhRVhzLBrQl4DQfVVMGITo/ZHNQodT7rDOeXmR0nROwHKIgAdROOK1pFH61yyezpmGxfqLzTeY4+34rAkNQkQveS/Qa79Uig0WHxLLa9Tf+DoFfFB8Dpg/tO6yNkkf5efMSLqiC/4sKKURVwXjrNIIgqRE2VTPWDb4Xd5H/83XJuuJb7iJR3FPo1RXZTevAhbrj5RO+kgrgQmUmcJ0bvJ3jRzJ/nux8mPqoz9N0nFC5RXbj6GOcxfCrkvw/Lt1Qz0EJlracPejWGhoELT5IBO0vLaPTa2tCxp9jVBsnksJ7DL7/pxzyYaSc98tzqyoYCUyt3AilkE+VF3LTZOjyLqVrrwbEi0jjdXJlEmQEpdtM0lGQzdCcCXTPCIMtsfQRrYKLBVymg3xPpk4jYABGqxoVsERJyZe8Mt6ksCB+oW8hzaCFywhE6NYRIHhoP5uF3oVvs5BRnsikzQjtYYpBoecXVjU6Rqfs2ttsRr8i6+3PyulCgw6BXZ6FIXrjqrMKxvLWVBJxAUKEcgNI05plnoHTPa919y+BaW9jZUcS+xtlDNq7f7r7l6VxL7Gztf0mzoJjbvxiMdOvNjZSa6N2fpdNc/xzIvdBhIAoDa3kbn2H0b376Bqhros2vAgHlhuInyP7jVvc6+c5EL8f0zJkJ4MTvnxL072+QoHxi/6v4rkMPaf7l1bbA04GqGQoFJgz0650dQaRn5B/ltGS33ayaIEoTnYkYtd4NTR/pCGb+WUmfntvUy1C6cZfDb5NImzHwG5pgzG5iQeOE0iJPLPUFn1tu9VrYl/rH3Fv30ZZeQ42lCvfVR60vwRlis0nauOS6PE2166P02TVOuOoICOyzMXLBXzzchVz+0tqI8dhzcBZSaIsGnZIbOiE1HAqxoRinEiaDDT/pMzB9bU1tZaV+6MJbJxjKrjsQ7lRk8jIphRayfs4vrASy/8/2XUQ3W6qKpwY8yXdwKgtBMQYUSqHdFs1AOMlL59T1JfamRW+V5w8uYIDS+iN+R6jqXqGujlZq4IbZqQ7JKviz0W6v2Fku8SGDZPlXJu7YQ5GO1AyyA96qsS44ZaQKjF2uh5+09yd0AG1jGWBIH9L/q617TkOlDpgSrSlMfqP7q7dPaANGg4nU1zAzhooxX3dn7QbPyZwMsXx+UlK6sdWSTqT4ivReHFTsHQYpWEtslFaPwufl6AoXV5EZrUsqSLgeh0YQ9yQsmCz26V8pyJu41/OAAM+7d6PoIaK7RKXXcZ+vtXETN1c3hW/mYJF85C5l7l20O/r2YTWQTFV/kyYoGbSHSYnfTYutG9SrVmG3ReuWhCKdK4Yeaikq1GLumIXBYkhHGr81EpS9ywMctq7SsKOhi54qP1zgFJulkuuun3Cj1UuV/jy7Zs7MjOvwrBSLauHWYrcVApZAjLpUM/grExIBBqKBAd7dtgywHIJcUNjJoiZmMx6G0urTKKrUXGlVrT+e3h2hmFwH2I1SCBfkwUoTjTSvvQEFqeH6+Mv4oFz0gFZHqvfbFy6mMMjf3BFLe6YUuLh5vD7PUO6+r42GWLkIf1CyOgADPy0HP+ZZjlvPA4Crz6OJQ3YxGtZKFtHnLs+zudyAa6eTT0fa73o/kl/iSl7WxVVhLPp9AtYR0UkWfqftduo8MX15MBp6iiy21MJyh+7GqIyDeos1SmJ8s+Q995xsIogNOh1V5IiG2xQSlpYhbkhv/JhGNTVwKioKGpETX4YWzlb9GwzEo9LUX6rtEO1RPiKw1FpOQA3sZdi5Q6oqhxHN7oSabvaDNUmYjdHQvh5/MemzhvF5/6CGzaDgUuZRuvGv4FxoUC5Ir3hpr+BK22H/i1cd6B7jAwvPbWL4eaePaEa66dbx2tfQuZBxx+mkCY9ohuBapKZlIoRrQela9KfKYY6JGeuh2uqdx53NM1pFylBGZ4zoo1/CbsFNANZPSY+DAn5aGne9gR44CJpEdNlWRqxXhci+FPbKPrw1eAu8keljB7UmETkyRfDJWXgf11PmbPsb90RxToOZjT3vEkj90zh0kw5FcdMD6Epfl46bLhEHKHQAACv+6p5Yrk4lU6yuMJkunmoPUwUnOMqHQ7XH4ar7nqcKCUJ7Nd5wFTwg5ueHmNQOYNLSgAH8a86qav8MUNk2bHQsWNMCKaLe7Y34aF0MGCoMFPalG5HgyCpXu1+d/wvIwi+0OirVoaJLcODlVGXMugjIo4vRf7J46OWa2TaWExDeg2BFq37b4yg/bhLTe2LlebMAaivcKgUuvgZt2yH83XqgAAAAAAHembcN0b2iJmF9VP5uA9KEMQHdQdpaevRn1zvtmo7nVmaX0qP5ria72xgq37w9aVihAJCSCao4I90BBxDQYY76M4Ek8NXy1RICu+rtjNeSK/4cpf03kJ/YLrjIV4KwMsrVeOa/MMp1WpjNnuWea9UK8H9b82gOT5pN2kxE2kXLk1bSBnTAiDIP4T8FFl9TtT5oHZwAXodKfUknxey5fi9yQE81Tz/61x7uW8Ticuxz7cZcLY8N+j6u+qDndRdk5gQpfTTBQZzsxh1cSKCBTRrdDIZs9Spx7I03YvVJhQNQWfTrip65UqF/x+do5AgobE3cBnyBsKdg+g9qEe8huvejSd1tAuQuQLAX/Wlm2RhOojIU3pGgIJmg1eCAAhh5R6WJyEWSzJlAJx3vHGxMGl90efW6rRHXE9te2p8xsR99T8apqvdoqTQ9i+FfjD1QskueJHXibsZfSTNCYO3ffHWhXmeYXqBOvoSz732MvaIT4cpsuXmo+lHMFvPLVi7bHij0EGs69Q34dAFmeQcPs76sSgAAAAAAFJuru4Dq/uDZtFmFeNBYuUrrKBrNB/n9TArowgIIUNUx3Mjl9Iv+NDR/2DGW8uOgpqWva0Wu3yyqCqI7fzTTzLU4IA8HuH9hgcgqiZcgXHoH0cuLufOy70++u8JWjO0BL6dX09f+r5kE41ZiJdt5bpCbQ+7AmHcYdAdWnPOlUDq3r43c/lokQfVTMf11EasGhJWDnq0ZeCYWaGGPCH+WKzCSObbZPrSHcETyXh+kEf23r0BvYNjq97C0cwOJu5busgpN0JO+i6YWxpL0CupW48FCorGcQQp9sf3y1dXaC1bREJiQbBPFJuyJDcQckGyCedw7/8D2n++oBO8B+t/sPw/rgxphORLkJeRrZYwrjXqN2tSn5i6lQWdxOtCBHOMUqsjAKk7irNgNNRIyExlJvMXXTCs5+zmD+zsHk6+5IKTd4hpbAC2Iq97WQXFWxfCHzSoHD3uNNoSSNUPpJPLKE3m5mfLNQgb/Xgc/WLjvV+gWFFlNbbKxp6CZL6+O/cibIWbCFJ5y80WV7qLQ5/REYPZFFeW/daO3o//j8/Z2FJiJy2D5MS7fq5LgmPnlKkOTbrHcbMXjEt+FU+LkmM78yqns0umA04kQvyYHmHRK7fUuhE5xVG5Z0pyNXcL/K7t/vGY0L8ARETZz7DeRPbylV3GS4VxgyrDD6jqEsCnN1NAKerXuWZWaqrYW5F1siGWM7cXPDpkqlXnEEMGjQWVtVP+EZoob4vWjtOzU+BdoW1p59RQSKX6CSqxoGild14ePE9YVFI3zPqbo7pu8y0sAUeYA1pkGteUx1FX/cxcu5cvVfSG6+vD2R0193uyoSsBum7pY5ebT6zlRpc4T09RPbHHCthEdWTMZhd25Kl9B7ykL1yJpVAbRr78BvMAE3cIZ8XLTFN48ZgZKkcvXn0XCGqdaraxuQ4XaCTm+GqtmeS8LD/rzQ/WVz79bFlfUsCKx6kWtyhPtY8Mkb0eYm3eUpPccd9zDx/3K5zyGhe3UnZbCKfmSeTv8xM1aqFJP9eWdc684FLz6M53cidKnuyHK7TSc4m50PY3MytiPa2FtAgqhvD9o0rCxAxm4mA/mHPFsDWz9NDUhVMU8awfsJji9yhZkGgXHJXxeQBu98W25HFxOMtDjGTOftuIw6E+uKFKJzrtu9jTPSr6yEIcWI0+/N/xUPmH6tbsEg76jsle68tawaRl1f+prfiy4JHUm7G34NhqzRpN6/mCpfduhUgLlLv0IfGlLzCG/ImguaG2NBO9jA9eJyKzmyI6npBNOI2IUcfR0SOEx41W1TiOWirstAQYQ/cXX/DvsjJeSjWdzBm7iGRvQ4/+JpDzQWAuqgqako46C5jgFfaJwqG0OD7aF5qgRpopPuEKd8ycLV9Ptg5uk3Jgc0KrdL0NDRf+S3Wt6+3eyScVVoTDuDNPXohyi03OFeyOa+WsdeQITXMBK8B9JidypEkXzCYZg7P3DL6DO3hpJFcozOUmh9+sl3ypwbCNFIqc7AHjDJNZKtd3CX8CQnTmBUSR8PLx0HnQmtZHZC6f3j/L5RQAAA3whE82D33LSZ4i/trRo36nyS2IeHdNOm4MAYf4hmF8bDYMpEJG2rs+Ch9IfcqTRCLUOgTRp724Qj1ZJVXijUcQBtj3LTq91htPFWDjSZLekP4+FcuozsR5i2rckdHYH6cB2/soueCkOdfyLbV/2YaS21uNKBQtN5vbDMiNSAZaMR86KO94Igz+B2E1ML6mXXGjCnnHVLZHAw9UufcXXjhtlt7fWEuafZ8bOQ8OONkRElRNQhgQnrIbARiCwe6fpdmY2DbfvXMl9RGRQynzqi97N6AZXho2maFi0goUuyLyvxZG8hHbDbTthBAXs7HzgiFpajhQTtNk0fBdWk9+TJcZ6K3SeC5/+B/+ljmmV0n+0jLUolcgseZ7azc8G0rpXhEnRNsubDIilsn7Iz9t98f91S3ZbUBV5QBkfF35kaAoMBFzmOfgi2az8CyunuW1cgkIbq/3i4bvje4lwZEEpzJbmgGL0E5j9xkevD+v2ejSWpbDEghOZck76L6IejPxWM+iQ+6Hzcx7UTa/Gfje0FSyBAcBQEhoDWu7f3I+JGTFAUNeyyaX5yUdjDQ441EDlbci23nj5iF1dEHxWUxcHDblGO30eot7VRmaJHMxEfdXNn2iH9GedSsbvf1Qob96pEmYteUURdOdyMJy4HA/ShFe4GgKfAAAAAAAAAAAAABtOPCmJ8FZrY3lMwVNHm6kDl1sQ/bxZzCbj9gcQaWvJthkQxv3R9RqzW/xQfbRcTTffBXXJvKvW3220XOiNXbqiA8DcVb4xZW1FuscZd1ksLLFFouZtviSnkxfRYCRHfh9rLtEx6mtQMjBbiDVJTAtL9Zf0m1ao6DbARXYUfuXfxjjjgDxaw4ylSH2lJrCsL0TCZGDxW0ehksH5hMBE3XPU4kWtIFsnaUYmROnrE5ZsLO2BbvhVzSwdYk3MzPR91g0zdcGWhxrZssR4u7OnHTQw+JylhDADflZjVS7fEMcGLNPssXrTxhpQZytEVjcHEe9nRb/X7u2VtudOeDKUp7gaC9XJLgADwNXhDEqo/Xs7QV3NrHgPSCjQgA78r9nI8LO2zY+yG2FsAG0PPbEMv1QFzxEt/SaBBIEAKMgf134NmYQZPN+vaezwV/mBuuavv/MiiKUlBRLSiGB5lG1QFt9gn5IaamZoiVtpXH2+10jpYFW7pWZZdoHAPhpRXKYJ16KDgiXkue08H5c450TXpf4zZ7TwfmkFd8se08jl8cs5/vnxSrSgKjGcV/4BS10y2Zp9aEtatEUbpmMkCLdCpDDWU1CBZVjiyNa9KLgW6N/6tKCa8iqm8PSZnY8p72RYf8Ug7RGdxzPNwvFE8YTkLRHNXgLyPu8nvbcn3FUQ/jNntPCACqx30NFdpXBZMupwdpNiaZ1LI3K5b8WrgpLXPPisK+W7qeRHHBCOn8Tm5Ws0dMR735kKJP/YbG5Y0aIiKAaPOQQ2G4ibqULgyaUMmytx0vxKGwsH1R5LD63uzsGKiyu6sBH2j/N4bdR7eKi5KQmDqhbzDV2cZOSaoCt9IOcJ9P1PTqqGwe6l+yKWUT9ZZqQ+9Z0ZQOKlZ3ueTwI3vxAytwwMk+XPa25A6WEs9dHE4i+celeh1T0alW1nVgQUkHhg+AkKzxR0k759zfXFV+MBezThwySIuoOGDE2tuYEf2Hsk82icBL99RFy2P6If0EwNZN+Ws03GL8Sl4hjra7sI79tZ4TKH5+/2a2Nu0J7dijN9j5pwGOkzoeZijZ31lsBnq1uavXXjlYri+iXcDPwNvzTJn2D6aZxcbC8lzwrXwH30OW6Vq9s8edjkCbd1R2IMZ1d+R2TcdOfrr0/CmbcmJoNoK1sgydgnBRDN26qHJ4BGPkj4SC8EEidw4TTWLefDy29l7o2CxyNisqebGPruOHNml+1xqmuLExfUpUofUX3QyU7Mbvp3hawCjq4yhywjidpigXjlMbOYiWQPdGDM/p20BqOA2DUzwWZG/NXxMPEp0e244jFwPOM2fcMsh0hcF/tPBvnmhkzQGAyw8z6fh1abkUnuJJwoqa6EJ4s6CHOm4DHzxZdJnew0IVZNW7c7JpKIGZhpz54H/F6KnCZcbFbkLpaukKmLAJGk1MH8U73zAYZHnd9Aawhthgz8j8fkZ3g8vYc4Y5GYozsPBckPuQFpzZQyXjtuH18/l+EcTscxRLOXz6VH9Kfs3D7M4kBq+iE5NfRC7MJaVvyoEdQGUUMIFyrRVp0xwLtpuObdxl3c49ZHuh/dW5Lnk7TNXF5SS8Y3Bsl1t+nADLowgJQPlRnNEVY7LfHv9+heOMRLKeiUeRs2pjC+Uytgq/8gAAt2MIJLKodUmaCFX3pOOZQXSB0/5KSeO600c28wLi0+iR1HRTuGsJj7ZWVT03/fJ62i44mmbrPH+VT4a6JEbyk5S8gF79VK7w0VIJ86voC5B3hlut9k2jQ/HGwvDXfovmiGA0x2XIfotW1sa/qc6TqCuohDJTYqOZGS6JbXD75Uuzr8w2Vs7QtmoiTKQwYm8ORjoHLI34LsTjnTen6MvKFxRlcvzvv0GYwMPXXkVct1eSuFfJUj5dqiRqT+6jnsAeV4PXyOvkDzGN8n48PzuB0MfrkdYISwG/kvzuiY3FQMQ7eGAEpPLf2fXuLwwO/8iaomeBYPARE9miEznnFV410vgyQraDk4Gm/KXTjk76Rbu8D3toVcj7qm45rP4rEl7GMXwrBSlEnDCW1dUtSnqE8lEjXJ+qPIfyDz/e7HAp4oL07Y/UDfnvc4Z56N5/DzNHXF0PF7IRMyg2pc8P33cVRjKSjwus5d4m9RuPL6LYIvSu0V7jeOVFLyxys8ZXcxXdLMZ+gyRGJl0jzOxtjuR0nTgvrQJrv3n6+W/RTZdTuLzIVBIPM5uV56p74cIFN2X6EtfDGT0sbfuOA6qi2k5qofbM/doIPl7pCfLOezWvSMcfzukR2DoS1+ECLM0jlNhG6f8xCgIvHrKHn6J/RjRYRCAbbKiiYtluGCpNaaEHsGheowptsGjL1GIbj8ftWNonpnL0F5lQGIuZbiNqa5T2x1rMqIt3ngnQa4CLZNxMgODO9hgpJWEHXu17O0ZvT8zJdUNuEnDf6LLlas3d6VC4WAJM4orCF1B8dOc3D30yDWgskl3Tsm+kY6Z2gxOSUpeL/EWfwWXweEA5TiX/xZ33uZ7NEhI7gJ1LZqB9WsysKjzL8u9MGpxuydiHtzD0GaJ2kn67sM+twuziYVKRic5hvzdWoQk9nGDBTu5L+E1ffn0wMWAqMsoix6owGAd5BV+OOe9yCrs04qBhRijisTOaQLNHudwJanweAaEQoqk/WSwxzSehvSA8iBjQdZAr53J+/Q6TOBnQ1Yz5IG7xRwLJ1alZJvZXxfbIztZW/fmzxwhquufBlooA6gCZT2BvHevI2iv4vmD7HKMfIXIaAZtCujb//DIKk6xPxYSip/Q5kA0k/rMQiK2QdEr0e3bCEPs+HpEQNUnXlNmBi2pbA1nCld/LtMR0n8KcynyWJ+yKNHbPdN2xuCzLGj649A7K0aEMuxKwGXRPwR+ejbFO81O7EYAZ8Jg6HPDwTXjI8LfY5mrVgKdAholvUPjiGkaY77J6mQv9JI7tVLjPdurHxqSYpUJnFEfEnEBbSAN3dJYRJhlaibAAolkjLyZCC5kp4Rv1K3ba1dHNIKG0tULdTUVYOWBxva2m24LjqS+eclbVhH/uErqOmt4ofODX+dqzM4/bV6X+Mer8JlZ1A7TkmPN/c55tGDdqFpHo0h0PLUcKzFs8tQYcZR0NL9R2Lzb2xIaaAPLeR+c3UHclaPYji+EIz+Y1rvtVNj4KHN02slvf+snDTsoqHO5mQgJ/r/Lf+Vjw0NS0Jf/Ai0JmGqSXLJRi3eLlq8V3toM6PNEM7Mj3prArqhZxrjZGZhVveLLlERH9jbGDWbWJU2fqoLQ9ym0hl00AjCPSzVuR4HdB37piUUsMXxPzm4FDnHCSpq6vZZ9F+8OIdSsOdl+0qxFfC5+ulq3Z7O1gGT9mbaMUyGlCbDZ7iEyow1kcx2q0/gN0FhX63y4LXNOoUAu0smSawdllIipr3WB+douHS4GR7PCO2AUt9S4uLxgpB6+uZ83rwk4v0Uc0HY3uTTUKBn96TDpSzcQr+YfTuLBYQEEgMojOmy341G4DCOPgq2Eh92SZ1rAmsqTbMqd30aomqk2BNkufVoeIqAL/RQIas5ATCZJbO8S4hhFJPub6m4j/HOI+Jgp/3CKfBOXCxF2AtmGmdtmg+g00WNTUJRYwUcm3eVtjosHd8Tyzd9rPumPdnLO/RGJp7a7lTw8TIZAFfJFsUZ8XPrGi/ZEjic5lw1rXHYZ1M9LfFtVnMyH27EjpuNmz04Z7fH0g8hpV3ZYzVJ6Li9y/oLqMGFzP4Eu1AUEOJLpL3KI5r3R2kT+kT9uDK9DjfFbK62sZ3NqT2xsey3Hgw02wizv/tvn5S4G5br8Cr9cPmYSdU3q3AdTKJ7q029hy6QelhkUZScwRMKYtrX/doEdVqJMGWEFmY1+2ePZXaSncK9wxyG/N+/wRAp96BaU8RmKYQuTIBP9+DutKetjrK8sOvKFeUx1spOAbt3FMRxFP62oIqUqHL7tGqL87W3Z6HWYPHBM9CTfT1pmoZPKFp2wEm2DvNWp+EyW+hXjLhfNCDVzcrDfIWsrak2xvRfW4JZmbmxPDURHakvPBziSGxmsEmgD2GdR4HRIQyEdFa05xxTUzwgxyNp1sfOaw+lDz9GRQ6FKmuOOd8itwMFwQzf4cZp0vY+owfzNnkmIca7Du+tIdjeDmVwQpbV8szOYSZ7P4pplxfz1GmqKOQNu0T58CEldwuiLoquFe2iyvxHr78DT5YhIzx0aD3Dwlk7fj2GucDaxfE7g/KHSbw4VXy4gCAWO7wTUbMb/UGzMU5y5AmlAcqe8BcPWmRHjpqlExEtac7K0WIrRJ1HNlFL+ou9q23aBrxeb1rv5+h5UVuHsHoTYto5JsXLDW5w2XP61PmBQ1fFCnAkWWxcRGEvefK6MKxk9SmRhOl85WnrKBSrDi85sF+yrof2h6dO8/oGHqih8kABzdKZCWTC6+1OHkXqNMYTZbTM2srdRhyBnI42+6xlsSReVTyZpcKix1D82V8j2e8phohNDt542C5uejZb8Q2xQzQydhxDSb7YIjecA/SZs/XJVG6PbfC6hiU8sBmVlXgK0gKQ3O3XbtVMsnxHoLT8fdU8UW5kdXtSe2If5CFX7ji4vLppcTJtNUb8rd6hUHXPxHmDCpNRG5n+X8xZ7oY9XfUsP4ai5fFSsMPAuEs6+KrikVT6RXSvDOn48fskrXjOXuownjOEjL8u0QKgSqf38dyn7chmwbQdBt0EwS/yyK+DHCkvvbGk/WkKA6QFS5u/yrmqn96HIo/fiGUeWLBeGGkFgwWOYm9MiyBVzaWPJ7M8fQfNNOQuFox1kz11JrGQy2DBg0jCucw1ZFpxMSxvtM312nSfJ5svvRHX4QUFA3/HGVqt2X5TPbFSfaSFiVU5Ffe457wFHGmzBzVhL3k3RYQeCCW5Ylwg0v3wWNrZ5N4VVdQI/lKGiroa20AHB7iEP44RBW/OjFF9+sKxFrcyiZnU6XUjSLGE+NFjpXZy55WAFXrIt8ihbF6ioOJRrXyUBr7dzJ3Kg2JkL5qjyqWIQhupA2WYNvrtzxDk+d1F2WXlI7KtfGuej+MnTNCnCBeqWye1wQa9SqCB+pOaMqwWyPc7hzgKyFV4g+5OBcZDHg2YqMhI4WfiwQHr7Q0U6OaLHW2Iyyy3OyGWI0NTg+sOKSFQ1Dg+vNmH2XynU3PyZOCLxH38ox26KFSkorbxjPZciprCbqI43KIht3Nr/JxVipu5UuYrW0W09D4Y7bEGCJ73e8izzDeI0Fw0FNFPXewR+pUHGLypmJ0cQg049M01VfDVfyAZmSn6cvr9tIUddNwkKwSKV7Wi6GEaWq5WJh5wxJ1LO45lC+D/2jRrojFL3E/HZGyXBRwXhNz5KQU83s02Nw7U8QvQ6WI332XifyXELKfBp2jmENpsw3NEkk29AOAL6lWfLC3gRtLlvRuB0S0ZkUvt/VsLingu3mcpyKNlJfq+5I7LElEdPfhX6H3zKCahTEc8M09IuHFoAOl3ykEGSewnbrUWPaPE76geYmUKSmHG3xqX1rWnTY8x3cLOijDq06Uu28OvcZe1q7Nb+JYzm3NOnykmc8f0Nc3snC7EaUz3Npac0pMw0o3EEVfTJxVFqkY2/k0ZWVv0l+yBzF38gp955KWSK+KNlocaSwwaZppEQ6sLDJABvy7Ng7fD5beKHXuxBcN4+4B53kUy93CkROSSLvqjIojLk11BOvOoz0jrFemVf+2Jp1tlaVBFzAoqwHbVP/57CcBDh0lEG1C4H5VvDyMkyn7n4zJRQ+HGiGcEhVBFhY7jOa4SzwOtl0sSPYZaftWBEYKHpWT9gf5u8D3PRSpZdfzkgqGlGnsyEAHY4CM7UTbM8viXHFZX2Co3Wb5YD6DMXdV2F27tAUZHUonXuDldl1oJPHKYyIiCwrli9ThiOHb42ZVdDrUjKTrk5Hiu7ss3ztYmZpJ39q/AtOGcxlwiko/linc81E/NoSrU8ugXrKKCuIfJpKmI677dgGjd09dQCx9rXCHE2jT/PW4JPDUG8s8fC7d0ULkGyuJiCjCARF35g4S7PI9ZK34mdyOBR1bw2t64wiPuJ2zNrS8YIWYzjRUbeA1SSRG+aIddcaRf7xtfhaGyvsMGRuiGJlvD0E75U5Ta7BaRQfykb11wRoCrLvtWvP9utfdP1WmcW0uYw8n5xv5YUvaAEV/30XQaPRwKghZIdhc0IzqPcRRSGysbg1vBNgTUWkItJ02P7XQUeqjIhowziDamCqvKP0i08xowu5ytVbo8/VEXk7dvULBH3F7k9eeqwdrGxQnELUagqeX9DPr3OSeGrVY5YI8GZQ9hBD+4LSNtEe1S2wUEcljwOj2THwCHVFtq4n5k5QtL4ivSjKELCqARsxhz3w0AFUHz4jvuKY4O4d/sgCwi3uE389mXW8ALifBeZqciEIJyEGEbBU3+b/1u80FlggZqAXraPp+29CynepcrW/ez9GamFBEa4wVWA2hriXcCw2Plm3Gzf1SDjavz7S+itF15E60N4j7gFPj+bxDuNpoWzr5EFjZrr0cR72pn3sOb8g+QKgLBaT3hpLCbdSOLIlxei3FQFwInBd6iEXxEzEVWAb0s7UaRZ7docHmfExCMF0stAIQm9bS1DK/NOR007WcslUfZyXnruMqooVv2zSbOOcf3lhFuOOMKPKyE538atrf5tmbcTSOiMQZMXlPukjcXzJnwixqBdcUxk3JJ0O7qSJeUMzNoSgItLTeaMuzYo4ePjkgb8wKQKHJHXzUG+Ci7db4wJSZTs1xUMOabtgdpcdghawlJDYr4aCeYDSzjWhxK7BODYf/GfUCkrj1nrT6vItoeUY033QAzuOLWARVQsf4biW+xQst96fm/RwVe8f6hYyjYS/DXDfRazeRyCVRacmfwIWPzTfyIC+IpkYqKw/4BzFANOwaR8oysfiBWOUQFrupA/DmL4OBs3V094pBlzFRWedppAnEsaQraU6LpOUp+gZWmbSeFWvpyxt0Uv7UUCnCtzgljha+6Z1Z5YjpsJ/GeoN0wa7clwf55YyAjcr3gVY5C0p9bYHauN7UYo+BeCsFzPEwvLaE3pHFwkBMJByTcv1UTJ95yFLi+4oj/wUwsYvxvftZPBTq7qCoLBh5BkhywYJGNj5MgqbdcNxn/61vjWq7zyffKhrO+vVPss1u6I/uFN8wQ1JR8FAZRxwgGKohHGt092z3e2ZmJf4fb33817QVZnn0CJVxorh0QsYpto5dbgMPY9tVuV7iDx+Vt93Qowr6KjGJgS/YM2KKSC9/Ouni+bNCDbRGDaZqkb1wF0cx1DL+PE9mq6EGAbVAPssybpwFEAEtQz8XhV/EYuGKCvY+mrosgDIinrOVDaa5iEymo1H8VUCwXlYiW5eskcDFMId/Y6dAbFeBv0fe80e0es1vdpVW1zxnXAZ3j2xofAmYxMkpe02biLWcgzrwovFRDN5Ke40jITy7uxcu7IgIqzzDq7ZouBCW53NshY+1twi/Qk7h6cpZv+BBRMe7/eIweoJhPgjOmyNl76unOt2xrdXHrwATXAFHzAAAAA==", "zoom": "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"}, "en": {"full": "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", "zoom": "UklGRlJWAABXRUJQVlA4IEZWAAAwXgGdASowAkUCPmEuk0ekIqiho9LaWRAMCWdu+9r4dRf7QoDJlubeonDT6AObx0EvjO8AcrpWfif7T+o87d3pqK5pvWWUn0mZ5/9/6sf097Av62dL7+zegP9o/2b92b/Xftz7qP7B/mf2g/wHyAf0f/LetR/0/ZJ/tv/R9g/9iP//68P7rfCX/bP+3+8XwMftn/5/YA9czpf+pH9u/tf7IeZf9h/tv97/aH/D+m/4p8w/Y/7l+0/9t9rv5Q81/n/81/o/8l6l/xz7Aff/7H/lv+X/gPbj/M/mH/ffSH4yf1XqC/kv8m/uv9g/xX/e/wvqi7NvVf+D/pfUF9X/mf+d/u37u/3729Pcv8j/dPUf9B/sH+N/wX42fYB/Hv5z/qv8N+9v+Z////0+2v8X4Wv2H/f/tN8AX8s/sn/N/zn+r/cb6Vv5j/x/538pPbL+Zf5X/t/5z8s/sH/lf9c/53+E/0P7ZeA30fP3l//47iB+bSkGowaWQ6BowEMseO0pT7surkRFg1D9l05iC05+zRyjiDy6ox3m8Q/MRNWgdSXxyBLEyyKecP+43ShRkcRiPG3cwWpnJp+T9aDOr0M4osQrlllg1kcENepSmMqGVHCyU5YBl+havacQ0SsvFHbUmHpy7/4s4hCwXbKgJ1z0BwJBcU5xelXUkJEj6UfACR9KPgBJEqk+HBMMnNiINDwj01ICerlEEcbygH6TSS5joLNEr/ZH0o+AEj6UfACR9KZHxWviYhiib9Gd8rqHlk52y6rWOJjwsitD04KM/lcKiZ7et6VcGH6Mh74wfO39boa7GPuqjv4pD8TvIePoW6GH1XlJPtcqD06mPJTuxHKzOY+86cG5TJWp4xM04y9xhRNaP2u0ASJ02QTfASRJKM7Tc3BoSJ4GcPOCrDvJZE+YyU7sX8Pll+9GihQ1kgeHvAudJZhhZU7MDAloXXH9F64YwQReWZzb8vwKhW7amoiNEStGKVZDoG3FShbZ1L3wLtrahzTQHixgVS6wD04auGSa4Y98IlPa1beTZgsO7fS2NrYTpxJf4xMVeIRcMQNm8gk2m/0y6JhxEZSMlx/JpSavKWbT3dSuTc4foULZhHSkP43GwgUQ6Jx3EDzJ40D6hKNZjxUCwa+M+BwdxmhtOfM1TJIrMC/86/aW2aEOwP7s5xdk6OGRvOn/SZUbSAr+kB9om2+16FvCTeuGICpbskF5WnmzZ1T8/Csd7k1biru0Tkz02H+OzXoOAxGepjmd7CMgUmNmTH567V98KOp/H0x2TZQuT8EZ4Kyz8+6QflGaspGOcx2X7TNQxnYV6/cTii3/n8k+eIx7DDv5IVVWMR9/B2l1QjlWdEcqzojlWdEcqWP/neH+ZN0F7hgyMjIyMZqRoxgfAdn4L1+zSkRjLYj9uW7rryikgetWVMtnWjcNeJ+dEZFbWlr+EnTS0fmtOyFtOgjRs8RrHQ4WU5ISIPFaZvY9s8DKrCFB3bxsb6gAcFIOas6MOX6I6/+sC44OeKHxcItR339LmJ54neDkRxZpoOXEiCZhdzTucXMLq/aSrG0MVYvKaRwW9wBk9aDckGr+/KDT/rj679sI7bYCa/QSuc3C5OL4PYsYf/hkkY4QEvpU5QUOeAJH0o9oJcTVZz7ywR1x/GXvvw78H3tO/3pEtLf2PK453qQcr/Fh5bnaOZw3GTJp0Y0pE0pizK23GNcFCaRgaB7mZ71e+hF0+GzvAVUNpSG6tylJ0DbGvCkfkQa/DLKYCUwEka7eWYblJ4mvrC+EFYTq27hRIa5Royx6wch0UTdpBpBvDvlCsE+FxcOnsNIn235cELZZs1wWCDVkUIzORDZ+I8EUXl7BNPHa4ZBeM6eBV1qxS6SsGmVxmPUNAAI/LXFBz5FV33tmjzTQewyfU/vgt6AbMrLgr3DCQXhamv3d+honRQySA4Htwcue2KYSPxmNRzltkfkwNTilHJQLHXN5tIxPJ81t3tgcd6WqHn/Mc26zG2P1vLAFlEXN+cNurm/Nno3bsEgzOuXR5d8N4kuIPQgjgUxEKVujfCEINQ+vwIJjXqNqwllMs45lmZqLwRk+ybhEgV5kMIMb78glzfnDbq5vzhsJ5GvKkkvOQgICAf9B/z8/P0IB/0ICAgICAgICAgICAgICAgICAegLCUM4jVd7Ad7wlJCE3Ulwm6kuE3Ulwm6kuE3Ulwm6kuE3UlwcaEZfgZTyF+ZKu9fjt+YZOxkwEckWeBjAC51W9LWr7WVZUGzVlQbNWVBs1ZUGzVlQlc1dnpBWu6F7BxruGGYgyXqjD2kqqHuXelFX9t6bdXN+cNurm/OG3VzgLb0SkTGK3jtHACR9KPgBI+lHwAkfSj4DEH50bBTxwkyoGb87A+f7+YfqOi4FpWZRq4vW536l7D81LpqylmfO2DeRXnCsbRFWaWCc27uOdiKJ+KXdcGxTEjJ51y/0jBXh9oahgY0mVIuB97i8J85FAaR0DyLJwOk/IFJwUZdSxYJ5FU07ezaU/og3TYg7RgHaYofBrLDpO46BiBv2paZ16SP15H4i2cMhmhIeP7+eOfmKW0RD57zbnZ5zEAcv4FtvS8AlEUHlB9+aEV6hjE8WfhE30OQlN/Bcp7u9DEsVec16u0w0Bwrbu1t9UTFC/9g0Wa8UCUb8HdC0oQt1p1FLKD/Gdz70619bh1PdxrbBMIE/FN6VTQpmeWB2jAxeTLD1p3NKRq+ysegu1E4kr4mCZ37x1hJk6uFtQfACR9KRLIDsiWF9xKstbWZ6CqDhlXWkvWkON5vFRyofCRoPLYCeXSU0Umb84bdXN+cN1ZHTiapYu7ydRyRzYoQ0rSWzXyEYDmCHnAyUBGaj3tNrQAS4BqCkVhfiWIvcEHQpC80C4EG09zcUeVn4bWn1CNfJnjz8gsyTkDgPBMOBnYEAqPhg4YbdXN+cNvEP4yS7OoWZOB+E5V+cIbjTTlSBbB62tjiL9h55FsicAM/I5kqFaxTrm/OG3VzfnD5D5cs1p39OeNXtmuHGFPWWV/qy1jN7cSxZzVNZ7FV4qvJ9KPgBI+lHwAlp7C5TsPoNPxGxsmxuorbNsJ5jmaFEqDCqoueUGHpS4aFx/CVgxxAlsGI9zfXHk+lHwAkfSj4AcS6LqO+V93lIMBqaV/ZhcWkpovSuVw9gR5PpR8AJH0o+AHHGHi4QqNGbq2YPE7GOtB5xapyKwQXWBiCRaylC7PqIAsPj1CbV2Ok7MiON1c35w26ub9JPXIrV0dcx2LWqkA+a2pC3wQ5lZQcm/8dEKmqxcDIJhoU0alnVjhs5TDPW36hTIkfieh716Mcl2B/su2XsP2ODA3yJhC/K0QOeQ85FACHTDYKLZ7Ry+66kuE3UlPonRze5mv/ODa4305XpIxqdEcqzojlTHUcmEHMzSGgutKkXhTsCgMBaDew7Mr/p3TG0dHtwvsxI2ulfBkpwLEj548IynlNpCgLP6oABiSwBvy0bpMqedEZPYDsjahooAWWin7HFAX9d8xzTbClwi1GnStIzZ+7dVHBkKSKqneUpnq9CO8JrrJ0PGA76smSNyVl6ulp0RyrOiOBFcqokxofaWVY+WpmmU5pFJCW0DNHvQfGLmGZ+UrQrXZn9iZFnnF74CR9KKBNsJmMBzI+AEj6UfGElmfOLH5pOgQbm7O8aGQyAVMEuXCbqS4TdSXCbqS4TdSXCbqS4TdSVJKNreYK6/u6FgchpmpuEIXpuQ4WVIbkaGodNyHCypDcdzrJo3AD+skkOuGxrAbS1MAnWy5X7Oto4dDreNP+32NKcmPz9+qjw9W7B2U+dX+clskQ7Xo1MlrzaF3OAEc43XSzNseQZt9blMdCQrNjn+3GduY5oVB5Uo2fAclIao3AgVaoHQ+WZGyZQNYLq300Kh3Yz9fp73hsRQ0tNrxhEv3iFjr2v3qwCSFomNhXQySDdZPlEcqwoQaUSbEEYeQwXW9GkZ/e67B7id1UBMNMnXdg6LFQuTFH+o2MY3XdkgYF//2SwSn85k6VSV8WrHw6OxEr3gudNNvBdwCHTq/cFUh4TbrXjNa33v0B8BxyvvXZeZNequXUEkXczlSA0zb8oMSfpsVPhjH3dX5Yyw62Eg3LQad7ALkVdrKk4fSy4jhzCPU5fDZsAwxHC0dyJLfoCnVzo28EdgqEXGLls+oUXhDy+xlZZ6xLxp77+Rid4ANVsDqX4ORuE1AaqHnrOD/BsUYFSyyKdjDGzL3i9aWedXbnL0ffNF03uZDAyCYOQ+TfXv9TN70jXbW17LQPSoyp8GV/4QSFJXsB227nVl/3bVNfvOsOpl86oCmTfA1F1yu6cz4R19zoaGUdnofl3qwagr/grgLQKkzGKd/WKtDRBFSu5ew174WaIHu4cJgWvJfWvkoiHwfWvnwGbIRzht/r8DBD4gLElyLDe+JN1s+WGmhJLRhvelYFrmMPeYx1qFdpMFV5icgP68Hoj1KWLJyg7bLk94Sj/GzUZ/epDd3FV6i9Kql6kMCvRvi7d4xcEt8qVMNtjH2yUgmR2Ik3x9pnu2iHyqlFfMkX3kHrvyIloJyyLIpOZ0Wkr4r+VCcmmVqu2vO3St9Eqdm6c5N4ML1i8x2oMCzQemcAIzcrpK/RgD0y3omTuXlxodnsEieInV+YCwNnfc9Bslo25XTjM5aLxSds/xtqwLba+ybcZ2WlXPnLi6LE1IhgcMu1j2EuaQaD1rSdU5cyKtHJfbomUJLCAeGSIk+Y1g+HG7ASd3o5S8rRet/tPUkRyFyz5tWYFTxrgRq4MoRp2vAJHQ+kiiVYKEaOQl/2JDxE9mnzmH1TTC2c+fqO6XDmfyuBQnc2xKqxty/cieh4FE7a1I62bxbJRUx/v63HRaT9K4iRlaAOD5P6WFo/8VNX9D34lC0hILhv4K0o1XUcZKI1fEC+Td8ITFf852zK0HhFhZfgVChxATJXjznRwNPMCabdDCQfXFOgqpsQAAAACGupLmT1oPBvZmaRi1NXtWUgK6P0NjbBoO0SnQp6DMOrglgVkZQZew+HyAWyddjWgGyGQLLUS6CW9YguP4w29pgjNCAAAAA2Qh19Cg3B8afmjTrOrAkH4mA6//StD88uU2pj9qryaaDYwZH0gsK8vMFgXZVnCfxdlkXArMklMABhracMAVnY5J7833ODPF+dqgXLXuH0yfA4LNk4pn/NuoBHqJdP39Q9OSOO426/eyqewP7WhNYSnp5eEHQkbUbUeaQm6SV4zm0zY7TD2QA7BB9JgnhW0JWflYLbn9UsjcA/7bb0e4G5rQpTph0g/X5Rehe4eWbmY3ENFMNTOF/3Vt1TvKCJ2t0Y/qjM7kVIlKB6iaJVwY/+aA5KOc5nnGCG7CNcKKe9dU8cmB2Jed07NY9cpG3P4XqxF149MmvfVop/tNNmk6X/yrDXg4PofdkVjSAWG+W+ZJcS8228N+VhuH9+pyI4l4g8tWrZiPfH1xU4+3D7FF436La+cImWQbPIkgC/jqNdmoN76tCBZpUlCJQSvz9VT1pB5s8BTtSiBdmaQKPnFRAOjZA4SlPQtPwOEuOvHrHpLj8I+tSK+yBHc9fDhLdP//xjgPQ+PjHNmTBXV+aIW2gBPP1t/U9qWObN52cBeJ/GjBGQc2cJegptSCt8HQIutixxTV/sjypg9E8y0REHvQiQ+3UvwxYmF3jndUGawXar3jf5bCXvkd/20bcUwa/zzn42f2AHQsCeWqsZVER+l3TlyU4pBnh4G2uYUGFxaSZhlEbeWodRHVBbp4kAEG2c/9VRKPWYh8wpo1K2X6tLhU3yXqoeQPrsmpx/ltiG70nh+S5HXbpoSJI2Avwvmhs5SOlvCLewPpFe9D2AB4pKdo2aS14sYcvFT2uMgqf0hPm6af3eWGJeRpdkTgKpMsuOGP0yt9O1B1CW5XQ+4xbROvnFCnKmsxVlPhi7mTii69SJjj8eJob6vg89OUtDXAQ+Bje7XByVoWJ1OcNA2TQi9YkP/qWzwIfjHcvkPOyCpJ1R0l9F8OY3dztRxRMPIc7WXupfm5E9J1Ub/x+Y3tLLOGf+MPcEJCWEp+veZepPlzxii5L1VlDqaA9H9l0+oe3pjcDe07DpQ45dw1gsFUvsUp/kHBcVlAWZx+77xafebzefZjavVtcBg3bwJx2r/pTSMG9ZJ5t9fQxxzi3MVllyCniCH5uyTUI6ssN4ykRhw+0epMnuvD6OX0YigcPiCcks1iFtFQwFdVkGNu8O4N/OhlAi9HzyoVajoQiwZL6eFWzBnqklD5PxMyQ+2pQk2Qe4BFbdF66qUx5Ez7Ws/3goFzKruJscjAAiyVMak2Zbp7Tweq6XC1BCeFj5ks72lG1zGwlkbTK7vpPmGHhzjeXwDIYbRLm+hMcY9vhdWSvsuIgucofRB9qIpzSzeZkD3OWii1BwzO1MMwA19MrnPibsr5AXf8Pt0J4wAfYqIRP3TdoOmZE6iap5rYp3DyVTI+bcSS2BR/Ng83gLkhwj9cdy/2nMOnQFGqeyyo6gZ2qXnkW8dkwKJNwfhxnxWPVEsbuQdEz1xCvMzypleACR+yyp+35nQWq/fR7qY2TGImd0xOLO01bDg91IsCzJH2VqkrV0s5vd03hRy5ettTuuJJHyz0qTPYvmc6S5kl3Eau77TLyg+Mxn4W3ucwAdz3TW1DxGxAjUsf+NRlgXUYhwMhfXYOvKgqf9X3ETsCOBWLdiTZ1LgCK9594O2r/2k7UIa056NTg5xPInzfQmOMe32FGREtSnuCK3BWYCoALNikWb+K+/Z4gtElXYA1JP2Fjh5dieFldqYCu7AAQ3CXnqPojm84FDVPW73iaamXwRcfN+sZm3QFerRTc5O3B747TmNVS8xvqaNKIHLyUxFmAS5500RKqU7NjqL4HnX8WqGnJx5YsVS4os7LJmM9WVKY2FnVgS93132gcPkVj8wdwqb0iFyPwHqgWbh+0h0l3Isr5YyIZhZ4cqKygs08pzUruD9///786LuGYaot64tWBOzjew23uOyHaIUoH+Po+cJqiQ4/yxELh2x3fX8zP7i4eUNks2NQZun0KsBxsMvpkco1iIe/psQGpzOgiTORONqh81qRf3RoGW+BSsoa+eeAsdvHJR2wbgZV+3kip1kyJXiRIn9ctUKBAS8nFvz1CHTuN4VqL6LVsp/LsbQdy6ILoEEJGxvsc5MrI9jf6QPVJYhxRGckEPXCxZMHNHjAqvz5w9Te1oxr8HL9EuiQRAj7nmMuoHdxJ9JFN2738Af+VTeKJqRtsUyaLr1RxoUAhxAmCAECsNh15eUKKgIZ46pxXqV0CWUxTzUWLp0vs3f2Hchbv9A+PLkWjYhav4UrwUAzvxh/fByW0zdc5ZjjtM2NCyoaCY42aVdhEFvk6By+4yPV8uxAC5UQB6eKKmKuXa25+AWQVezEppd7q/Ph1EeBEp598dygpoj7lq7IQs9u23ZHJAkKXG6V69dUbYc8W+8QITNt5Z8GQY1gRL8ftAMK7hE8ZYWgDS8dkt4FAXaYuC0TWlz0xf34SxbCUj/1ZyunHBT0nr4iWT9XGXU5IJnnj9Egsw5KM4mf1Fd1h7an+2k0UGMY/eAlMeTjZNaMRpmhSTfudYwfOgcVYMYz+JV4Nly91L0Wn4aUamimNiywV18aREu9MSU43uHxTH9St0JQxA7eqkIhUpyhT5P9teFFnBIwcuQqfHEnteOlm1Ail7KSJrBgFSvQR4OiHxrdb0Q425FVEDG9o8rLMscl/Jyzd61e/eSnvRWmlbPvEv+pCVbCDo4KdDopgRfPEnKLl0QEsN9d3HUc01QLR253P+nflAwXFumQE8t1S355KATRspeRK5Q77esgQ8yhwKoe1RWHJFTPGCIani+QScKSeHZawv0gNxMUJ3RraSukLE9otyoNsol/k/+yuQY/BoH8XGXVUaUjsXqchP6B74ezIoaJd6PcuT3GNbBzizIkR3GaiP8csg1g4jNt7pinzGxO0TY7k+ul5QMEwhdHeimhrt2K/Fewqael7d2LfvrZkmvy+DahY7axmIZAnTu4aFnv9aDuYmgxydHmYbs3Zrjd6kHFzIhh8ySVBzRgyDYo+UFGdtho3wYeYEIAP8kZOmS0l29hik7MaW298NfblozZJAkd58wyJVq3kZRbF/JPJIicmy6BATN4hfxJBvfXyr7BoJSV3fEniFowMUJlhd+XtbO15xowexSTeHthVjXXShI0lQwkRxnkHEicIrZiUZd8cmxlRNy00bzGWuQ6IJ2Km5SQegr9Sx6B2zV6xxEfWuKPHbWC62vg3qdD+D/+B6xEG3WoOHPtMcgWBdzORroCXGHjoEFrjuU4Gkx15b94N1nFyJUwmCYztBrNZsHb0gy2t+Iefvxx3hqpL9TmXj9wTUYRxgbQE1+kusD/niwolsM7S/tvte2IXbT61hb2iZu14UJvVuzYSjRM72rmTgnZ0y9cQAYbRPjDEmJSQhx73mCWkFTL2AeSTzFI15L6rINuhQJo+07MRVrmy0XJHHDp0iA0rHNxSdp+id3xBADq9JFJko3DxUbV7A9ayGWTizx1OvqRzT/uWKKocwLLJAY2i7aYGHa93QRIg2fFAL16Jkexjur3EjqqgMmd5fJiwNO5olKl7A9MSKnL1cywljn0bfuGCB7IenQQc0kazfP0GapESVY14fDzUDxqQDW2hTK1723NjwaCJlw/GnAAGuokAGy8UPNW36GKxYg+eNWyl+k8yjJ+AS73x5WFhJ6t92VjiUkvKttWuhpQCA3ZXMK49/P7h3FgAWrO2P8vRho398/b3BrxI9icViHMl47nid+cIV6wShs1iKmN0e2aN8tAPPWK6a9TCvj8i+iFyxWeVB5XIcFSM8397Ev7+5t46h5xumzBY6gbqjMejKTvL5m6XiiZ68S6P0wmxbrCcHxDg6/+1aFINSUmUxoAKyHLKn16VejBfh3cod15sJ/RsfEbp8fgilyerIWM4rabA4itxNNQqsol8rCCDe/ZC3rfRr8jKnBePL0CblRsxNdaxJUmE1XLGUV3o88wjjR380HmPHqj/oCYMs2uNjA52/JCeHiyIUThRzl7BD4sGyWkjudk7CLlH4vME9Lc2Ku9EOlun7P+KdZNyrXjXMz2Ogf3+DARc6Ui2V1eeK+YxgvRcCvAr6yoWcLylF1P7QxSS2p3YtOugpA7POyW/VyQLF7iy30AXPXqPeXK5iEN/cXvGxMqiTT16Vz8NKwXNv+/26WCCIuiN4TsJjOKlN5vFyTAFItFDWfMZ/+fAOx685WPM5WMiZ9zWWM8OsgCBGbNhcuCUKXbZT6kABfROY4gkE7O4qf7IXIgVADoJ0jNCnq+fTZgYuIioi3/exFjHTH4805GQ2zbjqKPNi4pTDcshWeGAGZyhKPvkXuZ0sZPG5WoTKklzwvy2hzrnQ2G2rFEiEQ9wCo3wISI3t97nKzmz4Fo6DA26CgB8SBrKiYkgZ8kh4ofEGzjOZEU9YqFIflPKsZiN8+Zs9qctstuMiiptDXcf5jJREt9KK/xbqcEb+My++yo8D/rPP9v+1DxaiY4D6a3X9aFMgk+LO9TDqTvk73Qp+Tb93jj80SNwmuP/ftDBTwMyPHiHYAbP3mHhPlh/EwPm8Igsg0kvcSAVFSOA71bjoEtdFIPHOdwN56TjQExdwF1u3eAVo7TGPyfj+jSOjCus+QbCIwXNcj/HkhC3FHmv2B9hvcdEQncyoW/cR3FGqWekxPPD6KkodXIYKLZjq0KkZszAlnGaKCSef15AGtv782iCy7vxd1XYlikAcTHyRh7DW6AMs2jfsUZHmxA3NWr3W4wYl192KRUIxtX1s37ArXIvSEJYI7Jc49e0iFBKgU09ArZCPipwvQw+U7StiVz3K+xIWiQnJrNzj5FcmS0ei+Sz8wwr/sdwwh/Z2XcESQu/2XXxAsYD+g6Rx78CG4jMBM0iPNGRd+NEximnaeehNv9r7eARssPAVhyoUXmAZHT+HybFI8U8Bw2QdClBoc346G1yHFgMhV8+/HmRzjFW/taCDbrKtOo7CTkawIu1xibA8FJ6CfqmaMOvOC162lw2M1Lu3xTzambVUD//Jbm+fRwKjyWXgnwbYgkhk1u44n9rtHJijXvglbHJFOzSnhCYDQy+DCA8jVbs3OMLkzwjFWK78ADgGIP6Ofkd8hGh3UelpwHmC8C+q83Y7J1fMNmYpzCERKqgMp5SP33MyAV7cwJ26JW20mJPmQY3uX+fN1d8fo3EmbXlKz2qu0GCSy5IMeqo7a1zk1LZk/WJYBnpFpYGqh1OhRIX6DOqVz8oAPW92rIWUJ3e2MDB6EUwXqApKEwxhI41zIQeTtInWexS5ZJDsGZLkxw5BDDkt4OrFiQGZDYKqyGpldFFeWltmouJy/5aeilHaQ17F7GcA//hyxuDi97pYCMk3yDL4q1crxjeaHcMt2xTI8XVPz3ruIh4cOP1Bmf7u5wRSxCSPSR4qE9TUiMQkPuvRxfbhNRmqXSqEbGFQBCvFmCjnCM5dSxMvJCDprqAiSyxDTlRqfrDH2wN8dGHfWhle4vdOiix1jgbd+gtAV2KTkRVzmLaaETXlsiCLu8i8TRFgQJza4a4I4MvlFEKiGT9x/i9kKE3GKwVDegT6wAIDeeirFw6vsSUNnY+u+zrHmukI4IGxhHJz/NcV+njS2xn80wbJB3hMEtqHYO2XxCX1edM/WWWxcNGXJDjd/L3nqwKGpAk5bT2i9qaJvUHjm3P7d0vm8DfJgnfaFEgCbLddQKjvIPBsuyezo4CGhQhVf4C7bMi77Ij8qx5m0d58w7XDLdEC/BE2IVnH+d2A3n3Ic+ZLVzO7q4FdH+GEJecdh8glQv5mMjKN2JsZ3IVB1UbqLxE6LDzmuusv0jA3ZvN40bAJYnQxx9loSPwbg4BtDBBfOOPQD4KM3dje56YDRtQd8TbrZNaSsqM6Euavj1OExohZPY+xL3aJQL1N5h+bh3xm45QK8u9El7V5fGCxq4aBLIemSOoKoaYCTu6lyE93Yfe49pgCrOXK70QrNTmRLWMw2ywgr5syBePnXkMX9tdmeSqZZ2bts+l1nHoFYx2H53P4h8pQFvIt4ccVNaDdR8JvCwkO81L5GyU8H0lozkkSI7l4aPDBg8FU4lUq5v/T3Z8pmydKzgvNdDM3QkagUOxZdGFyqEW/KMIdkfElF18nBynvpsFIZPkZBx5+Qy+thT/nue+v0eg/MekAwRVdeKThyIjP5xKRXDFsbDC9/uBKCKAxjOqUpxUxUvOTaiuaGxOaU4xlYmJjIguAY7MX2Kk+ftKqcWIHhg3hgDqvi07jXbPqDT9+qcTP0WmRyLQZ2jWwsWXaDdZzEM7Y1iFBMPiETh1Q4f3P7+h7Jt3bDAQvr/pz+asTocm72rXMHDU5aTXtVeu5yE9EkGni0XX29nD8w/12fx/LSao+BpF0IZquNAZ5rgPKNRLKlfighAuULCCWFtk1pWCq2N/SWtBOjzxIzyty+CsLjJDpGy7D/keYZ5+/Af94/NzScaufRHwVu/ikfGPpys2ElPGuBsE6LrL0JGb8fX1QLW/xOMgIYOygtdjbzjdpbrWAscyVSVHvg0TxomMcNtFOezp1cHjbc6Hvy4M/GL6+uG/Evgfu/6UA5M4LfCA8Twwk+l6xrJeSbMsZzXsymwUJnOycNfG11Pj63RXMorgGzrhfsJ7R6n0BM9cx3ra8/209v1hCJfUX5/Gnv+s/8LmS3aqUgAAIw+cCwUA5sNjrpop6zbvGlkjmDW3mo2cG7lozLZbT+WqZxXMHdlZPGlzjU4QZiYiFhkUOnnBUwEnM+IZkxAYw9mogQZvwrJN2fQFCcDAoeMn/OlaK7/XTLFmR8PqB0azfgABtAGwrjsH9n3YkVsBz4d4CX+JNdumkP+ed0P7LtqN5eamud3RD+sljxu1Ae9XIulzgt+VntvuOq1xnGGjzRN4z2lU3rMO6Ppu2MsVxcY8yDYDyuAVegu7z7yvbqSe6Kdbu6oo7JV5sDjXdud/2uP2a+qi6O5O1ymNMs47scWIz4h1YpnaPN9rcQ0ERtl0kVYYFkzyTURqCTjUn+e8VWAPx3HKTrresVWx3mum1KV/B6nWoTtskFwQLBTb5CfQ7H/lb36Czx4YMHOREvbCGcRY/yoIHgXIrfUka0o6VYhTMVAOO0xJHY5bAvQ431wry/klHuunUsD/k3B66Z3aIxpZqqFcpApCfUfA2NytnR/m/x8psDN5abkw9q1DoHVHs15MqIuKZGf3yPye+KXeCKJ/CMw3C98/x+6NEChiagpusVqZDXtNRN5YxDbSanWgSwi7tLrg44Z8XxiN9iiaFXeXr6gNIayac7krP9Fk7FL+RwbqqfKX6R2W1x0ARZTDGSwAyohp4P2hydOqypsxuXYkzC1SlbB+zdeVQdG/c33N9v6xbQZ9F2O1hnxfqo3B4irF6SYC3HFhck3Bue3ewvpurNJjKiUb10zh8fJMVeK5DefhailVuIQFRTsh52qWGgK6nus8HCQY8ikKwtTAE/6t+uWXdXrFBPGPwA2X0c5xejO5seQpnMGWKWO+rE7Rl3+awWtETmwAM9omcNUw6WEDyJpu87m2VKOr4DbshlGbTOhT1b9rJBcF37+N2hOIsvlwoce9qHzWl1p/074GbkVg1nxelNKpAMyJ0SP58tD3bgmaZHSZgBKkdiB5b80t3PvyNBamZHpU9JBtZm+yYHDGmBSkHom1mxuYsemyJ4AqHWLrneIMStp4JFzmpdo4Lx2sOaIHKpaIk888RJjAgVPULdIskyG925GcQHxjh+sTx8Vpx993vjqmplS4VwL0PSNjGP/gW3S5dfXKcSAetyCwxc6BZT9OTR5uoMrndjX/ikFcs+a16GwcbxykTPNutjFPMFNFeU5YsjGCdf25axlpJ1KCM1A5BgXi2Pkrqpc35rB0zPAXHNre04B+/bQqcB9vo6a2OYAUwGNgoP7mDRuWmXlIZaEdUShBNvuUcROXLLc+VLID0fZz51h38rQdVSA4TdjBF71wV/4YTMwhh7rqH1HJHiW7AvfKUTJPReXosADUxskDR+QFjmK7fsHv9EApxQF9ajz2flaG38pd26bXZUQF+IAEVc6o9qohUXp7H9268Mb/TrZdBW7FXeITEQGjDeCq4dHYUSZ4a71joVCBG7tRDEj5m66F/GVbZF1BfH9BGATXAaPvBZzErZxWl6GwDCajukolf+3awTEd03pYTWQwyunDsWcVhS1IiHBgTMdk8IWYzDG/LA5xE/+ZFNAHd59eT68I9bWCPzkZEi5gvX7eCPm3VMAnoe9PwOOUnz3v7HuszNOWRGPuXnMNCZcVA3wck8RW/VG9qsxFzu3vPNtpHBGhPtlKjwBTghcgwo7orLIY2UG0h8WI9+vU13Zn/tWCAj/VNCsJoh+pjcOWiC50JEen+qyZAJA1wAAbbJzbeWwMy27IM0a2LLRxiIJExS/1bJx4ZcT025Mv3sDtxRhSARNVYeG8c4gvyLcHSxhy9bEd7pumYV28OzfU/77JbNEOEJ7Qhtl8TV0Ed+N+LSYj3/HyAGtOm+Zi58Uy5QqOQlcUhDWwsrjp4JGHNdtfGawqcOt6wNT38SmYkMyZGeGBo1MkIQtOoiOH+8tKIMfx6iHBw5GSpgX7EVWcDJQ6oD+aUYp5016DCY4aQOz8YPiXWir0dqU3FXzd70s591/nblh0DqmFPAQAAs1zOIrA9vC5x9XWd/0mWH+moVGRVZLY9O/gMCDgEGYSyimbjEke26Q+71/zPiVMZNHQSgtA805qjAWIP0PJEFvvpc91acaM2tCJotTEd7x9APw2YIS1a1xi6qVcE2+/Fk9yiWyGu+7WkZEHrs2cBv+I8w3mpZoQ+BV9h5BTtS+I/Lk+c3Zkp2pbjrvJWuBwZcj7mJzMy+N1q+UU6Rc5cKH26Pj3ab6IWSClyBpeCf+dtCdfdMbaau2DzUlr7KWwnzCzwpspYYGTlkstFTmxkUBAV5PBrccyA2HI6Yg392cwh+HxIB79hma+ev2170mtG4tVTy5/USCDX4C9b/e7Ii2MBKHqNsGrE88ImIyYZXqf+7xJ/AgBvliReus4Q+VbYbExlv6CKxMO6ZCaJ+DNB5MarQ2w1+uYMAI4+8DI8HU51Q3/Jsk5pAnyD3DRG224AgSUs0JEt85qGpxkQtxIbzMjc90w+s03yzSeu5Nm4KiWcOP5WgQgA+wVQaiJoMeWaDJxx/WdomurkpVmJ9gItRbRfl1FbvfYdUAYiyjwbpzxk4UUPFn+W5MRqw/LTapJ2ljN6Hq3yPyC4UmM5Spcy/ZIhWIfXHcuC58ubko1GqbGugZ5M+aP7+fBvhSSQI73HdBS9MOYw31XcKVu3d9mmxLnjAKhtAcKWeEQ2v+9XbEiBQg5+oi2NlOqtSPqmazPniMtL5fTGHV4pA9s25eeOwFkmX0zPfGbsboxNNJX2FJU8qogf7LJ5ibO9mT5kEN9Zg9Vi4IOZzLMnl1x5F7wxX+13qYMN8+EHE9XH4ri4GnZKaqHgMqv+0nkhJLM0aPhmeQhy3F8d+bJYoQoZ0jxCnE1cA4k3M3FjHKJeoiga3dHwPPX/YHwYzVUMO41CQOlIDv2by4JpUSPolNH1twtQ/U84DkuEwp55hLQuhEKqyWzTocBx9HRWNQnJSUqtkVl0kmcEdkV0RvF4eiL8nl7oLzAO2URbhq2PuZ/2+Nl+E+0oGIV3TLtsx6QSgayZ8BGHrhC77G9dGt2eF50uZklN5ZS5l8xPoyObZNFjv5oMhANd9y7ba3WSZdptFpA3V3JTJ+/hQreNkf/q/v/x9hNm3dNTGsufnyL3Gcwuvb7Zk60BmvJZFNakt5xVUW5O6Vxfz6RghPI6gUZoAkhcemWyoVGrI5MVIzTYq4ml46gvFeVLFGaEXCG16rL8JSq0k5A2zEVrplENXKCge2W2M3t5SRm7iAoOaz0HDix6nFN9IWqpzBF8tFq5lclr9bnAYpBLE5NjDBibqsMqp4aGJojdyL9platj+Xp7xR1UEPagPu9uKXsHaL4tMXFv+V5orWHfkQFvl9opVA/yIiQCkH6ErlO2sYSur6vzKkl1rcVITvb4vaTwPwHzRB4U+vgmTfZu/rNmzXtzW9tMPvZhYYLf3lCIJweiHIEv7SyL5jovgtwtbeOVGSp29nm/yhmcFT9+2k/xLYplGQFgvQz+popnBe62IaUcKVSLNsOgnntbnppKmLMJgN91ZLI45CEE2WPJuscj858oiprv4ovj5BqT8bfcHg5dG3vxy0VbgOxiHgmWv3gVtp2PGYHAWqNT69l0mUi67txS0D6quD8wm+Il6ewIa2yJNWdZ59n6UpHCChV/tR837v/HvyEql/NdXBciraGOjFTFOPo/h2TXplagbdq3+tiQ3iuXudcVcNgpqFWUFR7tFu6DM8pF7P1H1Qy3R+32cCXQgnTU14IE6vUzwIcoJS5tKniFYvHSlqD9QIYZZRR9wE1z4Sza5LWIP+9yegDIInXA05Ego44cPdmAfwHwMnDXi5mMttFgIEz7cTb0CgL8pL3BWQV5Z6CcnMOuAxATldi9ztnWqlNmZKMW7JoD1MMzPgzFS70tEixtFklcd41ji9Mwchd/ieBQXZfQB760gVKUI5wJwp1h3j+DX+GAEGJJY/Ryt0WfMY4ezAxRNzmRH/dLzSRbnRd/zZFTAVkFioBGvfbVgoRxIsF4NJfIL7HnysmawBYkiO8jrrUR2wQX38wwaYhphPEZclNLDNj7nj+WuqiP8RrNdzBV/OkzNbo0t8iS0cvxo0qq0ryvKdcPlN5jx7ZsERGWbZN6XRB+kPI+25I6GCTxdacMqqoc4eNKijnwhOFuywf3liMiDlXQosvRU6xs6GrNmAykfxpg8dS4cZEkWJGL5P8H4O6WGUxn+QN5unuLBH6FnS1cO5y49fFh/LdCFho1P37NyFxTPQ0br8Ee5FdgxJZjcWNxGPX/oLpxMRIWU0a8CH0tSQO63mV66kUFJOsTS4prvNVQQfFgf/arxwQZGPrxxebMexy5NwH3uNAn3q0rmT1y29KXpk4J6Le3EWWpVwoZXDXEiZm6tL4l8vA77vC/ZtffCetBLL9MVDERlMoUyR89zMCP2AqqlMhTi3euWerSa7sqixdIqAXi+1l7Nv9Do671p6JBxcROIFPG7C2y39jHDTnX8p2/3a6JvdQclRZNe8yofATH51p4qrBbbjBxmpBLl0M70/6S26udEDog80CLuLuYCGCYnggAbqbof1CB62qrRu/rXCOcdgjWPjZx2h8XHKq6M8b2Sk0SpXOIBajzDE0/U6uLeN8/iEw5rjxmrM+jVwq2cIMKbb2pSwli0CE2jEIOs7snX3WVnbkDGvaxOxxWTYrmtBhfPNcE2ODcSHq+8QmSDM+KKHzQcZpiD3ckrMi4cZB9j4ZJub91S7yLu669jhcinVX3EzMnsHRYcuE/rPmuszaIdOiayiLGwfgM2PiqHCDpr1oxD/cqS9c1RoOhV9Jt5n18qJVtyRO1yPYpsK39YCI7Y8W7JT6nYiV4Uksd5/r5u0E6UDe/MsmsIvMl8H7APgOTASMNMMg6w4SLdHg3mjZ+HGiWLZwlTqq9SpKBb+YaY7F8nwW1+goZURDFOh+5JcHebi0W+yCEsviUc7+7W0/dVvdLTbX1tX7yaUVUrjdPITrOUqBt1Vayz1jnEMObazS9/yl3pjvHay93tjFqqX3AZx0+r+yLzZ8z6DEpMTtNbMvR8cT7UhB6T7VFH2osjg84x5bDiOnU1aZFgqvTKiKOwKSZxMZnXYvrtlAA2K6zA0evvbd867vZcU2v5QW2A6n/4h3RAAodga7ACS17mqJRCN4jxWFH0LYe+YxaUM8I638WY4OZH/uLBGXzedfRX7582ML/ZscR16KzVIyv9j+h0WUfoYMzFY0ugFq3JNOQUkKJlqtYLkAAAAEPywLtMU8dOpopQu1JTjsVrxyPqHJh0gBVMqz3pdRsAFzYUBGrpy8ceH6bOgHT144OZFI/MZttG9ZGrUVrbSpnoJ/hsgxkZi0kvrb27nZlzKcDm+uIP8FYSiB8XJ7sYbB8aWbFFSf1uEG+LqMHoNXtR4Rb77M05VyNFIxXIbNQrrhoY59Dvl97zMh3Jg5XckX0S3j7DAatwFBv84w88j63gL/mlys34RgodNOFv68ljf78B+ybJG0oWlZsSmA6kGepb0Y7/1OmB+hXl9sGkWt2rQf4qaylymzO4f7W7uP69icctS/74L4y19b9/j1S0YGyVh0v+aoPSbpYgqGz3kmOUmnTmPL6yztTTbZGygkzL9NZMNNp0vMZMN4G6TnjlIUUTU+qYByeVPtSI8wYLd0W0CXQUk4o6nJzevKR6s6Um4N/3BV8mgPelA8cNIT5knPxsr6iA7J3KzsOq30EXglZSQzLFQmhIY99FZFmj9m65u1R50X/gr2fadf/NAJjFJA865CxxctdUL+lLVsFG+ilt5dbvmuHR6BIQm2wyxppDHQPWhPXs2ix8hgqQeaO7hp6Rnj7dxgJXwlCKpugAjODtTgEKrRcuIa970JaaPzCdOuOwoZmYmYDEdi2ERfLDnkyM1lPcQGIthAAAAvm1GX1+MgKrEY0+EFFJykczrOj0mWTxZ9YVb3n8m2BiDkgzlT8wFyC0OD1w+aIHKEEgZVXKEZo0aNDpMNHPnz58+fPnz58+fPnz58+fR+9MgagnAMQuq60CUy8scTdkPlM9w9RjrWt+7BwHamUZRhw+f5c1PKUGUhRi2tWbaCO1o66fzj01tKoifG7o7OgC9XDm3N7YkPv7RkZfZM1cIKrot5HN2qauEFV0W8jm7VNXCCq6LeRzdqmrhBVdFvI5u4MP5I0IkT3saYATlbvkoAdwdAl2dqpq3JAho+CHl4tonjaEXKWRTmkzGFnGV3R/sGYVbqPyD2ekrT9M3tKIyQJpg7PxN7xFHpfTJSq4tK1SAxt1u+U9LsFINFPOOE2LDxIthQ0iU11mKZp/JJvzUwpcnPJ37CZ/jxCUQRbDCLi32g+BjP5JNcrm/9RzciHdRK7ntPTr7tdc64rVhcMXV4pEB94bYWexYUneaI9xMvddLx8DPf/6kjBbM0oVmEX/qcuMO+rPoFFsynomG93311cVQP1un/Ir/aQAOTi3LnZbw8nZgnB+aEbxhYcsBIIPc9PJM515GcZ3XcJ0EbaJ5SQ9e07YPc+8AwODPQQU9z/PMC8b7nOv7DOZddZP9QRf+OvbcAbXimEqWAQAAAAAGIIhCIm5u4SQl3bP5X1cEWEZkxgOE0y+BAGvhsKOSfQcCYTF+AfJFw0CklFXmFPLMEn5xBXc5+UEineROG3I7tH5GVHm8KKKBmyIX+HtnWiJbSUaCxU67CC27F9mARSQ4h3936gP7X+wekSxbx/jZGxNEYoekSZWKhIOEzFnzOuk6NkMYM928UUbTf/F/o29Y6VBMNeZtAv5Ka4jyddPvCQ8gGSgx3U39LwyNLjP16fd5vP1C3wRMYAlz80AQjYMxu1GPqhF0W7fW8LRmOXVNWbmi3idQjfvPT2gY7i91p8CuQwGtjnALdx2zrilvy5ua0oR471Y0NL91eHEAfgRrflt6G9I5ARbVxT1gGk7RAAAAEv5wbRKcHnQ31NmRFpfkAAAAAW8jFukqiqAxF7T4H4HExFNpufpFlYHuiL98SWhdXWkxi3YAM70vY1rQBb9wcyw4gSTTOjcVQE1Q2fB/UnunEYka1/BZQ0rtAfpTLPyIdlVZhTN2+CQQMkKFyUOkt+vhYxxJCHqJQtwCbupvYGoTLd3PFKh6N5swJVrVr42dR7r7Kz/Ud5qinpJFLrB86b7CaCQBxj3FUJAuPdMugZICdmDz/A9hp2/ScdGEYyq4t5oU+3pmmqJoieTWPbJ99dySdnJ/Rp3cznMsPOTq+raYJAHyc2+WQ2t0kC9e+DcRxaAmmYzwX9atIbwWuAAX9L/teYanLmDmept5VouFRXrkeHjd3gAay86j3gFmDVvWdmISV65MS3KLd9Dg8gooTP3CFDAJPa6W19DfImTORDuip8dK9HnFnut+UyPOiYoOmhXJVQnLWIZ5nIJQ/IHWRPPkYm34a6qLsTAc8zdyWrWfAkLWFdvDPY9c0aAUFwsT+vsQrRwO50X/xMV1RZU7NNvww+GTXVumMbadVA9WQzEpc6f+Q3+XWbxKCmMo2+a6215z3Ot+l6t5YGNuEo0evwsss0vSH/F8lqQOK6U/yDSXVmWDQWJeWU3qZx13d9dsuCzlEfcbqAfDgIKnFS0p7KOY1/zh6FUSsO0VZE57eeNyDdlexNu2fE6xnpyUyYYgjtIx/hOl0fCvOcm2iqOqN5AAGFC2PI84JL4+8OieFS5fcVULUUWSgh045Ugt/puUSUNqTN3SSvzlDfkjxPP8GoY+TNJip/T2TqAUVVQ7BwVk9+dGfwnpfgm2UiJFOwZPc3IJBDTx63OtgzWHx+nZ34oAxT+bUQkLhlBM8EZvRxI47kYb1BdWV0t4p8MDoCos1S2uGttbhsI1aEvZpccI+RplylgPZIvDD4AYVAnaR3PGDJRjorceQzqkNI/Vzi7GQnOFIgrJA4NV9p9e+Kb73uuECCnMm+fUO3wxdS95I9ql894BfTfXnqaW3IPy/cT7bx4cEsPJiTM0Y83BiVr35CVgOonsCRO0r0y7G3axCHiUQq0o+GvjDAwl5D60uqeAYIFOnCM7GFNsfObHazEjOVmvy7/9n2pu/3wWmmttyUm8vBzg7NNC7CfKJl2q7oRB073f7cz7VE7L8P2Wm1/jfTPatdHLVS/vgQF9Bc9D6p01IsSLpLITF6t9mQDtF+VzZXAd7YGnrAyP8V+ChYN+HWEbEKarBORiho6XFPsGLyfQOgHwPVWConItkzy1cuZjrbpRiPtlRNhNF6UAyvkHE2at+OYQt8XdbUXMcg2HhVDsUN0BRBpCaKQ90jJCEHdx9JGpda4DSF7b5uyULbavz3hp04ieuTpX22DLKLsOxi2sbzDg7jFzQlJnb51LoKvBWKZ0otFAhLyUGNRxnby5ReYmviyAXhL3aXNoIWSSEGDwbSCgEB897W9p/iJUJ4NhS6ZVT/EAq+7C/DtpaR3MF9b4VlZZOq58UjiPGTowK39Ri0Hdk0ZzshXirJm/XWMEQVy4y6vtm262przd5cPQupNd07NxaoaC2P+gZG7ndDL8oBNCzkbuNTZXdfbPHqnJuRJhHHOxvtHTwcqW//WVfdidtWadcto+wV5D6ohc9A1T8zJCst1hvb44ww9bApFGXf8ZbghcgdN0Ri7oddBrp5Vjjz0a8Rcuee2us+WkRdA5MVjT7QdLuAk4bi9xO4jfkAfk68BwkMJShxpsW9t1HdLDMtet8bhK20rbpopHkJFNja4tahcPuC7XNzQgiMTUuUKzdb/OrrpJA8UXJ1uN/vrJjtXZx84LE6pG8rA7U7RLPe6m8PHAgq7kl6Ydnnn8TLmMwhO38FeMbpy+PXFcpKtCcCS8ocVcYD870jqFKpE6MWuy30TaWmJtcV7gT7i3QDJMF53xnd2ibH9Lj4keU94XGleadTHoqZVRPyLrVgpBtSf3nmlb/5408SoeLyTqSWGHOl/X8kAg+z77KHBuM1s8NnI4R0V9EDOIFwGRtAm7/DfvtVH1c+9z9h8JqfbXEe4WfovpyPVR6UVUdXq/M/ZTDzCJjeHFGSz0f+cdNos/n+4yS6/Pa4p41HaaxOG2i9T86N2iiZnr0Rr+az9f4hnTKMJDaT0Elqkd45RulFpl4e8Rna1UqxNiA/OMJT5fw2L6QYkyk/WHgijEdKji+5njw5m82/4giivDX3gwRBTY9W1Rk8WYtqkGGBtolBD3Ym8MnpwnQ18OnjpaTKSmR6uNZ8Q/QvKoCwNMXUMQT6D13Nmtafhnj2nyyX0XlbFdgN3kOGmvFqf2LjFGU+FnOk48V0EHcDRkRVzY5bOewOuv9BjHRFK8GRC7Ra0P0jaIpjyC+H2GzW57HXoHfE2FoFCMYnMQyZKFnMQRXCp5GO5Xyt86W57/FrUZ0snTN5Sg4yIPpcm8bbrYnW1ZSvgusVoPrBZjBy0ahJD4AoBsCkaHAvBsMRuvd775lg+3Rp6roOtIfWDVDnuwLtIFnFr9KCiXxnsQavWT5ZQRrNR7ybIocIMvOoLJxU4T3oaD+SHiPAK1TNTjQXY4pmz2kPGH3+gl659V5yk5ZqKCTptTOBzoeisEIKKp8wWiVZpa9tLx+n46ADhyJbH19/o8/VyRHIwLxIapxGbB0eKRoeCGJ8Tm5tNMrYOwsvhbCe+PlJ2i+jgHDZ747wCk8RCgdo2I/l9aGFQuJM7w+WI5dsQofY+7Gut64cdkpYu1S26eb1SAfZUecUQbefWkPPiVt7/lcqurS2MEB3CI10lRWNDstEu5JoWvWMxqPO7YAIppeqkG83t8BmjdR0CdUq5dQw+Bgj80m5PUrUMlWwOh3B/7BJ7G+rFjQi+qLS3rZY3p2mc4a43vZ07HKkbQvfWguijiDtksdk0osv6JH7nmsSIrjbsY7tx87ONgC7r2N9FD9whQZvG3bGUDBV9h0RGjB+hFpyoo6E2FCAGyvRhagysaM2Mzszh762gu8O1lIgxsWJNq9UttahyPDOmcbh/tSTqf8WGdWj72L4hsyg4/xM51vOZNUapJOCfgDFqOvMETJ2kxZBA/pQLFatGX/KuJOp2aW1NlLIJOHA6GRHUsEEbsuTLv3gruaiO+XegaWRoXJJTqKqslwsw+gCdFr7sr5kYR4VhGT7MA7WnGboM0MTwZyCRTyI4fcSWYWUlk8JxtaYnBSwfSHRpvea2EfvSCh/KDB11+RL2YHe2INWWTuIB8WpMyN2SIFjFKRSOIqmgAuw6EvbOKeZfrGhvsLKcT83QpIsrPHtWOjBeLHVCX6G0FLEU3W0ncrlY/hUrpwRaJTyMPqktGk7nILvq1TrjvFJlIh40I3t+3nL3xPgLZfeZvbJLvlgPUVlP7dqv9AeBVPwGH5q3vsXYRL4a/L2dW4aPLUQcruOp7K8E+ArQ8cIBnKphOKpJFK145JJPgAUmrZ9jgpeT9Pf7/2F7DRR5ptlNVaf8gIsHHU9h9PLCKSeJvzDxm+pS174EpW9GjDhhFQ7KoMRCTDGNS0VbkOly+2BTVTNxc8b4CT40JBTIy2zIeEXTQDc+loul66nM3+NcFh7Q09hkmsc6XTe21mTeIpddooApBXSgaQm4mRN51byj8lheOeStw8t+CjgdwqyeEksmAk84RjsAeWec1l/SXIopjLEdMrS/tbT6de5EvWX3yKlY0S1N7XdYGgmhwkTh7rcZ2kNZ3bqNRi/tgQLqeMGGvbmVcUp8VUT8E1vKXqn+ruyiD+70A13vv2v6QS8n1DlU+O+oJvrUbAtYFJPQMDM+WfC6Ux25ChYnSEO+ksHOgEZEdSOmypScFcg2c5YkJQ7Srd+3c/0FENPxZSEJkN0DZg/2yJQv2FF4XZyvUSB7jSRBwx57MmfyLkOz/9r+QSoHUpdC+Q3EzTN7V8mS9IP0/QttpaMa5cC+Ec09yMl96yZ1gkLyGkvKip+18Xk1iZUONm380hjMyeHPKtLwlpy6rBOAsB8KlQFl+r0Oc/kZfTc8o4bCOb8EdZHwdyNFgZ2iqtKc1UZrp2tKNCvLDcrgA8Ly5xMOGbalINbbGGeEIOfqjb2yPyM3nCLt9DTzNkUpumXiQfVWCJT508qTU/q89lAFPGxZ4X+QtkJQIUGYXQAAAAAMpM7j5ghbnBpPE7C31qWeXIMMrOzNlDPN0asEyjJ+6T6rIDqf7GT/nUF9pufxbLnYv+3hOMUWSkO5gT6E18pLr1W+EshfQ3Ja6SVwyg2YqA5rq2wCgK7/xgH34MOpVXdXFoAf3yRzIUYH7vv6bLwjZlruL0G4xpDJVUQgKRHMjpdJVgb33zIEWo1dCHDHyVFc+yIjjOf+RtfLx0E8lK3xUJmWObBfBR69etz4FR+1APBzVNiofc2Mjr93Djg1/gpstxAQsMOZTbfYt6tS1EJOA1I+TLPeGIRbgmN4pt5/vn0vKDGM8oiHkqnUpBZixS7wOSdF4mw0u7G5+VBe52UMng8q41b/wdtNoJjeTnGtuoJ99yNmKgRSU2oXfqJCq6bMGJlcwVJGJ3X36YMbwDz6IYZ+gMpWk8H3w0RE211R1pCBRdAADPjZJs+4TgD/pQGz9GQjhJM3JGtPxdRBUw03BK8qhqW5+WMGmO09v6fiZ2T0BVFBLnLxMAwIBpfNlSXaI0+dUXbQU72oby+DgglfkaMY4c9nlqd1b0cmCbT/4Kkm53IrAgOkS9ICkqhbbDnvX7lcQw68qG+D3raLHv+zRPdg+fgk7w6X2nfd3RC2YKll/xQjL6NITbR3B2qyRP3/9ct3h7U7klcimPnrHDSgsjCrp0ZGltgN+VRwNHZ4X6qaLHdDQn+MmIawaE6Ghvb7Lt/mOKHdkNdWLdUHkRA/pwHFCzcLASgY0O7UQERrHD885A+ZBy/beO6aQCITTJkFq29CqpxXpTvXLPFE9NrLW3NmQ7+Z7XFYbWXzTCequkewrGMHTNtY4l8IfLy/oy5oxuJBN2yzchWY1JjMrNvW0EmpY8BXccP9ocbXMDtYCzQxZmk+kV3IzPAHfAemCeOaPix2o9K2Q4g4jU0qrmE6HrkoDznVo5FTUC3q6RZQuUsgzCqnjnlSJDdEYB/2kMGcyVJP8gb5yubpsDC/vS7fkaZA9Zsdi1DHp8C80pk+6iR31zIAtFP+BOHniWmP7J4kA2b8hYjf+U0J/RZuQpojCgaSOwzdLJFZI+oL6pVXr1ELF3xE9JR0OjGQ6U9yKxkNqSam3WxZQK7/7CCDpDJti4ppBLhdL8TQKxmwt5RuXJ3vDgWot/iDqp5jXarOdr18egz5KM1d7/UMfLMU+3vFu2tJft6Yvm2Q7iVP0vXZEWt40DkAl1RsF2c4hvv7G1Cy2Ciy6kVAlo6LmSY8jlZxv5qCVXR0OMj582zzCTfQ7VOrmI8ct1YNQuKfhtOzY+kS7lUrzv6f/ga5qFEAtwZUpkwjs5gwhqLRkOQjd2o/ArYAMYextu9S8xu1FtMxc3Yewpx3QaZnZ1XXZ0LIZpTqznLdIolEvNP6F0ZoudtApisfdpKc28UULsU+55GhnaiaqSd+s8EWtQiJTEtsN2lwwxqgtAng9EfR1Ch4JDV2RWLntmpIK2x2vw18JBhyVUmabRcdU0cvhoydD29ESPL44xAZ5J9k1dCjlKlvZU8D9y+PHha7MWK4WJmvVOvuueHE6TCVG3OZkALzr5GDzcEGDLzZ2wvrCV/wwpM37YxbGQ0QPW030w2Ho6thZR6gr8iE1LZX2AR58TN0MZaPaeskG4dIBBa2t2izdpJ6Ko57ucMxG5pToYeiP7ITAKsHdW/CD6IsrgNaQvt0e6h6xfcvAAAm5ZNr5FaIhlXKururFXq5PW3pjW+cj08Lh8pfrGi2QScrtv3UOjftFwpm5IyvKbRI4gzoZHlZmBAUYF4kVm+68ANpBRKkTmN5rqSL8Gj6OLvRsARCJEuLiDiqEJLcFhyUtvd1qyNj6SQRUDKchctwf/Cv2FcNgX3rsTpOFf54Wa5vf6XM8m4xYCJzZHWIP3/l/vLOihHKHLO6WrrIMwzjYp+e+jnXWyX7ZpBHQlfHdvMtIWYfTBuVPasIkPnLdIXAFV7E4FoXAlapfWvTId9qI1lRiK/m59mCbRaurBrvDK5NO4xoAgbEuGl1/Hkm0/8C6xQ1EKu0DnxVOpUOS+t3ysOfvK934u7aI9qGZtBjCAAAAKkfJexUBXg3W7oy8H7V0ANnrHgcOr9NxnQWrx2mANbMcjis/2+lQmgoomHubLSagBFdBxGgujnPdo/unFu8dB2TN3qk3Z1A66ca8V3B3grKEOyXPduLiL/ZQpmcRQeuwZg0wIC1z1vkFVF3mIqH/fNbvC1qexSPFiniNl7Hi23OoCRkYLXse9IqUWxU2j3SINZ7p3tQHQ23bKIvU6P9w3lIAACPOytmxVMji4NAo1ZmGB2T41X7H1TPJvQVaTBdaYJIm8anoN/P0NpHg5oAsS4H95y7ab+JXwDjX3afJU9+diH1q3rkv1PmmFx+VX+nbMGeQDyLKW/F7HIyNAPFzAnLQ2T9IZj1F1G9pQhrlVz+B297lWhD8Q4B5rMwov4h4qazqWsbeE4g7UIWTvHXWPJ6deljH3Ofw48OXueSlnqHSmUZjt4XpxaKL0QNBBxND8Kg8aalsRrG/hVmw2HP1V9vRoY20Y1RJUOpu+nsDiyUU671kv7m4blTKlnCblpygM+U/KrgGEfgCxrl3Gi44qUicZLz0yuMW5doNdBn2UC2S8M1meAE9WolFw+VU47OOKc9L3YRNRgklG//uQNJmKNfulmvkKIr/DfzKQMq7ma6vbuBz76mUOAnwjh8V+dpAdq8iaN0fYZDgIcy3OurHIJQ5E6nTjSw42tc+KlXSAgjGPmB3fSgrFAh9cdnJyctL1TaUV7JmJEo5n7+CbVli5dRI2JcqkgoF5jacLWt34iDOnYWibsup3dH6wK0b4sjhQAABt6rfz3CYLmwvNdAetJJ8y2mDLOFfjj1u1qhFOcvwohZbu0X8F+igFvME4njumpS01CI3xebzxpr3kVgdcf2+F08Yo03TPUOsU8nblk7wE7bdBXJ19opa9zv3ENGe0Q94zthVuq1HA0DHyvbA2CmCEsgizR9m4AAAjzvQQ8Xf4ZBOOmZdOC4X+xyecGPVa/16RUohPX/qnx7zWoO2lgVcPjioo21rbfvUaGiqBI2R6L6l9wO+taOQ2COMZ6ouBYh0N6ttnjLPgzONKxlsb1wj/pkZ8bJ0JGNpO78vjJo2yk3ocw8u4Dr16EeRapqu4RJUk8ASYi2GBwzjJUsWTgGRivRBsOjxqDGkCkhGvC95w7JnjsyrK69yAERlk3zu0CpBy23Cllv0y9Lem8FBvoMff/DkihYxEu8D6tC6RhMHrTiN+bMLpVWnQ2oBmshDcKNa45NNxt7VfU/2M+TKzLtpqyRfN8r1zTKAQBnzat6hZlP3kUHCIkyVWG4HXl0XuvgfpeIkmkwOPHESKKNWEuEmddInPhjJdFI/Xi+7vwwPCFbGi71iv1YjfEuSfJv6dRWDC1F1UfwiNZbBkWQawXSTALfsBhoNvIeSx0LrpBOgMqlkBQ9JThkGttVlWHkfRPrBaflqTG9PjfO9q4KQknStl4kHHXpL7YAAI87FN/RBHKb7uV/f5szHfmB1e81kpRuyj1ofkYxaZ56fhec8+zcuFBDVX2KYXe/GQvKVZnC94Vw5E07zTUWXQV1JSnz7nZCpJan+Vjp5of5r0ZWCdsqAQ1DgyatS4urH0K3ipBZM5nx6blBquVx9eTGcjB09wL8yuaXDuU+R+trJTzZRYLeMwN6mZHaMEcUzUyzZDxH7N3Rj+KFqAGyuJiGl2vpF76Jqa7QWonIyBarmgs9GJFe/6dlklbCcsFnz63YQBqPxqdkUZCqB2b9KZE9GyRvfIQ9rB4mXjPvcBU6obaISLkcPUI/uNPIY9NxFkFLWNLZzZ0nhnZYU8hOf/RaPj+m4ZN8+PZ5ZIpfQK9RAv+Eybj0YfZkV+HZNgZGOCBEdUfKTGJdXxGNvidi7dWE9WbmG/r3hMSmitSZUfArIOf+Pbxi1vzRhXaxybGTSWeLej3Aq1C4zsah3S1doAFYJvZKz9Pdu01bSVFA9apyu6oJ5RD/Q9ITdCAUCHu27P/UinBwUf8imYELdCZactkoXZv/ZXzX7ZUUOK7gxosgcELqigRqI+/Jmd4YxBMahWf6+46ZaknNfLqK3iA3w3TQo/6ze9+cqX+xlPnDrlcXhnJ3EG2hNmSmVIAeD6R4jLk8dNmtjDZtkmvuYIOS/JgAZzMoInMw+dGwOOgPNtcylmL62YsfKafQ02O9rrKCMheeo2zkdVmdeZoPGNMD0fRlm+UGJtrANPDRLhPh8d8cLgfHBfLP4M+8bzBLLzvXfUN7uA0IU2qJEujYggw9YDDYFmkH+lX6nAb7XIk4U/POj1iRjKJz3qUYH8DMu9A+q/QZKUzk2sZslbyMc/drGcBnv4uT10fJrmVSpj9GMg2zJjvVEErgayp143TpmJiYJK5Om7LTAD2VGoV4H6a7ZhL+wM+qNayFxnE6ftH41sOHDhlNj1wumTgwnSo+Dtcezxxuz+YQa2tUwGadFh7X1Qf/dLs+ICTcucAGLhKwQ8W50BlTbW/gYu2a/rtRjw7xqMUJz99od+S4RsU980dNC8Zsmw/QGPuq5kCvO5vsCUa9EfSb4vizzGoHIcWpA4rH5xbT7eYL1Vk+i3Jfc1xf8JJChXPQBEez6qLbFSquTjGWHP3qTkSSZVWagGxyaRgk/BKBgs9Exl42QMRIKoI9N9Mk/iHW9eL/AdPEHu/VkPvnE0AxaIrps18xAmw46+kZ7P07pZi3wbcSupGYITtXDYkIrCUP7weO+wnbFVVxE9ydtTAhrqOFJRxjeEOCd2SzxIfFsis+97lu1Hjw6bWHuHc8TzWQAYRspqafSxkX0sRJTn+rG0bguZDlAyIvpWoNMHAS/T+/RsIyGIERvmelgJSo3Fb4Hd/pE9uAGf8eVdXs9uVM7jP0AZ3ZtbgMJ+20rJ6QnM93Uo7WirdcjnGy/ZZc8X2313HuB5eTa8EaFgqJcvN1RYjSmA7IdTcB/0eNm4WABRWq2wWWbQQeCipqwKG3krMsuu/KH97EuFwU+k+lRcGa18KoIQRE+ddZvb8Ri7QFHfCm9Gj81sIaFJVdQ4fNewS5pq/31n0ycvPoYPAmqe0oSePhnX0p9bUgY+8QwjlLy18MAM/vDzau/7q/K6RSaMMm2QwroQ2u07LUTdmgPFY1tVzk/4QXu3KKSRGYIuI0NX3sTLqG7Fi+J+ANJ6LMmt6AEjmglzvdkIDjC+e9vdxZm/ENE0YSvSl3dsvedHUEZym5d3EGrUpaNoCjlNQcWB+HSgoRUevinRsGbQZExulJ6rgWfkqP5Ip+1B4ce8gjEyNVR//jGxeBL0MdNBiwPmF6Z9bOACenD1LGI3TsGR+u4WvN4o/wTO2VHt//lEAY/XyXY21mwHvfPKr7Z9wTeohSpwfb711AWqJ+MPlqBjpCOMF5faof5phgZzRM0/4klov9Y4FhEsF20vWvkw3a1olZFGkvw3Qzrs72iqsF0Vxpg+QmTDThoaw+saZuJMBl9wzo+9vvGNSUvOK3ShpTKCYh63zA8YQcJNH20B8yhCYZZriPqurBMTmHxF05xZVDkJyQexZlqJkQJimWH5X15xwmtNPU0sBIN9+WaRaFs/KcPGYYeNKn8DXMuSEyN8018kWaZcJOKoPv1LD1oqSoFQscJNIO3mYWxEO8euuL+4suu+5tnL31UjM2CVskf/8/HERz95YjF7Mazana9a9bSnNjmcrr9KVvIhUIn87m7KA7r35ELn30g+6WaEpUmyYuX4rLi/VDGVJdo3MuurVRKIb3K2s2IIYGKxDgWg9MZHjuLKGmbDz7jjS0cfaQq5HbKovqEcWFHf82W8oHhwAFJw/2p58WTKjo9wbreu6soLczHOX8dWbmaKmkJoVjtu1jUuKLamUnmW6krNgWoy+N1A5exFew+EkFeewDf/jtCYm9xdliuRfF5/xsPvgyXeouFZJPW3w+jYUw0hyJUNUVHSvRvtWSRQ3i1ystJTZRF2An7UR7QC9CG28OUyEsujFhdELGEDl7AsO1xX2tAaCOwMztRijEUP2Ae7spMXMakXbSp3HXG7AeC0lU5680UvElKy7MOX3n/G/KLut9iulsTrSkOFnw15qc8vY3+ZiiwqbJkcI+K0TVZWQpffZpvyw0V+zKsl1imHbXr5GvL0wezV/3bz6qQYMhXXeFTgoZdf7NwasHQaMUT3cRzRmg1Yf++Gz+JTlP5qkDwa69HFBtSo4iiWaj6EjbdiV3Yvbg4PJgtQTUgug8dbk1VNEnvChlriTHPWGb7MluP7j2Wl5n6n9NUSa2aqr/mvsMkGdcOkDjczBJy9Ca27yIy+oksVDDyCnqXDOBOClRoj9eGxoicbVR4G4eXIlXQPDrSTssE9LcODdAQAA2UNhwL1eHrNMy4YfLZId+xMh5LxZrw6THNYbcCL8psQDJn0uQXHeHj0T7B6YAQ1OW5HiXCuwZr3QADKYDzCJyNYN1vZNEwN3WPgDAQws05cruB8joIG3uVrtWTnrocujSvw1BB2VdATPxB1fqIULFNAieRQZMmX6cFyy8gkQ/cgnNiGryhMmVQ1OBcK/E80Dr9mNXsZAZBj1FfjmFkr6aNcEtkzuqsk+g5Esu4CyPJPOvf/hSXaOfVKJ4kgDmkgPy6eqduAv4KrPsycPi2TQRNf9TtwF/BVZ9oxSdtNUUAAA="}}; // 遊び方の画面写真（Lean モードのスイッチの位置）
function leanHelpShots() { // スイッチの場所を示す、画面の写真
  const sh = LEAN_SHOTS[LANG === "en" ? "en" : "ja"];
  return __T(3168, [sh.full]) +
    __T(3169, [sh.zoom]);
}
function leanHelpHTML() {
  return __T(3170, [leanHelpShots(), leanHelpSample(), RD(__T(824)), RD(__T(785)), RD(__T(792)), RD(__T(796)), WN("7-1"), WN("10-5"), WN("12-1"), WN("15-1"), WN("15-1")]) + `<p class="note">${L1(__T(3171), "If you want to write Lean tactics yourself, try the ")}<a href="https://adam.math.hhu.de/#/g/leanprover-community/nng4" target="_blank" rel="noopener">Natural Number Game</a>${L1(__T(3172), ".")}</p>`;
}
function openHelp(page = HELP_PAGE) {
  helpStop();
  if (!PROG.helpSeen) { PROG.helpSeen = true; saveProgress(); renderTools(); if (SCREEN === "play") updateUndo(); else { const hb = document.querySelector(".hero-actions .pulse-new"); if (hb) { hb.classList.remove("pulse-new"); const nb = hb.querySelector(".new-badge"); if (nb) nb.remove(); } } }
  HELP_PAGE = Math.max(0, Math.min(page, HELP_PAGES.length - 1));
  const pg = HELP_PAGES[HELP_PAGE];
  showModal(__T(3173, [HELP_PAGES.map((x, i) => `<button type="button" role="tab" class="help-tab" data-helppage="${i}" aria-selected="${i === HELP_PAGE}">${x.t}</button>`).join(""), pg.html(), HELP_PAGE > 0 ? `<button class="btn" type="button" data-helppage="${HELP_PAGE - 1}">← ${HELP_PAGES[HELP_PAGE - 1].t}</button>` : "", HELP_PAGE < HELP_PAGES.length - 1 ? `<button class="btn" type="button" data-helppage="${HELP_PAGE + 1}">${HELP_PAGES[HELP_PAGE + 1].t} →</button>` : ""]), true);
  if ($("#rpdTree")) rpdStart();
  if (pg.anim && $("#helpAnim")) playScene($("#helpAnim"), pg.anim(), st => { const c = $("#helpAnimCap"); if (c) c.innerHTML = __T(3174, [st.h]); });
  if (HELP_PAGE === 0) {
    hmGo(0);
    const reduce = !!(window.matchMedia && window.matchMedia("(prefers-reduced-motion: reduce)").matches);
    if (!reduce) HELP_TIMER = setInterval(() => { if (!$("#hmMock")) { helpStop(); return; } hmGo((HM_I + 1) % HM_ITEMS.length); }, 2600);
  }
}

function command(c) {
  switch (c) {
    case "map": SCREEN = "select"; S = null; NEG_SUGAR = true; closeModal(); renderTools(); renderSelect(); window.scrollTo(0, 0); break;
    case "undo": if (PROB) (UI.mode === "refute" ? undoR() : undo()); break;
    case "refuteDone": if (!document.body.classList.contains("ev-calc")) refuteDone(); break;
    case "credits": showModal(creditsHTML(), true); break;
    case "hub": backToHub(); break;
    case "reset":
      if (PROB && UI.mode === "refute" && STAGE.fol) { HISTR.push(JSON.stringify(R)); R = initStruct(); renderStruct(); break; }
      if (PROB && UI.mode === "refute") {
        if (R.floors.length > 1 || R.floors[0].own.length) { HISTR.push(JSON.stringify(R)); R = initR(); renderRefute(); toast(__T(3175)); }
        break;
      }
      if (S && (S.ops > 0 || S.log.length)) {
        HIST.push(JSON.stringify(S)); S = initState(PROB); UI.sel = null; UI.can = new Set(); UI.fx = true;
        renderDynamic(); wipSave(); toast(__T(3176));
      }
      break;
    case "help": openHelp(); break;
    case "maze": {
      PREFS.mazeMode = !PREFS.mazeMode; savePrefs();
      applyTheme();
      renderTools(); if (SCREEN === "play") updateUndo(); else renderSelect();
      toast(PREFS.mazeMode ? __T(3177) : __T(3178));
      break;
    }
    case "lang": { // 日本語 ⇔ English（文章は読み込み時に決まるので、切り替えたら読み込み直す）
      PREFS.lang = LANG === "zh-CN" ? "ja" : LANG === "ja" ? "en" : "zh-CN"; savePrefs(); location.reload(); break;
    }
    case "theme": { // 自動 → ライト → ダーク
      const order = ["auto", "light", "dark"], cur = order.includes(PREFS.theme) ? PREFS.theme : "auto";
      PREFS.theme = order[(order.indexOf(cur) + 1) % 3]; savePrefs(); applyTheme();
      renderTools(); if (SCREEN === "play") updateUndo();
      requestAnimationFrame(() => { if (typeof drawKeyLinks === "function") drawKeyLinks(); });
      toast(__T(3179, [THEME_LABEL[PREFS.theme], PREFS.theme === "auto" ? __T(3180) : ""]));
      break;
    }
    case "story": { // ストーリーモード（お試し）
      PREFS.story = !PREFS.story; savePrefs(); renderSelect();
      toast(PREFS.story ? __T(3181) : __T(3182));
      break;
    }
    case "mazeBars": case "mazeDeco": { // お試しの装飾
      PREFS[c] = !PREFS[c]; savePrefs(); applyTheme(); renderSelect(); break;
    }
    case "tutorial": {
      const list = SCREEN === "play" && STAGE ? (STAGE.tut || []) : [];
      openTutorial(list.find(k => !(PROG.seenTut || {})[k]) || list[0] || (SCREEN === "play" && STAGE ? latestTut(STAGE) : "basics"));
      break;
    }
    case "lantern": {
      if (!S || !S.open.length || !UI.lanternLeft) break;
      let ok = 0, dead = 0;
      const judgeFn = STAGE.classical && !STAGE.noRAA ? provableC : provable; // 背理法が使えるなら古典論理（真理値表）で判定
      for (const id of S.open) { const g = S.goals[id], v = judgeFn(g.ctx.map(c => c.f), g.target); UI.lit.set(goalSig(g), v); v ? ok++ : dead++; }
      UI.lanternLeft--;
      renderDynamic();
      toast(dead ? __T(3183, [dead])
                 : __T(3184, [ok]), dead ? "bad" : undefined);
      break;
    }
    case "togglemap": {
      PREFS.mapView = !PREFS.mapView; savePrefs(); UI.lastActive = null;
      document.body.classList.toggle("mapmode", SCREEN === "play" && !!PREFS.mapView);
      if (S) renderDynamic();
      toast(PREFS.mapView ? __T(3185) : __T(3186));
      break;
    }
    case "togglenames": {
      PREFS.manualNames = !PREFS.manualNames; savePrefs(); UI.pick = null;
      if (S) renderDynamic();
      toast(PREFS.manualNames ? __T(3187) : __T(3188));
      break;
    }
    case "togglelean": {
      PREFS.leanMode = !PREFS.leanMode; savePrefs();
      const b = $("#leanToggle"); if (b) b.setAttribute("aria-pressed", String(PREFS.leanMode));
      const lb = $("#leanBox"); if (lb) lb.hidden = !PREFS.leanMode;
      toast(PREFS.leanMode ? __T(3189) : __T(3190));
      if (S) renderDynamic();
      break;
    }
    case "toggleterm": {
      PREFS.showTerm = !PREFS.showTerm; savePrefs();
      const b = $("#termToggle"); if (b) b.setAttribute("aria-pressed", String(PREFS.showTerm));
      if (S) renderDynamic();
      break;
    }
    case "hint": UI.hints = Math.min(UI.hints + 1, STAGE.hints.length); renderHints(); break;
    case "close": closeModal(); break;
    case "library": showModal(libraryHTML(), true); break;
    case "cards": showModal(cardsHTML(), true); break;
    case "inscr": showModal(inscrListHTML(), true); break;
    case "record": openRecord(); break;
    case "dbgclear": debugClear(); break;
    case "ending": endingShow(); break;
    case "thirdway": thirdWayDone(); break;
    case "unlockall":
      PREFS.unlockAll = !PREFS.unlockAll; savePrefs(); renderSelect();
      toast(PREFS.unlockAll ? __T(3191) : __T(3192));
      break;
    case "resetAsk": // 進行度のリセット（確認してから）
      showModal(__T(3193), true);
      break;
    case "resetDo": {
      const withPrefs = !!($("#resetPrefs") && $("#resetPrefs").checked);
      PROG = { best: {} }; saveProgress(); SEEN_CLEARED = null;
      if (withPrefs) { const lang = PREFS.lang; PREFS = { ...PREF_DEFAULTS, ...(lang ? { lang } : {}) }; savePrefs(); location.reload(); break; }
      closeModal(); renderSelect(); renderTools(); window.scrollTo(0, 0);
      toast(__T(3194));
      break;
    }
    case "retry": startStage(STAGE.id); break;
    case "next": { const nx = nextStageOf(STAGE); if (nx && !stageOpen(nx)) { closeModal(); renderSelect(); toast(stageLockMsg(nx)); break; } if (nx) startStage(nx.id); else command("map"); break; }
    case "nextdoor": if (S && S.open.length > 1) { const i = S.open.indexOf(S.active); S.active = S.open[(i + 1) % S.open.length]; UI.sel = null; UI.can = new Set(); UI.fx = true; renderDynamic(); } break;
  }
}

/* --- 入力（クリック・タップ） --- */
let suppressUntil = 0;
document.addEventListener("click", e => {
  if (Date.now() < suppressUntil) { e.preventDefault(); return; }
  const t = e.target;
  const jvb = t.closest("[data-jview]"); if (jvb) { judgeView(jvb.dataset.jview); return; } // 鑑定の扉の証明・反例を見返す
  const sb = t.closest("[data-sym]"); if (sb) { const inp = document.getElementById(sb.dataset.for); if (inp) { const a = inp.selectionStart ?? inp.value.length, b = inp.selectionEnd ?? a, c = sb.dataset.sym; // 記号ボタン
    inp.value = inp.value.slice(0, a) + c + inp.value.slice(b); inp.focus(); inp.setSelectionRange(a + c.length, a + c.length); inputRead(inp); } return; }
  const pvb = t.closest("[data-proofview]"); if (pvb) { proofView(pvb.dataset.proofview, !!t.closest(".overlay")); return; } // クリアした証明を見返す（冒険の記録からなら、記録に戻れる）
  if (t.closest("[data-ptfit]")) { PREFS.ptFit = !PREFS.ptFit; savePrefs(); ptFitApply(); return; }
  if (t.closest("[data-foldspent]")) { PREFS.foldSpent = !PREFS.foldSpent; savePrefs(); renderDynamic(); return; }
  const spo = t.closest("[data-spentopen]"); if (spo) { const box = spo.closest(".keys"), open = !box.classList.contains("spent-open"); box.classList.toggle("spent-open", open); spo.setAttribute("aria-expanded", String(open)); spo.textContent = spo.textContent.replace(/[▸▾]$/, open ? "▾" : "▸"); return; }
  const kvd = t.closest("#kvDone .kv-chip"); if (kvd) { kvHi(UI.kvf === kvd.dataset.kf ? null : kvd.dataset.kf); return; } // クリア画面の「すべての階の明暗」
  const cmd = t.closest("[data-cmd]"); if (cmd) { command(cmd.dataset.cmd); return; }
  const gd = t.closest("[data-guide]"); if (gd) { const a = gd.dataset.guide; if (a === "start") guideStart(); else if (a === "clear") guideStart(["clear"]); else if (a === "next" && GUIDE) { GUIDE.i++; guideShow(); } else guideEnd(true); return; }
  const tu = t.closest("[data-tut]"); if (tu) { helpStop(); openTutorial(tu.dataset.tut); return; }
  const hp = t.closest("[data-helppage]"); if (hp) { openHelp(+hp.dataset.helppage); return; }
  const hg = t.closest("[data-hmgo]"); if (hg) { helpStop(); hmGo(+hg.dataset.hmgo); return; }
  const rpb = t.closest("[data-rp]"); if (rpb) { rpCmd(rpb.dataset.rp); return; }
  const rpg = t.closest("[data-rp-go]"); if (rpg && RP) { rpStop(); RP.k = +rpg.dataset.rpGo; rpRender(); return; }
  const ts = t.closest("[data-tutstep]"); if (ts && TUT) { openTutorial(TUT.id, TUT.si + (ts.dataset.tutstep === "next" ? 1 : -1)); return; }
  const bsec = t.closest("[data-bk-sec]"); if (bsec && BOOK_UI) { e.preventDefault(); bookGo(bookPages(BOOK_UI.key).findIndex(p => p.sec === bsec.dataset.bkSec)); return; }
  const bpg = t.closest("[data-bk-pg]"); if (bpg && BOOK_UI) { bookGo(+bpg.dataset.bkPg); return; }
  const arc = t.closest("[data-archive]"); if (arc) { const aw = archWorld(arc.dataset.archive); if (aw && !worldOpen(aw)) { toast(lockMsg(aw)); return; } openArchive(arc.dataset.archive); return; }
  const ctp = t.closest("[data-cardtip]"); if (ctp) { const cs = STAGES.find(x => x.id === ctp.dataset.cardtip); if (cs) toast(__T(3195, [cardTip(cs), F(CARDS[cs.earns].f)])); return; }
  if (t.closest("[data-rvskip], [data-rvgo]")) { revealEnd(); return; }
  if (t.closest("#endShow") && ES && ES.scene === "fin" && !t.closest("button")) { if (!esFF()) esPopup(); return; } // （終）がまだなら先に（終）を出す
  if (t.closest("#endShow .es-pop") && !t.closest("button")) return;
  if (t.closest("#endShow") && !t.closest("button, textarea, a, .es-fcard, .es-wcard")) { esFF(); return; } // 画面を押すと次の文を表示するだけ。次の場面へは「次へ」で進む
  if (t.closest("[data-esopen]")) { esOpen(); return; }
  const wpb = t.closest("[data-wip]"); if (wpb) { if (wpb.dataset.wip === "resume") wipResume(); else { wipDrop(STAGE.pid); const b = $("#wipBar"); if (b) b.remove(); } return; }
  const smb = t.closest("[data-storymore]"); if (smb) { const box = smb.closest(".story-box"), open = !box.classList.contains("open"); box.classList.toggle("open", open); smb.setAttribute("aria-expanded", String(open)); smb.textContent = open ? L1(__T(1804), "Close") : L1(__T(1957), "Read more"); return; }
  if (t.closest("[data-esnext]")) { esNext(); return; }
  const esl = t.closest("[data-esleave]"); if (esl) { esPick(esl.dataset.esleave); return; }
  const esc = t.closest("[data-esconfirm]"); if (esc) { esPlace(esc.dataset.esconfirm); return; }
  const esw = t.closest("[data-eswhite]"); if (esw) { esWhiteDone(esw.dataset.eswhite === "save"); return; }
  if (t.closest("[data-esskip], [data-esend]")) { esFinish(); return; }
  if (t.closest("[data-esreplay]")) { endingShow({ replay: true }); return; }
  if (t.closest("[data-rvreplay]")) { revealShow(); return; }
  if (SCREEN === "play" && STAGE && STAGE.kind === "tower" && towerClick(t)) return;
  const rtab = t.closest("[data-rectab]"); if (rtab) { REC_UI.tab = rtab.dataset.rectab; recRefresh(); if (SCREEN === "select" && (REC_UI.tab === "qa" || REC_UI.tab === "memo")) { const rb = $(".rec-btn .new-badge"); if (rb && !qaNew() && !memoNew()) rb.remove(); } return; }
  const rw = t.closest("[data-recw]"); if (rw) { REC_UI.tab = "story"; REC_UI.wid = rw.dataset.recw; recRefresh(); return; }
  const epg = t.closest("[data-endpg]"); if (epg) { showModal(endingHTML(+epg.dataset.endpg), SCREEN !== "play"); return; }
  const fin = t.closest(".w-final");
  if (fin && SCREEN === "select" && finalOpen() && (!fin.classList.contains("sf-on") || !t.closest("[data-stage], [data-archive], button, a"))) { sfActivate(fin); return; } // 変身前は、扉を押しても、まず変身する（最終層に入れるときだけ）
  const bk = t.closest("[data-book]"); if (bk) { const bw = bookWorld(bk.dataset.book); if (bw && !worldOpen(bw)) { toast(lockMsg(bw)); return; } openBook(bk.dataset.book); return; }
  const rc = t.closest("[data-rule]"); // 証明図や操作の記録の規則名：その規則を解説する本のページを開く
  if (rc && !t.closest(".sc") && !t.closest(".overlay") && RULE_BOOK[rc.dataset.rule]) { const [bkk, sec] = RULE_BOOK[rc.dataset.rule], bw = bookWorld(bkk); if (bw && worldOpen(bw)) { openBook(bkk, sec); return; } }
  const shot = t.closest(".help-shot img"); if (shot) { shot.closest(".help-shots").classList.toggle("big"); return; } // 遊び方の写真：押すと大きく表示
  const stg = t.closest("[data-stage]"); if (stg) { const st0 = STAGES.find(x => x.id === stg.dataset.stage); if (st0 && !stageOpen(st0)) { toast(stageLockMsg(st0)); return; } startStage(stg.dataset.stage); return; }
  if (SCREEN === "play" && STAGE && !t.closest(".overlay")) {
    const pm = t.closest("[data-part]"); if (pm) { openPart(pm.dataset.part, pm.dataset.partmode); return; }
    const md = t.closest("[data-mode]"); if (md) { setMode(md.dataset.mode); return; }
    if (PROB && UI.mode === "refute") { // クリプキモデルの編集
      if (GUIDE && t.closest("#kmodel, #kHead")) guideEnd(true); // 反例を作り始めたら案内を閉じる
      const tvb = t.closest("[data-tv]"); if (tvb) { tvCycle(tvb.dataset.tv); return; }
      if (t.closest("[data-unk-false]")) { unknownToFalse(); return; }
      if (t.closest("[data-unk-reset]")) { resetUnknown(); return; }
      if (t.closest("[data-ksym]")) { PREFS.kSym = !PREFS.kSym; savePrefs(); renderRefute(); return; }
      const evb = t.closest("[data-evview]"); if (evb) { if (!CL() && STAGE && !STAGE.fol) PREFS.kView = evb.dataset.evview; else PREFS.evMode = evb.dataset.evview === "all" ? "graph" : evb.dataset.evview; savePrefs(); if (UI) UI.kvf = null; STAGE.fol ? renderStruct() : renderRefute(); return; }
      const tgt = t.closest("[data-tg-tog]"); if (tgt) { UI.tgOpen = UI.tgOpen || new Map(); const pth = tgt.dataset.tgTog; UI.tgOpen.set(pth, !tgt.closest("li").querySelector(":scope > ul")); STAGE.fol ? renderStruct() : renderRefute(); return; }
      const kgt = t.closest("[data-kg-tog]"); if (kgt) { kHi(kgt); UI.kgOpen = UI.kgOpen || new Map(); UI.kgOpen.set(kgt.dataset.kgTog, !kgt.closest("li").querySelector(":scope > ul")); renderRefute(); return; }
      const ktg = t.closest("[data-kt-tog]"); if (ktg) { kHi(ktg.closest("[data-kw]")); UI.ktOpen = UI.ktOpen || new Map(); UI.ktOpen.set(ktg.dataset.ktTog, ktg.getAttribute("aria-expanded") !== "true"); renderRefute(); return; }
      const ttg = t.closest("[data-tt-tog]"); if (ttg) { UI.ttOpen = UI.ttOpen || new Map(); UI.ttOpen.set(ttg.dataset.ttTog, ttg.getAttribute("aria-expanded") !== "true"); STAGE.fol ? renderStruct() : renderRefute(); return; }
      if (STAGE.fol) { // 構造の編集
        const rl = t.closest("[data-rel]"); if (rl) { const i = rl.dataset.rel.indexOf(":"); const P = rl.dataset.rel.slice(0, i), tup = rl.dataset.rel.slice(i + 1); const snap = JSON.stringify(R); sToggle(R, P, tup); HISTR.push(snap); renderStruct(); return; }
        if (t.closest("[data-preset-open]")) { UI.presetOpen = !UI.presetOpen; renderStruct(); return; }
        const pz = t.closest("[data-preset]"); if (pz) { loadPreset(pz.dataset.preset); return; }
        const cn = t.closest("[data-con]"); if (cn) { const [c, d] = cn.dataset.con.split(":"); if (R.con[c] === d) return; const snap = JSON.stringify(R); R.con[c] = d; HISTR.push(snap); renderStruct(); return; }
        const fc = t.closest("[data-fun]"); if (fc) { const i = fc.dataset.fun.indexOf(":"), f = fc.dataset.fun.slice(0, i), key = fc.dataset.fun.slice(i + 1); const snap = JSON.stringify(R);
          R.fun[f] = R.fun[f] || {}; const cur = R.fun[f][key]; R.fun[f][key] = cur == null || +cur >= R.n ? "1" : String(+cur + 1); // ? → 1 → … → n → 1 …（未定には戻らない）
          HISTR.push(snap); renderStruct(); return; }
        const dm = t.closest("[data-dom]"); if (dm) { const snap = JSON.stringify(R); if (sDom(R, dm.dataset.dom === "+" ? 1 : -1) !== false) { HISTR.push(snap); renderStruct(); } return; }
        return;
      }
      const lp = t.closest("[data-lamp]"); if (lp) { const [id, a] = lp.dataset.lamp.split(":"); actR(R => kToggle(R, +id, a)); return; }
      const af = t.closest("[data-addfloor]"); if (af) { actR(R => kAdd(R, +af.dataset.addfloor)); return; }
      const df = t.closest("[data-delfloor]"); if (df) { actR(R => kDel(R, +df.dataset.delfloor)); return; }
      const kvc = t.closest("#kEval .kv-chip, #kvDone .kv-chip"); if (kvc) { kvHi(UI.kvf === kvc.dataset.kf ? null : kvc.dataset.kf); return; }
      const khn = t.closest("#kEval [data-kw]"); if (khn && !t.closest("[data-kg-tog], [data-kt-tog], [data-floorsel]")) { kHi(khn); return; }
      const fs = t.closest("[data-floorsel]") || t.closest("#kmodel [data-floor]");
      if (fs) { R.sel = +(fs.dataset.floorsel != null ? fs.dataset.floorsel : fs.dataset.floor); R.selPick = true; renderRefute(); return; }
      return;
    }
  }
  if (SCREEN !== "play" || !S || t.closest(".overlay")) return;
  const pick = t.closest("[data-scope-pick]");
  if (pick) {
    const n = +pick.dataset.scopePick; UI.autoScope = false; UI.scope = UI.scope === n ? null : n; UI.hoverScope = null; applyScope();
    // 狭い画面では証明図が下にあるので、部屋を選んだら証明図が見える位置までスクロールする
    const tree = $("#liveTree");
    if (UI.scope != null && tree && pick.closest("#rooms") && window.innerWidth < 960) {
      const r = tree.getBoundingClientRect();
      if (r.top > window.innerHeight || r.bottom < 0) tree.scrollIntoView({ behavior: matchMedia("(prefers-reduced-motion: reduce)").matches ? "auto" : "smooth", block: "center" });
    }
    return;
  }
  if (t.closest("[data-exfalso]")) { doAct(S => opExfalso(S, S.active)); return; }
  if (t.closest("[data-raa]")) { doAct(S => opRAA(S, S.active)); return; }
  const orp = t.closest("[data-orpick]");
  if (orp) { const side = orp.dataset.orpick; UI.orChoice = null; if (side === "x") renderDynamic(); else doAct(S => opOrIntro(S, S.active, side)); return; }
  if (UI.lemma) {
    const lp = t.closest("[data-lempick]");
    if (lp) { const L = parse(STAGE.lemmas[+lp.dataset.lempick]); doAct(S => opCut(S, S.active, L)); return; }
    if (t.closest("[data-lemx]")) { UI.lemma = null; renderDynamic(); return; }
    if (t.closest("[data-lemgo]")) { submitLemma(); return; }
  }
  if (t.closest("[data-indoff]")) { toast(__T(3196)); return; }
  if (t.closest("[data-ind]")) { if (!STAGE.ind) return; doAct(S => opInd(S, S.active)); return; }
  if (t.closest("[data-lemma]")) { UI.lemma = UI.lemma ? null : { gid: S.active }; UI.pick = null; UI.orChoice = null; UI.sel = null; UI.can = new Set(); renderDynamic(); const inp = $("#lemmaInput"); if (inp && window.matchMedia && !matchMedia("(pointer: coarse)").matches) inp.focus(); return; }
  if (t.closest("[data-deadundo]") && UI.deadAlert && S) { // 行き止まりに入る前まで戻す
    const k = UI.deadAlert.k; S = JSON.parse(HIST[k]); HIST.length = k; UI.sel = null; UI.can = new Set(); UI.fx = true; UI.orChoice = null; UI.pick = null;
    UI.deadAlert = null; UI.deadSeen = new Set(); UI.deadMoves = 0; renderDynamic(); wipSave();
    toast(L1(__T(3197), "Undone to before the dead end.")); return;
  }
  { const mp = t.closest("[data-matchpick]"); if (mp && UI.match) { const m = UI.match, k = +mp.dataset.matchpick; if (doAct(S => opMatchRew(S, m.key, m.gid, k)) === false && !UI.match) UI.match = m; return; } } // 照合：当てはめ方を選ぶ
  if (t.closest("[data-matchx]")) { UI.match = null; renderDynamic(); return; }
  if (t.closest(".orpick") && !t.closest("[data-tpick]") && !t.closest("[data-tgo]") && !t.closest("[data-occ]") && !t.closest("[data-rewgo]") && !t.closest("[data-rewx]") && !t.closest("[data-rewflip]")) return;
  if (UI.rew) {
    const oc = t.closest("[data-occ]");
    if (oc) { const k = +oc.dataset.occ; UI.rew.sel = UI.rew.sel.includes(k) ? UI.rew.sel.filter(x => x !== k) : [...UI.rew.sel, k].sort(); renderDynamic(); return; }
    if (t.closest("[data-rewx]")) { UI.rew = null; renderDynamic(); return; }
    if (t.closest("[data-rewflip]")) { UI.rew.dir = UI.rew.dir === "rev" ? "std" : "rev"; const inf = rewInfo(S.goals[S.active], UI.rew); UI.rew.n = countOcc(inf.tgt, inf.from); UI.rew.sel = Array.from({ length: UI.rew.n }, (_, i) => i); renderDynamic(); return; }
    if (t.closest("[data-rewgo]")) { const rw = UI.rew; if (doAct(S => rewOp(S, rw, rw.sel)) === false && !UI.rew) UI.rew = rw; return; }
  }
  if (t.closest("[data-tgo]") && UI.pick) { submitTerm(); return; }
  const tp = t.closest("[data-tpick]");
  if (tp && UI.pick) { const v = tp.dataset.tpick, pk = UI.pick; UI.pick = null;
    if (v === "x") renderDynamic(); else if (doAct(S => pickOp(S, pk, v)) === false) UI.pick = pk; else chainAllE(pk); return; } // 拒否されたら選択欄を開いたままにする
  const uf = t.closest("[data-unfold]");
  if (uf) { const v = uf.dataset.unfold; doAct(S => v === "door" ? opUnfoldDoor(S, S.active) : opUnfoldKey(S, v, S.active)); return; }
  const intro = t.closest("[data-intro]");
  if (intro) {
    const tg = S.goals[S.active].target;
    if (tg.t === "or") { UI.orChoice = UI.orChoice ? null : S.active; UI.pick = null; UI.sel = null; UI.can = new Set(); renderDynamic(); return; }
    if (tg.t === "ex") { UI.pick = UI.pick ? null : { kind: "exI", gid: S.active }; UI.orChoice = null; UI.sel = null; UI.can = new Set(); renderDynamic(); return; }
    if (tg.t === "all" && PREFS.manualNames && STAGE.fol) { UI.pick = UI.pick ? null : { kind: "allI", gid: S.active }; UI.orChoice = null; UI.sel = null; UI.can = new Set(); renderDynamic(); return; }
    doAct(S => opIntro(S, S.active)); return;
  }
  const split = t.closest("[data-split]");
  if (split) { const n = split.dataset.split, e = findEntry(S.goals[S.active], n);
    if (e && e.f.t === "all") { UI.pick = UI.pick && UI.pick.key === n ? null : { kind: "allE", key: n, gid: S.active }; UI.orChoice = null; UI.sel = null; UI.can = new Set(); renderDynamic(); return; }
    if (e && e.f.t === "ex" && PREFS.manualNames) { UI.pick = UI.pick && UI.pick.key === n ? null : { kind: "exE", key: n, gid: S.active }; UI.orChoice = null; UI.sel = null; UI.can = new Set(); renderDynamic(); return; }
    doAct(S => opSplit(S, n, S.active)); return; }
  const mx = t.closest("[data-mexp]");
  if (mx) { const k = mx.dataset.mexp; if (UI.mapExp.has(k)) UI.mapExp.delete(k); else UI.mapExp.add(k); renderDynamic(); return; }
  const go = t.closest("[data-goto]");
  if (go) { S.active = go.dataset.goto; UI.sel = null; UI.can = new Set(); UI.fx = true; UI.orChoice = null; UI.pick = null; renderDynamic(); return; }
  const key = t.closest("#rooms .key"); if (key) { tapKey(key.dataset.key); return; }
  const door = t.closest("#rooms .door"); if (door) { tapDoor(); return; }
  if (UI.sel && t.closest("#area")) select(null);
});

document.addEventListener("pointermove", e => { if (typeof UI === "object" && UI) UI.ptr = { x: e.clientX, y: e.clientY }; }, { passive: true });
document.addEventListener("pointerover", e => {
  if (e.pointerType !== "mouse" || SCREEN !== "play" || drag || !S || !PROB || UI.mode === "refute") return;
  const t = e.target.closest ? e.target : e.target.parentElement;
  const pick = t.closest("[data-scope-pick]");
  const n = pick ? +pick.dataset.scopePick : null;
  if (n !== UI.hoverScope) { UI.hoverScope = n; applyScope(); }
  if (!S.active || $(".overlay")) return;
  if (UI.previewHold) { if (Math.hypot(e.clientX - UI.previewHold.x, e.clientY - UI.previewHold.y) < 10) return; UI.previewHold = null; }
  // マウスを重ねた操作を試して、証明図に見本を出す
  const orp = t.closest("[data-orpick]"), intro = t.closest("[data-intro]"), split = t.closest("[data-split]");
  if (t.closest("[data-exfalso]")) return previewOp("exf", St => opExfalso(St, St.active));
  const ufv = t.closest("[data-unfold]");
  if (ufv) { const v = ufv.dataset.unfold; return previewOp("uf:" + v, St => v === "door" ? opUnfoldDoor(St, St.active) : opUnfoldKey(St, v, St.active)); }
  if (t.closest("[data-raa]")) return previewOp("raa", St => opRAA(St, St.active));
  const lpv = t.closest("[data-lempick]");
  if (lpv && UI.lemma) { const L = parse(STAGE.lemmas[+lpv.dataset.lempick]); return previewOp("lem:" + lpv.dataset.lempick, St => opCut(St, St.active, L)); }
  if (t.closest("[data-ind]")) return previewOp("ind", St => opInd(St, St.active));
  if (t.closest("[data-lemma]")) return previewOp("lemhint", null, { preview: true, rule: __T(792), fig: __T(3198) });
  if (orp && orp.dataset.orpick !== "x") { const side = orp.dataset.orpick; return previewOp("or:" + side, St => opOrIntro(St, St.active, side)); }
  if (UI.rew && t.closest("[data-rewgo]")) { const rw = UI.rew; return previewOp("rew:" + rw.sel.join(","), St => rewOp(St, rw, rw.sel)); }
  const tpv = t.closest("[data-tpick]");
  if (tpv && UI.pick && tpv.dataset.tpick !== "x") { const v = tpv.dataset.tpick, pk = UI.pick;
    return previewOp("tp:" + v, St => pickOp(St, pk, v)); }
  if (intro && S.goals[S.active].target.t === "ex")
    return previewOp("exhint", null, { preview: true, rule: "∃I", fig: __T(3199) });
  if (split && (findEntry(S.goals[S.active], split.dataset.split) || {}).f && findEntry(S.goals[S.active], split.dataset.split).f.t === "all")
    return previewOp("allhint", null, { preview: true, rule: "∀E", fig: __T(3200) });
  if (intro) {
    if (S.goals[S.active].target.t === "or")
      return previewOp("orhint", null, { preview: true, rule: "∨I", fig: __T(3201) });
    return previewOp("intro", St => opIntro(St, St.active));
  }
  if (split) { const k = split.dataset.split; return previewOp("split:" + k, St => opSplit(St, k, St.active)); }
  if (UI.sel) {
    const door = t.closest("#rooms .door"), key = t.closest("#rooms .key");
    if (door) { const a = UI.sel; return previewOp("use:" + a, St => opUse(St, a, St.active)); }
    if (key && key.dataset.key !== UI.sel) { const a = UI.sel, b = key.dataset.key; return previewOp("comb:" + a + ":" + b, St => opCombine(St, a, b, St.active)); }
  }
  endPreview();
});

/* --- 入力（ドラッグ：マウスとタッチの両方に対応） --- */
let pend = null, drag = null;
document.addEventListener("pointerdown", e => {
  if (SCREEN !== "play" || (e.button != null && e.button > 0)) return;
  const key = e.target.closest && e.target.closest("#rooms .key");
  if (!key || e.target.closest(".mainop")) return;
  pend = { name: key.dataset.key, x: e.clientX, y: e.clientY, el: key };
});
window.addEventListener("pointermove", e => {
  if (!pend) return;
  if (!drag) {
    if (Math.hypot(e.clientX - pend.x, e.clientY - pend.y) < 8) return;
    const ghost = document.createElement("div");
    ghost.className = "ghost"; ghost.innerHTML = pend.el.outerHTML;
    ghost.firstElementChild.classList.remove("sel", "can", "fresh");
    document.body.appendChild(ghost); document.body.classList.add("dragging");
    drag = { name: pend.name, ghost, over: null };
    select(pend.name);
  }
  e.preventDefault();
  drag.ghost.style.left = e.clientX + "px"; drag.ghost.style.top = e.clientY + "px";
  const el = document.elementFromPoint(e.clientX, e.clientY);
  let tgt = el && (el.closest("#rooms .door") || el.closest("#rooms .key"));
  if (tgt && tgt.dataset.key === drag.name) tgt = null;
  if (drag.over !== tgt) {
    if (drag.over) drag.over.classList.remove("drop-hover");
    if (tgt) tgt.classList.add("drop-hover");
    drag.over = tgt;
    const a = drag.name; // ドラッグ中も、落とす先に応じて証明図に見本を出す
    if (!tgt) endPreview();
    else if (tgt.classList.contains("door")) previewOp("use:" + a, St => opUse(St, a, St.active));
    else { const b = tgt.dataset.key; previewOp("comb:" + a + ":" + b, St => opCombine(St, a, b, St.active)); }
  }
}, { passive: false });
function endDrag() {
  if (!drag) return null;
  const d = drag; drag = null;
  d.ghost.remove(); document.body.classList.remove("dragging");
  if (d.over) d.over.classList.remove("drop-hover");
  return d;
}
window.addEventListener("pointerup", () => {
  if (!pend) return;
  pend = null;
  const d = endDrag();
  if (!d) return; // 動かしていなければタップとしてクリック処理に任せる
  suppressUntil = Date.now() + 350;
  if (!d.over) { endPreview(); select(null); return; }
  if (d.over.classList.contains("door")) doAct(S => opUse(S, d.name, S.active));
  else { const other = d.over.dataset.key; doAct(S => opCombine(S, d.name, other, S.active)); }
});
window.addEventListener("pointercancel", () => { pend = null; if (endDrag()) { endPreview(); select(null); } });

document.addEventListener("keydown", e => { // 本を開いているときは、← → でページをめくる
  if (BOOK_UI && document.querySelector(".overlay .modal.book-modal") && (e.key === "ArrowLeft" || e.key === "ArrowRight")) { e.preventDefault(); bookGo(BOOK_UI.page + (e.key === "ArrowRight" ? 1 : -1)); return; }
});
document.addEventListener("keydown", e => {
  if (e.target && e.target.tagName === "TEXTAREA") return; // 白いカードに書いているときは、ほかのキー操作を無効にする
  if (document.getElementById("endShow")) { // 結末の演出中：Enter・スペース・→ で次の文へ（ボタンにいるときはボタンを押す）
    if ((e.key === "Enter" || e.key === " " || e.key === "ArrowRight") && ES && ES.scene === "fin") { e.preventDefault(); if (!esFF()) esPopup(); return; }
    if ((e.key === "Enter" || e.key === " " || e.key === "ArrowRight") && !(e.target && e.target.closest && e.target.closest("button"))) { e.preventDefault(); esFF(); }
    return; }
  if (e.key === "Escape") { if ($(".overlay")) closeModal(); else if (UI.sel) select(null); return; }
  if ((e.key === "Enter" || e.key === " ") && e.target.matches && e.target.matches("#rooms .key, #rooms .door")) { e.preventDefault(); e.target.click(); return; }
  if (e.target && e.target.id === "lemmaInput") { if (e.key === "Enter") { e.preventDefault(); submitLemma(); } return; } // 入力欄では他のキー操作を無効にする
  if (e.target && e.target.id === "termInput") { if (e.key === "Enter") { e.preventDefault(); submitTerm(); } return; }
  if (SCREEN === "play" && PROB && !$(".overlay") && (e.key === "z" || e.key === "Z") && !e.altKey) { e.preventDefault(); UI.mode === "refute" ? undoR() : undo(); }
});

// 動作確認用

applyTheme();
renderTools();
renderSelect();
})();
