/* Reproduce the visible locale routes, including Japanese dynamic interpolation. */
const fs = require('node:fs');
const vm = require('node:vm');
const path = require('node:path');
const assert = require('node:assert/strict');
const root = path.join(__dirname, '..');
const app = fs.readFileSync(path.join(root, 'src/js/app.js'), 'utf8');
const prefix = app.slice(app.indexOf('const __T_ZH_RECENT'), app.indexOf('const RD ='));
const localize = app.slice(app.indexOf('const L1 = '), app.indexOf('if (LANG === "en" && !document.getElementById("enFonts"))'));
assert(prefix.includes('__T_ZH_RECENT'));
assert(localize.includes('__T_ZH_RECENT.has(ja)'));
const source = fs.readFileSync(path.join(root,'src/i18n/catalog.js'),'utf8') + '\n' +
  fs.readFileSync(path.join(root,'src/i18n/zh-CN.js'),'utf8');
function locale(lang) {
  const context = vm.createContext({});
  vm.runInContext(source + '\nconst LANG = ' + JSON.stringify(lang) + ';\n' +
    prefix + '\n' + localize + '\nthis.localeTest = {T:__T, L1};', context);
  return context.localeTest;
}
const zh=locale('zh-CN');
for (const [index, old] of [
  [1912,'No more dead-end notices'],
  [1913,'Up to Level 6'],
  [1992,'How truth values are decided'],
  [1989,'Assignment'],
]) {
  const result = zh.L1(zh.T(index), old);
  assert(!result.includes(old), 'English fallback for ' + index);
  assert(/[\u3400-\u9fff]/.test(result), 'Missing Chinese characters for ' + index);
}
const truth = zh.T(1992,[zh.T(1989,['A','B','A→B','A','B','¬A','A'])]);
assert(truth.includes('真值如何确定'));
assert(truth.includes('由可靠性定理'));
assert(!truth.includes('How truth values are decided'));
const deadoff=zh.L1(zh.T(1913), 'Up to Level 6');
assert(deadoff.includes('不再给出死路提醒'));
// Previously, the kana heuristic threw away an entire translated paragraph.
const injected=zh.L1(zh.T(1913,[]).replace('提醒','提醒（テスト）'), 'No more dead-end notices');
// The normal __T+L1 call, with a Japanese argument substituted, must survive.
const mixed=zh.L1(zh.T(1992,[zh.T(1989,['テスト','B','A→B','A','B','¬A','A'])]), 'How truth values are decided');
assert(mixed.includes('真值如何确定'));
assert(mixed.includes('テスト'));
const ja=locale('ja'), en=locale('en');
assert(ja.T(1992).includes('真偽の決まり方'));
assert(en.T(1992).includes('How truth values are decided'));
assert(en.L1(en.T(1912), 'No more dead-end notices') === 'No more dead-end notices');
assert(zh.L1('これはテスト','English fallback') === 'English fallback');
console.log('PASS: 3-language routes, truth-assignment guide, dead-end explanation, and interpolated Japanese text.');
