/* Verify dynamically rendered Chinese book pages without a browser. */
const fs = require('node:fs');
const vm = require('node:vm');
const path = require('node:path');
const assert = require('node:assert/strict');
const script = fs.readFileSync(path.join(__dirname,'../src/i18n/books.zh-CN.js'),'utf8');
const ctx = vm.createContext({});
vm.runInContext(script,ctx);
const books = vm.runInContext('BOOK_ZH_CN',ctx);
const seen = [];
const helpers = {
  KEY: (...x) => `<div class="bk-key">${x.map(s=>`<div>${s}</div>`).join('')}</div>`,
  bkTable: (h,r) => `<table><thead>${h.join(' / ')}</thead><tbody>${r.map(x=>x.join(' | ')).join('')}</tbody></table>`,
  bkRefs: keys=>keys.join('、'),
};
const sections = ['def','force','persist','sound','ex','complete','rel','game'];
const pages = {def:2,force:2,persist:1,sound:3,ex:2,complete:3,rel:2,game:1};
for(const section of sections) {
  assert.equal(typeof books.kripke[section],'function',`Missing kripke.${section}`);
  const html=books.kripke[section](helpers);
  assert(!/[ぁ-ゟ゠-ヿ]/.test(html),`Japanese kana remain in kripke.${section}`);
  assert(!/\$\{[^}]*\}/.test(html),`Unevaluated template in kripke.${section}`);
  assert.equal(html.split('<!--pg-->').length,pages[section],`Page count changed in kripke.${section}`);
  assert.equal((html.match(/<p>/g)||[]).length,(html.match(/<\/p>/g)||[]).length);
  assert.equal((html.match(/\\\(/g)||[]).length,(html.match(/\\\)/g)||[]).length);
  assert(html.length>80);
  seen.push(section);
}
console.log('PASS: complete Kripke book translated (8 body sections, original pagination and math delimiters preserved).');
