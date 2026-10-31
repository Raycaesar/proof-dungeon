/* Ensure all raw bilingual body templates omitted from the translation index
 * have Chinese overrides, with stable pagination and usable MathJax syntax.
 */
const fs = require('node:fs');
const vm = require('node:vm');
const path = require('node:path');
const assert = require('node:assert/strict');
const root = path.join(__dirname, '..');
const booksCode = fs.readFileSync(path.join(root,'src/i18n/books.zh-CN.js'),'utf8');
const ctx=vm.createContext({});vm.runInContext(booksCode,ctx);
const books=vm.runInContext('BOOK_ZH_CN',ctx);
const expected={
  kripke:{def:2,force:2,persist:1,sound:3,ex:2,complete:3,rel:2,game:1},
  transl:{glivenko:2,fail:2,kuroda:2,embed:1},
  selfref:{barber:2,diag:2,decide:1,check:1,consis:2,godel:3,more:1},
};
const helpers={
 KEY:(...xs)=>`<div class="bk-key">${xs.join(' ')}</div>`,
 bkTable:(h,rows)=>`<table>${[h,...rows].map(row=>`<tr>${row.map(cell=>`<td>${cell}</td>`).join('')}</tr>`).join('')}</table>`,
 bkRefs:keys=>keys.join('、'),
};
let count=0;
for (const [book,sections] of Object.entries(expected)) {
  for (const [section,pageCount] of Object.entries(sections)) {
    assert.equal(typeof books[book]?.[section],'function',`Missing ${book}/${section}`);
    const html=books[book][section](helpers);
    assert.equal(html.split('<!--pg-->').length,pageCount,`Page count: ${book}/${section}`);
    assert(!/[ぁ-ゟ゠-ヿ]/.test(html),`Japanese kana: ${book}/${section}`);
    assert(!/\b(?:The|This|With|For|After|First)\s+(?:[a-z]{3,}\s+){2,}/.test(html),`English prose: ${book}/${section}`);
    assert.equal((html.match(/<p>/g)||[]).length,(html.match(/<\/p>/g)||[]).length,`HTML <p>: ${book}/${section}`);
    assert.equal((html.match(/\\\(/g)||[]).length,(html.match(/\\\)/g)||[]).length,`MathJax inline: ${book}/${section}`);
    assert(!/\$\{[^}]*\}/.test(html),`Unevaluated template ${book}/${section}`);
    assert(html.length>100);
    count++;
  }
}
const app=fs.readFileSync(path.join(root,'src/js/app.js'),'utf8');
const rawMatches=[...app.matchAll(/\bL1\(\s*String\.raw/g)];
assert.equal(rawMatches.length,count,`A raw bilingual book section was added without a Chinese override: ${rawMatches.length} vs ${count}`);
assert(app.includes('BOOK_ZH_CN[id]?.[sec.id]'));
console.log(`PASS: ${count} raw-language book sections translated, all original page splits and formulas preserved.`);
