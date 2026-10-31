// Batch 07: verify all previously untranslated 404–716 tutorial and stage-hint entries.
const assert = require('node:assert/strict');
const fs = require('node:fs');
const vm = require('node:vm');
const path = require('node:path');
const root = path.resolve(__dirname, '..');
const ctx = vm.createContext({});
for (const name of ['catalog.js', 'zh-CN.js']) {
  vm.runInContext(fs.readFileSync(path.join(root, 'src/i18n', name), 'utf8'), ctx, { filename: name });
}
const catalog = vm.runInContext('TLX', ctx);
const zh = vm.runInContext('ZH_CN', ctx);
const hits = (s, regex) => [...s.matchAll(regex)].map(m => m[0]).sort();
const patterns = [
  /⟦\d+⟧/g,
  /\{\{[^}]+\}\}/g,
  /<\/?\s*[a-zA-Z][^<>]*>/g,
];
const ids = new Set();
for (const line of fs.readFileSync(path.join(root, 'docs', 'TRANSLATION_BATCH07_IDS.txt'), 'utf8').trim().split('\n')) {
  if (line.trim()) ids.add(Number(line.trim()));
}
assert.equal(ids.size, 253);
for (const id of ids) {
  const text = zh[id];
  assert.equal(typeof text, 'string', `missing translation ${id}`);
  assert.ok(text.trim(), `blank translation ${id}`);
  for (const pat of patterns) {
    assert.deepEqual(hits(text, pat), hits(catalog[id][0], pat), `tokens or markup mismatch ${id}`);
  }
  assert.doesNotMatch(text, /[\u3040-\u30ff]/, `Japanese kana left at ${id}`);
}
assert.equal(Object.keys(zh).length, 2819);
assert.match(zh[451], /可靠性定理/);
assert.match(zh[671], /格利文科定理/);
assert.match(zh[682], /黑田翻译/);
assert.match(zh[703], /独立/);
console.log('PASS: 253 batch-07 tutorials and hints translated, preserved placeholders, crossreferences and HTML.');
