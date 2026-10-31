// Batch 06: audit Chinese countermodel analyses, independent of the proof engine.
const assert = require('node:assert/strict');
const fs = require('node:fs');
const vm = require('node:vm');
const path = require('node:path');
const root = path.join(__dirname, '..');
const ctx = vm.createContext({});
for (const name of ['catalog.js', 'zh-CN.js']) {
  vm.runInContext(fs.readFileSync(path.join(root, 'src/i18n', name), 'utf8'), ctx, { filename: name });
}
const catalog = vm.runInContext('TLX', ctx);
const zh = vm.runInContext('ZH_CN', ctx);
const findAll = (s, regex) => [...s.matchAll(regex)].map(m => m[0]).sort();
const placeholder = s => findAll(s, /⟦\d+⟧/g);
const crossref = s => findAll(s, /\{\{[^}]+\}\}/g);
const tags = s => findAll(s, /<\/?\s*[a-zA-Z][^<>]*>/g);
for (let id = 2158; id <= 2349; id++) {
  const text = zh[id];
  assert.equal(typeof text, 'string', `missing translation at ${id}`);
  const original = catalog[id][0];
  assert.deepEqual(placeholder(text), placeholder(original), `placeholder mismatch at ${id}`);
  assert.deepEqual(crossref(text), crossref(original), `reference mismatch at ${id}`);
  assert.deepEqual(tags(text), tags(original), `markup mismatch at ${id}`);
  assert.doesNotMatch(text, /[\u3040-\u30ff]/, `untranslated Japanese script at ${id}`);
}
assert.ok(Object.keys(zh).length >= 2566, "batch-06 translations must survive later updates");
assert.match(zh[2213], /量词/);
assert.match(zh[2234], /佐恩引理/);
assert.match(zh[2279], /独立/);
assert.ok(zh[2317].includes('data-cmd="retry"'));
assert.ok(zh[2347].includes('data-cmd="map"'));
console.log('PASS: 192 consecutive entries localized; placeholders, HTML structure and crossrefs preserved.');
