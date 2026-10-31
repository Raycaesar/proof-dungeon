// Ensure the continuous narrative block is localized without disturbing placeholders.
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const vm = require('node:vm');
const root = path.join(__dirname, '..');
const ctx = vm.createContext({});
for (const name of ['catalog.js', 'zh-CN.js']) {
  vm.runInContext(fs.readFileSync(path.join(root, 'src/i18n', name), 'utf8'), ctx, { filename: name });
}
const originals = vm.runInContext('TLX', ctx);
const translated = vm.runInContext('ZH_CN', ctx);
const ph = s => new Set([...s.matchAll(/⟦\d+⟧/g)].map(x => x[0]));
for (let i=1000; i<=1287; i++) {
  assert.ok(Object.hasOwn(translated, String(i)), `missing translated story ${i}`);
  assert.deepEqual([...ph(translated[i])].sort(), [...ph(originals[i][0])].sort(), `placeholder mismatch ${i}`);
  assert.match(translated[i], /[\u3400-\u9fff]/, `expected Chinese script in ${i}`);
}
assert.equal(Object.keys(translated).length, 2105);
console.log('PASS: all 288 narrative entries localized; 2105 total; placeholders preserved.');
