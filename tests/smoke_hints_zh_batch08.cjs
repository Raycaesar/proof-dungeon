// Batch 08: translations for the missing 762–999 entries, including the Lean/help table.
const assert = require('node:assert/strict');
const fs = require('node:fs');
const vm = require('node:vm');
const path = require('node:path');
const root = path.resolve(__dirname, '..');
const ctx = vm.createContext({});
for (const name of ['catalog.js', 'zh-CN.js']) {
  vm.runInContext(fs.readFileSync(path.join(root,'src/i18n', name),'utf8'),ctx,{filename:name});
}
const c = vm.runInContext('TLX',ctx);
const z = vm.runInContext('ZH_CN',ctx);
const ids = fs.readFileSync(path.join(root,'docs/TRANSLATION_BATCH08_IDS.txt'),'utf8').trim().split('\n').map(Number);
assert.equal(ids.length, 136);
assert.equal(new Set(ids).size,136);
assert.ok(ids.every(id => id>=762 && id<=999));
const tokens = s => Array.from(s.matchAll(/⟦\d+⟧|\{\{[^}]+\}\}/g),m=>m[0]).sort();
for (const id of ids) {
  assert.equal(typeof z[id],'string', `missing ${id}`);
  assert.equal(z[id].trim().length>0,true, `empty ${id}`);
  assert.deepEqual(tokens(z[id]),tokens(c[id][0]), `placeholder mismatch ${id}`);
  assert.doesNotMatch(z[id],/[ぁ-んァ-ヶ]/,`Japanese kana left ${id}`);
}
assert.match(z[953],/操作|点击/);
assert.match(z[978],/翻译所/);
assert.match(z[979],/30258/);
assert.match(z[999],/矛盾/);
assert.ok(Object.keys(z).length>=2955);
console.log('PASS batch-08: 136 batch-08 tutorial, proof-tree, story and help entries retained.');
