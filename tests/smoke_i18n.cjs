/* Dependency-free smoke test for translation scripts, placeholders and language precedence. */
const fs = require('node:fs');
const vm = require('node:vm');
const path = require('node:path');
const assert = require('node:assert/strict');
const root = path.join(__dirname, '..');
const source = fs.readFileSync(path.join(root, 'src/js/app.js'), 'utf8');
const top = source.substring(0, source.indexOf('(() => {\n"use strict";'));
function run(lang) {
  const prefs = lang == null ? {} : {lang};
  const document = {documentElement:{lang:'ja'},title:'',querySelector:() => ({textContent:'original'})};
  const ctx = vm.createContext({
    document,
    localStorage:{getItem: () => JSON.stringify(prefs)},
    navigator:{language:'ja-JP'}
  });
  for (const f of ['src/i18n/catalog.js','src/i18n/zh-CN.js']) {
    vm.runInContext(fs.readFileSync(path.join(root,f),'utf8'),ctx,{filename:f});
  }
  vm.runInContext(top,ctx,{filename:'src/js/app.js'});
  return {translate:(i,variables)=>vm.runInContext(`__T(${i}, ${variables ? JSON.stringify(variables): 'undefined'})`,ctx),
    lang:vm.runInContext('LANG',ctx),html:document.documentElement.lang};
}
const zh=run(),en=run('en'),ja=run('ja');
assert.equal(zh.lang,'zh-CN');
assert.equal(zh.html,'zh-CN');
assert.equal(zh.translate(25),'假设之室');
assert.equal(zh.translate(29,['P∧Q','P','Q']),'要证明 P∧Q，只需分别证明 P 和 Q。');
assert.equal(en.translate(25),'Rooms of Assumption');
assert.equal(ja.translate(25),'仮定の部屋');
assert.equal(zh.translate(1),'括号不匹配');
assert(zh.translate(214).length>0);
console.log('PASS: Simplified Chinese defaults, placeholders interpolate, English/Japanese retain their original entries.');
