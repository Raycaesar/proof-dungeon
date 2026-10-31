const assert = require('node:assert/strict');
const fs = require('node:fs');
const vm = require('node:vm');
const source = fs.readFileSync('src/i18n/zh-CN.js', 'utf8');
const translation = vm.runInNewContext(source + '\nZH_CN');
const catalog = JSON.parse(fs.readFileSync('src/i18n/catalog.js', 'utf8').split('const TLX = ')[1].trim().replace(/;$/, ''));
const ids = [17, 18, 19, 20, 21, 54, 56, 57, 58, 59, 61, 63, 64, 65, 67, 68, 69, 70, 72, 73, 74, 75, 76, 80, 81, 82, 83, 85, 86, 87, 88, 90, 91, 92, 93, 95, 96, 97, 98, 100, 101, 102, 103, 107, 108, 110, 112, 113, 114, 115, 117, 118, 119, 120, 122, 123, 124, 125, 127, 128, 129, 130, 131, 135, 136, 137, 138, 140, 141, 142, 143, 145, 146, 147, 148, 150, 151, 152, 153, 155, 156, 157, 158, 159, 160, 161, 165, 166, 167, 168, 170, 171, 172, 173, 175, 176, 177, 179, 180, 181, 182, 183, 185, 186, 187, 188, 189, 191, 192, 193, 194, 195, 196, 197, 198, 202, 203, 204, 205, 207, 208, 209, 210, 212, 214, 215, 217, 218, 219, 220, 222, 223, 224, 225, 229, 230, 231, 232, 234, 235, 236, 237, 238, 240, 241, 242, 243, 244, 245, 246, 250, 251, 252, 253, 255, 256, 257, 258, 260, 261, 262, 263, 265, 266, 267, 268, 270, 271, 272, 273, 274, 278, 279, 280, 281, 282, 284, 285, 286, 287, 289, 290, 291, 292, 294, 295, 296, 297, 298, 299, 300, 301, 303, 304, 305, 306, 308, 309, 310, 311, 313, 314, 315, 316, 320, 321, 322, 323, 325, 326, 327, 328, 330, 331, 332, 333, 335, 336, 337, 338, 339, 341, 342, 343, 344, 345, 347, 348, 349, 350, 352, 353, 354, 355, 357, 359, 360, 361, 362, 364, 365, 366, 367, 369, 370, 371, 372, 374, 375, 376, 377, 381, 382, 383, 384, 386, 387, 388, 389, 390, 392, 393, 394, 395, 397, 398, 399, 400, 402];
const placeholders = s => [...s.matchAll(/⟦\d+⟧/g)].map(m=>m[0]).sort();
for (const id of ids) {
  assert.ok(typeof translation[id] === 'string' && translation[id].length, `Missing Chinese translation: ${id}`);
  assert.deepEqual(placeholders(translation[id]), placeholders(catalog[id][0]), `Placeholder mismatch at ${id}`);
  for (const token of catalog[id][0].match(/\{\{[^}]+\}\}/g)||[]) assert.ok(translation[id].includes(token), `Missing reference ${token} at ${id}`);
}
assert.equal(ids.length, 269);
console.log(`OK: ${ids.length} batch-05 translations with preserved placeholders and references.`);
