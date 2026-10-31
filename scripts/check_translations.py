#!/usr/bin/env python3
"""Check Chinese placeholder parity against the original bilingual catalog."""
import json,re,pathlib
root=pathlib.Path(__file__).resolve().parent.parent
a=(root/'src/i18n/catalog.js').read_text()
b=(root/'src/i18n/zh-CN.js').read_text()
tlx=json.loads(a.split('const TLX = ',1)[1].rsplit(';',1)[0])
trans=json.loads(b.split('Object.freeze(',1)[1].rsplit(');',1)[0])
for k,v in trans.items():
 i=int(k)
 assert i<len(tlx)
 old=set(re.findall(r'⟦\d+⟧',tlx[i][0]))
 new=set(re.findall(r'⟦\d+⟧',v))
 if old != new:raise AssertionError(f'entry {k}: placeholder mismatch {old} != {new}')
print(f'OK: {len(trans)} translated / {len(tlx)} total entries; all placeholder sets preserved.')
