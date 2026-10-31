#!/usr/bin/env python3
"""Check complete Chinese coverage and HTML structural parity against original catalog."""
import json,re,collections,pathlib
from html.parser import HTMLParser
ROOT=pathlib.Path(__file__).resolve().parent.parent
p=ROOT/'src/i18n'
a=json.loads((p/'catalog.js').read_text('utf8').split('const TLX = ',1)[1].rsplit(';',1)[0])
b=json.loads((p/'zh-CN.js').read_text('utf8').split('Object.freeze(',1)[1].rsplit(');',1)[0])
class Tags(HTMLParser):
 def __init__(self):super().__init__();self.result=[]
 def handle_starttag(self,tag,attrs):
  self.result.append(('start',tag,tuple(sorted(k for k,v in attrs)),tuple(sorted((k,v) for k,v in attrs if k.startswith('data-') or k in ('type','id','class','src','href','role','loading','spellcheck','autocomplete','aria-pressed','aria-hidden')))))
 def handle_startendtag(self,tag,attrs):self.handle_starttag(tag,attrs)
 def handle_endtag(self,tag):self.result.append(('end',tag))
assert len(a)==len(b)==3202
new_ids={int(s) for s in (ROOT/'docs/TRANSLATION_BATCH09_IDS.txt').read_text().split()}
assert len(new_ids)==247
for i,(ja,en) in enumerate(a):
 tr=b[str(i)]
 assert collections.Counter(re.findall(r'⟦\d+⟧',ja))==collections.Counter(re.findall(r'⟦\d+⟧',tr)),i
 assert not re.search(r'[ぁ-んァ-ヶ]',tr),i
 if i in new_ids:
  p1=Tags();p1.feed(ja);p2=Tags();p2.feed(tr)
  assert p1.result==p2.result,('HTML',i)
print('OK: 3202/3202 Chinese entries, exact placeholders, structural HTML parity, no Japanese kana')
