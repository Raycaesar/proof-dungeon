#!/usr/bin/env python3
"""Ensure translated HTML templates retain their operational tag/attribute structure."""
from html.parser import HTMLParser
import re, json, pathlib, collections
p=pathlib.Path(__file__).resolve().parents[1]
rows=json.loads((p/'src/i18n/catalog.js').read_text().split('const TLX = ',1)[1].rsplit(';',1)[0])
trans=json.loads((p/'src/i18n/zh-CN.js').read_text().split('Object.freeze(',1)[1].rsplit(');',1)[0])
class Parser(HTMLParser):
    def __init__(self): super().__init__(convert_charrefs=False);self.tags=[];self.attrs=[]
    def handle_starttag(self,tag,attrs):
      
      if tag not in ("b", "strong", "em", "i", "code"): self.tags.append(tag)
      
      if tag not in ("b", "strong", "em", "i", "code"): self.attrs.append((tag,tuple((k,v) for k,v in attrs if k in ('id','class','role','type','href','src','name','checked','disabled','autocomplete','spellcheck') or k.startswith('data-'))))
    def handle_startendtag(self,tag,attrs):self.handle_starttag(tag,attrs)

def html(s):
 a=Parser();a.feed(s);return a.tags,a.attrs
errors=[];total=0
for k,v in trans.items():
 i=int(k); j,e=rows[i];source=e or j
 if '<' not in v and '<' not in source:continue
 if ('<' in v)!=( '<' in source):
  # Some natural language text contains raw '<' or HTML only in a different source language.
  pass
 b=html(source);c=html(v)
 if b!=c:errors.append((i,b[0],c[0],b[1][:2],c[1][:2]))
 total+=1
print('HTML templates checked:',total,'mismatch count:',len(errors));
for err in errors[:30]:print('MISMATCH',err)
if errors:raise SystemExit(1)
