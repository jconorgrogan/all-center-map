#!/usr/bin/env python3
"""Proof-side token diagnostic; kernel/Comparator axiom audits remain authoritative.
Mask nested Lean comments and string contents so documentation is not mistaken
for declarations. The independent Challenge protocol hole is checked separately.
"""
import re
from pathlib import Path

def code_only(text):
    result=[]; i=0; depth=0; string=False
    while i<len(text):
        if depth:
            if text.startswith('/-',i): depth+=1;result.extend('  ');i+=2
            elif text.startswith('-/',i): depth-=1;result.extend('  ');i+=2
            else: result.append('\n' if text[i]=='\n' else ' ');i+=1
        elif string:
            if text[i]=='\\': result.extend('  ');i+=2
            elif text[i]=='"': string=False;result.append(' ');i+=1
            else: result.append('\n' if text[i]=='\n' else ' ');i+=1
        elif text.startswith('/-',i): depth=1;result.extend('  ');i+=2
        elif text.startswith('--',i):
            end=text.find('\n',i);end=len(text) if end<0 else end
            result.extend(' '*(end-i));i=end
        elif text[i]=='"': string=True;result.append(' ');i+=1
        else: result.append(text[i]);i+=1
    if depth or string: raise ValueError('Unterminated Lean comment/string')
    return ''.join(result)

def main():
    root=Path(__file__).resolve().parent.parent
    bad=re.compile(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b|\bLean\.ofReduceBool\b')
    errors=[]
    paths=sorted((root/'Proof').rglob('*.lean'))+[root/'Solution.lean']
    for path in paths:
        for number,line in enumerate(code_only(path.read_text()).splitlines(),1):
            if bad.search(line): errors.append(f'{path.relative_to(root)}:{number}: {line.strip()}')
    challenge=code_only((root/'Challenge.lean').read_text())
    if len(re.findall(r'\bsorry\b',challenge))!=1:
        errors.append('Challenge must contain exactly one intentional protocol hole')
    for error in errors: print(error)
    if errors: return 1
    print(f'Proof-source scan passed for {len(paths)} files; one separate Challenge protocol hole.')
    return 0

if __name__=='__main__':
    raise SystemExit(main())
