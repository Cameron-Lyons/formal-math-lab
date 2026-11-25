#!/usr/bin/env python3
"""Mechanical first pass; compiler diagnostics and manual diff audit follow.

This is not an attestation that all aliases have been converted.
"""
from pathlib import Path
import re,json
R=Path(__file__).resolve().parent;S=Path(json.loads((R/'source.json').read_text())['source_directory'])


def mask(text):
    # Keep offsets/braces, but hide comments and literals from lexical scans.
    pattern=r'/\*[\s\S]*?\*/|//[^\n]*|"(?:\\.|[^"\n\\])*"|\'(?:\\.|[^\'\n\\])*\''
    return re.sub(pattern,lambda m:''.join('\n' if c=='\n' else ' ' for c in m[0]),text)


def close(text,start,left='[',right=']'):
    assert text[start]==left;depth=0
    for i in range(start,len(text)):
        depth += (text[i]==left)-(text[i]==right)
        if depth==0:return i
    raise ValueError('unbalanced delimiter')


def direct(text):
    m=mask(text);edits=[]
    def atom_start(end):
        i=end-1
        while i>=0 and m[i].isspace():i-=1
        if m[i] in '])':
            right=m[i];left='[' if right==']' else '(';depth=1;j=i-1
            while depth:
                depth+=(m[j]==right)-(m[j]==left);j-=1
            start=j+1
            if right==']':return atom_start(start)
            return start
        assert m[i].isalnum() or m[i]=='_',m[max(0,i-20):end]
        while i>=0 and (m[i].isalnum() or m[i]=='_'):i-=1
        return i+1
    for match in re.finditer(r'->ev\s*\[',m):
        start=atom_start(match.start())
        while m[max(0,start-2):start]=='->' or m[max(0,start-1):start]=='.':
            start=atom_start(start-(2 if m[start-2:start]=='->' else 1))
        a=match.end()-1;b=close(m,a);c=b+1
        while c<len(m) and m[c].isspace():c+=1
        if c>=len(m) or m[c]!='[':continue
        d=close(m,c);base=text[start:match.start()]
        pointer=text[start:b+1];index=text[c+1:d]
        edits.append((start,d+1,f'stored_exp_read({pointer}, {index}, {base}->evl)'))
    for a,b,s in reversed(edits):text=text[:a]+s+text[b:]
    return text,len(edits)


def functions(text):
    m=mask(text);depth=0;start=None;header_start=0
    for i,c in enumerate(m):
        if c=='{':
            if depth==0:
                prev=m[:i].rstrip()
                if prev.endswith(')'):
                    start=i
                    header_start=max(m.rfind(';',0,i),m.rfind('}',0,i))+1
            depth+=1
        elif c=='}':
            depth-=1
            if depth==0 and start is not None:
                yield header_start,start,i+1;start=None


def aliases(fragment):
    m=mask(fragment);arrays={};singles={};edits=[]
    for match in re.finditer(r'\b((?:stored_)?exp_t\s*\*(?:\s*const)?\s*\*(?:\s*const)?)\s*(\w+)\s*=\s*([A-Za-z_]\w*(?:->\w+)*)->ev\b',m):
        arrays[match[2]]=match[3]
        if match[1].startswith('exp_t'):edits.append((match.start(1),match.start(1)+5,'stored_exp_t'))
    if 'reinsert_in_hash_table(' in fragment.split('{',1)[0]:
        arrays['oev']='ht'
        param=re.search(r'\bexp_t\s*\*\s*const\s*\*oev',m)
        assert param;edits.append((param.start(),param.start()+5,'stored_exp_t'))
    declarations=list(re.finditer(r'\bexp_t\s*\*(?:\s*const)?\s*(\w+)',m))
    for match in declarations:
        name=match[1]
        source=re.search(r'\b'+re.escape(name)+r'\s*=\s*([A-Za-z_]\w*(?:->\w+)*)->ev\s*\[',m)
        root=source[1] if source else None
        if root is None:
            for array,base in arrays.items():
                if re.search(r'\b'+re.escape(name)+r'\s*=\s*'+array+r'\s*\[',m):root=base;break
        if root:
            singles[name]=root;edits.append((match.start(),match.start()+5,'stored_exp_t'))
    for a,b,s in reversed(sorted(set(edits))):fragment=fragment[:a]+s+fragment[b:]
    # Names remain the same after their declarations become type-distinct.
    m=mask(fragment);edits=[]
    for name,root in singles.items():
        for match in re.finditer(r'(?<![A-Za-z0-9_>.])'+re.escape(name)+r'\s*\[',m):
            a=match.end()-1;b=close(m,a);index=fragment[a+1:b]
            edits.append((match.start(),b+1,f'stored_exp_read({name}, {index}, {root}->evl)'))
    # Simple nested writes are left to compiler/manual audit rather than guessed.
    for i,(a,b,s) in enumerate(edits):
        for c,d,_ in edits[:i]:
            assert b<=c or d<=a,('overlapping alias edits',fragment[a:b],fragment[c:d])
    for a,b,s in reversed(sorted(edits)):fragment=fragment[:a]+s+fragment[b:]
    return fragment,dict(arrays=arrays,stored_aliases=singles)


def writes(text):
    m=mask(text);edits=[]
    for match in re.finditer(r'\bstored_exp_read\(',m):
        a=match.end()-1;b=close(m,a,'(',')');tail=b+1
        while tail<len(m) and m[tail].isspace():tail+=1
        operation=re.match(r'(\+=|-=|\*=|=(?!=))',m[tail:])
        if not operation:continue
        args=text[a+1:b].split(',');assert len(args)==3,args
        end=m.find(';',tail);assert end>=0
        rhs=text[tail+len(operation[1]):end].strip()
        if operation[1]!='=':rhs=text[match.start():b+1]+' '+operation[1][0]+' ('+rhs+')'
        edits.append((match.start(),end,'stored_exp_write('+args[0]+','+args[1]+', '+rhs+','+args[2]+')'))
    for a,b,s in reversed(edits):text=text[:a]+s+text[b:]
    return text


records=[]
for path in (S/'src').rglob('*.c'):
    text=path.read_text();text,direct_count=direct(text)
    blocks=list(functions(text));report=[]
    for start,body,end in reversed(blocks):
        transformed,info=aliases(text[start:end])
        if info['arrays'] or info['stored_aliases']:
            report.append(dict(header=text[start:body].strip()[:150],**info))
        text=text[:start]+transformed+text[end:]
    text=writes(text)
    if direct_count or report:
        path.write_text(text);records.append(dict(path=str(path.relative_to(S)),direct_reads=direct_count,functions=report))
(R/'mechanical_alias_inventory.json').write_text(json.dumps(records,indent=2)+'\n')
print('converted',len(records),'source files; compiler/manual audit still required')
