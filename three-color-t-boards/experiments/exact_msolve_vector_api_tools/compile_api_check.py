#!/usr/bin/env python3
"""Verify that accidental dense/stored pointer or scalar use is a compile error."""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parent
header='#include "'+str(R/'msolve-cc044551f8e202d00691990fd3fd0b1226a88ea2/src/neogb/data.h')+'"\n'
cases={
 'dense_pointer_from_stored':'exp_t *p=h->ev[1];(void)p;',
 'stored_pointer_from_dense':'stored_exp_t *p=d;(void)p;',
 'raw_scalar_read':'exp_t x=h->ev[1][1];(void)x;',
 'raw_scalar_write':'h->ev[1][1]=1;',
 'raw_scalar_arithmetic':'int x=h->ev[1][1]+1;(void)x;',
 'wrong_import_source':'stored_exp_import(h->ev[1],h->ev[2],h->evl,h->evbytes);',
 'wrong_export_destination':'stored_exp_export(h->ev[1],h->evl,h->ev[2],h->evbytes);',
 'wrong_copy_source':'stored_exp_copy(h->ev[1],d,h->evl,h->evbytes);',
 'wrong_read_source':'(void)stored_exp_read(d,0,h->evl);',
 'wrong_write_destination':'stored_exp_write(d,0,0,h->evl);',
 'valid':'stored_exp_import(h->ev[1],d,h->evl,h->evbytes);stored_exp_export(d,h->evl,h->ev[1],h->evbytes);stored_exp_write(h->ev[1],0,stored_exp_read(h->ev[2],0,h->evl),h->evl);'
}
results=[]
for name,body in cases.items():
 source=header+'void probe(ht_t *h,exp_t *d){'+body+'}\n'
 command=['cc','-std=c23','-Wall','-Wextra','-Wpedantic','-Werror','-fsyntax-only','-x','c','-']
 p=subprocess.run(command,input=source,capture_output=True,text=True)
 assert (p.returncode==0)==(name=='valid'),(name,p)
 (R/('compile_api_'+name+'.log')).write_text(p.stdout+p.stderr)
 results.append(dict(name=name,returncode=p.returncode,source=source,command=command))
(R/'compile_api_check.json').write_text(json.dumps(dict(status='PASS',negative_cases=len(cases)-1,positive_cases=1,results=results),indent=2)+'\n')
print('PASS 10 compiler-enforced misuse rejections; 1 valid typed use')
