#!/usr/bin/env python3
"""Explicit dense/stored boundaries after the mechanical read conversion."""
from pathlib import Path
import json,re
R=Path(__file__).resolve().parent;S=Path(json.loads((R/'source.json').read_text())['source_directory'])
namespace={'__file__':str(R/'accessor_conversion.py')};exec((R/'accessor_conversion.py').read_text().split('records=[]')[0],namespace)
mask=namespace['mask'];close=namespace['close']


def function_span(text,name):
 m=mask(text);match=re.search(r'\b'+name+r'\s*\(',m);assert match,name
 a=m.find('(',match.start());b=close(m,a,'(',')');c=m.find('{',b)
 assert ';' not in m[b:c],name
 d=close(m,c,'{','}');return match.start(),c,d+1


def after(text,name,addition):
 _,_,end=function_span(text,name);return text[:end]+addition+text[end:]


path=S/'src/neogb/hash.c';s=path.read_text()
for name,returntype,extras in [
 ('generate_short_divmask','sdm_t',''),('is_contained_in_hash_table','int32_t',', const val_t h, hi_t *kp'),
 ('insert_in_hash_table','hi_t','')]:
 args={'generate_short_divmask':'dense, ht','is_contained_in_hash_table':'dense, ht, h, kp','insert_in_hash_table':'dense, ht'}[name]
 params={'generate_short_divmask':'a, ht','is_contained_in_hash_table':'a, ht, h, kp','insert_in_hash_table':'a, ht'}[name]
 second='ht_t *ht' if name=='insert_in_hash_table' else 'const ht_t *ht'
 add=f'''
/* Type-selected boundary: callers cannot reinterpret stored bytes as dense. */
static inline {returntype} {name}_stored(const stored_exp_t *a, {second}{extras})
{{
    exp_t dense[128];
    stored_exp_export(dense, ht->evl, a, ht->evbytes);
    return {name}({args});
}}
#define {name}({params}) _Generic((a), \\
    exp_t *: {name}, const exp_t *: {name}, \\
    stored_exp_t *: {name}_stored, const stored_exp_t *: {name}_stored)({params})
'''
 s=after(s,name,add)
# dense candidate imports; signature scratch was typed as stored and copies directly.
start,body,end=function_span(s,'insert_multiplied_signature_in_hash_table')
part=s[start:end].replace('memcpy(e, a, (unsigned long)evl * sizeof(exp_t));','stored_exp_copy(e, a, ht->evl, ht->evbytes);')
s=s[:start]+part+s[end:]
s=s.replace('memcpy(e, a, (unsigned long)evl * sizeof(exp_t));','stored_exp_import(e, a, ht->evl, ht->evbytes);')
s=s.replace('memcpy(e, a, (unsigned long)ht->evl * sizeof(exp_t));','stored_exp_import(e, a, ht->evl, ht->evbytes);')
s=s.replace('memcpy(e, n, (unsigned long)evl * sizeof(exp_t));','stored_exp_copy(e, n, ht->evl, ht->evbytes);')
s=s.replace('memcpy(bht->ev[bht->eld], uht->ev[lcms[l]],\n                (unsigned long)evl * sizeof(exp_t));',
            'stored_exp_copy(bht->ev[bht->eld], uht->ev[lcms[l]], bht->evl, bht->evbytes);')
s=s.replace('memcpy(evt, evs[hcm[row[l]]],\n                (unsigned long)evl * sizeof(exp_t));',
            'stored_exp_export(evt, bht->evl, evs[hcm[row[l]]], bht->evbytes);')
s=s.replace('ht->evl > SIZE_MAX/sizeof(exp_t) ||\n            new_esz > SIZE_MAX/((size_t)ht->evl*sizeof(exp_t)) ||',
            'ht->evbytes != stored_exp_bytes(ht->evl) ||\n            new_esz > SIZE_MAX/ht->evbytes ||')
s=s.replace('(size_t)sht->evl > SIZE_MAX/sizeof(exp_t))',
            'sht->evbytes != stored_exp_bytes(sht->evl))')
s=s.replace('bht == sht || bht->evl != sht->evl ||','bht == sht || bht->evl != sht->evl || bht->evbytes != sht->evbytes ||')
s=s.replace('memcpy(tmp, bht->ev[0], ht->evbytes * ht->esz);',
            'stored_exp_copy_vectors(tmp, bht->ev[0], ht->evl, ht->evbytes, ht->esz);')
s=s.replace('memmove(block+packed*sht->evbytes, block+id*sht->evbytes, vector_bytes);',
            'stored_exp_copy(block+packed*sht->evbytes, block+id*sht->evbytes, sht->evl, vector_bytes);')
# Dense row candidate: table realloc never invalidates this stack vector.
start,body,end=function_span(s,'insert_multiplied_poly_in_hash_table');part=s[start:end]
part=part.replace('    stored_exp_t *n;','')
part=part.replace('    stored_exp_t **ev2     = ht2->ev;','    exp_t n[ht1->evl];')
part=part.replace('        n = ev2[ht2->eld];\n','')
part=part.replace('stored_exp_write(n, j, checked_exp_add(ea[j], stored_exp_read(eb, j, ht1->evl)), ht2->evl);',
                  'n[j] = checked_exp_add(ea[j], stored_exp_read(eb, j, ht1->evl));')
s=s[:start]+part+s[end:]
s=after(s,'multiplied_poly_to_matrix_row',r'''
static inline hm_t *multiplied_poly_to_matrix_row_stored(
    ht_t *sht,const ht_t *bht,const val_t hm,const stored_exp_t *em,const hm_t *poly)
{
    exp_t dense[128];
    stored_exp_export(dense,bht->evl,em,bht->evbytes);
    return multiplied_poly_to_matrix_row(sht,bht,hm,dense,poly);
}
#define multiplied_poly_to_matrix_row(sht,bht,hm,em,poly) _Generic((em), \
    exp_t *: multiplied_poly_to_matrix_row, const exp_t *: multiplied_poly_to_matrix_row, \
    stored_exp_t *: multiplied_poly_to_matrix_row_stored, \
    const stored_exp_t *: multiplied_poly_to_matrix_row_stored)(sht,bht,hm,em,poly)
''')
path.write_text(s)

path=S/'src/neogb/f4sat.c';s=path.read_text()
s=after(s,'is_pure_power',r'''
static inline int is_pure_power_stored(const stored_exp_t *ev,const ht_t *ht)
{
    exp_t dense[128];
    stored_exp_export(dense,ht->evl,ev,ht->evbytes);
    return is_pure_power(dense,ht);
}
#define is_pure_power(ev,ht) _Generic((ev), \
    exp_t *: is_pure_power, const exp_t *: is_pure_power, \
    stored_exp_t *: is_pure_power_stored, const stored_exp_t *: is_pure_power_stored)(ev,ht)
''')
s=s.replace('memcpy(etmp, ht->ev[oqb[j]], (unsigned long)(nv+1)*sizeof(exp_t));;',
            'stored_exp_export(etmp, ht->evl, ht->ev[oqb[j]], ht->evbytes);')
s=s.replace('memset(bht->ev[0], 0, (unsigned long)bht->evl * sizeof(exp_t));',
            'for (size_t zero_lane=0;zero_lane<(size_t)bht->evl;++zero_lane)\n        stored_exp_write(bht->ev[0],zero_lane,0,bht->evl);')
path.write_text(s)

# These direct reads were hidden by a disabled debug block in the conservative
# mechanical scanner; explicit replacements are recorded for manual review.
path=S/'src/neogb/modular.c';s=path.read_text()
s=s.replace('2*bht->ev[sat->hm[0][OFFSET]][DEG]',
            '2*stored_exp_read(bht->ev[sat->hm[0][OFFSET]], DEG, bht->evl)')
s=s.replace('memset(etmp, 0, (unsigned long)(bht->evl) * sizeof(exp_t));',
            'for (size_t zero_lane=0;zero_lane<(size_t)bht->evl;++zero_lane)\n        stored_exp_write(etmp,zero_lane,0,bht->evl);')
s=s.replace('memset(bht->ev[0], 0, (unsigned long)(bht->evl) * sizeof(exp_t));',
            'for (size_t zero_lane=0;zero_lane<(size_t)bht->evl;++zero_lane)\n        stored_exp_write(bht->ev[0],zero_lane,0,bht->evl);')
s=s.replace('memset(bht->ev[0], 0, (unsigned long)bht->evl * sizeof(exp_t));',
            'for (size_t zero_lane=0;zero_lane<(size_t)bht->evl;++zero_lane)\n        stored_exp_write(bht->ev[0],zero_lane,0,bht->evl);')
path.write_text(s)

# Excluded signature path still has to compile without dense/stored casts.
path=S/'src/neogb/sba.c';s=path.read_text()
s=re.sub(r'stored_exp_read\(([^,]+), ([^,]+), ([^)]+)\)\+\+',
         r'stored_exp_write(\1, \2, stored_exp_read(\1, \2, \3)+1, \3)',s)
s=s.replace('memcpy(ev, ht->ev[smat->pr[idx][SM_SMON]],\n            (unsigned long)ht->evl * sizeof(exp_t));;',
            'stored_exp_copy(ev, ht->ev[smat->pr[idx][SM_SMON]], ht->evl, ht->evbytes);')
s=s.replace('memcpy(ev, ht->ev[cr[i]], (unsigned long)ht->evl * sizeof(exp_t));',
            'stored_exp_copy(ev, ht->ev[cr[i]], ht->evl, ht->evbytes);')
path.write_text(s)

# This saturation-only prefix clear deliberately retains the upstream nv count.
path=S/'src/neogb/convert.c';s=path.read_text()
s=s.replace('memset(ht->ev[0], 0, (uint64_t)ht->nv * sizeof(exp_t));',
            'for (size_t zero_lane=0;zero_lane<(size_t)ht->nv;++zero_lane)\n        stored_exp_write(ht->ev[0],zero_lane,0,ht->evl);')
path.write_text(s)
print('typed import/export/hash boundaries inserted')
