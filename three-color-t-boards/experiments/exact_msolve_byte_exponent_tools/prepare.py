#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess,tarfile,difflib
R=Path(__file__).resolve().parent;E=R.parent;B=E/'exact_msolve_symbolic_reserve_tools'
base=json.loads((B/'source.json').read_text());S=R/Path(base['source_directory']).name
assert not S.exists()
with tarfile.open(base['source_archive']) as t:t.extractall(R,filter='data')
patches=base['predecessor_patches']+[dict(path=str(B/'symbolic-row-reserve.patch'),sha256=base['symbolic_reserve_patch_sha256'])]
for item in patches:
 p=Path(item['path']);assert hashlib.sha256(p.read_bytes()).hexdigest()==item['sha256'];subprocess.run(['patch','-p1','-i',str(p)],cwd=S,check=True,capture_output=True)
paths=['src/neogb/data.h','src/neogb/io.c','src/neogb/hash.c','src/neogb/symbol.c','src/neogb/engine.c','src/msolve/main.c']
before={p:(S/p).read_text() for p in paths}
s=before[paths[0]].replace('typedef uint16_t exp_t;  /* exponent type */',r'''/* Dedicated checked ordinary-F3 build: never truncate an exponent. */
typedef uint8_t exp_t;
static inline exp_t checked_exp_value(const int64_t value)
{
    if (value < 0 || value > UINT8_MAX) {
        fprintf(stderr, "Error: byte exponent/degree overflow.\n");
        exit(EXIT_FAILURE);
    }
    return (exp_t)value;
}
static inline exp_t checked_exp_add(const exp_t a, const exp_t b)
{
    return checked_exp_value((uint32_t)a+(uint32_t)b);
}
static inline exp_t checked_exp_sub(const exp_t a, const exp_t b)
{
    return checked_exp_value((int32_t)a-(int32_t)b);
}''')
(S/paths[0]).write_text(s)
s=before[paths[1]].replace('(exp_t)(iev+((int64_t)nv * idx))[i]', 'checked_exp_value((iev+((int64_t)nv * idx))[i])').replace('ev[0]   +=  ev[i+1];','ev[0] = checked_exp_add(ev[0], ev[i+1]);').replace('ev[ebl]    +=  ev[i+off];','ev[ebl] = checked_exp_add(ev[ebl], ev[i+off]);')
(S/paths[1]).write_text(s)
s=before[paths[2]].replace('a[j] = ht->ev[h1][j] + ht->ev[h2][j];','a[j] = checked_exp_add(ht->ev[h1][j], ht->ev[h2][j]);').replace('n[j]  = (exp_t)(ea[j] + eb[j]);','n[j] = checked_exp_add(ea[j], eb[j]);').replace('etmp[0]  += etmp[i];','etmp[0] = checked_exp_add(etmp[0], etmp[i]);').replace('etmp[ebl] += etmp[i];','etmp[ebl] = checked_exp_add(etmp[ebl], etmp[i]);')
(S/paths[2]).write_text(s)
s=before[paths[3]].replace('(exp_t)(elcm[l] - eb[l])','checked_exp_sub(elcm[l], eb[l])').replace('(exp_t)(e[k]-f[k])','checked_exp_sub(e[k], f[k])')
(S/paths[3]).write_text(s)
s=before[paths[4]]
marker='int initialize_gba_input_data('
guard=r'''/* Initial field domains certify the byte-degree bound max(6, 2*n+1) <= 255.
 * Only an explicit scalar multiple of x_i^3-x_i is accepted as a domain.
 * Every other initial monomial must have each coordinate at most two. */
static void checked_byte_model(const int32_t *lens, const int32_t *exps,
        const int32_t *cfs, const int32_t nv, const int32_t ng)
{
    if (nv < 1 || nv > 127 || ng < nv || lens == NULL ||
            exps == NULL || cfs == NULL) {
        fprintf(ERRSTREAM, "Error: unsupported byte exponent input layout.\n");
        exit(EXIT_FAILURE);
    }
    uint8_t domains[127] = {0};
    int64_t offset = 0;
    for (int32_t g=0; g<ng; ++g) {
        const int32_t len=lens[g];
        if (len < 1 || offset > INT32_MAX-len) {
            fprintf(ERRSTREAM, "Error: unsupported byte exponent term count.\n");
            exit(EXIT_FAILURE);
        }
        int domain_var=-1, kind[2]={0,0}, has_high=0;
        for (int32_t t=0; t<len; ++t) {
            int nz=0, var=-1, exponent=0;
            uint32_t degree=0;
            for (int32_t v=0; v<nv; ++v) {
                const int32_t e=exps[(offset+t)*(int64_t)nv+v];
                if (e < 0 || e > UINT8_MAX) {
                    fprintf(ERRSTREAM, "Error: input exponent outside byte range.\n");
                    exit(EXIT_FAILURE);
                }
                degree+=(uint32_t)e;
                if (e>2) has_high=1;
                if (e) {nz++;var=v;exponent=e;}
            }
            if (degree>UINT8_MAX) {
                fprintf(ERRSTREAM, "Error: input total degree outside byte range.\n");
                exit(EXIT_FAILURE);
            }
            if (len==2 && nz==1 && (exponent==1 || exponent==3)) {
                if (domain_var==-1) domain_var=var;
                if (domain_var==var) kind[t]=exponent;
            }
        }
        int is_domain=0;
        if (len==2 && domain_var>=0 && ((kind[0]==1 && kind[1]==3) ||
                (kind[0]==3 && kind[1]==1))) {
            const int a=(cfs[offset]%3+3)%3, b=(cfs[offset+1]%3+3)%3;
            is_domain=(a!=0 && (a+b)%3==0);
        }
        if (has_high && !is_domain) {
            fprintf(ERRSTREAM, "Error: non-domain input monomial is not field-reduced.\n");
            exit(EXIT_FAILURE);
        }
        if (is_domain) domains[domain_var]=1;
        offset+=len;
    }
    for (int32_t v=0; v<nv; ++v) if (!domains[v]) {
        fprintf(ERRSTREAM, "Error: missing explicit x_i^3-x_i field domain.\n");
        exit(EXIT_FAILURE);
    }
}

'''
assert marker in s;s=s.replace(marker,guard+marker,1)
marker='    bs_t *bs    = *bsp;'
gate=r'''    if (field_char != 3 || mon_order != 0 || elim_block_len != 0 ||
            nr_threads != 1 || la_option != 2 || use_signatures != 0 ||
            nr_nf != 0 || truncate_lifting != 0 || reduce_gb != 1) {
        fprintf(ERRSTREAM, "Error: unsupported mode in byte exponent build.\n");
        exit(EXIT_FAILURE);
    }
    checked_byte_model(lens, exps, (const int32_t *)cfs, nr_vars, nr_gens);

'''
s=s.replace(marker,gate+marker,1)
marker='    return core_f4(bs, md, errp, fc);'
s=s.replace(marker,r'''    if (fc != 3 || md->fc != 3 || md->mo != 0 || md->nev != 0 ||
            md->nthrds != 1 || md->laopt != 2 || md->use_signatures != 0 ||
            md->nf != 0 || md->trace_level != NO_TRACER ||
            (md->print_gb != 1 && md->print_gb != 2)) {
        fprintf(ERRSTREAM, "Error: unsupported core mode in byte exponent build.\n");
        exit(EXIT_FAILURE);
    }
'''+marker,1)
(S/paths[4]).write_text(s)
s=before[paths[5]].replace('#include "libmsolve.c"','#include "libmsolve.c"\n#include "byte_input_guard.h"',1)
marker='    switch(opt) {'
s=s.replace(marker,r'''    if (opt != 'f' && opt != 'o' && opt != 'g' && opt != 'l' &&
            opt != 't' && opt != 'r' && opt != 'c' && opt != 's' &&
            opt != 'm' && opt != 'u' && opt != 'v' && opt != 'h' && opt != 'V') {
        byte_input_error("unsupported command-line option");
    }
    if (opt != 'f' && opt != 'o' && opt != 'h' && opt != 'V') {
        byte_cli_integer(optarg);
    }
'''+marker,1)
marker='    /* srand initialization */'
s=s.replace(marker,r'''    if (la_option != 2 || nr_threads != 1 || reduce_gb != 1 ||
            (print_gb != 1 && print_gb != 2) || genericity_handling != 0 ||
            initial_hts < 4 || initial_hts > 26 || info_level < 0 || info_level > 2 ||
            files->in_file == NULL || files->bin_file != NULL ||
            files->bin_out_file != NULL) {
        byte_input_error("unsupported command-line mode");
    }
    /* Validate raw tokens before the upstream parser can narrow strtol. */
    byte_validate_file(files->in_file);

'''+marker,1)
(S/paths[5]).write_text(s)
header=(R/'byte_input_guard.h').read_text();(S/'src/msolve/byte_input_guard.h').write_text(header)
patch=''.join(''.join(difflib.unified_diff(before[p].splitlines(True),(S/p).read_text().splitlines(True),fromfile='a/'+p,tofile='b/'+p)) for p in paths)
patch+=''.join(difflib.unified_diff([],header.splitlines(True),fromfile='/dev/null',tofile='b/src/msolve/byte_input_guard.h'))
(R/'checked-byte-exponents.patch').write_text(patch)
metadata={k:base[k] for k in ['repository','tag','commit','archive_sha256','source_archive','build_environment','build_commands','runtime_library_sha256','compiler_version']}
metadata.update(source_directory=str(S),predecessor_patches=patches,baseline_executable=str(B/'msolve'),baseline_executable_sha256=base['executable_sha256'],modified_source_sha256={p:hashlib.sha256((S/p).read_bytes()).hexdigest() for p in paths+['src/msolve/byte_input_guard.h']},checked_byte_patch_sha256=hashlib.sha256(patch.encode()).hexdigest())
(R/'source.json').write_text(json.dumps(metadata,indent=2)+'\n');print(metadata['checked_byte_patch_sha256'])

subprocess.run(["python3",str(R/"finish_scope_fix.py")],check=True)
