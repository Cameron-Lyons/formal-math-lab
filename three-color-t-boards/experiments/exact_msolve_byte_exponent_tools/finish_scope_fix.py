#!/usr/bin/env python3
from pathlib import Path
import json,difflib,hashlib
R=Path(__file__).resolve().parent;B=R.parent/'exact_msolve_symbolic_reserve_tools';S=R/'msolve-cc044551f8e202d00691990fd3fd0b1226a88ea2';BS=B/S.name
p=S/'src/neogb/engine.c';s=p.read_text();a=s.index('/* Initial field domains certify');b=s.index('int initialize_gba_input_data(',a);guard=s[a:b]
(S/'src/neogb/byte_model_guard.h').write_text('#ifndef MSOLVE_BYTE_MODEL_GUARD_H\n#define MSOLVE_BYTE_MODEL_GUARD_H\n'+guard+'#endif\n')
s=s[:a]+s[b:];s=s.replace('#include "../msolve/streams.h"','#include "../msolve/streams.h"\n#include "byte_model_guard.h"',1);p.write_text(s)
p=S/'src/neogb/io.c';s=p.read_text().replace('#include "../msolve/streams.h"','#include "../msolve/streams.h"\n#include "byte_model_guard.h"',1)
a=s.index('void import_input_data(');b=s.index('    int32_t i, j;',a)
s=s[:b]+r'''    if (st == NULL || bs == NULL || bs->ht == NULL || st->fc != 3 ||
            st->mo != 0 || st->nev != 0 || st->nthrds != 1 ||
            st->laopt != 2 || st->use_signatures != 0 || st->nf != 0 ||
            st->trace_level != NO_TRACER || start != 0 || stop != st->ngens_input) {
        fprintf(ERRSTREAM, "Error: unsupported import mode in byte exponent build.\n");
        exit(EXIT_FAILURE);
    }
    checked_byte_model(lens, exps, (const int32_t *)vcfs, bs->ht->nv, stop);

'''+s[b:];p.write_text(s)
p=S/'src/msolve/main.c';s=p.read_text().replace('#include "byte_input_guard.h"','#include "byte_input_guard.h"\n#include "../neogb/byte_model_guard.h"',1)
needle='    get_data_from_file(files->in_file, &nr_vars, &field_char, &nr_gens, gens);'
s=s.replace(needle,needle+'\n    checked_byte_model(gens->lens, gens->exps, gens->cfs, nr_vars, nr_gens);',1);p.write_text(s)
paths=['src/neogb/data.h','src/neogb/io.c','src/neogb/hash.c','src/neogb/symbol.c','src/neogb/engine.c','src/msolve/main.c','src/msolve/byte_input_guard.h','src/neogb/byte_model_guard.h']
patch=''
for f in paths:
 old=(BS/f).read_text() if (BS/f).exists() else ''
 patch+=''.join(difflib.unified_diff(old.splitlines(True),(S/f).read_text().splitlines(True),fromfile='a/'+f if old else '/dev/null',tofile='b/'+f))
(R/'checked-byte-exponents.patch').write_text(patch)
p=R/'source.json';m=json.loads(p.read_text());m['modified_source_sha256']={f:hashlib.sha256((S/f).read_bytes()).hexdigest() for f in paths};m['checked_byte_patch_sha256']=hashlib.sha256(patch.encode()).hexdigest();m['rejected_attempts']=[{'directory':'rejected_attempt1','reason':'model guard bypass on prime CLI initialization; fixed in common import and parsed CLI model'}]
p.write_text(json.dumps(m,indent=2)+'\n');print(m['checked_byte_patch_sha256'])
