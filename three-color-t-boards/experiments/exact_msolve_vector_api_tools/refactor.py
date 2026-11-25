#!/usr/bin/env python3
"""Build the reviewable API patch from immutable eighth source bytes."""

import json
import shutil
from pathlib import Path

R = Path(__file__).resolve().parent
M = json.loads((R / "source.json").read_text())
S = Path(M["source_directory"])
B = Path(
    json.loads((R.parent / "exact_msolve_byte_exponent_tools/source.json").read_text())[
        "source_directory"
    ]
)
for p in (B / "src").rglob("*"):
    if p.is_file() and p.suffix in (".c", ".h") and p.name != "msolve-version.h":
        destination = S / p.relative_to(B)
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(p, destination)


def mutate(path, fn):
    p = S / path
    p.write_text(fn((B / path).read_text()))


def data(s):
    s = s.replace(
        "typedef int32_t deg_t;", '#include "stored_exp.h"\n\ntypedef int32_t deg_t;', 1
    )
    return s.replace(
        "exp_t **ev;   /* exponent vector */",
        "stored_exp_t **ev; /* stored byte vectors, never dense exp_t scratch */\n    size_t evbytes; /* physical bytes per stored vector; evl stays logical */",
    )


mutate("src/neogb/data.h", data)
shutil.copy2(R / "stored_exp.h", S / "src/neogb/stored_exp.h")


def io(s):
    s = s.replace(
        "exp_t *e  = ht->ev[0]; /* use as temporary storage */",
        "exp_t e[ht->evl]; /* dense scratch independent of stored-table realloc */",
    )
    return s.replace(
        "                e  = ht->ev[0]; /* reset e if enlarging */",
        "                /* dense scratch remains valid across table growth */",
    )


mutate("src/neogb/io.c", io)


def hash_first(s):
    # Persistent layout is type-separated. Values remain byte-for-byte identical.
    s = s.replace(
        "ht->rn  = calloc",
        "ht->evbytes = stored_exp_bytes(ht->evl);\n    ht->rn  = calloc",
        1,
    )
    s = s.replace(
        "ht->evl   = bht->evl;",
        "ht->evl   = bht->evl;\n    ht->evbytes = bht->evbytes;",
    )
    s = s.replace("(exp_t **)", "(stored_exp_t **)").replace(
        "sizeof(exp_t *)", "sizeof(stored_exp_t *)"
    )
    s = s.replace("exp_t **ev  = ht->ev", "stored_exp_t **ev  = ht->ev")
    s = s.replace("exp_t **oev  = ht->ev", "stored_exp_t **oev  = ht->ev")
    s = s.replace("exp_t **new_ev =", "stored_exp_t **new_ev =")
    s = s.replace(
        "exp_t *tmp  = (exp_t *)malloc(", "stored_exp_t *tmp  = (stored_exp_t *)malloc("
    )
    s = s.replace("exp_t *old_block = ht->ev[0]", "stored_exp_t *old_block = ht->ev[0]")
    s = s.replace("exp_t *new_block = realloc", "stored_exp_t *new_block = realloc")
    s = s.replace(
        "static exp_t *stage_missing_symbolic_exponents",
        "static stored_exp_t *stage_missing_symbolic_exponents",
    )
    s = s.replace("exp_t *block = sht->ev[0]", "stored_exp_t *block = sht->ev[0]")
    s = s.replace("exp_t *staged = realloc", "stored_exp_t *staged = realloc")
    s = s.replace(
        "exp_t *fresh = symbolic_stage_calloc",
        "stored_exp_t *fresh = symbolic_stage_calloc",
    )
    s = s.replace("exp_t *staged = NULL", "stored_exp_t *staged = NULL")
    # All source strides below will be separately audited; byte values don't change.
    s = s.replace(
        "(unsigned long)ht->evl * ht->esz * sizeof(exp_t)", "ht->evbytes * ht->esz"
    )
    s = s.replace("(j*ht->evl)", "(j*ht->evbytes)")
    s = s.replace("esz * (unsigned long)ht->evl * sizeof(exp_t)", "esz * ht->evbytes")
    s = s.replace("(i*ht->evl)", "(i*ht->evbytes)")
    s = s.replace("esz * (unsigned long)evl * sizeof(exp_t)", "esz * ht->evbytes")
    s = s.replace("(i*evl)", "(i*ht->evbytes)")
    s = s.replace("(unsigned long)evl * esz * sizeof(exp_t)", "ht->evbytes * esz")
    s = s.replace("tmp + k*evl", "tmp + k*ht->evbytes")
    s = s.replace(
        "(size_t)new_esz*(size_t)ht->evl*sizeof(exp_t)", "(size_t)new_esz*ht->evbytes"
    )
    s = s.replace("new_block + i*ht->evl", "new_block + i*ht->evbytes")
    s = s.replace(
        "const size_t vector_bytes = (size_t)sht->evl*sizeof(exp_t);",
        "const size_t vector_bytes = sht->evbytes;",
    )
    s = s.replace("block+id*sht->evl", "block+id*sht->evbytes").replace(
        "block+packed*sht->evl", "block+packed*sht->evbytes"
    )
    s = s.replace("fresh+id*sht->evl", "fresh+id*sht->evbytes")
    return s.replace(
        "staged+(size_t)symbolic_hash*bht->evl",
        "staged+(size_t)symbolic_hash*bht->evbytes",
    )


mutate("src/neogb/hash.c", hash_first)
mutate(
    "src/neogb/symbol.c",
    lambda s: s.replace("exp_t *elcm, *eb;", "exp_t *elcm; exp_t *eb;"),
)

print("initial type separation written; semantic access conversion follows")
