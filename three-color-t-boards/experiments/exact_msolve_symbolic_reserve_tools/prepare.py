#!/usr/bin/env python3
"""Reconstruct the seventh build from pinned source and prior patches."""

import difflib
import hashlib
import json
import subprocess
import tarfile
from pathlib import Path

R = Path(__file__).resolve().parent
E = R.parent
B = E / "exact_msolve_staged_f3_tools"
base = json.loads((B / "source.json").read_text())
S = R / Path(base["source_directory"]).name
assert not S.exists(), "refusing to overwrite source"
with tarfile.open(base["source_archive"]) as t:
    t.extractall(R, filter="data")
patches = base["predecessor_patches"] + [
    {
        "path": str(B / "enable-f3-staging.patch"),
        "sha256": base["enable_f3_patch_sha256"],
    }
]
for item in patches:
    p = Path(item["path"])
    assert hashlib.sha256(p.read_bytes()).hexdigest() == item["sha256"]
    subprocess.run(
        ["patch", "-p1", "-i", str(p)], cwd=S, check=True, capture_output=True
    )
paths = ["src/neogb/hash.c", "src/neogb/symbol.c"]
before = {p: (S / p).read_text() for p in paths}
s = before[paths[0]]
s = s.replace(
    "/* Keep exponent capacity independent from power-of-two probing buckets.\n * This helper is used only by the guarded ordinary F4 promotion path. */\nstatic void reserve_basis_hash_table_for_promotion(",
    """/* Keep exponent capacity independent from power-of-two probing buckets.
 * Shared checked allocator for the guarded promotion and symbolic paths. */
static void reserve_hash_table_checked(""",
    1,
)
s = s.replace(
    "    const hl_t additional,\n    const int info_level\n    )\n{\n    const hl_t quantum = (hl_t)1 << 16;",
    """    const hl_t additional,
    const hl_t quantum,
    const int info_level,
    const char *context
    )
{""",
    1,
)
s = s.replace(
    "    if (ht == NULL || ht->esz == 0 || ht->esz > max_entries ||",
    """    if (quantum == 0 || quantum > ((hl_t)1 << 16) ||
            (quantum & (quantum-1)) != 0 || context == NULL ||
            ht == NULL || ht->esz == 0 || ht->esz > max_entries ||""",
    1,
)
s = s.replace(
    "MSOLVE_PROMOTION_CAPACITY_REQUEST required_with_spare=%lu",
    "MSOLVE_%s_CAPACITY_REQUEST required_with_spare=%lu",
    1,
)
s = s.replace(
    "(unsigned long)required, (unsigned long)ht->esz,",
    "context, (unsigned long)required, (unsigned long)ht->esz,",
    1,
)
marker = (
    "/* Private allocations only: rn/dv/dm remain borrowed from the basis table. */"
)
wrapper = r"""static void reserve_basis_hash_table_for_promotion(
        ht_t *ht, const hl_t additional, const int info_level)
{
    reserve_hash_table_checked(ht, additional, (hl_t)1 << 16,
            info_level, "PROMOTION");
}

/* Reserve a translated source row before the unchanged constructor.
 * Each source term inserts at most one symbolic monomial. With one spare,
 * eld+LENGTH+1 slots make the constructor's legacy growth loop a no-op.
 * No symbolic exponent-data pointer may be used after this call. */
static void reserve_symbolic_row_capacity(
        ht_t *sht, const hm_t *poly, const md_t *md)
{
    if (md == NULL) {
        fprintf(ERRSTREAM, "Error: missing metadata in symbolic row reserve.\n");
        exit(EXIT_FAILURE);
    }
    if (!((md->fc == 2 || md->fc == 3) && md->laopt == 2 &&
            md->nthrds == 1 && md->trace_level == NO_TRACER &&
            md->nf == 0 && md->in_final_reduction_step == 0 &&
            md->nev == 0 && md->print_gb > 0)) {
        return;
    }
    const hl_t max_entries = (hl_t)1 << 30;
    if (sht == NULL || md->ht != sht || poly == NULL ||
            sht->eld == 0 || sht->eld >= max_entries ||
            (hl_t)poly[LENGTH] > max_entries-1-sht->eld) {
        fprintf(ERRSTREAM, "Error: invalid symbolic row reservation.\n");
        exit(EXIT_FAILURE);
    }
    const hl_t required = sht->eld+(hl_t)poly[LENGTH]+1;
    if (required <= sht->esz) {
        return;
    }
    /* Geometric growth for small tables; 64K rounding above that scale. */
    hl_t quantum = 2;
    while (quantum < required && quantum < ((hl_t)1 << 16)) {
        quantum *= 2;
    }
    const hl_t requested = ((required+quantum-1)/quantum)*quantum;
    if (md->info_level > 1) {
        fprintf(VERBSTREAM, "\nMSOLVE_SYMBOLIC_ROW_RESERVE old_load=%lu row_length=%lu required_with_spare=%lu requested_capacity=%lu\n",
                (unsigned long)sht->eld, (unsigned long)poly[LENGTH],
                (unsigned long)required, (unsigned long)requested);
        fflush(VERBSTREAM);
    }
    reserve_hash_table_checked(sht, (hl_t)poly[LENGTH], quantum,
            md->info_level, "SYMBOLIC");
}

"""
assert marker in s
s = s.replace(marker, wrapper + marker, 1)
s = s.replace(
    "            (sht->esz & (sht->esz-1)) != 0 ||\n            sht->eld !=",
    """            /* Large non-power capacities restore to power-of-two 2048. */
            (sht->esz < 2048 && (sht->esz & (sht->esz-1)) != 0) ||
            sht->eld !=""",
    1,
)
s = s.replace(
    "            sht->hsz < sht->eld || sht->hsz > SIZE_MAX/sizeof(hi_t) ||",
    """            sht->hsz < sht->eld || sht->hsz > SIZE_MAX/sizeof(hi_t) ||
            sht->hsz == 0 || (sht->hsz & (sht->hsz-1)) != 0 ||
            sht->esz > sht->hsz/2 ||""",
    1,
)
(S / paths[0]).write_text(s)
s = before[paths[1]]
split = s.index("static int32_t select_spairs_by_minimal_degree(")
head, s = s[:split], s[split:]
for old in [
    "        rrows[nrr]  = multiplied_poly_to_matrix_row(sht, bht, h, etmp, b);",
    "            trows[ntr] = multiplied_poly_to_matrix_row(sht, bht, h, etmp, b);",
    "        rows[rr]  = multiplied_poly_to_matrix_row(sht, bht, h, etmp, b);",
]:
    assert s.count(old) == 1
    indent = old[: len(old) - len(old.lstrip())]
    s = s.replace(old, indent + "reserve_symbolic_row_capacity(sht, b, md);\n" + old, 1)
(S / paths[1]).write_text(head + s)
patch = "".join(
    "".join(
        difflib.unified_diff(
            before[p].splitlines(True),
            (S / p).read_text().splitlines(True),
            fromfile="a/" + p,
            tofile="b/" + p,
        )
    )
    for p in paths
)
(R / "symbolic-row-reserve.patch").write_text(patch)
metadata = {
    k: base[k]
    for k in [
        "repository",
        "tag",
        "commit",
        "archive_sha256",
        "source_archive",
        "build_environment",
        "build_commands",
        "runtime_library_sha256",
        "compiler_version",
    ]
}
metadata.update(
    source_directory=str(S),
    predecessor_patches=patches,
    baseline_executable=str(B / "msolve"),
    baseline_executable_sha256=base["executable_sha256"],
    modified_source_sha256={
        p: hashlib.sha256((S / p).read_bytes()).hexdigest() for p in paths
    },
    symbolic_reserve_patch_sha256=hashlib.sha256(patch.encode()).hexdigest(),
)
(R / "source.json").write_text(json.dumps(metadata, indent=2) + "\n")
print(json.dumps(metadata["modified_source_sha256"], indent=2))
