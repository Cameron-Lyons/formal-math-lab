#!/usr/bin/env bash
# Rebuild witness data from a nauty 2.9.3 source tree with configure completed.
set -euo pipefail
if (( $# != 1 )); then
    echo "usage: $0 /path/to/configured/nauty2_9_3" >&2
    exit 2
fi
nauty_src=$(realpath "$1")
tool_dir=$(cd -- "$(dirname -- "$0")" && pwd)
project_dir=$(realpath "$tool_dir/../..")
output_dir="$project_dir/.lake/cert16-generation"
mkdir -p "$output_dir"
(
    cd "$nauty_src"
    make geng
    objects=(gtoolsW.o nautyW1.o nautilW1.o naugraphW1.o schreierW.o naurng.o)
    cc -std=c23 -O3 -mpopcnt -DMAXN=WORDSIZE -DWORDSIZE=32 "-DPLUGIN=\"$tool_dir/c9prune.h\"" \
       geng.c "${objects[@]}" -o "$output_dir/densegeng"
    c++ -std=c++23 -O3 -Wall -Wextra -Wpedantic -Werror -mpopcnt -DMAXN=WORDSIZE -DWORDSIZE=32 -isystem . \
       "$tool_dir/witnesses.cpp" "${objects[@]}" -o "$output_dir/witnesses"
)
for n in {1..16}; do
    "$output_dir/densegeng" "$n" "$output_dir/graphs$n.g6"
done
"$output_dir/witnesses" "$output_dir" "$output_dir"
python3 -B "$tool_dir/tables.py" "$output_dir" "$project_dir/Ramsey556/Cert16/Tables.lean"
python3 -B "$tool_dir/rows.py" "$output_dir" "$project_dir/Ramsey556/Cert16"
