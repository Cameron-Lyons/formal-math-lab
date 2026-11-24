#!/bin/sh
# Write the part modules NAME/Part/Pk.lean and their summary NAME/Parts.lean for the N lists of
# cubes in NAME/Cases.lean.  The files differ only in the index k.  NAME is E670 unless given;
# a project that builds on this one passes the name of its own library.
#
#   usage: scripts/parts.sh N [NAME]
set -e
n=$1
name=${2:-E670}
rm -rf "$name/Part"
mkdir -p "$name/Part"
for k in $(seq 0 $((n - 1))); do
  printf 'import %s.Cases\n\ntheorem %s.part%d : Refutes formula parts[%d]! := by refute\n' "$name" "$name" "$k" "$k" > "$name/Part/P$k.lean"
done
{
  for k in $(seq 0 $((n - 1))); do echo "import $name.Part.P$k"; done
  printf '\n/-- Every list of cubes in `parts` is refuted. -/\ntheorem %s.parts_refuted : ∀ k < %d, Refutes formula parts[k]!\n' "$name" "$n"
  for k in $(seq 0 $((n - 1))); do echo "  | $k, _ => part$k"; done
  printf '  | _ + %d, h => absurd h (by omega)\n' "$n"
} > "$name/Parts.lean"
