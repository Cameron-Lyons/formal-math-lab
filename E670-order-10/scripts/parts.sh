#!/bin/sh
# Write the part modules E670/Part/Pk.lean and their summary E670/Parts.lean for the N lists of
# cubes in E670/Cases.lean.  The files differ only in the index k.
#
#   usage: scripts/parts.sh N
set -e
n=$1
rm -rf E670/Part
mkdir -p E670/Part
for k in $(seq 0 $((n - 1))); do
  printf 'import E670.Cases\n\ntheorem E670.part%d : Refutes formula parts[%d]! := by refute\n' "$k" "$k" > "E670/Part/P$k.lean"
done
{
  for k in $(seq 0 $((n - 1))); do echo "import E670.Part.P$k"; done
  printf '\n/-- Every list of cubes in `parts` is refuted. -/\ntheorem E670.parts_refuted : ∀ k < %d, Refutes formula parts[k]!\n' "$n"
  for k in $(seq 0 $((n - 1))); do echo "  | $k, _ => part$k"; done
  printf '  | _ + %d, h => absurd h (by omega)\n' "$n"
} > E670/Parts.lean
