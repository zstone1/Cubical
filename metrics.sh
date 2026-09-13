#!/usr/bin/env bash
# Debloat metrics: line count and concept count, tree-wide and per area.
# Baseline at da3f467: 58881 lines, 1962 defs, 3230 theorems.
set -u
DEFRE='^((noncomputable|private|protected|partial|unsafe|scoped|local) )*(def|abbrev|structure|inductive|class) '
files=$(find CubeChains -name '*.lean')
printf 'at %s\n' "$(git rev-parse --short HEAD)"
printf '%7d  lines    (baseline 58881)\n' "$(cat $files CubeChains.lean | wc -l)"
printf '%7d  defs     (baseline  1962)\n' "$(grep -rhE "$DEFRE" $files CubeChains.lean | wc -l)"
printf '%7d  theorems (baseline  3230)\n' "$(grep -rhE '^((private|protected|nonrec) )*theorem ' $files | wc -l)"
echo
printf '%6s %5s  %s\n' lines defs area
for d in Concurrency/Presentation Machinery/Presentation Concurrency/Grading \
         Concurrency/Merge Foundations/Polygraph Machinery/Braid \
         Precubical/Basic Precubical/Chains Precubical/Segal Precubical/Wedge \
         Concurrency/Salvetti Concurrency/Complexification Concurrency/Executions \
         Machinery/Localization Machinery/Cube Machinery/Arrangement \
         Machinery/Rewriting Testing/Enumerate Testing/H; do
  [ -d "CubeChains/$d" ] || continue
  printf '%6d %5d  %s\n' \
    "$(cat CubeChains/$d/*.lean 2>/dev/null | wc -l)" \
    "$(grep -hE "$DEFRE" CubeChains/$d/*.lean 2>/dev/null | wc -l)" "$d"
done
