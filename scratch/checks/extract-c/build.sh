#!/usr/bin/env bash
# Extract a standalone C implementation of garbled circuits from the Lean development.
#
# Lean's code generator already emits C for every module on each `lake build`
# (.lake/build/ir/**/*.c).  This script compiles the emitted C and links a native binary
# that garbles and evaluates circuits over ChaCha20, with no Lean and no Mathlib at run time.
#
# Usage:  lake build && bash scratch/checks/extract-c/build.sh [outdir]
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
OUT="${1:-$ROOT/.lake/extract-c}"
INC="$(lake env lean --print-prefix)/include"
mkdir -p "$OUT/obj"
cd "$ROOT"

echo "== emitting C for the driver =="
lake env lean -c "$OUT/GarbleMain.c" scratch/checks/GarbleMain.lean

echo "== compiling emitted C (project modules only; the other root is a name-for-name twin) =="
: > "$OUT/objs.txt"
for c in $(find .lake/build/ir -name '*.c' | grep -v SymbolicGarbledCircuitsInLean); do
  # skip stale C from modules that no longer exist
  [ -f "${c#.lake/build/ir/}" ] || [ -f "$(echo "$c" | sed 's|\.lake/build/ir/||; s|\.c$|.lean|')" ] || continue
  o="$OUT/obj/$(echo "$c" | tr '/' '_' | sed 's/\.c$/.o/')"
  gcc -O1 -ffunction-sections -fdata-sections -I"$INC" -c "$c" -o "$o"
  echo "$o" >> "$OUT/objs.txt"
done
gcc -O1 -ffunction-sections -fdata-sections -I"$INC" -c "$OUT/GarbleMain.c" -o "$OUT/obj/GarbleMain.o"
echo "$OUT/obj/GarbleMain.o" >> "$OUT/objs.txt"

echo "== first link: discover what is still referenced =="
# --gc-sections drops everything unreachable from `main`.  What remains undefined is the
# measurement: if any Mathlib *code* were reachable it would show up here.
leanc @"$OUT/objs.txt" -o "$OUT/garble" -Wl,--gc-sections -Wl,--error-limit=0 > "$OUT/link1.log" 2>&1 || true
grep -oE 'undefined symbol: [A-Za-z0-9_]+' "$OUT/link1.log" | sed 's/undefined symbol: //' \
  | sort -u > "$OUT/undefined.txt" || true
echo "   undefined after --gc-sections: $(wc -l < "$OUT/undefined.txt") symbols"
if grep -qv '^initialize_' "$OUT/undefined.txt" 2>/dev/null; then
  echo "   !! something other than a module initialiser is referenced:"
  grep -v '^initialize_' "$OUT/undefined.txt"
  exit 1
fi

echo "== stubbing the Mathlib module initialisers =="
# Sound only because the check above passed: no Mathlib code or data is reachable, so these
# initialisers have nothing to initialise that this binary can observe.
{ echo '#include <lean/lean.h>'
  while read -r s; do
    printf 'LEAN_EXPORT lean_object* %s(uint8_t b, lean_object* w) { (void)b; (void)w; return lean_io_result_mk_ok(lean_box(0)); }\n' "$s"
  done < "$OUT/undefined.txt"
} > "$OUT/stubs.c"
gcc -O1 -ffunction-sections -I"$INC" -c "$OUT/stubs.c" -o "$OUT/obj/stubs.o"
echo "$OUT/obj/stubs.o" >> "$OUT/objs.txt"

echo "== final link =="
leanc @"$OUT/objs.txt" -o "$OUT/garble" -Wl,--gc-sections
strip "$OUT/garble" || true
ls -la "$OUT/garble"
echo "== run =="
"$OUT/garble"
