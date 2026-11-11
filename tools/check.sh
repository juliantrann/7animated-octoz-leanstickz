#!/usr/bin/env bash
# Checks the theorems of checks/ID (PLAN.md §8, G0 CI) the way Zellic's checks/*/verify-source.sh does:
#   1. Lean 4.34.0 builds the challenge (the theorems stated by `sorry`) and the solution (the same theorems proved);
#   2. lean4export (refs/lean4export, tag v4.34.0) exports each, with the constants `lake comparator` requires;
#   3. Lean 4.35.0's `lake comparator`, configured by checks/ID/comparator.json, checks that the solution proves the
#      challenge's theorems over the same constants, with no axiom but the permitted ones, and replays the solution in
#      Lean's kernel and in the independent kernels the toolchain ships (con-leche, con-ron, nanoda).
# It ends with "Your solution is okay!" and exit status 0 if it accepts.
# Usage: tools/check.sh ID [comparator options...]     e.g. tools/check.sh sections
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
id=$1; shift
here="$root/checks/$id"; config="$here/comparator.json"
exporter="$root/refs/lean4export/.lake/build/bin/lean4export"
read -r chal sol thms < <(python3 -I -c 'import json,sys; c=json.load(open(sys.argv[1]))
print(c["challenge_module"], c["solution_module"], " ".join(c["theorem_names"]))' "$config")
work=$(mktemp -d "$here/.check.XXXXXX"); trap 'rm -rf -- "$work"' EXIT
PATH="$(elan run leanprover/lean4:v4.35.0 lean --print-prefix)/bin:$PATH"
base="Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft
  Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam
  outParam propext Quot.sound Classical.choice"
cd "$root/lean"
echo "== 1. building $chal (its warnings \"declaration uses \`sorry\`\" are expected) and $sol"
elan run leanprover/lean4:v4.34.0 lake build "$chal" "$sol" 2>&1 | grep -v '^✔' || true
echo "== 2. exporting"
# shellcheck disable=SC2086
elan run leanprover/lean4:v4.34.0 lake env "$exporter" "$chal" -- $thms $base > "$work/challenge.ndjson"
# shellcheck disable=SC2086
elan run leanprover/lean4:v4.34.0 lake env "$exporter" "$sol" -- $thms $base > "$work/solution.ndjson"
ls -la "$work"/*.ndjson | awk '{print "   ", $5, $NF}'
echo "== 3. lake comparator"
cd "$here"
elan run leanprover/lean4:v4.35.0 lake comparator --config "$config" "$@" \
  --challenge-from-export "$work/challenge.ndjson" --solution-from-export "$work/solution.ndjson"
