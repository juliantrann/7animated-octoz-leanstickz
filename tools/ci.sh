#!/usr/bin/env bash
# The project's checks, run by .github/workflows/b.yml (in parallel jobs) and by hand; exit status 0 iff all pass.
# Run tools/setup.sh first (once). Steps:
#   pins       refs/zellic-x86 = pinned commit + patches/zellic-x86.patch; the other sources at their commits;
#              release/26.06/7zz, 7zzs with the pinned SHA-256
#   build      Zellic's default targets; this project's FV7z, Challenges and tools
#   axioms     every checks/*/comparator.json permits no axiom but propext, Quot.sound, Classical.choice
#   proofs     tools/check.sh ID accepts every checks/ID, and rejects every checks/neg-*: a solution that is the
#              challenge itself, with `sorry` (that the checker can say no)
#   g0         tools/g0.sh: decoder lengths equal objdump's on every instruction; the coverage counts no higher than
#              ci/baseline.txt; CODEMAP.md as kept (when the checkout has it)
#   difftest   tools/difftest/run.py: the model's instruction semantics against this processor, 0 mismatches
#   x87        tools/fcwprobe: FCW and FSW after each x87 state load as Profile.x87LoadsKnown says (Intel)
#   xsave      tools/xsavetest/run.py: the model's XSAVE, XSAVEC and XRSTOR against this processor, 0 mismatches
#              (difftest and xsave draw their cases from the seed $TEST_SEED, 1 when unset)
#   systest    tools/systest/run.py: the model's G1 system calls against this kernel, 0 mismatches
#   systrace   tools/systrace.sh: no thread under the single-threaded flags (PLAN.md §5, option (a))
#   min        tools/mintrace.sh: under qemu-user's baseline processor the same commands translate none of the
#              instructions with an issue under the feature set `min` (H-CPU-min); needs g0's outputs
#   dispatch   tools/dispatch.py: every variant a glibc IFUNC resolver picks needs no feature its choice does not
#              guarantee (featneed: per function, the features whose absence faults); needs g0's outputs
# Usage: tools/ci.sh [STEP...]          (no STEP: all of them, in this order; logs in $CI_LOG_DIR, else a new /tmp dir)
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd); cd "$root"
log=${CI_LOG_DIR:-$(mktemp -d "${TMPDIR:-/tmp}/fv7z-ci.XXXXXX")}; mkdir -p "$log"; log=$(cd "$log" && pwd)
steps=("$@"); [ ${#steps[@]} = 0 ] && steps=(pins build axioms proofs g0 difftest x87 xsave systest systrace min dispatch)
declare -A result
echo "machine: $(nproc) CPUs, $(awk '/MemTotal/ {printf "%.1f", $2/1048576}' /proc/meminfo) GiB RAM, $(df -h --output=avail . | tail -1 | tr -d ' ') disk free"

step_pins() {
  tools/zellic_patch.sh check &&
  [ "$(git -C refs/lean4export rev-parse HEAD)" = 076e8e57707e813375e8f9da8bf989799ace9680 ] &&
  [ "$(git -C upstream/7zip rev-parse HEAD)" = d3296e39e1f1f92c7b41c0c3848e65640428d42d ] &&
  (cd release/26.06 && sha256sum -c "$root/pins/release-26.06.sha256")
}
step_build() {
  # the kernel check of Im5.L* recurses deep (a95) on the main thread (Elab.async false): a finite 1 GB stack, since
  # with `unlimited` lean takes its 8 MB default for the main thread (`--tstack` is for the other threads)
  ulimit -s 1048576 2>/dev/null || ulimit -s unlimited 2>/dev/null || true
  (cd refs/zellic-x86 && lake build 2>&1 | grep -E 'error|warning: declaration uses .sorry.|Build completed'; exit "${PIPESTATUS[0]}") &&
  (cd lean && for h in $(grep -v '^\s*#' heavy-targets | xargs); do
     lake build "$h" 2>&1 | grep -E 'error|Build completed'; [ "${PIPESTATUS[0]}" = 0 ] || exit 1; done) &&
  (cd lean && lake build FV7z Challenges insncov featneed difftest systest xsavetest 2>&1 | grep -E 'error|Build completed'; exit "${PIPESTATUS[0]}")
}
step_axioms() {
  python3 -I - checks <<'PY'
import json, pathlib, sys
ok = {"propext", "Quot.sound", "Classical.choice"}
bad = 0
for c in sorted(pathlib.Path(sys.argv[1]).glob("*/comparator.json")):
    a = set(json.load(open(c))["permitted_axioms"])
    print(f"{c.parent.name}: {sorted(a)}")
    if not a <= ok: print(f"FAIL: {c} permits {sorted(a - ok)}"); bad = 1
sys.exit(bad)
PY
}
step_proofs() {
  # CHECK_SHARD=K/N: only every N-th check, starting at the K-th (the checks spread over N parallel jobs)
  local rc=0 id i=0 shard=${CHECK_SHARD:-1/1}
  for d in checks/*/; do
    id=$(basename "$d")
    i=$((i + 1)); [ $(( (i - 1) % ${shard#*/} + 1 )) = "${shard%/*}" ] || continue
    if tools/check.sh "$id" > "$log/check.$id" 2>&1 && grep -q 'Your solution is okay!' "$log/check.$id"; then
      if [[ $id == neg-* ]]; then echo "FAIL: $id accepted"; rc=1; else echo "ok: $id accepted"; fi
    else
      if [[ $id == neg-* ]]; then echo "ok: $id rejected ($(grep -m1 -o 'Illegal axiom[^.]*' "$log/check.$id" || echo 'rejected'))"
      else echo "FAIL: $id rejected (log: $log/check.$id)"; tail -5 "$log/check.$id"; rc=1; fi
    fi
  done
  return $rc
}
step_g0() {
  # without these g0.sh still runs but names nothing, and CODEMAP.md would differ for that reason alone
  [ -d refs/focal/x ] && [ -s build/rebuild/7zip-objs.a ] || { echo "FAIL: run tools/setup.sh (refs/focal/x, build/rebuild)"; return 1; }
  # CODEMAP.md is kept outside this repository: a checkout without it only regenerates it
  local before had=0; before=$(mktemp); if [ -e CODEMAP.md ]; then cp CODEMAP.md "$before"; had=1; fi
  tools/g0.sh release/26.06/7zzs 7zzs || return 1
  local rc=0 len full min
  len=$(grep -c 'decode: length' build/7zzs.insncov.full.insns || true)
  full=$(sed -n 's/^== feature set full: \([0-9]*\) instructions.*/\1/p' build/7zzs.insncov.summary)
  min=$(sed -n 's/^== feature set min: \([0-9]*\) instructions.*/\1/p' build/7zzs.insncov.summary)
  echo "decoder length mismatches: $len; issues: full $full, min $min"
  [ "$len" = 0 ] || { echo "FAIL: the decoder's length differs from objdump's"; rc=1; }
  while read -r k v; do
    case "$k" in insncov.full.issues) n=$full ;; insncov.min.issues) n=$min ;; *) continue ;; esac
    if [ "$n" -gt "$v" ]; then echo "FAIL: $k $n, above the baseline $v"; rc=1
    elif [ "$n" -lt "$v" ]; then echo "note: $k $n, below the baseline $v: lower it in ci/baseline.txt"; fi
  done < <(grep -v '^#' ci/baseline.txt)
  [ "$had" = 0 ] || cmp -s "$before" CODEMAP.md ||
    { echo "FAIL: CODEMAP.md was out of date (now regenerated: commit it)"; rc=1; }
  rm -f "$before"; return $rc
}
step_difftest() {
  echo "cpu: $(sed -n 's/^model name\s*: //p' /proc/cpuinfo | head -1)"
  python3 -I tools/difftest/run.py -n 200 -s "${TEST_SEED:-1}" > "$log/difftest.full"; local rc=$?
  # the host's features, each mismatch's first cases, and the per-form table when any differs
  grep -E '^(host features|NM )' "$log/difftest.full"
  if [ $rc != 0 ]; then grep -A3 '^DIFF' "$log/difftest.full" | head -60; awk '$NF ~ /^[1-9]/' "$log/difftest.full"; fi
  tail -1 "$log/difftest.full"; return $rc
}
# Profile.x87LoadsKnown (an assumption about Intel processors): what FCW and FSW read back after each load
step_x87() {
  gcc -O1 -Wall -o build/fcwprobe tools/fcwprobe/fcw.c && build/fcwprobe
}
step_xsave() {
  python3 -I tools/xsavetest/run.py -n 150 -s "${TEST_SEED:-1}" --dump "$log/xsave.diffs" > "$log/xsave.full"; local rc=$?
  grep -E '^(host|NM )' "$log/xsave.full"
  [ $rc != 0 ] && grep -A2 '^DIFF' "$log/xsave.full" | cut -c1-400 | head -40
  tail -8 "$log/xsave.full"; return $rc
}
step_systest() {
  python3 -I tools/systest/run.py > "$log/systest.full"; local rc=$?
  grep -v ' ok native' "$log/systest.full" | tail -40; return $rc
}
step_systrace() { tools/systrace.sh release/26.06/7zzs build/systrace | tail -1; return "${PIPESTATUS[0]}"; }
step_min() {
  [ -s build/7zzs.insncov.min.insns ] || { echo "FAIL: run the step g0 first (build/7zzs.insncov.min.insns)"; return 1; }
  tools/mintrace.sh release/26.06/7zzs build/7zzs.insncov.min.insns build/mintrace
}
step_dispatch() {
  [ -s build/7zzs.insncov.min.insns ] || { echo "FAIL: run the step g0 first (build/7zzs.insncov.min.insns)"; return 1; }
  python3 -I tools/dispatch.py targets release/26.06/7zzs build/7zzs.funcs.tsv build/7zzs.dispatch.funcs || return 1
  # and every function with an instruction `min` lacks, for the dispatch points other than the resolvers
  awk -F'\t' 'NR > 1 && $6 > 0 { print $1 "\t" $2 }' build/7zzs.insncov.min >> build/7zzs.dispatch.funcs
  sort -u -o build/7zzs.dispatch.funcs build/7zzs.dispatch.funcs
  (cd lean && lake exe featneed ../release/26.06/7zzs ../build/7zzs.objdump.tsv ../build/7zzs.dispatch.funcs \
    ../build/7zzs.featneed.tsv) || return 1
  python3 -I tools/dispatch.py check release/26.06/7zzs build/7zzs.funcs.tsv build/7zzs.featneed.tsv \
    build/7zzs.insncov.min.insns build/7zzs.dispatch.txt
}

for s in "${steps[@]}"; do
  echo "=== $s"; t0=$(date +%s)
  if "step_$s" 2>&1 | tee "$log/$s"; [ "${PIPESTATUS[0]}" = 0 ]; then result[$s]=pass; else result[$s]=FAIL; fi
  echo "--- $s: ${result[$s]} ($(( $(date +%s) - t0 )) s)"
done
echo "=== summary (logs: $log)"
rc=0; for s in "${steps[@]}"; do printf '  %-9s %s\n' "$s" "${result[$s]}"; [ "${result[$s]}" = pass ] || rc=1; done
if [ -n "${GITHUB_STEP_SUMMARY:-}" ]; then
  for s in "${steps[@]}"; do echo "- $s: ${result[$s]}"; done >> "$GITHUB_STEP_SUMMARY"
fi
exit $rc
