#!/usr/bin/env bash
# G1 (PLAN.md §7, H-CPU-min): on a processor with no optional extension, 7zzs executes none of the instructions the
# model's decoder gives #UD for under the feature set `min` (OUT.min.insns of insncov, tools/g0.sh): the CPUID dispatch
# of glibc (IFUNC) and of 7-Zip picks the baseline code. Measured, not proved (the proof that the dispatch does so is
# part of the statements, G2/G3), on the commands of tools/systrace.sh over its corpus:
#   1. control: tools/minprobe/ud.c executes one instruction of each extension; under the emulator's baseline
#      processor each must die of SIGILL (so a run of 7zzs that does not, executed none of these);
#   2. every command under qemu-user with that processor (QEMU, default qemu-x86_64; MIN_CPU, default the x86-64
#      baseline: qemu64 without SSE3 and POPCNT), logging every instruction it translates (`-d in_asm`, a superset of
#      those executed); none may die of a signal;
#   3. no address translated is one of the `min` instructions with an issue.
# Usage: tools/mintrace.sh BINARY MIN_INSNS OUTDIR     e.g. tools/mintrace.sh release/26.06/7zzs build/7zzs.insncov.min.insns build/mintrace
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
bin=$(realpath "$1"); insns=$(realpath "$2"); out=$(realpath -m "$3")
QEMU=${QEMU:-qemu-x86_64}; CPU=${MIN_CPU:-qemu64,-pni,-popcnt}
command -v "$QEMU" >/dev/null || { echo "FAIL: no $QEMU (apt install qemu-user)" >&2; exit 1; }
rm -rf "$out"; mkdir -p "$out"; work=$(mktemp -d "$out/work.XXXX"); trap 'rm -rf "$work"' EXIT
echo "emulator: $("$QEMU" --version | head -1); processor $CPU"

echo "== 1. control: each extension's instruction dies of SIGILL under $CPU"
gcc -O1 -Wall -o "$work/ud" "$root/tools/minprobe/ud.c"
rc=0; n=$("$work/ud")
for i in $(seq 0 $((n - 1))); do
  set +e; bash -c '"$@"; exit $?' _ "$QEMU" -cpu "$CPU" "$work/ud" "$i" > "$work/ud.out" 2>&1; st=$?; set -e
  name=$(grep -v 'Illegal instruction' "$work/ud.out" | head -1 || true)
  if [ $st = 132 ]; then echo "  ok: $name: SIGILL"; else echo "  FAIL: $name: exit status $st, not SIGILL"; rc=1; fi
done
[ $rc = 0 ] || exit 1

echo "== 2. the commands of tools/systrace.sh under $CPU"
cd "$work"
mkdir src; head -c 300000 /dev/urandom > src/rand.bin; seq 1 200000 > src/seq.txt; mkdir src/sub; echo hi > src/sub/a.txt
ln -s ../seq.txt src/sub/link
k=0
run() {  # name, then the command line
  local name=$1; shift; k=$((k + 1))
  set +e; "$QEMU" -cpu "$CPU" -d in_asm -D "$work/log.$k" "$bin" "$@" > "$work/out" 2>&1; local st=$?; set -e
  echo "$name $st" >> "$out/status"
  if [ $st -ge 128 ]; then echo "  FAIL: $name died of signal $((st - 128))"; tail -3 "$work/out"; rc=1; fi
  grep -ahoE '^0x[0-9a-fA-F]+:' "$work/log.$k" | sort -u > "$work/addr.$k" || true
  rm -f "$work/log.$k"
}
for f in 7z zip tar xz gzip bzip2 wim; do
  case $f in
    xz|gzip|bzip2) run "a.$f" a -t$f "c.$f" src/seq.txt -bso0 -bsp0 ;;
    *) run "a.$f" a -t$f "c.$f" src -bso0 -bsp0 ;;
  esac
done
run a.enc.7z a -t7z -pPW -mhe=on c.enc.7z src -bso0 -bsp0
for f in 7z zip tar xz gzip bzip2 wim enc.7z; do
  for m in mt1 mtX; do
    o=(); [ $m = mt1 ] && case $f in 7z|enc.7z) o=(-t7z -mmt1 -mmtf=off) ;; *) o=(-mmt1) ;; esac
    run "l.$f.$m" l "c.$f" -pPW "${o[@]}"
    run "t.$f.$m" t "c.$f" -pPW "${o[@]}"
    rm -rf x; run "x.$f.$m" x "c.$f" -pPW -ox -y "${o[@]}"
    rm -rf x; run "e.$f.$m" e "c.$f" -pPW -ox -y "${o[@]}"
  done
done
run a.7z.mt1 a -t7z n.7z src -mmt1 -mmtf=off; run u.7z.mt1 u n.7z src/seq.txt -mmt1 -mmtf=off
run d.7z.mt1 d n.7z seq.txt -mmt1 -mmtf=off; run rn.7z.mt1 rn n.7z rand.bin r2.bin -mmt1 -mmtf=off
echo "  $k commands; exit statuses: $(awk '{print $2}' "$out/status" | sort | uniq -c | tr -s ' ' | tr '\n' ';')"
cat "$work"/addr.* | sort -u > "$out/translated"

echo "== 3. the min instructions with an issue, among those translated"
python3 -I - "$insns" "$out/translated" "$root/build/7zzs.codemap.tsv" "$out" <<'PY' || rc=1
import sys, pathlib
insns, translated, codemap, out = sys.argv[1:5]
ud = {}
for l in list(open(insns))[1:]:
    a, _len, mn, fn, issue = l.rstrip("\n").split("\t")[:5]
    ud[int(a, 16)] = (mn, fn, issue)
tr = {int(l.strip().rstrip(":"), 16) for l in open(translated) if l.strip()}
starts = []
p = pathlib.Path(codemap)
if p.exists():
    for l in list(open(p))[1:]:
        r = l.rstrip("\n").split("\t")
        starts.append((int(r[0], 16), int(r[1]), r[3], r[4]))
img = [a for a in tr if 0x400000 <= a < 0x800000]
hit = sorted(a for a in tr if a in ud)
# the functions of the image with at least one instruction translated
import bisect
keys = [s[0] for s in starts]
seen = set()
for a in img:
    i = bisect.bisect_right(keys, a) - 1
    if i >= 0 and a < starts[i][0] + starts[i][1]:
        seen.add(i)
with open(pathlib.Path(out) / "functions", "w") as f:
    for i in sorted(seen):
        f.write(f"{starts[i][0]:x}\t{starts[i][2]}\t{starts[i][3]}\n")
print(f"  {len(tr)} distinct addresses translated, {len(img)} in the image, in {len(seen)} of its functions")
print(f"  min instructions with an issue: {len(ud)}, in {len({v[1] for v in ud.values()})} functions; translated: {len(hit)}")
for a in hit[:20]:
    print(f"  FAIL: {a:x} {ud[a][0]} (function {ud[a][1]}): {ud[a][2]}")
sys.exit(1 if hit or not img else 0)
PY
[ $rc = 0 ] && echo "ok: none of the min instructions with an issue was translated"
exit $rc
