#!/usr/bin/env bash
# G0 (PLAN.md §6.2): the syscalls 7zzs makes per command, measured with strace on a small corpus.
# Not evidence for any theorem: it sizes the syscall model (G1) and seeds the allowlist (SYS) that the
# proofs must then justify. Usage: tools/systrace.sh BINARY OUTDIR
set -euo pipefail
bin=$(realpath "$1"); out=$(realpath -m "$2")
mkdir -p "$out"; work=$(mktemp -d "$out/work.XXXX"); trap 'rm -rf "$work"' EXIT
cd "$work"
mkdir src; head -c 300000 /dev/urandom > src/rand.bin; seq 1 200000 > src/seq.txt; mkdir src/sub; echo hi > src/sub/a.txt
ln -s ../seq.txt src/sub/link
# corpus: one archive per format 7zzs can write, built by 7zzs itself
for f in 7z zip tar xz gzip bzip2 wim; do
  case $f in
    xz|gzip|bzip2) "$bin" a -t$f "c.$f" src/seq.txt -bso0 -bsp0 ;;
    *) "$bin" a -t$f "c.$f" src -bso0 -bsp0 ;;
  esac
done
"$bin" a -t7z -pPW -mhe=on c.enc.7z src -bso0 -bsp0
trace() {  # name, then the command line
  local name=$1; shift
  strace -f -qq -o "$work/t" "$bin" "$@" >/dev/null 2>&1 || true
  sed -E 's/^[0-9]+ +//; s/^([a-z_0-9]+)\(.*/\1/; /^[^a-z]/d; /resumed>/d; /^\+\+\+/d; /^---/d' "$work/t" | sort | uniq -c | sort -rn > "$out/$name.sys"
}
for f in 7z zip tar xz gzip bzip2 wim enc.7z; do
  for m in mt1 mtX; do
    # single-threaded flags per type (PLAN.md §5, option (a)): -mmtf=off stops 7z's CMixerMT thread per coder,
    # but turns bzip2's decoder thread on, so it is given for 7z only, with the type fixed by -t
    o=(); [ $m = mt1 ] && case $f in 7z|enc.7z) o=(-t7z -mmt1 -mmtf=off) ;; *) o=(-mmt1) ;; esac
    trace "l.$f.$m" l "c.$f" -pPW "${o[@]}"
    trace "t.$f.$m" t "c.$f" -pPW "${o[@]}"
    rm -rf x; trace "x.$f.$m" x "c.$f" -pPW -ox -y "${o[@]}"
    rm -rf x; trace "e.$f.$m" e "c.$f" -pPW -ox -y "${o[@]}"
  done
done
trace a.7z.mt1 a -t7z n.7z src -mmt1 -mmtf=off; trace u.7z.mt1 u n.7z src/seq.txt -mmt1 -mmtf=off
trace d.7z.mt1 d n.7z seq.txt -mmt1 -mmtf=off; trace rn.7z.mt1 rn n.7z rand.bin r2.bin -mmt1 -mmtf=off
# union per command family
cd "$out"
for c in l t x e a u d rn; do
  cat $c.*.sys 2>/dev/null | awk '{print $2}' | sort -u > "union.$c"
done
for c in l t x e; do
  cat $c.*.mt1.sys | awk '{print $2}' | sort -u > "union.$c.mt1"
done
cat union.? union.?? | sort -u > union.all
# the single-threaded hypothesis of R1–R3 (PLAN.md §5): no thread is created under the single-threaded flags
if grep -lw clone "$out"/*.mt1.sys; then echo "FAIL: clone under the single-threaded flags" >&2; exit 1; fi
echo "ok: no clone under the single-threaded flags; $(wc -l < union.all) distinct syscalls in all"
