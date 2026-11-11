#!/usr/bin/env bash
# G0 inventory of a release binary (PLAN.md §8, G0); regenerates build/<name>.*:
#   objdump.tsv   every instruction of objdump's linear sweep: address, length, mnemonic, text
#   funcs.tsv     function inventory (tools/ehframe_funcs.py): FDEs, asm sections, runs without FDE
#   insncov.*     the model's coverage of those instructions (lean/Tools/InsnCov.lean)
#   names.lib.tsv runtime functions named by tools/libmatch.py, if refs/focal/x holds the Ubuntu 20.04 archives
#   names.7zip.tsv 7-Zip's functions named the same way from build/rebuild/7zip-objs.a (tools/rebuild_focal.sh)
#   codemap.tsv   every function: origin, name, coverage, status (tools/codemap.py)
#   reach.tsv     every function: whether the entry may reach it, and how (tools/reach.py); reach.txt, its summary
# and then CODEMAP.md (tools/codemap.py) for 7zzs.
# Usage: tools/g0.sh BINARY NAME      e.g. tools/g0.sh release/26.06/7zzs 7zzs
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd); bin=$(realpath "$1"); out="$root/build/$2"
mkdir -p "$root/build"
objdump -d -w "$bin" | awk -F'\t' '/^ *[0-9a-f]+:\t/ {
  a=$1; gsub(/[ :]/,"",a); b=$2; gsub(/ +$/,"",b); n=split(b,x," "); m=$3; sub(/^ +/,"",m); gsub(/ +/," ",m)
  split(m,w," "); mn=w[1]
  if (mn ~ /^(lock|rep|repz|repnz|repe|repne|bnd|notrack|data16|addr32|cs|ds|ss|es|fs|gs|rex.*|xacquire|xrelease)$/ && w[2]!="") mn=mn" "w[2]
  print a"\t"n"\t"mn"\t"m }' > "$out.objdump.tsv"
python3 -I "$root/tools/ehframe_funcs.py" "$bin" "$out.objdump.tsv" > "$out.funcs.tsv"
(cd "$root/lean" && lake build insncov >/dev/null && .lake/build/bin/insncov "$bin" "$out.objdump.tsv" "$out.funcs.tsv" "$out.insncov" >/dev/null)
F="$root/refs/focal/x"
if [ -d "$F" ]; then
  python3 -I "$root/tools/libmatch.py" "$bin" "$out.funcs.tsv" \
    "$F"/libc6-dev-9.18/usr/lib/x86_64-linux-gnu/{libc.a,libpthread.a,libm-2.31.a} \
    "$F"/libstdc++-9-dev/usr/lib/gcc/x86_64-linux-gnu/9/libstdc++.a \
    "$F"/libgcc-9-dev/usr/lib/gcc/x86_64-linux-gnu/9/{libgcc.a,libgcc_eh.a} > "$out.names.lib.tsv"
  # 7-Zip's own functions, from the GCC 9.4 rebuild of tools/rebuild_focal.sh, if it was made
  A="$root/build/rebuild/7zip-objs.a"
  [ -f "$A" ] && python3 -I "$root/tools/libmatch.py" "$bin" "$out.funcs.tsv" "$A" > "$out.names.7zip.tsv"
  [ "$2" = 7zzs ] && python3 -I "$root/tools/codemap.py" 7zzs > "$root/CODEMAP.md"
  [ "$2" = 7zzs ] && (cd "$root" && python3 -I tools/reach.py 7zzs "$bin" > "$out.reach.txt")
fi
echo "$(wc -l < "$out.objdump.tsv") instructions, $(wc -l < "$out.funcs.tsv") functions; see $out.insncov.summary"
