"""The functions a run of 7zzs enters (PLAN.md §M, "M1 function set": the lower bound).

A gdb script: a breakpoint at the start of every function of FUNCS (build/7zzs.funcs.tsv, tools/ehframe_funcs.py),
each deleted at its first hit, so the run slows only once per function; writes the starts hit, in order, to OUT.
7zzs is static and not PIE, so the addresses are the file's. One concrete run: a lower bound of what a theorem about
the command must cover (the upper bound is the static call graph with the format fixed).
Usage (in an empty scratch directory):
  FUNCS=build/7zzs.funcs.tsv OUT=t.hit gdb -batch -nx -x tools/funchit.gdb.py --args 7zzs t c.lzma -tlzma:s0 -mmt1
"""
import gdb, os
funcs = [int(l.split("\t")[0], 16) for l in open(os.environ["FUNCS"]) if l[0] in "0123456789abcdef"]
hit = []
gdb.execute("set pagination off"); gdb.execute("set confirm off")
gdb.execute("starti")
bps = {}
for a in funcs:
    bps[a] = gdb.Breakpoint(f"*{a:#x}", internal=True)
while True:
    try:
        gdb.execute("continue", to_string=True)
    except gdb.error:
        break
    try:
        pc = int(gdb.parse_and_eval("$pc"))
    except gdb.error:
        break
    if pc in bps:
        hit.append(pc); bps.pop(pc).delete()
    else:
        break
open(os.environ["OUT"], "w").write("".join(f"{a:x}\n" for a in hit))
