"""The addresses of the instructions a run of 7zzs executes, one per step (PLAN.md §M, for `tools/cfg_gen.py check`).

A gdb script: `stepi` from the first instruction, writing `rip` (hex) per step to OUT, for at most N steps. A call
into the vDSO is run at full speed to its return address (single-stepping it makes the time functions' seqlock loop
retry for ever, and the theorems assume no vDSO, `vdso = false`): the trace shows the vDSO's entry, then the return
address, which `cfg_gen.py check` takes as an opaque call.
Usage (in an empty scratch directory):
  N=4000000 OUT=trace.txt gdb -batch -nx -x tools/stepi.gdb.py --args 7zzs t c.lzma -tlzma:s0 -mmt1
"""
import os

import gdb

VDSO = 0x7F0000000000
gdb.execute("set pagination off")
gdb.execute("starti")
n = int(os.environ["N"])
with open(os.environ["OUT"], "w") as out:
    for _ in range(n):
        try:
            pc = int(gdb.parse_and_eval("$pc"))
            out.write("%x\n" % pc)
            if pc >= VDSO:
                ra = int(gdb.parse_and_eval("*(unsigned long *)$sp"))
                gdb.execute("tbreak *%#x" % ra, to_string=True)
                gdb.execute("continue", to_string=True)
            else:
                gdb.execute("stepi", to_string=True)
        except gdb.error:
            break
