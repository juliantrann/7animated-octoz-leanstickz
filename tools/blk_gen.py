#!/usr/bin/env python3
"""Generate lean/FV7z/<Group>/Code.lean, Pats.lean, Blocks.lean and Cuts.lean for a function with branches (PLAN.md G2,
pilot).

From the model's decoder's own output (`lake exe decshow`) for the function:
  Code.lean    its bytes in 7zzs 26.06 (`def`, pinned to the file by `decide +kernel`);
  Pats.lean    each distinct stretch of straight-line code between labels and jumps, and each distinct jump, as its
               own short list of bytes: what its instructions decode to (`Dec`, by `rfl`), their effects (`Op`), and
               the stretch as a `Blk`;
  Blocks.lean  where the patterns lie in the code (`<+:`, by `decide +kernel`), and for each basic block an `Sp`:
               the stretch's `wp`, then its jump's exits;
  Cuts.lean    the cut points (the entry, the ends of the range coder's normalizations, where two ways meet), and from
               each the blocks up to the next cut points as one `Sp`; the table of these for `Seg.cfg`.

Usage (from lean/):  python3 -I ../tools/blk_gen.py DECDIR FV7z/Lzma [NAME]
NAME is a function of the table `FNS` (`dr3` without one). DECDIR holds `<name>.txt` from
`lake exe decshow ../release/26.06/7zzs <hex addr> <len>`; a missing one is made.
"""
import os, re, subprocess, sys, textwrap

# name -> the function: its group (directory and namespace), C name, address and length in 7zzs 26.06; `pos`: the code
# is taken where it lies in 7zzs (its instructions have operands `[rip + d]`), else wherever it lies; `stops`: offsets
# the proof does not go past (exits, like the `ret`: the invariant there says they are not reached, or what holds);
# `tag`, `src`: for the files' headers.
FNS = {
    "dr3": dict(grp="Lzma", cn="LzmaDec_DecodeReal_3", a=0x6d4040, n=4719, pos=False, stops=(), tag="PLAN.md G2, pilot",
                src="`C/LzmaDec.c`'s `LzmaDec_DecodeReal_3` (section `.text$LZMADECOPT`, the assembly of "
                    "`Asm/x86/LzmaDecOpt.asm`;\n`objdump -d`)"),
    # glibc 2.31 elf/dl-tunables.c. Stops: a name of the environment is an alias of a tunable (0x165), is
    # `GLIBC_TUNABLES` (0x1eb); `__libc_enable_secure` is set (0x52e).
    "tin": dict(grp="Tun", cn="__tunables_init", a=0x66ee10, n=1413, pos=True, stops=(0x165, 0x1eb, 0x52e),
                tag="PLAN.md G3, startup", src="glibc 2.31's `__tunables_init` (`elf/dl-tunables.c`; `objdump -d`)"),
    # glibc 2.31 elf/dl-support.c. `jt`: its `switch`'s jump table (address, entries: 32-bit offsets from the table to
    # the cases). Stop: the vector is empty (0x410, a `ret`).
    "aux": dict(grp="Auxv", cn="_dl_aux_init", a=0x66f410, n=1041, pos=True, stops=(0x410,), jt=(0x6f3660, 31),
                tag="PLAN.md G3, startup", src="glibc 2.31's `_dl_aux_init` (`elf/dl-support.c`; `objdump -d`)"),
    # glibc 2.31 elf/enbl-secure.c. Stops: the `ret` (0xe, a block of its own); `__libc_enable_secure_decided` is 0
    # (0x10: the path that asks the kernel for the user's and the group's ids).
    "sec": dict(grp="Sec", cn="__libc_init_secure", a=0x6706a0, n=78, pos=True, stops=(0xe, 0x10),
                tag="PLAN.md G3, startup", src="glibc 2.31's `__libc_init_secure` (`elf/enbl-secure.c`; `objdump -d`)"),
    # glibc 2.31 elf/dl-debug.c. Stops: the two `ret`s (0x5c after the stores, 0x60 with nothing to do).
    "dbg": dict(grp="Dbg", cn="_dl_debug_initialize", a=0x66e4a0, n=124, pos=True, stops=(0x5c, 0x60),
                tag="PLAN.md G3, startup", src="glibc 2.31's `_dl_debug_initialize` (`elf/dl-debug.c`; `objdump -d`)"),
    # glibc 2.31 setjmp/sigjmp.c. Stops: the `ret` without a mask to save (0x12), and where one is saved (0x18).
    "sjs": dict(grp="Sjs", cn="__sigjmp_save", a=0x67e0b0, n=52, pos=True, stops=(0x12, 0x18),
                tag="PLAN.md G3, startup", src="glibc 2.31's `__sigjmp_save` (`setjmp/sigjmp.c`; `objdump -d`)"),
    # glibc 2.31 sysdeps/x86_64/start.S, the file's entry. Stop: the `call` of `__libc_start_main` (0x28), which
    # does not return (after it, a `hlt`).
    "ent": dict(grp="Entry", cn="_start", a=0x41d350, n=47, pos=True, stops=(0x28,),
                tag="PLAN.md G3, startup", src="glibc 2.31's `_start` (`sysdeps/x86_64/start.S`; `objdump -d`)"),
    # The section `.init` (crti.o's and crtn.o's pieces, `sysdeps/x86_64/crti.S`): `_init`, which `__libc_csu_init`
    # calls. Stops: the `call` of `__gmon_start__` (0x14; the symbol is 0, so not reached) and the `ret` (0x1a).
    "ini": dict(grp="Ini", cn="_init", a=0x401000, n=27, pos=True, stops=(0x14, 0x1a),
                tag="PLAN.md G3, startup", src="the section `.init`, `_init` (`sysdeps/x86_64/crti.S`; `objdump -d`)"),
    # GCC's crtstuff.c (crtbegin.o): `deregister_tm_clones`, which `__do_global_dtors_aux` calls. Stops: the `jmp`
    # through `_ITM_deregisterTMCloneTable` (0x1c; the table is empty and the symbol 0, so not reached), the `ret` (0x20).
    "dtc": dict(grp="Dtc", cn="deregister_tm_clones", a=0x41d390, n=33, pos=True, stops=(0x1c, 0x20),
                tag="PLAN.md G3, startup", src="GCC 9.4's `deregister_tm_clones` (`libgcc/crtstuff.c`; `objdump -d`)"),
    # GCC's crtstuff.c (crtbegin.o): `register_tm_clones`, which `frame_dummy` jumps to. Stops: the `jmp` through
    # `_ITM_registerTMCloneTable` (0x2e; the table is empty and the symbol 0, so not reached), the `ret` (0x30).
    "rtc": dict(grp="Rtc", cn="register_tm_clones", a=0x41d3c0, n=49, pos=True, stops=(0x2e, 0x30),
                tag="PLAN.md G3, startup", src="GCC 9.4's `register_tm_clones` (`libgcc/crtstuff.c`; `objdump -d`)"),
    # The section `.fini` (crti.o's and crtn.o's pieces): `_fini`, which `__libc_csu_fini` calls last. Stop: the `ret`.
    "fin": dict(grp="Fin", cn="_fini", a=0x6d7670, n=13, pos=True, stops=(0xc,),
                tag="PLAN.md G3, startup", src="the section `.fini`, `_fini` (`sysdeps/x86_64/crti.S`; `objdump -d`)"),
    # glibc 2.31 csu/static-reloc.c: nothing to do in a file that is not position-independent.
    "pie": dict(grp="Pie", cn="_dl_relocate_static_pie", a=0x41d380, n=5, pos=True, stops=(),
                tag="PLAN.md G3, startup",
                src="glibc 2.31's `_dl_relocate_static_pie` (`csu/static-reloc.c`; `objdump -d`)"),
    # glibc 2.31 csu/libc-start.c, to where `init_cpu_features` begins (0xd3; from there: FV7z/CpuFeat). Stops: the
    # auxiliary vector has no `AT_PHDR` (0x92: the program headers are taken from the ELF header).
    "lsm": dict(grp="Start", cn="__libc_start_main", a=0x613040, n=2071, pos=True, stops=(0x92, 0xd3), calls=True,
                tag="PLAN.md G3, startup", src="glibc 2.31's `__libc_start_main` (`csu/libc-start.c`; `objdump -d`)"),
    # glibc 2.31 sysdeps/unix/sysv/linux/x86_64/brk.c. Stops: the `syscall` (9), the kernel's answer is an error
    # (0x28), the break is below what was asked for (0x48): both set `errno`.
    "brk": dict(grp="Brk", cn="__brk", a=0x6a2a00, n=0x5c, pos=True, stops=(0x28, 0x48), calls=True,
                tag="PLAN.md G3, startup",
                src="glibc 2.31's `__brk` (`sysdeps/unix/sysv/linux/x86_64/brk.c`; `objdump -d`)"),
    # glibc 2.31 misc/sbrk.c. Stops: the calls of `__brk` (0x62, 0x7c); `errno` is set (0x38: an overflow of the
    # break, or `__brk` failed), a decrement (0x78).
    "sbk": dict(grp="Sbrk", cn="__sbrk", a=0x666390, n=0xa0, pos=True, stops=(0x38, 0x46, 0x78), calls=True,
                tag="PLAN.md G3, startup", src="glibc 2.31's `__sbrk` (`misc/sbrk.c`; `objdump -d`)"),
    # glibc 2.31 csu/libc-tls.c. Stops: `__libc_fatal` after `arch_prctl` fails (0x15b), no `PT_TLS` header (0x210),
    # its alignment 0 (0x270); the `ret` is at 0x20b.
    "tls": dict(grp="Tls", cn="__libc_setup_tls", a=0x613a10, n=0x288, pos=True, stops=(0x15b, 0x210, 0x270),
                calls=True, tag="PLAN.md G3, startup",
                src="glibc 2.31's `__libc_setup_tls` (`csu/libc-tls.c`; `objdump -d`)"),
    # glibc 2.31 csu/libc-start.c from 0x6133c0 (`entry`), after `__libc_setup_tls`: the code is `Start`'s (`code`),
    # with operands `fs:[…]` (`fs`: the thread control block). Stops: `setjmp` returns again (0x497: a thread ends),
    # `__libc_fatal` for a kernel too old (0x62a) and for a version not found (0x736), the call of
    # `__libc_check_standard_fds` (0x7b9: `__libc_enable_secure` is 0).
    "lsb": dict(grp="StartB", code=("Start", "lsm"), cn="__libc_start_main", a=0x613040, n=2071, entry=896, pos=True,
                fs=True, stops=(0x497, 0x62a, 0x736, 0x7b9), calls=True, tag="PLAN.md G3, startup",
                src="glibc 2.31's `__libc_start_main` (`csu/libc-start.c`; `objdump -d`)"),
    # glibc 2.31 sysdeps/unix/sysv/linux/syscall-template.S (`uname`). Stops: the `syscall` (9; a step of its own),
    # the `ret` (0x13, a block of its own), the kernel's answer is an error (0x14: `errno` is set).
    "unm": dict(grp="Uname", cn="__uname", a=0x6649e0, n=37, pos=True, stops=(0x13, 0x14), calls=True,
                tag="PLAN.md G3, startup",
                src="glibc 2.31's `__uname` (`sysdeps/unix/sysv/linux/syscall-template.S`; `objdump -d`)"),
    # glibc 2.31 sysdeps/unix/sysv/linux/dl-sysdep.c. Stop: `__uname` failed (0xb0: the release is read from
    # `/proc/sys/kernel/osrelease`); the `ret`s are at 0x8a (three parts read) and 0xa9 (fewer).
    "osv": dict(grp="Osv", cn="_dl_discover_osversion", a=0x671d50, n=268, pos=True, stops=(0xb0,), calls=True,
                tag="PLAN.md G3, startup",
                src="glibc 2.31's `_dl_discover_osversion` (`sysdeps/unix/sysv/linux/dl-sysdep.c`; `objdump -d`)"),
    # glibc 2.31 nptl/nptl-init.c. Stops: a waiter on `__default_pthread_attr_lock` is woken (0x2bb, `futex`), the
    # lock is taken (0x2db: `__lll_lock_wait_private`), `__stack_chk_fail` (0x2ec). By hand: `rep stos` (248),
    # `or [m], r` (340), `lock cmpxchg` (545), `xchg [m], r` (587).
    "pim": dict(grp="Pim", cn="__pthread_initialize_minimal_internal", a=0x6000b0, n=753, pos=True, fs=True,
                stops=(0x2bb, 0x2db, 0x2ec), calls=True, hand=(248, 340, 545, 587), tag="PLAN.md G3, startup",
                src="glibc 2.31's `__pthread_initialize_minimal_internal` (`nptl/nptl-init.c`; `objdump -d`)"),
    # glibc 2.31 csu/init-first.c (`__libc_init_first`, static). Stops: the branch for a `_dl_starting_up` that is not
    # 0 (0x1d: the weak symbol is 0, so not reached) and the `jmp` to `__ctype_init` (0x58).
    "lif": dict(grp="Lif", cn="__libc_init_first", a=0x672160, n=0x81, pos=True, stops=(0x1d, 0x58), calls=True,
                tag="PLAN.md G3, startup", src="glibc 2.31's `__libc_init_first` (`csu/init-first.c`; `objdump -d`)"),
    # glibc 2.31 ctype/ctype-info.c. Stop: the `ret` (0x53).
    "cti": dict(grp="Cti", cn="__ctype_init", a=0x6160e0, n=0x54, pos=True, fs=True, stops=(0x53,),
                tag="PLAN.md G3, startup", src="glibc 2.31's `__ctype_init` (`ctype/ctype-info.c`; `objdump -d`)"),
    # glibc 2.31 nptl/libc_pthread_init.c. Stop: the `ret` (0x28).
    # glibc 2.31 sysdeps/unix/sysv/linux/syscall-template.S (`mprotect`). Stops: the `ret` (0x13), the kernel's
    # answer is an error (0x14: `errno` is set).
    "mpr": dict(grp="Mpr", cn="__mprotect", a=0x666600, n=37, pos=True, stops=(0x13, 0x14), calls=True,
                tag="PLAN.md G3, startup",
                src="glibc 2.31's `__mprotect` (`sysdeps/unix/sysv/linux/syscall-template.S`; `objdump -d`)"),
    # glibc 2.31 elf/dl-reloc.c. Stops: the `ret` (0x32), `__mprotect` failed (0x4c: `_dl_signal_error`); the `call`
    # of `__mprotect` is at 0x43.
    "dpr": dict(grp="Dpr", cn="_dl_protect_relro", a=0x6ab6a0, n=0x70, pos=True, stops=(0x32, 0x4c), calls=True,
                tag="PLAN.md G3, startup",
                src="glibc 2.31's `_dl_protect_relro` (`elf/dl-reloc.c`; `objdump -d`)"),
    # glibc 2.31 stdlib/getenv.c. Stops: a name of one character (0x39), the `ret` (0x71), a string of the
    # environment begins with the name and `=` (0xc7), `__environ` is null or the name empty (0xd0); the `call`s of
    # `strlen` and `strncmp` through the PLT are at 0x78 and 0xb7.
    "gev": dict(grp="Genv", cn="getenv", a=0x623070, n=0xe0, pos=True, stops=(0x39, 0x71, 0xc7, 0xd0), calls=True,
                tag="PLAN.md G3, startup", src="glibc 2.31's `getenv` (`stdlib/getenv.c`; `objdump -d`)"),
    # glibc 2.31 misc/init-misc.c. Stops: the two `ret`s (0x49, 0x50).
    "ims": dict(grp="Ims", cn="__init_misc", a=0x668da0, n=0x51, pos=True, stops=(0x49, 0x50), calls=True,
                tag="PLAN.md G3, startup", src="glibc 2.31's `__init_misc` (`misc/init-misc.c`; `objdump -d`)"),
    # glibc 2.31 elf/dl-support.c, without a vDSO. Stops: the vDSO's map (0x46, 0x48c), a secure exec (0x7aa),
    # an environment variable that is set (0x7ec, 0x833, 0x854, 0x878, 0x89e, 0x8f5), an empty platform string
    # (0x8d2), the two `ret`s (0xace, 0xb50).
    "ndi": dict(grp="Ndi", cn="_dl_non_dynamic_init", a=0x66f830, n=0xb51, pos=True,
                stops=(0x46, 0x48c, 0x7aa, 0x7ec, 0x833, 0x854, 0x878, 0x89e, 0x8d2, 0x8f5, 0xace, 0xb50), calls=True,
                tag="PLAN.md G3, startup",
                src="glibc 2.31's `_dl_non_dynamic_init` (`elf/dl-support.c`; `objdump -d`)"),
    "lpi": dict(grp="Lpi", cn="__libc_pthread_init", a=0x62da30, n=41, pos=True, stops=(0x28,), calls=True,
                tag="PLAN.md G3, startup",
                src="glibc 2.31's `__libc_pthread_init` (`nptl/libc_pthread_init.c`; `objdump -d`)"),
    # glibc 2.31 nptl/register-atfork.c. Stops: the `ret` (0xbf), the table of handlers is already there (0xc0), the
    # process has more than one thread (0x118: the lock is taken with `lock cmpxchg`; 0x150: it is released with
    # `xchg`). By hand: `cmpxchg [m], r` (0x2b), `sub dword [m], 1` (0xaa).
    "raf": dict(grp="Raf", cn="__register_atfork", a=0x62da60, n=439, pos=True, fs=True, vop=True,
                stops=(0xbf, 0xc0, 0x118, 0x150), calls=True, hand=(0x2b, 0xaa), tag="PLAN.md G3, startup",
                src="glibc 2.31's `__register_atfork` (`nptl/register-atfork.c`; `objdump -d`)"),
    # glibc 2.31 stdlib/cxa_atexit.c (`__cxa_atexit`, its `__internal_atexit` inlined). Stops: the `ret` (0x91), the
    # process has more than one thread (0x98: the lock is taken with `lock cmpxchg`; 0xc0: it is released with `xchg`),
    # `__new_exitfn` gave no entry (0xed), the function is null (0x108: `__assert_fail`). By hand: `cmpxchg [m], r`
    # (0x2f), `sub dword [m], 1` (0x82).
    "cxa": dict(grp="Cxa", cn="__cxa_atexit", a=0x623690, n=318, pos=True, fs=True,
                stops=(0x91, 0x98, 0xc0, 0xed, 0x108), calls=True, hand=(0x2f, 0x82), tag="PLAN.md G3, startup",
                src="glibc 2.31's `__cxa_atexit` (`stdlib/cxa_atexit.c`; `objdump -d`)"),
    # glibc 2.31 stdlib/cxa_atexit.c. Stops: the `ret` (0xaa), the last block is full (0xb3: `calloc`), the list is
    # null (0xde: `__assert_fail`), `__exit_funcs_done` is set (0xfd). By hand: `add qword [m], 1` (0x9c).
    "nef": dict(grp="Nef", cn="__new_exitfn", a=0x623430, n=0x111, pos=True, stops=(0xaa, 0xb3, 0xde, 0xfd),
                calls=True, hand=(0x9c,), tag="PLAN.md G3, startup",
                src="glibc 2.31's `__new_exitfn` (`stdlib/cxa_atexit.c`; `objdump -d`)"),
    # glibc 2.31 csu/elf-init.c. Stop: the `ret` (0x93). The two `call *(%r15,%rbx,8)` (0x40, 0x78) and the `call`
    # of `_init` (0x5b) are cut points by `calls`.
    "csu": dict(grp="Csu", cn="__libc_csu_init", a=0x613ca0, n=0x94, pos=True, stops=(0x93,), calls=True,
                tag="PLAN.md G3, startup", src="glibc 2.31's `__libc_csu_init` (`csu/elf-init.c`; `objdump -d`)"),
    # glibc 2.31 sysdeps/x86_64/setjmp.S with `__sigjmp_save` (setjmp/sigjmp.c) after it, where its last `jmp` goes.
    # Stops: the `ret` (0x82), a signal mask to save (0x88). By hand: `rdsspq rax` (0x59).
    "ssj": dict(grp="Ssj", cn="__sigsetjmp", a=0x67e040, n=0xa4, pos=True, fs=True, stops=(0x82, 0x88), calls=True,
                hand=(0x59,), tag="PLAN.md G3, startup",
                src="glibc 2.31's `__sigsetjmp` and `__sigjmp_save` (`sysdeps/x86_64/setjmp.S`, `setjmp/sigjmp.c`;\n"
                    "`objdump -d`)"),
    # glibc 2.31 sysdeps/x86_64/bsd-_setjmp.S. Stop: the `jmp` to `__sigsetjmp` (0x6).
    "sjp": dict(grp="Sjp", cn="_setjmp", a=0x622340, n=11, pos=True, stops=(0x6,), calls=True,
                tag="PLAN.md G3, startup",
                src="glibc 2.31's `_setjmp` (`sysdeps/x86_64/bsd-_setjmp.S`; `objdump -d`)"),
    # glibc 2.31 nptl/nptl-init.c (`__pthread_tunables_init`, static). Stops: the `ret` (0x42), `__stack_chk_fail`
    # (0x43).
    "pti": dict(grp="Pti", cn="__pthread_tunables_init", a=0x5ffbc0, n=72, pos=True, fs=True, stops=(0x42, 0x43),
                calls=True, tag="PLAN.md G3, startup",
                src="glibc 2.31's `__pthread_tunables_init` (`nptl/pthread_mutex_conf.c`; `objdump -d`)"),
    # glibc 2.31 malloc/arena.c. Stops: the `ret` (0x183), `call __stack_chk_fail` (0x184).
    "pmi": dict(grp="Pmi", cn="ptmalloc_init", a=0x632170, n=0x189, pos=True, fs=True, stops=(0x183, 0x184),
                calls=True, tag="PLAN.md G3, malloc",
                src="glibc 2.31's `ptmalloc_init` (`malloc/arena.c`; `objdump -d`)"),
    # glibc 2.31 sysdeps/unix/sysv/linux/x86/elision-conf.c. Stops: the `ret` (0xab), `call __stack_chk_fail` (0xac).
    # glibc 2.31 nptl/pthread_mutex_lock.c (`__pthread_mutex_lock`), up to the first `__assert_fail`. Stops: the `ret`
    # (0x5b); `__pthread_force_elision` is set (0x60); the mutex is not of a plain kind (0x90: the `jmp` to
    # `__pthread_mutex_lock_full`); it is not a timed one (0x98); the lock is held (0xd0: `__lll_lock_wait`); it has an
    # owner (0x185: `__assert_fail`). By hand: `lock cmpxchg [rdi], edx` (0x2f), `add dword [rdi + 12], 1` (0x4f).
    "pml": dict(grp="Pml", cn="pthread_mutex_lock", a=0x5fc450, n=0x1a4, pos=True, fs=True,
                stops=(0x5b, 0x60, 0x90, 0x98, 0xd0, 0x185), calls=True, hand=(0x2f, 0x4f), tag="PLAN.md G3, pthread",
                src="glibc 2.31's `__pthread_mutex_lock` (`nptl/pthread_mutex_lock.c`; `objdump -d`)"),
    # glibc 2.31 nptl/pthread_mutex_unlock.c (`__pthread_mutex_unlock`, `__pthread_mutex_unlock_usercnt` inlined).
    # Stops: the `ret` (0x36); not a plain kind (0x40: `__pthread_mutex_unlock_full`); not timed (0x50); somebody
    # waits (0x70: `futex`). By hand: `sub dword [rdi + 12], 1` (0x1b), `xchg [rdi], eax` (0x2b).
    "pmu": dict(grp="Pmu", cn="pthread_mutex_unlock", a=0x5fd1d0, n=0x76, pos=True,
                stops=(0x36, 0x40, 0x50, 0x70), calls=True, hand=(0x1b, 0x2b), tag="PLAN.md G3, pthread",
                src="glibc 2.31's `__pthread_mutex_unlock` (`nptl/pthread_mutex_unlock.c`; `objdump -d`)"),
    # libgcc's unwind-dw2-fde.c: `__register_frame_info_bases` (its body at 0x612730, the entry with the checks at
    # 0x6127c0) and `__register_frame_info` (0x6127e0, the entry here: offset 0xb0). Stops: the tail call of
    # `pthread_mutex_unlock` (0x6a), the `ret`s (0x76, 0xa8, 0xd0), the other entry (0x90).
    "rfi": dict(grp="Rfi", cn="__register_frame_info", a=0x612730, n=0xd1, entry=0xb0, pos=True,
                stops=(0x6a, 0x76, 0x90, 0xa8, 0xd0), calls=True, tag="PLAN.md G3, startup",
                src="libgcc's `__register_frame_info` (`libgcc/unwind-dw2-fde.c`; `objdump -d`)"),
    # libgcc's crtstuff.c in crtbegin.o: `frame_dummy` (0x41d440, the first entry of `.init_array`). Stops: the two
    # `jmp register_tm_clones` (0x22, 0x30; `register_tm_clones` is `rtc`), by hand.
    "fdm": dict(grp="Fdm", cn="frame_dummy", a=0x41d440, n=0x35, pos=True,
                stops=(0x22, 0x30), calls=True, tag="PLAN.md G3, startup",
                src="libgcc's `frame_dummy` (`libgcc/crtstuff.c`; `objdump -d`)"),
    # glibc's `__default_morecore` (`malloc/morecore.c`): `__sbrk (n)`, a null pointer for its -1.
    "dmc": dict(grp="Dmc", cn="__default_morecore", a=0x635ab0, n=0x1f, pos=True, stops=(0x1e,), calls=True,
                tag="PLAN.md G3, `malloc`",
                src="glibc 2.31's `__default_morecore` (`malloc/morecore.c`; `objdump -d`)"),
    # glibc 2.31 malloc/malloc.c, the way of the first call (the main arena, its top the initial one, of size 0, the
    # heap contiguous, no hook). Stops: no arena (0x290), a request not below the `mmap` threshold (0x190), a top
    # that is not the initial one (0x6d), the assertions (0x755, 0x7fc), another arena (0xa9), a heap not
    # contiguous (0x400, 0x7d3), nothing to ask for (0x4fd), `MORECORE` failing (0x4f0, 0x6d0),
    # `__after_morecore_hook` set (0x6f8, 0x718), `mp_.sbrk_base` set (0x3ca), the new space following the old top
    # (0x3dc), an old top of some size (0x632, 0x5cf), no room (0x270), the `ret` (0x18e).
    "smm": dict(grp="Smm", cn="sysmalloc", a=0x630360, n=0x880, pos=True,
                stops=(0x290, 0x190, 0x6d, 0x755, 0x7fc, 0xa9, 0x400, 0x7d3, 0x4fd, 0x4f0, 0x6d0, 0x6f8, 0x718, 0x3ca,
                       0x3dc, 0x632, 0x5cf, 0x270, 0x18e),
                calls=True, tag="PLAN.md G3, `malloc`",
                src="glibc 2.31's `sysmalloc` (`malloc/malloc.c`; `objdump -d`)"),
    "eli": dict(grp="Eli", cn="elision_init", a=0x5ffc50, n=0xb1, pos=True, fs=True, stops=(0xab, 0xac),
                calls=True, tag="PLAN.md G3, startup",
                src="glibc 2.31's `elision_init` (`sysdeps/unix/sysv/linux/x86/elision-conf.c`; `objdump -d`)"),
    # glibc 2.31 elf/dl-tunables.c. Stops: the callback's tail call `jmp rdx` (0x55), the `ret` (0x60).
    "tgv": dict(grp="Tgv", cn="__tunable_get_val", a=0x66f3a0, n=109, pos=True, stops=(0x55, 0x60),
                tag="PLAN.md G3, startup",
                src="glibc 2.31's `__tunable_get_val` (`elf/dl-tunables.c`; `objdump -d`)"),
    # glibc 2.31 elf/dl-tls.c. Stop: the `ret` (0x18).
    "gts": dict(grp="Gts", cn="_dl_get_tls_static_info", a=0x66e6c0, n=25, pos=True, stops=(0x18,),
                tag="PLAN.md G3, startup", src="glibc 2.31's `_dl_get_tls_static_info` (`elf/dl-tls.c`; `objdump -d`)"),
    # glibc 2.31 sysdeps/unix/sysv/linux/getrlimit64.c. Stops: the `ret` (0x1c), the kernel's answer an error (0x20).
    "grl": dict(grp="Grl", cn="__getrlimit", a=0x666310, n=50, pos=True, stops=(0x1c, 0x20), calls=True,
                tag="PLAN.md G3, startup",
                src="glibc 2.31's `__getrlimit64` (`sysdeps/unix/sysv/linux/getrlimit64.c`; `objdump -d`)"),
    # glibc 2.31 sysdeps/unix/sysv/linux/sigaction.c. Stops: the old action is asked for (0xe6), the `ret` (0x19c),
    # the kernel's answer an error (0x1c0), `__stack_chk_fail` (0x1d4). `vop`: the copies of the mask through `xmm`
    # registers.
    "sga": dict(grp="Sga", cn="__libc_sigaction", a=0x600ff0, n=473, pos=True, fs=True, vop=True,
                stops=(0xe6, 0x19c, 0x1c0, 0x1d4), calls=True, tag="PLAN.md G3, startup",
                src="glibc 2.31's `__libc_sigaction` (`sysdeps/unix/sysv/linux/sigaction.c`; `objdump -d`)"),
}


def file_bytes(path, va, n):
    """`n` bytes at virtual address `va` of the ELF file (its `PT_LOAD` segments)"""
    import struct
    d = open(path, "rb").read()
    phoff, = struct.unpack_from("<Q", d, 0x20)
    phentsize, phnum = struct.unpack_from("<HH", d, 0x36)
    for k in range(phnum):
        t, _, off, vaddr, _, filesz = struct.unpack_from("<IIQQQQ", d, phoff + k * phentsize)
        if t == 1 and vaddr <= va and va + n <= vaddr + filesz:
            return d[off + va - vaddr: off + va - vaddr + n]
    raise Exception(f"{va:#x} is not in the file")


def parse(path, n):
    t = open(path).read()
    bs = re.search(r'bytes \w+ \d+: \[([^\]]*)\]', t)[1].split(', ')[:n]
    assert len(bs) == n
    out = []
    for b in re.split(r'\n(?=\d+ \()', t)[1:]:
        b = re.sub(r'ZellicX86\.Decode\.(Opd\.|Mn\.)?', '', b); b = re.sub(r'\s+', ' ', b)
        b = re.sub(r'rep := none, lock := false, mask := none, zero := false, fop := 0 ', '', b)
        b = b.replace('high8 := false', '').replace('width := ', 'w').replace('num := ', 'n')
        m = re.match(r'(\d+) \(\w+\): \{ mn := ([^,]+), opsz := (\d+), ops := \[(.*)\], len := (\d+), \}', b)
        if not m:
            # an instruction with a prefix (`rep`, `lock`, …): not supported, an error only if the proof reaches it
            m = re.match(r'(\d+) \(\w+\): \{ mn := ([^,]+), opsz := (\d+), ops := \[(.*)\], len := (\d+),', b)
            if not m: raise Exception(b)
            off, mn, sz, ops, ln = m.groups()
            out.append((int(off), "prefixed " + mn.strip(), int(sz), [], int(ln)))
            continue
        off, mn, sz, ops, ln = m.groups()
        if int(off) >= n: continue
        ol = [re.sub(r'\s+', ' ', x.strip()) for x in re.split(r',\s*(?=(?:reg|imm|rel|mem|xmm) )', ops)] if ops.strip() else []
        out.append((int(off), mn.strip(), int(sz), ol, int(ln)))
    return [int(x, 16) for x in bs], out


MEM = re.compile(r'mem \{ seg := none, base := (none|some \d+), index := (none|some \d+), scale := (\d+), '
                 r'disp := (\d+), ripRel := false, addr32 := (false|true), w(\d+) \}')


MRIP = re.compile(r'mem \{ seg := none, base := none, index := none, scale := 1, disp := (\d+), ripRel := true, '
                  r'addr32 := false, w(\d+) \}')


MFS = re.compile(r'mem \{ seg := some \(Seg\.fs\), base := (none|some \d+), index := (none|some \d+), scale := (\d+), '
                 r'disp := (\d+), ripRel := false, addr32 := false, w(\d+) \}')


def opt(x):
    return "none" if x == "none" else f"({x})"


def operand(o):
    """(kind, Lean term of the operand, fields)"""
    m = re.fullmatch(r'reg \{ w(\d+), n(\d+), ?\}', o)
    if m: return ('r', f"gr {m[1]} {m[2]}", (int(m[1]), int(m[2])))
    m = re.fullmatch(r'xmm (\d+)', o)
    if m: return ('x', f".xmm {m[1]}", (int(m[1]),))
    m = re.fullmatch(r'imm (\d+) (\d+)', o)
    if m: return ('i', f".imm {m[1]} {m[2]}", (int(m[1]), int(m[2])))
    m = re.fullmatch(r'rel (\d+)', o)
    if m: return ('rel', f".rel {m[1]}", (int(m[1]),))
    m = MEM.fullmatch(o)
    if m:
        b, i, sc, d, a32, w = opt(m[1]), opt(m[2]), m[3], m[4], m[5] == 'true', int(m[6])
        return ('ma' if a32 else 'm', f".mem ({'mga' if a32 else 'mg'} {b} {i} {sc} {d} {w})", (b, i, sc, d, w))
    m = MFS.fullmatch(o)
    if m:
        b, i, sc, d, w = opt(m[1]), opt(m[2]), m[3], m[4], int(m[5])
        return ('mf', f".mem (mf {b} {i} {sc} {d} {w})", (b, i, sc, d, w))
    m = MRIP.fullmatch(o)
    if m: return ('mr', f".mem (mrip {m[1]} {m[2]})", (int(m[1]), int(m[2])))
    return ('?', ".mem { " + o[6:].replace(' w', ' width := ').replace('Seg.', '.') if o.startswith('mem') else o, ())


def hw2(w): return {32: "(.inl rfl)", 64: "(.inr rfl)"}[w]
def hw3(w): return {16: "(.inl rfl)", 32: "(.inr (.inl rfl))", 64: "(.inr (.inr rfl))"}[w]
def hw4(w): return {8: "(.inl rfl)", 16: "(.inr (.inl rfl))", 32: "(.inr (.inr (.inl rfl)))", 64: "(.inr (.inr (.inr rfl)))"}[w]


def effect(mn, sz, ol, pc=None):
    """(Lean term of the instruction's operands, its `Op`, the proof of its `OpI`; of its `OpIA`, if the proof's name
    starts with `OpIA`: an instruction with an operand `[rip + d]`, `pc` the address of the instruction's end)"""
    ops = [operand(o) for o in ol]
    ks = tuple(o[0] for o in ops)
    terms = "[" + ", ".join(o[1] for o in ops) + "]"
    f = [o[2] for o in ops]
    def src(o):
        return f"(.r {o[2][1]})" if o[0] == 'r' else f"(.i {o[2][1]})"
    def tsrc(w):
        return f"[{ops[0][1]}, Src.opd {w} {src(ops[1])}]"
    def mem(o):
        b, i, sc, d, _ = o[2]
        return f"{b} {i} {sc} {d}"
    def absa(o):
        if pc is None: raise Exception(f"[rip + d] in a code taken wherever it lies: {mn} {ol}")
        return (pc + o[2][0]) % 2 ** 64
    if mn == 'nop':
        return terms, "Op.nop", "OpI.nop"
    # moves of an `xmm` register from and to memory, the register's value not followed (`vop`;
    # FV7z/Lemmas/BlkOps7.lean)
    if mn.startswith('sse '):
        sm = re.fullmatch(r'sse \(SseMn\.(\w+)\)', mn)[1]
        if sm in ('movdqu', 'movups') and ks == ('x', 'm') and f[1][4] == 128:
            return terms, f"Op.vl 16 {mem(ops[1])}", f"OpI.vl_{sm}"
        if sm in ('movdqu', 'movups') and ks == ('m', 'x') and f[0][4] == 128:
            return terms, f"Op.vs 16 {mem(ops[0])}", f"OpI.vs_{sm}"
        if sm in ('movq', 'movhps') and ks == ('x', 'm') and f[1][4] == 64:
            return terms, f"Op.vl 8 {mem(ops[1])}", f"OpI.vl_{sm}"
        if sm in ('movdqa', 'movaps') and ks == ('x', 'mr') and f[1][1] == 128:
            return terms, f"Op.vla 16 {absa(ops[1])}", f"OpIA.vl_{sm}_rip (by decide) (by decide)"
        if sm in ('movdqa', 'movaps') and ks == ('mr', 'x') and f[0][1] == 128:
            return terms, f"Op.vsa 16 {absa(ops[0])}", f"OpIA.vs_{sm}_rip (by decide) (by decide)"
        raise Exception(f"no effect for {mn} {sz} {ol}")
    # through `fs` (FV7z/Lemmas/SpFs.lean): the `Op` has the `fs` base `fb`
    if mn == 'mov' and ks == ('r', 'mf') and sz in (32, 64):
        assert f[1][4] == sz
        return terms, f"Op.ldf fb {sz} {f[0][1]} {mem(ops[1])}", f"OpIF.ldf {hw2(sz)}"
    if mn == 'mov' and ks == ('mf', 'r') and sz in (32, 64):
        assert f[0][4] == sz
        return terms, f"Op.stf fb {sz} {mem(ops[0])} {f[1][1]}", f"OpIF.stf {hw2(sz)}"
    if mn == 'mov' and ks == ('mf', 'r') and sz == 8:   # FV7z/Lemmas/BlkOps6.lean
        return terms, f"Op.stf8 fb {mem(ops[0])} {f[1][1]}", "OpIF.stf8"
    if mn == 'mov' and ks == ('mf', 'i'):
        assert f[0][4] == sz
        return terms, f"Op.stfi fb {sz} {mem(ops[0])} {f[1][1]}", f"OpIF.stfi {hw4(sz)}"
    if mn == 'xor' and ks == ('r', 'mf') and sz in (32, 64):
        assert f[1][4] == sz
        return terms, f"Op.xormf fb {sz} {f[0][1]} {mem(ops[1])}", f"OpIF.xormf {hw2(sz)}"
    if mn == 'xor' and sz == 8 and ks in (('r', 'r'), ('r', 'i')):
        return tsrc(8), f"Op.xor8 {f[0][1]} {src(ops[1])}", f"OpI.xor8 {src(ops[1])}"
    if mn == 'cbw' and sz == 64 and not ops:   # FV7z/Lemmas/BlkOps7.lean
        return terms, "Op.cdqe", "OpI.cdqe"
    if mn == 'endbr64' and not ops:
        return terms, "Op.nop", "OpI.endbr"
    if mn in ('cmp', 'test') and sz == 8 and ks in (('r', 'r'), ('r', 'i')):
        return tsrc(8), f"Op.{mn} 8 {f[0][1]} {src(ops[1])}", f"OpI.{mn}8 {src(ops[1])}"
    if mn == 'cmp' and ks == ('m', 'r') and sz in (32, 64):   # FV7z/Lemmas/BlkOps12.lean
        assert f[0][4] == sz
        return terms, f"Op.cmpmr {sz} {mem(ops[0])} {f[1][1]}", f"OpI.cmpmr {hw2(sz)}"
    if mn == 'cmp' and ks == ('mr', 'r') and sz in (32, 64):
        assert f[0][1] == sz
        return terms, f"Op.cmpmra {sz} {absa(ops[0])} {f[1][1]}", f"OpIA.cmpmr_rip {hw2(sz)} (by decide)"
    if mn == 'test' and ks == ('m', 'i') and sz == 8:
        assert f[0][4] == 8
        return terms, f"Op.testmi 8 {mem(ops[0])} {f[1][1]}", "OpI.testmi8"
    if mn == 'test' and ks == ('mr', 'i') and sz == 8:
        return terms, f"Op.testmia 8 {absa(ops[0])} {f[1][1]}", "OpIA.testmi8_rip (by decide)"
    if mn == 'cmp' and ks == ('m', 'i') and sz in (8, 32):
        assert f[0][4] == sz
        return terms, f"Op.cmpmi {sz} {mem(ops[0])} {f[1][1]}", f"OpI.cmpmi {'(.inl rfl)' if sz == 8 else '(.inr rfl)'}"
    if mn == 'cmp' and ks == ('m', 'i') and sz == 64:
        assert f[0][4] == sz
        return terms, f"Op.cmpmi 64 {mem(ops[0])} {f[1][1]}", "OpI.cmpmi64"
    if mn == 'cmp' and ks == ('mr', 'i') and sz == 8:   # FV7z/Lemmas/BlkOps8.lean
        return terms, f"Op.cmpmia 8 {absa(ops[0])} {f[1][1]}", "OpIA.cmpmi8_rip (by decide)"
    if mn == 'mov' and ks == ('mr', 'i') and sz == 8:
        return terms, f"Op.stia 8 {absa(ops[0])} {f[1][1]}", "OpIA.sti8_rip (by decide)"
    if mn == 'add' and ks == ('r', 'mr') and sz in (32, 64):
        assert f[1][1] == sz
        return terms, f"Op.addma {sz} {f[0][1]} {absa(ops[1])}", f"OpIA.addm_rip {hw2(sz)} (by decide)"
    if mn == 'cmp' and ks == ('r', 'mr') and sz in (16, 32, 64):   # FV7z/Lemmas/BlkOps9.lean
        assert f[1][1] == sz
        return terms, f"Op.cmpma {sz} {f[0][1]} {absa(ops[1])}", f"OpIA.cmpm_rip {hw3(sz)} (by decide)"
    if mn == 'cmp' and ks == ('mr', 'i') and sz in (32, 64):
        return terms, f"Op.cmpmia {sz} {absa(ops[0])} {f[1][1]}", f"OpIA.cmpmi_rip {hw2(sz)} (by decide)"
    if mn == 'mov' and ks == ('r', 'mr') and sz in (32, 64):
        assert f[1][1] == sz
        return terms, f"Op.lda {sz} {f[0][1]} {absa(ops[1])}", f"OpIA.ld_rip {hw2(sz)} (by decide)"
    if mn == 'movzx' and ks == ('r', 'mr') and sz == 32:
        v = f[1][1]
        return (terms, f"Op.ldzxa {v} {f[0][1]} {absa(ops[1])}",
                f"OpIA.ldzx_rip {'(.inl rfl)' if v == 8 else '(.inr rfl)'} (by decide)")
    if mn == 'mov' and ks == ('mr', 'r') and sz in (16, 32, 64):
        assert f[0][1] == sz
        return terms, f"Op.sta {sz} {absa(ops[0])} {f[1][1]}", f"OpIA.st_rip {hw3(sz)} (by decide)"
    if mn == 'mov' and ks == ('mr', 'i') and sz in (16, 32, 64):
        assert f[0][1] == sz
        return terms, f"Op.stia {sz} {absa(ops[0])} {f[1][1]}", f"OpIA.sti_rip {hw3(sz)} (by decide)"
    if mn.startswith('setcc ') and ks == ('r',) and sz == 8:
        return terms, f"Op.setcc {mn.split()[1]} {f[0][1]}", "OpI.setcc"
    if mn == 'movsx' and ks == ('r', 'm') and sz == 32 and f[1][4] == 8:   # FV7z/Lemmas/BlkOps5.lean
        return terms, f"Op.ldsxb {f[0][1]} {mem(ops[1])}", "OpI.ldsxb"
    if mn == 'movsxd' and ks == ('r', 'm') and sz == 64 and f[1][4] == 32:
        return terms, f"Op.ldsx {f[0][1]} {mem(ops[1])}", "OpI.ldsx"
    if mn == 'lea' and ks == ('r', 'mr') and sz == 64:
        return terms, f"Op.mov 64 {f[0][1]} (.i {absa(ops[1])})", "OpIA.lea_rip (by decide)"
    if mn in ('sub', 'cmp', 'add', 'and', 'or', 'xor', 'test', 'sbb', 'mov') and ks in (('r', 'r'), ('r', 'i')):
        r = f[0][1]
        if sz == 8 and mn == 'add':
            return tsrc(8), f"Op.add8 {r} {src(ops[1])}", f"OpI.add8 {src(ops[1])}"
        assert sz in (32, 64), (mn, sz, ol)
        return (tsrc(sz), f"Op.{mn} {sz} {r} {src(ops[1])}",
                f"OpI.{mn} {src(ops[1])} {hw2(sz)}")
    if mn == 'cmp' and ks == ('r', 'm') and sz == 16:   # FV7z/Lemmas/BlkOps10.lean
        assert f[1][4] == 16
        return terms, f"Op.cmpm 16 {f[0][1]} {mem(ops[1])}", "OpI.cmpm16"
    if mn in ('sub', 'cmp', 'add', 'and', 'xor') and ks == ('r', 'm'):
        assert sz in (32, 64) and f[1][4] == sz
        return terms, f"Op.{mn}m {sz} {f[0][1]} {mem(ops[1])}", f"OpI.{mn}m {hw2(sz)}"
    if mn in ('inc', 'dec', 'neg') and ks == ('r',):
        return terms, f"Op.{mn} {sz} {f[0][1]}", f"OpI.{mn} {hw2(sz)}"
    if mn == 'mov' and ks == ('r', 'm'):
        if sz == 8: return terms, f"Op.ld8 {f[0][1]} {mem(ops[1])}", "OpI.ld8"
        return terms, f"Op.ld {sz} {f[0][1]} {mem(ops[1])}", f"OpI.ld {hw2(sz)}"
    if mn == 'mov' and ks == ('m', 'r'):
        return terms, f"Op.st {sz} {mem(ops[0])} {f[1][1]}", f"OpI.st {hw4(sz)}"
    if mn == 'mov' and ks == ('m', 'i'):
        return terms, f"Op.sti {sz} {mem(ops[0])} {f[1][1]}", f"OpI.sti {hw4(sz)}"
    if mn == 'movzx' and ks == ('r', 'm') and sz == 32:
        v = f[1][4]
        return terms, f"Op.ldzx {v} {f[0][1]} {mem(ops[1])}", f"OpI.ldzx {'(.inl rfl)' if v == 8 else '(.inr rfl)'}"
    if mn.startswith('cmovcc ') and ks == ('r', 'r'):
        cc = mn.split()[1]
        return terms, f"Op.cmov{sz} {cc} {f[0][1]} {f[1][1]}", f"OpI.cmov{sz}"
    if mn == 'imul' and ks == ('r', 'r') and sz == 32:
        return terms, f"Op.imul {f[0][1]} {f[1][1]}", "OpI.imul"
    if mn == 'imul' and ks == ('r', 'r') and sz == 64:   # FV7z/Lemmas/BlkOps4.lean
        return terms, f"Op.imul64 {f[0][1]} {f[1][1]}", "OpI.imul64"
    if mn == 'lea' and ks == ('r', 'm'):
        return terms, f"Op.lea {sz} {f[0][1]} {mem(ops[1])}", f"OpI.lea {hw2(sz)}"
    if mn == 'lea' and ks == ('r', 'ma') and sz == 32:
        return terms, f"Op.lea32a {f[0][1]} {mem(ops[1])}", "OpI.lea32a"
    if mn in ('shl', 'shr', 'sar') and sz == 32 and ks in (('r', 'r'), ('r', 'i')):
        return (tsrc(8), f"Op.{mn} {f[0][1]} {src(ops[1])}",
                f"OpI.{mn} {src(ops[1])}")
    if mn in ('shl', 'shr', 'sar') and sz == 64 and ks in (('r', 'r'), ('r', 'i')):   # FV7z/Lemmas/BlkOps3.lean
        return tsrc(8), f"Op.{mn}64 {f[0][1]} {src(ops[1])}", f"OpI.{mn}64 {src(ops[1])}"
    if mn in ('rol', 'ror') and sz == 64 and ks in (('r', 'r'), ('r', 'i')):   # FV7z/Lemmas/BlkOps11.lean
        return tsrc(8), f"Op.{mn}64 {f[0][1]} {src(ops[1])}", f"OpI.{mn}64 {src(ops[1])}"
    if mn in ('push', 'pop') and ks == ('r',) and sz == 64:
        return terms, f"Op.{mn} {f[0][1]}", f"OpI.{mn}"
    raise Exception(f"no effect for {mn} {sz} {ol}")


REFILL = ["Op.shl 5 (.i 8)", "Op.ld8 5 (some 15) none 1 0", "Op.shl 0 (.i 8)", "Op.inc 64 15"]


def mnl(mn): return f"(.{mn})" if ' ' in mn else f".{mn}"


def rows(bs): return ",\n".join("  " + ", ".join(f"0x{b:02x}" for b in bs[i:i + 16]) for i in range(0, len(bs), 16))


def main():
    S, out = sys.argv[1], sys.argv[2]
    nm = sys.argv[3] if len(sys.argv) > 3 else "dr3"
    F = FNS[nm]
    # `code`: the code is another group's (its `Code.lean`), read from another offset (`entry`)
    cgrp, nm = F.get("code", (F["grp"], nm))
    E0 = F.get("entry", 0)
    # `fs`: instructions with operands `fs:[…]`; the pieces are `SpF`s, for runs with the `fs` base `fb`
    FSM = bool(F.get("fs"))
    SP, FB, FA = ("SpF", " (fb : Addr)", " fb") if FSM else ("Sp", "", "")
    FS0, FS1 = ("(", ").fs") if FSM else ("", "")
    OPN = f"open FV7z.{cgrp} ({nm} {nm}_at {nm}_length)\n" if "code" in F else ""
    grp, cn, a, n, pos, stops, tag = F["grp"], F["cn"], F["a"], F["n"], F["pos"], set(F["stops"]), F["tag"]
    # the jump table's bytes and the offsets of the cases
    jtb, jtg = b"", []
    if "jt" in F:
        ja, jn = F["jt"]
        jtb = file_bytes("../release/26.06/7zzs", ja, 4 * jn)
        jtg = [ja + int.from_bytes(jtb[4 * k: 4 * k + 4], "little", signed=True) - a for k in range(jn)]
        assert all(0 <= x < n for x in jtg)
    # the code's place in the statements: a binder and its use, or the address where the code lies in 7zzs
    EB, EA, ER = ("", f" {nm}_at", "") if pos else (" (e' : Addr)", " e'", " e'")
    os.makedirs(S, exist_ok=True); os.makedirs(out, exist_ok=True)
    p = f"{S}/{nm}.txt"
    if not os.path.exists(p):
        r = subprocess.run(["lake", "exe", "decshow", "../release/26.06/7zzs", f"{a:x}", str(n)],
                           capture_output=True, text=True, check=True)
        open(p, "w").write(r.stdout)
    bs, ins = parse(p, n)
    idx = {i[0]: k for k, i in enumerate(ins)}

    def tgt(i):
        off, mn, sz, ol, ln = i
        r = int(re.search(r'rel (\d+)', ol[-1])[1])
        return off + ln + (r if r < 2 ** 63 else r - 2 ** 64)
    ctl = lambda i: i[1].split()[0] in ('jcc', 'jmp', 'ret')
    jr = lambda i: i[1] == 'jmp' and i[3][0].startswith('reg')   # `jmp r`: through the jump table
    # calls (`calls`): the proof stops at a `call` and starts again after it, a cut point; the `call` itself is the
    # caller's to do (`SpAt.call`, FV7z/Lemmas/SpCall.lean)
    # (`syscall` likewise: `Seg.s_brk_grow` and its like, FV7z/Start/SysSeg.lean; `div` and the moves of an `xmm`
    # register: `Seg.s_div64`, `Seg.s_movq_ld` and its like, FV7z/Lemmas/BlkOps4.lean)
    # (`hand`: offsets of other instructions done by a lemma of their own: `rep stos`, `lock cmpxchg`, …)
    # (`vop`: the moves of an `xmm` register from and to memory are `Op`s that do not follow the register's value)
    callat = ({i[0]: i[0] + i[4] for i in ins
               if i[1].split()[0] in (('call', 'syscall', 'div') if F.get("vop") else ('call', 'syscall', 'div', 'sse'))
               or i[0] in F.get("hand", ())}
              if F.get("calls") else {})
    stops |= set(callat)
    # leaders: the entry, jump targets, what follows a jump
    leaders = {E0} | stops | set(jtg) | {x for x in callat.values() if x < n}
    for k, i in enumerate(ins):
        if jr(i): pass   # its targets are the table's (`jt`), needed if the proof reaches it
        elif i[1].split()[0] in ('jcc', 'jmp'):
            if tgt(i) in idx: leaders.add(tgt(i))   # else out of the code: an error only if the proof reaches it
        if ctl(i) and k + 1 < len(ins): leaders.add(ins[k + 1][0])
    # the range coder's normalizations: `cmp eax, 2^24; jae e`, then the four instructions that read a byte
    heads = {}   # offset of the cmp -> (offset after the jae, e)
    for k, i in enumerate(ins):
        if (i[1], i[2]) == ('cmp', 32) and i[3][1:] == ['imm 32 16777216'] and effect(*i[1:4])[1] == "Op.cmp 32 0 (.i 16777216)":
            j = ins[k + 1]
            assert j[1] == 'jcc 3' and [effect(*x[1:4])[1] for x in ins[k + 2:k + 6]] == REFILL, i
            heads[i[0]] = (j[0] + j[4], tgt(j))
            leaders.add(i[0])
    # reachable leaders
    blocks = {}   # leader -> (run instructions, terminator or None, next offset)
    for l in sorted(leaders):
        k = idx[l]; run = []
        while True:
            i = ins[k]
            if ctl(i): blocks[l] = (run, i, i[0] + i[4]); break
            run.append(i); k += 1
            if k == len(ins) or ins[k][0] in leaders: blocks[l] = (run, None, i[0] + i[4]); break
    reach, todo, called = set(), [E0], set()
    while todo:
        l = todo.pop()
        if l in callat and l not in called and l not in set(F["stops"]):
            called.add(l); todo.append(callat[l])
        if l in reach or l in stops: continue
        reach.add(l)
        run, t, nx = blocks[l]
        if t is None: todo.append(nx)
        elif jr(t):
            assert jtg, f"jmp r at {t[0]}: no jump table given"
            todo += jtg
        elif t[1].split()[0] == 'jmp': todo.append(tgt(t))
        elif t[1].split()[0] == 'jcc': todo += [tgt(t), nx]
    blocks = {l: b for l, b in blocks.items() if l in reach}

    # Code.lean
    jtdef = f"""
/-- Where its jump table lies in `7zzs`. -/
abbrev {nm}_jt_at : Addr := {F["jt"][0]:#x}

/-- Its jump table: {F["jt"][1]} offsets of 32 bits from the table to the cases. -/
def {nm}_jt : List Byte := [
{rows(list(jtb))}]

theorem {nm}_jt_pin : Exe.bytesAt V2606.zzs.blob {F["jt"][0]:#x} {len(jtb)} = some {nm}_jt := by decide +kernel

/-- The cases: where in the code the table's entries lead. -/
def {nm}_cases : List Nat := [{", ".join(map(str, jtg))}]
""" if jtg else ""
    atdef = f"\n/-- Where the code lies in `7zzs`. -/\nabbrev {nm}_at : Addr := {a:#x}\n" if pos else ""
    if "code" not in F: open(out + "/Code.lean", "w").write(f"""import ZellicX86.Spec.Executable
import FV7z.Image
import FV7z.Lemmas.InsFn
/-!
# The code of `{cn}` in `7zzs` ({tag})

The bytes of {F["src"]}, as a list, and the fact that they are the file's (`{nm}_pin`, by the kernel's evaluation of Zellic's
ELF reader). Generated by `tools/blk_gen.py`.
-/
namespace FV7z.{grp}
set_option maxRecDepth 100000
open ZellicX86

/-- `{cn}`, `{a:#x}` to `{a+n-1:#x}` of `7zzs`. -/
def {nm} : List Byte := [
{rows(bs)}]

theorem {nm}_pin : Exe.bytesAt V2606.zzs.blob {a:#x} {n} = some {nm} := by decide +kernel
theorem {nm}_length : {nm}.length = {n} := by decide +kernel
{atdef}{jtdef}
end FV7z.{grp}
""")

    # Pats.lean: distinct runs and jumps
    pats, jpats = {}, {}
    patA = set()   # the stretches with an operand `[rip + d]`: a `BlkA`, at the stretch's address
    patF = set()   # the stretches with an operand `fs:[…]`: a `BlkF`, at the stretch's address, the `fs` base `fb`
    isfs = lambda run: any('Seg.fs' in o for i in run for o in i[3])
    P = []
    missing = []
    def pkey(l):
        """the stretch at `l`: its bytes, and its address if an instruction has an operand `[rip + d]`"""
        run = blocks[l][0]
        b = bytes(bs[run[0][0]: run[-1][0] + run[-1][4]])
        return (b, a + l if isfs(run) or any('ripRel := true' in o for i in run for o in i[3]) else None)
    for l in sorted(blocks):
        for (off, mn, sz, ol, ln) in blocks[l][0]:
            try: effect(mn, sz, ol, a + off + ln if pos else None)
            except Exception as e: missing.append(f"{off} ({a + off:#x}): {e}")
    if missing:
        print("\n".join(missing)); sys.exit(1)
    for l in sorted(blocks):
        run, t, nx = blocks[l]
        if run:
            b = pkey(l)
            if b not in pats:
                k = len(pats); pats[b] = k
                if isfs(run): patF.add(k)
                elif b[1] is not None: patA.add(k)
                decs, ops, cons = [], [], []
                for (off, mn, sz, ol, ln) in run:
                    o = off - run[0][0]
                    terms, op, pf = effect(mn, sz, ol, a + off + ln if pos else None)
                    if k in patA and not pf.startswith("OpIA"): pf = f"({pf}).at _"
                    if k in patF and not pf.startswith("OpIF"):
                        pf = f"({pf}).fs _" if pf.startswith("OpIA") else f"(({pf}).at _).fs _"
                    decs.append(f"theorem p{k}_{o} : ∀ feat, Dec feat p{k} {o} (FV7z.mk {mnl(mn)} {sz} {terms} {ln}) := "
                                "by dec_rfl")
                    ops.append(op)
                    cons.append(f"  .cons (p{k}_{o} _) ({pf}) (by decide) <|")
                bst = (f"BlkF prof p{k} ({b[1]:#x} : Addr) fb" if k in patF else
                       f"BlkA prof p{k} ({b[1]:#x} : Addr)" if k in patA else f"Blk prof p{k}")
                ob, ou = (" (fb : Addr)", f"(o{k} fb)") if k in patF else ("", f"o{k}")
                P.append(f"/-- The stretch at `{l}`. -/\ndef p{k} : List Byte := [\n{rows(list(b[0]))}]\n\n"
                         + "\n".join(decs) + f"\n\n/-- What the stretch does. -/\ndef o{k}{ob} : List Op := [\n  "
                         + ",\n  ".join(ops) + f"]\n\ntheorem b{k} (prof : Profile){ob} : {bst} 0 {len(b[0])} {ou} :=\n"
                         + "\n".join(cons) + f"\n  .nil {len(b[0])}\n")
        if t is not None and t[1] != 'ret':
            b = bytes(bs[t[0]: t[0] + t[4]])
            if b not in jpats:
                k = len(jpats); jpats[b] = k
                (off, mn, sz, ol, ln) = t
                P.append(f"def j{k} : List Byte := [{', '.join(f'0x{x:02x}' for x in b)}]\n"
                         f"theorem j{k}_0 : ∀ feat, Dec feat j{k} 0 (FV7z.mk {mnl(mn)} {sz} [{operand(ol[0])[1]}] {ln}) := "
                         "by dec_rfl\n")
    open(out + "/Pats.lean", "w").write(f"""import FV7z.Lemmas.Sp{"Fs" if FSM else ""}
{"import FV7z.Lemmas.BlkOps12" + chr(10) if any(k in x for x in P for k in ("Op.cmpmr", "Op.testmi")) else ""}{"import FV7z.Lemmas.BlkOps11" + chr(10) if any(k in x for x in P for k in ("Op.rol64", "Op.ror64")) else ""}{"import FV7z.Lemmas.BlkOps10" + chr(10) if any("Op.cmpm 16" in x for x in P) else ""}{"import FV7z.Lemmas.BlkOps9" + chr(10) if any("Op.cmpma" in x for x in P) else ""}{"import FV7z.Lemmas.BlkOps8" + chr(10) if any(k in x for x in P for k in ("Op.vla", "Op.vsa", "Op.addma", "Op.cmpmia 8", "Op.stia 8")) else ""}{"import FV7z.Lemmas.BlkOps7" + chr(10) if any(k in x for x in P for k in ("Op.vl", "Op.vs", "Op.cdqe")) else ""}{"import FV7z.Lemmas.BlkOps6" + chr(10) if any(k in x for x in P for k in ("Op.stf8", "Op.stfi", "Op.xormf")) else ""}{("import FV7z.Lemmas.BlkOps5" if any("Op.ldsxb" in x for x in P) else
  "import FV7z.Lemmas.BlkOps4" if any("Op.imul64" in x for x in P) else
  "import FV7z.Lemmas.BlkOps3" if any(k in x for x in P for k in ("Op.shl64", "Op.shr64", "Op.sar64")) else
  "import FV7z.Lemmas.BlkOps2") + chr(10) if pos else ""}/-!
# The stretches of straight-line code of `{cn}` ({tag})

Each distinct stretch between labels and jumps (`p*`, {len(pats)} of them) and each distinct jump (`j*`, {len(jpats)}) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.{grp}
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

""" + "\n".join(P) + f"\nend FV7z.{grp}\n")

    # Blocks.lean
    B = []
    marks = []
    for l in sorted(blocks):
        marks.append(len(B))
        run, t, nx = blocks[l]
        e = run[-1][0] + run[-1][4] if run else l
        if run:
            k = pats[pkey(l)]
            B.append(f"theorem w_{l} : p{k} <+: {nm}.drop {l} := by decide +kernel\n" + (
                     f"theorem blk_{l} (prof : Profile) (fb : Addr) : BlkF prof {nm} {nm}_at fb {l} {e} (o{k} fb) :=\n"
                     f"  (b{k} prof fb).shift (by decide) w_{l}" if k in patF else
                     f"theorem blk_{l} (prof : Profile) : BlkA prof {nm} {nm}_at {l} {e} o{k} :=\n"
                     f"  (b{k} prof).shift (by decide) w_{l}" if k in patA else
                     f"theorem blk_{l} (prof : Profile) : Blk prof {nm} {l} {e} o{k} := (b{k} prof).shift w_{l}"))
        bk = "blkF" if run and k in patF else "blkA" if run and k in patA else "blk"
        ok, bl = (f"(o{k} fb)", f"blk_{l} prof fb") if run and k in patF else (f"o{k}" if run else "", f"blk_{l} prof")
        if t is None:
            B.append(f"theorem sp_{l} (prof : Profile){EB}{FB} : {SP} prof {nm}{EA}{FA} {l} fun F Wl Q => wp F Wl {ok} (Q {e}) :=\n"
                     f"  {SP}.{bk} ({bl})\n")
            continue
        (off, mn, sz, ol, ln) = t
        if mn == 'ret':
            B.append(f"/-- To the `ret` at `{off}`. -/\n"
                     f"theorem sp_{l} (prof : Profile){EB}{FB} : {SP} prof {nm}{EA}{FA} {l} fun F Wl Q => wp F Wl {ok} (Q {e}) :=\n"
                     f"  {SP}.{bk} ({bl})\n")
            continue
        jb = bytes(bs[off: off + ln]); jk = jpats[jb]
        B.append(f"theorem wj_{off} : j{jk} <+: {nm}.drop {off} := by decide +kernel")
        if jr(t):
            w = (f"∃ tgt, tgt < {nm}.length ∧ g.get (regOf {operand(ol[0])[2][1]}) = Addr.add{EA} tgt ∧ "
                 "Q tgt g (rfz f) V")
            B.append(f"theorem spj_{off} (prof : Profile){EB}{FB} : {SP} prof {nm}{EA}{FA} {off} fun _ _ Q g f V =>\n"
                     f"    {w} :=\n  {FS0}Sp.jmpr (Dec.shift (j{jk}_0 _) wj_{off} (by decide)) (lt_len (by decide)){FS1}")
            assert run
            B.append(f"theorem sp_{l} (prof : Profile){EB}{FB} : {SP} prof {nm}{EA}{FA} {l} fun F Wl Q => wp F Wl {ok} fun g f V =>\n"
                     f"    {w} :=\n  {SP}.{bk}_then ({bl}) (spj_{off} prof{ER}{FA})\n")
            continue
        tg = tgt(t)
        if mn == 'jmp':
            w = f"Q {tg} g (rfz f) V"
            rule = "Sp.jmp"
        else:
            cc = mn.split()[1]
            w = f"(f.cond {cc} = true → Q {tg} g (rfz f) V) ∧ (f.cond {cc} = false → Q {nx} g (rfz f) V)"
            rule = "Sp.jcc"
        B.append(f"theorem spj_{off} (prof : Profile){EB}{FB} : {SP} prof {nm}{EA}{FA} {off} fun _ _ Q g f V =>\n"
                 f"    {w} :=\n  {FS0}{rule} (j := {off}) (tgt := {tg}) (Dec.shift (j{jk}_0 _) wj_{off} (by decide)) "
                 f"(lt_len (by decide)) (by decide) (lt_len (by decide)){FS1}")
        if run:
            B.append(f"theorem sp_{l} (prof : Profile){EB}{FB} : {SP} prof {nm}{EA}{FA} {l} fun F Wl Q => wp F Wl {ok} fun g f V =>\n"
                     f"    {w} :=\n  {SP}.{bk}_then ({bl}) (spj_{off} prof{ER}{FA})\n")
        else:
            B.append("")
    # in parts: the kernel's memory for the evaluations adds up within a file
    PART = 40
    cuts_at = marks[::PART] + [len(B)]
    nparts = len(cuts_at) - 1
    for i in range(nparts):
        imp = f"import FV7z.{cgrp}.Code\nimport FV7z.{grp}.Pats\n" + (f"import FV7z.{grp}.Blocks1\n" if i else "")
        head = (f"theorem lt_len {{j : Nat}} (h : j < {n}) : j < {nm}.length := {nm}_length ▸ h\n\n" if i == 0 else "")
        open(out + f"/Blocks{i + 1}.lean", "w").write(imp + f"""/-!
# The basic blocks of `{cn}`, part {i + 1} of {nparts} ({tag})

Generated by `tools/blk_gen.py`; see `Blocks.lean`.
-/
namespace FV7z.{grp}
set_option maxRecDepth 100000
open ZellicX86 Decode FV7z.Leaf
{OPN}
""" + head + "\n".join(B[cuts_at[i]:cuts_at[i + 1]]) + f"\nend FV7z.{grp}\n")
    open(out + "/Blocks.lean", "w").write("".join(f"import FV7z.{grp}.Blocks{i + 1}\n" for i in range(nparts)) + f"""/-!
# The basic blocks of `{cn}` ({tag})

Where the stretches of `Pats.lean` lie in the code (`w_*`, `wj_*`: a prefix of the code from an offset, by the kernel's
evaluation), and for each of the {len(blocks)} basic blocks that the entry reaches an `Sp` (`sp_*`, by the block's offset): what
its straight-line code needs (`wp`) for `Q` at its jump's exits. In {nparts} parts, `Blocks1.lean` to `Blocks{nparts}.lean`: the
kernel's memory for the evaluations adds up within a file. Generated by `tools/blk_gen.py`.
-/
"""
)
    # Cuts.lean: the cut points, and from each the blocks up to the next ones as one piece
    refills = {r for (r, e) in heads.values()}
    for h, (r, e) in heads.items():
        if h not in blocks: continue
        run, t, nx = blocks[r]
        assert len(run) == 4 and (nx == e if t is None else t[1] == 'jmp' and tgt(t) == e), h
        assert blocks[h][0][-1][0] == h and len(blocks[h][0]) == 1

    def succs(l):
        if l in heads: return [heads[l][1]]
        run, t, nx = blocks[l]
        if t is None: return [nx]
        if jr(t): return []
        m = t[1].split()[0]
        return [tgt(t)] if m == 'jmp' else [tgt(t), nx] if m == 'jcc' else []
    nodes = [l for l in sorted(blocks) if l not in refills]
    npred = {}
    for l in nodes:
        for s in succs(l): npred[s] = npred.get(s, 0) + 1
    cuts = sorted({E0} | {heads[h][1] for h in heads if h in blocks}
                  | {l for l in nodes if l not in heads and npred.get(l, 0) >= 2} | (set(jtg) & set(nodes))
                  | ({callat[c] for c in called} & set(nodes)))
    cutset = set(cuts)
    C, done, size = [], set(), {}

    def at(j, fl):
        """(what is needed at exit `j`, its `Sp`)"""
        if j in heads: return f"Wnorm {heads[j][1]} F Wl Q g {fl} V", f"(c_{j} prof{ER})"
        if j in cutset or j not in blocks: return f"Q {j} g {fl} V", f"({SP}.skip {j})"
        return f"W_{j}{FA} F Wl Q g {fl} V", f"(c_{j} prof{ER}{FA})"

    wl = lambda l: f"(W_{l} fb)" if FSM else f"W_{l}"

    def emit(l):
        if l in done: return 0
        done.add(l)
        if l in heads:
            r, e = heads[l]
            C.append(f"theorem c_{l} (prof : Profile){EB} : Sp prof {nm}{EA} {l} (Wnorm {e}) :=\n"
                     f"  Sp.norm (by decide) (sp_{l} prof{ER}) ((sp_{r} prof{ER}).mono fun _ _ _ _ _ _ h => "
                     f"wp_mono _ (fun _ _ _ h => h _) h)\n")
            return 1
        run, t, nx = blocks[l]
        ss = [s for s in succs(l) if s in blocks and s not in cutset]
        sz = 1 + sum(emit(s) for s in ss)
        size[l] = sz
        k = pats[pkey(l)] if run else None
        bk = "blkF" if run and k in patF else "blkA" if run and k in patA else "blk"
        ok, bl = (f"(o{k} fb)", f"blk_{l} prof fb") if run and k in patF else (f"o{k}", f"blk_{l} prof")
        if t is None or t[1] == 'ret':
            e = nx if t is None else t[0]
            w, s = at(e, "f")
            w = w[:-len(" g f V")]
            C.append(f"def W_{l}{FB} : Wpt := fun F Wl Q => wp F Wl {ok} ({w})\n"
                     f"theorem c_{l} (prof : Profile){EB}{FB} : {SP} prof {nm}{EA}{FA} {l} {wl(l)} :="
                     f"{chr(10) + ' ' if FSM else ''} {SP}.{bk}_then ({bl}) {s}\n")
            return sz
        m = t[1].split()[0]
        if jr(t):
            body = (f"∃ tgt, tgt < {nm}.length ∧ g.get (regOf {operand(t[3][0])[2][1]}) = Addr.add{EA} tgt ∧ "
                    "Q tgt g (rfz f) V")
            sp = f"spj_{t[0]} prof{ER}{FA}"
        elif m == 'jmp':
            w, s = at(tgt(t), "(rfz f)")
            body, sp = w, f"{SP}.jmp_then (spj_{t[0]} prof{ER}{FA}) {s}"
        else:
            cc = t[1].split()[1]
            w1, s1 = at(tgt(t), "(rfz f)"); w2, s2 = at(nx, "(rfz f)")
            body = f"(f.cond {cc} = true → {w1}) ∧\n    (f.cond {cc} = false → {w2})"
            sp = f"{SP}.jcc_then (spj_{t[0]} prof{ER}{FA}) {s1} {s2}"
        if run:
            C.append(f"def W_{l}{FB} : Wpt := fun F Wl Q => wp F Wl {ok} fun g f V =>\n    {body}\n"
                     f"theorem c_{l} (prof : Profile){EB}{FB} : {SP} prof {nm}{EA}{FA} {l} {wl(l)} :=\n"
                     f"  {SP}.{bk}_then ({bl}) ({sp})\n")
        else:
            C.append(f"def W_{l}{FB} : Wpt := fun F Wl Q g f V =>\n    {body}\n"
                     f"theorem c_{l} (prof : Profile){EB}{FB} : {SP} prof {nm}{EA}{FA} {l} {wl(l)} :=\n  {sp}\n")
        return sz
    for l in cuts: emit(l)
    assert done == set(nodes), sorted(set(nodes) - done)
    chain = "".join(f"  if ℓ = {l} then W_{l}{FA} else\n" for l in cuts)
    tab = "".join(f"  {SP}.table (c_{l} prof{ER}{FA}) <|\n" for l in cuts)
    cutdoc = (f"""The {len(cuts)} cut points: the entry, where a normalization of the range coder ends, and where two ways meet. From each,
the blocks up to the next cut points as one piece (`W_*`, with its `Sp`, `c_*`): a block's straight-line code, then at
its jump's exits the next block's condition, or `Q` at a cut point; a normalization is `Wnorm` (`Norm.lean`). `Wt` is
the table of the cut points' conditions, `spAll` its `Sp`s, for `Seg.cfg`. Generated by `tools/blk_gen.py`.""" if heads else
              f"""The {len(cuts)} cut points: the entry and where two ways meet. From each, the blocks up to the next cut points as one
piece (`W_*`, with its `Sp`, `c_*`): a block's straight-line code, then at its jump's exits the next block's condition,
or `Q` at a cut point or at an offset the proof does not go past ({", ".join(str(x) for x in sorted(stops))}; the `ret`). `Wt` is the table of the cut
points' conditions, `spAll` its `Sp`s, for `Seg.cfg`. Generated by `tools/blk_gen.py`.""")
    if max(len(x) for x in cutdoc.split("\n")) > 120:
        cutdoc = textwrap.fill(cutdoc, 120)
    open(out + "/Cuts.lean", "w").write(f"""import FV7z.{grp}.Blocks
{"import FV7z." + grp + ".Norm" if heads else "import FV7z.Lemmas.Wp"}
/-!
# The cut points of `{cn}` ({tag})

{cutdoc}
-/
namespace FV7z.{grp}
set_option linter.unusedVariables false
open ZellicX86 Decode FV7z.Leaf
{OPN}
""" + "\n".join(C) + f"""
/-- The cut points. -/
def cuts : List Nat := [{', '.join(map(str, cuts))}]

/-- What the code from a cut point needs for `Q` at the next ones. -/
def Wt{FB} (ℓ : Nat) : Wpt :=
{chain}  fun _ _ _ _ _ _ => False

theorem spAll (prof : Profile){EB}{FB} (ℓ : Nat) : {SP} prof {nm}{EA}{FA} ℓ (Wt{FA} ℓ) :=
{tab}  {SP}.never ℓ

end FV7z.{grp}
""")
    print(f"{len(ins)} instructions, {len(blocks)} blocks, {len(pats)} stretches, {len(jpats)} jumps, "
          f"{len(heads)} normalizations, {len(cuts)} cut points")
    print("blocks from each cut point:", " ".join(f"{l}:{size[l]}" for l in cuts))


main()
