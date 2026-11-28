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
# `tag`, `src`: for the files' headers; `cut`: more cut points, to split the proof.
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
    # glibc 2.31 sysdeps/unix/sysv/linux/close.c (`SYSCALL_CANCEL`). Stops: the `ret` (0x1f), the process has more
    # than one thread (0x20: `multiple_threads` is not 0), the `ret` after `errno` is set (0x71); the `syscall` (0x15)
    # is a step of its own.
    "cls": dict(grp="Close", cn="__close", a=0x5ff3b0, n=0x85, pos=True, fs=True, stops=(0x1f, 0x20, 0x71), calls=True,
                tag="PLAN.md §M, M1", src="glibc 2.31's `__close` (`sysdeps/unix/sysv/linux/close.c`; `objdump -d`)"),
    # glibc 2.31 sysdeps/unix/sysv/linux/read.c (`SYSCALL_CANCEL`). Stops: the `ret` (0x1a), the process has more
    # than one thread (0x20: `multiple_threads` is not 0), the `ret` after `errno` is set (0x83); the `syscall` (0x10)
    # is a step of its own (`eax` is 0, `read`'s number, from the `test` of `multiple_threads`).
    "rd": dict(grp="Read", cn="__libc_read", a=0x5ff310, n=0x99, pos=True, fs=True, stops=(0x1a, 0x20, 0x83), calls=True,
               tag="PLAN.md §M, M1", src="glibc 2.31's `__libc_read` (`sysdeps/unix/sysv/linux/read.c`; `objdump -d`)"),
    # glibc 2.31 sysdeps/unix/sysv/linux/_exit.c (`_Exit`): `exit_group`, then (never, as the run ends there) `exit`
    # and `hlt`. Stop: after the `syscall` `exit_group` (0x36); the `syscall` (0x34) is a step of its own.
    "ext": dict(grp="Exit", cn="_Exit", a=0x664a70, n=0x58, pos=True, fs=True, stops=(0x36,), calls=True,
                tag="PLAN.md §M, M1", src="glibc 2.31's `_Exit` (`sysdeps/unix/sysv/linux/_exit.c`; `objdump -d`)"),
    # glibc 2.31 sysdeps/unix/sysv/linux/lseek64.c via syscall-template.S (`__libc_lseek`). Stops: the `ret` (0x13),
    # the padding after it (0x14), the `ret` after `errno` is set (0x2b); the `syscall` (9) is a step of its own.
    "lsk": dict(grp="Lseek", cn="__libc_lseek", a=0x5ff440, n=0x2c, pos=True, fs=True, stops=(0x13, 0x14, 0x2b),
                calls=True, tag="PLAN.md §M, M1",
                src="glibc 2.31's `__libc_lseek` (`sysdeps/unix/sysv/linux/syscall-template.S`; `objdump -d`)"),
    # glibc 2.31 sysdeps/unix/sysv/linux/getdents64.c (`__getdents64`, aliased `__getdents` on x86_64): `count` capped
    # at `INT_MAX` (`cmova`), then `getdents64` (217) as is: no conversion of the entries. Stops: the `ret` (0x23), the
    # padding after it (0x24), the `ret` after `errno` is set (0x3b); the `syscall` (0x19) is a step of its own.
    # glibc 2.31 malloc/malloc.c (`__libc_calloc`), the way of one thread with `__malloc_hook` null and the tcache
    # made: `n * m` (`mul`, no overflow), the top chunk's size read, `_int_malloc (&main_arena, n)` (0x7b), the chunk
    # of the main arena, not mmapped, `perturb_byte` 0, the size to clear (`min` with the old top's size when the
    # chunk is the old top), cleared inline (to 72 bytes) or by `memset` (0x2cd). Stops: the `ret` (0xd1), the padding
    # after it (0xd2), the product too big (0x190), `_int_malloc` gave null (0x1b0), the hook set (0x1c0), more than
    # one thread (0x1f0, 0x260), no tcache (0x240), mmapped and `perturb_byte` set (0x2e0), not of the main arena
    # (0x13b), the asserts (0x151, 0x366).
    "cal": dict(grp="Cal", cn="__libc_calloc", a=0x634a60, n=901, pos=True, fs=True,
                stops=(0xd1, 0xd2, 0x190, 0x1b0, 0x1c0, 0x1f0, 0x260, 0x240, 0x2e0, 0x13b, 0x151, 0x366), calls=True,
                tag="PLAN.md §M, M1", src="glibc 2.31's `__libc_calloc` (`malloc/malloc.c`; `objdump -d`)"),
    # glibc 2.31 malloc/malloc.c (`unlink_chunk`, `av` dropped by IPA-SRA: `rdi` = p): the size checked against the
    # next chunk's `prev_size`, `fd->bk == p` and `bk->fd == p` checked, `p` taken out of its bin; for a large chunk
    # (size over 0x3ff) with `fd_nextsize` set, the `nextsize` list too, after its checks. Stops: the `ret` (0x6e),
    # the padding (0x6f, 0x99, 0xac), the calls of `malloc_printerr` (0xa0, 0xbf, 0xcb: corruption).
    "ulk": dict(grp="Ulk", cn="unlink_chunk.isra.0", a=0x62ea20, n=215, pos=True, fs=True,
                stops=(0x6e, 0x6f, 0x99, 0xa0, 0xac, 0xbf, 0xcb), calls=True,
                tag="PLAN.md §M, M1", src="glibc 2.31's `unlink_chunk` (`malloc/malloc.c`; `objdump -d`)"),
    # glibc 2.31 malloc/malloc.c (`munmap_chunk`): the chunk mmapped (else the assert, 0x7c), its block page-aligned
    # (else `malloc_printerr`, 0x70), `mp_.n_mmaps` and `mp_.mmapped_mem` updated (`lock`), then the tail call of
    # `__munmap (p - prev_size, prev_size + size)`. Stops: the `jmp` to `__munmap` (0x63), the padding (0x68), the
    # failures (0x70, 0x7c).
    "mck": dict(grp="Mck", cn="munmap_chunk", a=0x62e660, n=155, pos=True, fs=True, stops=(0x63, 0x68, 0x70, 0x7c),
                calls=True, hand=(0x47, 0x54), tag="PLAN.md §M, M1",
                src="glibc 2.31's `munmap_chunk` (`malloc/malloc.c`; `objdump -d`)"),
    # glibc 2.31 malloc/malloc.c (`systrim`, for `main_arena`: `rdi` = pad): the bytes to give back from the top
    # chunk, a page multiple; `MORECORE (0)` through `__morecore` (0x33); if the top ends at the break,
    # `MORECORE (-extra)` (0x5e), `__after_morecore_hook` if set (0xa8), `MORECORE (0)` again (0x72) and the top and
    # `system_mem` made smaller. Stops: the `ret` (0x51), the padding (0x52, 0xa3).
    "stm": dict(grp="Stm", cn="systrim.isra.0.constprop.0", a=0x62f8e0, n=172, pos=True, fs=True,
                stops=(0x51, 0x52, 0xa3), calls=True, hand=(0x8d,),
                tag="PLAN.md §M, M1", src="glibc 2.31's `systrim` (`malloc/malloc.c`; `objdump -d`)"),
    # glibc 2.31 malloc/malloc.c (`malloc_consolidate (av)`): `have_fastchunks` cleared, each of the ten fastbins
    # emptied (`xchg`, 0x27) and its chunks merged with free neighbours (`unlink_chunk`, 0xf7, 0x12a) into the top
    # chunk or the unsorted bin (the `xmm` stores 0x7b, 0x94). Stops: the `ret` (0x49), the padding (0x4a, 0x11b,
    # 0x13c), the calls of `malloc_printerr` (0x140, 0x14c). By hand: `xchg` (0x27), `and qword [m], -2` (0x5c),
    # `pxor` (0x77), the `xmm` moves (0x7b, 0x82, 0x8b, 0x94).
    "mcn": dict(grp="Mcn", cn="malloc_consolidate", a=0x62eb00, n=344, pos=True, fs=True,
                stops=(0x49, 0x4a, 0x11b, 0x13c, 0x140, 0x14c), calls=True,
                hand=(0x27, 0x5c, 0x77, 0x7b, 0x82, 0x8b, 0x94),
                tag="PLAN.md §M, M1", src="glibc 2.31's `malloc_consolidate` (`malloc/malloc.c`; `objdump -d`)"),
    # glibc 2.31 malloc/malloc.c (`_int_memalign (av, alignment, bytes)`): the request size `nb`, `_int_malloc (av,
    # nb + alignment + MINSIZE)` (0x3a), the chunk cut at the first aligned spot (`div`, 0x51) with the leader given
    # back by `_int_free` (0xd8) and the tail past `nb` too (0x150). Stops: the `ret` (0x166), the padding (0x167,
    # 0x183, 0x196), the failed `assert` (0x1b7). By hand: `or qword [r13 + r14 + 8], 1` (0xba).
    "mga": dict(grp="Mga", cn="_int_memalign", a=0x631bc0, n=470, pos=True, fs=True,
                stops=(0x166, 0x167, 0x183, 0x196, 0x1b7), calls=True, hand=(0xba,),
                tag="PLAN.md §M, M1", src="glibc 2.31's `_int_memalign` (`malloc/malloc.c`; `objdump -d`)"),
    # glibc 2.31 iconv/gconv_cache.c `find_module_idx (str, idxp)`: `__hash_string (str)` (the `call`, 0x2e), the
    # probes of the cache's hash table from `hval % hash_size` by `1 + hval % (hash_size - 2)`, `strcmp` (the
    # `call` through the PLT, 0x76) of each name inside the string table. Stops: the `ret`s (0xba: an empty slot,
    # -1; 0xdb: found, `*idxp` set, 0).
    "fmi": dict(grp="Fmi", cn="find_module_idx", a=0x67ce30, n=220, pos=True, stops=(0xba, 0xdb), calls=True,
                tag="PLAN.md §M, M1", src="glibc 2.31's `find_module_idx` (`iconv/gconv_cache.c`; `objdump -d`)"),
    # glibc 2.31 intl/l10nflist.c `_nl_normalize_codeset (codeset, name_len)`: the count of the name's alphanumerics
    # and whether all are digits (the loop at 0x30, `__ctype_b` at 0x7914c8), `malloc` (the `call`s, 0x5b, 0xc4,
    # 0xf5), "iso" before an all-digit name, then the copy of the alphanumerics, letters lowered by `__ctype_tolower`
    # (0x7914d0; the loop at 0x8c). Stops: the `ret`s (0xbe: the new name; 0xea: `malloc` failed, 0).
    "nlc": dict(grp="Nlc", cn="_nl_normalize_codeset", a=0x619f30, n=271, pos=True, stops=(0xbe, 0xea), calls=True,
                tag="PLAN.md §M, M1", src="glibc 2.31's `_nl_normalize_codeset` (`intl/l10nflist.c`; `objdump -d`)"),
    "gdn": dict(grp="Gdn", cn="__getdents", a=0x6a2820, n=0x3c, pos=True, fs=True, stops=(0x23, 0x24, 0x3b),
                calls=True, tag="PLAN.md §M, M1",
                src="glibc 2.31's `__getdents` (`sysdeps/unix/sysv/linux/getdents64.c`; `objdump -d`)"),
    # glibc 2.31 sysdeps/unix/sysv/linux/close_nocancel.c via INLINE_SYSCALL (`__close_nocancel`). Stops: the `ret`
    # (0x13), the padding after it (0x14), the `ret` after `errno` is set (0x29); the `syscall` (9) is a step of its own.
    "cnc": dict(grp="Cnc", cn="__close_nocancel", a=0x665f20, n=42, pos=True, fs=True, stops=(0x13, 0x14, 0x29),
                calls=True, tag="PLAN.md §M, M1",
                src="glibc 2.31's `__close_nocancel` (`sysdeps/unix/sysv/linux/close_nocancel.c`; `objdump -d`)"),
    # 7-Zip 26.06's `AddRef`s of three classes (`Z7_COM_ADDREF_RELEASE`, `CPP/Common/MyCom.h`): the reference
    # count at `this + d` incremented and returned. Stop: the `ret` (13).
    "ar1": dict(grp="Ar1", cn="CArchiveExtractCallback::AddRef", a=0x5b20e0, n=14, pos=True, stops=(13,),
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `CArchiveExtractCallback::AddRef` (`MyCom.h`; `objdump -d`)"),
    "ar4": dict(grp="Ar4", cn="CExtractCallbackConsole::AddRef", a=0x5ea370, n=20, pos=True, stops=(19,),
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `CExtractCallbackConsole::AddRef` (`MyCom.h`; `objdump -d`)"),
    # 7-Zip's CPP/Windows/TimeUtils.cpp `UnixTime64_To_FileTime64 (unixTime)`: `(unixTime + 11644473600) * 10^7`.
    "utf": dict(grp="Utf", cn="NWindows::NTime::UnixTime64_To_FileTime64", a=0x458880, n=25, pos=True, stops=(24,),
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `UnixTime64_To_FileTime64` (`TimeUtils.cpp`; `objdump -d`)"),
    # `CriticalSection_Delete` by the symbol table (C/Threads.c): nothing for a null pointer, else a tail jump to
    # glibc's `__pthread_mutex_lock`. Stops: the jump (9), the `ret` (16).
    "csd": dict(grp="Csd", cn="CriticalSection_Delete", a=0x448b60, n=17, pos=True, stops=(9, 16),
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `CriticalSection_Delete` (`C/Threads.c`; `objdump -d`)"),
    # The second `CriticalSection_Delete` of the symbol table (0x448b80): the same code as `csd`, the tail jump to
    # glibc's `__pthread_mutex_unlock`. Stops: the jump (9), the `ret` (16).
    "csx": dict(grp="Csx", cn="CriticalSection_Delete (0x448b80)", a=0x448b80, n=17, pos=True, stops=(9, 16),
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `CriticalSection_Delete` (`C/Threads.c`; `objdump -d`)"),
    # 7-Zip's CPP/7zip/Common/StreamUtils.cpp `InStream_SeekToBegin (stream)`: `stream->Seek (0, STREAM_SEEK_SET,
    # NULL)` as a tail jump through the vtable (`jmp rax`). Stop: the jump (17).
    "isb": dict(grp="Isb", cn="InStream_SeekToBegin", a=0x4631e0, n=19, pos=True, stops=(17,),
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `InStream_SeekToBegin` (`StreamUtils.cpp`; `objdump -d`)"),
    # 7-Zip's CPP/7zip/UI/Common/ArchiveExtractCallback.cpp `CArchiveExtractCallback::SetRatioInfo`: forwarded to
    # `_compressProgress->SetRatioInfo` (at `this + 552`) by a tail jump through its vtable. Stop: the jump (14).
    "sri": dict(grp="Sri", cn="CArchiveExtractCallback::SetRatioInfo", a=0x5aa190, n=17, pos=True, stops=(14,),
                tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `CArchiveExtractCallback::SetRatioInfo` (`ArchiveExtractCallback.cpp`; `objdump -d`)"),
    # The thunk of `CArchiveExtractCallback::SetRatioInfo` for its `ICompressProgressInfo` base: `this` - 24, then a
    # jump to `sri` (0x5aa190). Stop: the jump (8).
    "srt": dict(grp="Srt", cn="CArchiveExtractCallback::SetRatioInfo (thunk)", a=0x5aa1b0, n=10, pos=True, stops=(8,),
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `SetRatioInfo` thunk (`objdump -d`)"),
    # 7-Zip's CPP/7zip/UI/Common/OpenArchive.cpp `Archive_IsItem_Dir (arc, index, result)`: a tail jump to
    # `Archive_GetItemBoolProp (arc, index, kpidIsDir, result)` (0x5d15e0). Stop: the jump (12).
    "aid": dict(grp="Aid", cn="Archive_IsItem_Dir", a=0x5d1670, n=17, pos=True, stops=(12,),
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `Archive_IsItem_Dir` (`OpenArchive.cpp`; `objdump -d`)"),
    # 7-Zip's CPP/7zip/UI/Console/OpenCallbackConsole.cpp `COpenCallbackConsole::Open_SetTotal (files, bytes)`: the
    # totals into the percent printer when it is on, then `CheckBreak2 ()` (`NConsoleClose::g_BreakCounter` at
    # 0x79f088). Stop: the `ret` (0x4f).
    "ost": dict(grp="Ost", cn="COpenCallbackConsole::Open_SetTotal", a=0x5f65b0, n=0x7d, pos=True, stops=(0x4f,),
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `Open_SetTotal` (`OpenCallbackConsole.cpp`; `objdump -d`)"),
    # 7-Zip's CPP/7zip/UI/Console/ConsoleClose.cpp `CCtrlHandlerSetter::~CCtrlHandlerSetter ()`: `signal (SIGINT,
    # memo_sig_int)` (the `call`, 16; a cut after it) and `signal (SIGTERM, memo_sig_term)` as a tail jump. Stop: the
    # `jmp` (31).
    "chd": dict(grp="Chd", cn="CCtrlHandlerSetter::~CCtrlHandlerSetter", a=0x5e77a0, n=36, pos=True, stops=(31,),
                calls=True, tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `~CCtrlHandlerSetter` (`ConsoleClose.cpp`; `objdump -d`)"),
    # 7-Zip's C/LzmaDec.c `LzmaDec_FreeProbs (p, alloc)`: `ISzAlloc_Free (alloc, p->probs); p->probs = NULL`, the
    # free through `alloc->Free` (`call [rax + 8]`, 18; a cut after it). Stop: the `ret` (30).
    # 7-Zip's C/LzmaDec.c `LzmaDec_Free (p, alloc)`: `LzmaDec_FreeProbs (p, alloc)` (16), then
    # `ISzAlloc_Free (alloc, p->dic)` (28), `p->dic` = NULL. Stop: the `ret` (45).
    "ldf": dict(grp="Ldf", cn="LzmaDec_Free", a=0x42be70, n=46, pos=True, stops=(45,), calls=True,
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `LzmaDec_Free` (`C/LzmaDec.c`; `objdump -d`)"),
    # 7-Zip's C/LzmaDec.c `LzmaDec_AllocateProbs2 (p, propNew, alloc)` (`lc` = esi, `lp` = edx): `numProbs` = 0x7c0 +
    # (0x300 << (lc + lp)); the same `probs` kept (0x26 to 0x57), else `LzmaDec_FreeProbs` (0x2e), `alloc->Alloc`
    # (0x3b), SZ_ERROR_MEM on NULL (0x60). Stop: the `ret` (0x5b).
    # 7-Zip's C/LzmaDec.c `LzmaDec_TryDummy (p, buf, bufOut)`: the range decoder's dry run of one symbol from `buf`
    # up to `*bufOut`, reading the probabilities, `dic` and the input, storing only `*bufOut` (the end of the
    # symbol). Stops: the two `ret`s (354, 765).
    "tdm": dict(grp="Tdm", cn="LzmaDec_TryDummy", a=0x42af80, n=1570, pos=True, stops=(354, 765),
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `LzmaDec_TryDummy` (`C/LzmaDec.c`; `objdump -d`)"),
    # 7-Zip's C/LzmaDec.c `LzmaDec_DecodeReal2 (p, limit, bufLimit)`: with `checkDicSize` (the 4 bytes at `p + 0x44`)
    # 0, `limit` cut to `dicPos + (dicSize - processedPos)`; `LZMA_DECODE_REAL` (call, 40, to `0x6d4040`); then
    # `checkDicSize` = `dicSize` once `processedPos` reaches it. Stop: the `ret` (64).
    "dr2": dict(grp="Dr2", cn="LzmaDec_DecodeReal2", a=0x42b5b0, n=65, pos=True, stops=(64,), calls=True,
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `LzmaDec_DecodeReal2` (`C/LzmaDec.c`; `objdump -d`)"),
    "lap": dict(grp="Lap", cn="LzmaDec_AllocateProbs2", a=0x42be00, n=103, pos=True, stops=(0x5b,), calls=True,
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `LzmaDec_AllocateProbs2` (`C/LzmaDec.c`; `objdump -d`)"),
    "lfp": dict(grp="Lfp", cn="LzmaDec_FreeProbs", a=0x42bde0, n=31, pos=True, stops=(30,), calls=True,
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `LzmaDec_FreeProbs` (`C/LzmaDec.c`; `objdump -d`)"),
    # 7-Zip's C/LzmaDec.c `LzmaDec_InitDicAndState (p, initDic, initState)`: `remainLen` = kMatchSpecLenStart + 1,
    # `tempBufSize` = 0, and with `initDic` `processedPos` = `checkDicSize` = 0 and `remainLen` + 1; with `initState`
    # `remainLen` + 1. Stop: the `ret` (48).
    "lid": dict(grp="Lid", cn="LzmaDec_InitDicAndState", a=0x42b600, n=49, pos=True, stops=(48,),
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `LzmaDec_InitDicAndState` (`C/LzmaDec.c`; `objdump -d`)"),
    # 7-Zip's CPP/7zip/UI/Common/OpenArchive.h `CArcErrorInfo::ClearErrors ()`: the flags and the tail size 0, the
    # two `UString`s emptied (length 0, first character 0). Stop: the `ret` (60).
    "cle": dict(grp="Cle", cn="CArcErrorInfo::ClearErrors", a=0x5d2b40, n=61, pos=True, stops=(60,),
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `CArcErrorInfo::ClearErrors` (`OpenArchive.h`; `objdump -d`)"),
    # 7-Zip's CPP/7zip/Archive/Base64Handler.cpp (by the symbol table `NArchive::NGz::CHandler`)
    # `GetArchivePropertyInfo (index, name, propID, varType)`: E_INVALIDARG for an index past 1, else the property's
    # id and type from the tables and `name` = NULL. Stops: the two `ret`s (48, 61).
    "gpi": dict(grp="Gpi", cn="CHandler::GetArchivePropertyInfo", a=0x49e900, n=62, pos=True, stops=(48, 61),
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `GetArchivePropertyInfo` (`Base64Handler.cpp`; `objdump -d`)"),
    # 7-Zip's CPP/7zip/UI/Common/DirItem.h `CDirItems::CDirItems ()`: 0 in the object's fields (24 qword stores, a
    # dword at 64, bytes at 68 and 184). Stop: the `ret` (229).
    "cdi": dict(grp="Cdi", cn="CDirItems::CDirItems", a=0x5c0830, n=230, pos=True, stops=(229,),
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `CDirItems` constructor (`DirItem.h`; `objdump -d`)"),
    # 7-Zip's CPP/7zip/Common/ProgressUtils.cpp `CLocalProgress::CLocalProgress ()`: the vtable pointer at 0, 0 in
    # the 4 bytes at 8 and the 8 bytes at 16, 24, 32, 40, 48, 1 in the bytes at 12 and 13. Stop: the `ret` (74).
    "lpc": dict(grp="Lpc", cn="CLocalProgress::CLocalProgress", a=0x461fa0, n=75, pos=True, stops=(74,),
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `CLocalProgress` constructor (`ProgressUtils.cpp`; `objdump -d`)"),
    # 7-Zip's CPP/Windows/FileFind.cpp `CFileInfoBase::ClearBase ()`: size, the times, the attributes and the rest of
    # the base fields 0 (12 qword stores and a dword at 72). Stop: the `ret` (106).
    "cfb": dict(grp="Cfb", cn="CFileInfoBase::ClearBase", a=0x4558d0, n=107, pos=True, stops=(106,),
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `CFileInfoBase::ClearBase` (`FileFind.cpp`; `objdump -d`)"),
    # 7-Zip's CPP/7zip/Compress/LzmaDecoder.cpp `CDecoder::ReleaseInStream ()`: `_inStream.Release ()`, the
    # `Release` through the vtable (`call [rax + 16]`, 23; a cut after it) when `_inStream` (at `this + 256`) is set,
    # then 0 (`S_OK`). Stop: the `ret` (40).
    "ris": dict(grp="Ris", cn="CDecoder::ReleaseInStream", a=0x57f930, n=41, pos=True, stops=(40,), calls=True,
                tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `CDecoder::ReleaseInStream` (`LzmaDecoder.cpp`; `objdump -d`)"),
    # 7-Zip's CPP/Common/Wildcard.cpp `CCensorNode::NeedCheckSubDirs ()`: over `SubNodes` (items at `this + 40`,
    # count at `this + 48`), true at the first node with `ExcludeDirItems` (the byte at 16) set or more than one
    # `IncludeItems` (the count at 8). Stops: the `ret`s (63, 73).
    "ncs": dict(grp="Ncs", cn="CCensorNode::NeedCheckSubDirs", a=0x452fa0, n=79, pos=True, stops=(63, 73),
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `CCensorNode::NeedCheckSubDirs` (`Wildcard.cpp`; `objdump -d`)"),
    # 7-Zip's CPP/Common/MyString.cpp `UString::ReverseFind (c)`: from the end of the characters (at `this`, the
    # length at `this + 8`) back to the first, the index of the last 4-byte character equal to `c` (`esi`), else -1.
    # Stops: the `ret`s (44, 53).
    "rfw": dict(grp="Rfw", cn="UString::ReverseFind", a=0x44dd40, n=54, pos=True, stops=(44, 53),
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `UString::ReverseFind` (`MyString.cpp`; `objdump -d`)"),
    # 7-Zip's CPP/Common/MyString.cpp `UString::ReverseFind_PathSepar ()`: as `ReverseFind ('/')`. Stops: the `ret`s
    # (35, 47).
    "rpp": dict(grp="Rpp", cn="UString::ReverseFind_PathSepar", a=0x44dd80, n=48, pos=True, stops=(35, 47),
                tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `UString::ReverseFind_PathSepar` (`MyString.cpp`; `objdump -d`)"),
    # 7-Zip's CPP/7zip/UI/Common/OpenArchive.cpp `GetOpenArcErrorFlags (prop, isDefinedProp)`: the flags of a
    # `VT_UI4`/`VT_UI8` (0x13, 0x15) property, 0 for `VT_EMPTY`, `*isDefinedProp` set when not NULL; any other type
    # throws (the jumps to 0x4176fe, 64 and 89). Stops: the `ret`s (42, 58), the jumps (64, 89).
    "gae": dict(grp="Gae", cn="GetOpenArcErrorFlags", a=0x5d2ae0, n=94, pos=True, stops=(42, 58, 64, 89),
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `GetOpenArcErrorFlags` (`OpenArchive.cpp`; `objdump -d`)"),
    # 7-Zip's CPP/Windows/FileFind.cpp `NFind::DoesDirExist (name, followLink)`: a frame of 168 bytes with the stack
    # guard at `rsp + 152`, `MY_lstat (name, &st, followLink)` (call at 0x25), `S_ISDIR (st.st_mode)`, the guard's
    # check. Stops: the `ret` (0x5f), the call of `__stack_chk_fail` (0x60).
    "dde": dict(grp="Dde", cn="NWindows::NFile::NFind::DoesDirExist", a=0x455cf0, n=101, pos=True, fs=True,
                stops=(0x5f, 0x60), calls=True, tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `NFind::DoesDirExist` (`FileFind.cpp`; `objdump -d`)"),
    # 7-Zip's CPP/Windows/FileFind.cpp `CFileInfo::Find_DontFill_Name (path, followLink)`: two pushes, a frame of 168
    # bytes with the stack guard at `rsp + 152`, `MY_lstat (path, &st, followLink)` (call at 0x30), when it answers 0
    # `SetFrom_stat (st)` (call at 0x45) and `al` = 1, the guard's check. Stops: the `ret` (0x6c), the call of
    # `__stack_chk_fail` (0x6d).
    "fdn": dict(grp="Fdn", cn="NWindows::NFile::NFind::CFileInfo::Find_DontFill_Name", a=0x455b00, n=114, pos=True,
                fs=True, stops=(0x6c, 0x6d), calls=True, tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `CFileInfo::Find_DontFill_Name` (`FileFind.cpp`; `objdump -d`)"),
    # glibc 2.31 dlfcn/dlerror.c `fini` (`check_free (&last_result)`): `last_result.errstring` (0x7a4c18) freed and
    # cleared unless NULL or the static "out of memory" (14 bytes at 0x6d945c; `repz cmpsb`, by hand: 31). Stops: the
    # `ret`s (42, 64).
    "fni": dict(grp="Fni", cn="fini", a=0x41c0f0, n=65, pos=True, stops=(42, 64), calls=True, hand=(31,),
                tag="PLAN.md §M, M1", src="glibc 2.31's `fini` (`dlfcn/dlerror.c`; `objdump -d`)"),
    # 7-Zip's `Correct_PathPart (s)` (`CPP/7zip/UI/Common/ExtractingFilePath.cpp`, static): "." and ".." emptied,
    # else each '/' of the `wchar_t`s made '_' and, when the byte at 0x79eda0 is set, the trailing '.' and ' ' too.
    # Stops: the `ret`s (0x1e, 0x65, 0x8e); the loops' heads are cuts (0x42, 0x82).
    "cpp": dict(grp="Cpp", cn="Correct_PathPart", a=0x5c6ee0, n=156, pos=True, stops=(0x1e, 0x65, 0x8e),
                tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `Correct_PathPart` (`CPP/7zip/UI/Common/ExtractingFilePath.cpp`; `objdump -d`)"),
    # 7-Zip's C/Alloc.c `MyAlloc (size)`: 0 for size 0, else a tail jump to `malloc`. Stops: the jump (9), the `ret`
    # (18).
    "mya": dict(grp="Mya", cn="MyAlloc", a=0x41f3c0, n=19, pos=True, stops=(9, 18),
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `MyAlloc` (`C/Alloc.c`; `objdump -d`)"),
    "ar2": dict(grp="Ar2", cn="CCrcHasher::AddRef", a=0x49fe10, n=14, pos=True, stops=(13,),
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `CCrcHasher::AddRef` (`MyCom.h`; `objdump -d`)"),
    "ar3": dict(grp="Ar3", cn="CInFileStream::AddRef", a=0x5a48a0, n=14, pos=True, stops=(13,),
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `CInFileStream::AddRef` (`MyCom.h`; `objdump -d`)"),
    # 7-Zip 26.06's handlers' counts of properties (`IMP_IInArchive_Props` etc.): `*n` stored, 0 returned. Stop: `ret`.
    "nrp": dict(grp="Nrp", cn="NHash::CHandler::GetNumRawProps", a=0x49e940, n=13, pos=True, stops=(12,),
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `NHash::CHandler::GetNumRawProps` (`objdump -d`)"),
    "gnp": dict(grp="Gnp", cn="NArchive::NGz::CHandler::GetNumberOfArchiveProperties", a=0x49e8f0, n=13, pos=True, stops=(12,),
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `NGz::CHandler::GetNumberOfArchiveProperties` (`objdump -d`)"),
    # 7-Zip 26.06's CPP/Windows/FileName.cpp `GetRootPrefixSize`: 1 if the path starts with `/`, else 0. Stop: `ret`.
    "rps": dict(grp="Rps", cn="NWindows::NFile::NName::GetRootPrefixSize(const char *)", a=0x456a60, n=13, pos=True, stops=(12,),
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `GetRootPrefixSize` (`CPP/Windows/FileName.cpp`; `objdump -d`)"),
    "rpw": dict(grp="Rpw", cn="NWindows::NFile::NName::GetRootPrefixSize(const wchar_t *)", a=0x456a70, n=13, pos=True, stops=(12,),
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `GetRootPrefixSize` (`CPP/Windows/FileName.cpp`; `objdump -d`)"),
    # 7-Zip 26.06's CPP/7zip/UI/Common/ArchiveCommandLine.h `CArcCommand`'s tests of `CommandType`. Stop: `ret`.
    "ifx": dict(grp="Ifx", cn="CArcCommand::IsFromExtractGroup", a=0x5a70d0, n=16, pos=True, stops=(15,),
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `CArcCommand::IsFromExtractGroup` (`ArchiveCommandLine.h`; `objdump -d`)"),
    "gpm": dict(grp="Gpm", cn="CArcCommand::GetPathMode", a=0x5a70e0, n=21, pos=True, stops=(20,),
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `CArcCommand::GetPathMode` (`ArchiveCommandLine.h`; `objdump -d`)"),
    # 7-Zip 26.06's CPP/Common/MyWindows.cpp `SysStringLen`: 0 for null, else the byte length before `bstr` / 4.
    # Stops: the two `ret`s (15, 18).
    "ssl": dict(grp="Ssl", cn="SysStringLen", a=0x5a0100, n=19, pos=True, stops=(15, 18),
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `SysStringLen` (`CPP/Common/MyWindows.cpp`; `objdump -d`)"),
    # 7-Zip's CPP/Windows/FileIO.cpp `CFileBase::Close ()`: nothing when `_handle` is -1, else `close (_handle)`,
    # `_handle` = -1 on success. Stop: the `ret` (0x2f); the `call` of `__close` is at 0x14.
    "fcl": dict(grp="Fcl", cn="NWindows::NFile::NIO::CFileBase::Close", a=0x456030, n=48, pos=True, stops=(0x2f,),
                calls=True, tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `CFileBase::Close` (`CPP/Windows/FileIO.cpp`; `objdump -d`)"),
    # glibc 2.31 elf/dl-profstub.c `_dl_mcount_wrapper_check (selfpc)`: nothing unless
    # `GLRO(dl_profile_map)` is set. Stops: the tail jump to `_dl_mcount` (0x15), the `ret` (0x20).
    "dmw": dict(grp="Dmw", cn="_dl_mcount_wrapper_check", a=0x670700, n=33, pos=True, stops=(0x15, 0x20),
                tag="PLAN.md §M, M1", src="glibc 2.31's `_dl_mcount_wrapper_check` (`elf/dl-profstub.c`; `objdump -d`)"),
    # glibc 2.31 sysdeps/unix/sysv/linux/getpagesize.c `__getpagesize ()`: `GLRO(dl_pagesize)`, asserted not 0.
    # Stops: the `ret` (0x10), the call of `__assert_fail` (0x2c).
    "gps": dict(grp="Gps", cn="__getpagesize", a=0x666460, n=49, pos=True, stops=(0x10, 0x2c), calls=True,
                tag="PLAN.md §M, M1",
                src="glibc 2.31's `__getpagesize` (`sysdeps/unix/sysv/linux/getpagesize.c`; `objdump -d`)"),
    # glibc 2.31 libio/fileno.c `__fileno (fp)`: `fp->_fileno` when the stream is open (`_IO_IS_FILEBUF`) and it is
    # not negative, else `errno` = `EBADF` and -1. Stops: the `ret` (0x13), the `ret` after `errno` is set (0x2b).
    "fno": dict(grp="Fno", cn="__fileno", a=0x627140, n=44, pos=True, fs=True, stops=(0x13, 0x2b),
                tag="PLAN.md §M, M1", src="glibc 2.31's `__fileno` (`libio/fileno.c`; `objdump -d`)"),
    # glibc 2.31 nptl/pthread_mutex_destroy.c `__pthread_mutex_destroy (mutex)`: `EBUSY` if the mutex is not robust
    # and has users, else `__kind` = -1 and 0. Stop: the `ret` (0x21).
    "pmd": dict(grp="Pmd", cn="__pthread_mutex_destroy", a=0x5fbd00, n=34, pos=True, stops=(0x21,),
                tag="PLAN.md §M, M1",
                src="glibc 2.31's `__pthread_mutex_destroy` (`nptl/pthread_mutex_destroy.c`; `objdump -d`)"),
    # glibc 2.31 signal/sigaction.c `__sigaction (sig, act, oact)`: `errno` = `EINVAL` and -1 unless `sig` is from 1 to
    # 64 and not `SIGCANCEL` (32) or `SIGSETXID` (33), else a tail jump to `__libc_sigaction`. Stops: the jump (0x14),
    # the `ret` (0x33).
    # glibc 2.31 `__fxstat (vers, fd, buf)` and `__xstat (vers, path, buf)` (`sysdeps/unix/sysv/linux/wordsize-64/`):
    # `vers` above 1 is `EINVAL`, else the `syscall` `fstat` (5) or `stat` (4), the error to `errno`. Stops: the `ret`s,
    # the padding after the first two; the `syscall` is a step of its own.
    "fxs": dict(grp="Fxs", cn="__fxstat", a=0x665360, n=84, pos=True, fs=True, stops=(0x21, 0x22, 0x39, 0x3a, 0x53),
                calls=True, tag="PLAN.md §M, M1",
                src="glibc 2.31's `__fxstat` (`sysdeps/unix/sysv/linux/wordsize-64/fxstat.c`; `objdump -d`)"),
    "xst": dict(grp="Xst", cn="__xstat", a=0x665300, n=84, pos=True, fs=True, stops=(0x22, 0x23, 0x39, 0x3a, 0x53),
                calls=True, tag="PLAN.md §M, M1",
                src="glibc 2.31's `__xstat` (`sysdeps/unix/sysv/linux/wordsize-64/xstat.c`; `objdump -d`)"),
    "sgw": dict(grp="Sgw", cn="__sigaction", a=0x6011d0, n=52, pos=True, fs=True, stops=(0x14, 0x33),
                tag="PLAN.md §M, M1", src="glibc 2.31's `__sigaction` (`signal/sigaction.c`; `objdump -d`)"),
    # glibc 2.31 `__wmemcpy (d, s, n)`: `n` scaled to bytes (`shl rdx, 2`), a tail jump to `memcpy`'s PLT entry.
    # Stop: the `jmp` (0x8).
    "wmc": dict(grp="Wmc", cn="__wmemcpy", a=0x65d300, n=13, pos=True, stops=(0x8,),
                tag="PLAN.md §M, M1", src="glibc 2.31's `__wmemcpy` (`wcsmbs/wmemcpy.c`; `objdump -d`)"),
    # glibc 2.31 `__libc_free (mem)` (malloc/malloc.c): `__free_hook`, `free (0)`, the mmapped chunk (the dynamic
    # threshold, then `munmap_chunk`), the tcache made if absent (`tcache_init`), the arena, then `_int_free`.
    # Stops: the tail jumps to `_int_free` (0x56) and `munmap_chunk` (0x82), the `ret` (0x94), the hook's `jmp`
    # (0xa1) and the call of `tcache_init` (0xe0).
    "fre": dict(grp="Fre", cn="__libc_free", a=0x633750, n=247, pos=True, fs=True, stops=(0x56, 0x82, 0x94, 0xa1, 0xe0),
                calls=True, tag="PLAN.md G3, `free`", src="glibc 2.31's `__libc_free` (`malloc/malloc.c`; `objdump -d`)"),
    # glibc 2.31 `_int_free (av, p, have_lock)` (malloc/malloc.c), to its tcache put: the size checks, `tc_idx`, the
    # double free test (`e->key == tcache`), the bin's count, the put, the canary, the pops, the `ret`. Stops: an
    # invalid pointer (0x2e0) or size (0x2f0), not put in the tcache (0xa3: no tcache, `tc_idx` too big, the bin
    # full), the key is the tcache (0x6f8: the scan of the bin), the canary changed (0x987), the `ret` (0x155).
    "ifr": dict(grp="Ifr", cn="_int_free", a=0x62f990, n=2506, pos=True, fs=True,
                stops=(0x2e0, 0x2f0, 0xa3, 0x6f8, 0x987, 0x155), calls=True, cut=(90, 696, 307),
                tag="PLAN.md G3, `free`", src="glibc 2.31's `_int_free` (`malloc/malloc.c`; `objdump -d`)"),
    # glibc 2.31 nptl/cleanup_compat.c `_pthread_cleanup_push (buffer, routine, arg)`: the buffer filled, linked in
    # front of the thread's `cleanup` list (`fs:0x2f8`). Stop: the `ret` (0x21).
    "pcp": dict(grp="Pcp", cn="_pthread_cleanup_push", a=0x5fefe0, n=34, pos=True, fs=True, stops=(0x21,),
                tag="PLAN.md §M, M1", src="glibc 2.31's `_pthread_cleanup_push` (`nptl/cleanup_compat.c`; `objdump -d`)"),
    # glibc 2.31 nptl/cleanup_compat.c `_pthread_cleanup_pop (buffer, execute)`: the thread's `cleanup` list
    # (`fs:0x2f8`) set back to `buffer->__prev`; if `execute`, a tail jump to `buffer->__routine (buffer->__arg)`.
    # Stops: the `jmp rax` (0x1f) and the `ret` (0x28).
    "pco": dict(grp="Pco", cn="_pthread_cleanup_pop", a=0x5ff010, n=41, pos=True, fs=True, stops=(0x1f, 0x28),
                tag="PLAN.md §M, M1", src="glibc 2.31's `_pthread_cleanup_pop` (`nptl/cleanup_compat.c`; `objdump -d`)"),
    # glibc 2.31 string/strdup.c `__strdup (s)`: `strlen (s) + 1` bytes from `malloc`, then a tail jump to `memcpy`
    # through the PLT; `malloc`'s 0 is the answer. Stops: the `jmp` to `memcpy` (0x34) and the `ret` (0x3f).
    # glibc's `__hash_string (str)` (`intl/hash-string.c`): the ELF-style hash of the bytes up to the NUL, a loop
    # from 0x28 back to itself; three `ret`s (0x4f, 0x50, 0x5a: the empty string).
    "hsh": dict(grp="Hsh", cn="__hash_string", a=0x6222e0, n=91, pos=True, stops=(0x4f, 0x50, 0x5a),
                tag="PLAN.md §M, M1", src="glibc 2.31's `__hash_string` (`intl/hash-string.c`; `objdump -d`)"),
    # libio's `_IO_default_imbue`: `endbr64; ret`.
    "imb": dict(grp="Imb", cn="_IO_default_imbue", a=0x5ab370, n=5, pos=True, stops=(0x4,),
                tag="PLAN.md §M, M1", src="glibc 2.31's `_IO_default_imbue` (`libio/genops.c`; `objdump -d`)"),
    # 7-Zip's CPP/Common/MyWindows.cpp `SysFreeString (bstr)`: null, a `ret` (0x18); else a tail jump to `free`
    # (0xd) at the allocation, 4 bytes before.
    # 7-Zip's CPP/Common/MyWindows.cpp `VariantClear (PROPVARIANT *prop)`: `SysFreeString (prop->bstrVal)` if
    # `prop->vt` is `VT_BSTR`, then `prop->vt` = `VT_EMPTY`, answer `S_OK`. Stops: the two `ret`s (22, 49).
    # 7-Zip 26.06's CPP/Common/MyWindows.cpp `SysAllocStringLen (s, len)`: `len` above 0x3ffffffc or `malloc`
    # (the `call`, 0x22) null: 0 (0x6a, the `ret`); else the length word, `memcpy` of `s` (the `call`, 0x41) when
    # `s` is not null, the terminator, `rax` = the string (0x58, the `ret`).
    # glibc 2.31's libio/genops.c `_IO_setb (f, b, eb, a)`: `f->_IO_buf_base` not null and the user-buffer flag
    # clear: `free` of it (the `call`, 0x50, then back to 0x27); the flag set or cleared by `a` (`cmovne`), the two
    # pointers stored by one `movups` (0x3e), the flags word, the `ret` (0x4a).
    "stb": dict(grp="Stb", cn="_IO_setb", a=0x62b4a0, n=89, pos=True, stops=(0x4a,), calls=True,
                tag="PLAN.md §M, M1", src="glibc 2.31's `_IO_setb` (`libio/genops.c`; `objdump -d`)"),
    "sas": dict(grp="Sas", cn="SysAllocStringLen", a=0x5a0010, n=107, pos=True, stops=(0x58, 0x6a), calls=True,
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `SysAllocStringLen` (`CPP/Common/MyWindows.cpp`; `objdump -d`)"),
    "vcl": dict(grp="Vcl", cn="VariantClear", a=0x5a0120, n=50, pos=True, stops=(22, 49), calls=True,
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `VariantClear` (`CPP/Common/MyWindows.cpp`; `objdump -d`)"),
    # 7-Zip's CPP/Windows/FileIO.cpp `CInFile::read_part (data, size)`: `read (_handle, data, min (size, 1 << 22))`
    # (the `call`, 26). Stop: the `ret` (35); the 15 bytes after it are a separate `endbr64` landing pad, left out.
    "irp": dict(grp="Irp", cn="CInFile::read_part", a=0x4561a0, n=36, pos=True, stops=(35,), calls=True,
                tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `CInFile::read_part` (`CPP/Windows/FileIO.cpp`; `objdump -d`)"),
    # 7-Zip's CPP/Windows/PropVariant.cpp `CPropVariant::InternalClear ()`: `vt` 0, `wReserved1` = 0 and `S_OK`; else
    # `PropVariant_Clear (this)` (the `call`, 32) and on an error `vt` = `VT_ERROR`, `scode` = it. Stops: the `ret`s.
    "pic": dict(grp="Pic", cn="CPropVariant::InternalClear", a=0x457130, n=54, pos=True, stops=(23, 53), calls=True,
                tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `CPropVariant::InternalClear` (`CPP/Windows/PropVariant.cpp`; `objdump -d`)"),
    # 7-Zip's CPP/Windows/PropVariant.cpp `CPropVariant::Detach (pDest)`: `PropVariant_Clear (pDest)` (the `call`, 51)
    # if `pDest->vt` is not 0; on success the 16 bytes of `*this` to `*pDest` and `vt` = 0. Stop: the `ret` (45).
    # `vop`: the copy through `xmm0`.
    "pdt": dict(grp="Pdt", cn="CPropVariant::Detach", a=0x4570f0, n=62, pos=True, stops=(45,), calls=True, vop=True,
                tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `CPropVariant::Detach` (`CPP/Windows/PropVariant.cpp`; `objdump -d`)"),
    # 7-Zip's CPP/Windows/PropVariant.h `CPropVariant::~CPropVariant ()`: `VariantClear (this)` (the `call`, 42) unless
    # `vt` is one of the simple types (`vt` <= 7, or bit `vt - 10` of 0x40000000003fc3). Stops: the `ret`s (51, 52, 56);
    # the 15 bytes after 56 are a separate `endbr64` landing pad, left out.
    "pvd": dict(grp="Pvd", cn="CPropVariant::~CPropVariant", a=0x456f60, n=57, pos=True, stops=(51, 52, 56), calls=True,
                tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `CPropVariant::~CPropVariant` (`CPP/Windows/PropVariant.h`; `objdump -d`)"),
    # glibc 2.31 dirent/closedir.c `__closedir (dirp)`: a null `dirp`, `errno` EINVAL and -1 (0x2c, the `ret`); else
    # `fd` = `dirp->fd` kept in `rbp`, `free (dirp)` (the `call`, 0xc), then a tail jump to `__close_nocancel` (0x14).
    # glibc 2.31 `__bsd_signal (sig, handler)` (`signal/signal.c`): `sig` out of 1..64, `handler` = `SIG_ERR` or
    # `sig` 32 or 33 (glibc's own), `errno` = `EINVAL` and -1 (0x20 to the `ret` at 0x35); else a tail jump (0x1a) to
    # `__bsd_signal.part.0` (`Bsg`).
    "bsn": dict(grp="Bsn", cn="__bsd_signal", a=0x6225b0, n=54, pos=True, fs=True, stops=(0x1a, 0x35), calls=True,
                tag="PLAN.md §M, M1", src="glibc 2.31's `__bsd_signal` (`signal/signal.c`; `objdump -d`)"),
    "cld": dict(grp="Cld", cn="__closedir", a=0x663860, n=45, pos=True, fs=True, stops=(0x14, 0x2c), calls=True,
                tag="PLAN.md §M, M1", src="glibc 2.31's `__closedir` (`sysdeps/posix/closedir.c`; `objdump -d`)"),
    # 7-Zip 26.06's CPP/Windows/FileFind.cpp `MY_lstat (path, st, followLink)`: the `stat` zeroed (`rep stosq`, 0xd,
    # 18 quadwords; by hand), then a tail jump to `__xstat (1, path, st)` (0x28) with `followLink`, else to `__lxstat` (0x1f).
    "mls": dict(grp="Mls", cn="MY_lstat", a=0x4558a0, n=45, pos=True, stops=(0x1f, 0x28), calls=True, hand=(0xd,),
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `MY_lstat` (`CPP/Windows/FileFind.cpp`; `objdump -d`)"),
    # glibc 2.31 sysdeps/posix/opendir.c `__opendir (name)` with `opendir_tail` and `__alloc_dir` inlined: an empty
    # `name`, `errno` ENOENT (0x120); `__open_nocancel` (0x32), `__fxstat` (0x4b), not a directory `errno` ENOTDIR
    # (0x100), `malloc` of the buffer (0x94, again smaller at 0x14c), `__close_nocancel` on the errors (0x113, 0x16e);
    # the stack guard's check (0x13d: `__stack_chk_fail`). Stops: the `ret` (0xfe).
    # glibc 2.31 sysdeps/posix/readdir.c (`__readdir64`, aliased `__readdir`): `dirp->lock` taken, then the next entry
    # of the buffer, refilled by `__getdents` (0x80) when used up; `errno` kept unless the call failed with other than
    # `ENOENT`. Stops: the `ret` (0xcc), the process has more than one thread (0xd9: the lock is released with `xchg`;
    # 0xfd: it is taken with `lock cmpxchg`). By hand: `cmpxchg [rdi + 4], edx` (0x34), `sub dword [r14 + 4], 1` (0xbc).
    "rdd": dict(grp="Rdd", cn="__readdir", a=0x6638a0, n=285, pos=True, fs=True, stops=(0xcc, 0xd9, 0xfd), calls=True,
                hand=(0x34, 0xbc), tag="PLAN.md §M, M1",
                src="glibc 2.31's `__readdir` (`sysdeps/posix/readdir.c`; `objdump -d`)"),
    "opd": dict(grp="Opd", cn="__opendir", a=0x6635d0, n=380, pos=True, fs=True, stops=(0xfe,), calls=True,
                tag="PLAN.md §M, M1", src="glibc 2.31's `__opendir` (`sysdeps/posix/opendir.c`; `objdump -d`)"),
    # 7-Zip's C/LzmaDec.c `LzmaDec_Init (p)`: `p->dicPos` = 0, then a tail jump (0x16) to
    # `LzmaDec_InitDicAndState (p, True, True)`.
    "lzi": dict(grp="Lzi", cn="LzmaDec_Init", a=0x42b640, n=27, pos=True, stops=(0x16,), calls=True,
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `LzmaDec_Init` (`C/LzmaDec.c`; `objdump -d`)"),
    # glibc 2.31 libio/fileops.c `_IO_file_stat (fp, st)`: a tail jump (0xf) to `__fxstat (1, fp->_fileno, st)`.
    "ifs": dict(grp="Ifs", cn="_IO_file_stat", a=0x6287b0, n=20, pos=True, stops=(0xf,), calls=True,
                tag="PLAN.md §M, M1", src="glibc 2.31's `_IO_file_stat` (`libio/fileops.c`; `objdump -d`)"),
    # 7-Zip 26.06 `CreateArc` of the lzma handler (`CPP/7zip/Archive/LzmaHandler.cpp`, `new CHandler`): `operator new
    # (0x58)` (the `call`, 0xd, to the body at 0x602970), then the fields and the two vtables stored (to the `ret`).
    "cra": dict(grp="Cra", cn="CreateArc", a=0x49e9c0, n=0x4b, pos=True, stops=(0x4a,), calls=True,
                tag="PLAN.md §M, M1", src="7-Zip 26.06's lzma `CreateArc` (`CPP/7zip/Archive/LzmaHandler.cpp`; `objdump -d`)"),
    # 7-Zip's CPP/Windows/TimeUtils.cpp `FiTime_To_FILETIME_ns100 (ts, ft, ns100)`: `UnixTime64_To_FileTime64
    # (ts.tv_sec)` (call, 20), plus `tv_nsec / 100` into `ft`, `tv_nsec % 100` into `ns100`. Stop: the `ret` (95).
    "fft": dict(grp="Fft", cn="FiTime_To_FILETIME_ns100", a=0x458db0, n=96, pos=True, stops=(95,), calls=True,
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `FiTime_To_FILETIME_ns100` (`TimeUtils.cpp`; `objdump -d`)"),
    # 7-Zip's CPP/Windows/FileFind.cpp `CFileInfoBase::SetFrom_stat (st)`: the fields of `st` into the object.
    # Stop: the `ret` (105).
    "sst": dict(grp="Sst", cn="CFileInfoBase::SetFrom_stat", a=0x4559d0, n=106, pos=True, stops=(105,),
                tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `CFileInfoBase::SetFrom_stat` (`FileFind.cpp`; `objdump -d`)"),
    # 7-Zip's CPP/Common/MyString.cpp `FindCharPosInString (s, c)` for `char`: the index of the first `c` before the
    # NUL, else -1. Stops: the `ret`s (45, 50, 53).
    "fcc": dict(grp="Fcc", cn="FindCharPosInString (char)", a=0x44b960, n=54, pos=True, stops=(45, 50, 53),
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `FindCharPosInString` (`MyString.cpp`; `objdump -d`)"),
    # 7-Zip 26.06 `CArchiveExtractCallback::PrepareOperation (askExtractMode)`: with `_extractCallback2`... the inner
    # callback (0xc0) a tail jump through its vtable (0x16, slot 0x28); else the flags at 0x6d and the tail jump through
    # `_extractCallback3`'s slot 0x30 (0x66, `jmp r10`).
    "pop": dict(grp="Pop", cn="CArchiveExtractCallback::PrepareOperation", a=0x5aa500, n=0x77, pos=True,
                stops=(0x16, 0x66), tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `CArchiveExtractCallback::PrepareOperation` (`CPP/7zip/UI/Common/ArchiveExtractCallback.cpp`; `objdump -d`)"),
    # 7-Zip 26.06 `COpenCallbackImp::SetTotal (files, bytes)`: through `ReOpenCallback` (0x60) a tail `jmp rax` (0x17,
    # slot 0x18); else through `Callback` (0x68) a call of slot 8 (0x30) and its answer (`ret` 0x37); else 0 (0x42).
    "sto": dict(grp="Sto", cn="COpenCallbackImp::SetTotal", a=0x5b2c80, n=0x43, pos=True,
                stops=(0x17, 0x37, 0x42), calls=True, tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `COpenCallbackImp::SetTotal` (`CPP/7zip/UI/Common/ArchiveOpenCallback.cpp`; `objdump -d`)"),
    "hcl": dict(grp="Hcl", cn="NArchive::NLzma::CHandler::Close", a=0x49ea60, n=0x4e, pos=True,
                stops=(0x4d,), calls=True, tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `NArchive::NLzma::CHandler::Close` (`CPP/7zip/Archive/LzmaHandler.cpp`; `objdump -d`)"),
    "sis": dict(grp="Sis", cn="NCompress::NLzma::CDecoder::SetInStream", a=0x57f8d0, n=0x40, pos=True,
                stops=(0x3f,), calls=True, tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `NCompress::NLzma::CDecoder::SetInStream` (`CPP/7zip/Compress/LzmaDecoder.cpp`; `objdump -d`)"),
    # 7-Zip 26.06 `NWildcard::CCensor::FindPairForPrefix (prefix)`: the loop over `Pairs` with `CompareFileNames`
    # (0x4522b0) at 0x39; the `ret`s at 0x48 (found), 0x59 (none) and 0x5f (no pairs).
    "ffp": dict(grp="Ffp", cn="NWildcard::CCensor::FindPairForPrefix", a=0x453550, n=0x60, pos=True,
                stops=(0x48, 0x59, 0x5f), calls=True, tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `NWildcard::CCensor::FindPairForPrefix` (`CPP/Common/Wildcard.cpp`; `objdump -d`)"),
    # 7-Zip 26.06 C/LzmaDec + CPP/7zip/Compress/LzmaDecoder.cpp `CDecoder::SetOutStreamSizeResume (outSize)`: the
    # flags and sizes, then a tail jump (0x2f) to `LzmaDec_Init (&_state)`.
    "sos": dict(grp="Sos", cn="NCompress::NLzma::CDecoder::SetOutStreamSizeResume", a=0x57fd80, n=52, pos=True,
                stops=(0x2f,), calls=True, hand=(0xf,), tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `CDecoder::SetOutStreamSizeResume` (`CPP/7zip/Compress/LzmaDecoder.cpp`; `objdump -d`)"),
    # 7-Zip 26.06 CPP/Common/Wildcard.cpp `CItem::AreAllAllowed ()`: 0 (the `ret`, 0x1e) unless the three flags are set
    # and there is one path part; then a tail jump (0x30) to `StringsAreEqual_Ascii (PathParts[0], "*")`.
    "aaa": dict(grp="Aaa", cn="NWildcard::CItem::AreAllAllowed", a=0x452990, n=53, pos=True, stops=(0x1e, 0x30),
                calls=True, tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `CItem::AreAllAllowed` (`CPP/Common/Wildcard.cpp`; `objdump -d`)"),
    # 7-Zip 26.06 CPP/7zip/Crypto/7zAes.h `CKey::Wipe ()`: `memset` of the password's bytes if any (the `call`, 0x3e),
    # then the 88 bytes of the key zeroed; the `ret` (0x31).
    "ckw": dict(grp="Ckw", cn="NCrypto::N7z::CKey::Wipe", a=0x59ea70, n=69, pos=True, stops=(0x31,), calls=True,
                vop=True, tag="PLAN.md §M, M1", src="7-Zip 26.06's `CKey::Wipe` (`CPP/7zip/Crypto/7zAes.h`; `objdump -d`)"),
    # 7-Zip 26.06 CPP/7zip/Compress/LzmaDecoder.cpp `CDecoder::CreateInputBuffer ()`: the buffer kept if its size is
    # right (the `ret`, 0x41), else `MyFree` (0x1b) and `MyAlloc` (0x2a); S_OK (0x41) or E_OUTOFMEMORY (0x48).
    "cib": dict(grp="Cib", cn="NCompress::NLzma::CDecoder::CreateInputBuffer", a=0x57fcc0, n=73, pos=True,
                stops=(0x41, 0x48), calls=True, tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `CDecoder::CreateInputBuffer` (`CPP/7zip/Compress/LzmaDecoder.cpp`; `objdump -d`)"),
    # 7-Zip 26.06 `NWildcard::CCensorNode::CheckPathCurrent (include, pathParts, isFile)`: the loop over
    # `IncludeItems` or `ExcludeItems` (`cmove`) with `CItem::CheckPath` (0x4529d0) at 0x4a; the `ret`s at 0x5d (one
    # matched, its `al`) and 0x6c (none, 0).
    "cpt": dict(grp="Cpt", cn="NWildcard::CCensorNode::CheckPathCurrent", a=0x453050, n=0x6e, pos=True,
                stops=(0x5d, 0x6c), calls=True, tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `NWildcard::CCensorNode::CheckPathCurrent` (`CPP/Common/Wildcard.cpp`; `objdump -d`)"),
    "eex": dict(grp="Eex", cn="NWildcard::CCensor::ExtendExclude", a=0x4535b0, n=0x97, pos=True,
                stops=(0x83, 0x96), calls=True, tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `NWildcard::CCensor::ExtendExclude` (`CPP/Common/Wildcard.cpp`; `objdump -d`)"),
    "sfs": dict(grp="Sfs", cn="SysFreeString", a=0x5a00c0, n=25, pos=True, stops=(0xd, 0x18),
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `SysFreeString` (`CPP/Common/MyWindows.cpp`; `objdump -d`)"),
    # 7-Zip's CPP/Common/Wildcard.cpp `DoesNameContainWildcard (const UString &)`: the `wchar_t`s (4 bytes, at
    # `[rdi]`, `[rdi+8]` of them) scanned for `*` or `?`; three `ret`s (0x3b found, 0x40 none, 0x43 empty).
    "dnw": dict(grp="Dnw", cn="DoesNameContainWildcard", a=0x452940, n=68, pos=True, stops=(0x3b, 0x40, 0x43),
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `DoesNameContainWildcard` (`CPP/Common/Wildcard.cpp`; `objdump -d`)"),
    # 7-Zip's CPP/Common/StringToInt.cpp `ConvertStringToUInt64 (const wchar_t *s, const wchar_t **end)`: decimal
    # digits (4-byte `wchar_t`s) to a `UInt64`, 0 on overflow; the end stored at `[rsi]` when `rsi` is not 0. Stops:
    # the `ret`s (0x55 overflow, 0x68 the end stored, 0x77 no end).
    "lhp": dict(grp="Lhp", cn="CHeader_Parse", a=0x49ec00, n=0xa9, pos=True, stops=(0x43,),
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `NArchive::NLzma::CHeader::Parse` (`CPP/7zip/Archive/LzmaHandler.cpp`; "
                "`objdump -d`)"),
    # 7-Zip's CPP/Common/UTFConvert.cpp `Utf16_To_Utf8_Calc (src, srcLim, flags)` (`wchar_t` 4 bytes): the
    # UTF-8 size of the characters in [src, srcLim), a loop from 0x18 back to itself; two `ret`s (0x7a, 0x88).
    "u8c": dict(grp="U8c", cn="Utf16_To_Utf8_Calc", a=0x4518e0, n=0xf9, pos=True, stops=(0x7a, 0x88),
                tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `Utf16_To_Utf8_Calc` (`CPP/Common/UTFConvert.cpp`; `objdump -d`)"),
    # 7-Zip's CPP/Common/UTFConvert.cpp `Utf16_To_Utf8 (dest, src, srcLim, flags)` (`wchar_t` 4 bytes): the
    # characters in [src, srcLim) to UTF-8 at dest, the end returned; the outer loop at 0x20, the continuation
    # bytes' loop at 0x98; one `ret` (0xc1).
    "u8w": dict(grp="U8w", cn="Utf16_To_Utf8", a=0x4519e0, n=0x241, pos=True, stops=(0xc1,),
                tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `Utf16_To_Utf8` (`CPP/Common/UTFConvert.cpp`; `objdump -d`)"),
    # 7-Zip's CPP/Common/UTFConvert.cpp. Stop: the `ret` (0x14f).
    "u16": dict(grp="U16", cn="Utf8_To_Utf16", a=0x451690, n=0x24b, pos=True, stops=(0x14f,),
                tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `Utf8_To_Utf16` (`CPP/Common/UTFConvert.cpp`; `objdump -d`)"),
    "lpd": dict(grp="Lpd", cn="LzmaProps_Decode", a=0x42bea0, n=0x66, pos=True, stops=(0x56, 0x65),
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `LzmaProps_Decode` (`C/LzmaDec.c`; `objdump -d`)"),
    "stu": dict(grp="Stu", cn="ConvertStringToUInt64", a=0x451330, n=0x7c, pos=True, stops=(0x55, 0x68, 0x77),
                tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `ConvertStringToUInt64` (`CPP/Common/StringToInt.cpp`; `objdump -d`)"),
    # 7-Zip's CPP/Common/IntToString.cpp `ConvertUInt64ToString (UInt64 val, char *s)`: a value to `0xffffffff` by a
    # tail jump to `ConvertUInt32ToString` (0xc4), else the digits from the last into a stack buffer (0x38, `x / 10`
    # by `mul` with `0xcccccccccccccccd` and `shr 3`), the first at `s`, the others copied out in reverse (0x80); the
    # stack guard (`fs:0x28`). Stops: the `ret` (0xac), the tail jump (0xc4), `__stack_chk_fail` (0xc9).
    "c64": dict(grp="C64", cn="ConvertUInt64ToString", a=0x44ac30, n=206, pos=True, fs=True, stops=(0xac, 0xc4, 0xc9),
                cut=(146, 176),
                tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `ConvertUInt64ToString` (`CPP/Common/IntToString.cpp`; `objdump -d`)"),
    # 7-Zip's CPP/Common/IntToString.cpp `ConvertUInt32ToString (UInt32, char *)`: one digit at once (0x21), or the
    # digits from the last into a stack buffer (0x58, `x / 10` by `0xcccccccd` and `shr 35`), then copied out in
    # reverse (0x98); the stack guard (`fs:0x28`). Stops: the `ret` (0x42), `__stack_chk_fail` (0xb2).
    "u2s": dict(grp="U2s", cn="ConvertUInt32ToString", a=0x44ab70, n=0xb7, pos=True, fs=True, stops=(0x42, 0xb2),
                tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `ConvertUInt32ToString` (`CPP/Common/IntToString.cpp`; `objdump -d`)"),
    "sdp": dict(grp="Sdp", cn="__strdup", a=0x635dd0, n=64, pos=True, stops=(0x34, 0x3f), calls=True,
                tag="PLAN.md §M, M1", src="glibc 2.31's `__strdup` (`string/strdup.c`; `objdump -d`)"),
    # 7-Zip's CPP/Common/MyString.cpp `FindCharPosInString (s, c)` for `char`: the index of the first `c` in `s` up to
    # its 0, else -1. Stops: the three `ret`s (0x2d: -1, 0x32: the index, 0x35: 0); the loop's head is a cut (0x24).
    "fcp": dict(grp="Fcp", cn="FindCharPosInString(const char *, char)", a=0x44b960, n=54, pos=True,
                stops=(0x2d, 0x32, 0x35), tag="PLAN.md §M, M1",
                src="7-Zip's `FindCharPosInString` (`CPP/Common/MyString.cpp`; `objdump -d`)"),
    # The same for `wchar_t` (4 bytes). Stops: the `ret`s (0x24: -1, 0x2f: the index, 0x32: 0); loop head 0x1b.
    "fcw": dict(grp="Fcw", cn="FindCharPosInString(const wchar_t *, wchar_t)", a=0x44b9a0, n=51, pos=True,
                stops=(0x24, 0x2f, 0x32), tag="PLAN.md §M, M1",
                src="7-Zip's `FindCharPosInString` (`CPP/Common/MyString.cpp`; `objdump -d`)"),
    # `MyStringLower_Ascii (s)` for `char`: 'A'..'Z' to 'a'..'z' up to the 0. Stop: the `ret` (0x2a); loop head 0x23.
    "lwa": dict(grp="Lwa", cn="MyStringLower_Ascii(char *)", a=0x44b9e0, n=43, pos=True, stops=(0x2a,),
                tag="PLAN.md §M, M1", src="7-Zip's `MyStringLower_Ascii` (`CPP/Common/MyString.cpp`; `objdump -d`)"),
    # The same for `wchar_t`. Stop: the `ret` (0x29); loop head 0x23.
    "lww": dict(grp="Lww", cn="MyStringLower_Ascii(wchar_t *)", a=0x44ba10, n=42, pos=True, stops=(0x29,),
                tag="PLAN.md §M, M1", src="7-Zip's `MyStringLower_Ascii` (`CPP/Common/MyString.cpp`; `objdump -d`)"),
    # `StringsAreEqual_Ascii (u, a)`: the `wchar_t`s of `u` those of the `char`s of `a`, its 0 included. Stops: the
    # `ret`s (0x31: 1, 0x3a: 0); cuts at the loop's head (0x28) and the answer 0 (0x38).
    "sea": dict(grp="Sea", cn="StringsAreEqual_Ascii(const wchar_t *, const char *)", a=0x44bb60, n=59, pos=True,
                stops=(0x31, 0x3a), tag="PLAN.md §M, M1",
                src="7-Zip's `StringsAreEqual_Ascii` (`CPP/Common/MyString.cpp`; `objdump -d`)"),
    # `AString::ReverseFind_PathSepar ()`: the index of the last `/` of the string (`_chars` at 0, `_len` at 8), else
    # -1. Stops: the `ret`s (0x33: -1, 0x3a: the index); cuts at 0x29 (the loop's head), 0x2e and 0x38.
    "rfp": dict(grp="Rfp", cn="AString::ReverseFind_PathSepar", a=0x44cb50, n=59, pos=True, stops=(0x33, 0x3a),
                tag="PLAN.md §M, M1",
                src="7-Zip's `AString::ReverseFind_PathSepar` (`CPP/Common/MyString.cpp`; `objdump -d`)"),
    # 7-Zip's CPP/Common/MyString.cpp `AString::SetStartLen (len)`: `_chars` = NULL, then `_chars` = `new char[len + 1]`
    # (`operator new`, the `call` at 0x1d), `_len` = `_limit` = `len`. Stop: the `ret` (0x31).
    # 7-Zip's CPP/Common/MyString.cpp `AString::ReAlloc (newLimit)`: `newBuf = new char[newLimit + 1]` (the `call` at
    # 0x1a), `memcpy (newBuf, _chars, _len + 1)` (0x32), `delete [] _chars` (0x3a), then `_chars`, `_limit`. Stop:
    # the `ret` (0x4f).
    "arl": dict(grp="Arl", cn="AString::ReAlloc", a=0x44bfc0, n=80, pos=True, stops=(0x4f,), calls=True,
                tag="PLAN.md §M, M1", src="7-Zip's `AString::ReAlloc` (`CPP/Common/MyString.cpp`; `objdump -d`)"),
    # `AString::ReAlloc2 (newLimit)`: above `k_Alloc_Len_Limit` (0x3ffffffe) the throw at 0x401350 (the `ja` at 0xe,
    # by hand: its target is outside); else `newBuf = new char[newLimit + 1]` (0x1f), `newBuf[0] = 0`, `delete []
    # _chars` unless null (0x32), `_chars`, `_limit`, `_len` = 0. Stop: the `ret` (0x48).
    "arb": dict(grp="Arb", cn="AString::ReAlloc2", a=0x44c010, n=73, pos=True, stops=(0x48,), calls=True, hand=(0xe,),
                tag="PLAN.md §M, M1", src="7-Zip's `AString::ReAlloc2` (`CPP/Common/MyString.cpp`; `objdump -d`)"),
    # `AString (const char *s1, unsigned num1, const char *s2, unsigned num2)`: `SetStartLen`, `memcpy`, then a tail
    # jump to `memcpy` (46).
    "acs": dict(grp="Acs", cn="AString::AString (s1, num1, s2, num2)", a=0x44c260, n=75, pos=True, stops=(0x46,),
                calls=True, tag="PLAN.md §M, M1",
                src="7-Zip's `AString (const char *, unsigned, const char *, unsigned)` (`CPP/Common/MyString.cpp`; "
                    "`objdump -d`)"),
    # `AString (const AString &s)`: `SetStartLen (s._len)`, then the copy loop (40) through the 0.
    "acp": dict(grp="Acp", cn="AString::AString (const AString &)", a=0x44c420, n=62, pos=True, stops=(0x3d,),
                calls=True, tag="PLAN.md §M, M1",
                src="7-Zip's `AString (const AString &)` (`CPP/Common/MyString.cpp`; `objdump -d`)"),
    # `AString (const char *s)`: the length loop (32), `SetStartLen (len)`, then the copy loop (64) through the 0.
    "acc": dict(grp="Acc", cn="AString::AString (const char *)", a=0x44c3c0, n=86, pos=True, stops=(0x55,),
                calls=True, tag="PLAN.md §M, M1",
                src="7-Zip's `AString (const char *)` (`CPP/Common/MyString.cpp`; `objdump -d`)"),
    # `AString::operator= (const AString &s)`: the self test (je 71), the limit test (jb 88), the copy loop (56)
    # through the 0, the epilogue (71); at 88 `operator new []` (95), `operator delete []` (112) unless null, the
    # stores at 117 and the `jmp` back to 38.
    "aas": dict(grp="Aas", cn="AString::operator= (const AString &)", a=0x44c550, n=128, pos=True, stops=(0x54,),
                calls=True, tag="PLAN.md §M, M1",
                src="7-Zip's `AString::operator= (const AString &)` (`CPP/Common/MyString.cpp`; `objdump -d`)"),
    # `AString::operator= (const char *s)`: the length loop (32), `ReAlloc` inline (96) through `operator new []`
    # (100) and `operator delete []` (117) when the limit is below the length, then the copy loop (64) through the 0.
    "aac": dict(grp="Aac", cn="AString::operator= (const char *)", a=0x44c4c0, n=132, pos=True, stops=(0x5e,),
                calls=True, tag="PLAN.md §M, M1",
                src="7-Zip's `AString::operator= (const char *)` (`CPP/Common/MyString.cpp`; `objdump -d`)"),
    "asl": dict(grp="Asl", cn="AString::SetStartLen", a=0x44c060, n=50, pos=True, stops=(0x31,), calls=True,
                tag="PLAN.md §M, M1", src="7-Zip's `AString::SetStartLen` (`CPP/Common/MyString.cpp`; `objdump -d`)"),
    # `UString::UString ()`: `_chars` = NULL, then `_chars` = `new wchar_t[4]` (the `call` at 0x14), `_len` = 0,
    # `_limit` = 3, `_chars[0]` = 0. Stop: the `ret` (0x31).
    "uct": dict(grp="Uct", cn="UString::UString()", a=0x44d3e0, n=50, pos=True, stops=(0x31,), calls=True,
                tag="PLAN.md §M, M1", src="7-Zip's `UString::UString` (`CPP/Common/MyString.cpp`; `objdump -d`)"),
    # 7-Zip 26.06's CPP/Common/CommandLineParser.cpp `CParser::CParser ()`: `_switches` (the vector at 0) empty and
    # `StopSwitchIndex` (at 0x18) -1, then the `AString` at 0x20 (the `call` at 0x34, to 0x44c360) and the `UString`
    # at 0x30 (the `call` at 0x3d, `UString::UString ()`). Stop: the `ret` (0x4c).
    "cpc": dict(grp="Cpc", cn="NCommandLineParser::CParser::CParser", a=0x5a0490, n=77, pos=True, stops=(0x4c,),
                calls=True, tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `CParser::CParser` (`CPP/Common/CommandLineParser.cpp`; `objdump -d`)"),
    # `UString::SetStartLen (len)`: as `AString`'s, `new wchar_t[len + 1]` (the `call` at 0x21). Stop: the `ret` (0x35).
    # 7-Zip's CPP/Common/MyString.cpp `UString::TrimRight ()`: from the end back, past the characters 9, 10 and ' '
    # (the loop at 0x20); none left: `_chars[0]` = 0, `_len` = 0 (0x3b); some trimmed: the 0 after the last kept
    # (0x55, 0x3b). Stop: the `ret` (0x45).
    "utr": dict(grp="Utr", cn="UString::TrimRight", a=0x44de20, n=90, pos=True, stops=(0x45,),
                tag="PLAN.md §M, M1", src="7-Zip's `UString::TrimRight` (`CPP/Common/MyString.cpp`; `objdump -d`)"),
    # 7-Zip's CPP/Common/MyString.cpp `StringsAreEqualNoCase (s1, s2)` for `wchar_t`: each pair of characters equal,
    # or equal after `MyCharUpper` (`c - 0x20` for 'a'..'z', `towupper` above 0x7f: the `call`s at 0x28, 0x6b), up to
    # and with the 0. Stops: the `ret`s (0x8d: 1, 0x9a: 0).
    "sen": dict(grp="Sen", cn="StringsAreEqualNoCase", a=0x44ba80, n=155, pos=True, stops=(0x8d, 0x9a), calls=True,
                tag="PLAN.md §M, M1",
                src="7-Zip's `StringsAreEqualNoCase` (`CPP/Common/MyString.cpp`; `objdump -d`)"),
    # 7-Zip's CPP/Common/MyString.cpp `AString::Replace (oldString, newString)`: nothing for an empty `oldString` or
    # one equal to `newString` (`strcmp`, 0x8f); else from 0, `Find` (0x6b), `Delete` (0x48), `Insert` (0x55), on past
    # the inserted string while in the string. Stops: the `ret`s (0x84, 0xa6).
    "rpl": dict(grp="Rpl", cn="AString::Replace", a=0x44ced0, n=167, pos=True, stops=(0x84, 0xa6), calls=True,
                tag="PLAN.md §M, M1", src="7-Zip's `AString::Replace` (`CPP/Common/MyString.cpp`; `objdump -d`)"),
    # 7-Zip 26.06 CPP/Common/Wildcard.cpp `CCensorNode::AreAllAllowed ()`: 0 (the `ret`, 0x21) unless `Name` is empty,
    # no `SubNodes`, no `ExcludeItems` and one item of `IncludeItems`; then a tail jump (0x2f) to its `AreAllAllowed`.
    "caa": dict(grp="Caa", cn="NWildcard::CCensorNode::AreAllAllowed", a=0x452b20, n=52, pos=True, stops=(0x21, 0x2f),
                calls=True, tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `CCensorNode::AreAllAllowed` (`CPP/Common/Wildcard.cpp`; `objdump -d`)"),
    # 7-Zip 26.06 CPP/Windows/PropVariant.cpp `CPropVariant::operator= (UInt32)`: `InternalClear ()` (the `call`, 0x16)
    # unless `vt` is `VT_UI4`, then `vt` = `VT_UI4`, `wReserved1` = 0, `ulVal` = the value. Stop: the `ret` (0x3c).
    "pvu": dict(grp="Pvu", cn="CPropVariant::operator=(UInt32)", a=0x457430, n=61, pos=True, stops=(0x3c,), calls=True,
                tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `CPropVariant::operator= (UInt32)` (`CPP/Windows/PropVariant.cpp`; `objdump -d`)"),
    # 7-Zip 26.06 CPP/Common/Wildcard.cpp `ExtractFileNameFromPath (path)`: `path.ReverseFind_PathSepar ()` (the `call`,
    # 0x14), then `UString (path + it + 1)` into the result (0x26). Stop: the `ret` (0x35).
    "efn": dict(grp="Efn", cn="ExtractFileNameFromPath(const UString &)", a=0x4528f0, n=54, pos=True, stops=(0x35,),
                calls=True, tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `ExtractFileNameFromPath` (`CPP/Common/Wildcard.cpp`; `objdump -d`)"),
    # 7-Zip 26.06 CPP/Common/MyString.cpp `UString::Grow_1 ()`: `next = _len + _len / 2 + 16`, rounded down to 16, less
    # 1, capped at `0x3ffffffe` (and so when below `_len`); not above `_len`: a jump to the throw stub (0x2c, `0x4013e4`,
    # by hand); else a tail jump to `ReAlloc (next)` (0x36).
    "ug1": dict(grp="Ug1", cn="UString::Grow_1", a=0x44d0a0, n=59, pos=True, stops=(0x36,), calls=True, hand=(0x2c,),
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `UString::Grow_1` (`CPP/Common/MyString.cpp`; `objdump -d`)"),
    # 7-Zip 26.06 CPP/Common/MyString.cpp `UString::Grow (n)`: nothing (the `ret`, 0x58) when `_limit - _len` is at
    # least `n`; else `next = _len + n`, `next + next / 2 + 16` rounded down to 16, less 1, capped at `0x3ffffffe`
    # (and so when below `_len`); not above `_len`, or less than `n` above it: jumps to the throw stub (0x37, 0x43,
    # `0x401406`, by hand); else a tail jump to `ReAlloc (next - 1)` (0x50).
    "ugr": dict(grp="Ugr", cn="UString::Grow", a=0x44d0e0, n=89, pos=True, stops=(0x50, 0x58), calls=True,
                hand=(0x37, 0x43), tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `UString::Grow` (`CPP/Common/MyString.cpp`; `objdump -d`)"),
    # 7-Zip 26.06 CPP/Common/MyString.cpp `AString::Grow_1 ()`: the bytes of `UString::Grow_1` (`ug1`) but for the
    # jump targets; the throw stub `0x401372` (0x2c, by hand), else a tail jump to `ReAlloc (next)` (0x36).
    "ag1": dict(grp="Ag1", cn="AString::Grow_1", a=0x44c0a0, n=59, pos=True, stops=(0x36,), calls=True, hand=(0x2c,),
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `AString::Grow_1` (`CPP/Common/MyString.cpp`; `objdump -d`)"),
    # 7-Zip 26.06 CPP/Common/MyString.cpp `AString::Grow (n)`: as `UString::Grow` (`ugr`) with other registers (`n` kept
    # in `eax`, `next` in `esi`); nothing (the `ret`, 0x58) when `_limit - _len` is at least `n`; the throw stub
    # `0x401394` (0x3a, 0x46, by hand); else a tail jump to `ReAlloc (next)` (0x50).
    "agr": dict(grp="Agr", cn="AString::Grow", a=0x44c0e0, n=89, pos=True, stops=(0x50, 0x58), calls=True,
                hand=(0x3a, 0x46), tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `AString::Grow` (`CPP/Common/MyString.cpp`; `objdump -d`)"),
    # 7-Zip 26.06 CPP/Common/MyString.cpp `operator+ (const AString &s1, const AString &s2)`: `AString (s1._chars,
    # s1._len, s2._chars, s2._len)` into the result (the `call` at 0x1a, to 0x44c260), the result's address back in
    # `rax`. Stop: the `ret` (0x24).
    "apl": dict(grp="Apl", cn="operator+(const AString &, const AString &)", a=0x44c2b0, n=37, pos=True, stops=(0x24,),
                calls=True, tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `operator+ (const AString &, const AString &)` (`CPP/Common/MyString.cpp`; "
                    "`objdump -d`)"),
    # The same for `UString` (`operator+ (const UString &, const UString &)`, the `call` at 0x1a to 0x44d2e0): the
    # bytes of `apl` but for the `call`'s target.
    "upl": dict(grp="Upl", cn="operator+(const UString &, const UString &)", a=0x44d330, n=37, pos=True, stops=(0x24,),
                calls=True, tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `operator+ (const UString &, const UString &)` (`CPP/Common/MyString.cpp`; "
                    "`objdump -d`)"),
    # 7-Zip 26.06 CPP/Common/MyString.cpp `UString::operator+= (const UString &s)`: `Grow (s._len)` (the `call` at
    # 0x14, to `ugr`), `wmemcpy (_chars + _len, s._chars, s._len + 1)` (the `call` at 0x2f), `_len += s._len`,
    # `this` back in `rax`. Stop: the `ret` (0x46). By hand: `add dword [r12 + 8], eax` (0x37).
    "upe": dict(grp="Upe", cn="UString::operator+=(const UString &)", a=0x44db90, n=71, pos=True, stops=(0x46,),
                hand=(0x37,), calls=True, tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `UString::operator+= (const UString &)` (`CPP/Common/MyString.cpp`; `objdump -d`)"),
    # 7-Zip's C/LzmaDec.c `LzmaDec_AllocateProbs (p, props, propsSize, alloc)`: two pushes (`r12` = `alloc`, `rbx` =
    # `p`), a frame of 24 bytes with the stack guard at `rsp + 8`, `LzmaProps_Decode (&propNew, props, propsSize)`
    # (call at 0x24, `propNew` at `rsp`); when it answers 0, `LzmaDec_AllocateProbs2 (p, &propNew, alloc)` (call at
    # 0x57) and, when that answers 0, `p->prop = propNew` (8 bytes); the guard's check. Stops: the `ret` (0x44), the
    # call of `__stack_chk_fail` (0x69).
    "lpb": dict(grp="Lpb", cn="LzmaDec_AllocateProbs", a=0x42bf10, n=0x6e, pos=True, fs=True, stops=(0x44, 0x69),
                calls=True, tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `LzmaDec_AllocateProbs` (`C/LzmaDec.c`; `objdump -d`)"),
    "usl": dict(grp="Usl", cn="UString::SetStartLen", a=0x44d060, n=54, pos=True, stops=(0x35,), calls=True,
                tag="PLAN.md §M, M1", src="7-Zip's `UString::SetStartLen` (`CPP/Common/MyString.cpp`; `objdump -d`)"),
    # `UString::UString (const UString &s)`: `SetStartLen (s._len)` (the `call` at 0x13 to `usl`), then a tail jump
    # (0x2b) to `wmemcpy (_chars, s._chars, s._len + 1)`.
    "ucc": dict(grp="Ucc", cn="UString::UString(const UString&)", a=0x44d5d0, n=48, pos=True, stops=(0x2b,),
                calls=True, tag="PLAN.md §M, M1",
                src="7-Zip's `UString::UString (const UString &)` (`CPP/Common/MyString.cpp`; `objdump -d`)"),
    # `UString::ReAlloc (newLimit)`: `newBuf = new wchar_t[newLimit + 1]` (the `call` at 0x18), `wmemcpy (newBuf,
    # _chars, _len + 1)` (0x2c), `delete [] _chars` unless null (0x39), `_chars = newBuf`, `_limit = newLimit`. Stop:
    # the `ret` (0x48).
    "ura": dict(grp="Ura", cn="UString::ReAlloc", a=0x44cfc0, n=73, pos=True, stops=(0x48,), calls=True,
                tag="PLAN.md §M, M1", src="7-Zip's `UString::ReAlloc` (`CPP/Common/MyString.cpp`; `objdump -d`)"),
    # `UString::ReAlloc2 (newLimit)`: above `0x3ffffffe` a jump to the throw stub (0xe, `0x4013c2`, by hand); else
    # `newBuf = new wchar_t[newLimit + 1]` (0x23), `newBuf[0] = 0`, `delete [] _chars` unless null (0x39), `_chars =
    # newBuf`, `_limit = newLimit`, `_len = 0`. Stop: the `ret` (0x4f).
    "ur2": dict(grp="Ur2", cn="UString::ReAlloc2", a=0x44d010, n=80, pos=True, stops=(0x4f,), calls=True,
                hand=(0xe,),
                tag="PLAN.md §M, M1", src="7-Zip's `UString::ReAlloc2` (`CPP/Common/MyString.cpp`; `objdump -d`)"),
    # `UString::UString (num, s)`: `num` capped at `s._len` (`cmovbe`), `SetStartLen (num)` (0x1b), `wmemcpy (_chars,
    # s._chars, num)` (0x2b), `_chars[num] = 0`; the `ret` at 0x3f.
    "ucu": dict(grp="Ucu", cn="UString::UString(unsigned, const UString&)", a=0x44d240, n=64, pos=True, stops=(0x3f,),
                calls=True, tag="PLAN.md §M, M1",
                src="7-Zip's `UString::UString (unsigned, const UString &)` (`CPP/Common/MyString.cpp`; `objdump -d`)"),
    # `UString::UString (s1, num1, s2, num2)`: `SetStartLen (num1 + num2)` (0x1e), `wmemcpy (_chars, s1, num1)` (0x30),
    # a tail jump to `wmemcpy (_chars + num1, s2, num2 + 1)` (0x47).
    "uc4": dict(grp="Uc4", cn="UString::UString(const wchar_t*, unsigned, const wchar_t*, unsigned)", a=0x44d2e0,
                n=76, pos=True, stops=(0x47,), calls=True, tag="PLAN.md §M, M1",
                src="7-Zip's `UString::UString (const wchar_t *, unsigned, const wchar_t *, unsigned)` "
                    "(`CPP/Common/MyString.cpp`; `objdump -d`)"),
    # `UString::UString (const wchar_t *s)`: the length `len` of `s` (the loop at 0x20; 0 by 0x50), `SetStartLen (len)`
    # (0x37), a tail jump to `wmemcpy (_chars, s, len + 1)` (0x49).
    "ucw": dict(grp="Ucw", cn="UString::UString(const wchar_t*)", a=0x44d480, n=90, pos=True, stops=(0x49,),
                calls=True, tag="PLAN.md §M, M1",
                src="7-Zip's `UString::UString (const wchar_t *)` (`CPP/Common/MyString.cpp`; `objdump -d`)"),
    # `UString::operator= (const UString &s)`: nothing for `&s` = `this` (0x14); for `s._len` above `_limit` (0x1f)
    # `newBuf = new wchar_t[s._len + 1]` (0x52), `delete [] _chars` unless null (0x63), `_chars = newBuf`, `_limit =
    # s._len`; then `_len = s._len`, `wmemcpy (_chars, s._chars, s._len + 1)` (0x32). Stop: the `ret` (0x44).
    "uau": dict(grp="Uau", cn="UString::operator=(const UString&)", a=0x44d710, n=115, pos=True, stops=(0x44,),
                calls=True, tag="PLAN.md §M, M1",
                src="7-Zip's `UString::operator= (const UString &)` (`CPP/Common/MyString.cpp`; `objdump -d`)"),
    # `UString::UString (num, s)`: the length `n` of `s` (`s[0]` at 0x16, then the loop at 0x20 from the index 1),
    # `min (num, n)` (0x2e), `SetStartLen` (0x41), `wmemcpy (_chars, s, num)` (0x4f), `_chars[num] = 0`, `ret` (0x69).
    "ucn": dict(grp="Ucn", cn="UString::UString(unsigned, const wchar_t*)", a=0x44d1c0, n=122, pos=True, stops=(0x69,),
                calls=True, tag="PLAN.md §M, M1",
                src="7-Zip's `UString::UString (unsigned, const wchar_t *)` (`CPP/Common/MyString.cpp`; `objdump -d`)"),
    # `UString::SetFrom (s, len)`: for `len` above `_limit` (0x17) the throw stub above `0x3ffffffe` (0x56, by hand),
    # else `newBuf = new wchar_t[len + 1]` (0x67), `delete [] _chars` unless null (0x78), `_chars = newBuf`, `_limit =
    # len`; then `wmemcpy (_chars, s, len)` unless `len` = 0 (0x2c), `_chars[len] = 0`, `_len = len`; `ret` (0x48).
    "usf": dict(grp="Usf", cn="UString::SetFrom", a=0x44d790, n=134, pos=True, stops=(0x48,), calls=True,
                hand=(0x56,), tag="PLAN.md §M, M1",
                src="7-Zip's `UString::SetFrom (const wchar_t *, unsigned)` (`CPP/Common/MyString.cpp`; `objdump -d`)"),
    # `UString::operator= (const wchar_t *s)`: the length `n` of `s` (`s[0]` at 0x12, the loop at 0x20 from the index
    # 1); for `n` above `_limit` (0x38) `newBuf = new wchar_t[n + 1]` (0x68), `delete [] _chars` unless null (0x79),
    # `_chars = newBuf`, `_limit = n`; then `_len = n` (0x3e), `wmemcpy (_chars, s, n + 1)` (0x4b). Stop: the `ret` (0x5b).
    "uaw": dict(grp="Uaw", cn="UString::operator=(const wchar_t*)", a=0x44d670, n=155, pos=True, stops=(0x5b,),
                calls=True, tag="PLAN.md §M, M1",
                src="7-Zip's `UString::operator= (const wchar_t *)` (`CPP/Common/MyString.cpp`; `objdump -d`)"),
    # `UString::SetFromBstr (s)`: `len = SysStringLen (s)` (0x17); for `len` above `_limit` (0x21) `newBuf = new
    # wchar_t[len + 1]` (0x52), `delete [] _chars` unless null (0x63), `_chars = newBuf`, `_limit = len`; then `_len =
    # len` (0x27) and a tail jump to `wmemcpy (_chars, s, len + 1)`. Stop: the tail jump (0x3d).
    "usb": dict(grp="Usb", cn="UString::SetFromBstr", a=0x44d820, n=113, pos=True, stops=(0x3d,), calls=True,
                tag="PLAN.md §M, M1",
                src="7-Zip's `UString::SetFromBstr (LPCOLESTR)` (`CPP/Common/MyString.cpp`; `objdump -d`)"),
    "uca": dict(grp="Uca", cn="UString::UString(const char*)", a=0x44d4e0, n=140, pos=True, stops=(0x77,), calls=True,
                tag="PLAN.md §M, M1",
                src="7-Zip's `UString::UString (const char *)` (`CPP/Common/MyString.cpp`; `objdump -d`)"),
    # CPP/UI/Common/EnumDirItems.cpp `CDirItems::ScanProgress (dirPath)`: without a `Callback` (at 0xc0) 0, else a tail
    # jump to `Callback->ScanProgress (Stat, false, dirPath)` (`Stat` at 0x48), its vtable's second entry. Stops: the
    # `jmp rax` (0x26) and the `ret` (0x32).
    "dsp": dict(grp="Dsp", cn="CDirItems::ScanProgress", a=0x5c01d0, n=51, pos=True, stops=(0x26, 0x32),
                tag="PLAN.md §M, M1",
                src="7-Zip's `CDirItems::ScanProgress` (`CPP/UI/Common/EnumDirItems.cpp`; `objdump -d`)"),
    # 7-Zip 26.06's CPP/UI/Common/OpenArchive.cpp `Archive_GetItemBoolProp (arc, index, propID, result)`: `result`
    # false, a `CPropVariant` on the stack (`vt` 0), `arc->GetProperty (index, propID, &prop)` (the `call [rax +
    # 0x30]` at 0x3b); its result if not 0, else `VT_BOOL`: `result` = `boolVal != 0`, `VT_EMPTY`: S_OK, else
    # E_FAIL; `~CPropVariant` (the `call` at 0x5e), the stack guard. Stops: the `ret` (0x7e), `__stack_chk_fail`
    # (0x8b).
    # CPP/Common/MyVector.h `CObjectVector<CRecordVector<unsigned>>::~CObjectVector ()`: from the last item down,
    # `delete [] item->_items` (the `call` at 0x32, when not null) and `delete item` (the `call` at 0x3f, 16 bytes),
    # then `delete [] _items` as a tail jump (0x5b) when not null, else the `ret` (0x64).
    # 7-Zip's `SortFileNames (strings, indices)`: `indices` cleared and reserved for the `strings.Size ()` indices
    # (`operator delete` of the old ones, 0x4a, `operator new[]`, 0x65; `js` to the cold throw when negative), filled
    # with 0..n-1 (0x90), then a heap sort by `CompareFileNames` (0x5dca50) through the indices: the heap built
    # (0xd0, sift down from 0x11f), then the largest swapped out (0x1c1, sift down from 0x208); the stack guard
    # (`fs:0x28`). Stops: the `ret` (0x1b2), `__stack_chk_fail` (0x27c). By hand: the `js` (0x3c; its target is
    # outside), `sub qword [rsp + 0x20], 2` (0x17a; `Seg.s_sub_mi64`, FV7z/Lemmas/Rmw8.lean).
    "sfn": dict(grp="Sfn", cn="SortFileNames", a=0x5dca70, n=641, pos=True, fs=True, stops=(0x1b2, 0x27c),
                hand=(0x3c, 0x17a),
                calls=True, tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `SortFileNames` (`CPP/7zip/UI/Common/SortUtils.cpp`; `objdump -d`)"),
    "msi": dict(grp="Msi", cn="CMultiStreams::Init", a=0x5b3260, n=125, pos=True, stops=(0x7c,), calls=True,
                tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `CMultiStreams::Init` (`CPP/7zip/Archive/Common/MultiStream.cpp`; `objdump -d`)"),
    "ocv": dict(grp="Ocv", cn="CObjectVector<CRecordVector<unsigned>>::~CObjectVector", a=0x454600, n=101, pos=True,
                stops=(0x5b, 0x64), calls=True, tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `CObjectVector<CRecordVector<unsigned>>::~CObjectVector` (`CPP/Common/MyVector.h`; "
                    "`objdump -d`)"),
    "gbp": dict(grp="Gbp", cn="Archive_GetItemBoolProp", a=0x5d15e0, n=144, pos=True, fs=True, stops=(0x7e, 0x8b),
                hand=(0x86,),
                calls=True, tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `Archive_GetItemBoolProp` (`CPP/UI/Common/OpenArchive.cpp`; `objdump -d`)"),
    # C/7zStream.c `InStream_AtBegin_GetSize (stream, sizeRes)`: `stream->Seek (stream, sizeRes, SZ_SEEK_END)` (the
    # `call [rax + 0x20]` at 0x1b), then `InStream_SeekToBegin (stream)` (the `call` at 0x24); the first's result
    # if not 0, else the second's. Stop: the `ret` (0x3a).
    "iag": dict(grp="Iag", cn="InStream_AtBegin_GetSize", a=0x463200, n=59, pos=True, stops=(0x3a,), calls=True,
                tag="PLAN.md §M, M1", src="7-Zip's `InStream_AtBegin_GetSize` (`C/7zStream.c`; `objdump -d`)"),
    # 7-Zip's CPP/Common/MyString.cpp `IsString1PrefixedByString2_NoCase_Ascii (u, a)`: each `char` of `a` up to its
    # 0 equal to the `wchar_t` of `u` at its index, ASCII letters without case: 1, else 0. Stops: the `ret`s (0x5d: 1,
    # 0x62: 0).
    "isp": dict(grp="Isp", cn="IsString1PrefixedByString2_NoCase_Ascii", a=0x44bde0, n=99, pos=True,
                stops=(0x5d, 0x62), tag="PLAN.md §M, M1",
                src="7-Zip's `IsString1PrefixedByString2_NoCase_Ascii` (`CPP/Common/MyString.cpp`; `objdump -d`)"),
    # `UString::Delete (index, count)`: `count` cut to `_len - index`; if not 0, `memmove` (the `call` at 0x4f, the
    # PLT entry) of the rest down and `_len` - `count`. Stops: the `ret`s (0x25, 0x5d).
    "udl": dict(grp="Udl", cn="UString::Delete", a=0x44e0b0, n=94, pos=True, stops=(0x25, 0x5d), calls=True,
                hand=(0x54,), tag="PLAN.md §M, M1", src="7-Zip's `UString::Delete` (`CPP/Common/MyString.cpp`; `objdump -d`)"),
    # 7-Zip's CPP/Windows/FileIO.cpp `CFileBase::seek (off, whence)`: the descriptor (`this->_handle`, at 0), then
    # `lseek`. Stop: the `jmp` to `__libc_lseek` (6), a branch to another segment (`Seg.s_jmp_x`).
    "fsk": dict(grp="Fsk", cn="NWindows::NFile::NIO::CFileBase::seek", a=0x4560b0, n=11, pos=True, stops=(6,),
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `CFileBase::seek` (`CPP/Windows/FileIO.cpp`; `objdump -d`)"),
    # glibc 2.31 sysdeps/unix/sysv/linux/write.c (`SYSCALL_CANCEL`). Stops: the `ret` (0x1f), the process has more
    # than one thread (0x20: `multiple_threads` is not 0), the `ret` after `errno` is set (0x83); the `syscall` (0x15)
    # is a step of its own.
    "wrt": dict(grp="Write", cn="__libc_write", a=0x5ff270, n=0x99, pos=True, fs=True, stops=(0x1f, 0x20, 0x83),
                calls=True, tag="PLAN.md §M, M1",
                src="glibc 2.31's `__libc_write` (`sysdeps/unix/sysv/linux/write.c`; `objdump -d`)"),
    # glibc 2.31 sysdeps/unix/sysv/linux/open64_nocancel.c (`__open64_nocancel`, `openat (AT_FDCWD, …)`). Stops: the
    # `ret` (0x68), the padding after it (0x69), the flags have `O_CREAT` or `O_TMPFILE` (0x70: the mode from the
    # `va_list`), the padding after that (0x92), `__stack_chk_fail` (0xab); the `syscall` (0x4a) is a step of its own.
    "onc": dict(grp="Onc", cn="__open64_nocancel", a=0x666090, n=0xb0, pos=True, fs=True,
                stops=(0x68, 0x69, 0x70, 0x92, 0xab), calls=True, tag="PLAN.md §M, M1",
                src="glibc 2.31's `__open64_nocancel` (`sysdeps/unix/sysv/linux/open64_nocancel.c`; `objdump -d`)"),
    # glibc 2.31 sysdeps/unix/sysv/linux/syscall-template.S (`__munmap`). Stops: the `ret` (0x13), the `ret` after
    # `errno` is set (0x24); the `syscall` (9) is a step of its own.
    "mun": dict(grp="Mun", cn="__munmap", a=0x6665d0, n=37, pos=True, fs=True, stops=(0x13, 0x24), calls=True,
                tag="PLAN.md §M, M1",
                src="glibc 2.31's `__munmap` (`sysdeps/unix/sysv/linux/syscall-template.S`; `objdump -d`)"),
    # glibc 2.31 sysdeps/unix/sysv/linux/mmap64.c (`__mmap64`). Stops: the `ret` (0x30), the padding after it (0x31),
    # an offset not a page's (0x38: `EINVAL`), `PROT_EXEC` asked for without an address (0x55: the `MAP_32BIT` try of
    # `MMAP_PREPARE`); the `syscall` (0x24) is a step of its own.
    "mmp": dict(grp="Mmp", cn="__mmap", a=0x666520, n=0xa5, pos=True, fs=True, stops=(0x30, 0x31, 0x38, 0x55),
                calls=True, tag="PLAN.md §M, M1",
                src="glibc 2.31's `__mmap64` (`sysdeps/unix/sysv/linux/mmap64.c`; `objdump -d`)"),
    # glibc 2.31 sysdeps/unix/sysv/linux/getdtsz.c (`__getdtablesize`: `RLIMIT_NOFILE`'s soft limit, or 256). Stops:
    # the `ret` (0x44), `__stack_chk_fail` (0x45); the `call` of `__getrlimit` (0x20) is a cut point.
    # glibc 2.31 sysdeps/unix/sysv/linux/isatty.c (`__isatty`, `__tcgetattr (fd, &term) == 0`). Stops: the `ret`
    # (0x3c) and the stack guard's failure call (0x3d).
    "ity": dict(grp="Ity", cn="__isatty", a=0x665d20, n=0x42, pos=True, fs=True, stops=(0x3c, 0x3d),
                calls=True, tag="PLAN.md §M, M1",
                src="glibc 2.31's `__isatty` (`sysdeps/unix/sysv/linux/isatty.c`; `objdump -d`)"),
    # glibc 2.31 signal/signal.c `__bsd_signal (sig, handler)`, the part after the range check: a frame of 0x148 bytes
    # with the stack guard, `sa_mask` zeroed (`rep stos`, by hand: 0x39) with `sig`'s bit set, `sa_flags` SA_RESTART
    # unless `sig` is in `_sigintr`, `__sigaction` (the `call`, 0x67), the old handler or -1. Stops: the `ret` (0x98),
    # its padding guard `__stack_chk_fail` (0x99).
    "bsg": dict(grp="Bsg", cn="__bsd_signal.part.0", a=0x622510, n=0x9e, pos=True, fs=True, stops=(0x98, 0x99),
                calls=True, hand=(0x39, 0x4b), tag="PLAN.md §M, M1",
                src="glibc 2.31's `__bsd_signal` (`signal/signal.c`; `objdump -d`)"),
    "gdt": dict(grp="Gdt", cn="__getdtablesize", a=0x6664a0, n=0x4a, pos=True, fs=True, stops=(0x44, 0x45),
                calls=True, tag="PLAN.md §M, M1",
                src="glibc 2.31's `__getdtablesize` (`sysdeps/unix/sysv/linux/getdtsz.c`; `objdump -d`)"),
    # glibc 2.31 sysdeps/unix/sysv/linux/tcgetattr.c (`__tcgetattr`, `ioctl (fd, TCGETS, &k_termios)`). Stops: the
    # copy of the settings, the kernel's answer 0 (0x4b: `movdqa xmm0, [rsp]`, an aligned load of the stack), the
    # `ret` (0xa6), the padding after it (0xa7), `__stack_chk_fail` (0xc4); the `syscall` (0x28) is a step of its own.
    "tcg": dict(grp="Tcg", cn="__tcgetattr", a=0x666240, n=0xc9, pos=True, fs=True,
                stops=(0x4b, 0xa6, 0xa7, 0xc4), calls=True, tag="PLAN.md §M, M1",
                src="glibc 2.31's `__tcgetattr` (`sysdeps/unix/sysv/linux/tcgetattr.c`; `objdump -d`)"),
    # The copy of the settings in `__tcgetattr` after the kernel's answer 0, from after the two loads into `xmm0` and
    # `xmm1` (0x56) to the first `movups` store (0x86): the `xmm` moves are steps of their own (FV7z/Tcg/Copy.lean).
    "tcc": dict(grp="TcgC", code=("Tcg", "tcg"), cn="__tcgetattr", a=0x666240, n=0xc9, entry=0x56, pos=True,
                stops=(0x86,), tag="PLAN.md §M, M1",
                src="glibc 2.31's `__tcgetattr` (`sysdeps/unix/sysv/linux/tcgetattr.c`; `objdump -d`)"),
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
    # 7-Zip's static constructor `csuTg 75` (0x41c770, offset 1584 of `sti`): a table of 256 bytes at 0x79d340, each
    # its index with the bits reversed. Stop: the `ret` (1665).
    # 7-Zip's static constructor `csuTg 70` (0x41c6e0, offset 1440 of `sti`): the CRC-16 table (polynomial 0x1021)
    # of 256 words at 0x79d140, two loops. Stop: the `ret` (1514).
    "c70": dict(grp="C70", code=("Ctor", "sti"), cn="csuTg 70", a=0x41c140, n=4624, entry=1440, pos=True,
                stops=(1514,), tag="PLAN.md G3, constructors",
                src="a static constructor of 7-Zip (`objdump -d`)"),
    # The CRC tables a constructor jumps to (`endbr64; jmp F`), named by their shape after 7-Zip's source: m = 78
    # (CRC-32 MSB first for bzip2, 0x79d440), 3 (CRC-32 and its slicing tables, 0x7a4e00), 15 (CRC-64 and its slicing
    # tables, 0x7967c0).
    "c78": dict(grp="C78", cn="CBZip2Crc::InitTable", a=0x56c470, n=0x44, entry=0, pos=True, stops=(0x43,),
                tag="PLAN.md G3, constructors", src="a function a static constructor of 7-Zip jumps to (`objdump -d`)"),
    "c3": dict(grp="C3", cn="CrcGenerateTable", a=0x41d5e0, n=0x6b, entry=0, pos=True, stops=(0x6a,),
               tag="PLAN.md G3, constructors", src="a function a static constructor of 7-Zip jumps to (`objdump -d`)"),
    "c15": dict(grp="C15", cn="Crc64GenerateTable", a=0x443e70, n=0x8f, entry=0, pos=True, stops=(0x8e,),
                tag="PLAN.md G3, constructors", src="a function a static constructor of 7-Zip jumps to (`objdump -d`)"),
    # 7-Zip's static constructors `csuTg 37` (0x41c380, offset 576 of `sti`) and `csuTg 55` (0x41c560, offset 1056): a
    # CRC table in two loops (CRC-16 with the polynomial 0xa001, 256 words at 0x79cb40; CRC-32C, 256 dwords at
    # 0x79cd40), then `lea rdi, [rip + d]; jmp RegisterArc`. Stop: the `jmp` (644, 1123).
    "c37": dict(grp="C37", code=("Ctor", "sti"), cn="csuTg 37", a=0x41c140, n=4624, entry=576, pos=True,
                stops=(644,), tag="PLAN.md G3, constructors",
                src="a static constructor of 7-Zip (`objdump -d`)"),
    "c55": dict(grp="C55", code=("Ctor", "sti"), cn="csuTg 55", a=0x41c140, n=4624, entry=1056, pos=True,
                stops=(1123,), tag="PLAN.md G3, constructors",
                src="a static constructor of 7-Zip (`objdump -d`)"),
    # `subb $1, [rip + d]` (a byte at 0x7921b0), then `lea rdi, [rip + d]; jmp RegisterArc`. Stop: the `jmp` (1234).
    "c61": dict(grp="C61", code=("Ctor", "sti"), cn="csuTg 61", a=0x41c140, n=4624, entry=1216, pos=True,
                stops=(1234,), tag="PLAN.md G3, constructors",
                src="a static constructor of 7-Zip (`objdump -d`)"),
    "c75": dict(grp="C75", code=("Ctor", "sti"), cn="csuTg 75", a=0x41c140, n=4624, entry=1584, pos=True,
                stops=(1665,), tag="PLAN.md G3, constructors",
                src="a static constructor of 7-Zip (`objdump -d`)"),
    # `csuTg 82` (0x41c8a0, offset 1888 of `sti`) and `csuTg 87` (0x41c9b0, offset 2160): loops that fill tables
    # from tables of `.rodata` (Deflate's length and distance slots).
    "c82": dict(grp="C82", code=("Ctor", "sti"), cn="csuTg 82", a=0x41c140, n=4624, entry=1888, pos=True,
                stops=(2081,), tag="PLAN.md G3, constructors",
                src="a static constructor of 7-Zip (`objdump -d`)"),
    # glibc's `init_cacheinfo` (`sysdeps/x86/cacheinfo.c`), `csuTg 103` (0x41cef0, offset 3504 of `sti`): by the
    # vendor of `init_cpu_features` (0x7a4b48), `handle_intel` or `handle_amd` for the three cache sizes, the
    # threads that share a cache from `cpuid` leaves 4 and 0xb (loops over subleaves), the stores of `__x86_*`. Stop:
    # the `ret` (3731). By hand: `cpuid` (`Seg.s_cpuid`), `idiv` (`Seg.s_idiv64`), `bsr` (`Seg.s_bsr32`).
    "c103": dict(grp="C103", code=("Ctor", "sti"), cn="csuTg 103", a=0x41c140, n=4624, entry=3504, pos=True,
                 stops=(3731,), calls=True, jt=(0x6f20a4, 39),
                 hand=(3865, 4079, 4100, 4141, 4197, 4346, 3707, 3981, 4005, 4223, 4380, 4454, 4594),
                 tag="PLAN.md M, ctor 103", src="glibc's `init_cacheinfo` (`sysdeps/x86/cacheinfo.c`; `objdump -d`)"),
    # glibc's `handle_amd` (`sysdeps/x86/cacheinfo.c`, 0x65cb10), the size of a cache from `cpuid` 0x80000005 or
    # 0x80000006; its group's code (`hca`, 1624 bytes) also holds `intel_check_word` and `handle_intel`. `jt`: the
    # `switch` on the name. Stops: the cases of an associativity or a line size (0x68, 0x88, 0xb0, 0xd8, 0x100,
    # 0x120; init_cacheinfo asks for sizes only) and a name out of range (0x1b0, `__assert_fail`). By hand: `cpuid`.
    "hca": dict(grp="Hca", cn="handle_amd", a=0x65cb10, n=1624, pos=True, calls=True, jt=(0x6f2000, 9),
                stops=(0x68, 0x88, 0xb0, 0xd8, 0x100, 0x120, 0x1b0), hand=(6, 39), tag="PLAN.md M, ctor 103",
                src="glibc's `handle_amd`, `intel_check_word` and `handle_intel` (`sysdeps/x86/cacheinfo.c`; "
                    "`objdump -d`)"),
    # glibc's `intel_check_word` (0x65cce0, offset 464 of `hca`): the descriptor bytes of a `cpuid` 2 word, by a
    # binary search of `intel_02_known` (0x6f2140) or `cpuid` 4's subleaves. Stops: the two `assert`s on the name
    # (1085, 1116; the name's offset is 0 for the three sizes). By hand: `cpuid`.
    "icw": dict(grp="Icw", code=("Hca", "hca"), cn="intel_check_word", a=0x65cb10, n=1624, entry=464, pos=True,
                calls=True, stops=(1085, 1116), hand=(773, 829, 1172, 1258), tag="PLAN.md M, ctor 103",
                src="glibc's `intel_check_word` (`sysdeps/x86/cacheinfo.c`; `objdump -d`)"),
    # glibc's `handle_intel` (0x65d010, offset 1280 of `hca`): `cpuid` 2's rounds, `intel_check_word` for each of
    # the four words, the stack protector's check. Stop: `__stack_chk_fail` (1619). By hand: `cpuid`.
    "hin": dict(grp="Hin", code=("Hca", "hca"), cn="handle_intel", a=0x65cb10, n=1624, entry=1280, pos=True,
                fs=True, calls=True, stops=(1619,), hand=(1376,), tag="PLAN.md M, ctor 103",
                src="glibc's `handle_intel` (`sysdeps/x86/cacheinfo.c`; `objdump -d`)"),
    # 7-Zip's `CCriticalSection` constructor (`C/Threads.c`, `CriticalSection_Init`): `pthread_mutex_init (m, NULL)`
    # for `m` not null. Stops: the tail jump (0xb), `m` null (0x10).
    "mxs": dict(grp="Mxs", cn="CriticalSection_Init", a=0x448b40, n=0x16, pos=True, stops=(0xb, 0x10),
                tag="PLAN.md G3, constructors", src="7-Zip's `CriticalSection_Init` (`C/Threads.c`; `objdump -d`)"),
    # glibc 2.31 nptl/pthread_mutex_init.c, the way of a null `attr`. Stops: `attr` not null (0x2a),
    # `__stack_chk_fail` (0x1d8). `vop`: the zeroing through `xmm0`.
    "mxi": dict(grp="Mxi", cn="__pthread_mutex_init", a=0x5fbb20, n=0x1dd, pos=True, fs=True, vop=True,
                stops=(0x2a, 0x1d8), tag="PLAN.md G3, constructors",
                src="glibc 2.31's `__pthread_mutex_init` (`nptl/pthread_mutex_init.c`; `objdump -d`)"),
    "c87": dict(grp="C87", code=("Ctor", "sti"), cn="csuTg 87", a=0x41c140, n=4624, entry=2160, pos=True,
                stops=(2387,), tag="PLAN.md G3, constructors",
                src="a static constructor of 7-Zip (`objdump -d`)"),
    "rfi": dict(grp="Rfi", cn="__register_frame_info", a=0x612730, n=0xd1, entry=0xb0, pos=True,
                stops=(0x6a, 0x76, 0x90, 0xa8, 0xd0), calls=True, tag="PLAN.md G3, startup",
                src="libgcc's `__register_frame_info` (`libgcc/unwind-dw2-fde.c`; `objdump -d`)"),
    # libgcc's crtstuff.c in crtbegin.o: `frame_dummy` (0x41d440, the first entry of `.init_array`). Stops: the two
    # `jmp register_tm_clones` (0x22, 0x30; `register_tm_clones` is `rtc`), by hand.
    "fdm": dict(grp="Fdm", cn="frame_dummy", a=0x41d440, n=0x35, pos=True,
                stops=(0x22, 0x30), calls=True, tag="PLAN.md G3, startup",
                src="libgcc's `frame_dummy` (`libgcc/crtstuff.c`; `objdump -d`)"),
    # glibc's `__default_morecore` (`malloc/morecore.c`): `__sbrk (n)`, a null pointer for its -1.
    # 7-Zip's registrars, which the constructors of `.init_array` call (`CPP/7zip/Archive/ArchiveExports.cpp`,
    # `CPP/7zip/Common/CreateCoder.cpp`): the pointer into the table if there is room. Stop: the `ret`.
    "rga": dict(grp="Rga", cn="RegisterArc", a=0x5ceb20, n=38, pos=True, stops=(0x25,),
                tag="PLAN.md §M, constructors",
                src="7-Zip's `RegisterArc` (`CPP/7zip/Archive/ArchiveExports.cpp`; `objdump -d`)"),
    "rgc": dict(grp="Rgc", cn="RegisterCodec", a=0x458e60, n=35, pos=True, stops=(0x22,),
                tag="PLAN.md §M, constructors",
                src="7-Zip's `RegisterCodec` (`CPP/7zip/Common/CreateCoder.cpp`; `objdump -d`)"),
    "rgh": dict(grp="Rgh", cn="RegisterHasher", a=0x458e90, n=35, pos=True, stops=(0x22,),
                tag="PLAN.md §M, constructors",
                src="7-Zip's `RegisterHasher` (`CPP/7zip/Common/CreateCoder.cpp`; `objdump -d`)"),
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
    # glibc 2.31 malloc/malloc.c, the way of the first call (`tcache_init`'s, of 0x280 bytes: the main arena, its bins
    # empty, its top the initial one, so `sysmalloc`). Stops: the branches that way does not take, and the `ret`
    # (0x3b6). `cmp qword fs:[-0x28], 0` (1087) is the test of the thread's cache.
    # The same function on the second call (`malloc (50)` after `tcache_init`: `nb` 64, a small bin, empty; the thread's
    # cache there; the top from the first call, large enough, so it is split). Stops: the branches that way does not
    # take, and the `ret` (0x3b6).
    "im2": dict(grp="Im2", code=("Imm", "imm"), cn="_int_malloc", a=0x630be0, n=3702, pos=True, fs=True,
                stops=(0x2e, 0x6a, 0x154, 0x244, 0x47f, 0x610, 0x63e, 0x7b9, 0x808, 0xa1b, 0xc07, 0xc20, 0xc38, 0xcc0,
                       0x3b6),
                calls=True, tag="PLAN.md G3, `malloc`",
                src="glibc 2.31's `_int_malloc` (`malloc/malloc.c`; `objdump -d`)"),
    # The same function on the second call for a request `n ≤ 8` (`nb` = `MINSIZE` 32): `0 → 63 → 544 → 563`, then the
    # way of `im2` (gdb trace of `n` = 1 and 8). Stops: the branches that way does not take before 1115, 1115 itself
    # (`im2`'s cut point, where the proof goes on), and the `ret` (0x3b6).
    "im3": dict(grp="Im3", code=("Imm", "imm"), cn="_int_malloc", a=0x630be0, n=3702, pos=True, fs=True,
                stops=(0x45, 0x6a, 0x130, 0x244, 0x45b, 0x47f, 0x610, 0x638, 0x3b6),
                calls=True, tag="PLAN.md G3, `malloc`",
                src="glibc 2.31's `_int_malloc` (`malloc/malloc.c`; `objdump -d`)"),
    # The same function on the second call for a request `121 ≤ n ≤ 1000` (`nb` 144 … 1008, a smallbin size):
    # `0 → 304 → 346 → 848`, then the way of `im2` from 848 (gdb trace of `n` = 121, 500 and 1000). Stops: the
    # branches that way does not take before 1115, 1115 itself and the `ret`.
    "im4": dict(grp="Im4", code=("Imm", "imm"), cn="_int_malloc", a=0x630be0, n=3702, pos=True, fs=True,
                stops=(0x2e, 0x6a, 0x160, 0x3c0, 0x45b, 0x47f, 0x610, 0x63e, 0x3b6),
                calls=True, tag="PLAN.md G3, `malloc`",
                src="glibc 2.31's `_int_malloc` (`malloc/malloc.c`; `objdump -d`)"),
    # The same function on the second call for a request `1001 ≤ n ≤ 4096` (`nb` 1024 … 4112, a largebin size): the
    # index `48 + (nb >> 6)` (480) or `91 + (nb >> 9)` (490), no `malloc_consolidate` (517), from 1115 the unsorted bin
    # empty, the largebin of `nb` empty (2000), the binmap from block 2 (exit 2511) or 3 (exit 2486) on to 2549 (gdb
    # trace of `n` = 2000 and 4096). Stops: the branches that way does not take, 2549 itself and the `ret`.
    "im5": dict(grp="Im5", code=("Imm", "imm"), cn="_int_malloc", a=0x630be0, n=3702, pos=True, fs=True,
                stops=(0x2e, 0x1ec, 0x20b, 0x350, 0x3c0, 0x47f, 0x610, 0x63e, 0x7d2, 0x808, 0x9d1, 0x9f5, 0xc07, 0x3b6),
                calls=True, tag="PLAN.md G3, `malloc`",
                src="glibc 2.31's `_int_malloc` (`malloc/malloc.c`; `objdump -d`)"),
    # The same function on the second call for a request `nb >> 12 > 10` with `nb >> 15 < 5` (`nb` 45056 … 163824,
    # largebin index `110 + (nb >> 15)`): the way of `im5` but through 492 and 2192 (gdb trace of `n` = 72704,
    # `private/recon/malloc102.trace`). Stops: those of `im5` but 492, and 507 (`nb >> 12 ≤ 10`).
    "im6": dict(grp="Im6", code=("Imm", "imm"), cn="_int_malloc", a=0x630be0, n=3702, pos=True, fs=True,
                stops=(0x2e, 0x1fb, 0x20b, 0x350, 0x3c0, 0x47f, 0x610, 0x63e, 0x7d2, 0x808, 0x9d1, 0x9f5, 0xc07, 0x3b6),
                calls=True, tag="PLAN.md G3, `malloc`",
                src="glibc 2.31's `_int_malloc` (`malloc/malloc.c`; `objdump -d`)"),
    # The same function on the second call for every largebin request (`nb > 1023`): the index by any of the three
    # ways (480: `48 + (nb >> 6)`, 490: `91 + (nb >> 9)`, 507: `110 + (nb >> 12)`, 2192: the `cmovb` of `119 +
    # (nb >> 15)` and `124 + min (nb >> 18, 2)`), then as `im5`/`im6`. Stops: those of `im6` but 507.
    "im7": dict(grp="Im7", code=("Imm", "imm"), cn="_int_malloc", a=0x630be0, n=3702, pos=True, fs=True,
                stops=(0x2e, 0x20b, 0x350, 0x3c0, 0x47f, 0x610, 0x63e, 0x7d2, 0x808, 0x9d1, 0x9f5, 0xc07, 0x3b6),
                calls=True, tag="PLAN.md G3, `malloc`",
                src="glibc 2.31's `_int_malloc` (`malloc/malloc.c`; `objdump -d`)"),
    "imm": dict(grp="Imm", cn="_int_malloc", a=0x630be0, n=3702, pos=True, fs=True,
                stops=(0x2e, 0x6a, 0x160, 0x3c0, 0x44b, 0x47f, 0x610, 0x63e, 0x7b9, 0x808, 0x988, 0x9e7, 0xa2b, 0xc07,
                       0xc20, 0xc77, 0xcef, 0x3b6),
                calls=True, tag="PLAN.md G3, `malloc`",
                src="glibc 2.31's `_int_malloc` (`malloc/malloc.c`; `objdump -d`)"),
    # glibc 2.31 malloc/malloc.c (`tcache_init`), the way of one thread with the arena set by `ptmalloc_init`. Stops:
    # no arena yet (0xa0: `get_free_list`/`arena_get2`), more than one thread (0x110: `lock cmpxchg`; 0x130: `xchg`),
    # `_int_malloc` gave null (0xe0: `arena_get_retry`), the `ret` (0x96). By hand:
    # `cmpxchg [rbp], edx` (0x2a), `sub dword [rbp], 1` (0x57), `rep stos` (0x92).
    "tci": dict(grp="Tci", cn="tcache_init", a=0x631a60, n=346, pos=True, fs=True,
                stops=(0xa0, 0x110, 0xe0, 0x130, 0x96), calls=True, hand=(0x2a, 0x57, 0x92),
                tag="PLAN.md G3, `malloc`", src="glibc 2.31's `tcache_init` (`malloc/malloc.c`; `objdump -d`)"),
    # glibc 2.31 malloc/hooks.c (`malloc_hook_ini`) with `__libc_malloc` inlined, the way of the first `malloc`: not
    # initialized yet (`ptmalloc_init`), no hook after it, the thread's cache not made yet (`tcache_init`), its bin
    # empty, one thread, `_int_malloc` of the main arena, a chunk not mapped of the main arena. Stops: the branches
    # that way does not take, and the `ret` (0xbb).
    "mhi": dict(grp="Mhi", cn="malloc_hook_ini", a=0x632ba0, n=832, pos=True, fs=True,
                stops=(0x24, 0x165, 0x188, 0x56, 0x120, 0x1a8, 0x178, 0x9a, 0xbb), calls=True,
                tag="PLAN.md G3, `malloc`", src="glibc 2.31's `malloc_hook_ini` (`malloc/hooks.c`; `objdump -d`)"),
    # glibc 2.31 malloc/malloc.c (`__libc_malloc`), the way of a hook set (the first call: `__malloc_hook` =
    # `malloc_hook_ini`): three pushes, the hook read, three pops, `jmp rax` with the return address in `rsi`. Stops:
    # no hook (0x1b), the `jmp rax` (0x179, by hand).
    "mal": dict(grp="Mal", cn="__libc_malloc", a=0x633160, n=784, pos=True, stops=(0x1b, 0x179),
                tag="PLAN.md G3, `malloc`", src="glibc 2.31's `__libc_malloc` (`malloc/malloc.c`; `objdump -d`)"),
    # glibc 2.31 malloc/malloc.c (`__libc_malloc`), the way of a call after the first (`__malloc_hook` null, the
    # tcache made, one thread): `tc_idx`, the tcache's count, `_int_malloc (&main_arena, n)` (0x6d), the chunk's
    # flags. Stops: the `ret` (0xab), `_int_malloc` gave null (0x140), `n` negative (0x150), the hook set (0x170),
    # more than one thread (0x180), no tcache (0xc8), not of the main arena (0x2e6). A chunk in the tcache (0x110):
    # `tcache_get`, then 0xa4.
    "mnx": dict(grp="Mnx", cn="__libc_malloc", a=0x633160, n=784, pos=True, fs=True,
                stops=(0xab, 0x140, 0x150, 0x170, 0x180, 0xc8, 0x2e6), calls=True,
                tag="PLAN.md G3, `malloc`", src="glibc 2.31's `__libc_malloc` (`malloc/malloc.c`; `objdump -d`)"),
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
    # glibc 2.31 sysdeps/unix/sysv/linux/dl-origin.c. Stops: `_dl_origin_path` is set (0xa4; `LD_ORIGIN_PATH` unset
    # leaves it null), the `ret` (0x10f), the link's contents do not start with `/` (0x136: `__assert_fail`). The
    # `syscall` (`readlink`, 0x31) and the `call`s of `malloc` (0x7c, 0x116) and `mempcpy` (0x12c) are cut points.
    # By hand: the stack probe `or qword [rsp], 0` (0x11).
    # glibc 2.31 elf/dl-hwcaps.c, the way without a vDSO (`_dl_sysinfo_map` null) and with 3 or 4 capabilities (the
    # platform, `x86_64`, maybe `avx512_1`, `tls`). Stops (from gdb traces with `_dl_hwcap` 2 and 6): the vDSO's
    # notes (0xa6), the `ret` (0x691), more than 6 capabilities (0x339, 0x3cd), a stack probe of a page (0x7ca), one
    # capability (0x81e), too many bytes or `malloc` gave null (0x83e, 0x853), an empty platform (0x85b, 0x8d8),
    # the counts disagree (0x90a). By hand: the stack probe `or qword [rsp + rax - 8], 0` (0x6ec).
    "hwc": dict(grp="Hwc", cn="_dl_important_hwcaps", a=0x6ad140, n=2345, pos=True, fs=True,
                stops=(0xa6, 0x691, 0x339, 0x3cd, 0x7ca, 0x81e, 0x83e, 0x853, 0x85b, 0x8d8, 0x90a), calls=True,
                hand=(0x6ec,), tag="PLAN.md G3, startup", src="glibc 2.31's `_dl_important_hwcaps` (`elf/dl-hwcaps.c`; `objdump -d`)"),
    # glibc 2.31 elf/dl-load.c, `_dl_init_paths (llp)` with `llp` null (`LD_LIBRARY_PATH` unset): the hwcaps, the
    # 4 system directories, `env_path_list` -1. Stops: `llp` not null (0x1c3), a system directory not starting with
    # `/` (0x2e7: `__assert_fail`), `malloc` gave null (0x306, 0x31b: `_dl_signal_error`). The `call`s of
    # `_dl_important_hwcaps` (0x35), `malloc` (0x46, 0x94) and `memset` (0x114) are cut points.
    "ipa": dict(grp="Ipa", cn="_dl_init_paths", a=0x6a88f0, n=816, pos=True, stops=(0x1c3, 0x2e7, 0x306, 0x31b),
                calls=True, tag="PLAN.md G3, startup",
                src="glibc 2.31's `_dl_init_paths` (`elf/dl-load.c`; `objdump -d`)"),
    "gor": dict(grp="Gor", cn="_dl_get_origin", a=0x6aefa0, n=352, pos=True, stops=(0xa4, 0x10f, 0x136), calls=True,
                hand=(0x11,),
                tag="PLAN.md G3, startup",
                src="glibc 2.31's `_dl_get_origin` (`sysdeps/unix/sysv/linux/dl-origin.c`; `objdump -d`)"),
    # 7-Zip's `ParseComplexSize` (CPP/7zip/UI/Common/OpenArchive.cpp): a number, then nothing or one of `b`, `k`,
    # `m`, `g`, `t` (either case). `jt`: the `switch` on the suffix, less 'b'. Stops: the `ret` (0xa6), the padding
    # after it (0xa7), `__stack_chk_fail` (0x10c); the `call` of `ConvertStringToUInt64` (0x2a) is a cut point.
    "pcs": dict(grp="Pcs", cn="ParseComplexSize", a=0x5d38f0, n=273, pos=True, fs=True, stops=(0xa6, 0xa7, 0x10c),
                calls=True, jt=(0x6e8e8c, 19), tag="PLAN.md §M, M1",
                src="7-Zip's `ParseComplexSize` (`CPP/7zip/UI/Common/OpenArchive.cpp`; `objdump -d`)"),
    # glibc 2.31 nptl/pthread_once.c `__pthread_once_slow (once_control, init_routine)`: done (bit 2), the answer 0;
    # else `lock cmpxchg` takes the word from its value to `__fork_generation | 1`; another thread at it (bit 0 of the
    # same generation) is waited for (`futex` wait); else `_pthread_cleanup_push`, `init_routine ()` (`call rbx`),
    # `_pthread_cleanup_pop`, the word 2 and a `futex` wake. Stops: the `ret` (0x4f), the wait (the `syscall` at
    # 0x76), `__libc_fatal` (0x95), `__stack_chk_fail` (0x100). By hand: `lock cmpxchg [m], r` (0x59).
    "pos": dict(grp="Pos", cn="__pthread_once_slow", a=0x5fee60, n=261, pos=True, fs=True,
                stops=(0x4f, 0x76, 0x95, 0x100), calls=True, hand=(0x59,), tag="PLAN.md §M, M1",
                src="glibc 2.31's `__pthread_once_slow` (`nptl/pthread_once.c`; `objdump -d`)"),
    # glibc 2.31 stdlib/strtol_l.c `____strtoul_l_internal (nptr, endptr, base, group, loc)`: spaces, a sign, the
    # base's prefix, the digits (the bound and the overflow flag), `*endptr`, `errno`. Stops: the `ret`s (0x1ad,
    # 0x1ce) and the padding after them (0x1ae, 0x1cf); `group` not 0 (0x2b8), a thousands separator (0x200, 0x3e0).
    "stl": dict(grp="Stl", cn="____strtoul_l_internal", a=0x6238b0, n=1220, pos=True, fs=True,
                stops=(0x1ad, 0x1ae, 0x1ce, 0x1cf, 0x200, 0x2b8, 0x3e0), tag="PLAN.md §M, M1",
                src="glibc 2.31's `____strtoul_l_internal` (`stdlib/strtol_l.c`; `objdump -d`)"),
    # glibc 2.31 locale/loadlocale.c `_nl_intern_locale_data (category, data, datasize)`: the file's magic for the
    # category, `nstrings` at least `_nl_category_num_items[category]` (0x6ef020) and the index in the data, the
    # `struct __locale_data` from `malloc` (the `call`, 0x7a), its fields, then for each string its offset in the data
    # (the loop at 0xc4): through the `switch` on the category (`jt`, 13 entries), the bound of the category's
    # `_nl_value_types` (0x7804c0); a word (type 5) aligned and read, else the address. A bad offset: `free` (the
    # `call`, 0xf3), `errno` = EINVAL, NULL. Stops: the `ret` (0x116); `LC_ALL` or a category above 12 (0x1c6, the
    # `__assert_fail`).
    "ild": dict(grp="Ild", cn="_nl_intern_locale_data", a=0x615210, n=485, pos=True, fs=True, stops=(0x116, 0x1c6),
                calls=True, jt=(0x6ee9e0, 13), cut=(0xc4, 0x108, 0x120, 0x133, 0xf0), tag="PLAN.md §M, M1",
                src="glibc 2.31's `_nl_intern_locale_data` (`locale/loadlocale.c`; `objdump -d`)"),
    # 7-Zip 26.06 CPP/UI/Common/ArchiveExtractCallback.cpp `CArchiveExtractCallback::GetUnpackSize ()`: the arguments
    # of `CArc::GetItem_Size (_index, _fi.Size, _fi.SizeDefined)` from `this` (`_arc` at `this + 0x40`, `_index` at
    # `this + 0x1a8`, `&_fi.Size` = `this + 0x198`, `&_fi.SizeDefined` = `this + 0x6a`), then a tail jump to it (0x19).
    "gus": dict(grp="Gus", cn="CArchiveExtractCallback::GetUnpackSize", a=0x5abac0, n=30, pos=True, stops=(0x19,),
                calls=True, tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `CArchiveExtractCallback::GetUnpackSize` (`CPP/UI/Common/ArchiveExtractCallback.cpp`; "
                    "`objdump -d`)"),
    # 7-Zip 26.06 CPP/UI/Console/ExtractCallbackConsole.cpp `CExtractScanConsole::StartScanning ()`: when the 8 bytes
    # at `this + 0x50` are not 0 and the byte at `this + 0x58` is 0, a tail jump (0x1c) to `AString::operator= (const
    # char *)` with the `AString` at `this + 0x30` and the string "Scan" at `0x6e9b63`; else the `ret` (0x28).
    "sts": dict(grp="Sts", cn="CExtractScanConsole::StartScanning", a=0x5e85c0, n=41, pos=True, stops=(0x1c, 0x28),
                calls=True, tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `CExtractScanConsole::StartScanning` (`CPP/UI/Console/ExtractCallbackConsole.cpp`; "
                    "`objdump -d`)"),
    # 7-Zip 26.06 CPP/Windows/FileName.cpp `NormalizeDirPathPrefix (UString &dirPath)`: nothing (the `ret`, 0x1f)
    # when `dirPath` is empty or ends in `/`; else (a frame of 24 bytes) `Grow_1 ()` (the `call` at 0x4d, to `ug1`)
    # when `_len == _limit`, then `_chars[_len] = '/'`, `_chars[_len + 1] = 0`, `_len += 1` (the `ret`, 0x41).
    "ndp": dict(grp="Ndp", cn="NWindows::NFile::NName::NormalizeDirPathPrefix", a=0x4568a0, n=102, pos=True,
                stops=(0x1f, 0x41), calls=True, tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `NormalizeDirPathPrefix` (`CPP/Windows/FileName.cpp`; `objdump -d`)"),
    # 7-Zip 26.06 CPP/Windows/FileDir.cpp `MyGetTempPath (AString &path)`: `path = "/tmp"` (the `call` at 0xf, to
    # `AString::operator= (const char *)`, the string at `0x6d944d`), `NFind::DoesDirExist (path._chars, true)` (0x1d),
    # then `path = "/tmp/"` (`0x6d9447`) when it answers true, else `path = "./"` (`0x6ee956`; the `call` at 0x39),
    # `true` in `eax`. Stop: the `ret` (0x44).
    "mgt": dict(grp="Mgt", cn="NWindows::NFile::NDir::MyGetTempPath", a=0x454b40, n=69, pos=True, stops=(0x44,),
                calls=True, tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `MyGetTempPath` (`CPP/Windows/FileDir.cpp`; `objdump -d`)"),
    # 7-Zip 26.06 CPP/UI/Common/LoadCodecs.cpp `CArcInfoEx::FindExtension (const UString &ext)`: for `i` from 0 below
    # `Exts.Size ()` (`this + 0x30`, the items at `this + 0x28`), `StringsAreEqualNoCase (ext, Exts[i].Ext)` (the
    # `call` at 0x39, to `sen`): `i` when it answers true (the `ret`, 0x48); -1 past the end (0x59) or for none (0x5f).
    "fex": dict(grp="Fex", cn="CArcInfoEx::FindExtension", a=0x5ceb50, n=96, pos=True, stops=(0x48, 0x59, 0x5f),
                calls=True, tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `CArcInfoEx::FindExtension` (`CPP/UI/Common/LoadCodecs.cpp`; `objdump -d`)"),
    # 7-Zip 26.06 CPP/UI/Common/LoadCodecs.cpp `CCodecs::FindFormatForArchiveType (const UString &arcType)`: for `i`
    # from 0 below `Formats.Size ()` (`this + 0x18`, the items at `this + 0x10`), `StringsAreEqualNoCase
    # (Formats[i].Name, arcType)` (the `call` at 0x3a, to `sen`; `Name` at the item's `+ 0x18`): `i` when it answers
    # true (the `ret`, 0x49); -1 past the end (0x59) or for none (0x5f).
    "ffa": dict(grp="Ffa", cn="CCodecs::FindFormatForArchiveType", a=0x5ced10, n=96, pos=True,
                stops=(0x49, 0x59, 0x5f), calls=True, tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `CCodecs::FindFormatForArchiveType` (`CPP/UI/Common/LoadCodecs.cpp`; "
                    "`objdump -d`)"),
    # 7-Zip 26.06 CPP/Windows/FileFind.cpp `CFileInfo::Find (CFSTR path, bool followLink)`: `Find_DontFill_Name`
    # (the `call` at 0x11, to `fdn`); when it answers true, the last part of `path` (the loop at 0x3a over its bytes,
    # after each `/` followed by a byte not 0), `Name = ...` (`AString::operator=`, the `call` at 0x57, to `aac`), and
    # a trailing `/` dropped from `Name` (the store at 0x76); `eax` = the answer, the `ret` (0x81).
    "fnd": dict(grp="Fnd", cn="NWindows::NFile::NFind::CFileInfo::Find", a=0x455b80, n=130, pos=True, stops=(0x81,),
                calls=True, tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `CFileInfo::Find` (`CPP/Windows/FileFind.cpp`; `objdump -d`)"),
    # Tail-jump wrappers of M1 (one straight-line block, then a `jmp` to the callee; the stop is the `jmp`).
    # 7-Zip 26.06 CPP/UI/Console/ExtractCallbackConsole.h: the `this - 8` thunks of `CExtractCallbackConsole`'s
    # `IOpenCallbackUI` methods (`sub rdi, 8; jmp`).
    "tbo": dict(grp="Tbo", cn="CExtractCallbackConsole::BeforeOpen (thunk, this - 8)", a=0x5e7cb0, n=13, pos=True,
                stops=(0x8,), calls=True, tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `CExtractCallbackConsole` thunk (`CPP/UI/Console/ExtractCallbackConsole.h`; `objdump -d`)"),
    "ter": dict(grp="Ter", cn="CExtractCallbackConsole::ExtractResult (thunk, this - 8)", a=0x5e85b0, n=13, pos=True,
                stops=(0x8,), calls=True, tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `CExtractCallbackConsole` thunk (`CPP/UI/Console/ExtractCallbackConsole.h`; `objdump -d`)"),
    "tor": dict(grp="Tor", cn="CExtractCallbackConsole::OpenResult (thunk, this - 8)", a=0x5e9ef0, n=13, pos=True,
                stops=(0x8,), calls=True, tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `CExtractCallbackConsole` thunk (`CPP/UI/Console/ExtractCallbackConsole.h`; `objdump -d`)"),
    # 7-Zip 26.06 CPP/Common/UTFConvert.cpp.
    "u8f": dict(grp="U8f", cn="ConvertUTF8ToUnicode_Flags", a=0x451fe0, n=23, pos=True, stops=(0x12,), calls=True,
                tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `ConvertUTF8ToUnicode_Flags` (`CPP/Common/UTFConvert.cpp`; `objdump -d`)"),
    "u8u": dict(grp="U8u", cn="ConvertUTF8ToUnicode", a=0x452000, n=14, pos=True, stops=(0x9,), calls=True,
                tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `ConvertUTF8ToUnicode` (`CPP/Common/UTFConvert.cpp`; `objdump -d`)"),
    "uu8": dict(grp="Uu8", cn="ConvertUnicodeToUTF8", a=0x4520b0, n=18, pos=True, stops=(0xd,), calls=True,
                tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `ConvertUnicodeToUTF8` (`CPP/Common/UTFConvert.cpp`; `objdump -d`)"),
    # 7-Zip 26.06 CPP/Windows/FileName.cpp `GetFullPath (const char *path, AString &fullPath)`.
    "gfp": dict(grp="Gfp", cn="NWindows::NFile::NName::GetFullPath", a=0x456e30, n=17, pos=True, stops=(0xc,),
                calls=True, tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `GetFullPath (path, fullPath)` (`CPP/Windows/FileName.cpp`; `objdump -d`)"),
    # 7-Zip 26.06 CPP/Windows/FileIO.h `CInFile::Open (name)`: `OpenBinary (name, O_RDONLY, 0666)` (the symbol at
    # 0x456180 is folded with others of the same bytes).
    # 7-Zip 26.06 CPP/Common/StdOutStream.cpp `CStdOutStream::Flush ()`: `return fflush (_stream) == 0;` (the
    # `call` of `fflush` at 0xb, then `test eax, eax; sete al; add rsp, 8; ret`)
    "fls": dict(grp="Fls", cn="CStdOutStream::Flush", a=0x5a1440, n=26, pos=True, stops=(0x19,), calls=True,
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `CStdOutStream::Flush` (`CPP/Common/StdOutStream.cpp`; "
                "`objdump -d`)"),
    # 7-Zip 26.06 CPP/Common/StdOutStream.cpp `endl (CStdOutStream &outStream)`: `outStream << '\\n'` as
    # `fputc ('\\n', _stream)` (the `call` at 0x11), then `mov rax, r12; pop r12; ret` as in `operator+` (`Apl`)
    "enl": dict(grp="Enl", cn="endl(CStdOutStream &)", a=0x5a1470, n=28, pos=True, stops=(0x1b,), calls=True,
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `endl (CStdOutStream &)` (`CPP/Common/StdOutStream.cpp`; "
                "`objdump -d`)"),
    "obn": dict(grp="Obn", cn="NWindows::NFile::NIO::CInFile::Open", a=0x456180, n=16, pos=True, stops=(0xb,),
                calls=True, tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `CInFile::Open` (`CPP/Windows/FileIO.h`; `objdump -d`)"),
    # 7-Zip 26.06 CPP/Common/MyString.cpp `AString::Add_Space ()`: `if (_limit == _len) Grow_1 ();` (the `call` of
    # `AString::Grow_1` at 0x28, then `mov eax, [rbx + 8]; jmp 16`), then at 16 the stores (' ', then 0, the length
    # plus 1) and `pop rbx; ret` (0x24)
    "asp": dict(grp="Asp", cn="AString::Add_Space", a=0x44c6f0, n=50, pos=True, stops=(0x24,), calls=True,
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `AString::Add_Space` (`CPP/Common/MyString.cpp`; `objdump -d`)"),
    # 7-Zip 26.06 CPP/Common/MyString.cpp `AString::Add_Minus ()`: as `Add_Space` (`asp`) with '-'
    "amn": dict(grp="Amn", cn="AString::Add_Minus", a=0x44c810, n=50, pos=True, stops=(0x24,), calls=True,
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `AString::Add_Minus` (`CPP/Common/MyString.cpp`; `objdump -d`)"),
    # 7-Zip 26.06 CPP/Common/MyString.cpp `AString::operator+= (char c)`: as `Add_Space` (`asp`) with `c` kept in
    # `ebp` (`push rbp; mov ebp, esi; push rbx; sub rsp, 8`); the `ret` at 0x30, the `call` of `Grow_1` at 0x38
    "ach": dict(grp="Ach", cn="AString::operator+=(char)", a=0x44c6a0, n=66, pos=True, stops=(0x30,), calls=True,
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `AString::operator+= (char)` (`CPP/Common/MyString.h`; "
                "`objdump -d`)"),
    # 7-Zip 26.06 `Release ()` of a COM class through its third base (`_ZThn24`): `this` - 24 the object, the count at
    # `rdi + 0x20`; `if (--__m_RefCount == 0) delete this;` as the destructor's `call` (0x22, `0x5b2340`) and the sized
    # `operator delete (p, 0x2c0)` (0x2f, `0x6014e0`); the `ret` at 0x3e with the count in `eax`
    "trl": dict(grp="Trl", cn="_ZThn24 Release", a=0x5b2940, n=63, pos=True, stops=(0x3e,), calls=True,
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `MY_ADDREF_RELEASE` `Release ()` (`CPP/Common/MyCom.h`; "
                "`objdump -d`)"),
    # Tail-jump leaves of M1. The symbol `_txnal_cow_string_c_str` (0x454a40, folded with other bytes) is `endbr64;
    # jmp 0x456e30` (`GetFullPath`, `gfp`); the stop is the `jmp` (4).
    "txc": dict(grp="Txc", cn="_txnal_cow_string_c_str", a=0x454a40, n=9, pos=True, stops=(0x4,), calls=True,
                tag="PLAN.md §M, M1", src="the symbol `_txnal_cow_string_c_str` of `7zzs` (`objdump -d`)"),
    # glibc 2.31 nptl/pthread_once.c `__pthread_once`: `if (once_control & __PTHREAD_ONCE_DONE) return 0;` (the `ret`
    # at 0xc), else a tail jump to `__pthread_once_slow` (0x10, `pos`)
    "pto": dict(grp="Pto", cn="__pthread_once", a=0x5fefc0, n=21, pos=True, stops=(0xc, 0x10), calls=True,
                tag="PLAN.md §M, M1", src="glibc 2.31's `__pthread_once` (`nptl/pthread_once.c`; `objdump -d`)"),
    # glibc 2.31 stdlib/strtol.c `__strtol`: `____strtol_l_internal (nptr, endptr, base, 0, _NL_CURRENT_LOCALE)` as
    # `mov rax, -128; xor ecx, ecx; mov r8, fs:[rax]` (the thread's locale), then a tail jump (0x11) to 0x6238b0 (`stl`)
    # 7-Zip 26.06 CPP/Common/MyString.cpp `AString::operator+= (const AString &s)`: `Grow (s._len)` (the `call` at
    # 20), then the copy loop of `s._chars` through the 0 to `_chars + _len` (48, as in `aas`), `_len += s._len`,
    # `rax` = `this`, the `ret` at 82. By hand: `add dword [r12 + 8], eax` (0x43).
    "ape": dict(grp="Ape", cn="AString::operator+=(const AString &)", a=0x44c920, n=83, pos=True, stops=(0x52,),
                hand=(0x43,), calls=True, tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `AString::operator+= (const AString &)` (`CPP/Common/MyString.cpp`; `objdump -d`)"),
    "stw": dict(grp="Stw", cn="__strtol", a=0x623890, n=22, pos=True, fs=True, stops=(0x11,), calls=True,
                tag="PLAN.md §M, M1", src="glibc 2.31's `__strtol` (`stdlib/strtol.c`; `objdump -d`)"),
    # 7-Zip 26.06 CPP/UI/Common/EnumDirItems.cpp `FindFile_KeepDots (fi, path, followLink)`: `fi.Find (path,
    # followLink)` (the `call` at 16, to `fnd`); when it answers true and `path` ends in "." after a '/', at its start,
    # or as ".." likewise, `fi.Name = p` (`AString::operator= (const char *)`, the `call` at 92, to `aac`) with `p` the
    # dots; `eax` = the answer, the `ret` (104).
    "fkd": dict(grp="Fkd", cn="FindFile_KeepDots", a=0x5bff20, n=117, pos=True, stops=(0x68,), calls=True,
                tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `FindFile_KeepDots` (`CPP/UI/Common/EnumDirItems.cpp`; `objdump -d`)"),
    # 7-Zip's `Set_ModuleDirPrefix_From_ProgArg0 (s)` (`CPP/7zip/UI/Common/ArchiveCommandLine.cpp`): a frame of 32
    # bytes under `push rbp` with the stack guard at `rsp + 24` and an `AString` at `rsp` (`rbp`): its constructor
    # from `s` (call at 0x22), `ReverseFind_PathSepar ()` (0x2a), the string cut after the separator when that is
    # shorter (0x32..0x43), `operator=` into the global prefix at 0x79ed90 (0x4e), `delete []` of the chars unless
    # NULL (0x5c), the guard's check. Stops: the `ret` (0x76), the call of `__stack_chk_fail` (0x77).
    "smd": dict(grp="Smd", cn="Set_ModuleDirPrefix_From_ProgArg0", a=0x5a9ed0, n=124, pos=True, fs=True,
                stops=(0x76, 0x77), calls=True, tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `Set_ModuleDirPrefix_From_ProgArg0` (`ArchiveCommandLine.cpp`; `objdump -d`)"),
    # 7-Zip 26.06 CPP/7zip/UI/Console/List.cpp `GetPropName (propID, name, nameA, nameU)` (static): a known `propID`
    # (<= 0x68) `nameA = kPropIdToName[propID]` (the table at 0x77f520, a tail jump to `AString::operator= (const char
    # *)` at 0x43); else with `name` `nameU = name` (a tail jump to `UString::operator= (const wchar_t *)`, 0x14),
    # without, `nameA.Empty (); nameA.Add_UInt32 (propID)` (the stores, a tail jump to `Add_UInt32`, 0x30)
    "gpn": dict(grp="Gpn", cn="GetPropName", a=0x5ebc80, n=72, pos=True, stops=(0x14, 0x30, 0x43), calls=True,
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `GetPropName` (`CPP/7zip/UI/Console/List.cpp`; `objdump -d`)"),
    # 7-Zip 26.06 CPP/7zip/UI/Common/ExtractingFilePath.cpp `Get_Correct_FsFile_Name (name)`: `UString res = name`
    # (the copy constructor's `call` at 0xe), `Correct_PathPart (res)` when not empty (0x1f), `res = '_'` when it is
    # empty then (0x48); `rax` = the result's place, the `ret`s (0x37, 0x57). The landing pad (0x58..) is left out.
    "gcf": dict(grp="Gcf", cn="Get_Correct_FsFile_Name", a=0x5c7070, n=88, pos=True, stops=(0x37, 0x57), calls=True,
                tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `Get_Correct_FsFile_Name` (`ExtractingFilePath.cpp`; `objdump -d`)"),
    # 7-Zip's CPP/7zip/Compress/LzmaDecoder.cpp `CDecoder::CDecoder ()`: the 8 vtable pointers (the class's
    # interfaces, from 0x78c498) at `this + 8 * i`, the flags and sizes 0, `_inBufSize` = `_outStep` = 1 MiB. Stop:
    # the `ret` (184).
    "ldc": dict(grp="Ldc", cn="NCompress::NLzma::CDecoder::CDecoder", a=0x57fb70, n=185, pos=True, stops=(184,),
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `CDecoder` constructor (`LzmaDecoder.cpp`; `objdump -d`)"),
    # 7-Zip's CPP/7zip/Compress/LzmaDecoder.cpp `CDecoder::~CDecoder ()`: the 8 vtable pointers back, then
    # `LzmaDec_Free (&_state, &g_AlignedAlloc)` (the `call` at 110, to `ldf`), `MidFree (_inBuf)` (119), and
    # `_inStream.Release ()` through the vtable (`call [rax + 16]`, 139) when `_inStream` (at `this + 256`) is set.
    # Stop: the `ret` (143).
    "ldd": dict(grp="Ldd", cn="NCompress::NLzma::CDecoder::~CDecoder", a=0x57fc30, n=144, pos=True, stops=(143,),
                calls=True, tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `CDecoder` destructor (`LzmaDecoder.cpp`; `objdump -d`)"),
    # 7-Zip 26.06 CPP/7zip/Common/FileStreams.h `CInFileStream::CInFileStream ()`: the five vtable pointers (from
    # 0x78e748), `File` (a `CFileBase` at 0x2c) set up in line, `Callback` and `CallbackRef` 0, then the two `UString`s
    # at 0xd0 (the `call` at 0x7a) and 0xe0 (0x86, `UString::UString ()`), the three fields after them 0. Stop: the `ret`
    # (0xb1); the bytes from 0xb2 on are the landing pads.
    "ifc": dict(grp="Ifc", cn="CInFileStream::CInFileStream", a=0x5a3f70, n=178, pos=True, stops=(0xb1,), calls=True,
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `CInFileStream::CInFileStream` (`FileStreams.h`; `objdump -d`)"),
    # 7-Zip 26.06 CPP/7zip/Common/FileStreams.cpp `CInFileStream::~CInFileStream ()`: the five vtable pointers set back,
    # `if (Callback) Callback->InFileStream_On_Destroy (this, CallbackRef)` (`call qword [rax + 8]` at 0x57), the two
    # `UString`s' chars freed unless NULL (`operator delete []`, the `call`s at 0x66, 0x77), then `File.Close ()` (0x80,
    # `CFileBase::Close`). Stop: the `ret` (0x86).
    "ifd": dict(grp="Ifd", cn="CInFileStream::~CInFileStream", a=0x5a4040, n=135, pos=True, stops=(0x86,), calls=True,
                tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `CInFileStream::~CInFileStream` (`FileStreams.cpp`; `objdump -d`)"),
    # glibc 2.31 math/s_nan.c `__nan (tagp)`: `__strtod_nan (tagp, NULL, 0)` as `xor edx, edx; xor esi, esi`, then a
    # tail jump (8) to 0x461ed0
    "nan": dict(grp="Nan", cn="__nan", a=0x4621f0, n=13, pos=True, stops=(0x8,), calls=True,
                tag="PLAN.md §M, M1", src="glibc 2.31's `__nan` (`math/s_nan.c`; `objdump -d`)"),
    # 7-Zip 26.06 `CArchiveExtractCallback::Release ()` (`MY_ADDREF_RELEASE`, `CPP/Common/MyCom.h`): as the `_ZThn24`
    # thunk (`trl`) with `this` in `rdi` and the count at `rdi + 0x38`; the destructor's `call` (0x1e, `0x5b2340`), the
    # sized `operator delete (p, 0x2c0)` (0x2b, `0x6014e0`); the `ret` at 0x3a with the count in `eax`
    "rel": dict(grp="Rel", cn="CArchiveExtractCallback::Release", a=0x5b2840, n=59, pos=True, stops=(0x3a,),
                calls=True, tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `MY_ADDREF_RELEASE` `Release ()` (`CPP/Common/MyCom.h`; `objdump -d`)"),
    # `AString::operator+=(const char *)`: length loop, `Grow` as a continuation, copy loop, `_len += n`
    "apc": dict(grp="Apc", cn="AString::operator+=(const char *)", a=0x44c890, n=93, pos=True, stops=(0x5c,),
                hand=(0x50,), calls=True, tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `AString::operator+= (const char *)` (`CPP/Common/MyString.cpp`; `objdump -d`)"),
    # 7-Zip 26.06 CPP/Windows/PropVariant.cpp `NCOM::AllocBstrFromAscii (s)`: NULL for `s` NULL (the `ret` at 0x62);
    # `len = strlen (s)` (the `call` of the PLT entry at 0x12), `p = SysAllocStringLen (NULL, len)` (0x1e), NULL for
    # `p` NULL (0x58); else the copy loop at 0x30 (`p[i] = (Byte)s[i]` for `i <= len`), the `ret` at 0x46.
    "aba": dict(grp="Aba", cn="AllocBstrFromAscii", a=0x456e50, n=99, pos=True, stops=(0x46, 0x58, 0x62), calls=True,
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `NCOM::AllocBstrFromAscii` (`PropVariant.cpp`; `objdump -d`)"),
    # 7-Zip 26.06 CPP/7zip/Common/FileStreams.cpp `CInFileStream::Seek (offset, seekOrigin, newPosition)`: the origin
    # checked (0x0b), `File.seek` (the `call` at 0x17), on -1 `GetLastError_noZero_HRESULT` (0x38) and `File.GetPosition`
    # (0x5a), the result stored. Stop: the `ret` (0x34); the bytes from 0x78 on are the landing pads.
    "isk": dict(grp="Isk", cn="CInFileStream::Seek", a=0x5a3770, n=120, pos=True, stops=(0x34,), calls=True,
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `CInFileStream::Seek` (`FileStreams.cpp`; `objdump -d`)"),
    # 7-Zip 26.06 CPP/7zip/Common/FileStreams.cpp `CInFileStream::Read (data, size, processedSize)`: `File.read_part`
    # (the `call`s at 0x21 and 0x40, with and without `processedSize`), on -1 `GetLastError_noZero_HRESULT` (0x50) and
    # `if (Callback) Callback->InFileStream_On_Error (CallbackRef, errorCode)` (`call qword [rax]` at 0x71). Stops: the
    # `ret`s (0x36, 0x79); the bytes from 0xa0 on are the landing pads.
    "ird": dict(grp="Ird", cn="CInFileStream::Read", a=0x5a35a0, n=160, pos=True, stops=(0x36, 0x79), calls=True,
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `CInFileStream::Read` (`FileStreams.cpp`; `objdump -d`)"),
    # 7-Zip 26.06 `CDummyOutStream::Write (data, size, processedSize)` (`CPP/7zip/UI/Common/Extract.cpp`, the
    # dummy stream of `7z t`): a frame of 24 bytes under `push rbp; push rbx` with the stack guard at `rsp + 8` and
    # `realProcessed` (= `size`) at `rsp + 4`; when `_stream` (`[rdi + 0x10]`) is not NULL, `_stream->Write (data,
    # size, &realProcessed)` (the `call [rax + 0x18]` at 0x35); `_size += realProcessed` (by hand: `add [rbx + 0x18],
    # rcx`, 0x3e); `*processedSize = realProcessed` unless NULL (0x47); the guard's check. Stops: the `ret` (0x60),
    # the call of `__stack_chk_fail` (0x61).
    "dow": dict(grp="Dow", cn="CDummyOutStream::Write", a=0x4e2470, n=102, pos=True, fs=True, stops=(0x60, 0x61),
                hand=(0x3e,), calls=True, tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `CDummyOutStream::Write` (`CPP/7zip/UI/Common/Extract.cpp`; `objdump -d`)"),
    # 7-Zip 26.06 CPP/7zip/Common/StreamUtils.cpp `WriteStream (stream, data, size)`: a frame of 16 bytes under five
    # pushes with the stack guard at `rsp + 8` and `processedSize` at `rsp + 4`; the loop (head 0x49) of
    # `stream->Write (data, min (size, 0x80000000), &processedSize)` (the `call [rax + 0x18]` at 0x5f), `data +=`,
    # `size -=` the processed size; a result not 0 is returned, a processed size 0 gives `E_FAIL` (0x98), size 0
    # gives 0 (0x90). Stops: the `ret` (0x8c), the call of `__stack_chk_fail` (0x9f).
    "wst": dict(grp="Wst", cn="WriteStream", a=0x463420, n=164, pos=True, fs=True, stops=(0x8c, 0x9f), calls=True,
                tag="PLAN.md §M, M1", src="7-Zip 26.06's `WriteStream` (`CPP/7zip/Common/StreamUtils.cpp`; `objdump -d`)"),
    # 7-Zip 26.06 CPP/7zip/Common/StreamUtils.cpp `ReadStream (stream, data, processedSize)`: `size = *processedSize;
    # *processedSize = 0;` then the loop (head 0x59) of `stream->Read (data, min (size, 0x80000000), &processed)`
    # (the `call [rax + 0x18]` at 0x6f), `*processedSize += processed` (by hand: `add [r14], rdx`, 0x76), `data +=`,
    # `size -=`; a result not 0 is returned, a processed size 0 or size 0 give 0 (0x83, 0xa8). Stops: the `ret`
    # (0xa1), the call of `__stack_chk_fail` (0xac).
    "rst": dict(grp="Rst", cn="ReadStream", a=0x4632b0, n=177, pos=True, fs=True, stops=(0xa1, 0xac), hand=(0x76,),
                calls=True, tag="PLAN.md §M, M1",
                src="7-Zip 26.06's `ReadStream` (`CPP/7zip/Common/StreamUtils.cpp`; `objdump -d`)"),
    # 7-Zip's C/LzmaDec.c `LzmaDec_Allocate (p, props, propsSize, alloc)`: `LzmaProps_Decode (&propNew, props,
    # propsSize)` (call, 0x27, `Lpd`) into the frame, `LzmaDec_AllocateProbs2 (p, &propNew, alloc)` (0x67, `Lap`), the
    # dictionary size rounded up to 4 KiB (below 4 MiB) or 1 MiB (0x73..0xc1; 0x100: above 1 GiB), the old dictionary
    # freed (`alloc->Free`, 0xcf) and a new one allocated (`alloc->Alloc`, 0xe1) unless it is there with that size;
    # a null result `LzmaDec_FreeProbs` (0x11c, `Lfp`) and SZ_ERROR_MEM. The guard's check. Stops: the `ret` (0x54),
    # the call of `__stack_chk_fail` (0x126).
    "lza": dict(grp="Lza", cn="LzmaDec_Allocate", a=0x42bf80, n=299, pos=True, fs=True, stops=(0x54, 0x126),
                calls=True, tag="PLAN.md §M, M1", src="7-Zip 26.06's `LzmaDec_Allocate` (`C/LzmaDec.c`; `objdump -d`)"),
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
    m = re.fullmatch(r'reg \{ w8, n(\d+), high8 := true \}', o)   # `ah`, `ch`, `dh`, `bh`
    if m: return ('rh', f"gh {m[1]}", (8, int(m[1])))
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
        if sm == 'pxor' and ks == ('x', 'x'):   # FV7z/Lemmas/BlkOps19.lean
            return terms, "Op.vld 0 fun _ => 0", "OpI.vz_pxor"
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
    if mn == 'cmp' and ks == ('mf', 'i') and sz == 8:   # FV7z/Lemmas/BlkOps14.lean
        assert f[0][4] == 8
        return terms, f"Op.cmpmif fb 8 {mem(ops[0])} {f[1][1]}", "OpIF.cmpmif8"
    if mn == 'cmp' and sz == 16 and ks == ('r', 'i'):   # FV7z/Lemmas/BlkOps25.lean
        return tsrc(16), f"Op.cmp 16 {f[0][1]} {src(ops[1])}", f"OpI.cmp16 {src(ops[1])}"
    if mn == 'test' and sz == 16 and ks in (('r', 'r'), ('r', 'i')):
        return tsrc(16), f"Op.test 16 {f[0][1]} {src(ops[1])}", f"OpI.test16 {src(ops[1])}"
    if mn == 'cmp' and ks == ('mf', 'i') and sz in (32, 64):   # FV7z/Lemmas/BlkOps13.lean
        assert f[0][4] == sz
        return terms, f"Op.cmpmif fb {sz} {mem(ops[0])} {f[1][1]}", f"OpIF.cmpmif {hw2(sz)}"
    if mn == 'xor' and ks == ('r', 'mf') and sz in (32, 64):
        assert f[1][4] == sz
        return terms, f"Op.xormf fb {sz} {f[0][1]} {mem(ops[1])}", f"OpIF.xormf {hw2(sz)}"
    if mn == 'xor' and sz == 8 and ks in (('r', 'r'), ('r', 'i')):
        return tsrc(8), f"Op.xor8 {f[0][1]} {src(ops[1])}", f"OpI.xor8 {src(ops[1])}"
    if mn == 'or' and sz == 8 and ks in (('r', 'r'), ('r', 'i')):   # FV7z/Lemmas/BlkOps23.lean
        return tsrc(8), f"Op.or8 {f[0][1]} {src(ops[1])}", f"OpI.or8 {src(ops[1])}"
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
    if mn == 'test' and ks == ('m', 'i') and sz == 32:   # FV7z/Lemmas/BlkOps22.lean
        assert f[0][4] == 32
        return terms, f"Op.testmi 32 {mem(ops[0])} {f[1][1]}", "OpI.testmi32"
    if mn == 'test' and ks == ('mr', 'i') and sz == 8:
        return terms, f"Op.testmia 8 {absa(ops[0])} {f[1][1]}", "OpIA.testmi8_rip (by decide)"
    if mn == 'test' and ks == ('mr', 'r') and sz == 64:   # FV7z/Lemmas/TestMr.lean
        return terms, f"Op.testmra 64 {absa(ops[0])} {f[1][1]}", "OpIA.testmr_rip (by decide)"
    if mn == 'cmp' and ks == ('m', 'i') and sz == 16:   # FV7z/Lemmas/CmpMi16.lean
        return terms, f"Op.cmpmi 16 {mem(ops[0])} {f[1][1]}", "OpI.cmpmi16"
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
    if mn == 'movzx' and ks == ('r', 'r') and sz == 32 and f[1][0] == 8:   # FV7z/Lemmas/BlkOps14.lean
        return terms, f"Op.zxr {f[0][1]} {f[1][1]}", "OpI.zxr"
    if mn == 'movzx' and ks == ('r', 'r') and sz == 32 and f[1][0] == 16:   # FV7z/Lemmas/BlkOps18.lean
        return terms, f"Op.zxr16 {f[0][1]} {f[1][1]}", "OpI.zxr16"
    if mn.startswith('setcc ') and ks == ('r',) and sz == 8:
        return terms, f"Op.setcc {mn.split()[1]} {f[0][1]}", "OpI.setcc"
    if mn == 'movsx' and ks == ('r', 'm') and sz == 32 and f[1][4] == 8:   # FV7z/Lemmas/BlkOps5.lean
        return terms, f"Op.ldsxb {f[0][1]} {mem(ops[1])}", "OpI.ldsxb"
    if mn == 'movsx' and ks == ('r', 'm') and sz == 64 and f[1][4] == 8:   # FV7z/Lemmas/BlkOps26.lean
        return terms, f"Op.ldsxq {f[0][1]} {mem(ops[1])}", "OpI.ldsxq"
    if mn == 'movsxd' and ks == ('r', 'm') and sz == 64 and f[1][4] == 32:
        return terms, f"Op.ldsx {f[0][1]} {mem(ops[1])}", "OpI.ldsx"
    if mn == 'mul' and ks == ('r',) and sz == 64:   # FV7z/Lemmas/BlkOps17.lean
        return terms, f"Op.mul64 {f[0][1]}", "OpI.mul64"
    if mn == 'bit (BitMn.bt)' and ks == ('r', 'r') and sz == 64:   # FV7z/Lemmas/BlkOps16.lean
        return terms, f"Op.bt64 {f[0][1]} {f[1][1]}", "OpI.bt64"
    if mn == 'movsxd' and ks == ('r', 'r') and sz == 64 and f[1][0] == 32:   # FV7z/Lemmas/BlkOps15.lean
        return terms, f"Op.sxr {f[0][1]} {f[1][1]}", "OpI.sxr"
    if mn == 'lea' and ks == ('r', 'mr') and sz == 64:
        return terms, f"Op.mov 64 {f[0][1]} (.i {absa(ops[1])})", "OpIA.lea_rip (by decide)"
    if mn in ('sub', 'cmp', 'add', 'and', 'or', 'xor', 'test', 'sbb', 'mov') and ks in (('r', 'r'), ('r', 'i')):
        r = f[0][1]
        if sz == 8 and mn == 'add':
            return tsrc(8), f"Op.add8 {r} {src(ops[1])}", f"OpI.add8 {src(ops[1])}"
        if sz == 8 and mn == 'sbb':   # FV7z/Lemmas/RepCmpsb.lean
            return tsrc(8), f"Op.sbb8 {r} {src(ops[1])}", f"OpI.sbb8 {src(ops[1])}"
        assert sz in (32, 64), (mn, sz, ol)
        return (tsrc(sz), f"Op.{mn} {sz} {r} {src(ops[1])}",
                f"OpI.{mn} {src(ops[1])} {hw2(sz)}")
    if mn == 'cmp' and ks == ('r', 'm') and sz == 8:   # FV7z/Lemmas/BlkOps20.lean
        assert f[1][4] == 8
        return terms, f"Op.cmpm 8 {f[0][1]} {mem(ops[1])}", "OpI.cmpm8"
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
    if mn.startswith('cmovcc ') and ks == ('r', 'm') and sz == 32:   # FV7z/Lemmas/CmovLd.lean
        cc = mn.split()[1]
        return terms, f"Op.cmovld32 {cc} {f[0][1]} {mem(ops[1])}", "OpI.cmovld32"
    if mn.startswith('cmovcc ') and ks == ('r', 'm') and sz == 64:   # FV7z/Lemmas/CmovLd.lean
        cc = mn.split()[1]
        return terms, f"Op.cmovld64 {cc} {f[0][1]} {mem(ops[1])}", "OpI.cmovld64"
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
    if mn in ('and', 'test') and ks == ('rh', 'i') and sz == 8:   # FV7z/Lemmas/BlkOps20.lean
        return terms, f"Op.{mn}h {f[0][1]} {f[1][1]}", f"OpI.{mn}h"
    if mn == 'not' and ks == ('r',) and sz == 32:   # FV7z/Lemmas/BlkOps20.lean
        return terms, f"Op.not32 {f[0][1]}", "OpI.not32"
    if mn == 'not' and ks == ('r',) and sz == 64:   # FV7z/Lemmas/BlkOps23.lean
        return terms, f"Op.not64 {f[0][1]}", "OpI.not64"
    if mn == 'cwd' and ks == () and sz == 64:
        return terms, "Op.cqo", "OpI.cqo"
    if mn == 'shr' and ks == ('r', 'i') and sz == 16:   # FV7z/Lemmas/BlkOps24.lean
        return terms, f"Op.shr16 {f[0][1]} {f[1][1]}", "OpI.shr16"
    if mn == 'movsx' and ks == ('r', 'r') and sz == 16 and f[1][0] == 8:
        return terms, f"Op.sxb16 {f[0][1]} {f[1][1]}", "OpI.sxb16"
    if mn == 'imul' and ks == ('r', 'r', 'i') and sz == 32:
        return terms, f"Op.imul3d {f[0][1]} {f[1][1]} {f[2][1]}", "OpI.imul3d"
    if mn == 'imul' and ks == ('r', 'r', 'i') and sz == 64:
        return terms, f"Op.imul3 {f[0][1]} {f[1][1]} {f[2][1]}", "OpI.imul3"
    if mn == 'imul' and ks == ('r', 'mr', 'i') and sz == 64:
        assert f[1][1] == 64
        return terms, f"Op.imul3ma {f[0][1]} {absa(ops[1])} {f[2][1]}", "OpIA.imul3_rip (by decide)"
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
    # `jmp r` (through the jump table) and `jmp [m]` (through a vtable: `Seg.s_jmp_mx`, at a stop)
    jr = lambda i: i[1] == 'jmp' and not i[3][0].startswith('rel')
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
{"import FV7z.Lemmas.BlkOps26" + chr(10) if any("Op.ldsxq" in x for x in P) else ""}{"import FV7z.Lemmas.CmovLd" + chr(10) if any(k in x for x in P for k in ("Op.cmovld32", "Op.cmovld64")) else ""}{"import FV7z.Lemmas.RepCmpsb" + chr(10) if any("Op.sbb8" in x for x in P) else ""}{"import FV7z.Lemmas.TestMr" + chr(10) if any("Op.testmra" in x for x in P) else ""}{"import FV7z.Lemmas.CmpMi16" + chr(10) if any("Op.cmpmi 16" in x for x in P) else ""}{"import FV7z.Lemmas.BlkOps25" + chr(10) if any("Op.cmp 16" in x for x in P) else ""}{"import FV7z.Lemmas.BlkOps24" + chr(10) if any(k in x for x in P for k in ("Op.shr16", "Op.sxb16", "Op.imul3d")) else ""}{"import FV7z.Lemmas.BlkOps23" + chr(10) if any(k in x for x in P for k in ("Op.or8", "Op.not64")) else ""}{"import FV7z.Lemmas.BlkOps22" + chr(10) if any("Op.testmi 32" in x for x in P) else ""}{"import FV7z.Lemmas.BlkOps20" + chr(10) if any(k in x for x in P for k in ("Op.not32", "Op.cqo", "Op.imul3", "Op.andh", "Op.testh", "Op.cmpm 8")) else ""}{"import FV7z.Lemmas.BlkOps19" + chr(10) if any("Op.vld 0" in x for x in P) else ""}{"import FV7z.Lemmas.BlkOps18" + chr(10) if any("Op.zxr16" in x for x in P) else ""}{"import FV7z.Lemmas.BlkOps17" + chr(10) if any("Op.mul64" in x for x in P) else ""}{"import FV7z.Lemmas.BlkOps16" + chr(10) if any("Op.bt64" in x for x in P) else ""}{"import FV7z.Lemmas.BlkOps15" + chr(10) if any("Op.sxr" in x for x in P) else ""}{"import FV7z.Lemmas.BlkOps14" + chr(10) if any(k in x for x in P for k in ("Op.zxr", "Op.test 16", "Op.cmpmif fb 8")) else ""}{"import FV7z.Lemmas.BlkOps13" + chr(10) if any("Op.cmpmif" in x for x in P) else ""}{"import FV7z.Lemmas.BlkOps12" + chr(10) if any(k in x for x in P for k in ("Op.cmpmr", "Op.testmi")) else ""}{"import FV7z.Lemmas.BlkOps11" + chr(10) if any(k in x for x in P for k in ("Op.rol64", "Op.ror64")) else ""}{"import FV7z.Lemmas.BlkOps10" + chr(10) if any("Op.cmpm 16" in x for x in P) else ""}{"import FV7z.Lemmas.BlkOps9" + chr(10) if any("Op.cmpma" in x for x in P) else ""}{"import FV7z.Lemmas.BlkOps8" + chr(10) if any(k in x for x in P for k in ("Op.vla", "Op.vsa", "Op.addma", "Op.cmpmia 8", "Op.stia 8")) else ""}{"import FV7z.Lemmas.BlkOps7" + chr(10) if any(k in x for x in P for k in ("Op.vl", "Op.vs", "Op.cdqe")) else ""}{"import FV7z.Lemmas.BlkOps6" + chr(10) if any(k in x for x in P for k in ("Op.stf8", "Op.stfi", "Op.xormf")) else ""}{("import FV7z.Lemmas.BlkOps5" if any("Op.ldsxb" in x for x in P) else
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
                 f"    {w} :=\n  {FS0}{rule} (j := {off}) (tgt := {tg}) (Dec.shift (j{jk}_0 _) wj_{off} (by decide))\n"
                 f"    (lt_len (by decide)) (by decide) (lt_len (by decide)){FS1}")
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
                  | ({callat[c] for c in called} & set(nodes)) | (set(F.get("cut", ())) & set(nodes)))
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
