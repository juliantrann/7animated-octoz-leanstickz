#!/usr/bin/env python3
"""Name the functions of a stripped static binary that come from static libraries (G0 symbol mapping, PLAN.md §8).

For every function symbol of every member of the given `.a` archives, its bytes with the fields its relocations
patch masked out are compared with the bytes of each function of FUNCS.TSV (tools/ehframe_funcs.py) of the same
size. A match is evidence, not proof, that the binary's function is the library's: two functions of a library can
have the same masked bytes (aliases, or bodies that differ only in what they call), and then all the names are given.
The linker's relaxations of GOT loads (R_X86_64_GOTPCRELX, R_X86_64_REX_GOTPCRELX) rewrite the opcode too, which is
masked with the field.

Output (TSV): start_hex  size  library  member  symbol[,symbol...]
Usage: libmatch.py BINARY FUNCS.TSV LIB.a... > names.tsv
"""
import collections, struct, sys

def ar_members(path):
    data = open(path, "rb").read()
    assert data[:8] == b"!<arch>\n", path
    i, names = 8, b""
    while i + 60 <= len(data):
        hdr = data[i:i + 60]
        name, size = hdr[:16].decode().strip(), int(hdr[48:58].decode().strip())
        body = data[i + 60:i + 60 + size]
        i += 60 + size + (size & 1)
        if name == "//":
            names = body
        elif name in ("/", "/SYM64/"):
            continue
        else:
            if name.startswith("/") and name[1:].isdigit():
                o = int(name[1:]); name = names[o:names.index(b"/\n", o)].decode()
            yield name.rstrip("/"), body

FIELD = {1: 8, 2: 4, 4: 4, 9: 4, 10: 4, 11: 4, 19: 4, 22: 4, 23: 4, 24: 8, 26: 4, 41: 4, 42: 4, 34: 4}
RELAX = {41: 2, 42: 3, 22: 3, 9: 2}   # bytes before the field the linker may rewrite

def elf_funcs(obj):
    """(symbol, bytes, mask) of each defined function of a relocatable ELF64 x86-64 object."""
    if obj[:4] != b"\x7fELF" or obj[4] != 2:
        return
    shoff, = struct.unpack_from("<Q", obj, 0x28)
    shentsize, shnum, shstrndx = struct.unpack_from("<HHH", obj, 0x3a)
    secs = [struct.unpack_from("<IIQQQQIIQQ", obj, shoff + k * shentsize) for k in range(shnum)]
    def data(s): return obj[s[4]:s[4] + s[5]]
    masks = {k: bytearray(b"\xff" * s[5]) for k, s in enumerate(secs) if s[1] == 1}
    for s in secs:
        if s[1] == 4 and s[7] in masks:          # SHT_RELA for section sh_info
            d, m = data(s), masks[s[7]]
            for off in range(0, len(d), 24):
                r_off, r_info = struct.unpack_from("<QQ", d, off)
                t = r_info & 0xffffffff
                w, b = FIELD.get(t, 4), RELAX.get(t, 0)
                for j in range(max(0, r_off - b), min(len(m), r_off + w)):
                    m[j] = 0
    for s in secs:
        if s[1] != 2:                             # SHT_SYMTAB
            continue
        strtab = data(secs[s[6]]); d = data(s)
        for off in range(0, len(d), 24):
            st_name, st_info, _, st_shndx, st_value, st_size = struct.unpack_from("<IBBHQQ", d, off)
            if st_info & 0xf != 2 or st_size == 0 or not (0 < st_shndx < len(secs)) or st_shndx not in masks:
                continue
            name = strtab[st_name:strtab.index(b"\0", st_name)].decode()
            body = data(secs[st_shndx])[st_value:st_value + st_size]
            yield name, bytes(body), bytes(masks[st_shndx][st_value:st_value + st_size])

def main(binary, funcs, *libs):
    img = open(binary, "rb").read()
    base = 0x400000                                # p_vaddr - p_offset of the first PT_LOAD (readelf -l)
    by_size = collections.defaultdict(list)
    for l in open(funcs):
        a, n, k, _ = l.rstrip("\n").split("\t")[:4]
        by_size[int(n)].append(int(a, 16))
    found = collections.defaultdict(set)
    nsym = 0
    for lib in libs:
        libname = lib.rsplit("/", 1)[-1]
        for member, obj in ar_members(lib):
            for name, body, mask in elf_funcs(obj):
                nsym += 1
                for a in by_size.get(len(body), ()):
                    o = a - base
                    cand = img[o:o + len(body)]
                    if all((x ^ y) & m == 0 for x, y, m in zip(cand, body, mask)):
                        found[a].add((libname, member, name))
    for a in sorted(found):
        libs_ = sorted({(l, m) for l, m, _ in found[a]})
        names = ",".join(sorted({s for _, _, s in found[a]}))
        n = next(n for n, v in by_size.items() if a in v)
        print(f"{a:x}\t{n}\t{libs_[0][0]}\t{';'.join(m for _, m in libs_)}\t{names}")
    print(f"# {nsym} library function symbols, {len(found)} functions of the binary named", file=sys.stderr)

if __name__ == "__main__":
    main(*sys.argv[1:])
