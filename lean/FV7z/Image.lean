import ZellicX86.Load.FileImage
/-!
# S5: the bytes of `7zzs`, 7-Zip 26.06 for linux-x64 (PLAN.md §4)

`../../release/26.06/7zzs`, taken from the author's release `7z2606-linux-x64.tar.xz`
(SHA-256 `2b539cf067b2ad48e1baa5093dbaa8818b73542d1222a0ffde9dc5f2922ea62e`), as `FV7z.V2606.zzs`, through Zellic's
trusted loader `#file_image`: building this module fails unless the file has the SHA-256 written here. Every
statement of this project about `7zzs` is about the constants this command defines (`FV7z.V2606.zzs.blob`).

The file is a statically linked, non-PIE (`ET_EXEC`) x86-64 executable, stripped of its symbol table, built by
GCC 9.4.0 (Ubuntu 20.04) against glibc 2.31.
-/

#file_image "../../release/26.06/7zzs" sha256 "0b58a64e71ebdf53751cd954cad1cc552c6a11ef51336bee6acafbdc54c28c1f"
  as FV7z.V2606.zzs
