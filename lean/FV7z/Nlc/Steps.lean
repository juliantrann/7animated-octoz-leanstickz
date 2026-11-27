import FV7z.Nlc.Cuts
import FV7z.Sbrk.Holds
/-!
# `_nl_normalize_codeset`: the steps outside the generated pieces (PLAN.md §M, M1)

- `call_91`, `call_196`, `call_245`: the `call`s of `malloc` (`len + 1`; `len + 4` for an all-digit name; `4` for an
  empty one); `ml_91`, `ml_196`, `ml_245`: their target, `0x633160`.
- `ret_190`, `ret_234`: the `ret`s (the new name; `malloc` failed).
-/
namespace FV7z.Nlc
open ZellicX86 Decode FV7z.Leaf

def pc91 : List Byte := [0xe8, 0xd0, 0x91, 0x01, 0x00]
theorem pc91_0 : ∀ feat, Dec feat pc91 0 (FV7z.mk .call 64 [.rel 102864] 5) := by dec_rfl
theorem w_91 : pc91 <+: nlc.drop 91 := by decide +kernel
theorem call_91 (feat : Features) : Dec feat nlc 91 (FV7z.mk .call 64 [.rel 102864] 5) :=
  Dec.shift (j := 91) (k := 0) (pc91_0 feat) w_91 (Nat.zero_le _)

def pc196 : List Byte := [0xe8, 0x67, 0x91, 0x01, 0x00]
theorem pc196_0 : ∀ feat, Dec feat pc196 0 (FV7z.mk .call 64 [.rel 102759] 5) := by dec_rfl
theorem w_196 : pc196 <+: nlc.drop 196 := by decide +kernel
theorem call_196 (feat : Features) : Dec feat nlc 196 (FV7z.mk .call 64 [.rel 102759] 5) :=
  Dec.shift (j := 196) (k := 0) (pc196_0 feat) w_196 (Nat.zero_le _)

def pc245 : List Byte := [0xe8, 0x36, 0x91, 0x01, 0x00]
theorem pc245_0 : ∀ feat, Dec feat pc245 0 (FV7z.mk .call 64 [.rel 102710] 5) := by dec_rfl
theorem w_245 : pc245 <+: nlc.drop 245 := by decide +kernel
theorem call_245 (feat : Features) : Dec feat nlc 245 (FV7z.mk .call 64 [.rel 102710] 5) :=
  Dec.shift (j := 245) (k := 0) (pc245_0 feat) w_245 (Nat.zero_le _)

theorem w_190 : Sbrk.pret <+: nlc.drop 190 := by decide +kernel
theorem ret_190 (feat : Features) : Dec feat nlc 190 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 190) (k := 0) (Sbrk.pret_0 feat) w_190 (Nat.zero_le _)
theorem w_234 : Sbrk.pret <+: nlc.drop 234 := by decide +kernel
theorem ret_234 (feat : Features) : Dec feat nlc 234 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 234) (k := 0) (Sbrk.pret_0 feat) w_234 (Nat.zero_le _)

/-- The three calls are of `malloc` (`0x633160`). -/
theorem ml_91 : nlc_at.add (91 + 5) + BitVec.ofNat 64 102864 = 0x633160 := by decide
theorem ml_196 : nlc_at.add (196 + 5) + BitVec.ofNat 64 102759 = 0x633160 := by decide
theorem ml_245 : nlc_at.add (245 + 5) + BitVec.ofNat 64 102710 = 0x633160 := by decide

/-! ## Next steps (not done yet)

None of `Nlc/` has been built yet: triage `FV7z.Nlc.Steps` first (it imports the generated pieces).

`Nlc/Vc.lean`, the straight pieces by `mcx` as in `Fmi/Vc.lean`. Split each one where its flags branch, with
hypotheses such as `(g.rsi == 0) = true`:
- `vc_0e` (`rsi = 0`): to 245, `edi = 4`. `vc_0n`: to 48, with `rbx = [0x7914c8]` (`__ctype_b`), `rbp = rdx = str`,
  `r12 = n`, `r8 = str + n`, `r9 = 0`, `esi = 1`, `edi = 0`.
- `vc_48n` (byte not alnum: `rb V (rbx + c*2) &&& 8 = 0`): to 74. `vc_48d`, `vc_48x` (alnum, a digit or not:
  `c - 48 < 10` in 32 bits): to 74, `rdi + 1`, `esi` kept or 0 (`cmov` zero-extends).
- `vc_74l` (`r8 ≠ rdx + 1`): to 48. `vc_74d` (`esi ≠ 0`): to the `call` at 196, `rdi + 4`. `vc_74n`: to 91,
  `rdi + 1`.
- `vc_96z`, `vc_201z`, `vc_250z` (`rax = 0`): to 224. `vc_224`: the pops, `rax = 0`, to the `ret` at 234.
- `vc_96n`: to 104, `r9 = rax`. `vc_201n`, `vc_250n`: "iso\0" stored (`0x6f7369`, 4 bytes), `rax = p + 3`, to 104 or
  180. `vc_104`: `r8 = [0x7914d0]` (`__ctype_tolower`), `edx = 0`, to 140.
- `vc_140a` (`[rbx + c*2 + 1] &&& 4 ≠ 0`): to 131, storing the low byte of `[r8 + c*4]` at `rax`, then `rax + 1`.
  `vc_140s` (not a digit): to 131. `vc_140dl` and `vc_140de` (a digit stored; `r12 > rdx + 1` or not): to 140 or 180.
- `vc_131l` and `vc_131e` (`rdx + 1 < r12` or not): to 140 or 180. `vc_180`: the 0 stored, `rax = r9`, the pops, to 190.

`Nlc/Holds.lean`, as `Fmi/Holds.lean`:
- `Rt V0 s n` is the region read: `[s, s+n)`, the table at `[0x7914c8]` (512 bytes), the one at `[0x7914d0]` (1024
  bytes) and the two pointers. It needs `F.data`, and must lie apart from `[S-32, S)`.
- `malloc` is a continuation hypothesis `Mal`. At `0x633160`, with `rdi = sz` and the return address at `rsp`, the run
  goes on if it goes on from every return with `rsp + 8`, `Km`, and the bytes kept on `R = Rt ∪ [S-24, S+8)`, where
  `rax = 0`, or `rax = p` with `p + sz ≤ 2^64`, `[p, p+sz)` in `Wl` and apart from `R`.
- `ch` is the byte a name byte gives: its `tolower` if alpha, itself if a digit, else none. `out k` is `ch` over the
  first `k` bytes, `cnt k` the count of the alnums, and `dg k` whether all the alnums are digits.
- The counting loop holds at 48 (`rdx = s + k`, `rdi = cnt k`, `esi = dg k`). The copy loop holds at 140, with the
  bytes `Vst Vm w0 (out k)`, `rax = w0 + |out k|` and `w0 = p` or `p + 3`.
- An Env hypothesis is needed: for `i < n`, alpha or digit implies alnum. Then `|out k| ≤ cnt k` and the stores stay
  in `[p, p+sz)`.
- The result: `rax = 0` (`malloc` failed), or `rax = p` with the bytes `("iso" if dg n) ++ out n ++ [0]` at `p`.
-/

end FV7z.Nlc
