import FV7z.Ndi.Mem
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
/-!
# `_dl_non_dynamic_init`: the conditions of its first two cut points (PLAN.md G3, startup)

The prologue, and the way from the return of `_dl_get_origin` to the first `getenv` when the kernel gave no vDSO.
-/
open FV7z.Sga (vo vr vs)
namespace FV7z.Ndi
variable {F : Footprint} {Wl : List Rgn}
/-- The bytes after the five `push`es. -/
def frV (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r14 8)) (g.rsp - 16#64) (toBytesLE g.r13 8))
    (g.rsp - 24#64) (toBytesLE g.r12 8)) (g.rsp - 32#64) (toBytesLE g.rbp 8)) (g.rsp - 40#64) (toBytesLE g.rbx 8)

/-- The prologue: to the `call` of `_dl_get_origin`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hst : ∀ i < 40, Foot Wl (Addr.add (g.rsp - 40#64) i)) (hsp : 40 ≤ g.rsp.toNat) :
    W_0 F Wl (fun j' g' _ V' => j' = 16 ∧ g' = { g with rsp := g.rsp - 120#64 } ∧ V' = frV V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  unfold frV
  dsimp only at hst hsp ⊢
  have w : ∀ (a : Addr) (k : Nat), k + 8 ≤ 40 → a.toNat = rsp.toNat - 40 + k → ∀ i < 8, Foot Wl (Addr.add a i) := by
    intro a k hk ha i hi
    have := hst (k + i) (by omega)
    rwa [show Addr.add (rsp - 40#64) (k + i) = Addr.add a i by simp only [Addr.add]; bv_omega] at this
  have w1 := w (rsp - 8) 32 (by omega) (by bv_omega)
  have w2 := w (rsp - 16#64) 24 (by omega) (by bv_omega)
  have w3 := w (rsp - 24#64) 16 (by omega) (by bv_omega)
  have w4 := w (rsp - 32#64) 8 (by omega) (by bv_omega)
  have w5 := w (rsp - 40#64) 0 (by omega) (by bv_omega)
  clear w hst
  wpx [W_0, o0, Op.push]
  simp only [s16, s24, s32, s40, s120]
  exact ⟨w1, w2, w3, w4, w5, trivial, trivial⟩

/-- The bytes after the stores up to `getenv ("LD_WARN")`: `_dl_origin_path`'s neighbour `0x793828` (the main map's
`l_origin`) is `org`, the main map's `l_phdr` and `l_phnum` (`0x793788`, `0x793798`) are `ph` and `pn`, the four vDSO
pointers (`0x791cc0` to `0x791cd8`) and `0x791cb8` are null. -/
def aV (V : Addr → Byte) (org ph pn : BitVec 64) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (Vst (Vst (Vst V 7944232#64 (toBytesLE org 8)) 7944072#64 (toBytesLE ph 8))
    7944088#64 (toBytesLE (pn.setWidth 16) 2)) 7937240#64 (toBytesLE 0#64 8)) 7937232#64 (toBytesLE 0#64 8))
    7937224#64 (toBytesLE 0#64 8)) 7937216#64 (toBytesLE 0#64 8)) 7937208#64 (toBytesLE 0#64 8)

/-- After `_dl_get_origin`, without a vDSO (`_dl_sysinfo_dso` at `0x7a8508` and `_dl_sysinfo_map` at `0x7a84f0`
null) and not a secure exec (`__libc_enable_secure` at `0x791ce0` is 0): to the `call` of `getenv ("LD_WARN")`. -/
theorem vc_21 {g : Gprs} {f : Rflags} {V : Addr → Byte} {ph pn : BitVec 64}
    (hr : ∀ x : Addr, 7827456 ≤ x.toNat → x.toNat < 8032256 → Foot F.data x)
    (hw : ∀ x : Addr, 7827456 ≤ x.toNat → x.toNat < 8032256 → Foot Wl x)
    (h1 : rdq(V, 8029448#64) = 0#64) (h2 : rdq(V, 8029568#64) = ph) (h3 : rdq(V, 8029592#64) = pn)
    (h4 : rdq(V, 8029424#64) = 0#64) (h5 : rdd(V, 7937248#64) = 0#32) :
    W_21 F Wl (fun j' g' _ V' => j' = 2018 ∧
      g' = { g with rax := 0#64, rdx := 0#64, rbp := 0#64, rdi := 7289136#64 } ∧ V' = aV V g.rax ph pn) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  unfold aV
  wpx [W_21, W_2800, W_2816, W_2827, W_2838, W_2849, W_2860, W_1945, W_2011, o1, o35, o36, o37, o38, o39, o40, o2, o3,
    Op.cmpmia, Op.sta, Op.lda, Op.stia]
  simp (disch := decide) only [rq, h1, h2, h3, h4, h5, BitVec.xor_self]
  exact ⟨gf hr _ 8 (by decide), gf hw _ 8 (by decide), gf hr _ 8 (by decide), gf hw _ 8 (by decide),
    gf hr _ 8 (by decide), gf hw _ 2 (by decide), fun _ => ⟨gf hr _ 8 (by decide), fun h => absurd h (by decide),
      fun _ => ⟨gf hw _ 8 (by decide), gf hw _ 8 (by decide), gf hw _ 8 (by decide), gf hw _ 8 (by decide),
        gf hr _ 4 (by decide), gf hw _ 8 (by decide), fun _ => ⟨rfl, rfl⟩, fun h => absurd h (by decide)⟩⟩,
    fun h => absurd h (by decide)⟩
end FV7z.Ndi
