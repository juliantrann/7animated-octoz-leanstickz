import FV7z.Strlen.Len
import FV7z.Start.ToTls
import FV7z.Lemmas.CallM
/-!
# `strlen` through the PLT (PLAN.md M, the PLT contracts)

`7zzs` calls `strlen` at `0x401108`: `jmp qword [rip + 0x390ff2]`, through the GOT's slot `0x792100`, which
`apply_irel` filled with what the resolver at `0x636090` returned (`GotOkB`): `__strlen_sse2` (`0x6546d0`) unless the
processor has AVX and AVX2. Without both, a call at `0x401108` does what `Str.LenAt` says (`lenAtG_plt`).

The jump reads the slot, so the slot has to be a byte of the footprint's data (`GotFoot`), which `Str.LenAt` does not
ask: `Pm` speaks of the bytes `V` only, and `V` is the memory's only on the footprint. `LenAtG` is `Str.LenAt` with
`GotFoot F`; the contracts reached through the PLT are to take it (PLAN.md M).
-/
namespace FV7z
open ZellicX86 Decode

section
variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- `jmp qword [rip + d]`: to the address read. -/
theorem jmp_mrip {d len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .jmp 64 [.mem (mrip d 64)] len))
    (hld : Readable prof s (eaR s len d) 8)
    (hcan : Addr.canonical prof.feat.la57 (ofBytesLE 64 (readBytes s.proc.mm.mem (eaR s len d) 8)) = true) :
    (instruction prof s).runStream o t =
      (.running (upd s (ofBytesLE 64 (readBytes s.proc.mm.mem (eaR s len d) 8)) s.cpu.gpr (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, Sem.jmp, mk, mrip, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
    effOffset, pure, Prog.readRip, Prog.read, Prog.run, Opd.width, BitVec.mul_one, jumpTo]
  rw [eaR_adv, checkAccess_ok (s := advance s len) hac hld]
  rw [show (advance s len).proc.mm.mem = s.proc.mm.mem from rfl, hcan]
  simp only [↓reduceIte, Prog.writeRip, done, Prog.run, bind, Prog.bind, pure, BitVec.setWidth_eq]
  rfl

end

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t j : Nat}
  {e' : Addr} {code : List Byte} {V : Addr → Byte}

/-- `jmp qword [rip + d]`, through bytes of the footprint's data, to the first byte of a segment. -/
theorem s_jmp_mrip (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {d len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .jmp 64 [.mem (mrip d 64)] len))
    (hl : ∀ i < 8, Foot F.data ((eaR X len d).add i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) (h₂ : 0 < code₂.length)
    (htgt : ofBytesLE 64 ((byteAddrs (eaR X len d) 8).map V) = e₂)
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e₂ ∧ Y.cpu.gpr = X.cpu.gpr) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    have hca := ((c.codeAt hK' hin₂) 0 h₂).1
    rw [addr_add_zero] at hca
    obtain ⟨hrd, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' hl
    have hT : ofBytesLE 64 (readBytes (X.withMem M).proc.mm.mem (eaR (X.withMem M) len d) 8) = e₂ :=
      (congrArg (ofBytesLE 64) hv).trans htgt
    have hr := jmp_mrip (s := X.withMem M) (o := o) (t := t + 1) htf hac (c.dec hK' hin hrip hd) hrd
      (by rw [hT]; exact hca)
    rw [hT] at hr
    exact ⟨_, _, hr, hK'.upd rfl rfl rfl, hA', rfl, rfl⟩) k'

end FV7z.Fn.Seg

namespace FV7z.Strlen
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Glibc FV7z.Start

/-- The 8 bytes of `7zzs` at `0x401108`, `strlen`'s PLT entry: `jmp qword [rip + 0x390ff2]`, `xchg ax, ax`. -/
def pltLen : List Byte := [0xff, 0x25, 0xf2, 0x0f, 0x39, 0x00, 0x66, 0x90]

theorem pltLen_pin : Exe.bytesAt V2606.zzs.blob 0x401108 8 = some pltLen := by decide +kernel

theorem pd0 : ∀ feat, Dec feat pltLen 0 (FV7z.mk .jmp 64 [.mem (mrip 3739634 64)] 6) := by dec_rfl

/-- The GOT's slots, `[0x792018, 0x792110)`, are bytes of the footprint's data. -/
def GotFoot (F : Footprint) : Prop := ∀ a : Addr, 0x792018 ≤ a.toNat → a.toNat < 0x792110 → Foot F.data a

/-- Without both AVX and AVX2, the GOT's slot of `strlen` holds `__strlen_sse2`. -/
theorem got_strlen {prof : Profile} {W : Addr → Byte} (hG : GotOkB prof W)
    (hb : ¬ (prof.feat.avx = true ∧ prof.feat.avx2 = true)) :
    ofBytesLE 64 ((byteAddrs 0x792100#64 8).map W) = 0x6546d0#64 := by
  have hR : Returns prof [(0x6546d0, []), (0x654a90, [Features.avx, Features.avx2])]
      (ofBytesLE 64 ((byteAddrs 0x792100#64 8).map W)) :=
    hG (0x792100, 0x636090) (by unfold V2606.irel; exact List.Mem.tail _ (List.Mem.head _))
      (0x636090, 53, [(0x6546d0, []), (0x654a90, [Features.avx, Features.avx2])])
      (by unfold V2606.resolvers; exact List.Mem.head _) rfl
  obtain ⟨v, hv, hw, hf⟩ := hR
  rcases List.mem_cons.1 hv with rfl | hv
  · exact hw
  · rcases List.mem_cons.1 hv with rfl | hv
    · exact (hb ⟨hf _ (List.Mem.head _), hf _ (List.Mem.tail _ (List.Mem.head _))⟩).elim
    · nomatch hv

/-- `Str.LenAt` with the GOT's slots bytes of the footprint's data (`GotFoot`). -/
def LenAtG (prof : Profile) (L : List (Addr × List Byte)) (o : Oracle) (e : Addr) (Pm : (Addr → Byte) → Prop) :
    Prop :=
  ∀ {F : Footprint} {Wl : List Rgn} {s₀ : State} {gev : List Event} {gP : State → Nat → List Event → Prop}
    {gE : Outcome → List Event → Prop} {X : State} {t : Nat} {V : Addr → Byte} {e' : Addr} {code : List Byte}
    {j : Nat} (n : Nat), Seg prof F Wl L s₀ o → GotFoot F → KeptW Wl s₀ X → Agree F X.proc.mm.mem V →
    X.cpu.rip = e → Pm V →
    CodeIn L e' code → j < code.length → rdq(V, X.cpu.gpr.rsp) = e'.add j →
    (∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) →
    X.cpu.gpr.rdi.toNat + n < 2 ^ 64 →
    (∀ k < n, V (Addr.add X.cpu.gpr.rdi k) ≠ 0) → V (Addr.add X.cpu.gpr.rdi n) = 0 →
    (∀ x : Addr, X.cpu.gpr.rdi.toNat / 4096 ≤ x.toNat / 4096 →
      x.toNat / 4096 ≤ (X.cpu.gpr.rdi.toNat + n) / 4096 → Foot F.data x) →
    (∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e'.add j →
      Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → Z.cpu.gpr.rax = BitVec.ofNat 64 n → Z.cpu.gpr.rbx = X.cpu.gpr.rbx →
      Z.cpu.gpr.rbp = X.cpu.gpr.rbp → Z.cpu.gpr.r12 = X.cpu.gpr.r12 → Z.cpu.gpr.r13 = X.cpu.gpr.r13 →
      Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 → GoG prof L o gev gP gE Z t') →
    GoG prof L o gev gP gE X t

/-- `strlen` through the PLT, on a processor without both AVX and AVX2: the jump through the GOT's slot to
`__strlen_sse2`, then `lenAt_sse2`. -/
theorem lenAtG_plt {prof : Profile} {L : List (Addr × List Byte)} {o : Oracle}
    (hb : ¬ (prof.feat.avx = true ∧ prof.feat.avx2 = true))
    (hinP : CodeIn L 4198664#64 pltLen) (hin : CodeIn L 0x6546d0#64 sl2) :
    LenAtG prof L o 4198664#64 (GotOkB prof) := by
  intro F Wl s₀ gev gP gE X t V e' code j n c hgf hK hA hrip hG hin₂ hj hra hl hov hnz hz hft K
  have he : eaR X 6 3739634 = 0x792100#64 := by simp only [eaR, hrip]; rfl
  refine c.s_jmp_mrip hK hA hinP (j := 0) (by decide) (by rw [hrip, addr_add_zero]) (pd0 prof.feat)
    (fun i hi => ?_) hin (by rw [sl2_length]; decide) (by rw [he]; exact got_strlen hG hb) ?_
  · rw [he]
    apply hgf
    · simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
    · simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
  · rintro Y t' hKY hAY ⟨hrY, hgY⟩
    have h := lenAt_sse2 (prof := prof) (L := L) (o := o) (Pm := fun _ => True) hin n c hKY hAY hrY trivial hin₂ hj
    rw [hgY] at h
    exact h hra hl hov hnz hz hft K

end FV7z.Strlen
