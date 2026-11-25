import FV7z.Lemmas.Sse2
import FV7z.Lemmas.Xmm2
/-!
# `movups` loads and stores whose values are followed (PLAN.md M, `__memmove_sse2_unaligned`)

glibc's `__memmove_sse2_unaligned` copies 16 to 32 bytes with two loads and two stores, the second pair at
`[rsi + rdx - 16]` and `[rdi + rdx - 16]` (`movups xmm1, [rsi + rdx - 16]`, `movups [rdi + rdx - 16], xmm1`).

- `VOp.movups_m`, `VOp.movups_mi`: `movups xmmN, [b + d]` and `movups xmmN, [b + i + d]` as `VOp`s, the register's
  new low 128 bits the bytes loaded; `VOpI.movups_m`, `VOpI.movups_mi`.
- `toBytesLE_ofBytesLE`: a register loaded from bytes and stored as many bytes stores them.
- `movups_sti`, `Seg.s_movups_sti`: `movups xmmword [b + i + d], xmmN`, as `movups_st` and `Seg.s_movups_stv`.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- A store of a load of as many bytes: the bytes. -/
theorem toBytesLE_ofBytesLE {w : Nat} {bs : List Byte} (hw : w = 8 * bs.length) :
    toBytesLE (ofBytesLE w bs) bs.length = bs := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [toBytesLE, List.getElem_map, List.getElem_range]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, getLsbD_ofBytesLE]
  have h3 : (8 * k + i) / 8 = k := by omega
  have h4 : (8 * k + i) % 8 = i := by omega
  rw [h3, h4, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
  simp [hi, h2, show 8 * k + i < w by omega]

namespace VOp

/-- `movups xmmN, [b + d]`. -/
def movups_m (n b d : Nat) : VOp :=
  .v 16 false (fun g => eaB g b d) (fun g _ _ => g) fun _ x bs => xset x (xmmOf n) (ofBytesLE 128 bs)

/-- The address `[b + i + d]` of registers `g`. -/
abbrev eaBI (g : Gprs) (b i d : Nat) : Addr := g.get (regOf b) + g.get (regOf i) + BitVec.ofNat 64 d

/-- `movups xmmN, [b + i + d]`. -/
def movups_mi (n b i d : Nat) : VOp :=
  .v 16 false (fun g => eaBI g b i d) (fun g _ _ => g) fun _ x bs => xset x (xmmOf n) (ofBytesLE 128 bs)

end VOp

theorem VOpI.movups_m {w n b d len : Nat} :
    VOpI prof (mk (.sse .movups) w [.xmm n, .mem (mbd b d 128)] len) (VOp.movups_m n b d) := by
  intro s o t htf hac hdec hld _
  refine ⟨withZmm s.cpu.vec.zmm (xmmOf n) ((s.cpu.vec.zmm (xmmOf n)).extractLsb' 128 384 ++
    ofBytesLE 128 (readBytes s.proc.mm.mem (eaD s b d) 16)),
    t, instruction_next htf hdec ?_, xsOf_with _ _ _ _⟩
  simp only [exec, execSse, Sem.movups, moveBits, mbd, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
    memRef, effOffset, pure, Prog.readReg, Prog.read, Prog.run, BitVec.mul_one, writeOp, Prog.readZmm]
  rw [eaD_adv, checkAccess_ok (s := advance s len) hac hld]
  rfl

theorem VOpI.movups_mi {w n b i d len : Nat} :
    VOpI prof (mk (.sse .movups) w [.xmm n, .mem (mbi b i d 128)] len) (VOp.movups_mi n b i d) := by
  intro s o t htf hac hdec hld _
  refine ⟨withZmm s.cpu.vec.zmm (xmmOf n) ((s.cpu.vec.zmm (xmmOf n)).extractLsb' 128 384 ++
    ofBytesLE 128 (readBytes s.proc.mm.mem (eaI s b i d) 16)),
    t, instruction_next htf hdec ?_, xsOf_with _ _ _ _⟩
  simp only [exec, execSse, Sem.movups, moveBits, mbi, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
    memRef, effOffset, pure, Prog.readReg, Prog.read, Prog.run, BitVec.mul_one, writeOp, Prog.readZmm]
  rw [checkAccess_ok (s := advance s len) hac hld]
  rfl

/-- `movups xmmword [b + i + d], xmmN`. -/
theorem movups_sti {n b i d len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) =
      .ok (mk (.sse .movups) 32 [.mem (mbi b i d 128), .xmm n] len))
    (hwr : Writable prof s (eaI s b i d) 16) :
    (instruction prof s).runStream o t =
      (.running (nx (st s (eaI s b i d) (toBytesLE ((s.cpu.vec.zmm (xmmOf n)).setWidth 128) 16)) len
        s.cpu.gpr (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, execSse, Sem.movups, moveBits, mbi, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
    memRef, effOffset, pure, Prog.readReg, Prog.write, Prog.run, BitVec.mul_one, writeOp, Prog.readZmm]
  rw [checkAccess_ok (s := advance s len) hac hwr]
  rfl

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t j : Nat}
  {e' : Addr} {code : List Byte} {V : Addr → Byte}

/-- `movups xmmword [b + i + d], xmmN`, into bytes the run may store into; the vector registers are kept. -/
theorem s_movups_sti (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {n b i d len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk (.sse .movups) 32 [.mem (mbi b i d 128), .xmm n] len))
    (hst : ∀ k < 16, Foot Wl ((eaI X b i d).add k))
    (k' : ContG prof F Wl L s₀ o gev gP gE (Vst V (eaI X b i d) (toBytesLE (xlo X n) 16))
      fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr ∧ Y.cpu.vec = X.cpu.vec) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (xlo X n) 16) (a := eaI X b i d) (by simpa using hst)
    rw [toBytesLE_length] at hwr
    exact ⟨_, _, movups_sti (s := X.withMem M) htf hac (c.dec hK' hin hrip hd) hwr, hKs.nx rfl rfl rfl, hAs,
      rip_add hrip M len, rfl, rfl⟩) k'

end FV7z.Fn.Seg
