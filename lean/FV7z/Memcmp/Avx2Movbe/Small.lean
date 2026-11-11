import FV7z.Memcmp.Avx2Movbe.Tail
/-!
# `__memcmp_avx2_movbe` of `7zzs`: fewer than 32 bytes (PLAN.md G2.1)

The paths from `432` by `n`: `n = 0` (`416`), `n = 1` (`400`), and, to come, `2..3` (`368`), `4..7` (`304`),
`8..15` (`458`), `16..31` (`528`). Also a `jcc` step that keeps `CF` when not taken, which `432` and `304` need.
-/
namespace FV7z.MemcmpCall
open ZellicX86 Decode Memcmp

variable {prof : Profile} {code : List Byte} {e : Addr} {L : List (Addr × List Byte)} {s₀ : State} {ra : Addr}
  {o : Oracle} {X : State} {t k : Nat}

namespace Call

/-- `jcc`, as `s_jcc`, with `CF` kept when not taken. -/
theorem s_jcc' (c : Call prof code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length) (hrip : X.cpu.rip = e.add k)
    {cc : Cond} {rel len tgt : Nat} (hd : Dec prof.feat code k (FV7z.mk (.jcc cc) 64 [.rel rel] len))
    (htgt : (k + len + rel) % 2 ^ 64 = tgt % 2 ^ 64) (ht : tgt < code.length)
    (taken : X.cpu.rflags.cond cc = true → Then prof L s₀ ra o e tgt fun Y => Y.cpu.gpr = X.cpu.gpr ∧
      Y.cpu.vec.zmm = X.cpu.vec.zmm)
    (fall : X.cpu.rflags.cond cc = false → Then prof L s₀ ra o e (k + len) fun Y => Y.cpu.gpr = X.cpu.gpr ∧
      Y.cpu.vec.zmm = X.cpu.vec.zmm ∧ Y.cpu.rflags.cf = X.cpu.rflags.cf) :
    Go prof L s₀ ra o X t := by
  cases hcc : X.cpu.rflags.cond cc
  · exact c.next hK hk hrip (fun M hK' htf _ => ⟨_, _, jcc_n (s := X.withMem M) htf (c.dec hK' hrip hd) hcc,
      hK'.nx rfl rfl rfl, rip_add hrip M len, rfl, rfl, rfl⟩) (fall hcc)
  · exact c.s_jcc hK hk hrip hd htgt ht (fun _ => taken hcc) (fun h => absurd (hcc.symm.trans h) (by simp))

end Call
end FV7z.MemcmpCall

namespace FV7z.MemcmpAvx2
open ZellicX86 Decode Memcmp MemcmpCall Order

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {ra : Addr} {o : Oracle} {e : Addr}

theorem addr_add_zero (b : Addr) : b.add 0 = b := by simp [Addr.add]

/-- At `416`, no bytes: `XOR eax, eax`, `RET`. -/
theorem at416 (x : Ctx prof L s₀ ra o e) {X : State} {t : Nat} (hK : Kept s₀ X) (hC : Callee s₀ X)
    (hrip : X.cpu.rip = e.add 416) (hn : nn s₀ = 0) : Go prof L s₀ ra o X t :=
  x.c.s_xor_rr hK (by simp [avx2Movbe_length]) hrip (d416 _ x.f) fun Y1 _ hK1 hr1 ⟨g1, _⟩ =>
  x.c.ret hK1 (hC.of_gpr (by simp [g1])) (by simp [avx2Movbe_length]) hr1 (d418 _ x.f)
    (post_eq (by simp [g1]) fun i hi => absurd hi (by omega))

/-- At `400`, one byte: `MOVZX`, `MOVZX`, `SUB`, `RET`. -/
theorem at400 (x : Ctx prof L s₀ ra o e) {X : State} {t : Nat} (hK : Kept s₀ X) (hC : Callee s₀ X)
    (hrip : X.cpu.rip = e.add 400) (hdi : X.cpu.gpr.rdi = (p₁ s₀).add 0) (hsi : X.cpu.gpr.rsi = (p₂ s₀).add 0)
    (hn : nn s₀ = 1) : Go prof L s₀ ra o X t :=
  x.c.s_movzx8_d hK (by simp [avx2Movbe_length]) hrip (d400 _ x.f) mem₁ (a := 0) (by simp [hdi])
    (show _ ≤ nn s₀ by omega) fun Y1 _ hK1 hr1 g1 =>
  x.c.s_movzx8_d hK1 (by simp [avx2Movbe_length]) hr1 (d403 _ x.f) mem₂ (a := 0) (by simp [g1, hsi])
    (show _ ≤ nn s₀ by omega) fun Y2 _ hK2 hr2 g2 =>
  x.c.s_sub_rr hK2 (by simp [avx2Movbe_length]) hr2 (Or.inl rfl) (d406 _ x.f) fun Y3 _ hK3 hr3 ⟨g3, _, _⟩ => by
    have hY : Y3.cpu.gpr.rax.setWidth 32 = (s₀.proc.mm.mem.readByte ((p₁ s₀).add 0)).setWidth 32 -
        (s₀.proc.mm.mem.readByte ((p₂ s₀).add 0)).setWidth 32 := by
      simp only [g3, g2, g1, set_regOf_0, set_regOf_1, rv, get_0, get_1]
      rw [BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq, setWidth_byte, setWidth_byte]
    refine x.c.ret hK3 (hC.of_gpr (by simp [g3, g2, g1])) (by simp [avx2Movbe_length]) hr3 (d408 _ x.f) ?_
    by_cases h0 : Ag s₀ 0
    · refine post_eq (by rw [hY, show s₀.proc.mm.mem.readByte ((p₁ s₀).add 0) =
        s₀.proc.mm.mem.readByte ((p₂ s₀).add 0) from h0, BitVec.sub_self]; rfl) fun i hi => ?_
      rw [show i = 0 by omega]; exact h0
    · exact post_diff (q := 0) (by omega) (fun i hi => absurd hi (by omega)) h0 rfl rfl hY

/-- At `528`, 16 to 31 bytes: the window of 16 at 0, `LEA` both pointers to the last 16, the window there, `RET` 0. -/
theorem at528 (x : Ctx prof L s₀ ra o e) {X : State} {t : Nat} (hK : Kept s₀ X) (hC : Callee s₀ X)
    (hrip : X.cpu.rip = e.add 528) (hdi : X.cpu.gpr.rdi = (p₁ s₀).add 0) (hsi : X.cpu.gpr.rsi = (p₂ s₀).add 0)
    (hdx : X.cpu.gpr.rdx = BitVec.ofNat 64 (nn s₀)) (h16 : 16 ≤ nn s₀) (h32 : nn s₀ ≤ 32) :
    Go prof L s₀ ra o X t :=
  win x hK hC (Or.inr rfl) (a := 0) (d528 _ x.f) (d532 _ x.f) (d536 _ x.f) (d540 _ x.f) (d545 _ x.f) (by decide)
    (by decide) hrip hdi hsi (by omega) (fun i hi => absurd hi (by omega))
    fun hall1 Y1 _ hK1 hr1 ⟨hC1, hdi1, hsi1, hdx1, _, _⟩ =>
  x.c.s_lea hK1 (by simp [avx2Movbe_length]) hr1 (d551 _ x.f) fun Y2 _ hK2 hr2 ⟨g2, _⟩ =>
  x.c.s_lea hK2 (by simp [avx2Movbe_length]) hr2 (d556 _ x.f) fun Y3 _ hK3 hr3 ⟨g3, _⟩ =>
  win x hK3 (hC1.of_gpr (by simp [g3, g2])) (Or.inr rfl) (a := nn s₀ - 16) (d561 _ x.f) (d565 _ x.f) (d569 _ x.f)
    (d573 _ x.f) (d578 _ x.f) (by decide) (by decide) hr3
    (by simp only [g3, g2, set_regOf_6, set_regOf_7, eaI, get_7, get_2, hdi1, hdx1, hdi, hdx, add_addr]
        exact add_mod _ (by have := nn_lt s₀; omega))
    (by simp only [g3, g2, set_regOf_6, set_regOf_7, eaI, get_6, get_2, hsi1, hdx1, hsi, hdx, add_addr]
        exact add_mod _ (by have := nn_lt s₀; omega))
    (by omega) (fun i hi => hall1 i (by omega))
    fun hall Y4 _ hK4 hr4 ⟨hC4, _, _, _, hz4, _⟩ =>
  x.c.ret hK4 hC4 (by simp [avx2Movbe_length]) hr4 (d584 _ x.f) (post_eq hz4 fun i hi => hall i (by omega))

/-- The result of two blocks of each string compared as big-endian numbers, the first `k` bytes and the bytes from
`j ≤ k` on: the contract's result. -/
theorem post_be {Y : State} {j k : Nat} (hjk : j ≤ k) (hk : k ≤ nn s₀)
    (hY : compare (Y.cpu.gpr.rax.setWidth 32).toInt 0 =
      compare (beV (readBytes s₀.proc.mm.mem (p₁ s₀) k ++ readBytes s₀.proc.mm.mem ((p₁ s₀).add j) (nn s₀ - j)))
        (beV (readBytes s₀.proc.mm.mem (p₂ s₀) k ++ readBytes s₀.proc.mm.mem ((p₂ s₀).add j) (nn s₀ - j)))) :
    contract.post s₀ Y := by
  have h := cmp_cover (xs := readBytes s₀.proc.mm.mem (p₁ s₀) (nn s₀))
    (ys := readBytes s₀.proc.mm.mem (p₂ s₀) (nn s₀)) (by simp [readBytes_length]) hjk
  rw [readBytes_take _ _ _ _ hk, readBytes_take _ _ _ _ hk, readBytes_drop, readBytes_drop] at h
  show compare (Y.cpu.gpr.rax.setWidth 32).toInt 0 = _
  rw [hY, cmp_be (by simp [readBytes_length])]
  exact h

/-- The register of the path at `368`: two bytes `R` by `MOVZX`, `SHL 8`, `BSWAP`, the byte `C` into the low
byte; as a number, `R` then `C`, big-endian. -/
theorem v368 {R C : List Byte} (hR : R.length = 2) (hC : C.length = 1) {v1 v2 v3 v4 : BitVec 64}
    (h1 : v1 = ((ofBytesLE 16 R).setWidth 32).setWidth 64)
    (h2 : v2 = (v1.setWidth 32 <<< 8).setWidth 64)
    (h3 : v3 = (ZellicX86.bswap (v2.setWidth 32)).setWidth 64)
    (h4 : v4 = (v3 &&& ~~~(BitVec.ofNat 64 ((2 ^ 8 - 1) * 2 ^ 0))) ||| ((ofBytesLE 8 C).setWidth 64 <<< 0)) :
    (v4.setWidth 32).toNat = beV (R ++ C) := by
  obtain ⟨b0, b1, rfl⟩ : ∃ b0 b1, R = [b0, b1] := by
    match R, hR with | [b0, b1], _ => exact ⟨b0, b1, rfl⟩
  obtain ⟨c, rfl⟩ : ∃ c, C = [c] := by
    match C, hC with | [c], _ => exact ⟨c, rfl⟩
  have e1 : v1.setWidth 32 = ofBytesLE 32 [b0, b1] := by
    rw [h1, BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq, setWidth_ofBytesLE (by simp)]
  have e2 : v2.setWidth 32 = ofBytesLE 32 ([0, b0, b1] ++ [0]) := by
    rw [h2, BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq, e1, ofBytesLE_snoc_zero,
      ofBytesLE_cons_zero]
  have e3 : v3 = ofBytesLE 64 (0 :: [b1, b0, 0]) := by
    rw [h3, e2, bswap_ofBytesLE (by simp), setWidth_ofBytesLE (by simp)]; rfl
  rw [h4, e3, setLow8, setWidth_ofBytesLE (by simp), toNat_ofBytesLE _ (by simp), leV_eq_beV]
  show beV [0, b0, b1, c] = beV [b0, b1, c]
  simp [beV]

/-- At `368`, 2 or 3 bytes: the first two and the last as big-endian numbers, their difference. -/
theorem at368 (x : Ctx prof L s₀ ra o e) {X : State} {t : Nat} (hK : Kept s₀ X) (hC : Callee s₀ X)
    (hrip : X.cpu.rip = e.add 368) (hdi : X.cpu.gpr.rdi = (p₁ s₀).add 0) (hsi : X.cpu.gpr.rsi = (p₂ s₀).add 0)
    (hdx : X.cpu.gpr.rdx = BitVec.ofNat 64 (nn s₀)) (h2 : 2 ≤ nn s₀) (h3 : nn s₀ ≤ 3) :
    Go prof L s₀ ra o X t :=
  have hv := nn_lt s₀
  x.c.s_movzx16_d hK (by simp [avx2Movbe_length]) hrip (d368 _ x.f) mem₁ (a := 0) (by simp [hdi])
    (show _ ≤ nn s₀ by omega) fun Y1 _ hK1 hr1 g1 =>
  x.c.s_movzx16_d hK1 (by simp [avx2Movbe_length]) hr1 (d371 _ x.f) mem₂ (a := 0) (by simp [g1, hsi])
    (show _ ≤ nn s₀ by omega) fun Y2 _ hK2 hr2 g2 =>
  x.c.s_shl32_8 hK2 (by simp [avx2Movbe_length]) hr2 (d374 _ x.f) fun Y3 _ hK3 hr3 g3 =>
  x.c.s_shl32_8 hK3 (by simp [avx2Movbe_length]) hr3 (d377 _ x.f) fun Y4 _ hK4 hr4 g4 =>
  x.c.s_bswap32 hK4 (by simp [avx2Movbe_length]) hr4 (d380 _ x.f) fun Y5 _ hK5 hr5 g5 =>
  x.c.s_bswap32 hK5 (by simp [avx2Movbe_length]) hr5 (d382 _ x.f) fun Y6 _ hK6 hr6 g6 =>
  x.c.s_mov8_i hK6 (by simp [avx2Movbe_length]) hr6 (d384 _ x.f) mem₁ (a := nn s₀ - 1)
    (by simp only [g6, g5, g4, g3, g2, g1, set_regOf_0, set_regOf_1, eaI, get_7, get_2, hdi, hdx, add_addr]
        exact add_mod _ (by omega))
    (show _ ≤ nn s₀ by omega) fun Y7 _ hK7 hr7 g7 =>
  x.c.s_mov8_i hK7 (by simp [avx2Movbe_length]) hr7 (d388 _ x.f) mem₂ (a := nn s₀ - 1)
    (by simp only [g7, g6, g5, g4, g3, g2, g1, set_regOf_0, set_regOf_1, eaI, get_6, get_2, hsi, hdx, add_addr]
        exact add_mod _ (by omega))
    (show _ ≤ nn s₀ by omega) fun Y8 _ hK8 hr8 g8 =>
  x.c.s_sub_rr hK8 (by simp [avx2Movbe_length]) hr8 (Or.inl rfl) (d392 _ x.f) fun Y9 _ hK9 hr9 ⟨g9, _, _⟩ => by
    have ha := v368 (R := readBytes s₀.proc.mm.mem ((p₁ s₀).add 0) 2)
      (C := readBytes s₀.proc.mm.mem ((p₁ s₀).add (nn s₀ - 1)) 1) (readBytes_length _ _ _) (readBytes_length _ _ _)
      (v1 := Y2.cpu.gpr.rax) (v2 := Y4.cpu.gpr.rax) (v3 := Y6.cpu.gpr.rax) (v4 := Y8.cpu.gpr.rax)
      (by simp only [g2, g1, set_regOf_0, set_regOf_1]) (by simp only [g4, g3, set_regOf_0, set_regOf_1, rv, get_0])
      (by simp only [g6, g5, set_regOf_0, set_regOf_1, rv, get_0])
      (by simp only [g8, g7, set_regOf_0, set_regOf_1, get_0])
    have hb := v368 (R := readBytes s₀.proc.mm.mem ((p₂ s₀).add 0) 2)
      (C := readBytes s₀.proc.mm.mem ((p₂ s₀).add (nn s₀ - 1)) 1) (readBytes_length _ _ _) (readBytes_length _ _ _)
      (v1 := Y3.cpu.gpr.rcx) (v2 := Y5.cpu.gpr.rcx) (v3 := Y7.cpu.gpr.rcx) (v4 := Y8.cpu.gpr.rcx)
      (by simp only [g3, g2, g1, set_regOf_0, set_regOf_1]) (by simp only [g5, g4, set_regOf_0, set_regOf_1, rv, get_1])
      (by simp only [g7, g6, set_regOf_0, set_regOf_1, rv, get_1])
      (by simp only [g8, set_regOf_1, get_1])
    rw [addr_add_zero] at ha hb
    have hn1 : nn s₀ - (nn s₀ - 1) = 1 := by omega
    have la := beV_lt (readBytes s₀.proc.mm.mem (p₁ s₀) 2 ++ readBytes s₀.proc.mm.mem ((p₁ s₀).add (nn s₀ - 1)) 1)
    have lb := beV_lt (readBytes s₀.proc.mm.mem (p₂ s₀) 2 ++ readBytes s₀.proc.mm.mem ((p₂ s₀).add (nn s₀ - 1)) 1)
    simp only [List.length_append, readBytes_length] at la lb
    refine x.c.ret hK9 (hC.of_gpr (by simp [g9, g8, g7, g6, g5, g4, g3, g2, g1])) (by simp [avx2Movbe_length])
      hr9 (d394 _ x.f) (post_be (j := nn s₀ - 1) (k := 2) (by omega) h2 ?_)
    simp only [g9, set_regOf_0, rv, get_0, get_1]
    rw [BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq,
      compare_sub (by rw [ha]; omega) (by rw [hb]; omega), ha, hb, hn1]

/-- The register of the path at `304`: four bytes `A` by `MOVBE`, `SHL 32`, `OR` with four bytes `D` by `MOVBE`; as a
number, `A` then `D`, big-endian. -/
theorem v304 {A D : List Byte} (hA : A.length = 4) (hD : D.length = 4) {v1 v2 d v3 : BitVec 64}
    (h1 : v1 = (ZellicX86.bswap (ofBytesLE 32 A)).setWidth 64) (h2 : v2 = v1.setWidth 64 <<< 32)
    (hd : d = (ZellicX86.bswap (ofBytesLE 32 D)).setWidth 64) (h3 : v3 = v2.setWidth 64 ||| d.setWidth 64) :
    v3.toNat = beV (A ++ D) := by
  subst h1 h2 hd h3
  simp only [BitVec.setWidth_eq]
  rw [bswap_ofBytesLE hA, bswap_ofBytesLE hD, toNat_hilo (by simp [hA]) (by simp [hD]), leV_eq_beV,
    List.reverse_append, List.reverse_reverse, List.reverse_reverse]

theorem cond4 (f : Rflags) : f.cond 4 = f.zf := rfl

/-- At `304`, 4 to 7 bytes: the first four and the last four of each string as one big-endian number of 64 bits;
equal, 0; else `SBB`, `OR 1`: -1 or 1 by the borrow. -/
theorem at304 (x : Ctx prof L s₀ ra o e) {X : State} {t : Nat} (hK : Kept s₀ X) (hC : Callee s₀ X)
    (hrip : X.cpu.rip = e.add 304) (hdi : X.cpu.gpr.rdi = (p₁ s₀).add 0) (hsi : X.cpu.gpr.rsi = (p₂ s₀).add 0)
    (hdx : X.cpu.gpr.rdx = BitVec.ofNat 64 (nn s₀)) (h4 : 4 ≤ nn s₀) (h7 : nn s₀ ≤ 7) :
    Go prof L s₀ ra o X t :=
  have hv := nn_lt s₀
  x.c.s_movbe_d hK (by simp [avx2Movbe_length]) hrip (d304 _ x.f) mem₁ (a := 0) (by simp [hdi])
    (show _ ≤ nn s₀ by omega) fun Y1 _ hK1 hr1 g1 =>
  x.c.s_movbe_d hK1 (by simp [avx2Movbe_length]) hr1 (d308 _ x.f) mem₂ (a := 0) (by simp [g1, hsi])
    (show _ ≤ nn s₀ by omega) fun Y2 _ hK2 hr2 g2 =>
  x.c.s_shl64_32 hK2 (by simp [avx2Movbe_length]) hr2 (d312 _ x.f) fun Y3 _ hK3 hr3 g3 =>
  x.c.s_shl64_32 hK3 (by simp [avx2Movbe_length]) hr3 (d316 _ x.f) fun Y4 _ hK4 hr4 g4 =>
  x.c.s_movbe_i hK4 (by simp [avx2Movbe_length]) hr4 (d320 _ x.f) mem₁ (a := nn s₀ - 4)
    (by simp only [g4, g3, g2, g1, set_regOf_0, set_regOf_1, eaI, get_7, get_2, hdi, hdx, add_addr]
        exact add_mod _ (by omega))
    (show _ ≤ nn s₀ by omega) fun Y5 _ hK5 hr5 g5 =>
  x.c.s_movbe_i hK5 (by simp [avx2Movbe_length]) hr5 (d326 _ x.f) mem₂ (a := nn s₀ - 4)
    (by simp only [g5, g4, g3, g2, g1, set_regOf_0, set_regOf_1, set_regOf_7, eaI, get_6, get_2, hsi, hdx, add_addr]
        exact add_mod _ (by omega))
    (show _ ≤ nn s₀ by omega) fun Y6 _ hK6 hr6 g6 =>
  x.c.s_or_rr hK6 (by simp [avx2Movbe_length]) hr6 (d332 _ x.f) fun Y7 _ hK7 hr7 g7 =>
  x.c.s_or_rr hK7 (by simp [avx2Movbe_length]) hr7 (d335 _ x.f) fun Y8 _ hK8 hr8 g8 =>
  x.c.s_sub_rr hK8 (by simp [avx2Movbe_length]) hr8 (Or.inr rfl) (d338 _ x.f) fun Y9 _ hK9 hr9 ⟨g9, _, f9⟩ => by
    have ha := v304 (A := readBytes s₀.proc.mm.mem ((p₁ s₀).add 0) 4)
      (D := readBytes s₀.proc.mm.mem ((p₁ s₀).add (nn s₀ - 4)) 4) (readBytes_length _ _ _) (readBytes_length _ _ _)
      (v1 := Y2.cpu.gpr.rax) (v2 := Y6.cpu.gpr.rax) (d := Y6.cpu.gpr.rdi) (v3 := Y8.cpu.gpr.rax)
      (by simp only [g2, g1, set_regOf_0, set_regOf_1])
      (by simp only [g6, g5, g4, g3, set_regOf_0, set_regOf_1, set_regOf_6, set_regOf_7, rv, get_0])
      (by simp only [g6, g5, set_regOf_6, set_regOf_7])
      (by simp only [g8, g7, set_regOf_0, set_regOf_1, rv, get_0, get_7])
    have hb := v304 (A := readBytes s₀.proc.mm.mem ((p₂ s₀).add 0) 4)
      (D := readBytes s₀.proc.mm.mem ((p₂ s₀).add (nn s₀ - 4)) 4) (readBytes_length _ _ _) (readBytes_length _ _ _)
      (v1 := Y2.cpu.gpr.rcx) (v2 := Y7.cpu.gpr.rcx) (d := Y7.cpu.gpr.rsi) (v3 := Y8.cpu.gpr.rcx)
      (by simp only [g2, set_regOf_1])
      (by simp only [g7, g6, g5, g4, g3, set_regOf_0, set_regOf_1, set_regOf_6, set_regOf_7, rv, get_1])
      (by simp only [g7, g6, set_regOf_0, set_regOf_6])
      (by simp only [g8, set_regOf_1, rv, get_1, get_6])
    rw [addr_add_zero] at ha hb
    have hn4 : nn s₀ - (nn s₀ - 4) = 4 := by omega
    have hC9 : Callee s₀ Y9 := hC.of_gpr (by simp [g9, g8, g7, g6, g5, g4, g3, g2, g1])
    refine x.c.s_jcc' hK9 (by simp [avx2Movbe_length]) hr9 (d341 _ x.f) (tgt := 352) (by decide)
      (by simp [avx2Movbe_length]) (fun hc => ?_) (fun hc => ?_)
    · rw [cond4, f9, subF_zf, decide_eq_true_iff] at hc
      have hc' : Y8.cpu.gpr.rax = Y8.cpu.gpr.rcx := by simpa using hc
      intro Y10 _ hK10 hr10 ⟨g10, _⟩
      have hz : Y10.cpu.gpr.rax.setWidth 32 = 0 := by simp [g10, g9, hc']
      refine x.c.ret hK10 (hC9.of_gpr (by simp [g10])) (by simp [avx2Movbe_length]) hr10 (d352 _ x.f)
        (post_be (j := nn s₀ - 4) (k := 4) (by omega) h4 ?_)
      rw [hn4, ← ha, ← hb, hz, hc', Nat.compare_eq_eq.2 rfl]
      decide
    · rw [cond4, f9, subF_zf, decide_eq_false_iff_not] at hc
      have hc' : Y8.cpu.gpr.rax ≠ Y8.cpu.gpr.rcx := by simpa using hc
      intro Y10 _ hK10 hr10 ⟨g10, _, c10⟩
      refine x.c.s_sbb_rr hK10 (by simp [avx2Movbe_length]) hr10 (d343 _ x.f) fun Y11 _ hK11 hr11 g11 => ?_
      refine x.c.s_or_ri hK11 (by simp [avx2Movbe_length]) hr11 (d345 _ x.f) fun Y12 _ hK12 hr12 g12 => ?_
      refine x.c.ret hK12 (hC9.of_gpr (by simp [g12, g11, g10])) (by simp [avx2Movbe_length]) hr12 (d348 _ x.f)
        (post_be (j := nn s₀ - 4) (k := 4) (by omega) h4 ?_)
      rw [hn4, ← ha, ← hb]
      rcases Nat.lt_trichotomy Y8.cpu.gpr.rax.toNat Y8.cpu.gpr.rcx.toNat with h | h | h
      · rw [Nat.compare_eq_lt.2 h]
        have hcf : Y10.cpu.rflags.cf = true := by rw [c10, f9, subF_cf]; simpa using h
        simp only [g12, g11, set_regOf_0, rv, get_0, hcf, BitVec.sub_self]
        decide
      · exact absurd (BitVec.eq_of_toNat_eq h) hc'
      · rw [Nat.compare_eq_gt.2 h]
        have hcf : Y10.cpu.rflags.cf = false := by rw [c10, f9, subF_cf]; simp; omega
        simp only [g12, g11, set_regOf_0, rv, get_0, hcf, BitVec.sub_self]
        decide

/-! ## A window of 8 bytes (`VMOVQ`) -/

theorem elem_ofBytesLE_ge {w : Nat} {bs : List Byte} {j : Nat} (hj : bs.length ≤ j) :
    elem 8 (ofBytesLE w bs) j = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h1 : (8 * j + i) / 8 = j := by omega
  simp only [getLsbD_elem, getLsbD_ofBytesLE, h1]
  simp [show ¬ j < bs.length by omega]

theorem q128 {R : List Byte} (h : R.length = 8) : ((ofBytesLE 64 R).setWidth 512).setWidth 128 = ofBytesLE 128 R := by
  rw [BitVec.setWidth_setWidth_of_le _ (by omega), setWidth_ofBytesLE (by omega)]

/-- Lane `j` of the comparison of 8 bytes of the strings at `a`, loaded by `VMOVQ`: whether they agree at `a + j`, and
the upper lanes, 0 in both, agree. -/
theorem qbit {a j : Nat} (hj : j < 16) :
    decide (elem 8 (ofBytesLE 128 (readBytes s₀.proc.mm.mem ((p₂ s₀).add a) 8)) j =
      elem 8 (ofBytesLE 128 (readBytes s₀.proc.mm.mem ((p₁ s₀).add a) 8)) j) =
      (!decide (j < 8) || decide (Ag s₀ (a + j))) := by
  have hl : ∀ q : Addr, (readBytes s₀.proc.mm.mem q 8).length = 8 := fun q => readBytes_length _ _ _
  by_cases h8 : j < 8
  · rw [elem_ofBytesLE (by rw [hl]; exact h8) (by rw [hl]; omega), elem_ofBytesLE (by rw [hl]; exact h8)
      (by rw [hl]; omega), readBytes_getElem, readBytes_getElem, addr_add_add, addr_add_add]
    simp only [h8, decide_true, Bool.not_true, Bool.false_or]
    exact decide_eq_decide.2 eq_comm
  · rw [elem_ofBytesLE_ge (by rw [hl]; omega), elem_ofBytesLE_ge (by rw [hl]; omega)]
    simp [h8]

theorem fq_true {P : Prop} [Decidable P] {j : Nat} (hj : j < 8) (h : (!decide (j < 8) || decide P) = true) : P := by
  simpa [hj] using h

theorem fq_false {P : Prop} [Decidable P] {j : Nat} (h : (!decide (j < 8) || decide P) = false) : j < 8 ∧ ¬ P := by
  by_cases hj : j < 8 <;> simp_all

/-- A window of 8 bytes at `a` (`VMOVQ` ×2, `VPCMPEQB`, `VPMOVMSKB`, `SUB 0xffff`, `JNE` to `272`): its first difference
returns, or the run goes on knowing the strings agree to `a + 8`, with `eax` 0. -/
theorem winq (x : Ctx prof L s₀ ra o e) {X : State} {t k rel a : Nat} (hK : Kept s₀ X) (hC : Callee s₀ X)
    (h0 : Dec prof.feat avx2Movbe k (FV7z.mk (.avx .vmovq) 32 [.vreg 1 128, .mem (mbd 7 0 64)] 4))
    (h1 : Dec prof.feat avx2Movbe (k + 4) (FV7z.mk (.avx .vmovq) 32 [.vreg 2 128, .mem (mbd 6 0 64)] 4))
    (h2 : Dec prof.feat avx2Movbe (k + 4 + 4)
      (FV7z.mk (.avx (.vpcmpeq 8)) 32 [.vreg 2 128, .vreg 2 128, .vreg 1 128] 4))
    (h3 : Dec prof.feat avx2Movbe (k + 4 + 4 + 4) (FV7z.mk (.avx .vpmovmskb) 32 [gr 32 0, .vreg 2 128] 4))
    (h4 : Dec prof.feat avx2Movbe (k + 4 + 4 + 4 + 4) (FV7z.mk .sub 32 [gr 32 0, .imm 32 (2 ^ 16 - 1)] 5))
    (h5 : Dec prof.feat avx2Movbe (k + 4 + 4 + 4 + 4 + 5) (FV7z.mk (.jcc 5) 64 [.rel rel] 6))
    (htgt : (k + 4 + 4 + 4 + 4 + 5 + 6 + rel) % 2 ^ 64 = 272 % 2 ^ 64) (hlen : k + 4 + 4 + 4 + 4 + 5 + 6 < 980)
    (hrip : X.cpu.rip = e.add k) (hdi : X.cpu.gpr.rdi = (p₁ s₀).add a) (hsi : X.cpu.gpr.rsi = (p₂ s₀).add a)
    (hn : a + 8 ≤ nn s₀) (hpre : ∀ i < a, Ag s₀ i)
    (k' : (∀ i < a + 8, Ag s₀ i) → Then prof L s₀ ra o e (k + 4 + 4 + 4 + 4 + 5 + 6) fun Y => Callee s₀ Y ∧
      Y.cpu.gpr.rdi = X.cpu.gpr.rdi ∧ Y.cpu.gpr.rsi = X.cpu.gpr.rsi ∧ Y.cpu.gpr.rdx = X.cpu.gpr.rdx ∧
      Y.cpu.gpr.rax.setWidth 32 = 0) :
    Go prof L s₀ ra o X t :=
  x.c.s_vmovq hK (by simp [avx2Movbe_length]; omega) hrip h0 mem₁ (a := a) (by simp [hdi]) hn
    fun Y1 _ hK1 hr1 ⟨g1, z1⟩ =>
  x.c.s_vmovq hK1 (by simp [avx2Movbe_length]; omega) hr1 h1 mem₂ (a := a) (by simp [g1, hsi]) hn
    fun Y2 _ hK2 hr2 ⟨g2, z2⟩ =>
  x.c.s_vpcmpeqb_r hK2 (by simp [avx2Movbe_length]; omega) hr2 h2 fun Y3 _ hK3 hr3 ⟨g3, z3⟩ =>
  x.c.s_vpmovmskb hK3 (by simp [avx2Movbe_length]; omega) hr3 h3 fun Y4 _ hK4 hr4 ⟨g4, z4⟩ =>
  x.c.s_sub_ri hK4 (by simp [avx2Movbe_length]; omega) hr4 (Or.inl rfl) h4 fun Y5 _ hK5 hr5 ⟨g5, z5, f5⟩ => by
    have hk : (16 : Nat) ≤ 32 := by omega
    have hm : rv Y4 32 0 = ofBits 32 fun j => decide (j < 16) && (!decide (j < 8) || decide (Ag s₀ (a + j))) := by
      rw [rv_set0 Y4 (by rw [g4, set_regOf_0]), z3, withZmm_same, movmsk_eqb (by omega), z2, withZmm_same,
        withZmm_ne _ _ (by decide), z1, withZmm_same, q128 (readBytes_length _ _ _), q128 (readBytes_length _ _ _)]
      apply ofBits_congr
      intro j _
      by_cases hj : j < 16
      · simp only [show j < 128 / 8 from hj, decide_true, Bool.true_and]; exact qbit hj
      · simp [hj, show ¬ j < 128 / 8 from hj]
    have hr5' : rv Y5 32 0 = rv Y4 32 0 - BitVec.ofNat 32 (2 ^ 16 - 1) := rv_set0 Y5 (by rw [g5, set_regOf_0])
    refine x.c.s_jcc hK5 (by simp [avx2Movbe_length]; omega) hr5 h5 htgt (by simp [avx2Movbe_length])
      (fun hc => ?_) (fun hc => ?_)
    · rw [f5, cond5, Bool.not_eq_true', decide_eq_false_iff_not, ← sub_eq_zero_iff, hm, mask_sub_eq_zero hk] at hc
      have hex : ∃ j < 16, (!decide (j < 8) || decide (Ag s₀ (a + j))) = false := by
        refine Classical.byContradiction fun hno => hc fun j hj => ?_
        cases hb : (!decide (j < 8) || decide (Ag s₀ (a + j)))
        · exact absurd ⟨j, hj, hb⟩ hno
        · rfl
      obtain ⟨p, hp, hf, ht⟩ := exists_first _ hex
      obtain ⟨hp8, hne⟩ := fq_false hf
      intro Y6 _ hK6 hr6 ⟨g6, _⟩
      have hY6 : rv Y6 32 0 = rv Y4 32 0 - BitVec.ofNat 32 (2 ^ 16 - 1) := by
        rw [← hr5']; simp only [rv, g6]
      refine diff272 x hK6 (hC.of_gpr (by simp [g6, g5, g4, g3, g2, g1])) hr6 (a := a) (p := p)
        (by simp [g6, g5, g4, g3, g2, g1, hdi]) (by simp [g6, g5, g4, g3, g2, g1, hsi]) ?_ ?_ (by omega) (by omega)
        ?_ (by simpa using hne)
      · rw [hY6, hm, Ne, sub_eq_zero_iff, ← sub_eq_zero_iff, mask_sub_eq_zero hk]
        intro h; have := h p hp; rw [hf] at this; exact Bool.false_ne_true this
      · rw [hY6, hm]; exact mask_sub_lowest hk _ hp hf ht
      · intro i hi
        by_cases hia : i < a
        · exact hpre i hia
        · have := fq_true (by omega) (ht (i - a) (by omega))
          rwa [show a + (i - a) = i by omega] at this
    · rw [f5, cond5, Bool.not_eq_false', decide_eq_true_iff, ← sub_eq_zero_iff] at hc
      have hz : rv Y5 32 0 = 0 := hr5' ▸ hc
      rw [hm, mask_sub_eq_zero hk] at hc
      have hall : ∀ i < a + 8, Ag s₀ i := fun i hi => by
        by_cases hia : i < a
        · exact hpre i hia
        · have := fq_true (by omega) (hc (i - a) (by omega))
          rwa [show a + (i - a) = i by omega] at this
      intro Y6 t6 hK6 hr6 ⟨g6, _⟩
      refine k' hall Y6 t6 hK6 hr6 ⟨hC.of_gpr (by simp [g6, g5, g4, g3, g2, g1]), by simp [g6, g5, g4, g3, g2, g1],
        by simp [g6, g5, g4, g3, g2, g1], by simp [g6, g5, g4, g3, g2, g1], ?_⟩
      simpa [rv, g6] using hz

/-- At `458`, 8 to 15 bytes: the window of 8 at 0, `LEA` both pointers to the last 8, the window there, `RET` 0. -/
theorem at458 (x : Ctx prof L s₀ ra o e) {X : State} {t : Nat} (hK : Kept s₀ X) (hC : Callee s₀ X)
    (hrip : X.cpu.rip = e.add 458) (hdi : X.cpu.gpr.rdi = (p₁ s₀).add 0) (hsi : X.cpu.gpr.rsi = (p₂ s₀).add 0)
    (hdx : X.cpu.gpr.rdx = BitVec.ofNat 64 (nn s₀)) (h8 : 8 ≤ nn s₀) (h16 : nn s₀ ≤ 16) :
    Go prof L s₀ ra o X t :=
  winq x hK hC (a := 0) (d458 _ x.f) (d462 _ x.f) (d466 _ x.f) (d470 _ x.f) (d474 _ x.f) (d479 _ x.f) (by decide)
    (by decide) hrip hdi hsi (by omega) (fun i hi => absurd hi (by omega))
    fun hall1 Y1 _ hK1 hr1 ⟨hC1, hdi1, hsi1, hdx1, _⟩ =>
  x.c.s_lea hK1 (by simp [avx2Movbe_length]) hr1 (d485 _ x.f) fun Y2 _ hK2 hr2 ⟨g2, _⟩ =>
  x.c.s_lea hK2 (by simp [avx2Movbe_length]) hr2 (d490 _ x.f) fun Y3 _ hK3 hr3 ⟨g3, _⟩ =>
  winq x hK3 (hC1.of_gpr (by simp [g3, g2])) (a := nn s₀ - 8) (d495 _ x.f) (d499 _ x.f) (d503 _ x.f)
    (d507 _ x.f) (d511 _ x.f) (d516 _ x.f) (by decide) (by decide) hr3
    (by simp only [g3, g2, set_regOf_6, set_regOf_7, eaI, get_7, get_2, hdi1, hdx1, hdi, hdx, add_addr]
        exact add_mod _ (by have := nn_lt s₀; omega))
    (by simp only [g3, g2, set_regOf_6, set_regOf_7, eaI, get_6, get_2, hsi1, hdx1, hsi, hdx, add_addr]
        exact add_mod _ (by have := nn_lt s₀; omega))
    (by omega) (fun i hi => hall1 i (by omega))
    fun hall Y4 _ hK4 hr4 ⟨hC4, _, _, _, hz4⟩ =>
  x.c.ret hK4 hC4 (by simp [avx2Movbe_length]) hr4 (d522 _ x.f) (post_eq hz4 fun i hi => hall i (by omega))

/-! ## The dispatch at `432` -/

theorem cfw (f : Rflags) {w v imm : Nat} (hv : v < 2 ^ w) (hi : imm < 2 ^ w) :
    (subF f (BitVec.ofNat w v) (BitVec.ofNat w imm)).cf = decide (v < imm) := by
  rw [subF_cf]; simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hi]

theorem zfw (f : Rflags) {w v imm : Nat} (hv : v < 2 ^ w) (hi : imm < 2 ^ w) :
    (subF f (BitVec.ofNat w v) (BitVec.ofNat w imm)).zf = decide (v = imm) := by
  rw [subF_zf]
  exact decide_eq_decide.2 ⟨fun h => by
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hi] at this
    exact this, fun h => h ▸ rfl⟩

theorem cond2s (f : Rflags) : f.cond 2 = f.cf := rfl
theorem cond3s (f : Rflags) : f.cond 3 = !f.cf := rfl

/-- At `432`, fewer than 32 bytes: `CMP dl` with 1, 4, 8, 16 and the jumps to the paths by `n`. -/
theorem at432 (x : Ctx prof L s₀ ra o e) {X : State} {t : Nat} (hK : Kept s₀ X) (hC : Callee s₀ X)
    (hrip : X.cpu.rip = e.add 432) (hdi : X.cpu.gpr.rdi = (p₁ s₀).add 0) (hsi : X.cpu.gpr.rsi = (p₂ s₀).add 0)
    (hdx : X.cpu.gpr.rdx = BitVec.ofNat 64 (nn s₀)) (hn : nn s₀ < 32) : Go prof L s₀ ra o X t :=
  have hdl : ∀ Y : State, Y.cpu.gpr = X.cpu.gpr → rv Y 8 2 = BitVec.ofNat 8 (nn s₀) := fun Y h => by
    simp only [rv, get_2, h, hdx]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  have h8 : nn s₀ < 2 ^ 8 := Nat.lt_of_lt_of_le hn (by decide)
  x.c.s_cmp_ri hK (by simp [avx2Movbe_length]) hrip (d432 _ x.f) fun Y1 _ hK1 hr1 ⟨g1, _, f1⟩ => by
    rw [hdl X rfl] at f1
    refine x.c.s_jcc' hK1 (by simp [avx2Movbe_length]) hr1 (d435 _ x.f) (tgt := 400) (by decide) (by simp [avx2Movbe_length]) (fun hc => ?_) (fun hc => ?_)
    · rw [cond4, f1, zfw _ h8 (by decide), decide_eq_true_iff] at hc
      intro Y2 _ hK2 hr2 ⟨g2, _⟩
      have gY : Y2.cpu.gpr = X.cpu.gpr := by rw [g2, g1]
      exact at400 x hK2 (hC.of_gpr (by simp [gY])) hr2 (by rw [gY, hdi]) (by rw [gY, hsi]) hc
    · rw [cond4, f1, zfw _ h8 (by decide), decide_eq_false_iff_not] at hc
      intro Y2 _ hK2 hr2 ⟨g2, _, c2⟩
      have gY2 : Y2.cpu.gpr = X.cpu.gpr := by rw [g2, g1]
      refine x.c.s_jcc hK2 (by simp [avx2Movbe_length]) hr2 (d437 _ x.f) (tgt := 416) (by decide) (by simp [avx2Movbe_length]) (fun hc' => ?_) (fun hc' => ?_)
      · rw [cond2s, c2, f1, cfw _ h8 (by decide), decide_eq_true_iff] at hc'
        intro Y3 _ hK3 hr3 ⟨g3, _⟩
        exact at416 x hK3 (hC.of_gpr (by simp [g3, gY2])) hr3 (by omega)
      · rw [cond2s, c2, f1, cfw _ h8 (by decide), decide_eq_false_iff_not] at hc'
        intro Y3 _ hK3 hr3 ⟨g3, _⟩
        have gY3 : Y3.cpu.gpr = X.cpu.gpr := by rw [g3, gY2]
        refine x.c.s_cmp_ri hK3 (by simp [avx2Movbe_length]) hr3 (d439 _ x.f) fun Y4 _ hK4 hr4 ⟨g4, _, f4⟩ => ?_
        rw [hdl Y3 gY3] at f4
        have gY4 : Y4.cpu.gpr = X.cpu.gpr := by rw [g4, gY3]
        refine x.c.s_jcc hK4 (by simp [avx2Movbe_length]) hr4 (d442 _ x.f) (tgt := 368) (by decide) (by simp [avx2Movbe_length]) (fun h4 => ?_) (fun h4 => ?_)
        · rw [cond2s, f4, cfw _ h8 (by decide), decide_eq_true_iff] at h4
          intro Y5 _ hK5 hr5 ⟨g5, _⟩
          have gY : Y5.cpu.gpr = X.cpu.gpr := by rw [g5, gY4]
          exact at368 x hK5 (hC.of_gpr (by simp [gY])) hr5 (by rw [gY, hdi]) (by rw [gY, hsi]) (by rw [gY, hdx])
            (by omega) (by omega)
        · rw [cond2s, f4, cfw _ h8 (by decide), decide_eq_false_iff_not] at h4
          intro Y5 _ hK5 hr5 ⟨g5, _⟩
          have gY5 : Y5.cpu.gpr = X.cpu.gpr := by rw [g5, gY4]
          refine x.c.s_cmp_ri hK5 (by simp [avx2Movbe_length]) hr5 (d444 _ x.f) fun Y6 _ hK6 hr6 ⟨g6, _, f6⟩ => ?_
          rw [hdl Y5 gY5] at f6
          have gY6 : Y6.cpu.gpr = X.cpu.gpr := by rw [g6, gY5]
          refine x.c.s_jcc hK6 (by simp [avx2Movbe_length]) hr6 (d447 _ x.f) (tgt := 304) (by decide) (by simp [avx2Movbe_length]) (fun h6 => ?_) (fun h6 => ?_)
          · rw [cond2s, f6, cfw _ h8 (by decide), decide_eq_true_iff] at h6
            intro Y7 _ hK7 hr7 ⟨g7, _⟩
            have gY : Y7.cpu.gpr = X.cpu.gpr := by rw [g7, gY6]
            exact at304 x hK7 (hC.of_gpr (by simp [gY])) hr7 (by rw [gY, hdi]) (by rw [gY, hsi]) (by rw [gY, hdx])
              (by omega) (by omega)
          · rw [cond2s, f6, cfw _ h8 (by decide), decide_eq_false_iff_not] at h6
            intro Y7 _ hK7 hr7 ⟨g7, _⟩
            have gY7 : Y7.cpu.gpr = X.cpu.gpr := by rw [g7, gY6]
            refine x.c.s_cmp_ri hK7 (by simp [avx2Movbe_length]) hr7 (d453 _ x.f) fun Y8 _ hK8 hr8 ⟨g8, _, f8⟩ => ?_
            rw [hdl Y7 gY7] at f8
            have gY8 : Y8.cpu.gpr = X.cpu.gpr := by rw [g8, gY7]
            refine x.c.s_jcc hK8 (by simp [avx2Movbe_length]) hr8 (d456 _ x.f) (tgt := 528) (by decide) (by simp [avx2Movbe_length]) (fun h9 => ?_) (fun h9 => ?_)
            · rw [cond3s, f8, cfw _ h8 (by decide), Bool.not_eq_true', decide_eq_false_iff_not] at h9
              intro Y9 _ hK9 hr9 ⟨g9, _⟩
              have gY : Y9.cpu.gpr = X.cpu.gpr := by rw [g9, gY8]
              exact at528 x hK9 (hC.of_gpr (by simp [gY])) hr9 (by rw [gY, hdi]) (by rw [gY, hsi]) (by rw [gY, hdx])
                (by omega) (by omega)
            · rw [cond3s, f8, cfw _ h8 (by decide), Bool.not_eq_false', decide_eq_true_iff] at h9
              intro Y9 _ hK9 hr9 ⟨g9, _⟩
              have gY : Y9.cpu.gpr = X.cpu.gpr := by rw [g9, gY8]
              exact at458 x hK9 (hC.of_gpr (by simp [gY])) hr9 (by rw [gY, hdi]) (by rw [gY, hsi]) (by rw [gY, hdx])
                (by omega) (by omega)

end FV7z.MemcmpAvx2
