import FV7z.Lap.Cuts
import FV7z.Lfp.Holds
import FV7z.Lemmas.CallM
import FV7z.Tun.Inv
/-!
# `LzmaDec_AllocateProbs2` (PLAN.md §M, M1)

7-Zip 26.06's `LzmaDec_AllocateProbs2 (p, propNew, alloc)` at `0x42be00` in `7zzs` (`C/LzmaDec.c`), with `lc` in
`esi`, `lp` in `edx` and `alloc` in `rcx`: `numProbs` = `0x7c0 + (0x300 << (lc + lp))` (`np`); if `p->probs` (the 8
bytes at `p + 8`) is not NULL and `numProbs` is `p->numProbs` (the 4 bytes at `p + 96`), `eax` = 0 and back (87);
else `LzmaDec_FreeProbs (p, alloc)` (46, `Lfp.lfp_ok`), `p->probs = alloc->Alloc (alloc, numProbs * 2)` (59,
`Seg.s_callM` through the 8 bytes at `alloc`), `eax` = 2 (`SZ_ERROR_MEM`) if NULL, else `p->numProbs` =
`numProbs`, `p->probs_1664` (the 8 bytes at `p + 16`) = `probs + 0xd00`, `eax` = 0. `push r12; push rbp; push rbx`
(`r12` = `alloc`, `rbp` = `numProbs`, `rbx` = `p`); with `s` the entry's `rsp`, the saved registers at `s - 8`,
`s - 16`, `s - 24`, the return address into `LzmaDec_AllocateProbs2` at `s - 32` (both calls),
`LzmaDec_FreeProbs`'s `rbx` and return address at `s - 40` and `s - 48`.

The callees are hypotheses, as in `Lfp.lfp_ok`: `kf1` for `alloc->Free` from `LzmaDec_FreeProbs` (its post `Pc1`,
with `hP1`: `rbp`, `r12` kept and the target of the second call), `kf2` for `alloc->Alloc` (its post `Pc2`), and
the three ways back: `kr0` (the same `probs` kept), `krN` (NULL), `krA` (allocated).

- `vc_0`, `vc_40`, `vc_51`, `vc_63`, `vc_87`: the verification conditions of the pieces.
- `tail_87`: from 87 to the return address, `rbx`, `rbp`, `r12` popped.
- `lap_ok`: from the entry to the return address on each of the three ways.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Lap

/-- The call of `LzmaDec_FreeProbs`. -/
def pcl : List Byte := [0xe8, 0xad, 0xff, 0xff, 0xff]
theorem pcl_0 : ∀ feat, Dec feat pcl 0 (FV7z.mk .call 64 [.rel 18446744073709551533] 5) := by dec_rfl
theorem wl_46 : pcl <+: lap.drop 46 := by decide +kernel
theorem call_46 (feat : Features) : Dec feat lap 46 (FV7z.mk .call 64 [.rel 18446744073709551533] 5) :=
  Dec.shift (j := 46) (k := 0) (pcl_0 feat) wl_46 (Nat.zero_le _)

/-- The call through `alloc->Alloc`. -/
def pcall : List Byte := [0x41, 0xff, 0x14, 0x24]
theorem pcall_0 : ∀ feat, Dec feat pcall 0 (FV7z.mk .call 64 [.mem (mbd 12 0 64)] 4) := by dec_rfl
theorem wc_59 : pcall <+: lap.drop 59 := by decide +kernel
theorem call_59 (feat : Features) : Dec feat lap 59 (FV7z.mk .call 64 [.mem (mbd 12 0 64)] 4) :=
  Dec.shift (j := 59) (k := 0) (pcall_0 feat) wc_59 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_91 : pret <+: lap.drop 91 := by decide +kernel
theorem ret_91 (feat : Features) : Dec feat lap 91 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 91) (k := 0) (pret_0 feat) w_91 (Nat.zero_le _)

/-! ## Offsets from the entry's `rsp` -/

theorem m8_8 (x : BitVec 64) : x - 8 - 8 = x - 16 := by bv_omega
theorem m16_8 (x : BitVec 64) : x - 16 - 8 = x - 24 := by bv_omega
theorem m24_8 (x : BitVec 64) : x - 24 - 8 = x - 32 := by bv_omega
theorem m32_8 (x : BitVec 64) : x - 32 - 8 = x - 40 := by bv_omega
theorem m32_16 (x : BitVec 64) : x - 32 - 16 = x - 48 := by bv_omega
theorem p32_8 (x : BitVec 64) : x - 32 + 8 = x - 24 := by bv_omega
theorem p24_8 (x : BitVec 64) : x - 24 + 8 = x - 16 := by bv_omega
theorem p16_8 (x : BitVec 64) : x - 16 + 8 = x - 8 := by bv_omega
theorem p8_8 (x : BitVec 64) : x - 8 + 8 = x := by bv_omega
theorem ad0 (x : BitVec 64) : x + 0#64 = x := by bv_omega

/-! ## Loads past stores -/

/-- The 4 bytes at `a`, little-endian. -/
abbrev rd4 (V : Addr → Byte) (a : Addr) : BitVec 32 := ofBytesLE 32 (List.map V (byteAddrs a 4))

theorem rd8 (W : Addr → Byte) (a x : Addr) (bs : List Byte) (m : Nat) (hb : bs.length = m)
    (ha : a.toNat + m ≤ 2 ^ 64) (hx : x.toNat + 8 ≤ 2 ^ 64) (h : a.toNat + m ≤ x.toNat ∨ x.toNat + 8 ≤ a.toNat) :
    rdq(Vst W a bs, x) = rdq(W, x) := by
  rw [Tun.rd_Vst W a bs x 8 (by rw [hb]; exact ha) hx (by rw [hb]; exact h)]

theorem rd4s (W : Addr → Byte) (a x : Addr) (bs : List Byte) (m : Nat) (hb : bs.length = m)
    (ha : a.toNat + m ≤ 2 ^ 64) (hx : x.toNat + 4 ≤ 2 ^ 64) (h : a.toNat + m ≤ x.toNat ∨ x.toNat + 4 ≤ a.toNat) :
    rd4 (Vst W a bs) x = rd4 W x := by
  simp only [rd4]
  rw [Tun.rd_Vst W a bs x 4 (by rw [hb]; exact ha) hx (by rw [hb]; exact h)]

theorem rs8 (W : Addr → Byte) (a : Addr) (v : BitVec 64) (ha : a.toNat + 8 ≤ 2 ^ 64) :
    rdq(Vst W a (toBytesLE v 8), a) = v := by
  rw [Tun.rd_Vst_self W a _ (toBytesLE_length _ _) ha]
  exact ofBytesLE_toBytesLE (n := 8) rfl _

/-! ## The pieces -/

/-- `ecx` = `lc + lp`. -/
def cx (g : Gprs) : BitVec 64 := ((g.rdx + g.rsi).setWidth 32).setWidth 64
/-- `numProbs` = `0x7c0 + (0x300 << (lc + lp))`, the shift count taken from `cl` modulo 32. -/
def np (g : Gprs) : BitVec 32 :=
  BitVec.ofNat 32 768 <<< ((((g.rdx + g.rsi).setWidth 32).setWidth 8).toNat % 32) + BitVec.ofNat 32 1984

/-- The registers at 31: `r12` = `alloc`, `rbp` = `numProbs`, `rbx` = `p`, `rsp` 24 below. -/
abbrev g24 (g : Gprs) : Gprs :=
  { g with rcx := cx g, rbx := g.rdi, rsp := g.rsp - 24, rbp := (np g).setWidth 64, r12 := g.rcx }
/-- The bytes at 31: `r12`, `rbp` and `rbx` pushed. -/
abbrev V24 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 16) (toBytesLE g.rbp 8)) (g.rsp - 24) (toBytesLE g.rbx 8)
/-- The size asked of `alloc->Alloc`: `numProbs * 2`. -/
abbrev sz (g : Gprs) : BitVec 64 := (np g).setWidth 64 + (np g).setWidth 64
/-- The bytes at `alloc->Free`'s entry from `LzmaDec_FreeProbs`. -/
abbrev M1 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (V24 V g) (g.rsp - 32) (toBytesLE (lap_at.add 51) 8)) (g.rsp - 40) (toBytesLE g.rdi 8))
    (g.rsp - 48) (toBytesLE (Lfp.lfp_at.add 21) 8)
/-- The registers at `alloc->Free`'s entry from `LzmaDec_FreeProbs`. -/
abbrev G1 (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with
    rax := g.rcx, rcx := cx g, rbx := g.rdi, rsp := g.rsp - 48, rbp := (np g).setWidth 64,
    rsi := rdq(V, g.rdi + 8#64), rdi := g.rcx, r12 := g.rcx }

variable {F : Footprint} {Wl : List Rgn}

/-- From the entry to 40 or 87: the pushes, `numProbs`, and the two tests of `p->probs` and `p->numProbs`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs8 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs16 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 16) i))
    (hs24 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 24) i))
    (hl8 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 8#64) i))
    (hl96 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 96#64) i))
    (hx8 : rdq(Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 16) (toBytesLE g.rbp 8)) (g.rsp - 24)
      (toBytesLE g.rbx 8), g.rdi + 8#64) = rdq(V, g.rdi + 8#64))
    (hx96 : ofBytesLE 32 (List.map (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 16)
      (toBytesLE g.rbp 8)) (g.rsp - 24) (toBytesLE g.rbx 8)) (byteAddrs (g.rdi + 96#64) 4)) = rd4 V (g.rdi + 96#64))
    (h40 : ∀ a fl, Q 40 { g24 g with rax := a } fl (V24 V g))
    (h87 : ∀ fl, rdq(V, g.rdi + 8#64) ≠ 0#64 → np g = rd4 V (g.rdi + 96#64) →
      Q 87 { g24 g with rax := 0#64 } fl (V24 V g)) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs8 hs16 hs24 hl8 hl96 hx8 hx96 h40 h87 ⊢
  revert h40 h87
  wpx [W_0, W_33, o0, o1, Op.cmpmi, g24, V24, rd4, cx, np, hx8, hx96, m8_8, m16_8, BitVec.xor_self,
    BitVec.reduceSetWidth, decide_eq_true_eq, decide_eq_false_iff_not]
  intro h40 h87
  repeat' (first | exact hs8 | exact hs16 | exact hs24 | exact hl8 | exact hl96 | apply And.intro | intro _)
  all_goals first | exact h40 _ _ | exact h87 _ ‹_› ‹_›

/-- `mov rsi, r12; mov rdi, rbx`. -/
theorem vc_40 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 46 { g with rsi := g.r12, rdi := g.rbx } fl V) : W_40 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_40, o2]
  repeat' (first | apply And.intro | intro _)
  all_goals exact h _

/-- `mov esi, ebp; mov rdi, r12; add rsi, rsi`. -/
theorem vc_51 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 59
      { g with
        rsi := (g.rbp.setWidth 32).setWidth 64 + (g.rbp.setWidth 32).setWidth 64,
        rdi := g.r12 } fl V) : W_51 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_51, o3]
  repeat' (first | apply And.intro | intro _)
  all_goals exact h _

/-- From 63 to 87: `p->probs` = `rax`; NULL: `eax` = 2; else `p->numProbs` = `ebp`, `p->probs_1664` =
`rax + 0xd00`, `eax` = 0. -/
theorem vc_63 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fw8 : ∀ i < 8, Foot Wl (Addr.add (g.rbx + 8#64) i)) (fw96 : ∀ i < 4, Foot Wl (Addr.add (g.rbx + 96#64) i))
    (fw16 : ∀ i < 8, Foot Wl (Addr.add (g.rbx + 16#64) i))
    (hN : ∀ fl, g.rax = 0#64 → Q 87 { g with rax := 2#64 } fl (Vst V (g.rbx + 8#64) (toBytesLE g.rax 8)))
    (hA : ∀ fl, g.rax ≠ 0#64 → Q 87 { g with rax := 0#64 } fl
      (Vst (Vst (Vst V (g.rbx + 8#64) (toBytesLE g.rax 8)) (g.rbx + 96#64) (toBytesLE (g.rbp.setWidth 32) 4))
        (g.rbx + 16#64) (toBytesLE (g.rax + 3328#64) 8))) :
    W_63 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fw8 fw96 fw16 hN hA ⊢
  revert hN hA
  wpx [W_63, W_96, W_72, o4, o5, o7, BitVec.and_self, BitVec.xor_self, BitVec.reduceSetWidth, beq_iff_eq,
    beq_eq_false_iff_ne]
  intro hN hA
  repeat' (first | exact fw8 | exact fw96 | exact fw16 | apply And.intro | intro _)
  all_goals first | exact hN _ ‹_› | exact hA _ ‹_›

/-- `pop rbx; pop rbp; pop r12`. -/
theorem vc_87 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hl0 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (hl1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i))
    (hl2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i))
    (h : ∀ fl, Q 91
      { g with
        rbx := rdq(V, g.rsp), rbp := rdq(V, g.rsp + 8), r12 := rdq(V, g.rsp + 8 + 8),
        rsp := g.rsp + 8 + 8 + 8 } fl V) :
    W_87 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl0 hl1 hl2 h ⊢
  wpx [W_87, o6]
  repeat' (first | exact hl0 | exact hl1 | exact hl2 | apply And.intro | intro _)
  all_goals first | exact h _ | (simp only [BitVec.setWidth_eq]; exact h _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- From 87, `rsp` = `s - 24` and the saved registers `b`, `r`, `q` at `s - 24`, `s - 16`, `s - 8`, to the return
address at `s`. -/
theorem tail_87 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L lap_at lap) {Z : State} {V₃ : Addr → Byte}
    (hK : KeptW Wl s₀ Z) (hA : Agree F Z.proc.mm.mem V₃) (hr : Z.cpu.rip = lap_at.add 87) {s : Addr}
    (hs : Z.cpu.gpr.rsp = s - 24)
    (hl0 : ∀ i < 8, Foot F.data (Addr.add (s - 24) i)) (hl1 : ∀ i < 8, Foot F.data (Addr.add (s - 16) i))
    (hl2 : ∀ i < 8, Foot F.data (Addr.add (s - 8) i)) (hl3 : ∀ i < 8, Foot F.data (Addr.add s i))
    {b r q : BitVec 64} (h24 : rdq(V₃, s - 24) = b) (h16 : rdq(V₃, s - 16) = r) (h8 : rdq(V₃, s - 8) = q)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hret : rdq(V₃, s) = e₂.add j₂)
    (k : ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem V₃ → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with rbx := b, rbp := r, r12 := q, rsp := s + 8 } → GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE Z t := by
  refine (c_87 prof).run c hin (fun j' g' _ V' => j' = 91 ∧
      g' = { Z.cpu.gpr with rbx := b, rbp := r, r12 := q, rsp := s } ∧ V' = V₃) hK hA hr
    (vc_87 (by rw [hs]; exact hl0) (by rw [hs, p24_8]; exact hl1) (by rw [hs, p24_8, p16_8]; exact hl2)
      fun _ => ⟨rfl, by simp only [hs, p24_8, p16_8, p8_8, h24, h16, h8], rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ W t₁ hKW hAW hrW hgW -
  have hsW : W.cpu.gpr.rsp = s := by rw [hgW]
  refine c.s_ret hKW hAW hin (lt_len (by decide)) hrW (ret_91 _) (by rw [hsW]; exact hl3) hin₂ h₂
    (by rw [hsW]; exact hret) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine k Z' t₂ hKZ' hAZ' hrZ' ?_
  rw [hgZ', hgW]
  try rfl

/-- `LzmaDec_AllocateProbs2 (p, propNew, alloc)` (`p` = `rdi`, `lc` = `esi`, `lp` = `edx`, `alloc` = `rcx`) from
its entry, `s` its `rsp`. The same `probs` kept: `kr0`. Else at `alloc->Free`'s entry from `LzmaDec_FreeProbs` the
registers are `G1` and the bytes `M1` (`kf1`); its return (`Pc1`, with `hP1`) leads to `alloc->Alloc (alloc,
numProbs * 2)`, whose entry has `rbx` = `p`, `rsp` = `s - 32`, the return address `lap_at + 63` at `s - 32` (`kf2`);
from its return (`Pc2`) the run reaches the return address with `p->probs` = `rax`, and `eax` = 2 if `rax` is NULL
(`krN`), else `p->numProbs` = `numProbs`, `p->probs_1664` = `rax + 0xd00` and `eax` = 0 (`krA`); `rbx`, `rbp`,
`r12` restored. -/
theorem lap_ok {Pc1 Pc2 : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o)
    (hin : CodeIn L lap_at lap) (hinL : CodeIn L Lfp.lfp_at Lfp.lfp)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = lap_at)
    (hp : 48 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs8 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs16 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs24 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 24) i))
    (hs32 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hs40 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 40) i))
    (hs48 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 48) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fw8 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (fw16 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 16#64) i))
    (fw96 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 96#64) i))
    (hpn : X.cpu.gpr.rdi.toNat + 104 ≤ 2 ^ 64)
    (hps : X.cpu.gpr.rdi.toNat + 104 ≤ X.cpu.gpr.rsp.toNat - 48 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    (fa : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rcx i))
    (fb : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rcx + 8#64) i))
    (han : X.cpu.gpr.rcx.toNat + 16 ≤ 2 ^ 64)
    (has : X.cpu.gpr.rcx.toNat + 16 ≤ X.cpu.gpr.rsp.toNat - 48 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rcx.toNat)
    (hpa : X.cpu.gpr.rdi.toNat + 104 ≤ X.cpu.gpr.rcx.toNat ∨ X.cpu.gpr.rcx.toNat + 16 ≤ X.cpu.gpr.rdi.toNat + 8)
    {eF : Addr} {codeF : List Byte} (hinF : CodeIn L eF codeF) (hF0 : 0 < codeF.length)
    (htgt : rdq(V, X.cpu.gpr.rcx + 8#64) = eF)
    {eA : Addr} {codeA : List Byte} (hinA : CodeIn L eA codeA) (hA0 : 0 < codeA.length)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (kr0 : ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem (V24 V X.cpu.gpr) →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { X.cpu.gpr with rax := 0#64, rcx := cx X.cpu.gpr, rsp := X.cpu.gpr.rsp + 8 } →
      rdq(V, X.cpu.gpr.rdi + 8#64) ≠ 0#64 → np X.cpu.gpr = rd4 V (X.cpu.gpr.rdi + 96#64) →
      GoG prof L o gev gP gE Z' t')
    (kf1 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (M1 V X.cpu.gpr) →
      Y.cpu.rip = eF → Y.cpu.gpr = G1 V X.cpu.gpr →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = Lfp.lfp_at.add 21 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
        rdq(V', X.cpu.gpr.rsp - 40) = X.cpu.gpr.rdi → rdq(V', X.cpu.gpr.rsp - 32) = lap_at.add 51 → Pc1 Z V' →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (hP1 : ∀ (Z : State) (V' : Addr → Byte), Pc1 Z V' → Z.cpu.gpr.rbp = (np X.cpu.gpr).setWidth 64 ∧
      Z.cpu.gpr.r12 = X.cpu.gpr.rcx ∧ rdq(V', X.cpu.gpr.rcx) = eA)
    (kf2 : ∀ (Zc : State) (V' : Addr → Byte), Pc1 Zc V' → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (Vst V' (X.cpu.gpr.rdi + 8#64) (toBytesLE 0#64 8)) (X.cpu.gpr.rsp - 32)
        (toBytesLE (lap_at.add 63) 8)) →
      Y.cpu.rip = eA →
      Y.cpu.gpr = { Zc.cpu.gpr with
        rbx := X.cpu.gpr.rdi, rsp := X.cpu.gpr.rsp - 32, rsi := sz X.cpu.gpr, rdi := X.cpu.gpr.rcx } →
      (∀ (Z : State) (V'' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V'' →
        Z.cpu.rip = lap_at.add 63 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
        Z.cpu.gpr.rbp = (np X.cpu.gpr).setWidth 64 →
        rdq(V'', X.cpu.gpr.rsp - 24) = X.cpu.gpr.rbx → rdq(V'', X.cpu.gpr.rsp - 16) = X.cpu.gpr.rbp →
        rdq(V'', X.cpu.gpr.rsp - 8) = X.cpu.gpr.r12 → rdq(V'', X.cpu.gpr.rsp) = e₂.add j₂ → Pc2 Z V'' →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (krN : ∀ (Z : State) (V'' : Addr → Byte) (Z' : State) (t' : Nat), Pc2 Z V'' → Z.cpu.gpr.rax = 0#64 →
      KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem (Vst V'' (X.cpu.gpr.rdi + 8#64) (toBytesLE Z.cpu.gpr.rax 8)) →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with
        rax := 2#64, rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, r12 := X.cpu.gpr.r12, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t')
    (krA : ∀ (Z : State) (V'' : Addr → Byte) (Z' : State) (t' : Nat), Pc2 Z V'' → Z.cpu.gpr.rax ≠ 0#64 →
      KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (Vst (Vst (Vst V'' (X.cpu.gpr.rdi + 8#64) (toBytesLE Z.cpu.gpr.rax 8))
        (X.cpu.gpr.rdi + 96#64) (toBytesLE (np X.cpu.gpr) 4)) (X.cpu.gpr.rdi + 16#64)
        (toBytesLE (Z.cpu.gpr.rax + 3328#64) 8)) →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z.cpu.gpr with
        rax := 0#64, rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, r12 := X.cpu.gpr.r12, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have t8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have t16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := by rw [BitVec.toNat_sub]; simp <;> omega
  have t24 : (X.cpu.gpr.rsp - 24).toNat = X.cpu.gpr.rsp.toNat - 24 := by rw [BitVec.toNat_sub]; simp <;> omega
  have t32 : (X.cpu.gpr.rsp - 32).toNat = X.cpu.gpr.rsp.toNat - 32 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tp8 : (X.cpu.gpr.rdi + 8#64).toNat = X.cpu.gpr.rdi.toNat + 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have tp16 : (X.cpu.gpr.rdi + 16#64).toNat = X.cpu.gpr.rdi.toNat + 16 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have tp96 : (X.cpu.gpr.rdi + 96#64).toNat = X.cpu.gpr.rdi.toNat + 96 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have ta8 : (X.cpu.gpr.rcx + 8#64).toNat = X.cpu.gpr.rcx.toNat + 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs8 i hi)
  have h16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 16) i) := fun i hi => c.hws _ (hs16 i hi)
  have h24 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 24) i) := fun i hi => c.hws _ (hs24 i hi)
  have h32 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 32) i) := fun i hi => c.hws _ (hs32 i hi)
  -- the reads of `p->probs` and `p->numProbs` past the pushes
  have hx8 : rdq(V24 V X.cpu.gpr, X.cpu.gpr.rdi + 8#64) = rdq(V, X.cpu.gpr.rdi + 8#64) := by
    simp only [V24]
    rw [rd8 _ (X.cpu.gpr.rsp - 24) (X.cpu.gpr.rdi + 8#64) _ 8 (toBytesLE_length _ _) (by omega) (by omega)
        (by omega),
      rd8 _ (X.cpu.gpr.rsp - 16) (X.cpu.gpr.rdi + 8#64) _ 8 (toBytesLE_length _ _) (by omega) (by omega)
        (by omega),
      rd8 _ (X.cpu.gpr.rsp - 8) (X.cpu.gpr.rdi + 8#64) _ 8 (toBytesLE_length _ _) (by omega) (by omega) (by omega)]
  have hx96 : rd4 (V24 V X.cpu.gpr) (X.cpu.gpr.rdi + 96#64) = rd4 V (X.cpu.gpr.rdi + 96#64) := by
    simp only [V24]
    rw [rd4s _ (X.cpu.gpr.rsp - 24) (X.cpu.gpr.rdi + 96#64) _ 8 (toBytesLE_length _ _) (by omega) (by omega)
        (by omega),
      rd4s _ (X.cpu.gpr.rsp - 16) (X.cpu.gpr.rdi + 96#64) _ 8 (toBytesLE_length _ _) (by omega) (by omega)
        (by omega),
      rd4s _ (X.cpu.gpr.rsp - 8) (X.cpu.gpr.rdi + 96#64) _ 8 (toBytesLE_length _ _) (by omega) (by omega)
        (by omega)]
  -- to 40 or 87
  refine (c_0 prof).run c hin (fun j' g' _ V' => V' = V24 V X.cpu.gpr ∧
      ((j' = 40 ∧ ∃ a, g' = { g24 X.cpu.gpr with rax := a }) ∨
       (j' = 87 ∧ g' = { g24 X.cpu.gpr with rax := 0#64 } ∧ rdq(V, X.cpu.gpr.rdi + 8#64) ≠ 0#64 ∧
         np X.cpu.gpr = rd4 V (X.cpu.gpr.rdi + 96#64)))) hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 hs8 hs16 hs24 (fun i hi => c.hws _ (fw8 i hi)) (fun i hi => c.hws _ (fw96 i hi)) hx8 hx96
      (fun a _ => ⟨rfl, Or.inl ⟨rfl, a, rfl⟩⟩) fun _ h1 h2 => ⟨rfl, Or.inr ⟨rfl, rfl, h1, h2⟩⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hj⟩ Y t₁ hKY hAY hrY hgY -
  rcases hj with ⟨rfl, a, rfl⟩ | ⟨rfl, rfl, hn1, hn2⟩
  rotate_left
  · -- the same `probs`: back
    refine tail_87 c hin hKY hAY hrY (s := X.cpu.gpr.rsp) (by rw [hgY]) h24 h16 h8 hl
      (b := X.cpu.gpr.rbx) (r := X.cpu.gpr.rbp) (q := X.cpu.gpr.r12) ?_ ?_ ?_ hin₂ h₂ ?_ ?_
    · exact rs8 _ _ _ (by omega)
    · simp only [V24]
      rw [rd8 _ (X.cpu.gpr.rsp - 24) (X.cpu.gpr.rsp - 16) _ 8 (toBytesLE_length _ _) (by omega) (by omega)
        (by omega)]
      exact rs8 _ _ _ (by omega)
    · simp only [V24]
      rw [rd8 _ (X.cpu.gpr.rsp - 24) (X.cpu.gpr.rsp - 8) _ 8 (toBytesLE_length _ _) (by omega) (by omega)
          (by omega),
        rd8 _ (X.cpu.gpr.rsp - 16) (X.cpu.gpr.rsp - 8) _ 8 (toBytesLE_length _ _) (by omega) (by omega)
          (by omega)]
      exact rs8 _ _ _ (by omega)
    · simp only [V24]
      rw [rd8 _ (X.cpu.gpr.rsp - 24) X.cpu.gpr.rsp _ 8 (toBytesLE_length _ _) (by omega) hp8 (by omega),
        rd8 _ (X.cpu.gpr.rsp - 16) X.cpu.gpr.rsp _ 8 (toBytesLE_length _ _) (by omega) hp8 (by omega),
        rd8 _ (X.cpu.gpr.rsp - 8) X.cpu.gpr.rsp _ 8 (toBytesLE_length _ _) (by omega) hp8 (by omega)]
      exact hra
    · intro Z' t' hKZ' hAZ' hrZ' hgZ'
      refine kr0 Z' t' hKZ' hAZ' hrZ' ?_ hn1 hn2
      rw [hgZ', hgY]
      try rfl
  -- at 40: `rsi` = `alloc`, `rdi` = `p`
  refine (c_40 prof).run c hin (fun j' g' _ V' => j' = 46 ∧
      g' = { Y.cpu.gpr with rsi := X.cpu.gpr.rcx, rdi := X.cpu.gpr.rdi } ∧ V' = V24 V X.cpu.gpr) hKY hAY hrY
    (vc_40 fun _ => ⟨rfl, by rw [hgY], rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₂ hK₁ hA₁ hr₁ hg₁ -
  have hs₁ : Y₁.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hg₁, hgY]
  refine c.s_call hK₁ hA₁ hin (lt_len (by decide)) hr₁ (call_46 _) hinL (Lfp.lt_len (by decide)) (by decide)
    (by rw [hs₁, m24_8]; exact hs32) ?_
  rintro Y₂ t₃ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hs₁, m24_8] at hA₂
  have hA₂' : Agree F Y₂.proc.mm.mem (Vst (V24 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (lap_at.add 51) 8)) :=
    hA₂
  have hs₂ : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 32 := by rw [hg₂, hs₁, m24_8]; rfl
  have hb₂ : Y₂.cpu.gpr.rbx = X.cpu.gpr.rdi := by rw [hg₂, hg₁, hgY]; rfl
  have hd₂ : Y₂.cpu.gpr.rdi = X.cpu.gpr.rdi := by rw [hg₂, hg₁, hgY]; rfl
  have hi₂ : Y₂.cpu.gpr.rsi = X.cpu.gpr.rcx := by rw [hg₂, hg₁, hgY]; rfl
  -- the reads of `p->probs` and of `alloc->Free` past the four stores of the frame
  have rp8 : rdq(Vst (V24 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (lap_at.add 51) 8), X.cpu.gpr.rdi + 8#64) =
      rdq(V, X.cpu.gpr.rdi + 8#64) := by
    rw [rd8 _ (X.cpu.gpr.rsp - 32) (X.cpu.gpr.rdi + 8#64) _ 8 (toBytesLE_length _ _) (by omega) (by omega)
      (by omega)]
    exact hx8
  have ra8 : rdq(Vst (V24 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (lap_at.add 51) 8), X.cpu.gpr.rcx + 8#64) =
      rdq(V, X.cpu.gpr.rcx + 8#64) := by
    simp only [V24]
    rw [rd8 _ (X.cpu.gpr.rsp - 32) (X.cpu.gpr.rcx + 8#64) _ 8 (toBytesLE_length _ _) (by omega) (by omega)
        (by omega),
      rd8 _ (X.cpu.gpr.rsp - 24) (X.cpu.gpr.rcx + 8#64) _ 8 (toBytesLE_length _ _) (by omega) (by omega)
        (by omega),
      rd8 _ (X.cpu.gpr.rsp - 16) (X.cpu.gpr.rcx + 8#64) _ 8 (toBytesLE_length _ _) (by omega) (by omega)
        (by omega),
      rd8 _ (X.cpu.gpr.rsp - 8) (X.cpu.gpr.rcx + 8#64) _ 8 (toBytesLE_length _ _) (by omega) (by omega) (by omega)]
  refine Lfp.lfp_ok (Pc := Pc1) (e₂ := lap_at) (j₂ := 51) c hinL hK₂ hA₂' hr₂
    (by rw [hs₂, t32]; omega) (by rw [hs₂, t32]; omega)
    (by rw [hs₂, m32_8]; exact hs40) (by rw [hs₂, m32_16]; exact hs48)
    (fun i hi => by rw [hs₂]; exact h32 i hi)
    (by rw [hd₂]; exact fw8) (by rw [hd₂, tp8]; omega) (by rw [hd₂, hs₂, tp8, t32]; omega)
    (by rw [hi₂]; exact fb) (by rw [hi₂, ta8]; omega) (by rw [hi₂, hs₂, ta8, t32]; omega)
    hinF hF0 (by rw [hi₂, ra8]; exact htgt) hin (lt_len (by decide)) ?_ ?_
  · -- into `alloc->Free` from `LzmaDec_FreeProbs`
    intro Y₃ t₄ hK₃ hA₃ hr₃ hg₃ k₃
    rw [hs₂, m32_8, m32_16, hb₂] at hA₃
    refine kf1 Y₃ t₄ hK₃ hA₃ hr₃ ?_ ?_
    · rw [hg₃, hg₂, hg₁, hgY]
      simp only [Lfp.gC, g24, G1, sk4', rsp_mk, m24_8, m32_16, rp8]
    · intro Z V' t'' hKZ hAZ hrZ hzs hzb hb hr' hPc
      exact k₃ Z V' t'' hKZ hAZ hrZ (by rw [hzs, hs₂, m32_8]) (by rw [hzb, hd₂])
        (by rw [hs₂, m32_8, hb₂]; exact hb) (by rw [hs₂]; exact hr') hPc
  · -- back at 51
    intro Z V' Z' t₄ hPc hKZ' hAZ' hrZ' hgZ'
    obtain ⟨hzp, hzr, hvt⟩ := hP1 Z V' hPc
    rw [hd₂] at hAZ'
    have hz'b : Z'.cpu.gpr.rbx = X.cpu.gpr.rdi := by rw [hgZ', hb₂]
    have hz's : Z'.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hgZ', hs₂, p32_8]
    have hz'p : Z'.cpu.gpr.rbp = (np X.cpu.gpr).setWidth 64 := by rw [hgZ']; exact hzp
    have hz'r : Z'.cpu.gpr.r12 = X.cpu.gpr.rcx := by rw [hgZ']; exact hzr
    refine (c_51 prof).run c hin (fun j' g' _ V'' => j' = 59 ∧
        g' = { Z'.cpu.gpr with rsi := sz X.cpu.gpr, rdi := X.cpu.gpr.rcx } ∧
        V'' = Vst V' (X.cpu.gpr.rdi + 8#64) (toBytesLE 0#64 8)) hKZ' hAZ' hrZ'
      (vc_51 fun _ => ⟨rfl, by simp only [hz'p, hz'r, sw_64_32], rfl⟩) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ U t₅ hKU hAU hrU hgU -
    have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hgU]; exact hz's
    have he : eaD U 12 0 = X.cpu.gpr.rcx := by
      show U.cpu.gpr.get (regOf 12) + BitVec.ofNat 64 0 = _
      rw [hgU]
      show Z'.cpu.gpr.r12 + 0#64 = _
      rw [hz'r, ad0]
    have rt : rdq(Vst V' (X.cpu.gpr.rdi + 8#64) (toBytesLE 0#64 8), X.cpu.gpr.rcx) = eA := by
      rw [rd8 _ (X.cpu.gpr.rdi + 8#64) X.cpu.gpr.rcx _ 8 (toBytesLE_length _ _) (by omega) (by omega) (by omega)]
      exact hvt
    refine c.s_callM hKU hAU hin (lt_len (by decide)) hrU (call_59 _) (by rw [he]; exact fa) hinA hA0
      (by rw [he]; exact rt) (by rw [hsU, m24_8]; exact hs32) ?_
    rintro Y₄ t₆ hK₄ hA₄ ⟨hr₄, hg₄⟩
    rw [hsU, m24_8] at hA₄
    refine kf2 Z V' hPc Y₄ t₆ hK₄ hA₄ hr₄ ?_ ?_
    · rw [hg₄, hsU, m24_8, hgU, hgZ']
      simp only [sk4', hb₂]
    · -- back at 63
      intro Z₂ V'' t'' hKZ₂ hAZ₂ hrZ₂ hz2s hz2b hz2p hb24 hb16 hb8 hret hPc2
      refine (c_63 prof).run c hin (fun j' g' _ V₃ => j' = 87 ∧
          ((Z₂.cpu.gpr.rax = 0#64 ∧ g' = { Z₂.cpu.gpr with rax := 2#64 } ∧
            V₃ = Vst V'' (X.cpu.gpr.rdi + 8#64) (toBytesLE Z₂.cpu.gpr.rax 8)) ∨
           (Z₂.cpu.gpr.rax ≠ 0#64 ∧ g' = { Z₂.cpu.gpr with rax := 0#64 } ∧
            V₃ = Vst (Vst (Vst V'' (X.cpu.gpr.rdi + 8#64) (toBytesLE Z₂.cpu.gpr.rax 8)) (X.cpu.gpr.rdi + 96#64)
              (toBytesLE (np X.cpu.gpr) 4)) (X.cpu.gpr.rdi + 16#64) (toBytesLE (Z₂.cpu.gpr.rax + 3328#64) 8))))
        hKZ₂ hAZ₂ hrZ₂
        (vc_63 (by rw [hz2b]; exact fw8) (by rw [hz2b]; exact fw96) (by rw [hz2b]; exact fw16)
          (fun _ h0 => ⟨rfl, Or.inl ⟨h0, rfl, by rw [hz2b]⟩⟩)
          fun _ h0 => ⟨rfl, Or.inr ⟨h0, rfl, by rw [hz2b, hz2p, sw_64_32]⟩⟩) ?_
      rintro j' g fl V₃ ⟨rfl, hc⟩ W t₇ hKW hAW hrW hgW -
      rcases hc with ⟨h0, rfl, rfl⟩ | ⟨h0, rfl, rfl⟩
      · -- NULL
        refine tail_87 c hin hKW hAW hrW (s := X.cpu.gpr.rsp) (by rw [hgW]; exact hz2s) h24 h16 h8 hl
          (b := X.cpu.gpr.rbx) (r := X.cpu.gpr.rbp) (q := X.cpu.gpr.r12) ?_ ?_ ?_ hin₂ h₂ ?_ ?_
        · rw [rd8 _ (X.cpu.gpr.rdi + 8#64) (X.cpu.gpr.rsp - 24) _ 8 (toBytesLE_length _ _) (by omega) (by omega)
            (by omega)]
          exact hb24
        · rw [rd8 _ (X.cpu.gpr.rdi + 8#64) (X.cpu.gpr.rsp - 16) _ 8 (toBytesLE_length _ _) (by omega) (by omega)
            (by omega)]
          exact hb16
        · rw [rd8 _ (X.cpu.gpr.rdi + 8#64) (X.cpu.gpr.rsp - 8) _ 8 (toBytesLE_length _ _) (by omega) (by omega)
            (by omega)]
          exact hb8
        · rw [rd8 _ (X.cpu.gpr.rdi + 8#64) X.cpu.gpr.rsp _ 8 (toBytesLE_length _ _) (by omega) hp8 (by omega)]
          exact hret
        · intro Z' t' hKZ' hAZ' hrZ' hgZ'
          refine krN Z₂ V'' Z' t' hPc2 h0 hKZ' hAZ' hrZ' ?_
          rw [hgZ', hgW]
          try rfl
      · -- allocated
        refine tail_87 c hin hKW hAW hrW (s := X.cpu.gpr.rsp) (by rw [hgW]; exact hz2s) h24 h16 h8 hl
          (b := X.cpu.gpr.rbx) (r := X.cpu.gpr.rbp) (q := X.cpu.gpr.r12) ?_ ?_ ?_ hin₂ h₂ ?_ ?_
        · rw [rd8 _ (X.cpu.gpr.rdi + 16#64) (X.cpu.gpr.rsp - 24) _ 8 (toBytesLE_length _ _) (by omega)
              (by omega) (by omega),
            rd8 _ (X.cpu.gpr.rdi + 96#64) (X.cpu.gpr.rsp - 24) _ 4 (toBytesLE_length _ _) (by omega)
              (by omega) (by omega),
            rd8 _ (X.cpu.gpr.rdi + 8#64) (X.cpu.gpr.rsp - 24) _ 8 (toBytesLE_length _ _) (by omega)
              (by omega) (by omega)]
          exact hb24
        · rw [rd8 _ (X.cpu.gpr.rdi + 16#64) (X.cpu.gpr.rsp - 16) _ 8 (toBytesLE_length _ _) (by omega)
              (by omega) (by omega),
            rd8 _ (X.cpu.gpr.rdi + 96#64) (X.cpu.gpr.rsp - 16) _ 4 (toBytesLE_length _ _) (by omega)
              (by omega) (by omega),
            rd8 _ (X.cpu.gpr.rdi + 8#64) (X.cpu.gpr.rsp - 16) _ 8 (toBytesLE_length _ _) (by omega)
              (by omega) (by omega)]
          exact hb16
        · rw [rd8 _ (X.cpu.gpr.rdi + 16#64) (X.cpu.gpr.rsp - 8) _ 8 (toBytesLE_length _ _) (by omega)
              (by omega) (by omega),
            rd8 _ (X.cpu.gpr.rdi + 96#64) (X.cpu.gpr.rsp - 8) _ 4 (toBytesLE_length _ _) (by omega)
              (by omega) (by omega),
            rd8 _ (X.cpu.gpr.rdi + 8#64) (X.cpu.gpr.rsp - 8) _ 8 (toBytesLE_length _ _) (by omega)
              (by omega) (by omega)]
          exact hb8
        · rw [rd8 _ (X.cpu.gpr.rdi + 16#64) X.cpu.gpr.rsp _ 8 (toBytesLE_length _ _) (by omega) hp8 (by omega),
            rd8 _ (X.cpu.gpr.rdi + 96#64) X.cpu.gpr.rsp _ 4 (toBytesLE_length _ _) (by omega) hp8 (by omega),
            rd8 _ (X.cpu.gpr.rdi + 8#64) X.cpu.gpr.rsp _ 8 (toBytesLE_length _ _) (by omega) hp8 (by omega)]
          exact hret
        · intro Z' t' hKZ' hAZ' hrZ' hgZ'
          refine krA Z₂ V'' Z' t' hPc2 h0 hKZ' hAZ' hrZ' ?_
          rw [hgZ', hgW]
          try rfl

end FV7z.Lap
