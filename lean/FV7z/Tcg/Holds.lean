import FV7z.Tcg.Cuts
import FV7z.Write.Holds
/-!
# `__tcgetattr`, around the kernel's `ioctl (TCGETS)` (PLAN.md §M, M1)

glibc 2.31's `__tcgetattr (fd, termios_p)` at `0x666240` in `7zzs`: `ioctl (fd, TCGETS, &k)` (`0x5401`) into a
`struct __kernel_termios` `k` at `rsp` in a frame of 56 bytes with the stack guard (`fs:0x28`) at `rsp + 40`. The
kernel's answer `r`: an error (`Write.WrErr`, `ja` after `cmp rax, -4096`), `errno` (`fs:-0x48`) is set to `-r` and
`eax` to -1; not an error and not 0, it is returned (`eax`); 0, `k` is copied to `*termios_p` (the way at 57, not
one of these contracts). Three pieces of the code (`Tcg/Cuts.lean`): from the entry (0) to the `syscall` (40),
from after it (42) to where the ways meet (143), from there to the `ret` (166).

Zellic's model has `ioctl (TCGETS)` (36 bytes copied out to `rdx`): the step of the `syscall` is not part of these
contracts (as `Mun`, `Mmp`), nor is the copy after an answer 0. `tcg_pre` ends at the `syscall`; `tcg_post` starts
after it, from a run's start (a new `Seg`) whose processor is the one after the `syscall`, the answer in `rax` an
error or not 0.

- `tg1`, `tV`: the registers and the bytes at the `syscall`; `tErr`: the registers after the error path.
- `vc_0`, `vc_42_err`, `vc_42_nz`, `vc_143`: the verification conditions of the pieces.
- `tcg_pre`, `tcg_post`: from the entry to the `syscall`, from after it to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Write
namespace FV7z.Tcg

/-- The `syscall`. -/
def psys : List Byte := [0x0f, 0x05]
theorem psys_0 : ∀ feat, Dec feat psys 0 (FV7z.mk .syscall 32 [] 2) := by dec_rfl
theorem w_40 : psys <+: tcg.drop 40 := by decide +kernel
theorem sys_40 (feat : Features) : Dec feat tcg 40 (FV7z.mk .syscall 32 [] 2) :=
  Dec.shift (j := 40) (k := 0) (psys_0 feat) w_40 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_166 : pret <+: tcg.drop 166 := by decide +kernel
theorem ret_166 (feat : Features) : Dec feat tcg 166 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 166) (k := 0) (pret_0 feat) w_166 (Nat.zero_le _)

/-- The registers at the `syscall`: `eax` 16 (`ioctl`), `esi` `TCGETS`, `rdx` the frame, `r8` `termios_p`. -/
def tg1 (g : Gprs) : Gprs :=
  { g with rax := BitVec.setWidth 64 16#32, rdx := g.rsp - 56#64, rsp := g.rsp - 56#64,
           rsi := BitVec.setWidth 64 21505#32, r8 := g.rsi }

/-- The bytes at the `syscall`: the stack guard at `rsp - 56 + 40`. -/
def tV (V : Addr → Byte) (g : Gprs) (fb : Addr) : Addr → Byte :=
  Vst V (g.rsp - 56#64 + 40#64) (toBytesLE rdq(V, fb + 40#64) 8)

/-- The registers after the error path: `rdx` is `-0x48`, `eax` `-r`, `r9d` -1. -/
def tErr (g : Gprs) : Gprs :=
  { g with rax := BitVec.setWidth 64 (0 - BitVec.setWidth 32 g.rax), rdx := 18446744073709551544#64,
           r9 := BitVec.setWidth 64 4294967295#32 }

variable {F : Footprint} {Wl : List Rgn}

/-- What is left of a piece's condition: its footprint facts, equations, cases that cannot be. -/
local macro "vc_fin" : tactic =>
  `(tactic| repeat' (first | rfl | assumption | (intro h; exact absurd h (by decide)) | constructor | intro _))

/-- To the `syscall`. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hfw : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 56#64 + 40#64) i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 40 ∧ g' = tg1 g ∧ V' = tV V g fb) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hfw
  wpx [W_0, o0, Op.ldf]
  all_goals vc_fin

/-- From the `syscall` to where the ways meet, the kernel's answer `rax` an error: `errno` set. -/
theorem vc_42_err {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (he : WrErr g.rax)
    (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) :
    W_42 fb F Wl (fun j' g' _ V' => j' = 143 ∧ g' = tErr g ∧ V' = Vst V (errnoAt fb) (errnoB g.rax)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have he' : decide (WrErr rax) = true := decide_eq_true he
  wpx [W_42, W_176, W_50, W_57, o1, o6, o2, o3, Op.stf, ja_cmp, he']
  all_goals first
  | exact ⟨⟨fe, rfl⟩, fun h => absurd h (by decide)⟩
  | exact ⟨fe, rfl⟩
  | exact ⟨⟨fe, rfl, rfl⟩, fun h => absurd h (by decide)⟩
  | exact ⟨fe, rfl, rfl⟩
  | vc_fin

/-- From the `syscall` to where the ways meet, the kernel's answer `rax` not an error and `eax` not 0. -/
theorem vc_42_nz {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (he : ¬ WrErr g.rax)
    (hnz : BitVec.setWidth 32 g.rax ≠ 0) :
    W_42 fb F Wl (fun j' g' _ V' => j' = 143 ∧ g' = { g with r9 := BitVec.setWidth 64 (BitVec.setWidth 32 g.rax) } ∧
      V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have he' : decide (WrErr rax) = false := decide_eq_false he
  have hnz' : (BitVec.setWidth 32 rax == 0) = false := by simpa using hnz
  wpx [W_42, W_176, W_50, W_57, o1, o6, o2, o3, Op.stf, ja_cmp, he', BitVec.and_self, hnz', Bool.not_false]
  all_goals first
  | exact fun h => absurd h (by decide)
  | exact ⟨fun h => absurd h (by decide), fun _ => ⟨fun _ => ⟨rfl, rfl⟩, fun h => absurd h (by decide)⟩⟩
  | repeat' (first | rfl | assumption | (intro h; exact absurd h (by decide)) |
      (intro h; exact absurd h (by simp only [BitVec.and_self, hnz', Bool.not_false] <;> decide)) |
      constructor | intro _)

/-- The check of the stack guard, to the `ret`: `eax` is `r9d`, the frame dropped. -/
theorem vc_143 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hl : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64) i)) (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hc : rdq(V, g.rsp + 40#64) = rdq(V, fb + 40#64)) :
    W_143 fb F Wl (fun j' g' _ V' => j' = 166 ∧
      g' = { g with rax := BitVec.setWidth 64 (BitVec.setWidth 32 g.r9), rsp := g.rsp + 56#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl hc
  wpx [W_143, W_159, o4, o5, Op.xormf, hc, BitVec.xor_self]
  all_goals first
  | exact ⟨hl, hcl, fun h => absurd h (by decide), fun _ => rfl⟩
  | exact ⟨hl, hcl, fun _ => rfl⟩
  | exact ⟨hl, hcl, fun h => absurd h (by decide), fun _ => ⟨rfl, rfl⟩⟩
  | exact ⟨hl, hcl, fun h => absurd h (by decide), fun _ => ⟨rfl, rfl, rfl⟩⟩
  | exact ⟨hl, hcl⟩
  | vc_fin

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t : Nat} {V : Addr → Byte} {S : State}

/-- `__tcgetattr (fd, termios_p)` from its entry to its `syscall`: the run goes on from a state at the `syscall`
with the registers `tg1` (`ioctl (fd, TCGETS, rsp - 56)`) and the stack guard stored at `rsp - 16`. -/
theorem tcg_pre {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L tcg_at tcg)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = tcg_at)
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hfw : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 56#64 + 40#64) i))
    (k : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (tV V X.cpu.gpr fb) →
      Y.cpu.rip = tcg_at.add 40 → Y.cpu.gpr = tg1 X.cpu.gpr → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof fb).run c hfs hin
    (fun j' g' _ V' => j' = 40 ∧ g' = tg1 X.cpu.gpr ∧ V' = tV V X.cpu.gpr fb) hK hA
    (by rw [addr_add_zero]; exact hrip) (vc_0 hcl hfw) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  exact k Y t₁ hKY hAY hrY hgY

/-- `__tcgetattr` from after its `syscall` (a run's start `S`, the kernel's answer in `rax` an error or `eax` not
0) to the return address at `rsp + 56`, the stack guard at `rsp + 40` the one at `fs:0x28`, `errno` apart from
both: the run goes on with the frame dropped and the return address popped, the registers a call keeps as at `S`;
if the answer is not an error, `eax` is it and the bytes are as at `S`; if it is, `errno` = `-r` and `eax` = -1. -/
theorem tcg_post {fb : Addr} (c₁ : Seg prof F Wl L S o) (hfs : S.cpu.seg.fsBase = fb) (hin : CodeIn L tcg_at tcg)
    (hA : Agree F S.proc.mm.mem V) (hrip : S.cpu.rip = tcg_at.add 42)
    (hans : WrErr S.cpu.gpr.rax ∨ BitVec.setWidth 32 S.cpu.gpr.rax ≠ 0)
    (hsp : S.cpu.gpr.rsp.toNat + 64 ≤ 2 ^ 64)
    (hl40 : ∀ i < 8, Foot F.data (Addr.add (S.cpu.gpr.rsp + 40#64) i))
    (hl56 : ∀ i < 8, Foot F.data (Addr.add (S.cpu.gpr.rsp + 56#64) i))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)) (hcf : (fb + 40#64).toNat + 8 ≤ 2 ^ 64)
    (hc : rdq(V, S.cpu.gpr.rsp + 40#64) = rdq(V, fb + 40#64))
    (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) (hfe : (errnoAt fb).toNat + 4 ≤ 2 ^ 64)
    (hed : (errnoAt fb).toNat + 4 ≤ S.cpu.gpr.rsp.toNat + 40 ∨ S.cpu.gpr.rsp.toNat + 64 ≤ (errnoAt fb).toNat)
    (hedc : (errnoAt fb).toNat + 4 ≤ (fb + 40#64).toNat ∨ (fb + 40#64).toNat + 8 ≤ (errnoAt fb).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, S.cpu.gpr.rsp + 56#64) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl S Z → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr.rsp = S.cpu.gpr.rsp + 56#64 + 8 →
      (Z.cpu.gpr.rbx = S.cpu.gpr.rbx ∧ Z.cpu.gpr.rbp = S.cpu.gpr.rbp ∧ Z.cpu.gpr.r12 = S.cpu.gpr.r12 ∧
        Z.cpu.gpr.r13 = S.cpu.gpr.r13 ∧ Z.cpu.gpr.r14 = S.cpu.gpr.r14 ∧ Z.cpu.gpr.r15 = S.cpu.gpr.r15) →
      (¬ WrErr S.cpu.gpr.rax → Agree F Z.proc.mm.mem V ∧
        Z.cpu.gpr.rax = BitVec.setWidth 64 (BitVec.setWidth 32 S.cpu.gpr.rax)) →
      (WrErr S.cpu.gpr.rax → Agree F Z.proc.mm.mem (Vst V (errnoAt fb) (errnoB S.cpu.gpr.rax)) ∧
        Z.cpu.gpr.rax = BitVec.setWidth 64 4294967295#32) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE S t := by
  have e40 : (S.cpu.gpr.rsp + 40#64).toNat = S.cpu.gpr.rsp.toNat + 40 :=
    toNat_add_of_fits (a := S.cpu.gpr.rsp) (i := 40) (n := 64) (by decide) hsp
  have e56 : (S.cpu.gpr.rsp + 56#64).toNat = S.cpu.gpr.rsp.toNat + 56 :=
    toNat_add_of_fits (a := S.cpu.gpr.rsp) (i := 56) (n := 64) (by decide) hsp
  by_cases he : WrErr S.cpu.gpr.rax
  · have heb : (errnoB S.cpu.gpr.rax).length = 4 := toBytesLE_length _ _
    have h1 : (errnoAt fb).toNat + (errnoB S.cpu.gpr.rax).length ≤ 2 ^ 64 := by rw [heb]; exact hfe
    have r40 : rdq(Vst V (errnoAt fb) (errnoB S.cpu.gpr.rax), S.cpu.gpr.rsp + 40#64) =
        rdq(V, S.cpu.gpr.rsp + 40#64) := by
      rw [Tun.rd_Vst V (errnoAt fb) _ (S.cpu.gpr.rsp + 40#64) 8 h1 (by rw [e40]; omega) (by rw [heb, e40]; omega)]
    have r56 : rdq(Vst V (errnoAt fb) (errnoB S.cpu.gpr.rax), S.cpu.gpr.rsp + 56#64) =
        rdq(V, S.cpu.gpr.rsp + 56#64) := by
      rw [Tun.rd_Vst V (errnoAt fb) _ (S.cpu.gpr.rsp + 56#64) 8 h1 (by rw [e56]; omega) (by rw [heb, e56]; omega)]
    have rc : rdq(Vst V (errnoAt fb) (errnoB S.cpu.gpr.rax), fb + 40#64) = rdq(V, fb + 40#64) := by
      rw [Tun.rd_Vst V (errnoAt fb) _ (fb + 40#64) 8 h1 hcf (by rw [heb]; exact hedc)]
    refine (c_42 prof fb).run c₁ hfs hin
      (fun j' g' _ V' => j' = 143 ∧ g' = tErr S.cpu.gpr ∧ V' = Vst V (errnoAt fb) (errnoB S.cpu.gpr.rax))
      (KeptW.refl _ _) hA hrip (vc_42_err he fe) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Z₁ t₁ hKZ₁ hAZ₁ hrZ₁ hgZ₁ -
    have hs1 : Z₁.cpu.gpr.rsp = S.cpu.gpr.rsp := by rw [hgZ₁]; try rfl
    refine (c_143 prof fb).run c₁ hfs hin _ hKZ₁ hAZ₁ hrZ₁
      (vc_143 (g := Z₁.cpu.gpr) (by rw [hs1]; exact hl40) hcl (by rw [hs1, r40, rc]; exact hc)) ?_
    rintro j' g fl V₃ ⟨rfl, rfl, rfl⟩ Z₂ t₂ hKZ₂ hAZ₂ hrZ₂ hgZ₂ -
    have hs2 : Z₂.cpu.gpr.rsp = S.cpu.gpr.rsp + 56#64 := by rw [hgZ₂, hs1]; try rfl
    refine c₁.s_ret hKZ₂ hAZ₂ hin (lt_len (by decide)) hrZ₂ (ret_166 _) (fun i hi => by rw [hs2]; exact hl56 i hi)
      hin₂ h₂ (by rw [hs2]; exact r56.trans hra) ?_
    rintro Z₃ t₃ hKZ₃ hAZ₃ ⟨hrZ₃, hgZ₃⟩
    refine k Z₃ t₃ hKZ₃ hrZ₃ (by rw [hgZ₃, hgZ₂, hs1]; try rfl)
      (by rw [hgZ₃, hgZ₂, hgZ₁]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
      (fun h => absurd he h) fun _ => ⟨hAZ₃, by rw [hgZ₃, hgZ₂, hgZ₁]; first | rfl | decide⟩
  · have hnz : BitVec.setWidth 32 S.cpu.gpr.rax ≠ 0 := hans.resolve_left he
    refine (c_42 prof fb).run c₁ hfs hin
      (fun j' g' _ V' => j' = 143 ∧
        g' = { S.cpu.gpr with r9 := BitVec.setWidth 64 (BitVec.setWidth 32 S.cpu.gpr.rax) } ∧ V' = V)
      (KeptW.refl _ _) hA hrip (vc_42_nz he hnz) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Z₁ t₁ hKZ₁ hAZ₁ hrZ₁ hgZ₁ -
    have hs1 : Z₁.cpu.gpr.rsp = S.cpu.gpr.rsp := by rw [hgZ₁]; try rfl
    refine (c_143 prof fb).run c₁ hfs hin _ hKZ₁ hAZ₁ hrZ₁
      (vc_143 (g := Z₁.cpu.gpr) (by rw [hs1]; exact hl40) hcl (by rw [hs1]; exact hc)) ?_
    rintro j' g fl V₃ ⟨rfl, rfl, rfl⟩ Z₂ t₂ hKZ₂ hAZ₂ hrZ₂ hgZ₂ -
    have hs2 : Z₂.cpu.gpr.rsp = S.cpu.gpr.rsp + 56#64 := by rw [hgZ₂, hs1]; try rfl
    refine c₁.s_ret hKZ₂ hAZ₂ hin (lt_len (by decide)) hrZ₂ (ret_166 _) (fun i hi => by rw [hs2]; exact hl56 i hi)
      hin₂ h₂ (by rw [hs2]; exact hra) ?_
    rintro Z₃ t₃ hKZ₃ hAZ₃ ⟨hrZ₃, hgZ₃⟩
    refine k Z₃ t₃ hKZ₃ hrZ₃ (by rw [hgZ₃, hgZ₂, hs1]; try rfl)
      (by rw [hgZ₃, hgZ₂, hgZ₁]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
      (fun _ => ⟨hAZ₃, by rw [hgZ₃, hgZ₂, hgZ₁]; exact congrArg (BitVec.setWidth 64) (sw_64_32 _)⟩)
      fun h => absurd h he

end FV7z.Tcg
