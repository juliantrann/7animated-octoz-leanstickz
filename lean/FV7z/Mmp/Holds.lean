import FV7z.Mmp.Cuts
import FV7z.Write.Holds
/-!
# `__mmap`, around the kernel's `mmap` (PLAN.md §M, M1)

glibc 2.31's `__mmap (addr, len, prot, flags, fd, off)` at `0x666520` in `7zzs` (`mmap64.c`): an offset that is
not a page's multiple is refused (`EINVAL`, the way at 56); with `addr` 0 and `PROT_EXEC` the code may try
`MAP_32BIT` first (the way at 85); otherwise `mmap (addr, len, prot, flags, fd, off)` (with `rbp` and `rbx` saved on the
stack), the kernel's answer `r` returned if it is not an error (`Write.WrErr`); if it is, `errno` (`fs:-0x48`) is set
to `-r` and `rax` to -1. Pieces of the code (`Mmp/Cuts.lean`): from the entry (0) to where the ways meet (25), from
there to the `syscall` (36), from after it (38) to where the ways meet again (46), from there to the `ret` (48).

Zellic's model has `mmap` (`sysMmap`): it may add pages to the address space (or stop, for the cases it does not
model), which `Fn.Seg` (a footprint over a fixed address space) does not follow: so the step of the `syscall` is not
part of these contracts. `mmp_pre` ends at the `syscall`; `mmp_post` starts after it, from a run's start (a new
`Seg`) whose processor is the one after the `syscall`, any answer in `rax`.

- `mg0`, `mg1`, `mV`: the registers at 25 and at the `syscall`, the bytes with `rbp` and `rbx` pushed.
- `vc_0`, `vc_25`, `vc_38_ok`, `vc_38_err`, `vc_46`: the verification conditions of the pieces.
- `mmp_pre`: from the entry to the `syscall`, the offset a page's multiple and not (`addr` 0 and `PROT_EXEC`).
- `mmp_post`: from after the `syscall` to the return address, `rbx` and `rbp` popped, the return address popped.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Write
namespace FV7z.Mmp

/-- The `syscall`. -/
def psys : List Byte := [0x0f, 0x05]
theorem psys_0 : ∀ feat, Dec feat psys 0 (FV7z.mk .syscall 32 [] 2) := by dec_rfl
theorem w_36 : psys <+: mmp.drop 36 := by decide +kernel
theorem sys_36 (feat : Features) : Dec feat mmp 36 (FV7z.mk .syscall 32 [] 2) :=
  Dec.shift (j := 36) (k := 0) (psys_0 feat) w_36 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_48 : pret <+: mmp.drop 48 := by decide +kernel
theorem ret_48 (feat : Features) : Dec feat mmp 48 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 48) (k := 0) (pret_0 feat) w_48 (Nat.zero_le _)

/-- The registers at 25: `rbp` and `rbx` pushed, `rbp` is `addr`, `ebx` the flags. -/
def mg0 (g : Gprs) : Gprs :=
  { g with
    rbx := BitVec.setWidth 64 (BitVec.setWidth 32 g.rcx)
    rsp := g.rsp - 8 - 8
    rbp := g.rdi }

/-- The bytes at 25: `rbp` at `rsp - 8`, `rbx` at `rsp - 16`. -/
def mV (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst V (g.rsp - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8) (toBytesLE g.rbx 8)

/-- The registers at the `syscall`: `eax` 9 (`mmap`), `r10d` the flags. -/
def mg1 (g : Gprs) : Gprs :=
  { mg0 g with
    rax := BitVec.setWidth 64 9#32
    rdi := g.rdi
    r10 := BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 g.rcx))) }

theorem mg1_r10 (g : Gprs) : (mg1 g).r10 = BitVec.setWidth 64 (BitVec.setWidth 32 g.rcx) := by
  show BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 g.rcx))) = _
  rw [sw_64_32]

/-- The registers after the error path: `rax` is -1, `rdx` is `-0x48`. -/
def mErr (g : Gprs) : Gprs := { g with rax := 18446744073709551615#64, rdx := 18446744073709551544#64 }

variable {F : Footprint} {Wl : List Rgn}

/-- What is left of a piece's condition: its footprint facts, equations, cases that cannot be. -/
local macro "vc_fin" : tactic =>
  `(tactic| repeat' (first | rfl | assumption | (intro h; exact absurd h (by decide)) | constructor | intro _))

/-- From the entry to where the ways meet (25): the offset a page's multiple, and `addr` not 0 or no
`PROT_EXEC`: `rbp` and `rbx` pushed. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h9 : BitVec.setWidth 32 g.r9 &&& 4095#32 = 0) (hx : g.rdi ≠ 0 ∨ BitVec.setWidth 8 g.rdx &&& 4#8 = 0)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 25 ∧ g' = mg0 g ∧ V' = mV V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h9 hx hs1 hs2
  rcases hx with hne | hd
  · have hne' : (rdi == 0) = false := by simpa using hne
    wpx [W_0, W_13, W_80, o0, o1, o5, h9, BitVec.and_self, hne', Bool.not_false]
    all_goals vc_fin
  · wpx [W_0, W_13, W_80, o0, o1, o5, h9, BitVec.and_self, hd]
    all_goals vc_fin

/-- From 25 to the `syscall`. -/
theorem vc_25 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_25 fb F Wl (fun j' g' _ V' => j' = 36 ∧
      g' = { g with
        rax := BitVec.setWidth 64 9#32
        rdi := g.rbp
        r10 := BitVec.setWidth 64 (BitVec.setWidth 32 g.rbx) } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_25, o2]
  all_goals vc_fin

/-- From the `syscall` to where the ways meet (46), the kernel's answer `rax` not an error. -/
theorem vc_38_ok {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (he : ¬ WrErr g.rax) :
    W_38 fb F Wl (fun j' g' _ V' => j' = 46 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have he' : decide (WrErr rax) = false := decide_eq_false he
  wpx [W_38, W_144, o3, o6, Op.stf, ja_cmp, he']
  all_goals vc_fin

/-- From the `syscall` to where the ways meet (46), the kernel's answer `rax` an error: `errno` set, `rax` -1. -/
theorem vc_38_err {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (he : WrErr g.rax)
    (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) :
    W_38 fb F Wl (fun j' g' _ V' => j' = 46 ∧ g' = mErr g ∧ V' = Vst V (errnoAt fb) (errnoB g.rax)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have he' : decide (WrErr rax) = true := decide_eq_true he
  wpx [W_38, W_144, o3, o6, Op.stf, ja_cmp, he']
  all_goals first
  | exact ⟨fe, rfl⟩
  | exact ⟨fe, rfl, rfl⟩
  | vc_fin

/-- From 46 to the `ret`: `rbx` and `rbp` popped. -/
theorem vc_46 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hl : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (hl8 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i)) :
    W_46 fb F Wl (fun j' g' _ V' => j' = 48 ∧
      g' = { g with
        rbx := ofBytesLE 64 (List.map V (byteAddrs g.rsp 8))
        rsp := g.rsp + 8 + 8
        rbp := ofBytesLE 64 (List.map V (byteAddrs (g.rsp + 8) 8)) } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl hl8
  wpx [W_46, o4]
  all_goals first
  | exact ⟨hl, hl8, rfl⟩
  | exact ⟨hl, hl8⟩
  | vc_fin

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t : Nat} {V : Addr → Byte} {S : State}

/-- `__mmap (addr, len, prot, flags, fd, off)` from its entry to its `syscall`, the offset a page's multiple and
`addr` not 0 or no `PROT_EXEC`, the 16 bytes below the stack pointer in what the run may store into: the run goes on
from a state at the `syscall` with the registers `mg1` (`eax` 9, `r10` the flags, `rdi`, `rsi`, `rdx`, `r8`, `r9` as
at the entry) and the bytes `mV` (`rbp` and `rbx` pushed). -/
theorem mmp_pre {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L mmp_at mmp)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = mmp_at)
    (h9 : BitVec.setWidth 32 X.cpu.gpr.r9 &&& 4095#32 = 0)
    (hx : X.cpu.gpr.rdi ≠ 0 ∨ BitVec.setWidth 8 X.cpu.gpr.rdx &&& 4#8 = 0)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (k : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (mV V X.cpu.gpr) →
      Y.cpu.rip = mmp_at.add 36 → Y.cpu.gpr = mg1 X.cpu.gpr → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof fb).run c hfs hin (fun j' g' _ V' => j' = 25 ∧ g' = mg0 X.cpu.gpr ∧ V' = mV V X.cpu.gpr) hK hA
    (by rw [addr_add_zero]; exact hrip) (vc_0 h9 hx hs1 hs2) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  refine (c_25 prof fb).run c hfs hin (fun j' g' _ V' => j' = 36 ∧ g' = mg1 X.cpu.gpr ∧ V' = mV V X.cpu.gpr) hKY
    hAY hrY (by rw [hgY]; exact vc_25) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Y₂ t₂ hKY₂ hAY₂ hrY₂ hgY₂ -
  exact k Y₂ t₂ hKY₂ hAY₂ hrY₂ hgY₂

/-- `__mmap` from after its `syscall` (a run's start `S`, the kernel's answer in `rax`) to the return address at
`rsp + 16` (above the saved `rbx` and `rbp`), `errno` apart from the three words: the run goes on with `rbx` and `rbp`
popped and the return address popped; if the answer is not an error, it is in `rax` and the bytes are as at `S`; if
it is, `errno` = `-r` and `rax` = -1. -/
theorem mmp_post {fb : Addr} (c₁ : Seg prof F Wl L S o) (hfs : S.cpu.seg.fsBase = fb) (hin : CodeIn L mmp_at mmp)
    (hA : Agree F S.proc.mm.mem V) (hrip : S.cpu.rip = mmp_at.add 38)
    (hsp : S.cpu.gpr.rsp.toNat + 24 ≤ 2 ^ 64) (hl : ∀ i < 24, Foot F.data (Addr.add S.cpu.gpr.rsp i))
    (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) (hfe : (errnoAt fb).toNat + 4 ≤ 2 ^ 64)
    (hed : (errnoAt fb).toNat + 4 ≤ S.cpu.gpr.rsp.toNat ∨ S.cpu.gpr.rsp.toNat + 24 ≤ (errnoAt fb).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, S.cpu.gpr.rsp + 8 + 8) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl S Z → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr.rsp = S.cpu.gpr.rsp + 8 + 8 + 8 → Z.cpu.gpr.rbx = rdq(V, S.cpu.gpr.rsp) →
      Z.cpu.gpr.rbp = rdq(V, S.cpu.gpr.rsp + 8) →
      (Z.cpu.gpr.r12 = S.cpu.gpr.r12 ∧ Z.cpu.gpr.r13 = S.cpu.gpr.r13 ∧ Z.cpu.gpr.r14 = S.cpu.gpr.r14 ∧
        Z.cpu.gpr.r15 = S.cpu.gpr.r15) →
      (¬ WrErr S.cpu.gpr.rax → Agree F Z.proc.mm.mem V ∧ Z.cpu.gpr.rax = S.cpu.gpr.rax) →
      (WrErr S.cpu.gpr.rax → Agree F Z.proc.mm.mem (Vst V (errnoAt fb) (errnoB S.cpu.gpr.rax)) ∧
        Z.cpu.gpr.rax = 18446744073709551615#64) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE S t := by
  have hlt := S.cpu.gpr.rsp.isLt
  have e8 : (S.cpu.gpr.rsp + 8).toNat = S.cpu.gpr.rsp.toNat + 8 :=
    toNat_add_of_fits (a := S.cpu.gpr.rsp) (i := 8) (n := 24) (by decide) hsp
  have e16 : (S.cpu.gpr.rsp + 8 + 8).toNat = S.cpu.gpr.rsp.toNat + 16 := by
    have h := toNat_add_of_fits (a := S.cpu.gpr.rsp + 8) (i := 8) (n := 16) (by decide) (by rw [e8]; omega)
    exact h.trans (by rw [e8])
  have a8 : ∀ i < 8, Addr.add (S.cpu.gpr.rsp + 8) i = Addr.add S.cpu.gpr.rsp (8 + i) := fun i _ =>
    addr_add_add' S.cpu.gpr.rsp 8 i
  have a16 : ∀ i < 8, Addr.add (S.cpu.gpr.rsp + 8 + 8) i = Addr.add S.cpu.gpr.rsp (16 + i) := fun i _ => by
    have h2 := addr_add_add' (Addr.add S.cpu.gpr.rsp 8) 8 i
    have h3 := addr_add_add' S.cpu.gpr.rsp 8 (8 + i)
    have h4 : 8 + (8 + i) = 16 + i := by omega
    exact h2.trans (h3.trans (by rw [h4]))
  have hl0 : ∀ i < 8, Foot F.data (Addr.add S.cpu.gpr.rsp i) := fun i hi => hl i (by omega)
  have hl8 : ∀ i < 8, Foot F.data (Addr.add (S.cpu.gpr.rsp + 8) i) := fun i hi => by
    rw [a8 i hi]; exact hl (8 + i) (by omega)
  have hl16 : ∀ i < 8, Foot F.data (Addr.add (S.cpu.gpr.rsp + 8 + 8) i) := fun i hi => by
    rw [a16 i hi]; exact hl (16 + i) (by omega)
  by_cases he : WrErr S.cpu.gpr.rax
  · have heb : (errnoB S.cpu.gpr.rax).length = 4 := toBytesLE_length _ _
    have h1 : (errnoAt fb).toNat + (errnoB S.cpu.gpr.rax).length ≤ 2 ^ 64 := by rw [heb]; exact hfe
    have r0 : rdq(Vst V (errnoAt fb) (errnoB S.cpu.gpr.rax), S.cpu.gpr.rsp) = rdq(V, S.cpu.gpr.rsp) := by
      rw [Tun.rd_Vst V (errnoAt fb) _ S.cpu.gpr.rsp 8 h1 (by omega) (by rw [heb]; omega)]
    have r8 : rdq(Vst V (errnoAt fb) (errnoB S.cpu.gpr.rax), S.cpu.gpr.rsp + 8) = rdq(V, S.cpu.gpr.rsp + 8) := by
      rw [Tun.rd_Vst V (errnoAt fb) _ (S.cpu.gpr.rsp + 8) 8 h1 (by rw [e8]; omega) (by rw [heb, e8]; omega)]
    have r16 : rdq(Vst V (errnoAt fb) (errnoB S.cpu.gpr.rax), S.cpu.gpr.rsp + 8 + 8) =
        rdq(V, S.cpu.gpr.rsp + 8 + 8) := by
      rw [Tun.rd_Vst V (errnoAt fb) _ (S.cpu.gpr.rsp + 8 + 8) 8 h1 (by rw [e16]; omega) (by rw [heb, e16]; omega)]
    refine (c_38 prof fb).run c₁ hfs hin
      (fun j' g' _ V' => j' = 46 ∧ g' = mErr S.cpu.gpr ∧ V' = Vst V (errnoAt fb) (errnoB S.cpu.gpr.rax))
      (KeptW.refl _ _) hA hrip (vc_38_err he fe) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Z₁ t₁ hKZ₁ hAZ₁ hrZ₁ hgZ₁ -
    have hs1 : Z₁.cpu.gpr.rsp = S.cpu.gpr.rsp := by rw [hgZ₁]; try rfl
    refine (c_46 prof fb).run c₁ hfs hin _ hKZ₁ hAZ₁ hrZ₁
      (vc_46 (g := Z₁.cpu.gpr) (by rw [hs1]; exact hl0) (by rw [hs1]; exact hl8)) ?_
    rintro j' g fl V₃ ⟨rfl, rfl, rfl⟩ Z₂ t₂ hKZ₂ hAZ₂ hrZ₂ hgZ₂ -
    have hs2 : Z₂.cpu.gpr.rsp = S.cpu.gpr.rsp + 8 + 8 := by rw [hgZ₂, hs1]; try rfl
    refine c₁.s_ret hKZ₂ hAZ₂ hin (lt_len (by decide)) hrZ₂ (ret_48 _) (fun i hi => by rw [hs2]; exact hl16 i hi)
      hin₂ h₂ (by rw [hs2]; exact r16.trans hra) ?_
    rintro Z₃ t₃ hKZ₃ hAZ₃ ⟨hrZ₃, hgZ₃⟩
    refine k Z₃ t₃ hKZ₃ hrZ₃ (by rw [hgZ₃, hgZ₂, hs1]; try rfl) (by rw [hgZ₃, hgZ₂, hs1]; exact r0)
      (by rw [hgZ₃, hgZ₂, hs1]; exact r8) (by rw [hgZ₃, hgZ₂, hgZ₁]; exact ⟨rfl, rfl, rfl, rfl⟩)
      (fun h => absurd he h) fun _ => ⟨hAZ₃, by rw [hgZ₃, hgZ₂, hgZ₁]; try rfl⟩
  · refine (c_38 prof fb).run c₁ hfs hin (fun j' g' _ V' => j' = 46 ∧ g' = S.cpu.gpr ∧ V' = V)
      (KeptW.refl _ _) hA hrip (vc_38_ok he) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Z₁ t₁ hKZ₁ hAZ₁ hrZ₁ hgZ₁ -
    have hs1 : Z₁.cpu.gpr.rsp = S.cpu.gpr.rsp := by rw [hgZ₁]
    refine (c_46 prof fb).run c₁ hfs hin _ hKZ₁ hAZ₁ hrZ₁
      (vc_46 (g := Z₁.cpu.gpr) (by rw [hs1]; exact hl0) (by rw [hs1]; exact hl8)) ?_
    rintro j' g fl V₃ ⟨rfl, rfl, rfl⟩ Z₂ t₂ hKZ₂ hAZ₂ hrZ₂ hgZ₂ -
    have hs2 : Z₂.cpu.gpr.rsp = S.cpu.gpr.rsp + 8 + 8 := by rw [hgZ₂, hs1]; try rfl
    refine c₁.s_ret hKZ₂ hAZ₂ hin (lt_len (by decide)) hrZ₂ (ret_48 _) (fun i hi => by rw [hs2]; exact hl16 i hi)
      hin₂ h₂ (by rw [hs2]; exact hra) ?_
    rintro Z₃ t₃ hKZ₃ hAZ₃ ⟨hrZ₃, hgZ₃⟩
    refine k Z₃ t₃ hKZ₃ hrZ₃ (by rw [hgZ₃, hgZ₂, hs1]; try rfl) (by rw [hgZ₃, hgZ₂, hs1]; try rfl)
      (by rw [hgZ₃, hgZ₂, hs1]; try rfl) (by rw [hgZ₃, hgZ₂, hgZ₁]; exact ⟨rfl, rfl, rfl, rfl⟩)
      (fun _ => ⟨hAZ₃, by rw [hgZ₃, hgZ₂, hgZ₁]; try rfl⟩) fun h => absurd h he

end FV7z.Mmp
