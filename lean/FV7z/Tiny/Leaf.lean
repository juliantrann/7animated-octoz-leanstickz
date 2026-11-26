import FV7z.Image
import FV7z.Lemmas.FnFar
import FV7z.Lemmas.Wp
/-!
# Three tiny functions of `7zzs` (PLAN.md §M, M1)

- `_IO_default_imbue` (`0x5ab370`, glibc 2.31): `endbr64; ret`. `idi_ok`: to the return address.
- `CriticalSection_Delete (p)` (`0x448ba0`, 7-Zip's `Threads.c`): `test rdi, rdi; je` to a `ret`, else a tail jump
  to `0x5fbd00`. `csd_ok`: with `p` null to the return address, else to `0x5fbd00` with the registers as they were.
- `SysFreeString (s)` (`0x5a00c0`, 7-Zip's `MyWindows.cpp`): `test rdi, rdi; je` to a `ret`, else `rdi -= 4` and a
  tail jump to `free` (`0x633750`). `sfs_ok`: with `s` null to the return address, else to `free` with `s - 4`.

The callee of a tail jump is the caller's: a continuation at its entry. `zf_rdi`: after `test rdi, rdi`, `je` is
taken exactly when `rdi` is zero.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Tiny

/-- After `test rdi, rdi`, `je` is taken exactly when `rdi` is zero. -/
theorem zf_rdi {X Y : State} {g : Gprs} (hg : X.cpu.gpr = g) (hz : Y.cpu.rflags.zf = (rv X 64 7 &&& rv X 64 7 == 0)) :
    Y.cpu.rflags.cond 4 = true ↔ g.rdi = 0 := by
  rw [cond_4, hz]
  simp only [rv, BitVec.setWidth_eq, BitVec.and_self, beq_iff_eq, hg]
  try exact Iff.rfl

/-! ## `_IO_default_imbue` -/

/-- `_IO_default_imbue`, `0x5ab370` to `0x5ab375` of `7zzs`. -/
def idi : List Byte := [0xf3, 0x0f, 0x1e, 0xfa, 0xc3]
theorem idi_pin : Exe.bytesAt V2606.zzs.blob 0x5ab370 5 = some idi := by decide +kernel
theorem idi_0 : ∀ feat, Dec feat idi 0 (FV7z.mk .endbr64 32 [] 4) := by intro feat f; rfl
theorem idi_4 : ∀ feat, Dec feat idi 4 (FV7z.mk .ret 64 [] 1) := by intro feat f; rfl

/-! ## `CriticalSection_Delete` -/

/-- `CriticalSection_Delete`, `0x448ba0` to `0x448bb1` of `7zzs`. -/
def csd : List Byte := [0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x85, 0xff, 0x74, 0x07, 0xe9, 0x52, 0x31, 0x1b, 0x00, 0x66,
  0x90, 0xc3]
theorem csd_pin : Exe.bytesAt V2606.zzs.blob 0x448ba0 17 = some csd := by decide +kernel
theorem csd_0 : ∀ feat, Dec feat csd 0 (FV7z.mk .endbr64 32 [] 4) := by intro feat f; rfl
theorem csd_4 : ∀ feat, Dec feat csd 4 (FV7z.mk .test 64 [gr 64 7, gr 64 7] 3) := by intro feat f; rfl
theorem csd_7 : ∀ feat, Dec feat csd 7 (FV7z.mk (.jcc 4) 64 [.rel 7] 2) := by intro feat f; rfl
theorem csd_9 : ∀ feat, Dec feat csd 9 (FV7z.mk .jmp 64 [.rel 1782098] 5) := by intro feat f; rfl
theorem csd_16 : ∀ feat, Dec feat csd 16 (FV7z.mk .ret 64 [] 1) := by intro feat f; rfl

/-! ## `SysFreeString` -/

/-- `SysFreeString`, `0x5a00c0` to `0x5a00d9` of `7zzs`. -/
def sfs : List Byte := [0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x85, 0xff, 0x74, 0x0f, 0x48, 0x83, 0xef, 0x04, 0xe9, 0x7e,
  0x36, 0x09, 0x00, 0x66, 0x0f, 0x1f, 0x44, 0x00, 0x00, 0xc3]
theorem sfs_pin : Exe.bytesAt V2606.zzs.blob 0x5a00c0 25 = some sfs := by decide +kernel
theorem sfs_0 : ∀ feat, Dec feat sfs 0 (FV7z.mk .endbr64 32 [] 4) := by intro feat f; rfl
theorem sfs_4 : ∀ feat, Dec feat sfs 4 (FV7z.mk .test 64 [gr 64 7, gr 64 7] 3) := by intro feat f; rfl
theorem sfs_7 : ∀ feat, Dec feat sfs 7 (FV7z.mk (.jcc 4) 64 [.rel 15] 2) := by intro feat f; rfl
theorem sfs_9 : ∀ feat, Dec feat sfs 9 (FV7z.mk .sub 64 [gr 64 7, .imm 64 4] 4) := by intro feat f; rfl
theorem sfs_13 : ∀ feat, Dec feat sfs 13 (FV7z.mk .jmp 64 [.rel 603774] 5) := by intro feat f; rfl
theorem sfs_24 : ∀ feat, Dec feat sfs 24 (FV7z.mk .ret 64 [] 1) := by intro feat f; rfl

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t : Nat} {V : Addr → Byte}

/-- `_IO_default_imbue` from its entry: to the return address, `rsp` 8 above. -/
theorem idi_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L 0x5ab370#64 idi) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = 0x5ab370#64)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e₂.add j₂ ∧
      Y.cpu.gpr = X.cpu.gpr.set 4 (X.cpu.gpr.rsp + 8)) :
    GoG prof L o gev gP gE X t := by
  refine c.s_endbr hK hA hin (j := 0) (by decide) (by rw [hrip, addr_add_zero]) (idi_0 _) ?_
  rintro Y t₁ hKY hAY ⟨hrY, hgY⟩
  have hs : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
  refine c.s_ret hKY hAY hin (j := 4) (by decide) hrY (idi_4 _) (by rw [hs]; exact hl) hin₂ h₂
    (by rw [hs]; exact hra) ?_
  rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
  exact k' Z t₂ hKZ hAZ ⟨hrZ, by rw [hgZ, hgY]⟩

/-- `CriticalSection_Delete (p)` from its entry: with `p` null to the return address (`kz`), else to `0x5fbd00` with
the registers as they were (`kn`). -/
theorem csd_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L 0x448ba0#64 csd) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = 0x448ba0#64)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    {code₃ : List Byte} (hin₃ : CodeIn L 0x5fbd00#64 code₃) (h₃ : 0 < code₃.length)
    (kz : X.cpu.gpr.rdi = 0 → ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e₂.add j₂ ∧
      Y.cpu.gpr = X.cpu.gpr.set 4 (X.cpu.gpr.rsp + 8))
    (kn : X.cpu.gpr.rdi ≠ 0 → ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = 0x5fbd00#64 ∧
      Y.cpu.gpr = X.cpu.gpr) :
    GoG prof L o gev gP gE X t := by
  refine c.s_endbr hK hA hin (j := 0) (by decide) (by rw [hrip, addr_add_zero]) (csd_0 _) ?_
  rintro Y t₁ hKY hAY ⟨hrY, hgY⟩
  refine c.s_test_rr64 hKY hAY hin (j := 4) (by decide) hrY (csd_4 _) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, hz₂⟩
  have hg : Y₂.cpu.gpr = X.cpu.gpr := hg₂.trans hgY
  refine c.s_jcc hK₂ hA₂ hin (j := 7) (by decide) hr₂ (csd_7 _) (tgt := 16) (by decide) (by decide)
    (fun hcc => ?_) (fun hcc => ?_)
  · -- `p` null: `ret`
    have h0 : X.cpu.gpr.rdi = 0 := (zf_rdi hgY hz₂).1 hcc
    rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃⟩
    have hs : Y₃.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hg₃, hg]
    refine c.s_ret hK₃ hA₃ hin (j := 16) (by decide) hr₃ (csd_16 _) (by rw [hs]; exact hl) hin₂ h₂
      (by rw [hs]; exact hra) ?_
    rintro Z t₄ hKZ hAZ ⟨hrZ, hgZ⟩
    exact kz h0 Z t₄ hKZ hAZ ⟨hrZ, by rw [hgZ, hg₃, hg]⟩
  · -- `p` not null: the tail jump
    have h0 : X.cpu.gpr.rdi ≠ 0 := fun h => by simp [(zf_rdi hgY hz₂).2 h] at hcc
    rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃⟩
    refine c.s_jmp_x hK₃ hA₃ hin (j := 9) (by decide) hr₃ (csd_9 _) hin₃ (tgt := 0) h₃ (by decide) ?_
    rintro Z t₄ hKZ hAZ ⟨hrZ, hgZ⟩
    exact kn h0 Z t₄ hKZ hAZ ⟨by rw [hrZ, addr_add_zero], by rw [hgZ, hg₃, hg]⟩

/-- `SysFreeString (s)` from its entry: with `s` null to the return address (`kz`), else to `free` (`0x633750`) with
`rdi` = `s - 4` (`kn`). -/
theorem sfs_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L 0x5a00c0#64 sfs) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = 0x5a00c0#64)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    {code₃ : List Byte} (hin₃ : CodeIn L 0x633750#64 code₃) (h₃ : 0 < code₃.length)
    (kz : X.cpu.gpr.rdi = 0 → ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e₂.add j₂ ∧
      Y.cpu.gpr = X.cpu.gpr.set 4 (X.cpu.gpr.rsp + 8))
    (kn : X.cpu.gpr.rdi ≠ 0 → ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = 0x633750#64 ∧
      Y.cpu.gpr = { X.cpu.gpr with rdi := X.cpu.gpr.rdi - 4#64 }) :
    GoG prof L o gev gP gE X t := by
  refine c.s_endbr hK hA hin (j := 0) (by decide) (by rw [hrip, addr_add_zero]) (sfs_0 _) ?_
  rintro Y t₁ hKY hAY ⟨hrY, hgY⟩
  refine c.s_test_rr64 hKY hAY hin (j := 4) (by decide) hrY (sfs_4 _) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, hz₂⟩
  have hg : Y₂.cpu.gpr = X.cpu.gpr := hg₂.trans hgY
  refine c.s_jcc hK₂ hA₂ hin (j := 7) (by decide) hr₂ (sfs_7 _) (tgt := 24) (by decide) (by decide)
    (fun hcc => ?_) (fun hcc => ?_)
  · -- `s` null: `ret`
    have h0 : X.cpu.gpr.rdi = 0 := (zf_rdi hgY hz₂).1 hcc
    rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃⟩
    have hs : Y₃.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hg₃, hg]
    refine c.s_ret hK₃ hA₃ hin (j := 24) (by decide) hr₃ (sfs_24 _) (by rw [hs]; exact hl) hin₂ h₂
      (by rw [hs]; exact hra) ?_
    rintro Z t₄ hKZ hAZ ⟨hrZ, hgZ⟩
    exact kz h0 Z t₄ hKZ hAZ ⟨hrZ, by rw [hgZ, hg₃, hg]⟩
  · -- `s` not null: `sub rdi, 4` and the tail jump
    have h0 : X.cpu.gpr.rdi ≠ 0 := fun h => by simp [(zf_rdi hgY hz₂).2 h] at hcc
    rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃⟩
    refine c.s_sub_ri64 hK₃ hA₃ hin (j := 9) (by decide) hr₃ (sfs_9 _) ?_
    rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
    refine c.s_jmp_x hK₄ hA₄ hin (j := 13) (by decide) hr₄ (sfs_13 _) hin₃ (tgt := 0) h₃ (by decide) ?_
    rintro Z t₅ hKZ hAZ ⟨hrZ, hgZ⟩
    refine kn h0 Z t₅ hKZ hAZ ⟨by rw [hrZ, addr_add_zero], ?_⟩
    rw [hgZ, hg₄, hg₃, hg] <;> rfl

end FV7z.Tiny
