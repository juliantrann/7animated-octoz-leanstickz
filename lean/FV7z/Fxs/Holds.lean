import FV7z.Fxs.Cuts
import FV7z.Lemmas.SysStat
import FV7z.Close.Holds
import FV7z.Sgw.Holds
/-!
# `__fxstat` checks the version, then is the `syscall` `fstat` (PLAN.md §M, M1)

glibc 2.31's `__fxstat (vers, fd, buf)` at `0x665360` in `7zzs`: `vers` (32 bits) above 1 sets `errno` (`fs:-0x48`,
`Close.errnoAt`) to `EINVAL` (22) and returns -1 in `eax`; else the `syscall` `fstat (fd, buf)`, then the answer
returned, or `errno` set to the error and -1 in `eax` (`Close.CloseErr`, `cmp rax, -4096; ja`). Two pieces of the
code: from the entry (0) to the `syscall` (23) or to the `ret` of the `EINVAL` path (83), and from after the `syscall`
(25) to one of the two other `ret`s (33, 57); the `syscall` itself is `Seg.s_fstat` (`Lemmas/SysStat.lean`), after
which only `buf` has changed.

- `VerOk`: `vers` at most 1, the code's unsigned comparison (`cmp r8d, 1; ja`) as the model has it.
- `fxG`: the registers at the `syscall`.
- `fxs_ok`: called with `buf`'s 144 bytes and `errno`'s 4 in what the run may store into, the run reaches the return
  address with the return address popped, and either `errno` = `EINVAL` (`vers` above 1), or after `fstat`'s result
  `r` (`FsOk`) its bytes in `buf` and its answer in `rax`, or `errno` set to its error and `eax` -1.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Close
namespace FV7z.Fxs

/-- The `syscall`. -/
def psys : List Byte := [0x0f, 0x05]
theorem psys_0 : ∀ feat, Dec feat psys 0 (FV7z.mk .syscall 32 [] 2) := by dec_rfl
theorem w_23 : psys <+: fxs.drop 23 := by decide +kernel
theorem sys_23 (feat : Features) : Dec feat fxs 23 (FV7z.mk .syscall 32 [] 2) :=
  Dec.shift (j := 23) (k := 0) (psys_0 feat) w_23 (Nat.zero_le _)

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_33 : pret <+: fxs.drop 33 := by decide +kernel
theorem ret_33 (feat : Features) : Dec feat fxs 33 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 33) (k := 0) (pret_0 feat) w_33 (Nat.zero_le _)
theorem w_57 : pret <+: fxs.drop 57 := by decide +kernel
theorem ret_57 (feat : Features) : Dec feat fxs 57 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 57) (k := 0) (pret_0 feat) w_57 (Nat.zero_le _)
theorem w_83 : pret <+: fxs.drop 83 := by decide +kernel
theorem ret_83 (feat : Features) : Dec feat fxs 83 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 83) (k := 0) (pret_0 feat) w_83 (Nat.zero_le _)

/-- `vers` above 1: the code's unsigned comparison of its low 32 bits with 1 (`cmp r8d, 1; ja`) as the model has
it. -/
def VerBad (r : BitVec 64) : Bool :=
  !(decide ((BitVec.setWidth 32 r).toNat < 1) || decide (BitVec.setWidth 32 r = 1#32))

/-- The registers at the `syscall`: `eax` 5, `fd` in `edi` (32 bits), `buf` in `rsi`, `vers` in `r8d`. -/
def fxG (g : Gprs) : Gprs :=
  { g with
    rax := 5#64, rsi := g.rdx, rdi := BitVec.setWidth 64 (BitVec.setWidth 32 g.rsi),
    r8 := BitVec.setWidth 64 (BitVec.setWidth 32 g.rdi) }

theorem fxG_rsp (g : Gprs) : (fxG g).rsp = g.rsp := rfl
theorem fxG_rsi (g : Gprs) : (fxG g).rsi = g.rdx := rfl

variable {F : Footprint} {Wl : List Rgn}

/-- From the entry to the `syscall`: `vers` at most 1. -/
theorem vc_0_ok {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : VerBad g.rdi = false) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 23 ∧ g' = fxG g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  unfold VerBad at h
  dsimp only at h
  wpx [W_0, W_18, W_64, o0, o1, o4, Op.stfi]
  first
  | exact ⟨fun hc => absurd hc (by rw [h]; decide), fun _ => rfl⟩
  | exact ⟨fun hc => absurd hc (by rw [h]; decide), fun _ => ⟨rfl, rfl⟩⟩
  | exact ⟨fun hc => absurd hc (by rw [h]; decide), fun _ => ⟨rfl, rfl, rfl⟩⟩

/-- From the entry to the `ret` of the `EINVAL` path: `vers` above 1; `errno` = `EINVAL`, `eax` -1. -/
theorem vc_0_bad {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : VerBad g.rdi = true)
    (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 83 ∧ g' = { fxG g with rax := 4294967295#64 } ∧
      V' = Vst V (errnoAt fb) Sgw.einval) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  unfold VerBad at h
  dsimp only at h
  wpx [W_0, W_18, W_64, o0, o1, o4, Op.stfi]
  refine ⟨fun _ => ?_, fun hc => absurd hc (by rw [h]; decide)⟩
  first
  | exact ⟨fe, rfl⟩
  | exact ⟨fe, rfl, rfl⟩
  | exact ⟨fe, rfl, rfl, rfl⟩

/-- From the `syscall` to the first `ret`, the kernel's answer `rax` not an error. -/
theorem vc_25_ok {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (he : ¬ CloseErr g.rax) :
    W_25 fb F Wl (fun j' g' _ V' => j' = 33 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have he' : decide (CloseErr rax) = false := decide_eq_false he
  wpx [W_25, W_40, o2, o3, Op.stf, ja_cmp, he']
  first
  | exact fun h => absurd h (by decide)
  | exact ⟨fun h => absurd h (by decide), fun _ => ⟨rfl, rfl, rfl⟩⟩

/-- From the `syscall` to the second `ret`, the kernel's answer `rax` an error: `errno` set, `eax` -1. -/
theorem vc_25_err {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (he : CloseErr g.rax)
    (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) :
    W_25 fb F Wl (fun j' g' _ V' => j' = 57 ∧ g' = errG g ∧ V' = Vst V (errnoAt fb) (errnoB g.rax)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have he' : decide (CloseErr rax) = true := decide_eq_true he
  wpx [W_25, W_40, o2, o3, Op.stf, ja_cmp, he']
  exact ⟨⟨fe, rfl⟩, fun h => absurd h (by decide)⟩

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t : Nat} {V : Addr → Byte}

/-- `__fxstat (vers, fd, buf)` from its entry to the return address, `buf`'s 144 bytes below the end of the user
address space and apart from the return address: with `vers` above 1, `errno` = `EINVAL` and `eax` -1 (`kv`); else the
`syscall` `fstat` from `Y` (the registers `fxG`) gives some `r` (`FsOk`) and the run reaches the return address with
the return address popped and, if `r` is not an error, its bytes in `buf` and `rax` = its answer; if it is, `errno` =
`-r` and `eax` -1 (`errG`) (`ks`). -/
theorem fxs_ok {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L fxs_at fxs)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = fxs_at)
    (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) (hfe : (errnoAt fb).toNat + 4 ≤ 2 ^ 64)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) (hsp : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hsa : (errnoAt fb).toNat + 4 ≤ X.cpu.gpr.rsp.toNat ∨ X.cpu.gpr.rsp.toNat + 8 ≤ (errnoAt fb).toNat)
    (htop : X.cpu.gpr.rdx.toNat + 144 ≤ userPtrMax prof.feat) (hst : ∀ i < 144, Foot Wl (Addr.add X.cpu.gpr.rdx i))
    (hsb : X.cpu.gpr.rdx.toNat + 144 ≤ X.cpu.gpr.rsp.toNat ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdx.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (kv : VerBad X.cpu.gpr.rdi = true → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Z.cpu.rip = e₂.add j₂ →
      Agree F Z.proc.mm.mem (Vst V (errnoAt fb) Sgw.einval) →
      Z.cpu.gpr = { fxG X.cpu.gpr with rax := 4294967295#64 }.set 4 (X.cpu.gpr.rsp + 8) →
      GoG prof L o gev gP gE Z t')
    (ks : VerBad X.cpu.gpr.rdi = false → ∀ (Y Z : State) (r : FsOut) (t' : Nat), Y.cpu.gpr = fxG X.cpu.gpr →
      Y.cpu.rip = fxs_at.add 23 → FsOk r.bs r.ret → KeptW Wl s₀ Z → Z.cpu.rip = e₂.add j₂ →
      (¬ CloseErr r.ret → Agree F Z.proc.mm.mem (Vst V X.cpu.gpr.rdx r.bs) ∧
        Z.cpu.gpr = ((sysGpr Y 2).set 0 r.ret).set 4 (X.cpu.gpr.rsp + 8)) →
      (CloseErr r.ret → Agree F Z.proc.mm.mem (Vst V (errnoAt fb) (errnoB r.ret)) ∧
        Z.cpu.gpr = (errG ((sysGpr Y 2).set 0 r.ret)).set 4 (X.cpu.gpr.rsp + 8)) →
      GoG prof L o (gev ++ [fsEv (fxG X.cpu.gpr) r]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  cases hv : VerBad X.cpu.gpr.rdi
  · refine (c_0 prof fb).run c hfs hin (fun j' g' _ V' => j' = 23 ∧ g' = fxG X.cpu.gpr ∧ V' = V) hK hA
      (by rw [addr_add_zero]; exact hrip) (vc_0_ok hv) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    have hrsi : Y.cpu.gpr.rsi = X.cpu.gpr.rdx := by rw [hgY] <;> rfl
    refine c.s_fstat hKY hAY hin (lt_len (by decide)) hrY (sys_23 _) (by rw [hgY] <;> (first | decide | rfl))
      (by rw [hrsi]; exact htop) (by rw [hrsi]; exact hst) ?_
    intro r hok Y₂ t₂ hKY₂ hAY₂ ⟨hrY₂, hgY₂⟩
    rw [hrsi] at hAY₂
    rw [hgY]
    have hrS : Y₂.cpu.rip = fxs_at.add 25 := hrY₂
    have hr0 : ((sysGpr Y 2).set 0 r.ret).rax = r.ret := rfl
    have hspY : ((sysGpr Y 2).set 0 r.ret).rsp = X.cpu.gpr.rsp := by
      show Y.cpu.gpr.rsp = _
      rw [hgY] <;> rfl
    have hlen := hok.len
    by_cases he : CloseErr r.ret
    · have hb : r.bs = [] := by
        rcases hok with ⟨h0, -⟩ | ⟨hb, -⟩
        · rw [h0] at he
          exact absurd he (by decide)
        · exact hb
      have hAY₃ : Agree F Y₂.proc.mm.mem V := by
        have h := hAY₂
        rw [hb] at h
        exact h
      refine (c_25 prof fb).run c hfs hin
        (fun j' g' _ V' => j' = 57 ∧ g' = errG ((sysGpr Y 2).set 0 r.ret) ∧
          V' = Vst V (errnoAt fb) (errnoB ((sysGpr Y 2).set 0 r.ret).rax))
        hKY₂ hAY₃ hrS (by rw [hgY₂]; exact vc_25_err (by rw [hr0]; exact he) fe) ?_
      rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Z t₄ hKZ hAZ hrZ hgZ -
      have hspZ : Z.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgZ, errG_rsp, hspY]
      refine c.s_ret hKZ hAZ hin (lt_len (by decide)) hrZ (ret_57 _) (fun i hi => by rw [hspZ]; exact hl i hi)
        hin₂ h₂ ?_ ?_
      · have hb4 : (errnoB ((sysGpr Y 2).set 0 r.ret).rax).length = 4 := toBytesLE_length _ _
        have h1 : (errnoAt fb).toNat + (errnoB ((sysGpr Y 2).set 0 r.ret).rax).length ≤ 2 ^ 64 := by
          rw [hb4]; exact hfe
        have h2 : (errnoAt fb).toNat + (errnoB ((sysGpr Y 2).set 0 r.ret).rax).length ≤ X.cpu.gpr.rsp.toNat ∨
            X.cpu.gpr.rsp.toNat + 8 ≤ (errnoAt fb).toNat := by rw [hb4]; exact hsa
        rw [hspZ, Tun.rd_Vst V (errnoAt fb) (errnoB ((sysGpr Y 2).set 0 r.ret).rax) X.cpu.gpr.rsp 8 h1 hsp h2]
        exact hra
      rintro Z' t₅ hKZ' hAZ' ⟨hrZ', hgZ'⟩
      rw [hr0] at hAZ'
      refine ks hv Y Z' r t₅ hgY hrY hok hKZ' hrZ' (fun h => absurd he h) fun _ => ⟨hAZ', ?_⟩
      rw [hgZ', hgZ, errG_rsp, hspY]
      try rfl
    · refine (c_25 prof fb).run c hfs hin
        (fun j' g' _ V' => j' = 33 ∧ g' = (sysGpr Y 2).set 0 r.ret ∧ V' = Vst V X.cpu.gpr.rdx r.bs)
        hKY₂ hAY₂ hrS (by rw [hgY₂]; exact vc_25_ok (by rw [hr0]; exact he)) ?_
      rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ Z t₄ hKZ hAZ hrZ hgZ -
      subst V₂
      have hspZ : Z.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgZ, hspY]
      refine c.s_ret hKZ hAZ hin (lt_len (by decide)) hrZ (ret_33 _) (fun i hi => by rw [hspZ]; exact hl i hi)
        hin₂ h₂ ?_ ?_
      · have h47 : userPtrMax prof.feat ≤ 2 ^ 56 := by unfold userPtrMax; split <;> decide
        have h1 : X.cpu.gpr.rdx.toNat + r.bs.length ≤ 2 ^ 64 := by omega
        have h2 : X.cpu.gpr.rdx.toNat + r.bs.length ≤ X.cpu.gpr.rsp.toNat ∨
            X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdx.toNat := by omega
        rw [hspZ, Tun.rd_Vst V X.cpu.gpr.rdx r.bs X.cpu.gpr.rsp 8 h1 hsp h2]
        exact hra
      rintro Z' t₅ hKZ' hAZ' ⟨hrZ', hgZ'⟩
      refine ks hv Y Z' r t₅ hgY hrY hok hKZ' hrZ' (fun _ => ⟨hAZ', ?_⟩) fun h => absurd h he
      rw [hgZ', hgZ, hspY]
      try rfl
  · refine (c_0 prof fb).run c hfs hin
      (fun j' g' _ V' => j' = 83 ∧ g' = { fxG X.cpu.gpr with rax := 4294967295#64 } ∧
        V' = Vst V (errnoAt fb) Sgw.einval) hK hA (by rw [addr_add_zero]; exact hrip) (vc_0_bad hv fe) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Z t₁ hKZ hAZ hrZ hgZ -
    have hspZ : Z.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgZ] <;> rfl
    refine c.s_ret hKZ hAZ hin (lt_len (by decide)) hrZ (ret_83 _) (fun i hi => by rw [hspZ]; exact hl i hi)
      hin₂ h₂ ?_ ?_
    · have hb : Sgw.einval.length = 4 := toBytesLE_length _ _
      have h1 : (errnoAt fb).toNat + Sgw.einval.length ≤ 2 ^ 64 := by rw [hb]; exact hfe
      have h2 : (errnoAt fb).toNat + Sgw.einval.length ≤ X.cpu.gpr.rsp.toNat ∨
          X.cpu.gpr.rsp.toNat + 8 ≤ (errnoAt fb).toNat := by rw [hb]; exact hsa
      rw [hspZ, Tun.rd_Vst V (errnoAt fb) Sgw.einval X.cpu.gpr.rsp 8 h1 hsp h2]
      exact hra
    rintro Z' t₃ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    exact kv hv Z' t₃ hKZ' hrZ' hAZ' (by rw [hgZ', hgZ]; try rfl)

end FV7z.Fxs
