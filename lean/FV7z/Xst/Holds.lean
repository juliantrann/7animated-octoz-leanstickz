import FV7z.Xst.Cuts
import FV7z.Fxs.Holds
/-!
# `__xstat` checks the version, then is the `syscall` `stat` (PLAN.md §M, M1)

glibc 2.31's `__xstat (vers, path, buf)` at `0x665300` in `7zzs`, as `__fxstat` (`Fxs.fxs_ok`) with the `syscall`
`stat (path, buf)` (`Seg.s_stat`, `Lemmas/SysStat.lean`): `vers` (32 bits) above 1 (`Fxs.VerBad`) sets `errno` to
`EINVAL` and returns -1 in `eax`; else the answer of `stat` returned, or `errno` set to its error and -1 in `eax`. Two
pieces of the code: from the entry (0) to the `syscall` (24) or to the `ret` of the `EINVAL` path (83), and from after
the `syscall` (26) to one of the two other `ret`s (34, 57).

- `xstG`: the registers at the `syscall`.
- `xst_ok`: called with a path name of `m` nonzero bytes and a NUL in the footprint's data, `buf`'s 144 bytes and
  `errno`'s 4 in what the run may store into, the run reaches the return address with the return address popped, and
  either `errno` = `EINVAL` (`vers` above 1), or after the file system's answer `r` to `stat` (`statRes`, `FsOk`) its
  bytes in `buf` and its answer in `rax`, or `errno` set to its error and `eax` -1.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Close
open FV7z.Fxs (VerBad psys psys_0 pret pret_0)
namespace FV7z.Xst

/-- The `syscall`. -/
theorem w_24 : psys <+: xst.drop 24 := by decide +kernel
theorem sys_24 (feat : Features) : Dec feat xst 24 (FV7z.mk .syscall 32 [] 2) :=
  Dec.shift (j := 24) (k := 0) (psys_0 feat) w_24 (Nat.zero_le _)

/-- The `ret`s. -/
theorem w_34 : pret <+: xst.drop 34 := by decide +kernel
theorem ret_34 (feat : Features) : Dec feat xst 34 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 34) (k := 0) (pret_0 feat) w_34 (Nat.zero_le _)
theorem w_57 : pret <+: xst.drop 57 := by decide +kernel
theorem ret_57 (feat : Features) : Dec feat xst 57 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 57) (k := 0) (pret_0 feat) w_57 (Nat.zero_le _)
theorem w_83 : pret <+: xst.drop 83 := by decide +kernel
theorem ret_83 (feat : Features) : Dec feat xst 83 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 83) (k := 0) (pret_0 feat) w_83 (Nat.zero_le _)

/-- The registers at the `syscall`: `eax` 4, `path` in `rdi`, `buf` in `rsi`, `vers` in `r8d`. -/
def xstG (g : Gprs) : Gprs :=
  { g with
    rax := 4#64, rsi := g.rdx, rdi := g.rsi, r8 := BitVec.setWidth 64 (BitVec.setWidth 32 g.rdi) }

variable {F : Footprint} {Wl : List Rgn}

/-- From the entry to the `syscall`: `vers` at most 1. -/
theorem vc_0_ok {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : VerBad g.rdi = false) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 24 ∧ g' = xstG g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  unfold VerBad at h
  dsimp only at h
  wpx [W_0, W_19, W_64, o0, o1, o4, Op.stfi]
  first
  | exact ⟨fun hc => absurd hc (by rw [h]; decide), fun _ => rfl⟩
  | exact ⟨fun hc => absurd hc (by rw [h]; decide), fun _ => ⟨rfl, rfl⟩⟩
  | exact ⟨fun hc => absurd hc (by rw [h]; decide), fun _ => ⟨rfl, rfl, rfl⟩⟩

/-- From the entry to the `ret` of the `EINVAL` path: `vers` above 1; `errno` = `EINVAL`, `eax` -1. -/
theorem vc_0_bad {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : VerBad g.rdi = true)
    (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 83 ∧ g' = { xstG g with rax := 4294967295#64 } ∧
      V' = Vst V (errnoAt fb) Sgw.einval) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  unfold VerBad at h
  dsimp only at h
  wpx [W_0, W_19, W_64, o0, o1, o4, Op.stfi]
  refine ⟨fun _ => ?_, fun hc => absurd hc (by rw [h]; decide)⟩
  first
  | exact ⟨fe, rfl⟩
  | exact ⟨fe, rfl, rfl⟩
  | exact ⟨fe, rfl, rfl, rfl⟩

/-- From the `syscall` to the first `ret`, the kernel's answer `rax` not an error. -/
theorem vc_26_ok {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (he : ¬ CloseErr g.rax) :
    W_26 fb F Wl (fun j' g' _ V' => j' = 34 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have he' : decide (CloseErr rax) = false := decide_eq_false he
  wpx [W_26, W_40, o2, o3, Op.stf, ja_cmp, he']
  first
  | exact fun h => absurd h (by decide)
  | exact ⟨fun h => absurd h (by decide), fun _ => ⟨rfl, rfl, rfl⟩⟩

/-- From the `syscall` to the second `ret`, the kernel's answer `rax` an error: `errno` set, `eax` -1. -/
theorem vc_26_err {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (he : CloseErr g.rax)
    (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) :
    W_26 fb F Wl (fun j' g' _ V' => j' = 57 ∧ g' = errG g ∧ V' = Vst V (errnoAt fb) (errnoB g.rax)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have he' : decide (CloseErr rax) = true := decide_eq_true he
  wpx [W_26, W_40, o2, o3, Op.stf, ja_cmp, he']
  exact ⟨⟨fe, rfl⟩, fun h => absurd h (by decide)⟩

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t : Nat} {V : Addr → Byte}

/-- `__xstat (vers, path, buf)` from its entry to the return address: the path name `p` at `path` (`m` nonzero bytes
then a NUL, `0 < m`, the word it ends in in the footprint's data, below the end of the user address space), `buf`'s
144 bytes below the end of the user address space and apart from the return address: with `vers` above 1, `errno` =
`EINVAL` and `eax` -1 (`kv`); else the `syscall` `stat` from `Y` (the registers `xstG`) has some answer `r` (`statRes`,
`FsOk`) and the run reaches the return address with the return address popped and, if `r` is not an error, its bytes
in `buf` and `rax` = its answer; if it is, `errno` = `-r` and `eax` -1 (`errG`) (`ks`). -/
theorem xst_ok {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L xst_at xst)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = xst_at)
    (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) (hfe : (errnoAt fb).toNat + 4 ≤ 2 ^ 64)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) (hsp : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hsa : (errnoAt fb).toNat + 4 ≤ X.cpu.gpr.rsp.toNat ∨ X.cpu.gpr.rsp.toNat + 8 ≤ (errnoAt fb).toNat)
    {m : Nat} {p : List Byte} (hm : m < pathMax)
    (hpt : X.cpu.gpr.rsi.toNat + 8 * (m / 8 + 1) ≤ userPtrMax prof.feat)
    (hpl : ∀ i < 8 * (m / 8 + 1), Foot F.data (X.cpu.gpr.rsi.add i))
    (hnz : ∀ i < m, V (X.cpu.gpr.rsi.add i) ≠ 0) (hz : V (X.cpu.gpr.rsi.add m) = 0)
    (hp : (byteAddrs X.cpu.gpr.rsi m).map V = p) (hp0 : p ≠ [])
    (htop : X.cpu.gpr.rdx.toNat + 144 ≤ userPtrMax prof.feat) (hst : ∀ i < 144, Foot Wl (Addr.add X.cpu.gpr.rdx i))
    (hsb : X.cpu.gpr.rdx.toNat + 144 ≤ X.cpu.gpr.rsp.toNat ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdx.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (kv : VerBad X.cpu.gpr.rdi = true → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Z.cpu.rip = e₂.add j₂ →
      Agree F Z.proc.mm.mem (Vst V (errnoAt fb) Sgw.einval) →
      Z.cpu.gpr = { xstG X.cpu.gpr with rax := 4294967295#64 }.set 4 (X.cpu.gpr.rsp + 8) →
      GoG prof L o gev gP gE Z t')
    (ks : VerBad X.cpu.gpr.rdi = false → ∀ (Y Z : State) (r : StatResult) (t' : Nat),
      Y.cpu.gpr = xstG X.cpu.gpr → Y.cpu.rip = xst_at.add 24 → FsOk (statRes r).2 (statRes r).1 →
      KeptW Wl s₀ Z → Z.cpu.rip = e₂.add j₂ →
      (¬ CloseErr (statRes r).1 → Agree F Z.proc.mm.mem (Vst V X.cpu.gpr.rdx (statRes r).2) ∧
        Z.cpu.gpr = ((sysGpr Y 2).set 0 (statRes r).1).set 4 (X.cpu.gpr.rsp + 8)) →
      (CloseErr (statRes r).1 → Agree F Z.proc.mm.mem (Vst V (errnoAt fb) (errnoB (statRes r).1)) ∧
        Z.cpu.gpr = (errG ((sysGpr Y 2).set 0 (statRes r).1)).set 4 (X.cpu.gpr.rsp + 8)) →
      GoG prof L o (gev ++ [linkEv (xstG X.cpu.gpr) p (statRes r).1 (statRes r).2]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  cases hv : VerBad X.cpu.gpr.rdi
  · refine (c_0 prof fb).run c hfs hin (fun j' g' _ V' => j' = 24 ∧ g' = xstG X.cpu.gpr ∧ V' = V) hK hA
      (by rw [addr_add_zero]; exact hrip) (vc_0_ok hv) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    have hrsi : Y.cpu.gpr.rsi = X.cpu.gpr.rdx := by rw [hgY] <;> rfl
    have hrdi : Y.cpu.gpr.rdi = X.cpu.gpr.rsi := by rw [hgY] <;> rfl
    refine c.s_stat hKY hAY hin (lt_len (by decide)) hrY (sys_24 _) (by rw [hgY] <;> (first | decide | rfl)) hm
      (by rw [hrdi]; exact hpt) (by rw [hrdi]; exact hpl) (by rw [hrdi]; exact hnz) (by rw [hrdi]; exact hz)
      (by rw [hrdi]; exact hp) hp0 (by rw [hrsi]; exact htop) (by rw [hrsi]; exact hst) ?_
    intro r hok Y₂ t₂ hKY₂ hAY₂ ⟨hrY₂, hgY₂⟩
    rw [hrsi] at hAY₂
    rw [hgY]
    have hrS : Y₂.cpu.rip = xst_at.add 26 := hrY₂
    have hr0 : ((sysGpr Y 2).set 0 (statRes r).1).rax = (statRes r).1 := rfl
    have hspY : ((sysGpr Y 2).set 0 (statRes r).1).rsp = X.cpu.gpr.rsp := by
      show Y.cpu.gpr.rsp = _
      rw [hgY] <;> rfl
    have hlen := hok.len
    by_cases he : CloseErr (statRes r).1
    · have hb : (statRes r).2 = [] := by
        rcases hok with ⟨h0, -⟩ | ⟨hb, -⟩
        · rw [h0] at he
          exact absurd he (by decide)
        · exact hb
      have hAY₃ : Agree F Y₂.proc.mm.mem V := by
        have h := hAY₂
        rw [hb] at h
        exact h
      refine (c_26 prof fb).run c hfs hin
        (fun j' g' _ V' => j' = 57 ∧ g' = errG ((sysGpr Y 2).set 0 (statRes r).1) ∧
          V' = Vst V (errnoAt fb) (errnoB ((sysGpr Y 2).set 0 (statRes r).1).rax))
        hKY₂ hAY₃ hrS (by rw [hgY₂]; exact vc_26_err (by rw [hr0]; exact he) fe) ?_
      rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Z t₄ hKZ hAZ hrZ hgZ -
      have hspZ : Z.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgZ, errG_rsp, hspY]
      refine c.s_ret hKZ hAZ hin (lt_len (by decide)) hrZ (ret_57 _) (fun i hi => by rw [hspZ]; exact hl i hi)
        hin₂ h₂ ?_ ?_
      · have hb4 : (errnoB ((sysGpr Y 2).set 0 (statRes r).1).rax).length = 4 := toBytesLE_length _ _
        have h1 : (errnoAt fb).toNat + (errnoB ((sysGpr Y 2).set 0 (statRes r).1).rax).length ≤ 2 ^ 64 := by
          rw [hb4]; exact hfe
        have h2 : (errnoAt fb).toNat + (errnoB ((sysGpr Y 2).set 0 (statRes r).1).rax).length ≤
            X.cpu.gpr.rsp.toNat ∨ X.cpu.gpr.rsp.toNat + 8 ≤ (errnoAt fb).toNat := by rw [hb4]; exact hsa
        rw [hspZ, Tun.rd_Vst V (errnoAt fb) (errnoB ((sysGpr Y 2).set 0 (statRes r).1).rax) X.cpu.gpr.rsp 8 h1 hsp
          h2]
        exact hra
      rintro Z' t₅ hKZ' hAZ' ⟨hrZ', hgZ'⟩
      rw [hr0] at hAZ'
      refine ks hv Y Z' r t₅ hgY hrY hok hKZ' hrZ' (fun h => absurd he h) fun _ => ⟨hAZ', ?_⟩
      rw [hgZ', hgZ, errG_rsp, hspY]
      try rfl
    · refine (c_26 prof fb).run c hfs hin
        (fun j' g' _ V' => j' = 34 ∧ g' = (sysGpr Y 2).set 0 (statRes r).1 ∧
          V' = Vst V X.cpu.gpr.rdx (statRes r).2)
        hKY₂ hAY₂ hrS (by rw [hgY₂]; exact vc_26_ok (by rw [hr0]; exact he)) ?_
      rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ Z t₄ hKZ hAZ hrZ hgZ -
      subst V₂
      have hspZ : Z.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgZ, hspY]
      refine c.s_ret hKZ hAZ hin (lt_len (by decide)) hrZ (ret_34 _) (fun i hi => by rw [hspZ]; exact hl i hi)
        hin₂ h₂ ?_ ?_
      · have h47 : userPtrMax prof.feat ≤ 2 ^ 56 := by unfold userPtrMax; split <;> decide
        have h1 : X.cpu.gpr.rdx.toNat + (statRes r).2.length ≤ 2 ^ 64 := by omega
        have h2 : X.cpu.gpr.rdx.toNat + (statRes r).2.length ≤ X.cpu.gpr.rsp.toNat ∨
            X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdx.toNat := by omega
        rw [hspZ, Tun.rd_Vst V X.cpu.gpr.rdx (statRes r).2 X.cpu.gpr.rsp 8 h1 hsp h2]
        exact hra
      rintro Z' t₅ hKZ' hAZ' ⟨hrZ', hgZ'⟩
      refine ks hv Y Z' r t₅ hgY hrY hok hKZ' hrZ' (fun _ => ⟨hAZ', ?_⟩) fun h => absurd h he
      rw [hgZ', hgZ, hspY]
      try rfl
  · refine (c_0 prof fb).run c hfs hin
      (fun j' g' _ V' => j' = 83 ∧ g' = { xstG X.cpu.gpr with rax := 4294967295#64 } ∧
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

end FV7z.Xst
