import FV7z.Gdn.Cuts
import FV7z.Lemmas.SysDents
import FV7z.Lemmas.CmpImm
import FV7z.Lseek.Holds
/-!
# `__getdents` reads a directory's entries (PLAN.md §M, M1)

glibc 2.31's `__getdents (fd, buf, nbytes)` at `0x6a2820` in `7zzs` (`__getdents64`, `getdents64.c`): `nbytes`
capped at `INT_MAX` (`cmp`, `cmova`), then the `syscall` `getdents64` (217) as is, no conversion of the entries; the
answer returned, or `errno` (`fs:-0x48`) set to the error and -1 returned. Two pieces of the code: to the `syscall`
(25) and from after it (27) to one of the two `ret`s (35, 59); the `syscall` itself is `Seg.s_getdents_re`
(`Lemmas/SysDents.lean`), after which the run goes on from its own start. The answer is told apart as `__close`'s
(`Close.CloseErr`, `cmp rax, -4096; ja`), the error path as `__libc_lseek`'s (`Lseek.lsErrG`).

- `gdS`, `gdE`: the state after the `syscall` and its event.
- `gdn_ok`: called with `nbytes` at most `INT_MAX`, `buf`'s `nbytes` bytes and `errno`'s 4 in what the run may store
  into, apart from the return address, the run reaches the return address with the entries in `buf` (`dnBuf`: one
  store of `nbytes` bytes) and either the answer in `rax` or `errno` set and `rax` -1.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Close FV7z.Lseek
namespace FV7z.Gdn

/-- The `syscall`. -/
def psys : List Byte := [0x0f, 0x05]
theorem psys_0 : ∀ feat, Dec feat psys 0 (FV7z.mk .syscall 32 [] 2) := by dec_rfl
theorem w_25 : psys <+: gdn.drop 25 := by decide +kernel
theorem sys_25 (feat : Features) : Dec feat gdn 25 (FV7z.mk .syscall 32 [] 2) :=
  Dec.shift (j := 25) (k := 0) (psys_0 feat) w_25 (Nat.zero_le _)

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_35 : pret <+: gdn.drop 35 := by decide +kernel
theorem ret_35 (feat : Features) : Dec feat gdn 35 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 35) (k := 0) (pret_0 feat) w_35 (Nat.zero_le _)
theorem w_59 : pret <+: gdn.drop 59 := by decide +kernel
theorem ret_59 (feat : Features) : Dec feat gdn 59 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 59) (k := 0) (pret_0 feat) w_59 (Nat.zero_le _)

/-- The state after the `syscall` of `getdents64` from the state `S` at it, the kernel's result `r`. -/
abbrev gdS (S : State) (r : DnOut) : State := sysSt (dnSt S r) 2 r.ret

/-- The event of `getdents64` from `__getdents` called with registers `g`, the kernel's result `r`. -/
abbrev gdE (g : Gprs) (r : DnOut) : Event := ⟨217, [g.rdi, g.rsi, g.rdx, g.r10, g.r8, g.r9], r.ret, [], dnBytes r⟩

variable {F : Footprint} {Wl : List Rgn}

/-- To the `syscall`, `nbytes` at most `INT_MAX` (the `cmova` not taken): `eax` is 217. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hc : g.rdx.toNat ≤ 2147483647) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 25 ∧ g' = g.set 0 217 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have hc' : decide (rdx.toNat ≤ 2147483647) = true := decide_eq_true hc
  wpx [W_0, o0, Op.cmov64, be_imm (w := 64) _ 2147483647 (by decide), hc', Bool.not_true, Bool.false_eq_true]
  first | rfl | exact ⟨rfl, rfl⟩ | exact ⟨rfl, rfl, rfl⟩ | trivial

/-- From the `syscall` to the first `ret`, the kernel's answer `rax` not an error. -/
theorem vc_27_ok {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (he : ¬ CloseErr g.rax) :
    W_27 fb F Wl (fun j' g' _ V' => j' = 35 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have he' : decide (CloseErr rax) = false := decide_eq_false he
  wpx [W_27, W_40, o1, o2, Op.stf, ja_cmp, he']
  first
  | exact fun h => absurd h (by decide)
  | exact ⟨fun h => absurd h (by decide), fun _ => ⟨rfl, rfl, rfl⟩⟩

/-- From the `syscall` to the second `ret`, the kernel's answer `rax` an error: `errno` set, `rax` -1. -/
theorem vc_27_err {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (he : CloseErr g.rax)
    (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) :
    W_27 fb F Wl (fun j' g' _ V' => j' = 59 ∧ g' = lsErrG g ∧ V' = Vst V (errnoAt fb) (errnoB g.rax)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have he' : decide (CloseErr rax) = true := decide_eq_true he
  wpx [W_27, W_40, o1, o2, Op.stf, ja_cmp, he']
  exact ⟨⟨fe, rfl⟩, fun h => absurd h (by decide)⟩

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t : Nat} {V : Addr → Byte}

/-- `__getdents (fd, buf, nbytes)` from its entry to the return address, `nbytes` (`rdx`) at most `INT_MAX`, `buf`'s
`nbytes` bytes in what the run may store into and apart from the return address. The run goes on from `gdS S r`, the
state after the `syscall`, a new start: from `S`, the state at the `syscall` (`rax` 217, the registers else as at the
entry, the bytes as at the entry), the kernel's `getdents64` with result `r` (`dentsRes`, the stream of answers at
some `t₁`). It reaches the return address with the return address popped and the entries in `buf` (`dnBuf`, one store
of `nbytes` bytes); if `r.ret` is not an error, `rax` = `r.ret`; if it is, `errno` = `-r.ret` and `rax` = -1
(`lsErrG`). -/
theorem gdn_ok {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hrs : s₀.thread.rseq = none) (hin : CodeIn L gdn_at gdn) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = gdn_at) (hc : X.cpu.gpr.rdx.toNat ≤ 2147483647)
    (hst : ∀ i < X.cpu.gpr.rdx.toNat, Foot Wl (X.cpu.gpr.rsi.add i))
    (hbf : X.cpu.gpr.rsi.toNat + X.cpu.gpr.rdx.toNat ≤ 2 ^ 64)
    (hsb : X.cpu.gpr.rsi.toNat + X.cpu.gpr.rdx.toNat ≤ X.cpu.gpr.rsp.toNat ∨
      X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rsi.toNat)
    (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) (hfe : (errnoAt fb).toNat + 4 ≤ 2 ^ 64)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) (hsp : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hsa : (errnoAt fb).toNat + 4 ≤ X.cpu.gpr.rsp.toNat ∨ X.cpu.gpr.rsp.toNat + 8 ≤ (errnoAt fb).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (k : ∀ (S : State) (t₁ : Nat) (r : DnOut), r = dentsRes o t₁ S → KeptW Wl s₀ S →
      Agree F S.proc.mm.mem V → S.cpu.gpr = X.cpu.gpr.set 0 217 → Seg prof F Wl L (gdS S r) o →
      ∀ Z t', KeptW Wl (gdS S r) Z → Z.cpu.rip = e₂.add j₂ →
      (¬ CloseErr r.ret →
        Agree F Z.proc.mm.mem (Vst V X.cpu.gpr.rsi (dnBuf V X.cpu.gpr.rsi X.cpu.gpr.rdx.toNat r)) ∧
        Z.cpu.gpr = (gdS S r).cpu.gpr.set 4 (X.cpu.gpr.rsp + 8)) →
      (CloseErr r.ret → Agree F Z.proc.mm.mem
          (Vst (Vst V X.cpu.gpr.rsi (dnBuf V X.cpu.gpr.rsi X.cpu.gpr.rdx.toNat r)) (errnoAt fb) (errnoB r.ret)) ∧
        Z.cpu.gpr = (lsErrG (gdS S r).cpu.gpr).set 4 (X.cpu.gpr.rsp + 8)) →
      GoG prof L o (gev ++ [gdE X.cpu.gpr r]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  -- to the `syscall`
  refine (c_0 prof fb).run c hfs hin (fun j' g' _ V' => j' = 25 ∧ g' = X.cpu.gpr.set 0 217 ∧ V' = V) hK hA
    (by rw [addr_add_zero]; exact hrip) (vc_0 hc) ?_
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  have hsi : Y.cpu.gpr.rsi = X.cpu.gpr.rsi := by rw [hgY]; rfl
  have hdx : Y.cpu.gpr.rdx = X.cpu.gpr.rdx := by rw [hgY]; rfl
  have h32 : arg32 X.cpu.gpr.rdx = X.cpu.gpr.rdx.toNat := Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hc (by decide))
  -- `getdents64`
  refine c.s_getdents_re hrs hKY hAY hin (lt_len (by decide)) hrY (sys_25 _) (by rw [hgY]; rfl)
    (by rw [hsi, hdx, h32]; exact hst) ?_
  intro M t₂ t₃ hKM hAM c₁ hA₁
  have hev : dnEv Y.cpu.gpr (dentsRes o t₂ (Y.withMem M)) = gdE X.cpu.gpr (dentsRes o t₂ (Y.withMem M)) := by
    rw [hgY]; rfl
  rw [hev]
  have hsum : ((dentsRes o t₂ (Y.withMem M)).es.map Dirent.reclen).sum ≤ X.cpu.gpr.rdx.toNat := by
    have h1 := dentsRes_sum (o := o) (t := t₂) (s := Y.withMem M)
    have h2 : arg32 (Y.withMem M).cpu.gpr.rdx = X.cpu.gpr.rdx.toNat := by
      show arg32 Y.cpu.gpr.rdx = _
      rw [hdx, h32]
    omega
  rw [hsi, dn_one hsum hbf] at hA₁
  generalize hr : dentsRes o t₂ (Y.withMem M) = r at c₁ hA₁ hsum ⊢
  have hfs₁ : (gdS (Y.withMem M) r).cpu.seg.fsBase = fb := by
    show Y.cpu.seg.fsBase = fb
    rw [hKY.seg]
    exact hfs
  have hrip₁ : (gdS (Y.withMem M) r).cpu.rip = gdn_at.add 27 := rip_add hrY M 2
  have hgS : (Y.withMem M).cpu.gpr = X.cpu.gpr.set 0 217 := hgY
  have hspS : (gdS (Y.withMem M) r).cpu.gpr.rsp = X.cpu.gpr.rsp := by
    show Y.cpu.gpr.rsp = _
    rw [hgY]
    rfl
  have hr0 : (gdS (Y.withMem M) r).cpu.gpr.rax = r.ret := rfl
  -- the buffer is apart from the return address
  have hbl : (dnBuf V X.cpu.gpr.rsi X.cpu.gpr.rdx.toNat r).length = X.cpu.gpr.rdx.toNat := by
    rw [List.length_map, byteAddrs_len]
  have hra₁ : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map
      (Vst V X.cpu.gpr.rsi (dnBuf V X.cpu.gpr.rsi X.cpu.gpr.rdx.toNat r))) = e₂.add j₂ := by
    rw [Tun.rd_Vst V X.cpu.gpr.rsi _ X.cpu.gpr.rsp 8 (by rw [hbl]; exact hbf) hsp (by rw [hbl]; exact hsb)]
    exact hra
  have kk := fun Z t' => k (Y.withMem M) t₂ r hr.symm hKM hAM hgS c₁ Z t'
  -- to a `ret`
  by_cases he : CloseErr r.ret
  · refine (c_27 prof fb).run c₁ hfs₁ hin
      (fun j' g' _ V' => j' = 59 ∧ g' = lsErrG (gdS (Y.withMem M) r).cpu.gpr ∧
        V' = Vst (Vst V X.cpu.gpr.rsi (dnBuf V X.cpu.gpr.rsi X.cpu.gpr.rdx.toNat r)) (errnoAt fb)
          (errnoB (gdS (Y.withMem M) r).cpu.gpr.rax))
      (KeptW.refl _ _) hA₁ hrip₁ (vc_27_err (by rw [hr0]; exact he) fe) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Z t₄ hKZ hAZ hrZ hgZ -
    have hspZ : Z.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgZ, lsErrG_rsp, hspS]
    refine c₁.s_ret hKZ hAZ hin (lt_len (by decide)) hrZ (ret_59 _) (fun i hi => by rw [hspZ]; exact hl i hi)
      hin₂ h₂ ?_ ?_
    · have hb : (errnoB (gdS (Y.withMem M) r).cpu.gpr.rax).length = 4 := toBytesLE_length _ _
      have h1 : (errnoAt fb).toNat + (errnoB (gdS (Y.withMem M) r).cpu.gpr.rax).length ≤ 2 ^ 64 := by
        rw [hb]; exact hfe
      have h2 : (errnoAt fb).toNat + (errnoB (gdS (Y.withMem M) r).cpu.gpr.rax).length ≤ X.cpu.gpr.rsp.toNat ∨
          X.cpu.gpr.rsp.toNat + 8 ≤ (errnoAt fb).toNat := by rw [hb]; exact hsa
      rw [hspZ, Tun.rd_Vst (Vst V X.cpu.gpr.rsi (dnBuf V X.cpu.gpr.rsi X.cpu.gpr.rdx.toNat r)) (errnoAt fb)
        (errnoB (gdS (Y.withMem M) r).cpu.gpr.rax) X.cpu.gpr.rsp 8 h1 hsp h2]
      exact hra₁
    rintro Z' t₅ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    rw [hr0] at hAZ'
    refine kk Z' t₅ hKZ' hrZ' (fun h => absurd he h) fun _ => ⟨hAZ', ?_⟩
    rw [hgZ', hgZ, lsErrG_rsp, hspS]
    all_goals rfl
  · refine (c_27 prof fb).run c₁ hfs₁ hin (fun j' g' _ V' => j' = 35 ∧ g' = (gdS (Y.withMem M) r).cpu.gpr ∧
        V' = Vst V X.cpu.gpr.rsi (dnBuf V X.cpu.gpr.rsi X.cpu.gpr.rdx.toNat r))
      (KeptW.refl _ _) hA₁ hrip₁ (vc_27_ok (by rw [hr0]; exact he)) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ Z t₄ hKZ hAZ hrZ hgZ -
    subst V₂
    have hspZ : Z.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgZ, hspS]
    refine c₁.s_ret hKZ hAZ hin (lt_len (by decide)) hrZ (ret_35 _) (fun i hi => by rw [hspZ]; exact hl i hi)
      hin₂ h₂ (by rw [hspZ]; exact hra₁) ?_
    rintro Z' t₅ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    refine kk Z' t₅ hKZ' hrZ' (fun _ => ⟨hAZ', ?_⟩) fun h => absurd h he
    rw [hgZ', hgZ, hspS]
    all_goals rfl

end FV7z.Gdn
