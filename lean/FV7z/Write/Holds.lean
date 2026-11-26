import FV7z.Write.Cuts
import FV7z.Lemmas.SysWrite
import FV7z.Tun.Inv
/-!
# `__libc_write` writes bytes to a descriptor (PLAN.md §M, M1)

glibc 2.31's `__libc_write (fd, buf, n)` at `0x5ff270` in `7zzs`: in a process of one thread (`multiple_threads`,
`fs:0x18`, is 0) the `syscall` `write`, then the result returned, or `errno` (`fs:-0x48`) set to the error and -1
returned. Two pieces of the code: to the `syscall` (21) and from after it (23) to one of the two `ret`s (31, 131); the
`syscall` itself is `Seg.s_write` (`Lemmas/SysWrite.lean`), for an open file not on the pages of a file and a buffer in
the footprint's data.

- `WrErr r`: the kernel's answer `r` is an error (`-4095 ≤ r < 0`, as `cmp rax, -4096; ja` reads it).
- `errG`, `errnoB`: the registers and the bytes of `errno` after the error path.
- `write_ok`: called with `multiple_threads` 0, `errno`'s 4 bytes in what the run may store into, the run reaches the
  return address with either the answer in `rax` or `errno` set and `rax` -1; or the run ends as the signal the kernel
  sends (`SIGPIPE`, `SIGXFSZ`) decides (`kp`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Write

/-- The `syscall`. -/
def psys : List Byte := [0x0f, 0x05]
theorem psys_0 : ∀ feat, Dec feat psys 0 (FV7z.mk .syscall 32 [] 2) := by dec_rfl
theorem w_21 : psys <+: wrt.drop 21 := by decide +kernel
theorem sys_21 (feat : Features) : Dec feat wrt 21 (FV7z.mk .syscall 32 [] 2) :=
  Dec.shift (j := 21) (k := 0) (psys_0 feat) w_21 (Nat.zero_le _)

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_31 : pret <+: wrt.drop 31 := by decide +kernel
theorem ret_31 (feat : Features) : Dec feat wrt 31 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 31) (k := 0) (pret_0 feat) w_31 (Nat.zero_le _)
theorem w_131 : pret <+: wrt.drop 131 := by decide +kernel
theorem ret_131 (feat : Features) : Dec feat wrt 131 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 131) (k := 0) (pret_0 feat) w_131 (Nat.zero_le _)

/-- The kernel's answer is an error: above `-4096` as an unsigned number. -/
def WrErr (r : BitVec 64) : Prop := 18446744073709547520 < r.toNat

instance (r : BitVec 64) : Decidable (WrErr r) := inferInstanceAs (Decidable (_ < _))

/-- `errno`'s place: `fs:-0x48`. -/
abbrev errnoAt (fb : Addr) : Addr := fb + 18446744073709551544#64

/-- The bytes of `errno` after the error `r`: its negation, 32 bits. -/
abbrev errnoB (r : BitVec 64) : List Byte := toBytesLE (0 - r.setWidth 32) 4

/-- The registers after the error path: `rdx` is `-0x48`, `rax` is -1 (64 bits). -/
def errG (g : Gprs) : Gprs := (g.set 2 18446744073709551544#64).set 0 18446744073709551615#64

theorem errG_rsp (g : Gprs) : (errG g).rsp = g.rsp := by cases g; rfl

/-- The event of `write` from `__libc_write` called with registers `g`, the kernel's answer `v`, the bytes `out`
taken. -/
abbrev wrtEv (g : Gprs) (v : BitVec 64) (out : List Byte) : Event :=
  ⟨1, [g.rdi, g.rsi, g.rdx, g.r10, g.r8, g.r9], v, out, []⟩

variable {F : Footprint} {Wl : List Rgn}

/-- To the `syscall`: `multiple_threads` is 0, so no jump; `eax` is 1. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hmt : ofBytesLE 32 ((byteAddrs (fb + 24#64) 4).map V) = 0) (fm : ∀ i < 4, Foot F.data ((fb + 24#64).add i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 21 ∧ g' = g.set 0 1 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, W_16, o0, o1, Op.ldf, hmt]
  refine ⟨fm, fun h => absurd h (by decide), fun _ => ?_⟩
  rfl

/-- How `cmp rax, -4096; ja` reads the kernel's answer. -/
theorem ja_cmp (x : BitVec 64) :
    (!(decide (x.toNat < 18446744073709547520) || decide (x = 18446744073709547520#64))) = decide (WrErr x) := by
  by_cases h1 : x.toNat < 18446744073709547520
  · have h3 : ¬ WrErr x := by unfold WrErr; omega
    rw [decide_eq_true h1, decide_eq_false h3]
    rfl
  · by_cases h2 : x = 18446744073709547520#64
    · have h3 : ¬ WrErr x := by unfold WrErr; rw [h2]; decide
      rw [decide_eq_false h1, decide_eq_true h2, decide_eq_false h3]
      rfl
    · have h3 : WrErr x := by
        unfold WrErr
        have : x.toNat ≠ 18446744073709547520 := fun e => h2 (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
        omega
      rw [decide_eq_false h1, decide_eq_false h2, decide_eq_true h3]
      rfl

/-- From the `syscall` to the first `ret`, the kernel's answer `rax` not an error. -/
theorem vc_23_ok {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (he : ¬ WrErr g.rax) :
    W_23 fb F Wl (fun j' g' _ V' => j' = 31 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have he' : decide (WrErr rax) = false := decide_eq_false he
  wpx [W_23, W_112, o2, o3, Op.stf, ja_cmp, he']
  first
  | exact fun h => absurd h (by decide)
  | exact ⟨fun h => absurd h (by decide), fun _ => ⟨rfl, rfl, rfl⟩⟩

/-- From the `syscall` to the second `ret`, the kernel's answer `rax` an error: `errno` set, `rax` -1. -/
theorem vc_23_err {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (he : WrErr g.rax)
    (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) :
    W_23 fb F Wl (fun j' g' _ V' => j' = 131 ∧ g' = errG g ∧ V' = Vst V (errnoAt fb) (errnoB g.rax)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have he' : decide (WrErr rax) = true := decide_eq_true he
  wpx [W_23, W_112, o2, o3, Op.stf, ja_cmp, he']
  exact ⟨⟨fe, rfl⟩, fun h => absurd h (by decide)⟩

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t : Nat} {V : Addr → Byte}

/-- `__libc_write (fd, buf, n)` from its entry to the return address, in a process of one thread (`multiple_threads`
0), `fd` an open file `f` not on the pages of a file, `buf`'s `n` bytes in the footprint's data: the `syscall` `write`
from `Y` (the registers at the entry with `eax` 1) returns `v` having taken the bytes `out` (`WrOk`), and the run goes
on to the return address with the return address popped and, if `v` is not an error, `rax` = `v`; if it is,
`errno` = `-v` and `rax` = -1 (`errG`). Or the kernel sends a signal (`SIGPIPE`, `SIGXFSZ`), and the run goes on or
ends as `sigEnd` says (`kp`). -/
theorem write_ok {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L wrt_at wrt) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = wrt_at)
    (hmt : ofBytesLE 32 ((byteAddrs (fb + 24#64) 4).map V) = 0) (fm : ∀ i < 4, Foot F.data ((fb + 24#64).add i))
    (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) (hfe : (errnoAt fb).toNat + 4 ≤ 2 ^ 64)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) (hsp : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hsa : (errnoAt fb).toNat + 4 ≤ X.cpu.gpr.rsp.toNat ∨ X.cpu.gpr.rsp.toNat + 8 ≤ (errnoAt fb).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    {f : OpenFile} (hf : s₀.proc.files.desc (X.cpu.gpr.rdi.toNat % 2 ^ 32) = some f) (hw : f.writable = true)
    (hp : f.map.isPages = false) (hacc : accessOk prof.feat X.cpu.gpr.rsi X.cpu.gpr.rdx.toNat = true)
    (hn : X.cpu.gpr.rdx.toNat ≤ maxRwCount) (hb : ∀ i < X.cpu.gpr.rdx.toNat, Foot F.data (X.cpu.gpr.rsi.add i))
    (k : ∀ (Y Z : State) (v : BitVec 64) (out : List Byte) (t' : Nat),
      Y.cpu.gpr = X.cpu.gpr.set 0 1 → WrOk ((byteAddrs X.cpu.gpr.rsi X.cpu.gpr.rdx.toNat).map V) v out →
      KeptW Wl s₀ Z → Z.cpu.rip = e₂.add j₂ →
      (¬ WrErr v → Agree F Z.proc.mm.mem V ∧
        Z.cpu.gpr = ((sysGpr Y 2).set 0 v).set 4 (X.cpu.gpr.rsp + 8)) →
      (WrErr v → Agree F Z.proc.mm.mem (Vst V (errnoAt fb) (errnoB v)) ∧
        Z.cpu.gpr = (errG ((sysGpr Y 2).set 0 v)).set 4 (X.cpu.gpr.rsp + 8)) →
      GoG prof L o (gev ++ [wrtEv X.cpu.gpr v out]) gP gE Z t')
    (kp : ∀ (Y : State) (sig : Signal) (e : Nat) (M : Memory) (t' : Nat),
      Y.cpu.gpr = X.cpu.gpr.set 0 1 → Y.cpu.rip = wrt_at.add 21 → KeptW Wl s₀ (Y.withMem M) → Agree F M V →
      match sigEnd (nx (Y.withMem M) 2 (sysGpr Y 2) (rf0 Y)) sig e with
      | .running Z ev => GoG prof L o (gev ++ ev.toList) gP gE Z t'
      | .stopped out => gE out gev) :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof fb).run c hfs hin (fun j' g' _ V' => j' = 21 ∧ g' = X.cpu.gpr.set 0 1 ∧ V' = V) hK hA
    (by rw [addr_add_zero]; exact hrip) (vc_0 hmt fm) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hdi : Y.cpu.gpr.rdi = X.cpu.gpr.rdi := by rw [hgY]; rfl
  have hsi : Y.cpu.gpr.rsi = X.cpu.gpr.rsi := by rw [hgY]; rfl
  have hdx : Y.cpu.gpr.rdx = X.cpu.gpr.rdx := by rw [hgY]; rfl
  refine c.s_write hKY hAY hin (lt_len (by decide)) hrY (sys_21 _) (by rw [hgY]; rfl) (by rw [hdi]; exact hf) hw hp
    (by rw [hsi, hdx]; exact hacc) (by rw [hdx]; exact hn) (by rw [hsi, hdx]; exact hb) ?_
    (fun sig e M t' hKm hAm => kp Y sig e M t' hgY hrY hKm hAm)
  rintro v out hv Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
  rw [hsi, hdx] at hv
  have hev : wrEv Y.cpu.gpr v out = wrtEv X.cpu.gpr v out := by
    rw [hgY]
    rfl
  rw [hev]
  have hspY : ((sysGpr Y 2).set 0 v).rsp = X.cpu.gpr.rsp := by
    show Y.cpu.gpr.rsp = _
    rw [hgY]
    rfl
  have kk := fun Z' t' => k Y Z' v out t' hgY hv
  have hr0 : ((sysGpr Y 2).set 0 v).rax = v := rfl
  by_cases he : WrErr v
  · refine (c_23 prof fb).run c hfs hin
      (fun j' g' _ V' => j' = 131 ∧ g' = errG ((sysGpr Y 2).set 0 v) ∧
        V' = Vst V (errnoAt fb) (errnoB ((sysGpr Y 2).set 0 v).rax))
      hKZ hAZ hrZ (by rw [hgZ]; exact vc_23_err (by rw [hr0]; exact he) fe) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Z₁ t₄ hKZ₁ hAZ₁ hrZ₁ hgZ₁ -
    have hspZ : Z₁.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgZ₁, errG_rsp, hspY]
    refine c.s_ret hKZ₁ hAZ₁ hin (lt_len (by decide)) hrZ₁ (ret_131 _) (fun i hi => by rw [hspZ]; exact hl i hi)
      hin₂ h₂ ?_ ?_
    · have hb4 : (errnoB ((sysGpr Y 2).set 0 v).rax).length = 4 := toBytesLE_length _ _
      have h1 : (errnoAt fb).toNat + (errnoB ((sysGpr Y 2).set 0 v).rax).length ≤ 2 ^ 64 := by
        rw [hb4]; exact hfe
      have h2 : (errnoAt fb).toNat + (errnoB ((sysGpr Y 2).set 0 v).rax).length ≤ X.cpu.gpr.rsp.toNat ∨
          X.cpu.gpr.rsp.toNat + 8 ≤ (errnoAt fb).toNat := by rw [hb4]; exact hsa
      rw [hspZ, Tun.rd_Vst V (errnoAt fb) (errnoB ((sysGpr Y 2).set 0 v).rax) X.cpu.gpr.rsp 8 h1 hsp h2]
      exact hra
    rintro Z₂ t₅ hKZ₂ hAZ₂ ⟨hrZ₂, hgZ₂⟩
    rw [hr0] at hAZ₂
    refine kk Z₂ t₅ hKZ₂ hrZ₂ (fun h => absurd he h) fun _ => ⟨hAZ₂, ?_⟩
    (rw [hgZ₂, hgZ₁, errG_rsp, hspY]) <;> rfl
  · refine (c_23 prof fb).run c hfs hin (fun j' g' _ V' => j' = 31 ∧ g' = (sysGpr Y 2).set 0 v ∧ V' = V)
      hKZ hAZ hrZ (by rw [hgZ]; exact vc_23_ok (by rw [hr0]; exact he)) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ Z₁ t₄ hKZ₁ hAZ₁ hrZ₁ hgZ₁ -
    subst V₂
    have hspZ : Z₁.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgZ₁, hspY]
    refine c.s_ret hKZ₁ hAZ₁ hin (lt_len (by decide)) hrZ₁ (ret_31 _) (fun i hi => by rw [hspZ]; exact hl i hi)
      hin₂ h₂ (by rw [hspZ]; exact hra) ?_
    rintro Z₂ t₅ hKZ₂ hAZ₂ ⟨hrZ₂, hgZ₂⟩
    refine kk Z₂ t₅ hKZ₂ hrZ₂ (fun _ => ⟨hAZ₂, ?_⟩) fun h => absurd h he
    (rw [hgZ₂, hgZ₁, hspY]) <;> rfl

end FV7z.Write
