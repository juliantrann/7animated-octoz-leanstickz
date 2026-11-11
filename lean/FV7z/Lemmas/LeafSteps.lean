import FV7z.Lemmas.Leaf
import FV7z.Lemmas.InsRip
/-!
# A call of a leaf function, an instruction at a time (PLAN.md G2, "Dispatch theo CPUID")

`Memcmp/Steps.lean` for any `leaf` contract (`Lemmas/Leaf.lean`), for the forms of instruction glibc's IFUNC resolvers
use (`Lemmas/Ins.lean`, `Lemmas/InsRip.lean`): from a state `X` at the code's `k`-th byte, where the code decodes to the
instruction (`Dec`), the rest of the run goes on from every state `Y` it may leave, given what `Y`'s registers (and
the flags the code tests) are in terms of `X`'s. A load `[rip + d]` names a region the contract reads and the offset
in it, whose bytes are as at the call.
-/
namespace FV7z.Leaf
open ZellicX86 Decode

@[simp] theorem withMem_cpu (s : State) (M : Memory) : (s.withMem M).cpu = s.cpu := rfl

@[simp] theorem set_rax (g : Gprs) (v : BitVec 64) : g.set (regOf 0) v = { g with rax := v } := rfl
@[simp] theorem set_rcx (g : Gprs) (v : BitVec 64) : g.set (regOf 1) v = { g with rcx := v } := rfl
@[simp] theorem set_rdx (g : Gprs) (v : BitVec 64) : g.set (regOf 2) v = { g with rdx := v } := rfl
@[simp] theorem set_rsi (g : Gprs) (v : BitVec 64) : g.set (regOf 6) v = { g with rsi := v } := rfl
@[simp] theorem set_r8 (g : Gprs) (v : BitVec 64) : g.set (regOf 8) v = { g with r8 := v } := rfl
@[simp] theorem set_rdi (g : Gprs) (v : BitVec 64) : g.set (regOf 7) v = { g with rdi := v } := rfl

theorem cond4 (f : Rflags) : f.cond 4 = f.zf := rfl
theorem cond5 (f : Rflags) : f.cond 5 = !f.zf := rfl

variable {prof : Profile} {R : State → List Rgn} {P : State → Prop} {Q : State → BitVec 64 → Prop}
  {code : List Byte} {e : Addr} {L : List (Addr × List Byte)} {s₀ : State} {ra : Addr} {o : Oracle} {X : State}
  {t k : Nat}

/-- The rest of the run, from every state the step to the code's `k`-th byte may leave, of which `Pr` holds. -/
abbrev Then (prof : Profile) (R : State → List Rgn) (P : State → Prop) (Q : State → BitVec 64 → Prop)
    (L : List (Addr × List Byte)) (s₀ : State) (ra : Addr) (o : Oracle) (e : Addr) (k : Nat) (Pr : State → Prop) :
    Prop :=
  ∀ Y t', Kept s₀ Y → Y.cpu.rip = e.add k → Pr Y → Go prof R P Q L s₀ ra o Y t'

theorem rip_add (hrip : X.cpu.rip = e.add k) (M : Memory) (len : Nat) :
    (X.withMem M).cpu.rip.add len = e.add (k + len) := by
  show X.cpu.rip.add len = _
  rw [hrip, addr_add_add]

theorem addr_rel {e : Addr} {k len rel tgt : Nat} (h : (k + len + rel) % 2 ^ 64 = tgt % 2 ^ 64) :
    (e.add k).add len + BitVec.ofNat 64 rel = e.add tgt := by
  simp only [Addr.add]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem calleeOf {s₀ X : State} (h : X.cpu.gpr.rbx = s₀.cpu.gpr.rbx ∧ X.cpu.gpr.rsp = s₀.cpu.gpr.rsp ∧
    X.cpu.gpr.rbp = s₀.cpu.gpr.rbp ∧ X.cpu.gpr.r12 = s₀.cpu.gpr.r12 ∧ X.cpu.gpr.r13 = s₀.cpu.gpr.r13 ∧
    X.cpu.gpr.r14 = s₀.cpu.gpr.r14 ∧ X.cpu.gpr.r15 = s₀.cpu.gpr.r15) : Callee s₀ X := h

namespace Call

/-- A step of `len` bytes to a state of which `Pr` holds. -/
theorem next (c : Call prof R P Q code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {len : Nat} {Pr : State → Prop}
    (hrun : ∀ M, Kept s₀ (X.withMem M) → X.cpu.rflags.tf = false → X.cpu.rflags.ac = false →
      ∃ Y t', (instruction prof (X.withMem M)).runStream o (t + 1) = (.running Y none, t') ∧ Kept s₀ Y ∧
        Y.cpu.rip = e.add (k + len) ∧ Pr Y)
    (k' : Then prof R P Q L s₀ ra o e (k + len) Pr) : Go prof R P Q L s₀ ra o X t :=
  c.step hK hk hrip fun M _ hK' htf hac => by
    obtain ⟨Y, t', hr, hKY, hY, hP⟩ := hrun M hK' htf hac
    exact ⟨Y, t', hr, k' Y t' hKY hY hP⟩

/-- The address `[rip + d]` of an instruction of `len` bytes at the code's `k`-th byte, the `a`-th byte of a region
the contract reads: the `n` bytes there can be read, and are as at the call. -/
theorem ripRead (c : Call prof R P Q code e L s₀ ra o) {Y : State} (hK : Kept s₀ Y) (hrip : Y.cpu.rip = e.add k)
    {d len : Nat} {rg : Rgn} (hr : rg ∈ R s₀) {a n : Nat}
    (ha : e.add (k + len) + BitVec.ofNat 64 d = rg.base.add a) (hn : a + n ≤ rg.len) :
    Readable prof Y (eaR Y len d) n ∧
      readBytes Y.proc.mm.mem (eaR Y len d) n = readBytes s₀.proc.mm.mem (rg.base.add a) n := by
  have h : eaR Y len d = rg.base.add a := by
    show Y.cpu.rip.add len + _ = _
    rw [hrip, addr_add_add]; exact ha
  rw [h]
  exact c.read hK hr hn

theorem s_endbr (c : Call prof R P Q code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {len : Nat} (hd : Dec prof.feat code k (FV7z.mk .endbr64 32 [] len))
    (k' : Then prof R P Q L s₀ ra o e (k + len) fun Y => Y.cpu.gpr = X.cpu.gpr) :
    Go prof R P Q L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf _ => ⟨_, _, endbr (s := X.withMem M) htf (c.dec hK' hrip hd),
    hK'.nx rfl rfl rfl, rip_add hrip M len, rfl⟩) k'

theorem s_mov_ri64 (c : Call prof R P Q code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {r imm len : Nat}
    (hd : Dec prof.feat code k (FV7z.mk .mov 64 [gr 64 r, .imm 64 imm] len))
    (k' : Then prof R P Q L s₀ ra o e (k + len) fun Y => Y.cpu.gpr = X.cpu.gpr.set (regOf r) (BitVec.ofNat 64 imm)) :
    Go prof R P Q L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf _ => ⟨_, _, mov_ri64 (s := X.withMem M) htf (c.dec hK' hrip hd),
    hK'.nx rfl rfl rfl, rip_add hrip M len, rfl⟩) k'

/-- `lea r64, [rip + d]`, the address `v`. -/
theorem s_lea_rip (c : Call prof R P Q code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {r d len : Nat}
    (hd : Dec prof.feat code k (FV7z.mk .lea 64 [gr 64 r, .mem (mrip d 0)] len)) {v : Addr}
    (hv : e.add (k + len) + BitVec.ofNat 64 d = v)
    (k' : Then prof R P Q L s₀ ra o e (k + len) fun Y => Y.cpu.gpr = X.cpu.gpr.set (regOf r) v ∧
      Y.cpu.rflags.zf = X.cpu.rflags.zf) :
    Go prof R P Q L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf _ => ⟨_, _, lea_rip (s := X.withMem M) htf (c.dec hK' hrip hd),
    hK'.nx rfl rfl rfl, rip_add hrip M len, by
      show X.cpu.gpr.set (regOf r) (X.cpu.rip.add len + _) = _
      rw [hrip, addr_add_add, hv], rfl⟩) k'

theorem s_cmp_ri (c : Call prof R P Q code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {w r imm len : Nat}
    (hd : Dec prof.feat code k (FV7z.mk .cmp w [gr w r, .imm w imm] len))
    (k' : Then prof R P Q L s₀ ra o e (k + len) fun Y => Y.cpu.gpr = X.cpu.gpr ∧
      Y.cpu.rflags = subF (rf0 X) (rv X w r) (BitVec.ofNat w imm)) :
    Go prof R P Q L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf _ => ⟨_, _, cmp_ri (s := X.withMem M) htf (c.dec hK' hrip hd),
    hK'.nx rfl rfl rfl, rip_add hrip M len, rfl, rfl⟩) k'

theorem s_cmp_rr (c : Call prof R P Q code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {w r q len : Nat}
    (hd : Dec prof.feat code k (FV7z.mk .cmp w [gr w r, gr w q] len))
    (k' : Then prof R P Q L s₀ ra o e (k + len) fun Y => Y.cpu.gpr = X.cpu.gpr ∧
      Y.cpu.rflags = subF (rf0 X) (rv X w r) (rv X w q)) :
    Go prof R P Q L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf _ => ⟨_, _, cmp_rr (s := X.withMem M) htf (c.dec hK' hrip hd),
    hK'.nx rfl rfl rfl, rip_add hrip M len, rfl, rfl⟩) k'

theorem s_jcc (c : Call prof R P Q code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {cc : Cond} {rel len tgt : Nat}
    (hd : Dec prof.feat code k (FV7z.mk (.jcc cc) 64 [.rel rel] len))
    (htgt : (k + len + rel) % 2 ^ 64 = tgt % 2 ^ 64) (ht : tgt < code.length)
    (taken : X.cpu.rflags.cond cc = true → Then prof R P Q L s₀ ra o e tgt fun Y => Y.cpu.gpr = X.cpu.gpr)
    (fall : X.cpu.rflags.cond cc = false → Then prof R P Q L s₀ ra o e (k + len) fun Y => Y.cpu.gpr = X.cpu.gpr) :
    Go prof R P Q L s₀ ra o X t := by
  cases hcc : X.cpu.rflags.cond cc
  · exact c.next hK hk hrip (fun M hK' htf _ => ⟨_, _, jcc_n (s := X.withMem M) htf (c.dec hK' hrip hd) hcc,
      hK'.nx rfl rfl rfl, rip_add hrip M len, rfl⟩) (fall hcc)
  · refine c.step hK hk hrip fun M _ hK' htf _ => ?_
    have hca := ((hK'.codeAt c.call.foot c.call.ready.rseq c.code) tgt ht).1
    have ha : (X.withMem M).cpu.rip.add len + BitVec.ofNat 64 rel = e.add tgt := by
      rw [withMem_cpu, hrip]; exact addr_rel htgt
    exact ⟨_, _, jcc_t (s := X.withMem M) htf (c.dec hK' hrip hd) hcc (by rw [ha]; exact hca),
      taken hcc _ _ (hK'.upd rfl rfl rfl) ha rfl⟩

theorem s_test_ri32 (c : Call prof R P Q code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {r imm len : Nat}
    (hd : Dec prof.feat code k (FV7z.mk .test 32 [gr 32 r, .imm 32 imm] len))
    (k' : Then prof R P Q L s₀ ra o e (k + len) fun Y => Y.cpu.gpr = X.cpu.gpr ∧
      Y.cpu.rflags.zf = (rv X 32 r &&& BitVec.ofNat 32 imm == 0)) :
    Go prof R P Q L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf _ => by
    obtain ⟨af, t', hr⟩ := test_ri32 (s := X.withMem M) (o := o) (t := t + 1) (r := r) (imm := imm) htf
      (c.dec hK' hrip hd)
    exact ⟨_, _, hr, hK'.nx rfl rfl rfl, rip_add hrip M len, rfl, rfl⟩) k'

/-- `test r32, r32'`. -/
theorem s_test_rr32 (c : Call prof R P Q code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {r q len : Nat}
    (hd : Dec prof.feat code k (FV7z.mk .test 32 [gr 32 r, gr 32 q] len))
    (k' : Then prof R P Q L s₀ ra o e (k + len) fun Y => Y.cpu.gpr = X.cpu.gpr) :
    Go prof R P Q L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf _ => by
    obtain ⟨af, t', hr⟩ := test_rr32 (s := X.withMem M) (o := o) (t := t + 1) (r := r) (q := q) htf
      (c.dec hK' hrip hd)
    exact ⟨_, _, hr, hK'.nx rfl rfl rfl, rip_add hrip M len, rfl⟩) k'

/-- `and r8h, imm8` (`ah`, …, of general register `r`). -/
theorem s_and_h8i (c : Call prof R P Q code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {r imm len : Nat}
    (hd : Dec prof.feat code k (FV7z.mk .and 8 [gh r, .imm 8 imm] len))
    (k' : Then prof R P Q L s₀ ra o e (k + len) fun Y =>
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) ((X.cpu.gpr.get (regOf r) &&& ~~~(BitVec.ofNat 64 ((2 ^ 8 - 1) * 2 ^ 8))) |||
        (((X.cpu.gpr.get (regOf r) >>> 8).setWidth 8 &&& BitVec.ofNat 8 imm).setWidth 64 <<< 8)) ∧
      Y.cpu.rflags.zf = ((X.cpu.gpr.get (regOf r) >>> 8).setWidth 8 &&& BitVec.ofNat 8 imm == 0)) :
    Go prof R P Q L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf _ => by
    obtain ⟨af, t', hr⟩ := and_h8i (s := X.withMem M) (o := o) (t := t + 1) (r := r) (imm := imm) htf
      (c.dec hK' hrip hd)
    exact ⟨_, _, hr, hK'.nx rfl rfl rfl, rip_add hrip M len, rfl, rfl⟩) k'

theorem s_cmov (c : Call prof R P Q code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {cc : Cond} {r q len : Nat}
    (hd : Dec prof.feat code k (FV7z.mk (.cmovcc cc) 64 [gr 64 r, gr 64 q] len))
    (k' : Then prof R P Q L s₀ ra o e (k + len) fun Y =>
      Y.cpu.gpr = if X.cpu.rflags.cond cc then X.cpu.gpr.set (regOf r) (X.cpu.gpr.get (regOf q)) else X.cpu.gpr) :
    Go prof R P Q L s₀ ra o X t := by
  cases hcc : X.cpu.rflags.cond cc
  · exact c.next hK hk hrip (fun M hK' htf _ => ⟨_, _, cmov_n (s := X.withMem M) htf (c.dec hK' hrip hd) hcc,
      hK'.nx rfl rfl rfl, rip_add hrip M len, by simp [hcc]⟩) k'
  · exact c.next hK hk hrip (fun M hK' htf _ => ⟨_, _, cmov_t (s := X.withMem M) htf (c.dec hK' hrip hd) hcc,
      hK'.nx rfl rfl rfl, rip_add hrip M len, by simp [hcc, rv, BitVec.setWidth_eq]⟩) k'

/-- `mov r32, dword [rip + d]`, the `a`-th byte of a region the contract reads. -/
theorem s_mov32_rip (c : Call prof R P Q code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {r d len : Nat}
    (hd : Dec prof.feat code k (FV7z.mk .mov 32 [gr 32 r, .mem (mrip d 32)] len))
    {rg : Rgn} (hr : rg ∈ R s₀) {a : Nat} (ha : e.add (k + len) + BitVec.ofNat 64 d = rg.base.add a)
    (hn : a + 4 ≤ rg.len)
    (k' : Then prof R P Q L s₀ ra o e (k + len) fun Y =>
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) ((ofBytesLE 32 (readBytes s₀.proc.mm.mem (rg.base.add a) 4)).setWidth 64)) :
    Go prof R P Q L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf hac => by
    obtain ⟨h1, h2⟩ := c.ripRead (Y := X.withMem M) hK' hrip hr ha hn
    refine ⟨_, _, mov_r32_rip (s := X.withMem M) htf hac (c.dec hK' hrip hd) h1, hK'.nx rfl rfl rfl,
      rip_add hrip M len, ?_⟩
    rw [nx_gpr, h2]; rfl) k'

/-- `and r64, qword [rip + d]`, the `a`-th byte of a region the contract reads. -/
theorem s_and64_rip (c : Call prof R P Q code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {r d len : Nat}
    (hd : Dec prof.feat code k (FV7z.mk .and 64 [gr 64 r, .mem (mrip d 64)] len))
    {rg : Rgn} (hr : rg ∈ R s₀) {a : Nat} (ha : e.add (k + len) + BitVec.ofNat 64 d = rg.base.add a)
    (hn : a + 8 ≤ rg.len)
    (k' : Then prof R P Q L s₀ ra o e (k + len) fun Y =>
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) (X.cpu.gpr.get (regOf r) &&&
        ofBytesLE 64 (readBytes s₀.proc.mm.mem (rg.base.add a) 8)) ∧
      Y.cpu.rflags.zf = (X.cpu.gpr.get (regOf r) &&& ofBytesLE 64 (readBytes s₀.proc.mm.mem (rg.base.add a) 8) == 0)) :
    Go prof R P Q L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf hac => by
    obtain ⟨h1, h2⟩ := c.ripRead (Y := X.withMem M) hK' hrip hr ha hn
    obtain ⟨af, t', hrun⟩ := and_r64_rip (s := X.withMem M) (o := o) (t := t + 1) htf hac (c.dec hK' hrip hd) h1
    refine ⟨_, _, hrun, hK'.nx rfl rfl rfl, rip_add hrip M len, ?_, ?_⟩
    · rw [nx_gpr, h2]; simp [rv, BitVec.setWidth_eq]
    · rw [nx_rflags, arith_zf, h2]; simp [rv, BitVec.setWidth_eq]) k'

/-- `test byte [rip + d], imm8`, the `a`-th byte of a region the contract reads. -/
theorem s_test_m8i_rip (c : Call prof R P Q code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {d imm len : Nat}
    (hd : Dec prof.feat code k (FV7z.mk .test 8 [.mem (mrip d 8), .imm 8 imm] len))
    {rg : Rgn} (hr : rg ∈ R s₀) {a : Nat} (ha : e.add (k + len) + BitVec.ofNat 64 d = rg.base.add a)
    (hn : a + 1 ≤ rg.len)
    (k' : Then prof R P Q L s₀ ra o e (k + len) fun Y => Y.cpu.gpr = X.cpu.gpr ∧
      Y.cpu.rflags.zf = (ofBytesLE 8 (readBytes s₀.proc.mm.mem (rg.base.add a) 1) &&& BitVec.ofNat 8 imm == 0)) :
    Go prof R P Q L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf hac => by
    obtain ⟨h1, h2⟩ := c.ripRead (Y := X.withMem M) hK' hrip hr ha hn
    obtain ⟨af, t', hrun⟩ := test_m8i_rip (s := X.withMem M) (o := o) (t := t + 1) (imm := imm) htf hac
      (c.dec hK' hrip hd) h1
    refine ⟨_, _, hrun, hK'.nx rfl rfl rfl, rip_add hrip M len, rfl, ?_⟩
    rw [nx_rflags, arith_zf, h2]) k'

/-- `mov r64, qword [rip + d]`, the `a`-th byte of a region the contract reads. -/
theorem s_mov64_rip (c : Call prof R P Q code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {r d len : Nat}
    (hd : Dec prof.feat code k (FV7z.mk .mov 64 [gr 64 r, .mem (mrip d 64)] len))
    {rg : Rgn} (hr : rg ∈ R s₀) {a : Nat} (ha : e.add (k + len) + BitVec.ofNat 64 d = rg.base.add a)
    (hn : a + 8 ≤ rg.len)
    (k' : Then prof R P Q L s₀ ra o e (k + len) fun Y =>
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) (ofBytesLE 64 (readBytes s₀.proc.mm.mem (rg.base.add a) 8)) ∧
      Y.cpu.rflags.zf = X.cpu.rflags.zf) :
    Go prof R P Q L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf hac => by
    obtain ⟨h1, h2⟩ := c.ripRead (Y := X.withMem M) hK' hrip hr ha hn
    refine ⟨_, _, mov_r64_rip (s := X.withMem M) htf hac (c.dec hK' hrip hd) h1, hK'.nx rfl rfl rfl,
      rip_add hrip M len, ?_, rfl⟩
    rw [nx_gpr, h2]; simp [BitVec.setWidth_eq]) k'

/-- `mov r64, r64'`. -/
theorem s_mov_rr (c : Call prof R P Q code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {r q len : Nat}
    (hd : Dec prof.feat code k (FV7z.mk .mov 64 [gr 64 r, gr 64 q] len))
    (k' : Then prof R P Q L s₀ ra o e (k + len) fun Y =>
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) (X.cpu.gpr.get (regOf q))) :
    Go prof R P Q L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf _ => ⟨_, _, mov_rr (s := X.withMem M) htf (c.dec hK' hrip hd),
    hK'.nx rfl rfl rfl, rip_add hrip M len, by simp [rv, BitVec.setWidth_eq]⟩) k'

/-- `and r64, r64'`. -/
theorem s_and_rr64 (c : Call prof R P Q code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {r q len : Nat}
    (hd : Dec prof.feat code k (FV7z.mk .and 64 [gr 64 r, gr 64 q] len))
    (k' : Then prof R P Q L s₀ ra o e (k + len) fun Y =>
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) (X.cpu.gpr.get (regOf r) &&& X.cpu.gpr.get (regOf q)) ∧
      Y.cpu.rflags.zf = (X.cpu.gpr.get (regOf r) &&& X.cpu.gpr.get (regOf q) == 0)) :
    Go prof R P Q L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf _ => by
    obtain ⟨af, t', hr⟩ := and_rr64 (s := X.withMem M) (o := o) (t := t + 1) (r := r) (q := q) htf
      (c.dec hK' hrip hd)
    exact ⟨_, _, hr, hK'.nx rfl rfl rfl, rip_add hrip M len, by simp [rv, BitVec.setWidth_eq],
      by rw [nx_rflags, arith_zf]; simp [rv, BitVec.setWidth_eq]⟩) k'

/-- `and r32, imm32`. -/
theorem s_and_ri32 (c : Call prof R P Q code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {r imm len : Nat}
    (hd : Dec prof.feat code k (FV7z.mk .and 32 [gr 32 r, .imm 32 imm] len))
    (k' : Then prof R P Q L s₀ ra o e (k + len) fun Y =>
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) ((rv X 32 r &&& BitVec.ofNat 32 imm).setWidth 64) ∧
      Y.cpu.rflags.zf = (rv X 32 r &&& BitVec.ofNat 32 imm == 0)) :
    Go prof R P Q L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf _ => by
    obtain ⟨af, t', hr⟩ := and_ri32 (s := X.withMem M) (o := o) (t := t + 1) (r := r) (imm := imm) htf
      (c.dec hK' hrip hd)
    exact ⟨_, _, hr, hK'.nx rfl rfl rfl, rip_add hrip M len, rfl, rfl⟩) k'

/-- `test r8h, imm8` (`ah`, …, of general register `r`). -/
theorem s_test_h8i (c : Call prof R P Q code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {r imm len : Nat}
    (hd : Dec prof.feat code k (FV7z.mk .test 8 [gh r, .imm 8 imm] len))
    (k' : Then prof R P Q L s₀ ra o e (k + len) fun Y => Y.cpu.gpr = X.cpu.gpr ∧
      Y.cpu.rflags.zf = ((X.cpu.gpr.get (regOf r) >>> 8).setWidth 8 &&& BitVec.ofNat 8 imm == 0)) :
    Go prof R P Q L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf _ => by
    obtain ⟨af, t', hr⟩ := test_h8i (s := X.withMem M) (o := o) (t := t + 1) (r := r) (imm := imm) htf
      (c.dec hK' hrip hd)
    exact ⟨_, _, hr, hK'.nx rfl rfl rfl, rip_add hrip M len, rfl, rfl⟩) k'

/-- `test r8, imm8` (the low byte). -/
theorem s_test_r8i (c : Call prof R P Q code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {r imm len : Nat}
    (hd : Dec prof.feat code k (FV7z.mk .test 8 [gr 8 r, .imm 8 imm] len))
    (k' : Then prof R P Q L s₀ ra o e (k + len) fun Y => Y.cpu.gpr = X.cpu.gpr ∧
      Y.cpu.rflags.zf = (rv X 8 r &&& BitVec.ofNat 8 imm == 0)) :
    Go prof R P Q L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf _ => by
    obtain ⟨af, t', hr⟩ := test_r8i (s := X.withMem M) (o := o) (t := t + 1) (r := r) (imm := imm) htf
      (c.dec hK' hrip hd)
    exact ⟨_, _, hr, hK'.nx rfl rfl rfl, rip_add hrip M len, rfl, rfl⟩) k'

end Call

end FV7z.Leaf
