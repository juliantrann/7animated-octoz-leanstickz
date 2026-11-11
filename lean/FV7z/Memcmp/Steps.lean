import FV7z.Memcmp.Call
/-!
# A call of `memcmp`, an instruction at a time (PLAN.md G2.1)

For each form of instruction (`Lemmas/Ins.lean`), a step of a call's run (`Memcmp/Call.lean`) from a state `X` at the
code's `k`-th byte, where the code decodes to it (`Dec`): the rest of the run goes on from every state `Y` it may
leave, given what `Y`'s registers are in terms of `X`'s. A load names the string and the bytes it reads, which are as
at the call. The statements keep the states abstract, so that a path of many instructions stays small.
-/
namespace FV7z.MemcmpCall
open ZellicX86 Decode Memcmp

@[simp] theorem withMem_cpu (s : State) (M : Memory) : (s.withMem M).cpu = s.cpu := rfl

@[simp] theorem set_regOf_0 (g : Gprs) (v : BitVec 64) : g.set (regOf 0) v = { g with rax := v } := rfl
@[simp] theorem set_regOf_1 (g : Gprs) (v : BitVec 64) : g.set (regOf 1) v = { g with rcx := v } := rfl
@[simp] theorem set_regOf_2 (g : Gprs) (v : BitVec 64) : g.set (regOf 2) v = { g with rdx := v } := rfl
@[simp] theorem set_regOf_6 (g : Gprs) (v : BitVec 64) : g.set (regOf 6) v = { g with rsi := v } := rfl
@[simp] theorem set_regOf_7 (g : Gprs) (v : BitVec 64) : g.set (regOf 7) v = { g with rdi := v } := rfl

/-- The callee-saved registers are those of `g`. -/
theorem Callee.of_gpr {s₀ X Y : State} (hC : Callee s₀ X) (h : Y.cpu.gpr.rbx = X.cpu.gpr.rbx ∧
    Y.cpu.gpr.rsp = X.cpu.gpr.rsp ∧ Y.cpu.gpr.rbp = X.cpu.gpr.rbp ∧ Y.cpu.gpr.r12 = X.cpu.gpr.r12 ∧
    Y.cpu.gpr.r13 = X.cpu.gpr.r13 ∧ Y.cpu.gpr.r14 = X.cpu.gpr.r14 ∧ Y.cpu.gpr.r15 = X.cpu.gpr.r15) :
    Callee s₀ Y := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hC
  exact ⟨h1.trans c1, h2.trans c2, h3.trans c3, h4.trans c4, h5.trans c5, h6.trans c6, h7.trans c7⟩

variable {prof : Profile} {code : List Byte} {e : Addr} {L : List (Addr × List Byte)} {s₀ : State} {ra : Addr}
  {o : Oracle} {X : State} {t k : Nat}

/-- The rest of the run, from every state the step to the code's `k`-th byte may leave, of which `P` holds. -/
abbrev Then (prof : Profile) (L : List (Addr × List Byte)) (s₀ : State) (ra : Addr) (o : Oracle) (e : Addr)
    (k : Nat) (P : State → Prop) : Prop :=
  ∀ Y t', Kept s₀ Y → Y.cpu.rip = e.add k → P Y → Go prof L s₀ ra o Y t'

namespace Call

/-- A step of `len` bytes to a state of which `P` holds. -/
theorem next (c : Call prof code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length) (hrip : X.cpu.rip = e.add k)
    {len : Nat} {P : State → Prop}
    (hrun : ∀ M, Kept s₀ (X.withMem M) → X.cpu.rflags.tf = false → X.cpu.rflags.ac = false →
      ∃ Y t', (instruction prof (X.withMem M)).runStream o (t + 1) = (.running Y none, t') ∧ Kept s₀ Y ∧
        Y.cpu.rip = e.add (k + len) ∧ P Y)
    (k' : Then prof L s₀ ra o e (k + len) P) : Go prof L s₀ ra o X t :=
  c.step hK hk hrip fun M _ hK' htf hac => by
    obtain ⟨Y, t', hr, hKY, hY, hP⟩ := hrun M hK' htf hac
    exact ⟨Y, t', hr, k' Y t' hKY hY hP⟩

theorem rip_add (hrip : X.cpu.rip = e.add k) (M : Memory) (len : Nat) :
    (X.withMem M).cpu.rip.add len = e.add (k + len) := by
  show X.cpu.rip.add len = _
  rw [hrip, addr_add_add]

/-! ## Scalar -/

theorem s_endbr (c : Call prof code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length) (hrip : X.cpu.rip = e.add k)
    {len : Nat} (hd : Dec prof.feat code k (FV7z.mk .endbr64 32 [] len))
    (k' : Then prof L s₀ ra o e (k + len) fun Y => Y.cpu.gpr = X.cpu.gpr ∧ Y.cpu.vec.zmm = X.cpu.vec.zmm) :
    Go prof L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf _ => ⟨_, _, endbr (s := X.withMem M) htf (c.dec hK' hrip hd), hK'.nx rfl rfl rfl,
    rip_add hrip M len, rfl, rfl⟩) k'

theorem s_cmp_ri (c : Call prof code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {w r imm len : Nat} (hd : Dec prof.feat code k (FV7z.mk .cmp w [gr w r, .imm w imm] len))
    (k' : Then prof L s₀ ra o e (k + len) fun Y => Y.cpu.gpr = X.cpu.gpr ∧ Y.cpu.vec.zmm = X.cpu.vec.zmm ∧
      Y.cpu.rflags = subF (rf0 X) (rv X w r) (BitVec.ofNat w imm)) :
    Go prof L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf _ => ⟨_, _, cmp_ri (s := X.withMem M) htf (c.dec hK' hrip hd), hK'.nx rfl rfl rfl,
    rip_add hrip M len, rfl, rfl, rfl⟩) k'

theorem addr_rel {e : Addr} {k len rel tgt : Nat} (h : (k + len + rel) % 2 ^ 64 = tgt % 2 ^ 64) :
    (e.add k).add len + BitVec.ofNat 64 rel = e.add tgt := by
  simp only [Addr.add]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem s_jcc (c : Call prof code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length) (hrip : X.cpu.rip = e.add k)
    {cc : Cond} {rel len tgt : Nat} (hd : Dec prof.feat code k (FV7z.mk (.jcc cc) 64 [.rel rel] len))
    (htgt : (k + len + rel) % 2 ^ 64 = tgt % 2 ^ 64) (ht : tgt < code.length)
    (taken : X.cpu.rflags.cond cc = true → Then prof L s₀ ra o e tgt fun Y => Y.cpu.gpr = X.cpu.gpr ∧
      Y.cpu.vec.zmm = X.cpu.vec.zmm)
    (fall : X.cpu.rflags.cond cc = false → Then prof L s₀ ra o e (k + len) fun Y => Y.cpu.gpr = X.cpu.gpr ∧
      Y.cpu.vec.zmm = X.cpu.vec.zmm) :
    Go prof L s₀ ra o X t := by
  cases hcc : X.cpu.rflags.cond cc
  · exact c.next hK hk hrip (fun M hK' htf _ => ⟨_, _, jcc_n (s := X.withMem M) htf (c.dec hK' hrip hd) hcc, hK'.nx rfl rfl rfl,
      rip_add hrip M len, rfl, rfl⟩) (fall hcc)
  · refine c.step hK hk hrip fun M _ hK' htf _ => ?_
    have hca := ((hK'.codeAt c.call.foot c.call.ready.rseq c.code) tgt ht).1
    have ha : (X.withMem M).cpu.rip.add len + BitVec.ofNat 64 rel = e.add tgt := by
      rw [withMem_cpu, hrip]; exact addr_rel htgt
    exact ⟨_, _, jcc_t (s := X.withMem M) htf (c.dec hK' hrip hd) hcc (by rw [ha]; exact hca), taken hcc _ _ (hK'.upd rfl rfl rfl)
      ha ⟨rfl, rfl⟩⟩

theorem s_sub_ri (c : Call prof code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {w r imm len : Nat} (hw : w = 32 ∨ w = 64)
    (hd : Dec prof.feat code k (FV7z.mk .sub w [gr w r, .imm w imm] len))
    (k' : Then prof L s₀ ra o e (k + len) fun Y =>
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) ((rv X w r - BitVec.ofNat w imm).setWidth 64) ∧
      Y.cpu.vec.zmm = X.cpu.vec.zmm ∧ Y.cpu.rflags = subF (rf0 X) (rv X w r) (BitVec.ofNat w imm)) :
    Go prof L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf _ => ⟨_, _, sub_ri (s := X.withMem M) hw htf (c.dec hK' hrip hd), hK'.nx rfl rfl rfl,
    rip_add hrip M len, by simp, rfl, rfl⟩) k'

theorem s_sub_rr (c : Call prof code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {w r q len : Nat} (hw : w = 32 ∨ w = 64)
    (hd : Dec prof.feat code k (FV7z.mk .sub w [gr w r, gr w q] len))
    (k' : Then prof L s₀ ra o e (k + len) fun Y =>
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) ((rv X w r - rv X w q).setWidth 64) ∧
      Y.cpu.vec.zmm = X.cpu.vec.zmm ∧ Y.cpu.rflags = subF (rf0 X) (rv X w r) (rv X w q)) :
    Go prof L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf _ => ⟨_, _, sub_rr (s := X.withMem M) hw htf (c.dec hK' hrip hd), hK'.nx rfl rfl rfl,
    rip_add hrip M len, by simp, rfl, rfl⟩) k'

theorem s_add_ri (c : Call prof code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {r imm len : Nat} (hd : Dec prof.feat code k (FV7z.mk .add 64 [gr 64 r, .imm 64 imm] len))
    (k' : Then prof L s₀ ra o e (k + len) fun Y =>
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) (rv X 64 r + BitVec.ofNat 64 imm) ∧ Y.cpu.vec.zmm = X.cpu.vec.zmm) :
    Go prof L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf _ => ⟨_, _, add_ri (s := X.withMem M) htf (c.dec hK' hrip hd), hK'.nx rfl rfl rfl,
    rip_add hrip M len, by simp, rfl⟩) k'

theorem s_add_rr (c : Call prof code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {r q len : Nat} (hd : Dec prof.feat code k (FV7z.mk .add 64 [gr 64 r, gr 64 q] len))
    (k' : Then prof L s₀ ra o e (k + len) fun Y =>
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) (rv X 64 r + rv X 64 q) ∧ Y.cpu.vec.zmm = X.cpu.vec.zmm) :
    Go prof L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf _ => ⟨_, _, add_rr (s := X.withMem M) htf (c.dec hK' hrip hd), hK'.nx rfl rfl rfl,
    rip_add hrip M len, by simp, rfl⟩) k'

theorem s_sbb_rr (c : Call prof code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {r q len : Nat} (hd : Dec prof.feat code k (FV7z.mk .sbb 32 [gr 32 r, gr 32 q] len))
    (k' : Then prof L s₀ ra o e (k + len) fun Y =>
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) ((rv X 32 r - rv X 32 q - (BitVec.ofBool X.cpu.rflags.cf).setWidth 32).setWidth 64)) :
    Go prof L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf _ => by
    obtain ⟨fl, hr, h1, h2, h3⟩ := sbb_rr (s := X.withMem M) (o := o) (t := t + 1) (r := r) (q := q) htf (c.dec hK' hrip hd)
    exact ⟨_, _, hr, hK'.nx h1 h2 h3, rip_add hrip M len, rfl⟩) k'

theorem s_and_ri (c : Call prof code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {r imm len : Nat} (hd : Dec prof.feat code k (FV7z.mk .and 32 [gr 32 r, .imm 32 imm] len))
    (k' : Then prof L s₀ ra o e (k + len) fun Y =>
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) ((rv X 32 r &&& BitVec.ofNat 32 imm).setWidth 64) ∧
      Y.cpu.vec.zmm = X.cpu.vec.zmm) :
    Go prof L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf _ => by
    obtain ⟨fl, t', hr, h1, h2, h3⟩ := and_ri (s := X.withMem M) (o := o) (t := t + 1) (r := r) (imm := imm) htf (c.dec hK' hrip hd)
    exact ⟨_, _, hr, hK'.nx h1 h2 h3, rip_add hrip M len, rfl, rfl⟩) k'

theorem s_or_ri (c : Call prof code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {r imm len : Nat} (hd : Dec prof.feat code k (FV7z.mk .or 32 [gr 32 r, .imm 32 imm] len))
    (k' : Then prof L s₀ ra o e (k + len) fun Y =>
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) ((rv X 32 r ||| BitVec.ofNat 32 imm).setWidth 64)) :
    Go prof L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf _ => by
    obtain ⟨fl, t', hr, h1, h2, h3⟩ := or_ri (s := X.withMem M) (o := o) (t := t + 1) (r := r) (imm := imm) htf (c.dec hK' hrip hd)
    exact ⟨_, _, hr, hK'.nx h1 h2 h3, rip_add hrip M len, rfl⟩) k'

theorem s_or_rr (c : Call prof code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {r q len : Nat} (hd : Dec prof.feat code k (FV7z.mk .or 64 [gr 64 r, gr 64 q] len))
    (k' : Then prof L s₀ ra o e (k + len) fun Y =>
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) (rv X 64 r ||| rv X 64 q)) :
    Go prof L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf _ => by
    obtain ⟨fl, t', hr, h1, h2, h3⟩ := or_rr (s := X.withMem M) (o := o) (t := t + 1) (r := r) (q := q) htf (c.dec hK' hrip hd)
    exact ⟨_, _, hr, hK'.nx h1 h2 h3, rip_add hrip M len, by simp⟩) k'

theorem s_xor_rr (c : Call prof code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {r q len : Nat} (hd : Dec prof.feat code k (FV7z.mk .xor 32 [gr 32 r, gr 32 q] len))
    (k' : Then prof L s₀ ra o e (k + len) fun Y =>
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) ((rv X 32 r ^^^ rv X 32 q).setWidth 64) ∧ Y.cpu.vec.zmm = X.cpu.vec.zmm) :
    Go prof L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf _ => by
    obtain ⟨fl, t', hr, h1, h2, h3⟩ := xor_rr (s := X.withMem M) (o := o) (t := t + 1) (r := r) (q := q) htf (c.dec hK' hrip hd)
    exact ⟨_, _, hr, hK'.nx h1 h2 h3, rip_add hrip M len, rfl, rfl⟩) k'

theorem s_shl64_32 (c : Call prof code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {r len : Nat} (hd : Dec prof.feat code k (FV7z.mk .shl 64 [gr 64 r, .imm 8 32] len))
    (k' : Then prof L s₀ ra o e (k + len) fun Y => Y.cpu.gpr = X.cpu.gpr.set (regOf r) (rv X 64 r <<< 32)) :
    Go prof L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf _ => by
    obtain ⟨fl, t', hr, h1, h2, h3⟩ := shl64_32 (s := X.withMem M) (o := o) (t := t + 1) (r := r) htf (c.dec hK' hrip hd)
    exact ⟨_, _, hr, hK'.nx h1 h2 h3, rip_add hrip M len, by simp⟩) k'

theorem s_shl32_8 (c : Call prof code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {r len : Nat} (hd : Dec prof.feat code k (FV7z.mk .shl 32 [gr 32 r, .imm 8 8] len))
    (k' : Then prof L s₀ ra o e (k + len) fun Y =>
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) ((rv X 32 r <<< 8).setWidth 64)) :
    Go prof L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf _ => by
    obtain ⟨fl, t', hr, h1, h2, h3⟩ := shl32_8 (s := X.withMem M) (o := o) (t := t + 1) (r := r) htf (c.dec hK' hrip hd)
    exact ⟨_, _, hr, hK'.nx h1 h2 h3, rip_add hrip M len, rfl⟩) k'

theorem s_bswap32 (c : Call prof code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {r len : Nat} (hd : Dec prof.feat code k (FV7z.mk .bswap 32 [gr 32 r] len))
    (k' : Then prof L s₀ ra o e (k + len) fun Y =>
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) ((ZellicX86.bswap (rv X 32 r)).setWidth 64)) :
    Go prof L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf _ => ⟨_, _, bswap32 (s := X.withMem M) htf (c.dec hK' hrip hd), hK'.nx rfl rfl rfl,
    rip_add hrip M len, rfl⟩) k'

theorem s_mov_rr (c : Call prof code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {r q len : Nat} (hd : Dec prof.feat code k (FV7z.mk .mov 64 [gr 64 r, gr 64 q] len))
    (k' : Then prof L s₀ ra o e (k + len) fun Y =>
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) (rv X 64 q) ∧ Y.cpu.vec.zmm = X.cpu.vec.zmm) :
    Go prof L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf _ => ⟨_, _, mov_rr (s := X.withMem M) htf (c.dec hK' hrip hd), hK'.nx rfl rfl rfl,
    rip_add hrip M len, by simp, rfl⟩) k'

theorem s_lea (c : Call prof code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {r b i d len : Nat}
    (hd : Dec prof.feat code k (FV7z.mk .lea 64 [gr 64 r, .mem (mbi b i d 0)] len))
    (k' : Then prof L s₀ ra o e (k + len) fun Y =>
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) (eaI X b i d) ∧ Y.cpu.vec.zmm = X.cpu.vec.zmm) :
    Go prof L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf _ => ⟨_, _, lea (s := X.withMem M) htf (c.dec hK' hrip hd), hK'.nx rfl rfl rfl,
    rip_add hrip M len, rfl, rfl⟩) k'

/-! ## Loads -/

theorem s_movzx8_i (c : Call prof code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {r b i d len : Nat}
    (hd : Dec prof.feat code k (FV7z.mk .movzx 32 [gr 32 r, .mem (mbi b i d 8)] len))
    {g : Rgn} (hg : g ∈ strings s₀) {a : Nat} (hea : eaI X b i d = g.base.add a) (ha : a + 1 ≤ g.len)
    (k' : Then prof L s₀ ra o e (k + len) fun Y =>
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) (((s₀.proc.mm.mem.readByte (g.base.add a)).setWidth 32).setWidth 64)) :
    Go prof L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf hac => by
    obtain ⟨hR, hB⟩ := c.read hK' hg ha
    have hea' : eaI (X.withMem M) b i d = g.base.add a := hea
    refine ⟨_, _, movzx8_i (s := X.withMem M) htf hac (c.dec hK' hrip hd) (by rw [hea']; exact hR), hK'.nx rfl rfl rfl,
      rip_add hrip M len, ?_⟩
    simp only [nx_gpr, withMem_cpu]
    rw [hea', hB, FV7z.ofBytesLE_one]) k'

theorem s_movzx8_d (c : Call prof code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {r b len : Nat}
    (hd : Dec prof.feat code k (FV7z.mk .movzx 32 [gr 32 r, .mem (mbd b 0 8)] len))
    {g : Rgn} (hg : g ∈ strings s₀) {a : Nat} (hea : eaD X b 0 = g.base.add a) (ha : a + 1 ≤ g.len)
    (k' : Then prof L s₀ ra o e (k + len) fun Y =>
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) (((s₀.proc.mm.mem.readByte (g.base.add a)).setWidth 32).setWidth 64)) :
    Go prof L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf hac => by
    obtain ⟨hR, hB⟩ := c.read hK' hg ha
    have hea' : eaD (X.withMem M) b 0 = g.base.add a := hea
    refine ⟨_, _, movzx8_d (s := X.withMem M) htf hac (c.dec hK' hrip hd) (by rw [hea']; exact hR), hK'.nx rfl rfl rfl,
      rip_add hrip M len, ?_⟩
    simp only [nx_gpr, withMem_cpu]
    rw [hea', hB, FV7z.ofBytesLE_one]) k'

theorem s_movzx16_d (c : Call prof code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {r b len : Nat}
    (hd : Dec prof.feat code k (FV7z.mk .movzx 32 [gr 32 r, .mem (mbd b 0 16)] len))
    {g : Rgn} (hg : g ∈ strings s₀) {a : Nat} (hea : eaD X b 0 = g.base.add a) (ha : a + 2 ≤ g.len)
    (k' : Then prof L s₀ ra o e (k + len) fun Y =>
      Y.cpu.gpr = X.cpu.gpr.set (regOf r)
        (((ofBytesLE 16 (readBytes s₀.proc.mm.mem (g.base.add a) 2)).setWidth 32).setWidth 64)) :
    Go prof L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf hac => by
    obtain ⟨hR, hB⟩ := c.read hK' hg ha
    have hea' : eaD (X.withMem M) b 0 = g.base.add a := hea
    refine ⟨_, _, movzx16_d (s := X.withMem M) htf hac (c.dec hK' hrip hd) (by rw [hea']; exact hR),
      hK'.nx rfl rfl rfl, rip_add hrip M len, ?_⟩
    simp only [nx_gpr, withMem_cpu]
    rw [hea', hB]) k'

theorem s_mov8_i (c : Call prof code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {r b i d len : Nat}
    (hd : Dec prof.feat code k (FV7z.mk .mov 8 [gr 8 r, .mem (mbi b i d 8)] len))
    {g : Rgn} (hg : g ∈ strings s₀) {a : Nat} (hea : eaI X b i d = g.base.add a) (ha : a + 1 ≤ g.len)
    (k' : Then prof L s₀ ra o e (k + len) fun Y =>
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) ((X.cpu.gpr.get (regOf r) &&& ~~~(BitVec.ofNat 64 ((2 ^ 8 - 1) * 2 ^ 0))) |||
        ((ofBytesLE 8 (readBytes s₀.proc.mm.mem (g.base.add a) 1)).setWidth 64 <<< 0))) :
    Go prof L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf hac => by
    obtain ⟨hR, hB⟩ := c.read hK' hg ha
    have hea' : eaI (X.withMem M) b i d = g.base.add a := hea
    refine ⟨_, _, mov8_i (s := X.withMem M) htf hac (c.dec hK' hrip hd) (by rw [hea']; exact hR), hK'.nx rfl rfl rfl,
      rip_add hrip M len, ?_⟩
    simp only [nx_gpr, withMem_cpu]
    rw [hea', hB]) k'

theorem s_movbe_d (c : Call prof code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {r b len : Nat}
    (hd : Dec prof.feat code k (FV7z.mk .movbe 32 [gr 32 r, .mem (mbd b 0 32)] len))
    {g : Rgn} (hg : g ∈ strings s₀) {a : Nat} (hea : eaD X b 0 = g.base.add a) (ha : a + 4 ≤ g.len)
    (k' : Then prof L s₀ ra o e (k + len) fun Y =>
      Y.cpu.gpr = X.cpu.gpr.set (regOf r)
        ((ZellicX86.bswap (ofBytesLE 32 (readBytes s₀.proc.mm.mem (g.base.add a) 4))).setWidth 64)) :
    Go prof L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf hac => by
    obtain ⟨hR, hB⟩ := c.read hK' hg ha
    have hea' : eaD (X.withMem M) b 0 = g.base.add a := hea
    refine ⟨_, _, movbe_d (s := X.withMem M) htf hac (c.dec hK' hrip hd) (by rw [hea']; exact hR),
      hK'.nx rfl rfl rfl, rip_add hrip M len, ?_⟩
    simp only [nx_gpr, withMem_cpu]
    rw [hea', hB]) k'

theorem s_movbe_i (c : Call prof code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {r b i d len : Nat}
    (hd : Dec prof.feat code k (FV7z.mk .movbe 32 [gr 32 r, .mem (mbi b i d 32)] len))
    {g : Rgn} (hg : g ∈ strings s₀) {a : Nat} (hea : eaI X b i d = g.base.add a) (ha : a + 4 ≤ g.len)
    (k' : Then prof L s₀ ra o e (k + len) fun Y =>
      Y.cpu.gpr = X.cpu.gpr.set (regOf r)
        ((ZellicX86.bswap (ofBytesLE 32 (readBytes s₀.proc.mm.mem (g.base.add a) 4))).setWidth 64)) :
    Go prof L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf hac => by
    obtain ⟨hR, hB⟩ := c.read hK' hg ha
    have hea' : eaI (X.withMem M) b i d = g.base.add a := hea
    refine ⟨_, _, movbe_i (s := X.withMem M) htf hac (c.dec hK' hrip hd) (by rw [hea']; exact hR),
      hK'.nx rfl rfl rfl, rip_add hrip M len, ?_⟩
    simp only [nx_gpr, withMem_cpu]
    rw [hea', hB]) k'

theorem s_tzcnt (c : Call prof code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {r q len : Nat}
    (hd : Dec prof.feat code k (FV7z.mk (.bit .tzcnt) 32 [gr 32 r, gr 32 q] len) ∨
      Dec prof.feat code k (FV7z.mk (.bit .bsf) 32 [gr 32 r, gr 32 q] len))
    (hx : rv X 32 q ≠ 0)
    (k' : Then prof L s₀ ra o e (k + len) fun Y =>
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) ((BitVec.ofNat 32 (lowestSetBit (rv X 32 q))).setWidth 64) ∧
      Y.cpu.vec.zmm = X.cpu.vec.zmm) :
    Go prof L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf _ => by
    obtain ⟨fl, t', hr, h1, h2, h3⟩ := tzcnt_rr (s := X.withMem M) (o := o) (t := t + 1) (r := r) (q := q) htf
      (hd.imp (fun h => c.dec hK' hrip h) (fun h => c.dec hK' hrip h)) hx
    exact ⟨_, _, hr, hK'.nx h1 h2 h3, rip_add hrip M len, rfl, rfl⟩) k'

/-! ## Vector -/

theorem s_vmovdqu (c : Call prof code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {w n b d len : Nat}
    (hd : Dec prof.feat code k (FV7z.mk (.avx .vmovdqu) 32 [.vreg n w, .mem (mbd b d w)] len))
    {g : Rgn} (hg : g ∈ strings s₀) {a : Nat} (hea : eaD X b d = g.base.add a) (ha : a + w / 8 ≤ g.len)
    (k' : Then prof L s₀ ra o e (k + len) fun Y => Y.cpu.gpr = X.cpu.gpr ∧
      Y.cpu.vec.zmm = withZmm X.cpu.vec.zmm (xmmOf n)
        ((ofBytesLE w (readBytes s₀.proc.mm.mem (g.base.add a) (w / 8))).setWidth 512)) :
    Go prof L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf hac => by
    obtain ⟨hR, hB⟩ := c.read hK' hg ha
    have hea' : eaD (X.withMem M) b d = g.base.add a := hea
    refine ⟨_, _, vmovdqu_ld (s := X.withMem M) htf hac (c.dec hK' hrip hd) (by rw [hea']; exact hR),
      hK'.nxz rfl rfl rfl, rip_add hrip M len, rfl, ?_⟩
    simp only [nxz_zmm, withMem_cpu]
    rw [hea', hB]) k'

theorem s_vmovq (c : Call prof code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {n b len : Nat}
    (hd : Dec prof.feat code k (FV7z.mk (.avx .vmovq) 32 [.vreg n 128, .mem (mbd b 0 64)] len))
    {g : Rgn} (hg : g ∈ strings s₀) {a : Nat} (hea : eaD X b 0 = g.base.add a) (ha : a + 8 ≤ g.len)
    (k' : Then prof L s₀ ra o e (k + len) fun Y => Y.cpu.gpr = X.cpu.gpr ∧
      Y.cpu.vec.zmm = withZmm X.cpu.vec.zmm (xmmOf n)
        ((ofBytesLE 64 (readBytes s₀.proc.mm.mem (g.base.add a) 8)).setWidth 512)) :
    Go prof L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf hac => by
    obtain ⟨hR, hB⟩ := c.read hK' hg ha
    have hea' : eaD (X.withMem M) b 0 = g.base.add a := hea
    refine ⟨_, _, vmovq_ld (s := X.withMem M) htf hac (c.dec hK' hrip hd) (by rw [hea']; exact hR),
      hK'.nxz rfl rfl rfl, rip_add hrip M len, rfl, ?_⟩
    simp only [nxz_zmm, withMem_cpu]
    rw [hea', hB]) k'

theorem s_vpcmpeqb_m (c : Call prof code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {w n p b d len : Nat}
    (hd : Dec prof.feat code k (FV7z.mk (.avx (.vpcmpeq 8)) 32 [.vreg n w, .vreg p w, .mem (mbd b d w)] len))
    {g : Rgn} (hg : g ∈ strings s₀) {a : Nat} (hea : eaD X b d = g.base.add a) (ha : a + w / 8 ≤ g.len)
    (k' : Then prof L s₀ ra o e (k + len) fun Y => Y.cpu.gpr = X.cpu.gpr ∧
      Y.cpu.vec.zmm = withZmm X.cpu.vec.zmm (xmmOf n)
        ((eqb ((X.cpu.vec.zmm (xmmOf p)).setWidth w)
          (ofBytesLE w (readBytes s₀.proc.mm.mem (g.base.add a) (w / 8)))).setWidth 512)) :
    Go prof L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf hac => by
    obtain ⟨hR, hB⟩ := c.read hK' hg ha
    have hea' : eaD (X.withMem M) b d = g.base.add a := hea
    refine ⟨_, _, vpcmpeqb_m (s := X.withMem M) htf hac (c.dec hK' hrip hd) (by rw [hea']; exact hR),
      hK'.nxz rfl rfl rfl, rip_add hrip M len, rfl, ?_⟩
    simp only [nxz_zmm, withMem_cpu]
    rw [hea', hB]) k'

theorem s_vpcmpeqb_r (c : Call prof code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {w n p q len : Nat}
    (hd : Dec prof.feat code k (FV7z.mk (.avx (.vpcmpeq 8)) 32 [.vreg n w, .vreg p w, .vreg q w] len))
    (k' : Then prof L s₀ ra o e (k + len) fun Y => Y.cpu.gpr = X.cpu.gpr ∧
      Y.cpu.vec.zmm = withZmm X.cpu.vec.zmm (xmmOf n)
        ((eqb ((X.cpu.vec.zmm (xmmOf p)).setWidth w) ((X.cpu.vec.zmm (xmmOf q)).setWidth w)).setWidth 512)) :
    Go prof L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf _ => ⟨_, _, vpcmpeqb_r (s := X.withMem M) htf (c.dec hK' hrip hd),
    hK'.nxz rfl rfl rfl, rip_add hrip M len, rfl, rfl⟩) k'

theorem s_vpand (c : Call prof code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {n p q len : Nat}
    (hd : Dec prof.feat code k (FV7z.mk (.avx .vpand) 32 [.vreg n 256, .vreg p 256, .vreg q 256] len))
    (k' : Then prof L s₀ ra o e (k + len) fun Y => Y.cpu.gpr = X.cpu.gpr ∧
      Y.cpu.vec.zmm = withZmm X.cpu.vec.zmm (xmmOf n)
        (((X.cpu.vec.zmm (xmmOf p)).setWidth 256 &&& (X.cpu.vec.zmm (xmmOf q)).setWidth 256).setWidth 512)) :
    Go prof L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf _ => ⟨_, _, vpand (s := X.withMem M) htf (c.dec hK' hrip hd),
    hK'.nxz rfl rfl rfl, rip_add hrip M len, rfl, rfl⟩) k'

theorem s_vpmovmskb (c : Call prof code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {w r n len : Nat}
    (hd : Dec prof.feat code k (FV7z.mk (.avx .vpmovmskb) 32 [gr 32 r, .vreg n w] len))
    (k' : Then prof L s₀ ra o e (k + len) fun Y =>
      Y.cpu.gpr = X.cpu.gpr.set (regOf r)
        ((ofBits 32 fun j => decide (j < w / 8) && (elem 8 ((X.cpu.vec.zmm (xmmOf n)).setWidth w) j).msb).setWidth 64) ∧
      Y.cpu.vec.zmm = X.cpu.vec.zmm) :
    Go prof L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf _ => ⟨_, _, vpmovmskb (s := X.withMem M) htf (c.dec hK' hrip hd),
    hK'.nx rfl rfl rfl, rip_add hrip M len, rfl, rfl⟩) k'

theorem s_vptest (c : Call prof code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {p q len : Nat}
    (hd : Dec prof.feat code k (FV7z.mk (.avx .vptest) 32 [.vreg p 256, .vreg q 256] len))
    (k' : Then prof L s₀ ra o e (k + len) fun Y => Y.cpu.gpr = X.cpu.gpr ∧ Y.cpu.vec.zmm = X.cpu.vec.zmm ∧
      Y.cpu.rflags.cf =
        ((~~~(X.cpu.vec.zmm (xmmOf p)).setWidth 256 &&& (X.cpu.vec.zmm (xmmOf q)).setWidth 256) == 0)) :
    Go prof L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf _ => ⟨_, _, vptest (s := X.withMem M) htf (c.dec hK' hrip hd),
    hK'.nx rfl rfl rfl, rip_add hrip M len, rfl, rfl, rfl⟩) k'

theorem s_vzeroupper (c : Call prof code e L s₀ ra o) (hK : Kept s₀ X) (hk : k < code.length)
    (hrip : X.cpu.rip = e.add k) {len : Nat}
    (hd : Dec prof.feat code k (FV7z.mk (.avx .vzeroupper) 32 [] len))
    (k' : Then prof L s₀ ra o e (k + len) fun Y => Y.cpu.gpr = X.cpu.gpr) :
    Go prof L s₀ ra o X t :=
  c.next hK hk hrip (fun M hK' htf _ => ⟨_, _, vzeroupper (s := X.withMem M) htf (c.dec hK' hrip hd),
    hK'.nxz rfl rfl rfl, rip_add hrip M len, rfl⟩) k'

end Call

end FV7z.MemcmpCall
