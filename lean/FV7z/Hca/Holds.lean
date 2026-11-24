import FV7z.Hca.Cuts
import FV7z.Lemmas.SpCallK
import FV7z.Lemmas.Signed
import FV7z.Tun.Inv
/-!
# `handle_amd` returns, with the callee-saved registers and one stack slot changed back (PLAN.md M, ctor 103)

glibc's `handle_amd (name)` at `0x65cb10` in `7zzs` (`sysdeps/x86/cacheinfo.c`), as `init_cacheinfo` calls it: for
`_SC_LEVEL1_DCACHE_SIZE` (188), `_SC_LEVEL2_CACHE_SIZE` (191) and `_SC_LEVEL3_CACHE_SIZE` (194). It saves `rbx`, asks
`cpuid` for the highest extended leaf and for leaf `0x80000005` or `0x80000006`, takes the `switch` on `name - 188`
through the table at `0x6f2000` (cases 0, 3 and 6) and returns a size from `ecx` or `edx`, or 0.

`ham_fnK`: entered with `Te` (`name` one of the three, the slots below the return address the run's to store into
and read, the table's bytes as in the file, the return address in code), the function goes on to its return address
with `Rh`: `rsp` 8 up, `rbx`, `rbp` and `r12`–`r15` as at the entry, and the bytes as at the entry but for `rbx`'s
slot below the return address. The value it returns is not part of the contract (`init_cacheinfo` only stores it).

The proof: `cfgAt` over the cut points of `Cuts.lean` and the two `cpuid`s (`SpAt.cpuid`), with `Ih` at each cut
point (a measure that goes down along every edge), and `Fh` at the four `ret`s, where `Seg.s_ret` goes on.
-/
namespace FV7z.Hca
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn

/-! ## The `cpuid`s and `ret`s -/

def pcp : List Byte := [0x0f, 0xa2]
theorem pcp_0 : ∀ feat, Dec feat pcp 0 (FV7z.mk .cpuid 32 [] 2) := by dec_rfl
theorem wcp6 : pcp <+: hca.drop 6 := by decide +kernel
theorem wcp39 : pcp <+: hca.drop 39 := by decide +kernel
theorem cpuid_6 (feat : Features) : Dec feat hca 6 (FV7z.mk .cpuid 32 [] 2) :=
  Dec.shift (j := 6) (k := 0) (pcp_0 feat) wcp6 (Nat.zero_le _)
theorem cpuid_39 (feat : Features) : Dec feat hca 39 (FV7z.mk .cpuid 32 [] 2) :=
  Dec.shift (j := 39) (k := 0) (pcp_0 feat) wcp39 (Nat.zero_le _)

def prt : List Byte := [0xc3]
theorem prt_0 : ∀ feat, Dec feat prt 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem wr99 : prt <+: hca.drop 99 := by decide +kernel
theorem wr171 : prt <+: hca.drop 171 := by decide +kernel
theorem wr246 : prt <+: hca.drop 246 := by decide +kernel
theorem wr332 : prt <+: hca.drop 332 := by decide +kernel

/-- The four `ret`s. -/
theorem ret_at (feat : Features) {j : Nat} (hj : j = 99 ∨ j = 171 ∨ j = 246 ∨ j = 332) :
    j < hca.length ∧ Dec feat hca j (FV7z.mk .ret 64 [] 1) := by
  rcases hj with rfl | rfl | rfl | rfl
  · exact ⟨lt_len (by decide), Dec.shift (j := 99) (k := 0) (prt_0 feat) wr99 (Nat.zero_le _)⟩
  · exact ⟨lt_len (by decide), Dec.shift (j := 171) (k := 0) (prt_0 feat) wr171 (Nat.zero_le _)⟩
  · exact ⟨lt_len (by decide), Dec.shift (j := 246) (k := 0) (prt_0 feat) wr246 (Nat.zero_le _)⟩
  · exact ⟨lt_len (by decide), Dec.shift (j := 332) (k := 0) (prt_0 feat) wr332 (Nat.zero_le _)⟩

/-! ## The contract -/

/-- What `handle_amd` needs at its entry (`rsp` at the return address). -/
structure Te (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (g : Gprs) (V : Addr → Byte) : Prop where
  rdi : g.rdi = 188#64 ∨ g.rdi = 191#64 ∨ g.rdi = 194#64
  st : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)
  ld : ∀ i < 16, Foot F.data (Addr.add (g.rsp - 8) i)
  lo : 0x6f2000 + 44 ≤ g.rsp.toNat
  hi : g.rsp.toNat + 8 ≤ 2 ^ 64
  tab : ∀ x : Addr, 0x6f2000 ≤ x.toNat → x.toNat < 0x6f2000 + 36 → Foot F.data x
  jt : List.map V (byteAddrs 0x6f2000#64 36) = hca_jt
  ret : ∃ e₂ code₂ j₂, CodeIn L e₂ code₂ ∧ j₂ < code₂.length ∧
    ofBytesLE 64 (List.map V (byteAddrs g.rsp 8)) = e₂.add j₂

/-- The bytes after `push rbx`. -/
abbrev V1 (g₀ : Gprs) (V₀ : Addr → Byte) : Addr → Byte := Vst V₀ (g₀.rsp - 8) (toBytesLE g₀.rbx 8)

/-- At the return address: what changed and what did not. -/
def Rh (g₀ : Gprs) (V₀ : Addr → Byte) (g : Gprs) (V : Addr → Byte) : Prop :=
  g.rsp = g₀.rsp + 8 ∧ g.rbx = g₀.rbx ∧ g.rbp = g₀.rbp ∧ g.r12 = g₀.r12 ∧ g.r13 = g₀.r13 ∧ g.r14 = g₀.r14 ∧
    g.r15 = g₀.r15 ∧ V = V1 g₀ V₀

/-- Between the `push` and the `pop`. -/
def Mid (g₀ : Gprs) (V₀ : Addr → Byte) (g : Gprs) (V : Addr → Byte) : Prop :=
  g.rsp = g₀.rsp - 8 ∧ g.rbp = g₀.rbp ∧ g.r12 = g₀.r12 ∧ g.r13 = g₀.r13 ∧ g.r14 = g₀.r14 ∧ g.r15 = g₀.r15 ∧
    V = V1 g₀ V₀

/-- The invariants of the cut points, with the measure `n`. -/
def Ih (g₀ : Gprs) (V₀ : Addr → Byte) (ℓ n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  if ℓ = 0 then n = 9 ∧ g = g₀ ∧ V = V₀ else
  if ℓ = 6 then n = 8 ∧ g.rdi = g₀.rdi ∧ Mid g₀ V₀ g V else
  if ℓ = 8 then n = 7 ∧ g.rdi = g₀.rdi ∧ Mid g₀ V₀ g V else
  if ℓ = 39 then n = 6 ∧ g.rdi = g₀.rdi ∧ Mid g₀ V₀ g V else
  if ℓ = 41 then n = 5 ∧ g.rdi = g₀.rdi ∧ Mid g₀ V₀ g V else
  if ℓ = 54 then n = 4 ∧ g.rdi = g₀.rdi ∧ Mid g₀ V₀ g V else
  if ℓ = 96 then n = 3 ∧ Mid g₀ V₀ g V else
  if ℓ = 98 then n = 2 ∧ Mid g₀ V₀ g V else
  if ℓ = 160 then n = 3 ∧ Mid g₀ V₀ g V else
  if ℓ = 224 then n = 3 ∧ Mid g₀ V₀ g V else
  if ℓ = 312 then n = 3 ∧ Mid g₀ V₀ g V else
  False

/-- At a `ret`. -/
def Fh (g₀ : Gprs) (V₀ : Addr → Byte) (j : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  (j = 99 ∨ j = 171 ∨ j = 246 ∨ j = 332) ∧ g.rsp = g₀.rsp ∧ g.rbx = g₀.rbx ∧ g.rbp = g₀.rbp ∧ g.r12 = g₀.r12 ∧
    g.r13 = g₀.r13 ∧ g.r14 = g₀.r14 ∧ g.r15 = g₀.r15 ∧ V = V1 g₀ V₀

/-- At an exit: a cut point's invariant with a smaller measure, or a `ret`. -/
def Nx (g₀ : Gprs) (V₀ : Addr → Byte) (n : Nat) : Post :=
  fun j' g' _ V' => (∃ n', n' < n ∧ Ih g₀ V₀ j' n' g' V') ∨ Fh g₀ V₀ j' g' V'

/-- What the code from a cut point needs for `Q` at the next ones: at a `cpuid`, `Q` after it on every CPU. -/
def WtC (prof : Profile) (F : Footprint) (Wl : List Rgn) (ℓ : Nat) : Post → Gprs → Rflags → (Addr → Byte) → Prop :=
  if ℓ = 6 then fun Q g _ V => ∀ cpu, cpu < max prof.cpus 1 → ∀ fl, Q 8 (cpuidG prof cpu g) fl V else
  if ℓ = 39 then fun Q g _ V => ∀ cpu, cpu < max prof.cpus 1 → ∀ fl, Q 41 (cpuidG prof cpu g) fl V else
  Wt ℓ F Wl

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {g₀ g : Gprs} {V₀ V : Addr → Byte} {f : Rflags} {n : Nat}

/-- The cut points' pieces in a run with the code. -/
theorem spC (c : Seg prof F Wl L s₀ o) (hin : CodeIn L hca_at hca) (ℓ : Nat) :
    SpAt prof F Wl L s₀ o hca_at ℓ (WtC prof F Wl ℓ) := by
  unfold WtC
  split
  · subst ℓ
    exact SpAt.cpuid c hin (lt_len (by decide)) (cpuid_6 _)
  split
  · subst ℓ
    exact SpAt.cpuid c hin (lt_len (by decide)) (cpuid_39 _)
  exact (spAll prof ℓ).at c hin

/-! ## Arithmetic and bytes -/

theorem sub8 (s : Addr) (h : 8 ≤ s.toNat) : (s - 8).toNat = s.toNat - 8 := by bv_omega

theorem fit8 (hT : Te F Wl L g₀ V₀) : (g₀.rsp - 8).toNat + 8 ≤ 2 ^ 64 := by
  have := hT.lo
  have := g₀.rsp.isLt
  rw [sub8 _ (by omega)]
  omega

theorem ad8 (s : Addr) (i : Nat) : Addr.add (s - 8) (8 + i) = Addr.add s i := by
  simp only [Addr.add]; bv_omega

theorem ld8 (hT : Te F Wl L g₀ V₀) : ∀ i < 8, Foot F.data (Addr.add g₀.rsp i) := fun i hi => by
  have := hT.ld (8 + i) (by omega)
  rwa [ad8] at this

/-- `rbx` back from its slot. -/
theorem pop_self (hT : Te F Wl L g₀ V₀) :
    ofBytesLE 64 (List.map (V1 g₀ V₀) (byteAddrs (g₀.rsp - 8) 8)) = g₀.rbx := by
  rw [Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (fit8 hT)]
  exact ofBytesLE_toBytesLE (w := 64) (n := 8) rfl _

/-- The return address is not in `rbx`'s slot. -/
theorem rd_ret (hT : Te F Wl L g₀ V₀) :
    List.map (V1 g₀ V₀) (byteAddrs g₀.rsp 8) = List.map V₀ (byteAddrs g₀.rsp 8) := by
  have := hT.lo
  have e := sub8 g₀.rsp (by omega)
  exact Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; exact fit8 hT) hT.hi
    (Or.inl (by rw [toBytesLE_length, e]; omega))

/-- `m` bytes from the `k`-th of `n` read whole. -/
theorem sub_rd (V : Addr → Byte) (a : Addr) (l : List Byte) (n : Nat) (h : List.map V (byteAddrs a n) = l)
    (k m : Nat) (hk : k + m ≤ n) : List.map V (byteAddrs (Addr.add a k) m) = (l.drop k).take m := by
  subst h
  apply List.ext_getElem
  · simp [byteAddrs]; omega
  · intro i h1 h2
    have hi : i < m := by simpa [byteAddrs] using h1
    simp [byteAddrs, addr_add_add]

/-- An entry of the table, after the `push`. -/
theorem jt_rd (hT : Te F Wl L g₀ V₀) (hM : Mid g₀ V₀ g V) (k : Nat) (hk : k < 9) (x : Addr)
    (hx : x.toNat = 7282688 + 4 * k) : List.map V (byteAddrs x 4) = (hca_jt.drop (4 * k)).take 4 := by
  obtain ⟨-, -, -, -, -, -, rfl⟩ := hM
  have lo := hT.lo
  have e := sub8 g₀.rsp (by omega)
  have hxa : x = Addr.add 0x6f2000#64 (4 * k) := by
    apply BitVec.eq_of_toNat_eq
    rw [hx, toNat_add_of_fits (n := 36) (by omega) (by decide)]
    rfl
  rw [Tun.rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; exact fit8 hT) (by omega)
    (Or.inr (by rw [e]; omega)), hxa]
  exact sub_rd V₀ _ hca_jt 36 hT.jt (4 * k) 4 (by omega)

/-- The table's bytes may be read. -/
theorem tab4 (hT : Te F Wl L g₀ V₀) (x : Addr) (h1 : 7282688 ≤ x.toNat) (h2 : x.toNat + 4 ≤ 7282724) :
    ∀ i < 4, Foot F.data (Addr.add x i) := by
  intro i hi
  have e := toNat_add_of_fits (a := x) hi (by omega)
  exact hT.tab _ (by omega) (by omega)

/-! ## Between the `push` and the `pop` -/

theorem Mid.ld (hT : Te F Wl L g₀ V₀) (hM : Mid g₀ V₀ g V) : ∀ i < 8, Foot F.data (Addr.add g.rsp i) := by
  rw [hM.1]
  intro i hi
  exact hT.ld i (by omega)

/-- After the `pop`, at a `ret`. -/
theorem Mid.fh (hM : Mid g₀ V₀ g V) (hT : Te F Wl L g₀ V₀) {j : Nat} (hj : j = 99 ∨ j = 171 ∨ j = 246 ∨ j = 332)
    {g' : Gprs} (hs : g'.rsp = g.rsp + 8) (hb : g'.rbx = ofBytesLE 64 (List.map V (byteAddrs g.rsp 8)))
    (hp : g'.rbp = g.rbp) (h12 : g'.r12 = g.r12) (h13 : g'.r13 = g.r13) (h14 : g'.r14 = g.r14)
    (h15 : g'.r15 = g.r15) : Fh g₀ V₀ j g' V := by
  obtain ⟨m1, m2, m3, m4, m5, m6, rfl⟩ := hM
  refine ⟨hj, ?_, ?_, hp.trans m2, h12.trans m3, h13.trans m4, h14.trans m5, h15.trans m6, rfl⟩
  · rw [hs, m1]; exact BitVec.sub_add_cancel _ _
  · rw [hb, m1]; exact pop_self hT

theorem cp_rdi {cpu : Nat} {x : BitVec 64} (h : g.rdi = x) : (cpuidG prof cpu g).rdi = x := by
  cases g; exact h

theorem cp_mid {cpu : Nat} (h : Mid g₀ V₀ g V) : Mid g₀ V₀ (cpuidG prof cpu g) V := by
  cases g; exact h

/-! ## The cut points -/

theorem vc_0 (hT : Te F Wl L g₀ V₀) (h : Ih g₀ V₀ 0 n g V) : W_0 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rfl, rfl, rfl⟩ := h
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0]
  exact ⟨hT.st, Or.inl ⟨8, by decide, rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩⟩

theorem vc_6 (h : Ih g₀ V₀ 6 n g V) :
    ∀ cpu, cpu < max prof.cpus 1 → ∀ fl, Nx g₀ V₀ n 8 (cpuidG prof cpu g) fl V := by
  obtain ⟨rfl, hd, hM⟩ := h
  intro cpu _ fl
  exact Or.inl ⟨7, by decide, rfl, cp_rdi hd, cp_mid hM⟩

theorem vc_39 (h : Ih g₀ V₀ 39 n g V) :
    ∀ cpu, cpu < max prof.cpus 1 → ∀ fl, Nx g₀ V₀ n 41 (cpuidG prof cpu g) fl V := by
  obtain ⟨rfl, hd, hM⟩ := h
  intro cpu _ fl
  exact Or.inl ⟨5, by decide, rfl, cp_rdi hd, cp_mid hM⟩

theorem vc_8 (h : Ih g₀ V₀ 8 n g V) : W_8 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rfl, hd, hM⟩ := h
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_8, W_16, W_37, o1, o2, o3, Op.setcc]
  refine ⟨fun _ => Or.inl ⟨3, by decide, rfl, hM⟩, fun _ => ?_⟩
  intros
  exact ⟨fun _ => Or.inl ⟨3, by decide, rfl, hM⟩, fun _ => Or.inl ⟨6, by decide, rfl, hd, hM⟩⟩

theorem vc_41 (hT : Te F Wl L g₀ V₀) (h : Ih g₀ V₀ 41 n g V) : W_41 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rfl, hd, hM⟩ := h
  have hr : g.rdi = 188#64 ∨ g.rdi = 191#64 ∨ g.rdi = 194#64 := by rw [hd]; exact hT.rdi
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have hr' : rdi = 188#64 ∨ rdi = 191#64 ∨ rdi = 194#64 := hr
  wpx [W_41, W_49, o4, o5, cond_15, subF_of, subF_sf]
  rcases hr' with rfl | rfl | rfl <;>
    exact ⟨fun _ => Or.inl ⟨4, by decide, rfl, hd, hM⟩, fun h => absurd h (by decide)⟩

theorem vc_54 (hT : Te F Wl L g₀ V₀) (h : Ih g₀ V₀ 54 n g V) : W_54 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rfl, hd, hM⟩ := h
  have hr : g.rdi = 188#64 ∨ g.rdi = 191#64 ∨ g.rdi = 194#64 := by rw [hd]; exact hT.rdi
  have hj := jt_rd hT hM
  have hft := tab4 hT
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have hr' : rdi = 188#64 ∨ rdi = 191#64 ∨ rdi = 194#64 := hr
  wpx [W_54, W_69, o6, o7, Op.ldsx]
  rcases hr' with rfl | rfl | rfl
  · refine ⟨fun h => absurd h (by decide), fun _ => ⟨hft _ (by decide) (by decide), ?_⟩⟩
    simp (disch := decide) only [hj 0 (by decide)]
    exact ⟨160, lt_len (by decide), by decide +kernel, Or.inl ⟨3, by decide, rfl, hM⟩⟩
  · refine ⟨fun h => absurd h (by decide), fun _ => ⟨hft _ (by decide) (by decide), ?_⟩⟩
    simp (disch := decide) only [hj 3 (by decide)]
    exact ⟨224, lt_len (by decide), by decide +kernel, Or.inl ⟨3, by decide, rfl, hM⟩⟩
  · refine ⟨fun h => absurd h (by decide), fun _ => ⟨hft _ (by decide) (by decide), ?_⟩⟩
    simp (disch := decide) only [hj 6 (by decide)]
    exact ⟨312, lt_len (by decide), by decide +kernel, Or.inl ⟨3, by decide, rfl, hM⟩⟩

theorem vc_96 (h : Ih g₀ V₀ 96 n g V) : W_96 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rfl, hM⟩ := h
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_96, o8]
  intros
  exact Or.inl ⟨2, by decide, rfl, hM⟩

theorem vc_98 (hT : Te F Wl L g₀ V₀) (h : Ih g₀ V₀ 98 n g V) : W_98 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rfl, hM⟩ := h
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_98, o9]
  exact ⟨hM.ld hT, Or.inr (hM.fh hT (by decide) rfl rfl rfl rfl rfl rfl rfl)⟩

theorem vc_160 (hT : Te F Wl L g₀ V₀) (h : Ih g₀ V₀ 160 n g V) : W_160 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rfl, hM⟩ := h
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_160, o10]
  refine ⟨hM.ld hT, ?_⟩
  intros
  exact Or.inr (hM.fh hT (by decide) rfl rfl rfl rfl rfl rfl rfl)

theorem vc_224 (hT : Te F Wl L g₀ V₀) (h : Ih g₀ V₀ 224 n g V) : W_224 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rfl, hM⟩ := h
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_224, W_235, o11, o12, Op.testh, gvh]
  intros
  refine ⟨fun _ => Or.inl ⟨2, by decide, rfl, hM⟩, fun _ => ⟨hM.ld hT, ?_⟩⟩
  intros
  exact Or.inr (hM.fh hT (by decide) rfl rfl rfl rfl rfl rfl rfl)

theorem vc_312 (hT : Te F Wl L g₀ V₀) (h : Ih g₀ V₀ 312 n g V) : W_312 F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rfl, hM⟩ := h
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_312, W_323, o13, o14, Op.testh, gvh]
  intros
  refine ⟨fun _ => Or.inl ⟨2, by decide, rfl, hM⟩, fun _ => ⟨hM.ld hT, ?_⟩⟩
  intros
  exact Or.inr (hM.fh hT (by decide) rfl rfl rfl rfl rfl rfl rfl)

theorem vcAll (hT : Te F Wl L g₀ V₀) (ℓ : Nat) :
    ∀ n g f V, Ih g₀ V₀ ℓ n g V → WtC prof F Wl ℓ (Nx g₀ V₀ n) g f V := by
  intro n g f V h
  by_cases h0 : ℓ = 0
  · subst h0; exact vc_0 hT h
  by_cases h6 : ℓ = 6
  · subst h6; exact vc_6 h
  by_cases h8 : ℓ = 8
  · subst h8; exact vc_8 h
  by_cases h39 : ℓ = 39
  · subst h39; exact vc_39 h
  by_cases h41 : ℓ = 41
  · subst h41; exact vc_41 hT h
  by_cases h54 : ℓ = 54
  · subst h54; exact vc_54 hT h
  by_cases h96 : ℓ = 96
  · subst h96; exact vc_96 h
  by_cases h98 : ℓ = 98
  · subst h98; exact vc_98 hT h
  by_cases h160 : ℓ = 160
  · subst h160; exact vc_160 hT h
  by_cases h224 : ℓ = 224
  · subst h224; exact vc_224 hT h
  by_cases h312 : ℓ = 312
  · subst h312; exact vc_312 hT h
  · simp only [Ih, h0, h6, h8, h39, h41, h54, h96, h98, h160, h224, h312, ↓reduceIte] at h

/-- From a `ret`'s `Fh` to `Rh` after it. -/
theorem rh_of {j : Nat} (hF : Fh g₀ V₀ j g V) : Rh g₀ V₀ (g.set 4 (g.rsp + 8)) V := by
  obtain ⟨-, hs, hb, hp, h12, h13, h14, h15, hV⟩ := hF
  cases g
  exact ⟨congrArg (· + 8) hs, hb, hp, h12, h13, h14, h15, hV⟩

/-- `handle_amd` in a run with its code. -/
theorem ham_fnK (c : Seg prof F Wl L s₀ o) (hin : CodeIn L hca_at hca) :
    FnK prof F Wl L s₀ o hca_at (Te F Wl L) Rh := by
  refine ⟨?_⟩
  intro gev gP gE X t V hK hA hrip hT k
  refine cfgAt (spC c hin) (fun ℓ n g _ V' => Ih X.cpu.gpr V ℓ n g V') (fun j g _ V' => Fh X.cpu.gpr V j g V')
    (fun ℓ n g f V' h => vcAll hT ℓ n g f V' h) ?_ 9 0 hK hA (by rw [addr_add_zero]; exact hrip) ⟨rfl, rfl, rfl⟩
  intro j g fl V' hF Y t' hKY hAY hrY hg _
  have hF' := hF
  obtain ⟨hj, hs, -, -, -, -, -, -, hV⟩ := hF
  obtain ⟨e₂, code₂, j₂, hin₂, hj₂, hra⟩ := hT.ret
  have hl : ∀ i < 8, Foot F.data (Addr.add Y.cpu.gpr.rsp i) := by
    rw [hg, hs]; exact ld8 hT
  have hra' : ofBytesLE 64 ((byteAddrs Y.cpu.gpr.rsp 8).map V') = e₂.add j₂ := by
    rw [hg, hs, hV, rd_ret hT]; exact hra
  refine c.s_ret hKY hAY hin (ret_at _ hj).1 hrY (ret_at _ hj).2 hl hin₂ hj₂ hra' ?_
  rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
  exact k Z t₂ V' hKZ hAZ (hrZ.trans hra.symm) (by rw [hgZ, hg]; exact rh_of hF')

end FV7z.Hca
