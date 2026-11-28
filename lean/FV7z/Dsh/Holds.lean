import FV7z.Dsh.Cuts
import FV7z.Close.Holds
/-!
# `_dl_setup_hash` fills in a link map's hash table fields (PLAN.md G3, startup)

glibc 2.31's `_dl_setup_hash (map)` at `0x6ab020` in `7zzs`, `map` = `rdi`. With `map->l_info[DT_GNU_HASH]` (the 8
bytes at `map + 0x2a0`, `ghp`) not 0, it reads the GNU hash table's header at its `d_ptr` (`cG`) and stores
`l_nbuckets` (`map + 0x2f4`), `l_gnu_bitmask_idxbits` (`+ 0x2f8`), `l_gnu_shift` (`+ 0x2fc`), `l_gnu_bitmask`
(`+ 0x300`), `l_gnu_buckets` (`+ 0x308`) and `l_gnu_chain_zero` (`+ 0x310`), then `ret` (97); when the bitmask's word
count is not a power of two, `__assert_fail` (148), not covered. Else with `map->l_info[DT_HASH]` (`map + 0x60`, `hs`)
0 it returns at once (147); not 0, it stores `l_nchain` (`+ 0x310`), `l_nbuckets` and `l_buckets` (`+ 0x308`) from the
SysV table and returns (147).

- `ret_97`, `ret_147`: the two `ret`s; `vc_g`, `vc_n`, `vc_s`: the verification condition of the code from the entry,
  one for each way (GNU table; no table; SysV table).
- `dsh_ok`: under `Hy` (what the run reads and stores in the footprints, the power of two), with the stores apart
  from the return address, the run reaches the return address with the memory `Vr` (the stores of the way taken),
  `rsp` 8 up and the callee-saved registers as at the entry (`Kd`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Dsh

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_97 : pret <+: dsh.drop 97 := by decide +kernel
theorem ret_97 (feat : Features) : Dec feat dsh 97 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 97) (k := 0) (pret_0 feat) w_97 (Nat.zero_le _)
theorem w_147 : pret <+: dsh.drop 147 := by decide +kernel
theorem ret_147 (feat : Features) : Dec feat dsh 147 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 147) (k := 0) (pret_0 feat) w_147 (Nat.zero_le _)

/-! ## The values -/

/-- `map->l_info[DT_GNU_HASH]`. -/
abbrev ghp (V : Addr → Byte) (g : Gprs) : BitVec 64 := rdq(V, g.rdi + 672#64)
/-- Its `d_ptr`: the GNU hash table. -/
abbrev cG (V : Addr → Byte) (g : Gprs) : BitVec 64 := rdq(V, ghp V g + 8#64)
/-- Its bucket count. -/
abbrev nb (V : Addr → Byte) (g : Gprs) : BitVec 32 := rdd(V, cG V g)
/-- After `map->l_nbuckets` is stored. -/
abbrev V1 (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst V (g.rdi + 756#64) (toBytesLE (nb V g) 4)
/-- The bitmask's word count (read after the first store). -/
abbrev bm (V : Addr → Byte) (g : Gprs) : BitVec 32 := rdd(V1 V g, cG V g + 8#64)
/-- The symbol bias. -/
abbrev sb (V : Addr → Byte) (g : Gprs) : BitVec 32 := rdd(V1 V g, cG V g + 4#64)
/-- The word count less one (`l_gnu_bitmask_idxbits`). -/
abbrev mk1 (V : Addr → Byte) (g : Gprs) : BitVec 32 :=
  BitVec.setWidth 32 (BitVec.setWidth 64 (bm V g) + 18446744073709551615#64)
/-- After `map->l_gnu_bitmask_idxbits` is stored. -/
abbrev V2 (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst (V1 V g) (g.rdi + 760#64) (toBytesLE (mk1 V g) 4)
/-- The shift (read after the second store). -/
abbrev sh (V : Addr → Byte) (g : Gprs) : BitVec 32 := rdd(V2 V g, cG V g + 12#64)
/-- `l_gnu_buckets`. -/
abbrev bk (V : Addr → Byte) (g : Gprs) : BitVec 64 :=
  cG V g + 16#64 + BitVec.setWidth 64 (bm V g + bm V g) * 4#64
/-- `l_gnu_chain_zero`. -/
abbrev ch (V : Addr → Byte) (g : Gprs) : BitVec 64 :=
  bk V g + (BitVec.setWidth 64 (nb V g) - BitVec.setWidth 64 (sb V g)) * 4#64
/-- The memory after the GNU way. -/
abbrev VG (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst (V2 V g) (g.rdi + 768#64) (toBytesLE (cG V g + 16#64) 8)) (g.rdi + 776#64)
    (toBytesLE (bk V g) 8)) (g.rdi + 764#64) (toBytesLE (sh V g) 4)) (g.rdi + 784#64) (toBytesLE (ch V g) 8)

/-- `map->l_info[DT_HASH]`. -/
abbrev hs (V : Addr → Byte) (g : Gprs) : BitVec 64 := rdq(V, g.rdi + 96#64)
/-- Its `d_ptr`: the SysV hash table. -/
abbrev dS (V : Addr → Byte) (g : Gprs) : BitVec 64 := rdq(V, hs V g + 8#64)
/-- Its bucket count. -/
abbrev nc (V : Addr → Byte) (g : Gprs) : BitVec 32 := rdd(V, dS V g)
/-- The memory after the SysV way. -/
abbrev VS (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst V (g.rdi + 784#64) (toBytesLE (dS V g + 8#64) 8)) (g.rdi + 756#64) (toBytesLE (nc V g) 4))
    (g.rdi + 776#64) (toBytesLE (dS V g + 8#64 + BitVec.setWidth 64 (nc V g) * 4#64) 8)

/-- The memory at the return, by the way taken. -/
def Vr (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  bif ghp V g == 0 then (bif hs V g == 0 then V else VS V g) else VG V g

/-- The registers the code keeps: `rsp` and the callee-saved ones. -/
abbrev Fd (g0 g : Gprs) : Prop :=
  g.rsp = g0.rsp ∧ g.rbx = g0.rbx ∧ g.rbp = g0.rbp ∧ g.r12 = g0.r12 ∧ g.r13 = g0.r13 ∧ g.r14 = g0.r14 ∧
    g.r15 = g0.r15

/-- At the return address: `rsp` 8 up, the callee-saved registers as at the entry. -/
abbrev Kd (g0 g : Gprs) : Prop :=
  g.rsp = g0.rsp + 8 ∧ g.rbx = g0.rbx ∧ g.rbp = g0.rbp ∧ g.r12 = g0.r12 ∧ g.r13 = g0.r13 ∧ g.r14 = g0.r14 ∧
    g.r15 = g0.r15

/-! ## The ways -/

/-- What the GNU way needs: the word count a power of two, the reads and the stores in the footprints. -/
structure HyG (F : Footprint) (Wl : List Rgn) (V : Addr → Byte) (g : Gprs) : Prop where
  hz : (mk1 V g &&& bm V g == 0) = true
  fgh : ∀ i < 8, Foot F.data (Addr.add (ghp V g + 8#64) i)
  fc0 : ∀ i < 4, Foot F.data (Addr.add (cG V g) i)
  fc8 : ∀ i < 4, Foot F.data (Addr.add (cG V g + 8#64) i)
  fc4 : ∀ i < 4, Foot F.data (Addr.add (cG V g + 4#64) i)
  fc12 : ∀ i < 4, Foot F.data (Addr.add (cG V g + 12#64) i)
  w756 : ∀ i < 4, Foot Wl (Addr.add (g.rdi + 756#64) i)
  w760 : ∀ i < 4, Foot Wl (Addr.add (g.rdi + 760#64) i)
  w768 : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 768#64) i)
  w776 : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 776#64) i)
  w764 : ∀ i < 4, Foot Wl (Addr.add (g.rdi + 764#64) i)
  w784 : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 784#64) i)

/-- What the SysV way needs when there is a table. -/
structure HyS (F : Footprint) (Wl : List Rgn) (V : Addr → Byte) (g : Gprs) : Prop where
  fhs : ∀ i < 8, Foot F.data (Addr.add (hs V g + 8#64) i)
  fd : ∀ i < 4, Foot F.data (Addr.add (dS V g) i)
  w784 : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 784#64) i)
  w756 : ∀ i < 4, Foot Wl (Addr.add (g.rdi + 756#64) i)
  w776 : ∀ i < 8, Foot Wl (Addr.add (g.rdi + 776#64) i)

/-- What the run needs, by the way it takes. -/
structure Hy (F : Footprint) (Wl : List Rgn) (V : Addr → Byte) (g : Gprs) : Prop where
  f672 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 672#64) i)
  gnu : (ghp V g == 0) = false → HyG F Wl V g
  f96 : (ghp V g == 0) = true → ∀ i < 8, Foot F.data (Addr.add (g.rdi + 96#64) i)
  sysv : (ghp V g == 0) = true → (hs V g == 0) = false → HyS F Wl V g

variable {F : Footprint} {Wl : List Rgn}

/-- The GNU way: the loads, the six stores, the power-of-two check, to the `ret` at 97. -/
theorem vc_g {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (hg : (ghp V g == 0) = false)
    (f672 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 672#64) i)) (H : HyG F Wl V g)
    (h : ∀ g' fl, Fd g g' → Q 97 g' fl (VG V g)) :
    W_0 F Wl Q g f V := by
  obtain ⟨hz, fgh, fc0, fc8, fc4, fc12, w756, w760, w768, w776, w764, w784⟩ := H
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Fd, VG, V2, V1, ch, bk, sh, mk1, bm, sb, nb, cG, ghp] at hg hz f672 fgh fc0 fc8 fc4 fc12 w756 w760
    w768 w776 w764 w784 h
  wpx [W_0, W_16, W_43, W_104, W_113, o0, o1, o2, o3, o4, BitVec.and_self, hg, hz, Bool.not_true, Bool.not_false,
    Bool.true_eq_false, Bool.false_eq_true, false_implies, true_implies, and_true, true_and, implies_true]
  all_goals repeat' (first | refine h _ _ ?_ | rfl | assumption | exact trivial | apply And.intro | intro _)

/-- No table: `map->l_info[DT_HASH]` 0, to the `ret` at 147, nothing stored. -/
theorem vc_n {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (hg : (ghp V g == 0) = true)
    (hn : (hs V g == 0) = true)
    (f672 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 672#64) i))
    (f96 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 96#64) i))
    (h : ∀ g' fl, Fd g g' → Q 147 g' fl V) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Fd, hs, ghp] at hg hn f672 f96 h
  wpx [W_0, W_16, W_43, W_104, W_113, o0, o1, o2, o3, o4, BitVec.and_self, hg, hn, Bool.not_true, Bool.not_false,
    Bool.true_eq_false, Bool.false_eq_true, false_implies, true_implies, and_true, true_and, implies_true]
  all_goals repeat' (first | refine h _ _ ?_ | rfl | assumption | exact trivial | apply And.intro | intro _)

/-- The SysV way: the three stores, to the `ret` at 147. -/
theorem vc_s {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (hg : (ghp V g == 0) = true)
    (hn : (hs V g == 0) = false)
    (f672 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 672#64) i))
    (f96 : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 96#64) i)) (H : HyS F Wl V g)
    (h : ∀ g' fl, Fd g g' → Q 147 g' fl (VS V g)) :
    W_0 F Wl Q g f V := by
  obtain ⟨fhs, fd, w784, w756, w776⟩ := H
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Fd, VS, nc, dS, hs, ghp] at hg hn f672 f96 fhs fd w784 w756 w776 h
  wpx [W_0, W_16, W_43, W_104, W_113, o0, o1, o2, o3, o4, BitVec.and_self, hg, hn, Bool.not_true, Bool.not_false,
    Bool.true_eq_false, Bool.false_eq_true, false_implies, true_implies, and_true, true_and, implies_true]
  all_goals repeat' (first | refine h _ _ ?_ | rfl | assumption | exact trivial | apply And.intro | intro _)

/-! ## The return -/

/-- A read of 8 bytes apart from `[m + 756, m + 792)` past a store into it. -/
theorem rd_keep {V : Addr → Byte} {m x : Addr} (d k : Nat) {w : Nat} (v : BitVec w)
    (hdk : 756 ≤ d ∧ d < 792 ∧ d + k ≤ 792) (hm : m.toNat + 792 ≤ 2 ^ 64) (hx : x.toNat + 8 ≤ 2 ^ 64)
    (h : m.toNat + 792 ≤ x.toNat ∨ x.toNat + 8 ≤ m.toNat + 756) :
    List.map (Vst V (m + BitVec.ofNat 64 d) (toBytesLE v k)) (byteAddrs x 8) = List.map V (byteAddrs x 8) := by
  obtain ⟨h1, h2, h3⟩ := hdk
  have e : (m + BitVec.ofNat 64 d).toNat = m.toNat + d := toNat_add_of_fits (a := m) (i := d) (n := 792) h2 hm
  exact Tun.rd_Vst V _ _ x 8 (by rw [toBytesLE_length, e]; omega) hx (by rw [toBytesLE_length, e]; omega)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {V : Addr → Byte}

/-- From a `ret` of the function with `rsp` and the callee-saved registers as at the entry (`Fd`) to the return
address. -/
theorem fin_ret (c : Seg prof F Wl L s₀ o) (hin : CodeIn L dsh_at dsh) {j : Nat} (hj : j < dsh.length)
    (hd : Dec prof.feat dsh j (FV7z.mk .ret 64 [] 1)) {W : Addr → Byte} {Y : State} {t₁ : Nat}
    (hKY : KeptW Wl s₀ Y) (hAY : Agree F Y.proc.mm.mem W) (hrY : Y.cpu.rip = dsh_at.add j)
    (hF : Fd X.cpu.gpr Y.cpu.gpr) (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map W) = e₂.add j₂)
    (k : ∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W → Z.cpu.rip = e₂.add j₂ →
      Kd X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE Y t₁ := by
  refine c.s_ret hKY hAY hin hj hrY hd (by rw [hF.1]; exact hl) hin₂ h₂ (by rw [hF.1]; exact hra) ?_
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  refine k Z t' hKZ hAZ hrZ ?_
  rw [hgZ]
  exact ⟨by rw [hF.1]; try rfl, hF.2.1, hF.2.2.1, hF.2.2.2.1, hF.2.2.2.2.1, hF.2.2.2.2.2.1, hF.2.2.2.2.2.2⟩

/-- `_dl_setup_hash (map)`, `map` = `rdi`: the run reaches the return address with the hash table fields stored
(`Vr`), `rsp` 8 up and the callee-saved registers as at the entry. -/
theorem dsh_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L dsh_at dsh) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = dsh_at) (H : Hy F Wl V X.cpu.gpr)
    (hm : X.cpu.gpr.rdi.toNat + 792 ≤ 2 ^ 64)
    (hdr : X.cpu.gpr.rdi.toNat + 792 ≤ X.cpu.gpr.rsp.toNat ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat + 756)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) (hsp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (k : ∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Vr V X.cpu.gpr) → Z.cpu.rip = e₂.add j₂ →
      Kd X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  cases hg : (ghp V X.cpu.gpr == 0)
  · have eV : Vr V X.cpu.gpr = VG V X.cpu.gpr := by simp only [Vr, hg, cond_false]
    refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 97 ∧ Fd X.cpu.gpr g' ∧ V' = VG V X.cpu.gpr) hK hA
      (by rw [addr_add_zero]; exact hrip) (vc_g hg H.f672 (H.gnu hg) fun _ _ a => ⟨rfl, a, rfl⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hF, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁ hgY
    refine fin_ret c hin (lt_len (by decide)) (ret_97 _) hKY hAY hrY hF hl hin₂ h₂ ?_ (by rw [← eV]; exact k)
    dsimp only [VG, V2, V1]
    rw [rd_keep 784 8 _ (by decide) hm hsp8 hdr, rd_keep 764 4 _ (by decide) hm hsp8 hdr,
      rd_keep 776 8 _ (by decide) hm hsp8 hdr, rd_keep 768 8 _ (by decide) hm hsp8 hdr,
      rd_keep 760 4 _ (by decide) hm hsp8 hdr, rd_keep 756 4 _ (by decide) hm hsp8 hdr]
    exact hra
  · cases hn : (hs V X.cpu.gpr == 0)
    · have eV : Vr V X.cpu.gpr = VS V X.cpu.gpr := by simp only [Vr, hg, hn, cond_true, cond_false]
      refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 147 ∧ Fd X.cpu.gpr g' ∧ V' = VS V X.cpu.gpr) hK hA
        (by rw [addr_add_zero]; exact hrip)
        (vc_s hg hn H.f672 (H.f96 hg) (H.sysv hg hn) fun _ _ a => ⟨rfl, a, rfl⟩) ?_
      rintro j' g fl V₁ ⟨rfl, hF, hV₁⟩ Y t₁ hKY hAY hrY hgY -
      subst V₁ hgY
      refine fin_ret c hin (lt_len (by decide)) (ret_147 _) hKY hAY hrY hF hl hin₂ h₂ ?_ (by rw [← eV]; exact k)
      dsimp only [VS]
      rw [rd_keep 776 8 _ (by decide) hm hsp8 hdr, rd_keep 756 4 _ (by decide) hm hsp8 hdr,
        rd_keep 784 8 _ (by decide) hm hsp8 hdr]
      exact hra
    · have eV : Vr V X.cpu.gpr = V := by simp only [Vr, hg, hn, cond_true]
      refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 147 ∧ Fd X.cpu.gpr g' ∧ V' = V) hK hA
        (by rw [addr_add_zero]; exact hrip) (vc_n hg hn H.f672 (H.f96 hg) fun _ _ a => ⟨rfl, a, rfl⟩) ?_
      rintro j' g fl V₁ ⟨rfl, hF, hV₁⟩ Y t₁ hKY hAY hrY hgY -
      subst V₁ hgY
      exact fin_ret c hin (lt_len (by decide)) (ret_147 _) hKY hAY hrY hF hl hin₂ h₂ hra (by rw [← eV]; exact k)

end FV7z.Dsh
