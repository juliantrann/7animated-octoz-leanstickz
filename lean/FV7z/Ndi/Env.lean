import FV7z.Ndi.Calls
import FV7z.Ndi.Mem
import FV7z.Genv.Holds
/-!
# `_dl_non_dynamic_init`: a `getenv` from its body (PLAN.md G3, startup)

Between its prologue and its epilogue the function's stack pointer is one value, `sp`. What it calls stores below
`sp` only: `getenv` 72 bytes with its return address, `strlen` its return address, `_dl_protect_relro` 24.

- `Scr sp`: the 72 bytes below `sp`. `Eqo sp W M`: the bytes `W` are `M` but for those.
- `Ev`, `Ev.Ok`: the environment (`__environ`, its `N` strings), above `sp`. `NmOk`: a name `getenv` is called with,
  in the image below the data segment, that no string of the environment begins with.
- `par_ok`: these are what `Genv.getenv_none` needs (`Genv.Par.Ok`), for bytes that are the environment's above `sp`
  and the image's below the data segment.
- `ge`: a `call` of `getenv` in the body, to the instruction after it: `rax` null, `rsp` and `r15` kept, the bytes
  outside `Scr sp` kept.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Sga (vo vr vs)
namespace FV7z.Ndi

/-- A byte of the 72 below `sp`. -/
def Scr (sp a : Addr) : Prop := sp.toNat - 72 ≤ a.toNat ∧ a.toNat < sp.toNat

/-- `W` is `M` but for the 72 bytes below `sp`. -/
def Eqo (sp : Addr) (W M : Addr → Byte) : Prop := ∀ a, ¬ Scr sp a → W a = M a

theorem Vst_congr {P : Addr → Prop} : ∀ (bs : List Byte) (W M : Addr → Byte) (x : Addr),
    (∀ a, P a → W a = M a) → ∀ a, P a → Vst W x bs a = Vst M x bs a
  | [], _, _, _, h, a, ha => h a ha
  | b :: bs, W, M, x, h, a, ha => by
    simp only [Vst]
    refine Vst_congr bs _ _ _ (fun y hy => ?_) a ha
    simp only [upd1]
    split
    · rfl
    · exact h y hy

theorem Eqo.refl (sp : Addr) (W : Addr → Byte) : Eqo sp W W := fun _ _ => rfl

/-- The same store in both. -/
theorem Eqo.st {sp : Addr} {W M : Addr → Byte} (h : Eqo sp W M) (x : Addr) (bs : List Byte) :
    Eqo sp (Vst W x bs) (Vst M x bs) := Vst_congr bs W M x h

/-- Bytes that differ from `W`'s below `sp` only. -/
theorem Eqo.scr {sp : Addr} {W W' M : Addr → Byte} (h : Eqo sp W M) (h' : ∀ a, ¬ Scr sp a → W' a = W a) :
    Eqo sp W' M := fun a ha => (h' a ha).trans (h a ha)

/-- A store below `sp`. -/
theorem Eqo.push {sp : Addr} {W M : Addr → Byte} (h : Eqo sp W M) {x : Addr} {bs : List Byte}
    (h1 : sp.toNat - 72 ≤ x.toNat) (h2 : x.toNat + bs.length ≤ sp.toNat) : Eqo sp (Vst W x bs) M := by
  refine h.scr fun a ha => vo rfl (by have := sp.isLt; omega) ?_
  unfold Scr at ha
  omega

/-- What a load not below `sp` reads. -/
theorem Eqo.rd {sp : Addr} {W M : Addr → Byte} (h : Eqo sp W M) {x : Addr} {n : Nat}
    (hx : ∀ i < n, ¬ Scr sp (Addr.add x i)) : List.map W (byteAddrs x n) = List.map M (byteAddrs x n) := by
  refine List.map_congr_left fun a ha => ?_
  obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 ha
  exact h _ (hx i hi)

/-- No byte of `n` from `x` is below `sp`, if they end 72 under it or begin at it. -/
theorem scr_out {sp x : Addr} {n : Nat} (hf : x.toNat + n ≤ 2 ^ 64)
    (h : x.toNat + n + 72 ≤ sp.toNat ∨ sp.toNat ≤ x.toNat) : ∀ i < n, ¬ Scr sp (Addr.add x i) := by
  intro i hi
  have e : (Addr.add x i).toNat = x.toNat + i := toNat_add_of_fits hi hf
  unfold Scr
  rw [e]
  omega

/-- What a load from the image reads, the stack 72 bytes or more above it. -/
theorem Eqo.rdi {sp : Addr} {W M : Addr → Byte} (h : Eqo sp W M) (h72 : 8032256 + 72 ≤ sp.toNat) (x : Addr) (n : Nat)
    (hx : x.toNat + n ≤ 8032256) : List.map W (byteAddrs x n) = List.map M (byteAddrs x n) :=
  h.rd (scr_out (by omega) (.inl (by omega)))

/-- The environment: the array `envp` of `N` strings' addresses `ptr`, their lengths `len`. -/
structure Ev where
  envp : Addr
  N : Nat
  ptr : Nat → Addr
  len : Nat → Nat

/-- The environment in the bytes `V`, above `sp`: `__environ` (`0x7a4798`) is `envp`, not null; `envp` has the `N`
strings' addresses and a null; each string has `len i` characters and a 0, its pages and the byte after its first
read. -/
structure Ev.Ok (E : Ev) (V : Addr → Byte) (F : Footprint) (sp : Addr) : Prop where
  he : rdq(V, 8013720#64) = E.envp
  he0 : E.envp ≠ 0
  ehi : sp.toNat ≤ E.envp.toNat
  efit : E.envp.toNat + 8 * (E.N + 1) ≤ 2 ^ 64
  erd : ∀ k < 8 * (E.N + 1), Foot F.data (Addr.add E.envp k)
  eptr : ∀ i ≤ E.N, rdq(V, Addr.add E.envp (8 * i)) = E.ptr i
  enz : ∀ i < E.N, E.ptr i ≠ 0
  eend : E.ptr E.N = 0
  shi : ∀ i < E.N, sp.toNat ≤ (E.ptr i).toNat
  sfit : ∀ i < E.N, (E.ptr i).toNat + E.len i + 2 ≤ 2 ^ 64
  sz : ∀ i < E.N, V (Addr.add (E.ptr i) (E.len i)) = 0
  spg : ∀ i < E.N, ∀ x : Addr, (E.ptr i).toNat / 4096 ≤ x.toNat / 4096 →
    x.toNat / 4096 ≤ ((E.ptr i).toNat + E.len i) / 4096 → Foot F.data x
  s2 : ∀ i < E.N, Foot F.data (Addr.add (E.ptr i) 1)

/-- A name `getenv` is called with: `n ≥ 2` characters at `a` and a 0, in the image below the data segment, its pages
read; no string of the environment begins with the name and `=`. -/
structure NmOk (E : Ev) (V : Addr → Byte) (F : Footprint) (a : Addr) (n : Nat) : Prop where
  hn : 2 ≤ n
  lo : a.toNat + n < 7827456
  nnz : ∀ k < n, V (Addr.add a k) ≠ 0
  nz : V (Addr.add a n) = 0
  npg : ∀ x : Addr, a.toNat / 4096 ≤ x.toNat / 4096 → x.toNat / 4096 ≤ (a.toNat + n) / 4096 → Foot F.data x
  nom : ∀ i < E.N, (∀ k < n, V (Addr.add (E.ptr i) k) = V (Addr.add a k)) → V (Addr.add (E.ptr i) n) ≠ 61#8

/-- A one-byte load. -/
theorem rdb1 (V : Addr → Byte) (p : Addr) : rdb(V, p) = V p := by
  rw [byteAddrs_succ]
  simp [byteAddrs, ofBytesLE]

theorem t8 (sp : BitVec 64) (h : 8 ≤ sp.toNat) : (sp - 8#64).toNat = sp.toNat - 8 := by bv_omega
theorem t72 (sp : BitVec 64) : sp - 8#64 - 64#64 = sp - 72#64 := by bv_omega
theorem u8 (sp : BitVec 64) : sp - 8#64 + 8#64 = sp := by bv_omega

variable {F : Footprint} {Wl : List Rgn}

/-- What `getenv` needs, called from the body with the name at `a`: the bytes `W` are `V`'s outside the data segment
and the 72 bytes below `sp`, and `__environ` is still `envp`. -/
theorem par_ok {E : Ev} {V W : Addr → Byte} {g : Gprs} {sp a : Addr} {n : Nat} (hE : E.Ok V F sp)
    (hN : NmOk E V F a n) (h72 : 8032256 + 72 ≤ sp.toNat)
    (hWo : ∀ x : Addr, ¬ Scr sp x → (x.toNat < 7827456 ∨ 8032256 ≤ x.toNat) → W x = V x)
    (hWe : rdq(W, 8013720#64) = E.envp) (hstk : ∀ i < 72, Foot Wl (Addr.add (sp - 72#64) i))
    (hrd : ∀ i < 8, Foot F.data (Addr.add (sp - 8#64) i)) (hfe : ∀ i < 8, Foot F.data (Addr.add 8013720#64 i))
    (hg : g.rsp = sp - 8#64) (hdi : g.rdi = a) : Genv.Par.Ok ⟨g, W, n, E.envp, E.N, E.ptr, E.len⟩ F Wl := by
  have hlt := sp.isLt
  have e8 := t8 sp (by omega)
  have up : ∀ x : Addr, sp.toNat ≤ x.toNat → W x = V x := fun x hx =>
    hWo x (by unfold Scr; omega) (.inr (by omega))
  have lo : ∀ x : Addr, x.toNat < 7827456 → W x = V x := fun x hx => hWo x (by unfold Scr; omega) (.inl hx)
  have nf : ∀ x : Addr, x.toNat + 72 < sp.toNat ∨ sp.toNat ≤ x.toNat →
      ¬ Genv.InFr ⟨g, W, n, E.envp, E.N, E.ptr, E.len⟩ x := by
    intro x hx
    unfold Genv.InFr
    dsimp only
    rw [hg, e8]
    omega
  have an : ∀ k ≤ n, (Addr.add a k).toNat = a.toNat + k := fun k hk =>
    toNat_add_of_fits (n := n + 1) (by omega) (by have := hN.lo; omega)
  have ae : ∀ k < 8 * (E.N + 1), (Addr.add E.envp k).toNat = E.envp.toNat + k := fun k hk =>
    toNat_add_of_fits hk hE.efit
  have as : ∀ i < E.N, ∀ k ≤ E.len i + 1, (Addr.add (E.ptr i) k).toNat = (E.ptr i).toNat + k := fun i hi k hk =>
    toNat_add_of_fits (n := E.len i + 2) (by omega) (hE.sfit i hi)
  have hlo := hN.lo
  have c0 : (8013720#64).toNat = 8013720 := rfl
  constructor <;> try dsimp only
  case hsp => rw [hg, e8]; omega
  case stk => exact fun i hi => by rw [hg, t72]; exact hstk i (by omega)
  case ret => exact fun i hi => by rw [hg]; exact hrd i hi
  case top => rw [hg, e8]; omega
  case fe => exact hfe
  case oe => exact fun i hi => nf _ (.inl (by rw [toNat_add_of_fits hi (by decide), c0]; omega))
  case he => exact hWe
  case he0 => exact hE.he0
  case hn => exact hN.hn
  case nfit => rw [hdi]; omega
  case nnz =>
    intro k hk
    rw [hdi, lo _ (by rw [an k (by omega)]; omega)]
    exact hN.nnz k hk
  case nz =>
    rw [hdi, lo _ (by rw [an n (Nat.le_refl _)]; omega)]
    exact hN.nz
  case npg => rw [hdi]; exact hN.npg
  case nout =>
    intro k hk
    rw [hdi]
    exact nf _ (.inl (by rw [an k hk]; omega))
  case efit => exact hE.efit
  case erd => exact hE.erd
  case eout => exact fun k hk => nf _ (.inr (by rw [ae k hk]; have := hE.ehi; omega))
  case eptr =>
    intro i hi
    rw [← hE.eptr i hi]
    refine congrArg _ (List.map_congr_left fun x hx => ?_)
    obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hx
    refine up _ ?_
    rw [addr_add_add, ae _ (by omega)]
    have := hE.ehi
    omega
  case enz => exact hE.enz
  case eend => exact hE.eend
  case sfit => exact hE.sfit
  case sz =>
    intro i hi
    rw [up _ (by rw [as i hi _ (by omega)]; have := hE.shi i hi; omega)]
    exact hE.sz i hi
  case spg => exact hE.spg
  case s2 => exact hE.s2
  case sout => exact fun i hi k hk => nf _ (.inr (by rw [as i hi k hk]; have := hE.shi i hi; omega))
  case nom =>
    intro i hi h
    rw [hdi] at h
    have us : ∀ k ≤ E.len i + 1, W (Addr.add (E.ptr i) k) = V (Addr.add (E.ptr i) k) := fun k hk =>
      up _ (by rw [as i hi k hk]; have := hE.shi i hi; omega)
    have ln : n ≤ E.len i := by
      refine Nat.le_of_not_lt fun hlt' => hN.nnz _ hlt' ?_
      rw [← lo _ (by rw [an _ (by omega)]; omega), ← h _ hlt', us _ (by omega)]
      exact hE.sz i hi
    rw [us n (by omega)]
    refine hN.nom i hi fun k hk => ?_
    rw [← us k (by omega), h k hk]
    exact lo _ (by rw [an k (by omega)]; omega)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}

/-- A `call` of `getenv` in the body (at `j`), the name at `a` one no string of the environment begins with: the run
reaches the instruction after the `call` with `rax` null, `rsp` and `r15` as they were, and the bytes outside the 72
below `sp` as they were. -/
theorem ge {pl pc : List Byte} {Pm : (Addr → Byte) → Prop} {E : Ev} {V W : Addr → Byte} {sp a : Addr}
    {n j rel : Nat} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ndi_at ndi)
    (hig : CodeIn L Genv.gev_at Genv.gev)
    (hil : CodeIn L 4198664#64 pl) (hl0 : 0 < pl.length) (hlen : Str.LenAt prof L o 4198664#64 Pm)
    (hic : CodeIn L 4198472#64 pc) (hc0 : 0 < pc.length) (hcmp : Str.NcmpAt prof L o 4198472#64 Pm)
    (hj : j + 5 < 2897) (hd : Dec prof.feat ndi j (FV7z.mk .call 64 [.rel rel] 5))
    (htgt : ndi_at.add (j + 5) + BitVec.ofNat 64 rel = Genv.gev_at)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem W) (hrip : X.cpu.rip = ndi_at.add j)
    (hsp : X.cpu.gpr.rsp = sp) (hdi : X.cpu.gpr.rdi = a) (hE : E.Ok V F sp) (hN : NmOk E V F a n)
    (h72 : 8032256 + 72 ≤ sp.toNat)
    (hWo : ∀ x : Addr, ¬ Scr sp x → (x.toNat < 7827456 ∨ 8032256 ≤ x.toNat) → W x = V x)
    (hWe : rdq(W, 8013720#64) = E.envp) (hstk : ∀ i < 72, Foot Wl (Addr.add (sp - 72#64) i))
    (hfe : ∀ i < 8, Foot F.data (Addr.add 8013720#64 i))
    (hPm : ∀ W', (∀ x, ¬ Scr sp x → W' x = W x) → Pm W')
    (k : ∀ Z t' W', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' → (∀ x, ¬ Scr sp x → W' x = W x) →
      Z.cpu.rip = ndi_at.add (j + 5) → Z.cpu.gpr.rax = 0 → Z.cpu.gpr.rsp = sp →
      Z.cpu.gpr.r15 = X.cpu.gpr.r15 → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hlt := sp.isLt
  have e8 := t8 sp (by omega)
  have c0 : (8013720#64).toNat = 8013720 := rfl
  have hw8 : ∀ i < 8, Foot Wl (Addr.add (sp - 8#64) i) := fun i hi => by
    have := hstk (64 + i) (by omega)
    rwa [show Addr.add (sp - 72#64) (64 + i) = Addr.add (sp - 8#64) i by simp only [Addr.add]; bv_omega] at this
  refine c.s_call hK hA hin (lt_len (by omega)) hrip hd hig (Genv.lt_len (by decide)) htgt
    (fun i hi => by rw [hsp]; exact hw8 i hi) ?_
  rintro Y t₁ hKY hAY ⟨hrY, hgY⟩
  rw [hsp] at hAY hgY
  have q : ∀ x, ¬ Scr sp x → Vst W (sp - 8#64) (toBytesLE (ndi_at.add (j + 5)) 8) x = W x := fun x hx =>
    vo (toBytesLE_length _ _) (by omega) (by unfold Scr at hx; omega)
  have fr : ∀ x, ¬ Scr sp x → ¬ Genv.InFr ⟨Y.cpu.gpr, Vst W (sp - 8#64) (toBytesLE (ndi_at.add (j + 5)) 8), n,
      E.envp, E.N, E.ptr, E.len⟩ x := by
    intro x hx
    unfold Genv.InFr
    unfold Scr at hx
    dsimp only
    rw [show Y.cpu.gpr.rsp = sp - 8#64 by rw [hgY]; rfl, e8]
    omega
  refine Genv.getenv_none (P := ⟨Y.cpu.gpr, Vst W (sp - 8#64) (toBytesLE (ndi_at.add (j + 5)) 8), n, E.envp, E.N,
      E.ptr, E.len⟩) c hig hil hl0 hlen hic hc0 hcmp hKY hAY hrY rfl
    (par_ok hE hN h72 (fun x hx hx' => (q x hx).trans (hWo x hx hx')) ?_ hstk (fun i hi => c.hws _ (hw8 i hi)) hfe
      (by rw [hgY]; rfl) (by rw [hgY]; exact hdi))
    (fun W' hW' => hPm W' fun x hx => (hW' x (fr x hx)).trans (q x hx)) hin (lt_len hj) ?_ ?_
  · rw [vr (toBytesLE_length _ _) (by omega) (by decide) (by omega)]
    exact hWe
  · show rdq(Vst W (sp - 8#64) (toBytesLE (ndi_at.add (j + 5)) 8), Y.cpu.gpr.rsp) = _
    rw [show Y.cpu.gpr.rsp = sp - 8#64 by rw [hgY]; rfl, vs (toBytesLE_length _ _) (by omega)]
    exact ofBytesLE_toBytesLE (w := 64) (n := 8) rfl _
  intro Z t' W' hKZ hAZ hW' hrZ hax hb
  refine k Z t' W' hKZ hAZ (fun x hx => (hW' x (fr x hx)).trans (q x hx)) hrZ hax ?_ ?_
  · rw [hb.1, show Y.cpu.gpr.rsp = sp - 8#64 by rw [hgY]; rfl]
    exact u8 sp
  · rw [hb.2.2.2.2.2.2, hgY]
    rfl

/-! ## The bytes the body stores into -/

/-- An address among the variables the body stores into: the vDSO pointers (`0x791cb8` to `0x791ce0`),
`_dl_stack_flags` (`0x7933c8`), the main map's fields from `l_phdr` to `l_relro_size` (`0x793788` to `0x793958`),
`_dl_platformlen` (`0x7a8550`), `_dl_verbose` and `_dl_dynamic_weak` (`0x7a855c`, `0x7a8560`), `_dl_lazy`
(`0x7a8590`), `_dl_profile_output` and `_dl_bind_not` (`0x7a85a0`, `0x7a85a8`), `_dl_init_all_dirs` (`0x7a85b0`). -/
def nv (a : Nat) : Bool :=
  (7937208 ≤ a && a < 7937248) || (7943112 ≤ a && a < 7943116) || (7944072 ≤ a && a < 7944536) ||
    (8029520 ≤ a && a < 8029528) || (8029532 ≤ a && a < 8029540) || (8029584 ≤ a && a < 8029588) ||
    (8029600 ≤ a && a < 8029612) || (8029616 ≤ a && a < 8029624)

theorem nv_data {a : Nat} (h : nv a = true) : 7827456 ≤ a ∧ a < 8032256 := by
  simp only [nv, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  omega

/-- `M` is `V` but for those variables. -/
def Gk (V M : Addr → Byte) : Prop := ∀ x : Addr, nv x.toNat = false → M x = V x

theorem Gk.refl (V : Addr → Byte) : Gk V V := fun _ _ => rfl

/-- A store into one of the variables. -/
theorem Gk.st {V M : Addr → Byte} (h : Gk V M) {x : Addr} {bs : List Byte} {n : Nat} (hn : bs.length = n)
    (hx : ∀ k < n, nv (x.toNat + k) = true) : Gk V (Vst M x bs) := by
  intro y hy
  rw [← h y hy]
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    rw [List.length_eq_zero_iff.1 hn]
    rfl
  have hf : x.toNat + n ≤ 2 ^ 64 := by
    have := (nv_data (hx (n - 1) (by omega))).2
    omega
  refine vo hn hf (Classical.byContradiction fun hc => ?_)
  have := hx (y.toNat - x.toNat) (by omega)
  rw [show x.toNat + (y.toNat - x.toNat) = y.toNat by omega, hy] at this
  exact absurd this (by decide)

/-- What a load apart from the variables reads. -/
theorem Gk.rd {V M : Addr → Byte} (h : Gk V M) (x : Addr) (n : Nat) (hf : x.toNat + n ≤ 2 ^ 64)
    (hx : ∀ k < n, nv (x.toNat + k) = false) : List.map M (byteAddrs x n) = List.map V (byteAddrs x n) := by
  refine List.map_congr_left fun a ha => ?_
  obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 ha
  exact h _ (by rw [toNat_add_of_fits hi hf]; exact hx i hi)

/-- What a load below the data segment reads. -/
theorem Gk.rdl {V M : Addr → Byte} (h : Gk V M) (x : Addr) (n : Nat) (hx : x.toNat + n ≤ 7827456) :
    List.map M (byteAddrs x n) = List.map V (byteAddrs x n) :=
  h.rd x n (by omega) fun k hk => Bool.eq_false_iff.2 fun h' => by have := nv_data h'; omega

/-- The bytes of a region inside a range of addresses. -/
theorem rf {P : Addr → Prop} {lo hi : Nat} (h : ∀ x : Addr, lo ≤ x.toNat → x.toNat < hi → P x) (hh : hi ≤ 2 ^ 64)
    (a : Addr) (n : Nat) (hd : lo ≤ a.toNat ∧ a.toNat + n ≤ hi) : ∀ i < n, P (Addr.add a i) := fun i hi =>
  h _ (by rw [toNat_add_of_fits hi (by omega)]; omega) (by rw [toNat_add_of_fits hi (by omega)]; omega)

/-- What the body's `getenv`s and what follows them are given, the bytes `V` when the body begins: the code; the
contracts of `strlen` and `strncmp`, which hold of bytes that are `V`'s on the page of the GOT (`0x792000`); the
environment and the seven names; the stack above the image, 72 bytes below `sp` to store into; the data segment to
read and store into. -/
structure Cx (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (o : Oracle)
    (pl pc : List Byte) (Pm : (Addr → Byte) → Prop) (E : Ev) (V : Addr → Byte) (sp : Addr) : Prop where
  hin : CodeIn L ndi_at ndi
  hig : CodeIn L Genv.gev_at Genv.gev
  hil : CodeIn L 4198664#64 pl
  hl0 : 0 < pl.length
  hlen : Str.LenAt prof L o 4198664#64 Pm
  hic : CodeIn L 4198472#64 pc
  hc0 : 0 < pc.length
  hcmp : Str.NcmpAt prof L o 4198472#64 Pm
  hPm : ∀ W : Addr → Byte, (∀ x : Addr, 7938048 ≤ x.toNat → x.toNat < 7940480 → W x = V x) → Pm W
  hE : E.Ok V F sp
  n1 : NmOk E V F 7289136#64 7
  n2 : NmOk E V F 7289144#64 15
  n3 : NmOk E V F 7289160#64 11
  n4 : NmOk E V F 7289172#64 11
  n5 : NmOk E V F 7289184#64 15
  n6 : NmOk E V F 7289200#64 17
  n7 : NmOk E V F 7289218#64 16
  h72 : 8032256 + 72 ≤ sp.toNat
  hstk : ∀ i < 72, Foot Wl (Addr.add (sp - 72#64) i)
  hr : ∀ x : Addr, 7827456 ≤ x.toNat → x.toNat < 8032256 → Foot F.data x
  hw : ∀ x : Addr, 7827456 ≤ x.toNat → x.toNat < 8032256 → Foot Wl x

/-- The return address's bytes below `sp`. -/
theorem w8 {sp : Addr} (hstk : ∀ i < 72, Foot Wl (Addr.add (sp - 72#64) i)) :
    ∀ i < 8, Foot Wl (Addr.add (sp - 8#64) i) := fun i hi => by
  have := hstk (64 + i) (by omega)
  rwa [show Addr.add (sp - 72#64) (64 + i) = Addr.add (sp - 8#64) i by simp only [Addr.add]; bv_omega] at this

/-- Bytes that are `M`'s outside the 72 below `sp`, `M` being `V` but for the body's variables, are `V`'s on the
GOT (`[0x792000, 0x792980)`, the page of the GOT below `main_arena`, which `malloc` writes). -/
theorem got_kept {sp : Addr} {V M W : Addr → Byte} (h72 : 8032256 + 72 ≤ sp.toNat) (hM : Eqo sp W M)
    (hG : Gk V M) : ∀ x : Addr, 7938048 ≤ x.toNat → x.toNat < 7940480 → W x = V x := fun x h1 h2 =>
  (hM x (by unfold Scr; omega)).trans (hG x (by
    simp only [nv, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    omega))

/-- A `call` of `getenv` in the body, the bytes `M`'s outside the 72 below `sp`: to the instruction after it, with
`rax` null, `rsp` and `r15` as they were, the bytes again `M`'s outside the 72. -/
theorem gs {pl pc : List Byte} {Pm : (Addr → Byte) → Prop} {E : Ev} {V M W : Addr → Byte} {sp a : Addr}
    {n j rel : Nat} (c : Seg prof F Wl L s₀ o) (cx : Cx prof F Wl L o pl pc Pm E V sp) (hj : j + 5 < 2897)
    (hd : Dec prof.feat ndi j (FV7z.mk .call 64 [.rel rel] 5))
    (htgt : ndi_at.add (j + 5) + BitVec.ofNat 64 rel = Genv.gev_at)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem W) (hrip : X.cpu.rip = ndi_at.add j)
    (hsp : X.cpu.gpr.rsp = sp) (hdi : X.cpu.gpr.rdi = a) (hN : NmOk E V F a n) (hM : Eqo sp W M) (hG : Gk V M)
    (k : ∀ Z t' W', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' → Eqo sp W' M →
      Z.cpu.rip = ndi_at.add (j + 5) → Z.cpu.gpr.rax = 0 → Z.cpu.gpr.rsp = sp →
      Z.cpu.gpr.r15 = X.cpu.gpr.r15 → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have h72 := cx.h72
  refine ge c cx.hin cx.hig cx.hil cx.hl0 cx.hlen cx.hic cx.hc0 cx.hcmp hj hd htgt hK hA hrip hsp hdi cx.hE hN h72
    (fun x hx hx' => (hM x hx).trans (hG x ?_)) ?_ cx.hstk (gf cx.hr _ 8 (by decide))
    (fun W' hW' => cx.hPm W' (got_kept h72 (hM.scr hW') hG))
    (fun Z t' W' hKZ hAZ hW' => k Z t' W' hKZ hAZ (hM.scr hW'))
  · rcases hx' with h | h
    all_goals
      simp only [nv, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      omega
  · rw [hM.rdi h72 _ 8 (by decide), hG.rd _ 8 (by decide) (by decide)]
    exact cx.hE.he

end FV7z.Ndi
