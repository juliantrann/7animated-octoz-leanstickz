import FV7z.Start.SysSeg
import FV7z.Lemmas.SysMmap
/-!
# `mmap` of private anonymous memory, a step of a run (PLAN.md §M, M1)

`Lemmas/SysMmap.lean`'s system call as a step of a run that `Fn.Seg` describes, modelled on `Start/SysSeg.lean`'s
`brk` that grows the break. When the kernel answers an error, nothing changes: the run goes on in the same `Fn.Seg`.
When it maps new pages at `a`, the run goes on from the state after as a new start, with the region `[a, a + rsi)`
(`mmN`) among what it may store into, its bytes 0.

- `Seg.s_mmap_anon`: the step, the address space below `2 ^ 47` (no 5-level paging).
-/
namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf FV7z.Start FV7z.Write

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t j : Nat}
  {e' : Addr} {code : List Byte} {V : Addr → Byte}

/-- `syscall` for `mmap (rdi, rsi, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, r8, r9)`, `r9` a page's
multiple, `rsi` not 0, without 5-level paging. An error: the run goes on in the same `Fn.Seg`, `rax` the answer
(`k'`). The pages mapped at `a`: the run goes on from the state after, `Y`, as a new start, with the region
`[a, a + rsi)` (`mmN`) among what it may store into, its bytes 0 and the footprint's as before (`k₁`), `rax` = `a`.
`rcx` and `r11` as `syscall` sets them. -/
theorem s_mmap_anon (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .syscall 32 [] len)) (hnr : X.cpu.gpr.rax.toNat % 2 ^ 32 = 9)
    (hfl : X.cpu.gpr.r10.toNat = 34) (hpr : X.cpu.gpr.rdx.toNat = 3) (h9 : X.cpu.gpr.r9.toNat % 4096 = 0)
    (hl0 : 0 < X.cpu.gpr.rsi.toNat) (hla : prof.feat.la57 = false) (hrs : s₀.thread.rseq = none)
    (hp0 : s₀.cpu.pkru &&& 3 = 0)
    (k' : ∀ r : BitVec 64, WrErr r →
      ContG prof F Wl L s₀ o (gev ++ [tcEv X.cpu.gpr r []]) gP gE V
        fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = (sysGpr X len).set 0 r)
    (k₁ : ∀ (a : Nat) (V' : Addr → Byte) (Y : State) (t' : Nat), a % 4096 = 0 → 4096 ≤ a →
      a + pageUp X.cpu.gpr.rsi.toNat ≤ 2 ^ 47 - 4096 →
      (∀ y, Foot (mmN X a) y → V' y = 0) → (∀ y, Foot F.data y → V' y = V y) →
      Seg prof (withNew F (mmN X a)) (mmN X a ++ Wl) L Y o → Agree (withNew F (mmN X a)) Y.proc.mm.mem V' →
      Y.cpu.rip = e'.add (j + len) → Y.cpu.gpr = (sysGpr X len).set 0 (BitVec.ofNat 64 a) →
      Y.cpu.seg = X.cpu.seg → GoG prof L o (gev ++ [tcEv X.cpu.gpr (BitVec.ofNat 64 a) []]) gP gE Y t') :
    GoG prof L o gev gP gE X t :=
  c.stepE hK hin hj hrip fun M hM hK' htf hac => by
    classical
    have hA' : Agree F (X.withMem M).proc.mm.mem V := c.agreeK hK hA hM
    have hokX := c.foot.keptW c.ready.rseq c.hws hK' c.sub_self
    have hRX := c.ready.keptW c.foot c.hws hK'
    have hts : taskSize prof.feat = 2 ^ 47 - 4096 := by
      simp only [taskSize, userPtrMax, hla, Bool.false_eq_true, ↓reduceIte]
    refine syscall_mmap_anon (s := X.withMem M) (o := o) (t := t + 1)
      (P := fun res => ∃ Y t' ev, res = (.running Y ev, t') ∧ GoG prof L o (gev ++ ev.toList) gP gE Y t')
      htf (c.dec hK' hin hrip hd) hnr hfl hpr h9 hl0 hRX.layout.growsDown ?_ ?_
    · intro r t' he
      exact ⟨_, _, _, rfl, k' r he _ _ (hK'.nx rfl rfl rfl) hA' ⟨rip_add hrip M len, rfl⟩⟩
    · intro a t' ha1 ha2 ha3 hfr
      have ha3' : a + pageUp X.cpu.gpr.rsi.toNat ≤ 2 ^ 47 - 4096 := by rw [← hts]; exact ha3
      have hrsX : (X.withMem M).thread.rseq = none := by rw [hK'.thread]; exact hrs
      have hpkX : (X.withMem M).cpu.pkru &&& 3 = 0 := by rw [hK'.pkru]; exact hp0
      have hpg : pageUp X.cpu.gpr.rsi.toNat % 4096 = 0 := by unfold pageUp; omega
      have hle : X.cpu.gpr.rsi.toNat ≤ pageUp X.cpu.gpr.rsi.toNat := by unfold pageUp; omega
      have hb : (BitVec.ofNat 64 a).toNat = a := by
        rw [BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt (by omega)
      have hN : ∀ r ∈ mmN X a,
          r.In (a / 4096 * 4096) ((a / 4096 + pageUp X.cpu.gpr.rsi.toNat / 4096) * 4096) := by
        intro r hr
        rw [List.mem_singleton] at hr
        subst hr
        show a / 4096 * 4096 ≤ (BitVec.ofNat 64 a).toNat ∧
          (BitVec.ofNat 64 a).toNat + X.cpu.gpr.rsi.toNat ≤ (a / 4096 + pageUp X.cpu.gpr.rsi.toNat / 4096) * 4096
        rw [hb]
        omega
      have htop : (a / 4096 + pageUp X.cpu.gpr.rsi.toNat / 4096) * 4096 ≤ 2 ^ 47 := by omega
      have htop' : (a / 4096 + pageUp X.cpu.gpr.rsi.toNat / 4096) * 4096 ≤ taskSize prof.feat := by
        rw [hts]
        omega
      -- the new pages are apart from the footprint's bytes, which are mapped
      have hout : ∀ y, Foot F.data y → ¬ Foot (mmN X a) y := by
        rintro y hy ⟨r, hr, hm⟩
        obtain ⟨h1, h2⟩ := in_page (hN r hr) hm
        exact foot_mapped hokX c.own (foot_append_iff.2 (.inl hy)) (free_page hfr h1 h2)
      let V' : Addr → Byte := fun y => if Foot (mmN X a) y then 0 else V y
      have h0 : ∀ y, Foot (mmN X a) y → V' y = 0 := fun y hy => if_pos hy
      have hV : ∀ y, ¬ Foot (mmN X a) y → V' y = V y := fun y hy => if_neg hy
      refine ⟨_, _, _, rfl, k₁ a V' _ _ ha1 ha2 ha3' h0 (fun y hy => hV y (hout y hy)) ?_ ?_
        (rip_add hrip M len) rfl rfl⟩
      · exact
          { foot := footOk_grow hokX hRX.layout hfr rfl rfl hpkX hrsX hrsX c.own hN htop
            ready := ready_grow hRX hfr rfl rfl hRX.layout.brkMinLe htf hac rfl hrsX htop' hRX.layout.brkPage
            env := c.env
            code := c.code
            own := rfl
            hww := by
              intro y hy
              rcases foot_append_iff.1 hy with ⟨r, hr, hm⟩ | hy
              · exact ⟨r, List.mem_append_left _ hr, hm⟩
              · obtain ⟨q, hq, hm⟩ := c.hww y hy
                exact ⟨q, List.mem_append_right _ hq, hm⟩ }
      · exact agree_grow hokX hRX.layout hfr rfl c.own hN hA' h0 fun y _ hy => hV y hy

end FV7z.Fn.Seg
