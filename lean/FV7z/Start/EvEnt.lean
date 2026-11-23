import FV7z.Start.PlEnt
/-!
# The environment at `_dl_non_dynamic_init` (PLAN.md G3, startup)

`Ndi.Cx` asks for `Ndi.Ev.Ok` in `lif_ok`'s bytes: `__environ` (`0x7a4798`) is the array, which is above the
frame with the strings' addresses and a null, and each string has its 0. `__libc_init_first` stores `rdx` to
`__environ`; the array and the strings are those of the launch (`ent_hi`).

- `ent_he`: `__environ` in `lif_ok`'s bytes is `rdx` at the call of `__libc_init_first`.
- `evOf`: the environment of the launch as an `Ndi.Ev`, its address past the last string null.
- `ent_ev`: `Ndi.Ev.Ok` of it in `lif_ok`'s bytes, the footprint's pages given.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Tun (rd_Vst rd_Vst_self)
open FV7z.Tls (rd_ext)

/-- `he` of `Ndi.Ev.Ok`: `__environ` is `rdx`, which `__libc_init_first` stored there. -/
theorem ent_he {W : Addr → Byte} {g gY : Gprs} {ra ra₀ : BitVec 64} {sp : Addr}
    (hr : 8013728 + 32 ≤ g.rsp.toNat) (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64) (hsp : 8013728 ≤ sp.toNat + 80)
    (hsn : sp.toNat + 120 ≤ 2 ^ 64) :
    rdq(Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY,
      8013720#64) = g.rdx := by
  unfold Ndi.fV
  rw [rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst]
  unfold Lif.LifMem
  rw [rd_Vst_self _ _ _ (toBytesLE_length _ _) ?_]
  · exact ofBytesLE_toBytesLE (n := 8) rfl _
  all_goals first | (simp only [toBytesLE_length]; bv_omega) | bv_omega

/-- The environment of the launch; the address of the string `N` is 0. -/
def evOf (K : Ctx) : Ndi.Ev := ⟨K.envp, K.N, fun i => if i < K.N then K.ptr i else 0, K.len⟩

/-- `Ndi.Ev.Ok` in `lif_ok`'s bytes: the array and the strings above `lo`, which is above `__libc_start_main`'s
frame, the TLS block, the call of `__libc_init_first` and `lif_ok`'s stack; `rdx` the array there. -/
theorem ent_ev {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} {F : Footprint}
    {g gY : Gprs} {ra ra₀ : BitVec 64} {sp : Addr} (hK : K.Ok) (hM : MB K V) (hb : 0x7a9000 ≤ b.toNat)
    (hb' : b.toNat + 8192 ≤ 2 ^ 63) (hW : PtrW K W V b ver D) {lo : Nat} (hbp : K.bp.toNat + 376 ≤ lo)
    (htl : b.toNat + 8192 ≤ lo) (hr : g.rsp.toNat + 8 ≤ lo) (hsp : sp.toNat + 120 ≤ lo)
    (hle : lo ≤ K.envp.toNat) (hls : ∀ i < K.N, lo ≤ (K.ptr i).toNat)
    (hDe : ∀ k < 8 * (K.N + 1), D (Addr.add K.envp k)) (hDs : ∀ i < K.N, D (Addr.add (K.ptr i) (K.len i)))
    (hs2 : ∀ i < K.N, (K.ptr i).toNat + K.len i + 2 ≤ 2 ^ 64) (hdx : g.rdx = K.envp)
    (hrl : 8013728 + 32 ≤ g.rsp.toNat) (hspl : 8013728 ≤ sp.toNat + 80)
    (hFe : ∀ k < 8 * (K.N + 1), Foot F.data (Addr.add K.envp k))
    (hFs : ∀ i < K.N, ∀ x : Addr, (K.ptr i).toNat / 4096 ≤ x.toNat / 4096 →
      x.toNat / 4096 ≤ ((K.ptr i).toNat + K.len i) / 4096 → Foot F.data x)
    (hF2 : ∀ i < K.N, Foot F.data (Addr.add (K.ptr i) 1)) :
    (evOf K).Ok (Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY)
      F sp := by
  have hfit := hK.hfit
  have hr0 : 32 ≤ g.rsp.toNat := by omega
  have hsn : sp.toNat + 120 ≤ 2 ^ 64 := by have := K.envp.isLt; omega
  have hr' : g.rsp.toNat + 8 ≤ 2 ^ 64 := by have := K.envp.isLt; omega
  have hi : ∀ a : Addr, lo ≤ a.toNat → D a →
      Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY a =
        K.V0 a := fun a ha hDa =>
    ent_hi hM hb hb' hW (by omega) (by omega) (by omega) hr0 (by omega) hDa
  refine ⟨?_, ?_, ?_, ?_, hFe, fun i hi' => ?_, fun i hi' => ?_, ?_, fun i hi' => ?_, fun i hi' => ?_,
    fun i hi' => ?_, fun i hi' => ?_, fun i hi' => ?_⟩
  · exact (ent_he hrl hr' hspl hsn).trans hdx
  · intro h
    have h0 : K.envp.toNat = 0 := by rw [show K.envp = 0 from h]; rfl
    omega
  · simp only [evOf]
    omega
  · simp only [evOf]
    omega
  · -- `eptr`
    simp only [evOf] at hi' ⊢
    have ta : (Addr.add K.envp (8 * i)).toNat = K.envp.toNat + 8 * i :=
      toNat_add_of_fits (n := 8 * (K.N + 1)) (by omega) (by omega)
    have h8 : ∀ j < 8,
        Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY
        (Addr.add (Addr.add K.envp (8 * i)) j) = K.V0 (Addr.add (Addr.add K.envp (8 * i)) j) := by
      intro j hj
      have tj : (Addr.add (Addr.add K.envp (8 * i)) j).toNat = K.envp.toNat + 8 * i + j := by
        rw [toNat_add_of_fits (n := 8) hj (by omega), ta]
      have e : Addr.add (Addr.add K.envp (8 * i)) j = Addr.add K.envp (8 * i + j) := by
        apply BitVec.eq_of_toNat_eq
        rw [tj, toNat_add_of_fits (n := 8 * (K.N + 1)) (by omega) (by omega), Nat.add_assoc]
      exact hi _ (by omega) (by rw [e]; exact hDe _ (by omega))
    rw [rd_ext _ 8 h8]
    by_cases h : i < K.N
    · rw [if_pos h]
      exact hK.henv i h
    · rw [if_neg h, (by omega : i = K.N)]
      exact hK.hend
  · simp only [evOf] at hi' ⊢
    rw [if_pos hi']
    exact hK.hnz i hi'
  · simp [evOf]
  · simp only [evOf] at hi' ⊢
    rw [if_pos hi']
    have := hls i hi'
    omega
  · simp only [evOf] at hi' ⊢
    rw [if_pos hi']
    exact hs2 i hi'
  · -- `sz`
    simp only [evOf] at hi' ⊢
    rw [if_pos hi', hi _ ?_ (hDs i hi')]
    · exact (hK.hstr i hi' _ (Nat.le_refl _)).trans (hK.hz i hi')
    · rw [toNat_add_of_fits (n := K.len i + 1) (by omega) (by have := hs2 i hi'; omega)]
      have := hls i hi'
      omega
  · simp only [evOf] at hi' ⊢
    rw [if_pos hi']
    exact hFs i hi'
  · simp only [evOf] at hi' ⊢
    rw [if_pos hi']
    exact hF2 i hi'

end FV7z.Start
