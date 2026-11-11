import FV7z.Tls.PartC
import FV7z.Memcmp.Words
/-!
# `__libc_setup_tls`: the bytes it leaves (PLAN.md G3, startup)

- `Eo S W T`: outside `S` the bytes `W` are the bytes `T`; kept by a store done in both (`Eo.st`) and by a store
  in `S` (`Eo.st_in`).
- `Scr sp`: the 128 bytes below the stack pointer of the entry, which the function and its callees use.
- `T2`, `T3`, `T4`, `TlsMem`: the bytes after `__sbrk`, at the `call` of `memcpy`, after `memcpy`, and at the
  `ret`, as stores to the bytes at the entry: the two new pages 0, `__curbrk` the new break, the variables stored
  to, the image copied to `b + 2048`, the thread control block at `b + 2176`.
- `eo_sbrk`, `eo_cpy`: what `Sbrk.sbrk_first` and the contract of `memcpy` give, in that form.
- `TlsVar`, `TlsMem_out`, `TlsMem_congr`: the bytes `TlsMem` leaves as they were, and what of `V` it has.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
open FV7z.Brk (curbrk)

namespace FV7z.Tls

/-- Outside `S`, the bytes `W` are the bytes `T`. -/
def Eo (S : Addr → Prop) (W T : Addr → Byte) : Prop := ∀ a, ¬ S a → W a = T a

theorem Vst_congr : ∀ (bs : List Byte) (W T : Addr → Byte) (x a : Addr), W a = T a → Vst W x bs a = Vst T x bs a
  | [], _, _, _, _, h => h
  | b :: bs, W, T, x, a, h => by
    simp only [Vst]
    refine Vst_congr bs _ _ _ _ ?_
    simp only [upd1]
    split
    · rfl
    · exact h

/-- A store, the same in both. -/
theorem Eo.st {S : Addr → Prop} {W T : Addr → Byte} (h : Eo S W T) (x : Addr) (bs : List Byte) :
    Eo S (Vst W x bs) (Vst T x bs) := fun a ha => Vst_congr bs W T x a (h a ha)

/-- A store in `S`. -/
theorem Eo.st_in {S : Addr → Prop} {W T : Addr → Byte} (h : Eo S W T) (x : Addr) (bs : List Byte)
    (hin : ∀ i < bs.length, S (x.add i)) : Eo S (Vst W x bs) T :=
  fun a ha => (Vst_apart bs W x a fun i hi e => ha (e ▸ hin i hi)).trans (h a ha)

theorem Eo.rd {S : Addr → Prop} {W T : Addr → Byte} (h : Eo S W T) (x : Addr) (n : Nat)
    (hx : ∀ i < n, ¬ S (x.add i)) : List.map W (byteAddrs x n) = List.map T (byteAddrs x n) :=
  rd_ext x n fun i hi => h _ (hx i hi)

/-- The stack `__libc_setup_tls` uses below the stack pointer `sp` of its entry: 128 bytes. -/
def Scr (sp : Addr) (a : Addr) : Prop := sp.toNat - 128 ≤ a.toNat ∧ a.toNat < sp.toNat

/-- The stores of the thread control block, the same in both. -/
theorem Eo.wc {S : Addr → Prop} {W T : Addr → Byte} (h : Eo S W T) (c : Addr) : Eo S (WC W c) (WC T c) :=
  ((h.st _ _).st _ _).st _ _

/-- The stores of the end, the same in both. -/
theorem Eo.wd {S : Addr → Prop} {W T : Addr → Byte} (h : Eo S W T) (x : BitVec 64) : Eo S (WD W x) (WD T x) :=
  (((((((((((h.st _ _).st _ _).st _ _).st _ _).st _ _).st _ _).st _ _).st _ _).st _ _).st _ _).st _ _).st _ _

/-- The bytes after `__sbrk (4544)` from the break `b`: the two new pages are 0, `__curbrk` is the new break. -/
def T2 (V : Addr → Byte) (b : Addr) : Addr → Byte :=
  Vst (Vz V b.toNat (b.toNat + 8192)) curbrk (toBytesLE (b + 4544#64) 8)

/-- The bytes at the `call` of `memcpy`, but for the stack. -/
def T3 (V : Addr → Byte) (b : Addr) : Addr → Byte :=
  Vst (Vst (Vst (Vst (T2 V b) 8027904#64 (toBytesLE 62#64 8)) 7944496#64 (toBytesLE 128#64 8)) 8027936#64
    (toBytesLE (2048#64 + b) 8)) 8027944#64 (toBytesLE 0#64 8)

/-- The bytes after `memcpy`, but for the stack: the 40 bytes of the initialisation image are in the block. -/
def T4 (V : Addr → Byte) (b : Addr) : Addr → Byte :=
  Vst (T3 V b) (2048#64 + b) ((byteAddrs 7829360#64 40).map V)

/-- The bytes `__libc_setup_tls` leaves, but for the stack below its frame: from the bytes `V` at its entry and the
break `b`. -/
def TlsMem (V : Addr → Byte) (b : Addr) : Addr → Byte := WD (WC (T4 V b) b) 7829360#64

theorem eo_sbrk {V V₂ V₃ : Addr → Byte} {sp r b : Addr} (hb : 0x7a9000 ≤ b.toNat)
    (hb' : b.toNat + 8192 + 128 ≤ sp.toNat) (hr1 : sp.toNat - 128 ≤ r.toNat - 32) (hr2 : r.toNat ≤ sp.toNat)
    (h2 : ∀ a : Addr, ¬ Scr sp a → V₂ a = V a)
    (hz : ∀ a : Addr, b.toNat ≤ a.toNat → a.toNat < b.toNat + 8192 → V₃ a = 0)
    (hf : ∀ a : Addr, ¬ (b.toNat ≤ a.toNat ∧ a.toNat < b.toNat + 8192) →
      ¬ (r.toNat - 32 ≤ a.toNat ∧ a.toNat < r.toNat) → ¬ (0x7a4c38 ≤ a.toNat ∧ a.toNat < 0x7a4c40) → V₃ a = V₂ a)
    (hc : rdq(V₃, curbrk) = b + 4544#64) :
    Eo (Scr sp) V₃ (T2 V b) := by
  intro a ha
  unfold Scr at ha
  unfold T2
  by_cases h1 : 0x7a4c38 ≤ a.toNat ∧ a.toNat < 0x7a4c40
  · have hj : a.toNat - 0x7a4c38 < 8 := by omega
    have e : a = curbrk.add (a.toNat - 0x7a4c38) := by simp only [Addr.add]; bv_omega
    have hbs : (byteAddrs curbrk 8).map V₃ = toBytesLE (b + 4544#64) 8 := by
      rw [← hc, FV7z.Order.toBytesLE_ofBytesLE (by simp [byteAddrs]) (by decide)]
    have h3 := congrArg (fun l => l[a.toNat - 0x7a4c38]?) hbs
    simp only [byteAddrs, List.map_map, List.getElem?_map, List.getElem?_range hj] at h3
    rw [e, FV7z.CpuFeat.Vst_at _ _ _ (by rw [toBytesLE_length]; exact hj) (by rw [toBytesLE_length]; decide)]
    simpa [List.getElem?_eq_getElem, toBytesLE_length, hj] using h3
  · by_cases h2' : b.toNat ≤ a.toNat ∧ a.toNat < b.toNat + 8192
    · rw [hz a h2'.1 h2'.2, Vst_out _ _ _ _ (by sd) (by simp only [toBytesLE_length]; bv_omega),
        Vz_in h2'.1 h2'.2]
    · rw [hf a h2' (by omega) h1, h2 a ha, Vst_out _ _ _ _ (by sd) (by simp only [toBytesLE_length]; bv_omega),
        Vz_out h2']

/-- Below the variables `__libc_setup_tls` stores to before `memcpy`, the bytes are as at the entry. -/
theorem t3_low (V : Addr → Byte) {b a : Addr} (hb : 0x7a9000 ≤ b.toNat) (ha : a.toNat < 0x793000) :
    T3 V b a = V a := by
  unfold T3 T2
  rw [Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vz_out]
  all_goals first | (simp only [toBytesLE_length]; bv_omega) | bv_omega

theorem eo_cpy {S : Addr → Prop} {V V₅ V₆ : Addr → Byte} {b : Addr} (hb : 0x7a9000 ≤ b.toNat)
    (hb' : b.toNat + 8192 ≤ 2 ^ 63) (hS : ∀ a : Addr, a.toNat < b.toNat + 8192 → ¬ S a) (h5 : Eo S V₅ (T3 V b))
    (hcp : ∀ i < 40, V₆ (Addr.add (2048#64 + b) i) = V₅ (Addr.add 7829360#64 i))
    (hfr : ∀ a : Addr, ¬ ((2048#64 + b).toNat ≤ a.toNat ∧ a.toNat < (2048#64 + b).toNat + 40) → V₆ a = V₅ a) :
    Eo S V₆ (T4 V b) := by
  intro a ha
  unfold T4
  have hl : ((byteAddrs 7829360#64 40).map V).length = 40 := by simp [byteAddrs]
  by_cases hd : (2048#64 + b).toNat ≤ a.toNat ∧ a.toNat < (2048#64 + b).toNat + 40
  · have hj : a.toNat - (2048#64 + b).toNat < 40 := by omega
    have e : a = Addr.add (2048#64 + b) (a.toNat - (2048#64 + b).toNat) := by simp only [Addr.add]; bv_omega
    rw [e, hcp _ hj, FV7z.CpuFeat.Vst_at _ _ _ (by rw [hl]; exact hj) (by rw [hl]; bv_omega),
      h5 _ (hS _ (by simp only [Addr.add]; bv_omega)), t3_low V hb (by simp only [Addr.add]; bv_omega)]
    simp [byteAddrs]
  · rw [hfr a hd, h5 a ha, Vst_out _ _ _ _ (by rw [hl]; bv_omega) (by rw [hl]; omega)]

/-- `_dl_tls_static_size` is not stored to before the end. -/
theorem ssize_t (V : Addr → Byte) {b : Addr} (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63) :
    rdq(WC (T4 V b) b, 7938736#64) = rdq(V, 7938736#64) := by
  have hl : ((byteAddrs 7829360#64 40).map V).length = 40 := by simp [byteAddrs]
  unfold WC T4 T3 T2
  rw [rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vz]
  any_goals first | (simp only [toBytesLE_length]; bv_omega) | (rw [hl]; bv_omega) | bv_omega
  intro i hi
  simp only [Addr.add]
  bv_omega

/-- The block's address, read from the stack after `memcpy`'s `call`. -/
theorem rd24 (W : Addr → Byte) (q b : Addr) (ra : BitVec 64) (hq : 0x7a9000 + 8 ≤ q.toNat)
    (hq' : q.toNat + 88 ≤ 2 ^ 64) : rdq(Vst (WB W q b) (q - 8) (toBytesLE ra 8), q + 24#64) = b := by
  unfold WB
  rw [rd_Vst, rd_Vst, rd_Vst, rd_Vst, rd_Vst_self, ofBytesLE_toBytesLE (n := 8) rfl]
  all_goals sd

/-- The frame after the three stores of the thread control block. -/
theorem fr_c {q b : Addr} {g₀ : Gprs} {V₃ V₆ : Addr → Byte} {ra : BitVec 64} (hfr : Fr q g₀ V₃)
    (hb : 0x7a9000 ≤ b.toNat) (hbq : b.toNat + 8192 + 40 ≤ q.toNat) (hq' : q.toNat + 88 ≤ 2 ^ 64)
    (h6 : ∀ a : Addr, ¬ ((2048#64 + b).toNat ≤ a.toNat ∧ a.toNat < (2048#64 + b).toNat + 40) →
      V₆ a = Vst (WB V₃ q b) (q - 8) (toBytesLE ra 8) a) : Fr q g₀ (WC V₆ b) := by
  refine hfr.keep hq' fun a h1 h2 h3 => ?_
  have e1 : WC V₆ b a = V₆ a := by
    unfold WC
    rw [Vst_out, Vst_out, Vst_out]
    all_goals simp only [toBytesLE_length]
    all_goals bv_omega
  have e2 : Vst (WB V₃ q b) (q - 8) (toBytesLE ra 8) a = V₃ a := by
    unfold WB
    rw [Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out]
    all_goals simp only [toBytesLE_length]
    all_goals bv_omega
  rw [e1, h6 a (by bv_omega), e2]

/-- The variables `__libc_setup_tls` stores to: `_dl_tls_static_size`, the main map's TLS fields, `_dl_static_dtv`'s
entries in use, `__curbrk`, and the `_dl_tls_*` variables. -/
def TlsVar (a : Addr) : Prop :=
  (0x7922b0 ≤ a.toNat ∧ a.toNat < 0x7922b8) ∨ (0x793908 ≤ a.toNat ∧ a.toNat < 0x793940) ∨
    (0x7a33e0 ≤ a.toNat ∧ a.toNat < 0x7a33e8) ∨ (0x7a3408 ≤ a.toNat ∧ a.toNat < 0x7a3410) ∨
    (0x7a4c38 ≤ a.toNat ∧ a.toNat < 0x7a4c40) ∨ (0x7a7ed0 ≤ a.toNat ∧ a.toNat < 0x7a7f30)

/-- A byte `__libc_setup_tls` does not store to: none of the variables, and not in the two new pages. -/
theorem TlsMem_out (V : Addr → Byte) {b a : Addr} (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63)
    (h1 : ¬ TlsVar a) (h2 : ¬ (b.toNat ≤ a.toNat ∧ a.toNat < b.toNat + 8192)) : TlsMem V b a = V a := by
  unfold TlsVar at h1
  have hl : ((byteAddrs 7829360#64 40).map V).length = 40 := by simp [byteAddrs]
  unfold TlsMem WD WC T4 T3 T2
  rw [Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out,
    Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vz_out h2]
  all_goals first | (simp only [toBytesLE_length]; bv_omega) | (rw [hl]; bv_omega) | bv_omega

/-- `TlsMem` of bytes that are the same at the initialisation image and, outside the two new pages, at `a`. -/
theorem TlsMem_congr {V V' : Addr → Byte} {b a : Addr}
    (hi : ∀ i < 40, V (Addr.add 7829360#64 i) = V' (Addr.add 7829360#64 i))
    (ha : ¬ (b.toNat ≤ a.toNat ∧ a.toNat < b.toNat + 8192) → V a = V' a) : TlsMem V b a = TlsMem V' b a := by
  have e : (byteAddrs 7829360#64 40).map V = (byteAddrs 7829360#64 40).map V' := rd_ext _ _ hi
  unfold TlsMem WD WC T4 T3 T2
  rw [e]
  repeat (refine Vst_congr _ _ _ _ _ ?_)
  simp only [Vz]
  split
  · rfl
  · exact ha ‹_›

end FV7z.Tls
