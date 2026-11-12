import FV7z.Tci.Hand
import FV7z.Imm.Head
import FV7z.Lemmas.Lock3
import FV7z.Memcmp.Words
/-!
# `tcache_init` with one thread, the first call (PLAN.md G3, `malloc`)

glibc 2.31's `tcache_init` at `0x631a60` in `7zzs`, after `ptmalloc_init` (the main arena in `fs:-0x18`) with one
thread (`fs:0x18` is 0): the arena's lock is taken by an unlocked `cmpxchg`, `_int_malloc (arena, 640)` on its first
call (`Imm.im_first`) gives a chunk from new pages, the lock is given back by `sub`, the chunk becomes the thread's
cache (`fs:-0x28`) and its 640 bytes are set to 0 (two `mov` and `rep stos`).

- `vc_*`: the verification conditions of the pieces.
- `Vst_same`, `st0`, `fill0`: storing the bytes already there (zeros over zeros) changes nothing.
- `Vc`: the bytes at the entry of `_int_malloc` (`rbp` pushed, the lock 1, the return address), with its reads.
- `out_hi`, `out_lo`, `out_lk`, `fin_rd`: reads after `_int_malloc` through `Imm.Out`; `out_tci`: `Out` of the
  bytes at the entry of `tcache_init`; `cz`: the chunk's 640 bytes are 0; `fin`: the cache's stores.
- `tci_ok`: the run from the entry to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
open FV7z.Brk (curbrk)
open FV7z.Sbrk (rd_eq)
open FV7z.Smm (corr corr2 size smEv smEv2)
open FV7z.Imm (Out Vi add_n)
namespace FV7z.Tci
variable {F : Footprint} {Wl : List Rgn}

/-- From the entry, one thread and the arena that `ptmalloc_init` set in `fs:-0x18`: `rbp` pushed, the arena in
`rbp`, `eax` 0 and `edx` 1 for the `cmpxchg`. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hsp : 8 ≤ g.rsp.toNat)
    (hst : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i))
    (hta : rdq(V, fb + 18446744073709551592#64) = 7940672#64) (hmt : rdd(V, fb + 24#64) = 0)
    (hfa : ∀ i < 8, Foot F.data ((fb + 18446744073709551592#64).add i))
    (hfl : ∀ i < 4, Foot F.data ((fb + 24#64).add i))
    (hd1 : (fb + 18446744073709551592#64).toNat + 8 ≤ (g.rsp - 8).toNat)
    (hd2 : (fb + 24#64).toNat + 4 ≤ (g.rsp - 8).toNat) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 42 ∧
      g' = { g with rax := 0, rdx := 1, rsp := g.rsp - 8, rbp := 7940672#64 } ∧
      V' = Vst V (g.rsp - 8) (toBytesLE g.rbp 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hsp hst hd1 hd2 ⊢
  have l8 : (toBytesLE rbp 8).length = 8 := toBytesLE_length _ _
  have z8 := Imm.sub8 rsp hsp
  have e1 : rdq(Vst V (rsp - 8) (toBytesLE rbp 8), fb + 18446744073709551592#64) = 7940672#64 :=
    (congrArg (ofBytesLE 64) (rd_Vst _ _ _ _ 8 (by omega) (by omega) (.inr hd1))).trans hta
  have e2 : rdd(Vst V (rsp - 8) (toBytesLE rbp 8), fb + 24#64) = 0 :=
    (congrArg (ofBytesLE 32) (rd_Vst _ _ _ _ 4 (by omega) (by omega) (.inr hd2))).trans hmt
  wpx [W_0, W_21, W_37, o0, o1, o2, Op.ldf, e1, e2]
  exact ⟨hst, hfa, fun h => absurd h (by decide), fun _ => ⟨hfl, fun h => absurd h (by decide), fun _ => rfl⟩⟩

/-- The arguments of `_int_malloc`: the arena and 640 bytes. -/
theorem vc_46 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_46 fb F Wl (fun j' g' _ V' => j' = 54 ∧ g' = { g with rsi := 640#64, rdi := g.rbp } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_46, o3]
  rfl

/-- `_int_malloc` gave a chunk, one thread: the chunk in `r8`, `eax` 0. -/
theorem vc_59 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hax : g.rax ≠ 0)
    (hmt : rdd(V, fb + 24#64) = 0) (hfl : ∀ i < 4, Foot F.data ((fb + 24#64).add i)) :
    W_59 fb F Wl (fun j' g' _ V' => j' = 87 ∧ g' = { g with rax := 0, r8 := g.rax } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hax
  wpx [W_59, W_71, o4, o5, Op.ldf, hmt, BitVec.and_self, beq_iff_eq, hax]
  exact ⟨fun h => h.elim, fun _ => ⟨hfl, fun h => absurd h (by decide), fun _ => rfl⟩⟩

theorem and_m8 (x : BitVec 64) (h : x.toNat % 8 = 0) : x &&& 18446744073709551608#64 = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (18446744073709551608#64 : BitVec 64).toNat = 18446744073709551608 from rfl,
    Smm.nat_and_m8 _ x.isLt]
  omega

theorem m8_add (x : BitVec 64) (h : x.toNat % 8 = 0) : (x + 8#64).toNat % 8 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem sub_add8 (x : BitVec 64) : x - (x + 8#64) + 640#64 = 632#64 := by bv_omega

/-- The chunk as the cache: its address in `fs:-0x28`, its first and last quadwords 0, `rdi` its second quadword
and `rcx` 79 for the `rep stos`. -/
theorem vc_91 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (h8 : g.r8 ≠ 0) (ha : g.r8.toNat % 8 = 0)
    (hfa : ∀ i < 8, Foot Wl (Addr.add (fb + 18446744073709551576#64) i)) (hm0 : ∀ i < 8, Foot Wl (Addr.add g.r8 i))
    (hm1 : ∀ i < 8, Foot Wl (Addr.add (g.r8 + 632#64) i)) :
    W_91 fb F Wl (fun j' g' _ V' => j' = 146 ∧
      g' = { g with rax := 0, rcx := 79#64, rdi := g.r8 + 8#64, r8 := 18446744073709551608#64 } ∧
      V' = Vst (Vst (Vst V (fb + 18446744073709551576#64) (toBytesLE g.r8 8)) g.r8 (toBytesLE (0#64) 8))
        (g.r8 + 632#64) (toBytesLE (0#64) 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h8 ha hm0 hm1 ⊢
  have e1 := and_m8 _ (m8_add r8 ha)
  have e2 : r8 - (r8 + 8#64) = 18446744073709551608#64 := by bv_omega
  wpx [W_91, W_96, o6, o7, Op.stf, BitVec.and_self, beq_iff_eq, h8, e1, e2, BitVec.xor_self, BitVec.reduceAdd,
    BitVec.reduceSetWidth, BitVec.reduceHShiftRight, BitVec.reduceUShiftRight]
  exact ⟨fun h => h.elim, fun _ => ⟨hfa, hm0, hm1, fun _ => rfl⟩⟩

/-- The `pop` of `rbp`. -/
theorem vc_149 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hsp : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) :
    W_149 fb F Wl (fun j' g' _ V' => j' = 150 ∧ g' = { g with rbp := rdq(V, g.rsp), rsp := g.rsp + 8 } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_149, o8]
  exact hsp

/-- Storing the bytes already there changes nothing. -/
theorem Vst_same (bs : List Byte) (V : Addr → Byte) (a : Addr) (hf : a.toNat + bs.length ≤ 2 ^ 64)
    (h : ∀ j (hj : j < bs.length), V (a.add j) = bs[j]) : Vst V a bs = V := by
  funext x
  by_cases hx : ∃ j, j < bs.length ∧ x = a.add j
  · obtain ⟨j, hj, rfl⟩ := hx
    rw [CpuFeat.Vst_at bs V a hj hf, h j hj]
  · exact Vst_apart bs V a x fun i hi e => hx ⟨i, hi, e⟩

theorem z8 : ∀ j (hj : j < (toBytesLE (0 : BitVec 64) 8).length), (toBytesLE (0 : BitVec 64) 8)[j] = 0 := by
  decide

/-- A quadword 0 stored over eight bytes 0. -/
theorem st0 (V : Addr → Byte) (a : Addr) {v : BitVec 64} (hv : v = 0) (hf : a.toNat + 8 ≤ 2 ^ 64)
    (h : ∀ i < 8, V (a.add i) = 0) : Vst V a (toBytesLE v 8) = V := by
  subst hv
  refine Vst_same _ V a (by rw [toBytesLE_length]; exact hf) fun j hj => ?_
  rw [z8 j hj]
  rw [toBytesLE_length] at hj
  exact h j hj

/-- `n` quadwords 0 stored over bytes 0. -/
theorem fill0 {v : BitVec 64} (hv : v = 0) :
    ∀ (n : Nat) (V : Addr → Byte) (a : Addr), a.toNat + 8 * n ≤ 2 ^ 64 →
    (∀ i < 8 * n, V (a.add i) = 0) → Vfill V a v n = V
  | 0, _, _, _, _ => rfl
  | n + 1, V, a, hf, h => by
    rw [Vfill_succ, st0 V a hv (by omega) fun i hi => h i (by omega)]
    refine fill0 hv n V (a + 8) (by bv_omega) fun i hi => ?_
    have e : (a + 8).add i = a.add (8 + i) := by simp only [Addr.add]; bv_omega
    rw [e]
    exact h _ (by omega)

/-- The bytes at the entry of `_int_malloc`: `rbp` pushed at `S + 192`, the arena's lock 1, the return address at
`S + 184`. -/
abbrev Vc (S : Addr) (r : BitVec 64) (V : Addr → Byte) : Addr → Byte :=
  Vst (Vst (Vst V (S + 192#64) (toBytesLE r 8)) (7940672#64) (toBytesLE (1#32) 4)) (S + 184#64)
    (toBytesLE (tci_at.add (54 + 5)) 8)

theorem Vc_out (S : Addr) (r : BitVec 64) (V : Addr → Byte) (hS : S.toNat + 256 < 2 ^ 64) {x : Addr}
    (h1 : ¬ (7940672 ≤ x.toNat ∧ x.toNat < 7940676))
    (h2 : ¬ (S.toNat + 184 ≤ x.toNat ∧ x.toNat < S.toNat + 200)) :
    Vc S r V x = V x := by
  have e1 := add_n S 184 (by omega)
  have e2 := add_n S 192 (by omega)
  unfold Vc
  rw [Vst_out _ _ _ _ (by rw [toBytesLE_length]; omega) (by rw [toBytesLE_length]; omega),
    Vst_out _ _ _ _ (by rw [toBytesLE_length]; decide) (by rw [toBytesLE_length, BitVec.toNat_ofNat]; omega),
    Vst_out _ _ _ _ (by rw [toBytesLE_length]; omega) (by rw [toBytesLE_length]; omega)]

theorem Vc_rd (S : Addr) (r : BitVec 64) (V : Addr → Byte) (hS : S.toNat + 256 < 2 ^ 64) (hlo : 8029888 ≤ S.toNat)
    {x : Addr} {n : Nat}
    (h : x.toNat + n ≤ 7940672 ∨ (7940676 ≤ x.toNat ∧ x.toNat + n ≤ S.toNat + 184)) :
    List.map (Vc S r V) (byteAddrs x n) = List.map V (byteAddrs x n) :=
  rd_eq (by omega) fun _ h1 h2 => Vc_out S r V hS (by omega) (by omega)

theorem Vc_rbp (S : Addr) (r : BitVec 64) (V : Addr → Byte) (hS : S.toNat + 256 < 2 ^ 64)
    (hlo : 8029888 ≤ S.toNat) :
    rdq(Vc S r V, S + 192#64) = r := by
  have e1 := add_n S 184 (by omega)
  have e2 := add_n S 192 (by omega)
  unfold Vc
  rw [rd_Vst _ _ _ _ 8 (by rw [toBytesLE_length]; omega) (by omega) (.inl (by rw [toBytesLE_length]; omega)),
    rd_Vst _ _ _ _ 8 (by rw [toBytesLE_length]; decide) (by omega)
      (.inl (by rw [toBytesLE_length, BitVec.toNat_ofNat]; omega)),
    rd_Vst_self _ _ _ (toBytesLE_length _ _) (by omega)]
  exact ofBytesLE_toBytesLE (w := 64) (n := 8) rfl _

theorem Vc_ret (S : Addr) (r : BitVec 64) (V : Addr → Byte) (hS : S.toNat + 256 < 2 ^ 64) :
    rdq(Vc S r V, S + 184#64) = tci_at.add 59 := by
  have e1 := add_n S 184 (by omega)
  unfold Vc
  rw [rd_Vst_self _ _ _ (toBytesLE_length _ _) (by omega)]
  exact ofBytesLE_toBytesLE (w := 64) (n := 8) rfl _

/-- Above `_int_malloc`'s frame the bytes after its first call are those at its entry. -/
theorem out_hi {S : Addr} {g : Gprs} {W V' : Addr → Byte} {b nb R c sm : BitVec 64} {lo hi : Nat}
    (hO : Out (Vi S g W) V' b nb R c sm lo hi (S.toNat - 168) (S.toNat + 32)) (hS : S.toNat + 256 < 2 ^ 64)
    (hlo : 8029888 ≤ S.toNat) (hhi : hi ≤ S.toNat) (hw : (b + corr b).toNat + nb.toNat + 16 ≤ S.toNat)
    {x : Addr} {n : Nat} (h1 : S.toNat + 184 ≤ x.toNat) (h2 : x.toNat + n ≤ 2 ^ 64) :
    List.map V' (byteAddrs x n) = List.map W (byteAddrs x n) :=
  rd_eq h2 fun a a1 a2 => (hO.same a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)).trans (Imm.Vi_out S g W hS (.inr (by omega)))

/-- The arena's lock: four bytes 0 when it reads 0. -/
theorem lk0 {V : Addr → Byte} (h : rdd(V, 7940672#64) = 0) {j : Nat} (hj : j < 4) :
    V (Addr.add (7940672#64) j) = (toBytesLE (0#32) 4)[j]'(by rw [toBytesLE_length]; exact hj) := by
  have t := Order.toBytesLE_ofBytesLE (w := 32) (n := 4) (bs := List.map V (byteAddrs 7940672#64 4))
    (by simp [byteAddrs]) (by decide)
  rw [h] at t
  have := congrArg (fun l => l[j]?) t
  simp only [byteAddrs, List.map_map, List.getElem?_map, List.getElem?_range hj, Option.map_some,
    Function.comp_apply] at this
  exact Option.some_inj.1 (this.symm.trans (List.getElem?_eq_getElem _))

/-- The bytes after `tcache_init` gave the lock back, as `Out` of those at its entry: the stack part now reaches the
words of `tcache_init` (`S + 200`). -/
theorem out_tci {S : Addr} {g : Gprs} {r : BitVec 64} {V V' : Addr → Byte} {b nb R c sm : BitVec 64} {lo hi : Nat}
    (hO : Out (Vi S g (Vc S r V)) V' b nb R c sm lo hi (S.toNat - 168) (S.toNat + 32))
    (hS : S.toNat + 256 < 2 ^ 64) (hb : 8029888 ≤ b.toNat) (hb47 : b.toNat < 2 ^ 47) (hnb : nb.toNat < 2 ^ 47)
    (hlo : 8029888 ≤ lo) (hlk : rdd(V, 7940672#64) = 0) :
    Out V (Vst V' (7940672#64) (toBytesLE (0#32) 4)) b nb R c sm lo hi (S.toNat - 168) (S.toNat + 200) := by
  have hc : (corr b).toNat < 16 := by rw [Smm.corr_toNat]; omega
  have L : ∀ x : Addr, 7940676 ≤ x.toNat → x.toNat + 8 ≤ 2 ^ 64 →
      List.map (Vst V' (7940672#64) (toBytesLE (0#32) 4)) (byteAddrs x 8) = List.map V' (byteAddrs x 8) :=
    fun x h1 h2 => rd_Vst _ _ _ _ 8 (by rw [toBytesLE_length]; decide) h2
      (.inl (by rw [toBytesLE_length, BitVec.toNat_ofNat]; omega))
  have e1 : (b + corr b + 8#64).toNat = b.toNat + (corr b).toNat + 8 := by bv_omega
  have e2 : (b + corr b + nb + 8#64).toNat = b.toNat + (corr b).toNat + nb.toNat + 8 := by bv_omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a h1 h2 h3 h4 h5 h6 h7 h8 => ?_, fun a h1 h2 h3 h4 => ?_⟩
  · rw [L _ (by decide) (by decide)]; exact hO.top
  · rw [L _ (by omega) (by omega)]; exact hO.hd
  · rw [L _ (by omega) (by omega)]; exact hO.tsz
  · rw [L _ (by decide) (by decide)]; exact hO.sys
  · rw [L _ (by decide) (by decide)]; exact hO.mxs
  · rw [rd_Vst _ _ _ _ 8 (by rw [toBytesLE_length]; decide) (by decide) (.inr (by decide))]; exact hO.sbb
  · rw [L _ (by decide) (by decide)]; exact hO.cur
  · by_cases hm : 7940672 ≤ a.toNat ∧ a.toNat < 7940676
    · have e : a = Addr.add (7940672#64) (a.toNat - 7940672) := by simp only [Addr.add]; bv_omega
      rw [e, CpuFeat.Vst_at _ _ _ (by rw [toBytesLE_length]; omega) (by rw [toBytesLE_length]; decide),
        lk0 hlk (by omega)]
    · rw [Vst_out _ _ _ _ (by rw [toBytesLE_length]; decide)
        (by rw [toBytesLE_length, BitVec.toNat_ofNat]; omega)]
      rw [hO.same a h1 (by omega) h3 h4 h5 h6 h7 h8, Imm.Vi_out S g _ hS (by omega), Vc_out S r V hS hm (by omega)]
  · rw [Vst_out _ _ _ _ (by rw [toBytesLE_length]; decide) (by rw [toBytesLE_length, BitVec.toNat_ofNat]; omega)]
    exact hO.zero a h1 h2 h3 h4

/-- The chunk's 640 bytes after `_int_malloc`'s first call are 0: in the new pages, or in the rest of the old
break's page, 0 at the entry (`hz`). -/
theorem cz {S : Addr} {g : Gprs} {r : BitVec 64} {V V' : Addr → Byte} {b R c sm : BitVec 64} {hi : Nat}
    (hO : Out (Vi S g (Vc S r V)) V' b 656#64 R c sm (pageUp b.toNat / 4096 * 4096) hi (S.toNat - 168)
      (S.toNat + 32))
    (hS : S.toNat + 256 < 2 ^ 64) (hb : 8029888 ≤ b.toNat) (hb47 : b.toNat < 2 ^ 47)
    (hhi : b.toNat + 688 ≤ hi) (hhs : hi + 168 ≤ S.toNat)
    (hz : ∀ a : Addr, b.toNat ≤ a.toNat → a.toNat < pageUp b.toNat / 4096 * 4096 → V a = 0) :
    ∀ a : Addr, (b + corr b).toNat + 16 ≤ a.toNat → a.toNat < (b + corr b).toNat + 656 →
      Vst V' (7940672#64) (toBytesLE (0#32) 4) a = 0 := by
  have hc : (corr b).toNat < 16 := by rw [Smm.corr_toNat]; omega
  have hab : (b + corr b).toNat = b.toNat + (corr b).toNat := by bv_omega
  have h656 : (656#64 : BitVec 64).toNat = 656 := rfl
  have hpb : b.toNat ≤ pageUp b.toNat / 4096 * 4096 := by unfold pageUp; omega
  intro a h1 h2
  rw [Vst_out _ _ _ _ (by rw [toBytesLE_length]; decide) (by rw [toBytesLE_length, BitVec.toNat_ofNat]; omega)]
  by_cases ha : pageUp b.toNat / 4096 * 4096 ≤ a.toNat
  · exact hO.zero a ha (by omega) (by omega) (by omega)
  · rw [hO.same a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      Imm.Vi_out S g _ hS (.inl (by omega)), Vc_out S r V hS (by omega) (by omega)]
    exact hz a (by omega) (by omega)

/-- The stores of the cache: over the 640 bytes 0 only the pointer in `fs:-0x28` changes the bytes. -/
theorem fin {V₁ : Addr → Byte} {T M : Addr} {v w m : BitVec 64} (hv : v = 0) (hw : w = 0)
    (hT : T.toNat + 8 ≤ M.toNat) (hM : M.toNat + 640 < 2 ^ 64)
    (hz : ∀ a : Addr, M.toNat ≤ a.toNat → a.toNat < M.toNat + 640 → V₁ a = 0) :
    Vfill (Vst (Vst (Vst V₁ T (toBytesLE m 8)) M (toBytesLE v 8)) (M + 632#64) (toBytesLE v 8)) (M + 8#64) w (78 + 1)
      = Vst V₁ T (toBytesLE m 8) := by
  have hz' : ∀ a : Addr, M.toNat ≤ a.toNat → a.toNat < M.toNat + 640 → Vst V₁ T (toBytesLE m 8) a = 0 :=
    fun a h1 h2 => by
      rw [Vst_out _ _ _ _ (by rw [toBytesLE_length]; omega) (by rw [toBytesLE_length]; omega)]
      exact hz a h1 h2
  have a0 : ∀ i < 8, (Addr.add M i).toNat = M.toNat + i := fun i hi => by simp only [Addr.add]; bv_omega
  have a1 : ∀ i < 8, (Addr.add (M + 632#64) i).toNat = M.toNat + 632 + i := fun i hi => by
    simp only [Addr.add]; bv_omega
  have a2 : ∀ i < 632, (Addr.add (M + 8#64) i).toNat = M.toNat + 8 + i := fun i hi => by
    simp only [Addr.add]; bv_omega
  rw [st0 _ M hv (by omega) fun i hi => hz' _ (by rw [a0 i hi]; omega) (by rw [a0 i hi]; omega),
    st0 _ _ hv (by bv_omega) fun i hi => hz' _ (by rw [a1 i hi]; omega) (by rw [a1 i hi]; omega)]
  exact fill0 hw _ _ _ (by bv_omega) fun i hi => hz' _ (by rw [a2 i hi]; omega) (by rw [a2 i hi]; omega)

/-! ## Offsets, footprints and reads, stated apart from the run -/

theorem f40 (x : Addr) (h : 40 ≤ x.toNat) : (x + 18446744073709551576#64).toNat = x.toNat - 40 := by bv_omega
theorem f24 (x : Addr) (h : 24 ≤ x.toNat) : (x + 18446744073709551592#64).toNat = x.toNat - 24 := by bv_omega
theorem s200 (S : Addr) : S + 200#64 - 8 = S + 192#64 := by bv_omega
theorem s192 (S : Addr) : S + 192#64 - 8 = S + 184#64 := by bv_omega
theorem s8 (S : Addr) : S + 192#64 + 8 = S + 200#64 := by bv_omega
theorem s208 (S : Addr) : S + 200#64 + 8 = S + 208#64 := by bv_omega

/-- The chunk's memory `b + corr b + 16`, as a number. -/
theorem mt (b : BitVec 64) (hb : b.toNat < 2 ^ 47) :
    (b + corr b + 16#64).toNat = b.toNat + (corr b).toNat + 16 ∧ (b + corr b).toNat = b.toNat + (corr b).toNat ∧
      (corr b).toNat < 16 ∧ (b + corr b + 16#64).toNat % 8 = 0 := by
  have hc := Smm.corr_toNat b
  have h16 : (corr b).toNat < 16 := by omega
  have e : (b + corr b).toNat = b.toNat + (corr b).toNat := by bv_omega
  have e2 : (b + corr b + 16#64).toNat = b.toNat + (corr b).toNat + 16 := by bv_omega
  refine ⟨e2, e, h16, ?_⟩
  rw [e2, hc]
  omega

theorem at_add (x : Addr) (i : Nat) (h : x.toNat + i < 2 ^ 64) : (Addr.add x i).toNat = x.toNat + i := by
  simp only [Addr.add]
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- Bytes of the chunk, from the footprint of `_int_malloc`'s result. -/
theorem ch_ft {R : List Rgn} {b : BitVec 64} (hb47 : b.toNat < 2 ^ 47)
    (hh : ∀ a : Addr, (b + corr b).toNat ≤ a.toNat → a.toNat < (b + corr b).toNat + 656 + 16 → Foot R a)
    {x : Addr} {d n : Nat} (hx : x.toNat = (b + corr b).toNat + 16 + d) (hd : d + n ≤ 656) :
    ∀ i < n, Foot R (Addr.add x i) := fun i hi => by
  obtain ⟨-, hab, hc, -⟩ := mt b hb47
  have e := at_add x i (by omega)
  exact hh _ (by omega) (by omega)

/-- Eight bytes of the stack of `tcache_init` and `_int_malloc`. -/
theorem st_at {R : List Rgn} {S : Addr} (h : ∀ i < 376, Foot R (Addr.add (S - 168) i)) (d : Nat)
    (hd : d + 8 ≤ 208) : ∀ i < 8, Foot R (Addr.add (S + BitVec.ofNat 64 d) i) := fun i hi => by
  have e : Addr.add (S - 168) (168 + d + i) = Addr.add (S + BitVec.ofNat 64 d) i := by simp only [Addr.add]; bv_omega
  exact e ▸ h _ (by omega)

theorem st_in {R : List Rgn} {S : Addr} (h : ∀ i < 376, Foot R (Addr.add (S - 168) i)) :
    ∀ i < 360, Foot R (Addr.add (S - 168) i) := fun i hi => h i (by omega)

/-- The arena's lock. -/
theorem lk_ft {R : List Rgn} (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot R a) :
    ∀ i < 4, Foot R (Addr.add (7940672#64) i) := fun i hi =>
  hW _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)

/-- Reads of the fixed words at the entry of `_int_malloc`, below and above the lock. -/
theorem Vc_lo (S : Addr) (r : BitVec 64) (V : Addr → Byte) (hS : S.toNat + 256 < 2 ^ 64) (hlo : 8029888 ≤ S.toNat)
    (x n : Nat) (h : x + n ≤ 7940672) :
    List.map (Vc S r V) (byteAddrs (BitVec.ofNat 64 x) n) = List.map V (byteAddrs (BitVec.ofNat 64 x) n) :=
  Vc_rd S r V hS hlo (.inl (by rw [BitVec.toNat_ofNat]; omega))

theorem Vc_mid (S : Addr) (r : BitVec 64) (V : Addr → Byte) (hS : S.toNat + 256 < 2 ^ 64) (hlo : 8029888 ≤ S.toNat)
    (x n : Nat) (h1 : 7940676 ≤ x) (h : x + n ≤ 8029888) :
    List.map (Vc S r V) (byteAddrs (BitVec.ofNat 64 x) n) = List.map V (byteAddrs (BitVec.ofNat 64 x) n) :=
  Vc_rd S r V hS hlo (.inr ⟨by rw [BitVec.toNat_ofNat]; omega, by rw [BitVec.toNat_ofNat]; omega⟩)

/-- Below the break and above the fixed words, the bytes after `_int_malloc`'s first call are those at the entry
of `tcache_init`. -/
theorem out_lo {S : Addr} {g : Gprs} {r : BitVec 64} {V V' : Addr → Byte} {b nb R c sm : BitVec 64} {lo hi : Nat}
    (hO : Out (Vi S g (Vc S r V)) V' b nb R c sm lo hi (S.toNat - 168) (S.toNat + 32))
    (hS : S.toNat + 256 < 2 ^ 64) (hb47 : b.toNat < 2 ^ 47) (hblo : b.toNat ≤ lo) (hbS : b.toNat + 168 ≤ S.toNat)
    {x : Addr} {n : Nat} (h1 : 8029888 ≤ x.toNat) (h2 : x.toNat + n ≤ b.toNat) :
    List.map V' (byteAddrs x n) = List.map V (byteAddrs x n) := by
  obtain ⟨-, hab, -, -⟩ := mt b hb47
  exact rd_eq (by omega) fun a a1 a2 => (hO.same a (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)).trans ((Imm.Vi_out S g _ hS (.inl (by omega))).trans
      (Vc_out S r V hS (by omega) (by omega)))

/-- The lock after `_int_malloc`'s first call: still 1. -/
theorem out_lk {S : Addr} {g : Gprs} {r : BitVec 64} {V V' : Addr → Byte} {b nb R c sm : BitVec 64} {lo hi : Nat}
    (hO : Out (Vi S g (Vc S r V)) V' b nb R c sm lo hi (S.toNat - 168) (S.toNat + 32))
    (hS : S.toNat + 256 < 2 ^ 64) (hsl : 8029888 + 168 ≤ S.toNat) (hb : 8029888 ≤ b.toNat)
    (hb47 : b.toNat < 2 ^ 47) (hlo : 8029888 ≤ lo) :
    rdd(V', 7940672#64) = 1#32 := by
  obtain ⟨-, hab, -, -⟩ := mt b hb47
  have e1 := add_n S 184 (by omega)
  have e0 : (7940672#64 : Addr).toNat = 7940672 := rfl
  rw [rd_eq (by decide) fun a a1 a2 => (hO.same a (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)).trans (Imm.Vi_out S g _ hS (.inl (by omega)))]
  unfold Vc
  rw [rd_Vst _ _ _ _ 4 (by rw [toBytesLE_length]; omega) (by decide)
      (.inr (by rw [BitVec.toNat_ofNat]; omega)),
    rd_Vst_self _ _ _ (toBytesLE_length _ _) (by decide)]
  exact ofBytesLE_toBytesLE (w := 32) (n := 4) rfl _

/-- The words `tcache_init` reads back at the end: `rbp` and the return address. -/
theorem fin_rd {S T : Addr} {g : Gprs} {r m : BitVec 64} {V V' : Addr → Byte} {b nb R c sm : BitVec 64} {lo hi : Nat}
    (hO : Out (Vi S g (Vc S r V)) V' b nb R c sm lo hi (S.toNat - 168) (S.toNat + 32))
    (hS : S.toNat + 256 < 2 ^ 64) (hsl : 8029888 ≤ S.toNat) (hhi : hi ≤ S.toNat)
    (hw : (b + corr b).toNat + nb.toNat + 16 ≤ S.toNat) (hT : T.toNat + 8 ≤ S.toNat) :
    rdq(Vst (Vst V' (7940672#64) (toBytesLE (0#32) 4)) T (toBytesLE m 8), S + 192#64) = r ∧
      rdq(Vst (Vst V' (7940672#64) (toBytesLE (0#32) 4)) T (toBytesLE m 8), S + 200#64) = rdq(V, S + 200#64) := by
  have e2 := add_n S 192 (by omega)
  have e3 := add_n S 200 (by omega)
  have L : ∀ x : Addr, S.toNat + 184 ≤ x.toNat → x.toNat + 8 ≤ 2 ^ 64 →
      List.map (Vst (Vst V' (7940672#64) (toBytesLE (0#32) 4)) T (toBytesLE m 8)) (byteAddrs x 8) =
        List.map (Vc S r V) (byteAddrs x 8) := fun x h1 h2 => by
    rw [rd_Vst _ _ _ _ 8 (by rw [toBytesLE_length]; omega) h2 (.inl (by rw [toBytesLE_length]; omega)),
      rd_Vst _ _ _ _ 8 (by rw [toBytesLE_length]; decide) h2
        (.inl (by rw [toBytesLE_length, BitVec.toNat_ofNat]; omega))]
    exact out_hi hO hS hsl hhi hw h1 h2
  refine ⟨?_, ?_⟩
  · rw [L _ (by omega) (by omega)]
    exact Vc_rbp S r V hS hsl
  · rw [L _ (by omega) (by omega)]
    exact congrArg (ofBytesLE 64) (rd_eq (by omega) fun a a1 a2 => Vc_out S r V hS (by omega) (by omega))

/-- The registers a call keeps, other than `rsp` and `rbp`. -/
def K5 (g g' : Gprs) : Prop :=
  g'.rbx = g.rbx ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15

theorem K5.tr {g₁ g₂ g₃ : Gprs} (h₁ : K5 g₁ g₂) (h₂ : K5 g₂ g₃) : K5 g₁ g₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.1.trans h₁.2.2.2.1,
    h₂.2.2.2.2.trans h₁.2.2.2.2⟩

/-! ## The run -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle}
  {t : Nat} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {V : Addr → Byte}

/-- From the entry of `tcache_init` on the first call of `malloc`, one thread (`fs:0x18` 0), the main arena in
`fs:-0x18`, its lock free, no cache yet: the conditions of `Imm.im_first` on the bytes at the entry, and the rest of
the old break's page 0 (`hz`). The run takes the lock, gets a chunk of 640 bytes from `_int_malloc` (new pages `N`
and `Base` of the new break), gives the lock back, makes the chunk the cache (`fs:-0x28`) and reaches the return
address: `rsp`, `rbp` and the registers a call keeps come back, the bytes are `V₁` with the cache pointer stored,
`V₁` is `Out` of the entry bytes (the stack part up to `S + 200`) and the chunk's 640 bytes in `V₁` are 0. -/
theorem tci_ok {lim : Nat} {b fsb S : Addr} {ks : Kst} {pad sm mx : BitVec 64} (c : Seg prof F Wl L s₀ o)
    (hB : Base s₀ lim b fsb ks) (hinT : CodeIn L tci_at tci) (hin : CodeIn L Imm.imm_at Imm.imm)
    (hinS : CodeIn L Smm.smm_at Smm.smm) (hinD : CodeIn L Dmc.dmc_at Dmc.dmc)
    (hinK : CodeIn L Sbrk.sbk_at Sbrk.sbk) (hinb : CodeIn L Brk.brk_at Brk.brk)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = tci_at)
    (hrsp : X.cpu.gpr.rsp = S + 200#64) (hsp : 8029888 + 168 ≤ S.toNat) (hS : S.toNat + 256 < 2 ^ 64)
    (hst : ∀ i < 376, Foot Wl (Addr.add (S - 168) i))
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot Wl a)
    (hhk : ∀ i < 8, Foot Wl (Addr.add (8013152#64) i))
    (hcur : ∀ i < 8, Foot Wl (curbrk.add i)) (hml : ∀ i < 4, Foot Wl (Addr.add (7944640#64) i))
    (hpb : ∀ i < 4, Foot Wl (Addr.add (8013220#64) i))
    (hgf : ∀ i < 8, Foot F.data (Addr.add (8013224#64) i))
    (hft : ∀ i < 8, Foot Wl (Addr.add (fsb + 18446744073709551576#64) i))
    (hfa : ∀ i < 8, Foot Wl (Addr.add (fsb + 18446744073709551592#64) i))
    (hfm : ∀ i < 4, Foot Wl (Addr.add (fsb + 24#64) i))
    (hfs : 8029888 + 40 ≤ fsb.toNat) (hfb : fsb.toNat + 28 ≤ b.toNat)
    (hta : rdq(V, fsb + 18446744073709551592#64) = 7940672#64) (hmt : rdd(V, fsb + 24#64) = 0)
    (hlk : rdd(V, 7940672#64) = 0)
    (hgm : (rdq(V, 8013224#64)).toNat < 656) (hs41 : rdq(V, 7941432#64) = 7941408#64)
    (htc : rdq(V, fsb + 18446744073709551576#64) = 0#64) (hun : rdq(V, 7940792#64) = 7940768#64)
    (hm1 : rdd(V, 7942820#64) = 0) (hm2 : rdd(V, 7942824#64) = 0) (hm3 : rdd(V, 7942828#64) = 0)
    (hps : rdq(V, 7943128#64) = 4096#64)
    (hthr : 656 < (rdq(V, 7940528#64)).toNat)
    (htop : rdq(V, 7940768#64) = 7940768#64) (hsz : rdq(V, 7940776#64) = 0#64)
    (hpad : rdq(V, 7940520#64) = pad) (hnb : 656 + pad.toNat + 4127 < 2 ^ 47)
    (hfl : ofBytesLE 8 ((byteAddrs (7940676#64) 1).map V) &&& 2#8 = 0#8) (hfc : rdd(V, 7940680#64) = 0)
    (hmc : rdq(V, 7942872#64) = Dmc.dmc_at)
    (hcb : rdq(V, curbrk) = b) (hm0 : rdd(V, 7944640#64) = 0)
    (hk0 : rdq(V, 8013152#64) = 0#64) (hsm : rdq(V, 7942856#64) = sm) (hsb : rdq(V, 7940584#64) = 0#64)
    (hmx : rdq(V, 7942864#64) = mx) (hms : mx.toNat ≤ sm.toNat) (hsu : sm.toNat < 2 ^ 47)
    (hp0 : rdd(V, 8013220#64) = 0)
    (hmg : ∀ t p, o t (.memFail p) = none)
    (hlim : pageUp (b + size pad 656#64).toNat / 4096 ≤ lim)
    (hbl : 8029888 ≤ b.toNat)
    (hbs : (b + size pad 656#64).toNat + 4096 + 168 ≤ S.toNat)
    {N : List Rgn}
    (hN : ∀ r ∈ N, r.In (pageUp b.toNat / 4096 * 4096) (pageUp (b + size pad 656#64).toNat / 4096 * 4096))
    (hh : ∀ a : Addr, (b + corr b).toNat ≤ a.toNat → a.toNat < (b + corr b).toNat + 656 + 16 → Foot (N ++ Wl) a)
    (hz : ∀ a : Addr, b.toNat ≤ a.toNat → a.toNat < pageUp b.toNat / 4096 * 4096 → V a = 0)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, S + 200#64) = e₂.add j₂)
    (k : ∀ (V₁ : Addr → Byte) (g₁ g₂ : Gprs) (evs : List Event) (s₁ Z : State) (t' : Nat),
      Seg prof (withNew F N) (N ++ Wl) L s₁ o →
      Base s₁ lim (b + size pad 656#64 + corr2 b (corr b) (size pad 656#64)) fsb ks →
      KeptW (N ++ Wl) s₁ Z →
      Agree (withNew F N) Z.proc.mm.mem
        (Vst V₁ (fsb + 18446744073709551576#64) (toBytesLE (b + corr b + 16#64) 8)) →
      Z.cpu.rip = e₂.add j₂ →
      (Z.cpu.gpr.rsp = S + 208#64 ∧ Z.cpu.gpr.rbp = X.cpu.gpr.rbp ∧ K5 X.cpu.gpr Z.cpu.gpr) →
      Out V V₁ b 656#64 (size pad 656#64) (corr2 b (corr b) (size pad 656#64)) sm
        (pageUp b.toNat / 4096 * 4096) (pageUp (b + size pad 656#64).toNat / 4096 * 4096)
        (S.toNat - 168) (S.toNat + 200) →
      (∀ a : Addr, (b + corr b).toNat + 16 ≤ a.toNat → a.toNat < (b + corr b).toNat + 656 → V₁ a = 0) →
      g₁.rdi = 656#64 → (g₂.rax = b ∧ g₂.r14 = size pad 656#64) →
      (evs = [smEv g₁ pad b] ∨ evs = [smEv g₁ pad b, smEv2 g₂]) →
      GoG prof L o (gev ++ evs) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hS8 : 8029888 ≤ S.toNat := by omega
  have hbt := hB.brk_lt
  have hb47 : b.toNat < 2 ^ 47 := by omega
  obtain ⟨hMt, hab, hc16, hM8⟩ := mt b hb47
  have h656 : (656#64 : BitVec 64).toNat = 656 := rfl
  have hsn := Smm.size_toNat (pad := pad) (nb := 656#64) (by rw [h656]; omega)
  have hbR : (b + size pad 656#64).toNat = b.toNat + (size pad 656#64).toNat := by
    rw [BitVec.toNat_add]
    omega
  have hhi : b.toNat + 688 ≤ pageUp (b + size pad 656#64).toNat / 4096 * 4096 ∧
      pageUp (b + size pad 656#64).toNat / 4096 * 4096 + 168 ≤ S.toNat := by
    unfold pageUp
    omega
  have hlo : b.toNat ≤ pageUp b.toNat / 4096 * 4096 := by unfold pageUp; omega
  have r200 := add_n S 200 (by omega)
  have r192 := add_n S 192 (by omega)
  have hf40 := f40 fsb (by omega)
  have hf24 := f24 fsb (by omega)
  have hfp := add_n fsb 24 (by omega)
  -- `push rbp`, the arena from `fs:-0x18`, one thread
  refine (c_0 prof fsb).run c hB.fsb hinT _ hK hA (by rw [hrip]; rfl)
    (vc_0 (g := X.cpu.gpr) (by rw [hrsp]; omega) (by rw [hrsp, s200]; exact st_at hst 192 (by decide)) hta hmt
      (fun i hi => c.hws _ (hfa i hi)) (fun i hi => c.hws _ (hfm i hi))
      (by rw [hrsp, s200, hf24, r192]; omega) (by rw [hrsp, s200, hfp, r192]; omega)) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  -- the lock: `cmpxchg [rbp], edx`
  have ea₁ : eaD Y₁ 5 0 = 7940672#64 := by rw [eaD, hg₁]; rfl
  have rv0 : rv Y₁ 32 0 = 0#32 := by rw [rv, hg₁]; rfl
  have rv2 : rv Y₁ 32 2 = 1#32 := by rw [rv, hg₁]; rfl
  refine c.s_cmpxchg_bd32 hK₁ hA₁ hinT (lt_len (by decide)) hr₁ (cx_42 _) (by rw [ea₁]; exact lk_ft hW)
    (by
      rw [ea₁, rv0, hrsp, s200, rd_Vst _ _ _ _ 4 (by rw [toBytesLE_length]; omega) (by decide)
        (.inr (by rw [BitVec.toNat_ofNat]; omega))]
      exact hlk) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, -⟩
  rw [ea₁, rv2, hrsp, s200] at hA₂
  -- the arguments of `_int_malloc`
  refine (c_46 prof fsb).run c hB.fsb hinT _ hK₂ hA₂ hr₂ vc_46 ?_
  rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
  have sp3 : Y₃.cpu.gpr.rsp = S + 192#64 := by
    have : Y₃.cpu.gpr.rsp = Y₂.cpu.gpr.rsp := by rw [hg₃]
    rw [this, hg₂, hg₁]
    show X.cpu.gpr.rsp - 8 = _
    rw [hrsp, s200]
  have bp3 : Y₃.cpu.gpr.rbp = 7940672#64 := by
    have : Y₃.cpu.gpr.rbp = Y₂.cpu.gpr.rbp := by rw [hg₃]
    rw [this, hg₂, hg₁]
  have di3 : Y₃.cpu.gpr.rdi = 7940672#64 := by
    have : Y₃.cpu.gpr.rdi = Y₂.cpu.gpr.rbp := by rw [hg₃]
    rw [this, hg₂, hg₁]
  have si3 : Y₃.cpu.gpr.rsi = 640#64 := by rw [hg₃]
  have k3 : K5 X.cpu.gpr Y₃.cpu.gpr := by
    have : K5 Y₂.cpu.gpr Y₃.cpu.gpr := by rw [hg₃]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    rw [hg₂, hg₁] at this
    exact this
  -- `call _int_malloc`
  refine c.s_call hK₃ hA₃ hinT (lt_len (by decide)) hr₃ (call_54 _) hin (Imm.lt_len (j := 0) (by decide)) tgt_54
    (by rw [sp3, s192]; exact st_at hst 184 (by decide)) ?_
  rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
  rw [sp3, s192] at hA₄
  have hA₄' : Agree F Y₄.proc.mm.mem (Vc S X.cpu.gpr.rbp V) := hA₄
  have sp4 : Y₄.cpu.gpr.rsp = S + 184#64 := by rw [hg₄]; show Y₃.cpu.gpr.rsp - 8 = _; rw [sp3, s192]
  have si4 : Y₄.cpu.gpr.rsi = 640#64 := by rw [hg₄]; exact si3
  have di4 : Y₄.cpu.gpr.rdi = 7940672#64 := by rw [hg₄]; exact di3
  have bp4 : Y₄.cpu.gpr.rbp = 7940672#64 := by rw [hg₄]; exact bp3
  have k4 : K5 X.cpu.gpr Y₄.cpu.gpr := k3.tr (by rw [hg₄]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
  -- `_int_malloc (arena, 640)`, its first call
  have Lo := Vc_lo S X.cpu.gpr.rbp V hS hS8
  have Mi := Vc_mid S X.cpu.gpr.rbp V hS hS8
  have hcu : curbrk.toNat = 8014904 := by decide
  refine Imm.im_first (pad := pad) (sm := sm) (mx := mx) (N := N) c hB hin hinS hinD hinK hinb hK₄ hA₄' hr₄
    sp4 si4 di4 hsp hS (st_in hst) hW hhk hcur hml hpb hgf (fun i hi => c.hws _ (hft i hi)) (by rw [hf40]; omega)
    (by rw [Mi 8013224 8 (by decide) (by decide)]; exact hgm) (by rw [Mi 7941432 8 (by decide) (by decide)]; exact hs41)
    (by rw [Vc_rd S _ V hS hS8 (.inr ⟨by rw [hf40]; omega, by rw [hf40]; omega⟩)]; exact htc)
    (by rw [Mi 7940792 8 (by decide) (by decide)]; exact hun)
    (by rw [Mi 7942820 4 (by decide) (by decide)]; exact hm1) (by rw [Mi 7942824 4 (by decide) (by decide)]; exact hm2)
    (by rw [Mi 7942828 4 (by decide) (by decide)]; exact hm3) (by rw [Mi 7943128 8 (by decide) (by decide)]; exact hps)
    (by rw [Lo 7940528 8 (by decide)]; exact hthr) (by rw [Mi 7940768 8 (by decide) (by decide)]; exact htop)
    (by rw [Mi 7940776 8 (by decide) (by decide)]; exact hsz) (by rw [Lo 7940520 8 (by decide)]; exact hpad) hnb
    (by rw [Mi 7940676 1 (by decide) (by decide)]; exact hfl) (by rw [Mi 7940680 4 (by decide) (by decide)]; exact hfc)
    (by rw [Mi 7942872 8 (by decide) (by decide)]; exact hmc)
    (by rw [Vc_rd S _ V hS hS8 (.inr ⟨by rw [hcu]; omega, by rw [hcu]; omega⟩)]; exact hcb)
    (by rw [Mi 7944640 4 (by decide) (by decide)]; exact hm0) (by rw [Mi 8013152 8 (by decide) (by decide)]; exact hk0)
    (by rw [Mi 7942856 8 (by decide) (by decide)]; exact hsm) (by rw [Lo 7940584 8 (by decide)]; exact hsb)
    (by rw [Mi 7942864 8 (by decide) (by decide)]; exact hmx) hms hsu
    (by rw [Mi 8013220 4 (by decide) (by decide)]; exact hp0) hmg hlim hbl hbs hN hh hinT (lt_len (j := 59) (by decide))
    (Vc_ret S _ V hS) ?_
  intro V' g₁ g₂ evs s₁ Z t' c' hB' hK' hA' hr' hax ⟨y1, y2, y3, y4, y5, y6, y7⟩ hO hg1 hg2 hev
  have hhw : (b + corr b).toNat + (656#64 : BitVec 64).toNat + 16 ≤ S.toNat := by rw [h656]; omega
  have hM0 : b + corr b + 16#64 ≠ 0 := fun h => by
    have h' := congrArg BitVec.toNat h
    rw [hMt, show (0 : BitVec 64).toNat = 0 from rfl] at h'
    omega
  -- one thread still: the chunk in `r8`
  refine (c_59 prof fsb).run c' hB'.fsb hinT _ hK' hA' hr' (vc_59 (by rw [hax]; exact hM0)
    (by rw [out_lo hO hS hb47 hlo (by omega) (by rw [hfp]; omega) (by rw [hfp]; omega)]; exact hmt)
    (fun i hi => c'.hws _ (foot_append_iff.2 (.inr (hfm i hi))))) ?_
  rintro j' g fl V₅ ⟨rfl, rfl, rfl⟩ Y₅ t₅ hK₅ hA₅ hr₅ hg₅ -
  have r85 : Y₅.cpu.gpr.r8 = b + corr b + 16#64 := by rw [hg₅]; exact hax
  have bp5 : Y₅.cpu.gpr.rbp = 7940672#64 := by rw [hg₅]; exact y3.trans bp4
  have sp5 : Y₅.cpu.gpr.rsp = S + 192#64 := by rw [hg₅]; exact y1
  have k5 : K5 X.cpu.gpr Y₅.cpu.gpr :=
    (k4.tr ⟨y2, y4, y5, y6, y7⟩).tr (by rw [hg₅]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
  -- the lock given back: `sub dword [rbp], 1`
  have ea₅ : eaD Y₅ 5 0 = 7940672#64 := by rw [eaD]; show Y₅.cpu.gpr.rbp + _ = _; rw [bp5]; rfl
  refine c'.s_sub_mi32 hK₅ hA₅ hinT (lt_len (by decide)) hr₅ (sb_87 _)
    (by rw [ea₅]; exact fun i hi => foot_append_iff.2 (.inr (lk_ft hW i hi))) ?_
  rintro Y₆ t₆ hK₆ hA₆ ⟨hr₆, hg₆⟩
  rw [ea₅, out_lk hO hS hsp hbl hb47 (by omega), show (1#32 : BitVec 32) - BitVec.ofNat 32 1 = 0#32 by decide]
    at hA₆
  have r86 : Y₆.cpu.gpr.r8 = b + corr b + 16#64 := by rw [hg₆]; exact r85
  have sp6 : Y₆.cpu.gpr.rsp = S + 192#64 := by rw [hg₆]; exact sp5
  have k6 : K5 X.cpu.gpr Y₆.cpu.gpr := k5.tr (by rw [hg₆]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
  -- the chunk as the cache, its first and last quadwords 0
  refine (c_91 prof fsb).run c' hB'.fsb hinT _ hK₆ hA₆ hr₆
    (vc_91 (by rw [r86]; exact hM0) (by rw [r86]; exact hM8) (fun i hi => foot_append_iff.2 (.inr (hft i hi)))
      (by rw [r86]; exact ch_ft hb47 hh (d := 0) (by rw [hMt]; omega) (by decide))
      (by
        rw [r86]
        exact ch_ft hb47 hh (d := 632) (by rw [add_n (b + corr b + 16#64) 632 (by rw [hMt]; omega), hMt]; omega)
          (by decide))) ?_
  rintro j' g fl V₇ ⟨rfl, rfl, rfl⟩ Y₇ t₇ hK₇ hA₇ hr₇ hg₇ -
  have di7 : Y₇.cpu.gpr.rdi = b + corr b + 16#64 + 8#64 := by
    rw [hg₇]; show Y₆.cpu.gpr.r8 + 8#64 = _; rw [r86]
  have ax7 : Y₇.cpu.gpr.rax = 0 := by rw [hg₇]
  have sp7 : Y₇.cpu.gpr.rsp = S + 192#64 := by rw [hg₇]; exact sp6
  have k7 : K5 X.cpu.gpr Y₇.cpu.gpr := k6.tr (by rw [hg₇]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
  -- `rep stos`: the 632 bytes between, 0
  refine c'.s_rep_stosq hB'.df hinT (lt_len (j := 148) (by decide)) (lt_len (by decide)) (stos_146 _) 78 hK₇ hA₇
    hr₇ (by rw [hg₇]; rfl)
    (by
      rw [di7]
      exact ch_ft hb47 hh (d := 8) (by rw [add_n (b + corr b + 16#64) 8 (by rw [hMt]; omega), hMt]; omega)
        (by decide)) ?_
  rintro Y₈ t₈ hK₈ hA₈ ⟨hr₈, hg₈⟩
  rw [di7, ax7, r86, fin (v := 0#64) rfl rfl (by rw [hf40, hMt]; omega) (by rw [hMt]; omega) fun a h1 h2 =>
    cz hO hS hbl hb47 hhi.1 hhi.2 hz a (by rw [hMt] at h1; omega) (by rw [hMt] at h2; omega)] at hA₈
  generalize Y₇.cpu.gpr.rdi + BitVec.ofNat 64 (8 * (78 + 1)) = w₈ at hg₈
  have sp8 : Y₈.cpu.gpr.rsp = S + 192#64 := by rw [hg₈]; exact sp7
  have k8 : K5 X.cpu.gpr Y₈.cpu.gpr := k7.tr (by rw [hg₈]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
  obtain ⟨fr1, fr2⟩ := fin_rd (T := fsb + 18446744073709551576#64) (m := b + corr b + 16#64) hO hS hS8
    (by omega) hhw (by rw [hf40]; omega)
  -- `pop rbp`
  refine (c_149 prof fsb).run c' hB'.fsb hinT _ hK₈ hA₈ hr₈
    (vc_149 (by rw [sp8]; exact fun i hi => c'.hws _ (foot_append_iff.2 (.inr (st_at hst 192 (by decide) i hi))))) ?_
  rintro j' g fl V₉ ⟨rfl, rfl, rfl⟩ Y₉ t₉ hK₉ hA₉ hr₉ hg₉ -
  have sp9 : Y₉.cpu.gpr.rsp = S + 200#64 := by rw [hg₉]; show Y₈.cpu.gpr.rsp + 8 = _; rw [sp8, s8]
  have bp9 : Y₉.cpu.gpr.rbp = X.cpu.gpr.rbp := by rw [hg₉]; show rdq(_, Y₈.cpu.gpr.rsp) = _; rw [sp8]; exact fr1
  have k9 : K5 X.cpu.gpr Y₉.cpu.gpr := k8.tr (by rw [hg₉]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
  -- `ret`
  refine c'.s_ret hK₉ hA₉ hinT (lt_len (by decide)) hr₉ (ret_150 _)
    (by rw [sp9]; exact fun i hi => c'.hws _ (foot_append_iff.2 (.inr (st_at hst 200 (by decide) i hi)))) hin₂ h₂
    (by rw [sp9]; exact fr2.trans hra) ?_
  rintro Z₂ t₂' hKZ hAZ ⟨hrZ, hgZ⟩
  refine k _ g₁ g₂ evs s₁ Z₂ t₂' c' hB' hKZ hAZ hrZ ⟨?_, ?_, ?_⟩
    (out_tci hO hS hbl hb47 (by decide) (by omega) hlk) (cz hO hS hbl hb47 hhi.1 hhi.2 hz) hg1 hg2 hev
  · rw [hgZ]; show Y₉.cpu.gpr.rsp + 8 = _; rw [sp9, s208]
  · rw [hgZ]; exact bp9
  · exact k9.tr (by rw [hgZ]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)

end FV7z.Tci
