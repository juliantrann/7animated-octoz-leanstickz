import FV7z.Rfi.Cuts
import FV7z.Pml.Holds
import FV7z.Pmu.Holds
/-!
# `__register_frame_info` (PLAN.md G3, startup)

libgcc's `__register_frame_info (begin, ob)` at `0x6127e0` in `7zzs` (`libgcc/unwind-dw2-fde.c`), what `frame_dummy`
calls with `__EH_FRAME_BEGIN__` and its static `object`: with `begin` not null and its first word not 0, it goes on
into `__register_frame_info_bases (begin, ob, 0, 0)` (`0x612730`): the object's words are set (`pc_begin := -1`,
`tbase := 0`, `dbase := 0`, `u.single := begin`, `s.i := 0x7f8`), `pthread_mutex_lock (&object_mutex)`
(`0x7a33a0`), the object goes to the head of `unseen_objects` (`0x7a33d8`), `any_objects_registered` (`0x7a33c8`)
becomes 1, and the function ends in `pthread_mutex_unlock (&object_mutex)`.

- `call_55`, `jmp_106`: the instructions outside the blocks; `vc_176`, `vc_60`, `vc_88`: the verification
  conditions.
- `Env`: what the code, the 56 bytes of stack, the object, the mutex and the two words need; `Wr`: the bytes outside
  the stack the function stores into; `Vp`, `Vc`, `Ve`: the memory after the prologue, at the call and before the
  tail call; `Dat`: what the caller gets (`Dat.wide`: for a caller with a frame of its own).
- `rfi_ok`: called for the first time (`any_objects_registered` 0) with the mutex free, the run reaches the return
  address, the registers a call keeps as at the entry (`Osv.Back`), the object at the head of the list (`Dat`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Sga (vo vr vs rd_out)
open FV7z.Raf (off_ft)
namespace FV7z.Rfi

/-! ## The instructions outside the blocks -/

def pc0 : List Byte := [0xe8, 0xe4, 0x9c, 0xfe, 0xff]
theorem pc0_0 : ∀ feat, Dec feat pc0 0 (FV7z.mk .call 64 [.rel 18446744073709460708] 5) := by dec_rfl
theorem w_55 : pc0 <+: rfi.drop 55 := by decide +kernel
/-- `call pthread_mutex_lock`. -/
theorem call_55 (feat : Features) : Dec feat rfi 55 (FV7z.mk .call 64 [.rel 18446744073709460708] 5) :=
  Dec.shift (j := 55) (k := 0) (pc0_0 feat) w_55 (Nat.zero_le _)

def pj0 : List Byte := [0xe9, 0x31, 0xaa, 0xfe, 0xff]
theorem pj0_0 : ∀ feat, Dec feat pj0 0 (FV7z.mk .jmp 64 [.rel 18446744073709464113] 5) := by dec_rfl
theorem w_106 : pj0 <+: rfi.drop 106 := by decide +kernel
/-- `jmp pthread_mutex_unlock`. -/
theorem jmp_106 (feat : Features) : Dec feat rfi 106 (FV7z.mk .jmp 64 [.rel 18446744073709464113] 5) :=
  Dec.shift (j := 106) (k := 0) (pj0_0 feat) w_106 (Nat.zero_le _)

/-! ## The verification conditions -/

variable {F : Footprint} {Wl : List Rgn}

/-- From the entry of `__register_frame_info` to the call of `pthread_mutex_lock`: the object's five words. -/
theorem vc_176 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hd : g.rdi ≠ 0)
    (hbf : ∀ i < 4, Foot F.data (Addr.add g.rdi i)) (hb : rdd(V, g.rdi) ≠ 0)
    (h1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (h2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (ho : ∀ i < 40, Foot Wl (Addr.add g.rsi i)) :
    W_176 F Wl (fun j' g' _ V' => j' = 55 ∧
      g' = { g with rax := BitVec.setWidth 64 rdd(V, g.rdi), rcx := 0, rdx := 0, rbx := g.rsi,
                    rsp := g.rsp - 8 - 8 - 8#64, rbp := 6286176#64, rdi := 8008608#64 } ∧
      V' = Vst (Vst (Vst (Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8) (toBytesLE g.rbx 8))
        g.rsi (toBytesLE (18446744073709551615#64) 8)) (g.rsi + 8#64) (toBytesLE (0#64) 8))
        (g.rsi + 16#64) (toBytesLE (0#64) 8)) (g.rsi + 24#64) (toBytesLE g.rdi 8))
        (g.rsi + 32#64) (toBytesLE (2040#64) 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hd hbf hb h1 h2 ho
  wpx [W_176, W_185, W_191, W_0, W_48, o7, o8, o9, o0, o1, BitVec.xor_self, BitVec.and_self]
  exact ⟨fun h => absurd (by simpa using h) hd, fun _ => ⟨hbf, fun h => absurd (by simpa using h) hb, fun _ =>
    ⟨h1, h2, fun i hi => ho i (by omega), off_ft ho 8 rfl (by decide), off_ft ho 16 rfl (by decide),
      off_ft ho 24 rfl (by decide), off_ft ho 32 rfl (by decide), fun h => absurd h (by decide),
      fun _ => ⟨rfl, rfl⟩⟩⟩⟩

/-- The object to the head of `unseen_objects`; `any_objects_registered` was 0 and becomes 1. -/
theorem vc_60 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hu : ∀ i < 8, Foot Wl (Addr.add (8008664#64) i)) (hur : ∀ i < 8, Foot F.data (Addr.add (8008664#64) i))
    (hn : ∀ i < 8, Foot Wl (Addr.add (g.rbx + 40#64) i))
    (ha : ∀ i < 4, Foot Wl (Addr.add (8008648#64) i)) (har : ∀ i < 4, Foot F.data (Addr.add (8008648#64) i))
    (hany : rdd(Vst (Vst V (8008664#64) (toBytesLE g.rbx 8)) (g.rbx + 40#64) (toBytesLE rdq(V, 8008664#64) 8),
      8008648#64) = 0) :
    W_60 F Wl (fun j' g' _ V' => j' = 88 ∧ g' = { g with rax := 0 } ∧
      V' = Vst (Vst (Vst V (8008664#64) (toBytesLE g.rbx 8)) (g.rbx + 40#64) (toBytesLE rdq(V, 8008664#64) 8))
        (8008648#64) (toBytesLE (1#32) 4)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hu hur hn ha har hany
  wpx [W_60, W_128, o2, o6, Op.lda, Op.sta, Op.stia, hany, BitVec.and_self]
  exact ⟨hur, hu, hn, har, fun _ => ⟨ha, rfl⟩, fun h => absurd h (by decide)⟩

/-- The epilogue up to the tail call. -/
theorem vc_88 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hp : g.rbp = 6286176)
    (h1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (h2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i)) :
    W_88 F Wl (fun j' g' _ V' => j' = 106 ∧
      g' = { g with rbx := rdq(V, g.rsp + 8#64), rsp := g.rsp + 8#64 + 8 + 8, rbp := rdq(V, g.rsp + 8#64 + 8),
                    rdi := 8008608#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hp h1 h2
  subst hp
  wpx [W_88, W_93, W_112, o3, o4, o5, BitVec.and_self]
  exact ⟨fun h => absurd h (by decide), fun _ => ⟨h1, h2⟩⟩

/-! ## The memory -/

/-- What `__register_frame_info (begin, ob)`, called with the stack pointer `S` in the thread whose block is at
`fb`, needs of the code and the memory: the 56 bytes below `S` (its 24, the return address, `pthread_mutex_lock`'s
24), the object's 48, the mutex's 20 and the two words for the run to store into; the stack and the thread's block
above the data, the object below `__pthread_force_elision`. -/
structure Env (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (fb S ob : Addr) : Prop where
  code : CodeIn L rfi_at rfi
  lcode : CodeIn L Pml.pml_at Pml.pml
  ucode : CodeIn L Pmu.pmu_at Pmu.pmu
  s0 : 8008672 + 56 ≤ S.toNat
  s8 : S.toNat + 8 ≤ 2 ^ 64
  o0 : ob.toNat + 48 ≤ 7991628
  f0 : 8008672 ≤ fb.toNat
  f1 : fb.toNat + 724 ≤ S.toNat - 56
  st : ∀ i < 56, Foot Wl (Addr.add (S - 56#64) i)
  lr : ∀ i < 8, Foot F.data (Addr.add S i)
  ob : ∀ i < 48, Foot Wl (Addr.add ob i)
  mu : ∀ i < 20, Foot Wl (Addr.add (8008608#64) i)
  any : ∀ i < 4, Foot Wl (Addr.add (8008648#64) i)
  uns : ∀ i < 8, Foot Wl (Addr.add (8008664#64) i)
  tid : ∀ i < 4, Foot F.data (Addr.add (fb + 720#64) i)
  fe : ∀ i < 4, Foot F.data (Addr.add (7991628#64) i)

/-- The bytes outside the stack the function stores into: the object, the mutex's lock word, owner and count of
users, `any_objects_registered`, `unseen_objects`. -/
def Wr (ob : Addr) (n : Nat) : Prop :=
  (ob.toNat ≤ n ∧ n < ob.toNat + 48) ∨ (8008608 ≤ n ∧ n < 8008612) ∨ (8008616 ≤ n ∧ n < 8008624) ∨
    (8008648 ≤ n ∧ n < 8008652) ∨ (8008664 ≤ n ∧ n < 8008672)

/-- What the caller gets: the bytes outside the stack's `[lo, hi)` and `Wr` as they were; the object's six words,
the object the head of `unseen_objects`, `any_objects_registered` 1, the mutex free with as many users as before. -/
structure Dat (lo hi : Nat) (ob bg : Addr) (V V' : Addr → Byte) : Prop where
  out : ∀ a : Addr, ¬ (lo ≤ a.toNat ∧ a.toNat < hi) → ¬ Wr ob a.toNat → V' a = V a
  pcb : rdq(V', ob) = 18446744073709551615#64
  tb : rdq(V', ob + 8#64) = 0
  db : rdq(V', ob + 16#64) = 0
  bg : rdq(V', ob + 24#64) = bg
  enc : rdq(V', ob + 32#64) = 2040
  nxt : rdq(V', ob + 40#64) = rdq(V, 8008664#64)
  uns : rdq(V', 8008664#64) = ob
  any : rdd(V', 8008648#64) = 1
  lock : rdd(V', 8008608#64) = 0
  own : rdd(V', 8008608#64 + 8#64) = 0
  nus : rdd(V', 8008608#64 + 12#64) = rdd(V, 8008608#64 + 12#64)

/-- The same for a caller that had stored into a part of the stack around `[lo, hi)` before the call. -/
theorem Dat.wide {lo hi lo' hi' : Nat} {ob bg : Addr} {V V₁ V' : Addr → Byte} (h : Dat lo hi ob bg V₁ V')
    (hV : ∀ a : Addr, ¬ (lo' ≤ a.toNat ∧ a.toNat < hi') → V₁ a = V a) (hl : lo' ≤ lo) (hh : hi ≤ hi')
    (h0 : 8008672 ≤ lo') : Dat lo' hi' ob bg V V' where
  out := fun a h1 h2 => (h.out a (by omega) h2).trans (hV a h1)
  pcb := h.pcb
  tb := h.tb
  db := h.db
  bg := h.bg
  enc := h.enc
  nxt := h.nxt.trans (congrArg (ofBytesLE 64) (rd_out hV (by decide)
    (.inl (by have : (8008664#64).toNat = 8008664 := rfl; omega))))
  uns := h.uns
  any := h.any
  lock := h.lock
  own := h.own
  nus := h.nus.trans (congrArg (ofBytesLE 32) (rd_out hV (by decide)
    (.inl (by have : (8008608#64 + 12#64).toNat = 8008620 := rfl; omega))))

/-- The memory after the prologue: the two registers pushed, the object's five words. -/
abbrev Vp (V : Addr → Byte) (S ob bg : Addr) (rb rp : BitVec 64) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (Vst (Vst V (S - 8#64) (toBytesLE rp 8)) (S - 16#64) (toBytesLE rb 8))
    ob (toBytesLE (18446744073709551615#64) 8)) (ob + 8#64) (toBytesLE (0#64) 8))
    (ob + 16#64) (toBytesLE (0#64) 8)) (ob + 24#64) (toBytesLE bg 8)) (ob + 32#64) (toBytesLE (2040#64) 8)

/-- The memory at the call: the return address pushed. -/
abbrev Vc (V : Addr → Byte) (S ob bg : Addr) (rb rp ra : BitVec 64) : Addr → Byte :=
  Vst (Vp V S ob bg rb rp) (S - 32#64) (toBytesLE ra 8)

/-- The memory before the tail call: the object the head of the list, `any_objects_registered` 1. -/
abbrev Ve (Vl : Addr → Byte) (ob : Addr) (u : BitVec 64) : Addr → Byte :=
  Vst (Vst (Vst Vl (8008664#64) (toBytesLE ob 8)) (ob + 40#64) (toBytesLE u 8)) (8008648#64) (toBytesLE (1#32) 4)

/-- Bytes where two memories are the same. -/
theorem rd_of {V V' : Addr → Byte} {x : Addr} {n : Nat} (hx : x.toNat + n ≤ 2 ^ 64)
    (h : ∀ a : Addr, x.toNat ≤ a.toNat → a.toNat < x.toNat + n → V' a = V a) :
    List.map V' (byteAddrs x n) = List.map V (byteAddrs x n) := by
  apply List.map_congr_left
  intro y hy
  obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hy
  refine h _ ?_ ?_ <;> rw [toNat_add_of_fits hj hx] <;> omega

section
variable {S ob bg : Addr} {rb rp ra u : BitVec 64} {tid : BitVec 32} {V Vl Vf V₁ V₂ : Addr → Byte} {x : Addr}
  {n : Nat}

/-- The data between `__pthread_force_elision` and `unseen_objects` at the call. -/
theorem vc_rd (hx0 : 7991628 ≤ x.toNat) (hx1 : x.toNat + n ≤ 8008672) (hs0 : 8008672 + 56 ≤ S.toNat)
    (hs8 : S.toNat + 8 ≤ 2 ^ 64) (ho0 : ob.toNat + 48 ≤ 7991628) :
    List.map (Vc V S ob bg rb rp ra) (byteAddrs x n) = List.map V (byteAddrs x n) := by
  unfold Vc Vp
  repeat pv

/-- Bytes apart from what the function stores once it has the lock. -/
theorem e_l (hx : x.toNat + n ≤ 2 ^ 64) (ho0 : ob.toNat + 48 ≤ 7991628)
    (h1 : x.toNat + n ≤ 8008648 ∨ 8008652 ≤ x.toNat) (h2 : x.toNat + n ≤ 8008664 ∨ 8008672 ≤ x.toNat)
    (h3 : x.toNat + n ≤ ob.toNat + 40 ∨ ob.toNat + 48 ≤ x.toNat) :
    List.map (Ve Vl ob u) (byteAddrs x n) = List.map Vl (byteAddrs x n) := by
  unfold Ve
  pv
  pv
  pv

/-- Bytes apart from what `pthread_mutex_lock` stores. -/
theorem l_c (hD : Pml.Dat (S - 32#64) (8008608#64) tid V₁ Vl) (hx : x.toNat + n ≤ 2 ^ 64)
    (hs0 : 8008672 + 56 ≤ S.toNat) (h1 : x.toNat + n ≤ S.toNat - 40 ∨ S.toNat - 32 ≤ x.toNat)
    (h2 : x.toNat + n ≤ 8008608 ∨ 8008612 ≤ x.toNat) (h3 : x.toNat + n ≤ 8008616 ∨ 8008624 ≤ x.toNat) :
    List.map Vl (byteAddrs x n) = List.map V₁ (byteAddrs x n) :=
  rd_of hx fun a _ _ => hD.out a (by bv_omega) (by bv_omega) (by bv_omega)

/-- Bytes apart from what `pthread_mutex_unlock` stores. -/
theorem u_e (hD : Pmu.Dat (8008608#64) V₂ Vf) (hx : x.toNat + n ≤ 2 ^ 64)
    (h2 : x.toNat + n ≤ 8008608 ∨ 8008612 ≤ x.toNat) (h3 : x.toNat + n ≤ 8008616 ∨ 8008624 ≤ x.toNat) :
    List.map Vf (byteAddrs x n) = List.map V₂ (byteAddrs x n) :=
  rd_of hx fun a _ _ => hD.out a (by bv_omega) (by bv_omega)

/-- `any_objects_registered` once the object is in the list. -/
theorem pre_any (hDl : Pml.Dat (S - 32#64) (8008608#64) tid (Vc V S ob bg rb rp ra) Vl)
    (hs0 : 8008672 + 56 ≤ S.toNat) (hs8 : S.toNat + 8 ≤ 2 ^ 64) (ho0 : ob.toNat + 48 ≤ 7991628)
    (hany : rdd(V, 8008648#64) = 0) :
    rdd(Vst (Vst Vl (8008664#64) (toBytesLE ob 8)) (ob + 40#64) (toBytesLE rdq(Vl, 8008664#64) 8),
      8008648#64) = 0 := by
  pv
  pv
  exact (congrArg (ofBytesLE 32) ((l_c hDl (by bv_omega) hs0 (by bv_omega) (by bv_omega) (by bv_omega)).trans
    (vc_rd (by bv_omega) (by bv_omega) hs0 hs8 ho0))).trans hany

/-- What the epilogue and `pthread_mutex_unlock` read. -/
theorem pre_u (hDl : Pml.Dat (S - 32#64) (8008608#64) tid (Vc V S ob bg rb rp ra) Vl)
    (hs0 : 8008672 + 56 ≤ S.toNat) (hs8 : S.toNat + 8 ≤ 2 ^ 64) (ho0 : ob.toNat + 48 ≤ 7991628) :
    rdq(Ve Vl ob u, S - 16#64) = rb ∧ rdq(Ve Vl ob u, S - 8#64) = rp ∧ rdq(Ve Vl ob u, S) = rdq(V, S) ∧
      rdd(Ve Vl ob u, 8008608#64 + 16#64) = rdd(V, 8008608#64 + 16#64) ∧ rdd(Ve Vl ob u, 8008608#64) = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine (congrArg (ofBytesLE 64) ((e_l (by bv_omega) ho0 (by bv_omega) (by bv_omega) (by bv_omega)).trans
      (l_c hDl (by bv_omega) hs0 (by bv_omega) (by bv_omega) (by bv_omega)))).trans ?_
    unfold Vc Vp
    repeat pv
    rw [vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · refine (congrArg (ofBytesLE 64) ((e_l (by bv_omega) ho0 (by bv_omega) (by bv_omega) (by bv_omega)).trans
      (l_c hDl (by bv_omega) hs0 (by bv_omega) (by bv_omega) (by bv_omega)))).trans ?_
    unfold Vc Vp
    repeat pv
    rw [vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · refine (congrArg (ofBytesLE 64) ((e_l (by bv_omega) ho0 (by bv_omega) (by bv_omega) (by bv_omega)).trans
      (l_c hDl (by bv_omega) hs0 (by bv_omega) (by bv_omega) (by bv_omega)))).trans ?_
    unfold Vc Vp
    repeat pv
  · exact congrArg (ofBytesLE 32) ((e_l (by bv_omega) ho0 (by bv_omega) (by bv_omega) (by bv_omega)).trans
      ((l_c hDl (by bv_omega) hs0 (by bv_omega) (by bv_omega) (by bv_omega)).trans
        (vc_rd (by bv_omega) (by bv_omega) hs0 hs8 ho0)))
  · exact (congrArg (ofBytesLE 32) (e_l (by bv_omega) ho0 (by bv_omega) (by bv_omega) (by bv_omega))).trans
      hDl.lock

/-- The memory at the end. -/
theorem fin (hDl : Pml.Dat (S - 32#64) (8008608#64) tid (Vc V S ob bg rb rp ra) Vl)
    (hDu : Pmu.Dat (8008608#64) (Ve Vl ob rdq(Vl, 8008664#64)) Vf)
    (hs0 : 8008672 + 56 ≤ S.toNat) (hs8 : S.toNat + 8 ≤ 2 ^ 64) (ho0 : ob.toNat + 48 ≤ 7991628) :
    Dat (S.toNat - 56) S.toNat ob bg V Vf := by
  have thru : ∀ {x : Addr}, x.toNat + 8 ≤ 2 ^ 64 → ob.toNat ≤ x.toNat → x.toNat + 8 ≤ ob.toNat + 40 →
      List.map Vf (byteAddrs x 8) = List.map (Vc V S ob bg rb rp ra) (byteAddrs x 8) := fun {x} hx h0 h1 =>
    (u_e hDu hx (by omega) (by omega)).trans ((e_l hx ho0 (by omega) (by omega) (by omega)).trans
      (l_c hDl hx hs0 (by omega) (by omega) (by omega)))
  refine ⟨fun a h1 h2 => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hDu.lock, hDu.own, ?_⟩
  · have hw := h2
    simp only [Wr, not_or] at hw
    rw [hDu.out a (by bv_omega) (by bv_omega)]
    unfold Ve
    pv
    pv
    pv
    rw [hDl.out a (by bv_omega) (by bv_omega) (by bv_omega)]
    unfold Vc Vp
    repeat pv
  · refine (congrArg (ofBytesLE 64) (thru (by bv_omega) (by bv_omega) (by bv_omega))).trans ?_
    unfold Vc Vp
    repeat pv
    rw [vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · refine (congrArg (ofBytesLE 64) (thru (by bv_omega) (by bv_omega) (by bv_omega))).trans ?_
    unfold Vc Vp
    repeat pv
    rw [vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · refine (congrArg (ofBytesLE 64) (thru (by bv_omega) (by bv_omega) (by bv_omega))).trans ?_
    unfold Vc Vp
    repeat pv
    rw [vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · refine (congrArg (ofBytesLE 64) (thru (by bv_omega) (by bv_omega) (by bv_omega))).trans ?_
    unfold Vc Vp
    repeat pv
    rw [vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · refine (congrArg (ofBytesLE 64) (thru (by bv_omega) (by bv_omega) (by bv_omega))).trans ?_
    unfold Vc Vp
    repeat pv
    rw [vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · refine (congrArg (ofBytesLE 64) (u_e hDu (by bv_omega) (by bv_omega) (by bv_omega))).trans ?_
    unfold Ve
    pv
    rw [vs (by ln) (by bv_omega), ofBytesLE_toBytesLE (n := 8) rfl _]
    exact congrArg (ofBytesLE 64) ((l_c hDl (by bv_omega) hs0 (by bv_omega) (by bv_omega) (by bv_omega)).trans
      (vc_rd (by bv_omega) (by bv_omega) hs0 hs8 ho0))
  · refine (congrArg (ofBytesLE 64) (u_e hDu (by bv_omega) (by bv_omega) (by bv_omega))).trans ?_
    unfold Ve
    pv
    pv
    rw [vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · refine (congrArg (ofBytesLE 32) (u_e hDu (by bv_omega) (by bv_omega) (by bv_omega))).trans ?_
    unfold Ve
    rw [vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 4) rfl _
  · have e1 : rdd(Ve Vl ob rdq(Vl, 8008664#64), 8008608#64 + 12#64) = rdd(Vl, 8008608#64 + 12#64) :=
      congrArg (ofBytesLE 32) (e_l (by bv_omega) ho0 (by bv_omega) (by bv_omega) (by bv_omega))
    have e3 : rdd(Vc V S ob bg rb rp ra, 8008608#64 + 12#64) = rdd(V, 8008608#64 + 12#64) :=
      congrArg (ofBytesLE 32) (vc_rd (by bv_omega) (by bv_omega) hs0 hs8 ho0)
    rw [hDu.nus, e1, hDl.nus, e3]
    exact BitVec.add_sub_cancel _ _

end

/-! ## The whole -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {V : Addr → Byte}

theorem a16 (S : Addr) : S - 8 - 8 = S - 16#64 := by bv_omega
theorem a24 (S : Addr) : S - 8 - 8 - 8#64 = S - 24#64 := by bv_omega
theorem a32 (S : Addr) : S - 24#64 - 8 = S - 32#64 := by bv_omega
theorem a48 (S : Addr) : S - 8 = S - 56#64 + BitVec.ofNat 64 48 := by bv_omega
theorem a40 (S : Addr) : S - 8 - 8 = S - 56#64 + BitVec.ofNat 64 40 := by bv_omega
theorem d32 (S : Addr) : S - 32#64 = S - 56#64 + BitVec.ofNat 64 24 := by bv_omega
theorem d40 (S : Addr) : S - 32#64 - 8#64 = S - 56#64 + BitVec.ofNat 64 16 := by bv_omega
theorem d16 (S : Addr) : S - 16#64 = S - 56#64 + BitVec.ofNat 64 40 := by bv_omega
theorem d8 (S : Addr) : S - 8#64 = S - 56#64 + BitVec.ofNat 64 48 := by bv_omega
theorem c24 (S : Addr) : S - 32#64 + 8#64 = S - 24#64 := by bv_omega
theorem c16 (S : Addr) : S - 24#64 + 8#64 = S - 16#64 := by bv_omega
theorem c8 (S : Addr) : S - 24#64 + 8#64 + 8 = S - 8#64 := by bv_omega
theorem c0 (S : Addr) : S - 24#64 + 8#64 + 8 + 8 = S := by bv_omega

/-- `__register_frame_info (begin, ob)`, the first registration, the mutex free and of the plain kind, no elision:
the run reaches the return address, the registers a call keeps as at the entry, the object at the head of
`unseen_objects` (`Dat`). -/
theorem rfi_ok {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hE : Env F Wl L fb X.cpu.gpr.rsp X.cpu.gpr.rsi) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = rfi_at.add 176) (hd : X.cpu.gpr.rdi ≠ 0)
    (hbf : ∀ i < 4, Foot F.data (Addr.add X.cpu.gpr.rdi i)) (hb : rdd(V, X.cpu.gpr.rdi) ≠ 0)
    (hkd : rdd(V, 8008608#64 + 16#64) = 0) (hfe : rdd(V, 7991628#64) = 0) (hlk : rdd(V, 8008608#64) = 0)
    (how : rdd(V, 8008608#64 + 8#64) = 0) (hany : rdd(V, 8008648#64) = 0)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ V' Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Dat (X.cpu.gpr.rsp.toNat - 56) X.cpu.gpr.rsp.toNat X.cpu.gpr.rsi X.cpu.gpr.rdi V V' →
      Z.cpu.rip = e₂.add j₂ → Osv.Back X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hs0 := hE.s0
  have hs8 := hE.s8
  have ho0 := hE.o0
  have hf0 := hE.f0
  have hf1 := hE.f1
  -- the prologue and the object's words
  refine (c_176 prof).run c hE.code _ hK hA hrip
    (vc_176 hd hbf hb (off_ft hE.st 48 (a48 _) (by decide)) (off_ft hE.st 40 (a40 _) (by decide))
      (fun i hi => hE.ob i (by omega))) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  rw [a16, show X.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 8#64 from rfl] at hA₁
  have hsp₁ : Y₁.cpu.gpr.rsp = X.cpu.gpr.rsp - 24#64 := by rw [hg₁]; exact a24 _
  -- `pthread_mutex_lock (&object_mutex)`
  refine c.s_call hK₁ hA₁ hE.code (lt_len (by decide)) hr₁ (call_55 _) hE.lcode (Pml.lt_len (by decide))
    (by decide) (fun i hi => ?_) ?_
  · rw [hsp₁, a32]
    exact off_ft hE.st 24 (d32 _) (by decide) i hi
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsp₁, a32] at hA₂ hg₂
  have hsp₂ : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 32#64 := by rw [hg₂]; rfl
  have hdi₂ : Y₂.cpu.gpr.rdi = 8008608#64 := by rw [hg₂, hg₁]; rfl
  have hPE : Pml.Env F Wl L fb (X.cpu.gpr.rsp - 32#64) (8008608#64) :=
    { code := hE.lcode, s0 := by bv_omega, s8 := by bv_omega, m0 := .inl (by bv_omega), m8 := by decide,
      ml := by decide, f0 := by omega, f1 := .inl (by bv_omega), f2 := .inr (by bv_omega),
      st := off_ft hE.st 16 (d40 _) (by decide),
      lr := fun i hi => c.hws _ (off_ft hE.st 24 (d32 _) (by decide) i hi),
      mu := hE.mu, tid := hE.tid, fe := hE.fe }
  refine Pml.pml_ok c hfs (by rw [hsp₂, hdi₂]; exact hPE) hK₂ hA₂ hr₂ ?_ ?_ ?_ ?_ rfl hE.code (j₂ := 60)
    (lt_len (by decide)) ?_ ?_
  · rw [hdi₂]
    exact (congrArg (ofBytesLE 32) (vc_rd (by bv_omega) (by bv_omega) hs0 hs8 ho0)).trans hkd
  · exact (congrArg (ofBytesLE 32) (vc_rd (by bv_omega) (by bv_omega) hs0 hs8 ho0)).trans hfe
  · rw [hdi₂]
    exact (congrArg (ofBytesLE 32) (vc_rd (by bv_omega) (by bv_omega) hs0 hs8 ho0)).trans hlk
  · rw [hdi₂]
    exact (congrArg (ofBytesLE 32) (vc_rd (by bv_omega) (by bv_omega) hs0 hs8 ho0)).trans how
  · rw [hsp₂, vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  intro Vl Y₃ t₃ hK₃ hA₃ hDl hr₃ _ hbk₃
  rw [hsp₂, hdi₂] at hDl
  obtain ⟨hsp₃, hbx₃, hbp₃, h12₃, h13₃, h14₃, h15₃⟩ := hbk₃
  rw [hsp₂, c24] at hsp₃
  have hbx₃' : Y₃.cpu.gpr.rbx = X.cpu.gpr.rsi := by rw [hbx₃, hg₂, hg₁]; rfl
  have hbp₃' : Y₃.cpu.gpr.rbp = 6286176#64 := by rw [hbp₃, hg₂, hg₁]; rfl
  -- the object to the head of the list
  refine (c_60 prof).run c hE.code _ hK₃ hA₃ hr₃
    (vc_60 hE.uns (fun i hi => c.hws _ (hE.uns i hi)) (by rw [hbx₃']; exact off_ft hE.ob 40 rfl (by decide))
      hE.any (fun i hi => c.hws _ (hE.any i hi)) (by rw [hbx₃']; exact pre_any hDl hs0 hs8 ho0 hany)) ?_
  rintro j' g fl V₄ ⟨rfl, rfl, rfl⟩ Y₄ t₄ hK₄ hA₄ hr₄ hg₄ -
  rw [hbx₃'] at hA₄
  have hsp₄ : Y₄.cpu.gpr.rsp = X.cpu.gpr.rsp - 24#64 := by rw [hg₄]; exact hsp₃
  obtain ⟨p16, p8, pS, pk, pl⟩ := pre_u (u := rdq(Vl, 8008664#64)) hDl hs0 hs8 ho0
  -- the epilogue
  refine (c_88 prof).run c hE.code _ hK₄ hA₄ hr₄
    (vc_88 (by rw [hg₄]; exact hbp₃') (fun i hi => ?_) (fun i hi => ?_)) ?_
  · rw [hsp₄, c16]
    exact c.hws _ (off_ft hE.st 40 (d16 _) (by decide) i hi)
  · rw [hsp₄, c8]
    exact c.hws _ (off_ft hE.st 48 (d8 _) (by decide) i hi)
  rintro j' g fl V₅ ⟨rfl, rfl, rfl⟩ Y₅ t₅ hK₅ hA₅ hr₅ hg₅ -
  have hsp₅ : Y₅.cpu.gpr.rsp = X.cpu.gpr.rsp := by
    rw [hg₅]
    show Y₄.cpu.gpr.rsp + 8#64 + 8 + 8 = _
    rw [hsp₄]
    exact c0 _
  have hbx₅ : Y₅.cpu.gpr.rbx = X.cpu.gpr.rbx := by
    rw [hg₅]
    show rdq(_, Y₄.cpu.gpr.rsp + 8#64) = _
    rw [hsp₄, c16]
    exact p16
  have hbp₅ : Y₅.cpu.gpr.rbp = X.cpu.gpr.rbp := by
    rw [hg₅]
    show rdq(_, Y₄.cpu.gpr.rsp + 8#64 + 8) = _
    rw [hsp₄, c8]
    exact p8
  have sv₅ : Y₅.cpu.gpr.r12 = X.cpu.gpr.r12 ∧ Y₅.cpu.gpr.r13 = X.cpu.gpr.r13 ∧ Y₅.cpu.gpr.r14 = X.cpu.gpr.r14 ∧
      Y₅.cpu.gpr.r15 = X.cpu.gpr.r15 := by
    rw [hg₅, hg₄]
    show Y₃.cpu.gpr.r12 = _ ∧ Y₃.cpu.gpr.r13 = _ ∧ Y₃.cpu.gpr.r14 = _ ∧ Y₃.cpu.gpr.r15 = _
    rw [h12₃, h13₃, h14₃, h15₃, hg₂, hg₁]
    exact ⟨rfl, rfl, rfl, rfl⟩
  -- `pthread_mutex_unlock (&object_mutex)`, a tail call
  refine c.s_jmp_x hK₅ hA₅ hE.code (lt_len (by decide)) hr₅ (jmp_106 _) hE.ucode (tgt := 0)
    (Pmu.lt_len (by decide)) (by decide) ?_
  rintro Y₆ t₆ hK₆ hA₆ ⟨hr₆, hg₆⟩
  have hsp₆ : Y₆.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hg₆]; exact hsp₅
  have hdi₆ : Y₆.cpu.gpr.rdi = 8008608#64 := by rw [hg₆, hg₅]
  have hUE : Pmu.Env F Wl L X.cpu.gpr.rsp (8008608#64) :=
    { code := hE.ucode, s8 := hs8, m0 := .inl (by bv_omega), m8 := by decide, ml := by decide, lr := hE.lr,
      mu := hE.mu }
  refine Pmu.pmu_ok c (by rw [hsp₆, hdi₆]; exact hUE) hK₆ hA₆ (by rw [hr₆, addr_add_zero])
    (by rw [hdi₆]; exact pk.trans hkd) (by rw [hdi₆]; exact pl) hin₂ h₂ (by rw [hsp₆]; exact pS.trans hra) ?_
  intro Vf Z t' hKZ hAZ hDu hrZ _ hbkZ
  rw [hdi₆] at hDu
  refine k Vf Z t' hKZ hAZ (fin hDl hDu hs0 hs8 ho0) hrZ ?_
  obtain ⟨z1, z2, z3, z4, z5, z6, z7⟩ := hbkZ
  rw [hg₆] at z2 z3 z4 z5 z6 z7
  exact ⟨by rw [z1, hsp₆], z2.trans hbx₅, z3.trans hbp₅, z4.trans sv₅.1, z5.trans sv₅.2.1, z6.trans sv₅.2.2.1,
    z7.trans sv₅.2.2.2⟩

end FV7z.Rfi
