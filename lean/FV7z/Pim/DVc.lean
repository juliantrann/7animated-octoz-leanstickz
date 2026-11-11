import FV7z.Pim.C
import FV7z.Lpi.Holds
import FV7z.Pti.Holds
import FV7z.Lemmas.Signed
/-!
# `__pthread_initialize_minimal_internal`: the default attributes, the hooks and the return (PLAN.md G3, startup)

The last stretch of the function at `0x6000b0`, from offset 545: the lock of `__default_pthread_attr` taken (`lock
cmpxchg`) and released (`xchg`) with nobody waiting, the stack's size and the guard's in it, `_dl_init_static_tls` and
`_dl_wait_lookup_done` set, `__libc_pthread_init`, `__pthread_tunables_init`, the check of the stack guard, the two
registers back and the `ret`.

- `MemD1`, `MemD`: the bytes outside the frame to the call of `__libc_pthread_init`; `MemE`: the two stores after it.
- `MemD_rd`, `MemE_rd`: bytes those stores leave.
- `vc_553` … `vc_669`: the verification conditions (`pim_d`, the stretch, is in `Pim/D.lean`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Sga (vo vr vs)
open FV7z.Raf (off_ft)
namespace FV7z.Pim

variable {F : Footprint} {Wl : List Rgn}

/-- The bytes outside the frame at the `xchg`: the lock held, `__default_pthread_attr`'s `stacksize` (`sz`) and
`guardsize` (the page's size). -/
def MemD1 (G : Addr → Byte) (sz : BitVec 64) : Addr → Byte :=
  Vst (Vst (Vst G (8008032#64) (toBytesLE (1#32) 4)) (8027808#64) (toBytesLE sz 8))
    (8027792#64) (toBytesLE rdq(G, 7943128#64) 8)

/-- The bytes outside the frame at the call of `__libc_pthread_init`: the lock free, `_dl_init_static_tls` and
`_dl_wait_lookup_done` set. -/
def MemD (G : Addr → Byte) (sz : BitVec 64) : Addr → Byte :=
  Vst (Vst (Vst (MemD1 G sz) (8008032#64) (toBytesLE (0#32) 4)) (7943168#64) (toBytesLE (6266288#64) 8))
    (8029560#64) (toBytesLE (6266608#64) 8)

/-- After `__libc_pthread_init`: `__is_smp` 1 and the pointer it returned (`__libc_multiple_threads_ptr`). -/
def MemE (W : Addr → Byte) : Addr → Byte :=
  Vst (Vst W (8027748#64) (toBytesLE (1#32) 4)) (8027704#64) (toBytesLE (8029208#64) 8)

/-- Bytes the stores of `MemD` leave. -/
theorem MemD_rd {G : Addr → Byte} {sz : BitVec 64} {x : Addr} {n : Nat} (hx : x.toNat + n ≤ 2 ^ 64)
    (h : x.toNat + n ≤ 7943168 ∨ 8029568 ≤ x.toNat ∨ (8008036 ≤ x.toNat ∧ x.toNat + n ≤ 8027792)) :
    List.map (MemD G sz) (byteAddrs x n) = List.map G (byteAddrs x n) := by
  unfold MemD MemD1
  rw [vr (by ln) (by decide) hx (by bv_omega), vr (by ln) (by decide) hx (by bv_omega),
    vr (by ln) (by decide) hx (by bv_omega), vr (by ln) (by decide) hx (by bv_omega),
    vr (by ln) (by decide) hx (by bv_omega), vr (by ln) (by decide) hx (by bv_omega)]

/-- Bytes the stores of `MemE` and `__libc_pthread_init` leave. -/
theorem MemE_rd {W G : Addr → Byte} {sz : BitVec 64}
    (hW : ∀ a : Addr, ¬ (8011552 ≤ a.toNat ∧ a.toNat < 8011640) → ¬ (8029200 ≤ a.toNat ∧ a.toNat < 8029208) →
      W a = MemD G sz a) {x : Addr} {n : Nat} (hx : x.toNat + n ≤ 2 ^ 64)
    (h : x.toNat + n ≤ 7943168 ∨ 8029568 ≤ x.toNat) :
    List.map (MemE W) (byteAddrs x n) = List.map G (byteAddrs x n) := by
  unfold MemE
  rw [vr (by ln) (by decide) hx (by bv_omega), vr (by ln) (by decide) hx (by bv_omega),
    Raf.rd_out2 hW hx (by omega) (by omega)]
  exact MemD_rd hx (by omega)

/-- Bytes apart from three ranges where `V'` is not `V`. -/
theorem rd_out3 {V V' : Addr → Byte} {l1 h1 l2 h2 l3 h3 : Nat}
    (h : ∀ a : Addr, ¬ (l1 ≤ a.toNat ∧ a.toNat < h1) → ¬ (l2 ≤ a.toNat ∧ a.toNat < h2) →
      ¬ (l3 ≤ a.toNat ∧ a.toNat < h3) → V' a = V a)
    {x : Addr} {n : Nat} (hx : x.toNat + n ≤ 2 ^ 64) (d1 : x.toNat + n ≤ l1 ∨ h1 ≤ x.toNat)
    (d2 : x.toNat + n ≤ l2 ∨ h2 ≤ x.toNat) (d3 : x.toNat + n ≤ l3 ∨ h3 ≤ x.toNat) :
    List.map V' (byteAddrs x n) = List.map V (byteAddrs x n) := by
  apply List.map_congr_left
  intro y hy
  obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hy
  refine h _ ?_ ?_ ?_ <;> (rw [toNat_add_of_fits hj hx]; omega)

/-- The lock taken: the stack's size and the guard's, to the `xchg`. -/
theorem vc_553 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : f.zf = true)
    (h1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64) i)) (h2 : ∀ i < 8, Foot Wl (Addr.add 8027808#64 i))
    (h3 : ∀ i < 8, Foot F.data (Addr.add 7943128#64 i)) (h4 : ∀ i < 8, Foot Wl (Addr.add 8027792#64 i)) :
    W_553 fb F Wl (fun j' g' _ V' => j' = 587 ∧ g' = { g with rax := BitVec.setWidth 64 0#32 } ∧
      V' = Vst (Vst V (8027808#64) (toBytesLE rdq(V, g.rsp + 16#64) 8)) (8027792#64)
        (toBytesLE rdq(V, 7943128#64) 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  have e : rdq(Vst V (8027808#64) (toBytesLE rdq(V, rsp + 16#64) 8), 7943128#64) = rdq(V, 7943128#64) :=
    congrArg (ofBytesLE 64) (vr (by ln) (by decide) (by decide) (by decide))
  dsimp only at h1
  wpx [W_553, W_559, o19, Op.sta, Op.lda, BitVec.xor_self, hz, e]
  exact ⟨fun h => absurd h (by decide), fun _ => ⟨h1, h2, h3, h4⟩⟩

/-- Nobody waited for the lock: the two hooks, the arguments of `__libc_pthread_init`. -/
theorem vc_593 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hax : g.rax = BitVec.setWidth 64 1#32)
    (h1 : ∀ i < 8, Foot Wl (Addr.add 7943168#64 i)) (h2 : ∀ i < 8, Foot Wl (Addr.add 8029560#64 i)) :
    W_593 fb F Wl (fun j' g' _ V' => j' = 642 ∧
      g' = { g with rax := 6266608#64, rdx := BitVec.setWidth 64 0#32, rsi := 6264560#64, rdi := 8027680#64 } ∧
      V' = Vst (Vst V (7943168#64) (toBytesLE (6266288#64) 8)) (8029560#64) (toBytesLE (6266608#64) 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hax
  subst hax
  wpx [W_593, W_598, o20, o21, Op.sta, BitVec.xor_self, subF_g32]
  exact ⟨fun h => absurd h (by decide), fun _ => ⟨h1, h2⟩⟩

/-- `__is_smp` and the pointer `__libc_pthread_init` returned. -/
theorem vc_647 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h1 : ∀ i < 4, Foot Wl (Addr.add 8027748#64 i)) (h2 : ∀ i < 8, Foot Wl (Addr.add 8027704#64 i)) :
    W_647 fb F Wl (fun j' g' _ V' => j' = 664 ∧ g' = g ∧
      V' = Vst (Vst V (8027748#64) (toBytesLE (1#32) 4)) (8027704#64) (toBytesLE g.rax 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_647, o22, Op.stia, Op.sta]
  exact ⟨h1, h2⟩

/-- The check of the stack guard, the frame left, the two registers back. -/
theorem vc_669 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hl : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 184#64) i)) (hfl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hc : rdq(V, g.rsp + 184#64) = rdq(V, fb + 40#64))
    (h1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 200#64) i))
    (h2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 200#64 + 8) i)) :
    W_669 fb F Wl (fun j' g' _ V' => j' = 698 ∧
      g' = { g with rax := 0, rsp := g.rsp + 200#64 + 8 + 8, rbp := rdq(V, g.rsp + 200#64),
                    r12 := rdq(V, g.rsp + 200#64 + 8) } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hl hc h1 h2
  wpx [W_669, W_688, o23, o24, Op.xormf, hc, BitVec.xor_self]
  exact ⟨hl, hfl, fun h => absurd h (by decide), fun _ => ⟨h1, h2, rfl⟩⟩

end FV7z.Pim
