import FV7z.Ndi.Mem
/-!
# `_dl_non_dynamic_init`: the conditions of the cut points between its calls of `getenv` (PLAN.md G3, startup)

Each `getenv` returned `rax = 0` (the environment has no `LD_*` name), so each test of `rax` goes the same way and the
function stores a constant into a variable of `_rtld_global_ro` and loads the next name's address into `rdi`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Sga (vo vr vs)
namespace FV7z.Ndi

variable {F : Footprint} {Wl : List Rgn}

/-- After `getenv ("LD_LIBRARY_PATH")` (offset 2018) returned 0: `_dl_verbose := 0` (`0x7a855c`), next name. -/
theorem vc_2023 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hw : ∀ x : Addr, 7827456 ≤ x.toNat → x.toNat < 8032256 → Foot Wl x) (h0 : g.rax = 0#64) :
    W_2023 F Wl (fun j' g' _ V' => j' = 2050 ∧ g' = { g with rdi := 7289144#64 } ∧
      V' = Vst V 8029532#64 (toBytesLE (0#32) 4)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  subst h0
  wpx [W_2023, W_2037, o4, o5, Op.test, Op.mov, Op.sta]
  exact ⟨fun _ => ⟨gf hw _ 4 (by decide), rfl⟩, fun h => absurd h (by decide)⟩

/-- The argument of `_dl_init_paths`: what `getenv` returned. -/
theorem vc_2055 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_2055 F Wl (fun j' g' _ V' => j' = 2058 ∧ g' = { g with rdi := g.rax } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_2055, o6, Op.mov]

/-- After `_dl_init_paths`: `_dl_init_all_dirs := _dl_all_dirs` (`0x7a8570` to `0x7a85b0`), next name. -/
theorem vc_2063 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hr : ∀ x : Addr, 7827456 ≤ x.toNat → x.toNat < 8032256 → Foot F.data x)
    (hw : ∀ x : Addr, 7827456 ≤ x.toNat → x.toNat < 8032256 → Foot Wl x) :
    W_2063 F Wl (fun j' g' _ V' => j' = 2084 ∧
      g' = { g with rax := rdq(V, 8029552#64), rdi := 7289160#64 } ∧
      V' = Vst V 8029616#64 (toBytesLE rdq(V, 8029552#64) 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_2063, o7, Op.lda, Op.mov, Op.sta]
  exact ⟨gf hr _ 8 (by decide), gf hw _ 8 (by decide)⟩

/-- After a `getenv` that returned 0: the variable at `0x7a8590` becomes 1, next name. -/
theorem vc_2089 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hw : ∀ x : Addr, 7827456 ≤ x.toNat → x.toNat < 8032256 → Foot Wl x) (h0 : g.rax = 0#64) :
    W_2089 F Wl (fun j' g' _ V' => j' = 2120 ∧ g' = { g with rdx := 1#64, rdi := 7289172#64 } ∧
      V' = Vst V 8029584#64 (toBytesLE (1#32) 4)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  subst h0
  wpx [W_2089, W_2107, o8, o9, Op.test, Op.mov, Op.sta]
  exact ⟨fun _ => ⟨gf hw _ 4 (by decide), rfl⟩, fun h => absurd h (by decide)⟩

/-- After a `getenv` that returned 0: the variable at `0x7a85a8` becomes 0, next name. -/
theorem vc_2125 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hw : ∀ x : Addr, 7827456 ≤ x.toNat → x.toNat < 8032256 → Foot Wl x) (h0 : g.rax = 0#64) :
    W_2125 F Wl (fun j' g' _ V' => j' = 2153 ∧ g' = { g with rdx := 0#64, rdi := 7289184#64 } ∧
      V' = Vst V 8029608#64 (toBytesLE (0#32) 4)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  subst h0
  wpx [W_2125, W_2140, o10, o11, Op.test, Op.mov, Op.sta, Op.xor]
  simp only [BitVec.xor_self]
  exact ⟨fun _ => ⟨gf hw _ 4 (by decide), rfl, trivial⟩, fun h => absurd h (by decide)⟩

/-- After a `getenv` that returned 0: the variable at `0x7a8560` becomes 1, next name. -/
theorem vc_2158 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hw : ∀ x : Addr, 7827456 ≤ x.toNat → x.toNat < 8032256 → Foot Wl x) (h0 : g.rax = 0#64) :
    W_2158 F Wl (fun j' g' _ V' => j' = 2189 ∧ g' = { g with rdx := 1#64, rdi := 7289200#64 } ∧
      V' = Vst V 8029536#64 (toBytesLE (1#32) 4)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  subst h0
  wpx [W_2158, W_2176, o8, o12, Op.test, Op.mov, Op.sta]
  exact ⟨fun _ => ⟨gf hw _ 4 (by decide), rfl⟩, fun h => absurd h (by decide)⟩

/-- The name for the last `getenv`. -/
theorem vc_2269 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_2269 F Wl (fun j' g' _ V' => j' = 2276 ∧ g' = { g with rdi := 7289218#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_2269, o17, Op.mov]

/-- After `strlen (_dl_platform)`: `_dl_platformlen := rax` (`0x7a8550`). -/
theorem vc_2568 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hw : ∀ x : Addr, 7827456 ≤ x.toNat → x.toNat < 8032256 → Foot Wl x) :
    W_2568 F Wl (fun j' g' _ V' => j' = 2575 ∧ g' = g ∧ V' = Vst V 8029520#64 (toBytesLE g.rax 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_2568, o20, Op.sta]
  exact gf hw _ 8 (by decide)

end FV7z.Ndi
