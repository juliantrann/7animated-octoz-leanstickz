import FV7z.Ctor.BlkRet
/-!
# A constructor that sets up two static objects (PLAN.md §M, constructors)

`csuTg 97`, at `0x41cc50` (offset 2832 of `sti`), fills two 16-byte objects at `0x79ed70` and `0x79ed60`: a word
copied from `0x792970` (resp. `0x792968`), the byte 0 at `+8`, the half-word 1 at `+9`, the dword `-1` at `+12`;
then returns. Straight-line code: `blk_runs`.

- `st97 V`: the bytes after; `st97_out`: the same as `V` apart from `[0x79ed60, 0x79ed80)`.
- `vc97`: the stretch's `wp`; `runs97`: `csuTg 97` is a function as `Csu.csu_ok` asks.
-/
namespace FV7z.Ctor
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- `csuTg 97`. -/
def c97 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0xc7, 0xc0, 0x70, 0x29, 0x79, 0x00, 0xb9, 0x01, 0x00, 0x00, 0x00,
  0x48, 0x8b, 0x10, 0x48, 0xc7, 0xc0, 0x70, 0xed, 0x79, 0x00, 0x48, 0x89, 0x10, 0xba, 0x01, 0x00,
  0x00, 0x00, 0x66, 0x89, 0x50, 0x09, 0xc6, 0x40, 0x08, 0x00, 0xc7, 0x40, 0x0c, 0xff, 0xff, 0xff,
  0xff, 0x48, 0xc7, 0xc0, 0x68, 0x29, 0x79, 0x00, 0x48, 0x8b, 0x10, 0x48, 0xc7, 0xc0, 0x60, 0xed,
  0x79, 0x00, 0x48, 0x89, 0x10, 0xc6, 0x40, 0x08, 0x00, 0xc7, 0x40, 0x0c, 0xff, 0xff, 0xff, 0xff,
  0x66, 0x89, 0x48, 0x09, 0xc3]

theorem c97_0 : ∀ feat, Dec feat c97 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem c97_4 : ∀ feat, Dec feat c97 4 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 7940464)] 7) := by dec_rfl
theorem c97_11 : ∀ feat, Dec feat c97 11 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem c97_16 : ∀ feat, Dec feat c97 16 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 0) none 1 0 64)] 3) := by
  dec_rfl
theorem c97_19 : ∀ feat, Dec feat c97 19 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 7990640)] 7) := by dec_rfl
theorem c97_26 : ∀ feat, Dec feat c97 26 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 0 64), gr 64 2] 3) := by
  dec_rfl
theorem c97_29 : ∀ feat, Dec feat c97 29 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem c97_34 : ∀ feat, Dec feat c97 34 (FV7z.mk .mov 16 [.mem (mg (some 0) none 1 9 16), gr 16 2] 4) := by
  dec_rfl
theorem c97_38 : ∀ feat, Dec feat c97 38 (FV7z.mk .mov 8 [.mem (mg (some 0) none 1 8 8), .imm 8 0] 4) := by
  dec_rfl
theorem c97_42 : ∀ feat, Dec feat c97 42
    (FV7z.mk .mov 32 [.mem (mg (some 0) none 1 12 32), .imm 32 4294967295] 7) := by dec_rfl
theorem c97_49 : ∀ feat, Dec feat c97 49 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 7940456)] 7) := by dec_rfl
theorem c97_56 : ∀ feat, Dec feat c97 56 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 0) none 1 0 64)] 3) := by
  dec_rfl
theorem c97_59 : ∀ feat, Dec feat c97 59 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 7990624)] 7) := by dec_rfl
theorem c97_66 : ∀ feat, Dec feat c97 66 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 0 64), gr 64 2] 3) := by
  dec_rfl
theorem c97_69 : ∀ feat, Dec feat c97 69 (FV7z.mk .mov 8 [.mem (mg (some 0) none 1 8 8), .imm 8 0] 4) := by
  dec_rfl
theorem c97_73 : ∀ feat, Dec feat c97 73
    (FV7z.mk .mov 32 [.mem (mg (some 0) none 1 12 32), .imm 32 4294967295] 7) := by dec_rfl
theorem c97_80 : ∀ feat, Dec feat c97 80 (FV7z.mk .mov 16 [.mem (mg (some 0) none 1 9 16), gr 16 1] 4) := by
  dec_rfl
theorem c97_84 : ∀ feat, Dec feat c97 84 (FV7z.mk .ret 64 [] 1) := by dec_rfl

/-- What the stretch up to the `ret` does. -/
def o97 : List Op := [
  Op.nop,
  Op.mov 64 0 (.i 7940464),
  Op.mov 32 1 (.i 1),
  Op.ld 64 2 (some 0) none 1 0,
  Op.mov 64 0 (.i 7990640),
  Op.st 64 (some 0) none 1 0 2,
  Op.mov 32 2 (.i 1),
  Op.st 16 (some 0) none 1 9 2,
  Op.sti 8 (some 0) none 1 8 0,
  Op.sti 32 (some 0) none 1 12 4294967295,
  Op.mov 64 0 (.i 7940456),
  Op.ld 64 2 (some 0) none 1 0,
  Op.mov 64 0 (.i 7990624),
  Op.st 64 (some 0) none 1 0 2,
  Op.sti 8 (some 0) none 1 8 0,
  Op.sti 32 (some 0) none 1 12 4294967295,
  Op.st 16 (some 0) none 1 9 1]

theorem b97 (prof : Profile) : BlkA prof c97 (sti_at.add 2832) 0 84 o97 :=
  .cons (c97_0 _) ((OpI.endbr).at _) (by decide) <|
  .cons (c97_4 _) ((OpI.mov (.i 7940464) (.inr rfl)).at _) (by decide) <|
  .cons (c97_11 _) ((OpI.mov (.i 1) (.inl rfl)).at _) (by decide) <|
  .cons (c97_16 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (c97_19 _) ((OpI.mov (.i 7990640) (.inr rfl)).at _) (by decide) <|
  .cons (c97_26 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (c97_29 _) ((OpI.mov (.i 1) (.inl rfl)).at _) (by decide) <|
  .cons (c97_34 _) ((OpI.st (.inr (.inl rfl))).at _) (by decide) <|
  .cons (c97_38 _) ((OpI.sti (.inl rfl)).at _) (by decide) <|
  .cons (c97_42 _) ((OpI.sti (.inr (.inr (.inl rfl)))).at _) (by decide) <|
  .cons (c97_49 _) ((OpI.mov (.i 7940456) (.inr rfl)).at _) (by decide) <|
  .cons (c97_56 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (c97_59 _) ((OpI.mov (.i 7990624) (.inr rfl)).at _) (by decide) <|
  .cons (c97_66 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (c97_69 _) ((OpI.sti (.inl rfl)).at _) (by decide) <|
  .cons (c97_73 _) ((OpI.sti (.inr (.inr (.inl rfl)))).at _) (by decide) <|
  .cons (c97_80 _) ((OpI.st (.inr (.inl rfl))).at _) (by decide) <|
  .nil 84

theorem v97 : c97 <+: sti.drop 2832 := by decide +kernel
theorem tg97 : csuTg 97 = sti_at.add 2832 := by decide +kernel

/-- The first object, then the second (which reads its word after the first is written). -/
def st97a (V : Addr → Byte) : Addr → Byte :=
  Vst (Vst (Vst (Vst V 7990640#64 (toBytesLE rdq(V, 7940464#64) 8)) 7990649#64 (toBytesLE (1#16) 2))
    7990648#64 (toBytesLE (0#8) 1)) 7990652#64 (toBytesLE (BitVec.ofNat 32 4294967295) 4)

/-- The bytes after `csuTg 97`. -/
def st97 (V : Addr → Byte) : Addr → Byte :=
  Vst (Vst (Vst (Vst (st97a V) 7990624#64 (toBytesLE rdq(st97a V, 7940456#64) 8)) 7990632#64 (toBytesLE (0#8) 1))
    7990636#64 (toBytesLE (BitVec.ofNat 32 4294967295) 4)) 7990633#64 (toBytesLE (1#16) 2)

theorem st97_out (V : Addr → Byte) (a : Addr) (h : a.toNat < 7990624 ∨ 7990656 ≤ a.toNat) : st97 V a = V a := by
  unfold st97 st97a
  rw [vo, vo, vo, vo, vo, vo, vo, vo] <;> omega

/-- The stretch of `csuTg 97` up to its `ret`: the registers a call keeps, the bytes `st97 V`. -/
theorem vc97 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hl1 : ∀ i < 8, Foot F.data (Addr.add 7940464#64 i))
    (hl2 : ∀ i < 8, Foot F.data (Addr.add 7940456#64 i)) (hw : ∀ i < 32, Foot Wl (Addr.add 7990624#64 i)) :
    wp F Wl o97 (fun g' _ V' => Kp g g' ∧ V' = st97 V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [o97, Kp, BitVec.reduceAdd]
  repeat' apply And.intro
  all_goals first
    | rfl
    | exact hl1
    | exact hl2
    | exact ft_in hw (by decide) (by decide) (by decide)

/-- `csuTg 97` is a function as `Csu.csu_ok` asks, for an invariant the step from `97` to `98` takes through
`st97`, with the words it reads in the data footprint and the 32 bytes it writes in `Wl`. -/
theorem runs97 {J : Nat → (Addr → Byte) → Prop} {sp : Addr} {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64}
    (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg) (hin : CodeIn L sti_at sti)
    (hl1 : ∀ i < 8, Foot F.data (Addr.add 7940464#64 i)) (hl2 : ∀ i < 8, Foot F.data (Addr.add 7940456#64 i))
    (hw : ∀ i < 32, Foot Wl (Addr.add 7990624#64 i)) (hsp : 7990656 + 64 ≤ sp.toNat)
    (hJ : ∀ V, J 97 V → J 98 (st97 V)) : Csu.Runs prof F Wl L s₀ o gev gP gE J sp a₀ a₁ a₂ 97 (csuTg 97) :=
  blk_runs c hC hin tg97 (BlkA.shift (b97 prof) rfl v97)
    (Dec.shift (j := 2832) (k := 84) (c97_84 _) v97 (by decide)) (sti_lt (by decide))
    (fun _ _ _ => vc97 hl1 hl2 hw) (fun V a ha => st97_out V a (by omega)) hJ

end FV7z.Ctor
