import FV7z.Lzma.VcMLit
import FV7z.Lzma.VcPro
/-!
# The invariants of the 66 cut points, and their conditions together (PLAN.md G2.2)

`InvT K ℓ n`: what holds at the cut point `ℓ` with the measure `n`. `vcAll`: from it the condition `Wt ℓ` of the code
from `ℓ`, with at each exit the invariant there and a smaller measure, or `Ret` at the `ret`. This is what `Seg.cfg`
asks for.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Lzma
namespace FV7z.Lzma
variable {K : Ctx} {F : Footprint} {Wl : List Rgn}

/-- The invariant at each cut point. -/
def InvT (K : Ctx) (ℓ : Nat) : Nat → Gprs → (Addr → Byte) → Prop :=
  if ℓ = 0 then (Pre K) else
  if ℓ = 211 then (Pro211 K) else
  if ℓ = 259 then (Lit259 K) else
  if ℓ = 341 then (Lit341 K) else
  if ℓ = 424 then (fun n g V => LitI K n g V 2 4 8600 g.rdx g.rcx) else
  if ℓ = 505 then (fun n g V => LitI K n g V 3 8 8500 g.rcx g.rdx) else
  if ℓ = 586 then (fun n g V => LitI K n g V 4 16 8400 g.rdx g.rcx) else
  if ℓ = 667 then (fun n g V => LitI K n g V 5 32 8300 g.rcx g.rdx) else
  if ℓ = 748 then (fun n g V => LitI K n g V 6 64 8200 g.rdx g.rcx) else
  if ℓ = 829 then (fun n g V => LitI K n g V 7 128 8100 g.rcx g.rdx) else
  if ℓ = 905 then (fun n g V => LitI K n g V 8 256 8000 g.rdx g.rdx) else
  if ℓ = 1001 then (fun n g V => Sym K n g V 0 8 (g.r9.setWidth 32 = K.lpm)) else
  if ℓ = 1028 then (fun n g V => SymB K n g V 0 8 (g.r9.setWidth 32 = K.lpm)) else
  if ℓ = 1044 then (Mat1044 K) else
  if ℓ = 1088 then (Mat1088 K) else
  if ℓ = 1129 then (Len1129 K) else
  if ℓ = 1158 then (fun n g V => LenB K n g V 0 512 8100 5#64) else
  if ℓ = 1224 then (fun n g V => LenB K n g V 1 504 8000 4294967293#64) else
  if ℓ = 1280 then (Len1280 K) else
  if ℓ = 1306 then (Len1306 K) else
  if ℓ = 1376 then (Len1376 K) else
  if ℓ = 1422 then (Len1422 K) else
  if ℓ = 1479 then (Len1479 K) else
  if ℓ = 1505 then (Len1505 K) else
  if ℓ = 1581 then (Len1581 K) else
  if ℓ = 1695 then (Pos1695 K) else
  if ℓ = 1778 then (fun n g V => PosI K n g V 13 4 6300 g.rdx g.rcx) else
  if ℓ = 1859 then (fun n g V => PosI K n g V 14 8 6200 g.rcx g.rdx) else
  if ℓ = 1940 then (fun n g V => PosI K n g V 15 16 6100 g.rdx g.rcx) else
  if ℓ = 2021 then (fun n g V => PosI K n g V 16 32 6000 g.rcx g.rdx) else
  if ℓ = 2099 then (Pos2099 K) else
  if ℓ = 2208 then (Dir2208 K) else
  if ℓ = 2226 then (Dir2226 K) else
  if ℓ = 2295 then (fun n g V => AlnI K n g V 18 4900 g.rdx g.rcx (g.r9 = K.P + 4#64)) else
  if ℓ = 2379 then (fun n g V => AlnI K n g V 19 4800 g.rcx g.rdx (AlnA K g.r9 4 6)) else
  if ℓ = 2462 then (fun n g V => AlnI K n g V 20 4700 g.rdx g.rcx (AlnA K g.r9 8 12)) else
  if ℓ = 2546 then (fun n g V => AlnI K n g V 21 4600 g.rcx g.rcx (∃ a, g.r9 = BitVec.ofNat 64 a ∧ 8 ≤ a ∧ a < 16)) else
  if ℓ = 2594 then (Fin2594 K) else
  if ℓ = 2664 then (Cp2664 K) else
  if ℓ = 2736 then (Cp2736 K) else
  if ℓ = 2748 then (Cp2748 K) else
  if ℓ = 2784 then (Cp2784 K) else
  if ℓ = 2797 then (Cp2797 K) else
  if ℓ = 2825 then (fun n g V => Sym K n g V 14 24 (g.r12 = K.dic)) else
  if ℓ = 2852 then (fun n g V => SymB K n g V 14 24 (g.r12 = K.dic)) else
  if ℓ = 2960 then (MLit2960 K) else
  if ℓ = 3023 then (MLit3023 K) else
  if ℓ = 3118 then (fun n g V => MLitI K n g V 2 4 8600 (OfsR g)) else
  if ℓ = 3211 then (fun n g V => MLitI K n g V 3 8 8500 (OfsR g)) else
  if ℓ = 3304 then (fun n g V => MLitI K n g V 4 16 8400 (OfsR g)) else
  if ℓ = 3397 then (fun n g V => MLitI K n g V 5 32 8300 (OfsR g)) else
  if ℓ = 3490 then (fun n g V => MLitI K n g V 6 64 8200 (OfsR g)) else
  if ℓ = 3583 then (fun n g V => MLitI K n g V 7 128 8100 (OfsR g)) else
  if ℓ = 3670 then (fun n g V => MLitI K n g V 8 256 8000 True) else
  if ℓ = 3770 then (fun n g V => Sym K n g V 8 14 True) else
  if ℓ = 3797 then (fun n g V => SymB K n g V 8 14 True) else
  if ℓ = 3911 then (Rep3911 K) else
  if ℓ = 4002 then (fun n g V => RepB K n g V 2 8600 True) else
  if ℓ = 4055 then (fun n g V => RepB K n g V 3 8500 True) else
  if ℓ = 4182 then (fun n g V => RepB K n g V 3 8400 (RepV K g.r9 ∧ RepV K g.rbx)) else
  if ℓ = 4266 then (fun n g V => RepB K n g V 4 8300 (RepV K g.r9)) else
  if ℓ = 4384 then (Spec4384 K) else
  if ℓ = 4412 then (Spec4412 K) else
  if ℓ = 4505 then (Cp4505 K) else
  if ℓ = 4611 then (Out4611 K) else
  if ℓ = 4632 then (Out4632 K) else
  fun _ _ _ => False

/-- At an exit: the invariant there with a smaller measure, or what holds at `ret`. -/
def Nx (K : Ctx) (n : Nat) : Post := fun j' g' _ V' =>
  (∃ n', n' < n ∧ InvT K j' n' g' V') ∨ (j' = 4718 ∧ Ret K g' V')

theorem nx {n n' j : Nat} {g : Gprs} {fl : Rflags} {V : Addr → Byte} (hn : n' < n) (h : InvT K j n' g V) :
    Nx K n j g fl V := Or.inl ⟨n', hn, h⟩

/-- One more cut point of the table. -/
theorem vcT {ℓ k : Nat} {I I' : Nat → Gprs → (Addr → Byte) → Prop} {W W' : Wpt}
    (h : ∀ n g f V, I n g V → W F Wl (Nx K n) g f V) (h' : ∀ n g f V, I' n g V → W' F Wl (Nx K n) g f V) :
    ∀ n g f V, (if ℓ = k then I else I') n g V → (if ℓ = k then W else W') F Wl (Nx K n) g f V := by
  split
  · exact h
  · exact h'

/-- The conditions of all the cut points. -/
theorem vcAll (hK : K.Ok) (hE : Env K F Wl) (ℓ : Nat) :
    ∀ n g f V, InvT K ℓ n g V → Wt ℓ F Wl (Nx K n) g f V :=
  vcT (k := 0) (fun _ _ _ _ h => vc_0 hK hE h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 211) (fun _ _ _ _ h => vc_211 hK hE h (fun _ _ _ hn h' => nx hn h') (fun _ _ _ hn h' => nx hn h') (fun _ _ _ hn h' => nx hn h')) <|
  vcT (k := 259) (fun _ _ _ _ h => vc_259 hK hE h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 341) (fun _ _ _ _ h => vc_341 hK hE h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 424) (fun _ _ _ _ h => vc_lit9 hK hE (by decide) (by decide) (by decide) h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 505) (fun _ _ _ _ h => vc_lit10 hK hE (by decide) (by decide) (by decide) h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 586) (fun _ _ _ _ h => vc_lit9 hK hE (by decide) (by decide) (by decide) h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 667) (fun _ _ _ _ h => vc_lit10 hK hE (by decide) (by decide) (by decide) h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 748) (fun _ _ _ _ h => vc_lit9 hK hE (by decide) (by decide) (by decide) h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 829) (fun _ _ _ _ h => vc_829 hK hE h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 905) (fun _ _ _ _ h => vc_905 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 1001) (fun _ _ _ _ h => vc_sym (X := fun r9 _ => r9.setWidth 32 = K.lpm) hK hE (by decide) h (fun _ _ _ hn h' => nx hn h')) <|
  vcT (k := 1028) (fun _ _ _ _ h => vc_1028 hK hE h (fun _ _ _ hn h' => nx hn h') (fun _ _ _ hn h' => nx hn h')) <|
  vcT (k := 1044) (fun _ _ _ _ h => vc_1044 hK hE h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 1088) (fun _ _ _ _ h => vc_1088 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 1129) (fun _ _ _ _ h => vc_1129 hK hE h (fun _ _ _ hn h' => nx hn h')) <|
  vcT (k := 1158) (fun _ _ _ _ h => vc_1158 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 1224) (fun _ _ _ _ h => vc_1224 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 1280) (fun _ _ _ _ h => vc_1280 hK hE h (fun _ _ _ hn h' => nx hn h')) <|
  vcT (k := 1306) (fun _ _ _ _ h => vc_1306 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 1376) (fun _ _ _ _ h => vc_1376 hK hE h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 1422) (fun _ _ _ _ h => vc_1422 hK hE h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 1479) (fun _ _ _ _ h => vc_1479 hK hE h (fun _ _ _ hn h' => nx hn h')) <|
  vcT (k := 1505) (fun _ _ _ _ h => vc_1505 hK hE h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 1581) (fun _ _ _ _ h => vc_1581 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 1695) (fun _ _ _ _ h => vc_1695 hK hE h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 1778) (fun _ _ _ _ h => vc_pos9 hK hE (by decide) (by decide) (by decide) h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 1859) (fun _ _ _ _ h => vc_pos10 hK hE (by decide) (by decide) (by decide) h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 1940) (fun _ _ _ _ h => vc_pos9 hK hE (by decide) (by decide) (by decide) h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 2021) (fun _ _ _ _ h => vc_2021 hK hE h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 2099) (fun _ _ _ _ h => vc_2099 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 2208) (fun _ _ _ _ h => vc_2208 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 2226) (fun _ _ _ _ h => vc_2226 hK hE h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 2295) (fun _ _ _ _ h => vc_2295 hK hE h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 2379) (fun _ _ _ _ h => vc_2379 hK hE h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 2462) (fun _ _ _ _ h => vc_2462 hK hE h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 2546) (fun _ _ _ _ h => vc_2546 hK hE h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 2594) (fun _ _ _ _ h => vc_2594 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 2664) (fun _ _ _ _ h => vc_2664 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 2736) (fun _ _ _ _ h => vc_2736 hK hE h (fun _ _ _ hn h' => nx hn h')) <|
  vcT (k := 2748) (fun _ _ _ _ h => vc_2748 hK hE h (fun _ _ _ hn h' => nx hn h') (fun _ _ _ hn h' => nx hn h')) <|
  vcT (k := 2784) (fun _ _ _ _ h => vc_2784 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 2797) (fun _ _ _ _ h => vc_2797 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 2825) (fun _ _ _ _ h => vc_sym (X := fun _ r12 => r12 = K.dic) hK hE (by decide) h (fun _ _ _ hn h' => nx hn h')) <|
  vcT (k := 2852) (fun _ _ _ _ h => vc_2852 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ hn h' => nx hn h')) <|
  vcT (k := 2960) (fun _ _ _ _ h => vc_2960 hK hE h (fun _ _ _ hn h' => nx hn h')) <|
  vcT (k := 3023) (fun _ _ _ _ h => vc_3023 hK hE h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 3118) (fun _ _ _ _ h => vc_mlit53 hK hE (by decide) (by decide) (by decide) h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 3211) (fun _ _ _ _ h => vc_mlit53 hK hE (by decide) (by decide) (by decide) h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 3304) (fun _ _ _ _ h => vc_mlit53 hK hE (by decide) (by decide) (by decide) h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 3397) (fun _ _ _ _ h => vc_mlit53 hK hE (by decide) (by decide) (by decide) h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 3490) (fun _ _ _ _ h => vc_mlit53 hK hE (by decide) (by decide) (by decide) h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 3583) (fun _ _ _ _ h => vc_3583 hK hE h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 3670) (fun _ _ _ _ h => vc_3670 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 3770) (fun _ _ _ _ h => vc_sym (X := fun _ _ => True) hK hE (by decide) h (fun _ _ _ hn h' => nx hn h')) <|
  vcT (k := 3797) (fun _ _ _ _ h => vc_3797 hK hE h (fun _ _ _ hn h' => nx hn h') (fun _ _ _ hn h' => nx hn h')) <|
  vcT (k := 3911) (fun _ _ _ _ h => vc_3911 hK hE h (fun _ _ _ hn h' => nx hn h')) <|
  vcT (k := 4002) (fun _ _ _ _ h => vc_4002 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 4055) (fun _ _ _ _ h => vc_4055 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 4182) (fun _ _ _ _ h => vc_4182 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 4266) (fun _ _ _ _ h => vc_4266 hK hE h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 4384) (fun _ _ _ _ h => vc_4384 hK hE h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 4412) (fun _ _ _ _ h => vc_4412 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 4505) (fun _ _ _ _ h => vc_4505 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 4611) (fun _ _ _ _ h => vc_4611 hK hE h (fun _ _ _ hn h' => nx hn h')) <|
  vcT (k := 4632) (fun _ _ _ _ h => vc_4632 hK hE h (fun _ _ _ h' => Or.inr ⟨rfl, h'⟩)) <|
  fun _ _ _ _ h => h.elim

end FV7z.Lzma
