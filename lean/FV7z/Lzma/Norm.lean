import FV7z.Lemmas.Wp
/-!
# The range coder's normalization (PLAN.md G2, pilot `LzmaDec_DecodeReal_3`)

`cmp eax, 0x1000000; jae e; shl ebp, 8; mov bpl, [r15]; shl eax, 8; inc r15` and on at `e`, 63 times in
`LzmaDec_DecodeReal_3`: with the range (`eax`) at least `2^24` nothing changes; below, a byte is read at `r15`, the
range is shifted by 8 bits, `r15` goes on by one, and `rbp` (the code) changes. `Wnorm e` says so, without the
instructions; `Sp.norm` gives it for a `cmp` with its `jae` and the four instructions after.
-/
namespace FV7z.Lzma
open ZellicX86 Decode FV7z FV7z.Leaf

/-- The four instructions that read a byte. -/
def normRefill : List Op := [Op.shl 5 (.i 8), Op.ld8 5 (some 15) none 1 0, Op.shl 0 (.i 8), Op.inc 64 15]

/-- What a normalization needs for `Q` at its exit `e`. -/
def Wnorm (e : Nat) : Wpt := fun F _ Q g _ V =>
  (2 ^ 24 ≤ (g.rax.setWidth 32).toNat → ∀ fl, Q e g fl V) ∧
  ((g.rax.setWidth 32).toNat < 2 ^ 24 → Foot F.data g.r15 ∧
    ∀ fl rbp', Q e { g with rax := (g.rax.setWidth 32 <<< 8).setWidth 64, rbp := rbp', r15 := g.r15 + 1 } fl V)

variable {prof : Profile} {code : List Byte} {e' : Addr}

/-- A normalization: the `cmp` with its `jae` to `e`, else on at `r`, and the four instructions from `r` to `e`. -/
theorem Sp.norm {h r e : Nat} (her : e ≠ r)
    (h1 : Sp prof code e' h fun F Wl Q => wp F Wl [Op.cmp 32 0 (.i 16777216)] fun g f V =>
      (f.cond 3 = true → Q e g (rfz f) V) ∧ (f.cond 3 = false → Q r g (rfz f) V))
    (h2 : Sp prof code e' r fun F Wl Q => wp F Wl normRefill fun g _ V => ∀ fl, Q e g fl V) :
    Sp prof code e' h (Wnorm e) := by
  refine (Sp.then_at h1 h2).mono ?_
  intro F Wl Q g f V h
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Wnorm] at h
  obtain ⟨hn, hr⟩ := h
  wpx [normRefill, her, ↓reduceIte]
  refine ⟨fun hc => hn (by simpa using hc) _, fun hc _ => ?_⟩
  obtain ⟨hf, hq⟩ := hr (by simpa using hc)
  refine ⟨fun i hi => ?_, fun _ _ => hq _ _⟩
  obtain rfl : i = 0 := by omega
  rwa [addr_add_zero]

end FV7z.Lzma
