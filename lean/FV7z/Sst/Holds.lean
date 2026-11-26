import FV7z.Sst.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.BlkOps7
/-!
# `CFileInfoBase::SetFrom_stat` (PLAN.md §M, M1)

7-Zip 26.06's `NWindows::NFile::NFind::CFileInfoBase::SetFrom_stat (const struct stat &st)` at `0x4559d0` in
`7zzs` (`CPP/Windows/FileFind.cpp`; `objdump -d`), for the object at `p` = `rdi` and the `stat` at `s` = `rsi`:
`Size` (`p`) 0 for a directory (`st_mode & S_IFMT` = `S_IFDIR`), else `st_size` (`s + 48`); the three times'
16 bytes (`s + 104`, `s + 88`, `s + 72`) to `p + 8`, `p + 40`, `p + 24` by vector moves (the model does not track
what they store); `st_dev` (`s`) to `p + 56`, `st_mode` to `p + 72`, `st_ino` (`s + 8`) to `p + 64`, `st_nlink`
(`s + 16`) to `p + 80`, `st_uid` (`s + 28`) to `p + 88`, `st_gid` (`s + 32`) to `p + 92`, `st_rdev` (`s + 40`) to
`p + 96`. A leaf; one `ret` (105). Cut points: the entry and where the two ways for `Size` meet (29).

- `M`: the bytes after the stores, each load from the bytes before it; `sz`: `Size`; `Rs`, `Ws`: the bytes read and
  stored; `vc_0`, `vc_29`: the cut points' conditions; `sst_ok`: from the entry to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Sst

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_105 : pret <+: sst.drop 105 := by decide +kernel
theorem ret_105 (feat : Features) : Dec feat sst 105 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 105) (k := 0) (pret_0 feat) w_105 (Nat.zero_le _)

/-- `Size` from the `stat` at `s`: 0 for a directory, else `st_size`. -/
def sz (V : Addr → Byte) (s : Addr) : BitVec 64 :=
  if rdd(V, s + 24#64) &&& 61440#32 = 16384#32 then 0 else rdq(V, s + 48#64)

/-- The bytes after the stores into the object at `p` from the `stat` at `s`, in their order: `Size` `z`, the mode
`m`, the vector moves' bytes `b1`, `b2`, `b3`; each load from the bytes the stores before it left. -/
def M (V : Addr → Byte) (s p z : BitVec 64) (m : BitVec 32) (b1 b2 b3 : List Byte) : Addr → Byte :=
  let V1 := Vst V p (toBytesLE z 8)
  let V2 := Vst V1 (p + 8#64) b1
  let V3 := Vst V2 (p + 56#64) (toBytesLE rdq(V1, s) 8)
  let V4 := Vst V3 (p + 72#64) (toBytesLE m 4)
  let V5 := Vst V4 (p + 64#64) (toBytesLE rdq(V3, s + 8#64) 8)
  let V6 := Vst V5 (p + 80#64) (toBytesLE rdq(V4, s + 16#64) 8)
  let V7 := Vst V6 (p + 40#64) b2
  let V8 := Vst V7 (p + 88#64) (toBytesLE rdd(V6, s + 28#64) 4)
  let V9 := Vst V8 (p + 24#64) b3
  let V10 := Vst V9 (p + 92#64) (toBytesLE rdd(V8, s + 32#64) 4)
  Vst V10 (p + 96#64) (toBytesLE rdq(V10, s + 40#64) 8)

/-- The `stat`'s bytes the code reads, in `F.data`. -/
def Rs (F : Footprint) (s : Addr) : Prop :=
  (∀ i < 16, Foot F.data (Addr.add (s + 104#64) i)) ∧ (∀ i < 16, Foot F.data (Addr.add (s + 88#64) i)) ∧
  (∀ i < 8, Foot F.data (Addr.add s i)) ∧ (∀ i < 16, Foot F.data (Addr.add (s + 72#64) i)) ∧
  (∀ i < 8, Foot F.data (Addr.add (s + 8#64) i)) ∧ (∀ i < 8, Foot F.data (Addr.add (s + 16#64) i)) ∧
  (∀ i < 4, Foot F.data (Addr.add (s + 28#64) i)) ∧ (∀ i < 4, Foot F.data (Addr.add (s + 32#64) i)) ∧
  (∀ i < 8, Foot F.data (Addr.add (s + 40#64) i)) ∧ (∀ i < 4, Foot F.data (Addr.add (s + 24#64) i)) ∧
  (∀ i < 8, Foot F.data (Addr.add (s + 48#64) i))

/-- The object's bytes the code stores into, in `Wl`. -/
def Ws (Wl : List Rgn) (p : Addr) : Prop :=
  (∀ i < 8, Foot Wl (Addr.add p i)) ∧ (∀ i < 16, Foot Wl (Addr.add (p + 8#64) i)) ∧
  (∀ i < 8, Foot Wl (Addr.add (p + 56#64) i)) ∧ (∀ i < 4, Foot Wl (Addr.add (p + 72#64) i)) ∧
  (∀ i < 8, Foot Wl (Addr.add (p + 64#64) i)) ∧ (∀ i < 8, Foot Wl (Addr.add (p + 80#64) i)) ∧
  (∀ i < 16, Foot Wl (Addr.add (p + 40#64) i)) ∧ (∀ i < 4, Foot Wl (Addr.add (p + 88#64) i)) ∧
  (∀ i < 16, Foot Wl (Addr.add (p + 24#64) i)) ∧ (∀ i < 4, Foot Wl (Addr.add (p + 92#64) i)) ∧
  (∀ i < 8, Foot Wl (Addr.add (p + 96#64) i))

/-- The registers where the two ways meet: the mode in `rax`, its type bits in `rcx`, `Size` in `rdx`. -/
abbrev G29 (g : Gprs) (V : Addr → Byte) : Gprs :=
  { g with rax := BitVec.setWidth 64 rdd(V, g.rsi + 24#64),
    rcx := BitVec.setWidth 64 (rdd(V, g.rsi + 24#64) &&& 61440#32), rdx := sz V g.rsi }

/-- At the meeting point. -/
def P29 (g₀ : Gprs) (V₀ : Addr → Byte) : Post := fun j g _ V => j = 29 ∧ g = G29 g₀ V₀ ∧ V = V₀

/-- At the `ret`: `rax`, `rdx` changed, the bytes `M` for some vector bytes. -/
def P105 (g₀ : Gprs) (V₀ : Addr → Byte) : Post := fun j g _ V => j = 105 ∧
  (∃ a d, g = { g₀ with rax := a, rdx := d }) ∧ ∃ b1 b2 b3 : List Byte, b1.length = 16 ∧ b2.length = 16 ∧
    b3.length = 16 ∧ V = M V₀ g₀.rsi g₀.rdi g₀.rdx (g₀.rax.setWidth 32) b1 b2 b3

theorem x29 {g₀ : Gprs} {V₀ : Addr → Byte} {g : Gprs} {fl : Rflags} (hg : g = G29 g₀ V₀) : P29 g₀ V₀ 29 g fl V₀ :=
  ⟨rfl, hg, rfl⟩

theorem x105 {g₀ : Gprs} {V₀ : Addr → Byte} {b1 b2 b3 : List Byte} (h1 : b1.length = 16) (h2 : b2.length = 16)
    (h3 : b3.length = 16) {a d : BitVec 64} {g : Gprs} {fl : Rflags} {V : Addr → Byte}
    (hg : g = { g₀ with rax := a, rdx := d }) (hV : V = M V₀ g₀.rsi g₀.rdi g₀.rdx (g₀.rax.setWidth 32) b1 b2 b3) :
    P105 g₀ V₀ 105 g fl V :=
  ⟨rfl, ⟨a, d, hg⟩, b1, b2, b3, h1, h2, h3, hV⟩

variable {F : Footprint} {Wl : List Rgn}

/-- The entry: the mode, its type bits, `Size`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hr : Rs F g.rsi) : W_0 F Wl (P29 g V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨-, -, -, -, -, -, -, -, -, r24, r48⟩ := hr
  dsimp only at r24 r48 ⊢
  wpx [W_0, W_25, o0, o1]
  refine ⟨r24, fun _ _ => ⟨fun hc => ?_, fun hc => ⟨r48, ?_⟩⟩⟩
  · exact x29 (by simp only [G29, sz, if_pos (of_decide_eq_true hc), lf_xz])
  · exact x29 (by simp only [G29, sz, if_neg (of_decide_eq_false hc)])

/-- From the meeting point to the `ret`: the stores. -/
theorem vc_29 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hr : Rs F g.rsi) (hw : Ws Wl g.rdi) :
    W_29 F Wl (P105 g V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨r104, r88, r0, r72, r8, r16, r28, r32, r40, -, -⟩ := hr
  obtain ⟨w0, w8, w56, w72, w64, w80, w40, w88, w24, w92, w96⟩ := hw
  dsimp only at r104 r88 r0 r72 r8 r16 r28 r32 r40 w0 w8 w56 w72 w64 w80 w40 w88 w24 w92 w96 ⊢
  wpx [W_29, o2, Op.vl, Op.vs]
  exact ⟨r104, r88, w0, r0, r72, w8, fun b1 h1 => ⟨w56, r8, w72, r16, w64, w80, r28, w40, fun b2 h2 =>
    ⟨w88, r32, w24, fun b3 h3 => ⟨w92, r40, w96, x105 h1 h2 h3 rfl rfl⟩⟩⟩⟩

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- The bytes after the call from the registers `g` at the entry. -/
abbrev Ms (V : Addr → Byte) (g : Gprs) (b1 b2 b3 : List Byte) : Addr → Byte :=
  M V g.rsi g.rdi (sz V g.rsi) rdd(V, g.rsi + 24#64) b1 b2 b3

/-- `CFileInfoBase::SetFrom_stat (st)` from its entry to the return address: for some 16 bytes `b1`, `b2`, `b3`
(the times), the bytes `Ms`; `rax`, `rcx`, `rdx` changed, the other registers as at the entry but `rsp`. -/
theorem sst_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L sst_at sst) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = sst_at) (hr : Rs F X.cpu.gpr.rsi) (hw : Ws Wl X.cpu.gpr.rdi)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ∀ b1 b2 b3 : List Byte, b1.length = 16 → b2.length = 16 → b3.length = 16 →
      rdq(Ms V X.cpu.gpr b1 b2 b3, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat) (b1 b2 b3 : List Byte), b1.length = 16 → b2.length = 16 → b3.length = 16 →
      KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Ms V X.cpu.gpr b1 b2 b3) → Z.cpu.rip = e₂.add j₂ →
      (∃ a c d, Z.cpu.gpr = { X.cpu.gpr with rax := a, rcx := c, rdx := d }.set 4 (X.cpu.gpr.rsp + 8)) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (P29 X.cpu.gpr V) hK hA (by rw [addr_add_zero]; exact hrip) (vc_0 hr) ?_
  rintro j g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  refine (c_29 prof).run c hin (P105 Y.cpu.gpr V) hKY hAY hrY
    (vc_29 (by rw [hgY]; exact hr) (by rw [hgY]; exact hw)) ?_
  rintro j g fl V₂ ⟨rfl, ⟨a, d, rfl⟩, b1, b2, b3, h1, h2, h3, rfl⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
  have hM : M V Y.cpu.gpr.rsi Y.cpu.gpr.rdi Y.cpu.gpr.rdx (Y.cpu.gpr.rax.setWidth 32) b1 b2 b3 =
      Ms V X.cpu.gpr b1 b2 b3 := by
    rw [hgY]
    exact congrArg (fun m => M V X.cpu.gpr.rsi X.cpu.gpr.rdi (sz V X.cpu.gpr.rsi) m b1 b2 b3) (sw_64_32 _)
  rw [hM] at hA₂
  have hsp : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hg₂, hgY]
  refine c.s_ret hK₂ hA₂ hin (lt_len (by decide)) hr₂ (ret_105 _) (by rw [hsp]; exact hl) hin₂ h₂
    (by rw [hsp]; exact hra b1 b2 b3 h1 h2 h3) ?_
  rintro Z t₃ hKZ hAZ ⟨hrZ, hgZ⟩
  exact k Z t₃ b1 b2 b3 h1 h2 h3 hKZ hAZ hrZ ⟨a, (G29 X.cpu.gpr V).rcx, d, by rw [hgZ, hsp, hg₂, hgY]⟩

end FV7z.Sst
