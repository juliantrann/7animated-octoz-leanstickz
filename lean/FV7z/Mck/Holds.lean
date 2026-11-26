import FV7z.Mck.Vc
import FV7z.Mun.Holds
/-!
# `munmap_chunk` gives an mmapped chunk back (PLAN.md §M, M1)

glibc 2.31's `munmap_chunk (p)` at `0x62e660` in `7zzs`: with `IS_MMAPPED` set in `p`'s size word and the block
(`p - prev_size`) and its length (`prev_size + chunksize`) page multiples, `chunk2mem (p)`'s offset in its page a
power of two or 0, it takes one from `mp_.n_mmaps` (`lock dec`), the length from `mp_.mmapped_mem` (`lock add`) and
tail-calls `__munmap (block, length)`. A failed check calls `malloc_printerr` or `__assert_fail` (neither returns):
here the checks are hypotheses (`MckPre`).

- `mckB`, `mckT`: the block and its length; `mckV`: the bytes after the two counters' updates.
- `mck_ok`: from the entry to `__munmap`'s `syscall` (`Mun.mun_pre`): `eax` 11, `rdi` the block, `rsi` the length,
  `rsp` as at the entry (the return address is `munmap_chunk`'s caller's), the registers a call keeps.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Mck

/-- `mp_.n_mmaps`. -/
abbrev nmA : Addr := 7940552#64
/-- `mp_.mmapped_mem`. -/
abbrev mmA : Addr := 7940568#64

/-- The page size, `GLRO (dl_pagesize)`. -/
def mps (V : Addr → Byte) : Addr := rdq(V, 7943128#64)
/-- The size word. -/
def msz (V : Addr → Byte) (p : Addr) : Addr := rdq(V, p + 8#64)
/-- `prev_size`. -/
def mpv (V : Addr → Byte) (p : Addr) : Addr := rdq(V, p)
/-- The block's length, `prev_size (p) + chunksize (p)`. -/
def mckT (V : Addr → Byte) (p : Addr) : Addr := mpv V p + (msz V p &&& 18446744073709551608#64)
/-- The block, `p - prev_size (p)`. -/
def mckB (V : Addr → Byte) (p : Addr) : Addr := p - mpv V p
/-- After `atomic_decrement (&mp_.n_mmaps)`. -/
def mV1 (V : Addr → Byte) : Addr → Byte := Vst V nmA (toBytesLE (ofBytesLE 32 ((byteAddrs nmA 4).map V) - 1#32) 4)
/-- After `atomic_add (&mp_.mmapped_mem, -total_size)`. -/
def mckV (V : Addr → Byte) (p : Addr) : Addr → Byte :=
  Vst (mV1 V) mmA (toBytesLE (ofBytesLE 64 ((byteAddrs mmA 8).map (mV1 V)) + (0 - mckT V p)) 8)

/-- What `munmap_chunk (p)` needs: its checks hold, the words read are in the footprint, the counters in the
run's. -/
structure MckPre (F : Footprint) (Wl : List Rgn) (V : Addr → Byte) (p : Addr) : Prop where
  mm : ((msz V p).setWidth 32 &&& 2#32 == 0) = false
  ck : (mckc p (mpv V p) (msz V p) (mps V) == 0) = true
  f1 : ∀ i < 8, Foot F.data (Addr.add 7943128#64 i)
  f2 : ∀ i < 8, Foot F.data (Addr.add (p + 8#64) i)
  f3 : ∀ i < 8, Foot F.data (Addr.add p i)
  w1 : ∀ i < 4, Foot Wl (nmA.add i)
  w2 : ∀ i < 8, Foot Wl (mmA.add i)

section
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- `munmap_chunk (p)` (`rdi = p`) when its checks hold (`MckPre`): the run reaches `__munmap`'s `syscall` with
`eax` 11 (`munmap`), `rdi` the block, `rsi` its length, `rsp` as at the entry, the registers a call keeps as at the
entry and the bytes `mckV`. -/
theorem mck_ok {fb : Addr} {X : State} {t : Nat} {V : Addr → Byte}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L mck_at mck)
    (hinm : CodeIn L Mun.mun_at Mun.mun) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = mck_at) (hP : MckPre F Wl V X.cpu.gpr.rdi)
    (k : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (mckV V X.cpu.gpr.rdi) →
      Y.cpu.rip = Mun.mun_at.add 9 → Y.cpu.gpr.rax = 11#64 → Y.cpu.gpr.rdi = mckB V X.cpu.gpr.rdi →
      Y.cpu.gpr.rsi = mckT V X.cpu.gpr.rdi → Y.cpu.gpr.rsp = X.cpu.gpr.rsp → Km X.cpu.gpr Y.cpu.gpr →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  obtain ⟨hmm, hck, f1, f2, f3, w1, w2⟩ := hP
  refine (c_0 prof fb).run c hfs hin _ hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 (ps := mps V) (sz := msz V X.cpu.gpr.rdi) (pv := mpv V X.cpu.gpr.rdi) rfl rfl rfl hmm hck f1 f2 f3) ?_
  rintro j' g₁ fl V' ⟨rfl, hVV, hsi, hr8, hsp, hkm⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  subst V'
  refine c.s_lock_dec_rip32 hK₁ hA₁ hin (lt_len (by decide)) hr₁ (dec_71 _) (by decide) (by decide) w1 ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  refine (c_78 prof fb).run c hfs hin _ hK₂ hA₂ hr₂ vc_78 ?_
  rintro j' g₃ fl V' ⟨rfl, hVV, rfl⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
  subst V'
  refine c.s_lock_add_rip64r hK₃ hA₃ hin (lt_len (by decide)) hr₃ (add_84 _) (by decide) (by decide) w2 ?_
  rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
  have hrv : rv Y₃ 64 0 = 0 - mckT V X.cpu.gpr.rdi := by
    show (Y₃.cpu.gpr.get (regOf 0)).setWidth 64 = _
    rw [hg₃, hg₂, hg₁, BitVec.setWidth_eq]
    show 0 - g₁.rsi = _
    rw [hsi] <;> rfl
  rw [hrv] at hA₄
  refine (c_92 prof fb).run c hfs hin _ hK₄ hA₄ hr₄ vc_92 ?_
  rintro j' g₅ fl V' ⟨rfl, hVV, rfl⟩ Y₅ t₅ hK₅ hA₅ hr₅ hg₅ -
  subst V'
  refine c.s_jmp_x hK₅ hA₅ hin (lt_len (by decide)) hr₅ (jmp_99 _) hinm (Mun.lt_len (j := 0) (by decide))
    (by decide) ?_
  rintro Y₆ t₆ hK₆ hA₆ ⟨hr₆, hg₆⟩
  refine Mun.mun_pre c hfs hinm hK₆ hA₆ (by rw [hr₆, addr_add_zero]) ?_
  intro Y t' hKY hAY hrY hgY
  have hY : Y.cpu.gpr = ({ ({ g₁ with rax := 0 - g₁.rsi } : Gprs) with rdi := g₁.r8, rsp := g₁.rsp + 8#64 } :
      Gprs).set 0 11 := by
    rw [hgY, hg₆, hg₅, hg₄, hg₃, hg₂, hg₁] <;> rfl
  refine k Y t' hKY hAY hrY (by rw [hY] <;> rfl) (by rw [hY]; exact hr8) (by rw [hY]; exact hsi) ?_ ?_
  · rw [hY]
    show g₁.rsp + 8#64 = _
    rw [hsp]; exact BitVec.sub_add_cancel _ _
  · rw [hY]; exact hkm

end

end FV7z.Mck
