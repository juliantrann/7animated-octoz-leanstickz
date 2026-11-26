import FV7z.Ifr.Cuts
import FV7z.Ifr.Frame
/-!
# `_int_free` puts a chunk in the tcache (PLAN.md G3, `free`)

glibc 2.31's `_int_free (av, p, have_lock)` at `0x62f990` in `7zzs`, `p` in `rsi`: the six pushes, the canary
(`fs:0x28`) at `rsp + 56`, then for a chunk whose size (`csz`, the size word at `p + 8` with its 3 low bits clear)
passes the checks (`p` not above `-size`, `p` 16-aligned, the size at least 32 and a multiple of 16), with the thread's
tcache (`tcp`, `fs:-0x28`) made, the bin `tc_idx` (`tix`, `(size - 17) >> 4`) below `mp_.tcache_bins` (`0x792af0`), the
chunk's `key` (`p + 24`) not the tcache, and the bin's count (`tcn`) below `mp_.tcache_count` (`0x792b00`):
`tcache_put`, the canary checked, the pops, the `ret` (341). Four pieces: from the entry (0) to the tcache (90), from 90
to the put (696), the put (696 to 307), from 307 to the `ret`.

- `tcp`, `csz`, `tix`, `tcn`, `ent`: the tcache, the chunk's size, its bin, the bin's count and head.
- `PutOk`: the checks pass, and the layout and footprint of the stack, the chunk, the tcache, `fs` and `mp_`.
- `ifr_put_ok`: with `PutOk`, at the return address with the return address popped, the six callee-saved registers
  as they were, and the bytes outside the frame those of the four stores (`Vput`): `e->key = tcache`,
  `e->next = tcache->entries[tc_idx]`, `tcache->entries[tc_idx] = e`, `++tcache->counts[tc_idx]`.

Open gaps (left out by `PutOk`, each a branch the proof does not take):
- the `key = tcache` double-free scan (`e->key == tcache`, the jump to 1784);
- the full bin (`counts[tc_idx] ≥ mp_.tcache_count`), the tcache not made, `tc_idx ≥ mp_.tcache_bins` (all to 163,
  the non-tcache path);
- the non-tcache path itself (fastbins, `_int_free`'s consolidation; 163 onwards);
- the size and pointer checks failing (`free(): invalid pointer` / `invalid size`, 736 and 752) and the canary
  failing (`__stack_chk_fail`, 2439).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Tun (rd_Vst)
namespace FV7z.Ifr

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_341 : pret <+: ifr.drop 341 := by decide +kernel
theorem ret_341 (feat : Features) : Dec feat ifr 341 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 341) (k := 0) (pret_0 feat) w_341 (Nat.zero_le _)

/-- The thread's tcache, `fs:-0x28`. -/
abbrev tcp (V : Addr → Byte) (fb : Addr) : Addr := rdq(V, fb + 18446744073709551576#64)
/-- The size of the chunk `p`: its size word with the 3 low bits clear. -/
abbrev csz (V : Addr → Byte) (p : Addr) : BitVec 64 := rdq(V, p + 8#64) &&& 18446744073709551608#64
/-- Its tcache bin, `(size - 17) >> 4`. -/
abbrev tix (V : Addr → Byte) (p : Addr) : Addr := (csz V p + 18446744073709551599#64) >>> 4
/-- The count of its bin. -/
abbrev tcn (V : Addr → Byte) (fb p : Addr) : BitVec 16 :=
  ofBytesLE 16 (List.map V (byteAddrs (tcp V fb + tix V p * 2#64) 2))
/-- The head of its bin. -/
abbrev ent (V : Addr → Byte) (fb p : Addr) : Addr := rdq(V, tcp V fb + tix V p * 8#64 + 128#64)

variable {F : Footprint} {Wl : List Rgn}

/-- From the entry to the tcache: the frame made, the canary stored, the size checks passed. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {cn sz : BitVec 64}
    (hcn : rdq(Tls.P6 V g, fb + 40#64) = cn) (hsz : rdq(Vc g cn V, g.rsi + 8#64) = sz)
    (hw : g.rsi.toNat ≤ (0 - (sz &&& 18446744073709551608#64)).toNat)
    (hal : (BitVec.setWidth 8 g.rsi &&& 15#8 == 0) = true) (hmn : 31 < (sz &&& 18446744073709551608#64).toNat)
    (ha8 : (BitVec.setWidth 8 sz &&& 8#8 == 0) = true)
    (w1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (w4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (w5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i))
    (w6 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8 - 8) i))
    (fc : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (wc : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 72#64 + 56#64) i))
    (fs : ∀ i < 8, Foot F.data (Addr.add (g.rsi + 8#64) i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 90 ∧ g'.rsp = g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 72#64 ∧
      g'.rbx = sz &&& 18446744073709551608#64 ∧ g'.r12 = g.rsi ∧ g'.rsi = g.rsi ∧ V' = Vc g cn V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Vc, Tls.P6] at hcn hsz hw hal w1 w2 w3 w4 w5 w6 wc fs ⊢
  have j1 : (decide (rsi.toNat < (0 - (sz &&& 18446744073709551608#64)).toNat) ||
      decide (rsi = 0 - (sz &&& 18446744073709551608#64))) = true := by
    rcases Nat.lt_or_eq_of_le hw with h | h
    · rw [Bool.or_eq_true]; exact .inl (decide_eq_true h)
    · rw [Bool.or_eq_true]; exact .inr (decide_eq_true (BitVec.eq_of_toNat_eq h))
  have d6 : (decide ((sz &&& 18446744073709551608#64).toNat < 31) ||
      decide (sz &&& 18446744073709551608#64 = 31#64)) = false :=
    Bool.or_eq_false_iff.2 ⟨decide_eq_false (by omega),
      decide_eq_false fun h => by rw [h] at hmn; exact absurd hmn (by decide)⟩
  have d6' : (decide ((sz &&& 18446744073709551608#64).toNat < (31#64 : BitVec 64).toNat) ||
      decide (sz &&& 18446744073709551608#64 = 31#64)) = false := d6
  wpx [W_0, W_59, W_72, W_82, o0, o1, o2, o3, Op.ldf, BitVec.and_self, hcn, hsz, j1, hal, d6, d6', ha8,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, eq_self_iff_true,
      implies_true]
  all_goals repeat' first | assumption | rfl | trivial | apply And.intro | intro _

/-- From 90 to the put: the tcache made, `tc_idx` below `mp_.tcache_bins`, the `key` not the tcache, the count below
`mp_.tcache_count`. -/
theorem vc_90 {fb C ix : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hix : (g.rbx + 18446744073709551599#64) >>> 4 = ix)
    (htc : rdq(V, fb + 18446744073709551576#64) = C) (hC : C ≠ 0#64)
    (hbin : ix.toNat < rdq(V, 7940592#64).toNat) (hkey : C ≠ rdq(V, g.r12 + 24#64))
    (hcnt : (BitVec.setWidth 64 (BitVec.setWidth 32 (ofBytesLE 16 (List.map V (byteAddrs (C + ix * 2#64) 2))))).toNat <
      rdq(V, 7940608#64).toNat)
    (t0 : ∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551576#64) i))
    (t1 : ∀ i < 8, Foot F.data (Addr.add 7940592#64 i))
    (t2 : ∀ i < 8, Foot F.data (Addr.add (g.r12 + 24#64) i))
    (t3 : ∀ i < 2, Foot F.data (Addr.add (C + ix * 2#64) i))
    (t4 : ∀ i < 8, Foot F.data (Addr.add 7940608#64 i)) :
    W_90 fb F Wl (fun j' g' _ V' => j' = 696 ∧ g'.rsp = g.rsp ∧ g'.rax = ix ∧ g'.rdx = C ∧ g'.r12 = g.r12 ∧
      g'.rsi = g.rsi + 16#64 ∧ g'.rdi = C + ix * 2#64 ∧
      g'.rcx = BitVec.setWidth 64 (BitVec.setWidth 32 (ofBytesLE 16 (List.map V (byteAddrs (C + ix * 2#64) 2)))) ∧
      V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hix hkey t2 ⊢
  have hz : (C == 0) = false := beq_eq_false_iff_ne.2 hC
  have b6 : (decide (rdq(V, 7940592#64).toNat < ix.toNat) || decide (rdq(V, 7940592#64) = ix)) = false :=
    Bool.or_eq_false_iff.2 ⟨decide_eq_false (by omega),
      decide_eq_false fun h => by rw [h] at hbin; exact Nat.lt_irrefl _ hbin⟩
  have hk : decide (C = rdq(V, r12 + 24#64)) = false := decide_eq_false hkey
  have hc' := decide_eq_true hcnt
  subst hix
  wpx [W_90, W_107, W_124, W_139, o4, o5, o6, o7, Op.ldf, Op.shr64, Op.cmpmra, Op.cmpma, BitVec.and_self, htc, hz,
      b6, hk, hc', Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
      eq_self_iff_true, implies_true]
  all_goals repeat' first | with_reducible assumption | with_reducible rfl | exact True.intro | apply And.intro
    | intro _

/-- The put, 696 to 307: the four stores. -/
theorem vc_696 {fb p C ix : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hr12 : g.r12 = p) (hdx : g.rdx = C)
    (hax : g.rax = ix) (hsi : g.rsi = p + 16#64) (hdi : g.rdi = C + ix * 2#64)
    (f1 : ∀ i < 8, Foot Wl (Addr.add (p + 24#64) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (C + ix * 8#64 + 128#64) i))
    (f3 : ∀ i < 8, Foot Wl (Addr.add (p + 16#64) i))
    (f4 : ∀ i < 8, Foot Wl (Addr.add (C + ix * 8#64 + 128#64) i))
    (f5 : ∀ i < 2, Foot Wl (Addr.add (C + ix * 2#64) i)) :
    W_696 fb F Wl (fun j' g' _ V' => j' = 307 ∧ g'.rsp = g.rsp ∧
      V' = Vput V p C ix rdq(Vst V (p + 24#64) (toBytesLE C 8), C + ix * 8#64 + 128#64)
        (BitVec.setWidth 16 (BitVec.setWidth 32 g.rcx + 1#32))) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hr12 hdx hax hsi hdi ⊢
  subst hr12 hdx hax hsi hdi
  wpx [W_696, o10, eq_self_iff_true]
  all_goals repeat' first | assumption | rfl | trivial | apply And.intro | intro _

/-- From 307 to the `ret`: the canary checked, the frame dropped, the pops. -/
theorem vc_307 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hcan : rdq(V, g.rsp + 56#64) = rdq(V, fb + 40#64))
    (c0 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 56#64) i)) (c1 : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (q0 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 72#64) i))
    (q1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 72#64 + 8) i))
    (q2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 72#64 + 8 + 8) i))
    (q3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 72#64 + 8 + 8 + 8) i))
    (q4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 72#64 + 8 + 8 + 8 + 8) i))
    (q5 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 72#64 + 8 + 8 + 8 + 8 + 8) i)) :
    W_307 fb F Wl (fun j' g' _ V' => j' = 341 ∧ g'.rsp = g.rsp + 72#64 + 8 + 8 + 8 + 8 + 8 + 8 ∧
      g'.rbx = rdq(V, g.rsp + 72#64) ∧ g'.rbp = rdq(V, g.rsp + 72#64 + 8) ∧
      g'.r12 = rdq(V, g.rsp + 72#64 + 8 + 8) ∧ g'.r13 = rdq(V, g.rsp + 72#64 + 8 + 8 + 8) ∧
      g'.r14 = rdq(V, g.rsp + 72#64 + 8 + 8 + 8 + 8) ∧ g'.r15 = rdq(V, g.rsp + 72#64 + 8 + 8 + 8 + 8 + 8) ∧
      V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hcan c0 q0 q1 q2 q3 q4 q5 ⊢
  have hx : (rdq(V, rsp + 56#64) ^^^ rdq(V, fb + 40#64) == 0) = true := by
    (rw [hcan, BitVec.xor_self]) <;> decide
  wpx [W_307, W_327, o8, o9, Op.xormf, hx, Bool.not_true, Bool.false_eq_true, false_implies, eq_self_iff_true,
      implies_true]
  all_goals repeat' first | with_reducible assumption | with_reducible rfl | exact True.intro | apply And.intro
    | intro _

/-- What `ifr_put_ok` asks, `S` the stack pointer at the entry, `p` the chunk (`rsi`): the size checks pass, the tcache
put is taken (the tcache made, `tc_idx` below `mp_.tcache_bins` and below 64, the `key` not the tcache, the count below
`mp_.tcache_count`), and the layout: the frame `[S - 64, S)` writable and readable with the return address, the
chunk's words `[p + 8, p + 32)` readable and `[p + 16, p + 32)` writable, the tcache `[C, C + 640)` readable and
writable, `fs:-0x28` and `fs:0x28` readable, `mp_`'s two words readable, all of them apart. -/
structure PutOk (F : Footprint) (Wl : List Rgn) (V : Addr → Byte) (fb S p : Addr) : Prop where
  s0 : 120 ≤ S.toNat
  s1 : S.toNat + 8 ≤ 2 ^ 64
  sw : ∀ a : Addr, S.toNat - 64 ≤ a.toNat → a.toNat < S.toNat → Foot Wl a
  sd : ∀ a : Addr, S.toNat - 64 ≤ a.toNat → a.toNat < S.toNat + 8 → Foot F.data a
  p0 : p.toNat + 32 ≤ 2 ^ 64
  ps : p.toNat + 32 ≤ S.toNat - 64 ∨ S.toNat + 8 ≤ p.toNat + 8
  pd : ∀ a : Addr, p.toNat + 8 ≤ a.toNat → a.toNat < p.toNat + 32 → Foot F.data a
  pw : ∀ a : Addr, p.toNat + 16 ≤ a.toNat → a.toNat < p.toNat + 32 → Foot Wl a
  hw : p.toNat ≤ (0 - csz V p).toNat
  hal : (BitVec.setWidth 8 p &&& 15#8 == 0) = true
  hmn : 31 < (csz V p).toNat
  ha8 : (BitVec.setWidth 8 (rdq(V, p + 8#64)) &&& 8#8 == 0) = true
  hC : tcp V fb ≠ 0#64
  c0 : (tcp V fb).toNat + 640 ≤ 2 ^ 64
  cs : (tcp V fb).toNat + 640 ≤ S.toNat - 64 ∨ S.toNat + 8 ≤ (tcp V fb).toNat
  cp : p.toNat + 32 ≤ (tcp V fb).toNat ∨ (tcp V fb).toNat + 640 ≤ p.toNat + 8
  cd : ∀ a : Addr, (tcp V fb).toNat ≤ a.toNat → a.toNat < (tcp V fb).toNat + 640 → Foot F.data a
  cw : ∀ a : Addr, (tcp V fb).toNat ≤ a.toNat → a.toNat < (tcp V fb).toNat + 640 → Foot Wl a
  k64 : (tix V p).toNat < 64
  hbin : (tix V p).toNat < rdq(V, 7940592#64).toNat
  hkey : tcp V fb ≠ rdq(V, p + 24#64)
  hcnt : (tcn V fb p).toNat < rdq(V, 7940608#64).toNat
  f0 : 40 ≤ fb.toNat
  f1 : fb.toNat + 48 ≤ 2 ^ 64
  fs : fb.toNat + 48 ≤ S.toNat - 64 ∨ S.toNat + 8 ≤ fb.toNat - 40
  fp : fb.toNat + 48 ≤ p.toNat + 8 ∨ p.toNat + 32 ≤ fb.toNat - 40
  fc : fb.toNat + 48 ≤ (tcp V fb).toNat ∨ (tcp V fb).toNat + 640 ≤ fb.toNat - 40
  ft : ∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551576#64) i)
  fcn : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)
  g0 : 7940616 ≤ S.toNat - 64
  gd1 : ∀ i < 8, Foot F.data (Addr.add 7940592#64 i)
  gd2 : ∀ i < 8, Foot F.data (Addr.add 7940608#64 i)

/-- A read of the frame back from the put's bytes. -/
theorem rd_put {V : Addr → Byte} {g : Gprs} {cn : BitVec 64} {p C ix E : Addr} {c : BitVec 16}
    (h : 120 ≤ g.rsp.toNat) (hs : g.rsp.toNat + 8 ≤ 2 ^ 64) (hp : p.toNat + 32 ≤ 2 ^ 64)
    (hc : C.toNat + 640 ≤ 2 ^ 64) (hk : ix.toNat < 64)
    (ps : p.toNat + 32 ≤ g.rsp.toNat - 64 ∨ g.rsp.toNat + 8 ≤ p.toNat + 8)
    (cs : C.toNat + 640 ≤ g.rsp.toNat - 64 ∨ g.rsp.toNat + 8 ≤ C.toNat) {x : Addr} {m : Nat} (hm : x.toNat = m)
    (h1 : g.rsp.toNat - 64 ≤ m) (h2 : m ≤ g.rsp.toNat) :
    rdq(Vput (Vc g cn V) p C ix E c, x) = rdq(Vc g cn V, x) :=
  congrArg (ofBytesLE 64) (Vput_rd _ p C ix E c hp hc hk (x := x) (n := 8) (by omega) (by omega) (by omega))

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t : Nat} {V : Addr → Byte}

/-- `_int_free (av, p, _)` from its entry, with `PutOk`: the chunk put in its tcache bin. At the return address,
the return address popped, `rbx`, `rbp`, `r12`–`r15` as they were, and outside the frame `[S - 64, S)` the bytes of
the four stores of `tcache_put` (`Vput`): `p + 24` the tcache, `p + 16` the bin's old head, the bin's head `p + 16`,
the bin's count plus one. The branches left out (open gaps): the `key = tcache` scan (1784), the full bin, the
tcache not made and `tc_idx` too big (163), the non-tcache path, the failed checks (736, 752, 2439). -/
theorem ifr_put_ok {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L ifr_at ifr) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ifr_at)
    (h : PutOk F Wl V fb X.cpu.gpr.rsp X.cpu.gpr.rsi)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat) (W : Addr → Byte), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W →
      (∀ a : Addr, a.toNat < X.cpu.gpr.rsp.toNat - 64 ∨ X.cpu.gpr.rsp.toNat ≤ a.toNat →
        W a = Vput V X.cpu.gpr.rsi (tcp V fb) (tix V X.cpu.gpr.rsi) (ent V fb X.cpu.gpr.rsi)
          (tcn V fb X.cpu.gpr.rsi + 1#16) a) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 →
      Z.cpu.gpr.rbx = X.cpu.gpr.rbx → Z.cpu.gpr.rbp = X.cpu.gpr.rbp → Z.cpu.gpr.r12 = X.cpu.gpr.r12 →
      Z.cpu.gpr.r13 = X.cpu.gpr.r13 → Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  obtain ⟨s0, s1, sw, sd, p0, ps, pd, pw, hw, hal, hmn, ha8, hC, c0, cs, cp, cd, cw, k64, hbin, hkey, hcnt,
    f0, f1, fs, fp, fc, ft, fcn, g0, gd1, gd2⟩ := h
  have hR := X.cpu.gpr.rsp.isLt
  have hF := fb.isLt
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := stk X.cpu.gpr.rsp s0
  obtain ⟨q56, q72, q80, q88, q96, q104, q112, q120⟩ := stq e7 s0
  have hf40 : (fb + 40#64).toNat = fb.toNat + 40 := tAdd fb 40 (by omega)
  have hfm : (fb + 18446744073709551576#64).toNat = fb.toNat - 40 := by
    rw [BitVec.toNat_add, show (18446744073709551576#64 : BitVec 64).toNat = 18446744073709551576 from rfl]
    omega
  have hp8 : (X.cpu.gpr.rsi + 8#64).toNat = X.cpu.gpr.rsi.toNat + 8 := tAdd _ 8 (by omega)
  have hp16 : (X.cpu.gpr.rsi + 16#64).toNat = X.cpu.gpr.rsi.toNat + 16 := tAdd _ 16 (by omega)
  have hp24 : (X.cpu.gpr.rsi + 24#64).toNat = X.cpu.gpr.rsi.toNat + 24 := tAdd _ 24 (by omega)
  have hC2 := ix2 c0 k64
  have hC8 := ix8 c0 k64
  have hg1 : (7940592#64 : BitVec 64).toNat = 7940592 := rfl
  have hg2 : (7940608#64 : BitVec 64).toNat = 7940608 := rfl
  -- 0 → 90
  have hcn : rdq(Tls.P6 V X.cpu.gpr, fb + 40#64) = rdq(V, fb + 40#64) :=
    congrArg (ofBytesLE 64) (P6_rd V X.cpu.gpr s0 (by omega) (by omega))
  have hsz : rdq(Vc X.cpu.gpr (rdq(V, fb + 40#64)) V, X.cpu.gpr.rsi + 8#64) = rdq(V, X.cpu.gpr.rsi + 8#64) :=
    congrArg (ofBytesLE 64) (Vc_rd _ _ V s0 (by omega) (by omega))
  refine (c_0 prof fb).run c hfs hin _ hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 hcn hsz hw hal hmn ha8 (footR sw e1 (by omega) (by omega) (by omega))
      (footR sw e2 (by omega) (by omega) (by omega)) (footR sw e3 (by omega) (by omega) (by omega))
      (footR sw e4 (by omega) (by omega) (by omega)) (footR sw e5 (by omega) (by omega) (by omega))
      (footR sw e6 (by omega) (by omega) (by omega)) fcn (footR sw q56 (by omega) (by omega) (by omega))
      (footR pd hp8 (by omega) (by omega) (by omega))) ?_
  rintro j' g₁ fl V₁ ⟨rfl, hsp1, hbx1, h121, hsi1, rfl⟩ Y t₁ hKY hAY hrY hgY -
  subst hgY
  -- 90 → 696
  have hCv : rdq(Vc X.cpu.gpr (rdq(V, fb + 40#64)) V, fb + 18446744073709551576#64) = tcp V fb :=
    congrArg (ofBytesLE 64) (Vc_rd _ _ V s0 (by omega) (by omega))
  have eB : rdq(Vc X.cpu.gpr (rdq(V, fb + 40#64)) V, 7940592#64) = rdq(V, 7940592#64) :=
    congrArg (ofBytesLE 64) (Vc_rd _ _ V s0 (by omega) (by omega))
  have eT : rdq(Vc X.cpu.gpr (rdq(V, fb + 40#64)) V, 7940608#64) = rdq(V, 7940608#64) :=
    congrArg (ofBytesLE 64) (Vc_rd _ _ V s0 (by omega) (by omega))
  have eK : rdq(Vc X.cpu.gpr (rdq(V, fb + 40#64)) V, X.cpu.gpr.rsi + 24#64) = rdq(V, X.cpu.gpr.rsi + 24#64) :=
    congrArg (ofBytesLE 64) (Vc_rd _ _ V s0 (by omega) (by omega))
  have eN : List.map (Vc X.cpu.gpr (rdq(V, fb + 40#64)) V)
      (byteAddrs (tcp V fb + tix V X.cpu.gpr.rsi * 2#64) 2) =
      List.map V (byteAddrs (tcp V fb + tix V X.cpu.gpr.rsi * 2#64) 2) :=
    Vc_rd _ _ V s0 (by omega) (by omega)
  refine (c_90 prof fb).run c hfs hin _ hKY hAY hrY
    (vc_90 (C := tcp V fb) (ix := tix V X.cpu.gpr.rsi) (by rw [hbx1]) hCv hC (by rw [eB]; exact hbin)
      (by rw [h121, eK]; exact hkey) (by rw [eN, eT, sw16]; exact hcnt) ft gd1
      (by rw [h121]; exact footR pd hp24 (by omega) (by omega) (by omega))
      (footR cd hC2 (by omega) (by omega) (by omega)) gd2) ?_
  rintro j' g₂ fl V₂ ⟨rfl, hsp2, hax2, hdx2, h122, hsi2, hdi2, hcx2, rfl⟩ Z t₂ hKZ hAZ hrZ hgZ -
  subst hgZ
  -- 696 → 307
  refine (c_696 prof fb).run c hfs hin _ hKZ hAZ hrZ
    (vc_696 (p := X.cpu.gpr.rsi) (h122.trans h121) hdx2 hax2 (by rw [hsi2, hsi1]) hdi2
      (footR pw hp24 (by omega) (by omega) (by omega)) (footR cd hC8 (by omega) (by omega) (by omega))
      (footR pw hp16 (by omega) (by omega) (by omega)) (footR cw hC8 (by omega) (by omega) (by omega))
      (footR cw hC2 (by omega) (by omega) (by omega))) ?_
  rintro j' g₃ fl V₃ ⟨rfl, hsp3, rfl⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
  subst hg₃
  -- 307 → 341
  have hsQ : Y₃.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 72#64 := by rw [hsp3, hsp2, hsp1]
  refine (c_307 prof fb).run c hfs hin _ hK₃ hA₃ hr₃
    (vc_307
      (by
        rw [hsQ, rd_put s0 s1 p0 c0 k64 ps cs q56 (by omega) (by omega),
          Vput_rd _ _ _ _ _ _ p0 c0 k64 (x := fb + 40#64) (n := 8) (by omega) (by omega) (by omega),
          Vc_rd _ _ V s0 (x := fb + 40#64) (n := 8) (by omega) (by omega), (pops X.cpu.gpr _ V s0).1])
      (by rw [hsQ]; exact footR sd q56 (by omega) (by omega) (by omega)) fcn
      (by rw [hsQ]; exact footR sd q72 (by omega) (by omega) (by omega))
      (by rw [hsQ]; exact footR sd q80 (by omega) (by omega) (by omega))
      (by rw [hsQ]; exact footR sd q88 (by omega) (by omega) (by omega))
      (by rw [hsQ]; exact footR sd q96 (by omega) (by omega) (by omega))
      (by rw [hsQ]; exact footR sd q104 (by omega) (by omega) (by omega))
      (by rw [hsQ]; exact footR sd q112 (by omega) (by omega) (by omega))) ?_
  rintro j' g₄ fl V₄ ⟨rfl, hsp4, hbx4, hbp4, h124, h134, h144, h154, rfl⟩ Y₄ t₄ hK₄ hA₄ hr₄ hg₄ -
  subst hg₄
  have hS : Y₄.cpu.gpr.rsp = X.cpu.gpr.rsp := by
    rw [hsp4, hsQ]; exact BitVec.eq_of_toNat_eq q120
  have r1 : Y₄.cpu.gpr.rbx = X.cpu.gpr.rbx := by
    rw [hbx4, hsQ, rd_put s0 s1 p0 c0 k64 ps cs q72 (by omega) (by omega), (pops X.cpu.gpr _ V s0).2.1]
  have r2 : Y₄.cpu.gpr.rbp = X.cpu.gpr.rbp := by
    rw [hbp4, hsQ, rd_put s0 s1 p0 c0 k64 ps cs q80 (by omega) (by omega), (pops X.cpu.gpr _ V s0).2.2.1]
  have r3 : Y₄.cpu.gpr.r12 = X.cpu.gpr.r12 := by
    rw [h124, hsQ, rd_put s0 s1 p0 c0 k64 ps cs q88 (by omega) (by omega), (pops X.cpu.gpr _ V s0).2.2.2.1]
  have r4 : Y₄.cpu.gpr.r13 = X.cpu.gpr.r13 := by
    rw [h134, hsQ, rd_put s0 s1 p0 c0 k64 ps cs q96 (by omega) (by omega), (pops X.cpu.gpr _ V s0).2.2.2.2.1]
  have r5 : Y₄.cpu.gpr.r14 = X.cpu.gpr.r14 := by
    rw [h144, hsQ, rd_put s0 s1 p0 c0 k64 ps cs q104 (by omega) (by omega),
      (pops X.cpu.gpr _ V s0).2.2.2.2.2.1]
  have r6 : Y₄.cpu.gpr.r15 = X.cpu.gpr.r15 := by
    rw [h154, hsQ, rd_put s0 s1 p0 c0 k64 ps cs q112 (by omega) (by omega),
      (pops X.cpu.gpr _ V s0).2.2.2.2.2.2]
  -- the `ret`
  refine c.s_ret hK₄ hA₄ hin (lt_len (by decide)) hr₄ (ret_341 _)
    (by rw [hS]; exact footR sd rfl (by omega) (by omega) (by omega)) hin₂ h₂
    (by
      rw [hS, rd_put s0 s1 p0 c0 k64 ps cs (x := X.cpu.gpr.rsp) rfl (by omega) (by omega),
        Vc_rd _ _ V s0 (x := X.cpu.gpr.rsp) (n := 8) (by omega) (by omega)]
      exact hra) ?_
  rintro Z₅ t₅ hK₅ hA₅ ⟨hr₅, hg₅⟩
  refine k Z₅ t₅ _ hK₅ hA₅ ?_ hr₅ ?_ (by rw [hg₅]; exact r1) (by rw [hg₅]; exact r2)
    (by rw [hg₅]; exact r3) (by rw [hg₅]; exact r4) (by rw [hg₅]; exact r5) (by rw [hg₅]; exact r6)
  · intro a ha
    have hE : rdq(Vst (Vc X.cpu.gpr (rdq(V, fb + 40#64)) V) (X.cpu.gpr.rsi + 24#64) (toBytesLE (tcp V fb) 8),
        tcp V fb + tix V X.cpu.gpr.rsi * 8#64 + 128#64) = ent V fb X.cpu.gpr.rsi := by
      rw [rd_Vst _ _ _ _ _ (by simp only [toBytesLE_length]; omega) (by omega)
          (by simp only [toBytesLE_length]; omega),
        Vc_rd _ _ V s0 (by omega) (by omega)]
    rw [hE, hcx2, eN, cnt_inc]
    exact Tls.Vst_congr _ _ _ _ _ (Tls.Vst_congr _ _ _ _ _ (Tls.Vst_congr _ _ _ _ _
      (Tls.Vst_congr _ _ _ _ _ (Vc_out _ _ _ s0 a ha))))
  · (rw [hg₅, hS]) <;> rfl

end FV7z.Ifr
