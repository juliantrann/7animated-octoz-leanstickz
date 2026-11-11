import FV7z.Start.InitStack
import FV7z.Lemmas.FnSteps
/-!
# The words of the initial stack of `7zzs` (PLAN.md G3, startup)

- `wordBytes_getD`: the `k`-th byte of the `j`-th word of `wordBytes ws`.
- `bytes_at`: `Bytes`, byte by byte.
- `words_rdq`: where the bytes of `wordBytes ws` lie, the quadword at the `j`-th word's address is `ws[j]`.
- `launch_words`: at the first instruction of `7zzs`, the quadword at `rsp + 8 * j` is the `j`-th of the words
  `execve` writes (`stackWords`: `argc`, the `argv` pointers, 0, the `envp` pointers, 0, the auxiliary vector).
-/
namespace FV7z.Start
open ZellicX86

theorem wordBytes_getD : ∀ (ws : List Nat) (j : Nat), j < ws.length → ∀ k : Nat, k < 8 →
    (wordBytes ws).getD (8 * j + k) 0 = (toBytesLE (BitVec.ofNat 64 (ws.getD j 0)) 8).getD k 0
  | [], j, hj, _, _ => by cases hj
  | w :: ws, 0, _, k, hk => by
    have hl : (toBytesLE (BitVec.ofNat 64 w) 8).length = 8 := toBytesLE_length _ _
    simp only [wordBytes, List.flatMap_cons, Nat.mul_zero, Nat.zero_add, List.getD_eq_getElem?_getD,
      List.getElem?_cons_zero, Option.getD_some]
    rw [List.getElem?_append_left (by omega)]
  | w :: ws, j + 1, hj, k, hk => by
    have hl : (toBytesLE (BitVec.ofNat 64 w) 8).length = 8 := toBytesLE_length _ _
    have ih := wordBytes_getD ws j (by simpa using hj) k hk
    simp only [wordBytes, List.flatMap_cons, List.getD_eq_getElem?_getD, List.getElem?_cons_succ] at ih ⊢
    rw [List.getElem?_append_right (by omega), hl]
    have e : 8 * (j + 1) + k - 8 = 8 * j + k := by omega
    rw [e]
    exact ih

theorem bytes_at {s : State} {a : Nat} {bs : List Byte} (h : Bytes s (BitVec.ofNat 64 a) bs) {i : Nat}
    (hi : i < bs.length) : s.proc.mm.mem.readByte (BitVec.ofNat 64 (a + i)) = bs.getD i 0 := by
  have h1 := congrArg (fun l => l.getD i 0) h
  simp only [readBytes, byteAddrs, List.map_map, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hi, Option.map_some, Option.getD_some, Function.comp_apply, add_ofNat] at h1
  rw [h1, List.getD_eq_getElem?_getD]

theorem words_rdq {V : Addr → Byte} {a : Nat} {ws : List Nat}
    (h : ∀ i < (wordBytes ws).length, V (BitVec.ofNat 64 (a + i)) = (wordBytes ws).getD i 0) {j : Nat}
    (hj : j < ws.length) :
    ofBytesLE 64 (List.map V (byteAddrs (BitVec.ofNat 64 (a + 8 * j)) 8)) = BitVec.ofNat 64 (ws.getD j 0) := by
  have hl : (toBytesLE (BitVec.ofNat 64 (ws.getD j 0)) 8).length = 8 := toBytesLE_length _ _
  have e : List.map V (byteAddrs (BitVec.ofNat 64 (a + 8 * j)) 8) = toBytesLE (BitVec.ofNat 64 (ws.getD j 0)) 8 := by
    apply List.ext_getElem (by simp only [byteAddrs, List.length_map, List.length_range, hl])
    intro i h1 h2
    have hi : i < 8 := by omega
    have hlen := wordBytes_length ws
    simp only [byteAddrs, List.getElem_map, List.getElem_range, add_ofNat]
    rw [Nat.add_assoc, h _ (by omega), wordBytes_getD ws j hj i hi, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h2, Option.getD_some]
  rw [e]
  exact ofBytesLE_toBytesLE (w := 64) (n := 8) rfl _

theorem launch_words {l : Launch} {n : Nat} (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l)
    (hroom : StackRoom l.args n) :
    ∃ hdr c, readElf l.files l.exe = some (hdr, zzsPhdrs) ∧ c.Valid l.prof.linux zzsPhdrs l.args l.kcfg ∧
      l.s₀.cpu.gpr.rsp = BitVec.ofNat 64 (stackLayout l.args l.prof.linux c).sp ∧
      ∀ j, j < (stackWords (auxv l.prof hdr (phdrAddr hdr zzsPhdrs) l.args c
          (stackLayout l.args l.prof.linux c)) l.args (stackLayout l.args l.prof.linux c)).length →
        ofBytesLE 64 (List.map l.s₀.proc.mm.mem.readByte
          (byteAddrs (BitVec.ofNat 64 ((stackLayout l.args l.prof.linux c).sp + 8 * j)) 8)) =
        BitVec.ofNat 64 ((stackWords (auxv l.prof hdr (phdrAddr hdr zzsPhdrs) l.args c
          (stackLayout l.args l.prof.linux c)) l.args (stackLayout l.args l.prof.linux c)).getD j 0) := by
  obtain ⟨hdr, c, hr, hv, e, hB, -, -⟩ := launch_stack_bytes h hroom
  exact ⟨hdr, c, hr, hv, e, fun j hj => words_rdq (fun i hi => bytes_at hB hi) hj⟩

end FV7z.Start
