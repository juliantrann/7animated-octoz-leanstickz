import FV7z.Auxv.Holds
import FV7z.Sec.Holds
import FV7z.Tun.Holds
import FV7z.Lemmas.SpCall
/-!
# The functions `__libc_start_main` calls first, inside its run (PLAN.md G3, startup)

`_dl_aux_init`, `__libc_init_secure` and `__tunables_init` as `FnAt`s (`FV7z/Lemmas/SpCall.lean`): in a run that has
their code, from their entry to their `ret`, by their cut points' conditions, which are of any footprint. What the
caller has to show at the `call` is the function's context (`Ctx.Ok`), that the run may read and store what the
function does (`Env`), and its entry's invariant; what it gets at the `ret` is `Ret`: the registers a call keeps, what
the function has set, and the other bytes as before.
-/
namespace FV7z.Startup
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}

/-- `_dl_aux_init`. -/
theorem aux_fnAt (c : Seg prof F Wl L s₀ o) (hin : CodeIn L Auxv.aux_at Auxv.aux) :
    FnAt prof F Wl L s₀ o Auxv.aux_at 493 fun R g V =>
      ∃ K : Auxv.Ctx, (K.Ok ∧ Auxv.Env K F Wl) ∧ Auxv.P0 K (3 * K.N + 400) g V ∧
        ∀ g' V', Auxv.Ret K g' V' → R g' V' :=
  fnAt_cfg c hin (fun ℓ => Auxv.spAll prof ℓ) 493 (fun K ℓ n g V => Auxv.InvT K ℓ n g V) Auxv.Ret
    (fun K => K.Ok ∧ Auxv.Env K F Wl) (fun K => 3 * K.N + 400)
    (fun _ hK ℓ n g f V h => Auxv.vcAll hK.1 hK.2 ℓ n g f V h)

/-- `__tunables_init`. -/
theorem tin_fnAt (c : Seg prof F Wl L s₀ o) (hin : CodeIn L Tun.tin_at Tun.tin) :
    FnAt prof F Wl L s₀ o Tun.tin_at 344 fun R g V =>
      ∃ K : Tun.Ctx, (K.Ok ∧ Tun.Env K F Wl) ∧ Tun.P0 K (K.N * K.B + K.B + 1) g V ∧
        ∀ g' V', Tun.Ret K g' V' → R g' V' :=
  fnAt_cfg c hin (fun ℓ => Tun.spAll prof ℓ) 344 (fun K ℓ n g V => Tun.InvT K ℓ n g V) Tun.Ret
    (fun K => K.Ok ∧ Tun.Env K F Wl) (fun K => K.N * K.B + K.B + 1)
    (fun _ hK ℓ n g f V h => Tun.vcAll hK.1 hK.2 ℓ n g f V h)

/-! ## `__libc_init_secure` -/

/-- At the entry: the registers and bytes `K`, `__libc_enable_secure_decided` not 0. -/
def SecInv (K : Gprs × (Addr → Byte)) (ℓ : Nat) (_ : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  ℓ = 0 ∧ g = K.1 ∧ V = K.2 ∧ ofBytesLE 32 (List.map V (byteAddrs 0x7a85c4#64 4)) ≠ 0

/-- At the `ret`: only `rax` has changed. -/
def SecFin (K : Gprs × (Addr → Byte)) (g : Gprs) (V : Addr → Byte) : Prop :=
  V = K.2 ∧ ∃ a, g = K.1.set 0 a

theorem sec_vc (hE : ∀ i, i < 4 → Foot F.data (Addr.add 0x7a85c4#64 i)) (K : Gprs × (Addr → Byte)) (ℓ : Nat) :
    ∀ n g f V, SecInv K ℓ n g V → Sec.Wt ℓ F Wl
      (fun j' g' _ V' => (∃ n', n' < n ∧ SecInv K j' n' g' V') ∨ (j' = 14 ∧ SecFin K g' V')) g f V := by
  obtain ⟨g0, V0⟩ := K
  rintro n g f V ⟨rfl, rfl, rfl, hd⟩
  simp only [Sec.Wt, ↓reduceIte]
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [Sec.W_0, Sec.o0, Op.lda]
  exact ⟨hE, fun hc => absurd (by simpa using hc) hd, fun _ => Or.inr ⟨rfl, _, rfl⟩⟩

/-- `__libc_init_secure`, with `__libc_enable_secure_decided` not 0: it returns with all but `rax` as before. -/
theorem sec_fnAt (c : Seg prof F Wl L s₀ o) (hin : CodeIn L Sec.sec_at Sec.sec) :
    FnAt prof F Wl L s₀ o Sec.sec_at 14 fun R g V =>
      (∀ i, i < 4 → Foot F.data (Addr.add 0x7a85c4#64 i)) ∧
        ofBytesLE 32 (List.map V (byteAddrs 0x7a85c4#64 4)) ≠ 0 ∧ ∀ a, R (g.set 0 a) V :=
  (fnAt_cfg c hin (fun ℓ => Sec.spAll prof ℓ) 14 SecInv SecFin
    (fun _ => ∀ i, i < 4 → Foot F.data (Addr.add 0x7a85c4#64 i)) (fun _ => 0)
    (fun K hE ℓ => sec_vc hE K ℓ)).mono (by
      rintro R g V ⟨hE, hd, hR⟩
      exact ⟨(g, V), hE, ⟨rfl, rfl, rfl, hd⟩, by rintro g' V' ⟨rfl, a, rfl⟩; exact hR a⟩)

end FV7z.Startup
