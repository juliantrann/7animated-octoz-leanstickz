import FV7z.Start.TextP
import FV7z.Start.WitnessOracle
import FV7z.Start.WitnessExec
/-!
# The theorem against vacuity (PLAN.md §M)

Every hypothesis of `launch_main_plt` holds of one launch, oracle and code list together: the processor `prof0`
(`WitnessProf`), the environment `o0` (`WitnessOracle`), the start of `7zzs` by `execve` with `files0`, `args0`,
`k0`, `c0` (`WitnessExec`) and the code of the text segment with the PLT's (`text_code_plt`). So the theorem that
`7zzs` runs from its first instruction to `main` is not vacuous: `launch_main_witness` gives such a launch, and the run
from its start for it.
-/
namespace FV7z.Wit
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Glibc FV7z.AuxInit FV7z.Start

theorem launch_main_witness (gev : List Event) (t : Nat) :
    ∃ (l : Launch) (o : Oracle) (L : List (Addr × List Byte)),
      Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l ∧ LimitsUnlimited l.s₀ ∧ Undisturbed o ∧
      ∃ c, c.Valid l.prof.linux zzsPhdrs l.args l.kcfg ∧
        StackAt l.prof l.s₀ l.args (ElfHeader.read V2606.zzs.blob.bytes) zzsPhdrs c ∧
        (ctxOf l.prof l.s₀ l.args c).Ok ∧ Img (ctxOf l.prof l.s₀ l.args c).V0 ∧ Bss (ctxOf l.prof l.s₀ l.args c).V0 ∧
        GoG l.prof L o gev (fun X _ _ => X.cpu.rip = 0x41cd90#64) (fun _ _ => False) l.s₀ t := by
  obtain ⟨s, hE, hl⟩ := exec0
  obtain ⟨L, hL, hC, hT, hO, hP, hLC, hMC, hX, hMn, hCC, hPl⟩ := text_code_plt
  have h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size ⟨prof0, files0, exe0, args0, k0, s⟩ :=
    ⟨holds0, hE, args_ok0⟩
  exact ⟨⟨prof0, files0, exe0, args0, k0, s⟩, o0, L, h, hl, undisturbed0,
    launch_main_plt h room0 (Nat.le_refl _) rfl ⟨rfl, rfl⟩ hl (fun _ hi => absurd hi (Nat.not_lt_zero _))
      (fun _ hi => absurd hi (Nat.not_lt_zero _)) (fun _ hi => absurd hi (Nat.not_lt_zero _)) ok0 consistent0 chain0
      undisturbed0 vdso0 hL hC hT hO hP modest0 mg0 pse0 un0 hLC hMC hPl ssse3_0 avx_0 hX hMn hCC cacheEnds0⟩

end FV7z.Wit
