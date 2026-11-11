import FV7z.Start.Vc
/-!
# The start of `__libc_start_main`, to where `init_cpu_features` begins (PLAN.md G3, startup)

`start_cfg`: in a run that has the code of `__libc_start_main`, `_dl_relocate_static_pie`, `_dl_aux_init`,
`__libc_init_secure` and `__tunables_init`, from the entry with what the launch gives (`Ctx.Ok`, `Env`, `I0`) the run
goes on to offset 211 with `FinP` there: the frame set up, `__libc_multiple_libcs` 0, `__environ` and
`__libc_stack_end` set, `_dl_aux_init`'s variables as the vector's entries set them (`__libc_enable_secure` 0,
`_dl_phdr` not null), no tunable set, and the other bytes outside the stack as at the entry. What follows offset 211 is
the caller's (`hfin`), as in `Seg.cfg`.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {K : Ctx}

theorem start_cfg (c : Seg prof F Wl L s₀ o) (hl : CodeIn L lsm_at lsm) (hp : CodeIn L Pie.pie_at Pie.pie)
    (ha : CodeIn L Auxv.aux_at Auxv.aux) (hs : CodeIn L Sec.sec_at Sec.sec) (ht : CodeIn L Tun.tin_at Tun.tin)
    (hK : K.Ok) (hE : Env K F Wl)
    (hfin : ∀ g fl V', FinP K g V' → ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V' →
      Y.cpu.rip = lsm_at.add 211 → Y.cpu.gpr = g → Y.cpu.rflags = fl → GoG prof L o gev gP gE Y t')
    {X : State} {t : Nat} {V : Addr → Byte} (hX : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = lsm_at) (hI : I0 K (K.N + 20) X.cpu.gpr V) : GoG prof L o gev gP gE X t :=
  cfgAt (spC c hl hp ha hs ht) (fun ℓ n g _ V => InvT K ℓ n g V) (fun j g _ V => j = 211 ∧ FinP K g V)
    (fun ℓ n g f V h => vcAll hK hE ℓ n g f V h)
    (fun _ g fl V' h => by obtain ⟨rfl, hF⟩ := h; exact hfin g fl V' hF)
    (K.N + 20) 0 hX hA (by rw [hrip]; simp) hI

end FV7z.Start
