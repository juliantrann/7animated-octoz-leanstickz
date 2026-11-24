import ZellicX86.Spec.Statement
/-!
# Part (A) of `Confined`: the run follows the control-flow graph (PLAN.md §5.2)

`NoHijack`: the addresses of the instructions a run executes form a path of the file's interprocedural control-flow
graph, with every return going back to the address its call pushed. The graph (`Cfg`) is an artifact made from the
binary (`tools/cfg_gen.py`, to come): for each instruction, the ways control may leave it (`Edge`): the next
instruction, a `jcc`'s two targets, a direct `jmp`, each target of an indirect `jmp` (a `switch` table, a tail call
through a pointer), a call (direct, or each target of an indirect call: a vtable slot, a handler's or a codec's
function pointer, an IFUNC slot of `.got.plt`) with its return address, a return, an unwinder's jump to a landing pad,
and `longjmp`.

The return addresses live on a ghost stack, part of the statement only (`Walk`): a call pushes its return address, a
return must go to the address on top and pops it, an unwind drops frames down to a call site with a landing pad and
goes to that pad. So a run whose return address was overwritten (ROP), whose function pointer was replaced (a
hijacked vtable or `.got.plt` slot), or that jumps into data, does not follow the graph: an attacker who controls the
archive steers data, never code.

Each step of a run is one step of the model (`run`), so an instruction that repeats in place (`rep movsb`, one
iteration per step) needs an edge to itself; the generator adds it.
-/

namespace FV7z.Statement
open ZellicX86

/-- A way control may leave an instruction. -/
inductive Edge
  /-- to `q` with the ghost stack unchanged: the next instruction, a `jcc` target, a `jmp` (direct, or one target of
  an indirect one, a tail call included), the return of a system call -/
  | go (q : Addr)
  /-- a call of `q` (direct, or one target of an indirect call) that returns to `ra`: pushes `ra` -/
  | call (q ra : Addr)
  /-- a return: to the return address on top of the ghost stack, which it pops -/
  | ret
  /-- an exception unwinder's jump (`uw_install_context`) to a landing pad of a frame still on the stack -/
  | unwind
  /-- `longjmp` to a `setjmp`'s return point in a frame still on the stack -/
  | longjmp
  deriving DecidableEq, Repr

/-- The interprocedural control-flow graph of a file. -/
structure Cfg where
  /-- the address of the first instruction (the ELF entry, `_start`) -/
  entry : Addr
  /-- the ways control may leave the instruction at an address (none for an address that is not an instruction) -/
  edges : Addr → List Edge
  /-- the landing pads of the call site returning to an address (`.gcc_except_table`'s call-site records) -/
  pads : Addr → List Addr
  /-- the return points of the calls of `setjmp` -/
  setjmps : List Addr

/-- One step from `p` to `q` follows an edge of `p`, taking the ghost stack from `stk` to `stk'` (top first). -/
def Cfg.Step (g : Cfg) (stk : List Addr) (p q : Addr) (stk' : List Addr) : Prop :=
  ∃ e ∈ g.edges p, match e with
    | .go r => q = r ∧ stk' = stk
    | .call r ra => q = r ∧ stk' = ra :: stk
    | .ret => stk = q :: stk'
    | .unwind => ∃ drop ra, stk = drop ++ ra :: stk' ∧ q ∈ g.pads ra
    | .longjmp => q ∈ g.setjmps ∧ stk' <:+ stk

/-- `g.Walk tr stk`: the addresses `tr` (the last one first) are a path of `g` from its entry, which leaves the ghost
stack `stk` (top first). -/
inductive Cfg.Walk (g : Cfg) : List Addr → List Addr → Prop
  | start : g.Walk [g.entry] []
  | step {p q : Addr} {tr stk stk' : List Addr} :
      g.Walk (p :: tr) stk → g.Step stk p q stk' → g.Walk (q :: p :: tr) stk'

/-- The addresses `tr` (the last one first) are a path of `g` from its entry, for some ghost stack. -/
def Cfg.Follows (g : Cfg) (tr : List Addr) : Prop :=
  ∃ stk, g.Walk tr stk

theorem Cfg.step_go {g : Cfg} {stk : List Addr} {p q : Addr} (h : Edge.go q ∈ g.edges p) : g.Step stk p q stk :=
  ⟨.go q, h, rfl, rfl⟩

theorem Cfg.step_call {g : Cfg} {stk : List Addr} {p q ra : Addr} (h : Edge.call q ra ∈ g.edges p) :
    g.Step stk p q (ra :: stk) :=
  ⟨.call q ra, h, rfl, rfl⟩

theorem Cfg.step_ret {g : Cfg} {stk : List Addr} {p q : Addr} (h : Edge.ret ∈ g.edges p) :
    g.Step (q :: stk) p q stk :=
  ⟨.ret, h, rfl⟩

/-- The last step of a path of two addresses or more. -/
theorem Cfg.Walk.cons_cons {g : Cfg} {q p : Addr} {tr stk' : List Addr} (h : g.Walk (q :: p :: tr) stk') :
    ∃ stk, g.Walk (p :: tr) stk ∧ g.Step stk p q stk' := by
  cases h with
  | step h hs => exact ⟨_, h, hs⟩

/-- The address of the next instruction after `m` steps of the run from `s₀`, if it is still running. -/
def pcAt (prof : Profile) (o : Oracle) (s₀ : State) (t m : Nat) : Option Addr :=
  match run prof o m s₀ t with
  | (.running s, _, _) => some s.cpu.rip
  | (.done _, _, _) => none

/-- The addresses of the instructions of the first `n` steps of the run from `s₀` and of the next one, the last
first (those of the states the run is in after `0, 1, …, n` steps, while it runs). -/
def pcs (prof : Profile) (o : Oracle) (s₀ : State) (t n : Nat) : List Addr :=
  ((List.range (n + 1)).filterMap (pcAt prof o s₀ t)).reverse

/-- On processor `prof`, for every stream of answers satisfying `env`, every part of the run from `s₀` follows `g`. -/
def AlwaysPath (prof : Profile) (env : Oracle → Prop) (s₀ : State) (g : Cfg) : Prop :=
  ∀ o, env o → ∀ t n, g.Follows (pcs prof o s₀ t n)

end FV7z.Statement
