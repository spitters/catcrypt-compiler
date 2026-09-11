/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.OpSemCoverage
public import CatCrypt.Crypto.SecureCompilation.VIR.OpSemCoverage

/-!
# Whole-command run-correctness: `execCmd` is the monadic fold of `execInstr`

`OpSemCoverage.lean` lands the *per-instruction* run-correctness family —
`execInstrR_Cassgn_eq`, `execInstrR_Copn_eq`, the `Cif`/`Cwhile`/`Ccall`
keystones, and the counted `Cfor` keystone — one verified run-characterisation
per `InstrR` constructor. This file lifts that per-instruction layer to the
**whole-command** level.

A `Cmd` (`JasminCoqSemMirror.lean:455`) is `List Instr`. The executor `execCmd`
(`JasminCoqSemMirror.lean:1217`) runs a command list by running its head
instruction (`execInstr`) and threading the resulting `Estate` through the
`JResult` error monad into the tail run:

```
execCmd fuel s []        prog = .ok s
execCmd fuel s (i :: c)  prog = (execInstr fuel s i prog) >>= fun s' => execCmd fuel s' c prog
```

i.e. `execCmd` **is** the left-to-right monadic fold of `execInstr` over the
instruction list. Both clauses hold by `rfl` (they are the two defining
equations of `execCmd`); this file states them as named lemmas
(`execCmd_nil` / `execCmd_cons`), records the fold characterisation as the
deliverable, and lifts them to the concatenation law `execCmd_append`
(running `c₁ ++ c₂` = running `c₁`, then `c₂` on the result) by induction on
`c₁`.

## What this connects

The per-instruction keystones characterise the *effect of one instruction*;
`execCmd_cons` says the effect of a whole command is the head instruction's
effect, monadically composed with the tail's. Chaining `execCmd_cons` down a
straight-line list and rewriting each head with its per-instruction keystone
(e.g. `execInstrR_Cassgn_eq`) gives the whole-program effect as the explicit
left-to-right composition of the per-instruction effects — the whole-program
form of the `OpSemCoverage` per-constructor coverage. We exhibit this for a
straight-line block of `Cassgn`s (`execCmd_cassgnBlock_eq`) and as an
end-to-end concrete KAT (`block_kat`: `x := y + 1 ; z := x + x` started at
`y = 5` ends with `x = 6`, `z = 12`).

## Honest notes

* **Fuel threading.** `execCmd fuel s (i :: c)` passes *the same* `fuel` to both
  the head `execInstr` and the tail `execCmd` (fuel is *not* split per
  instruction — it bounds the *recursion depth inside* each instruction, e.g.
  loop/call unfolding, not the list length). The fold laws are therefore
  fuel-uniform: a single `fuel` parameter threads unchanged through the whole
  list. A head instruction that exhausts fuel (`execInstrR … 0 …`) short-circuits
  the whole command — see the next bullet.
* **Error short-circuit.** The composition is `JResult.bind`, which is *strict*
  on every non-`ok` constructor (`bind_typeError`/`bind_undefError`/
  `bind_addrUndef`/`bind_otherErr`, all `rfl`). So if the head instruction
  errors, `execCmd_cons` immediately yields that same error and the tail never
  runs — exactly the operational short-circuit of a real instruction sequence.
* These structural laws need **no** opaque-leaf hypothesis: they are facts about
  `execCmd`'s own recursion and the `JResult` monad, independent of the leaf
  semantics. The opaque-leaf edge (`LeafAgrees`) only enters when one rewrites a
  *specific* instruction's effect via a keystone that itself denotes a leaf.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.CmdRun

open CatCrypt.Crypto.Jasmin.CoqSemMirror
open CatCrypt.Crypto.SecureCompilation.VIR.OpSemCoverage

variable {SyscallState Mem : Type} [MemModel Mem]

/-! ## 1. The two defining run-laws of `execCmd` (the monadic fold)

Both clauses are the defining equations of `execCmd` — they hold by `rfl`. We
name them so downstream list inductions and rewrites do not have to re-derive
the unfolding, and so the *fold* characterisation (`execCmd_fold_eq`) is a
single referenceable statement. -/

/-- **Empty command = identity.** Running the empty instruction sequence from
    `s` returns `s` unchanged (`.ok s`). This is `execCmd`'s `[]` defining
    equation. -/
@[simp] theorem execCmd_nil
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls)
    (fuel : Nat) (s : Estate SyscallState Mem) (prog : Prog) :
    execCmd (Mem := Mem) aS opS gd fuel s [] prog = .ok s := by
  simp only [execCmd]

/-- **Cons = run head, then tail on the result.** Running `i :: c` from `s`
    runs the head instruction `i` (via `execInstr`) and threads its resulting
    state through `JResult.bind` into the tail run `execCmd … c`. This is
    `execCmd`'s `i :: c` defining equation: `execCmd` is the left-to-right
    monadic fold of `execInstr` over the list. The `bind` is strict on every
    error constructor, so a head error short-circuits the whole command. -/
theorem execCmd_cons
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls)
    (fuel : Nat) (s : Estate SyscallState Mem)
    (i : Instr) (c : Cmd) (prog : Prog) :
    execCmd (Mem := Mem) aS opS gd fuel s (i :: c) prog
      = (execInstr (Mem := Mem) aS opS gd fuel s i prog).bind
          (fun s' => execCmd (Mem := Mem) aS opS gd fuel s' c prog) := by
  simp only [execCmd]
  rfl

/-- **Fold characterisation (the deliverable).** Packaged together, the two
    defining equations exhibit `execCmd` as the monadic left-fold of `execInstr`
    over the instruction list: empty = `.ok`, cons = head `>>= ` tail. Every
    whole-command run-law in this file is a corollary of this fold shape. -/
theorem execCmd_fold_eq
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls)
    (fuel : Nat) (s : Estate SyscallState Mem) (prog : Prog) :
    (execCmd (Mem := Mem) aS opS gd fuel s [] prog = .ok s)
    ∧ (∀ (i : Instr) (c : Cmd) (s : Estate SyscallState Mem),
        execCmd (Mem := Mem) aS opS gd fuel s (i :: c) prog
          = (execInstr (Mem := Mem) aS opS gd fuel s i prog).bind
              (fun s' => execCmd (Mem := Mem) aS opS gd fuel s' c prog)) :=
  ⟨execCmd_nil aS opS gd fuel s prog,
   fun i c s => execCmd_cons aS opS gd fuel s i c prog⟩

/-! ## 2. The concatenation run-law `execCmd_append`

Running `c₁ ++ c₂` from `s` equals running `c₁` from `s` and then `c₂` from the
result. Proved by induction on `c₁`, reusing the two fold laws; both sides agree
on every error case via `JResult.bind`'s strictness on non-`ok` values.

(An identical lemma — also named `execCmd_append` — already lives inside the
heavy MAYO universal-connector namespace,
`MLIR.VectorDialect.MayoLeafJasminFullBody.UniversalConnector`. That file pulls
in the entire MAYO leaf-emit corpus; this additive re-proof in the operational
`VIR` namespace keeps the whole-command run-law importable from the lightweight
`OpSemCoverage` chain without that dependency.) -/

/-- **Concatenation = sequencing.** Running `c₁ ++ c₂` from `s` is the same as
    running `c₁` from `s`, then `c₂` from the result — `execInstr`-fold
    composition is associative over list concatenation. A head error in `c₁`
    short-circuits `c₂` (the `bind` is strict). -/
theorem execCmd_append
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls)
    (fuel : Nat) (s : Estate SyscallState Mem) (c₁ c₂ : Cmd) (prog : Prog) :
    execCmd (Mem := Mem) aS opS gd fuel s (c₁ ++ c₂) prog
      = (execCmd (Mem := Mem) aS opS gd fuel s c₁ prog).bind
          (fun s' => execCmd (Mem := Mem) aS opS gd fuel s' c₂ prog) := by
  induction c₁ generalizing s with
  | nil =>
    simp only [List.nil_append, execCmd_nil, JResult.bind]
  | cons i c ih =>
    rw [List.cons_append, execCmd_cons, execCmd_cons]
    cases h : execInstr (Mem := Mem) aS opS gd fuel s i prog with
    | ok s'      => simp only [JResult.bind, ih]
    | typeError  => rfl
    | undefError => rfl
    | addrUndef  => rfl
    | otherErr m => rfl

/-! ## 3. Straight-line `Cassgn` blocks: the whole-program form of coverage

Specialising the fold to a list of assignments connects the per-instruction
`Cassgn` keystone (`execInstrR_Cassgn_eq`) to a whole-command run. For a
two-assignment block `[MkI ii₁ (Cassgn lv₁ tag₁ ty₁ e₁), MkI ii₂ (Cassgn …)]`
at fuel `fuel'+1`, the whole-command run is the explicit composition of the two
`assignExec`s — the whole-program lift of `OpSemCoverage`'s per-constructor
characterisation. -/

/-- **Whole-command `Cassgn`-block run.** A two-instruction straight-line block
    of assignments, run at fuel `fuel'+1`, equals the monadic composition of the
    two per-instruction `assignExec` effects: evaluate/truncate/write the first
    assignment, then (on the resulting state) the second. Each head is rewritten
    by the per-instruction keystone `execInstrR_Cassgn_eq`; the list structure
    is supplied by `execCmd_cons`. -/
theorem execCmd_cassgnBlock_eq
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)
    (fuel' : Nat) (s : Estate SyscallState Mem)
    (ii₁ : InstrInfo) (lv₁ : Lval) (tag₁ : AssgnTag) (ty₁ : Atype) (e₁ : Pexpr)
    (ii₂ : InstrInfo) (lv₂ : Lval) (tag₂ : AssgnTag) (ty₂ : Atype) (e₂ : Pexpr) :
    execCmd (Mem := Mem) aS opS gd (fuel'+1) s
        [ .MkI ii₁ (.Cassgn lv₁ tag₁ ty₁ e₁),
          .MkI ii₂ (.Cassgn lv₂ tag₂ ty₂ e₂) ] prog
      = (assignExec (Mem := Mem) opS gd lv₁ ty₁ e₁ s).bind
          (fun s' => assignExec (Mem := Mem) opS gd lv₂ ty₂ e₂ s') := by
  -- `execInstr (MkI _ (Cassgn …))` unfolds (via `execInstr`) to `execInstrR`,
  -- which the per-instruction keystone `execInstrR_Cassgn_eq` rewrites to
  -- `assignExec`; `execCmd_cons`/`execCmd_nil` supply the list structure and
  -- `bind_pure_right` collapses the trailing `>>= fun s' => .ok s'`.
  simp only [execInstr, execInstrR_Cassgn_eq, execCmd_cons, execCmd_nil,
    JResult.bind_pure_right]

/-! ## 4. Worked end-to-end KAT: `x := y + 1 ; z := x + x`

Reusing the `OpSemCoverage.AssignExample` machinery (trivial memory, an
`OpSem` covering integer add, variables `x`/`y`), we build a concrete
two-instruction straight-line *command* and run it end-to-end. Started at
`y = 5`, the block `x := y + 1 ; z := x + x` produces `x = 6`, `z = 12` — the
composed per-instruction effects, checked by `native_decide`. -/

namespace BlockExample

open OpSemCoverage.AssignExample

/-- The third variable `z : aint` (target of the second assignment). -/
def zVar : VarI := { v_var := { vtype := .aint, vname := "z" } }

/-- The RHS of the second assignment, `x + x`. -/
def rhs2 : Pexpr :=
  .Papp2 (.Oadd .Op_int) (.Pvar (mkLvar xVar)) (.Pvar (mkLvar xVar))

/-- The second emitted assignment `z := x + x`. -/
def assignZX : InstrR := .Cassgn (.Lvar zVar) .AT_none .aint rhs2

/-- The straight-line command `x := y + 1 ; z := x + x` as a `Cmd`
    (`List Instr`). `InstrInfo` is `Unit` in the mirror, so `()` annotates. -/
def block : Cmd :=
  [ .MkI default assignXY, .MkI default assignZX ]

/-- Read `z` out of a post-state, projected to `Option Int`. -/
def readZ (s : Estate Unit TrivialMem) : Option Int :=
  match (Vm.get s.evm zVar.v_var) with
  | .Vint w => some w
  | _ => none

/-- **End-to-end whole-command KAT.** Started at `y = 5`, running the whole
    command `x := y + 1 ; z := x + x` writes `x = 6` then `z = x + x = 12`.
    This is `execCmd` over a real 2-instruction list, evaluated by
    `native_decide` — the composed per-instruction effects, end to end. -/
theorem block_kat :
    (match execCmd (Mem := TrivialMem) addAsmSem addOpSem []
              4 (startState 5) block with
     | .ok s => (readX s, readZ s)
     | _ => (none, none)) = (some 6, some 12) := by
  native_decide

/-- **Whole-command run = composed per-instruction effects (symbolic).** The
    same concrete block, run at *any* fuel `fuel'+1` from *any* start state,
    equals the monadic composition of the two `assignExec`s — a direct instance
    of `execCmd_cassgnBlock_eq`, connecting the whole-command run to the
    per-instruction `Cassgn` keystone without `native_decide`. -/
theorem block_eq_composed (n : Int) (fuel' : Nat) :
    execCmd (Mem := TrivialMem) addAsmSem addOpSem [] (fuel'+1)
        (startState n) block
      = (assignExec (Mem := TrivialMem) addOpSem [] (.Lvar xVar) .aint rhs
            (startState n)).bind
          (fun s' => assignExec (Mem := TrivialMem) addOpSem []
            (.Lvar zVar) .aint rhs2 s') :=
  execCmd_cassgnBlock_eq addAsmSem addOpSem [] Prog.empty fuel' (startState n)
    default (.Lvar xVar) .AT_none .aint rhs
    default (.Lvar zVar) .AT_none .aint rhs2

end BlockExample

end CatCrypt.Crypto.SecureCompilation.VIR.CmdRun
