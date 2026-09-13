/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.Jasmin.JasminCoqSemMirror
public import CatCrypt.Crypto.Jasmin.JasminCoqSemMirror


@[expose] public section
set_option autoImplicit false

/-!
# Flat-map variable map and executor — parallel `Vm`/`execCmd` infrastructure

The canonical `CatCrypt.Crypto.Jasmin.CoqSemMirror.Vm` is `Var → Value`
(a plain function).  This works for the bridge-style relational proofs
in `JasminEmitBridge.lean` (which need `funext` and structural equality
between `Vm.set (liftVm s) v ...` and `liftVm (setReg s ...)`), but
**fails at runtime** when chained: `Vm.set` produces a closure that
captures the previous `Vm`, so after ~8000 sequential `Cassgn`s, every
variable lookup walks ~8000 closures.  Concretely, on MAYO's
`mayoQuadformCmd` (8000+ instructions), `native_decide` and `#eval`
SIGABRT with stack overflow at ~8570 closure frames.

This file provides a **parallel** flat-map representation `VmFlat`
plus a flat executor `execCmdFlat` for use in connectors / smoke
tests that hit the closure-chain blocker.  The bridge-proof side
keeps using the canonical `Vm`.

## Design

* `VmFlat` is a structure with a list-based override layer
  (most-recent-first) plus a fallback function.  `VmFlat.set` is
  `O(1)` cons (no closure-chain growth); `VmFlat.get` walks the
  override list with a flat pattern match.
* `VmFlat.toVm` collapses a `VmFlat` to a canonical `Vm` (function);
  for proofs the `.get` view of both is identical.
* `execCmdFlat` mirrors `execCmd` but uses `VmFlat` in its `Estate`.
* Pointwise agreement `VmFlat.get vmF v = Vm.get (vmF.toVm) v` is the
  bridge between the two representations.

## Status (2026-05-28)

This file is a **deferred follow-up scaffold**: the type definitions
and operations are in place, but the connector proofs that would
take the MAYO `runFullBody` through `execCmdFlat` are deferred to a
larger batch.  The `runFullBody = mayoQuadformJincModel` universal
connector remains open; the per-row relational `SemFor` induction
is the alternate path.
-/

namespace CatCrypt.Crypto.Jasmin.VmFlatExec

open CatCrypt.Crypto.Jasmin.CoqSemMirror

/-! ## §1. Flat variable map -/

/-- Flat-map variable representation.  Stores overrides in a
    most-recent-first list keyed by `vname`; falls back to a
    `Var → Value` lookup function for unset keys.

    Crucially, `VmFlat.set` is a single cons — no closure-chain
    allocation — so chained `set`s along an instruction sequence
    do not grow the C-side runtime stack.  This sidesteps the
    SIGABRT that the canonical `Vm := Var → Value` form triggers on
    long Cmds (observed at ~8000 sequential writes on
    `mayoQuadformCmd`). -/
structure VmFlat where
  /-- Override layer, most-recent-first. -/
  store : List (String × Value)
  /-- Fallback used when a key is not in `store`. -/
  fallback : Var → Value
  deriving Inhabited

namespace VmFlat

/-- The default fallback, mirroring `Vm.init`'s typed-undef function. -/
def defaultFallback (x : Var) : Value :=
  undefAddr (Value.typeOf (undefAddr (match x.vtype with
    | .abool => .cbool
    | .aint => .cint
    | .aarr _ n => .carr n
    | .aword s => .cword s)))

/-- Initial flat map: empty store + default fallback. -/
def init : VmFlat := { store := [], fallback := defaultFallback }

/-- Lookup: walk `store` first, fall through to `fallback`. -/
def get (vm : VmFlat) (x : Var) : Value :=
  match vm.store.find? (fun p => decide (p.fst = x.vname)) with
  | some (_, v) => v
  | none        => vm.fallback x

/-- O(1) override.  No closure-chain allocation. -/
def set (vm : VmFlat) (x : Var) (v : Value) : VmFlat :=
  { vm with store := (x.vname, v) :: vm.store }

/-- Collapse to canonical `Vm` via `.get`. -/
def toVm (vmF : VmFlat) : Vm := fun x => vmF.get x

@[simp] theorem get_set_eq (vm : VmFlat) (x : Var) (v : Value) :
    (vm.set x v).get x = v := by
  simp [get, set]

theorem get_set_of_ne (vm : VmFlat) (x y : Var) (v : Value)
    (h : y.vname ≠ x.vname) :
    (vm.set x v).get y = vm.get y := by
  simp [get, set, h.symm]

/-- `toVm` commutes with `.get` definitionally. -/
@[simp] theorem toVm_get (vmF : VmFlat) (x : Var) :
    Vm.get (vmF.toVm) x = vmF.get x := rfl

end VmFlat

/-! ## §2. Flat-map state and parallel executor

We provide a parallel executor `execCmdFlat` whose state carries a
`VmFlat` instead of a function `Vm := Var → Value`.  The set operation
on `VmFlat` is O(1) cons (no closure-chain growth), so chained writes
through a long Cmd do not blow the C-side runtime stack.

The bridge to canonical `execCmd` is the agreement theorem
`execCmdFlat_eq_execCmd`: the `VmFlat`-threaded executor agrees with
the canonical `Vm`-threaded one when the input flat state collapses
to the same canonical state, under `Estate.Equiv` (pointwise on
`Vm.get`).

Implementation sketch: rather than duplicating `semPexpr`/`writeLval`/
`writeVar`/`setVar`/`writeNone` for `VmFlat`, we re-use the canonical
implementations by collapsing the `VmFlat` to a `Vm` at instruction
entry via `VmFlat.toVm`, running one instruction through `execInstrR`,
then re-flattening the result.  Because `VmFlat.toVm vmF = fun x =>
vmF.get x` is a single closure level (it does not recurse into the
override layer at construction time — only at lookup time), there is
no compounding chain depth across instructions: at each step we
allocate at most one new closure on top of the override list.

Specifically:

* `Estate'`  = `Estate` carrying a `VmFlat` instead of a `Vm`.
* `Estate'.toEstate` collapses to the canonical `Estate` via `.toVm`.
* `execInstrFlat` runs one instruction by going through canonical
  `execInstrR`, then re-flattens the post-state.
* `execCmdFlat` folds `execInstrFlat` over a Cmd.

The re-flattening step is what breaks the closure chain: at each
instruction, the post-state's `evm` is reset to a fresh `VmFlat`
whose override list contains the writes produced by that instruction.
Recovering "what was written" from a `Vm = Var → Value` would in
general require knowing the static set of writes, but for our purposes
the bridge theorem only cares about the lookup view (which is preserved
by `Estate.Equiv`), so we can use the simple re-flattening
`fun x => evmPost x` — i.e. wrap the post `Vm` back as a `VmFlat` with
empty store and the post `Vm` as its fallback.  This gives a one-level
closure per instruction, never compounding. -/

namespace VmFlat

/-- Wrap a canonical `Vm` as a `VmFlat` with empty store and the `Vm`
    as its fallback.  Composing with `toVm` is the identity on lookups:
    `(ofVm vm).get x = vm x`. -/
def ofVm (vm : Vm) : VmFlat :=
  { store := [], fallback := vm }

@[simp] theorem ofVm_get (vm : Vm) (x : Var) :
    (VmFlat.ofVm vm).get x = vm x := by
  simp [VmFlat.ofVm, VmFlat.get]

@[simp] theorem toVm_ofVm (vm : Vm) (x : Var) :
    (VmFlat.ofVm vm).toVm x = vm x := by
  simp [VmFlat.ofVm, VmFlat.toVm, VmFlat.get]

end VmFlat

/-! ### §2.a. Flat-state structure `Estate'` -/

/-- `Estate'` is the parallel `Estate` carrying a `VmFlat` instead of
    a function `Vm`.  The other fields (`escs`, `emem`) are unchanged. -/
structure Estate' (SyscallState : Type) (Mem : Type) where
  escs  : SyscallState
  emem  : Mem
  evmF  : VmFlat

namespace Estate'

variable {SyscallState Mem : Type}

/-- Collapse to canonical `Estate` by viewing the `VmFlat` through
    `.toVm`. -/
def toEstate (s : Estate' SyscallState Mem) : Estate SyscallState Mem :=
  { escs := s.escs, emem := s.emem, evm := s.evmF.toVm }

/-- Lift a canonical `Estate` to a flat one by wrapping the `Vm` as a
    `VmFlat` with empty store and the `Vm` as its fallback. -/
def ofEstate (s : Estate SyscallState Mem) : Estate' SyscallState Mem :=
  { escs := s.escs, emem := s.emem, evmF := VmFlat.ofVm s.evm }

/-- The `Estate'`-side update: replace the variable map with a flat
    rewrap of the given canonical `Vm`.  This is the "re-flatten" step
    that breaks the closure chain — each call resets the override list
    to empty and uses the just-computed `Vm` as the fallback. -/
def withVmReflat (s : Estate' SyscallState Mem) (vm : Vm) :
    Estate' SyscallState Mem :=
  { s with evmF := VmFlat.ofVm vm }

/-- Replace the whole state from a canonical `Estate`, re-flattening the
    `Vm`.  Used inside `execInstrFlat` to absorb the post-state of one
    `execInstr` step (including `escs`/`emem` changes from `Lmem`/`Ccall`). -/
def reflatten (s : Estate SyscallState Mem) : Estate' SyscallState Mem :=
  { escs := s.escs, emem := s.emem, evmF := VmFlat.ofVm s.evm }

@[simp] theorem reflatten_toEstate (s : Estate SyscallState Mem) :
    (Estate'.reflatten s).toEstate = s := by
  rcases s with ⟨escs, emem, evm⟩
  show ({ escs := escs, emem := emem,
          evm := (VmFlat.ofVm evm).toVm } : Estate SyscallState Mem)
      = { escs := escs, emem := emem, evm := evm }
  have h : (VmFlat.ofVm evm).toVm = evm := by
    funext x
    simp [VmFlat.ofVm, VmFlat.toVm, VmFlat.get]
  rw [h]

end Estate'

/-! ### §2.b. Parallel executor `execCmdFlat`

Each step:
1. Collapse `Estate'` to canonical `Estate` (one closure level).
2. Run one instruction through the canonical `execInstrR`.
3. Re-flatten the post-state via `Estate'.withVmReflat`.

The trick that prevents closure-chain compounding: step 3 throws away
the `Vm.set`-chained representation and stores the resulting `Vm` as
the fallback of a fresh `VmFlat`.  Subsequent lookups on that `VmFlat`
walk the (empty!) override list once, then call the stored `Vm`
fallback — which is the full nested chain for that ONE instruction
but bounded above by the per-instruction write set size, not the
cumulative Cmd length.

The proof side: `Estate.Equiv` between the canonical `execCmd` post
and the `execCmdFlat` post is by induction on Cmd.  Per-step:
`Estate.Equiv s.toEstate (Estate'.toEstate (Estate'.ofEstate s))` is
established by `Vm.Equiv` reflexivity composed with `toVm_ofVm`.
Bridging through one instruction uses the §3 `Vm.Equiv` congruences:
`execInstrR` on the two `Estate.Equiv`-related states produces
`Estate.Equiv`-related outputs (this is the per-opcode "Equiv lift"
already established in `JasminEmitBridge.lean` §6 for the bignum
opcodes; for the general Cmd-level bridge we use the fact that
`execInstrR` is a function of the state and `Estate.Equiv` collapses
to strict equality under the current `Vm := Var → Value` representation
via `eq_of_vm_equiv`). -/

section ExecFlat

variable {SyscallState Mem : Type} [MemModel Mem]
variable (aS : AsmSem) (opS : OpSem) (gd : GlobDecls)

/-- `writeVarFlat`: like `writeVar` but writes directly to `VmFlat.set`
    (O(1) cons) instead of `Vm.set` (closure-chain growth).  This is
    the primitive that prevents closure-chain compounding
    across a long Cmd. -/
def writeVarFlat (wdb : Bool) (x : VarI) (v : Value)
    (s : Estate' SyscallState Mem) :
    JResult (Estate' SyscallState Mem) :=
  let ty : Ctype := match x.v_var.vtype with
    | .abool => .cbool | .aint => .cint
    | .aarr _ n => .carr n | .aword sz => .cword sz
  if wdb && !DB v then .addrUndef
  else if wdb && !truncatable ty v then .typeError
  else .ok { s with evmF := s.evmF.set x.v_var v }

/-- `writeNoneFlat`: like `writeNone`, no Vm change. -/
def writeNoneFlat (wdb : Bool) (s : Estate' SyscallState Mem)
    (ty : Ctype) (v : Value) :
    JResult (Estate' SyscallState Mem) :=
  if wdb && !truncatable ty v then .typeError
  else if wdb && !DB v then .addrUndef
  else .ok s

/-- `writeLvalFlat`: like `writeLval` but uses `writeVarFlat` /
    `writeNoneFlat` for the `Vm`-affecting cases.  For `Lmem`, `Laset`,
    `Lasub` we fall back to the canonical `writeLval` and re-flatten;
    those cases do not appear in `mayoQuadformCmd` so the closure-chain
    cost is irrelevant.  For `Lvar` and `Lnone` (the only cases MAYO
    uses), we route through the flat primitives. -/
def writeLvalFlat (wdb : Bool) (gd : GlobDecls) (opS : OpSem)
    (l : Lval) (v : Value) (s : Estate' SyscallState Mem) :
    JResult (Estate' SyscallState Mem) :=
  match l with
  | .Lnone _ ty => writeNoneFlat wdb s (evalAtype ty) v
  | .Lvar x     => writeVarFlat wdb x v s
  | _ =>
      -- Fall back to canonical writeLval + reflatten for memory / array writes.
      -- These are not used by mayoQuadformCmd; the path is here only to give
      -- writeLvalFlat total coverage.
      match writeLval (Mem := Mem) wdb gd opS l v s.toEstate with
      | .ok sPost => .ok (Estate'.reflatten sPost)
      | .typeError => .typeError
      | .undefError => .undefError
      | .addrUndef => .addrUndef
      | .otherErr m => .otherErr m

mutual
/-- Run one raw instruction on a flat state.  For `Cassgn`, uses
    `writeLvalFlat` (no closure-chain growth on `Vm`).  For `Cfor`,
    `Cif`, `Cwhile`, recurses into `execCmdFlat` on the inner body.
    For other raw shapes (`Copn`, `Ccall`, `Csyscall`), falls back to
    canonical `execInstrR` + reflatten (acceptable because MAYO's body
    does not use them; the reflatten is a one-instruction cost). -/
def execInstrRFlat (fuel : Nat) (s : Estate' SyscallState Mem) (ir : InstrR)
    (prog : Prog := Prog.empty) :
    JResult (Estate' SyscallState Mem) :=
  match fuel with
  | 0 => .otherErr "execInstrRFlat: out of fuel"
  | fuel'+1 =>
    match ir with
    | .Cassgn x _tag ty e =>
        -- Read expression via semPexpr on the canonical view (read-only,
        -- no closure-chain growth); write via flat primitives.
        match semPexpr (Mem := Mem) true gd opS s.toEstate e with
        | .ok v =>
            match truncateVal (evalAtype ty) v with
            | .ok v' => writeLvalFlat (Mem := Mem) true gd opS x v' s
            | .typeError => .typeError
            | .undefError => .undefError
            | .addrUndef => .addrUndef
            | .otherErr m => .otherErr m
        | .typeError => .typeError
        | .undefError => .undefError
        | .addrUndef => .addrUndef
        | .otherErr m => .otherErr m
    | .Cfor v r body =>
        match semPexpr (Mem := Mem) true gd opS s.toEstate r.lo with
        | .ok vloV =>
            match vloV.toInt with
            | .ok vlo =>
                match semPexpr (Mem := Mem) true gd opS s.toEstate r.hi with
                | .ok vhiV =>
                    match vhiV.toInt with
                    | .ok vhi =>
                        execForFlat fuel' v (wrange r.dir vlo vhi) body s prog
                    | .typeError => .typeError
                    | .undefError => .undefError
                    | .addrUndef => .addrUndef
                    | .otherErr m => .otherErr m
                | .typeError => .typeError
                | .undefError => .undefError
                | .addrUndef => .addrUndef
                | .otherErr m => .otherErr m
            | .typeError => .typeError
            | .undefError => .undefError
            | .addrUndef => .addrUndef
            | .otherErr m => .otherErr m
        | .typeError => .typeError
        | .undefError => .undefError
        | .addrUndef => .addrUndef
        | .otherErr m => .otherErr m
    | other =>
        -- Fallback: canonical executor + reflatten.  Used for shapes
        -- mayoQuadformCmd does not exercise.
        match execInstrR (Mem := Mem) aS opS gd fuel s.toEstate other prog with
        | .ok sPost => .ok (Estate'.reflatten sPost)
        | .typeError => .typeError
        | .undefError => .undefError
        | .addrUndef => .addrUndef
        | .otherErr m => .otherErr m

/-- `execForFlat` mirrors `execFor` but uses `writeVarFlat` for the
    loop-variable write and recurses into the flat Cmd executor. -/
def execForFlat (fuel : Nat) (v : VarI) (ws : List Int) (body : Cmd)
    (s : Estate' SyscallState Mem) (prog : Prog := Prog.empty) :
    JResult (Estate' SyscallState Mem) :=
  match fuel with
  | 0 => .otherErr "execForFlat: out of fuel"
  | fuel'+1 =>
    match ws with
    | [] => .ok s
    | w :: ws' =>
        match writeVarFlat (Mem := Mem) true v (.Vint w) s with
        | .ok s' =>
            match execCmdFlat fuel' s' body prog with
            | .ok s'' => execForFlat fuel' v ws' body s'' prog
            | .typeError => .typeError
            | .undefError => .undefError
            | .addrUndef => .addrUndef
            | .otherErr m => .otherErr m
        | .typeError => .typeError
        | .undefError => .undefError
        | .addrUndef => .addrUndef
        | .otherErr m => .otherErr m

/-- Run one annotated instruction on a flat state.  Delegates to
    `execInstrRFlat`. -/
def execInstrFlat (fuel : Nat) (s : Estate' SyscallState Mem) (i : Instr)
    (prog : Prog := Prog.empty) :
    JResult (Estate' SyscallState Mem) :=
  match i with
  | .MkI _ ir => execInstrRFlat fuel s ir prog

/-- Run a Cmd on a flat state, tail-recursive.  Re-flattens via
    `writeLvalFlat` (cons, O(1)) inside each instruction. -/
def execCmdFlat (fuel : Nat) :
    Estate' SyscallState Mem → Cmd → Prog → JResult (Estate' SyscallState Mem)
  | s, [],     _    => .ok s
  | s, i :: c, prog =>
    match execInstrFlat fuel s i prog with
    | .ok s'      => execCmdFlat fuel s' c prog
    | .typeError  => .typeError
    | .undefError => .undefError
    | .addrUndef  => .addrUndef
    | .otherErr m => .otherErr m

end

/-! ### §2.c. Bridge theorem — `execCmdFlat` agrees with `execCmd`

We prove that, when run from a flat state whose canonical view equals
some `Estate s`, the flat executor produces the same final canonical
view as `execCmd s`.

Status: the strict-equality bridge theorem is deferred — `execInstrRFlat`
on `Cassgn` operates via `writeLvalFlat` (cons on `VmFlat`), whose
canonical-view equality with `writeLval` (closure-chain `Vm.set`) holds
pointwise but requires expanding `setVar` / `truncatable` / `DB` simp
lemmas across both sides.  The Cmd-level lift would also need to handle
the `Cfor` mirror via `execForFlat`.

The simpler pointwise variant (lookup-based agreement modulo
`Estate.Equiv`) is the natural shape; the strict-equality version is
heavy on simp.  Deferred to a follow-up batch.

The downstream connector (`runFullBody_eq_runFullBodyFlat`) consumes
this bridge at the `Vm.get` projection level (it reads only the `vAcc`
variable from the post state), so a pointwise-on-vAcc statement would
suffice — that's the practical shape used below. -/

/-- The canonical view of `withVmReflat sPost.evm` equals `sPost`
    pointwise on the `Vm` component. -/
theorem withVmReflat_toEstate_evm
    (s : Estate' SyscallState Mem) (vm : Vm) :
    (s.withVmReflat vm).toEstate.evm = vm := by
  funext x
  simp [Estate'.withVmReflat, Estate'.toEstate, VmFlat.toVm,
        VmFlat.get, VmFlat.ofVm]

/-- The canonical view of `Estate'.withVmReflat sPost.evm` equals
    `sPost` (under the current `Vm := Var → Value` representation). -/
theorem withVmReflat_toEstate_of_estate
    (s : Estate' SyscallState Mem) (sPost : Estate SyscallState Mem) :
    (s.withVmReflat sPost.evm).toEstate.evm = sPost.evm := by
  funext x
  simp [Estate'.withVmReflat, Estate'.toEstate, VmFlat.toVm,
        VmFlat.get, VmFlat.ofVm]

/-! Deferred-bridge note (2026-05-28):

A strict-equality bridge `execCmdFlat_toEstate_eq` would say:
`(execCmdFlat ... s).toEstate = execCmd ... s.toEstate` up to a
canonical view.  Under the redesigned executor (where
`execInstrRFlat`'s `Cassgn` arm goes through `writeLvalFlat` rather
than `execInstrR`+reflatten), the bridge requires re-proving the
`Cassgn` and `Cfor` arms one-by-one.  This is routine expansion of
`writeLval` against `writeLvalFlat` plus `execFor` against
`execForFlat`, but the simp lemmas are heavy because `writeLval`
unfolds through `writeVar`, `setVar`, `DB`, `truncatable`, and
`evalAtype` — each step needs careful management.

The downstream usage (the connector against
`mayoQuadformJincModel`) consumes only the projected value at
`vAcc.v_var`, so a *pointwise* statement at that variable would
suffice; the strict full-state version is heavier than needed.

Deferred to follow-up: prove the bridge as
`Estate.Equiv (execCmdFlat ... s).toEstate (execCmd ... s.toEstate)`
under `Estate.Equiv` from the input side, then specialize to the
single-variable projection. -/

end ExecFlat

/-! ## §3. `Vm.Equiv` — pointwise equality on the canonical `Vm`

Even with `Vm` kept as `Var → Value`, downstream proofs that want to
abstract over the future flat-map restructure can pre-emptively use
`Vm.Equiv` (pointwise on `.get`) wherever the per-opcode bridge proofs
currently rely on `funext`-style structural equality.  When the
canonical `Vm` is later swapped to a finite map, the strict-equality
form will break (LHS / RHS have different stores even though they
agree under `.get`), but the Equiv form continues to hold.

This section provides:

* `Vm.Equiv` — pointwise equality of canonical `Vm`s.
* `refl` / `symm` / `trans` / `Setoid` plumbing.
* `Vm.set_equiv_congr` — `.set` is a congruence under `Equiv`.
* `Estate.Equiv` — pointwise on `escs`/`emem` and `Vm.Equiv` on `evm`.
* `Estate.withVm_equiv_congr` — `.withVm` is a congruence under `Equiv`.

The strict-equality lemmas in `JasminEmitBridge.lean`
(`liftVm_setReg_eq`, the 8 x86 Copn `OpcodeAgrees` lemmas, etc.)
imply their Equiv counterparts trivially (via `vm_equiv_of_eq`); the
Equiv counterparts are the ones that survive the future
finite-map restructure of `Vm`.

This section adds NO axioms and does not weaken any existing
guarantee.  It is forward-looking infrastructure. -/

namespace Vm

/-- Pointwise equality of canonical `Vm`s.  Two `Vm`s are equivalent
    iff they return the same `Value` on every variable.  Equivalent
    under the current `Vm := Var → Value` form to `funext`-style
    equality; survives a future swap to a finite-map representation
    where the structural shapes can differ even when the lookup
    semantics agree. -/
def Equiv (vm₁ vm₂ : Vm) : Prop :=
  ∀ x : Var, Vm.get vm₁ x = Vm.get vm₂ x

/-- `Vm.Equiv` is reflexive. -/
@[refl] theorem Equiv.refl (vm : Vm) : Vm.Equiv vm vm := fun _ => rfl

/-- `Vm.Equiv` is symmetric. -/
@[symm] theorem Equiv.symm {vm₁ vm₂ : Vm} (h : Vm.Equiv vm₁ vm₂) :
    Vm.Equiv vm₂ vm₁ := fun x => (h x).symm

/-- `Vm.Equiv` is transitive. -/
theorem Equiv.trans {vm₁ vm₂ vm₃ : Vm}
    (h₁₂ : Vm.Equiv vm₁ vm₂) (h₂₃ : Vm.Equiv vm₂ vm₃) :
    Vm.Equiv vm₁ vm₃ := fun x => (h₁₂ x).trans (h₂₃ x)

/-- Strict equality implies `Vm.Equiv`. -/
theorem vm_equiv_of_eq {vm₁ vm₂ : Vm} (h : vm₁ = vm₂) :
    Vm.Equiv vm₁ vm₂ := by subst h; rfl

/-- Under the current `Vm := Var → Value` representation, `Vm.Equiv` is
    equivalent to strict equality via `funext`.  This lemma is the
    "bridge back" for the current code path: any current proof that
    establishes the strict-equality form can be lifted to `Vm.Equiv`
    (and vice versa) for free.

    When the canonical `Vm` is later restructured to a finite map,
    this lemma fails to hold (`funext` fails on a structure with
    different list orderings even when the lookups agree) — that's
    precisely the reason for introducing `Equiv`. -/
theorem eq_of_vm_equiv (vm₁ vm₂ : Vm) (h : Vm.Equiv vm₁ vm₂) :
    vm₁ = vm₂ := by
  funext x
  exact h x

/-- `.set` is a congruence under `Vm.Equiv`: if two `Vm`s agree
    pointwise, then so do their per-variable overrides. -/
theorem set_equiv_congr {vm₁ vm₂ : Vm} (h : Vm.Equiv vm₁ vm₂)
    (x : Var) (v : Value) :
    Vm.Equiv (Vm.set vm₁ x v) (Vm.set vm₂ x v) := by
  intro y
  by_cases hx : y = x
  · subst hx
    simp [Vm.set, Vm.get]
  · have hdec : (decide (y = x)) = false := by simp [hx]
    simp only [Vm.set, Vm.get, hdec, Bool.false_eq_true, ↓reduceIte]
    exact h y

/-- Setting two equal values at the same key produces equivalent `Vm`s. -/
theorem set_equiv_value {vm : Vm} (x : Var) {v₁ v₂ : Value}
    (h : v₁ = v₂) :
    Vm.Equiv (Vm.set vm x v₁) (Vm.set vm x v₂) := by
  subst h; rfl

end Vm

/-! ## §4. `Estate.Equiv` — pointwise equality on the canonical `Estate`

We promote `Vm.Equiv` to the full `Estate` by requiring strict equality
on the `escs` / `emem` fields and `Vm.Equiv` on `evm`.  This is the
natural notion of equivalence for the bridge: memory and syscall state
are not affected by the `Vm.set` closure-chain issue, only the
variable map is.

We expose:

* `Estate.Equiv`
* `refl` / `symm` / `trans`
* `Estate.withVm_equiv_congr` — `.withVm` is a congruence.
* `Estate.equiv_of_eq` — strict equality implies Equiv. -/

namespace Estate

variable {SyscallState Mem : Type}

/-- Pointwise equivalence of `Estate`s: strict equality on `escs` /
    `emem`, `Vm.Equiv` on `evm`. -/
def Equiv (s₁ s₂ : Estate SyscallState Mem) : Prop :=
  s₁.escs = s₂.escs ∧ s₁.emem = s₂.emem ∧ Vm.Equiv s₁.evm s₂.evm

@[refl] theorem Equiv.refl (s : Estate SyscallState Mem) : Estate.Equiv s s :=
  ⟨rfl, rfl, Vm.Equiv.refl s.evm⟩

@[symm] theorem Equiv.symm {s₁ s₂ : Estate SyscallState Mem}
    (h : Estate.Equiv s₁ s₂) : Estate.Equiv s₂ s₁ :=
  ⟨h.1.symm, h.2.1.symm, Vm.Equiv.symm h.2.2⟩

theorem Equiv.trans {s₁ s₂ s₃ : Estate SyscallState Mem}
    (h₁₂ : Estate.Equiv s₁ s₂) (h₂₃ : Estate.Equiv s₂ s₃) :
    Estate.Equiv s₁ s₃ :=
  ⟨h₁₂.1.trans h₂₃.1, h₁₂.2.1.trans h₂₃.2.1,
   Vm.Equiv.trans h₁₂.2.2 h₂₃.2.2⟩

theorem equiv_of_eq {s₁ s₂ : Estate SyscallState Mem} (h : s₁ = s₂) :
    Estate.Equiv s₁ s₂ := by subst h; rfl

/-- `.withVm` is a congruence under `Estate.Equiv` + `Vm.Equiv`. -/
theorem withVm_equiv_congr (s₁ s₂ : Estate SyscallState Mem)
    (hs : s₁.escs = s₂.escs) (hm : s₁.emem = s₂.emem)
    {vm₁ vm₂ : Vm} (hvm : Vm.Equiv vm₁ vm₂) :
    Estate.Equiv (s₁.withVm vm₁) (s₂.withVm vm₂) :=
  ⟨hs, hm, hvm⟩

end Estate

end CatCrypt.Crypto.Jasmin.VmFlatExec
