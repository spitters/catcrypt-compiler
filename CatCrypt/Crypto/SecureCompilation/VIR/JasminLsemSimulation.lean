/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
import CatCrypt.Crypto.SecureCompilation.VIR.FreshNameInjective

/-!
# Straight-line linearizer simulation — increment 2 of porting jasmin's `lsem`

Increment 1 (`JasminLsem.lean`) built the straight-line linear machine
(`Lstate`/`lsemStep`/`lsemStraight`) and its composition law
`lsemStraight_append`. This module supplies the simulation that
connects the `Com jasminDialect` evaluator (`Com.denote`) to that linear
machine through the SSA linearizer `JasminLprogExport.Com.toLprog`
(`comToBody`/`resolveVar`/`opToLinstrR`).

This is the real content of the Com→`lsem` faithfulness predicate
`ComLsemExportFaithful` (`LsemPortAll`), **restricted to the straight-line
word-op fragment** the linear machine models (increment 1). The theorem proved
here, `comToLprog_lsem_straightline`, is the non-trivial faithfulness fact for
the fragment.

## The fragment

The linear machine `Lstate w` is single-width (`String → BitVec w`), so the
faithful fragment is the **uniform-width `regArith` straight-line chain**: a
`Com jasminDialect Γ t` whose context `Γ` is entirely `.reg w`, every binding is
a binary `regArith bop w`, and `t = .reg w`. This is exactly the word-level
two-address fragment `comToBody` emits as `Lopn [.reg dst] (binOpName bop) srcs`
straight-line instructions (no control flow). The predicate
`UniformRegArith w` carves it out.

## Naming fidelity (matches `Com.toLprog`)

`comToBody nArgs argName _ com curDepth` writes binding `curDepth` to
`regName curDepth` and resolves each operand var `v` (de Bruijn index `i`) to
slot `curDepth - 1 - i`: `argName slot` if `slot < nArgs`, else `regName slot`.
The encoding `encode` here places argument slot `j` at `argName j` exactly as the
linearizer reads it, and `decode`/`obsOf` reads the final binding's `regName`,
which is what `comRetReg` names as `lfd_res`. The agreement invariant
`StoreAgrees` is the linear-store analogue of `JasminPrintSemCorrect`'s
`StoreAgrees` for the named-store `execCom`, here phrased over the
`resolveVar`-naming the linearizer actually uses.

## Scope

Only the straight-line `regArith` fragment is in scope, because that is the only
fragment increment 1's `lsemStep` models faithfully (no `none`-fallbacks). The
trailing `.ret`/`Lret` is handled by `obsOf` reading the result register rather
than by stepping `Lret` (which is control flow, out of scope for increment 1).
The simulation is over `straightOps` — the `.var`-chain of `LinstrR` the body
emits, which is `(comToBody …).dropLast` lifted to `LinstrR`
(`straightOps_eq_body`).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.FreshNameInjective

/-! ## 1. `regName` injectivity

`regName d = "r" ++ toString d`; prefixing with the constant `"r"` is
left-cancellable, so distinct depths get distinct register names. Needed so a
write at `regName curDepth` does not clobber any earlier in-scope register. -/

/-- `regName` is injective: distinct SSA depths give distinct register names.
    Same proof shape as `freshName_injective` (`"r"` prefix instead of `"v"`). -/
theorem regName_injective : Function.Injective regName := by
  intro a b hab
  unfold regName at hab
  apply natToString_injective
  have hd := congrArg String.toList hab
  simp only [String.toList_append] at hd
  exact String.toList_injective (List.append_cancel_left hd)

/-- `regName d ≠ regName d'` whenever `d ≠ d'`. -/
theorem regName_ne {d d' : Nat} (h : d ≠ d') : regName d ≠ regName d' :=
  fun he => h (regName_injective he)

/-- A register name `regName d` is never an argument name `argName j`
    (`"r"…` vs `"a"…`). -/
theorem regName_ne_argName (d j : Nat) : regName d ≠ argName j := by
  unfold regName argName
  intro h
  have hd := congrArg (fun s => s.toList.head?) h
  simp [String.toList_append] at hd

/-- `argName` is injective: distinct argument slots give distinct names. -/
theorem argName_injective : Function.Injective argName := by
  intro a b hab
  unfold argName at hab
  apply natToString_injective
  have hd := congrArg String.toList hab
  simp only [String.toList_append] at hd
  exact String.toList_injective (List.append_cancel_left hd)

/-- `argName j ≠ argName j'` whenever `j ≠ j'`. -/
theorem argName_ne {j j' : Nat} (h : j ≠ j') : argName j ≠ argName j' :=
  fun he => h (argName_injective he)

/-! ## 2. De Bruijn index bound

`varIndex v < Γ.length` for any `v : Var Γ τ` — the de Bruijn index is a valid
position into the context. This bounds the resolved slot below `curDepth` (under
the invariant `Γ.length = curDepth`), so a write at `regName curDepth` never
clobbers an in-scope register. -/

/-- The de Bruijn index of a variable is a valid index into its context. -/
theorem varIndex_lt {Γ : Ctxt jasminDialect} {τ : JasminTy} (v : Ctxt.Var Γ τ) :
    varIndex v < Γ.length := by
  induction v with
  | here => simp [varIndex]
  | there v ih => simp only [varIndex, List.length_cons]; omega

/-! ## 3. The uniform-width `regArith` straight-line fragment

`UniformRegArith w com` holds when every binding of `com` is a binary
`regArith bop w` (the word-op fragment increment 1 models). The context being
uniformly `.reg w` is carried separately as `UniformCtxt`. -/

/-- Every variable of `Γ` has type `.reg w`. The context-uniformity side of the
    fragment (the linear machine `Lstate w` is single-width). -/
def UniformCtxt (w : Nat) (Γ : Ctxt jasminDialect) : Prop :=
  ∀ {τ : JasminTy}, Ctxt.Var Γ τ → τ = .reg w

/-- `UniformCtxt` extends along a `.reg w` binder. -/
theorem UniformCtxt.cons {w : Nat} {Γ : Ctxt jasminDialect}
    (h : UniformCtxt w Γ) : UniformCtxt w (.reg w :: Γ) := by
  intro τ v
  cases v with
  | here => rfl
  | there v => exact h v

/-- The straight-line `regArith` fragment: every binding is a binary
    `regArith bop w` over the uniform context, and the program returns a
    register. Stated as a predicate on `Com`. -/
inductive UniformRegArith (w : Nat) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t → Prop where
  | ret {Γ : Ctxt jasminDialect} (v : Ctxt.Var Γ (.reg w)) :
      UniformRegArith w (.ret v)
  | var {Γ : Ctxt jasminDialect} {s : JasminTy} (bop : JasminBinOp)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.regArith bop w)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : UniformRegArith w body) :
      UniformRegArith w (.var ⟨JasminOp.regArith bop w, heq, args⟩ body)

/-! ## 4. `straightOps`: the `.var`-chain of linear instructions

`comToBody nArgs argName _ com curDepth` emits `opToLinstrR e.op (regName curDepth)
srcs :: …` for each binding and a trailing `[⟨0, .Lret⟩]`. The `Lret` is control
flow (out of scope for increment 1's `lsemStep`), so the simulation runs the
`.var`-chain only — exactly `(comToBody …).dropLast`, lifted from `Linstr` to
`LinstrR`. `straightOps` is that chain, defined recursively to match the
induction. -/

/-- The straight-line `LinstrR` chain a `Com` emits (the `comToBody` body with
    the trailing `Lret` dropped, lifted to `LinstrR`). `curDepth` is the SSA depth
    at which the head binding is emitted. -/
def straightOps (nArgs : Nat) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (curDepth : Nat) → List LinstrR
  | _, _, .ret _, _ => []
  | _, _, .var e body, curDepth =>
      opToLinstrR e.op (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none) e)
      :: straightOps nArgs body (curDepth + 1)

/-- `straightOps` is exactly `comToBody`'s body with the trailing `Lret` linstr
    dropped (lifted from `Linstr` to `LinstrR`). The fidelity tie: the simulation
    runs the same instruction list the linearizer emits, minus the control-flow
    terminator. -/
theorem straightOps_eq_body (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (curDepth : Nat) :
    straightOps nArgs com curDepth =
      ((comToBody nArgs argName (fun _ => none) com curDepth).dropLast).map Linstr.li_i := by
  induction com generalizing curDepth with
  | ret v => rfl
  | var e body ih =>
      simp only [straightOps, comToBody]
      rw [List.dropLast_cons_of_ne_nil, List.map_cons]
      · rw [ih]
      · cases body <;> simp [comToBody]

/-! ## 5. The store-agreement invariant

`StoreAgrees nArgs curDepth s V` says the linear store `s` reproduces the
valuation `V` through the linearizer's `resolveVar` naming: every variable `v`
(of type `.reg w`) reads, from `s`, the value `V` assigns it. This is the
linear-store analogue of `JasminPrintSemCorrect.StoreAgrees`, phrased over the
`resolveVar`-naming `comToBody` actually uses (so the linear body reads exactly
what `encode`/the previous bindings wrote). -/

/-- The linear store `s` agrees with valuation `V` at SSA depth `curDepth`:
    every in-scope variable, resolved through the linearizer's `resolveVar`
    naming, reads its `V`-value out of `s`. -/
def StoreAgrees (w nArgs curDepth : Nat) {Γ : Ctxt jasminDialect}
    (s : Lstate w) (V : Ctxt.Valuation Γ) : Prop :=
  ∀ {τ : JasminTy} (v : Ctxt.Var Γ τ) (h : τ = .reg w),
    evalOperand s (resolveVar curDepth nArgs argName (fun _ => none) v) =
      (h ▸ v.lookup V : ⟦(JasminTy.reg w)⟧)

/-- The slot a `.there v` resolves to at depth `curDepth+1` equals the slot `v`
    resolves to at depth `curDepth`: both are `curDepth - 1 - varIndex v`. -/
theorem resolveVar_there {curDepth nArgs : Nat} {Γ : Ctxt jasminDialect}
    {σ τ : JasminTy} (v : Ctxt.Var Γ τ) :
    resolveVar (curDepth + 1) nArgs argName (fun _ => none) (Ctxt.Var.there (s := σ) v) =
      resolveVar curDepth nArgs argName (fun _ => none) v := by
  simp only [resolveVar, varIndex]
  have : curDepth + 1 - 1 - (varIndex v + 1) = curDepth - 1 - varIndex v := by omega
  rw [this]

/-- Writing the fresh register `regName curDepth` does not change how an earlier
    variable (resolved slot `< curDepth`) reads from the store: the destination
    name differs from every earlier register/argument name. -/
theorem evalOperand_setReg_resolveVar {w curDepth nArgs : Nat} {Γ : Ctxt jasminDialect}
    {τ : JasminTy} (v : Ctxt.Var Γ τ) (s : Lstate w) (val : BitVec w)
    (hlt : varIndex v < curDepth) :
    evalOperand (s.setReg (regName curDepth) val)
        (resolveVar curDepth nArgs argName (fun _ => none) v) =
      evalOperand s (resolveVar curDepth nArgs argName (fun _ => none) v) := by
  simp only [resolveVar]
  set slot := curDepth - 1 - varIndex v with hslot
  have hslt : slot < curDepth := by omega
  by_cases hsa : slot < nArgs
  · simp only [hsa, if_true]
    simp only [evalOperand, Lstate.setReg]
    rw [if_neg]
    exact fun he => (regName_ne_argName curDepth slot) he.symm
  · simp only [hsa, if_false]
    simp only [evalOperand, Lstate.setReg]
    rw [if_neg]
    exact fun he => (regName_ne (by omega)) he.symm

/-- `evalOperand` ignores the program counter. -/
@[simp] theorem evalOperand_nextPc {w : Nat} (s : Lstate w) (o : LOperand) :
    evalOperand s.nextPc o = evalOperand s o := by cases o <;> rfl

/-- **Invariant preservation.** Writing the new binding's value `val` to
    `regName curDepth` and advancing the pc preserves `StoreAgrees`, extending the
    valuation with `val` at depth `curDepth + 1`. This is the linear-store
    analogue of `seedStore`/`execCom`'s store-update step. -/
theorem StoreAgrees.step {w nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : Lstate w} {V : Ctxt.Valuation Γ} (val : BitVec w)
    (hlen : Γ.length = curDepth) (harg : nArgs ≤ curDepth)
    (hagree : StoreAgrees w nArgs curDepth s V) :
    StoreAgrees w nArgs (curDepth + 1)
      ((s.setReg (regName curDepth) val).nextPc)
      (V.extend (Γ := Γ) (t := .reg w) val) := by
  intro τ v h
  cases v with
  | here =>
      -- `.here` resolves to slot `curDepth`, name `regName curDepth`; reads `val`.
      simp only [resolveVar, varIndex, evalOperand_nextPc]
      have hslot : curDepth + 1 - 1 - 0 = curDepth := by omega
      rw [hslot]
      have hsa : ¬ curDepth < nArgs := by omega
      simp only [hsa, if_false, evalOperand, Lstate.setReg]
      -- RHS: `(.here).lookup (V.extend val) = val`.
      rfl
  | there v' =>
      -- `.there v'` resolves the same as `v'` at `curDepth`; the new write is
      -- on a strictly-later register, so it does not disturb `v'`.
      rw [resolveVar_there, evalOperand_nextPc]
      have hlt : varIndex v' < curDepth := by
        have := varIndex_lt v'; omega
      rw [evalOperand_setReg_resolveVar v' s val hlt]
      exact hagree v' h

/-! ## 6. Per-op agreement

Each `regArith bop w` binding lowers to `Lopn [.reg dst] (withWidthTag w
(binOpName bop)) srcs`, and `lsemStep` evaluates `applyOpn (stripWidthTag …)`.
The width tag round-trips (`stripWidthTag_withWidthTag_binOpName`) and `applyOpn`
agrees with the dialect binop (`applyOpn_binOpName`), so the linear step computes
exactly the dialect denotation of the binding. -/

/-- The width tag round-trips on a binop mnemonic: `lsemStep` recovers the base
    opcode `binOpName bop` from the tagged mnemonic `comToBody` emits. Proved by
    kernel evaluation of the concrete `String.endsWith` per opcode (axiom-clean;
    `String.endsWith` is `Slice`-based and does not reduce by plain `rfl`). -/
theorem stripWidthTag_withWidthTag_binOpName (w : Nat) (bop : JasminBinOp) :
    stripWidthTag (withWidthTag w (binOpName bop)) = binOpName bop := by
  unfold withWidthTag
  split <;> cases bop <;> decide +kernel

/-! ## 7. The core straight-line simulation

Running the `.var`-chain `straightOps` of a uniform `regArith` `Com` from any
store that agrees with the valuation reaches a store whose final binding register
holds `Com.denote com V`, and which still agrees with the full
binding-extended valuation. Proved by induction on the `UniformRegArith`
derivation, peeling one binding (one `lsemStep`) at a time and applying
`StoreAgrees.step`. -/

/-- The per-binding step: a uniform `regArith` binding `lsemStep`s, from a store
    agreeing with `V`, to the state that writes `e.denote V` to `regName curDepth`
    and advances the pc. This is the `Lopn` arm of `eval_instr` computing exactly
    the dialect denotation of the binding. -/
theorem lsemStep_var {w nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : Lstate w}
    (bop : JasminBinOp)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.regArith bop w)))
    (hagree : StoreAgrees w nArgs curDepth st V) :
    lsemStep
        (opToLinstrR (JasminOp.regArith bop w) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.regArith bop w, heq, args⟩ : Expr jasminDialect Γ (.reg w))))
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.regArith bop w, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  -- `args = [arg0, arg1]` over `sig (regArith bop w) = [reg w, reg w]`.
  match args with
  | .cons a0 (.cons a1 .nil) =>
    have hargs : exprArgs curDepth nArgs argName (fun _ => none)
        (⟨JasminOp.regArith bop w, heq, .cons a0 (.cons a1 .nil)⟩ : Expr jasminDialect Γ (.reg w))
        = [resolveVar curDepth nArgs argName (fun _ => none) a0,
           resolveVar curDepth nArgs argName (fun _ => none) a1] := rfl
    simp only [opToLinstrR, hargs]
    rw [lsemStep_reg_cons2 (regName curDepth) (withWidthTag w (binOpName bop))
        (resolveVar curDepth nArgs argName (fun _ => none) a0)
        (resolveVar curDepth nArgs argName (fun _ => none) a1) st
        (fun base idx scale =>
          resolveVar_ne_arrIdx curDepth nArgs argName (fun _ => none) a0 base idx scale)]
    simp only [stripWidthTag_withWidthTag_binOpName]
    rw [hagree a0 rfl, hagree a1 rfl, applyOpn_binOpName]
    -- LHS reduces to `some (st.setReg … (bop.apply a b)).nextPc`, which is the
    -- RHS since `e.denote V = bop.apply (a0.lookup V) (a1.lookup V)` (defeq).
    rfl

/-- A uniform-`regArith` program returns a register: its result type is `.reg w`. -/
theorem UniformRegArith.ret_ty {w : Nat} {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : UniformRegArith w com) : t = .reg w := by
  induction hcom with
  | ret v => rfl
  | var _ _ _ _ ih => exact ih

/-- **Core simulation (parametrized by an agreeing start state).** From any store
    `s` agreeing with `V` at depth `curDepth` (with `Γ.length = curDepth`,
    `nArgs ≤ curDepth`), `lsemStraight (straightOps nArgs com curDepth) s`
    succeeds, lands in a store agreeing with the binding-extended valuation, and
    reads `Com.denote com V` at the return register
    `comRetReg nArgs argName com curDepth`. -/
theorem lsemStraight_straightOps {w : Nat} {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : UniformRegArith w com) :
    ∀ {nArgs curDepth : Nat} {st : Lstate w} {V : Ctxt.Valuation Γ},
      Γ.length = curDepth → nArgs ≤ curDepth →
      StoreAgrees w nArgs curDepth st V →
      ∃ st', lsemStraight (straightOps nArgs com curDepth) st = some st' ∧
        evalOperand st' (.reg (comRetReg nArgs argName com curDepth)) =
          (hcom.ret_ty ▸ com.denote V : ⟦(JasminTy.reg w)⟧) := by
  induction hcom with
  | ret v =>
      intro nArgs curDepth st V hlen harg hagree
      refine ⟨st, rfl, ?_⟩
      have key : resolveVar curDepth nArgs argName (fun _ => none) v
          = LOperand.reg (comRetReg nArgs argName (Com.ret v) curDepth) := by
        simp only [comRetReg, resolveVar]
        split <;> rfl
      rw [← key]; exact hagree v rfl
  | var bop heq args hbody ih =>
      intro nArgs curDepth st V hlen harg hagree
      -- the value the head binding writes
      set val : BitVec w :=
        (⟨JasminOp.regArith bop w, heq, args⟩ : Expr jasminDialect _ (.reg w)).denote V with hval
      -- step the head binding
      have hstep := lsemStep_var (V := V) (st := st) (nArgs := nArgs) (curDepth := curDepth)
        bop heq args hagree
      -- the stepped state still agrees, one depth deeper, with the extended valuation
      have hagree' : StoreAgrees w nArgs (curDepth + 1)
          ((st.setReg (regName curDepth) val).nextPc) (V.extend (t := JasminTy.reg w) val) :=
        StoreAgrees.step val hlen harg hagree
      obtain ⟨st', hrun, hret⟩ :=
        ih (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · -- the linear run: step the head, then run the body chain
        simp only [straightOps, lsemStraight_cons, hstep]
        exact hrun
      · -- the return register read agrees with the denotation
        simp only [comRetReg]
        rw [hret]
        rfl

/-! ## 8. `encode`/`decode` and the top-level faithfulness statement

`encode` places the argument valuation into the linear store under the
linearizer's `argName` naming (`argName j` for argument slot `j`, program-root
order). Argument slot `j` is entry `Γ.length - 1 - j` of `Γ` (most-recent-first);
equivalently, the de Bruijn-`i` argument lands at `argName (Γ.length - 1 - i)`,
exactly the slot `resolveVar` reads at the start depth `curDepth = Γ.length`. -/

/-- Encode a valuation into a linear store, placing the value at de Bruijn index
    `i` (counted from the head of `Γ`) at `argName (Γ.length - 1 - i)` — the
    argument register `comToBody` reads it from at the start depth `Γ.length`.
    Modeled at uniform width `w`; non-`reg w` heads (never occur under
    `UniformCtxt`) are skipped. -/
def encodeAux {w : Nat} : {Γ : Ctxt jasminDialect} → Ctxt.Valuation Γ → Lstate w → Lstate w
  | [], _, st => st
  | (.reg w') :: rest, .cons hd tl, st =>
      let st' := encodeAux tl st
      if h : w' = w then st'.setReg (argName rest.length) (h ▸ hd : ⟦(JasminTy.reg w)⟧) else st'
  | _ :: _, .cons _ tl, st => encodeAux tl st

/-- The canonical encoding of an argument valuation into a fresh linear store:
    `argName j ↦ V[j]` (slot 0 = root-first argument), `0` elsewhere. -/
def encode {w : Nat} {Γ : Ctxt jasminDialect} (V : Ctxt.Valuation Γ) : Lstate w :=
  encodeAux V { lvm := fun _ => 0 }

/-- Decode the result register from a linear store: read `obsName` out of `lvm`.
    Paired with `comRetReg` (the function's `lfd_res` name), this reads the value
    the straight-line body computed into its result register. -/
def decode {w : Nat} (st : Lstate w) (obsName : String) : BitVec w := st.lvm obsName

/-- `decode` of a state at the return register is `evalOperand` of that register. -/
theorem decode_eq_evalOperand {w : Nat} (st : Lstate w) (obsName : String) :
    decode st obsName = evalOperand st (.reg obsName) := rfl

/-- `encodeAux` reads back each variable at its `argName` slot: the value at de
    Bruijn index `varIndex v` is stored at `argName (Γ.length - 1 - varIndex v)`.
    Holds under context uniformity (every var is `.reg w`). -/
theorem encodeAux_lookup {w : Nat} {Γ : Ctxt jasminDialect} (hu : UniformCtxt w Γ)
    (V : Ctxt.Valuation Γ) (st : Lstate w) {τ : JasminTy} (v : Ctxt.Var Γ τ)
    (h : τ = .reg w) :
    (encodeAux V st).lvm (argName (Γ.length - 1 - varIndex v)) =
      (h ▸ v.lookup V : ⟦(JasminTy.reg w)⟧) := by
  induction v with
  | here =>
      -- `Γ = .reg w :: rest`; `varIndex = 0`, target `argName rest.length`.
      rename_i Γ' σ
      have hσ : σ = .reg w := h
      subst hσ
      cases V with
      | cons hd tl =>
        rw [show encodeAux (w := w) (HVector.cons hd tl) st
              = if h : w = w then (encodeAux tl st).setReg (argName Γ'.length)
                  (h ▸ hd : ⟦(JasminTy.reg w)⟧) else (encodeAux tl st) from rfl]
        simp only [List.length_cons, varIndex, dif_pos, Lstate.lvm_setReg]
        rw [if_pos (by congr 1)]
        rfl
  | there v' ih =>
      rename_i Γ' σ ρ
      have hσ : ρ = .reg w := hu (Ctxt.Var.here)
      subst hσ
      cases V with
      | cons hd tl =>
        have hut : UniformCtxt w Γ' := fun {τ} x => hu (Ctxt.Var.there x)
        rw [show encodeAux (w := w) (HVector.cons hd tl) st
              = if h : w = w then (encodeAux tl st).setReg (argName Γ'.length)
                  (h ▸ hd : ⟦(JasminTy.reg w)⟧) else (encodeAux tl st) from rfl]
        simp only [List.length_cons, varIndex, dif_pos, Lstate.lvm_setReg]
        rw [if_neg]
        · -- reduces to the tail lookup
          have htail := ih hut tl h
          have heq2 : Γ'.length + 1 - 1 - (varIndex v' + 1) = Γ'.length - 1 - varIndex v' := by omega
          rw [heq2]
          exact htail
        · -- target slot ≠ the written slot `argName Γ'.length`
          have hlt : varIndex v' < Γ'.length := varIndex_lt v'
          exact argName_ne (by omega)

/-- **`encode` establishes the start-state agreement.** The encoded store agrees
    with the valuation at the start depth `curDepth = nArgs = Γ.length`: every
    variable, resolved at that depth (always to an `argName` slot), reads its
    `V`-value out of `encode V`. The base case of the simulation induction. -/
theorem encode_StoreAgrees {w : Nat} {Γ : Ctxt jasminDialect}
    (hu : UniformCtxt w Γ) (V : Ctxt.Valuation Γ) :
    StoreAgrees w Γ.length Γ.length (encode V) V := by
  intro τ v h
  -- at `curDepth = Γ.length`, the resolved slot is `< Γ.length`, so it is an arg.
  have hslot : Γ.length - 1 - varIndex v < Γ.length := by
    have := varIndex_lt v; omega
  simp only [resolveVar, hslot, if_true, evalOperand, encode]
  -- the immSlotMap is `none`, so the operand is `.reg (argName slot)`
  exact encodeAux_lookup hu V _ v h

/-! ## 9. The straight-line faithfulness theorem

The content of `ComLsemExportFaithful` (`LsemPortAll`) for the
straight-line uniform-`regArith` fragment: running the linearizer's emitted
`.var`-chain on the encoded inputs, then decoding the result register, recovers
exactly the source program's denotation. -/

/-- **Straight-line linearizer simulation.** For a uniform-width `regArith`
    straight-line `Com`, decoding the result register after running the linear
    `.var`-chain `comToBody` emits — started from the encoded argument valuation —
    equals the source program's `Com.denote`. This is the simulation that
    discharges `ComLsemExportFaithful` for the straight-line fragment. -/
theorem comToLprog_lsem_straightline {w : Nat} {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : UniformRegArith w com)
    (hu : UniformCtxt w Γ) (V : Ctxt.Valuation Γ) :
    ∃ st', lsemStraight (straightOps Γ.length com Γ.length) (encode V) = some st' ∧
      decode st' (comRetReg Γ.length argName com Γ.length) =
        (hcom.ret_ty ▸ com.denote V : ⟦(JasminTy.reg w)⟧) := by
  obtain ⟨st', hrun, hret⟩ :=
    lsemStraight_straightOps hcom (nArgs := Γ.length) (curDepth := Γ.length)
      (st := encode V) (V := V) rfl le_rfl (encode_StoreAgrees hu V)
  exact ⟨st', hrun, by rw [decode_eq_evalOperand]; exact hret⟩

/-- **Faithfulness (packaged).** The straight-line fragment's faithfulness fact:
    the linearizer-emitted straight-line body, run on the encoded inputs and
    decoded at the result register, is *equal* to the source denotation. This is
    the semantic-preservation statement of `ComLsemExportFaithful` on the
    straight-line uniform-`regArith` fragment. -/
theorem comToLprog_faithful_straightline {w : Nat} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {com : Com jasminDialect Γ t} (hcom : UniformRegArith w com)
    (hu : UniformCtxt w Γ) (V : Ctxt.Valuation Γ) :
    (lsemStraight (straightOps Γ.length com Γ.length) (encode V)).map
        (fun st' => decode st' (comRetReg Γ.length argName com Γ.length)) =
      some (hcom.ret_ty ▸ com.denote V : ⟦(JasminTy.reg w)⟧) := by
  obtain ⟨st', hrun, hdec⟩ := comToLprog_lsem_straightline hcom hu V
  rw [hrun, Option.map_some, hdec]

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation
