/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.ImpToNF

/-!
# The lowering of `NFProg nfDialect` to `LowCT`

`nfToLowCT A R p ρ` lowers a one-result program `p` of `NFProg nfDialect` to a `LowCT` command
under the placement `A` and the result placement `R`, from the reading `ρ` of its context.
The variables of `p` are held in source names: a binding named by `NfOp.named` in its name,
an unnamed call in a fresh temporary (`tmpName`), and a literal, a tuple and a trip count are
read without a slot (`RB`, as for the readback `nfToImp`).

Each binding is lowered by the statement lowering `letHeadT A` of the typed exit front, on
the right-hand side of atoms the reading gives, when the exit fragment `exitSimOkT` accepts
the binding. A counted loop whose body starts with a named counter `i` is a `RForRuntime`
over a fresh trip index `t` whose bound is the trip count, with `i` set to `t + lo` at the
head of each trip; its carried values are held in the names of its initial atoms and
written back at the end of the body. The result is stored by `resultStoreT A`.

The lowering makes three choices that a lowering of the exit front's output makes by passes.
It emits no exit frame: there is no exit flag, payload slot or flag test, since a program of
`NFProg` has no early exit. It emits no zero initialisation of a scalar slot: the first write
to each slot is its binding or the counter assignment. It binds no literal: a literal is read
as an immediate operand of the commands that use it.

## Main definitions

* `nfHead` — the head of one binding, accepted by `exitSimOkT`.
* `nfAssigns` — the write-back of the carried names of a loop body.
* `atomSE` — the scalar expression of an atom.
* `LK`, `nfLow` — the continuation at a return, and the lowering with its fresh temporaries
  and the names it writes.
* `nfToLowCT` — the lowering of a one-result program.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax.NFToLowCT

open _root_.Hax (ImpExpr ImpLit)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.Hax.ImpToNF
open Ctxt (Var)

/-- The head of the binding of the name `n` to `rhs`: the statement lowering `letHeadT A n rhs`
    of the typed exit front, when the exit fragment `exitSimOkT A R` accepts the binding
    before `unitVal`. -/
def nfHead (A : ExitTowers) (R : ExitRes) (n : String) (rhs : ImpExpr) :
    Option (LowCT → LowCT) :=
  if exitSimOkT A R false false (.letBind n rhs .unitVal) then letHeadT A n rhs else none

/-- The write-back of the values of the atoms `as` to the carried names `ns`, as one binding
    of each name to its atom by `nfHead`; a name whose atom is itself is left out. `none`
    when a later atom reads a name an earlier write-back writes. -/
def nfAssigns (A : ExitTowers) (R : ExitRes) : List String → List ImpExpr → Option LowCT
  | [], [] => some .RSkip
  | n :: ns, a :: as =>
      if isVarOf n a then nfAssigns A R ns as
      else if as.any (isVarOf n) then none
      else (nfHead A R n a).bind fun h => (nfAssigns A R ns as).map h
  | _, _ => none

/-- The scalar expression of an atom: a variable, or a non-negative integer or unsigned
    literal. -/
def atomSE : ImpExpr → Option SExpr
  | .var x => some (.SVar x)
  | .lit (.int k) => if 0 ≤ k then some (.SLit k.toNat) else none
  | .lit (.uintLit _ k) => some (.SLit k)
  | _ => none

/-- The continuation of the lowering at a return: from the reading of the context and the
    returned variables, the command ending the program and the next fresh temporary. -/
abbrev LK (ts : List NfTy) : Type :=
  ∀ {Δ : Ctxt nfDialect}, RBEnv Δ → HVector (fun t => Var Δ t) ts → Nat →
    Option (LowCT × Nat)

/-- **The lowering** of an `NFProg` program from the reading `ρ` of its context, with the
    fresh temporaries from `c` and the continuation `lk` at its return. Its value is the
    command, the next fresh temporary and the names the command writes outside the
    continuation. A named binding is a head of its name, an unnamed call a head of a fresh
    temporary, and a literal, a unit, a tuple and a trip count are read without a slot. A
    counted loop whose count reads as a trip count and whose body starts with a named `ctr`
    is a `RForRuntime` over a fresh trip index, its carried values held in the names of its
    initial atoms and written back by `nfAssigns` at the end of the body; it is lowered only
    when it writes no name the reading of the context still reads. -/
def nfLow (A : ExitTowers) (R : ExitRes) :
    {Γ : Ctxt nfDialect} → {ts : List NfTy} → NFProg nfDialect Γ ts → RBEnv Γ →
    Nat → LK ts → Option (LowCT × Nat × List String)
  | _, _, .ret vs, ρ, c, lk => (lk ρ vs c).map fun r => (r.1, r.2, [])
  | _, _, .var e k, ρ, c, lk =>
      (rbBind ρ c e.op e.args).bind fun b =>
        match b with
        | .emit n rhs tmp =>
            (nfHead A R n rhs).bind fun h =>
              (nfLow A R k (RBEnv.cons (.name n) (ρ.clobber [n]))
                (if tmp then c + 1 else c) lk).map fun r => (h r.1, r.2.1, n :: r.2.2)
        | .inline r => nfLow A R k (RBEnv.cons r ρ) c lk
  | _, _, .forLoop (cs := cs) count inits body k, ρ, c, lk =>
      match body with
      | .var e rest =>
        (ctrOf? e.op e.args).bind fun ⟨i, a, b⟩ =>
          match ρ count with
          | .trip lo hi =>
            (atomSE hi).bind fun hiSE =>
            (rbAtoms ρ inits).bind fun xs => (namesOf xs).bind fun cn =>
              if cn.Nodup then
                let ρΓ : RBEnv _ := RBEnv.clobber cn ρ
                let ρB : RBEnv (cs ++ NfTy.word 64 :: _) :=
                  RBEnv.appNames cs cn (RBEnv.cons .idx (RBEnv.dropIdx ρΓ))
                match ρB a, ρB b with
                | .lit (.int lo'), .idx =>
                    if lo' = lo ∧ 0 ≤ lo then
                      let t := tmpName c
                      (nfLow A R rest (RBEnv.cons (.name i) (ρB.clobber [i])) (c + 1)
                          (fun ρ' vs c' => (rbAtoms ρ' vs).bind fun as =>
                            (nfAssigns A R cn as).map (·, c'))).bind fun bc =>
                        let wr := t :: i :: bc.2.2
                        if (RBEnv.allNames ρΓ).all fun n => !wr.contains n then
                          let loopC : LowCT :=
                            .RForRuntime t (.SSub hiSE (.SLit lo.toNat))
                              (.RSeq (.RScalarSetExpr i (.SAdd (.SVar t) (.SLit lo.toNat)))
                                bc.1)
                          (nfLow A R k (RBEnv.appNames cs cn ρΓ) bc.2.1 lk).map fun r =>
                            (.RSeq loopC r.1, r.2.1, wr ++ cn ++ r.2.2)
                        else none
                    else none
                | _, _ => none
              else none
          | _ => none
      | _ => none
  | _, _, .ifThenElse .., _, _, _ => none
  | _, _, .whileLoop .., _, _, _ => none

/-- **The lowering of a one-result program**: `nfLow` with the result read as an atom or a
    tuple and stored by `resultStoreT A`. -/
def nfToLowCT (A : ExitTowers) (R : ExitRes) {Γ : Ctxt nfDialect} {t : NfTy}
    (p : NFProg nfDialect Γ [t]) (ρ : RBEnv Γ) : Option LowCT :=
  (nfLow A R p ρ 0 fun ρ' vs c => match vs with
    | .cons v .nil => ((ρ' v).expr?.bind (resultStoreT A)).map (·, c)).map (·.1)

end CatCrypt.Crypto.Hax.NFToLowCT
