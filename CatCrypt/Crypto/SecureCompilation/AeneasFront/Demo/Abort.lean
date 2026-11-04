/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Reify
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.TestJoins
public import CatCrypt.Crypto.SecureCompilation.Haxc.ExtChain

/-!
# An Aeneas assertion read as an abort and eliminated

The Aeneas test function `joins.opt_add_1_or_panic` (`TestJoins`, copied unchanged from Aeneas
commit `b08bf81`) asserts its Boolean argument `b` with `massert b` and returns `x + 1`.
The Boolean argument `b` is the word `boolW b` of the layout, whose bit is bound first
(`Reify.argBit`). `reifyAeneas%` reads the assertion as the guard `Reify.assert`: the bit of
`b` (`readBit`) and its negation are bound, the negation is branched on, to the aborting arm
`abortArm` or to the empty return, and the continuation reads `x + 1`. The elimination of
aborting branches, the first step of the chain `extChain`, replaces the branch by its
continuation (`abortElim_guard`), and keeps every value of the program
(`NFProg.denote_abortElim` with `nfDenote_isAbort`).

## Main results

* `abortElim_guard` — the elimination replaces a guard of the reader by its continuation.
* `optAdd_denote` — a value of `joins.opt_add_1_or_panic` is the denotation of its NF program.
* `optAdd_abortElim_denote` — it is also the denotation of the program after the elimination.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo

open Aeneas.Std
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.AeneasFront
open CatCrypt.Crypto.SecureCompilation.Haxc (nfDenote_isAbort)
open CatCrypt.Crypto.Hax (hax64WExit)
open CatCrypt.Crypto.Hax.ImpToNF (PDenP tableOf)
open Ctxt (Var Valuation)

/-- **The elimination replaces a guard of the reader by its continuation**: the branch to the
    aborting arm `abortArm` and the empty return, after the binding of its bit, is eliminated,
    and the binding of the bit is kept. -/
theorem abortElim_guard {Γ : Ctxt nfDialect} {ts : List NfTy} (e : Expr nfDialect Γ .bit)
    (pk : NFProg nfDialect (.bit :: Γ) ts) :
    NFProg.abortElim NfOp.isAbort (.var e (.ifThenElse .here abortArm (.ret .nil) pk)) =
      .var e (NFProg.abortElim NfOp.isAbort pk) := by
  rw [NFProg.abortElim, NFProg.abortElim, abortArm, NFProg.abortElim, NFProg.abortElim,
    NFProg.abortElim, NFProg.iteElim]
  rfl

/-- `joins.opt_add_1_or_panic` read as an NF program. -/
def optAdd := reifyAeneas% joins.opt_add_1_or_panic

/-- A value of `joins.opt_add_1_or_panic` is the denotation of its NF program in the compiler's
    semantics. -/
theorem optAdd_denote (b : Bool) (x z : U32) (h : joins.opt_add_1_or_panic b x = .ok z) :
    ∃ N, ∀ fuel, N ≤ fuel → PDenP hax64WExit fuel optAdd.prog (wCons b (vCons x vNil)) =
      some (.cons (embW z) .nil) :=
  Reify.toDenote (optAdd.sound b x) h

/-- **A value of `joins.opt_add_1_or_panic` is the denotation of its NF program after the
    elimination of aborting branches**: `optAdd_denote` composed with
    `NFProg.denote_abortElim`. -/
theorem optAdd_abortElim_denote (b : Bool) (x z : U32)
    (h : joins.opt_add_1_or_panic b x = .ok z) :
    ∃ N, ∀ fuel, N ≤ fuel →
      PDenP hax64WExit fuel (NFProg.abortElim NfOp.isAbort optAdd.prog)
        (wCons b (vCons x vNil)) = some (.cons (embW z) .nil) := by
  obtain ⟨N, hN⟩ := optAdd_denote b x z h
  exact ⟨N, fun fuel hf =>
    @NFProg.denote_abortElim nfDialect _ _ _ _ NfOp.isAbort (nfDenote (tableOf hax64WExit)) _
      (fun e V h => nfDenote_isAbort (tableOf hax64WExit) e V h) _ _ optAdd.prog fuel _ _
      (hN fuel hf)⟩

end CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo
