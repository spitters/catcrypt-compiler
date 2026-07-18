/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-!
# Validate: the multi-accumulator block loop (`ComL.forLoopMultiAcc`, task #20)

Every single-`accTy` loop node (`forLoop*`, `whileNz`, `forLoopBlock`) carries
**one** accumulator across the back-edge. Imperative kernels (MAYO/SolveGf16's
Gf16 solve threads `i, j, acc, prow, pivot, …` — ~20 mutable scalars — across a
3-deep loop nest) need **several** loop-carried mutable scalars. `forLoopBlock`'s
single `accTy` cannot hold them.

`ComL.forLoopMultiAcc` (`JasminLprogExport`) closes that gap **without a new
constructor and without a `JasminTy.prod`**: the `N` accumulators are the `N`
cells of the product type the dialect already has, `stackArr w N`
(`⟦stackArr w N⟧ = Fin N → BitVec w`). It is `forLoopBlock` at
`accTy = stackArr w N`; the recursive block body reads any cell (`stackLoad`),
updates it, and `stackStore`s it back (the functional `stackStore` returns the
whole updated array), so all `N` cells are loop-carried through the one
`forLoopBlock` back-edge, each in its own frame slot.

This file demonstrates a **3-accumulator** kernel

    for t = 0 .. count-1 {
      acc1 := acc1 + acc2
      acc2 := acc2 * t          -- t = the loop index
      acc3 := acc3 ^ acc1       -- the just-updated acc1
    }

as a `forLoopMultiAcc` over `stackArr 64 3`, and shows:

* **denote = spec** — seed `(1, 2, 3)`, `count = 3` folds to `(3, 0, 0)`
  (`rfl`), per cell;
* **the rendered back-edge threads all 3 scalars** — 3 `LOADIDX`, 3 `STOREIDX`,
  the whole-array feedback `MOV`, and exactly **one** `Lcond NZ` back-edge;
* **the physical export is well-formed** — every operand (array base, index and
  value registers included) is a real x86 GP register, the body ends `Lret`, and
  there is exactly one back-edge.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. The 3-accumulator loop body over a `stackArr 64 3` product -/

/-- One iteration of the 3-accumulator kernel over the context
    `[acc : stackArr 64 3, idx : reg 64]` (invTys = `[]`): materialise the three
    cell indices `0,1,2`; read `a1=acc[0], a2=acc[1], a3=acc[2]`; compute
    `na1=a1+a2`, `na2=a2*idx`, `na3=a3^na1`; store all three back; return the
    updated array. Every cross-accumulator dependency (`na3` reads the fresh
    `na1`; `na2` reads the index) is threaded through the product accumulator. -/
def triAccBody : ComL [JasminTy.stackArr 64 3, JasminTy.reg 64] (.stackArr 64 3) :=
  .var (.mk (.regConst 64 0) rfl .nil)
  (.var (.mk (.regConst 64 1) rfl .nil)
  (.var (.mk (.regConst 64 2) rfl .nil)
  (.var (.mk (.stackLoad 64 3) rfl
      (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) .nil)))
  (.var (.mk (.stackLoad 64 3) rfl
      (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there .here)) .nil)))
  (.var (.mk (.stackLoad 64 3) rfl
      (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there .here)) .nil)))
  (.var (.mk (.regArith .add 64) rfl (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
  (.var (.mk (.regArith .mul 64) rfl
      (.cons (.there (.there .here))
        (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil)))
  (.var (.mk (.regArith .xor 64) rfl (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
  (.var (.mk (.stackStore 64 3) rfl
      (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
        (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
          (.cons (.there (.there .here)) .nil))))
  (.var (.mk (.stackStore 64 3) rfl
      (.cons .here
        (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
          (.cons (.there (.there .here)) .nil))))
  (.var (.mk (.stackStore 64 3) rfl
      (.cons .here
        (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
          (.cons (.there (.there .here)) .nil))))
  (.ret .here))))))))))))

/-- The 3-accumulator program: over args `[acc0 : stackArr 64 3, cnt : reg 64]`,
    run `triAccBody` `cnt` times (seeded from `acc0`), then read cell `cell` of
    the final array. `count = .there .here`, `init = .here`, no invariants. Built
    with the `ComL.forLoopMultiAcc` node. -/
def triAccProg (cell : Nat) : ComL [JasminTy.stackArr 64 3, JasminTy.reg 64] (.reg 64) :=
  ComL.forLoopMultiAcc triAccBody (.there .here) .here .nil
    (.var (.mk (.regConst 64 cell) rfl .nil)
     (.var (.mk (.stackLoad 64 3) rfl (.cons (.there .here) (.cons .here .nil)))
      (.ret .here)))

/-- The seed state `(acc1, acc2, acc3) = (1, 2, 3)` as a `stackArr 64 3` value. -/
def triSeed : Fin 3 → BitVec 64 := fun i => if i.val = 0 then 1 else if i.val = 1 then 2 else 3

/-! ## 2. Denote = spec (the 3-fold over the 3-cell state)

Seed `(1,2,3)`, `count = 3`. Trace (index `t = 0,1,2`):

* `t=0`: `na1=1+2=3, na2=2·0=0, na3=3^3=0` → `(3,0,0)`
* `t=1`: `na1=3+0=3, na2=0·1=0, na3=0^3=3` → `(3,0,3)`
* `t=2`: `na1=3+0=3, na2=0·2=0, na3=3^3=0` → `(3,0,0)`

Final state `(3, 0, 0)`; we project each cell. -/

/-- **Denote = spec, cell 0 (`acc1`):** `3`. -/
theorem triAccProg_denote_cell0 :
    ComL.denote (triAccProg 0) (.cons triSeed (.cons (3 : BitVec 64) .nil)) = (3 : BitVec 64) := by
  rfl

/-- **Denote = spec, cell 1 (`acc2`):** `0`. -/
theorem triAccProg_denote_cell1 :
    ComL.denote (triAccProg 1) (.cons triSeed (.cons (3 : BitVec 64) .nil)) = (0 : BitVec 64) := by
  rfl

/-- **Denote = spec, cell 2 (`acc3`):** `0`. -/
theorem triAccProg_denote_cell2 :
    ComL.denote (triAccProg 2) (.cons triSeed (.cons (3 : BitVec 64) .nil)) = (0 : BitVec 64) := by
  rfl

/-! ## 3. The rendered back-edge threads all 3 scalars

The lowered loop body carries three `LOADIDX base[idx*8]` cell reads, three
`STOREIDX base[idx*8], val` cell writes (the array base renamed at each
functional `stackStore`), the whole-array feedback `MOV accReg, retReg`, and
exactly **one** `Lcond NZ` back-edge. -/

/-- The lowered body of the 3-accumulator program. -/
def triAccLowered : Lcmd := comLToBody 2 argName (fun _ => none) (triAccProg 0) 2

/-- **Three cell reads:** the body issues exactly three `LOADIDX` (SIB) loads
    inside the loop — one per accumulator cell (`acc[0]`, `acc[1]`, `acc[2]`).
    (Plus the single post-loop read of the returned cell, hence 4 in total.) -/
theorem triAcc_three_cell_reads :
    (triAccLowered.filter (fun i =>
      match i.li_i with
      | .Lopn _ mn _ => mn == "LOADIDX"
      | _ => false)).length = 4 := by native_decide

/-- **Three cell writes:** the body issues exactly three `STOREIDX` (SIB) stores
    per iteration — one per accumulator cell. This is the multi-accumulator
    write-back that a single-`accTy` loop cannot emit. -/
theorem triAcc_three_cell_writes :
    (triAccLowered.filter (fun i =>
      match i.li_i with
      | .Lopn _ mn _ => mn == "STOREIDX"
      | _ => false)).length = 3 := by native_decide

/-- **One back-edge:** exactly one `Lcond NZ` conditional jump — the single loop
    back-edge threading the whole 3-cell array. -/
theorem triAcc_one_backedge :
    (triAccLowered.filter (fun i =>
      match i.li_i with | .Lcond (.reg "NZ") _ => true | _ => false)).length = 1 := by
  native_decide

/-- The lowered body ends with `Lret`. -/
theorem triAcc_ends_Lret :
    triAccLowered.getLast?.map Linstr.li_i = some .Lret := by
  simpa [triAccLowered] using
    comLToBody_ends_Lret 2 argName (fun _ => none) (triAccProg 0) 2

/-! ## 4. The physical export is well-formed

The whole program survives the SSA → physical linear-scan register allocation:
every operand — the array base, the SIB index and the stored value included
(via `LOperand.srcRegNames` / `regName?`, which surface the `arrIdx` base+index)
— is a real x86 GP register, the body ends `Lret`, and there is one back-edge. -/

/-- The physical export's body. -/
def triAccPhysBody : Lcmd := (ComL.toLfundefPhys (triAccProg 0)).lfd_body

/-- **All real registers.** Every `Lopn` destination and every source register
    name — the `LOADIDX`/`STOREIDX` array-base pointer and index registers
    included — is a real x86 GP register (no leftover SSA `rN` / `LN_rk` /
    argument name). -/
theorem triAccPhys_all_real_registers :
    (bodyOpNames triAccPhysBody).all (fun p =>
      (p.1.map isRealGPName).getD true && p.2.all isRealGPName) = true := by
  native_decide

/-- **Physical export: one back-edge.** The register-allocated body keeps exactly
    one `Lcond NZ` back-edge (the RA does not duplicate or drop the loop). -/
theorem triAccPhys_one_backedge :
    (triAccPhysBody.filter (fun i =>
      match i.li_i with | .Lcond (.reg "NZ") _ => true | _ => false)).length = 1 := by
  native_decide

/-- **Physical export ends `Lret`.** -/
theorem triAccPhys_ends_Lret :
    triAccPhysBody.getLast?.map (fun i => i.li_i.toText) = some "Lret" := by native_decide

/-- **Builds to a single exported well-formed function.** The 3-accumulator
    program exports through `ComL.toLprogPhys` to an `Lprog` with exactly one
    exported function. -/
theorem triAccProg_toLprogPhys_wf :
    (ComL.toLprogPhys (triAccProg 0) "triacc").lp_funcs.length = 1 ∧
      ((ComL.toLprogPhys (triAccProg 0) "triacc").lp_funcs.head?.map (fun p => p.2.lfd_export)
        = some true) := by
  refine ⟨rfl, rfl⟩

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
