/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.JasminComRunBlockSeq

/-!
# The straight-line block tie at the final context

`JasminComRunBlockSeq.lowerBlock_tie` reads one register after `runBlock`: the
one holding the variable the block returns. This module states the
correspondence at the whole final context — after `runBlock` of the lowered
block, *every* slot bound along the block sits in its allocated register and
holds the value the dialect valuation gives it.

## The final context

An `ArithBlock Γ` binds one `reg 64` slot per op, so it ends in a context
`finalCtxB ab` extending `Γ` by one slot per op. `finalNm` and `finalVal`
accumulate the register map and the valuation through those extensions, with the
same three extensions `lowerBlock`, `outReg` and `lowerBlock_tie` use: the
destination `g 0`, the shifted stream, and the op's denotation.

## What is proved

* `lowerBlock_tie_state` — `JStateInterpG (finalNm ab nm g) (finalVal ab V)`
  holds of `runBlock s (lowerBlock ab nm g)`: the state correspondence at the
  final context, for every slot of the block.
* `outVar_lookup_finalVal` — the returned variable's value in the final
  valuation is the program's denotation.
* `outReg_eq_finalNm` / `lowerBlock_tie_of_state` — the output register is the
  final register map at the returned variable, and `lowerBlock_tie` follows from
  the final-state correspondence at that one variable.
* `block2_final_state_slots` — on a concrete allocation, state and valuation,
  both slots of the two-op block `(a + b) * a` are readable: the intermediate
  `a + b` from its own register, and the result from the output register.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-! ## 1. The final context, register map, valuation and output variable -/

/-- **The context a block ends in.** `Γ` extended by one `reg 64` slot per op of
    the block. -/
def finalCtxB : {Γ : Ctxt jasminDialect} → ArithBlock Γ → Ctxt jasminDialect
  | Γ, .ret _ => Γ
  | _, .op _ _ _ _ rest => finalCtxB rest

/-- **The register map at the final context.** The map accumulated by
    `lowerBlock`: each op binds its destination `g 0` to the new slot and shifts
    the fresh stream. -/
def finalNm : {Γ : Ctxt jasminDialect} → (ab : ArithBlock Γ) → RegMapG Γ →
    (Nat → String) → RegMapG (finalCtxB ab)
  | _, .ret _, nm, _ => nm
  | _, .op _ _ _ _ rest, nm, g => finalNm rest (nm.extend (g 0)) (fun k => g (k + 1))

/-- **The valuation at the final context.** The valuation accumulated by
    `ArithBlock.toCom`'s denotation: each op extends with its own denotation. -/
def finalVal : {Γ : Ctxt jasminDialect} → (ab : ArithBlock Γ) →
    Ctxt.Valuation Γ → Ctxt.Valuation (finalCtxB ab)
  | _, .ret _, V => V
  | _, .op bop _ a b rest, V => finalVal rest (V.extend ((arithExpr bop a b).denote V))

/-- **The variable the block returns**, as a variable of the final context: the
    payload of the terminating `.ret`, reached through the op extensions. -/
def outVar : {Γ : Ctxt jasminDialect} → (ab : ArithBlock Γ) →
    Ctxt.Var (finalCtxB ab) (.reg 64)
  | _, .ret v => v
  | _, .op _ _ _ _ rest => outVar rest

/-! ## 2. The tie at the final context -/

/-- **The state correspondence at the final context.** After `runBlock` of the
    whole lowered block, every slot of the final context — every op's result as
    well as every input — sits in the register `finalNm` assigns it and holds the
    value `finalVal` gives it.

    Proven by structural induction on `ArithBlock`, composing the per-op tie
    (`lowerArith2_get_dst`) with its frame (`lowerArith2_get_other`) and carrying
    the fresh allocation through `FreshFor_extend`. -/
theorem lowerBlock_tie_state : {Γ : Ctxt jasminDialect} → (ab : ArithBlock Γ) →
    (nm : RegMapG Γ) → (g : Nat → String) → (s : JState 64) →
    (V : Ctxt.Valuation Γ) → JStateInterpG nm V s → FreshFor nm g →
    JStateInterpG (finalNm ab nm g) (finalVal ab V)
      (runBlock s (lowerBlock ab nm g))
  | _, .ret _, _, _, _, _, hinterp, _ => by
      simpa only [lowerBlock, finalCtxB, finalNm, finalVal, runBlock_nil] using hinterp
  | _, .op bop hbop a b rest, nm, g, s, V, hinterp, hfresh => by
      -- The op's freshly allocated destination `g 0` differs from every old register.
      have hdisj := hfresh.2 0
      -- The correspondence extends to the grown context on the post-op state.
      have hinterp' : JStateInterpG (nm.extend (g 0))
          (V.extend ((arithExpr bop a b).denote V))
          (runBlock s (lowerArith2 bop (nm a) (nm b) (g 0))) := by
        intro w
        match w with
        | .here =>
            show (runBlock s (lowerArith2 bop (nm a) (nm b) (g 0))).get (g 0)
                = bop.apply (a.lookup V) (b.lookup V)
            rw [lowerArith2_get_dst bop hbop (nm a) (nm b) (g 0) (hdisj b) s,
              hinterp a, hinterp b]
        | .there w0 =>
            show (runBlock s (lowerArith2 bop (nm a) (nm b) (g 0))).get (nm w0)
                = w0.lookup V
            rw [lowerArith2_get_other bop hbop (nm a) (nm b) (g 0) (nm w0)
              (fun h => (hdisj w0) h.symm) s]
            exact hinterp w0
      have hfresh' : FreshFor (nm.extend (g 0)) (fun k => g (k + 1)) :=
        FreshFor_extend nm g hfresh
      have key := lowerBlock_tie_state rest (nm.extend (g 0)) (fun k => g (k + 1))
        (runBlock s (lowerArith2 bop (nm a) (nm b) (g 0)))
        (V.extend ((arithExpr bop a b).denote V)) hinterp' hfresh'
      simpa only [lowerBlock, finalCtxB, finalNm, finalVal, runBlock_append] using key

/-! ## 3. The output register as one slot of the final context -/

/-- The block's output register is the final register map read at the returned
    variable. -/
theorem outReg_eq_finalNm : {Γ : Ctxt jasminDialect} → (ab : ArithBlock Γ) →
    (nm : RegMapG Γ) → (g : Nat → String) →
    outReg ab nm g = finalNm ab nm g (outVar ab)
  | _, .ret _, _, _ => rfl
  | _, .op _ _ _ _ rest, nm, g =>
      outReg_eq_finalNm rest (nm.extend (g 0)) (fun k => g (k + 1))

/-- The returned variable's value in the final valuation is the block's
    `Com jasminDialect` denotation. -/
theorem outVar_lookup_finalVal : {Γ : Ctxt jasminDialect} → (ab : ArithBlock Γ) →
    (V : Ctxt.Valuation Γ) → (outVar ab).lookup (finalVal ab V) = ab.toCom.denote V
  | _, .ret _, _ => rfl
  | _, .op bop _ a b rest, V =>
      outVar_lookup_finalVal rest (V.extend ((arithExpr bop a b).denote V))

/-- **The output-register tie as one instance of the final-state tie.** Reading
    the block's output register after `runBlock` yields the program's
    denotation — `lowerBlock_tie` recovered from `lowerBlock_tie_state` at the
    returned variable. -/
theorem lowerBlock_tie_of_state {Γ : Ctxt jasminDialect} (ab : ArithBlock Γ)
    (nm : RegMapG Γ) (g : Nat → String) (s : JState 64) (V : Ctxt.Valuation Γ)
    (hinterp : JStateInterpG nm V s) (hfresh : FreshFor nm g) :
    (runBlock s (lowerBlock ab nm g)).get (outReg ab nm g) = ab.toCom.denote V := by
  rw [outReg_eq_finalNm ab nm g,
    lowerBlock_tie_state ab nm g s V hinterp hfresh (outVar ab),
    outVar_lookup_finalVal ab V]

/-! ## 4. Non-vacuity — both slots of the two-op block are readable

A concrete allocation, machine state and valuation for `block2`
(`s1 := a + b ; s2 := s1 * a ; ret s2`) on the inputs `7` and `35`. The final
correspondence reads the intermediate `s1 = 42` from its own register as well as
the result `s2 = 294` from the output register. -/

/-- An injective family of register names: `i` renders as `i + 1` copies of
    `'r'`. -/
def tieRegName (i : Nat) : String := String.ofList (List.replicate (i + 1) 'r')

/-- The name family is injective. -/
theorem tieRegName_inj {i j : Nat} (h : tieRegName i = tieRegName j) : i = j := by
  have h1 : List.replicate (i + 1) 'r' = List.replicate (j + 1) 'r' := by
    simpa [tieRegName] using congrArg String.toList h
  simpa using congrArg List.length h1

/-- The register map of the witness: the two inputs in the first two names of the
    family. -/
def nmW : RegMapG Δ2 := fun v =>
  match v with
  | .here => tieRegName 0
  | .there .here => tieRegName 1

/-- The destination stream of the witness: the names of the family past the two
    input registers. -/
def gW : Nat → String := fun i => tieRegName (i + 2)

/-- The witness allocation is fresh: the stream is injective and misses both
    input registers. -/
theorem gW_fresh : FreshFor nmW gW := by
  refine ⟨fun i j hij h => hij ?_, ?_⟩
  · have := tieRegName_inj h
    omega
  · intro i v
    match v with
    | .here => exact fun h => by simpa using tieRegName_inj h
    | .there .here => exact fun h => by have := tieRegName_inj h; omega

/-- The witness valuation `⟨7, 35⟩`. -/
def valW : Ctxt.Valuation Δ2 := .cons (7 : BitVec 64) (.cons (35 : BitVec 64) .nil)

/-- A machine state holding the witness valuation in the two input registers. -/
def stateW : JState 64 :=
  { regs := fun r =>
      if r = tieRegName 0 then 7 else if r = tieRegName 1 then 35 else 0 }

/-- The witness state corresponds to the witness valuation. -/
theorem stateW_interp : JStateInterpG nmW valW stateW := by
  intro v
  match v with
  | .here => rfl
  | .there .here =>
      show (if tieRegName 1 = tieRegName 0 then (7 : BitVec 64)
              else if tieRegName 1 = tieRegName 1 then 35 else 0) = 35
      rw [if_neg (fun h => by simpa using tieRegName_inj h), if_pos rfl]

/-- **Both slots of the two-op block are readable.** After `runBlock` of the
    lowered block, the first op's register holds the intermediate `7 + 35 = 42`
    and the second op's register holds the result `42 * 7 = 294`. -/
theorem block2_final_state_slots :
    (runBlock stateW (lowerBlock block2 nmW gW)).get (gW 0) = (42 : BitVec 64)
      ∧ (runBlock stateW (lowerBlock block2 nmW gW)).get (gW 1) = (294 : BitVec 64) := by
  have h := lowerBlock_tie_state block2 nmW gW stateW valW stateW_interp gW_fresh
  exact ⟨h (.there .here), h .here⟩

end CatCrypt.Crypto.SecureCompilation.Ascent
