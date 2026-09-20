/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.JInstrToArithBlock

/-!
# Recognising a `Com jasminDialect` as an `ArithBlock`

`ArithBlock` is the only source the machine-side lowering `lowerBlock` accepts,
and the descent produces `Com jasminDialect`. This module recognises the second
as the first: `comToArithBlock` maps a `Com jasminDialect Γ (.reg 64)` whose
every binding is a scalar 64-bit `regArith`, a 64-bit `shlImm`/`shrImm` with a
count below the word width, or a 64-bit `regConst`, to the `ArithBlock Γ` with
those binders, and rejects everything else.

`comToArithBlock_toCom` is the round trip: a recognised program is exactly the
one its recognised block compiles back to, so the block carries no information
the program did not have. `com_lowerBlock_runBlock` composes the recogniser with
the imported `lowerBlock_tie`: a recognised `Com` lowers to a machine block whose
output register holds the `Com`'s own denotation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-! ## 1. The recogniser -/

/-- A two-element `HVector` is the `cons` of its head onto the `cons` of its
    tail's head. -/
theorem hvector_two_eta.{u, v} {α : Type u} {f : α → Type v} {t₁ t₂ : α}
    (xs : HVector f [t₁, t₂]) :
    HVector.cons xs.head (HVector.cons xs.tail.head HVector.nil) = xs := by
  match xs with
  | .cons _ (.cons _ .nil) => rfl

/-- A one-element `HVector` is the `cons` of its head onto the empty vector. -/
theorem hvector_one_eta.{u, v} {α : Type u} {f : α → Type v} {t₁ : α}
    (xs : HVector f [t₁]) : HVector.cons xs.head HVector.nil = xs := by
  match xs with
  | .cons _ .nil => rfl

/-- An empty `HVector` is `HVector.nil`. -/
theorem hvector_nil_eta.{u, v} {α : Type u} {f : α → Type v}
    (xs : HVector f ([] : List α)) : HVector.nil = xs := by
  match xs with
  | .nil => rfl

/-- **Recognise a dialect program as a straight-line arithmetic block.** A
    `Com.ret` is the block's return; a `Com.var` is one block op when its
    expression binds a `reg 64` slot and is a scalar `regArith` at width 64, a
    `shlImm`/`shrImm` at width 64 with a count below the word width, or a
    `regConst` at width 64, with the operands read off the expression's argument
    vector. Every other program is rejected. -/
def comToArithBlock : {Γ : Ctxt jasminDialect} →
    Com jasminDialect Γ (.reg 64) → Option (ArithBlock Γ)
  | _, .ret v => some (.ret v)
  | _, .var (t := t) e body =>
      match t, e, body with
      | JasminTy.reg 64, ⟨.regArith bop 64, _, args⟩, body =>
          if hs : isScalarBopB bop = true then
            (comToArithBlock body).map fun rest =>
              .op bop (IsScalarBop_of_isScalarBopB hs) args.head args.tail.head rest
          else none
      | JasminTy.reg 64, ⟨.shlImm 64 k, _, args⟩, body =>
          if hk : k < 64 then
            (comToArithBlock body).map fun rest =>
              .un (unOfShl k) (IsScalarUn_unOfShl hk) args.head rest
          else none
      | JasminTy.reg 64, ⟨.shrImm 64 k, _, args⟩, body =>
          if hk : k < 64 then
            (comToArithBlock body).map fun rest => .un (.shr k) hk args.head rest
          else none
      | JasminTy.reg 64, ⟨.regConst 64 n, _, _⟩, body =>
          (comToArithBlock body).map fun rest => .cnst n rest
      | _, _, _ => none

/-! ## 2. The round trip -/

/-- **One recognised binding.** A recognised `Com.var` recognises its body, and
    the block it yields compiles to the same binding over the body's block. -/
theorem comToArithBlock_var {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (body : Com jasminDialect (t :: Γ) (.reg 64))
    (ab : ArithBlock Γ) (h : comToArithBlock (.var e body) = some ab) :
    ∃ rest : ArithBlock (t :: Γ),
      comToArithBlock body = some rest ∧ ab.toCom = .var e rest.toCom := by
  unfold comToArithBlock at h
  split at h
  · rename_i bop hop args body'
    split at h
    · rename_i hs
      rcases hb : comToArithBlock body' with _ | rest
      · rw [hb] at h; simp at h
      · rw [hb] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        refine ⟨rest, rfl, ?_⟩
        simp only [ArithBlock.toCom, arithExpr, hvector_two_eta args]
    · simp at h
  · rename_i k hop args body'
    split at h
    · rename_i hk
      rcases hb : comToArithBlock body' with _ | rest
      · rw [hb] at h; simp at h
      · rw [hb] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        refine ⟨rest, rfl, ?_⟩
        simp only [ArithBlock.toCom, unExpr_unOfShl, hvector_one_eta args]
    · simp at h
  · rename_i k hop args body'
    split at h
    · rename_i hk
      rcases hb : comToArithBlock body' with _ | rest
      · rw [hb] at h; simp at h
      · rw [hb] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        refine ⟨rest, rfl, ?_⟩
        simp only [ArithBlock.toCom, unExpr, hvector_one_eta args]
    · simp at h
  · rename_i n hop args body'
    rcases hb : comToArithBlock body' with _ | rest
    · rw [hb] at h; simp at h
    · rw [hb] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      refine ⟨rest, rfl, ?_⟩
      simp only [ArithBlock.toCom, constExpr, hvector_nil_eta args]
  · simp at h

/-- **The recogniser invents nothing.** A recognised block compiles back to the
    program it was recognised from. -/
theorem comToArithBlock_toCom : {Γ : Ctxt jasminDialect} →
    (c : Com jasminDialect Γ (.reg 64)) → (ab : ArithBlock Γ) →
    comToArithBlock c = some ab → ab.toCom = c
  | _, .ret v, ab, h => by
      simp only [comToArithBlock, Option.some.injEq] at h
      subst h; rfl
  | _, .var e body, ab, h => by
      obtain ⟨rest, hb, heq⟩ := comToArithBlock_var e body ab h
      rw [heq, comToArithBlock_toCom body rest hb]

/-- The denotations agree: a recognised block's compiled program denotes what the
    recognised program denotes. -/
theorem comToArithBlock_denote {Γ : Ctxt jasminDialect}
    (c : Com jasminDialect Γ (.reg 64)) (ab : ArithBlock Γ)
    (h : comToArithBlock c = some ab) (V : Ctxt.Valuation Γ) :
    ab.toCom.denote V = c.denote V := by
  rw [comToArithBlock_toCom c ab h]

/-! ## 3. The composite -/

/-- **A recognised `Com` lowers to machine instructions carrying its denotation.**
    Under the state correspondence `JStateInterpG` and a fresh allocation
    `FreshFor`, reading the output register after `runBlock` of the lowered
    recognised block equals the dialect program's own `Com.denote`. -/
theorem com_lowerBlock_runBlock {Γ : Ctxt jasminDialect}
    (c : Com jasminDialect Γ (.reg 64)) (ab : ArithBlock Γ)
    (h : comToArithBlock c = some ab)
    (nm : RegMapG Γ) (g : Nat → String) (s : JState 64) (V : Ctxt.Valuation Γ)
    (hinterp : JStateInterpG nm V s) (hfresh : FreshFor nm g) :
    (runBlock s (lowerBlock ab nm g)).get (outReg ab nm g) = c.denote V := by
  rw [lowerBlock_tie ab nm g s V hinterp hfresh]
  exact comToArithBlock_denote c ab h V

/-! ## 4. Non-vacuity — a two-op dialect program recognised

A `Com jasminDialect` built directly over `regArith`, in the style of
`JasminDialect.smokeProg`, computing `(a + b) * a` on the two inputs. -/

/-- A two-op dialect program over `Δ2`: `s1 := a + b ; s2 := s1 * a ; ret s2`. -/
def comBlock2 : Com jasminDialect Δ2 (.reg 64) :=
  .var (.mk (.regArith .add 64) rfl (.cons dA (.cons dB .nil)))
    (.var (.mk (.regArith .mul 64) rfl (.cons .here (.cons (.there .here) .nil)))
      (.ret .here))

/-- The two-op program is recognised as the `ArithBlock` of the same two ops. -/
theorem comBlock2_recognise : comToArithBlock comBlock2 = some block2 := by
  with_unfolding_all rfl

/-- The recognised block compiles back to the program it was recognised from. -/
theorem comBlock2_toCom : block2.toCom = comBlock2 :=
  comToArithBlock_toCom comBlock2 block2 comBlock2_recognise

/-- The two-op program denotes to `(7 + 35) * 7 = 294` on the inputs `⟨7, 35⟩`. -/
theorem comBlock2_denote_concrete :
    comBlock2.denote (.cons (7 : BitVec 64) (.cons (35 : BitVec 64) .nil))
      = (294 : BitVec 64) := by
  with_unfolding_all rfl

/-- The recognised block's compiled program denotes the same value on the same
    inputs, through the round trip. -/
theorem block2_toCom_denote_concrete :
    block2.toCom.denote (.cons (7 : BitVec 64) (.cons (35 : BitVec 64) .nil))
      = (294 : BitVec 64) := by
  rw [comBlock2_toCom]
  exact comBlock2_denote_concrete

/-! ## 5. Non-vacuity — a program mixing a constant, a copy, shifts and an op

A five-binder program over the two inputs whose leading binder is a `regConst`:
`c := 5 ; t1 := a ; t2 := t1 <<< 3 ; t3 := b >>> 2 ; t4 := t2 ^^^ t3 ; ret t4`.
Every new block arm occurs — the constant, a copy, a left shift, a right shift —
alongside the binary `regArith`. -/

/-- The five-binder mixed dialect program. -/
def comBlock3 : Com jasminDialect Δ2 (.reg 64) :=
  .var (.mk (.regConst 64 5) rfl .nil)
    (.var (.mk (.shlImm 64 0) rfl (.cons (.there .here) .nil))
      (.var (.mk (.shlImm 64 3) rfl (.cons .here .nil))
        (.var (.mk (.shrImm 64 2) rfl
            (.cons (.there (.there (.there (.there .here)))) .nil))
          (.var (.mk (.regArith .xor 64) rfl (.cons (.there .here) (.cons .here .nil)))
            (.ret .here)))))

/-- The mixed program is recognised as the block of its five binders, the leading
    `regConst` included. -/
theorem comBlock3_recognise : comToArithBlock comBlock3 = some block3 := by
  with_unfolding_all rfl

/-- The recognised mixed block compiles back to the program it was recognised
    from. -/
theorem comBlock3_toCom : block3.toCom = comBlock3 :=
  comToArithBlock_toCom comBlock3 block3 comBlock3_recognise

/-- The mixed program denotes to `(7 <<< 3) ^^^ (35 >>> 2) = 48` on the inputs
    `⟨7, 35⟩`. -/
theorem comBlock3_denote_concrete :
    comBlock3.denote (.cons (7 : BitVec 64) (.cons (35 : BitVec 64) .nil))
      = (48 : BitVec 64) := by
  with_unfolding_all rfl

/-- **The block tie on the mixed block.** Under any state correspondence and
    fresh allocation, the machine `runBlock` of the whole lowered mixed block
    reads the program's own denotation. -/
theorem comBlock3_lowerBlock_runBlock (nm : RegMapG Δ2) (g : Nat → String)
    (s : JState 64) (V : Ctxt.Valuation Δ2)
    (hinterp : JStateInterpG nm V s) (hfresh : FreshFor nm g) :
    (runBlock s (lowerBlock block3 nm g)).get (outReg block3 nm g)
      = comBlock3.denote V :=
  com_lowerBlock_runBlock comBlock3 block3 comBlock3_recognise nm g s V hinterp hfresh

end CatCrypt.Crypto.SecureCompilation.Ascent
