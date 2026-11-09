/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.FieldRoute
public import CatCrypt.Crypto.SecureCompilation.Algebraic.EcJacobianLimbs

@[expose] public section

set_option autoImplicit false

/-!
# The Jacobian group law as route programs over word arrays

For a modulus record `P : LimbParams n` and a curve record `C : ECParams P.p`, the
Jacobian addition `jacAddProg P.p i` and doubling `jacDblProg P.p C.a i`
(`VIR/EllipticCurveLoweringJacobian`) are field programs returning coordinate `i` of the
output triple. Both pass the coverage decision `GoodVB`, so `FieldRoute.compileField`,
the run of the field chain at the identity step, accepts them; the route programs
`jacAddRoute` and `jacDblRoute` are its runs, the straight-line programs `fieldCom P c` over
word arrays: one array of `n` limbs per input coordinate, followed by the output array.

The layouts `addAbi n` and `dblAbi n` pass the output array in `%rdi` and the input
coordinates, last first, in the following System V argument registers; the addition has
six input coordinates, one more than those registers hold, and passes the first in `%r10`. `addVal n p sa` and `dblVal n p sa`
are the valuations of the program contexts read off a machine state `sa`, and the layouts
read them off `sa` (`AbiValOf`).

## Main results

* `goodVB_of_covered`: a program whose every operation passes `opGoodB` passes `GoodVB`.
* `jacAddRoute`, `jacDblRoute`, `compileField_jacAdd`, `compileField_jacDbl`: the route
  programs of the two programs at every modulus record and curve coefficient, as runs of
  `compileField`.
* `jacAddRoute_eq`, `jacDblRoute_eq`: the route programs as straight-line programs.
* `addAbi`, `addVal`, `abiValOf_addAbi`, `dblAbi`, `dblVal`, `abiValOf_dblAbi`: the
  layouts and the valuations they read off a machine state.
* `addAbiStack`, `addAbiStack_wf`, `exportReg_stackArgReg`: the System V layout of the
  addition with its seventh argument in the stack word `%rsp + 8`, its well-formed stack
  parameter, and the export name of a stack parameter.
* `jacAdd_denote`, `jacDbl_denote`: at the valuation of a machine state whose input arrays
  hold the Montgomery limbs of the input coordinates, the output array holds the
  Montgomery limbs of coordinate `i` of `jacAddGen` (resp. `jacDoubleGenA C.a`).
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.EcRoute

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
open CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect
open CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect.JacLower
open CatCrypt.Crypto.SecureCompilation.EcProjectiveGeneric (jacAddGen)
open CatCrypt.Crypto.SecureCompilation.EcProjectiveGenericA (jacDoubleGenA)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont (LimbParams enc)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs
open CatCrypt.Crypto.SecureCompilation.Algebraic.EcJacobianLimbs (Jac jacAddProg_covered
  jacDblProg_covered)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldRoute (compileField compileField_eq
  compileField_denote)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf wordsFn)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)

/-! ## 1. Coverage and the route programs -/

section Route

variable {n : Nat} (P : LimbParams n)

/-- A program whose every operation passes `opGoodB` passes the coverage decision
    `GoodVB`. -/
theorem goodVB_of_covered : {Γ : Ctxt fieldDialect} → {t : FieldTy} →
    (c : Com fieldDialect Γ t) → CoveredCom (fun e => opGoodB P e.op = true) c →
    GoodVB P c = true
  | _, _, .ret _, _ => rfl
  | _, _, .var e body, h => by
      simp only [GoodVB, Bool.and_eq_true]
      exact ⟨h.1, goodVB_of_covered body h.2⟩

theorem goodVB_jacAdd (i : Fin 3) : GoodVB P (jacAddProg P.p i) = true :=
  goodVB_of_covered P _ (jacAddProg_covered (fun e => opGoodB P e.op = true)
    (fun _ _ => by simp [eSub, opGoodB]) (fun _ _ => by simp [eMul, opGoodB])
    (fun _ => by simp [eSq, opGoodB]) (fun _ => by simp [eDbl, opGoodB]) i)

theorem goodVB_jacDbl (a : ZMod P.p) (i : Fin 3) : GoodVB P (jacDblProg P.p a i) = true :=
  goodVB_of_covered P _ (jacDblProg_covered (fun e => opGoodB P e.op = true)
    (fun _ _ => by simp [eAdd, opGoodB]) (fun _ _ => by simp [eSub, opGoodB])
    (fun _ _ => by simp [eMul, opGoodB]) (fun _ => by simp [eSq, opGoodB])
    (fun _ => by simp [eDbl, opGoodB]) (fun _ => by simp [eConst, opGoodB]) a i)

/-- The context of the addition over word arrays: six input arrays and the output
    array. -/
abbrev addCtx (n p : Nat) : Ctxt jasminDialect := arrCtx n (inCtxt6 p) ++ [arrTy n]

/-- The context of the doubling over word arrays: three input arrays and the output
    array. -/
abbrev dblCtx (n p : Nat) : Ctxt jasminDialect := arrCtx n (inCtxt3 p) ++ [arrTy n]

/-- The field chain at the identity step accepts coordinate `i` of the Jacobian
    addition. -/
theorem compileField_jacAdd_isSome (i : Fin 3) : (compileField P (jacAddProg P.p i)).isSome := by
  rw [compileField_eq, ite_eq_left (goodVB_jacAdd P i)]
  rfl

/-- The field chain at the identity step accepts coordinate `i` of the Jacobian doubling. -/
theorem compileField_jacDbl_isSome (a : ZMod P.p) (i : Fin 3) :
    (compileField P (jacDblProg P.p a i)).isSome := by
  rw [compileField_eq, ite_eq_left (goodVB_jacDbl P a i)]
  rfl

/-- **The route program of coordinate `i` of the Jacobian addition**: the run of the
    field chain at the identity step `FieldChain.fieldChainId P` (`compileField P`) on
    `jacAddProg P.p i`. -/
def jacAddRoute (i : Fin 3) : RouteProg (addCtx n P.p) (arrTy n) :=
  (compileField P (jacAddProg P.p i)).get (compileField_jacAdd_isSome P i)

/-- **The route program of coordinate `i` of the Jacobian doubling** at the curve
    coefficient `a`: the run of `FieldChain.fieldChainId P` (`compileField P`) on
    `jacDblProg P.p a i`. -/
def jacDblRoute (a : ZMod P.p) (i : Fin 3) : RouteProg (dblCtx n P.p) (arrTy n) :=
  (compileField P (jacDblProg P.p a i)).get (compileField_jacDbl_isSome P a i)

theorem compileField_jacAdd (i : Fin 3) :
    compileField P (jacAddProg P.p i) = some (jacAddRoute P i) :=
  (Option.some_get _).symm

theorem compileField_jacDbl (a : ZMod P.p) (i : Fin 3) :
    compileField P (jacDblProg P.p a i) = some (jacDblRoute P a i) :=
  (Option.some_get _).symm

/-- The route program of coordinate `i` of the Jacobian addition is the straight-line
    program `fieldCom P (jacAddProg P.p i)`. -/
theorem jacAddRoute_eq (i : Fin 3) :
    jacAddRoute P i = .straight (fieldCom P (jacAddProg P.p i)) := by
  have h := compileField_jacAdd P i
  rw [compileField_eq, ite_eq_left (goodVB_jacAdd P i)] at h
  exact (Option.some_inj.mp h).symm

/-- The route program of coordinate `i` of the Jacobian doubling is the straight-line
    program `fieldCom P (jacDblProg P.p a i)`. -/
theorem jacDblRoute_eq (a : ZMod P.p) (i : Fin 3) :
    jacDblRoute P a i = .straight (fieldCom P (jacDblProg P.p a i)) := by
  have h := compileField_jacDbl P a i
  rw [compileField_eq, ite_eq_left (goodVB_jacDbl P a i)] at h
  exact (Option.some_inj.mp h).symm

end Route

/-! ## 2. The layouts -/

/-- The `n` words at the entry value of the register `r` of the machine state `sa`. -/
abbrev wordsAtReg (sa : AState) (r : String) (n : Nat) : Fin n → BitVec 64 :=
  wordsFn sa (sa.regs r) n

/-- **The layout of the Jacobian addition over `n` limbs**: the output array in `%rdi`,
    then `Z₂`, `Y₂`, `X₂`, `Z₁`, `Y₁` in `%rsi`, `%rdx`, `%rcx`, `%r8`, `%r9` and `X₁` in
    `%r10`, each of `n` words; the result is the `n` words at the entry `%rdi`; the body's
    stack words lie in the `4096` bytes below the entry `%rsp`. -/
def addAbi (n : Nat) : AbiLayout where
  args := [⟨"out", "%rdi", .words n⟩, ⟨"z2", "%rsi", .words n⟩, ⟨"y2", "%rdx", .words n⟩,
    ⟨"x2", "%rcx", .words n⟩, ⟨"z1", "%r8", .words n⟩, ⟨"y1", "%r9", .words n⟩,
    ⟨"x1", "%r10", .words n⟩]
  consts := []
  result := .words "%rdi" n
  bounds := []
  frameLo := -4096
  frameHi := -8

/-- **The System V layout of the Jacobian addition over `n` limbs**: the parameters of
    `addAbi n`, with `X₁`, the seventh integer argument, carried in the stack word at entry
    `%rsp + 8` (`stackArgReg 1`). -/
def addAbiStack (n : Nat) : AbiLayout where
  args := [⟨"out", "%rdi", .words n⟩, ⟨"z2", "%rsi", .words n⟩, ⟨"y2", "%rdx", .words n⟩,
    ⟨"x2", "%rcx", .words n⟩, ⟨"z1", "%r8", .words n⟩, ⟨"y1", "%r9", .words n⟩,
    ⟨"x1", stackArgReg 1, .words n⟩]
  consts := []
  result := .words "%rdi" n
  bounds := []
  frameLo := -4096
  frameHi := 8

/-- The stack parameter of `addAbiStack n` lies above the return address and inside the
    stack words of the layout. -/
theorem addAbiStack_wf (n : Nat) : (addAbiStack n).StackWF := by
  intro a ha k hk
  simp only [addAbiStack, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only at hk <;>
    first
    | exact absurd hk (ne_stackArgReg (by decide) k)
    | (obtain rfl := stackArgReg_inj hk; exact ⟨le_rfl, by simp [addAbiStack]⟩)

/-- **The export name of a stack parameter**: the carrier name `stackArgReg k` exports as
    `"RSP+" ++ toString (8 * k)`, the name `abiStackOff?` reads as the stack offset `8 k`. -/
theorem exportReg_stackArgReg (k : Nat) :
    exportReg (stackArgReg k) = "RSP+" ++ toString (8 * k) :=
  exportReg_rsp _ (by
    simp only [Nat.toString_eq_ofList_toDigits, String.toList_ofList]
    exact List.all_eq_true.mpr fun c hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc)

/-- **The layout of the Jacobian doubling over `n` limbs**: the output array in `%rdi`,
    then `Z`, `Y`, `X` in `%rsi`, `%rdx`, `%rcx`, each of `n` words; the result is the `n`
    words at the entry `%rdi`. -/
def dblAbi (n : Nat) : AbiLayout where
  args := [⟨"out", "%rdi", .words n⟩, ⟨"z", "%rsi", .words n⟩, ⟨"y", "%rdx", .words n⟩,
    ⟨"x", "%rcx", .words n⟩]
  consts := []
  result := .words "%rdi" n
  bounds := []
  frameLo := -4096
  frameHi := -8

/-- The valuation of the context of the addition read off the machine state `sa`. -/
def addVal (n p : Nat) (sa : AState) : Valuation (addCtx n p) :=
  .cons (wordsAtReg sa "%r10" n) (.cons (wordsAtReg sa "%r9" n) (.cons (wordsAtReg sa "%r8" n)
    (.cons (wordsAtReg sa "%rcx" n) (.cons (wordsAtReg sa "%rdx" n)
      (.cons (wordsAtReg sa "%rsi" n) (.cons (wordsAtReg sa "%rdi" n) .nil))))))

/-- The valuation of the context of the doubling read off the machine state `sa`. -/
def dblVal (n p : Nat) (sa : AState) : Valuation (dblCtx n p) :=
  .cons (wordsAtReg sa "%rcx" n) (.cons (wordsAtReg sa "%rdx" n)
    (.cons (wordsAtReg sa "%rsi" n) (.cons (wordsAtReg sa "%rdi" n) .nil)))

theorem abiValOf_addAbi (n p : Nat) (sa : AState) : AbiValOf (addAbi n) sa (addVal n p sa) where
  arg := fun v => by
    rcases v with _ | _ | _ | _ | _ | _ | _ | ⟨⟨⟩⟩ <;> rfl
  reg := fun v => by
    rcases v with _ | _ | _ | _ | _ | _ | _ | ⟨⟨⟩⟩
  arr := fun v => by
    rcases v with _ | _ | _ | _ | _ | _ | _ | ⟨⟨⟩⟩ <;> exact ⟨_, rfl, rfl, rfl, rfl⟩

theorem abiValOf_dblAbi (n p : Nat) (sa : AState) : AbiValOf (dblAbi n) sa (dblVal n p sa) where
  arg := fun v => by
    rcases v with _ | _ | _ | _ | ⟨⟨⟩⟩ <;> rfl
  reg := fun v => by
    rcases v with _ | _ | _ | _ | ⟨⟨⟩⟩
  arr := fun v => by
    rcases v with _ | _ | _ | _ | ⟨⟨⟩⟩ <;> exact ⟨_, rfl, rfl, rfl, rfl⟩

/-! ## 3. The denotations at a machine state -/

section Denote

variable {n : Nat} (P : LimbParams n) [Fact P.p.Prime]

/-- **The output limbs of the compiled Jacobian addition at a machine state.** At the
    valuation `addVal` of a machine state whose input arrays hold the Montgomery limbs of
    the coordinates of `J₁` and `J₂`, the output array of the route program of coordinate
    `i` holds the Montgomery limbs of coordinate `i` of `jacAddGen`. -/
theorem jacAdd_denote (hn : n < 2 ^ 64) (sa : AState) (J1 J2 : Jac P.p) (i : Fin 3)
    (hx1 : arrLimbs (wordsAtReg sa "%r10" n) n 0 = enc P J1.1)
    (hy1 : arrLimbs (wordsAtReg sa "%r9" n) n 0 = enc P J1.2.1)
    (hz1 : arrLimbs (wordsAtReg sa "%r8" n) n 0 = enc P J1.2.2)
    (hx2 : arrLimbs (wordsAtReg sa "%rcx" n) n 0 = enc P J2.1)
    (hy2 : arrLimbs (wordsAtReg sa "%rdx" n) n 0 = enc P J2.2.1)
    (hz2 : arrLimbs (wordsAtReg sa "%rsi" n) n 0 = enc P J2.2.2) :
    arrLimbs ((jacAddRoute P i).denote (addVal n P.p sa)) n 0
      = enc P (coord (jacAddGen J1.1 J1.2.1 J1.2.2 J2.1 J2.2.1 J2.2.2) i) := by
  have h := compileField_denote P hn (compileField_jacAdd P i) (jacVal2 J1 J2)
    (.cons (wordsAtReg sa "%r10" n) (.cons (wordsAtReg sa "%r9" n)
      (.cons (wordsAtReg sa "%r8" n) (.cons (wordsAtReg sa "%rcx" n)
        (.cons (wordsAtReg sa "%rdx" n) (.cons (wordsAtReg sa "%rsi" n) .nil))))))
    (wordsAtReg sa "%rdi" n) (by
      show hvAppend _ (hvAppend _ (hvAppend _ (hvAppend _ (hvAppend _ (hvAppend _ .nil)))))
        = hvAppend (encL P (t := .fp P.p) J1.1) (hvAppend (encL P (t := .fp P.p) J1.2.1)
          (hvAppend (encL P (t := .fp P.p) J1.2.2) (hvAppend (encL P (t := .fp P.p) J2.1)
            (hvAppend (encL P (t := .fp P.p) J2.2.1)
              (hvAppend (encL P (t := .fp P.p) J2.2.2) .nil)))))
      rw [encL_fp, encL_fp, encL_fp, encL_fp, encL_fp, encL_fp, hx1, hy1, hz1, hx2, hy2,
        hz2])
  rw [jacAddProg_denote, encL_fp] at h
  exact h

/-- **The output limbs of the compiled Jacobian doubling at a machine state.** At the
    valuation `dblVal` of a machine state whose input arrays hold the Montgomery limbs of
    the coordinates of `J`, the output array of the route program of coordinate `i` at the
    curve coefficient `a` holds the Montgomery limbs of coordinate `i` of
    `jacDoubleGenA a`. -/
theorem jacDbl_denote (hn : n < 2 ^ 64) (sa : AState) (a : ZMod P.p) (J : Jac P.p)
    (i : Fin 3)
    (hx : arrLimbs (wordsAtReg sa "%rcx" n) n 0 = enc P J.1)
    (hy : arrLimbs (wordsAtReg sa "%rdx" n) n 0 = enc P J.2.1)
    (hz : arrLimbs (wordsAtReg sa "%rsi" n) n 0 = enc P J.2.2) :
    arrLimbs ((jacDblRoute P a i).denote (dblVal n P.p sa)) n 0
      = enc P (coord (jacDoubleGenA a J.1 J.2.1 J.2.2) i) := by
  have h := compileField_denote P hn (compileField_jacDbl P a i) (jacVal1 J)
    (.cons (wordsAtReg sa "%rcx" n) (.cons (wordsAtReg sa "%rdx" n)
      (.cons (wordsAtReg sa "%rsi" n) .nil)))
    (wordsAtReg sa "%rdi" n) (by
      show hvAppend _ (hvAppend _ (hvAppend _ .nil))
        = hvAppend (encL P (t := .fp P.p) J.1) (hvAppend (encL P (t := .fp P.p) J.2.1)
          (hvAppend (encL P (t := .fp P.p) J.2.2) .nil))
      rw [encL_fp, encL_fp, encL_fp, hx, hy, hz])
  rw [jacDblProg_denote, encL_fp] at h
  exact h

end Denote

end CatCrypt.Crypto.SecureCompilation.Haxc.EcRoute
