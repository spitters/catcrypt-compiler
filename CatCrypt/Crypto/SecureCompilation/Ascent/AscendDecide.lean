/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Ascend
public import CatCrypt.Crypto.SecureCompilation.Dialects.CoveredSCtlDecide

/-!
# Deciding the ascent fragments

`Ascend.lean` fronts each fragment with a tactic that proves fragment membership
by `repeat' constructor`. Constructor search reaches the structural constructors
but not the `IsArithClean` / `IsWordClean` side condition an `RScalarSetExpr`
terminal carries, so on a kernel whose terminals are expressions those goals stay
open.

This module decides membership: a `Bool` test per fragment, a soundness lemma
from the test to the predicate, and a tactic that discharges membership with one
`decide`.

The `decide` in each tactic reduces the checker over the whole kernel, so its cost
grows with the kernel. `ascend_meta` (`Ascent/AscendMeta.lean`) is the membership
route that avoids this: it walks the kernel's syntax and applies the fragment's
constructors directly, with `decide` only on single leaves, and closes the same
membership and `Corres` goals. `AscendMeta.lean` closes the Keccak round both ways
(`keccakRoundBody_bitwise`, `keccakRoundBody_bitwise_decide`).

The variable test is `notTmpB` and the literal test `litOkB`, both in
`Dialects/CoveredSCtlDecide.lean`.

## Main definitions

* `isArithCleanB` / `isWordCleanB` — the expression fragments
* `isAscendableB` / `isAscendableExprB` / `isAscendableBitwiseB` — the program fragments
* `ascend!` / `ascend_expr!` / `ascend_bitwise!` — the per-fragment deciding tactics
* `ascend_unified!` — the deciding tactic over `SRwordNT`, at either word spec
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar

/-- The arithmetic (`+`/`-`/`*`) expression fragment, as a decision procedure. -/
def isArithCleanB : SExpr → Bool
  | .SVar x => notTmpB x
  | .SLit n => litOkB n
  | .SAdd a b | .SSub a b | .SMul a b => isArithCleanB a && isArithCleanB b
  | _ => false

/-- The bitwise (`^^^`/`&&&`/`<<<`/`>>>`) expression fragment, as a decision
    procedure. -/
def isWordCleanB : SExpr → Bool
  | .SVar x => notTmpB x
  | .SLit n => litOkB n
  | .SXor a b | .SAnd a b | .SShl a b | .SShr a b => isWordCleanB a && isWordCleanB b
  | _ => false

/-- The straight-line literal fragment `ascend` covers. -/
def isAscendableB : LowCT → Bool
  | .RSkip => true
  | .RBlock body => isAscendableB body
  | .RSeq c₁ c₂ => isAscendableB c₁ && isAscendableB c₂
  | .RScalarSet _ _ => true
  | _ => false

/-- The straight-line arithmetic-expression fragment `ascend_expr` covers. -/
def isAscendableExprB : LowCT → Bool
  | .RSkip => true
  | .RBlock body => isAscendableExprB body
  | .RSeq c₁ c₂ => isAscendableExprB c₁ && isAscendableExprB c₂
  | .RScalarSet _ _ => true
  | .RScalarSetExpr _ e => isArithCleanB e
  | _ => false

/-- The straight-line bitwise-expression fragment `ascend_bitwise` covers, literal
    `RScalarSet` terminals included. -/
def isAscendableBitwiseB : LowCT → Bool
  | .RSkip => true
  | .RBlock body => isAscendableBitwiseB body
  | .RSeq c₁ c₂ => isAscendableBitwiseB c₁ && isAscendableBitwiseB c₂
  | .RScalarSet _ _ => true
  | .RScalarSetExpr _ e => isWordCleanB e
  | _ => false

/-! ## Soundness -/

theorem isArithCleanB_sound : ∀ (e : SExpr), isArithCleanB e = true → IsArithClean e
  | .SVar x, h => notTmpB_sound x h
  | .SLit _, h => by simpa [IsArithClean, isArithCleanB, litOkB] using h
  | .SAdd a b, h => by
      simp only [isArithCleanB, Bool.and_eq_true] at h
      exact ⟨isArithCleanB_sound a h.1, isArithCleanB_sound b h.2⟩
  | .SSub a b, h => by
      simp only [isArithCleanB, Bool.and_eq_true] at h
      exact ⟨isArithCleanB_sound a h.1, isArithCleanB_sound b h.2⟩
  | .SMul a b, h => by
      simp only [isArithCleanB, Bool.and_eq_true] at h
      exact ⟨isArithCleanB_sound a h.1, isArithCleanB_sound b h.2⟩

theorem isWordCleanB_sound : ∀ (e : SExpr), isWordCleanB e = true → IsWordClean e
  | .SVar x, h => notTmpB_sound x h
  | .SLit _, h => by simpa [IsWordClean, isWordCleanB, litOkB] using h
  | .SXor a b, h => by
      simp only [isWordCleanB, Bool.and_eq_true] at h
      exact ⟨isWordCleanB_sound a h.1, isWordCleanB_sound b h.2⟩
  | .SAnd a b, h => by
      simp only [isWordCleanB, Bool.and_eq_true] at h
      exact ⟨isWordCleanB_sound a h.1, isWordCleanB_sound b h.2⟩
  | .SShl a b, h => by
      simp only [isWordCleanB, Bool.and_eq_true] at h
      exact ⟨isWordCleanB_sound a h.1, isWordCleanB_sound b h.2⟩
  | .SShr a b, h => by
      simp only [isWordCleanB, Bool.and_eq_true] at h
      exact ⟨isWordCleanB_sound a h.1, isWordCleanB_sound b h.2⟩

theorem isAscendableB_sound : ∀ (c : LowCT), isAscendableB c = true → IsAscendable c
  | .RSkip, _ => .rSkip
  | .RBlock body, h => .rBlock (isAscendableB_sound body h)
  | .RSeq c₁ c₂, h => by
      simp only [isAscendableB, Bool.and_eq_true] at h
      exact .rSeq (isAscendableB_sound c₁ h.1) (isAscendableB_sound c₂ h.2)
  | .RScalarSet name n, _ => .rScalarSet name n

theorem isAscendableExprB_sound : ∀ (c : LowCT), isAscendableExprB c = true → IsAscendableExpr c
  | .RSkip, _ => .rSkip
  | .RBlock body, h => .rBlock (isAscendableExprB_sound body h)
  | .RSeq c₁ c₂, h => by
      simp only [isAscendableExprB, Bool.and_eq_true] at h
      exact .rSeq (isAscendableExprB_sound c₁ h.1) (isAscendableExprB_sound c₂ h.2)
  | .RScalarSet name n, _ => .rScalarSet name n
  | .RScalarSetExpr x e, h => .rScalarSetExpr x e (isArithCleanB_sound e h)

theorem isAscendableBitwiseB_sound :
    ∀ (c : LowCT), isAscendableBitwiseB c = true → IsAscendableBitwise c
  | .RSkip, _ => .rSkip
  | .RBlock body, h => .rBlock (isAscendableBitwiseB_sound body h)
  | .RSeq c₁ c₂, h => by
      simp only [isAscendableBitwiseB, Bool.and_eq_true] at h
      exact .rSeq (isAscendableBitwiseB_sound c₁ h.1) (isAscendableBitwiseB_sound c₂ h.2)
  | .RScalarSet name n, _ => .rScalarSet name n
  | .RScalarSetExpr x e, h => .rScalarSetExpr x e (isWordCleanB_sound e h)

/-! ## The deciding tactics

Each closes fragment membership with one `decide`, including the `IsArithClean` /
`IsWordClean` side conditions that constructor search leaves open. -/

/-- `ascend` over the literal fragment, deciding membership. -/
macro "ascend!" : tactic =>
  `(tactic| exact ascend_sound (isAscendableB_sound _ (by decide)))

/-- `ascend_expr` over the arithmetic-expression fragment, deciding membership. -/
macro "ascend_expr!" : tactic =>
  `(tactic| exact ascend_expr_sound (isAscendableExprB_sound _ (by decide)))

/-- `ascend_bitwise` over the bitwise-expression fragment, deciding membership. -/
macro "ascend_bitwise!" : tactic =>
  `(tactic| exact ascend_bitwise_sound (isAscendableBitwiseB_sound _ (by decide)))

/-- The deciding ascent over the `ZMod 2 ^ 64` word specs. Over the non-temp relation
    `SRwordNT` it closes a goal stated at the expression spec `asemWExpr c` through
    `ascend_expr_sound` and one stated at the literal spec `asemW c` through
    `ascend_expr_sound_of_isAscendable`, the kernel mixing `RScalarSet` and
    `RScalarSetExpr` terminals in either case; over the total relation `SRword` it
    closes the literal fragment through `ascend_sound`. -/
macro "ascend_unified!" : tactic =>
  `(tactic| first
      | exact ascend_expr_sound (isAscendableExprB_sound _ (by decide))
      | exact ascend_expr_sound_of_isAscendable (isAscendableB_sound _ (by decide))
      | exact ascend_sound (isAscendableB_sound _ (by decide)))

/-! ## The fragments the constructor-search tactics leave open

Each example below has an `RScalarSetExpr` terminal, so `repeat' constructor`
stops at its cleanliness side condition. -/

/-- Two arithmetic expression terminals in sequence. -/
example :
    Corres SRwordNT (fun _ => True)
      (asemWExpr (.RSeq (.RScalarSetExpr "acc" (.SAdd (.SVar "a") (.SVar "b")))
        (.RScalarSetExpr "out" (.SMul (.SVar "acc") (.SVar "c")))))
      (.RSeq (.RScalarSetExpr "acc" (.SAdd (.SVar "a") (.SVar "b")))
        (.RScalarSetExpr "out" (.SMul (.SVar "acc") (.SVar "c")))) := by
  ascend_expr!

/-- A nested block mixing a literal leaf with an expression terminal. -/
example :
    Corres SRwordNT (fun _ => True)
      (asemWExpr (.RBlock (.RSeq (.RScalarSet "k" 5)
        (.RScalarSetExpr "r" (.SSub (.SVar "x") (.SVar "k"))))))
      (.RBlock (.RSeq (.RScalarSet "k" 5)
        (.RScalarSetExpr "r" (.SSub (.SVar "x") (.SVar "k"))))) := by
  ascend_expr!

/-- A ChaCha-style quarter-round step over the bitwise fragment. -/
example :
    Corres SRwordBV (fun _ => True)
      (asemWBV (.RSeq (.RScalarSetExpr "d" (.SXor (.SVar "d") (.SVar "a")))
        (.RScalarSetExpr "b" (.SAnd (.SVar "b") (.SVar "c")))))
      (.RSeq (.RScalarSetExpr "d" (.SXor (.SVar "d") (.SVar "a")))
        (.RScalarSetExpr "b" (.SAnd (.SVar "b") (.SVar "c")))) := by
  ascend_bitwise!

/-- The literal fragment still closes, through the deciding front. -/
example :
    Corres SRword (fun _ => True)
      (asemW (.RSeq (.RScalarSet "x" 5) (.RScalarSet "y" 7)))
      (.RSeq (.RScalarSet "x" 5) (.RScalarSet "y" 7)) := by
  ascend!

/-! ## Mixed terminals in one call

`ascend_unified!` is the single entry point for the `ZMod 2 ^ 64` ascents. Its primary
route is `SRwordNT`, where both terminal forms live in one fragment. -/

/-- A kernel carrying a literal `RScalarSet`, two arithmetic `RScalarSetExpr`
    terminals, an `RSkip` and a nested `RBlock`, lifted by one tactic call. -/
example :
    Corres SRwordNT (fun _ => True)
      (asemWExpr
        (.RBlock (.RSeq (.RScalarSet "a" 3)
          (.RSeq (.RScalarSetExpr "b" (.SAdd (.SVar "a") (.SLit 7)))
            (.RSeq .RSkip (.RScalarSetExpr "c" (.SMul (.SVar "b") (.SVar "a"))))))))
      (.RBlock (.RSeq (.RScalarSet "a" 3)
        (.RSeq (.RScalarSetExpr "b" (.SAdd (.SVar "a") (.SLit 7)))
          (.RSeq .RSkip (.RScalarSetExpr "c" (.SMul (.SVar "b") (.SVar "a"))))))) := by
  ascend_unified!

/-- A literal-only kernel stated at the `asemW` spec, over the non-temp relation. -/
example :
    Corres SRwordNT (fun _ => True)
      (asemW (.RSeq (.RScalarSet "x" 5) (.RScalarSet "y" 7)))
      (.RSeq (.RScalarSet "x" 5) (.RScalarSet "y" 7)) := by
  ascend_unified!

/-- The literal fragment over the total relation `SRword`, through the same tactic. -/
example :
    Corres SRword (fun _ => True)
      (asemW (.RBlock (.RSeq (.RScalarSet "x" 5) (.RScalarSet "y" 7))))
      (.RBlock (.RSeq (.RScalarSet "x" 5) (.RScalarSet "y" 7))) := by
  ascend_unified!

/-- A literal seed and a bitwise expression terminal in one bitwise ascent. -/
example :
    Corres SRwordBV (fun _ => True)
      (asemWBV (.RSeq (.RScalarSet "c" 0)
        (.RScalarSetExpr "d" (.SXor (.SVar "d") (.SVar "c")))))
      (.RSeq (.RScalarSet "c" 0)
        (.RScalarSetExpr "d" (.SXor (.SVar "d") (.SVar "c")))) := by
  ascend_bitwise!

end CatCrypt.Crypto.SecureCompilation.Ascent
