/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.Ascent.Corres
public import CatCrypt.Crypto.SecureCompilation.Ascent.Control
public import CatCrypt.Crypto.SecureCompilation.Ascent.ExprLeaf

/-!
# The `ascend` tactic — the integrator

Assembles the per-constructor `corres_*` database (the leaf `corres_setScalar`, the
structural `corres_seq`/`_skip`/`_block`) into a **total** ascent over the assignable
straight-line fragment `IsAscendable`, fronted by the `ascend` tactic. This is the
AutoCorres/Ascent phase pass in total form for the fragment the value leaf covers: every
`IsAscendable` program lifts to its pure word spec `asemW c` over `ZMod 2^64`, with no
manual composition.

Frontier (honest, = the descent's): the loop/conditional rules `corres_for`/`corres_if`
(`Ascent.Control`) are proved and compose on concrete kernels, but a *uniform*
`ascend_sound` over all of `IsCoveredSU` additionally needs the `RScalarSetExpr` leaf
(the `semLowerSExpr` success guard) and a `Corres`-over-`semScalarWhile` variant for
`RWhileNz` — the same frontier the descent tracks.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar

/-- The assignable straight-line fragment the value leaf covers uniformly:
    `RSkip`/`RBlock`/`RSeq`/`RScalarSet`. -/
inductive IsAscendable : LowCT → Prop
  | rSkip : IsAscendable .RSkip
  | rBlock {body : LowCT} : IsAscendable body → IsAscendable (.RBlock body)
  | rSeq {c₁ c₂ : LowCT} : IsAscendable c₁ → IsAscendable c₂ → IsAscendable (.RSeq c₁ c₂)
  | rScalarSet (name : String) (n : Nat) : IsAscendable (.RScalarSet name n)

/-- The abstract word transformer (the spec) over `ZMod 2^64` for the ascendable
    fragment — the pure image of `semScalar`. -/
def asemW : LowCT → (String → ZMod (2 ^ 64)) → (String → ZMod (2 ^ 64))
  | .RSkip, a => a
  | .RBlock body, a => asemW body a
  | .RSeq c₁ c₂, a => asemW c₂ (asemW c₁ a)
  | .RScalarSet name n, a => fun s => if s = name then (n : ZMod (2 ^ 64)) else a s
  | _, a => a

/-- Total soundness of the ascent over `IsAscendable`: every such program lifts to its
    pure word spec `asemW c` under `SRword`, by structural recursion assembling the
    `corres_*` database. The precondition is `True` — the word abstraction to `ZMod 2^64`
    is unconditional (it *is* the wrapping semantics). -/
theorem ascend_sound {c : LowCT} (h : IsAscendable c) :
    Corres SRword (fun _ => True) (asemW c) c := by
  induction h with
  | rSkip => exact corres_skip SRword
  | rBlock _ ih => exact corres_block SRword ih
  | rSeq _ _ ih₁ ih₂ =>
      have h := corres_seq SRword ih₁ ih₂ (fun _ _ => trivial)
      exact h
  | rScalarSet name n => exact corres_setScalar name n

/-- The `ascend` tactic: synthesize the word spec `asemW c` and close
    `Corres SRword (fun _ => True) (asemW c) c` — proving `IsAscendable` by constructor
    search, then discharging by `ascend_sound`. -/
macro "ascend" : tactic => `(tactic| exact ascend_sound (by repeat' constructor))

/-! ## `ascend` in action + the control rules composing on concrete kernels -/

/-- A straight-line word kernel lifts by one tactic invocation. -/
example : Corres SRword (fun _ => True) (asemW (.RSeq (.RScalarSet "x" 5) (.RScalarSet "y" 7)))
    (.RSeq (.RScalarSet "x" 5) (.RScalarSet "y" 7)) := by ascend

/-- Nested blocks and sequencing, one `ascend`. -/
example : Corres SRword (fun _ => True)
    (asemW (.RBlock (.RSeq (.RScalarSet "a" 1) (.RSeq (.RScalarSet "b" 2) (.RScalarSet "c" 3)))))
    (.RBlock (.RSeq (.RScalarSet "a" 1) (.RSeq (.RScalarSet "b" 2) (.RScalarSet "c" 3)))) := by
  ascend

/-- The conditional rule composes on a concrete branch kernel (via `corres_if`). -/
example : Corres SRword (fun _ => True)
    (fun a s => if s = "r" then (if a "g" = 0 then (7 : ZMod (2 ^ 64)) else (5 : ZMod (2 ^ 64)))
      else a s)
    (.RIfNz "g" (.RScalarSet "r" 5) (.RScalarSet "r" 7)) :=
  corres_if "g" "r" 5 7

/-! ## The non-temp fragments: literal and expression terminals in one ascent

`semScalar`'s `RScalarSetExpr` arm lowers `e` through fresh temporaries and writes
the `tmpName` namespace. The total `SRword` constrains *every* name, so it is not
preserved across such a lowering. The non-temp relations `SRwordNT` (arithmetic
values in `ZMod 2^64`) and `SRwordBV` (bitwise values in `BitVec 64`) constrain only
the source names a kernel reads and writes, which the lowering leaves untouched, and
are preserved.

`IsAscendableExpr` is the fragment over `SRwordNT` carrying both terminal forms —
the literal `RScalarSet` through `corres_setScalar_NT`, the arithmetic
`RScalarSetExpr` through `corres_setExpr` — under the structural `RSkip`/`RBlock`/
`RSeq`, so a kernel mixing the two lifts in one step. It contains the `SRword`
fragment `IsAscendable` (`isAscendable_isAscendableExpr`) with the same word spec
(`asemW_eq_asemWExpr`), and `ascend_expr_sound_srword` enters it from a total-`SRword`
state. `Corres` mentions its state relation in the hypothesis as well as the
conclusion, so `Corres SRword` and `Corres SRwordNT` imply each other in neither
direction and `ascend_sound` is a statement in its own right.

`SRwordBV` is the same shape over the `BitVec 64` word algebra, where `^^^`/`&&&`/
`<<<`/`>>>` are not `ZMod` ring operations and the abstraction is the identity;
`IsAscendableBitwise` is its fragment, with literal and expression terminals. -/

/-- The straight-line arithmetic-expression fragment: `RScalarSet` literal leaves and
    `RScalarSetExpr` terminals over the `IsArithClean` (`+`/`-`/`*`) fragment, wrapped
    in the structural `RSkip`/`RBlock`/`RSeq`. -/
inductive IsAscendableExpr : LowCT → Prop
  | rSkip : IsAscendableExpr .RSkip
  | rBlock {body : LowCT} : IsAscendableExpr body → IsAscendableExpr (.RBlock body)
  | rSeq {c₁ c₂ : LowCT} : IsAscendableExpr c₁ → IsAscendableExpr c₂ →
      IsAscendableExpr (.RSeq c₁ c₂)
  | rScalarSet (name : String) (n : Nat) : IsAscendableExpr (.RScalarSet name n)
  | rScalarSetExpr (x : String) (e : SExpr) (he : IsArithClean e) :
      IsAscendableExpr (.RScalarSetExpr x e)

/-- The abstract `ZMod 2^64` word transformer for the arithmetic-expression fragment:
    the `RScalarSetExpr` terminal sets `x` to the clean `evalZMod` value. -/
def asemWExpr : LowCT → (String → ZMod (2 ^ 64)) → (String → ZMod (2 ^ 64))
  | .RSkip, a => a
  | .RBlock body, a => asemWExpr body a
  | .RSeq c₁ c₂, a => asemWExpr c₂ (asemWExpr c₁ a)
  | .RScalarSet name n, a => fun s => if s = name then (n : ZMod (2 ^ 64)) else a s
  | .RScalarSetExpr x e, a => fun s => if s = x then evalZMod a e else a s
  | _, a => a

/-- Soundness of the arithmetic-expression ascent over `SRwordNT`: every
    `IsAscendableExpr` program lifts to its `ZMod 2^64` spec `asemWExpr c`, assembling
    the `corres_skip`/`_block`/`_seq` structure with the literal leaf
    `corres_setScalar_NT` and the expression leaf `corres_setExpr`. -/
theorem ascend_expr_sound {c : LowCT} (h : IsAscendableExpr c) :
    Corres SRwordNT (fun _ => True) (asemWExpr c) c := by
  induction h with
  | rSkip => exact corres_skip SRwordNT
  | rBlock _ ih => exact corres_block SRwordNT ih
  | rSeq _ _ ih₁ ih₂ =>
      have h := corres_seq SRwordNT ih₁ ih₂ (fun _ _ => trivial)
      exact h
  | rScalarSet name n => exact corres_setScalar_NT name n
  | rScalarSetExpr x e he => exact corres_setExpr x e he

/-! ### The literal fragment as a special case

The structural lemmas `corres_skip`/`_block`/`_seq` (`Ascent.Corres`) take the state
relation as an argument, so both ascents use the same three; the fragments differ only
in their terminals and in which relation the terminals are proved over. -/

/-- Every `IsAscendable` program is `IsAscendableExpr`: the literal fragment's
    constructors are a sub-list of the non-temp fragment's. -/
theorem isAscendable_isAscendableExpr {c : LowCT} (h : IsAscendable c) :
    IsAscendableExpr c := by
  induction h with
  | rSkip => exact .rSkip
  | rBlock _ ih => exact .rBlock ih
  | rSeq _ _ ih₁ ih₂ => exact .rSeq ih₁ ih₂
  | rScalarSet name n => exact .rScalarSet name n

/-- On the literal fragment the two word specs agree: `asemWExpr` extends `asemW`
    only at `RScalarSetExpr`, which `IsAscendable` does not admit. -/
theorem asemW_eq_asemWExpr {c : LowCT} (h : IsAscendable c) : asemW c = asemWExpr c := by
  induction h with
  | rSkip => rfl
  | rBlock _ ih => funext a; exact congrFun ih a
  | rSeq _ _ ih₁ ih₂ => funext a; simp only [asemW, asemWExpr, ih₁, ih₂]
  | rScalarSet name n => rfl

/-- The literal fragment ascends through the non-temp soundness theorem, at its own
    spec `asemW c` — so a kernel accepted by `ascend` needs no separate rule to sit
    inside a non-temp ascent. -/
theorem ascend_expr_sound_of_isAscendable {c : LowCT} (h : IsAscendable c) :
    Corres SRwordNT (fun _ => True) (asemW c) c := by
  rw [asemW_eq_asemWExpr h]
  exact ascend_expr_sound (isAscendable_isAscendableExpr h)

/-- The non-temp ascent entered from a total-`SRword` state: `srword_srwordNT` supplies
    the non-temp relation on entry, and the post-state is related to the spec by
    `SRwordNT`. -/
theorem ascend_expr_sound_srword {c : LowCT} (h : IsAscendableExpr c)
    (env : SEnvScalar) (a : String → ZMod (2 ^ 64)) (hSR : SRword env a) :
    ∃ env', semScalar c env = some env' ∧ SRwordNT env' (asemWExpr c a) :=
  ascend_expr_sound h env a (srword_srwordNT hSR) trivial

/-- The straight-line bitwise fragment: literal `RScalarSet` terminals and
    `RScalarSetExpr` terminals over the `IsWordClean` (`^^^`/`&&&`/`<<<`/`>>>`)
    fragment, wrapped in the structural `RSkip`/`RBlock`/`RSeq`. -/
inductive IsAscendableBitwise : LowCT → Prop
  | rSkip : IsAscendableBitwise .RSkip
  | rBlock {body : LowCT} : IsAscendableBitwise body → IsAscendableBitwise (.RBlock body)
  | rSeq {c₁ c₂ : LowCT} : IsAscendableBitwise c₁ → IsAscendableBitwise c₂ →
      IsAscendableBitwise (.RSeq c₁ c₂)
  | rScalarSet (name : String) (n : Nat) : IsAscendableBitwise (.RScalarSet name n)
  | rScalarSetExpr (x : String) (e : SExpr) (he : IsWordClean e) :
      IsAscendableBitwise (.RScalarSetExpr x e)

/-- The abstract `BitVec 64` word transformer for the bitwise fragment: the spec stays
    in the word algebra (`SExpr.evalBV`), with no `ZMod` abstraction. -/
def asemWBV : LowCT → (String → BitVec 64) → (String → BitVec 64)
  | .RBlock body, a => asemWBV body a
  | .RSeq c₁ c₂, a => asemWBV c₂ (asemWBV c₁ a)
  | .RScalarSet name n, a => fun s => if s = name then BitVec.ofNat 64 n else a s
  | .RScalarSetExpr x e, a => fun s => if s = x then SExpr.evalBV a e else a s
  | _, a => a

/-- Soundness of the bitwise ascent over `SRwordBV`: every `IsAscendableBitwise`
    program lifts to its `BitVec 64` word spec `asemWBV c`, assembling the structural
    rules with the literal leaf `corres_setScalar_BV` and the expression leaf
    `corres_setExprBitwise`. -/
theorem ascend_bitwise_sound {c : LowCT} (h : IsAscendableBitwise c) :
    Corres SRwordBV (fun _ => True) (asemWBV c) c := by
  induction h with
  | rSkip => exact corres_skip SRwordBV
  | rBlock _ ih => exact corres_block SRwordBV ih
  | rSeq _ _ ih₁ ih₂ =>
      have h := corres_seq SRwordBV ih₁ ih₂ (fun _ _ => trivial)
      exact h
  | rScalarSet name n => exact corres_setScalar_BV name n
  | rScalarSetExpr x e he => exact corres_setExprBitwise x e he

/-- The `ascend_expr` tactic: as `ascend`, over the arithmetic-expression fragment.
    Closes fully when every terminal is a literal `RScalarSet`; an `RScalarSetExpr`
    terminal leaves its `IsArithClean` cleanliness as a residual goal. -/
macro "ascend_expr" : tactic => `(tactic| exact ascend_expr_sound (by repeat' constructor))

/-- The `ascend_bitwise` tactic: as `ascend`, over the bitwise-expression fragment. -/
macro "ascend_bitwise" : tactic => `(tactic| exact ascend_bitwise_sound (by repeat' constructor))

/-! ### The expression ascent in action -/

/-- A literal-only straight-line kernel lifts over `SRwordNT` by one `ascend_expr`. -/
example : Corres SRwordNT (fun _ => True)
    (asemWExpr (.RSeq (.RScalarSet "x" 5) (.RScalarSet "y" 7)))
    (.RSeq (.RScalarSet "x" 5) (.RScalarSet "y" 7)) := by ascend_expr

/-- **Expression terminals auto-assemble.** A two-step kernel whose *second* terminal
    is an arithmetic `SExpr` (`j := i + 1`) lifts to its `ZMod 2^64` spec — the
    `corres_setExpr` leaf slotted into the structural recursion. -/
example :
    Corres SRwordNT (fun _ => True)
      (asemWExpr (.RSeq (.RScalarSet "i" 0)
        (.RScalarSetExpr "j" (.SAdd (.SVar "i") (.SLit 1)))))
      (.RSeq (.RScalarSet "i" 0) (.RScalarSetExpr "j" (.SAdd (.SVar "i") (.SLit 1)))) :=
  ascend_expr_sound
    (.rSeq (.rScalarSet "i" 0)
      (.rScalarSetExpr "j" (.SAdd (.SVar "i") (.SLit 1))
        ⟨notTmp_of_short "i" (by decide), (by norm_num : (1 : ℕ) < 2 ^ 64)⟩))

/-- **A bitwise round auto-assembles.** A two-step ChaCha-style mix (`d := d ^^^ a`;
    `b := b ^^^ c`), both terminals bitwise `SExpr`s, lifts to its `BitVec 64` word
    spec via the bitwise leaf — the fragment the arithmetic ascent could not reach. -/
example :
    Corres SRwordBV (fun _ => True)
      (asemWBV (.RSeq (.RScalarSetExpr "d" (.SXor (.SVar "d") (.SVar "a")))
        (.RScalarSetExpr "b" (.SXor (.SVar "b") (.SVar "c")))))
      (.RSeq (.RScalarSetExpr "d" (.SXor (.SVar "d") (.SVar "a")))
        (.RScalarSetExpr "b" (.SXor (.SVar "b") (.SVar "c")))) :=
  ascend_bitwise_sound
    (.rSeq
      (.rScalarSetExpr "d" (.SXor (.SVar "d") (.SVar "a"))
        ⟨notTmp_of_short "d" (by decide), notTmp_of_short "a" (by decide)⟩)
      (.rScalarSetExpr "b" (.SXor (.SVar "b") (.SVar "c"))
        ⟨notTmp_of_short "b" (by decide), notTmp_of_short "c" (by decide)⟩))

/-! ## The value-leaf transfer via the `param_auto` coordinator

`ascend` integrates the *structural* leaves (`corres_setScalar`/`_seq`/`_block`/`_skip`).
Its arithmetic sibling — the `RScalarSetExpr` value leaf (`Ascent.ExprLeaf`) — rests on a
word-op-tree representation change through the registered `RelatedBinOp wEnc` squares
(`wEncAdd`/`wEncSub`/`wEncMul`, `Ascent.Corres`). Stated relationally, that obligation is
closed uniformly by ParamTransfer's `param_auto` coordinator, which routes it to `rcongr`
(cross-head congruence descent over the *same* `wEnc` squares that `composeBinOp` consumes).
One call site discharges the whole tree, of any op-shape — the tactic-level dual to the
`(inferInstance : Related wEnc …).rel` idiom.

Note: `param_auto` needs the goal in `Related wEnc` form to pick up the encoding; on a bare
`wEnc (t) = t'` equality `rcongr` defaults to `Related id` and cannot descend the squares —
so the value-leaf induction in `ExprLeaf` (bare-equality per node) still names its square. -/

/-- `param_auto` closes a value-leaf word-op tree (mixed `*`/`-`) via `rcongr`, dispatching
    over the registered `wEnc` squares — no explicit `.comm` naming. -/
example (x y z : BitVec 64) :
    Transfer.Related wEnc (x * y - z) (wEnc x * wEnc y - wEnc z) := by param_auto

/-- The equational face of the same value leaf: the coordinator builds the `Related`
    witness, `.rel` reads off the transfer equation `wEnc (t) = t'` the leaf needs. -/
example (x y z : BitVec 64) : wEnc (x * y - z) = wEnc x * wEnc y - wEnc z :=
  (by param_auto : Transfer.Related wEnc (x * y - z) (wEnc x * wEnc y - wEnc z)).rel

end CatCrypt.Crypto.SecureCompilation.Ascent
