/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxToLowCT

/-!
# Lowering `whileFoldReturn` by an exit flag and guarded continuations

`Hax.pipeline` rewrites a loop whose body contains `return e` into
`whileFoldReturn (var c) body`, with the `return e` turned into `cfBreak e`.
`Hax.denote'` evaluates `cfBreak e` to `val (controlFlow true v)`; `seq`,
`letBind` and `ifThenElse` pass such a value on without running their
continuation, and `denoteWhile'Return` returns it out of the loop.  `LowCT` has
no exit construct, so the lowering keeps the exit in scalar slots:

* `exitRetName` is the exit flag (`1` once a `cfBreak` has run) and
  `exitValName` the returned word;
* `cfBreak e` stores the payload into `exitValName` and sets the flag;
* a statement that follows a statement which may have exited runs under
  `RIfNz exitRetName RSkip _`;
* `whileFoldReturn (var c) body` zeroes the flag and the payload slot, copies the
  guard `c` into a loop slot `run`, and runs `RWhileNz run` over the lowered body
  followed by `RIfNz exitRetName (run := 0) (run := c)`.

The translator `haxToLowCTK fl e` carries downward the loop slot of the
innermost enclosing `whileFoldReturn` (`fl = none` outside every such loop,
where `cfBreak` is refused) and returns upward, next to the lowered command,
whether the command may have exited.  The loop slot of a `whileFoldReturn` is
`exitRunName fl`: `"__exit_run"` at the outermost level, one `_` appended per
nesting level.  The names `exitRetName`, `exitValName` and `exitRunName _` are
reserved: a program that binds any of them is outside the lowering's
simulation, which states that condition as a hypothesis.

Every constructor that cannot carry an exit is lowered by `haxToLowCT`, and a
`letBind` is lowered by `letHead`, the head context `haxToLowCT` builds around
its body (`haxToLowCT_letBind_eq_letHead`).  The projection `exitFree` keeps the
commands that cannot exit; `haxToLowCT_eq_haxToLowCTK_none` states that
`haxToLowCT` is that projection of `haxToLowCTK none`.

`AnfShapedK inLoop e` is the shape predicate of `haxToLowCTK`
(`haxToLowCTK_isSome_iff_anfK`); it accepts `cfBreak` exactly when `inLoop`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpLit ImpType IntWidth)
open CatCrypt.Crypto.Jasmin.LowCT (TowerType LowCT Located SExpr)

/-! ## §1  Reserved slots and the loop and exit shapes -/

/-- The exit flag slot: `1` once a `cfBreak` has run, `0` otherwise. -/
def exitRetName : String := "__exit_ret"

/-- The slot holding the word a `cfBreak` returns. -/
def exitValName : String := "__exit_val"

/-- The loop slot of a `whileFoldReturn` whose innermost enclosing
    `whileFoldReturn` has loop slot `fl`: `"__exit_run"` outside every such loop,
    and `fl ++ "_"` inside one. -/
def exitRunName : Option String → String
  | none => "__exit_run"
  | some r => r ++ "_"

/-- A statement run only when the exit flag is `0`. -/
def exitGuard (c : LowCT) : LowCT := .RIfNz exitRetName .RSkip c

/-- The lowered `whileFoldReturn (var c) body` with loop slot `run` and lowered
    body `bC`: zero the flag and the payload slot, copy `c` into `run`, and
    iterate while `run` is nonzero; after each trip `run` is `0` if the body
    exited and `c` otherwise. -/
def exitLoop (run c : String) (bC : LowCT) : LowCT :=
  .RLetU64Zero exitRetName (.RLetU64Zero exitValName (.RLetU64Zero run
    (.RSeq (.RScalarSetExpr run (.SVar c))
      (.RWhileNz run
        (.RSeq bC (.RIfNz exitRetName (.RScalarSet run 0)
                    (.RScalarSetExpr run (.SVar c))))))))

/-- The lowered `cfBreak e`: the payload is a scalar variable or a scalar
    literal, stored into `exitValName`, and the exit flag is set.  Any other
    payload is refused. -/
def exitStore : ImpExpr → Option LowCT
  | .var x =>
      some (.RSeq (.RScalarSetExpr exitValName (.SVar x)) (.RScalarSet exitRetName 1))
  | .lit (.uintLit w n) =>
      some (.RSeq (.RScalarSet exitValName (n % w.modulus)) (.RScalarSet exitRetName 1))
  | .lit (.int n) =>
      if 0 ≤ n then
        some (.RSeq (.RScalarSet exitValName n.toNat) (.RScalarSet exitRetName 1))
      else none
  | .lit (.bool b) =>
      some (.RSeq (.RScalarSet exitValName (if b then 1 else 0)) (.RScalarSet exitRetName 1))
  | _ => none

/-! ## §2  The head of a `letBind` -/

/-- The context `haxToLowCT` places around the lowered body of
    `letBind name val body`, as a function of the lowered body; `none` when
    `haxToLowCT` refuses the right-hand side. -/
def letHead (name : String) : ImpExpr → Option (LowCT → LowCT)
  | .app f args =>
      let dt := towerOfCallName f
      let dest : Located := { locVar := name, locSrc := dt }
      (haxArgsToLocated dt args).map fun args' bodyC =>
        if f = "array_update" then
          match args with
          | [.var arr, .var idx, .var src] =>
              let arrLoc : Located := { locVar := arr, locSrc := .TBytes 0 }
              let srcLoc : Located := { locVar := src, locSrc := .TBytes 0 }
              .RSeq (.RArrStore arrLoc idx srcLoc) bodyC
          | _ => .RLetZero name dt (.RSeq (.RCall f dest args') bodyC)
        else if f = "index" then
          match args with
          | [.var arr, .var idx] =>
              let dtL : TowerType := .TFp
              let destLoc : Located := { locVar := name, locSrc := dtL }
              let arrLoc  : Located := { locVar := arr,  locSrc := dtL }
              .RLetZero name dtL (.RSeq (.RArrLoad destLoc arrLoc idx) bodyC)
          | _ => .RLetZero name dt (.RSeq (.RCall f dest args') bodyC)
        else
          .RLetZero name dt (.RSeq (.RCall f dest args') bodyC)
  | .lit (.uintLit w n) =>
      some fun bodyC => .RLetU64Zero name (.RSeq (.RScalarSet name (n % w.modulus)) bodyC)
  | .lit (.int n) =>
      if n ≥ 0 then
        some fun bodyC => .RLetU64Zero name (.RSeq (.RScalarSet name n.toNat) bodyC)
      else none
  | .lit (.bool b) =>
      some fun bodyC =>
        .RLetU64Zero name (.RSeq (.RScalarSet name (if b then 1 else 0)) bodyC)
  | .var _ => some id
  | .proj (.var t) i =>
      let dtL : TowerType := .TFp
      some fun bodyC =>
        .RLetZero name dtL
          (.RSeq (.RTupleLoad { locVar := name, locSrc := dtL }
                              { locVar := t, locSrc := dtL } i) bodyC)
  | _ => none

/-- `haxToLowCT` lowers a `letBind` as its head context applied to the lowered
    body. -/
theorem haxToLowCT_letBind_eq_letHead (name : String) (val body : ImpExpr) :
    haxToLowCT (.letBind name val body) =
      match letHead name val, haxToLowCT body with
      | some k, some bC => some (k bC)
      | _, _ => none := by
  cases val with
  | lit l =>
    cases l with
    | int n =>
      by_cases h : n ≥ 0
      · simp only [haxToLowCT, letHead, h, dite_true, if_true]
        cases haxToLowCT body <;> rfl
      · simp only [haxToLowCT, letHead, h, dite_false, if_false]
    | uintLit w n => simp only [haxToLowCT, letHead]; cases haxToLowCT body <;> rfl
    | bool b => simp only [haxToLowCT, letHead]; cases haxToLowCT body <;> rfl
    | _ => simp only [haxToLowCT, letHead]
  | app f args =>
    simp only [haxToLowCT, letHead]
    cases haxArgsToLocated (towerOfCallName f) args <;> cases haxToLowCT body <;>
      simp only [Option.map]
    all_goals split_ifs <;> (repeat' split) <;> first | rfl | simp_all
  | var s => simp only [haxToLowCT, letHead]; cases haxToLowCT body <;> rfl
  | proj pe i =>
    cases pe with
    | var t => simp only [haxToLowCT, letHead]; cases haxToLowCT body <;> rfl
    | _ => simp only [haxToLowCT, letHead]
  | _ => simp only [haxToLowCT, letHead]

/-! ## §3  The translator -/

/-- The lowering with an exit flag.  `fl` is the loop slot of the innermost
    enclosing `whileFoldReturn` (`none` outside every such loop); the result
    pairs the lowered command with whether it may have exited.  Constructors
    that carry no exit are lowered by `haxToLowCT`, with the flag `false`. -/
def haxToLowCTK : Option String → ImpExpr → Option (LowCT × Bool)
  | fl, .letBind name val body =>
      match letHead name val, haxToLowCTK fl body with
      | some k, some (bC, x) => some (k bC, x)
      | _, _ => none
  | fl, .seq a b =>
      match haxToLowCTK fl a, haxToLowCTK fl b with
      | some (aC, xa), some (bC, xb) =>
          some (if xa then .RSeq aC (exitGuard bC) else .RSeq aC bC, xa || xb)
      | _, _ => none
  | fl, .ifThenElse (.var v) t e =>
      match haxToLowCTK fl t, haxToLowCTK fl e with
      | some (tC, xt), some (eC, xe) => some (.RIfNz v tC eC, xt || xe)
      | _, _ => none
  | fl, .typeAscription e _ => haxToLowCTK fl e
  | fl, .whileFoldReturn (.var c) body =>
      match haxToLowCTK (some (exitRunName fl)) body with
      | some (bC, _) => some (exitLoop (exitRunName fl) c bC, true)
      | none => none
  | some _, .cfBreak e => (exitStore e).map fun s => (s, true)
  | _, e => (haxToLowCT e).map fun c => (c, false)

/-- The commands that cannot exit: `some c` for a lowering `(c, false)`. -/
def exitFree : Option (LowCT × Bool) → Option LowCT
  | some (c, false) => some c
  | _ => none

/-- **`haxToLowCT` is the exit-free projection of `haxToLowCTK none`.** -/
theorem haxToLowCT_eq_haxToLowCTK_none (e : ImpExpr) :
    haxToLowCT e = exitFree (haxToLowCTK none e) := by
  have hmap : ∀ o : Option LowCT, exitFree (o.map fun c => (c, false)) = o := by
    intro o; cases o <;> rfl
  induction e using ImpExpr.ind with
  | letBind n val body _ ihb =>
    rw [haxToLowCT_letBind_eq_letHead, ihb]
    simp only [haxToLowCTK]
    rcases letHead n val with _ | k <;>
      rcases haxToLowCTK none body with _ | ⟨bC, _ | _⟩ <;> rfl
  | seq a b iha ihb =>
    simp only [haxToLowCT, haxToLowCTK]
    rw [iha, ihb]
    rcases haxToLowCTK none a with _ | ⟨aC, _ | _⟩ <;>
      rcases haxToLowCTK none b with _ | ⟨bC, _ | _⟩ <;> rfl
  | ifThenElse c t e _ iht ihe =>
    cases c with
    | var v =>
      simp only [haxToLowCT, haxToLowCTK]
      rw [iht, ihe]
      rcases haxToLowCTK none t with _ | ⟨tC, _ | _⟩ <;>
        rcases haxToLowCTK none e with _ | ⟨eC, _ | _⟩ <;> rfl
    | _ => simp only [haxToLowCTK]; exact (hmap _).symm
  | typeAscription e _ ih => simp only [haxToLowCT, haxToLowCTK]; exact ih
  | whileFoldReturn c body _ _ =>
    cases c with
    | var v =>
      simp only [haxToLowCT, haxToLowCTK]
      rcases haxToLowCTK (some (exitRunName none)) body with _ | ⟨bC, _⟩ <;> rfl
    | _ => simp only [haxToLowCTK]; exact (hmap _).symm
  | _ => simp only [haxToLowCTK]; exact (hmap _).symm

/-- Outside every `whileFoldReturn` a `cfBreak` is refused. -/
theorem haxToLowCTK_none_cfBreak (e : ImpExpr) : haxToLowCTK none (.cfBreak e) = none := rfl

/-! ## §4  The shape predicate -/

/-- The shape `haxToLowCTK` accepts, with `inLoop` recording whether the
    expression sits inside a `whileFoldReturn` body: a `letBind` whose head
    `letHead` accepts and whose body has the shape; `seq`, `ifThenElse` on a
    variable and a type ascription with components of the shape; a
    `whileFoldReturn` on a variable whose body has the shape inside the loop; a
    `cfBreak` of a variable or scalar literal inside a loop; and every other
    expression when `AnfShaped` accepts it. -/
def AnfShapedK (inLoop : Bool) : ImpExpr → Bool
  | .letBind name val body => (letHead name val).isSome && AnfShapedK inLoop body
  | .seq a b => AnfShapedK inLoop a && AnfShapedK inLoop b
  | .ifThenElse (.var _) t e => AnfShapedK inLoop t && AnfShapedK inLoop e
  | .typeAscription e _ => AnfShapedK inLoop e
  | .whileFoldReturn (.var _) body => AnfShapedK true body
  | .cfBreak e => inLoop && (exitStore e).isSome
  | e => AnfShaped e

/-- **The shape biconditional of `haxToLowCTK`.** The translator with loop slot
    `fl` succeeds exactly on the expressions of shape `AnfShapedK fl.isSome`. -/
theorem haxToLowCTK_isSome_iff_anfK (fl : Option String) (e : ImpExpr) :
    (haxToLowCTK fl e).isSome = true ↔ AnfShapedK fl.isSome e = true := by
  suffices h : ∀ fl, (haxToLowCTK fl e).isSome = AnfShapedK fl.isSome e by rw [h]
  have hmap : ∀ (fl : Option String) (e : ImpExpr),
      ((haxToLowCT e).map fun c => (c, false)).isSome = AnfShaped e := by
    intro fl e
    rw [Option.isSome_map]
    cases h : AnfShaped e
    · exact Bool.eq_false_iff.mpr (fun h' => by
        rw [(haxToLowCT_isSome_iff_anf e).mp h'] at h; cases h)
    · exact (haxToLowCT_isSome_iff_anf e).mpr h
  induction e using ImpExpr.ind with
  | letBind n val body _ ihb =>
    intro fl
    simp only [haxToLowCTK, AnfShapedK]
    rw [← ihb fl]
    rcases letHead n val with _ | k <;> rcases haxToLowCTK fl body with _ | ⟨bC, x⟩ <;> rfl
  | seq a b iha ihb =>
    intro fl
    simp only [haxToLowCTK, AnfShapedK]
    rw [← iha fl, ← ihb fl]
    rcases haxToLowCTK fl a with _ | ⟨aC, xa⟩ <;> rcases haxToLowCTK fl b with _ | ⟨bC, xb⟩ <;> rfl
  | ifThenElse c t e _ iht ihe =>
    intro fl
    cases c with
    | var v =>
      simp only [haxToLowCTK, AnfShapedK]
      rw [← iht fl, ← ihe fl]
      rcases haxToLowCTK fl t with _ | ⟨tC, xt⟩ <;>
        rcases haxToLowCTK fl e with _ | ⟨eC, xe⟩ <;> rfl
    | _ => simp only [haxToLowCTK, AnfShapedK]; exact hmap fl _
  | typeAscription e _ ih => intro fl; simp only [haxToLowCTK, AnfShapedK]; exact ih fl
  | whileFoldReturn c body _ ihb =>
    intro fl
    cases c with
    | var v =>
      simp only [haxToLowCTK, AnfShapedK]
      have h := ihb (some (exitRunName fl))
      rw [Option.isSome_some] at h
      rw [← h]
      rcases haxToLowCTK (some (exitRunName fl)) body with _ | ⟨bC, x⟩ <;> rfl
    | _ => simp only [haxToLowCTK, AnfShapedK]; exact hmap fl _
  | cfBreak e _ =>
    intro fl
    cases fl with
    | none => rfl
    | some r => simp only [haxToLowCTK, AnfShapedK, Option.isSome_map, Option.isSome_some,
        Bool.true_and]
  | _ => intro fl; simp only [haxToLowCTK, AnfShapedK]; exact hmap fl _

/-! ## §5  Agreement with the representability filter -/

/-- A representable expression at context `inLoop` that has the translator's
    shape inside a loop has the shape at `inLoop`: the filter confines `cfBreak`
    to `whileFoldReturn` bodies. -/
theorem anfShapedK_of_representable (inLoop : Bool) (e : ImpExpr)
    (hrep : LowCTRepresentable.ExprIn inLoop e = true)
    (hanf : AnfShapedK true e = true) : AnfShapedK inLoop e = true := by
  induction e using ImpExpr.ind generalizing inLoop with
  | letBind n val body _ ihb =>
    simp only [AnfShapedK, LowCTRepresentable.ExprIn, Bool.and_eq_true] at hrep hanf ⊢
    exact ⟨hanf.1, ihb inLoop hrep.2 hanf.2⟩
  | seq a b iha ihb =>
    simp only [AnfShapedK, LowCTRepresentable.ExprIn, Bool.and_eq_true] at hrep hanf ⊢
    exact ⟨iha inLoop hrep.1 hanf.1, ihb inLoop hrep.2 hanf.2⟩
  | ifThenElse c t e _ iht ihe =>
    cases c with
    | var v =>
      simp only [AnfShapedK, LowCTRepresentable.ExprIn, Bool.and_eq_true] at hrep hanf ⊢
      exact ⟨iht inLoop hrep.1.2 hanf.1, ihe inLoop hrep.2 hanf.2⟩
    | _ => simp only [AnfShapedK] at hanf ⊢; exact hanf
  | typeAscription e _ ih =>
    simp only [AnfShapedK, LowCTRepresentable.ExprIn] at hrep hanf ⊢
    exact ih inLoop hrep hanf
  | whileFoldReturn c body _ _ =>
    cases c with
    | var v => simp only [AnfShapedK] at hanf ⊢; exact hanf
    | _ => simp only [AnfShapedK] at hanf ⊢; exact hanf
  | cfBreak e _ =>
    simp only [AnfShapedK, LowCTRepresentable.ExprIn, Bool.and_eq_true] at hrep hanf ⊢
    exact ⟨hrep.1, hanf.2⟩
  | _ => simp only [AnfShapedK] at hanf ⊢; exact hanf

/-- **Filter and translator agree.** A representable expression of the
    translator's in-loop shape is lowered by `haxToLowCTK none`. The
    representability hypothesis rules out a `cfBreak` outside every
    `whileFoldReturn` body, which `AnfShapedK true` admits. -/
theorem haxToLowCTK_isSome_of_representable_and_anfK (e : ImpExpr)
    (hrep : LowCTRepresentable.Expr e = true) (hanf : AnfShapedK true e = true) :
    (haxToLowCTK none e).isSome = true :=
  (haxToLowCTK_isSome_iff_anfK none e).mpr (anfShapedK_of_representable false e hrep hanf)

/-! ## §6  The pipeline shape of a search loop

`searchLoopShape tail` is the output of `Hax.pipeline` on the search loop of
`Ascent/Demos/EarlyExit.lean` at `x = 1` (`searchU_pipeline`), with the
statement after the loop replaced by `tail`. The two theorems below are static
checks that pin which of these shapes `haxToLowCTK none` lowers; each closes by
`decide` in milliseconds. -/

/-- The pipeline output of the search loop at `x = 1`, followed by `tail`. -/
def searchLoopShape (tail : ImpExpr) : ImpExpr :=
  .letBind "three" (.lit (.uintLit .w64 3))
   (.letBind "one" (.lit (.uintLit .w64 1))
    (.letBind "xv" (.lit (.uintLit .w64 1))
     (.letBind "i" (.lit (.uintLit .w64 0))
      (.letBind "c" (.app "lt" [.var "i", .var "three"])
       (.seq
         (.whileFoldReturn (.var "c")
           (.letBind "e" (.app "le" [.var "xv", .var "i"])
             (.seq
               (.ifThenElse (.var "e") (.cfBreak (.var "i")) .unitVal)
               (.seq
                 (.seq (.letBind "i" (.app "add" [.var "i", .var "one"]) (.var "i")) .unitVal)
                 (.seq (.letBind "c" (.app "lt" [.var "i", .var "three"]) (.var "c"))
                   .unitVal)))))
         tail)))))

/-- With the literal `100` after the loop, as `searchU` has it, the lowering is
    refused: a literal in tail position has no result slot. -/
theorem searchLoopShape_litTail_refused :
    (haxToLowCTK none (searchLoopShape (.lit (.uintLit .w64 100)))).isSome = false := by
  decide

/-- With a variable after the loop, the lowering succeeds. -/
theorem searchLoopShape_varTail_lowers :
    (haxToLowCTK none (searchLoopShape (.var "xv"))).isSome = true := by
  decide

end CatCrypt.Crypto.Hax
