/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxToLowCT

/-!
# Lowering a function with early returns: exit flag, result slot, scalar operations

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
  followed by `RIfNz exitRetName (run := 0) (run := c)`;
* `forFoldReturn i lo hi body` with non-negative integer literal bounds and
  `hi ≤ 2^64` (`forBounds`) zeroes the flag and the payload slot and runs
  `RFor run (hi - lo)` over the guarded trip `exitForTrip`, which binds the
  counter `i` to `run + lo` and runs the lowered body; after an exit the guard
  skips the remaining trips (`exitForLoop`); `forFoldRevReturn` is lowered the
  same way with the counter bound to `hi - 1 - run` (`exitForLoopRev`).

**Result slot.**  A scalar variable, a scalar literal or `unitVal` in tail
position is written into `exitResName`.  `haxToLowCTFn` lowers a whole function
body: it zeroes the flag and the result slot, runs the lowered body, and when the
flag is set copies `exitValName` into `exitResName`.

**Scalar operations.**  With `sc = true`, `letBind x (app op [var a, var b])`
for hax-lean's unsigned comparisons and `add`/`sub` lowers to
`RScalarSetExpr x e` (`scalarOpExpr`); every other call keeps the tower-call
lowering of `haxToLowCT`.  The comparisons are exact over `Nat`.  LowCT's
`SAdd`/`SSub` do not reduce modulo `2^64` (`SSub` truncates at `0`), whereas
hax-lean's `add`/`sub` wrap; the simulation of those two arms carries the
no-overflow condition `a + b < 2^64` and `b ≤ a`, the condition `inRangeState`
imposes on the step from `RustExec` to the emitted code.

The translator `haxToLowCTK sc tl fl e` takes the scalar-operation mode `sc`,
whether `e` is in tail position (`tl`), and the exit context `fl`: the loop slot
of the innermost enclosing exit loop, `some exitFnSlot` in a function body
outside every exit loop, or `none` where no exit is handled (there `cfBreak` is
refused); it returns the lowered command and whether it may have exited.  The
loop slot of an exit loop is `exitRunName fl`: `"__exit_run"` at the outermost
level, one `_` appended per nesting level.  The names `exitRetName`,
`exitValName`, `exitResName`, `exitFnSlot` and `exitRunName _` are reserved:
the simulation takes as a hypothesis that the program binds none of them.

**Function-level exits.**  hax-lean emits an early `return` outside every loop
as a `cfBreak` at function level.  `haxToLowCTFn` lowers the body in the
function context `some exitFnSlot`, so such a `cfBreak` sets the exit flag like
one inside a loop; the statements after it run under `exitGuard`, and the frame
`exitFunction` copies `exitValName` into the result slot when the flag is set.

Every constructor that cannot carry an exit is lowered by `haxToLowCT` outside
tail position, and a `letBind` by `letHead`, the head context `haxToLowCT` builds
around its body (`haxToLowCT_letBind_eq_letHead`).  `exitFree` keeps the
commands that cannot exit; `haxToLowCT_eq_haxToLowCTK_none` states that
`haxToLowCT` is that projection of `haxToLowCTK false false none`.

`AnfShapedK sc tl inLoop e` is the shape predicate of `haxToLowCTK`
(`haxToLowCTK_isSome_iff_anfK`); it accepts `cfBreak` exactly when `inLoop`.

## Main results

* `haxToLowCTK`, `haxToLowCTFn`: the exit-flag lowering of an expression and of a
  function body
* `haxToLowCT_eq_haxToLowCTK_none`: `haxToLowCT` is the exit-free projection of
  `haxToLowCTK false false none`
* `haxToLowCTK_isSome_iff_anfK`: the lowering succeeds exactly on `AnfShapedK`
* `haxToLowCTFn_isSome_iff_anfK`: the function lowering succeeds exactly on
  `AnfShapedK true true true`, the shape with function-level exits
* `ExitGap`, `exitGapOf`, `haxToLowCTK_none_of_exitGap`: the early-exit
  constructors the lowering refuses, each with its name, and the refusal
* `searchLoopShape_lowers`: the search loop with an early return lowers
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpLit ImpType IntWidth)
open CatCrypt.Crypto.Jasmin.LowCT (TowerType LowCT Located SExpr)

/-! ## §1  Reserved slots and the loop, exit and result shapes -/

/-- The exit flag slot: `1` once a `cfBreak` has run, `0` otherwise. -/
def exitRetName : String := "__exit_ret"

/-- The slot holding the word a `cfBreak` returns. -/
def exitValName : String := "__exit_val"

/-- The function's result slot. -/
def exitResName : String := "__exit_res"

/-- The exit context of a function body: `haxToLowCTFn` lowers the body in
    context `some exitFnSlot`, where the function frame `exitFunction` handles an
    exit at function level. -/
def exitFnSlot : String := "__exit_fn"

/-- The loop slot of an exit loop in exit context `fl`: `"__exit_run"` outside
    every exit loop (`none` or the function context `some exitFnSlot`), and
    `r ++ "_"` inside an exit loop with loop slot `r`. -/
def exitRunName : Option String → String
  | none => "__exit_run"
  | some r => if r = exitFnSlot then "__exit_run" else r ++ "_"

/-- The function context names the same loop slot as the empty context. -/
@[simp] theorem exitRunName_fn : exitRunName (some exitFnSlot) = exitRunName none := by
  simp [exitRunName]

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

/-- The bounds of a counted loop with an exit: `some (lo, hi)` when both bounds
    are non-negative integer literals with `hi ≤ 2^64`, so that every counter
    value is a `u64` word. -/
def forBounds : ImpExpr → ImpExpr → Option (Nat × Nat)
  | .lit (.int lo), .lit (.int hi) =>
      if 0 ≤ lo ∧ 0 ≤ hi ∧ hi ≤ 2 ^ 64 then some (lo.toNat, hi.toNat) else none
  | _, _ => none

theorem forBounds_some {lo hi : ImpExpr} {l h : Nat} (hb : forBounds lo hi = some (l, h)) :
    lo = .lit (.int l) ∧ hi = .lit (.int h) ∧ h ≤ 2 ^ 64 := by
  match lo, hi, hb with
  | .lit (.int a), .lit (.int b), hb =>
    simp only [forBounds] at hb
    split at hb
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      refine ⟨?_, ?_, ?_⟩
      · rw [Int.toNat_of_nonneg hc.1]
      · rw [Int.toNat_of_nonneg hc.2.1]
      · omega
    · cases hb

/-- One trip of the lowered `forFoldReturn i lo _ body` with loop slot `run` and
    lowered body `bC`, run only when the exit flag is `0`: the counter `i` is
    bound to `run + lo` and the body runs. -/
def exitForTrip (run i : String) (lo : Nat) (bC : LowCT) : LowCT :=
  exitGuard (.RLetU64Zero i (.RSeq (.RScalarSetExpr i (.SAdd (.SVar run) (.SLit lo))) bC))

/-- The lowered `forFoldReturn i lo hi body` with loop slot `run` and lowered
    body `bC`: zero the flag and the payload slot, and run `hi - lo` trips of
    `exitForTrip` with `run` as the trip counter of `RFor`; after an exit the
    remaining trips are skipped by the guard. -/
def exitForLoop (run i : String) (lo hi : Nat) (bC : LowCT) : LowCT :=
  .RLetU64Zero exitRetName (.RLetU64Zero exitValName
    (.RFor run (hi - lo) (exitForTrip run i lo bC)))

/-- One trip of the lowered `forFoldRevReturn i _ hi body`: as `exitForTrip`,
    with the counter `i` bound to `hi - 1 - run`. -/
def exitForTripRev (run i : String) (hi : Nat) (bC : LowCT) : LowCT :=
  exitGuard (.RLetU64Zero i (.RSeq (.RScalarSetExpr i (.SSub (.SLit (hi - 1)) (.SVar run))) bC))

/-- The lowered `forFoldRevReturn i lo hi body`: as `exitForLoop`, over
    `exitForTripRev`. -/
def exitForLoopRev (run i : String) (lo hi : Nat) (bC : LowCT) : LowCT :=
  .RLetU64Zero exitRetName (.RLetU64Zero exitValName
    (.RFor run (hi - lo) (exitForTripRev run i hi bC)))

/-- Write a scalar value into `slot`: a scalar variable, a uint, nonnegative int
    or bool literal, or `unitVal` (the scalar `0`).  Any other expression is
    refused. -/
def storeScalar (slot : String) : ImpExpr → Option LowCT
  | .var x => some (.RScalarSetExpr slot (.SVar x))
  | .lit (.uintLit w n) => some (.RScalarSet slot (n % w.modulus))
  | .lit (.int n) => if 0 ≤ n then some (.RScalarSet slot n.toNat) else none
  | .lit (.bool b) => some (.RScalarSet slot (if b then 1 else 0))
  | .unitVal => some (.RScalarSet slot 0)
  | _ => none

/-- The lowered `cfBreak e`: store the payload into `exitValName` and set the
    exit flag. -/
def exitStore (e : ImpExpr) : Option LowCT :=
  (storeScalar exitValName e).map fun s => .RSeq s (.RScalarSet exitRetName 1)

/-- The lowered tail value `e`: store it into the result slot. -/
def resultStore (e : ImpExpr) : Option LowCT := storeScalar exitResName e

/-- The function frame around a lowered body `c`: zero the exit flag and the
    result slot, run `c`, and when the flag is set copy the returned word into
    the result slot. -/
def exitFunction (c : LowCT) : LowCT :=
  .RLetU64Zero exitRetName (.RLetU64Zero exitResName
    (.RSeq c (.RIfNz exitRetName (.RScalarSetExpr exitResName (.SVar exitValName)) .RSkip)))

/-! ## §2  The head of a `letBind` -/

/-- The context `haxToLowCT` places around the lowered body of
    `letBind name val body`, as a function of the lowered body; `none` when
    `haxToLowCT` refuses the right-hand side. -/
def letHead (name : String) : ImpExpr → Option (LowCT → LowCT)
  | .app f args =>
      let dt := towerOfCallName f
      let dest : Located := { locVar := name, locSrc := dt }
      match haxArgsToLocated dt args with
      | some args' => some fun bodyC =>
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
        else if scalarCallName f then
          match args with
          | [.var a, .var b] =>
              match scalarCallSExpr f (.SVar a) (.SVar b) with
              | some se => .RLetU64Zero name (.RSeq (.RScalarSetExpr name se) bodyC)
              | none => .RLetZero name dt (.RSeq (.RCall f dest args') bodyC)
          | _ => .RLetZero name dt (.RSeq (.RCall f dest args') bodyC)
        else
          .RLetZero name dt (.RSeq (.RCall f dest args') bodyC)
      | none =>
          (limbReadArgs f args).map fun p bodyC =>
            .RLetU64Zero name (.RSeq (.RScalarSetExpr name (.SLimb p.1 p.2)) bodyC)
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
    all_goals first
      | (cases limbReadArgs f args <;> rfl)
      | (split_ifs <;> (repeat' split) <;> first | rfl | simp_all)
  | var s => simp only [haxToLowCT, letHead]; cases haxToLowCT body <;> rfl
  | proj pe i =>
    cases pe with
    | var t => simp only [haxToLowCT, letHead]; cases haxToLowCT body <;> rfl
    | _ => simp only [haxToLowCT, letHead]
  | _ => simp only [haxToLowCT, letHead]

/-! ## §3  Scalar operations -/

/-- The `SExpr` of hax-lean's unsigned operation `op` on the scalars `a` and
    `b`.  Over `Nat`, `lt`, `gt`, `le`, `ge`, `eq` and `ne` are exact (each
    `SLt` is `0` or `1`, and `SSub` truncates at `0`); `add` and `sub` agree with
    hax-lean's wrapping `u64` operations when `a + b < 2^64` and `b ≤ a`. -/
def scalarOpExpr (op : String) (a b : SExpr) : Option SExpr :=
  match op with
  | "lt"  => some (.SLt a b)
  | "gt"  => some (.SLt b a)
  | "le"  => some (.SSub (.SLit 1) (.SLt b a))
  | "ge"  => some (.SSub (.SLit 1) (.SLt a b))
  | "eq"  => some (.SSub (.SSub (.SLit 1) (.SLt a b)) (.SLt b a))
  | "ne"  => some (.SAdd (.SLt a b) (.SLt b a))
  | "add" => some (.SAdd a b)
  | "sub" => some (.SSub a b)
  | _     => none

/-- The head of `letBind name val body` in scalar-operation mode `sc`: with
    `sc = true`, a scalar operation on two variables is the assignment
    `RScalarSetExpr name e`; otherwise the head is `letHead`. -/
def letHeadK (sc : Bool) (name : String) (val : ImpExpr) : Option (LowCT → LowCT) :=
  match sc, val with
  | true, .app op [.var a, .var b] =>
      match scalarOpExpr op (.SVar a) (.SVar b) with
      | some se => some fun bodyC => .RSeq (.RScalarSetExpr name se) bodyC
      | none => letHead name val
  | _, _ => letHead name val

theorem letHeadK_false (name : String) (val : ImpExpr) :
    letHeadK false name val = letHead name val := by
  unfold letHeadK; rfl

/-! ## §4  The translator -/

/-- The lowering with an exit flag and a result slot.  `sc` selects the
    scalar-operation arms, `tl` records tail position, `fl` is the exit context:
    the loop slot of the innermost enclosing exit loop, `some exitFnSlot` in a
    function body outside every exit loop, and `none` where no exit is handled
    (a `cfBreak` is refused only there); the result pairs the lowered command with whether it may have exited.  In
    tail position a scalar value is written into the result slot; outside tail
    position the constructors that carry no exit are lowered by `haxToLowCT`. -/
def haxToLowCTK (sc : Bool) : Bool → Option String → ImpExpr → Option (LowCT × Bool)
  | tl, fl, .letBind name val body =>
      match letHeadK sc name val, haxToLowCTK sc tl fl body with
      | some k, some (bC, x) => some (k bC, x)
      | _, _ => none
  | tl, fl, .seq a b =>
      match haxToLowCTK sc false fl a, haxToLowCTK sc tl fl b with
      | some (aC, xa), some (bC, xb) =>
          some (if xa then .RSeq aC (exitGuard bC) else .RSeq aC bC, xa || xb)
      | _, _ => none
  | tl, fl, .ifThenElse (.var v) t e =>
      match haxToLowCTK sc tl fl t, haxToLowCTK sc tl fl e with
      | some (tC, xt), some (eC, xe) => some (.RIfNz v tC eC, xt || xe)
      | _, _ => none
  | tl, fl, .typeAscription e _ => haxToLowCTK sc tl fl e
  | false, fl, .whileFoldReturn (.var c) body =>
      match haxToLowCTK sc false (some (exitRunName fl)) body with
      | some (bC, _) => some (exitLoop (exitRunName fl) c bC, true)
      | none => none
  | false, fl, .forFoldReturn i lo hi body =>
      match forBounds lo hi, haxToLowCTK sc false (some (exitRunName fl)) body with
      | some (l, h), some (bC, _) => some (exitForLoop (exitRunName fl) i l h bC, true)
      | _, _ => none
  | false, fl, .forFoldRevReturn i lo hi body =>
      match forBounds lo hi, haxToLowCTK sc false (some (exitRunName fl)) body with
      | some (l, h), some (bC, _) => some (exitForLoopRev (exitRunName fl) i l h bC, true)
      | _, _ => none
  | _, some _, .cfBreak e => (exitStore e).map fun s => (s, true)
  | true, _, e => (resultStore e).map fun s => (s, false)
  | false, _, e => (haxToLowCT e).map fun c => (c, false)

/-- The lowering of a function body: `haxToLowCTK` with the scalar-operation
    arms, in tail position, in the function context `some exitFnSlot`, inside the
    function frame `exitFunction`.  A `cfBreak` at function level (hax-lean's
    form of an early `return` outside every loop) sets the exit flag, and the
    frame copies its payload into the result slot. -/
def haxToLowCTFn (e : ImpExpr) : Option LowCT :=
  (haxToLowCTK true true (some exitFnSlot) e).map fun p => exitFunction p.1

/-- The commands that cannot exit: `some c` for a lowering `(c, false)`. -/
def exitFree : Option (LowCT × Bool) → Option LowCT
  | some (c, false) => some c
  | _ => none

/-- **`haxToLowCT` is the exit-free projection of `haxToLowCTK`** without the
    scalar-operation arms, outside tail position and outside every loop. -/
theorem haxToLowCT_eq_haxToLowCTK_none (e : ImpExpr) :
    haxToLowCT e = exitFree (haxToLowCTK false false none e) := by
  have hmap : ∀ o : Option LowCT, exitFree (o.map fun c => (c, false)) = o := by
    intro o; cases o <;> rfl
  induction e using ImpExpr.ind with
  | letBind n val body _ ihb =>
    rw [haxToLowCT_letBind_eq_letHead, ihb]
    simp only [haxToLowCTK, letHeadK_false]
    rcases letHead n val with _ | k <;>
      rcases haxToLowCTK false false none body with _ | ⟨bC, _ | _⟩ <;> rfl
  | seq a b iha ihb =>
    simp only [haxToLowCT, haxToLowCTK]
    rw [iha, ihb]
    rcases haxToLowCTK false false none a with _ | ⟨aC, _ | _⟩ <;>
      rcases haxToLowCTK false false none b with _ | ⟨bC, _ | _⟩ <;> rfl
  | ifThenElse c t e _ iht ihe =>
    cases c with
    | var v =>
      simp only [haxToLowCT, haxToLowCTK]
      rw [iht, ihe]
      rcases haxToLowCTK false false none t with _ | ⟨tC, _ | _⟩ <;>
        rcases haxToLowCTK false false none e with _ | ⟨eC, _ | _⟩ <;> rfl
    | _ => simp only [haxToLowCTK]; exact (hmap _).symm
  | typeAscription e _ ih => simp only [haxToLowCT, haxToLowCTK]; exact ih
  | whileFoldReturn c body _ _ =>
    cases c with
    | var v =>
      simp only [haxToLowCT, haxToLowCTK]
      rcases haxToLowCTK false false (some (exitRunName none)) body with _ | ⟨bC, _⟩ <;> rfl
    | _ => simp only [haxToLowCTK]; exact (hmap _).symm
  | forFoldReturn i lo hi body _ _ _ =>
    simp only [haxToLowCT, haxToLowCTK]
    rcases forBounds lo hi with _ | ⟨l, h⟩ <;>
      rcases haxToLowCTK false false (some (exitRunName none)) body with _ | ⟨bC, _⟩ <;> rfl
  | forFoldRevReturn i lo hi body _ _ _ =>
    simp only [haxToLowCT, haxToLowCTK]
    rcases forBounds lo hi with _ | ⟨l, h⟩ <;>
      rcases haxToLowCTK false false (some (exitRunName none)) body with _ | ⟨bC, _⟩ <;> rfl
  | _ => simp only [haxToLowCTK]; exact (hmap _).symm

/-- Outside every `whileFoldReturn` a `cfBreak` is refused. -/
theorem haxToLowCTK_none_cfBreak (sc tl : Bool) (e : ImpExpr) :
    haxToLowCTK sc tl none (.cfBreak e) = none := by
  cases tl <;> rfl

/-! ## §5  The shape predicate -/

/-- The shape `haxToLowCTK sc tl` accepts, with `inLoop` recording whether the
    expression sits in an exit context (an exit-loop body or a function body
    lowered by `haxToLowCTFn`): a `letBind` whose head
    `letHeadK sc` accepts and whose body has the shape; `seq` (its first
    component outside tail position), `ifThenElse` on a variable and a type
    ascription with components of the shape; outside tail position a
    `whileFoldReturn` on a variable whose body has the shape inside the loop; a
    `cfBreak` of a scalar value inside a loop; in tail position a scalar value;
    and outside tail position every other expression `AnfShaped` accepts. -/
def AnfShapedK (sc : Bool) : Bool → Bool → ImpExpr → Bool
  | tl, il, .letBind name val body => (letHeadK sc name val).isSome && AnfShapedK sc tl il body
  | tl, il, .seq a b => AnfShapedK sc false il a && AnfShapedK sc tl il b
  | tl, il, .ifThenElse (.var _) t e => AnfShapedK sc tl il t && AnfShapedK sc tl il e
  | tl, il, .typeAscription e _ => AnfShapedK sc tl il e
  | false, _, .whileFoldReturn (.var _) body => AnfShapedK sc false true body
  | false, _, .forFoldReturn _ lo hi body => (forBounds lo hi).isSome && AnfShapedK sc false true body
  | false, _, .forFoldRevReturn _ lo hi body =>
      (forBounds lo hi).isSome && AnfShapedK sc false true body
  | _, true, .cfBreak e => (exitStore e).isSome
  | true, _, e => (resultStore e).isSome
  | false, _, e => AnfShaped e

/-- **The shape biconditional of `haxToLowCTK`.** The translator with loop slot
    `fl` succeeds exactly on the expressions of shape `AnfShapedK sc tl fl.isSome`. -/
theorem haxToLowCTK_isSome_iff_anfK (sc tl : Bool) (fl : Option String) (e : ImpExpr) :
    (haxToLowCTK sc tl fl e).isSome = true ↔ AnfShapedK sc tl fl.isSome e = true := by
  suffices h : ∀ tl fl, (haxToLowCTK sc tl fl e).isSome = AnfShapedK sc tl fl.isSome e by
    rw [h]
  have hanf : ∀ e : ImpExpr, (haxToLowCT e).isSome = AnfShaped e := by
    intro e
    cases h : AnfShaped e
    · exact Bool.eq_false_iff.mpr (fun h' => by
        rw [(haxToLowCT_isSome_iff_anf e).mp h'] at h; cases h)
    · exact (haxToLowCT_isSome_iff_anf e).mpr h
  induction e using ImpExpr.ind with
  | letBind n val body _ ihb =>
    intro tl fl
    simp only [haxToLowCTK, AnfShapedK]
    rw [← ihb tl fl]
    rcases letHeadK sc n val with _ | k <;>
      rcases haxToLowCTK sc tl fl body with _ | ⟨bC, x⟩ <;> rfl
  | seq a b iha ihb =>
    intro tl fl
    simp only [haxToLowCTK, AnfShapedK]
    rw [← iha false fl, ← ihb tl fl]
    rcases haxToLowCTK sc false fl a with _ | ⟨aC, xa⟩ <;>
      rcases haxToLowCTK sc tl fl b with _ | ⟨bC, xb⟩ <;> rfl
  | ifThenElse c t e _ iht ihe =>
    intro tl fl
    cases c with
    | var v =>
      simp only [haxToLowCTK, AnfShapedK]
      rw [← iht tl fl, ← ihe tl fl]
      rcases haxToLowCTK sc tl fl t with _ | ⟨tC, xt⟩ <;>
        rcases haxToLowCTK sc tl fl e with _ | ⟨eC, xe⟩ <;> rfl
    | _ => cases tl <;> rfl
  | typeAscription e _ ih =>
    intro tl fl; simp only [haxToLowCTK, AnfShapedK]; exact ih tl fl
  | whileFoldReturn c body _ ihb =>
    intro tl fl
    cases tl with
    | true => cases c <;> rfl
    | false =>
      cases c with
      | var v =>
        simp only [haxToLowCTK, AnfShapedK]
        have h := ihb false (some (exitRunName fl))
        rw [Option.isSome_some] at h
        rw [← h]
        rcases haxToLowCTK sc false (some (exitRunName fl)) body with _ | ⟨bC, x⟩ <;> rfl
      | _ => simp only [haxToLowCTK, AnfShapedK, Option.isSome_map]; exact hanf _
  | forFoldReturn i lo hi body _ _ ihb =>
    intro tl fl
    cases tl with
    | true => rfl
    | false =>
      simp only [haxToLowCTK, AnfShapedK]
      have h := ihb false (some (exitRunName fl))
      rw [Option.isSome_some] at h
      rw [← h]
      rcases forBounds lo hi with _ | ⟨l, hb⟩ <;>
        rcases haxToLowCTK sc false (some (exitRunName fl)) body with _ | ⟨bC, x⟩ <;> rfl
  | forFoldRevReturn i lo hi body _ _ ihb =>
    intro tl fl
    cases tl with
    | true => rfl
    | false =>
      simp only [haxToLowCTK, AnfShapedK]
      have h := ihb false (some (exitRunName fl))
      rw [Option.isSome_some] at h
      rw [← h]
      rcases forBounds lo hi with _ | ⟨l, hb⟩ <;>
        rcases haxToLowCTK sc false (some (exitRunName fl)) body with _ | ⟨bC, x⟩ <;> rfl
  | cfBreak e _ =>
    intro tl fl
    cases fl with
    | none => cases tl <;> rfl
    | some r => cases tl <;> simp only [haxToLowCTK, AnfShapedK, Option.isSome_map,
        Option.isSome_some]
  | _ =>
    intro tl fl
    cases tl
    all_goals simp only [haxToLowCTK, AnfShapedK, Option.isSome_map]
    all_goals first | rfl | exact hanf _

/-! ## §6  Agreement with the representability filter -/

/-- A representable expression at context `inLoop` that has the translator's
    shape inside a loop has the shape at `inLoop`: the filter confines `cfBreak`
    to `whileFoldReturn` bodies. -/
theorem anfShapedK_of_representable (sc tl inLoop : Bool) (e : ImpExpr)
    (hrep : LowCTRepresentable.ExprIn inLoop e = true)
    (hanf : AnfShapedK sc tl true e = true) : AnfShapedK sc tl inLoop e = true := by
  induction e using ImpExpr.ind generalizing tl inLoop with
  | letBind n val body _ ihb =>
    simp only [AnfShapedK, LowCTRepresentable.ExprIn, Bool.and_eq_true] at hrep hanf ⊢
    exact ⟨hanf.1, ihb tl inLoop hrep.2 hanf.2⟩
  | seq a b iha ihb =>
    simp only [AnfShapedK, LowCTRepresentable.ExprIn, Bool.and_eq_true] at hrep hanf ⊢
    exact ⟨iha false inLoop hrep.1 hanf.1, ihb tl inLoop hrep.2 hanf.2⟩
  | ifThenElse c t e _ iht ihe =>
    cases c with
    | var v =>
      simp only [AnfShapedK, LowCTRepresentable.ExprIn, Bool.and_eq_true] at hrep hanf ⊢
      exact ⟨iht tl inLoop hrep.1.2 hanf.1, ihe tl inLoop hrep.2 hanf.2⟩
    | _ => cases tl <;> (simp only [AnfShapedK] at hanf ⊢; exact hanf)
  | typeAscription e _ ih =>
    simp only [AnfShapedK, LowCTRepresentable.ExprIn] at hrep hanf ⊢
    exact ih tl inLoop hrep hanf
  | cfBreak e _ =>
    cases inLoop with
    | true => exact hanf
    | false => simp [LowCTRepresentable.ExprIn] at hrep
  | whileFoldReturn c body _ _ =>
    cases tl <;> cases c <;> (simp only [AnfShapedK] at hanf ⊢; exact hanf)
  | _ => cases tl <;> (simp only [AnfShapedK] at hanf ⊢; exact hanf)

/-- **Filter and translator agree.** A representable expression of the
    translator's in-loop shape is lowered by `haxToLowCTK sc tl none`. The
    representability hypothesis rules out a `cfBreak` outside every
    `whileFoldReturn` body, which the in-loop shape admits. -/
theorem haxToLowCTK_isSome_of_representable_and_anfK (sc tl : Bool) (e : ImpExpr)
    (hrep : LowCTRepresentable.Expr e = true) (hanf : AnfShapedK sc tl true e = true) :
    (haxToLowCTK sc tl none e).isSome = true :=
  (haxToLowCTK_isSome_iff_anfK sc tl none e).mpr
    (anfShapedK_of_representable sc tl false e hrep hanf)

/-- **The shape biconditional of `haxToLowCTFn`.** The function lowering succeeds
    exactly on the tail-position shape with exits allowed at function level. -/
theorem haxToLowCTFn_isSome_iff_anfK (e : ImpExpr) :
    (haxToLowCTFn e).isSome = true ↔ AnfShapedK true true true e = true := by
  rw [haxToLowCTFn, Option.isSome_map]
  exact haxToLowCTK_isSome_iff_anfK true true (some exitFnSlot) e

/-! ## §7  The refused early-exit constructors -/

/-- The early-exit constructors `haxToLowCTK` refuses, each named by its
    construct: an `earlyReturn` or `questionMark` (which `Hax.pipeline` rewrites
    into a `cfBreak` inside a `whileFoldReturn`), a `cfContinue` or
    `cfBreakContinue`, and a bare `break_` or `continue_`. -/
inductive ExitGap where
  | earlyReturn
  | questionMark
  | cfContinue
  | cfBreakContinue
  | breakOutsideFold
  | continueOutsideFold
  deriving DecidableEq, Repr, BEq

/-- The `ExitGap` of an expression, or `none` when its head constructor is not
    one of the refused ones. -/
def exitGapOf : ImpExpr → Option ExitGap
  | .earlyReturn _ => some .earlyReturn
  | .questionMark _ => some .questionMark
  | .cfContinue _ => some .cfContinue
  | .cfBreakContinue _ => some .cfBreakContinue
  | .break_ _ => some .breakOutsideFold
  | .continue_ => some .continueOutsideFold
  | _ => none

/-- `haxToLowCTK` refuses every expression with an `ExitGap`, in every mode, at
    every tail position and in every loop context. -/
theorem haxToLowCTK_none_of_exitGap (sc tl : Bool) (fl : Option String) (e : ImpExpr)
    (g : ExitGap) (h : exitGapOf e = some g) : haxToLowCTK sc tl fl e = none := by
  cases e <;> simp only [exitGapOf, reduceCtorEq] at h <;> cases tl <;> cases fl <;> rfl

/-! ## §8  The pipeline shape of a search loop

`searchLoopShape` is the output of `Hax.pipeline` on the search loop of
`Ascent/Demos/EarlyExit.lean` at `x = 1` (`searchU_pipeline`).  The theorem below
is a static check that pins that `haxToLowCTFn` lowers it; it closes by `decide`
in milliseconds. -/

/-- The pipeline output of the search loop at `x = 1`. -/
def searchLoopShape : ImpExpr :=
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
         (.lit (.uintLit .w64 100)))))))

/-- The function lowering accepts the search loop's pipeline output. -/
theorem searchLoopShape_lowers : (haxToLowCTFn searchLoopShape).isSome = true := by
  decide

end CatCrypt.Crypto.Hax
