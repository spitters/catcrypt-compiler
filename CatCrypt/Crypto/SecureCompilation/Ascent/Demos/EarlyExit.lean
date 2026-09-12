/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Exit

/-!
# Demo: a search loop with an early return, read as an exception program

The source is hax-lean's raw `ImpExpr` `searchU x` for

```
let three = 3u64; let one = 1u64; let xv = x; let i = 0u64; let c = i < three;
while c { let e = xv <= i; if e { return i }; i = i + one; c = i < three };
100u64
```

The loop index runs over `0, 1, 2`; the loop returns the first index at or above
`x`, and when there is none the program falls through to `100`.

* `searchU_pipeline` — `Hax.pipeline` rewrites the loop into `whileFoldReturn`, the
  early return into `cfBreak`, and each assignment into a rebinding `letBind`.
* `searchU_denote_found` / `searchU_denote_notFound` — the reference run at
  `x = 1` returns early with `1`; at `x = 5` it falls through with `100`.
* `searchAbs` — the abstract exception program: `whileE` over the loop index,
  the step `searchStep` throwing the index once it reaches `x`, and `pure 100`
  after the loop.
* `searchU_except_found` / `searchU_except_notFound` — the pipeline's encoded
  outcome, read by `outcomeExceptCF`, is the run of `searchAbs`
  (`pipeline_exceptProg`).
* `searchU_word_found` / `searchU_word_notFound` — the pipeline's output word
  read by `haxOutcomeWordCF`.

The builtin table is `searchBuiltins`, hax-lean's unsigned comparison and
arithmetic tables; `searchBuiltins_deepNoControlFlow` is the table contract
`pipeline_full_correct` takes.

Part of the AutoCorres-in-Lean ascent begun by Sebastian Graf (sgraf812/ascent).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos

/-! ## The builtin table -/

/-- hax-lean's unsigned comparison table before its unsigned arithmetic table: the
    operations the search loop uses (`lt`, `le`, `add` on `uint` words). -/
def searchBuiltins : _root_.Hax.Builtins := fun f args =>
  _root_.Hax.widthCmpOps f args <|> _root_.Hax.widthArithOps f args

/-- A table that tries a `DeepNoControlFlow` table and falls back to another is
    `DeepNoControlFlow`. -/
theorem deepNoControlFlow_orElse (t₁ t₂ : _root_.Hax.Builtins)
    (h₁ : _root_.Hax.Builtins.DeepNoControlFlow t₁)
    (h₂ : _root_.Hax.Builtins.DeepNoControlFlow t₂) :
    _root_.Hax.Builtins.DeepNoControlFlow (fun f a => t₁ f a <|> t₂ f a) := by
  intro f args v h hargs
  cases ht : t₁ f args with
  | some w =>
      simp only [ht, HOrElse.hOrElse, OrElse.orElse, Option.orElse, Option.some.injEq] at h
      exact h ▸ h₁ f args w ht hargs
  | none =>
      simp only [ht, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at h
      exact h₂ f args v h hargs

/-- The unsigned comparison table returns booleans only. -/
theorem widthCmpOps_deepNoControlFlow :
    _root_.Hax.Builtins.DeepNoControlFlow _root_.Hax.widthCmpOps := by
  intro f args v h _
  revert h; unfold _root_.Hax.widthCmpOps
  split <;> intro h <;> cases h <;> simp [_root_.Hax.Value.deepNoControlFlow]

/-- The unsigned arithmetic table returns `uint` words only. -/
theorem widthArithOps_deepNoControlFlow :
    _root_.Hax.Builtins.DeepNoControlFlow _root_.Hax.widthArithOps := by
  intro f args v h _
  revert h; unfold _root_.Hax.widthArithOps
  split <;> intro h <;> (try split at h) <;> cases h <;>
    simp [_root_.Hax.Value.deepNoControlFlow, _root_.Hax.wrapUint]

/-- `searchBuiltins` never fabricates a control-flow value. -/
theorem searchBuiltins_deepNoControlFlow :
    _root_.Hax.Builtins.DeepNoControlFlow searchBuiltins :=
  deepNoControlFlow_orElse _ _ widthCmpOps_deepNoControlFlow widthArithOps_deepNoControlFlow

/-! ## The source program and what the pipeline makes of it -/

/-- The search loop: the first index in `0, 1, 2` at or above `x` is returned from
    inside the loop; without one the program falls through to `100`. Every guard is
    a variable and every call argument a variable, the shape an extraction has. -/
def searchU (x : Nat) : _root_.Hax.ImpExpr :=
  .letBind "three" (.lit (.uintLit .w64 3))
   (.letBind "one" (.lit (.uintLit .w64 1))
    (.letBind "xv" (.lit (.uintLit .w64 x))
     (.letBind "i" (.lit (.uintLit .w64 0))
      (.letBind "c" (.app "lt" [.var "i", .var "three"])
       (.seq
         (.whileLoop (.var "c")
           (.letBind "e" (.app "le" [.var "xv", .var "i"])
             (.seq
               (.ifThenElse (.var "e") (.earlyReturn (.var "i")) .unitVal)
               (.seq
                 (.assign "i" (.app "add" [.var "i", .var "one"]))
                 (.assign "c" (.app "lt" [.var "i", .var "three"]))))))
         (.lit (.uintLit .w64 100)))))))

/-- The pipeline's output for `searchU x`: the `whileLoop` becomes a
    `whileFoldReturn`, the `earlyReturn` a `cfBreak`, and each assignment a
    `letBind` rebinding the name. -/
theorem searchU_pipeline (x : Nat) :
    _root_.Hax.pipeline (searchU x) =
      .letBind "three" (.lit (.uintLit .w64 3))
       (.letBind "one" (.lit (.uintLit .w64 1))
        (.letBind "xv" (.lit (.uintLit .w64 x))
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
             (.lit (.uintLit .w64 100))))))) := rfl

/-- `searchU x` is loop-scoped: it has no `break` or `continue`. -/
theorem searchU_loopScoped (x : Nat) : _root_.Hax.LoopScoped (searchU x) := by
  unfold searchU
  repeat' first
    | constructor
    | (intro a ha
       simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
       rcases ha with rfl | rfl)

/-- `searchU x` has no `?` node. -/
theorem searchU_noQuestionMark (x : Nat) : _root_.Hax.NoQuestionMark (searchU x) := by
  unfold searchU
  repeat' first
    | constructor
    | (intro a ha
       simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
       rcases ha with rfl | rfl)

/-- `searchU x` has none of the pipeline's fold constructors. -/
theorem searchU_noCFConstructors (x : Nat) : _root_.Hax.NoCFConstructors (searchU x) := by
  unfold searchU
  repeat' first
    | constructor
    | (intro a ha
       simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
       rcases ha with rfl | rfl)

/-! ## The reference runs -/

/-- At `x = 1` the reference run returns early with the index `1`. -/
theorem searchU_denote_found :
    (_root_.Hax.denote searchBuiltins 8 (searchU 1) _root_.Hax.Env.empty).1
      = .earlyRet (.uint .w64 1) := by
  simp [searchU, searchBuiltins, _root_.Hax.denote, _root_.Hax.denoteWhile,
    _root_.Hax.denoteArgs, bind, StateT.bind, pure, StateT.pure, get, getThe,
    MonadStateOf.get, StateT.get, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    _root_.Hax.Value.ofLit, _root_.Hax.Env.extend, _root_.Hax.widthCmpOps,
    _root_.Hax.widthArithOps, _root_.Hax.wrapUint, _root_.Hax.IntWidth.modulus,
    _root_.Hax.IntWidth.bits]

/-- At `x = 5` no index qualifies and the reference run falls through with `100`. -/
theorem searchU_denote_notFound :
    (_root_.Hax.denote searchBuiltins 8 (searchU 5) _root_.Hax.Env.empty).1
      = .val (.uint .w64 100) := by
  simp [searchU, searchBuiltins, _root_.Hax.denote, _root_.Hax.denoteWhile,
    _root_.Hax.denoteArgs, bind, StateT.bind, pure, StateT.pure, get, getThe,
    MonadStateOf.get, StateT.get, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    _root_.Hax.Value.ofLit, _root_.Hax.Env.extend, _root_.Hax.widthCmpOps,
    _root_.Hax.widthArithOps, _root_.Hax.wrapUint, _root_.Hax.IntWidth.modulus,
    _root_.Hax.IntWidth.bits]

/-! ## The abstract exception program -/

/-- One trip of the search loop on the loop index: throw the index once it reaches
    `x`, otherwise step to the next index. -/
def searchStep (x i : Nat) : ExceptT _root_.Hax.Value Id Nat :=
  if x ≤ i then throw (.uint .w64 i) else pure (i + 1)

/-- The search loop as an exception program: `whileE` over the index with the
    guard `i < 3` and the step `searchStep x`, then the fall-through value `100`. -/
def searchAbs (x fuel : Nat) : ExceptT _root_.Hax.Value Id _root_.Hax.Value := do
  let _ ← whileE (fun i => decide (i < 3)) (searchStep x) fuel 0
  pure (.uint .w64 100)

/-- At `x = 1` the abstract program throws `1`. -/
theorem searchAbs_found : (searchAbs 1 8).run = .error (.uint .w64 1) := rfl

/-- At `x = 5` the abstract program returns `100`. -/
theorem searchAbs_notFound : (searchAbs 5 8).run = .ok (.uint .w64 100) := rfl

/-! ## The pipeline's outcome is the abstract program's run -/

/-- **Found.** The pipeline's encoded outcome at `x = 1`, read as an exception, is
    the run of `searchAbs 1`: the thrown index `1`. -/
theorem searchU_except_found :
    outcomeExceptCF
      (_root_.Hax.denote' searchBuiltins 8 (_root_.Hax.pipeline (searchU 1))
        _root_.Hax.Env.empty).1
      = some (searchAbs 1 8).run :=
  pipeline_exceptProg searchBuiltins searchBuiltins_deepNoControlFlow (searchU 1)
    (searchU_loopScoped 1) (searchU_noQuestionMark 1) (searchU_noCFConstructors 1) 8
    _root_.Hax.Env.empty _root_.Hax.Env.NoControlFlow.empty (searchAbs 1 8)
    (by rw [searchU_denote_found, searchAbs_found]; rfl)

/-- **Not found.** The pipeline's encoded outcome at `x = 5`, read as an exception,
    is the run of `searchAbs 5`: the normal result `100`. -/
theorem searchU_except_notFound :
    outcomeExceptCF
      (_root_.Hax.denote' searchBuiltins 8 (_root_.Hax.pipeline (searchU 5))
        _root_.Hax.Env.empty).1
      = some (searchAbs 5 8).run :=
  pipeline_exceptProg searchBuiltins searchBuiltins_deepNoControlFlow (searchU 5)
    (searchU_loopScoped 5) (searchU_noQuestionMark 5) (searchU_noCFConstructors 5) 8
    _root_.Hax.Env.empty _root_.Hax.Env.NoControlFlow.empty (searchAbs 5 8)
    (by rw [searchU_denote_notFound, searchAbs_notFound]; rfl)

/-! ## The output word -/

/-- **Found.** The pipeline's output word at `x = 1` is `1`: the early return's
    payload survives the control-flow encoding. -/
theorem searchU_word_found :
    haxOutcomeWordCF
      (_root_.Hax.denote' searchBuiltins 8 (_root_.Hax.pipeline (searchU 1))
        _root_.Hax.Env.empty).1
      = some (BitVec.ofNat 64 1) := by
  rw [_root_.Hax.pipeline_full_correct searchBuiltins searchBuiltins_deepNoControlFlow (searchU 1)
    (searchU_loopScoped 1) (searchU_noQuestionMark 1) (searchU_noCFConstructors 1) 8
    _root_.Hax.Env.empty _root_.Hax.Env.NoControlFlow.empty]
  show haxOutcomeWordCF (_root_.Hax.Outcome.encodeCF
    (_root_.Hax.denote searchBuiltins 8 (searchU 1) _root_.Hax.Env.empty).1) = _
  rw [searchU_denote_found, haxOutcomeWordCF_encodeCF_earlyRet]
  rfl

/-- **Not found.** The pipeline's output word at `x = 5` is the fall-through `100`. -/
theorem searchU_word_notFound :
    haxOutcomeWordCF
      (_root_.Hax.denote' searchBuiltins 8 (_root_.Hax.pipeline (searchU 5))
        _root_.Hax.Env.empty).1
      = some (BitVec.ofNat 64 100) := by
  rw [_root_.Hax.pipeline_full_correct searchBuiltins searchBuiltins_deepNoControlFlow (searchU 5)
    (searchU_loopScoped 5) (searchU_noQuestionMark 5) (searchU_noCFConstructors 5) 8
    _root_.Hax.Env.empty _root_.Hax.Env.NoControlFlow.empty]
  show haxOutcomeWordCF (_root_.Hax.Outcome.encodeCF
    (_root_.Hax.denote searchBuiltins 8 (searchU 5) _root_.Hax.Env.empty).1) = _
  rw [searchU_denote_notFound]
  rfl

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos
