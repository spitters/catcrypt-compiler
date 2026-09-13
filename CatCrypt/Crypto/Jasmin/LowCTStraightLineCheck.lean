/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.LowCTReflect
public import Std.Data.HashSet

/-!
# Dataflow checks for straight-line `LowCT` call chains

A hand-written `LowCT` orchestration body built only from `RSkip`, `RSeq` and
`RCall` is a sequence of leaf calls, each writing one destination slot and
reading a list of argument slots. This module computes that sequence and two
dataflow properties of a `ReifiedFunc` whose body has this shape:

* the call arguments that are read before any definition, i.e. neither a
  function argument nor the destination of an earlier call;
* the call destinations that no later call reads and that are not outputs of
  the function.

The checks are syntactic over slot names. They say nothing about what the
leaves compute. Reflect modules evaluate them with `#guard`, which fails
elaboration when the computed list differs from the stated one.

## Main definitions

* `LowCT.straightCalls` — the ordered `(destination, arguments)` list of a
  straight-line body, or `none` for any other constructor.
* `straightLineUndefined` — arguments read before definition.
* `straightLineUnread` — destinations never read afterwards, excluding the
  function outputs.
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.LowCTReflect

open CatCrypt.Crypto.Jasmin.LowCT

/-- Accumulator form of `LowCT.straightCalls`: appends the calls of `c`, in
    execution order, to `acc`. Returns `none` when `c` contains a constructor
    other than `RSkip`, `RSeq` or `RCall`. -/
def LowCT.straightCallsAux :
    LowCT → Array (String × List String) → Option (Array (String × List String))
  | .RSkip, acc => some acc
  | .RSeq c d, acc => (LowCT.straightCallsAux c acc).bind (LowCT.straightCallsAux d)
  | .RCall _ dst args, acc => some (acc.push (dst.locVar, args.map (·.locVar)))
  | _, _ => none

/-- The leaf calls of a straight-line body in execution order, each as the
    destination slot name paired with the argument slot names. Returns `none`
    when the body contains a constructor other than `RSkip`, `RSeq` or
    `RCall`. -/
def LowCT.straightCalls (c : LowCT) : Option (List (String × List String)) :=
  (LowCT.straightCallsAux c #[]).map Array.toList

/-- The call arguments of `f`'s straight-line body that are neither an
    argument of `f` nor the destination of an earlier call, listed in
    execution order with one entry per occurrence. Returns `none` when the body
    is not straight-line. -/
def straightLineUndefined (f : ReifiedFunc) : Option (List String) :=
  (LowCT.straightCallsAux f.body #[]).map fun calls =>
    let init : Std.HashSet String × Array String :=
      (Std.HashSet.ofList (f.args.map Prod.fst), #[])
    let res := calls.foldl (init := init) fun (defined, missing) (dst, args) =>
      let missing := args.foldl (init := missing) fun m a =>
        if defined.contains a then m else m.push a
      (defined.insert dst, missing)
    res.2.toList

/-- The destinations of `f`'s straight-line body that no later call reads,
    excluding `f.retName` and the names in `f.outNames`, listed in execution
    order with one entry per call. Returns `none` when the body is not
    straight-line. -/
def straightLineUnread (f : ReifiedFunc) : Option (List String) :=
  (LowCT.straightCallsAux f.body #[]).map fun calls =>
    let outs : Std.HashSet String := Std.HashSet.ofList (f.retName :: f.outNames)
    let init : Std.HashSet String × Array String := (∅, #[])
    let res := calls.foldr (init := init) fun (dst, args) (readLater, unread) =>
      let unread :=
        if outs.contains dst || readLater.contains dst then unread else unread.push dst
      (args.foldl (init := readLater) fun s a => s.insert a, unread)
    res.2.reverse.toList

end CatCrypt.Crypto.Jasmin.LowCTReflect
