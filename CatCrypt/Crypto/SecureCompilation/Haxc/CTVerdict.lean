/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.CTPub

@[expose] public section

set_option autoImplicit false

/-!
# The result of a layout's constant-time gate on bytes, with the refusal reason

`σ.ctRefusal bytes` is `none` when the gate `AbiLayout.ctGateB` of `CTPub` accepts `bytes`
from the public entry set `σ.pubA`, and otherwise the reason: the bytes do not decode, or the
first index at which the array decision `DecodedCT.bytesCTCheckFast` fails, as
`DecodedCT.firstFailureA` names it. `σ.ctVerdict bytes` is the same as one table field: `ct`
or `refused:<reason>`.

The acceptance executables `field-bytes-emit` and `mpn-bytes-emit` print `σ.ctVerdict` of the
bytes of each accepted program, under the layout `σ` of its `compileRegion` call.

## Main results

* `AbiLayout.ctRefusal`, `AbiLayout.ctVerdict` — the refusal reason and the table field.
* `AbiLayout.ctRefusal_eq_none_iff` — no refusal exactly when the gate accepts.
* `AbiLayout.ctRefusal_none_sound` — bytes without a refusal decode to a program whose runs
  from entry states agreeing on the public data of `σ`, with every step satisfying
  `FrameSep (σ.ctFrame prog)`, have equal leakage traces.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.CT (ConstantTimeRel)

namespace AbiLayout

/-- The reason the gate `σ.ctGateB` refuses `bytes`, or `none` when it accepts them: the
    bytes do not decode, or the first failing index of the array decision from `σ.pubA` with
    the reason `firstFailureA` gives. -/
def ctRefusal (σ : AbiLayout) (bytes : List (BitVec 8)) : Option String :=
  if σ.ctGateB bytes then none
  else
    match decodeLprog bytes with
    | none => some "bytes do not decode"
    | some prog =>
        let c := fastCert prog σ.pubA
        match firstFailureA ctRegime σ.pubA prog.toArray c.1 c.2 with
        | some (pc, why) => some s!"{why} at {pc}"
        | none => some "no failing index found"

/-- There is no refusal exactly when the gate accepts the bytes. -/
theorem ctRefusal_eq_none_iff (σ : AbiLayout) (bytes : List (BitVec 8)) :
    σ.ctRefusal bytes = none ↔ σ.ctGateB bytes = true := by
  unfold ctRefusal
  by_cases h : σ.ctGateB bytes = true
  · simp [h]
  · simp only [h, Bool.false_eq_true, ↓reduceIte, iff_false]
    split
    · simp
    · split <;> simp

/-- Bytes without a refusal decode to a program `prog` whose runs from index `0`, with every
    step satisfying `FrameSep (σ.ctFrame prog)`, from entry states agreeing on the public data
    of `σ`, have equal leakage traces. -/
theorem ctRefusal_none_sound {σ : AbiLayout} {bytes : List (BitVec 8)}
    (h : σ.ctRefusal bytes = none) :
    ∃ prog, decodeLprog bytes = some prog ∧
      ConstantTimeRel σ.PubAgree
        (fun sa t => ∃ sa', RunL ctRegime (FrameSep (σ.ctFrame prog)) prog 0 sa t sa') :=
  ctGateB_sound ((ctRefusal_eq_none_iff σ bytes).mp h)

/-- The result of the gate on `bytes` as one table field: `ct`, or `refused:` followed by
    the reason of `σ.ctRefusal`. -/
def ctVerdict (σ : AbiLayout) (bytes : List (BitVec 8)) : String :=
  match σ.ctRefusal bytes with
  | none => "ct"
  | some why => s!"refused:{why}"

end AbiLayout

end CatCrypt.Crypto.SecureCompilation.Haxc
