/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
import all Init.Data.Array.Range
import all Init.Data.List.Sort.Basic
import all Init.Data.List.Sort.Impl

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 100000

/-!
# Which primitives of the physical-ABI export reduce in the kernel

`VIR.JasminLprogExport.Com.toLprogPhysAbi` and its consumer
`X86Backend.CompileComToElfJInstrFull.physBodyOf` have no normal form:
`(physBodyOf c "f").length = n` closes under neither `rfl` nor `decide`. This
module records which of the primitives those definitions are built from reduce
inside the module system and which do not, so a claim about the export's
reducibility can be read off the primitive rather than rediscovered by bisecting
an eight-thousand-line file.

Irreducibility is a property of a constant, not a proposition, so the negative
half of the record is prose. The positive half is the theorems below: each one
is a form the exporter could use in place of a stuck one, or a form the `import
all` lines above unseal, checked by the kernel at the sizes the export uses.

The obstructions fall into two families. The first is the module system sealing
a core combinator, and is lifted by an `import all` line in the module that
states the equation — no change to the exporter. The second is the Lean 4.33
`String` API, and is not.

## Family 1: core combinators the module system seals

An `import all` line applies to the module it names and is not transitive, so
each of these has to be repeated in every module that states an equation
reaching it.

* `toString : Nat → String` — the register and argument names `regName` and
  `argName` build are `"r" ++ toString k` and `"a" ++ toString j`.
  `import all Init.Data.Repr` unseals it. `JasminLprogExport` already carries
  that line for its own elaboration.

* `List.MergeSort.Internal.splitInTwo` and `mergeFuel`, behind
  `JasminLprogExport.kernelMergeSort`, which `physLiveData` sorts the live
  intervals with, and hence `physLiveItems`, `physAssign` and
  `physAssignClassed`. `import all Init.Data.List.Sort.Basic` and
  `import all Init.Data.List.Sort.Impl` unseal it, and the linear scan then
  reduces: `physAssign` on a two-operation body closes by `decide`. `kernelMergeSort`
  is itself the fuelled replacement for `List.mergeSort`, which has no normal
  form with or without the `import all`.

* `Array.range` — `import all Init.Data.Array.Range` unseals it.

* `Array.map` — `Init.Data.Array.Basic` declares it, but `import all` on that
  module does not unseal it: `(#[1, 2, 3].map f).size` is stuck on a literal
  array. `physTable` and `physTableClassed` are `(Array.range univ).map …`, so
  the allocation table has no normal form even with every `import all` line
  above. `((List.range n).map f).toArray` computes the same array and reduces,
  which is the restatement available.

* `for _ in [0:n]` over `Std.Range` — stuck. Used once, in
  `straightCallRelocTableCore`, which `straightCallComposeTable` guards behind
  `bodyStraightCall`, so a call-free body does not reach it. A `List.range`
  fold is the restatement.

## Family 2: the Lean 4.33 `String` API

Every declaration named below lives in
`CatCrypt/Crypto/SecureCompilation/VIR/JasminLprogExport.lean`.

* `String.startsWith` — no normal form at any transparency inside a `module`
  (`with_unfolding_all rfl` fails; the same application reduces in a non-module
  file). `import all` on `Init.Data.String.Basic` and `Init.Data.Slice` does not
  lift it. Used by `parseCallW`, which `expandCallShadows` applies to every
  `Lopn` at the first step of `comToLfundefPhysAbiFromVirt`; by `isVectorMnem`,
  reached through `bodyVecSlots` → `physTableOut`; by `bodyHasMulHi`, reached
  through `bodyReservedGP`; by `virtBodyNumArgs` and the argument-name parser
  inside `physBodyWithStores`.

* `String.toNat?` — no normal form even outside a `module`: `String.Slice.isNat`
  loops with `forIn` over a `Std.Iter`, and the `Std.IteratorLoop` default
  implementation is a well-founded recursion whose accessibility argument is
  supplied by `Classical.propDecidable`, so `whnf` stops at a `Decidable.rec`
  over a `WellFounded` proposition. Used beside each `String.startsWith` above
  in `virtBodyNumArgs`, `physBodyWithStores`, `movImmTable` and
  `straightCallRelocTableCore`.

* `String.splitOn` — no normal form at any transparency; `whnf` stops at
  `WellFounded.apply` over `Prod.instWellFoundedRelation`. Used by
  `parseImmShiftMnem` and `parseCallW`.

* `Std.HashMap` keyed by `String` — `String.hash` is `opaque`, so no lookup has
  a normal form; inside a `module` even `isEmpty` of the empty map is stuck.
  `canonicalizeMemrefThread` tests `(arrChainAlias body).isEmpty`
  unconditionally, so this one is reached by every body.

`JasminLprogExport` already carries kernel-reducing replacements for the first
three: `hasPrefix` and `hasSuffix` over `List.isPrefixOf` / `List.isSuffixOf`,
and `natOfDigits?` over a character fold. The `String.splitOn` uses split on a
single separator character, which `List.splitOn` on the character list
expresses. Each replacement computes the same function, so restating them
changes no emitted byte. `String.hash` has no replacement: an association list
over `String` reduces where a `Std.HashMap` does not.

## What a call-free, spill-free body avoids

`firstFittingCell` is well-founded on `hulls.size - i`; `decide` does not reduce
it and `with_unfolding_all rfl` does. It is reached only from `allocCell`, i.e.
only when the linear scan spills. The `Std.Range` loop above is the other entry
a call-free body does not reach. Everything else is on the path of every body.
-/

namespace CatCrypt.Crypto.SecureCompilation.Ascent.PhysAbiReduction

/-- Prefix test over the character list, the shape `JasminLprogExport.hasPrefix`
    takes. -/
def hasPrefixChars (s pat : String) : Bool := List.isPrefixOf pat.toList s.toList

/-- Decimal parse over the character list, the shape
    `JasminLprogExport.natOfDigits?` takes. -/
def natOfDigitsChars (cs : List Char) : Option Nat :=
  match cs with
  | [] => none
  | _ => cs.foldl (fun acc c =>
      match acc with
      | some k => if '0' ≤ c && c ≤ '9' then some (k * 10 + (c.toNat - '0'.toNat)) else none
      | none => none) (some 0)

/-- A fold over a `List`, the shape the exporter's `Id.run do` bodies take. -/
def sumList (l : List Nat) : Nat := Id.run do
  let mut n := 0
  for x in l do n := n + x
  return n

/-- An identity-seeded table of size `n`, the shape `physTable` builds with
    `(Array.range n).map`. -/
def identityTable (n : Nat) : Array Nat := ((List.range n).map (fun s => s)).toArray

/-! ### Family 2 controls: the character-list replacements reduce -/

/-- A GP mnemonic is not vector-classed, by the character-list prefix test. -/
theorem hasPrefixChars_gp : hasPrefixChars "ADD:64" "V" = false := by decide

/-- A vector mnemonic is vector-classed, by the character-list prefix test. -/
theorem hasPrefixChars_vec : hasPrefixChars "VPADDQ:64" "V" = true := by decide

/-- An argument name's index parses, by the character-list decimal fold. -/
theorem natOfDigitsChars_arg : natOfDigitsChars ("a12".toList.drop 1) = some 12 := by decide

/-- A non-numeric tail parses to none. -/
theorem natOfDigitsChars_nonNumeric : natOfDigitsChars ("ax".toList.drop 1) = none := by decide

/-- A `List` for-loop reduces. -/
theorem sumList_three : sumList [1, 2, 3] = 6 := by decide

/-! ### Family 1 controls: the `import all` lines above, and the `Array.map`
restatement -/

/-- The name the exporter builds for argument slot 12 parses back to its index:
    `toString` on `Nat` reduces here because of `import all Init.Data.Repr`. -/
theorem natOfDigitsChars_argName :
    natOfDigitsChars (("a" ++ toString (12 : Nat)).toList.drop 1) = some 12 := by decide

/-- `Array.range` reduces here because of `import all Init.Data.Array.Range`. -/
theorem arrayRange_size : (Array.range 4).size = 4 := by decide

/-- The `List`-routed identity table reduces where `(Array.range n).map` does
    not. -/
theorem identityTable_size : (identityTable 4).size = 4 := by decide

/-- The `List`-routed identity table holds the identity. -/
theorem identityTable_get : (identityTable 4)[2]! = 2 := by decide

end CatCrypt.Crypto.SecureCompilation.Ascent.PhysAbiReduction
