/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScMuladdModel

/-!
# The parts of the shipped multiply-accumulate as lists of segments

`Imported.Ed25519ScMuladdShipped` divides the body of `ed25519_sc_muladd` into 138
segments and groups them into nine parts: sixteen segments each for parts 1 to 8 and ten
for part 9. `scmSegs n` is part `n` as the list of its segments, so that a part can be cut
at any segment boundary, and `scmPart_segs` identifies each part with the concatenation of
its segments.

A part check is cut at a segment boundary because there the live locations of the symbolic
state hold the nodes of statement slots, which read back as slots; inside a segment they can
hold nodes of a statement's expression, whose readback expands the shared graph.

## Main results

* `scmSegs`: the segments of each part.
* `scmPart_segs`: each of the nine parts is the concatenation of its segments.
* `scmPart_cut`: a part is the concatenation of its segments before and after a boundary.
* `mSlice_length`: the length of a slice of the statement list.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScMuladdShippedProof

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519ScMuladdShipped
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof

/-- The segments of part `n` of the body, in order. -/
def scmSegs : Nat → List (List (JInstr 64))
  | 1 => [ed25519ScMuladdShippedSeg001, ed25519ScMuladdShippedSeg002,
      ed25519ScMuladdShippedSeg003, ed25519ScMuladdShippedSeg004, ed25519ScMuladdShippedSeg005,
      ed25519ScMuladdShippedSeg006, ed25519ScMuladdShippedSeg007, ed25519ScMuladdShippedSeg008,
      ed25519ScMuladdShippedSeg009, ed25519ScMuladdShippedSeg010, ed25519ScMuladdShippedSeg011,
      ed25519ScMuladdShippedSeg012, ed25519ScMuladdShippedSeg013, ed25519ScMuladdShippedSeg014,
      ed25519ScMuladdShippedSeg015, ed25519ScMuladdShippedSeg016]
  | 2 => [ed25519ScMuladdShippedSeg017, ed25519ScMuladdShippedSeg018,
      ed25519ScMuladdShippedSeg019, ed25519ScMuladdShippedSeg020, ed25519ScMuladdShippedSeg021,
      ed25519ScMuladdShippedSeg022, ed25519ScMuladdShippedSeg023, ed25519ScMuladdShippedSeg024,
      ed25519ScMuladdShippedSeg025, ed25519ScMuladdShippedSeg026, ed25519ScMuladdShippedSeg027,
      ed25519ScMuladdShippedSeg028, ed25519ScMuladdShippedSeg029, ed25519ScMuladdShippedSeg030,
      ed25519ScMuladdShippedSeg031, ed25519ScMuladdShippedSeg032]
  | 3 => [ed25519ScMuladdShippedSeg033, ed25519ScMuladdShippedSeg034,
      ed25519ScMuladdShippedSeg035, ed25519ScMuladdShippedSeg036, ed25519ScMuladdShippedSeg037,
      ed25519ScMuladdShippedSeg038, ed25519ScMuladdShippedSeg039, ed25519ScMuladdShippedSeg040,
      ed25519ScMuladdShippedSeg041, ed25519ScMuladdShippedSeg042, ed25519ScMuladdShippedSeg043,
      ed25519ScMuladdShippedSeg044, ed25519ScMuladdShippedSeg045, ed25519ScMuladdShippedSeg046,
      ed25519ScMuladdShippedSeg047, ed25519ScMuladdShippedSeg048]
  | 4 => [ed25519ScMuladdShippedSeg049, ed25519ScMuladdShippedSeg050,
      ed25519ScMuladdShippedSeg051, ed25519ScMuladdShippedSeg052, ed25519ScMuladdShippedSeg053,
      ed25519ScMuladdShippedSeg054, ed25519ScMuladdShippedSeg055, ed25519ScMuladdShippedSeg056,
      ed25519ScMuladdShippedSeg057, ed25519ScMuladdShippedSeg058, ed25519ScMuladdShippedSeg059,
      ed25519ScMuladdShippedSeg060, ed25519ScMuladdShippedSeg061, ed25519ScMuladdShippedSeg062,
      ed25519ScMuladdShippedSeg063, ed25519ScMuladdShippedSeg064]
  | 5 => [ed25519ScMuladdShippedSeg065, ed25519ScMuladdShippedSeg066,
      ed25519ScMuladdShippedSeg067, ed25519ScMuladdShippedSeg068, ed25519ScMuladdShippedSeg069,
      ed25519ScMuladdShippedSeg070, ed25519ScMuladdShippedSeg071, ed25519ScMuladdShippedSeg072,
      ed25519ScMuladdShippedSeg073, ed25519ScMuladdShippedSeg074, ed25519ScMuladdShippedSeg075,
      ed25519ScMuladdShippedSeg076, ed25519ScMuladdShippedSeg077, ed25519ScMuladdShippedSeg078,
      ed25519ScMuladdShippedSeg079, ed25519ScMuladdShippedSeg080]
  | 6 => [ed25519ScMuladdShippedSeg081, ed25519ScMuladdShippedSeg082,
      ed25519ScMuladdShippedSeg083, ed25519ScMuladdShippedSeg084, ed25519ScMuladdShippedSeg085,
      ed25519ScMuladdShippedSeg086, ed25519ScMuladdShippedSeg087, ed25519ScMuladdShippedSeg088,
      ed25519ScMuladdShippedSeg089, ed25519ScMuladdShippedSeg090, ed25519ScMuladdShippedSeg091,
      ed25519ScMuladdShippedSeg092, ed25519ScMuladdShippedSeg093, ed25519ScMuladdShippedSeg094,
      ed25519ScMuladdShippedSeg095, ed25519ScMuladdShippedSeg096]
  | 7 => [ed25519ScMuladdShippedSeg097, ed25519ScMuladdShippedSeg098,
      ed25519ScMuladdShippedSeg099, ed25519ScMuladdShippedSeg100, ed25519ScMuladdShippedSeg101,
      ed25519ScMuladdShippedSeg102, ed25519ScMuladdShippedSeg103, ed25519ScMuladdShippedSeg104,
      ed25519ScMuladdShippedSeg105, ed25519ScMuladdShippedSeg106, ed25519ScMuladdShippedSeg107,
      ed25519ScMuladdShippedSeg108, ed25519ScMuladdShippedSeg109, ed25519ScMuladdShippedSeg110,
      ed25519ScMuladdShippedSeg111, ed25519ScMuladdShippedSeg112]
  | 8 => [ed25519ScMuladdShippedSeg113, ed25519ScMuladdShippedSeg114,
      ed25519ScMuladdShippedSeg115, ed25519ScMuladdShippedSeg116, ed25519ScMuladdShippedSeg117,
      ed25519ScMuladdShippedSeg118, ed25519ScMuladdShippedSeg119, ed25519ScMuladdShippedSeg120,
      ed25519ScMuladdShippedSeg121, ed25519ScMuladdShippedSeg122, ed25519ScMuladdShippedSeg123,
      ed25519ScMuladdShippedSeg124, ed25519ScMuladdShippedSeg125, ed25519ScMuladdShippedSeg126,
      ed25519ScMuladdShippedSeg127, ed25519ScMuladdShippedSeg128]
  | 9 => [ed25519ScMuladdShippedSeg129, ed25519ScMuladdShippedSeg130,
      ed25519ScMuladdShippedSeg131, ed25519ScMuladdShippedSeg132, ed25519ScMuladdShippedSeg133,
      ed25519ScMuladdShippedSeg134, ed25519ScMuladdShippedSeg135, ed25519ScMuladdShippedSeg136,
      ed25519ScMuladdShippedSeg137, ed25519ScMuladdShippedSeg138]
  | _ => []

/-- The nine parts of the body, by number. -/
def scmPart : Nat → List (JInstr 64)
  | 1 => ed25519ScMuladdShippedPart01
  | 2 => ed25519ScMuladdShippedPart02
  | 3 => ed25519ScMuladdShippedPart03
  | 4 => ed25519ScMuladdShippedPart04
  | 5 => ed25519ScMuladdShippedPart05
  | 6 => ed25519ScMuladdShippedPart06
  | 7 => ed25519ScMuladdShippedPart07
  | 8 => ed25519ScMuladdShippedPart08
  | 9 => ed25519ScMuladdShippedPart09
  | _ => []

/-- Each of the nine parts is the concatenation of its segments. -/
theorem scmPart_segs (n : Nat) (hn : 1 ≤ n ∧ n ≤ 9) : scmPart n = (scmSegs n).flatten := by
  obtain ⟨h1, h9⟩ := hn
  interval_cases n <;>
    simp only [scmPart, scmSegs, ed25519ScMuladdShippedPart01, ed25519ScMuladdShippedPart02,
      ed25519ScMuladdShippedPart03, ed25519ScMuladdShippedPart04, ed25519ScMuladdShippedPart05,
      ed25519ScMuladdShippedPart06, ed25519ScMuladdShippedPart07, ed25519ScMuladdShippedPart08,
      ed25519ScMuladdShippedPart09, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.append_assoc]

/-- A part is the concatenation of its segments before and after the boundary `b`. -/
theorem scmPart_cut (n b : Nat) (hn : 1 ≤ n ∧ n ≤ 9) :
    scmPart n = ((scmSegs n).take b).flatten ++ ((scmSegs n).drop b).flatten := by
  rw [scmPart_segs n hn, ← List.flatten_append, List.take_append_drop]

/-- The statement list of the multiply-accumulate has 418 entries. -/
theorem mStmts_len : mStmts.length = 418 := by decide +kernel

/-- A slice of the statement list within its range has the length its bounds give. -/
theorem mSlice_length (a b : Nat) (ha : 16 ≤ a) (hab : a ≤ b) (hb : b ≤ 434) :
    (mSlice a b).length = b - a := by
  simp only [mSlice, List.length_take, List.length_drop, mStmts_len]
  omega

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScMuladdShippedProof
