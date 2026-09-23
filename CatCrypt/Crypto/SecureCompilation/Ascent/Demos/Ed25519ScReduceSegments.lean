/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519SymExec

/-!
# The parts of the shipped scalar reduction as lists of segments

`Imported.Ed25519ScReduceShipped` divides the body of `ed25519_sc_reduce` into 113
segments and groups them into eight parts: sixteen segments each for parts 1 to 7 and one
for part 8. `scrSegs n` is part `n` as the list of its segments, so that a part can be cut
at any segment boundary, and `scrPart_segs` identifies each part with the concatenation of
its segments.

A part check is cut at a segment boundary because there the live locations of the symbolic
state hold the nodes of statement slots, which read back as slots; inside a segment they can
hold nodes of a statement's expression, whose readback expands the shared graph.

## Main results

* `scrSegs`: the segments of each part.
* `scrPart_segs`: each of the eight parts is the concatenation of its segments.
* `scrPart_cut`: a part is the concatenation of its segments before and after a boundary.
* `xSlice_length`: the length of a slice of the statement list.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519ScReduceShipped

/-- The segments of part `n` of the body, in order. -/
def scrSegs : Nat → List (List (JInstr 64))
  | 1 => [ed25519ScReduceShippedSeg001, ed25519ScReduceShippedSeg002,
      ed25519ScReduceShippedSeg003, ed25519ScReduceShippedSeg004, ed25519ScReduceShippedSeg005,
      ed25519ScReduceShippedSeg006, ed25519ScReduceShippedSeg007, ed25519ScReduceShippedSeg008,
      ed25519ScReduceShippedSeg009, ed25519ScReduceShippedSeg010, ed25519ScReduceShippedSeg011,
      ed25519ScReduceShippedSeg012, ed25519ScReduceShippedSeg013, ed25519ScReduceShippedSeg014,
      ed25519ScReduceShippedSeg015, ed25519ScReduceShippedSeg016]
  | 2 => [ed25519ScReduceShippedSeg017, ed25519ScReduceShippedSeg018,
      ed25519ScReduceShippedSeg019, ed25519ScReduceShippedSeg020, ed25519ScReduceShippedSeg021,
      ed25519ScReduceShippedSeg022, ed25519ScReduceShippedSeg023, ed25519ScReduceShippedSeg024,
      ed25519ScReduceShippedSeg025, ed25519ScReduceShippedSeg026, ed25519ScReduceShippedSeg027,
      ed25519ScReduceShippedSeg028, ed25519ScReduceShippedSeg029, ed25519ScReduceShippedSeg030,
      ed25519ScReduceShippedSeg031, ed25519ScReduceShippedSeg032]
  | 3 => [ed25519ScReduceShippedSeg033, ed25519ScReduceShippedSeg034,
      ed25519ScReduceShippedSeg035, ed25519ScReduceShippedSeg036, ed25519ScReduceShippedSeg037,
      ed25519ScReduceShippedSeg038, ed25519ScReduceShippedSeg039, ed25519ScReduceShippedSeg040,
      ed25519ScReduceShippedSeg041, ed25519ScReduceShippedSeg042, ed25519ScReduceShippedSeg043,
      ed25519ScReduceShippedSeg044, ed25519ScReduceShippedSeg045, ed25519ScReduceShippedSeg046,
      ed25519ScReduceShippedSeg047, ed25519ScReduceShippedSeg048]
  | 4 => [ed25519ScReduceShippedSeg049, ed25519ScReduceShippedSeg050,
      ed25519ScReduceShippedSeg051, ed25519ScReduceShippedSeg052, ed25519ScReduceShippedSeg053,
      ed25519ScReduceShippedSeg054, ed25519ScReduceShippedSeg055, ed25519ScReduceShippedSeg056,
      ed25519ScReduceShippedSeg057, ed25519ScReduceShippedSeg058, ed25519ScReduceShippedSeg059,
      ed25519ScReduceShippedSeg060, ed25519ScReduceShippedSeg061, ed25519ScReduceShippedSeg062,
      ed25519ScReduceShippedSeg063, ed25519ScReduceShippedSeg064]
  | 5 => [ed25519ScReduceShippedSeg065, ed25519ScReduceShippedSeg066,
      ed25519ScReduceShippedSeg067, ed25519ScReduceShippedSeg068, ed25519ScReduceShippedSeg069,
      ed25519ScReduceShippedSeg070, ed25519ScReduceShippedSeg071, ed25519ScReduceShippedSeg072,
      ed25519ScReduceShippedSeg073, ed25519ScReduceShippedSeg074, ed25519ScReduceShippedSeg075,
      ed25519ScReduceShippedSeg076, ed25519ScReduceShippedSeg077, ed25519ScReduceShippedSeg078,
      ed25519ScReduceShippedSeg079, ed25519ScReduceShippedSeg080]
  | 6 => [ed25519ScReduceShippedSeg081, ed25519ScReduceShippedSeg082,
      ed25519ScReduceShippedSeg083, ed25519ScReduceShippedSeg084, ed25519ScReduceShippedSeg085,
      ed25519ScReduceShippedSeg086, ed25519ScReduceShippedSeg087, ed25519ScReduceShippedSeg088,
      ed25519ScReduceShippedSeg089, ed25519ScReduceShippedSeg090, ed25519ScReduceShippedSeg091,
      ed25519ScReduceShippedSeg092, ed25519ScReduceShippedSeg093, ed25519ScReduceShippedSeg094,
      ed25519ScReduceShippedSeg095, ed25519ScReduceShippedSeg096]
  | 7 => [ed25519ScReduceShippedSeg097, ed25519ScReduceShippedSeg098,
      ed25519ScReduceShippedSeg099, ed25519ScReduceShippedSeg100, ed25519ScReduceShippedSeg101,
      ed25519ScReduceShippedSeg102, ed25519ScReduceShippedSeg103, ed25519ScReduceShippedSeg104,
      ed25519ScReduceShippedSeg105, ed25519ScReduceShippedSeg106, ed25519ScReduceShippedSeg107,
      ed25519ScReduceShippedSeg108, ed25519ScReduceShippedSeg109, ed25519ScReduceShippedSeg110,
      ed25519ScReduceShippedSeg111, ed25519ScReduceShippedSeg112]
  | 8 => [ed25519ScReduceShippedSeg113]
  | _ => []

/-- The eight parts of the body, by number. -/
def scrPart : Nat → List (JInstr 64)
  | 1 => ed25519ScReduceShippedPart01
  | 2 => ed25519ScReduceShippedPart02
  | 3 => ed25519ScReduceShippedPart03
  | 4 => ed25519ScReduceShippedPart04
  | 5 => ed25519ScReduceShippedPart05
  | 6 => ed25519ScReduceShippedPart06
  | 7 => ed25519ScReduceShippedPart07
  | 8 => ed25519ScReduceShippedPart08
  | _ => []

/-- Each of the eight parts is the concatenation of its segments. -/
theorem scrPart_segs (n : Nat) (hn : 1 ≤ n ∧ n ≤ 8) : scrPart n = (scrSegs n).flatten := by
  obtain ⟨h1, h8⟩ := hn
  interval_cases n <;>
    simp only [scrPart, scrSegs, ed25519ScReduceShippedPart01, ed25519ScReduceShippedPart02,
      ed25519ScReduceShippedPart03, ed25519ScReduceShippedPart04, ed25519ScReduceShippedPart05,
      ed25519ScReduceShippedPart06, ed25519ScReduceShippedPart07, ed25519ScReduceShippedPart08,
      List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]

/-- A part is the concatenation of its segments before and after the boundary `b`. -/
theorem scrPart_cut (n b : Nat) (hn : 1 ≤ n ∧ n ≤ 8) :
    scrPart n = ((scrSegs n).take b).flatten ++ ((scrSegs n).drop b).flatten := by
  rw [scrPart_segs n hn, ← List.flatten_append, List.take_append_drop]

/-- The statement list of the reduction has 338 entries. -/
theorem xStmts_len : xStmts.length = 338 := by decide +kernel

/-- A slice of the statement list within its range has the length its bounds give. -/
theorem xSlice_length (a b : Nat) (ha : 16 ≤ a) (hab : a ≤ b) (hb : b ≤ 354) :
    (xSlice a b).length = b - a := by
  simp only [xSlice, List.length_take, List.length_drop, xStmts_len]
  omega

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof
