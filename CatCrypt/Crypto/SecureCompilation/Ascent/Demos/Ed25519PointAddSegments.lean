/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddShippedParts

/-!
# The parts of the shipped point addition as lists of segments

`Imported.Ed25519PointAddShipped` divides the body of `ed25519_point_add` into 155
segments and groups them into ten parts: sixteen segments each for parts 1 to 9 and eleven
for part 10. `paSegs n` is part `n` as the list of its segments, so that a part can be cut
at any segment boundary, and `paPart_segs` identifies each part with the concatenation of
its segments.

A part check is cut at a segment boundary because there the live locations of the symbolic
state hold the nodes of statement slots, which read back as slots; inside a segment they can
hold nodes of a statement's expression, whose readback expands the shared graph.

## Main results

* `paSegs`: the segments of each part.
* `paPart_segs`: each of the ten parts is the concatenation of its segments.
* `paPart_cut`: a part is the concatenation of its segments before and after a boundary.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddShippedProof

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519PointAddShipped

/-- The segments of part `n` of the body, in order. -/
def paSegs : Nat → List (List (JInstr 64))
  | 1 => [ed25519PointAddShippedSeg001, ed25519PointAddShippedSeg002,
      ed25519PointAddShippedSeg003, ed25519PointAddShippedSeg004, ed25519PointAddShippedSeg005,
      ed25519PointAddShippedSeg006, ed25519PointAddShippedSeg007, ed25519PointAddShippedSeg008,
      ed25519PointAddShippedSeg009, ed25519PointAddShippedSeg010, ed25519PointAddShippedSeg011,
      ed25519PointAddShippedSeg012, ed25519PointAddShippedSeg013, ed25519PointAddShippedSeg014,
      ed25519PointAddShippedSeg015, ed25519PointAddShippedSeg016]
  | 2 => [ed25519PointAddShippedSeg017, ed25519PointAddShippedSeg018,
      ed25519PointAddShippedSeg019, ed25519PointAddShippedSeg020, ed25519PointAddShippedSeg021,
      ed25519PointAddShippedSeg022, ed25519PointAddShippedSeg023, ed25519PointAddShippedSeg024,
      ed25519PointAddShippedSeg025, ed25519PointAddShippedSeg026, ed25519PointAddShippedSeg027,
      ed25519PointAddShippedSeg028, ed25519PointAddShippedSeg029, ed25519PointAddShippedSeg030,
      ed25519PointAddShippedSeg031, ed25519PointAddShippedSeg032]
  | 3 => [ed25519PointAddShippedSeg033, ed25519PointAddShippedSeg034,
      ed25519PointAddShippedSeg035, ed25519PointAddShippedSeg036, ed25519PointAddShippedSeg037,
      ed25519PointAddShippedSeg038, ed25519PointAddShippedSeg039, ed25519PointAddShippedSeg040,
      ed25519PointAddShippedSeg041, ed25519PointAddShippedSeg042, ed25519PointAddShippedSeg043,
      ed25519PointAddShippedSeg044, ed25519PointAddShippedSeg045, ed25519PointAddShippedSeg046,
      ed25519PointAddShippedSeg047, ed25519PointAddShippedSeg048]
  | 4 => [ed25519PointAddShippedSeg049, ed25519PointAddShippedSeg050,
      ed25519PointAddShippedSeg051, ed25519PointAddShippedSeg052, ed25519PointAddShippedSeg053,
      ed25519PointAddShippedSeg054, ed25519PointAddShippedSeg055, ed25519PointAddShippedSeg056,
      ed25519PointAddShippedSeg057, ed25519PointAddShippedSeg058, ed25519PointAddShippedSeg059,
      ed25519PointAddShippedSeg060, ed25519PointAddShippedSeg061, ed25519PointAddShippedSeg062,
      ed25519PointAddShippedSeg063, ed25519PointAddShippedSeg064]
  | 5 => [ed25519PointAddShippedSeg065, ed25519PointAddShippedSeg066,
      ed25519PointAddShippedSeg067, ed25519PointAddShippedSeg068, ed25519PointAddShippedSeg069,
      ed25519PointAddShippedSeg070, ed25519PointAddShippedSeg071, ed25519PointAddShippedSeg072,
      ed25519PointAddShippedSeg073, ed25519PointAddShippedSeg074, ed25519PointAddShippedSeg075,
      ed25519PointAddShippedSeg076, ed25519PointAddShippedSeg077, ed25519PointAddShippedSeg078,
      ed25519PointAddShippedSeg079, ed25519PointAddShippedSeg080]
  | 6 => [ed25519PointAddShippedSeg081, ed25519PointAddShippedSeg082,
      ed25519PointAddShippedSeg083, ed25519PointAddShippedSeg084, ed25519PointAddShippedSeg085,
      ed25519PointAddShippedSeg086, ed25519PointAddShippedSeg087, ed25519PointAddShippedSeg088,
      ed25519PointAddShippedSeg089, ed25519PointAddShippedSeg090, ed25519PointAddShippedSeg091,
      ed25519PointAddShippedSeg092, ed25519PointAddShippedSeg093, ed25519PointAddShippedSeg094,
      ed25519PointAddShippedSeg095, ed25519PointAddShippedSeg096]
  | 7 => [ed25519PointAddShippedSeg097, ed25519PointAddShippedSeg098,
      ed25519PointAddShippedSeg099, ed25519PointAddShippedSeg100, ed25519PointAddShippedSeg101,
      ed25519PointAddShippedSeg102, ed25519PointAddShippedSeg103, ed25519PointAddShippedSeg104,
      ed25519PointAddShippedSeg105, ed25519PointAddShippedSeg106, ed25519PointAddShippedSeg107,
      ed25519PointAddShippedSeg108, ed25519PointAddShippedSeg109, ed25519PointAddShippedSeg110,
      ed25519PointAddShippedSeg111, ed25519PointAddShippedSeg112]
  | 8 => [ed25519PointAddShippedSeg113, ed25519PointAddShippedSeg114,
      ed25519PointAddShippedSeg115, ed25519PointAddShippedSeg116, ed25519PointAddShippedSeg117,
      ed25519PointAddShippedSeg118, ed25519PointAddShippedSeg119, ed25519PointAddShippedSeg120,
      ed25519PointAddShippedSeg121, ed25519PointAddShippedSeg122, ed25519PointAddShippedSeg123,
      ed25519PointAddShippedSeg124, ed25519PointAddShippedSeg125, ed25519PointAddShippedSeg126,
      ed25519PointAddShippedSeg127, ed25519PointAddShippedSeg128]
  | 9 => [ed25519PointAddShippedSeg129, ed25519PointAddShippedSeg130,
      ed25519PointAddShippedSeg131, ed25519PointAddShippedSeg132, ed25519PointAddShippedSeg133,
      ed25519PointAddShippedSeg134, ed25519PointAddShippedSeg135, ed25519PointAddShippedSeg136,
      ed25519PointAddShippedSeg137, ed25519PointAddShippedSeg138, ed25519PointAddShippedSeg139,
      ed25519PointAddShippedSeg140, ed25519PointAddShippedSeg141, ed25519PointAddShippedSeg142,
      ed25519PointAddShippedSeg143, ed25519PointAddShippedSeg144]
  | 10 => [ed25519PointAddShippedSeg145, ed25519PointAddShippedSeg146,
      ed25519PointAddShippedSeg147, ed25519PointAddShippedSeg148, ed25519PointAddShippedSeg149,
      ed25519PointAddShippedSeg150, ed25519PointAddShippedSeg151, ed25519PointAddShippedSeg152,
      ed25519PointAddShippedSeg153, ed25519PointAddShippedSeg154, ed25519PointAddShippedSeg155]
  | _ => []

/-- The ten parts of the body, by number. -/
def paPart : Nat → List (JInstr 64)
  | 1 => ed25519PointAddShippedPart01
  | 2 => ed25519PointAddShippedPart02
  | 3 => ed25519PointAddShippedPart03
  | 4 => ed25519PointAddShippedPart04
  | 5 => ed25519PointAddShippedPart05
  | 6 => ed25519PointAddShippedPart06
  | 7 => ed25519PointAddShippedPart07
  | 8 => ed25519PointAddShippedPart08
  | 9 => ed25519PointAddShippedPart09
  | 10 => ed25519PointAddShippedPart10
  | _ => []

/-- Each of the ten parts is the concatenation of its segments. -/
theorem paPart_segs (n : Nat) (hn : 1 ≤ n ∧ n ≤ 10) : paPart n = (paSegs n).flatten := by
  obtain ⟨h1, h10⟩ := hn
  interval_cases n <;>
    simp only [paPart, paSegs, ed25519PointAddShippedPart01, ed25519PointAddShippedPart02,
      ed25519PointAddShippedPart03, ed25519PointAddShippedPart04, ed25519PointAddShippedPart05,
      ed25519PointAddShippedPart06, ed25519PointAddShippedPart07, ed25519PointAddShippedPart08,
      ed25519PointAddShippedPart09, ed25519PointAddShippedPart10, List.flatten_cons,
      List.flatten_nil, List.append_nil, List.append_assoc]

/-- A part is the concatenation of its segments before and after the boundary `b`. -/
theorem paPart_cut (n b : Nat) (hn : 1 ≤ n ∧ n ≤ 10) :
    paPart n = ((paSegs n).take b).flatten ++ ((paSegs n).drop b).flatten := by
  rw [paPart_segs n hn, ← List.flatten_append, List.take_append_drop]

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddShippedProof
