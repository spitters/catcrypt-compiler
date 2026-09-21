/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519InvertChain
public import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519InvertShipped

/-!
# The steps of the shipped `ed25519_invert`

Segments 2 to 264 of `Imported.Ed25519InvertShipped.ed25519InvertShippedBlock` are the
segments of a list of `Ed25519InvertChain.Step`, one per part of the block; segment 1
carries the entry stores alongside its call and segment 265 reloads the output pointer, so
both stand outside the list. The exponent each field slot holds after those steps is a
closed arithmetic fact about the list.

## Main definitions

* `invertSteps01` … `invertSteps17`: the steps of each part of the block.
* `invertSteps`: their concatenation, the steps of segments 2 to 264.
* `invertEnv1`: the exponents after segment 1.

## Main results

* `invertPart01_eq` … `invertPart17_eq`, `invertBlock_eq`: the block as its first segment,
  the segments of `invertSteps`, and its last segment.
* `invertEnv_final`: the exponent in each slot after segments 1 to 264.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519InvertShippedProof

open CatCrypt.Crypto.SecureCompilation.Ascent.Imported


/-- The steps of segments 2 to 16. -/
def invertSteps01 : List Step :=
  [ .sqr .b1 (.buf .b0), .sqr .b1 (.buf .b1), .mul .b1 (.inp) (.buf .b1),
    .mul .b0 (.buf .b0) (.buf .b1), .sqr .b2 (.buf .b0), .mul .b1 (.buf .b1) (.buf .b2),
    .sqr .b2 (.buf .b1), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2),
    .sqr .b2 (.buf .b2), .mul .b1 (.buf .b2) (.buf .b1), .sqr .b2 (.buf .b1),
    .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2) ]

/-- The steps of segments 17 to 32. -/
def invertSteps02 : List Step :=
  [ .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2),
    .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2),
    .mul .b2 (.buf .b2) (.buf .b1), .sqr .b3 (.buf .b2), .sqr .b3 (.buf .b3),
    .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3),
    .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3) ]

/-- The steps of segments 33 to 48. -/
def invertSteps03 : List Step :=
  [ .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3),
    .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3),
    .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3),
    .mul .b2 (.buf .b3) (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2),
    .sqr .b2 (.buf .b2) ]

/-- The steps of segments 49 to 64. -/
def invertSteps04 : List Step :=
  [ .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2),
    .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2),
    .mul .b1 (.buf .b2) (.buf .b1), .sqr .b2 (.buf .b1), .sqr .b2 (.buf .b2),
    .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2),
    .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2) ]

/-- The steps of segments 65 to 80. -/
def invertSteps05 : List Step :=
  [ .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2),
    .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2),
    .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2),
    .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2) ]

/-- The steps of segments 81 to 96. -/
def invertSteps06 : List Step :=
  [ .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2),
    .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2),
    .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2),
    .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2) ]

/-- The steps of segments 97 to 112. -/
def invertSteps07 : List Step :=
  [ .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2),
    .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2),
    .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .mul .b2 (.buf .b2) (.buf .b1),
    .sqr .b3 (.buf .b2), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3),
    .sqr .b3 (.buf .b3) ]

/-- The steps of segments 113 to 128. -/
def invertSteps08 : List Step :=
  [ .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3),
    .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3),
    .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3),
    .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3) ]

/-- The steps of segments 129 to 144. -/
def invertSteps09 : List Step :=
  [ .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3),
    .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3),
    .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3),
    .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3) ]

/-- The steps of segments 145 to 160. -/
def invertSteps10 : List Step :=
  [ .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3),
    .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3),
    .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3),
    .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3) ]

/-- The steps of segments 161 to 176. -/
def invertSteps11 : List Step :=
  [ .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3),
    .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3),
    .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3),
    .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3) ]

/-- The steps of segments 177 to 192. -/
def invertSteps12 : List Step :=
  [ .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3),
    .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3),
    .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3),
    .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3) ]

/-- The steps of segments 193 to 208. -/
def invertSteps13 : List Step :=
  [ .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3),
    .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3),
    .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3),
    .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3), .sqr .b3 (.buf .b3),
    .mul .b2 (.buf .b3) (.buf .b2) ]

/-- The steps of segments 209 to 224. -/
def invertSteps14 : List Step :=
  [ .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2),
    .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2),
    .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2),
    .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2) ]

/-- The steps of segments 225 to 240. -/
def invertSteps15 : List Step :=
  [ .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2),
    .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2),
    .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2),
    .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2) ]

/-- The steps of segments 241 to 256. -/
def invertSteps16 : List Step :=
  [ .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2),
    .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2),
    .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2),
    .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2) ]

/-- The steps of segments 257 to 264. -/
def invertSteps17 : List Step :=
  [ .sqr .b2 (.buf .b2), .sqr .b2 (.buf .b2), .mul .b1 (.buf .b2) (.buf .b1),
    .sqr .b1 (.buf .b1), .sqr .b1 (.buf .b1), .sqr .b1 (.buf .b1), .sqr .b1 (.buf .b1),
    .sqr .b1 (.buf .b1) ]

theorem invertPart01_eq :
    Ed25519InvertShipped.ed25519InvertShippedPart01
      = Ed25519InvertShipped.ed25519InvertShippedSeg001 ++ invertSteps01.map segOfStep := rfl

theorem invertPart02_eq :
    Ed25519InvertShipped.ed25519InvertShippedPart02 = invertSteps02.map segOfStep := rfl

theorem invertPart03_eq :
    Ed25519InvertShipped.ed25519InvertShippedPart03 = invertSteps03.map segOfStep := rfl

theorem invertPart04_eq :
    Ed25519InvertShipped.ed25519InvertShippedPart04 = invertSteps04.map segOfStep := rfl

theorem invertPart05_eq :
    Ed25519InvertShipped.ed25519InvertShippedPart05 = invertSteps05.map segOfStep := rfl

theorem invertPart06_eq :
    Ed25519InvertShipped.ed25519InvertShippedPart06 = invertSteps06.map segOfStep := rfl

theorem invertPart07_eq :
    Ed25519InvertShipped.ed25519InvertShippedPart07 = invertSteps07.map segOfStep := rfl

theorem invertPart08_eq :
    Ed25519InvertShipped.ed25519InvertShippedPart08 = invertSteps08.map segOfStep := rfl

theorem invertPart09_eq :
    Ed25519InvertShipped.ed25519InvertShippedPart09 = invertSteps09.map segOfStep := rfl

theorem invertPart10_eq :
    Ed25519InvertShipped.ed25519InvertShippedPart10 = invertSteps10.map segOfStep := rfl

theorem invertPart11_eq :
    Ed25519InvertShipped.ed25519InvertShippedPart11 = invertSteps11.map segOfStep := rfl

theorem invertPart12_eq :
    Ed25519InvertShipped.ed25519InvertShippedPart12 = invertSteps12.map segOfStep := rfl

theorem invertPart13_eq :
    Ed25519InvertShipped.ed25519InvertShippedPart13 = invertSteps13.map segOfStep := rfl

theorem invertPart14_eq :
    Ed25519InvertShipped.ed25519InvertShippedPart14 = invertSteps14.map segOfStep := rfl

theorem invertPart15_eq :
    Ed25519InvertShipped.ed25519InvertShippedPart15 = invertSteps15.map segOfStep := rfl

theorem invertPart16_eq :
    Ed25519InvertShipped.ed25519InvertShippedPart16 = invertSteps16.map segOfStep := rfl

theorem invertPart17_eq :
    Ed25519InvertShipped.ed25519InvertShippedPart17
      = invertSteps17.map segOfStep ++ Ed25519InvertShipped.ed25519InvertShippedSeg265
        ++ Ed25519InvertShipped.ed25519InvertShippedSeg266 := rfl

/-- The steps of segments 2 to 264. -/
def invertSteps : List Step :=
  invertSteps01 ++ invertSteps02 ++ invertSteps03 ++ invertSteps04 ++ invertSteps05 ++
    invertSteps06 ++ invertSteps07 ++ invertSteps08 ++ invertSteps09 ++ invertSteps10 ++
    invertSteps11 ++ invertSteps12 ++ invertSteps13 ++ invertSteps14 ++ invertSteps15 ++
    invertSteps16 ++ invertSteps17

/-- The environment after segment 1: the slot at `%rsp` holds the square of the input. -/
def invertEnv1 : Env := ⟨some 2, none, none, none⟩

/-- The block as its first segment, the steps of segments 2 to 264, and its last
    segment. -/
theorem invertBlock_eq :
    Ed25519InvertShipped.ed25519InvertShippedBlock
      = Ed25519InvertShipped.ed25519InvertShippedSeg001 ++ invertSteps.map segOfStep
        ++ Ed25519InvertShipped.ed25519InvertShippedSeg265
        ++ Ed25519InvertShipped.ed25519InvertShippedSeg266 := by
  unfold Ed25519InvertShipped.ed25519InvertShippedBlock invertSteps
  simp only [List.map_append, invertPart01_eq, invertPart02_eq, invertPart03_eq,
    invertPart04_eq, invertPart05_eq, invertPart06_eq, invertPart07_eq, invertPart08_eq,
    invertPart09_eq, invertPart10_eq, invertPart11_eq, invertPart12_eq, invertPart13_eq,
    invertPart14_eq, invertPart15_eq, invertPart16_eq, invertPart17_eq, List.append_assoc]

/-- The exponent of the input in each slot after segments 1 to 264. -/
theorem invertEnv_final : runEnv invertEnv1 invertSteps =
    ⟨some 11,
     some 57896044618658097711785492504343953926634992332820282019728792003956564819936,
     some 1809251394333065553493296640760748560207343510400633813116523624223735808000,
     some 1606938044258990275541962092339894951921974764381296132096000⟩ := by
  decide +kernel

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519InvertShippedProof
