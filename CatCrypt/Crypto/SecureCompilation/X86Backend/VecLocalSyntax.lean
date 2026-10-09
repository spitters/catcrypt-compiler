/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.VecMach

@[expose] public section

set_option autoImplicit false

/-!
# The vector-locality check of a block

A block of scalar operations and vector instructions is vector-local when every vector
register and every mask register that a vector instruction of the block reads is written by
an earlier instruction of the block. `vecLocalCheck` decides this by a fold over the block
that keeps the registers written so far. The soundness of the check is
`VecLocalCheck.vecLocalCheck_sound`.

## Main definitions

* `vReadsZ`, `vReadsK`, `vWritesZ`, `vWritesK`: the vector and mask registers a vector
  instruction reads and writes.
* `vecLocalCheckFrom`, `vecLocalCheck`: the check over a block, from given sets of written
  registers and from the empty sets.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.VecLocalCheck

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.VecMach

/-! ## 1. The registers of a vector instruction -/

/-- The vector registers a vector instruction reads. `vzeroupper` maps each register to a
    function of itself and is given no reads. -/
def vReadsZ : VInstr → List (Fin 32)
  | .ld _ _ => []
  | .st src _ => [src]
  | .op _ _ s2 s1 _ => [s2, s1]
  | .shi _ _ _ src _ => [src]
  | .dup _ src _ none => [src]
  | .dup _ src d (some _) => [src, d]
  | .mova src _ => [src]
  | .perm x i _ => [x, i]
  | .blend _ a b _ => [a, b]
  | .rol _ _ src _ => [src]
  | .tern _ _ s3 s2 d => [d, s2, s3]
  | .ldK _ _ => []
  | .opK _ _ _ s1 _ => [s1]
  | .kmov _ => []
  | .zeroUpper => []

/-- The mask registers a vector instruction reads. -/
def vReadsK : VInstr → List (Fin 8)
  | .dup _ _ _ (some k) => [k]
  | .blend k _ _ _ => [k]
  | _ => []

/-- The vector register a vector instruction writes. -/
def vWritesZ : VInstr → List (Fin 32)
  | .ld _ d => [d]
  | .op _ _ _ _ d => [d]
  | .shi _ _ _ _ d => [d]
  | .dup _ _ d _ => [d]
  | .mova _ d => [d]
  | .perm _ _ d => [d]
  | .blend _ _ _ d => [d]
  | .rol _ _ _ d => [d]
  | .tern _ _ _ _ d => [d]
  | .ldK _ d => [d]
  | .opK _ _ _ _ d => [d]
  | _ => []

/-- The mask register a vector instruction writes. -/
def vWritesK : VInstr → List (Fin 8)
  | .kmov k => [k]
  | _ => []

/-! ## 2. The check -/

/-- **Every register a vector instruction of the block reads is written before**, from the
    vector registers `Z` and the mask registers `K` written so far. Scalar operations are
    not inspected. -/
def vecLocalCheckFrom (Z : List (Fin 32)) (K : List (Fin 8)) :
    List (JInstr 64 ⊕ VInstr) → Bool
  | [] => true
  | .inl _ :: ops => vecLocalCheckFrom Z K ops
  | .inr v :: ops =>
      (vReadsZ v).all (fun x => decide (x ∈ Z)) && (vReadsK v).all (fun k => decide (k ∈ K)) &&
        vecLocalCheckFrom (vWritesZ v ++ Z) (vWritesK v ++ K) ops

/-- **Every vector and mask register a vector instruction of the block reads is written
    earlier in the block.** -/
def vecLocalCheck (ops : List (JInstr 64 ⊕ VInstr)) : Bool :=
  vecLocalCheckFrom [] [] ops

end CatCrypt.Crypto.SecureCompilation.X86Backend.VecLocalCheck
