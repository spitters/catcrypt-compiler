/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGen
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGen

@[expose] public section

set_option autoImplicit false

/-!
# The decoded `mpn_mul_1` node from computed shapes

`MpnMul1DecodedNode.mul1PhysBodyLit_decode` decodes the function bytes of the physical body
of `mpn_mul_1` by kernel evaluation of the whole round trip. This module derives the same
equation from the generic node theorem `DecodeGen.decodeLprog_node_gen`: the shapes of the
prefix, the loop body and the suffix are computed by `DecodeGen.shapeOf`, and the remaining
hypotheses are checks on the literal body.

## Main results

* `mul1PhysBodyLit_decode_gen`: the function bytes of `mul1PhysBodyLit` decode to
  `nodeLayout mul1DecPre mul1DecLoop mul1DecPost`, from `decodeLprog_node_gen`.
* `mul1PhysBody_decode_gen`: the same for the exporter's physical body.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenMul1

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Linstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGen
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemLoop (nodeLayout)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1DecodedNode

deriving instance DecidableEq for Shape
deriving instance DecidableEq for DShape

/-- The guard and back-edge compare `CMP:64 RBP, #0`. -/
def mul1Cmp : Linstr := ⟨0, .Lopn [.reg "RBP"] "CMP:64" [.reg "RBP", .imm 0]⟩

/-- The node split of `mul1PhysBodyLit`: the prefix, the guard, the loop body, the back-edge,
    the suffix and the return. -/
theorem mul1PhysBodyLit_split :
    mul1PhysBodyLit = mul1PhysBodyLit.take 18 ++ mul1Cmp
      :: ⟨0, .Lcond (.reg "Z") 1073741828⟩ :: ⟨0, .Llabel .internal 4⟩
      :: ((mul1PhysBodyLit.drop 21).take 56 ++ mul1Cmp
        :: ⟨0, .Lcond (.reg "NZ") 4⟩ :: ⟨0, .Llabel .internal 1073741828⟩
        :: ((mul1PhysBodyLit.drop 80).take 6 ++ [⟨0, .Lret⟩])) := by
  decide +kernel

/-- **The decoded `mpn_mul_1` node, from computed shapes.** -/
theorem mul1PhysBodyLit_decode_gen :
    decodeLprog (encodeLfundefBytes mul1PhysBodyLit)
      = some (nodeLayout mul1DecPre mul1DecLoop mul1DecPost) := by
  rw [decodeLprog_node_gen mul1PhysBodyLit (mul1PhysBodyLit.take 18)
    ((mul1PhysBodyLit.drop 21).take 56) ((mul1PhysBodyLit.drop 80).take 6)
    mul1Cmp ⟨0, .Lcond (.reg "Z") 1073741828⟩ ⟨0, .Llabel .internal 4⟩
    mul1Cmp ⟨0, .Lcond (.reg "NZ") 4⟩ ⟨0, .Llabel .internal 1073741828⟩ ⟨0, .Lret⟩
    4 1073741828 "%rbp" .internal .internal mul1PhysBodyLit_split
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) rfl rfl
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)]
  decide +kernel

/-- **The decoded `mpn_mul_1` node of the exporter's physical body, from computed
    shapes.** -/
theorem mul1PhysBody_decode_gen :
    decodeLprog (encodeLfundefBytes mul1PhysBody)
      = some (nodeLayout mul1DecPre mul1DecLoop mul1DecPost) := by
  rw [mul1PhysBody_eq]
  exact mul1PhysBodyLit_decode_gen

/-! ## Coverage of `shapeOf` -/

#kat (shapesOf (Params.ofBody mul1PhysBodyLit) mul1PhysBodyLit).isSome

#kat (shapesOf (Params.ofBody (binLoopBody (andMid "AND:64" "SHL:0:64") "SHL:0:64"))
  (binLoopBody (andMid "AND:64" "SHL:0:64") "SHL:0:64")).isSome

#kat (shapesOf (Params.ofBody (binLoopBody (andMid "XOR:64" "SHL:0:64") "SHL:0:64"))
  (binLoopBody (andMid "XOR:64" "SHL:0:64") "SHL:0:64")).isSome

#kat (shapesOf (Params.ofBody (binLoopBody (iorMid "SHL:0:64") "SHL:0:64"))
  (binLoopBody (iorMid "SHL:0:64") "SHL:0:64")).isSome

end CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenMul1
