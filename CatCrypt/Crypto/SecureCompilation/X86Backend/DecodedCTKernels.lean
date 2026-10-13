/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1DecodedNode
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519KernelsBytes

/-!
# The byte-level constant-time checker on two shipped kernels

The checker `DecodedCT.bytesCTCheck` decided by the kernel on the decoded bytes of two
owned kernels, with a rejection for each when a pointer or the count is secret.

## Main results

* `mul1Node_bytesCT`: the checker accepts the decoded `mpn_mul_1` node with the pointer
  arguments `%rdi`, `%rsi`, the count `%rdx` and `%rsp` public, and the multiplier `%rcx`
  and the array contents secret; `mul1Node_secretCount_rejected` and
  `mul1Node_secretPointer_rejected` are the rejections with the count or the result
  pointer secret.
* `feAddFramed_bytesCT`: the encoding of the framed `fe25519_add` decodes to a block that,
  followed by `ret`, the checker accepts with the three pointers and `%rsp` public;
  `feAddFramed_secretPointer_rejected` is the rejection with an input pointer secret.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT

open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr)

/-! ## 1. The decoded `mpn_mul_1` node -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemLoop (nodeLayout)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1DecodedNode
  (mul1DecPre mul1DecLoop mul1DecPost)

/-- The public entry set of `mpn_mul_1`: the result pointer `%rdi`, the source pointer
    `%rsi`, the count `%rdx` and the stack pointer. The multiplier `%rcx`, the other
    registers, the memory and the flags are secret. -/
def mul1PubA : PubA := ⟨["%rdi", "%rsi", "%rdx", "%rsp"], [], false, []⟩

/-- The frame words the analysis of `mpn_mul_1` keeps public: the saved pointers at `56`
    and `48`, the saved count at `-8` and the saved source pointer at `-128`. -/
def mul1FrameCells : List Int := [56, 48, -8, -128]

/-- **The checker accepts the decoded `mpn_mul_1` node** under DOITM, from `mul1PubA`
    with the frame words `mul1FrameCells`. -/
theorem mul1Node_bytesCT :
    bytesCTCheck .doitm mul1FrameCells mul1PubA (nodeLayout mul1DecPre mul1DecLoop mul1DecPost)
      = true := by
  decide +kernel

/-- With the count `%rdx` secret the checker rejects the node: the loop guard reads it. -/
theorem mul1Node_secretCount_rejected :
    bytesCTCheck .doitm mul1FrameCells ⟨["%rdi", "%rsi", "%rsp"], [], false, []⟩
      (nodeLayout mul1DecPre mul1DecLoop mul1DecPost) = false := by
  decide +kernel

/-- With the result pointer `%rdi` secret the checker rejects the node: the stores
    address through it. -/
theorem mul1Node_secretPointer_rejected :
    bytesCTCheck .doitm mul1FrameCells ⟨["%rsi", "%rdx", "%rsp"], [], false, []⟩
      (nodeLayout mul1DecPre mul1DecLoop mul1DecPost) = false := by
  decide +kernel

/-! ## 2. The framed field addition `fe25519_add` -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder (decodeJStream)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder (encodeJBlock)
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384 (s2nAlloc)
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519KernelsBytes
  (feAddFramed feAddFramed_length feAddFramed_instrOk decode_phys)

/-- The public entry set of the field kernels: the output pointer `%rdi`, the input
    pointers `%rsi` and `%rdx`, and the stack pointer. The limbs, the other registers
    and the flags are secret. -/
def fePubA : PubA := ⟨["%rdi", "%rsi", "%rdx", "%rsp"], [], false, []⟩

/-- **The checker accepts the decoded `fe25519_add` bytes.** The encoding of the framed
    field addition decodes to a block `c`, and `c` followed by `ret` passes the checker
    under DOITM from `fePubA`, with no frame word public. -/
theorem feAddFramed_bytesCT :
    ∃ c, decodeJStream 57 (encodeJBlock s2nAlloc feAddFramed) = some c ∧
      bytesCTCheck .doitm [] fePubA (c.map .op ++ [.ret]) = true :=
  ⟨feAddFramed, feAddFramed_length ▸ decode_phys _ feAddFramed_instrOk, by decide +kernel⟩

/-- With the input pointer `%rdx` secret the checker rejects the block: its loads address
    through it. -/
theorem feAddFramed_secretPointer_rejected :
    bytesCTCheck .doitm [] ⟨["%rdi", "%rsi", "%rsp"], [], false, []⟩
      (feAddFramed.map .op ++ [.ret]) = false := by
  decide +kernel

end CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT
