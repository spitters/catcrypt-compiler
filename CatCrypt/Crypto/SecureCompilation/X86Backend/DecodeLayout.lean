/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGen

@[expose] public section

set_option autoImplicit false

/-!
# The decoded program of a function body's bytes

`DecodeGen.decodeLprog_encodeLfundefBytes_gen` decodes the function bytes of a body whose
per-instruction shapes are computed (`DecodeGen.shapesOf`, sound by `DecodeGen.shapeOf_ok`),
under the frame and branch hypotheses of `PhysAbiShape.decodeLprog_encodeLfundefBytes_shapes`.
This module collects those hypotheses into one Boolean class of bodies, `decodableLcmd`, and
names the program they decode to, `fundefLayout`, a function of the body alone.

`decodableLcmd body` holds when every instruction of `body` has a computed shape, the body
saves no register by `push`, its frame is non-zero and in `rel32` range, and the branches of
its item list are well formed (`LprogBytesDecode.branchOK`: every branch targets a defined
label followed by an instruction, at the byte offset its displacement names). The class is a
property of the body; no decoder runs over the function's byte stream.

## Main results

* `decodeLprog_encodeLfundefBytes`: for every body in the class `decodableLcmd`, the function
  bytes `encodeLfundefBytes body` decode to `fundefLayout body`.
* `decodeLprog_of_encodeChecked`: the same for the bytes of the gated encoder
  `encodeLfundefBytesChecked`.
* `decodeLprog_of_decodesToB`: bytes of the gated encoder decode to every program `p` that
  the Boolean test `decodesToB body p` accepts.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeLayout

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Lcmd)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (calleeSavedToSave)
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder (dispOk32)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGen

/-- The item list of the function bytes of `body` over its computed shapes: the frame `leaq`,
    the items of the body, the closing `leaq` and `ret`. -/
def fundefItems (body : Lcmd) : List Item :=
  fundefItemsL body (shapesD (Params.ofBody body) body)

/-- The program the function bytes of `body` decode to: the program its item list denotes,
    each branch resolved to the index of the instruction after its target label. -/
def fundefLayout (body : Lcmd) : Option (List RInstr) :=
  expectedFrom (fundefItems body) (fundefItems body)

/-- **The decodable bodies.** Every instruction has a computed shape, no register is saved by
    `push`, the frame is non-zero with both frame displacements in `rel32` range, and the
    branches of the item list are well formed. -/
def decodableLcmd (body : Lcmd) : Bool :=
  (shapesOf (Params.ofBody body) body).isSome
    && (calleeSavedToSave body).isEmpty
    && (Params.ofBody body).frame != 0
    && dispOk32 (Int.ofNat (Params.ofBody body).frame)
    && dispOk32 (-(Int.ofNat (Params.ofBody body).frame))
    && branchOK (fundefItems body) 0 (fundefItems body)

/-- **The decode equation of a decodable body.** The function bytes of every body in the class
    `decodableLcmd` decode to `fundefLayout body`. -/
theorem decodeLprog_encodeLfundefBytes {body : Lcmd} (h : decodableLcmd body = true) :
    decodeLprog (encodeLfundefBytes body) = fundefLayout body := by
  simp only [decodableLcmd, Bool.and_eq_true, List.isEmpty_iff, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨hsh, hsaves⟩, hF0⟩, hF⟩, hF'⟩, hbr⟩ := h
  exact decodeLprog_encodeLfundefBytes_gen body hsh hsaves (Int.ofNat_ne_zero.mpr hF0) hF hF'
    hbr

/-- The bytes of the gated encoder of a decodable body decode to `fundefLayout body`. -/
theorem decodeLprog_of_encodeChecked {body : Lcmd} {bytes : List (BitVec 8)}
    (he : encodeLfundefBytesChecked body = some bytes) (h : decodableLcmd body = true) :
    decodeLprog bytes = fundefLayout body := by
  rw [encodeLfundefBytesChecked_eq he]
  exact decodeLprog_encodeLfundefBytes h

/-- The body is decodable and `p` is its decoded program `fundefLayout body`. -/
def decodesToB (body : Lcmd) (p : List RInstr) : Bool :=
  decodableLcmd body && decide (fundefLayout body = some p)

/-- Bytes of the gated encoder at a body that `decodesToB` accepts at `p` decode to `p`. -/
theorem decodeLprog_of_decodesToB {body : Lcmd} {bytes : List (BitVec 8)} {p : List RInstr}
    (he : encodeLfundefBytesChecked body = some bytes) (h : decodesToB body p = true) :
    decodeLprog bytes = some p := by
  simp only [decodesToB, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [decodeLprog_of_encodeChecked he h.1, h.2]

end CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeLayout
