/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecodeClosed
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopFrontEmit

@[expose] public section

set_option autoImplicit false

/-!
# The decoder's loop bodies are the front's

`LprogBytesDecode.binLoopBody` is a literal `Lcmd`, and the byte round trips
`LprogBytesDecodeClosed.and_n_roundtrip_closed` and its siblings are stated at
it. `MpnLoopBytesEmit.kernels` links the objects encoded from
`MpnLoopFrontEmit.andLprog`, `xorLprog` and `iorLprog`, which
`MpnLoopFrontEmit.binLprog` front-compiles. This module equates the two.

## Main results

* `LinstrR` and `Linstr` carry `DecidableEq`.
* `andLprog_body_eq`, `xorLprog_body_eq`, `iorLprog_body_eq` — each front
  `Lprog` has one function, named as the seam links it, whose body is the
  decoder module's literal at that limb operation.
* `and_n_front_roundtrip`, `xor_n_front_roundtrip`, `ior_n_front_roundtrip` —
  the byte round trip at the front-compiled body.

## Scope

The three body equations are `native_decide`: the front's definitions do not
reduce in the kernel, so neither the bodies nor their lengths are `rfl`. Each
adds `Lean.ofReduceBool`, which `MpnLoopFrontEmit.andLprog_isSome` and its
siblings — already on the way to any statement about `andLprog.get` — also add.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopFrontBodyTie

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecodeClosed
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopFrontEmit

deriving instance DecidableEq for LinstrR
deriving instance DecidableEq for Linstr

/-! ## 1. The front bodies -/

/-- The body of the single function of a front-compiled `Lprog`, paired with the
    symbol that function is linked under. -/
def namedBody (p : Lprog) : List (String × Lcmd) :=
  p.lp_funcs.map (fun f => (f.1, f.2.lfd_body))

/-- **`mpn_and_n_loop_owned`.** The front `Lprog` the seam encodes has one
    function, linked as `mpn_and_n_loop_owned`, whose body is the decoder
    module's `binLoopBody` at the `AND:64` limb operation. -/
theorem andLprog_body_eq :
    namedBody (andLprog.get andLprog_isSome)
      = [("mpn_and_n_loop_owned", binLoopBody (andMid "AND:64" "SHL:0:64") "SHL:0:64")] := by
  native_decide

/-- **`mpn_xor_n_loop_owned`.** As `andLprog_body_eq`, at the `XOR:64` limb
    operation. -/
theorem xorLprog_body_eq :
    namedBody (xorLprog.get xorLprog_isSome)
      = [("mpn_xor_n_loop_owned", binLoopBody (andMid "XOR:64" "SHL:0:64") "SHL:0:64")] := by
  native_decide

/-- **`mpn_ior_n_loop_owned`.** As `andLprog_body_eq`, at the limb operation
    `iorMid`. -/
theorem iorLprog_body_eq :
    namedBody (iorLprog.get iorLprog_isSome)
      = [("mpn_ior_n_loop_owned", binLoopBody (iorMid "SHL:0:64") "SHL:0:64")] := by
  native_decide

/-! ## 2. The byte round trip at the front bodies -/

/-- The body a `namedBody` equation exhibits. -/
theorem body_of_namedBody {p : Lprog} {s : String} {body : Lcmd}
    (h : namedBody p = [(s, body)]) :
    ∃ fd, p.lp_funcs = [(s, fd)] ∧ fd.lfd_body = body := by
  unfold namedBody at h
  match hp : p.lp_funcs with
  | [] => rw [hp] at h; exact absurd h (by simp)
  | (s', fd) :: rest =>
      rw [hp] at h
      simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨hs, hb⟩, hrest⟩ := h
      refine ⟨fd, ?_, hb⟩
      rw [hs, List.map_eq_nil_iff.mp hrest]

/-- **The `and` kernel's bytes decode.** The front-compiled `Lprog` the seam
    encodes has one function, linked as `mpn_and_n_loop_owned`, and the function
    bytes the encoder lays down for its body decode to
    `binDecoded (andMidDecoded .and_)`. -/
theorem and_n_front_roundtrip :
    ∃ fd, (andLprog.get andLprog_isSome).lp_funcs = [("mpn_and_n_loop_owned", fd)]
      ∧ decodeLprog (encodeLfundefBytes fd.lfd_body)
          = some (binDecoded (andMidDecoded .and_)) := by
  obtain ⟨fd, hfd, hb⟩ := body_of_namedBody andLprog_body_eq
  exact ⟨fd, hfd, hb ▸ and_n_roundtrip_closed⟩

/-- **The `xor` kernel's bytes decode.** As `and_n_front_roundtrip`, at the
    `XOR:64` limb operation. -/
theorem xor_n_front_roundtrip :
    ∃ fd, (xorLprog.get xorLprog_isSome).lp_funcs = [("mpn_xor_n_loop_owned", fd)]
      ∧ decodeLprog (encodeLfundefBytes fd.lfd_body)
          = some (binDecoded (andMidDecoded .xor_)) := by
  obtain ⟨fd, hfd, hb⟩ := body_of_namedBody xorLprog_body_eq
  exact ⟨fd, hfd, hb ▸ xor_n_roundtrip_closed⟩

/-- **The `ior` kernel's bytes decode.** As `and_n_front_roundtrip`, at the limb
    operation `iorMid`. -/
theorem ior_n_front_roundtrip :
    ∃ fd, (iorLprog.get iorLprog_isSome).lp_funcs = [("mpn_ior_n_loop_owned", fd)]
      ∧ decodeLprog (encodeLfundefBytes fd.lfd_body) = some (binDecoded iorMidDecoded) := by
  obtain ⟨fd, hfd, hb⟩ := body_of_namedBody iorLprog_body_eq
  exact ⟨fd, hfd, hb ▸ ior_n_roundtrip_closed⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopFrontBodyTie
