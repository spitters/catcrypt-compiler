/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScMuladdSegments

/-!
# Part 9 of the shipped multiply-accumulate, checked in two halves

The part check of part 9 reduces a symbolic run of the whole part in `decide +kernel`;
this module checks the part as two runs, split after segment 5 of `scmSegs 9`, joined
at the boundary certificate `scmCut09`. The certificate is the symbolic state at the
boundary, produced by `scripts/cutgen/Ed25519ScMuladdCutAll.lean` from the same executor
outside the kernel. The second half starts at slot 425, one past the last slot the
certificate mentions.

## Main results

* `scm_part09a`, `scm_part09b`: the two half checks.
* `scm_part09_of_halves`: the conclusion `partCheck_sound` draws from the whole-part
  check, derived from the two halves.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false
set_option exponentiation.threshold 600

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScMuladdShippedProof

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519ScMuladdShipped
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof

/-- The locations of the symbolic state after segment 5 of part 9. -/
def scmCut09 : List (Loc × WE) :=
  [(CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%rcx",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.xor
    (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 422)
    (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 423)),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%r9",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.xor
    (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.lit 18446744073709551615)
    (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 424)),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%r12",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.xor
    (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 422)
    (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 423)),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%r11",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.and
    (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 422)
    (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 423)),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%rsi",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.shr
    (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.xor
      (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.and
        (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 412)
        (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.xor
          (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.lit 18446744073709551615)
          (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.lit 0)))
      (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.and
        (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.xor
          (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 412)
          (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.xor
            (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.lit 18446744073709551615)
            (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.lit 0)))
        (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.xor
          (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.lit 18446744073709551615)
          (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 423))))
    63),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%r13",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.and
    (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.xor
      (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 412)
      (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.xor
        (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.lit 18446744073709551615)
        (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.lit 0)))
    (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.xor
      (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.lit 18446744073709551615)
      (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 423))),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%r15",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 424),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%r10",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 421),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%rbx",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 418),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%rax",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 406),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%rdi",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 409),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%r8",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 412),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%rbp",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 415),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 128,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 424),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 144,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.lit 0),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 152,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.lit 1),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 160,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.lit 2),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 168,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.lit 3),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 120,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.lit 1503914060200516822),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 112,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.lit 0),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 104,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.lit 1152921504606846976)]

/-- The abstract state at the boundary. -/
def scmCut09State : DState :=
  ⟨true, [("%rcx", none),
 ("%r9", none),
 ("%rsi", none),
 ("%r8", none),
 ("%rdi", none),
 ("%r14", some (CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.const 0x1000000000000000#64)),
 ("%rdx", none)], [(("%rsp", 104), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.const 0x1000000000000000#64),
 (("%rsp", 112), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.const 0x0000000000000000#64),
 (("%rsp", 120), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.const 0x14def9dea2f79cd6#64),
 (("%rsp", 24), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.const 0xffffffffffffffeb#64),
 (("%rsp", 16), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.const 0x2106215d086329a7#64),
 (("%rsp", 8), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.const 0xed9ce5a30a2c131b#64),
 (("%rsp", 168), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.const 0x0000000000000003#64),
 (("%rsp", 160), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.const 0x0000000000000002#64),
 (("%rsp", 152), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.const 0x0000000000000001#64),
 (("%rsp", 144), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.const 0x0000000000000000#64),
 (("%rsp", 136), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.ptr "%rdi" 0),
 (("%rsp", -16), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.ptr "%rcx" 0),
 (("%rsp", -8), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.ptr "%rdx" 0),
 (("%rsp", 224), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.ptr "%rsi" 0),
 (("%rsp", 232), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.ptr "%rdi" 0)]⟩

/-- The first half carries the entry of part 9 to the certificate. -/
theorem scm_part09a :
    partCheck 416 ((mSlice 416 434).take 9) scmMap8 scmCut09
      (canonFromD shippedBank (scmState 8) ((scmSegs 9).take 5).flatten) = true := by
  decide +kernel

/-- The second half carries the certificate to the exit of part 9. -/
theorem scm_part09b :
    partCheck 425 ((mSlice 416 434).drop 9) scmCut09 scmOut
      (canonFromD shippedBank scmCut09State ((scmSegs 9).drop 5).flatten) = true := by
  decide +kernel

/-- The two halves carry the entry of part 9 to its exit across the canonical block of
    the whole part: the conclusion `partCheck_sound` draws from the whole-part check. -/
theorem scm_part09_of_halves (ρ : Nat → BitVec 64) (hH : Holds ρ 416 (mSlice 416 434))
    (hK : ∀ j c, cK j = some c → ρ j = BitVec.ofNat 64 c)
    (s : JState 64) (hin : MapHolds ρ scmMap8 s) :
    MapHolds ρ scmOut (runBlock s (canonFromD shippedBank (scmState 8) (scmPart 9))) := by
  have hlen : ((mSlice 416 434).take 9).length = 9 := by
    rw [List.length_take, mSlice_length 416 434 (by omega) (by omega) (by omega)]
    omega
  obtain ⟨h1, h2⟩ := (holds_append ρ ((mSlice 416 434).take 9) ((mSlice 416 434).drop 9) 416).1 (by
    rw [List.take_append_drop]
    exact hH)
  rw [hlen] at h2
  have q1 := partCheck_sound 416 _ scmMap8 scmCut09 _ scm_part09a ρ h1
    (fun j c _ hc => hK j c hc) s hin
  have q2 := partCheck_sound 425 _ scmCut09 scmOut _ scm_part09b ρ h2
    (fun j c _ hc => hK j c hc) _ q1
  have hstate : runD shippedBank (scmState 8) ((scmSegs 9).take 5).flatten = scmCut09State := by decide +kernel
  rw [scmPart_cut 9 5 (by decide), canonFromD_append, hstate, runBlock_cat]
  exact q2

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScMuladdShippedProof
