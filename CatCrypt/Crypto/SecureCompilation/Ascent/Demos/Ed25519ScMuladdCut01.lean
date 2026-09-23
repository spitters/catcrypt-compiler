/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScMuladdSegments

/-!
# Part 1 of the shipped multiply-accumulate, checked in two halves

The part check of part 1 reduces a symbolic run of the whole part in `decide +kernel`;
this module checks the part as two runs, split after segment 8 of `scmSegs 1`, joined
at the boundary certificate `scmCut01`. The certificate is the symbolic state at the
boundary, produced by `scripts/cutgen/Ed25519ScMuladdCutAll.lean` from the same executor
outside the kernel. The second half starts at slot 42, one past the last slot the
certificate mentions.

## Main results

* `scm_part01a`, `scm_part01b`: the two half checks.
* `scm_part01_of_halves`: the conclusion `partCheck_sound` draws from the whole-part
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

/-- The locations of the symbolic state after segment 8 of part 1. -/
def scmCut01 : List (Loc × WE) :=
  [(CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%rcx",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 40),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%rax",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 41),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%rsi",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 40),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%r14",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 7),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%rdx",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 0),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%r15",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 7),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%rbx",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 39),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%rdi",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.xor
    (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.and
      (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 10)
      (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 37))
    (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.and
      (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.xor
        (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 10)
        (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 37))
      (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.xor
        (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 19)
        (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 38)))),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%rbp",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.xor
    (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 19)
    (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 38)),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%r13",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.xor
    (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 34)
    (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 35)),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%r10",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 38),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%r9",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 37),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%r12",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 33),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%r8",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 11),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%r11",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 1),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" (-128),
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 40),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 96,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 28),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 128,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 7),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 112,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 6),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 104,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 5),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 88,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 4),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 120,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 3),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 80,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 2),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 168,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.lit 3),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 160,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.lit 2),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 152,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.lit 1),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 144,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 23),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rcx" 24,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 11),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rcx" 16,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 10),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rcx" 8,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 9),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rcx" 0,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 8),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rdx" 24,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 7),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rdx" 16,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 6),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rdx" 8,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 5),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rdx" 0,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 4),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsi" 24,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 3),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsi" 16,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 2),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsi" 8,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 1),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsi" 0,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 0)]

/-- The abstract state at the boundary. -/
def scmCut01State : DState :=
  ⟨true, [("%rcx", none), ("%rsi", none), ("%rdx", none), ("%rdi", none), ("%r9", none), ("%r8", none)], [(("%rsp", 168), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.const 0x0000000000000003#64),
 (("%rsp", 160), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.const 0x0000000000000002#64),
 (("%rsp", 152), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.const 0x0000000000000001#64),
 (("%rsp", 144), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.const 0x0000000000000000#64),
 (("%rsp", 136), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.ptr "%rdi" 0),
 (("%rsp", -16), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.ptr "%rcx" 0),
 (("%rsp", -8), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.ptr "%rdx" 0),
 (("%rsp", 224), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.ptr "%rsi" 0),
 (("%rsp", 232), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.ptr "%rdi" 0)]⟩

/-- The first half carries the entry of part 1 to the certificate. -/
theorem scm_part01a :
    partCheck 16 ((mSlice 16 69).take 26) scmIn scmCut01
      (canonFromD shippedBank {} ((scmSegs 1).take 8).flatten) = true := by
  decide +kernel

/-- The second half carries the certificate to the exit of part 1. -/
theorem scm_part01b :
    partCheck 42 ((mSlice 16 69).drop 26) scmCut01 scmMap1
      (canonFromD shippedBank scmCut01State ((scmSegs 1).drop 8).flatten) = true := by
  decide +kernel

/-- The two halves carry the entry of part 1 to its exit across the canonical block of
    the whole part: the conclusion `partCheck_sound` draws from the whole-part check. -/
theorem scm_part01_of_halves (ρ : Nat → BitVec 64) (hH : Holds ρ 16 (mSlice 16 69))
    (hK : ∀ j c, cK j = some c → ρ j = BitVec.ofNat 64 c)
    (s : JState 64) (hin : MapHolds ρ scmIn s) :
    MapHolds ρ scmMap1 (runBlock s (canonFromD shippedBank {} (scmPart 1))) := by
  have hlen : ((mSlice 16 69).take 26).length = 26 := by
    rw [List.length_take, mSlice_length 16 69 (by omega) (by omega) (by omega)]
    omega
  obtain ⟨h1, h2⟩ := (holds_append ρ ((mSlice 16 69).take 26) ((mSlice 16 69).drop 26) 16).1 (by
    rw [List.take_append_drop]
    exact hH)
  rw [hlen] at h2
  have q1 := partCheck_sound 16 _ scmIn scmCut01 _ scm_part01a ρ h1
    (fun j c _ hc => hK j c hc) s hin
  have q2 := partCheck_sound 42 _ scmCut01 scmMap1 _ scm_part01b ρ h2
    (fun j c _ hc => hK j c hc) _ q1
  have hstate : runD shippedBank {} ((scmSegs 1).take 8).flatten = scmCut01State := by decide +kernel
  rw [scmPart_cut 1 8 (by decide), canonFromD_append, hstate, runBlock_cat]
  exact q2

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScMuladdShippedProof
