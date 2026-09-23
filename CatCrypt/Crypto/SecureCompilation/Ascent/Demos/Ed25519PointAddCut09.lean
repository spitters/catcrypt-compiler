/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddSegments

/-!
# Part 9 of the shipped point addition, checked in two halves

The part check of part 9 reduces a symbolic run of the whole part in `decide +kernel`;
this module checks the part as two runs, split after segment 8 of `paSegs 9`, joined
at the boundary certificate `paCut09`. The certificate is the symbolic state at the
boundary, produced by `scripts/cutgen/Ed25519PointAddCutAll.lean` from the same executor
outside the kernel. The second half starts at slot 2130, one past the last slot the
certificate mentions.

## Main results

* `pa_part09a`, `pa_part09b`: the two half checks.
* `pa_part09_of_halves`: the conclusion `partCheck2_sound` draws from the whole-part
  check, derived from the two halves.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false
set_option exponentiation.threshold 600

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddShippedProof

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519PointAddShipped
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof

/-- The locations of the symbolic state after segment 8 of part 9. -/
def paCut09 : List (Loc × WE) :=
  [(CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%r11",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 2129),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%rax",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 2107),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%r8",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 2126),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%rdi",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 2125),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%r14",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 1412),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%rdx",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 1384),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%r15",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 1412),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%rsi",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.lit 0),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%rbx",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.lit 0),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%r10",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 2120),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%r12",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 2117),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%rcx",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 2113),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%rbp",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.lit 9223372036854775808),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%r9",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 2105),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%r13",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 2067),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 256,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 2128),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" (-128),
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 2107),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 288,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 2124),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 280,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 2123),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 272,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 2122),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 264,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 2121),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 248,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 1358),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 176,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 1384),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 184,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 1385),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 192,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 1386),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 200,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 1387),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 296,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 1412),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 312,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 1413),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 320,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 1414),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 328,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 1415),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 208,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 1667),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 216,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 1668),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 224,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 1669),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 304,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 1670),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 144,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 1894),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 152,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 1895),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 160,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 1896),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 168,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 1897),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 136,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 1901),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 128,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 1941)]

/-- The carry flag at the boundary. -/
def paCut09Carry : Option WE := some (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 2129)

/-- The zero flag at the boundary. -/
def paCut09Zero : Option WE := none

/-- The abstract state at the boundary. -/
def paCut09State : DState :=
  ⟨true, [("%rdi", none),
 ("%r8", none),
 ("%rdx", none),
 ("%rsi", some (CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.const 0x0000000000000000#64)),
 ("%rbx", some (CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.const 0x0000000000000000#64)),
 ("%rcx", none),
 ("%rbp", some (CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.const 0x8000000000000000#64)),
 ("%r9", none)], [(("%rsp", 384), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.ptr "%rsi" 0),
 (("%rsp", 392), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.ptr "%rdi" 0)]⟩

/-- The first half carries the entry of part 9 to the certificate. -/
theorem pa_part09a :
    partCheck2 1996 (paSl9.take 134) paMap8 none none paCut09
      paCut09Carry paCut09Zero (canonFromD shippedBank (paState 8) ((paSegs 9).take 8).flatten) = true := by
  decide +kernel

/-- The second half carries the certificate to the exit of part 9. -/
theorem pa_part09b :
    partCheck2 2130 (paSl9.drop 134) paCut09 paCut09Carry paCut09Zero paMap9
      (some (aoWE (.v 2250))) none (canonFromD shippedBank paCut09State ((paSegs 9).drop 8).flatten) = true := by
  decide +kernel

/-- The two halves carry the entry of part 9 to its exit across the canonical block of
    the whole part: the conclusion `partCheck2_sound` draws from the whole-part check. -/
theorem pa_part09_of_halves (ρ : Nat → BitVec 64) (hH : Holds ρ 1996 paSl9)
    (hK : ∀ j c, cK j = some c → ρ j = BitVec.ofNat 64 c)
    (s : JState 64) (hin : MapHolds ρ paMap8 s) (hc : CfHolds ρ none s)
    (hz : ZfHolds ρ none s) :
    MapHolds ρ paMap9 (runBlock s (canonFromD shippedBank (paState 8) (paPart 9))) ∧
      CfHolds ρ (some (aoWE (.v 2250))) (runBlock s (canonFromD shippedBank (paState 8) (paPart 9))) ∧
      ZfHolds ρ none (runBlock s (canonFromD shippedBank (paState 8) (paPart 9))) := by
  have hlen : (paSl9.take 134).length = 134 := by
    simp only [List.length_take, paSl9_len]
    omega
  obtain ⟨h1, h2⟩ := (holds_append ρ (paSl9.take 134) (paSl9.drop 134) 1996).1 (by
    rw [List.take_append_drop]
    exact hH)
  rw [hlen] at h2
  obtain ⟨q1, c1, z1⟩ := partCheck2_sound 1996 _ paMap8 none none paCut09
    paCut09Carry paCut09Zero _ pa_part09a ρ h1 (fun j c _ hc => hK j c hc) s hin hc hz
  obtain ⟨q2, c2, z2⟩ := partCheck2_sound 2130 _ paCut09 paCut09Carry paCut09Zero
    paMap9 (some (aoWE (.v 2250))) none _ pa_part09b ρ h2 (fun j c _ hc => hK j c hc) _ q1 c1 z1
  have hstate : runD shippedBank (paState 8) ((paSegs 9).take 8).flatten = paCut09State := by decide +kernel
  rw [paPart_cut 9 8 (by decide), canonFromD_append, hstate, runBlock_cat]
  exact ⟨q2, c2, z2⟩

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddShippedProof
