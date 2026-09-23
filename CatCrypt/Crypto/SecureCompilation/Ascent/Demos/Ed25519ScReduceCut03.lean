/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceSegments

/-!
# Part 3 of the shipped scalar reduction, checked in two halves

The part check of part 3 reduces a symbolic run of the whole part in `decide +kernel`;
this module checks the part as two runs, split after segment 8 of `scrSegs 3`, joined
at the boundary certificate `scrCut03`. The certificate is the symbolic state at the
boundary, produced by `scripts/cutgen/Ed25519ScReduceCutAll.lean` from the same executor
outside the kernel. The second half starts at slot 143, one past the last slot the
certificate mentions.

## Main results

* `scr_part03a`, `scr_part03b`: the two half checks.
* `scr_part03_of_halves`: the conclusion `partCheck_sound` draws from the whole-part
  check, derived from the two halves.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false
set_option exponentiation.threshold 600

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519ScReduceShipped

/-- The locations of the symbolic state after segment 8 of part 3. -/
def scrCut03 : List (Loc × WE) :=
  [(CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%rcx",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 142),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%rdi",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 141),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%rsi",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 140),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%r14",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.lit 18446744073709551615),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%rdx",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 12),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%r15",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.lit 18446744073709551615),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%rbx",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 139),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%rbp",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.xor
    (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.lit 18446744073709551615)
    (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 138)),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%r12",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.xor
    (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 134)
    (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 135)),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%r10",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 138),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%r11",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 133),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%r13",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.xor
    (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.lit 0)
    (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 125)),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%rax",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 124),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%r8",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 123),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%r9",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 118),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" (-128),
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 140),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 72,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 8),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 80,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 9),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 120,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 10),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 128,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 11),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 112,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.lit 6346243789798364141),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 104,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.lit 1503914060200516822),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 96,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.lit 0),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 88,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.lit 1152921504606846976),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 0,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 12),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 48,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 13),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 56,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 14),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 64,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 15),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 8,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.lit 17121812371768873755),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 16,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.lit 2379626136568277415),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 24,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.lit 18446744073709551595),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 32,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.lit 18446744073709551615),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 40,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.lit 15)]

/-- The abstract state at the boundary. -/
def scrCut03State : DState :=
  ⟨true, [("%rcx", none),
 ("%rdi", none),
 ("%rsi", none),
 ("%r14", some (CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.const 0xffffffffffffffff#64)),
 ("%rdx", none),
 ("%r15", some (CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.const 0xffffffffffffffff#64)),
 ("%r8", none),
 ("%r9", none)], [(("%rsp", 88), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.const 0x1000000000000000#64),
 (("%rsp", 96), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.const 0x0000000000000000#64),
 (("%rsp", 104), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.const 0x14def9dea2f79cd6#64),
 (("%rsp", 112), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.const 0x5812631a5cf5d3ed#64),
 (("%rsp", 40), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.const 0x000000000000000f#64),
 (("%rsp", 32), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.const 0xffffffffffffffff#64),
 (("%rsp", 24), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.const 0xffffffffffffffeb#64),
 (("%rsp", 16), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.const 0x2106215d086329a7#64),
 (("%rsp", 8), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.const 0xed9ce5a30a2c131b#64),
 (("%rsp", 168), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.const 0x0000000000000003#64),
 (("%rsp", 160), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.const 0x0000000000000002#64),
 (("%rsp", 152), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.const 0x0000000000000001#64),
 (("%rsp", 144), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.const 0x0000000000000000#64),
 (("%rsp", 136), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.ptr "%rdi" 0),
 (("%rsp", 224), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.ptr "%rsi" 0),
 (("%rsp", 232), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.ptr "%rdi" 0)]⟩

/-- The first half carries the entry of part 3 to the certificate. -/
theorem scr_part03a :
    partCheck 116 ((xSlice 116 169).take 27) scrMap2 scrCut03
      (canonFromD shippedBank (scrState 2) ((scrSegs 3).take 8).flatten) = true := by
  decide +kernel

/-- The second half carries the certificate to the exit of part 3. -/
theorem scr_part03b :
    partCheck 143 ((xSlice 116 169).drop 27) scrCut03 scrMap3
      (canonFromD shippedBank scrCut03State ((scrSegs 3).drop 8).flatten) = true := by
  decide +kernel

/-- The two halves carry the entry of part 3 to its exit across the canonical block of
    the whole part: the conclusion `partCheck_sound` draws from the whole-part check. -/
theorem scr_part03_of_halves (ρ : Nat → BitVec 64) (hH : Holds ρ 116 (xSlice 116 169))
    (hK : ∀ j c, cK j = some c → ρ j = BitVec.ofNat 64 c)
    (s : JState 64) (hin : MapHolds ρ scrMap2 s) :
    MapHolds ρ scrMap3 (runBlock s (canonFromD shippedBank (scrState 2) (scrPart 3))) := by
  have hlen : ((xSlice 116 169).take 27).length = 27 := by
    rw [List.length_take, xSlice_length 116 169 (by omega) (by omega) (by omega)]
    omega
  obtain ⟨h1, h2⟩ := (holds_append ρ ((xSlice 116 169).take 27) ((xSlice 116 169).drop 27) 116).1 (by
    rw [List.take_append_drop]
    exact hH)
  rw [hlen] at h2
  have q1 := partCheck_sound 116 _ scrMap2 scrCut03 _ scr_part03a ρ h1
    (fun j c _ hc => hK j c hc) s hin
  have q2 := partCheck_sound 143 _ scrCut03 scrMap3 _ scr_part03b ρ h2
    (fun j c _ hc => hK j c hc) _ q1
  have hstate : runD shippedBank (scrState 2) ((scrSegs 3).take 8).flatten = scrCut03State := by decide +kernel
  rw [scrPart_cut 3 8 (by decide), canonFromD_append, hstate, runBlock_cat]
  exact q2

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof
