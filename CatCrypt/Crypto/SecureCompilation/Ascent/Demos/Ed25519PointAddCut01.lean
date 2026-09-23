/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddSegments

/-!
# Part 1 of the shipped point addition, checked in two halves

The part check of part 1 reduces a symbolic run of the whole part in `decide +kernel`;
this module checks the part as two runs, split after segment 8 of `paSegs 1`, joined
at the boundary certificate `paCut01`. The certificate is the symbolic state at the
boundary, produced by `scripts/cutgen/Ed25519PointAddCutAll.lean` from the same executor
outside the kernel. The second half starts at slot 112, one past the last slot the
certificate mentions.

## Main results

* `pa_part01a`, `pa_part01b`: the two half checks.
* `pa_part01_of_halves`: the conclusion `partCheck2_sound` draws from the whole-part
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

/-- The locations of the symbolic state after segment 8 of part 1. -/
def paCut01 : List (Loc × WE) :=
  [(CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%rax",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 111),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%rbx",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 110),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%rcx",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 109),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%r13",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 108),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%r10",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 107),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%r12",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 105),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%r9",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 104),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%r8",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 96),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%rdi",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 95),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%rbp",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 92),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%rsi",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 89),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%r11",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 86),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.reg "%r15",
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 25),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 72,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 84),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" (-128),
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 61),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 64,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 83),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 56,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 82),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 48,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 81),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 144,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 25),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 152,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 26),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 168,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 27),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 184,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 28),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 80,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 29),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 88,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 30),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 96,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 31),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 104,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 32),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 232,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 33),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 240,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 34),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 248,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 35),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 256,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 36),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 160,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 37),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 176,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 38),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 192,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 39),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 200,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 40),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 208,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 41),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 216,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 42),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 224,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 43),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 264,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 44),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 112,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 45),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 120,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 46),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 128,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 47),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 136,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 48),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 304,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 49),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 312,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 50),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 320,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 51),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 328,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 52),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 272,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 53),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 280,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 54),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 288,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 55),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsp" 296,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 56),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsi" 248,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 56),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsi" 240,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 55),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsi" 232,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 54),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsi" 224,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 53),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsi" 216,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 52),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsi" 208,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 51),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsi" 200,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 50),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsi" 192,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 49),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsi" 184,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 48),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsi" 176,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 47),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsi" 168,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 46),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsi" 160,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 45),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsi" 152,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 44),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsi" 144,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 43),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsi" 136,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 42),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsi" 128,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 41),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsi" 120,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 40),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsi" 112,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 39),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsi" 104,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 38),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsi" 96,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 37),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsi" 88,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 36),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsi" 80,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 35),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsi" 72,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 34),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsi" 64,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 33),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsi" 56,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 32),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsi" 48,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 31),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsi" 40,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 30),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsi" 32,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 29),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsi" 24,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 28),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsi" 16,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 27),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsi" 8,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 26),
 (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.Loc.cell "%rsi" 0,
  CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 25)]

/-- The carry flag at the boundary. -/
def paCut01Carry : Option WE := none

/-- The zero flag at the boundary. -/
def paCut01Zero : Option WE := some (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.and
  (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 96)
  (CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof.WE.v 96))

/-- The abstract state at the boundary. -/
def paCut01State : DState :=
  ⟨true, [("%rcx", none),
 ("%r9", none),
 ("%r8", none),
 ("%rdi", none),
 ("%rsi", none),
 ("%r14", some (CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.ptr "%rsi" 0))], [(("%rsp", 384), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.ptr "%rsi" 0),
 (("%rsp", 392), CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived.AVal.ptr "%rdi" 0)]⟩

/-- The first half carries the entry of part 1 to the certificate. -/
theorem pa_part01a :
    partCheck2 57 (paSl1.take 55) paIn none none paCut01
      paCut01Carry paCut01Zero (canonFromD shippedBank {} ((paSegs 1).take 8).flatten) = true := by
  decide +kernel

/-- The second half carries the certificate to the exit of part 1. -/
theorem pa_part01b :
    partCheck2 112 (paSl1.drop 55) paCut01 paCut01Carry paCut01Zero paMap1
      (some (aoWE (.v 238))) none (canonFromD shippedBank paCut01State ((paSegs 1).drop 8).flatten) = true := by
  decide +kernel

/-- The two halves carry the entry of part 1 to its exit across the canonical block of
    the whole part: the conclusion `partCheck2_sound` draws from the whole-part check. -/
theorem pa_part01_of_halves (ρ : Nat → BitVec 64) (hH : Holds ρ 57 paSl1)
    (hK : ∀ j c, cK j = some c → ρ j = BitVec.ofNat 64 c)
    (s : JState 64) (hin : MapHolds ρ paIn s) (hc : CfHolds ρ none s)
    (hz : ZfHolds ρ none s) :
    MapHolds ρ paMap1 (runBlock s (canonFromD shippedBank {} (paPart 1))) ∧
      CfHolds ρ (some (aoWE (.v 238))) (runBlock s (canonFromD shippedBank {} (paPart 1))) ∧
      ZfHolds ρ none (runBlock s (canonFromD shippedBank {} (paPart 1))) := by
  have hlen : (paSl1.take 55).length = 55 := by
    simp only [List.length_take, paSl1_len]
    omega
  obtain ⟨h1, h2⟩ := (holds_append ρ (paSl1.take 55) (paSl1.drop 55) 57).1 (by
    rw [List.take_append_drop]
    exact hH)
  rw [hlen] at h2
  obtain ⟨q1, c1, z1⟩ := partCheck2_sound 57 _ paIn none none paCut01
    paCut01Carry paCut01Zero _ pa_part01a ρ h1 (fun j c _ hc => hK j c hc) s hin hc hz
  obtain ⟨q2, c2, z2⟩ := partCheck2_sound 112 _ paCut01 paCut01Carry paCut01Zero
    paMap1 (some (aoWE (.v 238))) none _ pa_part01b ρ h2 (fun j c _ hc => hK j c hc) _ q1 c1 z1
  have hstate : runD shippedBank {} ((paSegs 1).take 8).flatten = paCut01State := by decide +kernel
  rw [paPart_cut 1 8 (by decide), canonFromD_append, hstate, runBlock_cat]
  exact ⟨q2, c2, z2⟩

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddShippedProof
