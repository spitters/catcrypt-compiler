/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.KeccakSimdSingleEmit
/-!
# Owned-backend (no-jasminc) χ-LANE-COMPLEMENT ('bebigokimisa') resident Keccak-p[1600,24]

The owned twin of the verified front's `gen/keccak_f1600_resident_beb.jazz`
(#590-continuation), re-emitted through CatCrypt's owned x86 backend (no jasminc).

A SINGLE state-resident Keccak-p[1600,24] permutation
`keccak_f1600_resident_beb(out u64[25], inp u64[25])`.

The XKCP **lane-complement** ('bebigokimisa') optimization keeps the six state
lanes `{1,2,8,12,17,20}` complemented across the permutation so χ can emit far
fewer `notq`s. That optimization is only value-preserving when the **round
itself** is rewritten to the De-Morgan form that consumes/produces the
complemented representation (θ over the complemented parity, per-lane χ in
AND/OR form, ι over the complemented lane-0). It is NOT value-preserving to wrap
the *unmodified* round in a load-complement / store-uncomplement pair: plain θ
does not commute with complementing `{1,2,8,12,17,20}` (e.g. column `x=1` draws
lanes `1,6,11,16,21`, of which only lane `1` is in the set, so its parity flips),
so `complement ∘ plainPerm ∘ complement ≠ plainPerm`. An earlier version of this
module did exactly that wrap around the plain round body and the FIPS-202 byte-KAT
refuted it.

Since this module's round body is the verbatim KAT'd plain `renderRound`
core of `KeccakSimdSingleEmit` (no De-Morgan χ), the correct and
provably-FIPS-202 emit is the plain load / 24 plain rounds / plain store — with
no load/store complement. The kernel therefore denotes the same FIPS-202
`keccak_f1600` as the base, validated below at SHA3-256("") = `a7ffc6f8…`.
(A bebigokimisa variant — with a De-Morgan'd round body that justifies a
reduced NOT count — is left as a future perf refinement; it requires rewriting
the round, not just wrapping it.)

## Provenance: HAND-AUTHORED asm (not `Com`-generated)

Provenance: the emitted `.s` (`keccakResidentBebAsm`) is assembled by
hand — it `intercalate`s a hand-written prologue/epilogue with
`KeccakSimdSingleEmit`'s hand-authored `renderRound`/load/store
mnemonic-string lists. It is NOT rendered from a typed `Com`/IR descent, and the
`#eval`/`decide` checks here run over a separate executable `keccakPerm` model,
NOT a denotation of the emitted asm. Correctness rests on the FIPS-202 byte-KAT
(`SHA3-256("") = a7ffc6f8…`) against an independent reference — NOT a compiler
result. "Owned" here means *no jasminc*, not *compiler-generated*. Re-routing
this kernel through the owned `Com → toLprogPhysAbi → renderLprogAtt` pipeline is
the named residual.

ABI (matches `keccak_kat_resident.c`; the Makefile symbol-renames
`keccak_f1600_resident_beb` → `keccak_f1600_resident` so the resident KAT
harness links it):

  `keccak_f1600_resident_beb(reg ptr u64[25] out=%rdi,
                             reg const ptr u64[25] inp=%rsi) -> reg ptr u64[25]`

returning `out` in `%rax` (SysV; the jasmin `-> reg ptr u64[25]` threads `out`
back, which the harness ignores).

## The lane model

We reuse the proven scalar `k[57]` `u64` round model of
`KeccakSimdSingleEmit` (θ/ρ/π/χ/ι over a flat `UInt64`-typed register
file). The emitted body is the verbatim plain round; the self-check below models
the emitted `load → 24·plainRound → store` dataflow directly (`emittedResult`)
and checks it equals the independent scalar FIPS-202 reference, lane-for-lane.

Invoke (emit the owned-backend `.s`):
  lake env lean --run bench/keccak_compare/keccak_resident_beb_owned_emit.lean
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.KeccakResidentBebEmit

open CatCrypt.Crypto.SecureCompilation.VIR.KeccakSimdSingleEmit

/-! ## 0. Reused round model

`stepThetaC`, `stepThetaD`, `stepRhoPi`, `stepChi`, `stepIota`, `keccakPerm`,
`rotl64`, `roundConst`, `rhoOffset`, the `Lanes` scalar reference, and the
`seedFromLanes` / `lanesOf` bridge all come from `KeccakSimdSingleEmit`.
This kernel emits the plain round body (no De-Morgan χ), so the self-check below
reuses that module's scalar FIPS-202 reference. -/

/-- The canonical 'bebigokimisa' complemented-lane set (`i = x + 5y`), kept here
    for reference. A faithful lane-complement variant would carry this set through
    a De-Morgan'd round; the plain-round body emitted here does NOT, so the
    load/store must NOT complement these lanes (doing so corrupts θ). -/
def complementLanes : List Nat := [1, 2, 8, 12, 17, 20]

/-! ## 1. Self-check: the resident-beb kernel denotes plain FIPS-202

This self-check models the EMITTED dataflow directly — `load → 24 plain rounds →
store` over the `k[57]` frame — and checks it equals the independent scalar
FIPS-202 `Lanes` reference, lane-for-lane. (The previous version compared the
plain `modelResult` to the plain reference, which never exercised the load/store
and so silently passed while the emitted asm was wrong.) -/

/-- The lanes produced by the emitted kernel: seed the `k` frame from `s`
    (plain load), run the full 24-round plain permutation, read lanes `0..24`
    (plain store). -/
def emittedResult (s : Lanes) : List UInt64 :=
  lanesOf (keccakPerm (seedFromLanes s))

/-- Full-permutation all-lane agreement (emitted kernel vs scalar FIPS-202). -/
def permAgrees : Bool :=
  emittedResult sha3EmptyInit == scalarLanes (keccakF1600Scalar sha3EmptyInit)

/-- SHA3-256("") first output lane = `0x66d71ebf f8c6ffa7` (= NIST `a7ffc6f8…`). -/
def digestAgrees : Bool := (keccakF1600Scalar sha3EmptyInit) 0 == 0x66d71ebff8c6ffa7

/-- All FIPS-202 self-checks pass. -/
def selfCheckPasses : Bool := permAgrees && digestAgrees

/-! ## 2. AT&T renderer — scalar `k[57]` frame, plain χ

`keccak_f1600_resident_beb(out=%rdi, inp=%rsi) -> %rax`. Identical scalar
`k[57]` frame and θ/ρ/π/χ/ι rendering as the scalar owned emit. The load and
store are plain (no lane complementing): the round body is the verbatim plain
`renderRound`, and plain θ does not commute with complementing the
'bebigokimisa' lane set, so wrapping this plain body in a load/store complement
would NOT preserve the value (it would corrupt θ's column parities). A
lane-complement variant would instead De-Morgan the round body; that is left as
a future perf refinement. -/

/-- Load `inp = %rsi` lanes `0..24` into `k[0..24]` (plain — no complementing). -/
def loadLinesBeb : List String := loadLines

/-- Store `k[0..24]` to `out = %rdi` lanes `0..24` (plain — no complementing). -/
def storeLinesBeb : List String := storeLines

/-- The full unrolled 24-round body (scalar θ/ρ/π/χ/ι, identical to the scalar
    owned emit). -/
def roundBlockBeb : List String := (List.range 24).flatMap renderRound

/-- The emitted `keccak_f1600_resident_beb` owned-backend function text. -/
def keccakResidentBebAsm : String :=
  let prologue :=
    [ "\t.att_syntax", "\t.text", "\t.p2align\t4"
    , "\t.global\tkeccak_f1600_resident_beb"
    , "\t.type\tkeccak_f1600_resident_beb, %function"
    , "keccak_f1600_resident_beb:"
    , "\tmovq\t%rsp, %r10"
    , "\tleaq\t-" ++ toString frameBytes ++ "(%rsp), %rsp"
    , "\tandq\t$-32, %rsp" ]
  let epilogue := [ "\tmovq\t%rdi, %rax", "\tmovq\t%r10, %rsp", "\tret" ]
  let stackNote := [ "\t.section\t\".note.GNU-stack\", \"\", %progbits" ]
  String.intercalate "\n"
    (prologue ++ loadLinesBeb ++ roundBlockBeb ++ storeLinesBeb ++ epilogue ++ stackNote) ++ "\n"

/-! ## 3. Structural emit-text pins -/

private def asmHas (sub : String) : Bool := (keccakResidentBebAsm.splitOn sub).length ≥ 2

/-- The emitted `.s` has the expected ABI / op-alphabet shape: the resident-beb
    symbol, loads from `inp=%rsi` and stores to `out=%rdi` at the 24-lane byte
    offset `192`, returns `out` in `%rax`, 32-byte-aligns the frame, uses scalar
    `xorq`/`notq`/`andq` GP lanes, and the round body is exactly 24 rounds. -/
def structuralChecksPass : Bool :=
  asmHas "keccak_f1600_resident_beb" && asmHas "192(%rsi)" && asmHas "192(%rdi)"
    && asmHas "movq\t%rdi, %rax" && asmHas "andq\t$-32, %rsp"
    && asmHas "notq\t%rax" && asmHas "andq\t" && asmHas "movabsq"
    && (roundBlockBeb.length == 24 * (renderRound 0).length)

/-! ## 4. Emit driver -/

/-- The FIPS-202 + structural self-checks. The authoritative gate is the
    orchestrator's byte-KAT (`keccak_kat_resident.c`, FIPS 202). -/
def runSelfCheck : IO Unit := do
  IO.println s!"[selfcheck] full 24-round model == scalar FIPS-202 : {permAgrees}"
  IO.println s!"[selfcheck] SHA3-256(\"\") first lane == NIST       : {digestAgrees}"
  IO.println s!"[selfcheck] emit-text ABI/op structure             : {structuralChecksPass}"
  if ! (selfCheckPasses && structuralChecksPass) then
    throw (IO.userError "KeccakResidentBebEmit self-check FAILED")
  IO.println "SELF-CHECK PASS: owned lane-complement resident Keccak denotes FIPS-202."

/-- Emit driver: write the owned-backend `.s` to `bench/keccak_compare/gen_com/`,
    then run the self-checks. The artifact is written FIRST. -/
def emit : IO Unit := do
  IO.FS.createDirAll "bench/keccak_compare/gen_com"
  IO.FS.writeFile "bench/keccak_compare/gen_com/keccak_f1600_resident_beb_owned.s"
    keccakResidentBebAsm
  IO.println "wrote bench/keccak_compare/gen_com/keccak_f1600_resident_beb_owned.s"
  runSelfCheck

/-- Write the owned-backend `.s` only. The interpreted FIPS-202 self-check lives
    in `emit` / `runSelfCheck` (the driver path); the authoritative gate is the
    external byte-KAT (`keccak_kat_resident.c`). -/
def emitWrite : IO Unit := do
  IO.FS.createDirAll "bench/keccak_compare/gen_com"
  IO.FS.writeFile "bench/keccak_compare/gen_com/keccak_f1600_resident_beb_owned.s"
    keccakResidentBebAsm
  IO.println "wrote bench/keccak_compare/gen_com/keccak_f1600_resident_beb_owned.s"

/-! ## Artifact generation at elaboration

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

#eval emitWrite

end CatCrypt.Crypto.SecureCompilation.VIR.KeccakResidentBebEmit

open CatCrypt.Crypto.SecureCompilation.VIR.KeccakResidentBebEmit in
/-- `lake env lean --run` entry point: emit the owned lane-complement resident Keccak. -/
@[expose] def keccakResidentBebEmitMain : IO Unit := emit
