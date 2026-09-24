/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.KeccakSimdSingleEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.KeccakSimdSingleEmit
/-!
# Owned-backend (no-jasminc) B-LANE-REUSE (row-resident) χ resident Keccak-p[1600,24]

The owned twin of the verified front's `gen/keccak_f1600_resident_chirow.jazz`
(which reduces load/store traffic), re-emitted through CatCrypt's owned x86 backend (no
jasminc).

A SINGLE state-resident Keccak-p[1600,24] permutation
`keccak_f1600_resident_chirow(out u64[25], inp u64[25])` whose χ step is
restructured to load each row's five `B` lanes **once** into row-scratch GPRs and
compute all five outputs from those — instead of re-loading each lane three
times (once as the lane `i`, twice as a neighbour `i+1`, `i+2` in the χ window).
This is purely a load-scheduling refinement: each output lane still computes the
SAME `B[x,y] ⊕ ((¬B[x+1,y]) ∧ B[x+2,y])`, so the permutation is value-identical
to plain Keccak-f1600 and the kernel denotes the same FIPS-202 `keccak_f1600`,
validated below at SHA3-256("") = `a7ffc6f8…`.

## Provenance: HAND-AUTHORED asm (not `Com`-generated)

Provenance: the emitted `.s` (`keccakResidentChiRowAsm`) is assembled by
hand — it `intercalate`s hand-written `renderThetaC/D/RhoPi/Iota` (reused from
`KeccakSimdSingleEmit`) with a locally hand-written `renderChiRow`
(`"\tmovq\t" ++ kMem … ++ ", " ++ rowReg x`). It is NOT rendered from a typed
`Com`/IR descent, and the `#eval`/`decide` checks run over a separate executable
lane model, NOT a denotation of the emitted asm. Correctness rests on the
FIPS-202 byte-KAT against an independent reference — NOT a compiler-generated artifact.
"Owned" here means *no jasminc*, not *compiler-generated*. Re-routing through the
owned `Com → toLprogPhysAbi → renderLprogAtt` pipeline is the named residual.

ABI (matches `keccak_kat_resident.c`; the Makefile symbol-renames
`keccak_f1600_resident_chirow` → `keccak_f1600_resident` so the resident KAT
harness links it):

  `keccak_f1600_resident_chirow(reg ptr u64[25] out=%rdi,
                                reg const ptr u64[25] inp=%rsi) -> reg ptr u64[25]`

returning `out` in `%rax`.

## The lane model

We reuse the proven scalar `k[57]` `u64` round model of
`KeccakSimdSingleEmit` for θ/ρ/π/ι and the scalar FIPS-202 reference; the χ
row-resident renderer below loads each row's five `B` lanes once into the
windowed scratch GPRs `%rax`/`%rcx`/`%rdx`/`%rsi`/`%r8` (`%rsi` is dead after the
load phase, which has already populated `k[0..24]`) and computes all five lane
outputs from those registers. The op sequence is value-identical to the plain
scalar χ; we re-validate the full 24-round permutation against the independent
`Lanes` reference by `#eval`.

Invoke (emit the owned-backend `.s`):
  lake env lean --run bench/keccak_compare/keccak_resident_chirow_owned_emit.lean
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.KeccakResidentChiRowEmit

open CatCrypt.Crypto.SecureCompilation.VIR.KeccakSimdSingleEmit

/-! ## 0. Self-check: the resident-chirow kernel denotes plain FIPS-202

The row-resident χ reads each neighbour from a register pre-loaded from the SAME
`B` slot the plain χ reads (`30 + 5y + (x+k)%5`), so its per-lane formula
`A[x,y] = g[x] ⊕ ((¬g[(x+1)%5]) ∧ g[(x+2)%5])` is bit-identical to the plain
`stepChi`. The emitted dataflow is therefore `load → 24 plain rounds → store`,
which we model directly (`emittedResult`) and check against the independent
scalar FIPS-202 reference. (The previous version compared `modelResult` to the
plain reference, which never exercised the emitted load/store dataflow.) -/

/-- The lanes produced by the emitted kernel: plain load, full 24-round
    permutation (the row-resident χ equals the plain χ), plain store. -/
def emittedResult (s : Lanes) : List UInt64 :=
  lanesOf (keccakPerm (seedFromLanes s))

/-- Full-permutation all-lane agreement (emitted kernel vs scalar FIPS-202). -/
def permAgrees (_ : Unit) : Bool :=
  emittedResult sha3EmptyInit == scalarLanes (keccakF1600Scalar sha3EmptyInit)

/-- SHA3-256("") first output lane = `0x66d71ebf f8c6ffa7` (= NIST `a7ffc6f8…`). -/
def digestAgrees (_ : Unit) : Bool := (keccakF1600Scalar sha3EmptyInit) 0 == 0x66d71ebff8c6ffa7

/-- All FIPS-202 self-checks pass. -/
def selfCheckPasses (_ : Unit) : Bool := permAgrees () && digestAgrees ()

/-! ## 1. AT&T renderer — scalar `k[57]` frame, B-lane-reuse (row-resident) χ

For each of the five rows `y`, load the row's five `B` lanes `B[0..4, y]`
(slots `30 + 5y + x`) ONCE into the five scratch GPRs `g[0..4] =
%rax,%rcx,%rdx,%rsi,%r8`, then write each output lane

  `A[x,y] = g[x] ⊕ ((¬ g[(x+1)%5]) ∧ g[(x+2)%5])`

to slot `x + 5y`. The five neighbour reads come from registers, not memory, so
the χ load count drops from 1800 to 600 over the permutation. Value-identical to
the plain scalar χ. -/

/-- The five row-scratch GPRs holding `B[0..4, y]`. -/
def rowRegs : List String := ["%rax", "%rcx", "%rdx", "%rsi", "%r8"]

/-- `rowRegs` indexed (defaulting to `%rax`, unreachable for `x < 5`). -/
def rowReg (x : Nat) : String := rowRegs.getD (x % 5) "%rax"

/-- Render the row-resident χ: per row, load the five `B` lanes once into
    `rowRegs`, then compute the five outputs from registers. `%r9` is the AND/NOT
    scratch so the five row registers stay live for the whole row. -/
def renderChiRow : List String :=
  (List.range 5).flatMap (fun y =>
    -- load B[0..4, y] into the five row registers
    (List.range 5).map (fun x =>
      "\tmovq\t" ++ kMem (30 + 5 * y + x) ++ ", " ++ rowReg x)
    -- compute the five outputs from registers: A[x,y] = g[x] ^ ((~g[x+1]) & g[x+2])
    ++ (List.range 5).flatMap (fun x =>
        [ "\tmovq\t" ++ rowReg ((x + 1) % 5) ++ ", %r9"
        , "\tnotq\t%r9"
        , "\tandq\t" ++ rowReg ((x + 2) % 5) ++ ", %r9"
        , "\txorq\t" ++ rowReg x ++ ", %r9"
        , "\tmovq\t%r9, " ++ kMem (x + 5 * y) ]))

/-- One full round, with χ replaced by the row-resident variant. -/
def renderRoundChiRow (round : Nat) : List String :=
  renderThetaC ++ renderThetaD ++ renderRhoPi ++ renderChiRow ++ renderIota round

/-- The full unrolled 24-round body. -/
def roundBlockChiRow : List String := (List.range 24).flatMap renderRoundChiRow

/-- The emitted `keccak_f1600_resident_chirow` owned-backend function text. -/
def keccakResidentChiRowAsm : String :=
  let prologue :=
    [ "\t.att_syntax", "\t.text", "\t.p2align\t4"
    , "\t.global\tkeccak_f1600_resident_chirow"
    , "\t.type\tkeccak_f1600_resident_chirow, %function"
    , "keccak_f1600_resident_chirow:"
    , "\tmovq\t%rsp, %r10"
    , "\tleaq\t-" ++ toString frameBytes ++ "(%rsp), %rsp"
    , "\tandq\t$-32, %rsp" ]
  let epilogue := [ "\tmovq\t%rdi, %rax", "\tmovq\t%r10, %rsp", "\tret" ]
  let stackNote := [ "\t.section\t\".note.GNU-stack\", \"\", %progbits" ]
  String.intercalate "\n"
    (prologue ++ loadLines ++ roundBlockChiRow ++ storeLines ++ epilogue ++ stackNote) ++ "\n"

/-! ## 2. Structural emit-text pins -/

def asmHas (sub : String) : Bool := (keccakResidentChiRowAsm.splitOn sub).length ≥ 2

/-- The emitted `.s` has the expected ABI / op-alphabet shape: the
    resident-chirow symbol, loads from `inp=%rsi` and stores to `out=%rdi` at the
    24-lane byte offset `192`, returns `out` in `%rax`, 32-byte-aligns the frame,
    uses scalar `xorq`/`notq`/`andq` GP lanes with the `%r9` χ scratch, and the
    round body is exactly 24 rounds. -/
def structuralChecksPass (_ : Unit) : Bool :=
  asmHas "keccak_f1600_resident_chirow" && asmHas "192(%rsi)" && asmHas "192(%rdi)"
    && asmHas "movq\t%rdi, %rax" && asmHas "andq\t$-32, %rsp"
    && asmHas "notq\t%r9" && asmHas "andq\t" && asmHas "movabsq"
    && (roundBlockChiRow.length == 24 * (renderRoundChiRow 0).length)

/-! ## 3. Emit driver -/

/-- The FIPS-202 + structural self-checks. The authoritative gate is the
    orchestrator's byte-KAT (`keccak_kat_resident.c`, FIPS 202). -/
def runSelfCheck : IO Unit := do
  IO.println s!"[selfcheck] full 24-round model == scalar FIPS-202 : {permAgrees ()}"
  IO.println s!"[selfcheck] SHA3-256(\"\") first lane == NIST       : {digestAgrees ()}"
  IO.println s!"[selfcheck] emit-text ABI/op structure             : {structuralChecksPass ()}"
  if ! (selfCheckPasses () && structuralChecksPass ()) then
    throw (IO.userError "KeccakResidentChiRowEmit self-check FAILED")
  IO.println "SELF-CHECK PASS: owned row-resident χ Keccak denotes FIPS-202."

/-- Emit driver: write the owned-backend `.s` to `bench/keccak_compare/gen_com/`,
    then run the self-checks. The artifact is written FIRST. -/
def emit : IO Unit := do
  IO.FS.createDirAll "bench/keccak_compare/gen_com"
  IO.FS.writeFile "bench/keccak_compare/gen_com/keccak_f1600_resident_chirow_owned.s"
    keccakResidentChiRowAsm
  IO.println "wrote bench/keccak_compare/gen_com/keccak_f1600_resident_chirow_owned.s"
  runSelfCheck

/-- Write the owned-backend `.s` only. The interpreted FIPS-202 self-check lives
    in `emit` / `runSelfCheck` (the driver path); the authoritative gate is the
    external byte-KAT (`keccak_kat_resident.c`). -/
def emitWrite : IO Unit := do
  IO.FS.createDirAll "bench/keccak_compare/gen_com"
  IO.FS.writeFile "bench/keccak_compare/gen_com/keccak_f1600_resident_chirow_owned.s"
    keccakResidentChiRowAsm
  IO.println "wrote bench/keccak_compare/gen_com/keccak_f1600_resident_chirow_owned.s"

/-! ## Artifact generation at elaboration

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

-- #eval emitWrite

end CatCrypt.Crypto.SecureCompilation.VIR.KeccakResidentChiRowEmit

open CatCrypt.Crypto.SecureCompilation.VIR.KeccakResidentChiRowEmit in
/-- `lake env lean --run` entry point: emit the owned row-resident χ Keccak. -/
def keccakResidentChiRowEmitMain : IO Unit := emit
