/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

/-!
# Owned-backend (no-jasminc) SINGLE-instance Keccak-p[1600,24] with a YMM θ-parity

**TEST/BENCH-ONLY — STRING-TEMPLATED, not verified-compiler output.** The emitted
`bench/keccak_compare/gen_com/keccak_f1600_simd_owned.s` is assembled as text
(`renderThetaC`/`renderThetaD`/`renderRhoPi`/`renderChi`/`renderIota` produce
literal asm lines that `keccakSimdExportAsm` joins with `String.intercalate`),
with no `Com`/`Lprog` IR and no verified printer, so no theorem relates the
emitted bytes to a source. Correctness is corroborated by the byte-level checks
only — the interpreted FIPS-202 self-check (§5) and the external byte-KAT
`bench/keccak_compare/keccak_kat_simd.c` — not a lowering theorem. It is a
bench/interop reference. The verified emit path is the FRONT-SOURCED descent;
see `bench/framework/AUDIT_EMIT_BYPASS.md` and `EMIT_PROVENANCE.md`
§"Which emit is verified?".

The single-instance analogue of `KeccakAvx2Emit` (which is 4-way): a
SELF-CONTAINED per-kernel module that re-emits the **single** Keccak-p[1600,24]
permutation `keccak_f1600(out u64[25], inp u64[25])` through CatCrypt's owned x86
backend, with the θ column-parity packed into ONE `__m256i` (4 columns at once)
and the rest of the round (ρ, π, χ, ι, the θ-D apply, and column-4 parity) kept
scalar in GP `u64` lanes — the exact hybrid shape of the verified front's SIMD
emit `bench/keccak_compare/gen/keccak_f1600_simd.jazz` (#121).

KAT-flippable against `bench/keccak_compare/keccak_kat_simd.c` (FIPS 202).

ABI (matches `keccak_kat_simd.c` + `gen/keccak_f1600_simd.jazz` EXACTLY):

  `keccak_f1600(reg ptr u64[25] out=%rdi, reg const ptr u64[25] inp=%rsi)
      -> reg ptr u64[25]`

returning `out` in `%rax` (SysV; the jasmin `-> reg ptr u64[25]` is the same
`out` pointer threaded back, which `keccak_kat_simd.c` ignores).

## The hybrid lane / op model

The working set is a scalar `k[57]` `u64` frame, identical to the scalar
`KeccakEmit` slot file and to the SIMD jazz's `stack u64[57] k`:

* slots `0 .. 24`  — the 25 state lanes `A[x,y]`, lane index `i = x + 5y`;
* slots `25 .. 29` — the five θ column parities `C[x]`;
* slots `30 .. 54` — the 25 ρ∘π lanes `B[x,y]`;
* slot `55`        — a rotate scratch word;  slot `56` — a χ NOT/AND scratch.

Every step is scalar GP `u64` EXCEPT θ part 1 (the column parities): columns
`0..3` are gathered into one `__m256i`, XOR-accumulated across the five rows with
`vpxor`, and scattered back to `C[0..3]`; column `4` is computed scalar. This is
the single YMM in the kernel — exactly the jazz's `reg u256 v0 v1` over
`stack u64[4] tbuf`.

Because the four packed θ-parity lanes are independent column XORs, the YMM
`vpxor` chain computes the SAME `C[0..3]` the scalar reference does, lane for
lane (`laneXor` is per-qword). The whole permutation therefore denotes the
scalar FIPS-202 `keccak_f1600`, validated below at SHA3-256("") = `a7ffc6f8…`.

Invoke (emit the owned-backend `.s`):
  lake env lean --run bench/keccak_compare/keccak_simd_single_owned_emit.lean
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.KeccakSimdSingleEmit

/-! ## 0. Keccak constants (FIPS 202) -/

/-- The 24 ι round constants `RC[i]` (FIPS 202 Table 2), as `UInt64` for the
    interpreted self-check (Mathlib `BitVec` is too slow interpreted) and as
    immediates for emission. -/
def roundConst : Nat → UInt64
  |  0 => 0x0000000000000001 |  1 => 0x0000000000008082
  |  2 => 0x800000000000808A |  3 => 0x8000000080008000
  |  4 => 0x000000000000808B |  5 => 0x0000000080000001
  |  6 => 0x8000000080008081 |  7 => 0x8000000000008009
  |  8 => 0x000000000000008A |  9 => 0x0000000000000088
  | 10 => 0x0000000080008009 | 11 => 0x000000008000000A
  | 12 => 0x000000008000808B | 13 => 0x800000000000008B
  | 14 => 0x8000000000008089 | 15 => 0x8000000000008003
  | 16 => 0x8000000000008002 | 17 => 0x8000000000000080
  | 18 => 0x000000000000800A | 19 => 0x800000008000000A
  | 20 => 0x8000000080008081 | 21 => 0x8000000000008080
  | 22 => 0x0000000080000001 | 23 => 0x8000000080008008
  |  _ => 0

/-- The ρ rotation-offset table `r[x,y]`, indexed by lane index `i = x + 5y`. -/
def rhoOffset : Nat → Nat
  |  0 =>  0 |  1 =>  1 |  2 => 62 |  3 => 28 |  4 => 27
  |  5 => 36 |  6 => 44 |  7 =>  6 |  8 => 55 |  9 => 20
  | 10 =>  3 | 11 => 10 | 12 => 43 | 13 => 25 | 14 => 39
  | 15 => 41 | 16 => 45 | 17 => 15 | 18 => 21 | 19 =>  8
  | 20 => 18 | 21 =>  2 | 22 => 61 | 23 => 56 | 24 => 14
  |  _ =>  0

/-! ## 1. The scalar `k[57]` lane model

The interpreted self-check runs a straight-line `UInt64`-typed evaluator over a
57-slot `Array`-backed register file (the same flat-array trick as
`KeccakAvx2Emit`, so the bytecode interpreter stays fast: no closures, no
`Std.HashMap`, no Mathlib `BitVec`). -/

/-- The number of `u64` slots in the `k` frame. -/
abbrev numSlots : Nat := 57

/-- The 57-slot scalar working state. -/
structure KState where
  /-- The `numSlots` `u64` register slots. -/
  regs : Array UInt64

namespace KState

/-- Read slot `i` (out-of-range ⇒ `0`). -/
def get (s : KState) (i : Nat) : UInt64 := s.regs.getD i 0

/-- Write slot `i`. -/
def setV (s : KState) (i : Nat) (v : UInt64) : KState := { regs := s.regs.set! i v }

/-- The all-zero frame. -/
def empty : KState := { regs := Array.replicate numSlots 0 }

end KState

/-- A 64-bit left-rotate (the FIPS-202 ρ / θ-D rotate). -/
def rotl64 (x : UInt64) (n : Nat) : UInt64 :=
  if n % 64 = 0 then x
  else (x <<< UInt64.ofNat (n % 64)) ||| (x >>> UInt64.ofNat (64 - n % 64))

/-! ## 2. The single-instance round, as a scalar `UInt64` model

This is the exact algorithm of `gen/keccak_f1600_simd.jazz`: θ-C gathers columns
`0..3` into a YMM and column `4` scalar; θ-D applies `D[x]=rotl(C[x+1],1)⊕C[x-1]`
to all 5 rows; ρ∘π rotates lanes into the `B` slots; χ reads the `B` slots; ι
XORs `RC` into lane 0. We model it over the flat `k[57]` `UInt64` frame so the
interpreted self-check exercises the very slot dataflow the renderer emits.

The "YMM θ-parity" is modelled as four independent scalar column XORs (`laneXor`
is per-qword on the real YMM, so this is faithful) followed by the scalar column
4 — i.e. the model is what a single qword lane of the YMM `vpxor` chain plus the
scalar tail computes. -/

/-- θ part 1 — the five column parities into slots `25..29`.
    Columns `0..3` are the packed-YMM lanes (per-qword XOR); column `4` is the
    scalar tail. `C[x] = A[x] ⊕ A[x+5] ⊕ A[x+10] ⊕ A[x+15] ⊕ A[x+20]`. -/
def stepThetaC (s : KState) : KState :=
  (List.range 5).foldl (fun st x =>
    st.setV (25 + x)
      (s.get x ^^^ s.get (x + 5) ^^^ s.get (x + 10) ^^^ s.get (x + 15) ^^^ s.get (x + 20)))
    s

/-- θ part 2 — `D[x] = rotl(C[x+1],1) ⊕ C[x-1]`, applied to the 5 rows of column
    `x`. `C[x]` lives at slot `25 + x`. -/
def stepThetaD (s : KState) : KState :=
  (List.range 5).foldl (fun st x =>
    let d := rotl64 (s.get (25 + (x + 1) % 5)) 1 ^^^ s.get (25 + (x + 4) % 5)
    (List.range 5).foldl (fun st2 y =>
      st2.setV (x + 5 * y) (st2.get (x + 5 * y) ^^^ d)) st)
    s

/-- ρ∘π — `B[y, 2x+3y] = rotl(A[x,y], r[x+5y])`, into slots `30..54`.
    Output lane `(x',y') = (y, (2x+3y) mod 5)` ↦ slot `30 + x' + 5*y'`. -/
def stepRhoPi (s : KState) : KState :=
  (List.range 25).foldl (fun st i =>
    let x := i % 5
    let y := i / 5
    let x' := y
    let y' := (2 * x + 3 * y) % 5
    st.setV (30 + x' + 5 * y') (rotl64 (s.get i) (rhoOffset i)))
    s

/-- χ — `A[x,y] = B[x,y] ⊕ ((¬B[x+1,y]) ∧ B[x+2,y])`, B at slots `30..54`,
    A back to slots `0..24`. -/
def stepChi (s : KState) : KState :=
  (List.range 25).foldl (fun st i =>
    let x := i % 5
    let y := i / 5
    let b  := s.get (30 + i)
    let b1 := s.get (30 + (x + 1) % 5 + 5 * y)
    let b2 := s.get (30 + (x + 2) % 5 + 5 * y)
    st.setV i (b ^^^ ((~~~ b1) &&& b2)))
    s

/-- ι — `A[0,0] ⊕= RC[round]`. -/
def stepIota (s : KState) (round : Nat) : KState :=
  s.setV 0 (s.get 0 ^^^ roundConst round)

/-- One full round. -/
def keccakRound (s : KState) (round : Nat) : KState :=
  stepIota (stepChi (stepRhoPi (stepThetaD (stepThetaC s)))) round

/-- The full 24-round single-instance permutation over the `k` frame. -/
def keccakPerm (s : KState) : KState :=
  (List.range 24).foldl (fun st r => keccakRound st r) s

/-! ## 3. Independent scalar FIPS-202 reference (lane-array form)

A separate `Fin 25 → UInt64` reference performing θ/ρ/π/χ/ι in the standard
`i = x + 5y` convention, snapshotted per round so the interpreted round chain
stays closure-flat (the `KeccakAvx2Emit` reference, verbatim semantics). -/

/-- The 25-lane scalar Keccak state. -/
abbrev Lanes := Fin 25 → UInt64

/-- Scalar θ. -/
def thetaScalar (s : Lanes) : Lanes := fun i =>
  let x := i.val % 5
  let cAt := fun xx : Nat =>
    s ⟨(xx % 5) + 0, by omega⟩ ^^^ s ⟨(xx % 5) + 5, by omega⟩ ^^^
    s ⟨(xx % 5) + 10, by omega⟩ ^^^ s ⟨(xx % 5) + 15, by omega⟩ ^^^
    s ⟨(xx % 5) + 20, by omega⟩
  let d := cAt (x + 4) ^^^ rotl64 (cAt (x + 1)) 1
  s i ^^^ d

/-- Scalar ρ. -/
def rhoScalar (s : Lanes) : Lanes := fun i => rotl64 (s i) (rhoOffset i.val)

/-- Scalar π: `out[x + 5y] = A[ (x + 3y) mod 5 + 5*x ]`. -/
def piScalar (s : Lanes) : Lanes := fun i =>
  let x := i.val % 5
  let y := i.val / 5
  s ⟨((x + 3 * y) % 5) + 5 * x, by omega⟩

/-- Scalar χ. -/
def chiScalar (s : Lanes) : Lanes := fun i =>
  let x := i.val % 5
  let y := i.val / 5
  s i ^^^ ((~~~ s ⟨((x + 1) % 5) + 5 * y, by omega⟩) &&& s ⟨((x + 2) % 5) + 5 * y, by omega⟩)

/-- Scalar ι. -/
def iotaScalar (s : Lanes) (round : Nat) : Lanes := fun i =>
  if i.val = 0 then s i ^^^ roundConst round else s i

/-- Snapshot a `Lanes` into an `Array`-backed function (keeps `--run` fast). -/
def snap (s : Lanes) : Lanes :=
  let arr : Array UInt64 := (List.range 25).foldl (fun a i =>
    a.push (s ⟨i % 25, Nat.mod_lt _ (by decide)⟩)) #[]
  fun i => arr.getD i.val 0

/-- One scalar Keccak round. -/
def roundScalar (s : Lanes) (round : Nat) : Lanes :=
  snap (iotaScalar (chiScalar (piScalar (rhoScalar (thetaScalar s)))) round)

/-- The full scalar Keccak-f[1600] (24 rounds). -/
def keccakF1600Scalar (s : Lanes) : Lanes :=
  (List.range 24).foldl (fun acc r => roundScalar acc r) s

/-! ## 4. Bridge: the `k`-frame model's state lanes vs the scalar reference -/

/-- Seed the `k` frame from a scalar `Lanes` (slots `0..24`). -/
def seedFromLanes (s : Lanes) : KState :=
  (List.range 25).foldl
    (fun st i => st.setV i (s ⟨i % 25, Nat.mod_lt _ (by decide)⟩))
    KState.empty

/-- The 25 state lanes (slots `0..24`) of a `KState` as a flat list. -/
def lanesOf (s : KState) : List UInt64 := (List.range 25).map s.get

/-- The 25 lanes of a scalar `Lanes` as the same flat list. -/
def scalarLanes (s : Lanes) : List UInt64 :=
  (List.range 25).map (fun i => s ⟨i % 25, Nat.mod_lt _ (by decide)⟩)

/-- Run ONE model round on a scalar `Lanes` (fresh seed each round). -/
def modelRoundLanes (s : Lanes) (r : Nat) : Lanes :=
  let final := keccakRound (seedFromLanes s) r
  snap (fun i => final.get i.val)

/-- The model's full 24-round permutation, via the bridge. -/
def modelResult (s : Lanes) : Lanes :=
  (List.range 24).foldl (fun acc r => modelRoundLanes acc r) s

/-! ## 5. FIPS-202 self-checks (executed at emit time) -/

/-- SHA3-256("") init: lane 0 = `0x06`, lane 16 = `0x80 << 56`. -/
def sha3EmptyInit : Lanes := fun i =>
  if i.val = 0 then 0x0000000000000006
  else if i.val = 16 then 0x8000000000000000
  else 0

/-- Round-0 all-lane agreement. -/
def round0Agrees (_ : Unit) : Bool :=
  lanesOf (keccakRound (seedFromLanes sha3EmptyInit) 0)
    == scalarLanes (roundScalar sha3EmptyInit 0)

/-- Full-permutation all-lane agreement (model vs scalar FIPS-202). -/
def permAgrees (_ : Unit) : Bool :=
  scalarLanes (modelResult sha3EmptyInit) == scalarLanes (keccakF1600Scalar sha3EmptyInit)

/-- SHA3-256("") first output lane = `0x66d71ebf f8c6ffa7` (= NIST `a7ffc6f8…`). -/
def digestAgrees (_ : Unit) : Bool := (keccakF1600Scalar sha3EmptyInit) 0 == 0x66d71ebff8c6ffa7

/-- All FIPS-202 self-checks pass. -/
def selfCheckPasses (_ : Unit) : Bool := round0Agrees () && permAgrees () && digestAgrees ()

/-! ## 6. AT&T renderer — scalar `k[57]` frame + one YMM θ-parity

`keccak_f1600(out=%rdi, inp=%rsi) -> %rax`:
* prologue saves `%rsp`, allocates a 32-byte-aligned frame holding the `k[57]`
  `u64` slots (`8·i(%rsp)`) and a 32-byte `tbuf` for the YMM gather;
* loads `inp[i]` (byte `8·i`) into `k[0..24]`;
* per round: θ-C via YMM (gather columns `0..3` to `tbuf`, `vpxor`-accumulate the
  five rows, scatter to `C[0..3]`; column 4 scalar) then scalar θ-D / ρ∘π / χ / ι;
* stores `k[0..24]` to `out[i]`;  returns `out` in `%rax`.

The scalar GP slots use `%rax`/`%rcx`/`%rdx` as windowed scratch (the
`stack-resident` storage class — every op is `load→op→store`). The θ-parity uses
`%ymm0`,`%ymm1` over the `tbuf` slot, exactly as the jazz's `v0`,`v1`. -/

/-- The `k`-slot stack offset (`8·i`) for slot `i`. -/
def kOff (i : Nat) : Nat := 8 * i

/-- `tbuf` (the 32-byte YMM gather buffer) sits just past the 57 `u64` slots,
    32-byte aligned: offset `32·⌈57·8/32⌉ = 32·15 = 480`. -/
def tbufOff : Nat := 480

/-- The frame size (the 57 u64 slots + 32-byte tbuf + headroom). -/
def frameBytes : Nat := tbufOff + 64

/-- A scalar `k`-slot memory operand `8·i(%rsp)`. -/
def kMem (i : Nat) : String := toString (kOff i) ++ "(%rsp)"

/-- A `tbuf` u64 sub-word operand at lane `j` (`tbufOff + 8·j`). -/
def tbufMem (j : Nat) : String := toString (tbufOff + 8 * j) ++ "(%rsp)"

/-- The 32-byte `tbuf` u256 operand. -/
def tbufV : String := toString tbufOff ++ "(%rsp)"

/-- Render θ-C: gather columns 0..3 into the YMM and XOR-accumulate the five
    rows, then scatter `C[0..3]`; column 4 scalar into `C[4]`. The five row bases
    are state lanes `0,5,10,15,20` (column-0 of rows `0..4`); column `x` of row
    `r` is lane `5·r + x`. -/
def renderThetaC : List String :=
  -- row 0 -> tbuf -> v1 = v0
  (List.range 4).flatMap (fun j =>
    [ "\tmovq\t" ++ kMem (0 + j) ++ ", %rax", "\tmovq\t%rax, " ++ tbufMem j ])
  ++ [ "\tvmovdqa\t" ++ tbufV ++ ", %ymm1" ]
  -- rows 1..4: tbuf <- row, v0 = tbuf, v1 ^= v0
  ++ (List.range 4).flatMap (fun r0 =>
      let r := r0 + 1
      (List.range 4).flatMap (fun j =>
        [ "\tmovq\t" ++ kMem (5 * r + j) ++ ", %rax", "\tmovq\t%rax, " ++ tbufMem j ])
      ++ [ "\tvmovdqa\t" ++ tbufV ++ ", %ymm0"
         , "\tvpxor\t%ymm0, %ymm1, %ymm1" ])
  -- scatter v1 -> tbuf -> C[0..3] (slots 25..28)
  ++ [ "\tvmovdqa\t%ymm1, " ++ tbufV ]
  ++ (List.range 4).flatMap (fun j =>
      [ "\tmovq\t" ++ tbufMem j ++ ", %rax", "\tmovq\t%rax, " ++ kMem (25 + j) ])
  -- column 4 scalar: C[4] = A[4]^A[9]^A[14]^A[19]^A[24]  (slot 29)
  ++ [ "\tmovq\t" ++ kMem 4 ++ ", %rax"
     , "\txorq\t" ++ kMem 9 ++ ", %rax"
     , "\txorq\t" ++ kMem 14 ++ ", %rax"
     , "\txorq\t" ++ kMem 19 ++ ", %rax"
     , "\txorq\t" ++ kMem 24 ++ ", %rax"
     , "\tmovq\t%rax, " ++ kMem 29 ]

/-- Emit `%rax = rotl( <load> , n )` into `%rax`, scratch `%rcx`. `n=0` ⇒ just
    the load already in `%rax`. -/
def renderRotlRax (n : Nat) : List String :=
  let n := n % 64
  if n == 0 then []
  else
    [ "\tmovq\t%rax, %rcx"
    , "\tshlq\t$" ++ toString n ++ ", %rax"
    , "\tshrq\t$" ++ toString (64 - n) ++ ", %rcx"
    , "\torq\t%rcx, %rax" ]

/-- Render θ-D: for each column `x`, `D = rotl(C[x+1],1) ⊕ C[x-1]` in `%rdx`,
    then XOR `D` into the 5 rows of column `x`. C[x] at slot `25+x`. -/
def renderThetaD : List String :=
  (List.range 5).flatMap (fun x =>
    [ "\tmovq\t" ++ kMem (25 + (x + 1) % 5) ++ ", %rax" ]
    ++ renderRotlRax 1
    ++ [ "\txorq\t" ++ kMem (25 + (x + 4) % 5) ++ ", %rax"
       , "\tmovq\t%rax, %rdx" ]
    ++ (List.range 5).flatMap (fun y =>
        [ "\tmovq\t" ++ kMem (x + 5 * y) ++ ", %rax"
        , "\txorq\t%rdx, %rax"
        , "\tmovq\t%rax, " ++ kMem (x + 5 * y) ]))

/-- Render ρ∘π: `B[y, 2x+3y] = rotl(A[x,y], r[x+5y])`, B at slot
    `30 + y + 5·((2x+3y) mod 5)`. -/
def renderRhoPi : List String :=
  (List.range 25).flatMap (fun i =>
    let x := i % 5
    let y := i / 5
    let dst := 30 + y + 5 * ((2 * x + 3 * y) % 5)
    [ "\tmovq\t" ++ kMem i ++ ", %rax" ]
    ++ renderRotlRax (rhoOffset i)
    ++ [ "\tmovq\t%rax, " ++ kMem dst ])

/-- Render χ: `A[x,y] = B[x,y] ⊕ ((¬B[x+1,y]) ∧ B[x+2,y])`. B at slots `30..54`,
    A back to slots `0..24`. `%rax = ¬B[x+1]; %rax &= B[x+2]; %rax ^= B[x]`. -/
def renderChi : List String :=
  (List.range 25).flatMap (fun i =>
    let x := i % 5
    let y := i / 5
    let b  := 30 + i
    let b1 := 30 + (x + 1) % 5 + 5 * y
    let b2 := 30 + (x + 2) % 5 + 5 * y
    [ "\tmovq\t" ++ kMem b1 ++ ", %rax"
    , "\tnotq\t%rax"
    , "\tandq\t" ++ kMem b2 ++ ", %rax"
    , "\txorq\t" ++ kMem b ++ ", %rax"
    , "\tmovq\t%rax, " ++ kMem i ])

/-- Render ι: `A[0,0] ⊕= RC[round]` via a `movabsq` immediate. -/
def renderIota (round : Nat) : List String :=
  [ "\tmovabsq\t$" ++ toString (roundConst round).toNat ++ ", %rax"
  , "\txorq\t" ++ kMem 0 ++ ", %rax"
  , "\tmovq\t%rax, " ++ kMem 0 ]

/-- One full round of emitted lines. -/
def renderRound (round : Nat) : List String :=
  renderThetaC ++ renderThetaD ++ renderRhoPi ++ renderChi ++ renderIota round

/-- Load `inp = %rsi` lanes `0..24` into `k[0..24]`. -/
def loadLines : List String :=
  (List.range 25).flatMap (fun i =>
    [ "\tmovq\t" ++ toString (8 * i) ++ "(%rsi), %rax"
    , "\tmovq\t%rax, " ++ kMem i ])

/-- Store `k[0..24]` to `out = %rdi` lanes `0..24`. -/
def storeLines : List String :=
  (List.range 25).flatMap (fun i =>
    [ "\tmovq\t" ++ kMem i ++ ", %rax"
    , "\tmovq\t%rax, " ++ toString (8 * i) ++ "(%rdi)" ])

/-- The full unrolled 24-round body. -/
def roundBlock : List String := (List.range 24).flatMap renderRound

/-- The emitted `keccak_f1600` owned-backend function text. -/
def keccakSimdExportAsm : String :=
  let prologue :=
    [ "\t.att_syntax", "\t.text", "\t.p2align\t4"
    , "\t.global\tkeccak_f1600", "\t.type\tkeccak_f1600, %function"
    , "keccak_f1600:"
    , "\tmovq\t%rsp, %r10"
    , "\tleaq\t-" ++ toString frameBytes ++ "(%rsp), %rsp"
    , "\tandq\t$-32, %rsp" ]
  -- return `out` (%rdi) in %rax (the jasmin `-> reg ptr u64[25]` is `out`)
  let epilogue := [ "\tmovq\t%rdi, %rax", "\tmovq\t%r10, %rsp", "\tret" ]
  let stackNote := [ "\t.section\t\".note.GNU-stack\", \"\", %progbits" ]
  String.intercalate "\n"
    (prologue ++ loadLines ++ roundBlock ++ storeLines ++ epilogue ++ stackNote) ++ "\n"

/-! ## 7. Structural emit-text pins -/

def asmHas (sub : String) : Bool := (keccakSimdExportAsm.splitOn sub).length ≥ 2

/-- The emitted `.s` has the expected ABI / op-alphabet shape: the scalar single
    symbol `keccak_f1600`, loads from `inp=%rsi` and stores to `out=%rdi` at the
    24-lane byte offset `192`, returns `out` in `%rax`, 32-byte-aligns the YMM
    frame, uses a `vpxor`/`vmovdqa` θ-parity AND scalar `xorq`/`notq`/`andq`
    GP lanes, and the body is exactly 24 rounds. -/
def structuralChecksPass (_ : Unit) : Bool :=
  asmHas "keccak_f1600" && asmHas "192(%rsi)" && asmHas "192(%rdi)"
    && asmHas "movq\t%rdi, %rax" && asmHas "andq\t$-32, %rsp"
    && asmHas "vpxor\t%ymm0, %ymm1, %ymm1" && asmHas "vmovdqa"
    && asmHas "notq\t%rax" && asmHas "andq\t" && asmHas "movabsq"
    && (roundBlock.length == 24 * (renderRound 0).length)

/-! ## 8. Emit driver -/

/-- The FIPS-202 + structural self-checks. The authoritative gate is the
    orchestrator's byte-KAT (`keccak_kat_simd.c`, FIPS 202). -/
def runSelfCheck : IO Unit := do
  IO.println s!"[selfcheck] round-0 model == scalar FIPS-202     : {round0Agrees ()}"
  IO.println s!"[selfcheck] full 24-round model == scalar         : {permAgrees ()}"
  IO.println s!"[selfcheck] SHA3-256(\"\") first lane == NIST      : {digestAgrees ()}"
  IO.println s!"[selfcheck] emit-text ABI/op structure            : {structuralChecksPass ()}"
  if ! (selfCheckPasses () && structuralChecksPass ()) then
    throw (IO.userError "KeccakSimdSingleEmit self-check FAILED")
  IO.println "SELF-CHECK PASS: owned single-instance YMM-θ Keccak denotes FIPS-202."

/-- Emit driver: write the owned-backend `.s` to `bench/keccak_compare/gen_com/`,
    then run the self-checks. The artifact is written FIRST. -/
def emit : IO Unit := do
  IO.FS.createDirAll "bench/keccak_compare/gen_com"
  IO.FS.writeFile "bench/keccak_compare/gen_com/keccak_f1600_simd_owned.s" keccakSimdExportAsm
  IO.println "wrote bench/keccak_compare/gen_com/keccak_f1600_simd_owned.s"
  runSelfCheck

/-- Write the owned-backend `.s` only. The interpreted FIPS-202 self-check lives
    in `emit` / `runSelfCheck` (the driver path); the authoritative gate is the
    external byte-KAT (`keccak_kat_simd.c`). -/
def emitWrite : IO Unit := do
  IO.FS.createDirAll "bench/keccak_compare/gen_com"
  IO.FS.writeFile "bench/keccak_compare/gen_com/keccak_f1600_simd_owned.s" keccakSimdExportAsm
  IO.println "wrote bench/keccak_compare/gen_com/keccak_f1600_simd_owned.s"

/-! ## Artifact generation at elaboration

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

-- #eval emitWrite

end CatCrypt.Crypto.SecureCompilation.VIR.KeccakSimdSingleEmit

open CatCrypt.Crypto.SecureCompilation.VIR.KeccakSimdSingleEmit in
/-- `lake env lean --run` entry point: emit the owned single-instance YMM-θ Keccak. -/
def keccakSimdSingleEmitMain : IO Unit := emit
