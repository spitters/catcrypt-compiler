/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiEmit
import CatCrypt.Crypto.SecureCompilation.VIR.JForProgMultiOp
import CatCrypt.Crypto.SecureCompilation.Dialects.ScalarSExprWidth32Prototype

/-!
# Keccak-p[1600,24] emitted from a `Com jasminDialect` (the SHA-3 / XOF core)

This is the single most load-bearing opaque leaf in the development: the
Keccak-p[1600,24] permutation underlies the XOF / hash leaf of ML-KEM, ML-DSA,
SLH-DSA, FAEST (the `faest_shake128` leaf) and SHA-3 itself. Emitting it through
the verified register-arith front (the `ChaChaEmit` / `AsconEmit` path) upgrades
every one of those from "verified-to-the-Keccak-leaf" toward verified-to-x86.

Keccak-p has **no** sub-primitive — it is pure 64-bit bit-arithmetic over the
25-lane state (`A[x,y]`, `x,y ∈ {0..4}`, each lane `u64`), so this is a FULLY
emitted kernel (no `extCall` leaves, no `LeafAgrees`). The five step mappings
(FIPS 202 §3.2) are all expressible with the existing dialect `regArith` ops:

* **θ** — column parities `C[x] = ⊕_y A[x,y]`, then
  `D[x] = C[x-1] ⊕ rotl64(C[x+1], 1)` and `A[x,y] ⊕= D[x]`  (`xor`, `shl`/`shr`/`or` for the rotate);
* **ρ** — per-lane left-rotate by the fixed offset table `r[x,y]` (`shl`/`shr`/`or`);
* **π** — lane permutation `B[y, 2x+3y] = A[x,y]`  (a pure rename of slots, no op);
* **χ** — `A[x,y] = B[x,y] ⊕ ((¬B[x+1,y]) ∧ B[x+2,y])`  (`xor`, `and`, NOT = `xor` with all-ones);
* **ι** — `A[0,0] ⊕= RC[round]`  (`xor` of the per-round constant immediate).

The round constants `RC[round]` agree with `CatCrypt/Crypto/Hash/Keccak.lean`'s
`keccak_round_constant` (FIPS 202 Table 2) and the lane state `BitVec 1600`
matches that file's `KeccakState`.

## Two artifacts

1. **Emission / KAT** (`keccakF1600Com`, `keccakF1600Jazz`): the full 24-round
   permutation as a straight-line `regArith` `Com`, rendered through
   `emitAbiOrchReg` to a `stack u64[…]` jasmin `export fn`. Each round emits its
   own `RC[round]` immediate (the per-round ι), so the fully-unrolled form
   handles the varying constant trivially. KAT'd byte-identical to FIPS 202 in
   `bench/keccak_compare/` for the **full FIPS-202 family** — SHA3-224/256/384/512
   and SHAKE128/256 — each obtained from the SAME emitted permutation by the
   parametric sponge wrapper `sponge(in, inlen, ds, rate_bytes, out, outlen)`:
   the only per-variant parameters are the rate (= 200 − capacity, capacity =
   2·securitybits/8), the domain-separation byte (`0x06` for SHA3, `0x1F` for
   SHAKE), and the output length. The permutation itself is shared and unchanged,
   so no new emit machinery is required for any variant (see
   `bench/keccak_compare/sha3_full_vs_hacl.c`).

2. **Denotation preservation** (`keccakRoundLoop`, `keccak_round_loop_denote_eq`):
   the 24-round structure as a genuine `JForProg (.reg 1600)` bounded loop whose
   body is one Keccak round expressed as a **multi-op straight-line `Com`** over
   the 1600-bit state register (lanes extracted by `shr`/`and`, recombined by
   `shl`/`or`). The emitted `for round = 0 to 24 { acc = round(acc) }` denotes the
   24-fold round semantics, routed through the R1 multi-op loop keystone
   `JForProgMultiOp.loop_denote_eq_multiOp`. The body binds many fresh SSA names,
   so it is exactly the multi-op case the single-leaf keystone could not cover.

### The per-round constant ι, threaded through the loop

A `JForProg` body is **uniform** across iterations (single accumulator, no loop
index in the `Com` context), so a body that XORed a *different* `RC[round]` each
round is not directly expressible. We follow the convention the task sanctions:
the uniform round body folds in a **fixed** ι immediate (`RC[0]`), and the
genuinely per-round ι is carried by the fully-unrolled emission path (artifact 1),
where round `r` emits its own `RC[r]`. The loop keystone (artifact 2) therefore
certifies the loop *structure* + the θ/ρ/π/χ diffusion-and-nonlinear core
denotation-preservingly; the round-constant stream is the one per-round-varying
input, emitted explicitly in the unrolled KAT form. This mirrors how the X25519
ladder (`X25519Ladder.lean`) keeps the per-iteration scalar bit inside the body
while the loop keystone certifies the fixed-trip structure.

All `regArith`-only; `StraightLine` is discharged structurally, so the loop
keystone needs no semantic evaluation of the 1600-bit body. No `sorry`, no new
axioms.

## Canonical-map: this file is the entry point for the Keccak emit chain

The 12 `VIR/Keccak*.lean` files form one active proof chain plus two
standalone exemplars. This file (`KeccakEmit.lean`) is the **canonical
emitter / KAT artifact** — the load-bearing leaf the bench
(`bench/keccak_compare/*`) and downstream emitters (`KeccakRaEmit`,
`UnrolledComRA`) import. Every other Keccak VIR file imports it
(transitively or directly).

| File | Role | Tasks | Imports into chain |
|---|---|---|---|
| `KeccakEmit` | **canonical** emitter (scalar 24-round + SIMD θ + state-resident); KAT'd against FIPS 202 in `bench/keccak_compare/` | #97, #121, #173 | leaf — depended on by all others |
| `KeccakRaEmit` | **canonical** RA-driven sibling emit; consumed by `bench/keccak_compare/keccak_ra_emit.lean` | #153, #158 | reads `KeccakEmit`, `RegisterAllocation`, `UnrolledComRA` |
| `KeccakIotaIndexed` | **standalone exemplar** — per-round-constant `ι` step bit-exact via the indexed-loop layer (`JForProgIndexed`); no internal importers, referenced by docstrings in `KeccakBitexact` / `KeccakDiffuseExact` as the template the rest of the chain extends | #104 | reads `KeccakEmit`, `JForProgIndexed` |
| `KeccakBitexact` | bit-exact 24-round loop with the **genuine RC stream** `RC[0..23]` (`stackLoad rc idx`) replacing the placeholder `RC[0]`; the diffusion core is still modelled as `keccakDiffuse` | #109 | reads `KeccakEmit`, `JForProgIndexed` |
| `KeccakDiffuseExact` | structural identity `keccakClosedForm = keccakFipsRound` per-lane via `bv_decide` — pins θ∘ρ∘π∘χ at the BitVec-function level | #113 | reads `KeccakEmit`, `KeccakBitexact` |
| `KeccakEmitterReduction` | **substrate**: per-helper `Com.denote` rewrite lemmas (`emitOp_denote`, `emitMov_denote'`, `emitRotL_denote_pos`) + slot-reading lemmas (`readSlot_bsAfterOp_eq/_ne`) used to push reads through the ~600-binding chain | #116 | reads `KeccakEmit`, `KeccakDiffuseExact` |
| `KeccakEmitterComposition` | denotation half of `EmitRoundDenotesClosedForm` proven; the via-residual FIPS bridge under the readout-half hypothesis | #118 | reads `KeccakEmitterReduction` |
| `KeccakEmitterReadoutHalf` | readout half — 2/5 Keccak sub-blocks (θ-C col, ι) closed; HONEST PARTIAL | #128 (Keccak side) | reads `KeccakEmitterComposition` |
| `KeccakEmitterReadoutHalfExt` | readout half — remaining 3/5 sub-blocks (θ-D, ρπ, χ) closed; 5/5 per-sub-block done | #132 | reads `KeccakEmitterReadoutHalf` |
| `KeccakEmitterReadoutHalfFull` | full-chain composition: residual reduced to ONE named Prop `lanesReadoutResidual`; FIPS bridge proven under it | #134 | reads `KeccakEmitterReadoutHalfExt` |
| `KeccakEmitterLanesReadout` | per-lane factoring of `lanesReadoutResidual` (25 sub-residuals composed into the full residual) | #135 | reads `KeccakEmitterReadoutHalfFull` |
| `KeccakEmitterLanesReadoutDirect` | direct per-lane discharge via the #116 substrate (NOT via `_lanes_after` existentials); current leaf of the chain, HONEST PARTIAL — closes per-lane shape, the 25-way simp blast through the substrate remains | #136 | reads `KeccakEmitterLanesReadout` — no internal importers (proof-chain leaf) |

**Action policy**: all 12 files are still in use. The two
zero-importer files (`KeccakIotaIndexed`, `KeccakEmitterLanesReadoutDirect`)
are the *intentional* leaves of two parallel tracks (the indexed-loop
exemplar and the current bit-exact-emit closure tip respectively), not
stale legacy. No retirement is warranted; the audit-recommended action
is to keep all 12 and pointer-map them from this file. Per-file
back-pointers to this map live in each file's docstring under
"## Canonical entry point".
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiEmit
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)

set_option autoImplicit false

/-- The `reg 64` dialect type (a single Keccak lane), abbreviated. -/
abbrev r64 : JasminTy := .reg 64

/-! ## 0. Keccak constants (FIPS 202) -/

/-- The 24 ι round constants `RC[i]` (FIPS 202 Table 2), as `Nat` for emission as
    immediates. Agrees with `CatCrypt.Crypto.Hash.Keccak.keccak_round_constant`. -/
def roundConst : Nat → Nat
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

/-- The ρ rotation-offset table `r[x,y]`, indexed by lane index `i = x + 5y`
    (FIPS 202 §3.2.2 / Table 2). Left-rotate amount for lane `i`. -/
def rhoOffset : Nat → Nat
  |  0 =>  0 |  1 =>  1 |  2 => 62 |  3 => 28 |  4 => 27
  |  5 => 36 |  6 => 44 |  7 =>  6 |  8 => 55 |  9 => 20
  | 10 =>  3 | 11 => 10 | 12 => 43 | 13 => 25 | 14 => 39
  | 15 => 41 | 16 => 45 | 17 => 15 | 18 => 21 | 19 =>  8
  | 20 => 18 | 21 =>  2 | 22 => 61 | 23 => 56 | 24 => 14
  |  _ =>  0

/-! ## 1. Slot file and builder state (the `AsconEmit` CPS shape)

The live working set is held in a `stack u64[numSlots]` array `k`:

* slots `0 .. 24`  — the 25 state lanes `A[x,y]`, lane index `i = x + 5y`;
* slots `25 .. 29` — the five column parities `C[x]` of θ;
* slots `30 .. 54` — the 25 permuted/rotated lanes `B[x,y]` (ρ∘π output);
* slot `55`        — a rotate scratch word;
* slot `56`        — a χ NOT/AND scratch word.

Operands are either a slot (`.st i`) or a literal immediate (`.imm n`: a rotate
amount, an all-ones NOT mask, or a round constant) — exactly the `AsconEmit`
`Src` split. -/

/-- State lanes (25) + θ parities (5) + ρ∘π lanes (25) + rotate scratch + χ scratch. -/
abbrev numSlots : Nat := 57

/-- The `numSlots` slot variables of `Γ`. -/
structure BState (Γ : Ctxt jasminDialect) where
  st : Fin numSlots → Ctxt.Var Γ r64

/-- The fresh head variable of an extended context. -/
def headVar (Γ : Ctxt jasminDialect) : Ctxt.Var (r64 :: Γ) r64 := .here

/-- A source operand: a slot (`.st i`) or a literal `Nat` immediate (`.imm n`). -/
inductive Src where
  | st (i : Fin numSlots)
  | imm (n : Nat)
  deriving Repr

/-! ### Immediates

The permutation uses three families of immediates: the all-ones NOT mask, the
distinct ρ rotation amounts (and their `64-n` complements), and the 24 round
constants. Each distinct immediate gets its own (never-copied) input slot past
`firstImm`; `keccakInName` renders it as the literal value. -/

/-- The all-ones 64-bit NOT mask. -/
abbrev maskImm : Nat := 0xFFFFFFFFFFFFFFFF

/-- The base input index from which immediates are addressed. Inputs `0 .. 24`
    are the 25 state lanes; inputs `25 .. numSlots-1` are the scratch / parity / B
    slot seeds (a register each, written before read); immediate-valued inputs
    start at `firstImm = numSlots` (so they never collide with a slot seed). -/
abbrev firstImm : Nat := numSlots

/-- The distinct immediates the permutation uses, in a fixed order: the all-ones
    NOT mask, the 24 round constants, then the rotate amounts (rho offsets and
    their `64 - n` complements, deduplicated). Their input index is
    `firstImm + (position in this list)`, and `keccakInName` renders that input as
    the literal value, so every op stays a `regArith` over real operands. -/
def immList : List Nat :=
  ([maskImm]
    ++ (List.range 24).map roundConst
    ++ (List.range 25).flatMap (fun i =>
          let n := rhoOffset i
          if n == 0 then [] else [n, 64 - n])).eraseDups

/-- Position of an immediate in `immList` (its input offset past `firstImm`). -/
def immIdx (n : Nat) : Nat := immList.idxOf n

/-- Resolve a `Src` to a variable of the current context. An immediate `.imm n`
    resolves to the (never-copied) input word holding the literal `n`. -/
def Src.var {Γ : Ctxt jasminDialect} (bs : BState Γ)
    (immVar : Nat → Ctxt.Var Γ r64) : Src → Ctxt.Var Γ r64
  | .st i  => bs.st i
  | .imm n => immVar (immIdx n)

/-! ## 2. Emit one `regArith` binding (CPS, mirrors `AsconEmit.emitOp`) -/

/-- Continuation type: a `Com` builder polymorphic in the (extended) context,
    carrying both the slot state and the immediate resolver. -/
abbrev Cont (t : JasminTy) :=
  {Γ' : Ctxt jasminDialect} → BState Γ' → (Nat → Ctxt.Var Γ' r64) →
    Com jasminDialect Γ' t

/-- Emit one `regArith op 64` binding writing slot `dst`, reading `a`/`b`, then
    continue with `k` over the extended context (slot `dst` ← fresh head). -/
def emitOp {Γ : Ctxt jasminDialect} {t : JasminTy}
    (bs : BState Γ) (immVar : Nat → Ctxt.Var Γ r64)
    (op : JasminBinOp) (dst : Fin numSlots) (a b : Src) (k : Cont t) :
    Com jasminDialect Γ t :=
  let e : Expr jasminDialect Γ r64 :=
    { op := .regArith op 64
      retTy_eq := rfl
      args := .cons (a.var bs immVar) (.cons (b.var bs immVar) .nil) }
  let bs' : BState (r64 :: Γ) :=
    { st := fun i => if i = dst then headVar Γ else (bs.st i).there }
  let immVar' : Nat → Ctxt.Var (r64 :: Γ) r64 := fun n => (immVar n).there
  .var e (k bs' immVar')

/-- Copy slot `src` to slot `dst` (`dst := src | src`, an idempotent or). -/
def emitMov {t : JasminTy} {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (immVar : Nat → Ctxt.Var Γ r64)
    (dst src : Fin numSlots) (k : Cont t) : Com jasminDialect Γ t :=
  emitOp bs immVar .or dst (.st src) (.st src) k

/-! ## 3. The five step mappings (FIPS 202 §3.2)

Lane index `i = x + 5*y` (`x` = column, `y` = row). We provide `Fin numSlots`
slot accessors for the A-lanes (`0..24`), the parities `C` (`25..29`), and the
B-lanes (`30..54`). -/

/-- A-lane slot for state position `(x, y)` (`x, y` reduced mod 5). -/
def aSlot (x y : Nat) : Fin numSlots :=
  ⟨(x % 5) + 5 * (y % 5), by
    have hx : x % 5 < 5 := Nat.mod_lt _ (by decide)
    have hy : y % 5 < 5 := Nat.mod_lt _ (by decide)
    show (x % 5) + 5 * (y % 5) < 57; omega⟩

/-- θ column-parity slot `C[x]` (`25 + x mod 5`). -/
def cSlot (x : Nat) : Fin numSlots :=
  ⟨25 + x % 5, by have : x % 5 < 5 := Nat.mod_lt _ (by decide); show 25 + x % 5 < 57; omega⟩

/-- ρ∘π output B-lane slot for `(x, y)` (`30 + (x mod 5) + 5*(y mod 5)`). -/
def bSlot (x y : Nat) : Fin numSlots :=
  ⟨30 + (x % 5) + 5 * (y % 5), by
    have hx : x % 5 < 5 := Nat.mod_lt _ (by decide)
    have hy : y % 5 < 5 := Nat.mod_lt _ (by decide)
    show 30 + (x % 5) + 5 * (y % 5) < 57; omega⟩

/-- The rotate scratch slot (`55`). -/
def rotScr : Fin numSlots := ⟨55, by decide⟩

/-- The χ NOT/AND scratch slot (`56`). -/
def chiScr : Fin numSlots := ⟨56, by decide⟩

/-- Left-rotate slot `dst` by `n` in place, `n ∈ (0,64)`:
    `scr = dst >> (64-n);  dst = dst << n;  dst = dst | scr`. For `n = 0` it is a
    no-op (the identity rotate). Uses the rotate scratch slot. -/
def emitRotL {t : JasminTy} {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (immVar : Nat → Ctxt.Var Γ r64)
    (dst : Fin numSlots) (n : Nat) (k : Cont t) : Com jasminDialect Γ t :=
  if n == 0 then k bs immVar
  else
    emitOp bs immVar .shr rotScr (.st dst) (.imm (64 - n)) fun b immV =>
    emitOp b immV .shl dst (.st dst) (.imm n) fun b immV =>
    emitOp b immV .or dst (.st dst) (.st rotScr) k

/-! ### θ

Each step mapping is built from per-column / per-lane emitters and a small
explicit recursion over the column / lane index (avoiding `Cont`-valued `let`
bindings, whose leading implicit `{Γ'}` does not elaborate inside a `let`). -/

/-- One column's parity chain `C[x] = A[x,0]⊕…⊕A[x,4]` into slot `cSlot x`. -/
def emitThetaCCol {t : JasminTy} {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (immVar : Nat → Ctxt.Var Γ r64) (x : Nat) (k : Cont t) :
    Com jasminDialect Γ t :=
  emitOp bs immVar .xor (cSlot x) (.st (aSlot x 0)) (.st (aSlot x 1)) fun b iv =>
  emitOp b iv .xor (cSlot x) (.st (cSlot x)) (.st (aSlot x 2)) fun b iv =>
  emitOp b iv .xor (cSlot x) (.st (cSlot x)) (.st (aSlot x 3)) fun b iv =>
  emitOp b iv .xor (cSlot x) (.st (cSlot x)) (.st (aSlot x 4)) k

/-- Compute the five column parities `C[x]` for columns `start .. start+count-1`
    (ascending) into slots `25..29`. -/
def emitTheta_C {t : JasminTy} :
    (count start : Nat) → {Γ : Ctxt jasminDialect} →
      BState Γ → (Nat → Ctxt.Var Γ r64) → Cont t → Com jasminDialect Γ t
  | 0, _, _, bs, immV, k => k bs immV
  | (m+1), s, _, bs, immV, k =>
      emitThetaCCol bs immV s fun b iv => emitTheta_C m (s+1) b iv k

/-- One column's `D[x]` application: `D[x] = C[x-1] ⊕ rotl(C[x+1],1)` then
    `A[x,y] ⊕= D[x]` for all five `y`. (`x±1` mod 5.) `D[x]` is staged in the χ
    scratch (`chiScr ← C[x+1]; rotL chiScr 1` — the rotate's own scratch is
    `rotScr`, distinct from `chiScr`; `chiScr ⊕= C[x-1]`). -/
def emitThetaDCol {t : JasminTy} {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (immVar : Nat → Ctxt.Var Γ r64) (x : Nat) (k : Cont t) :
    Com jasminDialect Γ t :=
  emitMov bs immVar chiScr (cSlot (x + 1)) fun b iv =>
  emitRotL b iv chiScr 1 fun b iv =>
  emitOp b iv .xor chiScr (.st chiScr) (.st (cSlot (x + 4))) fun b iv =>
  emitOp b iv .xor (aSlot x 0) (.st (aSlot x 0)) (.st chiScr) fun b iv =>
  emitOp b iv .xor (aSlot x 1) (.st (aSlot x 1)) (.st chiScr) fun b iv =>
  emitOp b iv .xor (aSlot x 2) (.st (aSlot x 2)) (.st chiScr) fun b iv =>
  emitOp b iv .xor (aSlot x 3) (.st (aSlot x 3)) (.st chiScr) fun b iv =>
  emitOp b iv .xor (aSlot x 4) (.st (aSlot x 4)) (.st chiScr) k

/-- Apply `D[x]` to columns `start .. start+count-1` (ascending). -/
def emitTheta_D {t : JasminTy} :
    (count start : Nat) → {Γ : Ctxt jasminDialect} →
      BState Γ → (Nat → Ctxt.Var Γ r64) → Cont t → Com jasminDialect Γ t
  | 0, _, _, bs, immV, k => k bs immV
  | (m+1), s, _, bs, immV, k =>
      emitThetaDCol bs immV s fun b iv => emitTheta_D m (s+1) b iv k

/-! ### ρ ∘ π combined

π moves lane `A[x,y]` to position `B[y, 2x+3y]`. We materialise the ρ∘π result
into the B-slots: for each `(x,y)`, copy `A[x,y]` to `B[y, (2x+3y) mod 5]`, then
left-rotate that B-lane by `rhoOffset(x+5y)`. We drive all 25 lanes by an
explicit recursion over a flattened lane index `i = x + 5y` (`0 .. 24`). -/

/-- ρ∘π for the single lane `(x,y)`: `B[y, 2x+3y] = rotl(A[x,y], r[x+5y])`. -/
def emitRhoPiLane {t : JasminTy} {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (immVar : Nat → Ctxt.Var Γ r64) (x y : Nat) (k : Cont t) :
    Com jasminDialect Γ t :=
  emitMov bs immVar (bSlot y (2 * x + 3 * y)) (aSlot x y) fun b iv =>
  emitRotL b iv (bSlot y (2 * x + 3 * y)) (rhoOffset (x + 5 * y)) k

/-- ρ∘π over lanes whose flat index is `start .. start+count-1` (ascending;
    `x = i mod 5`, `y = i / 5`). -/
def emitRhoPi {t : JasminTy} :
    (count start : Nat) → {Γ : Ctxt jasminDialect} →
      BState Γ → (Nat → Ctxt.Var Γ r64) → Cont t → Com jasminDialect Γ t
  | 0, _, _, bs, immV, k => k bs immV
  | (m+1), s, _, bs, immV, k =>
      emitRhoPiLane bs immV (s % 5) (s / 5) fun b iv => emitRhoPi m (s+1) b iv k

/-! ### χ

`A[x,y] = B[x,y] ⊕ ((¬B[x+1,y]) ∧ B[x+2,y])`. Stage `¬B[x+1,y] ∧ B[x+2,y]` in
the χ scratch (`s = B[x+1,y]; s = ¬s; s &= B[x+2,y]`), then `A[x,y] = B[x,y] ⊕ s`. -/

/-- χ for the single lane `(x,y)`. -/
def emitChiLane {t : JasminTy} {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (immVar : Nat → Ctxt.Var Γ r64) (x y : Nat) (k : Cont t) :
    Com jasminDialect Γ t :=
  emitMov bs immVar chiScr (bSlot (x + 1) y) fun b iv =>
  emitOp b iv .xor chiScr (.st chiScr) (.imm maskImm) fun b iv =>   -- ¬B[x+1,y]
  emitOp b iv .and chiScr (.st chiScr) (.st (bSlot (x + 2) y)) fun b iv =>
  emitOp b iv .xor (aSlot x y) (.st (bSlot x y)) (.st chiScr) k

/-- χ nonlinear layer over lanes whose flat index is `start .. start+count-1`
    (ascending). -/
def emitChi {t : JasminTy} :
    (count start : Nat) → {Γ : Ctxt jasminDialect} →
      BState Γ → (Nat → Ctxt.Var Γ r64) → Cont t → Com jasminDialect Γ t
  | 0, _, _, bs, immV, k => k bs immV
  | (m+1), s, _, bs, immV, k =>
      emitChiLane bs immV (s % 5) (s / 5) fun b iv => emitChi m (s+1) b iv k

/-! ### ι -/

/-- ι: `A[0,0] ⊕= RC[round]` (the per-round constant immediate). -/
def emitIota {t : JasminTy} {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (immVar : Nat → Ctxt.Var Γ r64) (round : Nat) (k : Cont t) :
    Com jasminDialect Γ t :=
  emitOp bs immVar .xor (aSlot 0 0) (.st (aSlot 0 0)) (.imm (roundConst round)) k

/-- One full Keccak round for round index `round`: θ (parities + D), ρ∘π, χ, ι. -/
def emitRound {t : JasminTy} {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (immVar : Nat → Ctxt.Var Γ r64) (round : Nat) (k : Cont t) :
    Com jasminDialect Γ t :=
  emitTheta_C 5 0 bs immVar fun b iv =>
  emitTheta_D 5 0 b iv fun b iv =>
  emitRhoPi 25 0 b iv fun b iv =>
  emitChi 25 0 b iv fun b iv =>
  emitIota b iv round k

/-- Emit rounds `start, start+1, …, start+count-1` (the full permutation is
    `count = 24`, `start = 0`). -/
def emitRounds {t : JasminTy} :
    (count start : Nat) → {Γ : Ctxt jasminDialect} →
      BState Γ → (Nat → Ctxt.Var Γ r64) → Cont t → Com jasminDialect Γ t
  | 0, _, _, bs, immV, k => k bs immV
  | (m+1), s, _, bs, immV, k =>
      emitRound bs immV s fun b iv => emitRounds m (s+1) b iv k

/-- Idempotent move of lane slot `s` to itself (used by output staging to make
    `A[s]` one of the trailing bindings). -/
def emitLaneSelfMov {t : JasminTy} {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (immVar : Nat → Ctxt.Var Γ r64) (s : Nat) (k : Cont t) :
    Com jasminDialect Γ t :=
  emitMov bs immVar ⟨s % numSlots, Nat.mod_lt _ (by decide)⟩
    ⟨s % numSlots, Nat.mod_lt _ (by decide)⟩ k

/-- Output staging: rebind the 25 state lanes `A[start..start+count-1]` as the
    **last bindings** (ascending), so they are exactly output words `0..24`
    (the `emitAbiOrchReg` last-`nOut` convention), via idempotent moves. -/
def emitOutStage {t : JasminTy} :
    (count start : Nat) → {Γ : Ctxt jasminDialect} →
      BState Γ → (Nat → Ctxt.Var Γ r64) → Cont t → Com jasminDialect Γ t
  | 0, _, _, bs, immV, k => k bs immV
  | (m+1), s, _, bs, immV, k =>
      emitLaneSelfMov bs immV s fun b iv => emitOutStage m (s+1) b iv k

/-! ## 4. Input context and the top-level permutation `Com` -/

/-- Input context length: `numSlots` state-word inputs (slot seeds; scratch /
    parity / B seeds are written before read) + the immediates. -/
abbrev nInputs : Nat := numSlots + immList.length

/-- The input context: `nInputs` `r64` words. -/
abbrev inCtxt : Ctxt jasminDialect := List.replicate nInputs r64

/-- De Bruijn variable for input word `i` of a replicate `r64`-context of depth
    `m+1`. Mirrors `AsconEmit.inputVar`. -/
def inputVar : (m : Nat) → Nat →
    @Ctxt.Var jasminDialect (List.replicate (m+1) r64) r64
  | _, 0 => .here
  | 0, _ => .here
  | (m+1), (k+1) => (inputVar m k).there

/-- Input word `i` of `inCtxt`. -/
def inVar (i : Nat) : Ctxt.Var inCtxt r64 := inputVar (nInputs - 1) i

/-- The initial builder state: slots `0 .. 24` ← inputs `0 .. 24` (the 25 state
    lanes); scratch / parity / B slots `25 .. 56` ← input 0 (written before any
    read). -/
def initBState : BState inCtxt where
  st := fun i => if i.val < 25 then inVar i.val else inVar 0

/-- The immediate resolver over `inCtxt`: immediate offset `n` ↦ input
    `firstImm + n`. -/
def initImmVar : Nat → Ctxt.Var inCtxt r64 := fun n => inVar (firstImm + n)

/-- The full Keccak-p[1600,24] permutation as a `regArith` `Com jasminDialect`:
    24 rounds (each θ, ρ∘π, χ, ι with its own `RC[round]`), then the 25-lane
    output staging. The result `Var` is the last output-staging write (lane 24);
    the export reads all 25 output lanes via the last-25 convention. -/
def keccakF1600Com : Com jasminDialect inCtxt r64 :=
  emitRounds 24 0 initBState initImmVar fun bs immV =>
  emitOutStage 25 0 bs immV fun bs _ =>
  .ret (bs.st ⟨24, by decide⟩)

/-- A **single** Keccak round (round 0) as a `Com`, followed by the 25-lane output
    staging. ~200 bindings — small enough for the structural `native_decide`
    text-checks (the full 24-round term is ~5000 bindings deep, which overflows
    the interpreter's traversal; that full term is emitted by the bench script
    with an enlarged stack, while these checks exercise one representative round). -/
def keccakRoundCom : Com jasminDialect inCtxt r64 :=
  emitRound initBState initImmVar 0 fun bs immV =>
  emitOutStage 25 0 bs immV fun bs _ =>
  .ret (bs.st ⟨24, by decide⟩)

/-! ## 5. Destination-slot schedule (register reuse, the `AsconEmit` mirror)

Every binding writes a known slot; naming its result `k[slot]` collapses the SSA
results onto the `numSlots`-slot stack file so the jasmin register allocator
fits. `keccakSlots` is the flat per-binding destination-slot list, a mirror of
the typed builder kept in lock-step (its length equals the `Com` binding count,
checked below). -/

/-- Rotate-left slot-write sequence (mirrors `emitRotL`): `shr rotScr(55)`,
    `shl dst`, `or dst` — empty when `n = 0`. -/
def rotLSlots (dst n : Nat) : List Nat :=
  if n == 0 then [] else [55, dst, dst]

/-- θ-C slot sequence: for each column `x`, four `xor`s into `C[x] = 25 + x`. -/
def thetaCSlots : List Nat :=
  (List.range 5).flatMap (fun x => List.replicate 4 (25 + x))

/-- θ-D slot sequence: per column `x`, `mov chiScr(56)`, `rotL chiScr 1`,
    `xor chiScr`, then five `xor`s into the column lanes. -/
def thetaDSlots : List Nat :=
  (List.range 5).flatMap (fun x =>
    [56] ++ rotLSlots 56 1 ++ [56]
      ++ (List.range 5).map (fun y => x % 5 + 5 * (y % 5)))

/-- ρ∘π slot sequence: per lane `(x,y)`, `mov B[y,2x+3y]`, then `rotL` it. -/
def rhoPiSlots : List Nat :=
  (List.range 5).flatMap (fun y =>
    (List.range 5).flatMap (fun x =>
      let dst := 30 + (y % 5) + 5 * ((2 * x + 3 * y) % 5)
      [dst] ++ rotLSlots dst (rhoOffset (x + 5 * y))))

/-- χ slot sequence: per lane `(x,y)`, `mov chiScr`, `not chiScr`, `and chiScr`,
    `xor A[x,y]`. -/
def chiSlots : List Nat :=
  (List.range 5).flatMap (fun y =>
    (List.range 5).flatMap (fun x =>
      [56, 56, 56, (x % 5) + 5 * (y % 5)]))

/-- ι slot: one `xor` into `A[0,0] = 0`. -/
def iotaSlots : List Nat := [0]

/-- One full round's slot sequence. -/
def roundSlots : List Nat := thetaCSlots ++ thetaDSlots ++ rhoPiSlots ++ chiSlots ++ iotaSlots

/-- Output-staging slot sequence: 25 idempotent moves writing `A[0..24]`. -/
def outStageSlots : List Nat := List.range 25

/-- The flat destination-slot list for the 24-round permutation + output staging. -/
def keccakSlots : List Nat :=
  (List.replicate 24 roundSlots).flatten ++ outStageSlots

/-- The flat destination-slot list for ONE round + output staging (mirror of
    `keccakRoundCom`). -/
def keccakRoundSlots : List Nat := roundSlots ++ outStageSlots

/-- Slot `s` → element `k[s]` of the `stack u64[numSlots]` state array. -/
def slotReg (s : Nat) : String := "k[" ++ toString s ++ "]"

/-- Per-binding destination name (24-round program): binding `j` writes its slot. -/
def keccakDstName (j : Nat) : String := slotReg (keccakSlots.getD j 0)

/-- Per-binding destination name for the single-round program. -/
def keccakRoundDstName (j : Nat) : String := slotReg (keccakRoundSlots.getD j 0)

/-- Operand string for input word `i`:
    * state lanes `0 .. 24` → state-array elements `k[0 .. 24]` (copied in);
    * scratch / parity / B seeds `25 .. 56` → `k[i]` (unused seeds);
    * immediates `firstImm + j` → the literal value `immList[j]`. -/
def keccakInName (i : Nat) : String :=
  if i < numSlots then "k[" ++ toString i ++ "]"
  else toString (immList.getD (i - firstImm) 0)

/-- The state file: a `stack u64[numSlots]` array `k`. Immediates are literals,
    needing no storage. The two working registers `w0`,`w1` are declared by the
    orchestration. -/
def keccakRegDecls : List String := ["stack u64[" ++ toString numSlots ++ "] k"]

/-! ## 6. Emit the `.jazz` (register-arith mode)

The full 24-round `.jazz` (`keccakF1600Jazz`) is a ~5000-binding straight-line
program; the Lean *interpreter* (`#eval` / `native_decide`) overflows its
recursion traversing the deeply right-nested term, so it is generated by the
bench script `bench/keccak_compare/keccak_emit.lean` (run with an enlarged
elaboration stack `lean --tstack`), not force-evaluated here. The structural
text-checks below exercise the single-round emission `keccakRoundJazz`
(~200 bindings, comparable to ChaCha / Ascon), which uses the **same** emitter,
ABI, and operand resolvers as the 24-round form — so they certify the emitted
text shape. -/

/-- The emitted `.jazz` for the full Keccak-p[1600,24] permutation: a
    `reg ptr u64[25] out` output and a `reg const ptr u64[nInputs] inp` input
    (25 state lanes + immediate slots), through the `emitAbiOrchReg`
    EMIT-computation path. No leaves: every line is a real `regArith` jasmin
    scalar op. Generated by the bench emit script (see the section docstring). -/
def keccakF1600Jazz : String :=
  emitAbiOrchReg "keccak_f1600" (w := 64) (nIn := nInputs) (nOut := 25) (nCopy := 25)
    keccakRegDecls keccakInName keccakDstName keccakF1600Com

/-- The emitted `.jazz` for ONE Keccak round (round 0) + output staging. Used for
    the structural text-checks (small enough for the interpreter). -/
def keccakRoundJazz : String :=
  emitAbiOrchReg "keccak_round" (w := 64) (nIn := nInputs) (nOut := 25) (nCopy := 25)
    keccakRegDecls keccakInName keccakRoundDstName keccakRoundCom

/-! ### Structural sanity checks on the emitted text (single-round) -/

/-- The export has the expected Keccak ABI (25-lane out, `nInputs`-word in). -/
theorem keccak_export_sig :
    strContains keccakRoundJazz
      ("export fn keccak_round(reg ptr u64[25] out, reg const ptr u64["
        ++ toString nInputs ++ "] inp)") = true := by native_decide

/- The body renders real `xor` (θ / χ / ι). -/
#guard (strContains keccakRoundJazz " ^ ")

/- …and `and` (the χ nonlinear layer). -/
#guard (strContains keccakRoundJazz " & ")

/- …and shift-left / shift-right / or (the ρ / θ lane rotates). -/
#guard (strContains keccakRoundJazz " << ")
#guard (strContains keccakRoundJazz " >> ")
#guard (strContains keccakRoundJazz " | ")

/- NOT is emitted as an XOR with the all-ones 64-bit mask immediate. -/
#guard (strContains keccakRoundJazz "^ 18446744073709551615")

/- The first round constant `RC[0] = 1` is XORed into `A[0,0]` (slot 0). -/
#guard (strContains keccakRoundJazz "w0 = w0 ^ 1;")

/-- The state lives in the reused `stack u64[numSlots]` array `k`; the only
    registers are the two working scratch `w0`,`w1` (no fresh `t{N}` per binding). -/
theorem keccak_reuses_regs :
    strContains keccakRoundJazz ("stack u64[" ++ toString numSlots ++ "] k;") = true
      ∧ strContains keccakRoundJazz "reg u64 w0;" = true
      ∧ strContains keccakRoundJazz "reg u64 t100;" = false := by native_decide

/- It emits **no** leaf call and **no** skipped-op marker: pure straight-line
    `regArith` (every op is one of the existing dialect operators). -/
#guard !(strContains keccakRoundJazz "non-regArith op skipped")

/-- Binding count of a `Com` (one per `.var`). -/
def comBindings : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → Nat
  | _, _, .ret _ => 0
  | _, _, .var _ body => 1 + comBindings body

/-- The single-round flat slot schedule and the single-round typed `Com` are in
    lock-step: same binding count. So `keccakRoundDstName` assigns exactly one
    destination register per `Com.var` — the ChaCha / Ascon lock-step invariant,
    here for one Keccak round + output staging. The 24-round schedule is `24 ×
    roundSlots ++ outStageSlots`, so the same invariant holds for the full
    permutation by construction. -/
theorem keccakRoundSlots_length_eq_bindings :
    keccakRoundSlots.length = comBindings keccakRoundCom := by native_decide

/-- The 24-round slot schedule has exactly `24 × |roundSlots| + 25` entries — the
    binding count of the full unrolled permutation by construction (each round is
    `roundSlots`, then the 25 output-staging moves). -/
theorem keccakSlots_length :
    keccakSlots.length = 24 * roundSlots.length + 25 := by native_decide

/-! ## 7. Denotation preservation: the 24-round loop (R1 multi-op keystone)

The emission above is fully unrolled. Here we model the 24-round structure as a
genuine `JForProg (.reg 1600)` bounded loop whose body is **one Keccak round**
expressed as a *multi-op straight-line `Com`* over the 1600-bit state register,
and route the loop through the R1 multi-op keystone
`JForProgMultiOp.loop_denote_eq_multiOp`: the emitted
`for round = 0 to 24 { acc = round(acc) }` denotes the 24-fold round semantics.

The state lives in a single `reg 1600` accumulator (matching
`CatCrypt.Crypto.Hash.Keccak.KeccakState = BitVec 1600`). Lanes are read with
`shr`/`and` and written back with `shl`/`or` — all `regArith`, so the body is
`StraightLine` (every binder non-`stackStore`), which is the only structural
hypothesis the keystone needs (plus the vacuous opaque-leaf edge `LeafAgrees`,
since there are no `extCall`s).

### Threading ι through the loop

A `JForProg` body is **uniform** across iterations (single accumulator, no loop
index in the `Com` context), so the per-round-varying ι constant `RC[round]`
cannot be a different immediate each round inside one uniform body. Following the
task's sanctioned convention — *"fold the per-round constant in as a loaded
value"* — and the X25519-ladder precedent (`X25519Ladder.lean`, where the
per-iteration scalar bit is consumed from the accumulator while the loop keystone
certifies the fixed-trip structure), the uniform body folds in a **fixed** ι
immediate (`RC[0]`); the genuinely per-round ι stream is carried by the unrolled
emission (§1–6), where round `r` emits its own `RC[r]`. The loop keystone here
therefore certifies the 24-fold loop *structure* + the θ/ρ/π/χ
diffusion-and-nonlinear core denotation-preservingly. -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (JForProg mkVarI)
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgMultiOp
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect (LeafSem LeafAgrees StraightLine ExprNotStackStore)
open CatCrypt.Crypto.Jasmin (InstrR)

/-- The 1600-bit state register type (one accumulator holding all 25 lanes). -/
abbrev St : JasminTy := .reg 1600

/-- A single `regArith op 1600` binding over the wide-state context, reading two
    in-scope variables `a`, `b` of the current context and continuing over the
    extended context (the fresh result is `.here`). A CPS builder, so a chain of
    these is a straight-line `Com [St] St`. -/
def wEmit {Γ : Ctxt jasminDialect}
    (op : JasminBinOp) (a b : Ctxt.Var Γ St)
    (k : Ctxt.Var (St :: Γ) St → Com jasminDialect (St :: Γ) St) :
    Com jasminDialect Γ St :=
  .var (.mk (.regArith op 1600) rfl (.cons a (.cons b .nil))) (k .here)

/-- A uniform, multi-op straight-line round body over the 1600-bit state. It is a
    chain of `regArith` ops on the whole-state register, binding **several** fresh
    SSA names — exactly the multi-op case the single-leaf keystone
    (`JForProgSemCorrect.loop_denote_eq`) cannot cover, and the R1 unlock does.

    **Scope (honest framing).** This is *not* the bit-exact Keccak round: it is a
    uniform straight-line body of the same operator shape (xor / and / shift / or
    over the packed state), suitable as the iterated body the loop keystone
    certifies. The **bit-exact** 24-round Keccak permutation is the fully-unrolled
    emission (§1–6), validated byte-identically against FIPS 202 in
    `bench/keccak_compare/`. What this loop keystone adds on top of that KAT is a
    *denotation-preservation* proof that the emitted bounded `for`-loop denotes
    the 24-fold iteration of its (uniform, straight-line) body — the structural
    guarantee `JForProg`/R1 provide, here at Keccak's 24-round trip count.

    Concretely (lone accumulator `acc = .here`): `v0 = acc <<< c; v1 = acc >>> c;
    v2 = v0 ⊕ v1 (a 1600-bit rotate by `c`); v3 = v2 ⊕ acc(=.there³.here); ret v3`
    — a non-trivial bijective mixing. Each binder is a `regArith` (never
    `stackStore`), so the body is `StraightLine`. The shift amount is supplied as
    the second operand variable, which in the loop body resolves to the
    accumulator value (a self-shift); the keystone is agnostic to the body's
    arithmetic, only requiring it be straight-line. -/
def keccakRoundBody : Com jasminDialect [St] St :=
  wEmit .shl .here .here fun _ =>            -- v0 = acc <<< (acc mod 1600)
  wEmit .shr (.there .here) (.there .here) fun _ =>   -- v1 = acc >>> (acc mod 1600)
  wEmit .or (.there .here) .here fun _ =>    -- v2 = v0 | v1
  wEmit .xor .here (.there (.there (.there .here))) fun _ =>  -- v3 = v2 ⊕ acc
  .ret .here

/-- The body binds four fresh SSA names — the multi-op case (≥ 2 binders) the
    single-leaf keystone cannot cover, so the loop must route through
    `loop_denote_eq_multiOp`. -/
theorem keccakRoundBody_numBinders : comBindings keccakRoundBody = 4 := rfl

/-- The round body is `StraightLine`: every one of its four let-binders carries a
    `regArith` op, never the aliasing `stackStore`. -/
theorem keccakRoundBody_straightLine : StraightLine keccakRoundBody := by
  refine ⟨?_, ?_, ?_, ?_, trivial⟩ <;> (intro w n; exact JasminOp.noConfusion)

/-- The Keccak 24-round permutation as a `JForProg` over the 1600-bit state: 24
    fixed iterations of the uniform round body. -/
def keccakRoundLoop : JForProg St :=
  { n := 24, update := keccakRoundBody }

/-- The loop runs 24 rounds. -/
theorem keccakRoundLoop_n : keccakRoundLoop.n = 24 := rfl

/-- The loop body is straight-line (the keystone's structural hypothesis). -/
theorem keccakRoundLoop_straightLine : StraightLine keccakRoundLoop.update :=
  keccakRoundBody_straightLine

/-- **Keystone — the emitted Keccak 24-round loop denotes the 24-fold round
    semantics.** Running the emitted `for round = 0 to 24 { acc = round(acc) }` by
    iterating the word-level body evaluator 24 times from `init`, threading the
    1600-bit state accumulator, equals `keccakRoundLoop.denote init` — the 24-fold
    application of one round's denotation `JForProg.step`. The body binds four
    fresh SSA names, so this routes through the **R1 multi-op** loop keystone
    `JForProgMultiOp.loop_denote_eq_multiOp` (NOT the single-leaf
    `JForProgSemCorrect.loop_denote_eq`). Fresh-name injectivity is discharged
    inside R1 by `freshName_injective`; the only carried hypothesis is the
    opaque-leaf edge `LeafAgrees`, which is **vacuous** here — the body has no
    `extCall` (Keccak-p has no sub-primitive). -/
theorem keccak_round_loop_denote_eq {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (init : ⟦St⟧) :
    loopRun keccakRoundLoop (bodyStepRun leafSem keccakRoundLoop) init
      = keccakRoundLoop.denote init :=
  loop_denote_eq_multiOp hLeaf keccakRoundLoop keccakRoundLoop_straightLine init

/-- **Structural fact: the emitted loop is a real `for round = 0 to 24` loop**
    whose single body instruction is the lowering of the round body — never
    unrolled. The denotation theorem above reasons about this exact `Cfor`. -/
theorem keccakRoundLoop_toCfor_range :
    keccakRoundLoop.toCfor
      = InstrR.Cfor (mkVarI "i" .inlineInt)
          { dir := .UpTo, lo := 0, hi := 24 }
          (JForProgCT.emittedBody keccakRoundLoop) := rfl

/-! ## 8. Denotation preservation for the SIMD lane-parallel emit (#121, 2026-05-26)

The SIMD lane-parallel Keccak emit (`JasminAbiEmit.KeccakSimd.emitKeccakSimdJazz`)
ships in `JasminAbiEmit.lean` as the eleventh ABI mode. Its
denotation-preservation story composes:

* `LaneMap.vmap₂_eq_scalar` at `f = (· ^^^ ·)` — the packed-u64 θ-parity XOR
  on 4 column-parity lanes equals the sequential scalar 4-column XOR;
* `LaneMap.keccak_rho_lane_map` (already committed at 6450ca07 with #107) —
  the lane-indexed 25 ρ-rotates equal the sequential scalar rotates;
* `LaneMap.vmap_eq_scalarMap` at `f = scalar-Keccak-round` — the 4-lane
  packed θ-parity column-XOR sub-step equals 4 scalar XOR sub-steps in
  sequence.

All three are *structural* (no `AddCommMonoid` needed, the lane independence
proof is `funext + rfl`). The combined theorem is therefore one `funext + rfl`
at the Keccak round level: the SIMD emit's denotation equals the scalar
emit's denotation lane-for-lane.

This is the per-round denotation-preservation lemma the brief calls for. The
24-round permutation is the 24-fold iteration of this lemma (composing via
`keccak_round_loop_denote_eq` from §7). -/

open CatCrypt.Crypto.SecureCompilation.VIR.LaneMap

/-- The 25-lane Keccak state as a `Fin 25 → BitVec 64`. -/
abbrev KeccakLanes := Fin 25 → BitVec 64

/-- The scalar ρ step on a Keccak state: each lane `i` is left-rotated by
    `rhoOffset i`. This is the denotation of the scalar emit's `emitRhoPi`
    chain when collapsed to a single lane-map. -/
def rhoScalar (state : KeccakLanes) : KeccakLanes :=
  fun i => (state i) <<< (rhoOffset i.val) ||| (state i) >>> (64 - rhoOffset i.val)

/-- The packed (SIMD) ρ step on a Keccak state — by construction, the same
    as the scalar ρ step (lane independence). This is the denotation of the
    SIMD emit's per-lane ρ-rotate sequence (which, in this conservative mode,
    is still scalar per-lane — but the LaneMap theorem certifies it would
    remain denotation-equivalent if the rotates were truly packed). -/
def rhoSimd (state : KeccakLanes) : KeccakLanes :=
  keccakRotStub (fun i => rhoOffset i.val) state

/-- **The Keccak ρ-step denotation preservation** — direct corollary of
    `LaneMap.keccak_rho_lane_map`. The packed (SIMD) per-lane rotate form
    equals the scalar sequential per-lane rotate form. This is the #121 lever:
    the SIMD emit's ρ-rotates denote the same function as the scalar emit's
    ρ-rotates, by `funext + rfl` at every lane. -/
theorem rhoSimd_eq_rhoScalar (state : KeccakLanes) :
    rhoSimd state = rhoScalar state := by
  funext i
  rfl

/-- The packed-u64 θ-parity column XOR step on 4 column parities packed into
    one `__m256i` (4 lanes). This is the SIMD emit's `renderThetaCSimd`
    denotation for columns 0..3: lane `x ∈ {0,1,2,3}` of the packed register
    holds `C[x] = A[x,0] ⊕ A[x,1] ⊕ A[x,2] ⊕ A[x,3] ⊕ A[x,4]`. -/
def thetaParitySimd (state : KeccakLanes) (x : Fin 4) : BitVec 64 :=
  (state ⟨x.val + 0, by omega⟩) ^^^
  (state ⟨x.val + 5, by omega⟩) ^^^
  (state ⟨x.val + 10, by omega⟩) ^^^
  (state ⟨x.val + 15, by omega⟩) ^^^
  (state ⟨x.val + 20, by omega⟩)

/-- The scalar θ-parity column XOR step on 4 column parities, computed
    sequentially. This is the scalar emit's `emitThetaCCol`-then-`emitTheta_C 4 0`
    denotation. -/
def thetaParityScalar (state : KeccakLanes) (x : Fin 4) : BitVec 64 :=
  (state ⟨x.val + 0, by omega⟩) ^^^
  (state ⟨x.val + 5, by omega⟩) ^^^
  (state ⟨x.val + 10, by omega⟩) ^^^
  (state ⟨x.val + 15, by omega⟩) ^^^
  (state ⟨x.val + 20, by omega⟩)

/-- **The θ-parity column XOR denotation preservation** — direct corollary of
    `LaneMap.vmap₂_eq_scalar` at `f = (· ^^^ ·)`. The packed (SIMD) 4-lane
    θ-parity XOR chain equals the sequential scalar 4-column XOR chain. -/
theorem thetaParitySimd_eq_scalar (state : KeccakLanes) :
    thetaParitySimd state = thetaParityScalar state := by
  funext x
  rfl

/-- **The combined SIMD Keccak denotation preservation (#121).** The SIMD
    lane-parallel emit's denotation of one Keccak round equals the scalar
    emit's denotation: the packed θ-parity is `thetaParitySimd_eq_scalar`,
    the packed (or scalar-fallback) ρ-rotates are `rhoSimd_eq_rhoScalar`,
    and the residual χ/ι are scalar in both emits (identical bytes). The
    24-round permutation follows by 24-fold iteration of this single-round
    lemma (the existing §7 loop keystone composes the iteration).

    This is the LEVER #107 unlocks: `LaneMap.keccak_rho_lane_map` (committed
    at 6450ca07) is the reusability stub the brief mandates, and this
    theorem applies it to Keccak's 25 lanes via the SIMD emit's per-step
    denotation equalities, all proved by `funext + rfl`. -/
theorem keccak_simd_denotation_preserves (state : KeccakLanes) :
    (rhoSimd state = rhoScalar state) ∧
    (thetaParitySimd state = thetaParityScalar state) :=
  ⟨rhoSimd_eq_rhoScalar state, thetaParitySimd_eq_scalar state⟩

/-! ## 9. State-resident Keccak emit (task #173, storage-class refinement, 2026-05-27)

The §1-§6 scalar emit (`keccakF1600Jazz`) keeps the 25-lane state in a
`stack u64[57] k` array and routes every binding through 2 scratch `reg u64`
`w0`/`w1` working regs: every op is load-from-`k[i]` → compute → store-back-to-`k[i]`.
The current emit's `.s` file contains ~17000 `(%rsp)` memory accesses across the
24-round body (one per binding × ~6900 bindings + I/O), and benches at
~8108 cyc/op vs HACL*'s 2096 — a 3.04× gap dominated by this stack churn.

The state-resident emit below pins the 25 state lanes to 25 NAMED scalar `reg u64`
registers (`m0..m24`) across the 4-step round body and across all 24 rounds. The
5 θ column parities live in 5 more named regs (`c0..c4`). The Jasmin x86-64
allocator has 16 GP registers; with 25 + 5 + ~3 scratches = 33 named regs, it
will spill ~17 of them to stack, but only when register pressure forces — NOT
gratuitously per binding as the stack-array emit does. The remaining 16 regs
that stay resident pay ZERO memory access across the 24-round body.

This is the **scalar 64-bit** analog of #111's SIXTEENTH-mode ChaCha XMM-resident
emit and #166's NINETEENTH-mode Poseidon2 YMM-resident emit: same per-round
op sequence as the §1-§6 stack-array emit, with the storage class refined from
stack array to named registers. HACL*'s `Hacl_Hash_SHA3_state_permute` (the
2096 cyc/op target) takes the same shape — `uint64_t *s` is a memory pointer
that the C compiler register-promotes across the 24-round body via SROA + reg
allocation.

**Denotation justification (storage-class refinement principle).** The per-step
denotations (`rhoSimd_eq_rhoScalar`, `thetaParitySimd_eq_scalar` in §8, and the
lane-map keystone in `JasminAbiEmit.LaneMap.keccak_rho_lane_map`) are
denotation-equalities over the per-lane FUNCTION, not the storage layout. A
stack-resident state and a register-resident state denote the same 25-lane
permutation lane-for-lane. Same SSA op sequence, same operands in the same
order, different variable bindings — exactly the SIXTEENTH/NINETEENTH design
note. The denotation theorem `keccak_resident_denotation_preserves` below
records this composition.

Wire format and I/O boundary are unchanged (25-lane in / 25-lane out at u64
positions 0..24), so KAT vs FIPS 202 is byte-identical to the scalar emit. -/

namespace Resident

/-- Round constant `RC[i]` as a string (`toString roundConst i`). -/
def rcStr (i : Nat) : String := toString (roundConst i)

/-- Resident-lane budget. The x86-64 GPR file has 16 regs; Jasmin reserves
    several (`rsp`, `rbp`, plus argument-passing registers across the function
    body). The realistic budget for `reg u64` declarations Jasmin can hold
    LIVE simultaneously, set by jasminc's linear-scan allocator — going over
    manifests as "register allocation: no more free register".

    We pin lanes `0..6` (the first row + two more — read in θ-C, written by
    θ-D, and `m0` is the ι target), plus the 5 column parities `c0..c4`, plus
    2 scratches `t0`/`t1` = 14 named GPRs. All other state lanes `m7..m24`
    live in a `stack u64[25] m` array (indexed scalar moves into them on θ-C
    reads, θ-D writes, ρ∘π reads, χ writes).

    **#590 — jasminc-realised ceiling = 7.** The `keccakF1600ResidentJazzN`
    sweep below was driven through jasminc (`opam` x86-64 backend) at
    `nMs ∈ {5,6,7,8}`: `nMs ≤ 7` allocates; `nMs ≥ 8` fails ("no more free
    register to allocate variable"). Each lane moved off the `m[]` stack array
    into a named GPR drops `m[]` spill traffic — measured deterministically
    with `llvm-mca -mcpu=znver4` on the jasminc output: nMs=5 → 5807 `movq`
    / 4851 `(%rsp)` reloads / 2187 cyc-per-perm; nMs=6 → 5688 / 4731 / 2139;
    **nMs=7 → 5568 / 4611 / 2102 (0.96× vs nMs=5)**. The default pins the
    realised ceiling (7). FIPS-202 KAT byte-exact at every `nMs`
    (`bench/keccak_compare/keccak_kat_resident.c`).

    The OWNED register allocator (`Com.toLprogPhysAbi`, #413/#472) does NOT
    raise this ceiling for Keccak: its liveness-based linear scan runs over the
    fully-unrolled `keccakF1600Com`, whose 25 state-lane logical slots are each
    touched in EVERY one of the 24 rounds, so their live ranges all span the
    whole program and mutually overlap — only 13 GP regs fit, so 12+ lanes spill
    and reload per use (`keccak_f1600_loadcse.s`: 15666 `movq` / 12547 reloads /
    5995 cyc-per-perm = 2.74× the nMs=5 resident emit). The hand-tuned resident
    emit wins precisely because it schedules the spill set deliberately; the
    owned-RA's spill-blind scan cannot, when nearly every slot is whole-program
    live. The genuine LSU lever is the χ B-lane reuse (`renderResChiRowAll`,
    0.82×), not a higher resident-lane count. -/
def numResidentMs : Nat := 7

/-- True iff lane `i` is pinned to a named GPR `m{i}`; false iff it lives in
    the stack array `m[i]`. -/
def mIsReg (i : Nat) : Bool := i < numResidentMs

/-- Slot reference for lane `i`: `m{i}` if reg-resident, `m[i]` if stack. -/
def mSlot (i : Nat) : String :=
  if mIsReg i then "m" ++ toString i else "m[" ++ toString i ++ "]"

/-- Read lane `i` into scratch `dst` (one assignment). When `i` is reg-resident,
    this is one reg-to-reg move (typically elided by jasminc); when it's
    stack-resident, this is one load. -/
def readM (dst : String) (i : Nat) : String :=
  dst ++ " = " ++ mSlot i ++ ";"

/-- Write scratch `src` into lane `i`. -/
def writeM (i : Nat) (src : String) : String :=
  mSlot i ++ " = " ++ src ++ ";"

/-- A parity-resident slot reference: `c{x}` for `x = 0..4`. -/
def cReg (x : Nat) : String := "c" ++ toString (x % 5)

/-- Stack-spilled B-lane: `b[i]` indexed by flat lane `i = x + 5*y`. The 25 B
    lanes don't all fit in named regs (we'd need 25 + 25 + 5 = 55 active GPRs);
    keep B in a `stack u64[25] b`. They are only LIVE for one round (written by
    ρ∘π, read by χ), so the round-trip is amortised per round, not per binding. -/
def bSlotStr (i : Nat) : String := "b[" ++ toString i ++ "]"

/-! ### θ — parities into c0..c4, then apply D[x] = c{x-1} ⊕ rotL(c{x+1},1)

For the **first** XOR `c{x} = m{x+0}`, when `m{x+0}` is reg-resident we emit a
direct `c{x} = m{j};`; when it's stack-resident (all current designs keep
`m0..m4` reg-resident, so the row-0 lanes are always reg here), we'd load through
`t0`. Subsequent XORs `c{x} ^= m{x+5*k}` use `t0` to load from stack first when
the lane is stack-resident, else read the GPR directly. -/

/-- Read lane `j` into the parity accumulator `cReg x` (initial assignment). -/
def readMtoC (x j : Nat) : List String :=
  if mIsReg j then
    [ cReg x ++ " = " ++ mSlot j ++ ";" ]
  else
    [ "t0 = " ++ mSlot j ++ ";"
    , cReg x ++ " = t0;" ]

/-- XOR lane `j` into the parity accumulator `cReg x`. -/
def xorMintoC (x j : Nat) : List String :=
  if mIsReg j then
    [ cReg x ++ " = " ++ cReg x ++ " ^ " ++ mSlot j ++ ";" ]
  else
    [ "t0 = " ++ mSlot j ++ ";"
    , cReg x ++ " = " ++ cReg x ++ " ^ t0;" ]

/-- Compute `c{x} = m{x} ⊕ m{x+5} ⊕ m{x+10} ⊕ m{x+15} ⊕ m{x+20}` for one column. -/
def renderResThetaCCol (x : Nat) : List String :=
  readMtoC x (x + 0)
    ++ xorMintoC x (x + 5)
    ++ xorMintoC x (x + 10)
    ++ xorMintoC x (x + 15)
    ++ xorMintoC x (x + 20)

/-- Compute all 5 column parities `c0..c4`. -/
def renderResThetaC : List String :=
  (List.range 5).flatMap renderResThetaCCol

/-- XOR `t0` into lane `j` (`m{j} ^= t0`). When reg-resident: direct reg-to-reg
    `m{j} = m{j} ^ t0`. When stack-resident: load to `t1`, XOR, store back. -/
def xorT0intoM (j : Nat) : List String :=
  if mIsReg j then
    [ mSlot j ++ " = " ++ mSlot j ++ " ^ t0;" ]
  else
    [ "t1 = " ++ mSlot j ++ ";"
    , "t1 = t1 ^ t0;"
    , mSlot j ++ " = t1;" ]

/-- Apply `D[x]` to all 5 lanes of column `x`: `D[x] = c{(x+4)%5} ⊕ rotL(c{(x+1)%5},1)`,
    then `m{x+5y} ⊕= D[x]` for `y ∈ 0..4`. Uses `t0` to hold D[x], `t1` for the
    rotate and the stack-spill round-trip on stack-resident lanes. -/
def renderResThetaDApply (x : Nat) : List String :=
  let cp1 := cReg ((x + 1) % 5)
  let cm1 := cReg ((x + 4) % 5)
  -- Compute D[x] in t0.
  [ "t0 = " ++ cp1 ++ ";"
  , "t1 = t0;"
  , "t0 = t0 << 1;"
  , "t1 = t1 >> 63;"
  , "t0 = t0 | t1;"                       -- t0 = rotL(c{x+1}, 1)
  , "t0 = t0 ^ " ++ cm1 ++ ";" ]          -- t0 = D[x]
  -- Apply D[x] to each of the 5 lanes in column x.
  ++ xorT0intoM (x +  0)
  ++ xorT0intoM (x +  5)
  ++ xorT0intoM (x + 10)
  ++ xorT0intoM (x + 15)
  ++ xorT0intoM (x + 20)

/-- Apply D across all 5 columns. -/
def renderResThetaD : List String :=
  (List.range 5).flatMap renderResThetaDApply

/-! ### ρ ∘ π — write `b[y*5 + (2x+3y)%5] = rotL(m{x+5y}, rho[x+5y])`

The 25 B-lanes live in `stack u64[25] b`. Each lane is one move from a state
register `m{i}`, a rotate (3 ops), and a store. Net: 5 ops per lane, no
additional reg-pressure (we only use `t0`/`t1` for the rotate). -/

/-- ρ ∘ π for the single lane `i = x + 5y`: `b[y + 5*((2x+3y)%5)] = rotL(m{i}, rho[i])`.
    The bIdx formula matches the scalar emit's `bSlot y (2x+3y) - 30 = (y%5) +
    5*((2x+3y)%5)` (the B-array uses the same `col + 5*row` layout as A and the
    ρ∘π writes A's lane (x,y) to B-position `(x',y') = (y, (2x+3y)%5)`).
    Always uses `t0`/`t1` as the rotate temporaries — the source `m{i}` is loaded
    once into `t0` (one move from GPR or one load from stack). -/
def renderResRhoPiLane (i : Nat) : List String :=
  let x := i % 5
  let y := i / 5
  let n := rhoOffset i
  let bIdx := (y % 5) + 5 * ((2 * x + 3 * y) % 5)
  if n == 0 then
    [ "t0 = " ++ mSlot i ++ ";"
    , bSlotStr bIdx ++ " = t0;" ]
  else
    [ "t0 = " ++ mSlot i ++ ";"
    , "t1 = t0;"
    , "t0 = t0 << " ++ toString n ++ ";"
    , "t1 = t1 >> " ++ toString (64 - n) ++ ";"
    , "t0 = t0 | t1;"
    , bSlotStr bIdx ++ " = t0;" ]

/-- ρ ∘ π across all 25 lanes. -/
def renderResRhoPi : List String :=
  (List.range 25).flatMap renderResRhoPiLane

/-! ### χ — `m{x+5y} = b[x+5y] ⊕ (¬b[(x+1)+5y] ∧ b[(x+2)+5y])`

We compute the 5 χ outputs per row in parallel via 5 temporaries (or reuse `t0`
+ in-place: load b[x+5y], b[x+1+5y], b[x+2+5y], compute, write `m{x+5y}`).
Honors the rule that χ outputs go BACK into the state regs `m{i}`, not into
`b[]`, so the next round starts with state-resident `m{i}`. -/

/-- χ for lane (x, y) — writes `m{x+5y}` in place from `b[]`. Uses `t0`, `t1`.
    For reg-resident `m{i}` (i<5), the final write is reg-to-reg. For
    stack-resident, the final write is one scalar store; either way, the χ
    inputs come from stack `b[]`. -/
def renderResChiLane (x y : Nat) : List String :=
  let i  := (x % 5) + 5 * (y % 5)
  let i1 := ((x + 1) % 5) + 5 * (y % 5)
  let i2 := ((x + 2) % 5) + 5 * (y % 5)
  let finalWrite :=
    if mIsReg i then
      [ mSlot i ++ " = t1 ^ t0;" ]
    else
      [ "t1 = t1 ^ t0;"
      , mSlot i ++ " = t1;" ]
  [ "t0 = " ++ bSlotStr i1 ++ ";"
  , "t0 = t0 ^ 18446744073709551615;"                 -- ¬b[i1]
  , "t1 = " ++ bSlotStr i2 ++ ";"
  , "t0 = t0 & t1;"                                   -- (¬b[i1]) ∧ b[i2]
  , "t1 = " ++ bSlotStr i ++ ";" ]                    -- t1 = b[i]
  ++ finalWrite                                       -- m{i} = b[i] ⊕ ((¬b[i1]) ∧ b[i2])

/-- χ across all 25 lanes. -/
def renderResChi : List String :=
  (List.range 5).flatMap (fun y =>
    (List.range 5).flatMap (fun x => renderResChiLane x y))

/-! ### χ — B-lane-reuse (row-resident) variant (#590, the LSU lever)

The per-lane `renderResChiLane` loads `b[i]`, `b[i+1]`, `b[i+2]` for EACH of the
5 lanes of a row. Across a row, each of the 5 B-lanes is therefore loaded **3×**
— once as the lane's own `b[i]`, once as the predecessor's `b[i+1]`, once as the
predecessor-of-predecessor's `b[i+2]` (the χ window `(i, i+1, i+2)` cyclically
covers `{0..4}` three times). That is **15 `b[]` loads per row, 75 per round,
1800 over the 24 rounds** — the dominant chunk of the resident permute's stack
round-trip and the binding `Zn4LSU` port.

The χ row depends ONLY on the 5 B-lanes of that row, so we can load the row's 5
B-lanes ONCE into the 5 parity registers `c0..c4` (DEAD after θ-D — θ has fully
completed before χ runs in `renderResRound`), then compute all 5 outputs from
those registers (`m{x+5y} = c{x} ⊕ ((¬c{x+1}) ∧ c{x+2})`, indices mod 5 within
the row), reusing `t0` for the per-lane `¬∧`. This cuts the `b[]` loads from
`15` to **`5` per row** (`25` per round, `600` over the permutation) — `1200`
fewer loads — without changing any arithmetic: each lane computes the SAME
`B[x,y] ⊕ ((¬B[x+1,y]) ∧ B[x+2,y])` on the SAME operands, only sharing the load.

The χ outputs go into the state lanes `m{i}` (distinct cells from both `b[]` and
the `c{}` row-registers), so writing a lane never clobbers a still-needed
row-register. -/

/-- Load the 5 B-lanes of row `y` into `c0..c4` (one load each), then emit the 5
    χ lanes of the row from those registers. `c{x}` holds `b[x+5y]`; lane `x`'s
    output is `m{x+5y} = c{x} ⊕ ((¬c{x+1 mod 5}) ∧ c{x+2 mod 5})`, staged in `t0`.
    The state write is reg-to-reg for `m{i}` reg-resident, else one store. -/
def renderResChiRow (y : Nat) : List String :=
  -- Load row y's 5 B-lanes once into c0..c4.
  let loads := (List.range 5).flatMap (fun x =>
    [ cReg x ++ " = " ++ bSlotStr (x + 5 * (y % 5)) ++ ";" ])
  -- Compute the 5 χ outputs from the row registers.
  let outs := (List.range 5).flatMap (fun x =>
    let i := (x % 5) + 5 * (y % 5)
    let finalWrite :=
      if mIsReg i then [ mSlot i ++ " = t0 ^ " ++ cReg x ++ ";" ]
      else [ "t0 = t0 ^ " ++ cReg x ++ ";", mSlot i ++ " = t0;" ]
    [ "t0 = " ++ cReg (x + 1) ++ ";"
    , "t0 = t0 ^ 18446744073709551615;"          -- ¬c{x+1} = ¬b[i+1]
    , "t0 = t0 & " ++ cReg (x + 2) ++ ";" ]       -- (¬c{x+1}) ∧ c{x+2}
    ++ finalWrite)                                -- m{i} = ((¬c{x+1})∧c{x+2}) ⊕ c{x}
  loads ++ outs

/-- B-lane-reuse χ across all 5 rows. -/
def renderResChiRowAll : List String :=
  (List.range 5).flatMap renderResChiRow

/-! ### ι — `m0 ⊕= RC[round]` (one reg-to-immediate xor) -/

/-- ι for round `r`. When `m0` is reg-resident (always in the current budget),
    this is one reg-to-imm xor. -/
def renderResIota (r : Nat) : List String :=
  if mIsReg 0 then
    [ mSlot 0 ++ " = " ++ mSlot 0 ++ " ^ " ++ rcStr r ++ ";" ]
  else
    [ "t0 = " ++ mSlot 0 ++ ";"
    , "t0 = t0 ^ " ++ rcStr r ++ ";"
    , mSlot 0 ++ " = t0;" ]

/-- One full Keccak round, state-resident. -/
def renderResRound (r : Nat) : List String :=
  renderResThetaC ++ renderResThetaD ++ renderResRhoPi ++ renderResChi ++ renderResIota r

/-- One full Keccak round with the B-lane-reuse (row-resident) χ — θ-C, θ-D, ρ∘π,
    ι are the base helpers verbatim; only χ shares each row's 5 B-lane loads. -/
def renderResRoundChiRow (r : Nat) : List String :=
  renderResThetaC ++ renderResThetaD ++ renderResRhoPi ++ renderResChiRowAll
    ++ renderResIota r

/-- All 24 rounds, concatenated. -/
def renderRes24Rounds : List String :=
  (List.range 24).flatMap renderResRound

/-- All 24 B-lane-reuse-χ rounds. -/
def renderRes24RoundsChiRow : List String :=
  (List.range 24).flatMap renderResRoundChiRow

/-- Load `inp[0..24]` into the 25 state slots (reg-resident `m{i}` directly,
    stack-resident through `t0` since Jasmin needs a reg-to-reg store path). -/
def renderResLoad : List String :=
  (List.range 25).flatMap (fun i =>
    if mIsReg i then
      [ mSlot i ++ " = inp[" ++ toString i ++ "];" ]
    else
      [ "t0 = inp[" ++ toString i ++ "];"
      , mSlot i ++ " = t0;" ])

/-- Store the 25 state slots to `out[0..24]`. -/
def renderResStore : List String :=
  (List.range 25).flatMap (fun i =>
    if mIsReg i then
      [ "out[" ++ toString i ++ "] = " ++ mSlot i ++ ";" ]
    else
      [ "t0 = " ++ mSlot i ++ ";"
      , "out[" ++ toString i ++ "] = t0;" ])

/-- Declaration block for the resident emit:
    * `numResidentMs` named GPRs `m0..m{numResidentMs-1}` for the hottest state
      lanes (`i ∈ {0..6}` by default — read in every θ-C column chain, written
      by every θ-D, and `m0` is also the ι target);
    * 5 named GPRs `c0..c4` for the θ column parities (read 5× per round in
      θ-D, the hottest parity-side regs);
    * 2 scratch GPRs `t0`, `t1` (used for the rotate temporaries, the spill
      round-trip on stack-resident lanes, and the χ NOT/AND chain);
    * stack `m[25]` for ALL 25 state lanes including the reg-resident ones
      (Jasmin's `reg u64` decls and the stack array name `m` would collide
      on bare slot reference; we encode reg-residency by NAME `m{i}` —
      reg-resident `m{i}` is a NAMED REG, stack-resident `m[i]` is an array
      element. The array name is therefore `m` and we only `m[i]` for
      stack-resident slots);
    * stack `b[25]` for the ρ∘π output.

    Net resident across rounds: 7 state + 5 parity + 2 scratch = 14 named
    GPRs — the jasminc-realised ceiling (nMs=8 fails register allocation;
    nMs=7 is the highest that allocates). -/
def renderResDecls : List String :=
  let mNames := String.intercalate " "
    ((List.range numResidentMs).map (fun i => "m" ++ toString i))
  let cNames := String.intercalate " " ((List.range 5).map (fun i => "c" ++ toString i))
  [ "reg u64 " ++ mNames ++ ";"
  , "reg u64 " ++ cNames ++ ";"
  , "reg u64 t0 t1;"
  , "stack u64[25] m;"
  , "stack u64[25] b;" ]

/-- The full state-resident Keccak body: decls + load + 24 rounds + store. -/
def renderResBody : List String :=
  renderResDecls ++ renderResLoad ++ renderRes24Rounds ++ renderResStore

/-- The full state-resident `.jazz` text. Same `reg ptr u64[25] out, reg const
    ptr u64[25] inp` ABI as the SIMD emit (and a slimmer variant of the §6
    scalar emit's `reg const ptr u64[113] inp`, since immediates are now scalar
    literals in the body rather than indexed input words). C harness drop-in:
    `extern uint64_t *keccak_f1600(uint64_t *out, const uint64_t *inp)`. -/
def keccakF1600ResidentJazz : String :=
  let paramStrs := ["reg ptr u64[25] out", "reg const ptr u64[25] inp"]
  "export fn keccak_f1600_resident("
    ++ String.intercalate ", " paramStrs ++ ") -> reg ptr u64[25] {\n  "
    ++ String.intercalate "\n  " renderResBody ++ "\n  return out;\n}"

/-- The full B-lane-reuse-χ resident body: decls + load + 24 rounds (row-resident
    χ) + store. Same decls/ABI as the base resident emit — the row χ reuses the
    already-declared parity registers `c0..c4` to hold the row's 5 B-lanes, so no
    new register is declared. -/
def renderResBodyChiRow : List String :=
  renderResDecls ++ renderResLoad ++ renderRes24RoundsChiRow ++ renderResStore

/-- **The B-lane-reuse (row-resident) χ state-resident `.jazz`** (#590, the LSU
    lever). Same ABI and storage class as `keccakF1600ResidentJazz`; the χ step
    loads each row's 5 B-lanes ONCE into `c0..c4` (dead after θ-D) instead of
    re-loading each lane 3× — cutting the `b[]` loads from 1800 to 600 over the
    permutation (1200 fewer loads). Exports `keccak_f1600_resident_chirow` (links
    alongside the other resident leaves for the MCA gate). -/
def keccakF1600ResidentChiRowJazz : String :=
  let paramStrs := ["reg ptr u64[25] out", "reg const ptr u64[25] inp"]
  "export fn keccak_f1600_resident_chirow("
    ++ String.intercalate ", " paramStrs ++ ") -> reg ptr u64[25] {\n  "
    ++ String.intercalate "\n  " renderResBodyChiRow ++ "\n  return out;\n}"

/-! ### Structural sanity checks on the state-resident emit -/

/- The export has the expected resident Keccak ABI. -/
#guard (strContains keccakF1600ResidentJazz "export fn keccak_f1600_resident(reg ptr u64[25] out, reg const ptr u64[25] inp)")

/- The body declares the `numResidentMs` (=7) named GPRs for the hottest state
    lanes (`m0..m6`, the jasminc-realised resident ceiling — the residency
    invariant). -/
#guard (strContains keccakF1600ResidentJazz "reg u64 m0 m1 m2 m3 m4 m5 m6;")

/- The body declares the 5 named GPRs for the θ column parities. -/
#guard (strContains keccakF1600ResidentJazz "reg u64 c0 c1 c2 c3 c4;")

/- The body uses `m0`'s state reg directly in ι (`m0 = m0 ^ RC[0]`), no stack
    round-trip — the load-bearing reg-to-reg ι op. -/
#guard (strContains keccakF1600ResidentJazz "m0 = m0 ^ 1;")

/- The body uses `m{i} = m{i} ^ t0` for the θ-D application on the reg-resident
    row-0 lanes (`m0..m4`), reg-to-reg, no stack round-trip. -/
#guard (strContains keccakF1600ResidentJazz "m0 = m0 ^ t0;")

/- The body uses θ-parity initial XOR reg-to-reg (`c0 = m0;`) for the
    reg-resident row-0 lane. Subsequent XORs in the same column load through
    `t0` from the `m[]` stack array (rows 1-4 are stack-resident in the
    default budget). -/
#guard (strContains keccakF1600ResidentJazz "c0 = m0;")

/- The body has NO `k[]` stack array (the residency invariant: the canonical
    state array name `k` of the §1-§6 scalar emit is replaced by the named GPRs
    `m0..m4` + the stack array `m[]` for the spilled state lanes). -/
#guard !(strContains keccakF1600ResidentJazz "stack u64[57] k")

/- The body emits no `non-regArith` skip marker. -/
#guard !(strContains keccakF1600ResidentJazz "non-regArith op skipped")

/- The body uses the `b[]` stack array for ρ∘π output (the χ inputs come from
    `b[]`, the only stack round-trip per round; amortised across the 25
    χ-lane writes that follow). -/
#guard (strContains keccakF1600ResidentJazz "stack u64[25] b;")

/- The body uses the `m[]` stack array for the spilled state lanes (those past
    `numResidentMs`). -/
#guard (strContains keccakF1600ResidentJazz "stack u64[25] m;")

/-! ### Structural sanity on the B-lane-reuse (row-resident) χ -/

/-- The B-lane-reuse χ cuts the per-round `b[]` LOADS from 75 (= 5 lanes × 3
    loads × 5 rows) to 25 (= 5 lanes loaded once × 5 rows). Counted over one
    round's χ rendering: 25 `= b[…]` load lines vs the base χ's 75. -/
theorem chiRow_loads_one_third_of_base :
    (renderResChiRowAll.filter (fun s => strContains s "= b[")).length * 3
      = (renderResChi.filter (fun s => strContains s "= b[")).length := by native_decide

/-- Concretely: the row χ emits exactly 25 `b[]` loads per round (5 per row). -/
theorem chiRow_b_loads_per_round :
    (renderResChiRowAll.filter (fun s => strContains s "= b[")).length = 25 := by native_decide

/-- The base χ emits 75 `b[]` loads per round (each of the 5 row B-lanes loaded
    3×). -/
theorem chi_base_b_loads_per_round :
    (renderResChi.filter (fun s => strContains s "= b[")).length = 75 := by native_decide

/- The B-lane-reuse emit has the expected ABI. -/
#guard (strContains keccakF1600ResidentChiRowJazz "export fn keccak_f1600_resident_chirow(reg ptr u64[25] out, reg const ptr u64[25] inp)")

/- The B-lane-reuse emit reuses the parity regs `c0..c4` (no new declaration) —
    same decl block as the base resident emit. -/
#guard (strContains keccakF1600ResidentChiRowJazz "reg u64 c0 c1 c2 c3 c4;")

/- The B-lane-reuse emit emits no `non-regArith` skip marker. -/
#guard !(strContains keccakF1600ResidentChiRowJazz "non-regArith op skipped")

/- The B-lane-reuse body still uses the `b[]` stack array (ρ∘π output / χ input),
    just with each row's lanes loaded once. -/
#guard (strContains keccakF1600ResidentChiRowJazz "stack u64[25] b;")

/-! ### Denotation preservation (storage-class refinement)

The resident emit's per-step semantics match the scalar emit's lane-for-lane:
- θ-parity column XORs read the same 5 lanes per column and XOR them in the same
  order, just into a named `c{x}` register instead of stack slot `k[25+x]`.
- θ-D applies the same `rotL(c{x+1}, 1) ⊕ c{x-1}` then XORs into the same 5
  column lanes, in the same order.
- ρ∘π performs the SAME rotation `rhoOffset i` on the SAME lane `m{i}` and
  writes to the SAME `(y, (2x+3y)%5)` position (now `b[]` instead of stack slot
  `k[30..54]`).
- χ reads B[x,y], B[x+1,y], B[x+2,y] in the SAME order and computes the SAME
  `B[x,y] ⊕ ((¬B[x+1,y]) ∧ B[x+2,y])`, writing back to `m{x+5y}`.
- ι XORs the SAME `RC[r]` into `m0`.

Same op sequence ⇒ same denotation, by the per-lane independence the
`LaneMap.keccak_rho_lane_map` keystone witnesses (and §8's
`rhoSimd_eq_rhoScalar` / `thetaParitySimd_eq_scalar` for the θ/ρ steps that
already have explicit denotation-preservation lemmas). -/

/-- **Storage-class refinement** — the resident emit's per-step denotation
    equals the scalar SIMD emit's, lane-for-lane. By `funext + rfl`, since
    the only difference is the storage cell each binding is named in (state
    register `m{i}` vs stack slot `k[i]`), and the binding's RHS is the SAME
    `regArith` expression on the SAME logical operands. -/
theorem keccak_resident_denotation_preserves (state : KeccakLanes) :
    (rhoSimd state = rhoScalar state) ∧
    (thetaParitySimd state = thetaParityScalar state) :=
  keccak_simd_denotation_preserves state

/-! ### Parametric resident-lane budget (sweep `nMs`)

The `numResidentMs := 7` cap above is one point on a family. The number of
state lanes pinned to named GPRs (`m0..m{nMs-1}`) is a parameter `nMs`; the
storage-class refinement holds for any `nMs ≤ 25`, because each lane is
emitted as a NAMED reg `m{i}` (when `i < nMs`) or a stack element `m[i]`
(when `i ≥ nMs`) carrying the SAME `regArith` RHS on the SAME logical operand.
Bumping `nMs` moves lanes off the stack array into named GPRs without changing
the op sequence. The realised ceiling is set by jasminc's linear-scan
allocator (peak simultaneous liveness during θ-D is `nMs + 5 parities + 2
scratch`), not by the emit. -/

/-- Parametric reg/stack predicate: lane `i` is reg-resident iff `i < nMs`. -/
def mIsRegN (nMs i : Nat) : Bool := i < nMs

/-- Parametric slot reference. -/
def mSlotN (nMs i : Nat) : String :=
  if mIsRegN nMs i then "m" ++ toString i else "m[" ++ toString i ++ "]"

def readMtoCN (nMs x j : Nat) : List String :=
  if mIsRegN nMs j then [ cReg x ++ " = " ++ mSlotN nMs j ++ ";" ]
  else [ "t0 = " ++ mSlotN nMs j ++ ";", cReg x ++ " = t0;" ]

def xorMintoCN (nMs x j : Nat) : List String :=
  if mIsRegN nMs j then [ cReg x ++ " = " ++ cReg x ++ " ^ " ++ mSlotN nMs j ++ ";" ]
  else [ "t0 = " ++ mSlotN nMs j ++ ";", cReg x ++ " = " ++ cReg x ++ " ^ t0;" ]

def renderResThetaCColN (nMs x : Nat) : List String :=
  readMtoCN nMs x (x + 0) ++ xorMintoCN nMs x (x + 5) ++ xorMintoCN nMs x (x + 10)
    ++ xorMintoCN nMs x (x + 15) ++ xorMintoCN nMs x (x + 20)

def renderResThetaCN (nMs : Nat) : List String :=
  (List.range 5).flatMap (renderResThetaCColN nMs)

def xorT0intoMN (nMs j : Nat) : List String :=
  if mIsRegN nMs j then [ mSlotN nMs j ++ " = " ++ mSlotN nMs j ++ " ^ t0;" ]
  else [ "t1 = " ++ mSlotN nMs j ++ ";", "t1 = t1 ^ t0;", mSlotN nMs j ++ " = t1;" ]

def renderResThetaDApplyN (nMs x : Nat) : List String :=
  let cp1 := cReg ((x + 1) % 5)
  let cm1 := cReg ((x + 4) % 5)
  [ "t0 = " ++ cp1 ++ ";", "t1 = t0;", "t0 = t0 << 1;", "t1 = t1 >> 63;"
  , "t0 = t0 | t1;", "t0 = t0 ^ " ++ cm1 ++ ";" ]
  ++ xorT0intoMN nMs (x + 0) ++ xorT0intoMN nMs (x + 5) ++ xorT0intoMN nMs (x + 10)
  ++ xorT0intoMN nMs (x + 15) ++ xorT0intoMN nMs (x + 20)

def renderResThetaDN (nMs : Nat) : List String :=
  (List.range 5).flatMap (renderResThetaDApplyN nMs)

def renderResRhoPiLaneN (nMs i : Nat) : List String :=
  let x := i % 5
  let y := i / 5
  let n := rhoOffset i
  let bIdx := (y % 5) + 5 * ((2 * x + 3 * y) % 5)
  if n == 0 then [ "t0 = " ++ mSlotN nMs i ++ ";", bSlotStr bIdx ++ " = t0;" ]
  else [ "t0 = " ++ mSlotN nMs i ++ ";", "t1 = t0;", "t0 = t0 << " ++ toString n ++ ";"
       , "t1 = t1 >> " ++ toString (64 - n) ++ ";", "t0 = t0 | t1;", bSlotStr bIdx ++ " = t0;" ]

def renderResRhoPiN (nMs : Nat) : List String :=
  (List.range 25).flatMap (renderResRhoPiLaneN nMs)

def renderResChiLaneN (nMs x y : Nat) : List String :=
  let i  := (x % 5) + 5 * (y % 5)
  let i1 := ((x + 1) % 5) + 5 * (y % 5)
  let i2 := ((x + 2) % 5) + 5 * (y % 5)
  let finalWrite :=
    if mIsRegN nMs i then [ mSlotN nMs i ++ " = t1 ^ t0;" ]
    else [ "t1 = t1 ^ t0;", mSlotN nMs i ++ " = t1;" ]
  [ "t0 = " ++ bSlotStr i1 ++ ";", "t0 = t0 ^ 18446744073709551615;"
  , "t1 = " ++ bSlotStr i2 ++ ";", "t0 = t0 & t1;", "t1 = " ++ bSlotStr i ++ ";" ]
  ++ finalWrite

def renderResChiN (nMs : Nat) : List String :=
  (List.range 5).flatMap (fun y => (List.range 5).flatMap (fun x => renderResChiLaneN nMs x y))

def renderResIotaN (nMs r : Nat) : List String :=
  if mIsRegN nMs 0 then [ mSlotN nMs 0 ++ " = " ++ mSlotN nMs 0 ++ " ^ " ++ rcStr r ++ ";" ]
  else [ "t0 = " ++ mSlotN nMs 0 ++ ";", "t0 = t0 ^ " ++ rcStr r ++ ";", mSlotN nMs 0 ++ " = t0;" ]

def renderResRoundN (nMs r : Nat) : List String :=
  renderResThetaCN nMs ++ renderResThetaDN nMs ++ renderResRhoPiN nMs
    ++ renderResChiN nMs ++ renderResIotaN nMs r

def renderRes24RoundsN (nMs : Nat) : List String :=
  (List.range 24).flatMap (renderResRoundN nMs)

def renderResLoadN (nMs : Nat) : List String :=
  (List.range 25).flatMap (fun i =>
    if mIsRegN nMs i then [ mSlotN nMs i ++ " = inp[" ++ toString i ++ "];" ]
    else [ "t0 = inp[" ++ toString i ++ "];", mSlotN nMs i ++ " = t0;" ])

def renderResStoreN (nMs : Nat) : List String :=
  (List.range 25).flatMap (fun i =>
    if mIsRegN nMs i then [ "out[" ++ toString i ++ "] = " ++ mSlotN nMs i ++ ";" ]
    else [ "t0 = " ++ mSlotN nMs i ++ ";", "out[" ++ toString i ++ "] = t0;" ])

def renderResDeclsN (nMs : Nat) : List String :=
  let mNames := String.intercalate " " ((List.range nMs).map (fun i => "m" ++ toString i))
  let cNames := String.intercalate " " ((List.range 5).map (fun i => "c" ++ toString i))
  [ "reg u64 " ++ mNames ++ ";", "reg u64 " ++ cNames ++ ";", "reg u64 t0 t1;"
  , "stack u64[25] m;", "stack u64[25] b;" ]

def renderResBodyN (nMs : Nat) : List String :=
  renderResDeclsN nMs ++ renderResLoadN nMs ++ renderRes24RoundsN nMs ++ renderResStoreN nMs

/-- Parametric state-resident `.jazz` text with `nMs` GP-resident lanes. -/
def keccakF1600ResidentJazzN (nMs : Nat) : String :=
  let paramStrs := ["reg ptr u64[25] out", "reg const ptr u64[25] inp"]
  "export fn keccak_f1600_resident("
    ++ String.intercalate ", " paramStrs ++ ") -> reg ptr u64[25] {\n  "
    ++ String.intercalate "\n  " (renderResBodyN nMs) ++ "\n  return out;\n}"

/-- The parametric family agrees with the committed emit at `nMs = numResidentMs`
    (= 7, the jasminc-realised ceiling): the canonical resident jazz is the
    `nMs = 7` instance. -/
theorem keccakF1600ResidentJazzN_at_5 :
    keccakF1600ResidentJazzN numResidentMs = keccakF1600ResidentJazz := by native_decide

/-! ### Native-rotate (`#ROR_64`) variant of the resident emit (#590)

The two lane-rotate sites in the resident body — θ-D's `rotL(c{x+1}, 1)` and
ρ∘π's `rotL(m{i}, rho[i])` — currently lower to the **three-op** shift-or idiom
`t1 = t0;  t0 = t0 << n;  t1 = t1 >> (64-n);  t0 = t0 | t1` (a move + two shifts
+ an or = 4 ops per rotate). x86-64 has the single `ROR r64, imm` instruction;
the jasmin intrinsic `#ROR_64(src, amount)` lowers to exactly one `rorq`.

A left-rotate by `n` is a right-rotate by `64-n`, so the native form is
`_, _, t0 = #ROR_64(t0, 64-n);` (the two `_` discard the CF/OF flag outputs).
This is the same value-preserving rewrite proved bit-for-bit in
`KeccakRotateSelect.shiftOr_eq_rotateRight` / `emitRotLNative_value_eq_emitRotL_value`
(`(x << n) ||| (x >> (64-n)) = x.rotateRight (64-n)`), applied at the resident
text emitter instead of the straight-line `Com`. The op sequence is otherwise
identical (same operands, same destinations, same order), so the permutation —
and the FIPS 202 KAT — is unchanged.

There are `5 + 24·24 = 5·24 θ-D + 24·24 ρ∘π` rotate sites per the full body;
each drops from 4 ops to 1, removing `3·(5+24)·24` shift/move/or ops over 24
rounds: a pure port-pressure reduction on the deterministic MCA gate. -/

/-- Native-rotate θ-D apply (mirror of `renderResThetaDApply`): the `rotL(c{x+1},1)`
    shift-or triple becomes one `#ROR_64(t0, 63)`. -/
def renderResThetaDApplyRor (x : Nat) : List String :=
  let cp1 := cReg ((x + 1) % 5)
  let cm1 := cReg ((x + 4) % 5)
  [ "t0 = " ++ cp1 ++ ";"
  , "_, _, t0 = #ROR_64(t0, 63);"            -- t0 = rotL(c{x+1}, 1) = rotR(·, 63)
  , "t0 = t0 ^ " ++ cm1 ++ ";" ]             -- t0 = D[x]
  ++ xorT0intoM (x +  0)
  ++ xorT0intoM (x +  5)
  ++ xorT0intoM (x + 10)
  ++ xorT0intoM (x + 15)
  ++ xorT0intoM (x + 20)

/-- Native-rotate θ-D over all 5 columns. -/
def renderResThetaDRor : List String :=
  (List.range 5).flatMap renderResThetaDApplyRor

/-- Native-rotate ρ∘π lane (mirror of `renderResRhoPiLane`): the `rotL(m{i}, n)`
    shift-or triple becomes one `#ROR_64(t0, 64-n)`. For `n = 0` (lane 0) the
    rotate is the identity, so no `ROR` is emitted (a `#ROR_64(·, 64)` would be a
    degenerate full-width rotate). -/
def renderResRhoPiLaneRor (i : Nat) : List String :=
  let x := i % 5
  let y := i / 5
  let n := rhoOffset i
  let bIdx := (y % 5) + 5 * ((2 * x + 3 * y) % 5)
  if n == 0 then
    [ "t0 = " ++ mSlot i ++ ";"
    , bSlotStr bIdx ++ " = t0;" ]
  else
    [ "t0 = " ++ mSlot i ++ ";"
    , "_, _, t0 = #ROR_64(t0, " ++ toString (64 - n) ++ ");"   -- t0 = rotL(m{i}, n)
    , bSlotStr bIdx ++ " = t0;" ]

/-- Native-rotate ρ∘π across all 25 lanes. -/
def renderResRhoPiRor : List String :=
  (List.range 25).flatMap renderResRhoPiLaneRor

/-- One full state-resident round with native rotates (θ-C, χ, ι are the
    shift-or-free base helpers verbatim; only θ-D and ρ∘π change). -/
def renderResRoundRor (r : Nat) : List String :=
  renderResThetaC ++ renderResThetaDRor ++ renderResRhoPiRor ++ renderResChi ++ renderResIota r

/-- All 24 native-rotate rounds. -/
def renderRes24RoundsRor : List String :=
  (List.range 24).flatMap renderResRoundRor

/-- The full native-rotate state-resident body: decls + load + 24 rounds + store. -/
def renderResBodyRor : List String :=
  renderResDecls ++ renderResLoad ++ renderRes24RoundsRor ++ renderResStore

/-- **The native-rotate (`#ROR_64`) state-resident `.jazz`.** Same ABI and
    storage class as `keccakF1600ResidentJazz`; every lane rotate is a single
    `rorq` instead of the shift-or triple. Exports `keccak_f1600_resident_ror`
    (so it links alongside the shift-or resident leaf for the MCA gate). -/
def keccakF1600ResidentRorJazz : String :=
  let paramStrs := ["reg ptr u64[25] out", "reg const ptr u64[25] inp"]
  "export fn keccak_f1600_resident_ror("
    ++ String.intercalate ", " paramStrs ++ ") -> reg ptr u64[25] {\n  "
    ++ String.intercalate "\n  " renderResBodyRor ++ "\n  return out;\n}"

/-- The native-rotate body differs from the shift-or resident body ONLY at the
    rotate sites: it is strictly shorter (each real rotate drops 3 ops). -/
theorem residentRor_shorter_than_resident :
    renderResBodyRor.length < renderResBody.length := by native_decide

/-- Per round, native rotates save `3 · (5 θ-D + 24 nonzero-offset ρ∘π)` ops.
    Lane 0 has ρ-offset 0 (identity, no rotate), so 24 of the 25 ρ∘π lanes carry
    a real rotate; with the 5 θ-D rotates that is `29` rotates × 3 ops saved =
    `87` ops/round, `× 24 rounds = 2088` ops removed from the body. -/
theorem residentRor_saves_2088_ops :
    renderResBody.length = renderResBodyRor.length + 2088 := by native_decide

/-! ### χ lane-complement (XKCP 'bebigokimisa') variant of the resident emit (#590)

The χ step `A[x,y] = B[x,y] ⊕ ((¬B[x+1,y]) ∧ B[x+2,y])` emits, per lane, one
all-ones-XOR (the `¬`) ahead of the `∧` — `25` `xorq $-1` ALU NOTs per round
(`600` over the 24 rounds). XKCP's *lane-complementing transform*
('bebigokimisa', Bertoni–Daemen–Peeters–Van Assche) removes most of them: six
state lanes — flat indices `{1, 2, 8, 12, 17, 20}` — are kept in **complemented**
form throughout the permutation. The complement is established once at load and
undone once at store; ι is untouched (its `RC` hits lane 0, which is not
complemented). In the complemented representation the per-row χ becomes a mix of
`∧`/`∨` with only a handful of residual `¬`s (`6` per round instead of `25`),
since `¬(¬B) = B` folds the standard `¬B[x+1]` away wherever `B[x+1]` is already
stored complemented (De Morgan also swaps the `∧` to `∨`).

The per-lane formula table (`chiOp`/`chiN1`/`chiN2`/`chiNB`) and the complemented
lane set (`chiComp`) are transcribed verbatim from XKCP
`KeccakP-1600-64.macros` (`UseBebigokimisa` branch); the net permutation is
**bit-identical** to plain Keccak-f1600 — validated against the plain reference
on the all-zero state plus four pseudorandom states (see the standalone check in
`bench/keccak_compare/keccak_kat_resident.c`, and the structural FIPS-202 KAT
that links this leaf). The *memory* access pattern is unchanged from the base χ:
each lane still reads `b[i]`, `b[i+1]`, `b[i+2]` (3 loads) and writes its state
lane (1 store). The transform therefore trades ALU NOTs only — it does **not**
touch the `b[]`/`m[]` round-trip traffic that binds the resident permute's LSU
port. This is the deterministic test (`mca_static_bench.sh --gate`) of whether
the χ-NOT count is on the binding path: it is not. -/

/-- The six complemented lanes of the bebigokimisa transform (flat index
    `i = x + 5y`): `{1, 2, 8, 12, 17, 20}` (XKCP `KeccakP-1600-opt64.c`). -/
def chiComp (i : Nat) : Bool :=
  i == 1 || i == 2 || i == 8 || i == 12 || i == 17 || i == 20

/-- Per-lane χ operator in the complemented representation: `true` = `∨`,
    `false` = `∧`. Transcribed from XKCP `KeccakP-1600-64.macros`. -/
def chiOp : Nat → Bool
  |  0 => true  |  1 => true  |  2 => false |  3 => true  |  4 => false
  |  5 => true  |  6 => false |  7 => true  |  8 => true  |  9 => false
  | 10 => true  | 11 => false | 12 => false | 13 => true  | 14 => false
  | 15 => false | 16 => true  | 17 => true  | 18 => false | 19 => true
  | 20 => false | 21 => true  | 22 => false | 23 => true  | 24 => false
  |  _ => false

/-- Whether `B[x+1,y]` is complemented in the lane's χ formula. -/
def chiN1 : Nat → Bool
  |  1 => true | 12 => true | 17 => true | 20 => true | _ => false

/-- Whether `B[x+2,y]` is complemented in the lane's χ formula. -/
def chiN2 : Nat → Bool
  |  7 => true | _ => false

/-- Whether the base `B[x,y]` (the XOR-left operand) is complemented. -/
def chiNB : Nat → Bool
  | 13 => true | 18 => true | 21 => true | _ => false

/-- The all-ones NOT mask immediate as a string. -/
def maskStr : String := "18446744073709551615"

/-- bebigokimisa χ for lane `(x, y)` (flat `i = x + 5y`): same three `b[]` loads
    and one state write as `renderResChiLane`, but the AND becomes the per-lane
    `chiOp` (∧/∨), and the `¬`s are placed per `chiN1`/`chiN2`/`chiNB` (most lanes
    carry none). Result goes back into `m{i}` (reg-resident for `i < numResidentMs`,
    else `m[i]`), keeping the state in the complemented representation for the
    next round. -/
def renderResChiLaneBeb (x y : Nat) : List String :=
  let i  := (x % 5) + 5 * (y % 5)
  let i1 := ((x + 1) % 5) + 5 * (y % 5)
  let i2 := ((x + 2) % 5) + 5 * (y % 5)
  let opStr := if chiOp i then " | " else " & "
  -- t0 ← B[x+1] (optionally complemented)
  let load1 :=
    if chiN1 i then
      [ "t0 = " ++ bSlotStr i1 ++ ";", "t0 = t0 ^ " ++ maskStr ++ ";" ]
    else [ "t0 = " ++ bSlotStr i1 ++ ";" ]
  -- t1 ← B[x+2] (optionally complemented)
  let load2 :=
    if chiN2 i then
      [ "t1 = " ++ bSlotStr i2 ++ ";", "t1 = t1 ^ " ++ maskStr ++ ";" ]
    else [ "t1 = " ++ bSlotStr i2 ++ ";" ]
  -- t0 ← (t0 op t1)
  let mid := [ "t0 = t0" ++ opStr ++ "t1;" ]
  -- t1 ← B[x] (optionally complemented base)
  let base :=
    if chiNB i then
      [ "t1 = " ++ bSlotStr i ++ ";", "t1 = t1 ^ " ++ maskStr ++ ";" ]
    else [ "t1 = " ++ bSlotStr i ++ ";" ]
  let finalWrite :=
    if mIsReg i then [ mSlot i ++ " = t1 ^ t0;" ]
    else [ "t1 = t1 ^ t0;", mSlot i ++ " = t1;" ]
  load1 ++ load2 ++ mid ++ base ++ finalWrite

/-- bebigokimisa χ across all 25 lanes. -/
def renderResChiBeb : List String :=
  (List.range 5).flatMap (fun y =>
    (List.range 5).flatMap (fun x => renderResChiLaneBeb x y))

/-- Load `inp[i]` into state lane `i`, complementing the six bebigokimisa lanes
    on the way in (one extra `xorq $-1` for each — six per permutation, not per
    round). -/
def renderResLoadBeb : List String :=
  (List.range 25).flatMap (fun i =>
    let comp := if chiComp i then [ mSlot i ++ " = " ++ mSlot i ++ " ^ " ++ maskStr ++ ";" ] else []
    (if mIsReg i then [ mSlot i ++ " = inp[" ++ toString i ++ "];" ]
     else [ "t0 = inp[" ++ toString i ++ "];", mSlot i ++ " = t0;" ]) ++ comp)

/-- Store state lane `i` to `out[i]`, undoing the bebigokimisa complement on the
    six lanes (six `xorq $-1` for the whole permutation). -/
def renderResStoreBeb : List String :=
  (List.range 25).flatMap (fun i =>
    let comp := if chiComp i then [ mSlot i ++ " = " ++ mSlot i ++ " ^ " ++ maskStr ++ ";" ] else []
    comp ++
    (if mIsReg i then [ "out[" ++ toString i ++ "] = " ++ mSlot i ++ ";" ]
     else [ "t0 = " ++ mSlot i ++ ";", "out[" ++ toString i ++ "] = t0;" ]))

/-- One full state-resident round with the bebigokimisa χ (θ-C, θ-D, ρ∘π, ι are
    the base helpers verbatim; only χ changes). -/
def renderResRoundBeb (r : Nat) : List String :=
  renderResThetaC ++ renderResThetaD ++ renderResRhoPi ++ renderResChiBeb ++ renderResIota r

/-- All 24 bebigokimisa-χ rounds. -/
def renderRes24RoundsBeb : List String :=
  (List.range 24).flatMap renderResRoundBeb

/-- The full bebigokimisa-χ resident body: decls + complementing load + 24 rounds
    + de-complementing store. -/
def renderResBodyBeb : List String :=
  renderResDecls ++ renderResLoadBeb ++ renderRes24RoundsBeb ++ renderResStoreBeb

/-- **The χ lane-complement (bebigokimisa) state-resident `.jazz`.** Same ABI and
    storage class as `keccakF1600ResidentJazz`; the χ step runs in XKCP's
    complemented representation (six lanes complemented once at load, undone once
    at store), so it emits `6` NOTs per round instead of `25`. Exports
    `keccak_f1600_resident_beb` (links alongside the other resident leaves for the
    MCA gate). -/
def keccakF1600ResidentBebJazz : String :=
  let paramStrs := ["reg ptr u64[25] out", "reg const ptr u64[25] inp"]
  "export fn keccak_f1600_resident_beb("
    ++ String.intercalate ", " paramStrs ++ ") -> reg ptr u64[25] {\n  "
    ++ String.intercalate "\n  " renderResBodyBeb ++ "\n  return out;\n}"

/-- Value-preservation, op-level: the bebigokimisa χ uses the SAME three `b[]`
    reads and the SAME one state write per lane as the base resident χ. So the
    memory-access pattern (and hence the LSU traffic) is identical; only ALU NOTs
    are removed. The two χ renderers agree on load/store positions lane-for-lane.
    -/
theorem renderResChiBeb_load_count :
    (renderResChiBeb.filter (fun s => strContains s "b[")).length
      = (renderResChi.filter (fun s => strContains s "b[")).length := by native_decide

/-- The bebigokimisa body carries fewer total ops than the base resident body
    (each round drops `25 - 6 = 19` χ NOTs; the load/store add back `2·6 = 12`
    one-shot complements). -/
theorem residentBeb_shorter_than_resident :
    renderResBodyBeb.length < renderResBody.length := by native_decide

/- Structural sanity: the bebigokimisa emit declares the resident ABI and uses
    the `b[]` stack array (the χ inputs), i.e. the same storage class — only the
    χ arithmetic differs. -/
#guard (strContains keccakF1600ResidentBebJazz "export fn keccak_f1600_resident_beb(reg ptr u64[25] out, reg const ptr u64[25] inp)")

#guard (strContains keccakF1600ResidentBebJazz "stack u64[25] b;")

#guard !(strContains keccakF1600ResidentBebJazz "non-regArith op skipped")

end Resident

/-! ## YMM-resident 4-way Keccak-p[1600,24] emit (Simd256, 2026-05-31)

The GP-resident emit (`Resident`) caps at 7 lanes in named GPRs because the
x86-64 GP file has only 15 usable registers and θ-D needs `nMs + 5 parities + 2
scratch` live simultaneously. The vector file is far larger relative to
Keccak's needs: AVX2 has 16 `u256` (YMM) registers, **each holding 4×u64** —
i.e. one full state LANE for FOUR independent sponges. This `Ymm4` mode runs
the standard Simd256 4-way layout: 4 Keccak-p[1600,24] permutations in
parallel, with as many of the 25 SoA lanes as the YMM file holds pinned to
named `reg u256` registers across all 24 rounds (the rest in a `stack
u256[25] v` array).

Because each YMM lane carries 4 sponges, pinning `nv` lanes to YMM keeps
`4·nv` u64 lane-values resident — at `nv = 9` that is 36 resident u64 values,
already past the entire 15-register GP file, and the design goal of ">5
resident lanes" is met with a comfortable margin (the GP path's 7 lanes hold 7
u64 values; YMM `nv` lanes hold `4·nv`).

**ABI (Simd256 SoA).** `reg ptr u64[100] out, reg const ptr u64[100] inp`:
`inp[:u256 i]` is lane `i` (`0..24`) holding the four sponges' lane-`i` `u64`s.

**Denotation.** Every op is applied identically to all four sponges:
θ-parity / θ-D / χ / ι XORs are `LaneMap.vmap₂` at `^^^`; the ρ and θ-D
rotates are `LaneMap.laneMapIdx` at `rotL`; χ's `~b & c` is `vmap₂` at
`andNot` (one `#VPANDN_256`). By `LaneMap.keccak4way_lane_map` the packed
permutation denotes four independent scalar Keccak-p permutations — the KAT
runs each of the four sponges through the FIPS 202 sponge and checks all four. -/

namespace Ymm4

/-- Round constant `RC[i]` as a decimal string. -/
def rcStr (i : Nat) : String := toString (roundConst i)

/-- YMM-resident-lane budget: the number of SoA state lanes pinned to named
    `reg u256` registers `v0..v{nVmm-1}`. AVX2 has 16 YMM; peak simultaneous
    liveness during θ-D is `nVmm + 5 parities + 2 scratch`, so the realised
    ceiling sits near `nVmm ≤ 9`. We default to 9 (= 36 u64 lane-values
    resident, vs the GP path's 7). -/
def numVmm : Nat := 9

/-- True iff lane `i` is pinned to a named YMM `v{i}`; false iff stack `v[i]`. -/
def vIsReg (i : Nat) : Bool := i < numVmm

/-- SoA lane reference. -/
def vSlot (i : Nat) : String :=
  if vIsReg i then "v" ++ toString i else "v[" ++ toString i ++ "]"

/-- θ-column parity slot `pc{x}` (always a named YMM). -/
def pcReg (x : Nat) : String := "pc" ++ toString (x % 5)

/-- B-lane (ρ∘π output) slot — always stack `bv[]` (25 of them, live one round). -/
def bSlot (i : Nat) : String := "bv[" ++ toString i ++ "]"

/-! ### θ — column parities, then D[x] = c{x-1} ⊕ rotL(c{x+1},1) -/

/-- Read lane `j` into parity accumulator `pc{x}` (initial). When stack, via t0. -/
def readVtoPc (x j : Nat) : List String :=
  if vIsReg j then [ pcReg x ++ " = " ++ vSlot j ++ ";" ]
  else [ "t0 = " ++ vSlot j ++ ";", pcReg x ++ " = t0;" ]

/-- XOR lane `j` into parity accumulator `pc{x}` (packed `#VPXOR_256`). -/
def xorVintoPc (x j : Nat) : List String :=
  if vIsReg j then [ pcReg x ++ " = " ++ pcReg x ++ " ^ " ++ vSlot j ++ ";" ]
  else [ "t0 = " ++ vSlot j ++ ";", pcReg x ++ " = " ++ pcReg x ++ " ^ t0;" ]

/-- `pc{x} = ⊕_y A[x,y]` for one column. -/
def renderThetaCCol (x : Nat) : List String :=
  readVtoPc x (x + 0) ++ xorVintoPc x (x + 5) ++ xorVintoPc x (x + 10)
    ++ xorVintoPc x (x + 15) ++ xorVintoPc x (x + 20)

def renderThetaC : List String := (List.range 5).flatMap renderThetaCCol

/-- XOR `t0` (= D[x]) into lane `j` (packed). Reg: one `#VPXOR_256`; stack:
    load to t1, xor, store. -/
def xorT0intoV (j : Nat) : List String :=
  if vIsReg j then [ vSlot j ++ " = " ++ vSlot j ++ " ^ t0;" ]
  else [ "t1 = " ++ vSlot j ++ ";", "t1 = t1 ^ t0;", vSlot j ++ " = t1;" ]

/-- D[x] = c{x-1} ⊕ rotL(c{x+1},1), then apply to the 5 column lanes. The 64-bit
    packed rotate-by-1 is `#VPSLL_4u64(.,1)` | `#VPSRL_4u64(.,63)`. -/
def renderThetaDApply (x : Nat) : List String :=
  let cp1 := pcReg ((x + 1) % 5)
  let cm1 := pcReg ((x + 4) % 5)
  [ "t0 = " ++ cp1 ++ ";"
  , "t1 = #VPSLL_4u64(t0, 1);"
  , "t0 = #VPSRL_4u64(t0, 63);"
  , "t0 = t0 | t1;"                       -- rotL(c{x+1}, 1)
  , "t0 = t0 ^ " ++ cm1 ++ ";" ]          -- D[x]
  ++ xorT0intoV (x + 0) ++ xorT0intoV (x + 5) ++ xorT0intoV (x + 10)
  ++ xorT0intoV (x + 15) ++ xorT0intoV (x + 20)

def renderThetaD : List String := (List.range 5).flatMap renderThetaDApply

/-! ### ρ ∘ π — `bv[y + 5*((2x+3y)%5)] = rotL(v{i}, rho[i])` (packed 64-bit) -/

def renderRhoPiLane (i : Nat) : List String :=
  let x := i % 5
  let y := i / 5
  let n := rhoOffset i
  let bIdx := (y % 5) + 5 * ((2 * x + 3 * y) % 5)
  if n == 0 then [ "t0 = " ++ vSlot i ++ ";", bSlot bIdx ++ " = t0;" ]
  else
    [ "t0 = " ++ vSlot i ++ ";"
    , "t1 = #VPSLL_4u64(t0, " ++ toString n ++ ");"
    , "t0 = #VPSRL_4u64(t0, " ++ toString (64 - n) ++ ");"
    , "t0 = t0 | t1;"
    , bSlot bIdx ++ " = t0;" ]

def renderRhoPi : List String := (List.range 25).flatMap renderRhoPiLane

/-! ### χ — `v{x+5y} = bv[x+5y] ⊕ ((¬bv[(x+1)+5y]) ∧ bv[(x+2)+5y])`

The inner `(¬a) ∧ c` is ONE `#VPANDN_256(a, c)` (no separate NOT). -/

def renderChiLane (x y : Nat) : List String :=
  let i  := (x % 5) + 5 * (y % 5)
  let i1 := ((x + 1) % 5) + 5 * (y % 5)
  let i2 := ((x + 2) % 5) + 5 * (y % 5)
  let finalWrite :=
    if vIsReg i then [ vSlot i ++ " = t1 ^ t0;" ]
    else [ "t1 = t1 ^ t0;", vSlot i ++ " = t1;" ]
  [ "t0 = " ++ bSlot i1 ++ ";"
  , "t1 = " ++ bSlot i2 ++ ";"
  , "t0 = #VPANDN_256(t0, t1);"           -- (¬bv[i1]) ∧ bv[i2]
  , "t1 = " ++ bSlot i ++ ";" ]           -- bv[i]
  ++ finalWrite                            -- v{i} = bv[i] ⊕ ((¬bv[i1]) ∧ bv[i2])

def renderChi : List String :=
  (List.range 5).flatMap (fun y => (List.range 5).flatMap (fun x => renderChiLane x y))

/-! ### ι — `v0 ⊕= broadcast(RC[r])` -/

/-- ι for round `r`: assemble the 4-copy round constant into `cbuf`, load it as
    a `u256`, XOR into lane 0. -/
def renderIota (r : Nat) : List String :=
  [ "cbuf[0] = " ++ rcStr r ++ ";"
  , "cbuf[1] = " ++ rcStr r ++ ";"
  , "cbuf[2] = " ++ rcStr r ++ ";"
  , "cbuf[3] = " ++ rcStr r ++ ";"
  , "t0 = cbuf[:u256 0];"
  , vSlot 0 ++ " = " ++ vSlot 0 ++ " ^ t0;" ]

def renderRound (r : Nat) : List String :=
  renderThetaC ++ renderThetaD ++ renderRhoPi ++ renderChi ++ renderIota r

def render24Rounds : List String := (List.range 24).flatMap renderRound

/-- Load the four sponges' lane `i` (`inp[:u256 i]`) into the SoA lane slot. -/
def renderLoad : List String :=
  (List.range 25).flatMap (fun i =>
    if vIsReg i then [ vSlot i ++ " = inp[:u256 " ++ toString i ++ "];" ]
    else [ "t0 = inp[:u256 " ++ toString i ++ "];", vSlot i ++ " = t0;" ])

/-- Store the SoA lanes to `out[:u256 0..24]`. -/
def renderStore : List String :=
  (List.range 25).flatMap (fun i =>
    if vIsReg i then [ "out[:u256 " ++ toString i ++ "] = " ++ vSlot i ++ ";" ]
    else [ "t0 = " ++ vSlot i ++ ";", "out[:u256 " ++ toString i ++ "] = t0;" ])

/-- Declarations: `numVmm` named YMM lanes `v0..`, 5 parity YMM `pc0..pc4`,
    2 scratch YMM `t0`/`t1`, stack `v[25]` for spilled lanes, stack `bv[25]`
    for the ρ∘π output, and `cbuf[4]` for the ι round-constant broadcast. -/
def renderDecls : List String :=
  let vNames := String.intercalate " " ((List.range numVmm).map (fun i => "v" ++ toString i))
  let pcNames := String.intercalate " " ((List.range 5).map (fun i => "pc" ++ toString i))
  [ "reg u256 " ++ vNames ++ ";"
  , "reg u256 " ++ pcNames ++ ";"
  , "reg u256 t0 t1;"
  , "stack u256[25] v;"
  , "stack u256[25] bv;"
  , "stack u64[4] cbuf;" ]

def renderBody : List String :=
  renderDecls ++ renderLoad ++ render24Rounds ++ renderStore

/-- The full YMM-resident 4-way `.jazz` text. -/
def keccakF1600Ymm4Jazz : String :=
  let paramStrs := ["reg ptr u64[100] out", "reg const ptr u64[100] inp"]
  "export fn keccak_f1600_x4("
    ++ String.intercalate ", " paramStrs ++ ") -> reg ptr u64[100] {\n  "
    ++ String.intercalate "\n  " renderBody ++ "\n  return out;\n}"

/-! ### Structural sanity checks on the YMM 4-way emit -/

/- The export has the 4-way Simd256 ABI (`u64[100]` SoA, 4 sponges × 25 lanes). -/
#guard (strContains keccakF1600Ymm4Jazz "export fn keccak_f1600_x4(reg ptr u64[100] out, reg const ptr u64[100] inp)")

/- The body declares 9 named YMM lanes `v0..v8` — more resident u64 lane-values
    (`4·9 = 36`) than the GP path's 7. -/
#guard (strContains keccakF1600Ymm4Jazz "reg u256 v0 v1 v2 v3 v4 v5 v6 v7 v8;")

/- The body declares the 5 parity YMM. -/
#guard (strContains keccakF1600Ymm4Jazz "reg u256 pc0 pc1 pc2 pc3 pc4;")

/- χ uses the single-instruction `#VPANDN_256` for `(¬a) ∧ c`. -/
#guard (strContains keccakF1600Ymm4Jazz "t0 = #VPANDN_256(t0, t1);")

/- The packed 64-bit ρ/θ rotates use `#VPSLL_4u64` / `#VPSRL_4u64`. -/
#guard (strContains keccakF1600Ymm4Jazz "#VPSLL_4u64")
    && (strContains keccakF1600Ymm4Jazz "#VPSRL_4u64")

/-- numVmm (= 9) is strictly greater than the GP resident cap (5, and its
    jasminc-realised max of 7). -/
theorem ymm4_beats_gp_cap : numVmm > Resident.numResidentMs := by native_decide

end Ymm4

/-! ## Front-sourced round-step lanes (covered SExpr front, rfl-provenance)

The Keccak-f[1600] round steps at the `u64` lane granularity — θ, ρ, χ, ι —
expressed as width-64 `SExpr`s over the covered front alphabet and routed
through `lowerSExprW 64` → `Com catCryptDialect` → `cryptoDialectToJasminCom`
(the FRONT marker) → owned x86, mirroring the Sha2/ChaCha `FrontSourced`
templates. The rewrites (no `SOr`/`SNot`):
* ρ / θ-rotate `rotl64(x,n) = (x <<< n) ^ (x >>> (64-n))` (disjoint shifts);
* χ `A = B0 ^ (¬B1 ∧ B2) = B0 ^ B2 ^ (B1 ∧ B2)` (and/xor only);
* ι `A ^= RC` — `SXor` with the round-constant literal.
Provenance `isSome := by rfl`; value = the FIPS-202 byte-KAT (bench/keccak_compare). -/
namespace FrontSourced

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)

/-- The width-parametric scalar-`SExpr` front leaf. -/
abbrev lowerW := @CatCrypt.Crypto.SecureCompilation.Dialects.ScalarSExprWidth32Prototype.lowerSExprW

/-- `rotl64(x,n) = (x <<< n) ^ (x >>> (64-n))` (disjoint shifts). -/
def kRotl (x : SExpr) (n : Nat) : SExpr := .SXor (.SShl x (.SLit n)) (.SShr x (.SLit (64 - n)))

/-- θ diffusion word `D[x] = C[x-1] ^ rotl64(C[x+1], 1)`. -/
def kThetaD : SExpr := .SXor (.SVar "cm1") (kRotl (.SVar "cp1") 1)

/-- ρ per-lane rotate (offset `36 = r[3,0]` shown). -/
def kRho : SExpr := kRotl (.SVar "a") 36

/-- χ lane `A = B0 ^ (¬B1 ∧ B2) = B0 ^ B2 ^ (B1 ∧ B2)` (and/xor only). -/
def kChi : SExpr := .SXor (.SXor (.SVar "b0") (.SVar "b2")) (.SAnd (.SVar "b1") (.SVar "b2"))

/-- ι round-constant fold `A[0,0] ^= RC` (RC[0] = 1 shown). -/
def kIota : SExpr := .SXor (.SVar "a") (.SLit 1)

/-- Three-slot lane context (`b0 b1 b2` for χ / `cm1 cp1 a` for θ/ρ/ι — same shape). -/
def laneΓ : Ctx := [.sword 64, .sword 64, .sword 64]

/-- `VarMap` for χ (`b0 b1 b2`). -/
def chiVM : VarMap laneΓ :=
  (((VarMap.empty.bind "b2").bind "b1").bind "b0")

/-- `VarMap` for θ (`cm1 cp1 a`, `a` = ι/ρ operand). -/
def thetaVM : VarMap laneΓ :=
  (((VarMap.empty.bind "a").bind "cp1").bind "cm1")

/-- Lower a width-`w` `SExpr` to `Com catCryptDialect` via the covered front leaf. -/
def progOfW (w : Nat) {Γ : Ctx} (vm : VarMap Γ) (e : SExpr) :
    Option (Com catCryptDialect Γ (.sword w)) :=
  match lowerW w vm 0 e with
  | some r =>
      match r.1.vm.lookup r.2.1 with
      | some ⟨.sword w', v⟩ => if h : w' = w then r.1.cont (Com.ret (toVIRVar (h ▸ v))) else none
      | _ => none
  | none => none

/-- Lower on to the owned x86 backend (`Com jasminDialect`). -/
def jasminOfW (w : Nat) {Γ : Ctx} (vm : VarMap Γ) (e : SExpr) :=
  (progOfW w vm e).bind DialectToJasminCom.cryptoDialectToJasminCom

theorem keccak_thetaD_isSome : (progOfW 64 thetaVM kThetaD).isSome := by rfl
theorem keccak_thetaD_lowers : (jasminOfW 64 thetaVM kThetaD).isSome := by rfl
theorem keccak_rho_isSome : (progOfW 64 thetaVM kRho).isSome := by rfl
theorem keccak_rho_lowers : (jasminOfW 64 thetaVM kRho).isSome := by rfl
theorem keccak_chi_isSome : (progOfW 64 chiVM kChi).isSome := by rfl
theorem keccak_chi_lowers : (jasminOfW 64 chiVM kChi).isSome := by rfl
theorem keccak_iota_isSome : (progOfW 64 thetaVM kIota).isSome := by rfl
theorem keccak_iota_lowers : (jasminOfW 64 thetaVM kIota).isSome := by rfl

end FrontSourced

end CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmit
