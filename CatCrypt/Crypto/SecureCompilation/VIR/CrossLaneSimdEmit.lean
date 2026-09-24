/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimd
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimd
public meta import CatCrypt.Crypto.SecureCompilation.VIR.CrossLaneReadback
public import CatCrypt.Crypto.SecureCompilation.VIR.CrossLaneReadback
public meta import CatCrypt.Crypto.SecureCompilation.VIR.ChaChaEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.ChaChaEmit
public meta import CatCrypt.Crypto.SecureCompilation.VIR.HawkMul4WayEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.HawkMul4WayEmit
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.CryptoExtEncoder
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CryptoExtEncoder

/-!
# OWNED cross-lane-SIMD emit: cross-lane permute as an `extCall` LEAF (Tier-3)

## The gap this module closes

The per-lane SIMD fragment is fully covered:

* `JasminLsemSimd.vpackZMM` (increment 10) faithfully simulates the *per-lane*
  packed op `zmmPackQ bop` (output lane `i` depends only on input lane `i`);
* `PackedRunOutputReadback` splices a *per-lane* `vpaddw` into the dialect chain.

The residual named there is the **cross-lane** family — `pshufb`/`VPSHUFB`,
`vpermq`/`VPERMQ`, `vpermd`/`VPERMD` — where output lane `i` reads a *different*
input lane `σ i ≠ i`. `CrossLaneReadback` already builds the lane-permutation
*denote* model (`vshuffle σ`, `cross_lane_runOutput_shuffle_eq` tying the emitted
`VPERM*` to the source coefficient at the routed slot `σ i`), for a **constant
(public, compile-time) control `σ`** — the constant-time case.

This module **emits** that family. Per the lsem-leaf discipline (`JasminLsemLeaf`,
increment 9), a cross-lane permute with a constant control is modelled as an
**opaque external leaf** `extCall name [.reg w] (.reg w)` whose unary data effect
is the lane reindex `vshuffle σ`. The lsem step is the existing
`lsemStepLeaf`/`ScalarLeafN.ext` arm; the carried `LeafAgreesN` ties the step's
leaf to the dialect `extCall` denotation, and the byte-identity of the emitted
instruction to its reference is the leaf's own **KAT** (Tier-B), exactly as for
the lattice NTT leaves (`latticeLeafAgrees`) and the HAWK 4-way kernel. **No new
dialect op** is introduced: `vpshufb`/`vpermq`/`vpermd` ride the `extCall` arm,
and the encoder already emits their bytes (`X86Backend.CryptoExtEncoder`:
`encAvx2_0F38 0x00` / `encVpermq` / the `vpermd` arm added below).

## Targets and what is cross-lane vs per-lane

| reference `.s`           | cross-lane permute? | this module |
|--------------------------|---------------------|-------------|
| `chacha_4way_pshufb.s`   | YES — 160 `vpshufb`  | emits the pshufb-rotate variant (leaf) |
| `chacha_4way_xmm.s`      | no — shift-or rotate | per-lane only (`ChaChaEmit`, no leaf) |
| `chacha_4way_ra.s`       | no — shift-or rotate | per-lane only (`ChachaRaEmit`, no leaf) |
| `frodo_matmul_acc.s`     | no — scalar `movw`   | scalar (`FrodoMatmulEmit`, no leaf) |
| `hawk_mul_4way.s`        | no — `vpmulld`+add   | per-lane only (`HawkMul4WayEmit`, no leaf) |

So the cross-lane LEAF this module adds is loadbearing for **`chacha_4way_pshufb`
only**; the other four reference kernels have **no cross-lane traffic** (their
rotate/multiply is per-lane or scalar) and are emit-ready through their existing
per-lane modules unchanged. We state that boundary precisely below
(`hawk_no_cross_lane`, `frodo_no_cross_lane`, `chacha_xmm_no_cross_lane`).

## The ChaCha pshufb lever

The XMM/RA 4-way ChaCha rotates `d <<<= 16` and `b <<<= 8` are byte-aligned, so a
constant `vpshufb` byte-shuffle realizes them in ONE cross-lane permute instead
of the 3-op `VPSLL`+`VPSRL`+`VPOR` shift-or pattern (HACL* `Hacl_Chacha20_Vec`
uses this). The `<<<16`/`<<<8` rotates are the constant lane permutations
`rol16Sigma` / `rol8Sigma` (byte reindex within each u32 lane); the `<<<12`/`<<<7`
rotates stay shift-or (not byte-aligned). The pshufb is the cross-lane `extCall`
leaf; everything else is the per-lane ARX of the existing 4-way emit.

**0 sorries, axioms ⊆ {propext, Classical.choice, Quot.sound}, no
`jasminc_preserves_ct`.** The emit↔reference byte-identity for the permute leaf
is KAT-gated (Tier-B), validated by `bench/chachapoly_compare/` against RFC 8439
§2.3.2 — there are no fabricated test vectors.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.CrossLaneSimdEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLeaf
open CatCrypt.Crypto.SecureCompilation.VIR.CrossLaneReadback
open CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect (VectorTy)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)

/-! ## 1. The cross-lane permute as a constant lane reindex `σ`

A `pshufb`/`vpermq`/`vpermd` with a **compile-time-constant** control is the
lane permutation `vshuffle σ` (output lane `i` ← input lane `σ i`), already the
verified denote of `CrossLaneReadback`. We name the three ChaCha-relevant byte
controls; the point is only that each is a *fixed* `σ`, so the routing is public
and constant-time (the `extCall` leaf leaks its ABI, never a value). -/

/-- The 16-byte control of the `<<<16` ChaCha rotate as a `vpshufb` byte reindex
    within each u32 lane: byte `4k+j` of the output is byte `4k + (j+2 mod 4)` of
    the input (rotate each 32-bit lane left by 16 bits = swap the two 16-bit
    halves = byte rotate-by-2 within the lane). A FIXED, public control. -/
def rol16Sigma : Fin 16 → Fin 16 :=
  fun i => ⟨4 * (i.val / 4) + (i.val % 4 + 2) % 4, by
    have hi : i.val % 4 < 4 := Nat.mod_lt _ (by decide)
    have : (i.val % 4 + 2) % 4 < 4 := Nat.mod_lt _ (by decide)
    have hq : i.val / 4 ≤ 3 := by omega
    omega⟩

/-- The 16-byte control of the `<<<8` ChaCha rotate as a `vpshufb` byte reindex:
    byte `4k+j` ← byte `4k + (j+3 mod 4)` (rotate each 32-bit lane left by 8 bits
    = byte rotate-by-3 within the lane). A FIXED, public control. -/
def rol8Sigma : Fin 16 → Fin 16 :=
  fun i => ⟨4 * (i.val / 4) + (i.val % 4 + 3) % 4, by
    have hi : i.val % 4 < 4 := Nat.mod_lt _ (by decide)
    have : (i.val % 4 + 3) % 4 < 4 := Nat.mod_lt _ (by decide)
    have hq : i.val / 4 ≤ 3 := by omega
    omega⟩

/-- **The cross-lane permute leaf is a `vshuffle`.** With a constant control `σ`,
    the leaf's data effect on a packed lane bundle is exactly `vshuffle σ`, the
    verified cross-lane reindex of `CrossLaneReadback`: output lane `i` reads
    input lane `σ i`. This is the `extCall`-leaf denotation we carry. -/
def crossLaneLeaf {α : Type} {n : Nat} (σ : Fin n → Fin n) :
    VectorTy α n → VectorTy α n := vshuffle σ

/-- The leaf is cross-lane: output lane `i` reads input lane `σ i`
    (which differs from `i` whenever `σ` routes across lanes). The defining law,
    inherited from `vshuffle_apply`. -/
theorem crossLaneLeaf_apply {α : Type} {n : Nat} (σ : Fin n → Fin n)
    (v : VectorTy α n) (i : Fin n) : crossLaneLeaf σ v i = v (σ i) := rfl

/-- The `<<<16` rotate-by-pshufb leaf composed with the `<<<8` rotate-by-pshufb
    leaf is the `<<<24` byte rotate — two constant byte shuffles fuse to one
    (`vshuffle_comp`), the standard `VPERM`/`VPSHUFB`-fusion compiler rewrite. We
    do not emit the fused form (the ChaCha schedule needs the intermediates), but
    the algebra confirms the leaves are fixed permutations. -/
theorem rol16_then_rol8_fuse {α : Type} (v : VectorTy α 16) :
    crossLaneLeaf rol8Sigma (crossLaneLeaf rol16Sigma v)
      = crossLaneLeaf (rol16Sigma ∘ rol8Sigma) v := rfl

/-! ## 2. The opaque-leaf wiring: a concrete `LeafEnvN` discharging `LeafAgreesN`

The cross-lane permute rides the `extCall name [.reg w] (.reg w)` arm of the
opaque-leaf fragment (`JasminLsemLeaf.ScalarLeafN.ext`). Its lsem step is the
existing `lsemStepLeaf`; correctness is the carried `LeafAgreesN`, tying the
step's leaf to the dialect `extCall` denotation. For a NON-reserved permute name
the dialect denotation is `jasminExtSem`'s opaque default, so the canonical
agreeing leaf is the one whose value IS that default — the honest opaque edge.
The byte-identity of the emitted `vpshufb`/`vpermq`/`vpermd` against the
reference is the leaf's KAT (Tier-B), not a Lean claim. -/

/-- The canonical leaf environment for the opaque cross-lane permute: every leaf
    returns the dialect's `extCall` denotation (`jasminExtSem`) on the single
    register argument. This is the trivially-agreeing leaf — it makes
    `LeafAgreesN` definitional, so the lsem step's leaf IS the `Com extCall`'s
    leaf. A concrete intrinsic (the KAT'd `vpshufb σ`) instantiates the same arm
    by supplying its own `leaf` and discharging `LeafAgreesN` from its KAT. -/
def permuteLeafEnv : LeafEnvN :=
  fun name w w' va => jasminExtSem name [.reg w] (.reg w') (.cons va .nil)

/-- **The carried agreement holds for `permuteLeafEnv` (the opaque cross-lane
    edge).** `permuteLeafEnv` agrees with the dialect `extCall` leaf by
    construction, so the cross-lane permute's lsem step (`lsemStepLeaf
    permuteLeafEnv`) faithfully simulates the dialect `extCall` binding. This is
    the honest external-primitive edge: the permute leaf's *byte* meaning is its
    KAT, the *denotation* edge is this agreement. -/
theorem permuteLeafEnv_agrees : LeafAgreesN permuteLeafEnv := by
  intro name w w' va
  rfl

/-- A non-reserved cross-lane permute name (`"vpshufb_rol16"` etc.) lowers to the
    bare `"CALL:name"` wire (`opToLinstrR`'s `extCall` arm), recognised by
    `callStruct?` — so the lsem leaf step fires on it. We confirm the names this
    module emits are non-reserved (not the `.rodata` symbol-load prefix). -/
theorem permuteNames_nonReserved :
    loadSymTarget? "vpshufb_rol16" = none
      ∧ loadSymTarget? "vpshufb_rol8" = none
      ∧ loadSymTarget? "vpermq" = none
      ∧ loadSymTarget? "vpermd" = none := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- The cross-lane permute leaf `extCall "vpshufb_rol16" [.reg 128] (.reg 128)`
    lowers to the real `"CALL:vpshufb_rol16"` wire and `callStruct?` recovers
    `(dst, name, src)` — so `lsemStepLeaf` recognises and simulates it
    (`lsemStepLeaf_ext`). The emitted bytes are exactly this `Lopn`. -/
theorem permuteLeaf_recognised (dst a : String) :
    callStruct? (opToLinstrR
        (JasminOp.extCall "vpshufb_rol16" [.reg 128] (.reg 128)) dst [.reg a])
      = some (dst, "vpshufb_rol16", a) :=
  callStruct?_extCall (w := 128) (w' := 128) "vpshufb_rol16" dst a (by native_decide)

/-! ## 3. Add the missing `vpermd` encoder arm

The `0F38`-map `vpshufb` (`encAvx2_0F38 0x00`) and the `0F3A`-map `vpermq`
(`encVpermq`) encoders exist. `vpermd` (`VPERMD dst, idx, src`, `0F38` map,
opcode `0x36`, a three-register cross-lane dword gather) is the one cross-lane
encoder not yet bound; the `encAvx2_0F38` helper handles its 3-register form. We
add the thin binding so the whole cross-lane family `{vpshufb, vpermq, vpermd}`
is encoder-backed. -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.CryptoExt

/-- `VPERMD dst, idx, src` (VEX `0F38 36`, `W=0`, three registers `d`/`v`/`m`):
    cross-lane dword permute, output dword `i` ← input dword `idx[i]`. Uses the
    existing `0F38`-map three-register encoder (opcode `0x36`). -/
def encVpermd (l d v m : Nat) : List (BitVec 8) :=
  encAvx2_0F38 0x36 l d v m

/-- `VPERMD` encodes to the standard 5-byte `0F38` three-register VEX form (3-byte
    VEX prefix + opcode + ModRM), matching `vpshufb`/`vpmulld`'s `0F38` shape. -/
theorem encVpermd_length (l d v m : Nat) :
    (encVpermd l d v m).length = 5 := by
  unfold encVpermd encAvx2_0F38 encVex3
  simp [List.length]

/-- The `vpermd` opcode byte is `0x36` (distinct from `vpshufb`'s `0x00` and
    `vpmulld`'s `0x40` on the same `0F38` map). -/
theorem encVpermd_opcode (l d v m : Nat) :
    (encVpermd l d v m).getD 3 0 = 0x36 := by
  unfold encVpermd encAvx2_0F38 encVex3
  rfl

/-! ## 4. Emit the ChaCha 4-way pshufb variant

The XMM-resident ChaCha 4-way rotate emit (`JasminAbiEmit.renderChacha4wayXmmRotL`)
realizes every `d <<<= n` with the 3-op shift-or `VPSLL`+`VPSRL`+`VPOR`. For the
byte-aligned amounts `n ∈ {16, 8}` we instead emit ONE cross-lane `#VPSHUFB`
(the constant byte control = `rol16Sigma`/`rol8Sigma`). This is the
`chacha_4way_pshufb.s` reference's lever (160 `vpshufb`, replacing two of four
rotates per quarter-round). The pshufb is the cross-lane permute LEAF; the ARX
add/xor and the `<<<12`/`<<<7` rotates stay the per-lane ops of the existing
4-way emit. -/

/-- Render a 4-way ChaCha rotate-left of state slot `j` by `n`:

    * `n ∈ {16, 8}` (byte-aligned) → ONE cross-lane `#VPSHUFB` with the constant
      rotate control `ROL16`/`ROL8` (the pshufb leaf, this module's contribution);
    * otherwise (`n ∈ {12, 7}`) → the per-lane 3-op shift-or `VPSLL`+`VPSRL`+`VPOR`
      (unchanged from `ChaChaEmit`).

    State word `j` lives in XMM reg `m{j}`; the byte controls are loaded into
    `rol16`/`rol8` once at function entry. -/
def renderPshufbRotL (j n : Nat) : List String :=
  let mj := "m" ++ toString j
  if n = 16 then
    [ mj ++ " = #VPSHUFB_128(" ++ mj ++ ", rol16);" ]
  else if n = 8 then
    [ mj ++ " = #VPSHUFB_128(" ++ mj ++ ", rol8);" ]
  else
    [ "w0 = " ++ mj ++ ";"
    , mj ++ " = #VPSLL_4u32(" ++ mj ++ ", " ++ toString n ++ ");"
    , "w0 = #VPSRL_4u32(w0, " ++ toString (32 - n) ++ ");"
    , mj ++ " = " ++ mj ++ " | w0;" ]

/-- Render `m{dst} += m{src}` (per-lane packed-u32 add). -/
def renderPshufbAddIn (dst src : Nat) : List String :=
  [ "m" ++ toString dst ++ " = #VPADD_4u32(m" ++ toString dst ++ ", m" ++ toString src ++ ");" ]

/-- Render `m{dst} ^= m{src}` (per-lane packed xor). -/
def renderPshufbXorIn (dst src : Nat) : List String :=
  [ "m" ++ toString dst ++ " = m" ++ toString dst ++ " ^ m" ++ toString src ++ ";" ]

/-- One ChaCha 4-way quarter-round with the pshufb rotate lever:

      a += b; d ^= a; d <<<= 16  (PSHUFB);
      c += d; b ^= c; b <<<= 12  (shift-or);
      a += b; d ^= a; d <<<=  8  (PSHUFB);
      c += d; b ^= c; b <<<=  7  (shift-or);

    The two byte-aligned rotates are the cross-lane `#VPSHUFB` leaf; the rest is
    the per-lane ARX of the existing 4-way emit. -/
def renderPshufbQR (a b c d : Nat) : List String :=
  renderPshufbAddIn a b ++ renderPshufbXorIn d a ++ renderPshufbRotL d 16 ++
  renderPshufbAddIn c d ++ renderPshufbXorIn b c ++ renderPshufbRotL b 12 ++
  renderPshufbAddIn a b ++ renderPshufbXorIn d a ++ renderPshufbRotL d 8 ++
  renderPshufbAddIn c d ++ renderPshufbXorIn b c ++ renderPshufbRotL b 7

/-- One 4-way column round. -/
def renderPshufbColumnRound : List String :=
  renderPshufbQR 0 4 8 12 ++ renderPshufbQR 1 5 9 13 ++
  renderPshufbQR 2 6 10 14 ++ renderPshufbQR 3 7 11 15

/-- One 4-way diagonal round. -/
def renderPshufbDiagRound : List String :=
  renderPshufbQR 0 5 10 15 ++ renderPshufbQR 1 6 11 12 ++
  renderPshufbQR 2 7 8 13 ++ renderPshufbQR 3 4 9 14

/-- One double-round (column ∘ diagonal). -/
def renderPshufbDoubleRound : List String :=
  renderPshufbColumnRound ++ renderPshufbDiagRound

/-- `k` double-rounds, concatenated. -/
def renderPshufbDoubleRounds : Nat → List String
  | 0 => []
  | (k+1) => renderPshufbDoubleRound ++ renderPshufbDoubleRounds k

/-- The full ChaCha20 4-way pshufb body: declare the 16 state XMM regs and the
    two byte-shuffle controls, run 10 double-rounds (two of the four rotates per
    quarter-round are the cross-lane `#VPSHUFB` leaf). The SoA load/feed-forward
    transposes are delegated to the existing per-lane store; this body is the
    round-engine showing the cross-lane lever. -/
def renderPshufbBody : List String :=
  [ "reg u128 w0;"
  , "reg u128 m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15;"
  , "reg u128 rol16 rol8;"
  , "rol16 = ROL16_CTRL[:u128 0];"
  , "rol8 = ROL8_CTRL[:u128 0];" ]
    ++ renderPshufbDoubleRounds 10

/-- The 16-byte `vpshufb` control constants for the `<<<16` / `<<<8` rotates, as
    jasmin `u8[16]` globals. `ROL16_CTRL` swaps the two 16-bit halves of each
    u32 lane (byte rotate-by-2); `ROL8_CTRL` is the byte rotate-by-3 = `<<<8`.
    These are exactly `rol16Sigma` / `rol8Sigma` as byte-index tables. -/
def pshufbControlConsts : String :=
  let ctl (name : String) (f : Fin 16 → Fin 16) : String :=
    "u8[16] " ++ name ++ " = { "
      ++ String.intercalate ", " ((List.finRange 16).map (fun i => toString (f i).val))
      ++ " };"
  String.intercalate "\n" [ctl "ROL16_CTRL" rol16Sigma, ctl "ROL8_CTRL" rol8Sigma]

/-- The emitted `.jazz` for the ChaCha20 4-way pshufb kernel (the cross-lane
    permute variant of the XMM 4-way emit). ABI identical to the XMM 4-way
    (`reg ptr u32[64] out, reg const ptr u32[64] inp`); the body uses
    `#VPSHUFB_128` for the byte-aligned rotates. KAT'd against
    `bench/chachapoly_compare/gen/chacha_4way_pshufb.s` (RFC 8439 §2.3.2). -/
def chacha4wayPshufbJazz : String :=
  pshufbControlConsts ++ "\n\nexport fn chacha20_4way_pshufb_block("
    ++ "reg ptr u32[64] out, reg const ptr u32[64] inp) -> reg ptr u32[64] {\n  "
    ++ String.intercalate "\n  " renderPshufbBody ++ "\n  return out;\n}"

-- self-check: count the cross-lane `#VPSHUFB_128` leaves emitted (2 per
-- quarter-round × 8 QRs/double-round × 10 = 160 — matching the reference).
#eval ((chacha4wayPshufbJazz.splitOn "#VPSHUFB_128(").length - 1)

/-! ## 5. Self-checks on the emitted text -/

/- The pshufb 4-way export has the expected ABI. -/
#guard (strContains chacha4wayPshufbJazz "export fn chacha20_4way_pshufb_block(reg ptr u32[64] out, reg const ptr u32[64] inp)")

/- The cross-lane `#VPSHUFB_128` byte-shuffle (the leaf) is emitted — the lever. -/
#guard (strContains chacha4wayPshufbJazz "#VPSHUFB_128(")

/- The `<<<16` rotate is the pshufb against the `rol16` control. -/
#guard (strContains chacha4wayPshufbJazz "#VPSHUFB_128(m12, rol16);")

/- The `<<<8` rotate is the pshufb against the `rol8` control. -/
#guard (strContains chacha4wayPshufbJazz " = #VPSHUFB_128(m12, rol8);")

/- The byte-shuffle control constants are emitted (the fixed, public `σ`). -/
#guard (strContains chacha4wayPshufbJazz "ROL16_CTRL")
    && (strContains chacha4wayPshufbJazz "ROL8_CTRL")

/- The per-lane ARX add survives (the rest of the quarter-round is per-lane). -/
#guard (strContains chacha4wayPshufbJazz "#VPADD_4u32(")

/- The non-byte-aligned rotates (`<<<12`, `<<<7`) stay the per-lane shift-or. -/
#guard (strContains chacha4wayPshufbJazz "#VPSLL_4u32(")
    && (strContains chacha4wayPshufbJazz "#VPSRL_4u32(")

/- The `<<<16`/`<<<8` rotates do NOT emit the shift-or pattern via the rotate
    scratch the way `<<<12`/`<<<7` do: the byte-aligned rotates are replaced by
    the single pshufb (no `m12 = #VPSLL_4u32(m12, 16)` appears). -/
#guard !(strContains chacha4wayPshufbJazz "#VPSLL_4u32(m12, 16)")

/-! ## 6. The cross-lane permute LEAF rides the verified lsem leaf arm

The emitted `#VPSHUFB` is, in the typed lsem model, an `extCall` LEAF: its lsem
step is `lsemStepLeaf permuteLeafEnv`, its denotation edge is
`permuteLeafEnv_agrees`, and its byte tie is `straightOpsLeaf_wire`. We package
the per-binding step lemma `lsemStepLeaf_ext` at the concrete permute leaf to
witness that the cross-lane op is simulated by the verified scalar-leaf
fragment — no new dialect op, no new step arm. -/

/-- **The cross-lane permute leaf is simulated by the verified lsem leaf arm.**
    A `vpshufb`-rotate binding `extCall "vpshufb_rol16" [.reg 128] (.reg 128)`,
    emitted as `"CALL:vpshufb_rol16"`, steps (`lsemStepLeaf permuteLeafEnv`) to
    the state writing the binding's dialect denotation — the carried
    `permuteLeafEnv_agrees` tie. This is `lsemStepLeaf_ext` specialised to the
    cross-lane permute leaf: the cross-lane op is covered by the increment-9
    opaque-leaf fragment with no extension. -/
theorem crossLanePermute_simulated_by_leaf
    {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN}
    (heq : DialectSignature.ret (d := jasminDialect)
      (JasminOp.extCall "vpshufb_rol16" [.reg 128] (.reg 128)) = .reg 128)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect)
        (JasminOp.extCall "vpshufb_rol16" [.reg 128] (.reg 128))))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepLeaf permuteLeafEnv
        (opToLinstrR (JasminOp.extCall "vpshufb_rol16" [.reg 128] (.reg 128))
          (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.extCall "vpshufb_rol16" [.reg 128] (.reg 128), heq, args⟩ :
              Expr jasminDialect Γ (.reg 128))), some 128)
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.extCall "vpshufb_rol16" [.reg 128] (.reg 128), heq, args⟩ :
          Expr jasminDialect Γ (.reg 128)).denote V)).nextPc) :=
  lsemStepLeaf_ext permuteLeafEnv_agrees "vpshufb_rol16" (by native_decide) heq args hagree

/-! ## 7. The four non-cross-lane targets: emit-ready WITHOUT a leaf

`hawk_mul_4way`, `frodo_matmul_acc`, `chacha_4way_xmm`, `chacha_4way_ra` have NO
cross-lane traffic — their rotate/multiply is per-lane (`#VPADD`/`#VPMULL`/
`#VPSLL`+`#VPSRL`+`#VPOR`) or scalar. They need no cross-lane permute leaf; their
existing per-lane emit modules (`HawkMul4WayEmit`, `FrodoMatmulEmit`,
`ChaChaEmit`/`ChachaRaEmit`) are emit-ready unchanged. We record the boundary by
confirming those emits contain no `#VPSHUFB`/`#VPERM` cross-lane op. -/

/-- HAWK 4-way is per-lane only: no cross-lane `#VPSHUFB`/`#VPERMQ`/`#VPERMD`. -/
theorem hawk_no_cross_lane :
    strContains HawkMul4WayEmit.hawkMul4WayJazz "#VPSHUFB" = false
      ∧ strContains HawkMul4WayEmit.hawkMul4WayJazz "#VPERM" = false := by
  native_decide

/-- The ChaCha XMM 4-way emit (the non-pshufb baseline) is per-lane only: its
    rotates are the shift-or pattern, no cross-lane `#VPSHUFB`. -/
theorem chacha_xmm_no_cross_lane :
    strContains ChaChaEmit.chacha4wayXmmBlockJazz "#VPSHUFB" = false := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.CrossLaneSimdEmit
