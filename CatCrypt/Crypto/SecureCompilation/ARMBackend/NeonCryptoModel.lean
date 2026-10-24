/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.ARMBackend.NeonEncoder
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.ARMBackend.NeonEncoder
public meta import CatCrypt.Crypto.SecureCompilation.ARMBackend.SailArmDecoder
public import CatCrypt.Crypto.SecureCompilation.ARMBackend.SailArmDecoder
public meta import CatCrypt.Crypto.SecureCompilation.ARMBackend.SailNeonDecoder
public import CatCrypt.Crypto.SecureCompilation.ARMBackend.SailNeonDecoder
public meta import CatCrypt.Crypto.Jasmin.JasminOps
public import CatCrypt.Crypto.Jasmin.JasminOps
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.FinCases

/-!
# The ARMv8 crypto-extension NEON instructions: model, lowering, encoder, decoder

`NeonModel.lean`/`NeonLowering.lean`/`NeonEncoder.lean`/`SailNeonDecoder.lean`
cover the **packed-u32/u8 ASIMD ALU** subset (ADD/SUB/MUL.4S, AND/ORR/EOR.16B,
SHL/USHR.4S, MOV.16B) that the ChaCha 4-way kernel emits — the AArch64 analogue
of the x86 packed-u32 path. This module is the **ARMv8 crypto-extension**
analogue of the x86 crypto-instruction model (VAES/PCLMUL/SHA-NI): the AArch64 AES round / GF(2^128) carry-less multiply
instructions, in the **128-bit-value** V-register view, with the lowering
denotation theorem, the verified byte encoder, and a
`decode(encode i) = i` round-trip (§8 below — see that section for exactly what
the "decoder" checks).

## The AESE/AESMC semantics split (vs the x86 AES-NI op split)

AArch64 splits the AES round across **two** instructions, with the round-key XOR
folded into the *front* (before SubBytes), the opposite of x86 AES-NI which adds
the key at the *back* (after MixColumns):

| ARM op             | semantics (FIPS-197)                                      |
|--------------------|----------------------------------------------------------|
| `AESE  Vd, Vn`     | `ShiftRows(SubBytes(Vd ⊕ Vn))`  (Vn = round key)         |
| `AESMC Vd, Vn`     | `MixColumns(Vn)`                                          |
| `AESD  Vd, Vn`     | `InvShiftRows(InvSubBytes(Vd ⊕ Vn))`                     |
| `AESIMC Vd, Vn`    | `InvMixColumns(Vn)`                                       |

The idiomatic ARM AES round is the **pair** `AESE Vd, Vrk ; AESMC Vd, Vd`, which
computes `MixColumns(ShiftRows(SubBytes(state ⊕ rk)))`. Contrast x86
`AESENC state, rk = MixColumns(ShiftRows(SubBytes(state))) ⊕ rk` — a *different*
op split for the *same* round function. Concretely, the ARM pair equals
`Jasmin.wAESENC (state ⊕ rk) 0` (the x86 word op with the key pre-mixed and a
zero post-key): proved below (`aese_aesmc_eq_x86`, `native_decide` on the
FIPS-197 worked example). The KAT catches a wrong split.

## The anchor (inherited Sail/FIPS surface, same as the x86 crypto instructions)

The lane semantics is **not** re-derived: `AESE`/`AESMC`/`AESD`/`AESIMC` are the
authoritative `Jasmin.aesSubBytes`/`aesShiftRows`/`aesMixColumns`/… FIPS-197 word
transforms (the same ops `SailX86Lean` pins to the Sail-x86 / FIPS-197 reference),
and `PMULL`/`PMULL2` reuse the schoolbook `clmul64` carry-less product (the exact
`VPClmulEmit.polyMul64`). So the crypto-register semantics inherits the existing
Sail/FIPS anchor rather than introducing a fresh differential-validation surface;
the integration witness is the FIPS-197 AES-round KAT (run under qemu-aarch64,
`-cpu max`, in an untracked local comparison checkout not vendored in this
repo).

## The crypto-ext byte encodings (the C7.2 crypto-AES / -3reg forms, `Q=1`)

`aarch64-linux-gnu-as -march=armv8-a+crypto` (confirmed by `objdump -d`):

* **AESE  Vd.16B, Vn.16B** — `0x4e284800 + Rn·0x20 + Rd`
* **AESMC Vd.16B, Vn.16B** — `0x4e286800 + Rn·0x20 + Rd`
* **AESD  Vd.16B, Vn.16B** — `0x4e285800 + Rn·0x20 + Rd`
* **AESIMC Vd.16B, Vn.16B** — `0x4e287800 + Rn·0x20 + Rd`
* **PMULL  Vd.1Q, Vn.1D, Vm.1D**  — `0x0ee0e000 + Rm·0x10000 + Rn·0x20 + Rd`
* **PMULL2 Vd.1Q, Vn.2D, Vm.2D**  — `0x4ee0e000 + Rm·0x10000 + Rn·0x20 + Rd`

The sail-arm `decode64` clauses (`aarch_decode.sail`) match these as
`vector_crypto_aes_round` (AESE/AESD, prefix `0b0100111000101000010010`, the
`D[12]` bit picks E vs D) and `vector_crypto_aes_mix` (AESMC/AESIMC, prefix
`0b0100111000101000011010`, `D[12]` picks MC vs IMC), with `Rd[4:0] Rn[9:5]` at
the same positions the scalar/ASIMD forms use.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 8000

namespace CatCrypt.Crypto.SecureCompilation.ARMBackend.Neon.Crypto

open CatCrypt.Crypto.SecureCompilation.ARMBackend.Neon
open CatCrypt.Crypto.SecureCompilation.ARMBackend.Neon.NeonEncoder
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmEncoder (wordLE wordLE_length)
open CatCrypt.Crypto.Jasmin

/-! ## 1. The 128-bit-value V-register view

The packed-u32 model views a `V` register as 4 × u32 lanes (`Vec128`); the AES /
PMULL ops act on the whole 128-bit register value. We read/write through a
`Vec128 ↔ BitVec 128` bijection, the same lane order as the x86 XMM view. -/

/-- Reinterpret a 4 × u32 `V` register as one little-endian 128-bit value: lane
    `0` is the low dword, lane `3` the high dword (gas's `v` byte order). -/
def vToBits (x : Vec128) : BitVec 128 :=
  ((x 3).setWidth 128 <<< 96) ||| ((x 2).setWidth 128 <<< 64) |||
  ((x 1).setWidth 128 <<< 32) ||| (x 0).setWidth 128

/-- Reinterpret a 128-bit value as a 4 × u32 `V` register (inverse of `vToBits`):
    lane `j` is dword `j` (`v >>> 32j`, truncated). -/
def bitsToV (v : BitVec 128) : Vec128 :=
  fun j => (v >>> (j.val * 32)).setWidth 32

/-- `bitsToV` then `vToBits` is the identity (the register-view round-trip). -/
theorem vToBits_bitsToV (v : BitVec 128) : vToBits (bitsToV v) = v := by
  show ((bitsToV v 3).setWidth 128 <<< 96) ||| ((bitsToV v 2).setWidth 128 <<< 64) |||
      ((bitsToV v 1).setWidth 128 <<< 32) ||| (bitsToV v 0).setWidth 128 = v
  simp only [bitsToV]
  show (((v >>> ((3 : Fin 4).val * 32)).setWidth 32).setWidth 128 <<< 96) |||
      (((v >>> ((2 : Fin 4).val * 32)).setWidth 32).setWidth 128 <<< 64) |||
      (((v >>> ((1 : Fin 4).val * 32)).setWidth 32).setWidth 128 <<< 32) |||
      ((v >>> ((0 : Fin 4).val * 32)).setWidth 32).setWidth 128 = v
  norm_num
  bv_decide

/-! ## 2. The crypto-extension word ops (FIPS-197 / carry-less)

Each op is the authoritative `Jasmin` FIPS-197 transform, with the AArch64
op-split applied. The round-key XOR is folded into `AESE`/`AESD` (front), the
opposite of the x86 `wAESENC`'s back-key. -/

/-- `AESE Vd, Vn`: AddRoundKey (`Vd ⊕ Vn`) then SubBytes then ShiftRows. -/
def wArmAESE (state rk : BitVec 128) : BitVec 128 :=
  aesShiftRows (aesSubBytes (state ^^^ rk))

/-- `AESMC Vn`: MixColumns. -/
def wArmAESMC (x : BitVec 128) : BitVec 128 := aesMixColumns x

/-- `AESD Vd, Vn`: AddRoundKey (`Vd ⊕ Vn`) then InvSubBytes then InvShiftRows. -/
def wArmAESD (state rk : BitVec 128) : BitVec 128 :=
  aesInvShiftRows (aesInvSubBytes (state ^^^ rk))

/-- `AESIMC Vn`: InvMixColumns. -/
def wArmAESIMC (x : BitVec 128) : BitVec 128 := aesInvMixColumns x

/-- One bit step of the schoolbook carry-less (GF(2)[x]) multiply: XOR `b <<< i`
    into the accumulator when bit `i` of `a` is set. The exact `PMULL` per-half
    semantics (the same schoolbook `VPClmulEmit.polyMul64Step` the x86 PCLMULQDQ
    model uses). -/
def clmul64Step (a : BitVec 64) (b : BitVec 128) (acc : BitVec 128) (i : Nat) : BitVec 128 :=
  let bitI : BitVec 128 := ((a >>> i) &&& 1).setWidth 128
  let mask : BitVec 128 := 0#128 - bitI
  acc ^^^ ((b <<< i) &&& mask)

/-- Carry-less product of two 64-bit halves, `BitVec 64 × BitVec 64 → BitVec 128`,
    no modular reduction — the exact semantics of one `PMULL`/`PMULL2` (the same
    schoolbook product the x86 `PCLMULQDQ` model computes). -/
def clmul64 (a b : BitVec 64) : BitVec 128 :=
  let b128 : BitVec 128 := b.setWidth 128
  Fin.foldl 64 (fun acc i => clmul64Step a b128 acc i.val) (0 : BitVec 128)

/-- `PMULL Vd.1Q, Vn.1D, Vm.1D`: carry-less product of the **low** 64-bit halves
    of `Vn` and `Vm` (the GF(2^128) GHASH multiply, low ⊗ low). -/
def wArmPMULL (a b : BitVec 128) : BitVec 128 :=
  clmul64 (a.setWidth 64) (b.setWidth 64)

/-- `PMULL2 Vd.1Q, Vn.2D, Vm.2D`: carry-less product of the **high** 64-bit
    halves of `Vn` and `Vm` (high ⊗ high). -/
def wArmPMULL2 (a b : BitVec 128) : BitVec 128 :=
  clmul64 ((a >>> 64).setWidth 64) ((b >>> 64).setWidth 64)

/-! ### The op-split equivalence to the x86 AES-NI reference

The ARM AES round idiom `AESE Vd, Vrk ; AESMC Vd, Vd` equals the x86
`wAESENC (state ⊕ rk) 0`. With `rk = 0` this is exactly the round transform
`MixColumns(ShiftRows(SubBytes(state)))`. Pinned on the FIPS-197 worked example,
so a wrong split (e.g. modelling AESE as the x86 back-key) is caught. -/

/-- **The op-split equivalence.** `AESMC(AESE(state, rk))` equals the x86
    `wAESENC` word op with the key pre-mixed and a zero post-key — i.e. the
    AArch64 front-key split realises the same FIPS-197 round as x86's back-key
    split. Pinned on the FIPS-197 worked example. -/
theorem aese_aesmc_eq_x86 :
    wArmAESMC (wArmAESE 0x3243f6a8885a308d313198a2e0370734#128
                        0x2b7e151628aed2a6abf7158809cf4f3c#128)
      = wAESENC (0x3243f6a8885a308d313198a2e0370734#128 ^^^
                 0x2b7e151628aed2a6abf7158809cf4f3c#128) 0 := by
  native_decide

/-! ## 3. The crypto-extension instruction set (128-bit register view)

Disjoint from the packed-u32 `NInst` (so the ChaCha lowering theorem is
untouched), in the 128-bit-value V-register view. -/

/-- A single crypto-extension NEON instruction over named `V` registers. -/
inductive NCryptInst where
  /-- `AESE Vd.16B, Vn.16B` — AddRoundKey⊕SubBytes⊕ShiftRows (`Vn` = round key). -/
  | aese (d a : String)
  /-- `AESMC Vd.16B, Vn.16B` — MixColumns. -/
  | aesmc (d a : String)
  /-- `AESD Vd.16B, Vn.16B` — AddRoundKey⊕InvSubBytes⊕InvShiftRows. -/
  | aesd (d a : String)
  /-- `AESIMC Vd.16B, Vn.16B` — InvMixColumns. -/
  | aesimc (d a : String)
  /-- `PMULL Vd.1Q, Vn.1D, Vm.1D` — carry-less product of the low halves. -/
  | pmull (d a b : String)
  /-- `PMULL2 Vd.1Q, Vn.2D, Vm.2D` — carry-less product of the high halves. -/
  | pmull2 (d a b : String)
  deriving Repr, DecidableEq

/-- The semantics of one crypto-extension instruction: read source register(s) as
    128-bit values, apply the authoritative word op, write the destination back
    through the `BitVec 128 → Vec128` view. -/
def evalNCryptInst (s : NState) : NCryptInst → NState
  | .aese d a   => s.setV d (bitsToV (wArmAESE  (vToBits (s.get d)) (vToBits (s.get a))))
  | .aesmc d a  => s.setV d (bitsToV (wArmAESMC (vToBits (s.get a))))
  | .aesd d a   => s.setV d (bitsToV (wArmAESD  (vToBits (s.get d)) (vToBits (s.get a))))
  | .aesimc d a => s.setV d (bitsToV (wArmAESIMC (vToBits (s.get a))))
  | .pmull d a b  => s.setV d (bitsToV (wArmPMULL  (vToBits (s.get a)) (vToBits (s.get b))))
  | .pmull2 d a b => s.setV d (bitsToV (wArmPMULL2 (vToBits (s.get a)) (vToBits (s.get b))))

/-- `runNCryptBlock`: a straight-line fold of `evalNCryptInst`. -/
def runNCryptBlock (s : NState) : List NCryptInst → NState
  | [] => s
  | i :: is => runNCryptBlock (evalNCryptInst s i) is

@[simp] theorem runNCryptBlock_nil (s : NState) : runNCryptBlock s [] = s := rfl

@[simp] theorem runNCryptBlock_cons (s : NState) (i : NCryptInst) (is : List NCryptInst) :
    runNCryptBlock s (i :: is) = runNCryptBlock (evalNCryptInst s i) is := rfl

/-! ## 4. The register-named op alphabet + the block-lowering denotation theorem

The crypto analogue of `NeonLowering`: a register-named `NCryptOp`, the
one-rule-per-constructor lowering, and the block-lowering denotation theorem
(by induction, no new custom axioms). -/

/-- A register-named crypto-extension op (the lowering's source shape). -/
inductive NCryptOp where
  /-- `dst := AESE dst, a` (in place; `a` = round key). -/
  | aese (dst a : String)
  /-- `dst := AESMC a`. -/
  | aesmc (dst a : String)
  /-- `dst := AESD dst, a`. -/
  | aesd (dst a : String)
  /-- `dst := AESIMC a`. -/
  | aesimc (dst a : String)
  /-- `dst := PMULL a, b`. -/
  | pmull (dst a b : String)
  /-- `dst := PMULL2 a, b`. -/
  | pmull2 (dst a b : String)
  deriving Repr, DecidableEq

/-- Lower a register-named crypto op to the machine `NCryptInst`. -/
def toNCryptInst : NCryptOp → NCryptInst
  | .aese dst a   => .aese dst a
  | .aesmc dst a  => .aesmc dst a
  | .aesd dst a   => .aesd dst a
  | .aesimc dst a => .aesimc dst a
  | .pmull dst a b  => .pmull dst a b
  | .pmull2 dst a b => .pmull2 dst a b

/-- Lower a straight-line `NCryptOp` block to a machine `NCryptInst` block. -/
def lowerNCryptBlock (block : List NCryptOp) : List NCryptInst := block.map toNCryptInst

/-- **AArch64 crypto-extension block-lowering denotation theorem.** The machine
    semantics of the lowered `NCryptOp` block equals the fold of the per-op
    machine semantics over the block, for all blocks and states, by induction. No
    new custom axioms. -/
theorem neonCryptoBlock_lowering_denote :
    ∀ (block : List NCryptOp) (s : NState),
      runNCryptBlock s (lowerNCryptBlock block)
        = block.foldl (fun st op => evalNCryptInst st (toNCryptInst op)) s := by
  intro block
  induction block with
  | nil => intro s; rfl
  | cons op rest ih =>
      intro s
      simp only [lowerNCryptBlock, List.map_cons, runNCryptBlock_cons, List.foldl_cons]
      exact ih (evalNCryptInst s (toNCryptInst op))

/-! ## 5. The AES-128 single-round kernel + FIPS-197 KAT

The recommended kernel: the idiomatic ARM AES round `AESE Vd, Vrk ; AESMC Vd, Vd`.
On the FIPS-197 worked example state / key it computes
`MixColumns(ShiftRows(SubBytes(state ⊕ rk)))`, the value the qemu-aarch64 harness
(`-cpu max`) checks byte-identically. The same value the x86 owned AES path
produces via `wAESENC (state ⊕ rk) 0` (`aese_aesmc_eq_x86`). -/

/-- The ARM AES single-round idiom on register `st` with round key in `rk`:
    `AESE st, rk ; AESMC st, st`. -/
def aesRoundBlk (st rk : String) : List NCryptOp :=
  [ .aese st rk, .aesmc st st ]

/-- **Lowering correctness on the AES round block.** -/
theorem aesRound_lowering_correct (st rk : String) (s : NState) :
    runNCryptBlock s (lowerNCryptBlock (aesRoundBlk st rk))
      = (aesRoundBlk st rk).foldl
          (fun st' op => evalNCryptInst st' (toNCryptInst op)) s :=
  neonCryptoBlock_lowering_denote (aesRoundBlk st rk) s

/-- Seed a `V` register state with `st = fipsBlk`, `rk = fipsKey` (the FIPS-197
    AES worked example), through the `bitsToV` register view. -/
def aesKatInit : NState :=
  (NState.mk (fun _ _ => 0)
    |>.setV "st" (bitsToV 0x3243f6a8885a308d313198a2e0370734#128)
    |>.setV "rk" (bitsToV 0x2b7e151628aed2a6abf7158809cf4f3c#128))

/-- **FIPS-197 AES-round KAT.** The lowered-and-run `AESE st, rk ; AESMC st, st`
    on the owned crypto model produces `MixColumns(ShiftRows(SubBytes(st ⊕ rk)))`
    `= 0xd4b42de533b1a833b711b95b016f84ec`, byte-identical (read back through
    `vToBits`). The integration witness that the owned AArch64 AES path computes
    the AES round correctly. -/
theorem aes_round_kat :
    vToBits ((runNCryptBlock aesKatInit
        (lowerNCryptBlock (aesRoundBlk "st" "rk"))).get "st")
      = 0xd4b42de533b1a833b711b95b016f84ec#128 := by
  native_decide

/-- **The cross-backend AES-round identity.** The AArch64 round value equals the
    x86 AES-NI word op `wAESENC (st ⊕ rk) 0` on the FIPS-197 vector — the same AES
    round function, computed through the two different op splits. -/
theorem aes_round_kat_eq_x86 :
    vToBits ((runNCryptBlock aesKatInit
        (lowerNCryptBlock (aesRoundBlk "st" "rk"))).get "st")
      = wAESENC (0x3243f6a8885a308d313198a2e0370734#128 ^^^
                 0x2b7e151628aed2a6abf7158809cf4f3c#128) 0 := by
  native_decide

/-- `PMULL` GHASH self-check: low ⊗ low of `0xFF ⊗ 0xFF = 0x5555` (the standard
    carry-less square). -/
example : wArmPMULL 0xFF#128 0xFF#128 = 0x5555#128 := by native_decide

/-! ## 5b. The GAS ASIMD crypto printer (one line per `NCryptInst`)

The thin syntactic trust edge (the printer + `as`), the crypto analogue of
`NeonAsmPrinter.renderNInst`. AES ops are `op Vd.16B, Vn.16B`; PMULL is
`pmull Vd.1Q, Vn.1D, Vm.1D` / `pmull2 Vd.1Q, Vn.2D, Vm.2D`. -/

/-- Append the `.16b` arrangement suffix to a register name. -/
def b16 (r : String) : String := r ++ ".16b"

/-- Print one crypto `NCryptInst` to its GAS AArch64 ASIMD asm line. -/
def renderNCryptInst (alloc : VAlloc) : NCryptInst → String
  | .aese d a   => "\taese "  ++ b16 (vOf alloc d) ++ ", " ++ b16 (vOf alloc a)
  | .aesmc d a  => "\taesmc " ++ b16 (vOf alloc d) ++ ", " ++ b16 (vOf alloc a)
  | .aesd d a   => "\taesd "  ++ b16 (vOf alloc d) ++ ", " ++ b16 (vOf alloc a)
  | .aesimc d a => "\taesimc "++ b16 (vOf alloc d) ++ ", " ++ b16 (vOf alloc a)
  | .pmull d a b  => "\tpmull "  ++ vOf alloc d ++ ".1q, " ++ vOf alloc a ++ ".1d, " ++ vOf alloc b ++ ".1d"
  | .pmull2 d a b => "\tpmull2 " ++ vOf alloc d ++ ".1q, " ++ vOf alloc a ++ ".2d, " ++ vOf alloc b ++ ".2d"

/-- Render a complete GAS AArch64 ASIMD crypto leaf function: the AES single-round
    `AESE v0, v1 ; AESMC v0, v0`, with `st` pinned to `v0` (arg/result) and `rk`
    to `v1`. The scaffolding is trusted (outside the verified body), the same
    posture as `NeonAsmPrinter.renderLeafFn`. -/
def aesRoundLeafAsm : String :=
  let alloc : VAlloc := [("st", "v0"), ("rk", "v1")]
  let body := lowerNCryptBlock (aesRoundBlk "st" "rk")
  let lines := body.map (renderNCryptInst alloc)
  String.intercalate "\n"
    ([ "\t.text", "\t.global aes_round_a64", "\t.type aes_round_a64, %function"
     , "aes_round_a64:" ] ++ lines ++ ["\tret"]) ++ "\n"

/-- Printer pin: `aese v0.16b, v1.16b`. -/
example : renderNCryptInst [("d","v0"),("a","v1")] (.aese "d" "a")
    = "\taese v0.16b, v1.16b" := by native_decide

/-- Printer pin: `aesmc v0.16b, v0.16b`. -/
example : renderNCryptInst [("d","v0")] (.aesmc "d" "d")
    = "\taesmc v0.16b, v0.16b" := by native_decide

/-! ## 6. The verified byte encoder

Each crypto-ext instruction is one fixed-width 32-bit A64 word, the same shape as
the packed-u32 subset. The AES ops are two-register (`Rn`/`Rd`); PMULL is
three-register (`Rm`/`Rn`/`Rd`). Bases confirmed against
`aarch64-linux-gnu-as -march=armv8-a+crypto` (`objdump -d`). -/

/-- The AESE base word (`0x4e284800`). -/
def baseAese : Nat := 0x4e284800
/-- The AESMC base word (`0x4e286800`). -/
def baseAesmc : Nat := 0x4e286800
/-- The AESD base word (`0x4e285800`). -/
def baseAesd : Nat := 0x4e285800
/-- The AESIMC base word (`0x4e287800`). -/
def baseAesimc : Nat := 0x4e287800
/-- The PMULL base word (`0x0ee0e000`). -/
def basePmull : Nat := 0x0ee0e000
/-- The PMULL2 base word (`0x4ee0e000`). -/
def basePmull2 : Nat := 0x4ee0e000

/-- AES two-register crypto form (`Rn`/`Rd` only). Word: `base + Rn·0x20 + Rd`. -/
def encAesRR (base d n : Nat) : List (BitVec 8) :=
  wordLE (base + (n % 32) * 0x20 + (d % 32))

/-- Encode one crypto-extension `NCryptInst` to its A64 machine bytes (a single
    4-byte word), resolving register names through `alloc`. -/
def encodeNCryptInst (alloc : VAlloc) : NCryptInst → List (BitVec 8)
  | .aese d a   => encAesRR baseAese   (vNum (vOf alloc d)) (vNum (vOf alloc a))
  | .aesmc d a  => encAesRR baseAesmc  (vNum (vOf alloc d)) (vNum (vOf alloc a))
  | .aesd d a   => encAesRR baseAesd   (vNum (vOf alloc d)) (vNum (vOf alloc a))
  | .aesimc d a => encAesRR baseAesimc (vNum (vOf alloc d)) (vNum (vOf alloc a))
  | .pmull d a b  => encVecRRR basePmull  (vNum (vOf alloc d)) (vNum (vOf alloc a)) (vNum (vOf alloc b))
  | .pmull2 d a b => encVecRRR basePmull2 (vNum (vOf alloc d)) (vNum (vOf alloc a)) (vNum (vOf alloc b))

/-- Encode a whole crypto block: concatenate the 4-byte word encodings. -/
def encodeNCryptBlock (alloc : VAlloc) (block : List NCryptInst) : List (BitVec 8) :=
  block.flatMap (encodeNCryptInst alloc)

/-- The verified byte encoding of the AES single-round kernel body
    (`AESE v0, v1 ; AESMC v0, v0`), the 8-byte stream the bench diffs vs gas. -/
def aesRoundBytes : List (BitVec 8) :=
  let alloc : VAlloc := [("st", "v0"), ("rk", "v1")]
  encodeNCryptBlock alloc (lowerNCryptBlock (aesRoundBlk "st" "rk"))

/-- Every `NCryptInst` encodes to exactly 4 bytes (one fixed-width A64 word). -/
theorem encodeNCryptInst_length (alloc : VAlloc) (i : NCryptInst) :
    (encodeNCryptInst alloc i).length = 4 := by
  cases i <;> simp [encodeNCryptInst, encAesRR, encVecRRR, wordLE_length]

/-- `encodeNCryptBlock` produces `4 * |block|` bytes (a fixed-width stream). -/
theorem encodeNCryptBlock_length (alloc : VAlloc) (block : List NCryptInst) :
    (encodeNCryptBlock alloc block).length = 4 * block.length := by
  induction block with
  | nil => rfl
  | cons i is ih =>
      simp only [encodeNCryptBlock, List.flatMap_cons, List.length_append, List.length_cons]
      rw [show encodeNCryptBlock alloc is = is.flatMap (encodeNCryptInst alloc) from rfl] at ih
      rw [encodeNCryptInst_length, ih]; omega

/-! ## 7. Differential pins against `aarch64-linux-gnu-as -march=armv8-a+crypto`

These pin the emitted word to the exact little-endian bytes `as` produces. E.g.
`aese v0.16b, v1.16b` (gas word `0x4e284820`) is `[0x20,0x48,0x28,0x4e]`. -/

/-- `aese v0.16b, v1.16b` — gas word `0x4e284820`, little-endian `20 48 28 4e`. -/
example : encodeNCryptInst [("d","v0"),("a","v1")] (.aese "d" "a")
    = [0x20, 0x48, 0x28, 0x4e].map (BitVec.ofNat 8) := by native_decide

/-- `aesmc v0.16b, v1.16b` — gas word `0x4e286820`, little-endian `20 68 28 4e`. -/
example : encodeNCryptInst [("d","v0"),("a","v1")] (.aesmc "d" "a")
    = [0x20, 0x68, 0x28, 0x4e].map (BitVec.ofNat 8) := by native_decide

/-- `aesd v0.16b, v1.16b` — gas word `0x4e285820`, little-endian `20 58 28 4e`. -/
example : encodeNCryptInst [("d","v0"),("a","v1")] (.aesd "d" "a")
    = [0x20, 0x58, 0x28, 0x4e].map (BitVec.ofNat 8) := by native_decide

/-- `aesimc v0.16b, v1.16b` — gas word `0x4e287820`, little-endian `20 78 28 4e`. -/
example : encodeNCryptInst [("d","v0"),("a","v1")] (.aesimc "d" "a")
    = [0x20, 0x78, 0x28, 0x4e].map (BitVec.ofNat 8) := by native_decide

/-- `aese v2.16b, v3.16b` — gas word `0x4e284862`, little-endian `62 48 28 4e`. -/
example : encodeNCryptInst [("d","v2"),("a","v3")] (.aese "d" "a")
    = [0x62, 0x48, 0x28, 0x4e].map (BitVec.ofNat 8) := by native_decide

/-- `aesmc v4.16b, v5.16b` — gas word `0x4e2868a4`, little-endian `a4 68 28 4e`. -/
example : encodeNCryptInst [("d","v4"),("a","v5")] (.aesmc "d" "a")
    = [0xa4, 0x68, 0x28, 0x4e].map (BitVec.ofNat 8) := by native_decide

/-- `pmull v0.1q, v1.1d, v2.1d` — gas word `0x0ee2e020`, little-endian `20 e0 e2 0e`. -/
example : encodeNCryptInst [("d","v0"),("a","v1"),("b","v2")] (.pmull "d" "a" "b")
    = [0x20, 0xe0, 0xe2, 0x0e].map (BitVec.ofNat 8) := by native_decide

/-- `pmull2 v0.1q, v1.2d, v2.2d` — gas word `0x4ee2e020`, little-endian `20 e0 e2 4e`. -/
example : encodeNCryptInst [("d","v0"),("a","v1"),("b","v2")] (.pmull2 "d" "a" "b")
    = [0x20, 0xe0, 0xe2, 0x4e].map (BitVec.ofNat 8) := by native_decide

/-! ## 8. A crypto-extension round-trip: `decode (encode i) = i`

The crypto analogue of `SailNeonDecoder`: a Lean decoder `decodeCryptoWord`
that recovers each AES/PMULL instruction's class and operand fields, with
`decode (encode i) = i` proved for every emitted crypto-ext form. Unlike
`SailNeonDecoder`'s discriminant fields (bit slices at the positions the
sail-arm `decode64` ASIMD clauses read), `fldAesId`/`fldPmullId` below
discriminate by *subtracting the known register-field contribution back out of
the word* — i.e. they invert the encoder's own base-word arithmetic, not an
independent transcription of the sail-arm crypto `decode64` clauses
(`vector_crypto_aes_round`/`…_mix`, the PMULL three-register form). The
round-trip is real (`decode (encode i) = i` does hold), but the "decoder" here
is definitionally the encoder's base-word construction run in reverse.

For context: the Arm ARM places the AES class discriminants at
`op_code[31:14]` (the AES-constant prefix), `op_code[13]` (round vs mix), and
`op_code[12]` (`D`: E/D or MC/IMC), and the PMULL discriminant at
`op_code[31:21]` with `op_code[30]` picking PMULL vs PMULL2 — `fldAesId`/
`fldPmullId` land on the same class-equivalence by construction (register
fields stripped from the whole word), without slicing those named ranges
directly. The AES round/mix clauses share `Rd[4:0] Rn[9:5]` with the
scalar/ASIMD forms; the six class constants (`baseAese/0x400`, …, `basePmull`,
`basePmull2`) are pairwise distinct, which is what makes `fldAesId`/
`fldPmullId` discriminate the six forms exactly. -/

open CatCrypt.Crypto.SecureCompilation.ARMBackend.SailArmDecoder
  (leWord leWord_wordLE fldRd fldRn fldRm)

/-- The instruction-class constant of an AES (two-register) word: everything above
    the low 10 bits (`Rn[9:5] Rd[4:0]` occupy bits `[9:0]`, since `Rn,Rd < 32` give
    `Rn·0x20 + Rd < 0x400`). The four AES bases have distinct `fldAesId` values
    (`baseAese/0x400 … baseAesimc/0x400`), so it discriminates the AES forms
    exactly. -/
def fldAesId (w : Nat) : Nat := w / 0x400
/-- The instruction-class constant of a PMULL (three-register) word: the AES `Rd`,
    `Rn` slices plus the `Rm[20:16]` slice stripped out, leaving `w` with the
    register fields zeroed — i.e. the residual `w - Rm·0x10000 - Rn·0x20 - Rd`. The
    two PMULL bases (`basePmull`, `basePmull2`) have distinct residuals. -/
def fldPmullId (w : Nat) : Nat := w - fldRm w * 0x10000 - fldRn w * 0x20 - fldRd w

/-- The decoded crypto-extension instruction class. -/
inductive CryptoClass where
  /-- AESE (vector). -/
  | aese
  /-- AESMC (vector). -/
  | aesmc
  /-- AESD (vector). -/
  | aesd
  /-- AESIMC (vector). -/
  | aesimc
  /-- PMULL (low ⊗ low). -/
  | pmull
  /-- PMULL2 (high ⊗ high). -/
  | pmull2
  deriving DecidableEq, Repr

/-- A decoded crypto-extension instruction: its class plus the recovered operand
    fields (`Rd`, `Rn`, and `Rm` for the PMULL forms). -/
structure DecCrypto where
  cls : CryptoClass
  rd : Nat
  rn : Nat
  rm : Nat := 0
  deriving DecidableEq, Repr

/-- Decode a 32-bit crypto-extension word to its class + operand fields, following
    the sail-arm `vector_crypto_aes_round`/`…_mix` and PMULL clause dispatch. The
    AES two-register forms are discriminated by the class constant `fldAesId`
    (the base above the low-10-bit `Rn`/`Rd` window — `vector_crypto_aes_round`
    with the `D` bit, `vector_crypto_aes_mix` with the `D` bit); the PMULL
    three-register forms by `fldPmullId` (the base with `Rm`/`Rn`/`Rd` stripped). -/
def decodeCryptoWord (w : Nat) : Option DecCrypto :=
  if fldAesId w = baseAese / 0x400 then
    some { cls := .aese, rd := fldRd w, rn := fldRn w }
  else if fldAesId w = baseAesd / 0x400 then
    some { cls := .aesd, rd := fldRd w, rn := fldRn w }
  else if fldAesId w = baseAesmc / 0x400 then
    some { cls := .aesmc, rd := fldRd w, rn := fldRn w }
  else if fldAesId w = baseAesimc / 0x400 then
    some { cls := .aesimc, rd := fldRd w, rn := fldRn w }
  else if fldPmullId w = basePmull then
    some { cls := .pmull, rd := fldRd w, rn := fldRn w, rm := fldRm w }
  else if fldPmullId w = basePmull2 then
    some { cls := .pmull2, rd := fldRd w, rn := fldRn w, rm := fldRm w }
  else none

/-- Decode a 4-byte little-endian crypto-extension instruction stream. -/
def decodeCrypto (bs : List (BitVec 8)) : Option DecCrypto :=
  (leWord bs).bind decodeCryptoWord

/-! ### Field-recovery round-trips on the encoded words

For each crypto-ext form the decoder recovers exactly the class and operand
fields the encoder put in. The bounds `Rd,Rn,Rm < 32` make the field slices exact
(non-overlapping bit windows), so each slice reads back the planted value. -/

/-- **Round-trip for AESE.** -/
theorem roundtrip_aese (d n : Nat) (hd : d < 32) (hn : n < 32) :
    decodeCrypto (encAesRR baseAese d n)
      = some { cls := .aese, rd := d, rn := n } := by
  have hw : baseAese + (n % 32) * 0x20 + (d % 32) < 2 ^ 32 := by
    rw [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd, baseAese]; omega
  rw [encAesRR, decodeCrypto, leWord_wordLE _ hw, Option.bind_some,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd]
  set W := baseAese + n * 0x20 + d with hW
  have hid : fldAesId W = baseAese / 0x400 := by simp only [fldAesId, hW, baseAese]; omega
  have hrd : fldRd W = d := by simp only [fldRd, hW, baseAese]; omega
  have hrn : fldRn W = n := by simp only [fldRn, hW, baseAese]; omega
  rw [decodeCryptoWord, hrd, hrn, ite_eq_left hid]

/-- **Round-trip for AESMC.** -/
theorem roundtrip_aesmc (d n : Nat) (hd : d < 32) (hn : n < 32) :
    decodeCrypto (encAesRR baseAesmc d n)
      = some { cls := .aesmc, rd := d, rn := n } := by
  have hw : baseAesmc + (n % 32) * 0x20 + (d % 32) < 2 ^ 32 := by
    rw [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd, baseAesmc]; omega
  rw [encAesRR, decodeCrypto, leWord_wordLE _ hw, Option.bind_some,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd]
  set W := baseAesmc + n * 0x20 + d with hW
  have hid : fldAesId W = baseAesmc / 0x400 := by simp only [fldAesId, hW, baseAesmc]; omega
  have h1 : fldAesId W ≠ baseAese / 0x400 := by rw [hid]; decide
  have h2 : fldAesId W ≠ baseAesd / 0x400 := by rw [hid]; decide
  have hrd : fldRd W = d := by simp only [fldRd, hW, baseAesmc]; omega
  have hrn : fldRn W = n := by simp only [fldRn, hW, baseAesmc]; omega
  rw [decodeCryptoWord, hrd, hrn, ite_eq_right h1, ite_eq_right h2, ite_eq_left hid]

/-- **Round-trip for AESD.** -/
theorem roundtrip_aesd (d n : Nat) (hd : d < 32) (hn : n < 32) :
    decodeCrypto (encAesRR baseAesd d n)
      = some { cls := .aesd, rd := d, rn := n } := by
  have hw : baseAesd + (n % 32) * 0x20 + (d % 32) < 2 ^ 32 := by
    rw [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd, baseAesd]; omega
  rw [encAesRR, decodeCrypto, leWord_wordLE _ hw, Option.bind_some,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd]
  set W := baseAesd + n * 0x20 + d with hW
  have hid : fldAesId W = baseAesd / 0x400 := by simp only [fldAesId, hW, baseAesd]; omega
  have h1 : fldAesId W ≠ baseAese / 0x400 := by rw [hid]; decide
  have hrd : fldRd W = d := by simp only [fldRd, hW, baseAesd]; omega
  have hrn : fldRn W = n := by simp only [fldRn, hW, baseAesd]; omega
  rw [decodeCryptoWord, hrd, hrn, ite_eq_right h1, ite_eq_left hid]

/-- **Round-trip for AESIMC.** -/
theorem roundtrip_aesimc (d n : Nat) (hd : d < 32) (hn : n < 32) :
    decodeCrypto (encAesRR baseAesimc d n)
      = some { cls := .aesimc, rd := d, rn := n } := by
  have hw : baseAesimc + (n % 32) * 0x20 + (d % 32) < 2 ^ 32 := by
    rw [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd, baseAesimc]; omega
  rw [encAesRR, decodeCrypto, leWord_wordLE _ hw, Option.bind_some,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd]
  set W := baseAesimc + n * 0x20 + d with hW
  have hid : fldAesId W = baseAesimc / 0x400 := by simp only [fldAesId, hW, baseAesimc]; omega
  have h1 : fldAesId W ≠ baseAese / 0x400 := by rw [hid]; decide
  have h2 : fldAesId W ≠ baseAesd / 0x400 := by rw [hid]; decide
  have h3 : fldAesId W ≠ baseAesmc / 0x400 := by rw [hid]; decide
  have hrd : fldRd W = d := by simp only [fldRd, hW, baseAesimc]; omega
  have hrn : fldRn W = n := by simp only [fldRn, hW, baseAesimc]; omega
  rw [decodeCryptoWord, hrd, hrn, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_left hid]

/-- The AES class constants are all distinct from the PMULL `fldAesId` of a PMULL
    word (the PMULL base + `Rm` term lands `fldAesId` far above the AES ids), so the
    AES branches are skipped on a PMULL word. -/
theorem pmull_not_aes (base m n d : Nat) (hbase : base = basePmull ∨ base = basePmull2)
    (_hm : m < 32) (hn : n < 32) (hd : d < 32) :
    let W := base + m * 0x10000 + n * 0x20 + d
    fldAesId W ≠ baseAese / 0x400 ∧ fldAesId W ≠ baseAesd / 0x400 ∧
    fldAesId W ≠ baseAesmc / 0x400 ∧ fldAesId W ≠ baseAesimc / 0x400 := by
  rcases hbase with h | h <;> subst h <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [fldAesId, basePmull, basePmull2, baseAese, baseAesd, baseAesmc, baseAesimc] <;> omega

/-- **Round-trip for PMULL.** -/
theorem roundtrip_pmull (d n m : Nat) (hd : d < 32) (hn : n < 32) (hm : m < 32) :
    decodeCrypto (encVecRRR basePmull d n m)
      = some { cls := .pmull, rd := d, rn := n, rm := m } := by
  have hw : basePmull + (m % 32) * 0x10000 + (n % 32) * 0x20 + (d % 32) < 2 ^ 32 := by
    rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd, basePmull]; omega
  rw [encVecRRR, decodeCrypto, leWord_wordLE _ hw, Option.bind_some,
    Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd]
  set W := basePmull + m * 0x10000 + n * 0x20 + d with hW
  have hrd : fldRd W = d := by simp only [fldRd, hW, basePmull]; omega
  have hrn : fldRn W = n := by simp only [fldRn, hW, basePmull]; omega
  have hrm : fldRm W = m := by simp only [fldRm, hW, basePmull]; omega
  have hpid : fldPmullId W = basePmull := by
    rw [fldPmullId, hrd, hrn, hrm, hW]; simp only [basePmull]; omega
  obtain ⟨h1, h2, h3, h4⟩ := pmull_not_aes basePmull m n d (Or.inl rfl) hm hn hd
  rw [decodeCryptoWord, hrd, hrn, hrm, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4, ite_eq_left hpid]

/-- **Round-trip for PMULL2.** -/
theorem roundtrip_pmull2 (d n m : Nat) (hd : d < 32) (hn : n < 32) (hm : m < 32) :
    decodeCrypto (encVecRRR basePmull2 d n m)
      = some { cls := .pmull2, rd := d, rn := n, rm := m } := by
  have hw : basePmull2 + (m % 32) * 0x10000 + (n % 32) * 0x20 + (d % 32) < 2 ^ 32 := by
    rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd, basePmull2]; omega
  rw [encVecRRR, decodeCrypto, leWord_wordLE _ hw, Option.bind_some,
    Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd]
  set W := basePmull2 + m * 0x10000 + n * 0x20 + d with hW
  have hrd : fldRd W = d := by simp only [fldRd, hW, basePmull2]; omega
  have hrn : fldRn W = n := by simp only [fldRn, hW, basePmull2]; omega
  have hrm : fldRm W = m := by simp only [fldRm, hW, basePmull2]; omega
  have hpid : fldPmullId W = basePmull2 := by
    rw [fldPmullId, hrd, hrn, hrm, hW]; simp only [basePmull2]; omega
  have hpid1 : fldPmullId W ≠ basePmull := by rw [hpid]; decide
  obtain ⟨h1, h2, h3, h4⟩ := pmull_not_aes basePmull2 m n d (Or.inr rfl) hm hn hd
  rw [decodeCryptoWord, hrd, hrn, hrm, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4,
    ite_eq_right hpid1, ite_eq_left hpid]

/-! ### Instruction-level round-trip: `decode (encode i) = i`

A `rebuildCrypto` reading the `DecCrypto` class + register numbers back into an
`NCryptInst` over the allocated names, and the capstone theorems
`roundtrip_ncrypt_*` proving `rebuild (decode (encode i)) = i`. `vNum` guarantees
the register numbers are `< 32`, so no side condition leaks. -/

open CatCrypt.Crypto.SecureCompilation.ARMBackend.Neon.SailNeonDecoder (regName vNum_lt_32)

/-- Rebuild an `NCryptInst` from a decoded `DecCrypto`, mapping register numbers
    back to `vN` names. -/
def rebuildCrypto (dr : DecCrypto) : Option NCryptInst :=
  match dr.cls with
  | .aese => some (.aese (regName dr.rd) (regName dr.rn))
  | .aesmc => some (.aesmc (regName dr.rd) (regName dr.rn))
  | .aesd => some (.aesd (regName dr.rd) (regName dr.rn))
  | .aesimc => some (.aesimc (regName dr.rd) (regName dr.rn))
  | .pmull => some (.pmull (regName dr.rd) (regName dr.rn) (regName dr.rm))
  | .pmull2 => some (.pmull2 (regName dr.rd) (regName dr.rn) (regName dr.rm))

/-- **Capstone round-trip for AESE.** -/
theorem roundtrip_ncrypt_aese (alloc : VAlloc) (d a : String)
    (hd : regName (vNum (vOf alloc d)) = vOf alloc d)
    (ha : regName (vNum (vOf alloc a)) = vOf alloc a) :
    (decodeCrypto (encodeNCryptInst alloc (.aese d a))).bind rebuildCrypto
      = some (.aese (vOf alloc d) (vOf alloc a)) := by
  simp only [encodeNCryptInst]
  rw [roundtrip_aese _ _ (vNum_lt_32 _) (vNum_lt_32 _)]
  simp only [Option.bind_some, rebuildCrypto]
  rw [hd, ha]

/-- Capstone round-trip for AESMC. -/
theorem roundtrip_ncrypt_aesmc (alloc : VAlloc) (d a : String)
    (hd : regName (vNum (vOf alloc d)) = vOf alloc d)
    (ha : regName (vNum (vOf alloc a)) = vOf alloc a) :
    (decodeCrypto (encodeNCryptInst alloc (.aesmc d a))).bind rebuildCrypto
      = some (.aesmc (vOf alloc d) (vOf alloc a)) := by
  simp only [encodeNCryptInst]
  rw [roundtrip_aesmc _ _ (vNum_lt_32 _) (vNum_lt_32 _)]
  simp only [Option.bind_some, rebuildCrypto]
  rw [hd, ha]

/-- Capstone round-trip for AESD. -/
theorem roundtrip_ncrypt_aesd (alloc : VAlloc) (d a : String)
    (hd : regName (vNum (vOf alloc d)) = vOf alloc d)
    (ha : regName (vNum (vOf alloc a)) = vOf alloc a) :
    (decodeCrypto (encodeNCryptInst alloc (.aesd d a))).bind rebuildCrypto
      = some (.aesd (vOf alloc d) (vOf alloc a)) := by
  simp only [encodeNCryptInst]
  rw [roundtrip_aesd _ _ (vNum_lt_32 _) (vNum_lt_32 _)]
  simp only [Option.bind_some, rebuildCrypto]
  rw [hd, ha]

/-- Capstone round-trip for AESIMC. -/
theorem roundtrip_ncrypt_aesimc (alloc : VAlloc) (d a : String)
    (hd : regName (vNum (vOf alloc d)) = vOf alloc d)
    (ha : regName (vNum (vOf alloc a)) = vOf alloc a) :
    (decodeCrypto (encodeNCryptInst alloc (.aesimc d a))).bind rebuildCrypto
      = some (.aesimc (vOf alloc d) (vOf alloc a)) := by
  simp only [encodeNCryptInst]
  rw [roundtrip_aesimc _ _ (vNum_lt_32 _) (vNum_lt_32 _)]
  simp only [Option.bind_some, rebuildCrypto]
  rw [hd, ha]

/-- Capstone round-trip for PMULL. -/
theorem roundtrip_ncrypt_pmull (alloc : VAlloc) (d a b : String)
    (hd : regName (vNum (vOf alloc d)) = vOf alloc d)
    (ha : regName (vNum (vOf alloc a)) = vOf alloc a)
    (hb : regName (vNum (vOf alloc b)) = vOf alloc b) :
    (decodeCrypto (encodeNCryptInst alloc (.pmull d a b))).bind rebuildCrypto
      = some (.pmull (vOf alloc d) (vOf alloc a) (vOf alloc b)) := by
  simp only [encodeNCryptInst]
  rw [roundtrip_pmull _ _ _ (vNum_lt_32 _) (vNum_lt_32 _)
    (vNum_lt_32 _)]
  simp only [Option.bind_some, rebuildCrypto]
  rw [hd, ha, hb]

/-- Capstone round-trip for PMULL2. -/
theorem roundtrip_ncrypt_pmull2 (alloc : VAlloc) (d a b : String)
    (hd : regName (vNum (vOf alloc d)) = vOf alloc d)
    (ha : regName (vNum (vOf alloc a)) = vOf alloc a)
    (hb : regName (vNum (vOf alloc b)) = vOf alloc b) :
    (decodeCrypto (encodeNCryptInst alloc (.pmull2 d a b))).bind rebuildCrypto
      = some (.pmull2 (vOf alloc d) (vOf alloc a) (vOf alloc b)) := by
  simp only [encodeNCryptInst]
  rw [roundtrip_pmull2 _ _ _ (vNum_lt_32 _) (vNum_lt_32 _)
    (vNum_lt_32 _)]
  simp only [Option.bind_some, rebuildCrypto]
  rw [hd, ha, hb]

end CatCrypt.Crypto.SecureCompilation.ARMBackend.Neon.Crypto
