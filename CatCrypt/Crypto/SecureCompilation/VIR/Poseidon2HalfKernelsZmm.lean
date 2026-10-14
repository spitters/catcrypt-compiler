/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.KeccakThetaPiCom
public import CatCrypt.Crypto.SecureCompilation.X86Backend.KeccakThetaPiCom
public meta import CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent
public import CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Data.BitVec

/-!
# Poseidon2 BabyBear per-lane half-kernels on the unified `Com jasminDialect` (AVX-512 ZMM)

The four owned ZMM Poseidon2 half-kernels the permute driver
`p3_poseidon2_perm_zmm` (`Plonky3OrchLoopsEmit`) calls —
`zm_tomont_half_ptr` / `zm_frommont_half_ptr` / `zm_extround_half_ptr` /
`zm_intdiag_half_ptr` — are per-lane BabyBear single-pass-Montgomery field
arithmetic over the 8×u64 lanes of a `reg 512` ZMM register. Their field algorithm
(mirroring `poseidon2_avx512_mont_kernels`):

```
montreduce(t) = csub( ((t & MASK)·NPI & MASK)·P + t  >> 32 )
montmul(a,b)  = montreduce( (a & MASK)·(b & MASK) )
fadd(a,b)     = csub(a + b)
sbox(x)       = montmul(montmul(x², x²), montmul(x², x))    -- x⁷
```

Every op is a per-lane `zmmPackQ bop` (`vpaddq`/`vpsubq`/`vpmullq`/`vpandq`/
`vpsrlvq`), so the half-kernels ride the carry-free `vpackZMM` fragment of
`Com jasminDialect` — the same alphabet as `ButterflyBlockCom` /
`KeccakThetaPiCom`. There is no cross-lane traffic in a half-kernel: the M4 MDS
and the internal-round column sum are the SEPARATE cross-lane glue, carried at
the `zmmPerm`/`vshuffle σ` level by `Poseidon2MdsPermUnified` (`m4Zmm_lanes`,
`colsum_vec_eq_scalar`) with the emit-side permute leaf a Tier-B KAT.

The single subtlety is `csub`'s sign broadcast. The scalar reference uses an
arithmetic shift; over the carry-free binop alphabet the mask is built with a
logical shift and a negate — `s = t ≫ 63` (0/1), `m = 0 − s` (0 / all-ones),
`keep = m & P`, `out = t + keep` — denotationally the same branchless conditional
subtract, using only `vpsrlvq`/`vpsubq`/`vpandq`/`vpaddq`.

## What is proved

* the four half-kernel **vector bodies** as nested `zmmPackQ` expressions
  (`tomontVec` / `frommontVec` / `extroundVec` / `intdiagVec`), and
* their **per-lane denotation** against the scalar BabyBear reference
  (`tomontVec_lane` / … ): lane `k` of the packed body equals the scalar
  BabyBear `montmul`/`montreduce`/`sbox`/diagonal of lane `k` of the inputs,
  given the constant registers hold the BabyBear constants in every lane.

The four half-kernel `Com jasminDialect` producers and their `*_denote` pins
(`Com` denotation = vector body):

* `frommontCom` / `tomontCom` — straight-line `vpackZMM` chains (11 / 14
  bindings), pinned by the `denote_var_vpackZMM` peel;
* `intdiagCom` / `extroundCom` — composed by `spliceCom` (`FieldDialectBlockDescent`)
  from the `montmul` block (`tomontCom`) and the `fadd` block (`faddCom`), whose
  `montmul`/`fadd` fragments are renamed into the growing context. Composition
  keeps both the def and the `*_denote` proof independent of the kernel's binding
  count, where the flat `vpackZMM` chain hits the elaborator's dialect-propagation
  depth (~15 bindings) and the peel-chain's heartbeat budget.

`*Com_lane` composes each pin with the per-lane theorem: lane `k` of the emitted
`Com`'s denotation is the scalar BabyBear reference. The `Com`s lower to owned
AT&T `.s` through `VpackZmmAsmPrint.renderVpackZmmComAutoZmm`.

The lane proofs are pure `zmmPackQ_lane` peels: each packed op's lane is the
scalar `JasminBinOp.applyLane` of the input lanes, so the whole body's lane function
is the scalar BabyBear reference by construction — no numeric reasoning, no
`Avx512Model`, no `native_decide`.

## Main results

* `tomontL` / `frommontL` / `extroundL` / `intdiagL` — the scalar BabyBear
  half-kernel references over `BitVec 64`.
* `tomontVec` / `frommontVec` / `extroundVec` / `intdiagVec` — the packed
  `BitVec 512` bodies as nested `zmmPackQ`.
* `tomontVec_lane` / `frommontVec_lane` / `extroundVec_lane` / `intdiagVec_lane`
  — each packed body's lane `k` equals the scalar BabyBear op on the input lane.
* `csubCom` / `faddCom` and `csubCom_denote` / `faddCom_denote` / `csubCom_lane`
  — the `Com jasminDialect` emit path for the reduce/add fragments, pinning
  `Com.denote` to the vector body and composing to the scalar reference.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2HalfKernelsZmm

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.KeccakThetaPiCom

/-! ## 0. The 8×u64 ZMM lane round-trip and per-lane `zmmPackQ`

The qword lane bridges, proved locally (the pattern shared by every abstract-`Com`
tie module): only `JasminDialect`'s lane defs and Mathlib's `BitVec` lemmas. -/

/-- Reading lane `k` of an assembled 8-lane ZMM register recovers the lane value. -/
theorem zmmOfLanes_zmmLane' (f : Fin 8 → BitVec 64) (k : Fin 8) :
    zmmLane (zmmOfLanes f) k = f k := by
  fin_cases k <;>
    (unfold zmmLane zmmOfLanes
     norm_num [Fin.val_ofNat, BitVec.extractLsb'_append_eq_of_le,
       BitVec.extractLsb'_append_eq_of_add_le, BitVec.extractLsb'_append_eq_right,
       BitVec.extractLsb'_append_eq_left]) <;>
    rfl

/-- Lane `k` of `zmmPackQ bop a b` is `bop.applyLane (zmmLane a k) (zmmLane b k)`. -/
theorem packQ_lane (bop : JasminBinOp) (a b : BitVec 512) (k : Fin 8) :
    zmmLane (zmmPackQ bop a b) k = bop.applyLane (zmmLane a k) (zmmLane b k) := by
  unfold zmmPackQ
  rw [zmmOfLanes_zmmLane']

/-! ## 1. The scalar BabyBear per-lane reference (`BitVec 64`)

Each is the exact 64-bit-lane arithmetic `poseidon2_avx512_mont_kernels` computes;
the constants (`NPI`/`P`/`MASK`/`RSQR`) and the shift amounts (`32`/`63`) are
parameters, so a lane theorem instantiates them with the lane values of the
broadcast constant registers. `z` is the zero register's lane (`0`); `sh32`/`sh63`
are the shift-amount registers' lanes (`32`/`63`). -/

/-- Branchless canonical reduce `csub(y) = if y ≥ P then y − P else y`, over the
    carry-free binop alphabet: `t = y − P`, `s = t ≫ sh63` (0/1), `m = z − s`
    (0 / all-ones with `z = 0`), `keep = m & P`, `out = t + keep`. -/
def csubL (y P : BitVec 64) (sh63 : Nat) (z : BitVec 64) : BitVec 64 :=
  (y - P) + ((z - ((y - P) >>> sh63)) &&& P)

/-- `montreduce(t) = csub( ((t & MASK)·NPI & MASK)·P + t  ≫ 32 )`. -/
def montReduceL (t NPI P MASK : BitVec 64) (sh32 sh63 : Nat) (z : BitVec 64) : BitVec 64 :=
  csubL ((((((t &&& MASK) * NPI) &&& MASK) * P) + t) >>> sh32) P sh63 z

/-- `montmul(a,b) = montreduce( (a & MASK)·(b & MASK) )`. -/
def montMulL (a b NPI P MASK : BitVec 64) (sh32 sh63 : Nat) (z : BitVec 64) : BitVec 64 :=
  montReduceL ((a &&& MASK) * (b &&& MASK)) NPI P MASK sh32 sh63 z

/-- `fadd(a,b) = csub(a + b)`. -/
def faddL (a b P : BitVec 64) (sh63 : Nat) (z : BitVec 64) : BitVec 64 :=
  csubL (a + b) P sh63 z

/-- `sbox(x) = x⁷ = montmul(montmul(x²,x²), montmul(x²,x))`. -/
def sboxL (x NPI P MASK : BitVec 64) (sh32 sh63 : Nat) (z : BitVec 64) : BitVec 64 :=
  let x2 := montMulL x x NPI P MASK sh32 sh63 z
  let x4 := montMulL x2 x2 NPI P MASK sh32 sh63 z
  let t := montMulL x2 x NPI P MASK sh32 sh63 z
  montMulL x4 t NPI P MASK sh32 sh63 z

/-- `zm_tomont_half(v) = montmul(v, RSQR)`. -/
def tomontL (v RSQR NPI P MASK : BitVec 64) (sh32 sh63 : Nat) (z : BitVec 64) : BitVec 64 :=
  montMulL v RSQR NPI P MASK sh32 sh63 z

/-- `zm_frommont_half(v) = montreduce(v)`. -/
def frommontL (v NPI P MASK : BitVec 64) (sh32 sh63 : Nat) (z : BitVec 64) : BitVec 64 :=
  montReduceL v NPI P MASK sh32 sh63 z

/-- `zm_extround_half(v,c) = sbox(fadd(v,c))`. -/
def extroundL (v c NPI P MASK : BitVec 64) (sh32 sh63 : Nat) (z : BitVec 64) : BitVec 64 :=
  sboxL (faddL v c P sh63 z) NPI P MASK sh32 sh63 z

/-- `zm_intdiag_half(d,v,sum) = fadd(montmul(d,v), sum)`. -/
def intdiagL (d v sum NPI P MASK : BitVec 64) (sh32 sh63 : Nat) (z : BitVec 64) : BitVec 64 :=
  faddL (montMulL d v NPI P MASK sh32 sh63 z) sum P sh63 z

/-! ## 2. The packed `BitVec 512` half-kernel bodies (nested `zmmPackQ`)

The vector bodies: each scalar op is the per-lane packed op `zmmPackQ bop`. The
constant registers (`NPI`/`P`/`MASK`/`RSQR`/`c32`/`c63`/`zero`) are broadcast
`reg 512` operands. -/

/-- Packed branchless `csub`: `zmmPackQ`-lane image of `csubL`. -/
def csubVec (y P c63 zero : BitVec 512) : BitVec 512 :=
  let t := zmmPackQ .sub y P
  let s := zmmPackQ .shr t c63
  let m := zmmPackQ .sub zero s
  let keep := zmmPackQ .and m P
  zmmPackQ .add t keep

/-- Packed `montreduce`. -/
def montReduceVec (t NPI P MASK c32 c63 zero : BitVec 512) : BitVec 512 :=
  let tm := zmmPackQ .and t MASK
  let mm := zmmPackQ .mul tm NPI
  let mi := zmmPackQ .and mm MASK
  let mp := zmmPackQ .mul mi P
  let u := zmmPackQ .add mp t
  let sh := zmmPackQ .shr u c32
  csubVec sh P c63 zero

/-- Packed `montmul`. -/
def montMulVec (a b NPI P MASK c32 c63 zero : BitVec 512) : BitVec 512 :=
  let am := zmmPackQ .and a MASK
  let bm := zmmPackQ .and b MASK
  montReduceVec (zmmPackQ .mul am bm) NPI P MASK c32 c63 zero

/-- Packed `fadd`. -/
def faddVec (a b P c63 zero : BitVec 512) : BitVec 512 :=
  csubVec (zmmPackQ .add a b) P c63 zero

/-- Packed `sbox` (x⁷). -/
def sboxVec (x NPI P MASK c32 c63 zero : BitVec 512) : BitVec 512 :=
  let x2 := montMulVec x x NPI P MASK c32 c63 zero
  let x4 := montMulVec x2 x2 NPI P MASK c32 c63 zero
  let t := montMulVec x2 x NPI P MASK c32 c63 zero
  montMulVec x4 t NPI P MASK c32 c63 zero

/-- Packed `zm_tomont_half`. -/
def tomontVec (v RSQR NPI P MASK c32 c63 zero : BitVec 512) : BitVec 512 :=
  montMulVec v RSQR NPI P MASK c32 c63 zero

/-- Packed `zm_frommont_half`. -/
def frommontVec (v NPI P MASK c32 c63 zero : BitVec 512) : BitVec 512 :=
  montReduceVec v NPI P MASK c32 c63 zero

/-- Packed `zm_extround_half`. -/
def extroundVec (v c NPI P MASK c32 c63 zero : BitVec 512) : BitVec 512 :=
  sboxVec (faddVec v c P c63 zero) NPI P MASK c32 c63 zero

/-- Packed `zm_intdiag_half`. -/
def intdiagVec (d v sum NPI P MASK c32 c63 zero : BitVec 512) : BitVec 512 :=
  faddVec (montMulVec d v NPI P MASK c32 c63 zero) sum P c63 zero

/-! ## 3. Per-lane denotation against the scalar BabyBear reference

Lane `k` of each packed body is the scalar BabyBear reference of lane `k` of the
inputs — each `zmmPackQ_lane` peel turns a packed op's lane into the scalar
`JasminBinOp.applyLane` of the input lanes. -/

/-- Lane `k` of `csubVec` is `csubL` of the lanes. -/
theorem csubVec_lane (y P c63 zero : BitVec 512) (k : Fin 8) :
    zmmLane (csubVec y P c63 zero) k
      = csubL (zmmLane y k) (zmmLane P k) (zmmLane c63 k).toNat (zmmLane zero k) := by
  simp only [csubVec, csubL, packQ_lane, JasminBinOp.applyLane]

/-- Lane `k` of `montReduceVec` is `montReduceL` of the lanes. -/
theorem montReduceVec_lane (t NPI P MASK c32 c63 zero : BitVec 512) (k : Fin 8) :
    zmmLane (montReduceVec t NPI P MASK c32 c63 zero) k
      = montReduceL (zmmLane t k) (zmmLane NPI k) (zmmLane P k) (zmmLane MASK k)
          (zmmLane c32 k).toNat (zmmLane c63 k).toNat (zmmLane zero k) := by
  simp only [montReduceVec, montReduceL, csubVec_lane, csubL, packQ_lane, JasminBinOp.applyLane]

/-- Lane `k` of `montMulVec` is `montMulL` of the lanes. -/
theorem montMulVec_lane (a b NPI P MASK c32 c63 zero : BitVec 512) (k : Fin 8) :
    zmmLane (montMulVec a b NPI P MASK c32 c63 zero) k
      = montMulL (zmmLane a k) (zmmLane b k) (zmmLane NPI k) (zmmLane P k) (zmmLane MASK k)
          (zmmLane c32 k).toNat (zmmLane c63 k).toNat (zmmLane zero k) := by
  simp only [montMulVec, montMulL, montReduceVec_lane, packQ_lane, JasminBinOp.applyLane]

/-- Lane `k` of `faddVec` is `faddL` of the lanes. -/
theorem faddVec_lane (a b P c63 zero : BitVec 512) (k : Fin 8) :
    zmmLane (faddVec a b P c63 zero) k
      = faddL (zmmLane a k) (zmmLane b k) (zmmLane P k) (zmmLane c63 k).toNat (zmmLane zero k) := by
  simp only [faddVec, faddL, csubVec_lane, packQ_lane, JasminBinOp.applyLane]

/-- Lane `k` of `sboxVec` is `sboxL` of the lane. -/
theorem sboxVec_lane (x NPI P MASK c32 c63 zero : BitVec 512) (k : Fin 8) :
    zmmLane (sboxVec x NPI P MASK c32 c63 zero) k
      = sboxL (zmmLane x k) (zmmLane NPI k) (zmmLane P k) (zmmLane MASK k)
          (zmmLane c32 k).toNat (zmmLane c63 k).toNat (zmmLane zero k) := by
  simp only [sboxVec, sboxL, montMulVec_lane]

/-- **`zm_tomont_half` lane denotation.** Lane `k` is the scalar BabyBear
    `montmul(v, RSQR)`. -/
theorem tomontVec_lane (v RSQR NPI P MASK c32 c63 zero : BitVec 512) (k : Fin 8) :
    zmmLane (tomontVec v RSQR NPI P MASK c32 c63 zero) k
      = tomontL (zmmLane v k) (zmmLane RSQR k) (zmmLane NPI k) (zmmLane P k) (zmmLane MASK k)
          (zmmLane c32 k).toNat (zmmLane c63 k).toNat (zmmLane zero k) := by
  simp only [tomontVec, tomontL, montMulVec_lane]

/-- **`zm_frommont_half` lane denotation.** Lane `k` is the scalar BabyBear
    `montreduce(v)`. -/
theorem frommontVec_lane (v NPI P MASK c32 c63 zero : BitVec 512) (k : Fin 8) :
    zmmLane (frommontVec v NPI P MASK c32 c63 zero) k
      = frommontL (zmmLane v k) (zmmLane NPI k) (zmmLane P k) (zmmLane MASK k)
          (zmmLane c32 k).toNat (zmmLane c63 k).toNat (zmmLane zero k) := by
  simp only [frommontVec, frommontL, montReduceVec_lane]

/-- **`zm_extround_half` lane denotation.** Lane `k` is the scalar BabyBear
    `sbox(fadd(v, c))`. -/
theorem extroundVec_lane (v c NPI P MASK c32 c63 zero : BitVec 512) (k : Fin 8) :
    zmmLane (extroundVec v c NPI P MASK c32 c63 zero) k
      = extroundL (zmmLane v k) (zmmLane c k) (zmmLane NPI k) (zmmLane P k) (zmmLane MASK k)
          (zmmLane c32 k).toNat (zmmLane c63 k).toNat (zmmLane zero k) := by
  simp only [extroundVec, extroundL, sboxVec_lane, faddVec_lane]

/-- **`zm_intdiag_half` lane denotation.** Lane `k` is the scalar BabyBear
    `fadd(montmul(d, v), sum)`. -/
theorem intdiagVec_lane (d v sum NPI P MASK c32 c63 zero : BitVec 512) (k : Fin 8) :
    zmmLane (intdiagVec d v sum NPI P MASK c32 c63 zero) k
      = intdiagL (zmmLane d k) (zmmLane v k) (zmmLane sum k) (zmmLane NPI k) (zmmLane P k)
          (zmmLane MASK k) (zmmLane c32 k).toNat (zmmLane c63 k).toNat (zmmLane zero k) := by
  simp only [intdiagVec, intdiagL, faddVec_lane, montMulVec_lane]

/-! ## 4. The building-block `Com jasminDialect` producers and the owned `.s`

`csubCom` / `faddCom` are the two building-block half-kernel fragments as
straight-line `vpackZMM` `Com jasminDialect` programs. Their `*_denote` pins tie
`Com.denote` to the vector body (`csubVec` / `faddVec`), so the per-lane
denotation theorems above apply to the emitted `Com`. `denote_var_vpackZMM`
(KeccakThetaPiCom) peels one binding per `rw`. The larger kernels
(`montreduce`/`montmul`/`sbox` and the four exports) are the same straight-line
`vpackZMM` chains, assembled from these fragments. -/

abbrev r512 : JasminTy := .reg 512

/-- The `csub` input context `[y, P, c63, zero]`, each `reg 512`. -/
abbrev csubCtx : Ctxt jasminDialect := [r512, r512, r512, r512]

/-- `csub` as a straight-line `vpackZMM` `Com`: `t = y − P`, `s = t ≫ c63`,
    `m = zero − s`, `keep = m & P`, `out = t + keep`. -/
def csubCom : Com jasminDialect csubCtx r512 :=
  -- t = sub y P   (y = .here, P = .there .here)
  .var (.mk (.vpackZMM .sub) rfl (.cons .here (.cons (.there .here) .nil)))
    -- s = shr t c63   (t = .here, c63 = idx3)
    (.var (.mk (.vpackZMM .shr) rfl
            (.cons .here (.cons (.there (.there (.there .here))) .nil)))
      -- m = sub zero s   (zero = idx5, s = .here)
      (.var (.mk (.vpackZMM .sub) rfl
              (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil)))
        -- keep = and m P   (m = .here, P = idx4)
        (.var (.mk (.vpackZMM .and) rfl
                (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil)))
          -- out = add t keep   (t = idx3, keep = .here)
          (.var (.mk (.vpackZMM .add) rfl
                  (.cons (.there (.there (.there .here))) (.cons .here .nil)))
            (.ret .here)))))

/-- **`csubCom` denotation pin.** Denotes to the packed `csubVec`. -/
theorem csubCom_denote (y P c63 zero : BitVec 512) :
    csubCom.denote (.cons y (.cons P (.cons c63 (.cons zero .nil))))
      = csubVec y P c63 zero := by
  rw [csubCom, denote_var_vpackZMM, denote_var_vpackZMM, denote_var_vpackZMM,
    denote_var_vpackZMM, denote_var_vpackZMM]
  simp only [csubVec, Com.denote, lookup_here_extend, lookup_there_extend]
  rfl

/-- The `fadd` input context `[a, b, P, c63, zero]`, each `reg 512`. -/
abbrev faddCtx : Ctxt jasminDialect := [r512, r512, r512, r512, r512]

/-- `fadd` as a straight-line `vpackZMM` `Com`: `s0 = a + b`, then the `csub`
    chain on `s0`. -/
def faddCom : Com jasminDialect faddCtx r512 :=
  -- s0 = add a b   (a = .here, b = .there .here)
  .var (.mk (.vpackZMM .add) rfl (.cons .here (.cons (.there .here) .nil)))
    -- t = sub s0 P   (s0 = .here, P = idx3)
    (.var (.mk (.vpackZMM .sub) rfl
            (.cons .here (.cons (.there (.there (.there .here))) .nil)))
      -- s = shr t c63   (t = .here, c63 = idx5)
      (.var (.mk (.vpackZMM .shr) rfl
              (.cons .here (.cons (.there (.there (.there (.there (.there .here))))) .nil)))
        -- m = sub zero s   (zero = idx7, s = .here)
        (.var (.mk (.vpackZMM .sub) rfl
                (.cons (.there (.there (.there (.there (.there (.there (.there .here)))))))
                  (.cons .here .nil)))
          -- keep = and m P   (m = .here, P = idx6)
          (.var (.mk (.vpackZMM .and) rfl
                  (.cons .here
                    (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)))
            -- out = add t keep   (t = idx3, keep = .here)
            (.var (.mk (.vpackZMM .add) rfl
                    (.cons (.there (.there (.there .here))) (.cons .here .nil)))
              (.ret .here))))))

/-- **`faddCom` denotation pin.** Denotes to the packed `faddVec`. -/
theorem faddCom_denote (a b P c63 zero : BitVec 512) :
    faddCom.denote (.cons a (.cons b (.cons P (.cons c63 (.cons zero .nil)))))
      = faddVec a b P c63 zero := by
  rw [faddCom, denote_var_vpackZMM, denote_var_vpackZMM, denote_var_vpackZMM,
    denote_var_vpackZMM, denote_var_vpackZMM, denote_var_vpackZMM]
  simp only [faddVec, csubVec, Com.denote, lookup_here_extend, lookup_there_extend]
  rfl

/-- **`csubCom` per-lane BabyBear tie.** Composing `csubCom_denote` with
    `csubVec_lane`: lane `k` of the emitted `csub` `Com` is the scalar branchless
    reduce of lane `k`. -/
theorem csubCom_lane (y P c63 zero : BitVec 512) (k : Fin 8) :
    zmmLane (csubCom.denote (.cons y (.cons P (.cons c63 (.cons zero .nil))))) k
      = csubL (zmmLane y k) (zmmLane P k) (zmmLane c63 k).toNat (zmmLane zero k) := by
  rw [csubCom_denote, csubVec_lane]

/-! ## 5. The four full half-kernel `Com jasminDialect` producers

Each is one straight-line `vpackZMM` chain, de-Bruijn-indexed by the scheme:
after `s−1` prior bindings, an input at original index `i` is at `i + s − 1`, and
an intermediate produced by step `t` is at `s − 1 − t`. `zmmLane`-projecting the
denote pin composes with the per-lane theorem to the scalar BabyBear reference. -/

/-- The `frommont` (montreduce) input context `[v, NPI, P, MASK, c32, c63, zero]`,
    each `reg 512`. -/
abbrev frommontCtx : Ctxt jasminDialect := [r512, r512, r512, r512, r512, r512, r512]

/-- `zm_frommont_half(v) = montreduce(v)` as a straight-line `vpackZMM` `Com`. -/
def frommontCom : Com jasminDialect frommontCtx r512 :=
  -- s1  tm = and v MASK        (v=0, MASK=3)
  .var (.mk (.vpackZMM .and) rfl
          (.cons .here (.cons (.there (.there (.there .here))) .nil)))
  -- s2  mm = mul tm NPI        (tm=0, NPI=2)
  (.var (.mk (.vpackZMM .mul) rfl
          (.cons .here (.cons (.there (.there .here)) .nil)))
  -- s3  mi = and mm MASK       (mm=0, MASK=5)
  (.var (.mk (.vpackZMM .and) rfl
          (.cons .here (.cons (.there (.there (.there (.there (.there .here))))) .nil)))
  -- s4  mp = mul mi P          (mi=0, P=5)
  (.var (.mk (.vpackZMM .mul) rfl
          (.cons .here (.cons (.there (.there (.there (.there (.there .here))))) .nil)))
  -- s5  u = add mp v           (mp=0, v=4)
  (.var (.mk (.vpackZMM .add) rfl
          (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil)))
  -- s6  sh = shr u c32         (u=0, c32=9)
  (.var (.mk (.vpackZMM .shr) rfl
          (.cons .here
            (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
              .nil)))
  -- s7  t = sub sh P           (sh=0, P=8)
  (.var (.mk (.vpackZMM .sub) rfl
          (.cons .here
            (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
              .nil)))
  -- s8  sft = shr t c63        (t=0, c63=12)
  (.var (.mk (.vpackZMM .shr) rfl
          (.cons .here
            (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))
              .nil)))
  -- s9  m = sub zero sft       (zero=14, sft=0)
  (.var (.mk (.vpackZMM .sub) rfl
          (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))
            (.cons .here .nil)))
  -- s10 keep = and m P         (m=0, P=11)
  (.var (.mk (.vpackZMM .and) rfl
          (.cons .here
            (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
              .nil)))
  -- s11 out = add t keep       (t=3, keep=0)
  (.var (.mk (.vpackZMM .add) rfl
          (.cons (.there (.there (.there .here))) (.cons .here .nil)))
  (.ret .here)))))))))))

/-- **`frommontCom` denotation pin.** Denotes to the packed `frommontVec`. -/
theorem frommontCom_denote (v NPI P MASK c32 c63 zero : BitVec 512) :
    frommontCom.denote
        (.cons v (.cons NPI (.cons P (.cons MASK (.cons c32 (.cons c63 (.cons zero .nil)))))))
      = frommontVec v NPI P MASK c32 c63 zero := by
  rw [frommontCom, denote_var_vpackZMM, denote_var_vpackZMM, denote_var_vpackZMM,
    denote_var_vpackZMM, denote_var_vpackZMM, denote_var_vpackZMM, denote_var_vpackZMM,
    denote_var_vpackZMM, denote_var_vpackZMM, denote_var_vpackZMM, denote_var_vpackZMM]
  simp only [frommontVec, montReduceVec, csubVec, Com.denote, lookup_here_extend,
    lookup_there_extend]
  rfl

/-- The `tomont` (montmul with RSQR) input context
    `[v, RSQR, NPI, P, MASK, c32, c63, zero]`, each `reg 512`. -/
abbrev tomontCtx : Ctxt jasminDialect :=
  [r512, r512, r512, r512, r512, r512, r512, r512]

/-- `zm_tomont_half(v) = montmul(v, RSQR)` as a straight-line `vpackZMM` `Com`. -/
def tomontCom : Com jasminDialect tomontCtx r512 :=
  -- s1  am = and v MASK        (v=0, MASK=4)
  .var (.mk (.vpackZMM .and) rfl
          (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil)))
  -- s2  bm = and RSQR MASK     (RSQR=2, MASK=5)
  (.var (.mk (.vpackZMM .and) rfl
          (.cons (.there (.there .here))
            (.cons (.there (.there (.there (.there (.there .here))))) .nil)))
  -- s3  pr = mul am bm         (am=1, bm=0)
  (.var (.mk (.vpackZMM .mul) rfl
          (.cons (.there .here) (.cons .here .nil)))
  -- s4  tm = and pr MASK       (pr=0, MASK=7)
  (.var (.mk (.vpackZMM .and) rfl
          (.cons .here
            (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)))
  -- s5  mm = mul tm NPI        (tm=0, NPI=6)
  (.var (.mk (.vpackZMM .mul) rfl
          (.cons .here
            (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)))
  -- s6  mi = and mm MASK       (mm=0, MASK=9)
  (.var (.mk (.vpackZMM .and) rfl
          (.cons .here
            (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
              .nil)))
  -- s7  mp = mul mi P          (mi=0, P=9)
  (.var (.mk (.vpackZMM .mul) rfl
          (.cons .here
            (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
              .nil)))
  -- s8  u = add mp pr          (mp=0, pr=4)
  (.var (.mk (.vpackZMM .add) rfl
          (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil)))
  -- s9  sh = shr u c32         (u=0, c32=13)
  (.var (.mk (.vpackZMM .shr) rfl
          (.cons .here
            (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))
              .nil)))
  -- s10 t' = sub sh P          (sh=0, P=12)
  (.var (.mk (.vpackZMM .sub) rfl
          (.cons .here
            (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))
              .nil)))
  -- s11 sft = shr t' c63       (t'=0, c63=16)
  (.var (.mk (.vpackZMM .shr) rfl
          (.cons .here
            (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))
              .nil)))
  -- s12 m = sub zero sft       (zero=18, sft=0)
  (.var (.mk (.vpackZMM .sub) rfl
          (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))
            (.cons .here .nil)))
  -- s13 keep = and m P         (m=0, P=15)
  (.var (.mk (.vpackZMM .and) rfl
          (.cons .here
            (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))
              .nil)))
  -- s14 out = add t' keep      (t'=3, keep=0)
  (.var (.mk (.vpackZMM .add) rfl
          (.cons (.there (.there (.there .here))) (.cons .here .nil)))
  (.ret .here))))))))))))))

/-- **`tomontCom` denotation pin.** Denotes to the packed `tomontVec`. -/
theorem tomontCom_denote (v RSQR NPI P MASK c32 c63 zero : BitVec 512) :
    tomontCom.denote
        (.cons v (.cons RSQR (.cons NPI (.cons P (.cons MASK (.cons c32 (.cons c63 (.cons zero .nil))))))))
      = tomontVec v RSQR NPI P MASK c32 c63 zero := by
  rw [tomontCom, denote_var_vpackZMM, denote_var_vpackZMM, denote_var_vpackZMM,
    denote_var_vpackZMM, denote_var_vpackZMM, denote_var_vpackZMM, denote_var_vpackZMM,
    denote_var_vpackZMM, denote_var_vpackZMM, denote_var_vpackZMM, denote_var_vpackZMM,
    denote_var_vpackZMM, denote_var_vpackZMM, denote_var_vpackZMM]
  simp only [tomontVec, montMulVec, montReduceVec, csubVec, Com.denote,
    lookup_here_extend, lookup_there_extend]
  rfl

/-! ### The `montmul` block reused

`tomontCom` (`Com [a, b, NPI, P, MASK, c32, c63, zero] r512`) is the `montmul`
block: its denotation is `montMulVec a b …` (`tomontVec` unfolds to `montMulVec`),
so it doubles as the reusable `montmul` fragment the composed kernels splice. -/

open CatCrypt.Crypto.SecureCompilation.VIR
  (Com.rename)
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent
  (spliceCom spliceCom_denote pullV Com.denote_rename)

/-- `tomontCom`'s denotation as `montmul`: lane-wise `montMulVec a b …`. -/
theorem montMulCom_denote (a b NPI P MASK c32 c63 zero : BitVec 512) :
    tomontCom.denote
        (.cons a (.cons b (.cons NPI (.cons P (.cons MASK (.cons c32 (.cons c63 (.cons zero .nil))))))))
      = montMulVec a b NPI P MASK c32 c63 zero :=
  tomontCom_denote a b NPI P MASK c32 c63 zero

/-- The `intdiag` input context `[d, v, sum, NPI, P, MASK, c32, c63, zero]`,
    each `reg 512`. -/
abbrev intdiagCtx : Ctxt jasminDialect :=
  [r512, r512, r512, r512, r512, r512, r512, r512, r512]

/-- Rename `tomontCom`'s inputs `[a, b, NPI, P, MASK, c32, c63, zero]` into the
    `intdiag` context: `a ↦ d`, `b ↦ v`, and the shared constant tail unchanged
    (shifted past `sum`). -/
def homMMtoIntdiag : Ctxt.Hom tomontCtx intdiagCtx := fun
  | .here => .here
  | .there .here => .there .here
  | .there (.there vv) => .there (.there (.there vv))

/-- Rename `faddCom`'s inputs `[a, b, P, c63, zero]` into `r512 :: intdiagCtx`
    `= [mmres, d, v, sum, NPI, P, MASK, c32, c63, zero]`: `a ↦ mmres`, `b ↦ sum`,
    `P ↦ P`, `c63 ↦ c63`, `zero ↦ zero`. -/
def homFaddIntdiag : Ctxt.Hom faddCtx (r512 :: intdiagCtx) := fun
  | .here => .here
  | .there .here => .there (.there (.there .here))
  | .there (.there .here) =>
      .there (.there (.there (.there (.there .here))))
  | .there (.there (.there .here)) =>
      .there (.there (.there (.there (.there (.there (.there (.there .here)))))))
  | .there (.there (.there (.there .here))) =>
      .there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
  | .there (.there (.there (.there (.there vv)))) => nomatch vv

/-- `zm_intdiag_half(d,v,sum) = fadd(montmul(d,v), sum)` as a `Com jasminDialect`,
    composed by `spliceCom` from the `montmul` block (`tomontCom`) and the `fadd`
    block (`faddCom`) — sidestepping the flat-chain elaboration ceiling. -/
def intdiagCom : Com jasminDialect intdiagCtx r512 :=
  spliceCom (Com.rename homMMtoIntdiag tomontCom) (Com.rename homFaddIntdiag faddCom)

/-- **`intdiagCom` denotation pin.** Denotes to the packed `intdiagVec`. -/
theorem intdiagCom_denote (d v sum NPI P MASK c32 c63 zero : BitVec 512) :
    intdiagCom.denote
        (.cons d (.cons v (.cons sum (.cons NPI (.cons P (.cons MASK (.cons c32 (.cons c63 (.cons zero .nil)))))))))
      = intdiagVec d v sum NPI P MASK c32 c63 zero := by
  rw [intdiagCom, spliceCom_denote, Com.denote_rename, Com.denote_rename]
  rw [show pullV homMMtoIntdiag
        (.cons d (.cons v (.cons sum (.cons NPI (.cons P (.cons MASK (.cons c32 (.cons c63 (.cons zero .nil)))))))))
        = (.cons d (.cons v (.cons NPI (.cons P (.cons MASK (.cons c32 (.cons c63 (.cons zero .nil))))))))
        from rfl]
  rw [montMulCom_denote]
  rw [show pullV homFaddIntdiag
        (Ctxt.Valuation.extend
          (.cons d (.cons v (.cons sum (.cons NPI (.cons P (.cons MASK (.cons c32 (.cons c63 (.cons zero .nil)))))))))
          (montMulVec d v NPI P MASK c32 c63 zero))
        = (.cons (montMulVec d v NPI P MASK c32 c63 zero) (.cons sum (.cons P (.cons c63 (.cons zero .nil)))))
        from rfl]
  rw [faddCom_denote, intdiagVec]

/-! ### `extround` = sbox(fadd(v,c)) via nested `spliceCom`

`sbox(x) = montmul(montmul(x²,x²), montmul(x²,x))` with `x² = montmul(x,x)`, so
`extround` is one `fadd` block feeding four `montmul` blocks. Each block is
`tomontCom`/`faddCom` renamed into the growing context; the constant tail
`[NPI, P, MASK, c32, c63, zero]` is shared, so each `montmul` hom is three cases
(the two data inputs plus the uniform constant-tail weaken). -/

/-- The `extround` input context `[v, c, NPI, P, MASK, c32, c63, zero]`. -/
abbrev extroundCtx : Ctxt jasminDialect :=
  [r512, r512, r512, r512, r512, r512, r512, r512]

/-- `fadd(v,c)` block hom: `a ↦ v`, `b ↦ c`, `P ↦ P`, `c63 ↦ c63`, `zero ↦ zero`. -/
def homFaddExt : Ctxt.Hom faddCtx extroundCtx := fun
  | .here => .here
  | .there .here => .there .here
  | .there (.there .here) => .there (.there (.there .here))
  | .there (.there (.there .here)) =>
      .there (.there (.there (.there (.there (.there .here)))))
  | .there (.there (.there (.there .here))) =>
      .there (.there (.there (.there (.there (.there (.there .here))))))
  | .there (.there (.there (.there (.there vv)))) => nomatch vv

/-- `x2 = montmul(fa,fa)` hom into `[fa,v,c,…consts]`: both inputs `↦ fa`. -/
def homX2ext : Ctxt.Hom tomontCtx (r512 :: extroundCtx) := fun
  | .here => .here
  | .there .here => .here
  | .there (.there vv) => .there (.there (.there vv))

/-- `x4 = montmul(x2,x2)` hom into `[x2,fa,v,c,…consts]`: both inputs `↦ x2`. -/
def homX4ext : Ctxt.Hom tomontCtx (r512 :: r512 :: extroundCtx) := fun
  | .here => .here
  | .there .here => .here
  | .there (.there vv) => .there (.there (.there (.there vv)))

/-- `t = montmul(x2,fa)` hom into `[x4,x2,fa,v,c,…consts]`: `a ↦ x2`, `b ↦ fa`. -/
def homText : Ctxt.Hom tomontCtx (r512 :: r512 :: r512 :: extroundCtx) := fun
  | .here => .there .here
  | .there .here => .there (.there .here)
  | .there (.there vv) => .there (.there (.there (.there (.there vv))))

/-- `out = montmul(x4,t)` hom into `[t,x4,x2,fa,v,c,…consts]`: `a ↦ x4`, `b ↦ t`. -/
def homOutext : Ctxt.Hom tomontCtx (r512 :: r512 :: r512 :: r512 :: extroundCtx) := fun
  | .here => .there .here
  | .there .here => .here
  | .there (.there vv) => .there (.there (.there (.there (.there (.there vv)))))

/-- `zm_extround_half(v,c) = sbox(fadd(v,c))` as a `Com jasminDialect`, composed
    by nested `spliceCom` from the `fadd` block and four `montmul` blocks. -/
def extroundCom : Com jasminDialect extroundCtx r512 :=
  spliceCom (Com.rename homFaddExt faddCom)
    (spliceCom (Com.rename homX2ext tomontCom)
      (spliceCom (Com.rename homX4ext tomontCom)
        (spliceCom (Com.rename homText tomontCom)
          (Com.rename homOutext tomontCom))))

/-- The `fadd` block renamed into the `extround` context computes `faddVec v c`. -/
theorem faddBlkExt_denote (v c NPI P MASK c32 c63 zero : BitVec 512) :
    (Com.rename homFaddExt faddCom).denote
        (.cons v (.cons c (.cons NPI (.cons P (.cons MASK (.cons c32 (.cons c63 (.cons zero .nil))))))))
      = faddVec v c P c63 zero := by
  rw [Com.denote_rename]
  exact faddCom_denote v c P c63 zero

/-- `x2 = montmul(fa,fa)` block renamed into `[fa,…]`. -/
theorem x2BlkExt_denote (fa v c NPI P MASK c32 c63 zero : BitVec 512) :
    (Com.rename homX2ext tomontCom).denote
        (.cons fa (.cons v (.cons c (.cons NPI (.cons P (.cons MASK (.cons c32 (.cons c63 (.cons zero .nil)))))))))
      = montMulVec fa fa NPI P MASK c32 c63 zero := by
  rw [Com.denote_rename]
  exact montMulCom_denote fa fa NPI P MASK c32 c63 zero

/-- `x4 = montmul(x2,x2)` block renamed into `[x2,fa,…]`. -/
theorem x4BlkExt_denote (x2 fa v c NPI P MASK c32 c63 zero : BitVec 512) :
    (Com.rename homX4ext tomontCom).denote
        (.cons x2 (.cons fa (.cons v (.cons c (.cons NPI (.cons P (.cons MASK (.cons c32 (.cons c63 (.cons zero .nil))))))))))
      = montMulVec x2 x2 NPI P MASK c32 c63 zero := by
  rw [Com.denote_rename]
  exact montMulCom_denote x2 x2 NPI P MASK c32 c63 zero

/-- `t = montmul(x2,fa)` block renamed into `[x4,x2,fa,…]`. -/
theorem tBlkExt_denote (x4 x2 fa v c NPI P MASK c32 c63 zero : BitVec 512) :
    (Com.rename homText tomontCom).denote
        (.cons x4 (.cons x2 (.cons fa (.cons v (.cons c (.cons NPI (.cons P (.cons MASK (.cons c32 (.cons c63 (.cons zero .nil)))))))))))
      = montMulVec x2 fa NPI P MASK c32 c63 zero := by
  rw [Com.denote_rename]
  exact montMulCom_denote x2 fa NPI P MASK c32 c63 zero

/-- `out = montmul(x4,t)` block renamed into `[t,x4,x2,fa,…]`. -/
theorem outBlkExt_denote (t x4 x2 fa v c NPI P MASK c32 c63 zero : BitVec 512) :
    (Com.rename homOutext tomontCom).denote
        (.cons t (.cons x4 (.cons x2 (.cons fa (.cons v (.cons c (.cons NPI (.cons P (.cons MASK (.cons c32 (.cons c63 (.cons zero .nil))))))))))))
      = montMulVec x4 t NPI P MASK c32 c63 zero := by
  rw [Com.denote_rename]
  exact montMulCom_denote x4 t NPI P MASK c32 c63 zero

/-- **`extroundCom` denotation pin.** Denotes to the packed `extroundVec`. -/
theorem extroundCom_denote (v c NPI P MASK c32 c63 zero : BitVec 512) :
    extroundCom.denote
        (.cons v (.cons c (.cons NPI (.cons P (.cons MASK (.cons c32 (.cons c63 (.cons zero .nil))))))))
      = extroundVec v c NPI P MASK c32 c63 zero := by
  rw [extroundCom, spliceCom_denote, spliceCom_denote, spliceCom_denote, spliceCom_denote]
  simp only [Ctxt.Valuation.extend]
  rw [faddBlkExt_denote, x2BlkExt_denote, x4BlkExt_denote, tBlkExt_denote, outBlkExt_denote]
  simp only [extroundVec, sboxVec]

/-! ## 6. Per-lane BabyBear tie of the four emitted half-kernel `Com`s

Composing each half-kernel `Com`'s denotation pin with its per-lane theorem:
lane `k` of the emitted `Com`'s denotation is the scalar BabyBear reference of
lane `k` of the inputs. -/

/-- **`frommontCom` per-lane BabyBear tie.** -/
theorem frommontCom_lane (v NPI P MASK c32 c63 zero : BitVec 512) (k : Fin 8) :
    zmmLane (frommontCom.denote
        (.cons v (.cons NPI (.cons P (.cons MASK (.cons c32 (.cons c63 (.cons zero .nil)))))))) k
      = frommontL (zmmLane v k) (zmmLane NPI k) (zmmLane P k) (zmmLane MASK k)
          (zmmLane c32 k).toNat (zmmLane c63 k).toNat (zmmLane zero k) := by
  rw [frommontCom_denote, frommontVec_lane]

/-- **`tomontCom` per-lane BabyBear tie.** -/
theorem tomontCom_lane (v RSQR NPI P MASK c32 c63 zero : BitVec 512) (k : Fin 8) :
    zmmLane (tomontCom.denote
        (.cons v (.cons RSQR (.cons NPI (.cons P (.cons MASK (.cons c32 (.cons c63 (.cons zero .nil))))))))) k
      = tomontL (zmmLane v k) (zmmLane RSQR k) (zmmLane NPI k) (zmmLane P k) (zmmLane MASK k)
          (zmmLane c32 k).toNat (zmmLane c63 k).toNat (zmmLane zero k) := by
  rw [tomontCom_denote, tomontVec_lane]

/-- **`intdiagCom` per-lane BabyBear tie.** -/
theorem intdiagCom_lane (d v sum NPI P MASK c32 c63 zero : BitVec 512) (k : Fin 8) :
    zmmLane (intdiagCom.denote
        (.cons d (.cons v (.cons sum (.cons NPI (.cons P (.cons MASK (.cons c32 (.cons c63 (.cons zero .nil)))))))))) k
      = intdiagL (zmmLane d k) (zmmLane v k) (zmmLane sum k) (zmmLane NPI k) (zmmLane P k)
          (zmmLane MASK k) (zmmLane c32 k).toNat (zmmLane c63 k).toNat (zmmLane zero k) := by
  rw [intdiagCom_denote, intdiagVec_lane]

/-- **`extroundCom` per-lane BabyBear tie.** -/
theorem extroundCom_lane (v c NPI P MASK c32 c63 zero : BitVec 512) (k : Fin 8) :
    zmmLane (extroundCom.denote
        (.cons v (.cons c (.cons NPI (.cons P (.cons MASK (.cons c32 (.cons c63 (.cons zero .nil))))))))) k
      = extroundL (zmmLane v k) (zmmLane c k) (zmmLane NPI k) (zmmLane P k) (zmmLane MASK k)
          (zmmLane c32 k).toNat (zmmLane c63 k).toNat (zmmLane zero k) := by
  rw [extroundCom_denote, extroundVec_lane]

end CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2HalfKernelsZmm
