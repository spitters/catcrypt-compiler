/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.LaneMap
public import CatCrypt.Crypto.SecureCompilation.VIR.LaneMapVecCore
public import CatCrypt.Crypto.Optimizer.PackedArith256
public import CatCrypt.Crypto.Optimizer.PackedRotate256

/-!
# The SLH-DSA `batch8` widening pass: eight scalar `u32` SHA lanes to one YMM register

The SLH-DSA multi-buffer hash runs eight independent SHA-256 computations. Each
runs on 32-bit words; the eight are packed into one 256-bit YMM register (8×`u32`
dword lanes). `batch8` is the `Com jasminDialect → Com jasminDialect` transform
that widens a scalar SHA program: every `reg 32` value becomes a `reg 256`, and
every scalar op becomes the packed 256-bit YMM op that computes it on all eight
dword lanes at once.

The transform is a `FieldDialectBlockDescent.BlockLoweringData` instance. Each
scalar op lowers to a block of one or three YMM ops (`ror` expands to
`vpslld; vpsrld; vpor`), and `blockLowerCom` splices the blocks. The type map
sends `reg 32` to `reg 256` and fixes every other type; the variable and context
maps are the structural transports.

## Covered scalar ops

`regArith add / xor / or / and` at width 32 lower to `vpaddd / vpxor / vpor /
vpand`; `shlImm / shrImm` at width 32 to `vpslld / vpsrld`; `rorImm 32 n`
(rotate right, `0 < n < 32`) to the three-op rotate macro
`vpslld (32-n); vpsrld n; vpor`; `regConst 32 k` (a round constant) to the
lane-broadcast `regConst 256 (bcast256 k)`; and `stackLoad 32 n` (a message
word) to the SoA `stackLoad 256 n`. Together these are the whole SHA-256
compression body. Every other op takes the opaque widening fallback (a nullary
`extCall` returning the mapped type), which is outside the `Batch8Covered`
fragment the denotation theorem is stated over.

## SoA layout assumption

The message-word `stackLoad` widening encodes one layout fact: the widened input
buffer (`stackArr 256 n`) stores, at element `i`, a 256-bit slot whose dword lane
`j` is lane `j`'s scalar word `i`. This is exactly `laneOfTy` on a `stackArr 32`,
so the read requires no separate hypothesis — it follows from the `laneOf`
relation and the shared `reg 64` index (the index is not widened; all eight lanes
read the same message position).

## Main definitions

* `widen8Ty` / `widen8Ctxt` / `mapVar`: the type, context and de Bruijn transports.
* `lowering`: the `BlockLoweringData jasminDialect jasminDialect`.
* `batch8`: the whole-program widening `Com jasminDialect → Com jasminDialect`.
* `laneOfTy` / `laneOf`: per-type and per-valuation extraction of dword lane `k`.
* `Batch8Covered`: the fragment on which the widening is lane-preserving.
* `LaneMapVec.dwordYmm`: the lane shape of the widening (eight 32-bit lanes on the
  `vymm` dword ops, message arrays widened).

## Main results

* `laneOf_lookup`: reading a widened variable and extracting lane `k` equals
  reading the original variable against the lane-`k` valuation.
* `batch8_eq_laneMapVec`: on a covered program, `batch8` is
  `LaneMapVec.laneMapVec dwordYmm`.
* `blockOpLane`: each covered op's YMM block, read at dword lane `k`, computes the
  scalar op on lane `k`; the instance of `LaneShape.blockOpLane` at `dwordYmm`.
* `batch8_denote`: for a covered program returning `reg 32`, dword lane `k` of the
  widened program's denotation equals the scalar program's denotation on lane `k`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Batch8

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.YmmDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent
open CatCrypt.Crypto.Optimizer.PackedArith256
open CatCrypt.Crypto.Optimizer.PackedRotate256

/-! ## 1. Type, context and variable maps -/

/-- Widen `reg 32` to `reg 256` and a `stackArr 32` (the SoA input buffer of `u32`
    words) to `stackArr 256` (each element now a packed 8-lane slot); fix every
    other Jasmin type. -/
@[implicit_reducible]
def widen8Ty : JasminTy → JasminTy
  | .reg w => if w = 32 then .reg 256 else .reg w
  | .stackArr w n => if w = 32 then .stackArr 256 n else .stackArr w n
  | t => t

/-- Context map: `widen8Ty` pointwise. -/
@[implicit_reducible]
def widen8Ctxt (Γ : Ctxt jasminDialect) : Ctxt jasminDialect := Γ.map widen8Ty

/-- `List.map` is definitionally `cons`-compatible. -/
theorem mapCtx_cons (t : JasminTy) (Γ : Ctxt jasminDialect) :
    widen8Ctxt (t :: Γ) = widen8Ty t :: widen8Ctxt Γ := rfl

/-- de Bruijn index transport along `widen8Ty`. -/
def mapVar {Γ : Ctxt jasminDialect} {t : JasminTy} :
    Ctxt.Var Γ t → Ctxt.Var (widen8Ctxt Γ) (widen8Ty t)
  | .here => .here
  | .there v => .there (mapVar v)

/-- Broadcast a 32-bit constant into all eight dword lanes of a 256-bit word: the
    SoA-uniform round constant (every lane holds the same `k`, matching SHA-256's
    per-round `K_t`). -/
def bcast256 (k : Nat) : BitVec 256 :=
  (List.range 8).foldl (fun acc j => acc ||| ((BitVec.ofNat 32 k).setWidth 256 <<< (32 * j))) 0

/-- Dword lane `j` of the broadcast constant is the scalar constant. -/
theorem bcast256_lane (k : Nat) (j : Fin 8) :
    BitVec.extractLsb' (32 * j.val) 32 (bcast256 k) = BitVec.ofNat 32 k :=
  packFold32_lane256 (fun _ => BitVec.ofNat 32 k) j

/-! ## 2. The block lowering -/

/-- The block-expanding widening. Each covered scalar op becomes its packed YMM
    block; every other op takes the opaque nullary-`extCall` fallback. -/
def lowering : BlockLoweringData jasminDialect jasminDialect where
  mapTy := widen8Ty
  mapCtx := widen8Ctxt
  mapCtx_cons := mapCtx_cons
  mapVar := mapVar
  lowerExprBlock := fun {_Γ t} e =>
    match e with
    | ⟨.regArith .add 32, h, .cons a (.cons b .nil)⟩ =>
        congrArg widen8Ty h ▸
          Com.var ⟨.vymm .vpaddd, rfl, .cons (mapVar a) (.cons (mapVar b) .nil)⟩ (.ret .here)
    | ⟨.regArith .xor 32, h, .cons a (.cons b .nil)⟩ =>
        congrArg widen8Ty h ▸
          Com.var ⟨.vymm .vpxor, rfl, .cons (mapVar a) (.cons (mapVar b) .nil)⟩ (.ret .here)
    | ⟨.regArith .or 32, h, .cons a (.cons b .nil)⟩ =>
        congrArg widen8Ty h ▸
          Com.var ⟨.vymm .vpor, rfl, .cons (mapVar a) (.cons (mapVar b) .nil)⟩ (.ret .here)
    | ⟨.regArith .and 32, h, .cons a (.cons b .nil)⟩ =>
        congrArg widen8Ty h ▸
          Com.var ⟨.vymm .vpand, rfl, .cons (mapVar a) (.cons (mapVar b) .nil)⟩ (.ret .here)
    | ⟨.regArith .sub 32, h, .cons a (.cons b .nil)⟩ =>
        congrArg widen8Ty h ▸
          Com.var ⟨.vymm .vpsubd, rfl, .cons (mapVar a) (.cons (mapVar b) .nil)⟩ (.ret .here)
    | ⟨.regArith .mul 32, h, .cons a (.cons b .nil)⟩ =>
        congrArg widen8Ty h ▸
          Com.var ⟨.vymm .vpmulld, rfl, .cons (mapVar a) (.cons (mapVar b) .nil)⟩ (.ret .here)
    | ⟨.regArith .andn 32, h, .cons a (.cons b .nil)⟩ =>
        congrArg widen8Ty h ▸
          Com.var ⟨.vymm .vpandn, rfl, .cons (mapVar a) (.cons (mapVar b) .nil)⟩ (.ret .here)
    | ⟨.sarImm 32 n, h, .cons a .nil⟩ =>
        congrArg widen8Ty h ▸
          Com.var ⟨.vymm (.vpsrad n), rfl, .cons (mapVar a) .nil⟩ (.ret .here)
    | ⟨.shlImm 32 n, h, .cons a .nil⟩ =>
        congrArg widen8Ty h ▸
          Com.var ⟨.vymm (.vpslld n), rfl, .cons (mapVar a) .nil⟩ (.ret .here)
    | ⟨.shrImm 32 n, h, .cons a .nil⟩ =>
        congrArg widen8Ty h ▸
          Com.var ⟨.vymm (.vpsrld n), rfl, .cons (mapVar a) .nil⟩ (.ret .here)
    | ⟨.regArith .shl 32, h, .cons a (.cons b .nil)⟩ =>
        congrArg widen8Ty h ▸
          Com.var ⟨.vymm .vpsllvd, rfl, .cons (mapVar a) (.cons (mapVar b) .nil)⟩ (.ret .here)
    | ⟨.regArith .shr 32, h, .cons a (.cons b .nil)⟩ =>
        congrArg widen8Ty h ▸
          Com.var ⟨.vymm .vpsrlvd, rfl, .cons (mapVar a) (.cons (mapVar b) .nil)⟩ (.ret .here)
    | ⟨.rorImm 32 n, h, .cons a .nil⟩ =>
        congrArg widen8Ty h ▸
          Com.var ⟨.vymm (.vpslld (32 - n)), rfl, .cons (mapVar a) .nil⟩
            (Com.var ⟨.vymm (.vpsrld n), rfl, .cons (mapVar a).there .nil⟩
              (Com.var ⟨.vymm .vpor, rfl, .cons (.there .here) (.cons .here .nil)⟩
                (.ret .here)))
    | ⟨.regConst 32 kk, h, .nil⟩ =>
        congrArg widen8Ty h ▸
          Com.var ⟨.regConst 256 (bcast256 kk).toNat, rfl, .nil⟩ (.ret .here)
    | ⟨.stackLoad 32 n, h, .cons arr (.cons idx .nil)⟩ =>
        congrArg widen8Ty h ▸
          Com.var ⟨.stackLoad 256 n, rfl, .cons (mapVar arr) (.cons (mapVar idx) .nil)⟩
            (.ret .here)
    | ⟨_, _, _⟩ =>
        Com.var ⟨.extCall "batch8_uncovered" [] (widen8Ty t), rfl, .nil⟩ (.ret .here)

/-- Widen a whole scalar SHA program: eight `u32` lanes into one YMM register. -/
def batch8 {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t) :
    Com jasminDialect (widen8Ctxt Γ) (widen8Ty t) :=
  lowering.blockLowerCom c

/-! ## 3. Lane extraction -/

/-- Extract dword lane `k` of a widened value. A widened `reg 32` (now a
    `reg 256`) yields its lane-`k` dword; every other type is unchanged and passes
    through. -/
def laneOfTy (k : Fin 8) : (s : JasminTy) → ⟦widen8Ty s⟧ → ⟦s⟧
  | .reg w, v => by
      by_cases h : w = 32
      · subst h; exact BitVec.extractLsb' (32 * k.val) 32 v
      · simp only [widen8Ty, if_neg h] at v; exact v
  | .stackArr w n, v => by
      by_cases h : w = 32
      · subst h; exact fun i => BitVec.extractLsb' (32 * k.val) 32 (v i)
      · simp only [widen8Ty, if_neg h] at v; exact v
  | .inlineInt, v => v
  | .bool, v => v

/-- Lane extraction at `reg 32`: the lane-`k` dword. -/
theorem laneOfTy_reg32 (k : Fin 8) (v : ⟦widen8Ty (.reg 32)⟧) :
    laneOfTy k (.reg 32) v = BitVec.extractLsb' (32 * k.val) 32 v := rfl

/-- Extract dword lane `k` of a whole widened valuation, slot by slot. -/
def laneOf (k : Fin 8) : (Γ : Ctxt jasminDialect) →
    Ctxt.Valuation (widen8Ctxt Γ) → Ctxt.Valuation Γ
  | [], _ => .nil
  | s :: _, W => .cons (laneOfTy k s W.head) (laneOf k _ W.tail)

/-- Reading a widened variable and extracting lane `k` equals reading the original
    variable against the lane-`k` valuation. -/
theorem laneOf_lookup : {Γ : Ctxt jasminDialect} → {t : JasminTy} → (v : Ctxt.Var Γ t) →
    (W : Ctxt.Valuation (widen8Ctxt Γ)) → (k : Fin 8) →
    laneOfTy k t ((mapVar v).lookup W) = v.lookup (laneOf k Γ W)
  | _, _, .here, W, _ => by cases W; rfl
  | _, _, .there w, W, k => by
      cases W with
      | cons _ rest => exact laneOf_lookup w rest k

/-- Lane extraction at `stackArr 32 n`: the dword-`k` lane of each element. This is
    the SoA read — the widened array stores lane `j`'s word at dword `j` of each
    256-bit element, so projecting lane `k` recovers lane `k`'s scalar array. -/
theorem laneOfTy_stackArr32 (k : Fin 8) (n : Nat) (v : ⟦widen8Ty (.stackArr 32 n)⟧) :
    laneOfTy k (.stackArr 32 n) v = fun i => BitVec.extractLsb' (32 * k.val) 32 (v i) := rfl

/-- The `reg 64` message index is not widened, so lane extraction is the identity —
    the same index feeds all eight lanes. -/
theorem laneOfTy_reg64 (k : Fin 8) (v : ⟦widen8Ty (.reg 64)⟧) :
    laneOfTy k (.reg 64) v = v := rfl

/-- Lane extraction commutes with the total stack read: extracting dword `k` of a
    packed array element and then reading equals reading the per-lane-extracted
    array. -/
theorem extract_stackGet {n : Nat} (arr : Fin n → BitVec 256) (m : Nat) (k : Fin 8) :
    BitVec.extractLsb' (32 * k.val) 32 (stackGet arr m)
      = stackGet (fun i => BitVec.extractLsb' (32 * k.val) 32 (arr i)) m := by
  cases n with
  | zero => simp [stackGet]
  | succ m' => simp [stackGet]

/-- A `BitVec 256` round-trips through `Nat`: `regConst` materialises a `Nat`, so the
    broadcast constant is recovered from its `toNat`. -/
theorem ofNat_toNat_256 (x : BitVec 256) : BitVec.ofNat 256 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]

/-! ## 4. The covered fragment -/

/-- The scalar ops `batch8` widens lane-preservingly: `add/sub/mul/xor/or/and/andn`
    at width 32, the logical immediate shifts at counts below 32, the arithmetic
    `sarImm`, and rotate-right `rorImm 32 n` with `0 < n < 32`. The register-count
    shifts `shl/shr` are not covered: `vpsllvd`/`vpsrlvd` give `0` at counts of at
    least 32, where the scalar shift masks the count. The subtract, low product,
    and-not and arithmetic shift are what per-coefficient lattice arithmetic needs on
    top of the SHA fragment. -/
def CoveredExpr {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) : Prop :=
  match e.op with
  | .regArith .add w => w = 32
  | .regArith .sub w => w = 32
  | .regArith .mul w => w = 32
  | .regArith .xor w => w = 32
  | .regArith .or w => w = 32
  | .regArith .and w => w = 32
  | .regArith .andn w => w = 32
  | .shlImm w n => w = 32 ∧ n < 32
  | .shrImm w n => w = 32 ∧ n < 32
  | .sarImm w _ => w = 32
  | .rorImm w n => w = 32 ∧ 0 < n ∧ n < 32
  | .regConst w _ => w = 32
  | .stackLoad w _ => w = 32
  | _ => False

/-- A program whose every op is covered. -/
def Batch8Covered {Γ : Ctxt jasminDialect} {t : JasminTy} :
    Com jasminDialect Γ t → Prop
  | .ret _ => True
  | .var e body => CoveredExpr e ∧ Batch8Covered body

/-! ## 5. The rotate synthesis -/

/-- The scalar 32-bit rotate-right synthesis `x.rotateRight n = (x <<< (32-n)) |||
    (x >>> n)`, for `0 < n < 32` — the per-lane meaning of the `vpslld; vpsrld;
    vpor` rotate macro. -/
theorem ror32_synth (x : BitVec 32) (n : Nat) (h : n < 32) :
    x.rotateRight n = (x <<< (32 - n)) ||| (x >>> n) := by
  rw [BitVec.rotateRight_def, Nat.mod_eq_of_lt h, BitVec.or_comm]

/-! ## 6. The lane shape `dwordYmm` -/

end CatCrypt.Crypto.Optimizer.Batch8

namespace CatCrypt.Crypto.SecureCompilation.VIR.LaneMapVec

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.YmmDialect
open CatCrypt.Crypto.Optimizer.PackedArith256
open CatCrypt.Crypto.Optimizer.PackedRotate256

/-- The 256-bit packed expression of a scalar op on eight 32-bit lanes. -/
def ymmDPackExpr : JasminBinOp → PackBuilder 256
  | .add => fun _ a b => ⟨.vymm .vpaddd, rfl, .cons a (.cons b .nil)⟩
  | .sub => fun _ a b => ⟨.vymm .vpsubd, rfl, .cons a (.cons b .nil)⟩
  | .mul => fun _ a b => ⟨.vymm .vpmulld, rfl, .cons a (.cons b .nil)⟩
  | .and => fun _ a b => ⟨.vymm .vpand, rfl, .cons a (.cons b .nil)⟩
  | .or => fun _ a b => ⟨.vymm .vpor, rfl, .cons a (.cons b .nil)⟩
  | .xor => fun _ a b => ⟨.vymm .vpxor, rfl, .cons a (.cons b .nil)⟩
  | .andn => fun _ a b => ⟨.vymm .vpandn, rfl, .cons a (.cons b .nil)⟩
  | .shl => fun _ a b => ⟨.vymm .vpsllvd, rfl, .cons a (.cons b .nil)⟩
  | .shr => fun _ a b => ⟨.vymm .vpsrlvd, rfl, .cons a (.cons b .nil)⟩

/-- The 256-bit packed block of an immediate-count op on eight 32-bit lanes: `vpslld`,
    `vpsrld` and `vpsrad` by the count, and the rotate right by `n` as
    `vpslld (32 - n); vpsrld n; vpor`. -/
def ymmDImmBlock : ImmOp → Option (Nat → UnaryBuilder 256)
  | .shl => some fun n _ a => Com.var ⟨.vymm (.vpslld n), rfl, .cons a .nil⟩ (.ret .here)
  | .shr => some fun n _ a => Com.var ⟨.vymm (.vpsrld n), rfl, .cons a .nil⟩ (.ret .here)
  | .sar => some fun n _ a => Com.var ⟨.vymm (.vpsrad n), rfl, .cons a .nil⟩ (.ret .here)
  | .ror => some fun n _ a =>
      Com.var ⟨.vymm (.vpslld (32 - n)), rfl, .cons a .nil⟩
        (Com.var ⟨.vymm (.vpsrld n), rfl, .cons a.there .nil⟩
          (Com.var ⟨.vymm .vpor, rfl, .cons (.there .here) (.cons .here .nil)⟩ (.ret .here)))

/-- The counts at which `ymmDImmBlock` is lane-correct: counts below the lane width 32
    for the logical shifts (the vector shifts give `0` at larger counts, the masked
    scalar shift does not), every count for the arithmetic shift, and `0 < n < 32` for
    the rotate. -/
def ymmDImmCovers : ImmOp → Nat → Bool
  | .ror, n => decide (0 < n ∧ n < 32)
  | .shl, n => decide (n < 32)
  | .shr, n => decide (n < 32)
  | .sar, _ => true

/-- Eight 32-bit lanes in a YMM register, on the `vymm` dword ops, with the message
    array widened to an array of packed slots (the `batch8` shape). -/
def dwordYmm : LaneShape where
  laneBits := 32
  laneCount := 8
  regBits := 256
  regBits_eq := rfl
  lane := fun v k => BitVec.extractLsb' (32 * k.val) 32 v
  covers := fun | .shl => false | .shr => false | _ => true
  packExpr := ymmDPackExpr
  bcast := fun kk => (Optimizer.Batch8.bcast256 kk).toNat
  mulhiExpr := none
  immBlock := ymmDImmBlock
  immCovers := ymmDImmCovers
  arrWiden := true
  fallbackName := "batch8_uncovered"
  pack_lane := by
    intro _ bop hc _ a b V k
    cases bop
    case add => exact vpadddW_lane (a.lookup V) (b.lookup V) k
    case sub => exact vpsubdW_lane (a.lookup V) (b.lookup V) k
    case mul => exact vpmulldW_lane (a.lookup V) (b.lookup V) k
    case and => exact vpandW_lane (a.lookup V) (b.lookup V) k
    case or => exact vporW_lane (a.lookup V) (b.lookup V) k
    case xor => exact vpxorW_lane (a.lookup V) (b.lookup V) k
    case andn => exact vpandnW_lane (a.lookup V) (b.lookup V) k
    case shl => exact absurd hc (by decide)
    case shr => exact absurd hc (by decide)
  const_lane := by
    intro kk k
    show BitVec.extractLsb' (32 * k.val) 32
      (BitVec.ofNat 256 (Optimizer.Batch8.bcast256 kk).toNat) = _
    rw [Optimizer.Batch8.ofNat_toNat_256, Optimizer.Batch8.bcast256_lane]
  imm_lane := by
    intro _ op f hf n hc _ a V k
    cases op <;> cases hf
    case shl =>
      rw [ImmOp.apply, shiftMask_of_lt (of_decide_eq_true hc)]
      exact vpslldW_uniform_lane (a.lookup V) n k
    case shr =>
      rw [ImmOp.apply, shiftMask_of_lt (of_decide_eq_true hc)]
      exact vpsrldW_uniform_lane (a.lookup V) n k
    case sar => exact vpsradW_uniform_lane (a.lookup V) n k
    case ror =>
      have hn : n < 32 := (of_decide_eq_true hc).2
      show BitVec.extractLsb' (32 * k.val) 32
          (vporW (vpslldW (a.lookup V) (32 - n)) (vpsrldW (a.lookup V) n)) = _
      rw [vporW, BitVec.extractLsb'_or, vpslldW_uniform_lane, vpsrldW_uniform_lane,
        ← Optimizer.Batch8.ror32_synth _ n hn]
      rfl
  arr_index := fun _ => by decide
  lane_zero := fun _ _ => by simp

end CatCrypt.Crypto.SecureCompilation.VIR.LaneMapVec

namespace CatCrypt.Crypto.Optimizer.Batch8

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent
open CatCrypt.Crypto.SecureCompilation.VIR.LaneMapVec

/-! ## 7. `batch8` is `laneMapVec dwordYmm` on its covered fragment -/

/-- The variable maps of `batch8` and of `dwordYmm` agree. -/
theorem mapVar_dwordYmm : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    (v : Ctxt.Var Γ t) → mapVar v = dwordYmm.mapVar v
  | _, _, .here => rfl
  | _, _, .there v => congrArg Ctxt.Var.there (mapVar_dwordYmm v)

/-- On a covered op, the blocks of `batch8` and of `dwordYmm` agree. -/
theorem lowerExprBlock_dwordYmm {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (he : CoveredExpr e) :
    lowering.lowerExprBlock e = dwordYmm.lowerExprBlock e := by
  have hm : @mapVar = @LaneShape.mapVar dwordYmm := by
    funext Γ t v
    exact mapVar_dwordYmm v
  unfold lowering
  rw [hm]
  obtain ⟨op, rfl, args⟩ := e
  cases op <;> try (simp only [CoveredExpr] at he; done)
  case regArith bop w =>
    cases bop <;> simp only [CoveredExpr] at he <;>
      (subst he
       cases args; rename_i a rest; cases rest; rename_i b rest2; cases rest2; rfl)
  case shlImm w n =>
    obtain ⟨hw, _⟩ : w = 32 ∧ n < 32 := he
    subst hw
    cases args; rename_i a rest; cases rest; rfl
  case shrImm w n =>
    obtain ⟨hw, _⟩ : w = 32 ∧ n < 32 := he
    subst hw
    cases args; rename_i a rest; cases rest; rfl
  case sarImm w n =>
    simp only [CoveredExpr] at he; subst he
    cases args; rename_i a rest; cases rest; rfl
  case rorImm w n =>
    obtain ⟨hw, _, _⟩ : w = 32 ∧ 0 < n ∧ n < 32 := he
    subst hw
    cases args; rename_i a rest; cases rest; rfl
  case regConst w kk =>
    simp only [CoveredExpr] at he; subst he
    cases args; rfl
  case stackLoad w n =>
    simp only [CoveredExpr] at he; subst he
    cases args; rename_i arr rest; cases rest; rename_i idx rest2; cases rest2; rfl

/-- On a covered program, `batch8` is `laneMapVec dwordYmm`. -/
theorem batch8_eq_laneMapVec : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    (c : Com jasminDialect Γ t) → Batch8Covered c → batch8 c = laneMapVec dwordYmm c
  | _, _, .ret v, _ => congrArg Com.ret (mapVar_dwordYmm v)
  | _, _, .var e body, hc => by
      show spliceCom (lowering.lowerExprBlock e) (batch8 body)
        = spliceCom (dwordYmm.lowerExprBlock e) (laneMapVec dwordYmm body)
      rw [lowerExprBlock_dwordYmm e hc.1, batch8_eq_laneMapVec body hc.2]
      rfl

/-- The lane extractions of `batch8` and of `dwordYmm` agree. -/
theorem laneOfTy_dwordYmm (k : Fin 8) :
    (s : JasminTy) → (v : ⟦widen8Ty s⟧) → laneOfTy k s v = dwordYmm.laneOfTy k s v
  | .reg w, v => by
      by_cases h : w = 32
      · subst h; rfl
      · simp only [laneOfTy, LaneShape.laneOfTy, dif_neg h,
          dif_neg (show ¬w = dwordYmm.laneBits from h)]
        rfl
  | .stackArr w n, v => by
      by_cases h : w = 32
      · subst h; rfl
      · have h' : ¬(dwordYmm.arrWiden = true ∧ w = dwordYmm.laneBits) := fun h' => h h'.2
        simp only [laneOfTy, LaneShape.laneOfTy, dif_neg h, dif_neg h']
        rfl
  | .inlineInt, _ => rfl
  | .bool, _ => rfl

/-- The valuation lane extractions of `batch8` and of `dwordYmm` agree. -/
theorem laneOf_dwordYmm (k : Fin 8) : (Γ : Ctxt jasminDialect) →
    (W : Ctxt.Valuation (widen8Ctxt Γ)) → laneOf k Γ W = dwordYmm.laneOf k Γ W
  | [], _ => rfl
  | s :: Γ, W => by
      show HVector.cons _ _ = HVector.cons _ _
      rw [laneOfTy_dwordYmm k s, laneOf_dwordYmm k Γ]
      rfl

/-- An op covered by `batch8` is covered by `dwordYmm`. -/
theorem coveredExpr_dwordYmm {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (he : CoveredExpr e) : dwordYmm.CoveredExpr e := by
  obtain ⟨op, rfl, args⟩ := e
  cases op
  case regArith bop w =>
    cases bop <;> simp_all [CoveredExpr, LaneShape.CoveredExpr, dwordYmm]
  all_goals simp_all [CoveredExpr, LaneShape.CoveredExpr, dwordYmm, ymmDImmBlock,
    ymmDImmCovers]

/-- A program covered by `batch8` is covered by `dwordYmm`. -/
theorem covered_dwordYmm : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    (c : Com jasminDialect Γ t) → Batch8Covered c → dwordYmm.Covered c
  | _, _, .ret _, _ => trivial
  | _, _, .var e body, hc => ⟨coveredExpr_dwordYmm e hc.1, covered_dwordYmm body hc.2⟩

/-! ## 8. Lane preservation -/

/-- **Per-op lane square.** For each covered op, the widened YMM block read at
    dword lane `k` computes the scalar op on lane `k`. -/
theorem blockOpLane {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t)
    (he : CoveredExpr e) (W : Ctxt.Valuation (widen8Ctxt Γ)) (k : Fin 8) :
    laneOfTy k t ((lowering.lowerExprBlock e).denote W) = e.denote (laneOf k Γ W) := by
  have h := dwordYmm.blockOpLane_default rfl e (coveredExpr_dwordYmm e he) W k
  refine (laneOfTy_dwordYmm k t _).trans ?_
  rw [laneOf_dwordYmm, ← h]
  exact congrArg (fun c => dwordYmm.laneOfTy k t (Com.denote c W))
    (lowerExprBlock_dwordYmm e he)

/-- **`batch8` is lane-preserving.** For a covered program returning `reg 32`,
    dword lane `k` of the widened program's denotation equals the scalar program's
    denotation on the lane-`k` valuation: `laneMapVec_denote` at `dwordYmm`. -/
theorem batch8_denote {Γ : Ctxt jasminDialect} (c : Com jasminDialect Γ (.reg 32))
    (hc : Batch8Covered c) (W : Ctxt.Valuation (widen8Ctxt Γ)) (k : Fin 8) :
    BitVec.extractLsb' (32 * k.val) 32 ((batch8 c).denote W) = c.denote (laneOf k Γ W) := by
  rw [batch8_eq_laneMapVec c hc, laneOf_dwordYmm]
  exact laneMapVec_denote_default dwordYmm rfl c (covered_dwordYmm c hc) W k

end CatCrypt.Crypto.Optimizer.Batch8
