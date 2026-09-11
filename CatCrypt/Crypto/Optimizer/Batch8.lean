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

## Main results

* `laneOf_lookup`: reading a widened variable and extracting lane `k` equals
  reading the original variable against the lane-`k` valuation.
* `blockOpLane`: each covered op's YMM block, read at dword lane `k`, computes the
  scalar op on lane `k` — from the committed packed-lane lemmas.
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
def widen8Ty : JasminTy → JasminTy
  | .reg w => if w = 32 then .reg 256 else .reg w
  | .stackArr w n => if w = 32 then .stackArr 256 n else .stackArr w n
  | t => t

/-- Context map: `widen8Ty` pointwise. -/
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

/-- The scalar ops `batch8` widens lane-preservingly: `add/xor/or/and` at width 32,
    `shl/shr` at width 32, and rotate-right `rorImm 32 n` with `0 < n < 32`. -/
def CoveredExpr {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) : Prop :=
  match e.op with
  | .regArith .add w => w = 32
  | .regArith .xor w => w = 32
  | .regArith .or w => w = 32
  | .regArith .and w => w = 32
  | .regArith .shl w => w = 32
  | .regArith .shr w => w = 32
  | .shlImm w _ => w = 32
  | .shrImm w _ => w = 32
  | .rorImm w n => w = 32 ∧ 0 < n ∧ n < 32
  | .regConst w _ => w = 32
  | .stackLoad w _ => w = 32
  | _ => False

/-- A program whose every op is covered. -/
def Batch8Covered {Γ : Ctxt jasminDialect} {t : JasminTy} :
    Com jasminDialect Γ t → Prop
  | .ret _ => True
  | .var e body => CoveredExpr e ∧ Batch8Covered body

/-! ## 5. The per-op lane square -/

/-- The scalar 32-bit rotate-right synthesis `x.rotateRight n = (x <<< (32-n)) |||
    (x >>> n)`, for `0 < n < 32` — the per-lane meaning of the `vpslld; vpsrld;
    vpor` rotate macro. -/
theorem ror32_synth (x : BitVec 32) (n : Nat) (h : n < 32) :
    x.rotateRight n = (x <<< (32 - n)) ||| (x >>> n) := by
  rw [BitVec.rotateRight_def, Nat.mod_eq_of_lt h, BitVec.or_comm]

/-- **Variable packed left shift per lane.** Dword lane `k` of `vpsllvdW a b`
    (`VPSLLVD`, 8×`u32` shift left by a per-lane count vector) is lane `k` of `a`
    shifted left by the `.toNat` of lane `k` of `b`. -/
theorem vpsllvdW_lane (a b : BitVec 256) (k : Fin 8) :
    BitVec.extractLsb' (32 * k.val) 32 (vpsllvdW a b)
      = (BitVec.extractLsb' (32 * k.val) 32 a) <<< (BitVec.extractLsb' (32 * k.val) 32 b).toNat := by
  fin_cases k <;>
    simp only [vpsllvdW, yOfDwordsW, yDwordW, Fin.foldl_succ, Fin.foldl_zero, Fin.isValue,
      Fin.val_zero, Fin.val_succ] <;>
    bv_decide

/-- **Variable packed right shift per lane.** Dword lane `k` of `vpsrlvdW a b`
    (`VPSRLVD`, 8×`u32` shift right by a per-lane count vector) is lane `k` of `a`
    shifted right by the `.toNat` of lane `k` of `b`. -/
theorem vpsrlvdW_lane (a b : BitVec 256) (k : Fin 8) :
    BitVec.extractLsb' (32 * k.val) 32 (vpsrlvdW a b)
      = (BitVec.extractLsb' (32 * k.val) 32 a) >>> (BitVec.extractLsb' (32 * k.val) 32 b).toNat := by
  fin_cases k <;>
    simp only [vpsrlvdW, yOfDwordsW, yDwordW, Fin.foldl_succ, Fin.foldl_zero, Fin.isValue,
      Fin.val_zero, Fin.val_succ] <;>
    bv_decide

/-- **Per-op lane square.** For each covered op, the widened YMM block read at
    dword lane `k` computes the scalar op on lane `k` — from the committed packed
    lane lemmas. -/
theorem blockOpLane {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t)
    (he : CoveredExpr e) (W : Ctxt.Valuation (widen8Ctxt Γ)) (k : Fin 8) :
    laneOfTy k t ((lowering.lowerExprBlock e).denote W) = e.denote (laneOf k Γ W) := by
  obtain ⟨op, rfl, args⟩ := e
  cases op with
  | regArith bop w =>
      cases bop with
      | add =>
          simp only [CoveredExpr] at he; subst he
          cases args; rename_i a rest
          cases rest; rename_i b rest2
          cases rest2
          have LA := laneOf_lookup a W k
          have LB := laneOf_lookup b W k
          simp only [laneOfTy_reg32] at LA LB
          show yDwordW (vpadddW ((mapVar a).lookup W) ((mapVar b).lookup W)) k.val
              = (⟨.regArith .add 32, rfl, .cons a (.cons b .nil)⟩ :
                  Expr jasminDialect Γ (.reg 32)).denote (laneOf k Γ W)
          rw [vpadddW_lane]; simp only [yDwordW]; rw [LA, LB]; rfl
      | xor =>
          simp only [CoveredExpr] at he; subst he
          cases args; rename_i a rest
          cases rest; rename_i b rest2
          cases rest2
          have LA := laneOf_lookup a W k
          have LB := laneOf_lookup b W k
          simp only [laneOfTy_reg32] at LA LB
          show yDwordW (vpxorW ((mapVar a).lookup W) ((mapVar b).lookup W)) k.val
              = (⟨.regArith .xor 32, rfl, .cons a (.cons b .nil)⟩ :
                  Expr jasminDialect Γ (.reg 32)).denote (laneOf k Γ W)
          rw [vpxorW_lane]; simp only [yDwordW]; rw [LA, LB]; rfl
      | or =>
          simp only [CoveredExpr] at he; subst he
          cases args; rename_i a rest
          cases rest; rename_i b rest2
          cases rest2
          have LA := laneOf_lookup a W k
          have LB := laneOf_lookup b W k
          simp only [laneOfTy_reg32] at LA LB
          show yDwordW (vporW ((mapVar a).lookup W) ((mapVar b).lookup W)) k.val
              = (⟨.regArith .or 32, rfl, .cons a (.cons b .nil)⟩ :
                  Expr jasminDialect Γ (.reg 32)).denote (laneOf k Γ W)
          rw [vporW_lane]; simp only [yDwordW]; rw [LA, LB]; rfl
      | and =>
          simp only [CoveredExpr] at he; subst he
          cases args; rename_i a rest
          cases rest; rename_i b rest2
          cases rest2
          have LA := laneOf_lookup a W k
          have LB := laneOf_lookup b W k
          simp only [laneOfTy_reg32] at LA LB
          show yDwordW (vpandW ((mapVar a).lookup W) ((mapVar b).lookup W)) k.val
              = (⟨.regArith .and 32, rfl, .cons a (.cons b .nil)⟩ :
                  Expr jasminDialect Γ (.reg 32)).denote (laneOf k Γ W)
          rw [vpandW_lane]; simp only [yDwordW]; rw [LA, LB]; rfl
      | sub => simp only [CoveredExpr] at he
      | mul => simp only [CoveredExpr] at he
      | shl =>
          simp only [CoveredExpr] at he; subst he
          cases args; rename_i a rest
          cases rest; rename_i b rest2
          cases rest2
          have LA := laneOf_lookup a W k
          have LB := laneOf_lookup b W k
          simp only [laneOfTy_reg32] at LA LB
          show BitVec.extractLsb' (32 * k.val) 32
              (vpsllvdW ((mapVar a).lookup W) ((mapVar b).lookup W))
              = (⟨.regArith .shl 32, rfl, .cons a (.cons b .nil)⟩ :
                  Expr jasminDialect Γ (.reg 32)).denote (laneOf k Γ W)
          rw [vpsllvdW_lane, LA, LB]; rfl
      | shr =>
          simp only [CoveredExpr] at he; subst he
          cases args; rename_i a rest
          cases rest; rename_i b rest2
          cases rest2
          have LA := laneOf_lookup a W k
          have LB := laneOf_lookup b W k
          simp only [laneOfTy_reg32] at LA LB
          show BitVec.extractLsb' (32 * k.val) 32
              (vpsrlvdW ((mapVar a).lookup W) ((mapVar b).lookup W))
              = (⟨.regArith .shr 32, rfl, .cons a (.cons b .nil)⟩ :
                  Expr jasminDialect Γ (.reg 32)).denote (laneOf k Γ W)
          rw [vpsrlvdW_lane, LA, LB]; rfl
      | andn => simp only [CoveredExpr] at he
  | shlImm w n =>
      simp only [CoveredExpr] at he; subst he
      cases args; rename_i a rest
      cases rest
      have LA := laneOf_lookup a W k
      simp only [laneOfTy_reg32] at LA
      show BitVec.extractLsb' (32 * k.val) 32 (vpslldW ((mapVar a).lookup W) n)
          = (⟨.shlImm 32 n, rfl, .cons a .nil⟩ : Expr jasminDialect Γ (.reg 32)).denote
              (laneOf k Γ W)
      rw [vpslldW_uniform_lane, LA]; rfl
  | shrImm w n =>
      simp only [CoveredExpr] at he; subst he
      cases args; rename_i a rest
      cases rest
      have LA := laneOf_lookup a W k
      simp only [laneOfTy_reg32] at LA
      show BitVec.extractLsb' (32 * k.val) 32 (vpsrldW ((mapVar a).lookup W) n)
          = (⟨.shrImm 32 n, rfl, .cons a .nil⟩ : Expr jasminDialect Γ (.reg 32)).denote
              (laneOf k Γ W)
      rw [vpsrldW_uniform_lane, LA]; rfl
  | rorImm w n =>
      obtain ⟨hw, _, hn⟩ : w = 32 ∧ 0 < n ∧ n < 32 := he
      subst hw
      cases args; rename_i a rest
      cases rest
      have LA := laneOf_lookup a W k
      simp only [laneOfTy_reg32] at LA
      show BitVec.extractLsb' (32 * k.val) 32
          (vporW (vpslldW ((mapVar a).lookup W) (32 - n)) (vpsrldW ((mapVar a).lookup W) n))
          = (⟨.rorImm 32 n, rfl, .cons a .nil⟩ : Expr jasminDialect Γ (.reg 32)).denote
              (laneOf k Γ W)
      rw [vporW, BitVec.extractLsb'_or, vpslldW_uniform_lane, vpsrldW_uniform_lane]
      simp only [LA]
      rw [← ror32_synth (a.lookup (laneOf k Γ W)) n hn]
      rfl
  | stackLoad w n =>
      simp only [CoveredExpr] at he; subst he
      cases args; rename_i arr rest
      cases rest; rename_i idx rest2
      cases rest2
      have Larr := laneOf_lookup arr W k
      have Lidx := laneOf_lookup idx W k
      simp only [laneOfTy_stackArr32] at Larr
      simp only [laneOfTy_reg64] at Lidx
      show BitVec.extractLsb' (32 * k.val) 32
          (stackGet ((mapVar arr).lookup W) ((mapVar idx).lookup W).toNat)
          = (⟨.stackLoad 32 n, rfl, .cons arr (.cons idx .nil)⟩ :
              Expr jasminDialect Γ (.reg 32)).denote (laneOf k Γ W)
      rw [extract_stackGet, Larr, Lidx]; rfl
  | stackStore w n => simp only [CoveredExpr] at he
  | castW w w' => simp only [CoveredExpr] at he
  | extCall nm a r => simp only [CoveredExpr] at he
  | regConst w kk =>
      simp only [CoveredExpr] at he; subst he
      cases args
      show BitVec.extractLsb' (32 * k.val) 32 (BitVec.ofNat 256 (bcast256 kk).toNat)
          = (⟨.regConst 32 kk, rfl, .nil⟩ : Expr jasminDialect Γ (.reg 32)).denote (laneOf k Γ W)
      rw [ofNat_toNat_256, bcast256_lane]; rfl
  | vpackZMM bop => simp only [CoveredExpr] at he
  | vpackZMMd bop => simp only [CoveredExpr] at he
  | vprordZMM n => simp only [CoveredExpr] at he
  | vpslldq n => simp only [CoveredExpr] at he
  | vpsrldq n => simp only [CoveredExpr] at he
  | vsimd op => simp only [CoveredExpr] at he
  | mulhi w => simp only [CoveredExpr] at he
  | addCarryLo w => simp only [CoveredExpr] at he
  | addCarryHi w => simp only [CoveredExpr] at he
  | sarImm w n => simp only [CoveredExpr] at he
  | select w => simp only [CoveredExpr] at he
  | callN nm a r => simp only [CoveredExpr] at he
  | vymm op => simp only [CoveredExpr] at he

/-! ## 6. Whole-program lane preservation -/

/-- **`batch8` is lane-preserving.** For a covered program returning `reg 32`,
    dword lane `k` of the widened program's denotation equals the scalar program's
    denotation on the lane-`k` valuation. The induction on the `Com` let-chain uses
    `spliceCom_denote` to peel each block and `blockOpLane` for each op. -/
theorem batch8_denote : {Γ : Ctxt jasminDialect} → (c : Com jasminDialect Γ (.reg 32)) →
    Batch8Covered c → (W : Ctxt.Valuation (widen8Ctxt Γ)) → (k : Fin 8) →
    BitVec.extractLsb' (32 * k.val) 32 ((batch8 c).denote W) = c.denote (laneOf k Γ W)
  | _, .ret v, _, W, k => laneOf_lookup v W k
  | Γ, .var e body, hc, W, k => by
      obtain ⟨he, hbody⟩ := hc
      have hop := blockOpLane e he W k
      show BitVec.extractLsb' (32 * k.val) 32
          ((spliceCom (lowering.lowerExprBlock e) (batch8 body)).denote W)
          = body.denote (Ctxt.Valuation.extend (laneOf k Γ W) (e.denote (laneOf k Γ W)))
      rw [spliceCom_denote]
      have IH := batch8_denote body hbody
        (Ctxt.Valuation.extend W ((lowering.lowerExprBlock e).denote W)) k
      refine IH.trans ?_
      congr 1
      show Ctxt.Valuation.extend (laneOf k Γ W)
          (laneOfTy k _ ((lowering.lowerExprBlock e).denote W))
          = Ctxt.Valuation.extend (laneOf k Γ W) (e.denote (laneOf k Γ W))
      rw [hop]

end CatCrypt.Crypto.Optimizer.Batch8
