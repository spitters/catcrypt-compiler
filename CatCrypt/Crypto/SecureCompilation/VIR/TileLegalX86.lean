/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.TileLegal
public import CatCrypt.Crypto.SecureCompilation.VIR.LaneMapVec

/-!
# Tile legalisation targets on x86 vector registers

Three lane shapes of `jasminDialect` as `TileTarget` records: eight 64-bit lanes in a ZMM
register (`zmmQ`), sixteen 32-bit lanes in a ZMM register (`zmmD`) and four 64-bit lanes in
a YMM register (`ymmQ`). A tile of `n` lanes of `w` bits has the type `.reg (w * n)`.

A `VecKit n w` holds what the three shapes share: the lane read and the lane assembly of
the register, and a packed expression for every `JasminBinOp`. From it come the blocks of
a constant, of an elementwise binary operation, of a shift by a broadcast count, of a
rotation as two shifts and an `or`, and of a blend by a constant mask as `and`, `andn` and
`or`. `VecKit.target` builds the `TileTarget` from a kit and the blocks particular to the
shape, which take precedence.

| operation | `zmmQ` 8x64 | `zmmD` 16x32 | `ymmQ` 4x64 |
|---|---|---|---|
| `tileBin` | `vpackZMM` | `vpackZMMd` | `vymm` (`vpsllvq`, `vpsrlvq` for the shifts) |
| `tileConst` | `regConst` | `regConst` | `regConst` |
| `shl`, `lshr` by `c < w` | broadcast count | broadcast count | `vpsllq`, `vpsrlq` (every `c`) |
| `rotl` by `c < w` | two shifts and `or` | two shifts and `or` | `vprolq` (every `c`) |
| `rotr` | two shifts and `or`, `c < w` | `vprordZMM` (every `c`) | two shifts and `or`, `c < w` |
| `tileBlend` | `and`, `andn`, `or` | `and`, `andn`, `or` | `and`, `andn`, `or` |
| `tileShuffle` | refused | refused | two `vpermq` and a mask blend |
| `tileBroadcast` | refused | refused | `vpermq` |
| `tileReduce` | refused | refused | three `vpermq` and three `vpaddq` |
| `ashr`, `tileMulhu`, `tilePermute` | refused | refused | refused |

## Main definitions

* `regOf`, `packAt` — the register type of a tile type and the value transport.
* `isVecOp`, `VecQuiet`, `allVec` — the operations the blocks use, the leakage models in
  which they are quiet, and the blocks made of them.
* `VecKit`, `VecKit.target` — the shared packed operations and the target built from them.
* `kitZmmQ`, `kitZmmD`, `kitYmmQ`, `zmmQ`, `zmmD`, `ymmQ` — the three shapes.

## Main results

* `VecKit.un_spec`, `VecKit.bn_spec` — the lane laws of the shared blocks.
* `zmmDUn_spec`, `ymmUn_spec`, `ymmBn_spec` — the lane laws of the blocks particular to a
  shape.
* `zmmQ_quiet`, `zmmD_quiet`, `ymmQ_quiet`, `vecQuiet_jLeakModel` — the blocks emit no
  event in a model in which the vector operations are quiet.
* `mulhu_refused`, `bin_legal`, `zmm_refused`, `ymm_refused` — entries of the table.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.TileLegalX86

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.TileDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LaneMapVec
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.VIR.TileLegal
open CatCrypt.Crypto.SecureCompilation.VIR.YmmDialect
  (yQwordW yOfQwordsW vpermqW vpsllqW vpsrlqW vprolqW)
open CatCrypt.Crypto.Optimizer.PackedArith256 (yQwordW_yOfQwordsW)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak (JLeakParams jLeakModel jKind)

/-! ## 1. Registers of lanes -/

/-- The register type of a tile type: `w * n` bits for `n` lanes of `w` bits. -/
def regOf : TileTy → JasminTy
  | .tile n w => .reg (w * n)

/-- The register of a tile of `n` lanes of `w` bits: the assembly `of` of its lanes at the
    shape `n0`, `w0`, and zero at every other shape. -/
def packReg (n0 w0 : Nat) (of : (Fin n0 → BitVec w0) → BitVec (w0 * n0)) (n w : Nat)
    (x : Fin n → BitVec w) : BitVec (w * n) :=
  if h : n = n0 ∧ w = w0 then
    cast (by rw [h.1, h.2]) (of (cast (by rw [h.1, h.2]) x))
  else 0

/-- At the shape, `packReg` is the lane assembly. -/
theorem packReg_self (n0 w0 : Nat) (of : (Fin n0 → BitVec w0) → BitVec (w0 * n0))
    (x : Fin n0 → BitVec w0) : packReg n0 w0 of n0 w0 x = of x := by
  simp [packReg]

/-- The value transport of tiles to registers at the shape `n0`, `w0`. -/
def packAt (n0 w0 : Nat) (of : (Fin n0 → BitVec w0) → BitVec (w0 * n0)) :
    (t : TileTy) → ⟦t⟧ → ⟦regOf t⟧
  | .tile n w, x => packReg n0 w0 of n w x

/-- Two registers of `n` lanes of `w` bits with equal lanes are equal. -/
theorem extract_inj (n w : Nat) (x y : BitVec (w * n))
    (h : ∀ k : Fin n, x.extractLsb' (w * k.val) w = y.extractLsb' (w * k.val) w) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hw : 0 < w := by
    rcases Nat.eq_zero_or_pos w with h0 | h0
    · subst h0; simp at hi
    · exact h0
  have hk : i / w < n := Nat.div_lt_of_lt_mul hi
  have h1 := congrArg (fun v => v.getLsbD (i % w)) (h ⟨i / w, hk⟩)
  simp only [BitVec.getLsbD_extractLsb', Nat.mod_lt i hw, decide_true, Bool.true_and,
    Nat.div_add_mod] at h1
  exact h1

/-- The operations of `jasminDialect` the blocks of this file use: a register constant and
    the packed operations on ZMM and YMM registers. -/
def isVecOp : JasminOp → Bool
  | .regConst _ _ | .vpackZMM _ | .vpackZMMd _ | .vprordZMM _ | .vymm _ => true
  | _ => false

/-- The leakage models in which every operation of `isVecOp` is quiet. -/
def VecQuiet (M : LeakModel jasminDialect) : Prop :=
  ∀ op, isVecOp op = true → M.kind op = .quiet

/-- The model `jLeakModel Pj` is in `VecQuiet` when `Pj` classes no operation of `isVecOp`
    as a variable-time instruction. -/
theorem vecQuiet_jLeakModel (Pj : JLeakParams)
    (h : ∀ op, isVecOp op = true → Pj.opVT op = none) : VecQuiet (jLeakModel Pj) := by
  intro op hop
  cases op <;> first
    | (cases hop; done)
    | simp only [jLeakModel, jKind, h _ hop]

/-- A block whose every operation is in `isVecOp`. -/
def allVec : {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t → Prop
  | _, _, .ret _ => True
  | _, _, .var e body => isVecOp e.op = true ∧ allVec body

/-- A block of `allVec` emits no event in a model of `VecQuiet`. -/
theorem ctLeak_allVec {M : LeakModel jasminDialect} (hM : VecQuiet M) :
    ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t), allVec c →
      ∀ V : Ctxt.Valuation Γ, Com.ctLeak M c V = []
  | _, _, .ret _, _, _ => rfl
  | _, _, .var e body, h, V => by
      show Expr.ctLeak M e V ++ Com.ctLeak M body _ = []
      rw [ctLeak_allVec hM body h.2]
      unfold Expr.ctLeak opLeak
      rw [hM _ h.1]
      rfl

/-- At the leaf semantics `jasminExtSem`, `jasminDenoteWith` is `jasminDenote`. -/
theorem denoteWith_extSem : jasminDenoteWith jasminExtSem = jasminDenote := by
  unfold jasminDenoteWith
  congr 1
  funext op
  cases op <;> rfl

/-! ## 2. The packed operations of a register -/

/-- The packed operations of a register of `n` lanes of `w` bits: the lane read, the lane
    assembly it inverts, its injectivity, and a packed expression for every `JasminBinOp`
    with its lane law. -/
structure VecKit (n w : Nat) where
  /-- Lane `k` of a register. -/
  lane : BitVec (w * n) → Fin n → BitVec w
  /-- The register of given lanes. -/
  ofLanes : (Fin n → BitVec w) → BitVec (w * n)
  /-- Lane `k` of an assembled register. -/
  lane_ofLanes : ∀ f k, lane (ofLanes f) k = f k
  /-- Two registers with equal lanes are equal. -/
  lane_inj : ∀ x y, (∀ k, lane x k = lane y k) → x = y
  /-- The packed expression of a scalar operation. -/
  pk : JasminBinOp → PackBuilder (w * n)
  /-- Lane `k` of a packed expression is the scalar operation on lane `k`. -/
  pk_lane : ∀ (bop : JasminBinOp) (Γ : Ctxt jasminDialect) (a b : Ctxt.Var Γ (.reg (w * n)))
    (V : Ctxt.Valuation Γ) (k : Fin n),
    lane ((pk bop Γ a b).denote V) k = bop.apply (lane (a.lookup V) k) (lane (b.lookup V) k)
  /-- A packed expression is an operation of `isVecOp`. -/
  pk_vec : ∀ (bop : JasminBinOp) (Γ : Ctxt jasminDialect) (a b : Ctxt.Var Γ (.reg (w * n))),
    isVecOp (pk bop Γ a b).op = true

/-- A one-operand block on registers of `n` lanes of `w` bits. -/
abbrev Blk1 (n w : Nat) : Type := Com jasminDialect [.reg (w * n)] (.reg (w * n))

/-- A two-operand block on registers of `n` lanes of `w` bits. -/
abbrev Blk2 (n w : Nat) : Type :=
  Com jasminDialect [.reg (w * n), .reg (w * n)] (.reg (w * n))

/-- The law of a one-operand block: lane `k` of its value is lane `k` of the tile
    operation on the lanes of its operand, and its operations are in `isVecOp`. -/
def UnarySpec {n w : Nat} (lane : BitVec (w * n) → Fin n → BitVec w) (o : UnOp) (blk : Blk1 n w) :
    Prop :=
  (∀ (x : BitVec (w * n)) (k : Fin n),
    lane (blk.denote (.cons x .nil)) k = o.apply (lane x) k) ∧ allVec blk

/-- The law of a two-operand block. -/
def BinarySpec {n w : Nat} (lane : BitVec (w * n) → Fin n → BitVec w) (o : BinOp) (blk : Blk2 n w) :
    Prop :=
  (∀ (x y : BitVec (w * n)) (k : Fin n),
    lane (blk.denote (.cons x (.cons y .nil))) k = o.apply (lane x) (lane y) k) ∧ allVec blk

namespace VecKit

variable {n w : Nat} (K : VecKit n w)

/-- The register constant with the lanes `f`. -/
def cst (f : Fin n → BitVec w) {Γ : Ctxt jasminDialect} : Expr jasminDialect Γ (.reg (w * n)) :=
  ⟨.regConst (w * n) (K.ofLanes f).toNat, rfl, .nil⟩

/-- Lane `k` of the constant with the lanes `f` is `f k`. -/
theorem cst_lane (f : Fin n → BitVec w) {Γ : Ctxt jasminDialect} (V : Ctxt.Valuation Γ)
    (k : Fin n) : K.lane ((K.cst f (Γ := Γ)).denote V) k = f k := by
  show K.lane (BitVec.ofNat (w * n) (K.ofLanes f).toNat) k = f k
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, K.lane_ofLanes]

/-- The block of the constant tile of the value `c`. -/
def constBlk (c : Nat) : Com jasminDialect [] (.reg (w * n)) :=
  .var (K.cst fun _ => BitVec.ofNat w c) (.ret .here)

/-- The block of an elementwise binary operation. -/
def binBlk (bop : JasminBinOp) : Blk2 n w :=
  .var (K.pk bop _ .here (.there .here)) (.ret .here)

theorem binBlk_lane (bop : JasminBinOp) (x y : BitVec (w * n)) (k : Fin n) :
    K.lane ((K.binBlk bop).denote (.cons x (.cons y .nil))) k =
      bop.apply (K.lane x k) (K.lane y k) := by
  show K.lane ((K.pk bop _ .here (.there .here)).denote _) k = _
  rw [K.pk_lane]
  rfl

/-- The block of a binary operation against the broadcast constant `c`. -/
def shBlk (bop : JasminBinOp) (c : Nat) : Blk1 n w :=
  .var (K.cst fun _ => BitVec.ofNat w c) (.var (K.pk bop _ (.there .here) .here) (.ret .here))

theorem shBlk_lane (bop : JasminBinOp) (c : Nat) (x : BitVec (w * n)) (k : Fin n) :
    K.lane ((K.shBlk bop c).denote (.cons x .nil)) k =
      bop.apply (K.lane x k) (BitVec.ofNat w c) := by
  show K.lane ((K.pk bop _ (.there .here) .here).denote _) k = _
  rw [K.pk_lane]
  show bop.apply (K.lane x k) (K.lane ((K.cst _).denote _) k) = _
  rw [K.cst_lane]

/-- The block that combines by `or` two binary operations of the operand against the
    broadcast constants `c1` and `c2`. -/
def rotBlk (b1 : JasminBinOp) (c1 : Nat) (b2 : JasminBinOp) (c2 : Nat) : Blk1 n w :=
  .var (K.cst fun _ => BitVec.ofNat w c1)
    (.var (K.pk b1 _ (.there .here) .here)
      (.var (K.cst fun _ => BitVec.ofNat w c2)
        (.var (K.pk b2 _ (.there (.there (.there .here))) .here)
          (.var (K.pk .or _ (.there (.there .here)) .here) (.ret .here)))))

theorem rotBlk_lane (b1 : JasminBinOp) (c1 : Nat) (b2 : JasminBinOp) (c2 : Nat)
    (x : BitVec (w * n)) (k : Fin n) :
    K.lane ((K.rotBlk b1 c1 b2 c2).denote (.cons x .nil)) k =
      b1.apply (K.lane x k) (BitVec.ofNat w c1) ||| b2.apply (K.lane x k) (BitVec.ofNat w c2) := by
  show K.lane ((K.pk .or _ (.there (.there .here)) .here).denote _) k = _
  rw [K.pk_lane]
  show (K.lane ((K.pk b1 _ _ _).denote _) k) ||| (K.lane ((K.pk b2 _ _ _).denote _) k) = _
  rw [K.pk_lane, K.pk_lane]
  show b1.apply (K.lane x k) (K.lane ((K.cst _).denote _) k) |||
    b2.apply (K.lane x k) (K.lane ((K.cst _).denote _) k) = _
  rw [K.cst_lane, K.cst_lane]

theorem rotBlk_allVec (b1 : JasminBinOp) (c1 : Nat) (b2 : JasminBinOp) (c2 : Nat) :
    allVec (K.rotBlk b1 c1 b2 c2) :=
  ⟨rfl, K.pk_vec _ _ _ _, rfl, K.pk_vec _ _ _ _, K.pk_vec _ _ _ _, trivial⟩

theorem shBlk_allVec (bop : JasminBinOp) (c : Nat) : allVec (K.shBlk bop c) :=
  ⟨rfl, K.pk_vec _ _ _ _, trivial⟩

theorem constBlk_allVec (c : Nat) : allVec (K.constBlk c) := ⟨rfl, trivial⟩

/-- The blend of `a` and `b` by the constant mask `m`: with `c` the constant whose lane `i`
    is all ones when `m i` and zero otherwise, `(c and b) or (not c and a)`. -/
def blendCom (m : Fin n → Bool) {Γ : Ctxt jasminDialect} (a b : Ctxt.Var Γ (.reg (w * n))) :
    Com jasminDialect Γ (.reg (w * n)) :=
  .var (K.cst fun i => if m i then BitVec.allOnes w else 0)
    (.var (K.pk .and _ .here b.there)
      (.var (K.pk .andn _ (.there .here) a.there.there)
        (.var (K.pk .or _ (.there .here) .here) (.ret .here))))

/-- Lane `k` of the blend is lane `k` of `b` when `m k` and of `a` otherwise. -/
theorem blendCom_lane (m : Fin n → Bool) {Γ : Ctxt jasminDialect}
    (a b : Ctxt.Var Γ (.reg (w * n))) (V : Ctxt.Valuation Γ) (k : Fin n) :
    K.lane ((K.blendCom m a b).denote V) k =
      if m k then K.lane (b.lookup V) k else K.lane (a.lookup V) k := by
  show K.lane ((K.pk .or _ (.there .here) .here).denote _) k = _
  rw [K.pk_lane]
  show (K.lane ((K.pk .and _ _ _).denote _) k) ||| (K.lane ((K.pk .andn _ _ _).denote _) k) = _
  rw [K.pk_lane, K.pk_lane]
  show (K.lane ((K.cst _).denote _) k &&& K.lane (b.lookup V) k) |||
    (~~~ K.lane ((K.cst _).denote _) k &&& K.lane (a.lookup V) k) = _
  rw [K.cst_lane]
  cases m k <;> simp

theorem blendCom_allVec (m : Fin n → Bool) {Γ : Ctxt jasminDialect}
    (a b : Ctxt.Var Γ (.reg (w * n))) : allVec (K.blendCom m a b) :=
  ⟨rfl, K.pk_vec _ _ _ _, K.pk_vec _ _ _ _, K.pk_vec _ _ _ _, trivial⟩

/-- The one-operand blocks every kit has: the shifts by a broadcast count below the lane
    width, and the two rotations by a count below the lane width as two shifts and an
    `or`. -/
def un : UnOp → Option (Blk1 n w)
  | .shiftImm .shl c => if c < w then some (K.shBlk .shl c) else none
  | .shiftImm .lshr c => if c < w then some (K.shBlk .shr c) else none
  | .shiftImm .rotl c => if c < w then some (K.rotBlk .shl c .shr (w - c)) else none
  | .shiftImm .rotr c => if c < w then some (K.rotBlk .shr c .shl (w - c)) else none
  | _ => none

/-- The two-operand blocks every kit has: the elementwise binary operations and the blend
    by a constant mask. -/
def bn : BinOp → Option (Blk2 n w)
  | .bin bop => some (K.binBlk bop)
  | .blend mask => some (K.blendCom (fun i => mask.getD i.val false) .here (.there .here))
  | _ => none

omit K in
theorem toNat_ofNat_le {c : Nat} (hc : c ≤ w) : (BitVec.ofNat w c).toNat = c := by
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hc Nat.lt_two_pow_self)

/-- **The lane laws of the shared one-operand blocks.** -/
theorem un_spec (o : UnOp) (blk : Blk1 n w) (h : K.un o = some blk) : UnarySpec K.lane o blk := by
  cases o with
  | broadcast l => cases h
  | reduce => cases h
  | shiftImm op c =>
      cases op <;> simp only [un] at h
      case ashr => cases h
      case shl =>
        split at h
        · rename_i hc
          cases h
          refine ⟨fun x k => ?_, K.shBlk_allVec _ _⟩
          rw [shBlk_lane]
          show (K.lane x k) <<< (BitVec.ofNat w c).toNat = (K.lane x k) <<< c
          rw [toNat_ofNat_le (Nat.le_of_lt hc)]
        · cases h
      case lshr =>
        split at h
        · rename_i hc
          cases h
          refine ⟨fun x k => ?_, K.shBlk_allVec _ _⟩
          rw [shBlk_lane]
          show (K.lane x k) >>> (BitVec.ofNat w c).toNat = (K.lane x k) >>> c
          rw [toNat_ofNat_le (Nat.le_of_lt hc)]
        · cases h
      case rotl =>
        split at h
        · rename_i hc
          cases h
          refine ⟨fun x k => ?_, K.rotBlk_allVec _ _ _ _⟩
          rw [rotBlk_lane]
          show (K.lane x k) <<< (BitVec.ofNat w c).toNat |||
            (K.lane x k) >>> (BitVec.ofNat w (w - c)).toNat = (K.lane x k).rotateLeft c
          rw [toNat_ofNat_le (Nat.le_of_lt hc), toNat_ofNat_le (Nat.sub_le w c),
            BitVec.rotateLeft_def, Nat.mod_eq_of_lt hc]
        · cases h
      case rotr =>
        split at h
        · rename_i hc
          cases h
          refine ⟨fun x k => ?_, K.rotBlk_allVec _ _ _ _⟩
          rw [rotBlk_lane]
          show (K.lane x k) >>> (BitVec.ofNat w c).toNat |||
            (K.lane x k) <<< (BitVec.ofNat w (w - c)).toNat = (K.lane x k).rotateRight c
          rw [toNat_ofNat_le (Nat.le_of_lt hc), toNat_ofNat_le (Nat.sub_le w c),
            rorImm_denote_eq_shiftOr c hc]
        · cases h

/-- **The lane laws of the shared two-operand blocks.** -/
theorem bn_spec (o : BinOp) (blk : Blk2 n w) (h : K.bn o = some blk) : BinarySpec K.lane o blk := by
  cases o with
  | bin bop =>
      cases h
      exact ⟨fun x y k => K.binBlk_lane _ x y k, K.pk_vec _ _ _ _, trivial⟩
  | blend mask =>
      cases h
      exact ⟨fun x y k => K.blendCom_lane _ _ _ _ k, K.blendCom_allVec _ _ _⟩
  | permute => cases h
  | mulhu => cases h
  | shuffle idx => cases h

/-- The lanes of the register of a tile at the shape are the tile. -/
theorem lane_packAt (a : Fin n → BitVec w) :
    K.lane (packAt n w K.ofLanes (.tile n w) a) = a := by
  funext k
  show K.lane (packReg n w K.ofLanes n w a) k = a k
  rw [packReg_self, K.lane_ofLanes]

theorem orElse_spec1 (un1 : UnOp → Option (Blk1 n w))
    (h1 : ∀ o blk, un1 o = some blk → UnarySpec K.lane o blk) (o : UnOp) (blk : Blk1 n w)
    (h : ((un1 o).orElse fun _ => K.un o) = some blk) : UnarySpec K.lane o blk := by
  cases hu : un1 o with
  | some b => rw [hu] at h; cases h; exact h1 o _ hu
  | none => rw [hu] at h; exact K.un_spec o blk h

theorem orElse_spec2 (bn1 : BinOp → Option (Blk2 n w))
    (h2 : ∀ o blk, bn1 o = some blk → BinarySpec K.lane o blk) (o : BinOp) (blk : Blk2 n w)
    (h : ((bn1 o).orElse fun _ => K.bn o) = some blk) : BinarySpec K.lane o blk := by
  cases hu : bn1 o with
  | some b => rw [hu] at h; cases h; exact h2 o _ hu
  | none => rw [hu] at h; exact K.bn_spec o blk h

/-- **The target of a kit.** The `TileTarget` of `jasminDialect` at `n` lanes of `w` bits:
    the blocks `un1` and `bn1` of the shape where they are defined, and the shared blocks
    `K.un` and `K.bn` otherwise. -/
def target (un1 : UnOp → Option (Blk1 n w)) (bn1 : BinOp → Option (Blk2 n w))
    (h1 : ∀ o blk, un1 o = some blk → UnarySpec K.lane o blk)
    (h2 : ∀ o blk, bn1 o = some blk → BinarySpec K.lane o blk) : TileTarget jasminDialect where
  laneCount := n
  laneBits := w
  ty := regOf
  pack := packAt n w K.ofLanes
  lane := K.lane
  lane_pack := fun x k => congrFun (K.lane_packAt x) k
  lane_inj := K.lane_inj
  const? := fun c => some (K.constBlk c)
  unary? := fun o => (un1 o).orElse fun _ => K.un o
  binary? := fun o => (bn1 o).orElse fun _ => K.bn o
  const_lane := by
    intro c blk h k
    cases h
    exact K.cst_lane _ _ k
  unary_lane := by
    intro o blk h a k
    exact ((K.orElse_spec1 un1 h1 o blk h).1 _ k).trans (by rw [K.lane_packAt])
  binary_lane := by
    intro o blk h a b k
    exact ((K.orElse_spec2 bn1 h2 o blk h).1 _ _ k).trans
      (by rw [K.lane_packAt, K.lane_packAt])

/-- The blocks of the target of a kit emit no event in a model of `VecQuiet`. -/
theorem target_quiet (un1 : UnOp → Option (Blk1 n w)) (bn1 : BinOp → Option (Blk2 n w))
    (h1 : ∀ o blk, un1 o = some blk → UnarySpec K.lane o blk)
    (h2 : ∀ o blk, bn1 o = some blk → BinarySpec K.lane o blk)
    {M : LeakModel jasminDialect} (hM : VecQuiet M) :
    (K.target un1 bn1 h1 h2).Quiet M where
  const := by
    intro c blk h W
    cases h
    exact ctLeak_allVec hM _ (K.constBlk_allVec c) W
  unary := fun o blk h W => ctLeak_allVec hM _ (K.orElse_spec1 un1 h1 o blk h).2 W
  binary := fun o blk h W => ctLeak_allVec hM _ (K.orElse_spec2 bn1 h2 o blk h).2 W

end VecKit

/-! ## 3. The three kits -/

/-- Eight 64-bit lanes in a ZMM register, on `vpackZMM`. -/
def kitZmmQ : VecKit 8 64 where
  lane := zmmLane
  ofLanes := zmmOfLanes
  lane_ofLanes := KeccakThetaPiAbstractCom.zmmOfLanes_zmmLane'
  lane_inj := fun x y h => extract_inj 8 64 x y h
  pk := fun bop _ a b => ⟨.vpackZMM bop, rfl, .cons a (.cons b .nil)⟩
  pk_lane := fun bop Γ a b V k => by
    have h := qwordZmm.pack_lane jasminExtSem bop rfl Γ a b V k
    rw [denoteWith_extSem] at h
    exact h
  pk_vec := fun _ _ _ _ => rfl

/-- Sixteen 32-bit lanes in a ZMM register, on `vpackZMMd`. -/
def kitZmmD : VecKit 16 32 where
  lane := zmmLane32
  ofLanes := zmmOfLanes32
  lane_ofLanes := ZmmDwordLane.zmmOfLanes32_zmmLane32
  lane_inj := fun x y h => extract_inj 16 32 x y h
  pk := fun bop _ a b => ⟨.vpackZMMd bop, rfl, .cons a (.cons b .nil)⟩
  pk_lane := fun bop Γ a b V k => by
    have h := dwordZmm.pack_lane jasminExtSem bop rfl Γ a b V k
    rw [denoteWith_extSem] at h
    exact h
  pk_vec := fun _ _ _ _ => rfl

/-- Four 64-bit lanes in a YMM register, on the `vymm` operations of `ymmVPackExpr`. -/
def kitYmmQ : VecKit 4 64 where
  lane := fun v k => yQwordW v k.val
  ofLanes := yOfQwordsW
  lane_ofLanes := yQwordW_yOfQwordsW
  lane_inj := fun x y h => extract_inj 4 64 x y h
  pk := ymmVPackExpr
  pk_lane := fun bop Γ a b V k => by
    have h := qwordYmmV.pack_lane jasminExtSem bop rfl Γ a b V k
    rw [denoteWith_extSem] at h
    exact h
  pk_vec := fun bop _ _ _ => by cases bop <;> rfl

/-! ## 4. The ZMM targets -/

/-- **Eight 64-bit lanes in a ZMM register.** Every block is a shared block of
    `kitZmmQ`. -/
def zmmQ : TileTarget jasminDialect :=
  kitZmmQ.target (fun _ => none) (fun _ => none) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)

/-- The one-operand block particular to sixteen 32-bit lanes: the rotation right by an
    immediate as `vprordZMM`. -/
def zmmDUn : UnOp → Option (Blk1 16 32)
  | .shiftImm .rotr c => some (.var ⟨.vprordZMM c, rfl, .cons .here .nil⟩ (.ret .here))
  | _ => none

theorem zmmDUn_spec (o : UnOp) (blk : Blk1 16 32) (h : zmmDUn o = some blk) :
    UnarySpec kitZmmD.lane o blk := by
  cases o with
  | broadcast l => cases h
  | reduce => cases h
  | shiftImm op c =>
      cases op <;> first | (cases h; done) | skip
      cases h
      exact ⟨fun x k => ZmmDwordLane.zmmRorD_lane c x k, rfl, trivial⟩

/-- **Sixteen 32-bit lanes in a ZMM register.** The rotation right is `vprordZMM`; every
    other block is a shared block of `kitZmmD`. -/
def zmmD : TileTarget jasminDialect :=
  kitZmmD.target zmmDUn (fun _ => none) zmmDUn_spec (fun _ _ h => nomatch h)

/-! ## 5. The YMM target -/

/-- The immediate of `vpermq` that reads lane `s j` into lane `j`. -/
def immOf (s : Fin 4 → Fin 4) : Nat :=
  (s 0).val + 4 * (s 1).val + 16 * (s 2).val + 64 * (s 3).val

/-- The two-bit field `j` of `immOf s` is `s j`. -/
theorem immOf_field (s : Fin 4 → Fin 4) (j : Fin 4) :
    (immOf s >>> (2 * j.val)) &&& 3 = (s j).val := by
  have h0 := (s 0).isLt
  have h1 := (s 1).isLt
  have h2 := (s 2).isLt
  have h3 := (s 3).isLt
  have hm : ∀ x : Nat, x &&& 3 = x % 4 := fun x => Nat.and_two_pow_sub_one_eq_mod x 2
  rw [hm, Nat.shiftRight_eq_div_pow]
  fin_cases j <;> simp [immOf] <;> omega

/-- The `vpermq` that reads lane `s j` of `a` into lane `j`. -/
def permE (s : Fin 4 → Fin 4) {Γ : Ctxt jasminDialect} (a : Ctxt.Var Γ (.reg 256)) :
    Expr jasminDialect Γ (.reg 256) :=
  ⟨.vymm (.vpermq (immOf s)), rfl, .cons a .nil⟩

theorem permE_lane (s : Fin 4 → Fin 4) {Γ : Ctxt jasminDialect} (a : Ctxt.Var Γ (.reg 256))
    (V : Ctxt.Valuation Γ) (k : Fin 4) :
    yQwordW ((permE s a).denote V) k.val = yQwordW (a.lookup V) (s k).val := by
  show yQwordW (vpermqW (a.lookup V) (immOf s)) k.val = _
  rw [vpermqW, yQwordW_yOfQwordsW, immOf_field]

/-- The block of `tileReduce` on four lanes: the operand added to its three rotations by
    lanes. -/
def reduceBlk : Blk1 4 64 :=
  .var (permE (· + 1) .here)
    (.var (permE (· + 2) (.there .here))
      (.var (permE (· + 3) (.there (.there .here)))
        (.var (kitYmmQ.pk .add _ (.there (.there (.there .here))) (.there (.there .here)))
          (.var (kitYmmQ.pk .add _ .here (.there (.there .here)))
            (.var (kitYmmQ.pk .add _ .here (.there (.there .here))) (.ret .here))))))

theorem reduce_sum (f : Fin 4 → BitVec 64) (k : Fin 4) :
    f k + f (k + 1) + f (k + 2) + f (k + 3) = tileReduceApply f k := by
  have hs : tileReduceApply f k = 0 + f 0 + f 1 + f 2 + f 3 := rfl
  rw [hs]
  fin_cases k <;> simp <;>
    first
    | rfl
    | abel

theorem reduceBlk_lane (x : BitVec 256) (k : Fin 4) :
    kitYmmQ.lane (reduceBlk.denote (.cons x .nil)) k = tileReduceApply (kitYmmQ.lane x) k := by
  rw [← reduce_sum]
  show kitYmmQ.lane ((kitYmmQ.pk .add _ .here (.there (.there .here))).denote _) k = _
  rw [kitYmmQ.pk_lane]
  show kitYmmQ.lane ((kitYmmQ.pk .add _ .here (.there (.there .here))).denote _) k +
    yQwordW ((permE (· + 3) _).denote _) k.val = _
  rw [kitYmmQ.pk_lane, permE_lane]
  show kitYmmQ.lane ((kitYmmQ.pk .add _ (.there (.there (.there .here)))
      (.there (.there .here))).denote _) k +
    yQwordW ((permE (· + 2) _).denote _) k.val + _ = _
  rw [kitYmmQ.pk_lane, permE_lane]
  show yQwordW x k.val + yQwordW ((permE (· + 1) _).denote _) k.val + _ + _ = _
  rw [permE_lane]
  rfl

/-- The one-operand blocks particular to four 64-bit lanes in a YMM register: `vpsllq`,
    `vpsrlq` and `vprolq` by an immediate, `vpermq` for `tileBroadcast`, and `reduceBlk`. -/
def ymmUn : UnOp → Option (Blk1 4 64)
  | .shiftImm .shl c => some (.var ⟨.vymm (.vpsllq c), rfl, .cons .here .nil⟩ (.ret .here))
  | .shiftImm .lshr c => some (.var ⟨.vymm (.vpsrlq c), rfl, .cons .here .nil⟩ (.ret .here))
  | .shiftImm .rotl c => some (.var ⟨.vymm (.vprolq c), rfl, .cons .here .nil⟩ (.ret .here))
  | .broadcast l =>
      some (.var (permE (fun _ => ⟨l % 4, Nat.mod_lt _ (by decide)⟩) .here) (.ret .here))
  | .reduce => some reduceBlk
  | _ => none

theorem ymmUn_spec (o : UnOp) (blk : Blk1 4 64) (h : ymmUn o = some blk) :
    UnarySpec kitYmmQ.lane o blk := by
  cases o with
  | broadcast l =>
      cases h
      refine ⟨fun x k => ?_, rfl, trivial⟩
      exact permE_lane _ _ _ k
  | reduce =>
      cases h
      exact ⟨reduceBlk_lane, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  | shiftImm op c =>
      cases op <;> first | (cases h; done) | skip
      · cases h
        exact ⟨fun x k => yQwordW_vpsllqW x c k, rfl, trivial⟩
      · cases h
        exact ⟨fun x k => yQwordW_vpsrlqW x c k, rfl, trivial⟩
      · cases h
        refine ⟨fun x k => ?_, rfl, trivial⟩
        show yQwordW (vprolqW x c) k.val = (yQwordW x k.val).rotateLeft c
        rw [vprolqW, yQwordW_yOfQwordsW]

/-- The lane of either operand that lane `j` of a shuffle by `idx` reads. -/
def shufSel (idx : List Nat) : Fin 4 → Fin 4 :=
  fun j => ⟨idx.getD j.val j.val % 4, Nat.mod_lt _ (by decide)⟩

/-- The block of `tileShuffle` on four lanes: both operands permuted by `shufSel idx`, and
    blended by the mask that takes the second operand where the index is at least `4`. -/
def shufBlk (idx : List Nat) : Blk2 4 64 :=
  .var (permE (shufSel idx) .here)
    (.var (permE (shufSel idx) (.there (.there .here)))
      (kitYmmQ.blendCom (fun j => decide (¬ idx.getD j.val j.val % 8 < 4)) (.there .here) .here))

theorem shufBlk_lane (idx : List Nat) (x y : BitVec 256) (k : Fin 4) :
    kitYmmQ.lane ((shufBlk idx).denote (.cons x (.cons y .nil))) k =
      tileShuffleApply idx (kitYmmQ.lane x) (kitYmmQ.lane y) k := by
  show kitYmmQ.lane ((kitYmmQ.blendCom _ (.there .here) .here).denote _) k = _
  rw [kitYmmQ.blendCom_lane]
  show (if decide (¬ idx.getD k.val k.val % 8 < 4) = true
      then yQwordW ((permE (shufSel idx) _).denote _) k.val
      else yQwordW ((permE (shufSel idx) _).denote _) k.val) = _
  rw [permE_lane, permE_lane]
  unfold tileShuffleApply
  by_cases hx : idx.getD k.val k.val % 8 < 4
  · have e : idx.getD k.val k.val % 4 = idx.getD k.val k.val % (2 * 4) := by omega
    simp only [hx, not_true_eq_false, decide_false, Bool.false_eq_true, if_false, dif_pos]
    show yQwordW x (idx.getD k.val k.val % 4) = yQwordW x (idx.getD k.val k.val % (2 * 4))
    rw [e]
  · have e : idx.getD k.val k.val % 4 = idx.getD k.val k.val % (2 * 4) - 4 := by omega
    simp only [hx, not_false_eq_true, decide_true, if_true]
    show yQwordW y (idx.getD k.val k.val % 4) = yQwordW y (idx.getD k.val k.val % (2 * 4) - 4)
    rw [e]

/-- The two-operand block particular to four 64-bit lanes in a YMM register: `shufBlk`. -/
def ymmBn : BinOp → Option (Blk2 4 64)
  | .shuffle idx => some (shufBlk idx)
  | _ => none

theorem ymmBn_spec (o : BinOp) (blk : Blk2 4 64) (h : ymmBn o = some blk) :
    BinarySpec kitYmmQ.lane o blk := by
  cases o with
  | shuffle idx =>
      cases h
      exact ⟨shufBlk_lane idx, rfl, rfl, kitYmmQ.blendCom_allVec _ _ _⟩
  | bin bop => cases h
  | blend mask => cases h
  | permute => cases h
  | mulhu => cases h

/-- **Four 64-bit lanes in a YMM register.** The blocks of `ymmUn` and `ymmBn`, and the
    shared blocks of `kitYmmQ` otherwise. -/
def ymmQ : TileTarget jasminDialect := kitYmmQ.target ymmUn ymmBn ymmUn_spec ymmBn_spec

/-! ## 6. Leakage and the gate table -/

/-- The blocks of `zmmQ` emit no event in a model of `VecQuiet`. -/
theorem zmmQ_quiet {M : LeakModel jasminDialect} (hM : VecQuiet M) : zmmQ.Quiet M :=
  kitZmmQ.target_quiet _ _ _ _ hM

/-- The blocks of `zmmD` emit no event in a model of `VecQuiet`. -/
theorem zmmD_quiet {M : LeakModel jasminDialect} (hM : VecQuiet M) : zmmD.Quiet M :=
  kitZmmD.target_quiet _ _ _ _ hM

/-- The blocks of `ymmQ` emit no event in a model of `VecQuiet`. -/
theorem ymmQ_quiet {M : LeakModel jasminDialect} (hM : VecQuiet M) : ymmQ.Quiet M :=
  kitYmmQ.target_quiet _ _ _ _ hM

/-- The unsigned high multiply is refused at the three shapes. -/
theorem mulhu_refused :
    zmmQ.binary? .mulhu = none ∧ zmmD.binary? .mulhu = none ∧ ymmQ.binary? .mulhu = none :=
  ⟨rfl, rfl, rfl⟩

/-- Every elementwise binary operation and every constant-mask blend is accepted at the
    three shapes. -/
theorem bin_legal (bop : JasminBinOp) (mask : List Bool) :
    (zmmQ.binary? (.bin bop)).isSome = true ∧ (zmmD.binary? (.bin bop)).isSome = true ∧
      (ymmQ.binary? (.bin bop)).isSome = true ∧ (zmmQ.binary? (.blend mask)).isSome = true ∧
      (zmmD.binary? (.blend mask)).isSome = true ∧ (ymmQ.binary? (.blend mask)).isSome = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The operations refused at the two ZMM shapes: the arithmetic shift right, the gather,
    the static shuffle, the broadcast of a lane and the reduction. -/
theorem zmm_refused (c l : Nat) (idx : List Nat) :
    zmmQ.unary? (.shiftImm .ashr c) = none ∧ zmmD.unary? (.shiftImm .ashr c) = none ∧
      zmmQ.binary? .permute = none ∧ zmmD.binary? .permute = none ∧
      zmmQ.binary? (.shuffle idx) = none ∧ zmmD.binary? (.shuffle idx) = none ∧
      zmmQ.unary? (.broadcast l) = none ∧ zmmD.unary? (.broadcast l) = none ∧
      zmmQ.unary? .reduce = none ∧ zmmD.unary? .reduce = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- At the YMM shape the arithmetic shift right and the gather are refused, and the static
    shuffle, the broadcast of a lane, the reduction and the shifts and the rotation left by
    every immediate are accepted. -/
theorem ymm_refused (c l : Nat) (idx : List Nat) :
    ymmQ.unary? (.shiftImm .ashr c) = none ∧ ymmQ.binary? .permute = none ∧
      (ymmQ.binary? (.shuffle idx)).isSome = true ∧
      (ymmQ.unary? (.broadcast l)).isSome = true ∧ (ymmQ.unary? .reduce).isSome = true ∧
      (ymmQ.unary? (.shiftImm .shl c)).isSome = true ∧
      (ymmQ.unary? (.shiftImm .lshr c)).isSome = true ∧
      (ymmQ.unary? (.shiftImm .rotl c)).isSome = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end CatCrypt.Crypto.SecureCompilation.VIR.TileLegalX86
