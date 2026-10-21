/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.X86VecDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.TileLegalX86
public import CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextValidate

/-!
# Selection of tile operations into x86 vector operations

Two lane shapes of a ZMM register as `TileTarget` records over `jasminVec`, the operation
sum of `jasminDialect` and the dialect `x86vec` of vector operations: sixteen 32-bit lanes
(`selD`) and eight 64-bit lanes (`selQ`). A tile of `n` lanes of `w` bits has the type
`.reg (w * n)`, as in `TileLegalX86`. Every block of the two gates consists of operations
of `x86vec`, and the lane law of each block is proved from the lane lemmas of
`ZmmTextModel`.

The lane moves go through the two forms the text model has, the dword permutation
`vpermd` and the dword blend `vpblendmd`: a lane of `r` dwords is moved as `r` dwords
(`idxC`, `maskC`, `lane_gather`, `lane_blend`).

| operation | `selD` 16x32 | `selQ` 8x64 |
|---|---|---|
| `tileConst` | `bcst` | `bcst` |
| `tileBin` | `lw 32` | `lw 64` |
| `shl`, `lshr` by every `c` | `shi` | `shi` |
| `ashr` by every `c` | `sra` | `sra` |
| `rotl` by every `c` | `rol c` | `rol c` |
| `rotr` by every `c` | `rol (32 - c % 32)` | `rol (64 - c % 64)` |
| `tileBroadcast` | `cst`, `perm` | `cst`, `perm` |
| `tileBlend` | `blend` | `blend` |
| `tileShuffle` | `cst`, two `perm`, `blend` | `cst`, two `perm`, `blend` |
| `tilePermute` | `perm` | `shi`, `dup`, `cst`, `lw 32 add`, `perm` |
| `tileMulhu` | two `lw 64 muludq`, three `dup`, `blend` | refused |
| `tileReduce` | refused | refused |

## Main definitions

* `IsShape`, `vlane`, `vof` — the two lane shapes, the lane read and the lane assembly.
* `idxC`, `maskC` — the index register of a static gather and the mask of a static blend.
* `unSel`, `binSel` — the one-operand and the two-operand selection.
* `shufBlk`, `mulhuBlk`, `permQBlk` — the blocks of the static shuffle, of the unsigned
  high multiply of dwords and of the gather of qwords.
* `selD`, `selQ` — the two targets; `tileVec` — the source dialect of the selection.
* `selDCert`, `selQCert` — the step certificates of the selection.

## Main results

* `lane_gather`, `lane_blend` — the lane laws of the dword permutation by `idxC` and of the
  dword blend under `maskC`.
* `rotateRight_eq_rotateLeft` — a rotation right is a rotation left by the complement.
* `unSel_spec`, `binSel_spec` — the lane laws of the selected blocks.
* `mulhuBlk_lane`, `permQBlk_lane` — the lane laws of the two long blocks.
* `selD_quiet`, `selQ_quiet`, `selD_leakRun`, `selQ_leakRun` — the selected blocks emit no
  event, and a selected program runs to the events of its source.
* `sel_accepts`, `sel_refused`, `sel_single` — entries of the table.
* `selQ_unary_of_zmmQ`, `selQ_binary_of_zmmQ`, `selD_unary_of_zmmD`, `selD_binary` — every
  operation the targets of `TileLegalX86` accept at a ZMM shape is accepted here.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.TileSelectX86

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.TileDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.VIR.NFTileSum
open CatCrypt.Crypto.SecureCompilation.VIR.TileLegal
open CatCrypt.Crypto.SecureCompilation.VIR.TileLegalX86 (regOf packAt packReg packReg_self zmmQ
  zmmD)
open CatCrypt.Crypto.SecureCompilation.VIR.X86VecDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextModel (Mode LOp wr lane ofLanes lane_ofLanes
  semLW semShImm semDup semMerge semPerm semRol bcast lane_semLW lane_semShImm lane_semDup
  lane_semMerge lane_semPerm lane_semRol lane32_even lane32_odd getLsbD_lane)
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextValidate (prod_lanes maskAAAA)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open Ctxt (Var Valuation)

/-! ## 1. Lane shapes of a 512-bit register -/

/-- The lane shapes of a 512-bit register: `n` lanes of `L` bits, each of `r` dwords. -/
def IsShape (L n r : Nat) : Prop := (r = 1 ∧ L = 32 ∧ n = 16) ∨ (r = 2 ∧ L = 64 ∧ n = 8)

/-- Sixteen lanes of one dword. -/
theorem isShape_dword : IsShape 32 16 1 := .inl ⟨rfl, rfl, rfl⟩

/-- Eight lanes of two dwords. -/
theorem isShape_qword : IsShape 64 8 2 := .inr ⟨rfl, rfl, rfl⟩

section Shape

variable {L n r : Nat}

theorem IsShape.pos (hS : IsShape L n r) : 0 < L ∧ 0 < n ∧ 0 < r := by
  rcases hS with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> omega

theorem IsShape.bound (hS : IsShape L n r) {k : Nat} (hk : k < n) : L * k + L ≤ 512 := by
  rcases hS with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> omega

/-- Lane `k` of a register of `n` lanes of `L` bits. -/
def vlane (L n : Nat) (x : BitVec 512) (k : Fin n) : BitVec L := lane L x k.val

/-- The register with the lanes `f`. -/
def vof (L n : Nat) (f : Fin n → BitVec L) : BitVec 512 :=
  ofLanes L (fun k => if h : k < n then f ⟨k, h⟩ else 0)

/-- Lane `k` of an assembled register. -/
theorem vlane_vof (hS : IsShape L n r) (f : Fin n → BitVec L) (k : Fin n) :
    vlane L n (vof L n f) k = f k := by
  unfold vlane vof
  rw [lane_ofLanes _ hS.pos.1 (hS.bound k.isLt), dif_pos k.isLt]

/-- Two registers with equal lanes are equal. -/
theorem lane_inj512 (hS : IsShape L n r) (x y : BitVec 512)
    (h : ∀ k, k < n → lane L x k = lane L y k) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hL : 0 < L := hS.pos.1
  have hk : i / L < n := by
    rcases hS with ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩ <;> omega
  have h1 := congrArg (fun v => v.getLsbD (i % L)) (h (i / L) hk)
  simp only [getLsbD_lane, Nat.mod_lt i hL, decide_true, Bool.true_and, Nat.div_add_mod] at h1
  exact h1

theorem vlane_inj (hS : IsShape L n r) (x y : BitVec 512)
    (h : ∀ k, vlane L n x k = vlane L n y k) : x = y :=
  lane_inj512 hS x y (fun k hk => h ⟨k, hk⟩)

/-- Two qwords are equal when their two dwords are. -/
theorem lane64_eq_of_dwords (x y : BitVec 512) (k k' : Nat)
    (h0 : lane 32 x (2 * k) = lane 32 y (2 * k'))
    (h1 : lane 32 x (2 * k + 1) = lane 32 y (2 * k' + 1)) : lane 64 x k = lane 64 y k' := by
  rw [lane32_even, lane32_even] at h0
  rw [lane32_odd, lane32_odd] at h1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h : i < 32
  · have e := congrArg (fun v => v.getLsbD i) h0
    simp only [BitVec.getLsbD_setWidth, h, decide_true, Bool.true_and] at e
    exact e
  · have e := congrArg (fun v => v.getLsbD (i - 32)) h1
    have e2 : 32 + (i - 32) = i := by omega
    have e3 : i - 32 < 32 := by omega
    simp only [BitVec.getLsbD_extractLsb', e2, e3, decide_true, Bool.true_and] at e
    exact e

/-- Two lanes are equal when their dwords are. -/
theorem lane_eq_of_dwords (hS : IsShape L n r) (x y : BitVec 512) (k k' : Nat)
    (h : ∀ t, t < r → lane 32 x (r * k + t) = lane 32 y (r * k' + t)) :
    lane L x k = lane L y k' := by
  rcases hS with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩
  · have e := h 0 (by omega)
    simp only [Nat.one_mul, Nat.add_zero] at e
    exact e
  · exact lane64_eq_of_dwords x y k k' (h 0 (by omega)) (h 1 (by omega))

/-! ## 2. Lane moves through the dword permutation and the dword blend -/

/-- The index register of the dword permutation that reads lane `s k` into lane `k`, for
    lanes of `r` dwords. -/
def idxC (r : Nat) (s : Nat → Nat) : BitVec 512 :=
  ofLanes 32 (fun j => BitVec.ofNat 32 ((r * s (j / r) + j % r) % 16))

theorem lane_perm_idxC (r : Nat) (s : Nat → Nat) (x : BitVec 512) {j : Nat} (hj : j < 16) :
    lane 32 (semPerm 16 x (idxC r s)) j = lane 32 x ((r * s (j / r) + j % r) % 16) := by
  rw [lane_semPerm _ _ _ hj]
  unfold idxC
  rw [lane_ofLanes _ (by omega) (by omega), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show (r * s (j / r) + j % r) % 16 < 2 ^ 32 from
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (by omega)), Nat.mod_mod]

/-- **The static gather.** Lane `k` of the dword permutation by `idxC r s` is lane `s k`
    of the source. -/
theorem lane_gather (hS : IsShape L n r) (s : Nat → Nat) (x : BitVec 512)
    {k : Nat} (hk : k < n) (hs : s k < n) :
    lane L (semPerm 16 x (idxC r s)) k = lane L x (s k) := by
  apply lane_eq_of_dwords hS
  intro t ht
  have hj : r * k + t < 16 := by rcases hS with ⟨rfl, _, rfl⟩ | ⟨rfl, _, rfl⟩ <;> omega
  have hr : 0 < r := by omega
  rw [lane_perm_idxC r s x hj, Nat.mul_add_div hr, Nat.div_eq_of_lt ht, Nat.add_zero,
    Nat.mul_add_mod, Nat.mod_eq_of_lt ht,
    Nat.mod_eq_of_lt (by rcases hS with ⟨rfl, _, rfl⟩ | ⟨rfl, _, rfl⟩ <;> omega)]

/-- The dword mask of the lane predicate `f`, for lanes of `r` dwords. -/
def maskC (r : Nat) (f : Nat → Bool) : BitVec 16 :=
  BitVec.ofFnLE (fun j : Fin 16 => f (j.val / r))

theorem getLsbD_maskC (r : Nat) (f : Nat → Bool) {j : Nat} (hj : j < 16) :
    (maskC r f).getLsbD j = f (j / r) := by
  unfold maskC
  rw [BitVec.getLsbD_ofFnLE]
  simp only [hj, dif_pos]

/-- **The static blend.** Lane `k` of the dword blend under `maskC r f` is lane `k` of the
    first operand where `f k`, else of the second. -/
theorem lane_blend (hS : IsShape L n r) (f : Nat → Bool) (a b : BitVec 512)
    {k : Nat} (hk : k < n) :
    lane L (semMerge (maskC r f) a b) k = if f k then lane L a k else lane L b k := by
  have hr : 0 < r := hS.pos.2.2
  have key : ∀ t, t < r → lane 32 (semMerge (maskC r f) a b) (r * k + t) =
      if f k then lane 32 a (r * k + t) else lane 32 b (r * k + t) := by
    intro t ht
    have hj : r * k + t < 16 := by rcases hS with ⟨rfl, _, rfl⟩ | ⟨rfl, _, rfl⟩ <;> omega
    rw [lane_semMerge _ _ _ hj, getLsbD_maskC r f hj, Nat.mul_add_div hr, Nat.div_eq_of_lt ht,
      Nat.add_zero]
  cases hf : f k
  · rw [if_neg (by decide)]
    exact lane_eq_of_dwords hS _ _ _ _ (fun t ht => by rw [key t ht, hf, if_neg (by decide)])
  · rw [if_pos rfl]
    exact lane_eq_of_dwords hS _ _ _ _ (fun t ht => by rw [key t ht, hf, if_pos rfl])

/-- A rotation right is the rotation left by the complement of the count. -/
theorem rotateRight_eq_rotateLeft {w : Nat} (hw : 0 < w) (x : BitVec w) (c : Nat) :
    x.rotateRight c = x.rotateLeft (w - c % w) := by
  have hc := Nat.mod_lt c hw
  rw [BitVec.rotateRight_def, BitVec.rotateLeft_def]
  by_cases h : c % w = 0
  · rw [h, Nat.sub_zero, Nat.mod_self, Nat.sub_zero, BitVec.shiftLeft_eq_zero (Nat.le_refl w),
      BitVec.ushiftRight_eq_zero (Nat.le_refl w), BitVec.ushiftRight_zero, BitVec.shiftLeft_zero]
  · rw [Nat.mod_eq_of_lt (show w - c % w < w by omega), show w - (w - c % w) = c % w by omega,
      BitVec.or_comm]

/-! ## 3. Blocks -/

/-- A one-operand block on 512-bit registers. -/
abbrev Blk1 : Type := Com jasminVec [VReg] VReg

/-- A two-operand block on 512-bit registers. -/
abbrev Blk2 : Type := Com jasminVec [VReg, VReg] VReg

theorem denote_var {Γ : Ctxt jasminVec} {s t : JasminTy} (e : Expr jasminVec Γ s)
    (body : Com jasminVec (s :: Γ) t) (V : Valuation Γ) :
    (Com.var e body).denote V = body.denote (V.extend (e.denote V)) := Eq.trans rfl rfl

theorem denote_ret {Γ : Ctxt jasminVec} {t : JasminTy} (v : Var Γ t) (V : Valuation Γ) :
    (Com.ret v : Com jasminVec Γ t).denote V = v.lookup V := Eq.trans rfl rfl

theorem lookup_here {Γ : Ctxt jasminVec} (v : ⟦VReg⟧) (V : Valuation Γ) :
    (Var.here : Var (VReg :: Γ) VReg).lookup (V.extend v) = v := Eq.trans rfl rfl

theorem lookup_there {Γ : Ctxt jasminVec} (w : Var Γ VReg) (v : ⟦VReg⟧) (V : Valuation Γ) :
    (Var.there w : Var (VReg :: Γ) VReg).lookup (V.extend v) = w.lookup V := Eq.trans rfl rfl

theorem tileSelect_lookup_here_cons {Γ : Ctxt jasminVec} (v : ⟦VReg⟧) (V : Valuation Γ) :
    (Var.here : Var (VReg :: Γ) VReg).lookup (.cons v V) = v := Eq.trans rfl rfl

theorem tileSelect_lookup_there_cons {Γ : Ctxt jasminVec} (w : Var Γ VReg) (v : ⟦VReg⟧)
    (V : Valuation Γ) : (Var.there w : Var (VReg :: Γ) VReg).lookup (.cons v V) = w.lookup V :=
  Eq.trans rfl rfl

/-- Reads the variables of the entry valuation of a block. -/
local macro "vlook" : tactic =>
  `(tactic| repeat (first | rw [tileSelect_lookup_here_cons] | rw [tileSelect_lookup_there_cons]))

/-- The law of a one-operand block at the shape: lane `k` of its value is lane `k` of the
    tile operation on the lanes of its operand, and its operations are vector operations. -/
def UnarySpec (L n : Nat) (o : UnOp) (blk : Blk1) : Prop :=
  (∀ (x : BitVec 512) (k : Fin n),
    vlane L n (blk.denote (.cons x .nil)) k = o.apply (vlane L n x) k) ∧ allVec blk

/-- The law of a two-operand block at the shape. -/
def BinarySpec (L n : Nat) (o : BinOp) (blk : Blk2) : Prop :=
  (∀ (x y : BitVec 512) (k : Fin n),
    vlane L n (blk.denote (.cons x (.cons y .nil))) k =
      o.apply (vlane L n x) (vlane L n y) k) ∧ allVec blk

/-- The block of the constant tile of the value `c`: one broadcast. -/
def constBlk (L c : Nat) : Com jasminVec [] VReg := .var (bcstE L c) (.ret .here)

theorem constBlk_lane (hS : IsShape L n r) (c : Nat) (k : Fin n) :
    vlane L n ((constBlk L c).denote .nil) k = BitVec.ofNat L c := by
  unfold constBlk vlane
  simp only [denote_var, denote_ret, lookup_here, bcstE_denote]
  exact lane_ofLanes _ hS.pos.1 (hS.bound k.isLt)

/-- The block of the static gather by `s`: the index constant and one dword permutation. -/
def gatherBlk (r : Nat) (s : Nat → Nat) : Blk1 :=
  .var (cstE (idxC r s)) (.var (permE (.there .here) .here) (.ret .here))

/-- **The one-operand selection.** A shift by an immediate, an arithmetic shift right and a
    rotation left are one instruction; a rotation right is the rotation left by the
    complement; the broadcast of a lane is a static gather; the reduction is refused. -/
def unSel (L n r : Nat) : UnOp → Option Blk1
  | .shiftImm .shl c => some (.var (shiE L true c .here) (.ret .here))
  | .shiftImm .lshr c => some (.var (shiE L false c .here) (.ret .here))
  | .shiftImm .ashr c => some (.var (sraE L c .here) (.ret .here))
  | .shiftImm .rotl c => some (.var (rolE L c .here) (.ret .here))
  | .shiftImm .rotr c => some (.var (rolE L (L - c % L) .here) (.ret .here))
  | .broadcast l => some (gatherBlk r fun _ => l % n)
  | .reduce => none

/-- **The lane laws of the one-operand selection.** -/
theorem unSel_spec (hS : IsShape L n r) (o : UnOp) (blk : Blk1)
    (h : unSel L n r o = some blk) : UnarySpec L n o blk := by
  have hL := hS.pos.1
  cases o with
  | reduce => cases h
  | broadcast l =>
      cases h
      refine ⟨fun x k => ?_, ⟨_, rfl⟩, ⟨_, rfl⟩, trivial⟩
      unfold gatherBlk vlane
      simp only [denote_var, denote_ret, lookup_here, lookup_there, cstE_denote, permE_denote]
      vlook
      exact lane_gather hS (fun _ => l % n) x k.isLt (Nat.mod_lt _ hS.pos.2.1)
  | shiftImm op c =>
      cases op <;> cases h <;> refine ⟨fun x k => ?_, ⟨_, rfl⟩, trivial⟩ <;>
        unfold vlane <;>
        simp only [denote_var, denote_ret, lookup_here, shiE_denote, sraE_denote, rolE_denote,
          UnOp.apply, tileShiftImmApply, TileImmOp.apply] <;>
        vlook
      · exact (lane_semShImm true c x hL (hS.bound k.isLt)).trans (if_pos rfl)
      · exact (lane_semShImm false c x hL (hS.bound k.isLt)).trans (if_neg (by decide))
      · exact lane_semSra c x hL (hS.bound k.isLt)
      · exact lane_semRol c x hL (hS.bound k.isLt)
      · exact (lane_semRol _ x hL (hS.bound k.isLt)).trans
          (rotateRight_eq_rotateLeft hL _ c).symm

/-- The block of the static shuffle by `idx`: the index constant, the dword permutation of
    each operand and the blend that takes the second operand where the index is at least
    `n`. -/
def shufBlk (n r : Nat) (idx : List Nat) : Blk2 :=
  .var (cstE (idxC r fun k => idx.getD k k % (2 * n) % n))
    (.var (permE (.there .here) .here)
      (.var (permE (.there (.there (.there .here))) (.there .here))
        (.var (blendE (maskC r fun k => decide (¬ idx.getD k k % (2 * n) < n)) .here
            (.there .here))
          (.ret .here))))

theorem shufBlk_lane (hS : IsShape L n r) (idx : List Nat) (x y : BitVec 512) (k : Fin n) :
    vlane L n ((shufBlk n r idx).denote (.cons x (.cons y .nil))) k =
      tileShuffleApply idx (vlane L n x) (vlane L n y) k := by
  have hn : 0 < n := hS.pos.2.1
  unfold shufBlk vlane
  simp only [denote_var, denote_ret, lookup_here, lookup_there, cstE_denote, permE_denote,
    blendE_denote]
  vlook
  rw [lane_blend hS _ _ _ k.isLt, lane_gather hS _ y k.isLt (Nat.mod_lt _ hn),
    lane_gather hS _ x k.isLt (Nat.mod_lt _ hn)]
  unfold tileShuffleApply
  by_cases hx : idx.getD k.val k.val % (2 * n) < n
  · simp only [hx, not_true_eq_false, decide_false, Bool.false_eq_true, if_false, dif_pos]
    show lane L x (idx.getD k.val k.val % (2 * n) % n) =
      lane L x (idx.getD k.val k.val % (2 * n))
    rw [Nat.mod_eq_of_lt hx]
  · have hlt : idx.getD k.val k.val % (2 * n) < 2 * n := Nat.mod_lt _ (by omega)
    simp only [hx, not_false_eq_true, decide_true, if_true, dif_neg]
    show lane L y (idx.getD k.val k.val % (2 * n) % n) =
      lane L y (idx.getD k.val k.val % (2 * n) - n)
    rw [Nat.mod_eq_sub_mod (Nat.le_of_not_lt hx), Nat.mod_eq_of_lt (by omega)]

/-- The block of the unsigned high multiply of sixteen dwords: the even products, the odd
    products of the odd dwords moved to the even positions, the high dwords of the even
    products moved down, and the blend that takes the odd dwords of the odd products. -/
def mulhuBlk : Blk2 :=
  .var (lwE 64 .muludq .here (.there .here))
    (.var (dupE true (.there .here))
      (.var (dupE true (.there (.there (.there .here))))
        (.var (lwE 64 .muludq (.there .here) .here)
          (.var (dupE true (.there (.there (.there .here))))
            (.var (blendE 0xAAAA#16 (.there .here) .here) (.ret .here))))))

theorem mulhuBlk_lane (x y : BitVec 512) {j : Nat} (hj : j < 16) :
    lane 32 (mulhuBlk.denote (.cons x (.cons y .nil))) j =
      mulHiW (lane 32 x j) (lane 32 y j) := by
  unfold mulhuBlk
  simp only [denote_var, denote_ret, lookup_here, lookup_there, lwE_denote, dupE_denote,
    blendE_denote]
  vlook
  have hodd : ∀ (z : BitVec 512) (i : Nat), i < 8 →
      lane 32 (semDup true z) (2 * i) = lane 32 z (2 * i + 1) := by
    intro z i hi
    rw [lane_semDup _ _ (by omega), if_pos rfl]
    congr 1
    omega
  rw [lane_semMerge _ _ _ hj]
  obtain ⟨i, rfl | rfl⟩ : ∃ i, j = 2 * i ∨ j = 2 * i + 1 := ⟨j / 2, by omega⟩
  · have hi : i < 8 := by omega
    have h := prod_lanes (m := .zmm) x y (semDup true y)
      (fun i' hi' => hodd y i' (by have : Mode.zmm.act = 512 := rfl; omega)) i
      (by show 64 * i + 64 ≤ 512; omega)
    simp only [wr] at h
    rw [(maskAAAA i hi).1, if_neg (by decide), hodd _ i hi]
    exact h.2.1
  · have hi : i < 8 := by omega
    have h := prod_lanes (m := .zmm) x y (semDup true y)
      (fun i' hi' => hodd y i' (by have : Mode.zmm.act = 512 := rfl; omega)) i
      (by show 64 * i + 64 ≤ 512; omega)
    simp only [wr] at h
    rw [(maskAAAA i hi).2, if_pos rfl]
    exact h.2.2.2

/-- The dwords `0, 1, 0, 1, …`. -/
def oddOne : BitVec 512 := ofLanes 32 (fun j => BitVec.ofNat 32 (j % 2))

/-- The block of the gather of eight qwords by an index register: the index doubled, its
    low dword copied to both dwords, one added to the odd dword, and the dword
    permutation. -/
def permQBlk : Blk2 :=
  .var (shiE 64 true 1 .here)
    (.var (dupE false .here)
      (.var (cstE oddOne)
        (.var (lwE 32 (.bin .add) (.there .here) .here)
          (.var (permE (.there (.there (.there (.there (.there .here))))) .here)
            (.ret .here)))))

theorem permQ_idx (X : BitVec 64) (e : Nat) (he : e < 2) :
    ((X <<< 1).setWidth 32 + BitVec.ofNat 32 e).toNat % 16 = 2 * (X.toNat % 8) + e := by
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  omega

theorem permQBlk_lane (i a : BitVec 512) {k : Nat} (hk : k < 8) :
    lane 64 (permQBlk.denote (.cons i (.cons a .nil))) k =
      lane 64 a ((lane 64 i k).toNat % 8) := by
  unfold permQBlk
  simp only [denote_var, denote_ret, lookup_here, lookup_there, cstE_denote, permE_denote,
    shiE_denote, dupE_denote, lwE_denote]
  vlook
  have key : ∀ e, e < 2 →
      (lane 32 (semLW 32 (.bin .add) (semDup false (semShImm 64 true 1 i)) oddOne)
        (2 * k + e)).toNat % 16 = 2 * ((lane 64 i k).toNat % 8) + e := by
    intro e he
    have e1 : lane 32 (semDup false (semShImm 64 true 1 i)) (2 * k + e) =
        (lane 64 i k <<< 1).setWidth 32 := by
      rw [lane_semDup _ _ (by omega), if_neg (by decide),
        show 2 * ((2 * k + e) / 2) + 0 = 2 * k by omega, lane32_even,
        lane_semShImm _ _ _ (by omega) (by omega), if_pos rfl]
    have e2 : lane 32 oddOne (2 * k + e) = BitVec.ofNat 32 e := by
      unfold oddOne
      rw [lane_ofLanes _ (by omega) (by omega), show (2 * k + e) % 2 = e by omega]
    rw [lane_semLW _ _ _ (by omega) (by omega), e1, e2]
    exact permQ_idx _ e he
  apply lane64_eq_of_dwords
  · have h0 := key 0 (by omega)
    rw [Nat.add_zero] at h0
    rw [lane_semPerm _ _ _ (by omega), h0, Nat.add_zero]
  · rw [lane_semPerm _ _ _ (by omega), key 1 (by omega)]

/-- **The two-operand selection.** An elementwise operation is one instruction, a blend by
    a static mask one dword blend, a static shuffle two dword permutations and a blend; the
    gather is one dword permutation at dword lanes and `permQBlk` at qword lanes; the
    unsigned high multiply is `mulhuBlk` at dword lanes and refused at qword lanes. -/
def binSel (L n r : Nat) : BinOp → Option Blk2
  | .bin bop => some (.var (lwE L (.bin bop) .here (.there .here)) (.ret .here))
  | .blend mask =>
      some (.var (blendE (maskC r fun k => mask.getD k false) (.there .here) .here)
        (.ret .here))
  | .shuffle idx => some (shufBlk n r idx)
  | .permute =>
      if r = 1 then some (.var (permE (.there .here) .here) (.ret .here)) else some permQBlk
  | .mulhu => if r = 1 then some mulhuBlk else none

/-- **The lane laws of the two-operand selection.** -/
theorem binSel_spec (hS : IsShape L n r) (o : BinOp) (blk : Blk2)
    (h : binSel L n r o = some blk) : BinarySpec L n o blk := by
  have hL := hS.pos.1
  cases o with
  | bin bop =>
      cases h
      refine ⟨fun x y k => ?_, ⟨_, rfl⟩, trivial⟩
      unfold vlane
      simp only [denote_var, denote_ret, lookup_here, lwE_denote, BinOp.apply, tileBinApply]
      vlook
      exact lane_semLW (.bin bop) x y hL (hS.bound k.isLt)
  | blend mask =>
      cases h
      refine ⟨fun x y k => ?_, ⟨_, rfl⟩, trivial⟩
      unfold vlane
      simp only [denote_var, denote_ret, lookup_here, blendE_denote, BinOp.apply,
        tileBlendApply]
      vlook
      exact lane_blend hS _ y x k.isLt
  | shuffle idx =>
      cases h
      exact ⟨shufBlk_lane hS idx, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, trivial⟩
  | permute =>
      rcases hS with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · rw [binSel, if_pos rfl] at h
        cases h
        refine ⟨fun x y k => ?_, ⟨_, rfl⟩, trivial⟩
        unfold vlane
        simp only [denote_var, denote_ret, lookup_here, permE_denote, BinOp.apply,
          tilePermuteApply]
        vlook
        exact lane_semPerm 16 y x k.isLt
      · rw [binSel, if_neg (by decide)] at h
        cases h
        exact ⟨fun x y k => permQBlk_lane x y k.isLt,
          ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, trivial⟩
  | mulhu =>
      rcases hS with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · rw [binSel, if_pos rfl] at h
        cases h
        exact ⟨fun x y k => mulhuBlk_lane x y k.isLt,
          ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, trivial⟩
      · rw [binSel, if_neg (by decide)] at h
        cases h

end Shape

/-! ## 4. The targets -/

theorem vlane_packAt_dword (a : Fin 16 → BitVec 32) :
    vlane 32 16 (packAt 16 32 (vof 32 16) (.tile 16 32) a) = a := by
  funext k
  show vlane 32 16 (packReg 16 32 (vof 32 16) 16 32 a) k = a k
  rw [packReg_self, vlane_vof isShape_dword]

theorem vlane_packAt_qword (a : Fin 8 → BitVec 64) :
    vlane 64 8 (packAt 8 64 (vof 64 8) (.tile 8 64) a) = a := by
  funext k
  show vlane 64 8 (packReg 8 64 (vof 64 8) 8 64 a) k = a k
  rw [packReg_self, vlane_vof isShape_qword]

/-- **Sixteen 32-bit lanes in a ZMM register, on `x86vec`.** The blocks of `unSel` and
    `binSel` at dword lanes. -/
def selD : TileTarget jasminVec where
  laneCount := 16
  laneBits := 32
  ty := regOf
  pack := packAt 16 32 (vof 32 16)
  lane := vlane 32 16
  lane_pack := fun x k => congrFun (vlane_packAt_dword x) k
  lane_inj := fun x y h => vlane_inj isShape_dword x y h
  const? := fun c => some (constBlk 32 c)
  unary? := unSel 32 16 1
  binary? := binSel 32 16 1
  const_lane := by
    intro c blk h k
    cases h
    exact constBlk_lane isShape_dword c k
  unary_lane := by
    intro o blk h a k
    exact ((unSel_spec isShape_dword o blk h).1 _ k).trans (by rw [vlane_packAt_dword])
  binary_lane := by
    intro o blk h a b k
    exact ((binSel_spec isShape_dword o blk h).1 _ _ k).trans
      (by rw [vlane_packAt_dword, vlane_packAt_dword])

/-- **Eight 64-bit lanes in a ZMM register, on `x86vec`.** The blocks of `unSel` and
    `binSel` at qword lanes. -/
def selQ : TileTarget jasminVec where
  laneCount := 8
  laneBits := 64
  ty := regOf
  pack := packAt 8 64 (vof 64 8)
  lane := vlane 64 8
  lane_pack := fun x k => congrFun (vlane_packAt_qword x) k
  lane_inj := fun x y h => vlane_inj isShape_qword x y h
  const? := fun c => some (constBlk 64 c)
  unary? := unSel 64 8 2
  binary? := binSel 64 8 2
  const_lane := by
    intro c blk h k
    cases h
    exact constBlk_lane isShape_qword c k
  unary_lane := by
    intro o blk h a k
    exact ((unSel_spec isShape_qword o blk h).1 _ k).trans (by rw [vlane_packAt_qword])
  binary_lane := by
    intro o blk h a b k
    exact ((binSel_spec isShape_qword o blk h).1 _ _ k).trans
      (by rw [vlane_packAt_qword, vlane_packAt_qword])

/-! ## 5. Leakage and certificates -/

/-- The coproduct of `jasminVec` and `tileDialect`: the source dialect of the selection. -/
abbrev tileVec : Dialect := scalarTile jasminVec

instance : DialectSignature tileVec := instDialectSignatureScalarTile jasminVec
instance : HasWord64 tileVec := instHasWord64ScalarTile jasminVec
instance : HasBoolBit tileVec := instHasBoolBitScalarTile jasminVec
instance : CallDenote tileVec := instCallDenoteScalarTile jasminVec

/-- The blocks of `selD` emit no event, over every leakage model of `jasminDialect`. -/
theorem selD_quiet (M : LeakModel jasminDialect) : selD.Quiet (jasminVecLeak M) where
  const := by
    intro c blk h W
    cases h
    exact ctLeak_allVec M (constBlk 32 c) ⟨⟨_, rfl⟩, trivial⟩ W
  unary := fun o blk h W => ctLeak_allVec M _ (unSel_spec isShape_dword o blk h).2 W
  binary := fun o blk h W => ctLeak_allVec M _ (binSel_spec isShape_dword o blk h).2 W

/-- The blocks of `selQ` emit no event, over every leakage model of `jasminDialect`. -/
theorem selQ_quiet (M : LeakModel jasminDialect) : selQ.Quiet (jasminVecLeak M) where
  const := by
    intro c blk h W
    cases h
    exact ctLeak_allVec M (constBlk 64 c) ⟨⟨_, rfl⟩, trivial⟩ W
  unary := fun o blk h W => ctLeak_allVec M _ (unSel_spec isShape_qword o blk h).2 W
  binary := fun o blk h W => ctLeak_allVec M _ (binSel_spec isShape_qword o blk h).2 W

open PassChain in
/-- **The certificate of selection at sixteen 32-bit lanes.** -/
def selDCert (fuel : Nat) (Γ : Ctxt (scalarTile jasminVec))
    (ts : List (scalarTile jasminVec).Ty) :
    StepCert (legalise selD (Γ := Γ) (ts := ts)) (scalarTileSem jasminVec fuel Γ ts)
      (targetSem jasminVec fuel (Γ.map (legalTy selD)) (ts.map (legalTy selD))) :=
  tileLegalCert selD fuel Γ ts

open PassChain in
/-- **The certificate of selection at eight 64-bit lanes.** -/
def selQCert (fuel : Nat) (Γ : Ctxt (scalarTile jasminVec))
    (ts : List (scalarTile jasminVec).Ty) :
    StepCert (legalise selQ (Γ := Γ) (ts := ts)) (scalarTileSem jasminVec fuel Γ ts)
      (targetSem jasminVec fuel (Γ.map (legalTy selQ)) (ts.map (legalTy selQ))) :=
  tileLegalCert selQ fuel Γ ts

/-- **Selection at sixteen 32-bit lanes preserves runs and events.** -/
theorem selD_leakRun (M : LeakModel jasminDialect) (fuel : Nat)
    {Γ : Ctxt (scalarTile jasminVec)} {ts : List (scalarTile jasminVec).Ty}
    (p : NFProg (scalarTile jasminVec) Γ ts)
    (q : NFProg jasminVec (Γ.map (legalTy selD)) (ts.map (legalTy selD)))
    (h : legalise selD p = some q) (V : Valuation Γ) :
    NFProg.leakRun (jasminVecLeak M) fuel q (packVal selD V) =
      (scalarTileLeakRun jasminVec (instDialectDenoteMOptionOfPure jasminVec) (jasminVecLeak M)
        fuel p V).map fun r => (packOuts selD r.1, r.2) :=
  tileLegal_leakRun (selD_quiet M) fuel p q h V

/-- **Selection at eight 64-bit lanes preserves runs and events.** -/
theorem selQ_leakRun (M : LeakModel jasminDialect) (fuel : Nat)
    {Γ : Ctxt (scalarTile jasminVec)} {ts : List (scalarTile jasminVec).Ty}
    (p : NFProg (scalarTile jasminVec) Γ ts)
    (q : NFProg jasminVec (Γ.map (legalTy selQ)) (ts.map (legalTy selQ)))
    (h : legalise selQ p = some q) (V : Valuation Γ) :
    NFProg.leakRun (jasminVecLeak M) fuel q (packVal selQ V) =
      (scalarTileLeakRun jasminVec (instDialectDenoteMOptionOfPure jasminVec) (jasminVecLeak M)
        fuel p V).map fun r => (packOuts selQ r.1, r.2) :=
  tileLegal_leakRun (selQ_quiet M) fuel p q h V

/-! ## 6. The gate table -/

/-- The operations accepted at both shapes: every shift and rotation by an immediate, the
    broadcast of a lane, every elementwise operation, the blend, the static shuffle and
    the gather; and the unsigned high multiply at dword lanes. -/
theorem sel_accepts (op : TileImmOp) (c l : Nat) (bop : JasminBinOp) (idx : List Nat)
    (mask : List Bool) :
    (selQ.unary? (.shiftImm op c)).isSome = true ∧
      (selD.unary? (.shiftImm op c)).isSome = true ∧
      (selQ.unary? (.broadcast l)).isSome = true ∧ (selD.unary? (.broadcast l)).isSome = true ∧
      (selQ.binary? (.bin bop)).isSome = true ∧ (selD.binary? (.bin bop)).isSome = true ∧
      (selQ.binary? (.blend mask)).isSome = true ∧ (selD.binary? (.blend mask)).isSome = true ∧
      (selQ.binary? (.shuffle idx)).isSome = true ∧
      (selD.binary? (.shuffle idx)).isSome = true ∧
      (selQ.binary? .permute).isSome = true ∧ (selD.binary? .permute).isSome = true ∧
      (selD.binary? .mulhu).isSome = true := by
  cases op <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The operations refused: the reduction at both shapes and the unsigned high multiply at
    qword lanes. -/
theorem sel_refused :
    selQ.unary? .reduce = none ∧ selD.unary? .reduce = none ∧ selQ.binary? .mulhu = none :=
  ⟨rfl, rfl, rfl⟩

/-- **One instruction per shift and rotation.** The arithmetic shift right and the two
    rotations by an immediate are single operations of `x86vec` at both shapes. -/
theorem sel_single (c : Nat) :
    selQ.unary? (.shiftImm .ashr c) = some (.var (sraE 64 c .here) (.ret .here)) ∧
      selD.unary? (.shiftImm .ashr c) = some (.var (sraE 32 c .here) (.ret .here)) ∧
      selQ.unary? (.shiftImm .rotl c) = some (.var (rolE 64 c .here) (.ret .here)) ∧
      selD.unary? (.shiftImm .rotl c) = some (.var (rolE 32 c .here) (.ret .here)) ∧
      selQ.unary? (.shiftImm .rotr c) =
        some (.var (rolE 64 (64 - c % 64) .here) (.ret .here)) ∧
      selD.unary? (.shiftImm .rotr c) =
        some (.var (rolE 32 (32 - c % 32) .here) (.ret .here)) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Every one-operand operation `zmmQ` accepts is accepted by `selQ`. -/
theorem selQ_unary_of_zmmQ (o : UnOp) (h : (zmmQ.unary? o).isSome = true) :
    (selQ.unary? o).isSome = true := by
  cases o with
  | reduce => exact (Bool.false_ne_true h).elim
  | broadcast l => rfl
  | shiftImm op c => cases op <;> rfl

/-- Every two-operand operation `zmmQ` accepts is accepted by `selQ`. -/
theorem selQ_binary_of_zmmQ (o : BinOp) (h : (zmmQ.binary? o).isSome = true) :
    (selQ.binary? o).isSome = true := by
  cases o with
  | mulhu => exact (Bool.false_ne_true h).elim
  | bin bop => rfl
  | blend mask => rfl
  | shuffle idx => rfl
  | permute => rfl

/-- Every one-operand operation `zmmD` accepts is accepted by `selD`. -/
theorem selD_unary_of_zmmD (o : UnOp) (h : (zmmD.unary? o).isSome = true) :
    (selD.unary? o).isSome = true := by
  cases o with
  | reduce => exact (Bool.false_ne_true h).elim
  | broadcast l => rfl
  | shiftImm op c => cases op <;> rfl

/-- Every two-operand operation is accepted by `selD`. -/
theorem selD_binary (o : BinOp) : (selD.binary? o).isSome = true := by
  cases o <;> rfl

end CatCrypt.Crypto.SecureCompilation.VIR.TileSelectX86
