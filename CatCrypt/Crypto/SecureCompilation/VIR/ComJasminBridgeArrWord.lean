/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeArrIdx

/-!
# `Com ↔ Jasmin` bridge extension: `u64` word arrays

A JasminPrint stack array `stackArr 64 m` holds `m` limbs of 64 bits. The mirror
holds the same array as `Varr (8 * m)` bytes, and reads and writes a `U64` cell
at a scaled index as the 8 bytes at offset `8 * i`, little-endian
(`JArrayMirror.getWord` / `setWord`, the mirror of `WArray.get` / `set`).

`encodeWordArr m a` is the limb array of the byte array `a`; `WordArrCorr` and
`StateCorrArrW` are the word-array analogues of `ComJasminBridgeArr.ArrCorr` and
`StateCorrArr`.

## Contents

* `readLE_writeLE_same` / `readLE_writeLE_disjoint` — the little-endian read of a
  little-endian write.
* `encodeWordArr`, `encodeWordArr_writeLE` — the limb view, and a limb write as
  `stackSet`.
* `getWord_u64` / `setWord_u64` — the mirror scaled `U64` access at an in-range
  limb index.
* `semPexpr_pget_u64`, `cassgn_pget_u64_simulates`, `cassgn_pget_u64_endToEnd` —
  the register-index limb read `dst := arr[idx]`.
* `mirror_laset_u64_post`, `cassgn_laset_u64_simulates`, `cassgn_laset_u64_endToEnd`
  — the register-index limb write `arr[idx] := src`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeArrWord

open CatCrypt.Crypto.Jasmin.CoqSemMirror
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.StateBijection
open CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeFull
open CatCrypt.Crypto.SecureCompilation.VIR.OperandReadCorr
open CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeArrIdx
open JArrayMirror

variable {SyscallState Mem : Type} [MemModel Mem]

/-! ## §1. Little-endian reads of little-endian writes -/

/-- The byte at `q` after a write of `k` bytes at `p`. -/
theorem getD_writeLE {n : Nat} (a : JArrayMirror n) (p k v q : Nat) :
    getD (writeLE a p k v) q
      = if p ≤ q ∧ q < p + k ∧ q < n then BitVec.ofNat 8 (v / 256 ^ (q - p)) else getD a q := by
  unfold getD writeLE
  by_cases hq : q < n
  · simp only [dite_eq_left hq]
    by_cases hr : p ≤ q ∧ q < p + k
    · rw [ite_eq_left hr, ite_eq_left ⟨hr.1, hr.2, hq⟩]
    · rw [ite_eq_right hr, ite_eq_right (fun h => hr ⟨h.1, h.2.1⟩)]
  · simp [hq]

/-- Two arrays with the same bytes at `q, …, q + c - 1` have the same
    little-endian read there. -/
theorem readLE_congr {n : Nat} (a b : JArrayMirror n) :
    ∀ (c q : Nat), (∀ j < c, getD a (q + j) = getD b (q + j)) → readLE a q c = readLE b q c
  | 0, _, _ => rfl
  | c + 1, q, h => by
    simp only [readLE]
    have h0 := h 0 (by omega)
    simp only [Nat.add_zero] at h0
    rw [h0, readLE_congr a b c (q + 1) (fun j hj => by
      have := h (j + 1) (by omega)
      rwa [show q + (j + 1) = q + 1 + j by omega] at this)]

/-- A write of `k` bytes at `p` does not change a read of `c` bytes at `q` whose
    range is disjoint from it. -/
theorem readLE_writeLE_disjoint {n : Nat} (a : JArrayMirror n) (p k v q c : Nat)
    (h : q + c ≤ p ∨ p + k ≤ q) :
    readLE (writeLE a p k v) q c = readLE a q c := by
  apply readLE_congr
  intro j hj
  rw [getD_writeLE, ite_eq_right (by omega)]

/-- A read of the `k` bytes a little-endian write of `v` placed at `p` returns
    `v mod 256 ^ k`, when the bytes lie in the array. -/
theorem readLE_writeLE_same {n : Nat} (a : JArrayMirror n) :
    ∀ (k p v : Nat), p + k ≤ n → readLE (writeLE a p k v) p k = v % 256 ^ k
  | 0, _, v, _ => by simp [readLE, Nat.mod_one]
  | k + 1, p, v, hk => by
    simp only [readLE]
    have hshift : readLE (writeLE a p (k + 1) v) (p + 1) k
        = readLE (writeLE a (p + 1) k (v / 256)) (p + 1) k := by
      apply readLE_congr
      intro j hj
      rw [getD_writeLE, getD_writeLE, ite_eq_left (by omega), ite_eq_left (by omega),
        show p + 1 + j - p = j + 1 by omega, show p + 1 + j - (p + 1) = j by omega,
        Nat.pow_succ', Nat.div_div_eq_div_mul]
    rw [hshift, readLE_writeLE_same a k (p + 1) (v / 256) (by omega), getD_writeLE,
      ite_eq_left (by omega), Nat.sub_self, Nat.pow_zero, Nat.div_one, BitVec.toNat_ofNat,
      show (2 : Nat) ^ 8 = 256 from rfl, show (256 : Nat) ^ (k + 1) = 256 * 256 ^ k from Nat.pow_succ',
      Nat.mod_mul]

/-! ## §2. The limb view -/

/-- The `m` little-endian 64-bit limbs of an `8 * m`-byte array. -/
def encodeWordArr (m : Nat) (a : JArrayMirror (8 * m)) : Fin m → BitVec 64 :=
  fun k => BitVec.ofNat 64 (readLE a (8 * k.val) 8)

/-- Writing the little-endian bytes of `v` at the limb offset `8 * i` is
    `stackSet` of `v` at limb `i`. -/
theorem encodeWordArr_writeLE (m : Nat) (a : JArrayMirror (8 * m)) (i : Nat) (hi : i < m)
    (v : BitVec 64) :
    encodeWordArr m (writeLE a (8 * i) 8 v.toNat) = stackSet (encodeWordArr m a) i v := by
  cases m with
  | zero => omega
  | succ m' =>
    funext k
    simp only [stackSet, Nat.mod_eq_of_lt hi]
    by_cases hk : k = ⟨i, hi⟩
    · subst hk
      rw [ite_eq_left rfl]
      show BitVec.ofNat 64 (readLE (writeLE a (8 * i) 8 v.toNat) (8 * i) 8) = v
      rw [readLE_writeLE_same a 8 (8 * i) v.toNat (by omega)]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (show v.toNat < 256 ^ 8 from v.isLt),
        Nat.mod_eq_of_lt v.isLt]
    · rw [ite_eq_right hk]
      have hne : k.val ≠ i := fun e => hk (Fin.ext e)
      show BitVec.ofNat 64 (readLE (writeLE a (8 * i) 8 v.toNat) (8 * k.val) 8)
        = BitVec.ofNat 64 (readLE a (8 * k.val) 8)
      rw [readLE_writeLE_disjoint a (8 * i) 8 v.toNat (8 * k.val) 8 (by omega)]

/-! ## §3. The mirror scaled `U64` access -/

/-- A scaled `U64` access at limb index `i < m` of an `8 * m`-byte array is in
    bounds and aligned. -/
theorem accessOk_u64 (m : Nat) (al : Aligned) (i : Nat) (hi : i < m) :
    AccessOk (8 * m) al .U64 ((i : Int) * scale .AAscale .U64) := by
  have hp : ((i : Int) * scale .AAscale .U64) = ((8 * i : Nat) : Int) := by
    simp [scale, WSize.bytes]; ring
  rw [hp]
  refine ⟨Int.natCast_nonneg _, ?_, ?_⟩
  · simp only [Int.toNat_natCast, WSize.bytes]; omega
  · intro _; simp only [Int.toNat_natCast, WSize.bytes]; omega

/-- The mirror scaled `U64` read at limb index `i < m` is limb `i` of the limb view. -/
theorem getWord_u64 (m : Nat) (a : JArrayMirror (8 * m)) (al : Aligned) (i : Nat) (hi : i < m) :
    getWord a al .AAscale .U64 (i : Int) = .ok (encodeWordArr m a ⟨i, hi⟩) := by
  unfold getWord
  simp only
  rw [ite_eq_left (accessOk_u64 m al i hi)]
  have hp : ((i : Int) * scale .AAscale .U64).toNat = 8 * i := by
    simp [scale, WSize.bytes]; omega
  rw [hp]
  rfl

/-- The mirror scaled `U64` write at limb index `i < m` writes the little-endian
    bytes of `v` at byte offset `8 * i`. -/
theorem setWord_u64 (m : Nat) (a : JArrayMirror (8 * m)) (al : Aligned) (i : Nat) (hi : i < m)
    (v : BitVec 64) :
    setWord a al .AAscale .U64 (i : Int) v = .ok (writeLE a (8 * i) 8 v.toNat) := by
  unfold setWord
  simp only
  rw [ite_eq_left (accessOk_u64 m al i hi)]
  have hp : ((i : Int) * scale .AAscale .U64).toNat = 8 * i := by
    simp [scale, WSize.bytes]; omega
  rw [hp]
  rfl

/-! ## §4. The word-array correspondence -/

/-- A JasminPrint dynamic value `d` and a mirror value `v` correspond as an
    `m`-limb array: `v` is an `8 * m`-byte array whose limb view `d` holds. -/
def WordArrCorr (m : Nat) (d : DynVal) (v : Value) : Prop :=
  ∃ a : JArrayMirror (8 * m), v = .Varr (8 * m) a ∧ d = ⟨.stackArr 64 m, encodeWordArr m a⟩

/-- The word-array frame correspondence: each `(r, m)` in `frame` is an `m`-limb
    array at `r` on both sides. -/
def StateCorrArrW (frame : List (Var × Nat)) (st : Store) (vm : Vm) : Prop :=
  ∀ q ∈ frame, WordArrCorr q.2 (st q.1.vname) (vm.get q.1)

/-- Under `StateCorrArrW`, a word array `x` holding the byte array `a` has the
    JasminPrint limb array `encodeWordArr m a` at `x.vname`. -/
theorem store_get_wordArr (frame : List (Var × Nat)) (st : Store) (vm : Vm)
    (x : Var) (m : Nat) (a : JArrayMirror (8 * m))
    (hcorr : StateCorrArrW frame st vm) (hmem : (x, m) ∈ frame)
    (hread : vm.get x = .Varr (8 * m) a) :
    Store.get st x.vname (.stackArr 64 m) = encodeWordArr m a := by
  obtain ⟨a', hv, hd⟩ := hcorr (x, m) hmem
  rw [hread] at hv
  injection hv with _ ha
  subst ha
  unfold Store.get
  rw [hd]
  simp

/-! ## §5. The limb read `dst := arr[idx]` -/

/-- The mirror `semPexpr` of `Pget al AAscale U64 arr (idxExpr idx)`, when `arr`
    reads the `8 * m`-byte array `a` and `idx` reads `Vword U64 i` with
    `i.toNat < m`, is limb `i.toNat` of the limb view. -/
theorem semPexpr_pget_u64
    (gd : GlobDecls) (opS : OpSem) (s : Estate SyscallState Mem)
    (arr idx : VarI) (m : Nat) (a : JArrayMirror (8 * m)) (al : Aligned)
    (i : BitVec WSize.U64.bits)
    (hagree : IntOfWordAgrees opS)
    (hread : (s.evm).get arr.v_var = .Varr (8 * m) a)
    (hidx : (s.evm).get idx.v_var = .Vword .U64 i)
    (hin : i.toNat < m) :
    semPexpr (Mem := Mem) true gd opS s (.Pget al .AAscale .U64 (mkLvar arr) (idxExpr idx))
      = .ok (.Vword .U64 (encodeWordArr m a ⟨i.toNat, hin⟩)) := by
  have hgv : getGvar true gd s.evm (mkLvar arr) = .ok (.Varr (8 * m) a) := by
    unfold getGvar
    rw [show (mkLvar arr).isLvar = true from rfl]
    simp only [ite_true]
    show getVar true s.evm (mkLvar arr).gv.v_var = _
    unfold getVar
    rw [show (mkLvar arr).gv.v_var = arr.v_var from rfl, hread]
    rfl
  show (do
      let vr ← getGvar true gd s.evm (mkLvar arr)
      match vr with
      | .Varr n a =>
          let vi ← semPexpr (Mem := Mem) true gd opS s (idxExpr idx)
          let i ← vi.toInt
          let w ← JArrayMirror.getWord a al .AAscale .U64 i
          (.ok (.Vword .U64 w) : JResult Value)
      | _ => .typeError) = _
  rw [hgv]
  show (do
      let vi ← semPexpr (Mem := Mem) true gd opS s (idxExpr idx)
      let i ← vi.toInt
      let w ← JArrayMirror.getWord a al .AAscale .U64 i
      (.ok (.Vword .U64 w) : JResult Value)) = _
  rw [semPexpr_idxExpr gd opS s idx i hagree hidx]
  show (do
      let w ← JArrayMirror.getWord a al .AAscale .U64 (i.toNat : Int)
      (.ok (.Vword .U64 w) : JResult Value)) = _
  rw [getWord_u64 m a al i.toNat hin]
  rfl

/-- **Simulation for the limb read.** For `dst := arr[idx]` with `dst` a `u64`
    register frame-distinct from `names`, `arr` an `m`-limb array corresponding
    on `frameW`, and `idx ∈ names` a `u64` register holding an in-range limb
    index: the mirror `Cassgn` lands `dst := limb`, the post-state corresponds to
    `Store.set st dst.vname limb`, and the JasminPrint `stackLoad` read
    `stackGet (Store.get st arr.vname (stackArr 64 m)) (idx.toNat)` is that limb. -/
theorem cassgn_pget_u64_simulates
    (gd : GlobDecls) (opS : OpSem) (tag : AssgnTag)
    (dst arr idx : VarI) (m : Nat) (a : JArrayMirror (8 * m)) (al : Aligned)
    (i : BitVec WSize.U64.bits)
    (s : Estate SyscallState Mem) (st : Store) (names : List Var) (frameW : List (Var × Nat))
    (hagree : IntOfWordAgrees opS)
    (hdst : dst.v_var.vtype = .aword .U64)
    (hread : (s.evm).get arr.v_var = .Varr (8 * m) a)
    (hW : StateCorrArrW frameW st (s.evm)) (hWm : (arr.v_var, m) ∈ frameW)
    (him : idx.v_var ∈ names)
    (hidx : (s.evm).get idx.v_var = .Vword .U64 i)
    (hin : i.toNat < m)
    (hdistinct : ∀ r' ∈ names, r' ≠ dst.v_var ∧ r'.vname ≠ dst.v_var.vname)
    (hcorr : StateCorrReg names st (s.evm)) :
    OpSemCoverage.assignExec (Mem := Mem) opS gd (.Lvar dst) (.aword .U64)
        (.Pget al .AAscale .U64 (mkLvar arr) (idxExpr idx)) s
      = .ok (s.withVm ((s.evm).set dst.v_var (.Vword .U64 (encodeWordArr m a ⟨i.toNat, hin⟩))))
    ∧ StateCorrReg (dst.v_var :: names)
        (Store.set st dst.v_var.vname (t := .reg WSize.U64.bits) (encodeWordArr m a ⟨i.toNat, hin⟩))
        ((s.evm).set dst.v_var (.Vword .U64 (encodeWordArr m a ⟨i.toNat, hin⟩)))
    ∧ stackGet (Store.get st arr.v_var.vname (.stackArr 64 m))
        (BitVec.toNat (Store.get st idx.v_var.vname (.reg 64)))
      = encodeWordArr m a ⟨i.toNat, hin⟩ := by
  have hrhs := semPexpr_pget_u64 gd opS s arr idx m a al i hagree hread hidx hin
  obtain ⟨hrun, hcorr'⟩ := cassgn_regArith_simulates (SyscallState := SyscallState) (Mem := Mem)
    gd opS dst .U64 tag (.Pget al .AAscale .U64 (mkLvar arr) (idxExpr idx))
    (encodeWordArr m a ⟨i.toNat, hin⟩) s st names hdst hrhs hdistinct hcorr
  refine ⟨hrun, hcorr', ?_⟩
  have hi : Store.get st idx.v_var.vname (.reg WSize.U64.bits) = i :=
    (pvar_read_corr (Mem := Mem) gd opS s st names idx .U64 i hcorr him hidx).2
  have hi' : Store.get st idx.v_var.vname (.reg 64) = i := hi
  rw [store_get_wordArr frameW st s.evm arr.v_var m a hW hWm hread, hi']
  exact stackGet_id _ ⟨i.toNat, hin⟩

/-- **End-to-end limb read.** Under the hypotheses of `cassgn_pget_u64_simulates`,
    the `Cassgn` witnesses the relational step `SemIr`, and the post-state
    corresponds to `Store.set st dst.vname limb`. -/
theorem cassgn_pget_u64_endToEnd
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog) (fuel : Nat) (tag : AssgnTag)
    (dst arr idx : VarI) (m : Nat) (a : JArrayMirror (8 * m)) (al : Aligned)
    (i : BitVec WSize.U64.bits)
    (s : Estate SyscallState Mem) (st : Store) (names : List Var) (frameW : List (Var × Nat))
    (hagree : IntOfWordAgrees opS)
    (hdst : dst.v_var.vtype = .aword .U64)
    (hread : (s.evm).get arr.v_var = .Varr (8 * m) a)
    (hW : StateCorrArrW frameW st (s.evm)) (hWm : (arr.v_var, m) ∈ frameW)
    (him : idx.v_var ∈ names)
    (hidx : (s.evm).get idx.v_var = .Vword .U64 i)
    (hin : i.toNat < m)
    (hdistinct : ∀ r' ∈ names, r' ≠ dst.v_var ∧ r'.vname ≠ dst.v_var.vname)
    (hcorr : StateCorrReg names st (s.evm)) :
    SemIr (Mem := Mem) aS opS gd prog s
        (.Cassgn (.Lvar dst) tag (.aword .U64) (.Pget al .AAscale .U64 (mkLvar arr) (idxExpr idx)))
        (s.withVm ((s.evm).set dst.v_var (.Vword .U64 (encodeWordArr m a ⟨i.toNat, hin⟩))))
    ∧ StateCorrReg (dst.v_var :: names)
        (Store.set st dst.v_var.vname (t := .reg WSize.U64.bits) (encodeWordArr m a ⟨i.toNat, hin⟩))
        ((s.evm).set dst.v_var (.Vword .U64 (encodeWordArr m a ⟨i.toNat, hin⟩))) := by
  obtain ⟨hrun, hcorr', _⟩ :=
    cassgn_pget_u64_simulates gd opS tag dst arr idx m a al i s st names frameW
      hagree hdst hread hW hWm him hidx hin hdistinct hcorr
  refine ⟨?_, hcorr'⟩
  apply ExecAdequacy.execInstrR_sound (n := fuel + 1) aS opS gd prog
  rw [OpSemCoverage.execInstrR_Cassgn_eq]
  exact hrun

/-! ## §6. The limb write `arr[idx] := src` -/

/-- **Mirror limb-write post-state.** For `arr[idx] := src` with `arr : aarr ws (8 * m)`
    reading the byte array `a`, `idx` holding `Vword U64 i` with `i.toNat < m`, and
    `src` holding `Vword U64 v`, the mirror assignment writes the little-endian
    bytes of `v` at byte offset `8 * i.toNat`. -/
theorem mirror_laset_u64_post
    (gd : GlobDecls) (opS : OpSem)
    (arr idx src : VarI) (ws : WSize) (m : Nat) (a : JArrayMirror (8 * m)) (al : Aligned)
    (i : BitVec WSize.U64.bits) (v : BitVec WSize.U64.bits)
    (s : Estate SyscallState Mem)
    (hagree : IntOfWordAgrees opS)
    (harrTy : arr.v_var.vtype = .aarr ws (8 * m))
    (hread : (s.evm).get arr.v_var = .Varr (8 * m) a)
    (hidx : (s.evm).get idx.v_var = .Vword .U64 i)
    (hsrc : (s.evm).get src.v_var = .Vword .U64 v)
    (hin : i.toNat < m) :
    OpSemCoverage.assignExec (Mem := Mem) opS gd (.Laset al .AAscale .U64 arr (idxExpr idx))
        (.aword .U64) (.Pvar (mkLvar src)) s
      = .ok (s.withVm ((s.evm).set arr.v_var
          (.Varr (8 * m) (writeLE a (8 * i.toNat) 8 v.toNat)))) := by
  unfold OpSemCoverage.assignExec
  rw [semPexpr_pvar_vword gd opS s src .U64 v hsrc]
  show (do
      let v' ← truncateVal (.cword .U64) (.Vword .U64 v)
      writeLval (Mem := Mem) true gd opS (.Laset al .AAscale .U64 arr (idxExpr idx)) v' s) = _
  rw [truncateVal_aword_self]
  have hgv : getVar true s.evm arr.v_var = .ok (.Varr (8 * m) a) := by
    unfold getVar; rw [hread]; rfl
  have hw : Value.toWord .U64 (.Vword .U64 v) = .ok v := by
    show truncateWord .U64 (sz' := .U64) v = _
    unfold truncateWord
    simp only [le_refl, ite_true]
    congr 1
    apply BitVec.eq_of_toNat_eq; simp
  show (do
      let valR ← getVar true s.evm arr.v_var
      match valR with
      | .Varr n a =>
          let iV ← semPexpr (Mem := Mem) true gd opS s (idxExpr idx)
          let i ← iV.toInt
          let wv ← Value.toWord .U64 (.Vword .U64 v)
          let a' ← JArrayMirror.setWord a al .AAscale .U64 i wv
          writeVar (Mem := Mem) true arr (.Varr n a') s
      | _ => .typeError) = _
  rw [hgv]
  show (do
      let iV ← semPexpr (Mem := Mem) true gd opS s (idxExpr idx)
      let i ← iV.toInt
      let wv ← Value.toWord .U64 (.Vword .U64 v)
      let a' ← JArrayMirror.setWord a al .AAscale .U64 i wv
      writeVar (Mem := Mem) true arr (.Varr (8 * m) a') s) = _
  rw [semPexpr_idxExpr gd opS s idx i hagree hidx]
  show (do
      let wv ← Value.toWord .U64 (.Vword .U64 v)
      let a' ← JArrayMirror.setWord a al .AAscale .U64 (i.toNat : Int) wv
      writeVar (Mem := Mem) true arr (.Varr (8 * m) a') s) = _
  rw [hw]
  show (do
      let a' ← JArrayMirror.setWord a al .AAscale .U64 (i.toNat : Int) v
      writeVar (Mem := Mem) true arr (.Varr (8 * m) a') s) = _
  rw [setWord_u64 m a al i.toNat hin v]
  show writeVar (Mem := Mem) true arr (.Varr (8 * m) (writeLE a (8 * i.toNat) 8 v.toNat)) s = _
  unfold writeVar setVar
  rw [harrTy]
  simp [DB, Value.isDefined, truncatable, Value.typeOf]

/-- **Word-array write preservation.** Writing `arr := Varr (8 * m) a'` on the
    mirror and its limb view at `arr.vname` in the store extends `StateCorrArrW`
    to `(arr, m) :: frame`, for a frame of other variables with other names. -/
theorem stateCorrArrW_write (arr : Var) (m : Nat) (a' : JArrayMirror (8 * m))
    (st : Store) (vm : Vm) (frame : List (Var × Nat))
    (hd : ∀ q ∈ frame, q.1 ≠ arr ∧ q.1.vname ≠ arr.vname)
    (h : StateCorrArrW frame st vm) :
    StateCorrArrW ((arr, m) :: frame)
      (Store.set st arr.vname (t := .stackArr 64 m) (encodeWordArr m a'))
      (vm.set arr (.Varr (8 * m) a')) := by
  intro q hq
  rcases List.mem_cons.mp hq with h' | h'
  · subst h'
    refine ⟨a', by simp [Vm.get, Vm.set], by simp [Store.set]⟩
  · obtain ⟨hne, hname⟩ := hd q h'
    have hm : (vm.set arr (.Varr (8 * m) a')).get q.1 = vm.get q.1 := by
      simp [Vm.get, Vm.set, hne]
    have hs : Store.set st arr.vname (t := .stackArr 64 m) (encodeWordArr m a') q.1.vname
        = st q.1.vname := by simp [Store.set, hname]
    show WordArrCorr q.2 (Store.set st arr.vname (t := .stackArr 64 m) (encodeWordArr m a') q.1.vname)
      ((vm.set arr (.Varr (8 * m) a')).get q.1)
    rw [hm, hs]
    exact h q h'

/-- The paired word-array write at `arr` leaves `StateCorrReg` on a register
    frame of other variables with other names unchanged. -/
theorem stateCorrReg_write_wordArr (arr : Var) (m : Nat) (a' : JArrayMirror (8 * m))
    (st : Store) (vm : Vm) (names : List Var)
    (hd : ∀ r ∈ names, r ≠ arr ∧ r.vname ≠ arr.vname)
    (h : StateCorrReg names st vm) :
    StateCorrReg names
      (Store.set st arr.vname (t := .stackArr 64 m) (encodeWordArr m a'))
      (vm.set arr (.Varr (8 * m) a')) := by
  intro r hr
  obtain ⟨hne, hname⟩ := hd r hr
  show Store.set st arr.vname (t := .stackArr 64 m) (encodeWordArr m a') r.vname
    = encodeRegVal ((vm.set arr (.Varr (8 * m) a')).get r)
  have hm : (vm.set arr (.Varr (8 * m) a')).get r = vm.get r := by simp [Vm.get, Vm.set, hne]
  have hs : Store.set st arr.vname (t := .stackArr 64 m) (encodeWordArr m a') r.vname
      = st r.vname := by simp [Store.set, hname]
  rw [hm, hs]
  exact h r hr

/-- **Simulation for the limb write.** For `arr[idx] := src` under the hypotheses
    of `mirror_laset_u64_post`, with `arr` an `m`-limb array corresponding on
    `(arr, m) :: frameRest`, `idx, src ∈ regNames`, and both frames of other
    variables with other names than `arr`:

    * the mirror run writes `Varr (8 * m) a'` with `a' = writeLE a (8 * i) 8 v`;
    * the JasminPrint `stackStore` value
      `stackSet (Store.get st arr.vname) (idx.toNat) src` is the limb view of `a'`;
    * the post-states satisfy `StateCorrArrW ((arr, m) :: frameRest)` and
      `StateCorrReg regNames` for `Store.set st arr.vname (limb view of a')`. -/
theorem cassgn_laset_u64_simulates
    (gd : GlobDecls) (opS : OpSem)
    (arr idx src : VarI) (ws : WSize) (m : Nat) (a : JArrayMirror (8 * m)) (al : Aligned)
    (i : BitVec WSize.U64.bits) (v : BitVec WSize.U64.bits)
    (s : Estate SyscallState Mem) (st : Store) (regNames : List Var)
    (frameRest : List (Var × Nat))
    (hagree : IntOfWordAgrees opS)
    (harrTy : arr.v_var.vtype = .aarr ws (8 * m))
    (hread : (s.evm).get arr.v_var = .Varr (8 * m) a)
    (hidx : (s.evm).get idx.v_var = .Vword .U64 i)
    (hsrc : (s.evm).get src.v_var = .Vword .U64 v)
    (hin : i.toNat < m)
    (hW : StateCorrArrW ((arr.v_var, m) :: frameRest) st (s.evm))
    (hreg : StateCorrReg regNames st (s.evm))
    (him : idx.v_var ∈ regNames) (hsm : src.v_var ∈ regNames)
    (hdW : ∀ q ∈ frameRest, q.1 ≠ arr.v_var ∧ q.1.vname ≠ arr.v_var.vname)
    (hdR : ∀ r ∈ regNames, r ≠ arr.v_var ∧ r.vname ≠ arr.v_var.vname) :
    OpSemCoverage.assignExec (Mem := Mem) opS gd (.Laset al .AAscale .U64 arr (idxExpr idx))
        (.aword .U64) (.Pvar (mkLvar src)) s
      = .ok (s.withVm ((s.evm).set arr.v_var
          (.Varr (8 * m) (writeLE a (8 * i.toNat) 8 v.toNat))))
    ∧ stackSet (Store.get st arr.v_var.vname (.stackArr 64 m))
        (BitVec.toNat (Store.get st idx.v_var.vname (.reg 64)))
        (Store.get st src.v_var.vname (.reg 64))
      = encodeWordArr m (writeLE a (8 * i.toNat) 8 v.toNat)
    ∧ StateCorrArrW ((arr.v_var, m) :: frameRest)
        (Store.set st arr.v_var.vname (t := .stackArr 64 m)
          (encodeWordArr m (writeLE a (8 * i.toNat) 8 v.toNat)))
        ((s.evm).set arr.v_var (.Varr (8 * m) (writeLE a (8 * i.toNat) 8 v.toNat)))
    ∧ StateCorrReg regNames
        (Store.set st arr.v_var.vname (t := .stackArr 64 m)
          (encodeWordArr m (writeLE a (8 * i.toNat) 8 v.toNat)))
        ((s.evm).set arr.v_var (.Varr (8 * m) (writeLE a (8 * i.toNat) 8 v.toNat))) := by
  refine ⟨mirror_laset_u64_post gd opS arr idx src ws m a al i v s hagree harrTy hread hidx hsrc hin,
    ?_, stateCorrArrW_write arr.v_var m _ st s.evm frameRest hdW
      (fun q hq => hW q (List.mem_cons_of_mem _ hq)),
    stateCorrReg_write_wordArr arr.v_var m _ st s.evm regNames hdR hreg⟩
  have hi : Store.get st idx.v_var.vname (.reg 64) = i :=
    (pvar_read_corr (Mem := Mem) gd opS s st regNames idx .U64 i hreg him hidx).2
  have hv : Store.get st src.v_var.vname (.reg 64) = v :=
    (pvar_read_corr (Mem := Mem) gd opS s st regNames src .U64 v hreg hsm hsrc).2
  rw [store_get_wordArr _ st s.evm arr.v_var m a hW List.mem_cons_self hread, hi, hv]
  exact (encodeWordArr_writeLE m a i.toNat hin v).symm

/-- **End-to-end limb write.** Under the hypotheses of `cassgn_laset_u64_simulates`,
    the emitted `Cassgn` witnesses the relational step `SemIr` to the written
    state, and both correspondences hold after the paired write. -/
theorem cassgn_laset_u64_endToEnd
    (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog) (fuel : Nat) (tag : AssgnTag)
    (arr idx src : VarI) (ws : WSize) (m : Nat) (a : JArrayMirror (8 * m)) (al : Aligned)
    (i : BitVec WSize.U64.bits) (v : BitVec WSize.U64.bits)
    (s : Estate SyscallState Mem) (st : Store) (regNames : List Var)
    (frameRest : List (Var × Nat))
    (hagree : IntOfWordAgrees opS)
    (harrTy : arr.v_var.vtype = .aarr ws (8 * m))
    (hread : (s.evm).get arr.v_var = .Varr (8 * m) a)
    (hidx : (s.evm).get idx.v_var = .Vword .U64 i)
    (hsrc : (s.evm).get src.v_var = .Vword .U64 v)
    (hin : i.toNat < m)
    (hW : StateCorrArrW ((arr.v_var, m) :: frameRest) st (s.evm))
    (hreg : StateCorrReg regNames st (s.evm))
    (him : idx.v_var ∈ regNames) (hsm : src.v_var ∈ regNames)
    (hdW : ∀ q ∈ frameRest, q.1 ≠ arr.v_var ∧ q.1.vname ≠ arr.v_var.vname)
    (hdR : ∀ r ∈ regNames, r ≠ arr.v_var ∧ r.vname ≠ arr.v_var.vname) :
    SemIr (Mem := Mem) aS opS gd prog s
        (.Cassgn (.Laset al .AAscale .U64 arr (idxExpr idx)) tag (.aword .U64) (.Pvar (mkLvar src)))
        (s.withVm ((s.evm).set arr.v_var (.Varr (8 * m) (writeLE a (8 * i.toNat) 8 v.toNat))))
    ∧ StateCorrArrW ((arr.v_var, m) :: frameRest)
        (Store.set st arr.v_var.vname (t := .stackArr 64 m)
          (encodeWordArr m (writeLE a (8 * i.toNat) 8 v.toNat)))
        ((s.evm).set arr.v_var (.Varr (8 * m) (writeLE a (8 * i.toNat) 8 v.toNat)))
    ∧ StateCorrReg regNames
        (Store.set st arr.v_var.vname (t := .stackArr 64 m)
          (encodeWordArr m (writeLE a (8 * i.toNat) 8 v.toNat)))
        ((s.evm).set arr.v_var (.Varr (8 * m) (writeLE a (8 * i.toNat) 8 v.toNat))) := by
  obtain ⟨hrun, _, hW', hR'⟩ :=
    cassgn_laset_u64_simulates gd opS arr idx src ws m a al i v s st regNames frameRest
      hagree harrTy hread hidx hsrc hin hW hreg him hsm hdW hdR
  refine ⟨?_, hW', hR'⟩
  apply ExecAdequacy.execInstrR_sound (n := fuel + 1) aS opS gd prog
  rw [OpSemCoverage.execInstrR_Cassgn_eq]
  exact hrun

end CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeArrWord
