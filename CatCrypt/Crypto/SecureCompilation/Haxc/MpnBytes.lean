/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.FieldBytes
public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mpn

@[expose] public section

set_option autoImplicit false

/-!
# Fixed-size mpn functions at the bytes

The closed limb programs `mpnAddN n`, `mpnSubN n`, `mpnMul1 n` and `mpnAddmul1 n` of
`Algebraic/FieldLimbs/Mpn.lean` as straight-line programs over word arrays, presented to
the region back half `RegionBackend.compileRegion` as programs `NFProg.ofCom` with one
result.

The layouts follow the System V argument registers of GMP's `mpn_add_n(rp, up, vp, n)` at a
fixed `n`: the result array `rp` in `%rdi`, the operand `up` in `%rsi`, and the operand `vp`
(`mpnAbi2 n`) or the scalar `vl` (`mpnAbiS n`) in `%rdx`. A program returns one value
(`Com jasminDialect Γ t`, read back by `denVal t`), so `AbiLayout` cannot read back an array
together with a register: the carry, borrow or high word is stored in the extra cell
`rp[n]` of a result array of `n + 1` words, the convention of the hax `mpn_mul_1` layout
`Mul1Facts.mul1Abi`. GMP returns that word in `%rax` and writes `n` words. For `mpn_mul_1`
and `mpn_addmul_1` the scalar `vl` is in `%rdx`, where GMP passes `n` (and `vl` in `%rcx`).
The separation `AbiLayout.Regions` makes `rp` disjoint from `up` and `vp`; GMP admits
`rp = up`. For `mpn_addmul_1` the array `rp` is both the addend (its first `n` words on
entry) and the result.

The route programs load the operand limbs with `FieldToJasminLimbs.loadLimbs`, splice the
closed program at the loaded limbs with `spliceMultiK`, and store the result limbs with
`FieldToJasminLimbs.storeLimbs` after storing the extra word at index `n` (`storeNW`).

## Main results

* `mpnAbi2`, `mpnAbiS`, `mpnAbiNames`: the two layouts and their export names.
* `addSubCom`, `mul1Com`, `addmul1Com`: the route programs, and their output arrays
  (`addSubCom_denote`, `mul1Com_denote`, `addmul1Com_denote`).
* `mpn_add_n_bytes_correct`, `mpn_sub_n_bytes_correct`, `mpn_mul_1_bytes_correct`,
  `mpn_addmul_1_bytes_correct`: for every result of `compileRegion` on the program, from
  every separated entry state, the decoded bytes halt in a state whose result array holds
  the result limbs and, at index `n`, the carry, borrow or high word satisfying the mpn
  value equation.
* `mpnAcceptCases`: the compilations an acceptance executable runs, at `n = 4` and `n = 8`.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.MpnBytes

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent (pullV)
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS (lookup_pullV)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519
  (w64 w1 MC lk lk1 eConst eAdc eConst_denote eAdc_denote bindK bindK_denote adc_toNat)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont (Rn)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mpn
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf wordsFn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)

/-! ## 1. Storing result limbs and one word -/

section Store

variable {n : Nat}

/-- Storing limbs from index `j` keeps every word at an index past the stored ones. -/
theorem storeVal_get_ge {N : Nat} (o : Fin N → BitVec 64) (i : Nat) :
    ∀ {m : Nat} (j : Nat) (L : ListDenote (Rn m)), j + m ≤ i → i < N →
      stackGet (storeVal o j L) i = stackGet o i
  | 0, _, _, _, _ => rfl
  | m + 1, j, .cons x L, hji, hi => by
      show stackGet (storeVal (stackSet o j x) (j + 1) L) i = _
      rw [storeVal_get_ge _ i (j + 1) L (by omega) hi]
      obtain ⟨n', rfl⟩ : ∃ n', N = n' + 1 := ⟨N - 1, by omega⟩
      simp only [stackGet, stackSet]
      rw [ite_eq_right]
      intro he
      have := congrArg Fin.val he
      simp only [Nat.mod_eq_of_lt (show i < n' + 1 by omega),
        Nat.mod_eq_of_lt (show j < n' + 1 by omega)] at this
      omega

theorem stackGet_stackSet_self {N : Nat} (o : Fin N → BitVec 64) (k : Nat) (x : BitVec 64)
    (hk : k < N) : stackGet (stackSet o k x) k = x := by
  obtain ⟨n', rfl⟩ : ∃ n', N = n' + 1 := ⟨N - 1, by omega⟩
  simp only [stackGet, stackSet, ite_true]

/-- **The stores of `n` limbs and one word** into an array of `n + 1` words: the word `x`
    at index `n`, then the limbs `h` from index `0`; the program returns the last stored
    array. -/
def storeNW {Δ : Ctxt jasminDialect} (o : Var Δ (arrTy (n + 1))) (h : Ctxt.Hom (Rn n) Δ)
    (x : Var Δ w64) : MC Δ [arrTy (n + 1)] :=
  bindK (eConst n) fun r₁ i =>
  bindK (eStore (r₁ o) i (r₁ x)) fun r₂ o' =>
  storeLimbs n 0 o' fun w => r₂ (r₁ (h w))

theorem storeNW_denote (hn : n + 1 < 2 ^ 64) {Δ : Ctxt jasminDialect}
    (o : Var Δ (arrTy (n + 1))) (h : Ctxt.Hom (Rn n) Δ) (x : Var Δ w64) (W : Valuation Δ) :
    (storeNW o h x).denote W
      = .cons (storeVal (stackSet (o.lookup W) n (x.lookup W)) 0 (pullV h W)) .nil := by
  refine bindK_denote _ _ W _ fun r₁ i W₁ h₁ hi => ?_
  refine bindK_denote _ _ W₁ _ fun r₂ o' W₂ h₂ ho => ?_
  rw [storeLimbs_denote (n := n + 1) hn n 0 o' _ W₂ (by omega)]
  have e : (eStore (r₁ o) i (r₁ x)).denote W₁
      = stackSet ((r₁ o).lookup W₁) (i.lookup W₁).toNat ((r₁ x).lookup W₁) := rfl
  have e₀ : (i.lookup W₁).toNat = n := by
    rw [hi]
    exact (BitVec.toNat_ofNat n 64).trans (Nat.mod_eq_of_lt (by omega))
  rw [ho, e, e₀, h₁ o, h₁ x, pullV_comp_pres h₂ (fun w => r₁ (h w)), pullV_comp_pres h₁ h]

/-- The array `o` with the word `x` at index `n` and the limbs `L` from index `0` holds `L`
    in its first `n` words and `x` at index `n`. -/
theorem storeNW_val (o : Fin (n + 1) → BitVec 64) (x : BitVec 64) (L : ListDenote (Rn n)) :
    arrLimbs (storeVal (stackSet o n x) 0 L) n 0 = L
      ∧ stackGet (storeVal (stackSet o n x) 0 L) n = x :=
  ⟨arrLimbs_storeVal _ 0 L (by omega),
    (storeVal_get_ge _ n 0 L (by omega) (by omega)).trans
      (stackGet_stackSet_self o n x (by omega))⟩

/-- The stores of a result vector of `n` limbs followed by one word. -/
def storeRes {Δ : Ctxt jasminDialect} (o : Var Δ (arrTy (n + 1)))
    (res : HVector (fun u => Var Δ u) (Rn n ++ [w64])) : MC Δ [arrTy (n + 1)] :=
  storeNW o (fun w => hvToHom res (inlHom [w64] w))
    (hvToHom res (inrHom (Rn n) (Var.here (d := jasminDialect) (Γ := []) (t := w64))))

theorem storeRes_denote (hn : n + 1 < 2 ^ 64) {Δ : Ctxt jasminDialect}
    (o : Var Δ (arrTy (n + 1))) (res : HVector (fun u => Var Δ u) (Rn n ++ [w64]))
    (W : Valuation Δ) (S : ListDenote (Rn n)) (x : BitVec 64)
    (hres : MultiReturnCom.lookupVars res W = hvAppend S (.cons x .nil)) :
    (storeRes o res).denote W = .cons (storeVal (stackSet (o.lookup W) n x) 0 S) .nil := by
  rw [storeRes, storeNW_denote hn]
  have hp : pullV (hvToHom res) W = hvAppend S (.cons x .nil) := (pullV_hvToHom W res).trans hres
  have e₁ : pullV (fun w => hvToHom res (inlHom [w64] w)) W = S := by
    rw [pullV_comp (fun w => inlHom [w64] w) (fun w => hvToHom res w), hp, pullV_inlHom]
  have e₂ : (hvToHom res (inrHom (Rn n)
      (Var.here (d := jasminDialect) (Γ := []) (t := w64)))).lookup W = x := by
    rw [← lookup_pullV, hp, lookup_inrHom]
    rfl
  rw [e₁, e₂]

end Store

/-! ## 2. The layouts -/

/-- **The layout of a two-operand mpn function over `n` limbs**: the result array `rp` of
    `n + 1` words in `%rdi`, the operands `up` and `vp` of `n` words in `%rsi` and `%rdx`;
    the result is the `n + 1` words at the entry `%rdi`; the body's stack words lie in the
    `4096` bytes below the entry `%rsp`. -/
def mpnAbi2 (n : Nat) : AbiLayout where
  args := [⟨"rp", "%rdi", .words (n + 1)⟩, ⟨"up", "%rsi", .words n⟩, ⟨"vp", "%rdx", .words n⟩]
  consts := []
  result := .words "%rdi" (n + 1)
  bounds := []
  frameLo := -4096
  frameHi := -8

/-- **The layout of an mpn function of an operand and a word over `n` limbs**: the result
    array `rp` of `n + 1` words in `%rdi`, the operand `up` of `n` words in `%rsi`, the word
    `vl` in `%rdx`; the result is the `n + 1` words at the entry `%rdi`. -/
def mpnAbiS (n : Nat) : AbiLayout where
  args := [⟨"rp", "%rdi", .words (n + 1)⟩, ⟨"up", "%rsi", .words n⟩, ⟨"vl", "%rdx", .scalar⟩]
  consts := []
  result := .words "%rdi" (n + 1)
  bounds := []
  frameLo := -4096
  frameHi := -8

/-- The export names of the layout `σ` under the symbol `f`. -/
def mpnAbiNames (f : String) (σ : AbiLayout) : AbiNames where
  fname := f
  outArg := ""
  inArgs := []
  abiArgs := σ.args.map fun a => exportReg a.reg

/-- The context of a two-operand mpn route program: `vp`, `up`, then `rp`. -/
abbrev mpnCtx2 (n : Nat) : Ctxt jasminDialect := [arrTy n, arrTy n, arrTy (n + 1)]

/-- The context of an mpn route program of an operand and a word: `vl`, `up`, then `rp`. -/
abbrev mpnCtxS (n : Nat) : Ctxt jasminDialect := [w64, arrTy n, arrTy (n + 1)]

/-- The valuation of `mpnCtx2 n` read off the machine state `sa`: the words at the entry
    `%rdx`, `%rsi` and `%rdi`. -/
def abiVal2 (n : Nat) (sa : AState) : Valuation (mpnCtx2 n) :=
  .cons (wordsFn sa (sa.regs "%rdx") n)
    (.cons (wordsFn sa (sa.regs "%rsi") n) (.cons (wordsFn sa (sa.regs "%rdi") (n + 1)) .nil))

/-- The valuation of `mpnCtxS n` read off the machine state `sa`: the entry `%rdx`, and the
    words at the entry `%rsi` and `%rdi`. -/
def abiValS (n : Nat) (sa : AState) : Valuation (mpnCtxS n) :=
  .cons (sa.regs "%rdx")
    (.cons (wordsFn sa (sa.regs "%rsi") n) (.cons (wordsFn sa (sa.regs "%rdi") (n + 1)) .nil))

theorem abiValOf_mpnAbi2 (n : Nat) (sa : AState) : AbiValOf (mpnAbi2 n) sa (abiVal2 n sa) where
  arg := fun v => by
    rcases v with _ | _ | _ | ⟨⟨⟩⟩ <;> rfl
  reg := fun v => by
    rcases v with _ | _ | _ | ⟨⟨⟩⟩
  arr := fun v => by
    rcases v with _ | _ | _ | ⟨⟨⟩⟩
    · exact ⟨_, rfl, rfl, rfl, rfl⟩
    · exact ⟨_, rfl, rfl, rfl, rfl⟩
    · exact ⟨_, rfl, rfl, rfl, rfl⟩

theorem abiValOf_mpnAbiS (n : Nat) (sa : AState) : AbiValOf (mpnAbiS n) sa (abiValS n sa) where
  arg := fun v => by
    rcases v with _ | _ | _ | ⟨⟨⟩⟩ <;> rfl
  reg := fun v => by
    rcases v with _ | _ | _ | ⟨⟨⟩⟩
    exact ⟨_, rfl, rfl, rfl, rfl⟩
  arr := fun v => by
    rcases v with _ | _ | _ | ⟨⟨⟩⟩
    · exact ⟨_, rfl, rfl, rfl, rfl⟩
    · exact ⟨_, rfl, rfl, rfl, rfl⟩

/-- The value of the first `n` of the `k` words at the entry value of the register `r`. -/
def memVal (sa : AState) (r : String) (k n : Nat) : Nat :=
  limbsVal (arrLimbs (wordsFn sa (sa.regs r) k) n 0)

/-! ## 3. The route programs -/

section Route

variable {n : Nat}

/-- The renaming of the empty context. -/
def nilHom {Δ : Ctxt jasminDialect} : Ctxt.Hom ([] : Ctxt jasminDialect) Δ := fun v => nomatch v

/-- The variable of the context `[w1]`. -/
abbrev bitVar : Var (d := jasminDialect) [w1] w1 := Var.here

/-- **A two-operand mpn program over word arrays, as a multi-result program**: the loads of
    the `n` limbs of `up` and of `vp`, the program `blk` at `up ++ vp`, the carry word
    `0 + 0 + c` of its returned bit `c`, and the stores of its `n` result limbs and the
    carry word into `rp`. -/
def addSubBody (blk : MC (Rn n ++ (Rn n ++ [])) (Rn n ++ [w1])) :
    MC (mpnCtx2 n) [arrTy (n + 1)] :=
  loadLimbs n 0 (Var.there Var.here) fun r₁ hu =>
  loadLimbs n 0 (r₁ Var.here) fun r₂ hv =>
  spliceMultiK (MultiReturnCom.rename
      (appendHom (fun w => r₂ (hu w)) (appendHom hv nilHom)) blk) fun r₃ res =>
  bindK (eConst 0) fun r₄ z =>
  bindK (eAdc z z (r₄ (hvToHom res (inrHom (Rn n) bitVar)))) fun r₅ cw =>
  storeNW (r₅ (r₄ (r₃ (r₂ (r₁ (Var.there (Var.there Var.here)))))))
    (fun w => r₅ (r₄ (hvToHom res (inlHom [w1] w)))) cw

/-- **A two-operand mpn program over word arrays.** -/
def addSubCom (blk : MC (Rn n ++ (Rn n ++ [])) (Rn n ++ [w1])) :
    Com jasminDialect (mpnCtx2 n) (arrTy (n + 1)) :=
  (addSubBody blk).toComHead

theorem addCarryWord_zero (c : BitVec 1) : (addCarryWord (0 : BitVec 64) 0 c).toNat = c.toNat := by
  have h := adc_toNat 0 0 c
  have := c.isLt
  rw [show (0 : BitVec 64).toNat = 0 from rfl] at h
  omega

/-- **The output array of a two-operand mpn program.** If `blk` returns the limbs `S` and
    the bit `c` on the limbs of `a` followed by those of `b`, the first `n` words of the
    output array are `S` and its word `n` has the value of `c`. -/
theorem addSubCom_denote (hn : n + 1 < 2 ^ 64) (blk : MC (Rn n ++ (Rn n ++ [])) (Rn n ++ [w1]))
    (b a : Fin n → BitVec 64) (o : Fin (n + 1) → BitVec 64) (S : ListDenote (Rn n))
    (c : BitVec 1)
    (hblk : blk.denote (hvAppend (arrLimbs a n 0) (hvAppend (arrLimbs b n 0) .nil))
      = hvAppend S (.cons c .nil)) :
    arrLimbs ((addSubCom blk).denote (.cons b (.cons a (.cons o .nil)))) n 0 = S
      ∧ (stackGet ((addSubCom blk).denote (.cons b (.cons a (.cons o .nil)))) n).toNat
        = c.toNat := by
  have hbody : (addSubBody blk).denote (.cons b (.cons a (.cons o .nil)))
      = .cons (storeVal (stackSet o n (addCarryWord 0 0 c)) 0 S) .nil := by
    refine loadLimbs_denote n 0 _ _ _ _ (by omega) fun r₁ hu W₁ h₁ hhu => ?_
    refine loadLimbs_denote n 0 _ _ _ _ (by omega) fun r₂ hv W₂ h₂ hhv => ?_
    refine spliceMultiK_denote _ _ W₂ _ fun r₃ res W₃ h₃ hres => ?_
    refine bindK_denote _ _ W₃ _ fun r₄ z W₄ h₄ hz => ?_
    refine bindK_denote _ _ W₄ _ fun r₅ cw W₅ h₅ hcw => ?_
    rw [multiReturnCom_denote_rename, pullV_appendHom, pullV_appendHom,
      pullV_comp_pres h₂ hu, hhu, hhv, h₁ Var.here] at hres
    have hres' : MultiReturnCom.lookupVars res W₃ = hvAppend S (.cons c .nil) := hres.trans hblk
    have hp : pullV (hvToHom res) W₃ = hvAppend S (.cons c .nil) :=
      (pullV_hvToHom W₃ res).trans hres'
    have e₁ : pullV (fun w => r₅ (r₄ (hvToHom res (inlHom [w1] w)))) W₅ = S := by
      rw [pullV_comp_pres h₅ (fun w => r₄ (hvToHom res (inlHom [w1] w))),
        pullV_comp_pres h₄ (fun w => hvToHom res (inlHom [w1] w)),
        pullV_comp (fun w => inlHom [w1] w) (fun w => hvToHom res w), hp, pullV_inlHom]
    have e₂ : (hvToHom res (inrHom (Rn n) bitVar)).lookup W₃ = c := by
      rw [← lookup_pullV, hp, lookup_inrHom]
      rfl
    have e₃ : cw.lookup W₅ = addCarryWord 0 0 c := by
      rw [hcw, eAdc_denote]
      simp only [lk, lk1]
      rw [hz, h₄, e₂, eConst_denote]
      rfl
    rw [storeNW_denote hn, e₁, e₃, h₅, h₄, h₃, h₂, h₁]
    rfl
  rw [addSubCom, MultiReturnCom.toComHead_denote, hbody]
  obtain ⟨h1, h2⟩ := storeNW_val o (addCarryWord 0 0 c) S
  refine ⟨h1, ?_⟩
  show (stackGet (storeVal (stackSet o n (addCarryWord 0 0 c)) 0 S) n).toNat = _
  rw [h2, addCarryWord_zero]

/-- **`mpn_mul_1` over word arrays, as a multi-result program**: the loads of the `n` limbs
    of `up`, the program `mpnMul1 n` at `up` and `vl`, and the stores of its `n` low limbs
    and its high word into `rp`. -/
def mul1Body : MC (mpnCtxS n) [arrTy (n + 1)] :=
  loadLimbs n 0 (Var.there Var.here) fun r₁ hu =>
  spliceMultiK (MultiReturnCom.rename
      (appendHom hu (consHom (r₁ Var.here) nilHom)) (mpnMul1 n)) fun r₂ res =>
  storeRes (r₂ (r₁ (Var.there (Var.there Var.here)))) res

/-- **`mpn_mul_1` over word arrays.** -/
def mul1Com : Com jasminDialect (mpnCtxS n) (arrTy (n + 1)) := (mul1Body (n := n)).toComHead

/-- **The output array of `mpn_mul_1` over word arrays**: the first `n` words and word `n`
    are the low limbs and the high word that `mpnMul1 n` returns on the limbs of `a` and the
    word `v`. -/
theorem mul1Com_denote (hn : n + 1 < 2 ^ 64) (v : BitVec 64) (a : Fin n → BitVec 64)
    (o : Fin (n + 1) → BitVec 64) (S : ListDenote (Rn n)) (hi : BitVec 64)
    (hblk : (mpnMul1 n).denote (hvAppend (arrLimbs a n 0) (.cons v .nil))
      = hvAppend S (.cons hi .nil)) :
    arrLimbs ((mul1Com (n := n)).denote (.cons v (.cons a (.cons o .nil)))) n 0 = S
      ∧ stackGet ((mul1Com (n := n)).denote (.cons v (.cons a (.cons o .nil)))) n = hi := by
  have hbody : (mul1Body (n := n)).denote (.cons v (.cons a (.cons o .nil)))
      = .cons (storeVal (stackSet o n hi) 0 S) .nil := by
    refine loadLimbs_denote n 0 _ _ _ _ (by omega) fun r₁ hu W₁ h₁ hhu => ?_
    refine spliceMultiK_denote _ _ W₁ _ fun r₂ res W₂ h₂ hres => ?_
    rw [multiReturnCom_denote_rename, pullV_appendHom, hhu] at hres
    beta_reduce at hres
    have hv : pullV (consHom (r₁ Var.here) nilHom) W₁ = .cons v .nil := by
      show HVector.cons ((r₁ Var.here).lookup W₁) .nil = _
      rw [h₁]
      rfl
    rw [hv] at hres
    rw [storeRes_denote hn _ res W₂ S hi (hres.trans hblk), h₂, h₁]
    rfl
  rw [mul1Com, MultiReturnCom.toComHead_denote, hbody]
  exact storeNW_val o hi S

/-- **`mpn_addmul_1` over word arrays, as a multi-result program**: the loads of the first
    `n` limbs of `rp` and the `n` limbs of `up`, the program `mpnAddmul1 n` at `rp`, `up`
    and `vl`, and the stores of its `n` low limbs and its high word into `rp`. -/
def addmul1Body : MC (mpnCtxS n) [arrTy (n + 1)] :=
  loadLimbs n 0 (Var.there (Var.there Var.here)) fun r₁ hr =>
  loadLimbs n 0 (r₁ (Var.there Var.here)) fun r₂ hu =>
  spliceMultiK (MultiReturnCom.rename
      (appendHom (fun w => r₂ (hr w)) (appendHom hu (consHom (r₂ (r₁ Var.here)) nilHom)))
      (mpnAddmul1 n)) fun r₃ res =>
  storeRes (r₃ (r₂ (r₁ (Var.there (Var.there Var.here))))) res

/-- **`mpn_addmul_1` over word arrays.** -/
def addmul1Com : Com jasminDialect (mpnCtxS n) (arrTy (n + 1)) :=
  (addmul1Body (n := n)).toComHead

/-- **The output array of `mpn_addmul_1` over word arrays**: the first `n` words and word
    `n` are the low limbs and the high word that `mpnAddmul1 n` returns on the first `n`
    limbs of `o`, the limbs of `a` and the word `v`. -/
theorem addmul1Com_denote (hn : n + 1 < 2 ^ 64) (v : BitVec 64) (a : Fin n → BitVec 64)
    (o : Fin (n + 1) → BitVec 64) (S : ListDenote (Rn n)) (hi : BitVec 64)
    (hblk : (mpnAddmul1 n).denote
        (hvAppend (arrLimbs o n 0) (hvAppend (arrLimbs a n 0) (.cons v .nil)))
      = hvAppend S (.cons hi .nil)) :
    arrLimbs ((addmul1Com (n := n)).denote (.cons v (.cons a (.cons o .nil)))) n 0 = S
      ∧ stackGet ((addmul1Com (n := n)).denote (.cons v (.cons a (.cons o .nil)))) n = hi := by
  have hbody : (addmul1Body (n := n)).denote (.cons v (.cons a (.cons o .nil)))
      = .cons (storeVal (stackSet o n hi) 0 S) .nil := by
    refine loadLimbs_denote n 0 _ _ _ _ (by omega) fun r₁ hr W₁ h₁ hhr => ?_
    refine loadLimbs_denote n 0 _ _ _ _ (by omega) fun r₂ hu W₂ h₂ hhu => ?_
    refine spliceMultiK_denote _ _ W₂ _ fun r₃ res W₃ h₃ hres => ?_
    rw [multiReturnCom_denote_rename, pullV_appendHom, pullV_appendHom,
      pullV_comp_pres h₂ hr, hhr, hhu, h₁ (Var.there Var.here)] at hres
    have hv : pullV (consHom (r₂ (r₁ Var.here)) nilHom) W₂ = .cons v .nil := by
      show HVector.cons ((r₂ (r₁ Var.here)).lookup W₂) .nil = _
      rw [h₂, h₁]
      rfl
    beta_reduce at hres
    rw [hv] at hres
    rw [storeRes_denote hn _ res W₃ S hi (hres.trans hblk), h₃, h₂, h₁]
    rfl
  rw [addmul1Com, MultiReturnCom.toComHead_denote, hbody]
  exact storeNW_val o hi S

end Route

/-! ## 4. The mpn functions at the bytes -/

/-- **`mpn_add_n` at the bytes.** For a result `(P', bytes)` of `compileRegion` on the
    program of `mpnAddN n` (`NFProg.ofCom`) under the layout `mpnAbi2 n`: from every machine
    state `sa` satisfying the layout's regions, the bytes decode to a program that halts in
    a state from which the layout reads back an array of `n + 1` words whose first `n`
    words `S` and word `n` (the carry `cy`) satisfy `S + 2^(64n) · cy = up + vp`,
    `cy ≤ 1`. -/
theorem mpn_add_n_bytes_correct {n : Nat} (hn : n + 1 < 2 ^ 64) (a : AbiNames)
    {P' : Lprog} {bytes : List (BitVec 8)}
    (h : compileRegion (mpnAbi2 n) a (NFProg.ofCom (addSubCom (mpnAddN n))) = some (P', bytes))
    (sa : AState) (hreg : (mpnAbi2 n).Regions sa) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∃ arr : Fin (n + 1) → BitVec 64, (mpnAbi2 n).ResultOf sa sa' (arrVal arr)
        ∧ limbsVal (arrLimbs arr n 0) + 2 ^ (64 * n) * (stackGet arr n).toNat
            = memVal sa "%rsi" n n + memVal sa "%rdx" n n
        ∧ (stackGet arr n).toNat ≤ 1 := by
  obtain ⟨prog, sa', hd, hh, hr, -⟩ :=
    compileRegion_correct h sa (abiVal2 n sa) (abiValOf_mpnAbi2 n sa) hreg 0
      (NFProg.denote_ofCom _ 0 _)
  obtain ⟨S, cy, hS, hv, hc⟩ := mpnAddN_denote n (arrLimbs (wordsFn sa (sa.regs "%rsi") n) n 0)
    (arrLimbs (wordsFn sa (sa.regs "%rdx") n) n 0)
  obtain ⟨h1, h2⟩ := addSubCom_denote hn (mpnAddN n) _ _ (wordsFn sa (sa.regs "%rdi") (n + 1))
    S cy hS
  refine ⟨prog, sa', hd, hh, (addSubCom (mpnAddN n)).denote (abiVal2 n sa), hr, ?_, ?_⟩
  · rw [abiVal2, h1, h2]
    exact hv
  · rw [abiVal2, h2]
    exact hc

/-- **`mpn_sub_n` at the bytes.** For a result `(P', bytes)` of `compileRegion` on the
    program of `mpnSubN n` (`NFProg.ofCom`) under the layout `mpnAbi2 n`: from every machine
    state `sa` satisfying the layout's regions, the bytes decode to a program that halts in
    a state from which the layout reads back an array of `n + 1` words whose first `n`
    words `S` and word `n` (the borrow `bw`) satisfy `S + vp = up + 2^(64n) · bw`,
    `bw ≤ 1`. -/
theorem mpn_sub_n_bytes_correct {n : Nat} (hn : n + 1 < 2 ^ 64) (a : AbiNames)
    {P' : Lprog} {bytes : List (BitVec 8)}
    (h : compileRegion (mpnAbi2 n) a (NFProg.ofCom (addSubCom (mpnSubN n))) = some (P', bytes))
    (sa : AState) (hreg : (mpnAbi2 n).Regions sa) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∃ arr : Fin (n + 1) → BitVec 64, (mpnAbi2 n).ResultOf sa sa' (arrVal arr)
        ∧ limbsVal (arrLimbs arr n 0) + memVal sa "%rdx" n n
            = memVal sa "%rsi" n n + 2 ^ (64 * n) * (stackGet arr n).toNat
        ∧ (stackGet arr n).toNat ≤ 1 := by
  obtain ⟨prog, sa', hd, hh, hr, -⟩ :=
    compileRegion_correct h sa (abiVal2 n sa) (abiValOf_mpnAbi2 n sa) hreg 0
      (NFProg.denote_ofCom _ 0 _)
  obtain ⟨S, bw, hS, hv, hc⟩ := mpnSubN_denote n (arrLimbs (wordsFn sa (sa.regs "%rsi") n) n 0)
    (arrLimbs (wordsFn sa (sa.regs "%rdx") n) n 0)
  obtain ⟨h1, h2⟩ := addSubCom_denote hn (mpnSubN n) _ _ (wordsFn sa (sa.regs "%rdi") (n + 1))
    S bw hS
  refine ⟨prog, sa', hd, hh, (addSubCom (mpnSubN n)).denote (abiVal2 n sa), hr, ?_, ?_⟩
  · rw [abiVal2, h1, h2]
    exact hv
  · rw [abiVal2, h2]
    exact hc

/-- **`mpn_mul_1` at the bytes.** For a result `(P', bytes)` of `compileRegion` on the
    program of `mpnMul1 n` (`NFProg.ofCom`) under the layout `mpnAbiS n`: from every machine
    state `sa` satisfying the layout's regions, the bytes decode to a program that halts in
    a state from which the layout reads back an array of `n + 1` words whose first `n`
    words `S` and word `n` (the high word `hi`) satisfy `S + 2^(64n) · hi = up · vl`. -/
theorem mpn_mul_1_bytes_correct {n : Nat} (hn : n + 1 < 2 ^ 64) (a : AbiNames)
    {P' : Lprog} {bytes : List (BitVec 8)}
    (h : compileRegion (mpnAbiS n) a (NFProg.ofCom (mul1Com (n := n))) = some (P', bytes))
    (sa : AState) (hreg : (mpnAbiS n).Regions sa) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∃ arr : Fin (n + 1) → BitVec 64, (mpnAbiS n).ResultOf sa sa' (arrVal arr)
        ∧ limbsVal (arrLimbs arr n 0) + 2 ^ (64 * n) * (stackGet arr n).toNat
            = memVal sa "%rsi" n n * (sa.regs "%rdx").toNat := by
  obtain ⟨prog, sa', hd, hh, hr, -⟩ :=
    compileRegion_correct h sa (abiValS n sa) (abiValOf_mpnAbiS n sa) hreg 0
      (NFProg.denote_ofCom _ 0 _)
  obtain ⟨S, hi, hS, hv⟩ :=
    mpnMul1_denote n (arrLimbs (wordsFn sa (sa.regs "%rsi") n) n 0) (sa.regs "%rdx")
  obtain ⟨h1, h2⟩ := mul1Com_denote hn (sa.regs "%rdx") _ (wordsFn sa (sa.regs "%rdi") (n + 1))
    S hi hS
  refine ⟨prog, sa', hd, hh, (mul1Com (n := n)).denote (abiValS n sa), hr, ?_⟩
  rw [abiValS, h1, h2]
  exact hv

/-- **`mpn_addmul_1` at the bytes.** For a result `(P', bytes)` of `compileRegion` on the
    program of `mpnAddmul1 n` (`NFProg.ofCom`) under the layout `mpnAbiS n`: from every
    machine state `sa` satisfying the layout's regions, the bytes decode to a program that
    halts in a state from which the layout reads back an array of `n + 1` words whose first
    `n` words `S` and word `n` (the high word `hi`) satisfy `S + 2^(64n) · hi = rp + up · vl`,
    where `rp` is the value of the first `n` words at `%rdi` on entry. -/
theorem mpn_addmul_1_bytes_correct {n : Nat} (hn : n + 1 < 2 ^ 64) (a : AbiNames)
    {P' : Lprog} {bytes : List (BitVec 8)}
    (h : compileRegion (mpnAbiS n) a (NFProg.ofCom (addmul1Com (n := n))) = some (P', bytes))
    (sa : AState) (hreg : (mpnAbiS n).Regions sa) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∃ arr : Fin (n + 1) → BitVec 64, (mpnAbiS n).ResultOf sa sa' (arrVal arr)
        ∧ limbsVal (arrLimbs arr n 0) + 2 ^ (64 * n) * (stackGet arr n).toNat
            = memVal sa "%rdi" (n + 1) n + memVal sa "%rsi" n n * (sa.regs "%rdx").toNat := by
  obtain ⟨prog, sa', hd, hh, hr, -⟩ :=
    compileRegion_correct h sa (abiValS n sa) (abiValOf_mpnAbiS n sa) hreg 0
      (NFProg.denote_ofCom _ 0 _)
  obtain ⟨S, hi, hS, hv⟩ :=
    mpnAddmul1_denote n (arrLimbs (wordsFn sa (sa.regs "%rdi") (n + 1)) n 0)
      (arrLimbs (wordsFn sa (sa.regs "%rsi") n) n 0) (sa.regs "%rdx")
  obtain ⟨h1, h2⟩ := addmul1Com_denote hn (sa.regs "%rdx") _ _ S hi hS
  refine ⟨prog, sa', hd, hh, (addmul1Com (n := n)).denote (abiValS n sa), hr, ?_⟩
  rw [abiValS, h1, h2]
  exact hv

/-! ## 5. The acceptance cases -/

/-- The compilations an acceptance executable runs: each mpn function at `n = 4` and
    `n = 8` under its layout, as its symbol, its limb count and the call of `compileRegion`
    under the region names `nfAbiNames`. -/
def mpnAcceptCases (_ : Unit) :
    List (String × Nat × (Unit → Option (Lprog × List (BitVec 8)))) :=
  [4, 8].flatMap fun n =>
    [("mpn_add_n", n, fun _ => compileRegion (mpnAbi2 n) (nfAbiNames "mpn_add_n" (mpnAbi2 n))
        (NFProg.ofCom (addSubCom (mpnAddN n)))),
     ("mpn_sub_n", n, fun _ => compileRegion (mpnAbi2 n) (nfAbiNames "mpn_sub_n" (mpnAbi2 n))
        (NFProg.ofCom (addSubCom (mpnSubN n)))),
     ("mpn_mul_1", n, fun _ => compileRegion (mpnAbiS n) (nfAbiNames "mpn_mul_1" (mpnAbiS n))
        (NFProg.ofCom (mul1Com (n := n)))),
     ("mpn_addmul_1", n, fun _ =>
        compileRegion (mpnAbiS n) (nfAbiNames "mpn_addmul_1" (mpnAbiS n))
          (NFProg.ofCom (addmul1Com (n := n))))]

end CatCrypt.Crypto.SecureCompilation.Haxc.MpnBytes
