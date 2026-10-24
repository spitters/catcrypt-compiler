/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.MpnLoopCorrect

/-!
# The loop-carried store-at-index write invariant for the `mpn` output array

The runtime-N `mpn` add/sub kernels thread a **scalar** carry accumulator and
write their result to a caller-provided **output array** one word per trip, via a
register-indexed store `out[i] := v` (`storeMemIdx`). The scalar-accumulator loop
semantics (`JLoopBodyN.denote`) folds only the carry and treats every loop
invariant — the output memref included — as constant across trips, so it exposes
nothing about the stored words. This module supplies the missing observation: a
machine-level theorem about the **memory cells** the loop writes.

The result is stated over the `JState`/`bodyStep`/`runBoundedLoop` word-addressed
machine model (`JasminModel`, `LoopEmitBridge`), the model
`MpnLoopCorrect.mpnAddNStep` runs in.

## Main results

* `StoreStepSpec` — a per-trip characterisation of a store-at-index body: one
  `bodyStep` advances the index register by one and writes exactly one output
  cell, at the current index, with a value `storeVal` of the entry state,
  disturbing no other cell.
* `storeIterate_index` — under a no-wraparound bound the index register after `k`
  trips holds `i₀ + k`.
* `storeIterate_writeInv` — the loop-carried write invariant: after `n` trips each
  output cell `k < n` holds the trip-`k` stored value, and every other cell (a
  different base, or an out-of-range offset) is unchanged. Proved by induction on
  the trip count.

The non-aliasing hypothesis is structural in this model: memory is keyed by
`(base, offset)`, so distinct base names never alias, and `0 < scale` keeps the
per-trip offsets distinct. The output base being distinct from the input bases is
the disjoint-memref precondition GMP's `mpn_add_n` documents.

`mpnAddNStep_storeStepSpec` instantiates the specification for the `mpn_add_n`
step; `mpnAdd_runBounded_stored_cells` is the resulting stored-output theorem.
The functional identification of the stored word with the reference per-limb add
is factored as `MpnAddStoredWordAgrees`, corroborated at `n = 4` by
`MpnLoopCorrect.mpnAddN_kat_n4`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.MpnLoopStoreInvariant

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoopUnroll
open CatCrypt.Crypto.SecureCompilation.VIR.LoopEmitBridge
open CatCrypt.Crypto.SecureCompilation.VIR.MpnLoopCorrect

variable {w : Nat}

/-! ## 1. The generic store-at-index write invariant -/

/-- A **store-at-index body specification**: one `bodyStep` of `body` advances the
    index register `idxReg` by one and writes exactly the cell of `base` at the
    current index (offset `scale · (s.get idxReg).toNat`) with value `storeVal s`,
    leaving every other cell — any other base, or any other offset of `base` —
    unchanged. This is the memory footprint of the per-limb store `out[i] := v`,
    `i += 1` a runtime-N `mpn` kernel runs each trip. -/
structure StoreStepSpec (body : List (JInstr w)) (idxReg base : String)
    (scale : Nat) (storeVal : JState w → BitVec w) : Prop where
  /-- One trip advances the index register by one. -/
  index : ∀ s : JState w, (bodyStep body s).get idxReg = s.get idxReg + BitVec.ofNat w 1
  /-- One trip writes exactly `base` at the current index, value `storeVal s`. -/
  mem : ∀ s : JState w, (bodyStep body s).mem =
      fun b (o : Int) => if b = base ∧ o = ((scale * (s.get idxReg).toNat : Nat) : Int)
                 then storeVal s else s.mem b o

/-- Under a no-wraparound bound on the trip count, the index register after `k`
    trips of a `StoreStepSpec` body holds `i₀ + k` (as a `Nat` through `toNat`). -/
theorem storeIterate_index {body : List (JInstr w)} {idxReg base : String}
    {scale : Nat} {storeVal : JState w → BitVec w}
    (h : StoreStepSpec body idxReg base scale storeVal) (s : JState w)
    (hw : 0 < w) :
    ∀ k : Nat, (s.get idxReg).toNat + k < 2 ^ w →
      (((bodyStep body)^[k] s).get idxReg).toNat = (s.get idxReg).toNat + k := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
      intro hb
      have hbk : (s.get idxReg).toNat + k < 2 ^ w := by omega
      have h1 : (BitVec.ofNat w 1).toNat = 1 := by
        simp [BitVec.toNat_ofNat, Nat.one_mod_two_pow (by omega : 0 < w)]
      rw [Function.iterate_succ_apply', h.index, BitVec.toNat_add, ih hbk, h1,
        Nat.mod_eq_of_lt (by omega)]
      omega

/-- **The loop-carried store-at-index write invariant.** After `n` trips of a
    `StoreStepSpec` body from `s`: each output cell `k < n` (at offset
    `scale · (i₀ + k)` of `base`) holds the value the trip-`k` state stored, and
    every other cell — a different base, or an offset of `base` outside the written
    range — is unchanged. The output array of an `mpn` kernel therefore ends the
    loop holding exactly the per-trip stored words, with the input arrays intact
    (they live at distinct bases). Proved by induction on the trip count. -/
theorem storeIterate_writeInv {body : List (JInstr w)} {idxReg base : String}
    {scale : Nat} {storeVal : JState w → BitVec w}
    (h : StoreStepSpec body idxReg base scale storeVal) (hscale : 0 < scale)
    (hw : 0 < w) (s : JState w) (n : Nat) (hb : (s.get idxReg).toNat + n < 2 ^ w) :
    (∀ k, k < n →
        ((bodyStep body)^[n] s).mem base ((scale * ((s.get idxReg).toNat + k) : Nat) : Int)
          = storeVal ((bodyStep body)^[k] s))
    ∧ (∀ (b : String) (o : Int),
        (b ≠ base ∨ (∀ k, k < n → o ≠ ((scale * ((s.get idxReg).toNat + k) : Nat) : Int))) →
        ((bodyStep body)^[n] s).mem b o = s.mem b o) := by
  induction n with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro k hk; exact absurd hk (Nat.not_lt_zero k)
      · intro b o _; simp
  | succ n ih =>
      have hbn : (s.get idxReg).toNat + n < 2 ^ w := by omega
      obtain ⟨ihW, ihU⟩ := ih hbn
      have hidx : (((bodyStep body)^[n] s).get idxReg).toNat = (s.get idxReg).toNat + n :=
        storeIterate_index h s hw n hbn
      have hmemN := h.mem ((bodyStep body)^[n] s)
      have hstep : (bodyStep body)^[n+1] s = bodyStep body ((bodyStep body)^[n] s) :=
        Function.iterate_succ_apply' (bodyStep body) n s
      constructor
      · intro k hk
        simp only [hstep, hmemN, hidx]
        by_cases hkn : k = n
        · subst hkn; simp
        · have hne : ((scale * ((s.get idxReg).toNat + k) : Nat) : Int)
              ≠ ((scale * ((s.get idxReg).toNat + n) : Nat) : Int) := by
            have hkn' : (s.get idxReg).toNat + k ≠ (s.get idxReg).toNat + n := by omega
            have : scale * ((s.get idxReg).toNat + k) ≠ scale * ((s.get idxReg).toNat + n) :=
              fun hc => hkn' (Nat.eq_of_mul_eq_mul_left hscale hc)
            exact_mod_cast this
          rw [ite_eq_right (by rintro ⟨-, h2⟩; exact hne h2)]
          exact ihW k (by omega)
      · intro b o hbo
        simp only [hstep, hmemN, hidx]
        have hcond : ¬ (b = base ∧ o = ((scale * ((s.get idxReg).toNat + n) : Nat) : Int)) := by
          rcases hbo with hb' | hall
          · exact fun hc => hb' hc.1
          · exact fun hc => hall n (by omega) hc.2
        rw [ite_eq_right hcond]
        refine ihU b o ?_
        rcases hbo with hb' | hall
        · exact Or.inl hb'
        · exact Or.inr (fun k hk => hall k (by omega))

/-! ## 2. Register/memory frame helpers absent from `JasminModel` -/

/-- Writing a `B5W` result to `dst` leaves any other register `r' ≠ dst`. -/
theorem get_writeB5W_other (s : JState w) (dst r' : String) (t : B5W w)
    (h : r' ≠ dst) : (s.writeB5W dst t).get r' = s.get r' := by
  simp [JState.writeB5W, JState.get, h]

/-- Writing a `B5W` result leaves memory. -/
theorem mem_writeB5W (s : JState w) (dst : String) (t : B5W w) :
    (s.writeB5W dst t).mem = s.mem := rfl

/-- A register write leaves memory. -/
theorem mem_setReg (s : JState w) (r : String) (v : BitVec w) :
    (s.setReg r v).mem = s.mem := rfl

/-- A memory write leaves the registers, so a register read passes through. -/
theorem get_store (s : JState w) (base : String) (off : Int) (v : BitVec w)
    (r : String) : (s.store base off v).get r = s.get r := rfl

/-- The memory after a store, as an explicit conditional over `(base, off)`. -/
theorem mem_store (s : JState w) (base : String) (off : Int) (v : BitVec w) :
    (s.store base off v).mem =
      fun b o => if b = base ∧ o = off then v else s.mem b o := rfl

/-! ## 3. The `mpn_add_n` step instantiation -/

/-- The word the `mpn_add_n` step stores at trip `s`: the `"a"` register after the
    two half-add stages (`add`; `setc`; `adc`), i.e. the value `storeMemIdx` writes
    to `out[i]`. -/
def mpnAddStoreWord (s : JState 64) : BitVec 64 :=
  (runBlock s (mpnAddNStep.take 6)).get "a"

/-- **The `mpn_add_n` step meets the store-at-index specification.** One
    `bodyStep mpnAddNStep` advances the limb index `"i"` by one and writes exactly
    the cell `out["rp" + 8·i]` with `mpnAddStoreWord s`, disturbing no other cell —
    in particular no cell of the input arrays `"ap"`/`"bp"`. -/
theorem mpnAddNStep_storeStepSpec :
    StoreStepSpec mpnAddNStep "i" "rp" 8 mpnAddStoreWord := by
  constructor
  · intro s
    simp only [bodyStep, mpnAddNStep, runBlock_cons, runBlock_nil, evalInstr,
      JOperand.eval, JState.storeIdx, get_store, JState.get_setReg_same,
      JState.get_setReg_other, JState.get_writeB5W_same, get_writeB5W_other,
      x86_ADD, rflags_of_aluop, String.reduceEq, ne_eq, not_false_eq_true]
  · intro s
    simp only [bodyStep, mpnAddNStep, runBlock_cons, runBlock_nil, evalInstr,
      JOperand.eval, mem_setReg, mem_writeB5W, mem_store, JState.storeIdx,
      JState.get_setReg_other, JState.get_setReg_same, get_writeB5W_other,
      JState.get_writeB5W_same, x86_MOV, String.reduceEq, ne_eq, not_false_eq_true]
    rfl

/-! ## 4. The stored-output theorem for the deployed loop -/

/-- **The stored output cells of the runtime-N `mpn_add_n` loop.** After running
    the bounded back-edge loop `n` times from a state with limb index `i₀`, the
    output array `"rp"` holds, at each limb `k < n`, the word the trip-`k` step
    stored (`mpnAddStoreWord` of the trip-`k` state); the input arrays `"ap"`,
    `"bp"` are untouched. Composes the loop-carried write invariant with
    `MpnLoopCorrect.mpnAddN_loop_iterate` (`runBoundedLoop = n`-fold iterate).
    The non-aliasing hypothesis is that `"rp"` is distinct from `"ap"`/`"bp"`,
    which holds by construction (distinct base names). -/
theorem mpnAdd_runBounded_stored_cells (s : JState 64) (n : Nat)
    (hb : (s.get "i").toNat + n < 2 ^ 64) :
    (∀ k, k < n →
        (runBoundedLoop s n mpnAddNStep).load "rp" ((8 * ((s.get "i").toNat + k) : Nat) : Int)
          = mpnAddStoreWord ((bodyStep mpnAddNStep)^[k] s))
    ∧ (∀ (o : Int), (runBoundedLoop s n mpnAddNStep).load "ap" o = s.load "ap" o)
    ∧ (∀ (o : Int), (runBoundedLoop s n mpnAddNStep).load "bp" o = s.load "bp" o) := by
  have hspec := mpnAddNStep_storeStepSpec
  obtain ⟨hW, hU⟩ := storeIterate_writeInv hspec (by norm_num) (by norm_num) s n hb
  rw [mpnAddN_loop_iterate s n]
  refine ⟨?_, ?_, ?_⟩
  · intro k hk; simpa using hW k hk
  · intro o; simpa using hU "ap" o (Or.inl (by decide))
  · intro o; simpa using hU "bp" o (Or.inl (by decide))

/-! ## 5. The residual functional identification -/

/-- Residual value layer: the per-trip stored word `mpnAddStoreWord` realises the
    reference per-limb add `MpnLoopCorrect.refLimbAdd` — the low word of
    `a[i] + b[i] + cin`, with the carry-in read from the `"cy"` register. Isolated
    here, under its precondition, as the arithmetic identification the stored-cell
    theorem reduces the functional-correctness question to; its proof composes the
    `x86_ADD`/`x86_ADC` word semantics with `MultiLimbKernel.addLimbs_val`.
    Corroborated at `n = 4` by `MpnLoopCorrect.mpnAddN_kat_n4`. -/
def MpnAddStoredWordAgrees : Prop :=
  ∀ s : JState 64, (s.get "cy").toNat ≤ 1 →
    mpnAddStoreWord s =
      (MpnLoopCorrect.refLimbAdd (s.loadIdx "ap" "i" 8) (s.loadIdx "bp" "i" 8)
        (decide (s.get "cy" = (1 : BitVec 64)))).1

end CatCrypt.Crypto.SecureCompilation.VIR.MpnLoopStoreInvariant
