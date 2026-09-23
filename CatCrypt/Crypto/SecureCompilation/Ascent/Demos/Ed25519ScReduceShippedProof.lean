/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceCut01
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceCut02
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceCut03
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceCut04
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceCut05
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceCut06
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceCut07
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PartChain
public meta import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519SymExec
public meta import CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
public meta import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519ScReduceShipped

/-!
# Correctness of the shipped `ed25519_sc_reduce` machine code

`Imported.Ed25519ScReduceShipped.ed25519ScReduceShippedBlock` is the body of
`ed25519_sc_reduce_x86_from_lean(u64 *out, const u64 *x)` as printed by the owned
backend. This module proves that it stores in the four limbs of `out` the value
`x mod L`, `L = 2^252 + 27742317777372353535851937790883648493`, for every eight-limb
input `x`, first on the canonical block of `AddrMemDerived` under `runBlock`, then on the
address machine `runBlockA`.

The canonical block is checked part by part, over the eight parts of the imported block
and the abstract states `AddrMemDerived.scrState` between them. `Ed25519SymExec` carries
the symbolic executor, the part-check soundness theorem and the word model; the checks
here are `native_decide`, one per part.

The global slot function is the run `wrun` of the statements from the input limbs; the
statements read only earlier slots (`xStmts_wf`), so `wrun` satisfies them
(`holds_wrun`).

Each check reduces a symbolic run of a whole part in the kernel and costs gigabytes, so
this module is listed in `scripts/ci-only-modules.txt`.

## Main results

* `scReduceCanon_correct`: for every name-keyed state, the canonical block stores in the
  cells `(%rdi, 0)` … `(%rdi, 24)` the value `x mod L` of the eight cells
  `(%rsi, 0)` … `(%rsi, 56)`.
* `scReduceShipped_correct_addr`: the same for `runBlockA` on the imported block, when
  the cells of `scrCells` (the stack cells the block uses and the input and output limbs)
  occupy pairwise disjoint eight-byte ranges.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false
set_option exponentiation.threshold 600

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519ScReduceShipped
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
open CatCrypt.Crypto.SecureCompilation.FieldReduceIdioms
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMontMulCiosWordModel
open CatCrypt.Util (Ed25519L ed25519L_eq)


theorem scr_part8 :
    partCheck 354 (xSlice 354 354) scrOut scrOut
      (canonFromD shippedBank (scrState 7) ed25519ScReduceShippedPart08) = true := by
  native_decide

/-! ## 9. The canonical block -/

/-- The canonical block is the concatenation of the canonical parts, each from the abstract
    state after the previous part. -/
theorem canonD_scReduce :
    canonD shippedBank ed25519ScReduceShippedBlock =
      canonFromD shippedBank {} ed25519ScReduceShippedPart01 ++
      (canonFromD shippedBank (scrState 1) ed25519ScReduceShippedPart02 ++
      (canonFromD shippedBank (scrState 2) ed25519ScReduceShippedPart03 ++
      (canonFromD shippedBank (scrState 3) ed25519ScReduceShippedPart04 ++
      (canonFromD shippedBank (scrState 4) ed25519ScReduceShippedPart05 ++
      (canonFromD shippedBank (scrState 5) ed25519ScReduceShippedPart06 ++
      (canonFromD shippedBank (scrState 6) ed25519ScReduceShippedPart07 ++
      canonFromD shippedBank (scrState 7) ed25519ScReduceShippedPart08)))))) := by
  unfold canonD ed25519ScReduceShippedBlock
  simp only [List.append_assoc]
  rw [canonFromD_append, scReduce_D_part01.2, canonFromD_append, scReduce_D_part02.2,
    canonFromD_append, scReduce_D_part03.2, canonFromD_append, scReduce_D_part04.2,
    canonFromD_append, scReduce_D_part05.2, canonFromD_append, scReduce_D_part06.2,
    canonFromD_append, scReduce_D_part07.2]

/-- The entry slot values: slot `8 + k` is input cell `(%rsi, 8k)`. -/
def rho0 (st : JState 64) (j : Nat) : BitVec 64 :=
  if 8 ≤ j ∧ j < 16 then st.mem "%rsi" ((8 * (j - 8) : Nat) : Int) else 0

/-- The slot values of the reduction on the input cells of `st`. -/
def rhoX (st : JState 64) : Nat → BitVec 64 := wrun 16 xStmts (rho0 st)

theorem xStmts_wf : wfB 16 xStmts = true := by native_decide

theorem xStmts_length : xStmts.length = 338 := by native_decide

theorem xOuts_eq : xOuts = [.v 350, .v 351, .v 352, .v 353] := by native_decide

theorem holds_rhoX (st : JState 64) : Holds (rhoX st) 16 xStmts :=
  holds_wrun _ _ _ xStmts_wf


theorem rhoX_const (st : JState 64) (j c : Nat) (h : cK j = some c) :
    rhoX st j = BitVec.ofNat 64 c := by
  have hH := holds_rhoX st
  have hs : xStmts = constStmts ++ (xStmts.drop 9) := by native_decide
  rw [hs, holds_append] at hH
  have hc : constStmts = cLits.map WE.lit := by
    simp only [constStmts, cLits, List.map_append]
  rw [hc] at hH
  unfold cK at h
  split_ifs at h with hj
  have := holds_lits_get _ cLits 16 (j - 16) c hH.1 h
  rwa [show 16 + (j - 16) = j by omega] at this

theorem scrIn_holds (st : JState 64) : MapHolds (rhoX st) scrIn st := by
  intro p hp
  simp only [scrIn, List.mem_map, List.mem_range] at hp
  obtain ⟨k, hk, rfl⟩ := hp
  simp only [Loc.val, WE.eval, rhoX]
  rw [wrun_below _ _ _ _ (by omega)]
  rw [rho0, if_pos (by omega), Nat.add_sub_cancel_left]

/-- **The canonical block computes `x mod L`.** For every name-keyed state, the canonical
    block stores in the cells `(%rdi, 0)` … `(%rdi, 24)` the four limbs of `x mod L`, where
    `x` is the eight-limb value of the cells `(%rsi, 0)` … `(%rsi, 56)`; the result is
    below `L`. -/
theorem scReduceCanon_correct (st : JState 64) :
    bignumVal ((List.range 4).map fun i =>
        (runBlock st (canonD shippedBank ed25519ScReduceShippedBlock)).mem "%rdi"
          ((8 * i : Nat) : Int)) =
      bignumVal ((List.range 8).map fun i => st.mem "%rsi" ((8 * i : Nat) : Int)) % Ed25519L ∧
    bignumVal ((List.range 4).map fun i =>
        (runBlock st (canonD shippedBank ed25519ScReduceShippedBlock)).mem "%rdi"
          ((8 * i : Nat) : Int)) < Ed25519L := by
  set ρ := rhoX st with hρ
  have hH := holds_rhoX st
  rw [← hρ] at hH
  have hK : ∀ a j c, j < a → cK j = some c → ρ j = BitVec.ofNat 64 c :=
    fun _ j c _ h => rhoX_const st j c h
  have hsl : ∀ a b, 16 ≤ a → a ≤ b → b ≤ 354 → Holds ρ a (xSlice a b) := fun a b h1 h2 h3 =>
    holds_slice ρ xStmts 16 a b hH h1 h2 (by rw [xStmts_length]; omega)
  have hK' : ∀ j c, cK j = some c → ρ j = BitVec.ofNat 64 c := fun j c h => rhoX_const st j c h
  have H := mapHolds_cat ρ
    (fun s h => scr_part01_of_halves ρ (hsl _ _ le_rfl (by omega) (by omega)) hK' s h)
    (mapHolds_cat ρ
    (fun s h => scr_part02_of_halves ρ (hsl _ _ (by omega) (by omega) (by omega)) hK' s h)
    (mapHolds_cat ρ
    (fun s h => scr_part03_of_halves ρ (hsl _ _ (by omega) (by omega) (by omega)) hK' s h)
    (mapHolds_cat ρ
    (fun s h => scr_part04_of_halves ρ (hsl _ _ (by omega) (by omega) (by omega)) hK' s h)
    (mapHolds_cat ρ
    (fun s h => scr_part05_of_halves ρ (hsl _ _ (by omega) (by omega) (by omega)) hK' s h)
    (mapHolds_cat ρ
    (fun s h => scr_part06_of_halves ρ (hsl _ _ (by omega) (by omega) (by omega)) hK' s h)
    (mapHolds_cat ρ
    (fun s h => scr_part07_of_halves ρ (hsl _ _ (by omega) (by omega) (by omega)) hK' s h)
    (fun s h => partCheck_sound _ _ _ _ _ scr_part8 ρ (hsl _ _ (by omega) le_rfl le_rfl)
      (hK 354) s h)))))))
  have h8 := H st (scrIn_holds st)
  simp only [scrPart] at h8
  rw [← canonD_scReduce] at h8
  generalize runBlock st (canonD shippedBank ed25519ScReduceShippedBlock) = out at h8 ⊢
  have hmem : ∀ i, i < 4 → out.mem "%rdi" ((8 * i : Nat) : Int) = ρ (350 + i) := by
    intro i hi
    have := h8 (.cell "%rdi" ((8 * i : Nat) : Int), .v (350 + i))
      (by interval_cases i <;> simp [scrOut, dk])
    rw [Loc.val_cell, WE.eval_v] at this
    exact this
  have hlhs : ((List.range 4).map fun i => out.mem "%rdi" ((8 * i : Nat) : Int)) =
      xOuts.map (WE.eval ρ) := by
    rw [xOuts_eq]
    simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
      List.cons_append]
    rw [hmem 0 (by omega), hmem 1 (by omega), hmem 2 (by omega), hmem 3 (by omega)]
    simp only [WE.eval]
  have hx : (slotsFrom 8 8).map (WE.eval ρ) =
      (List.range 8).map fun i => st.mem "%rsi" ((8 * i : Nat) : Int) := by
    simp only [slotsFrom, List.map_map]
    apply List.map_congr_left
    intro i hi
    simp only [List.mem_range] at hi
    have := scrIn_holds st (.cell "%rsi" ((8 * i : Nat) : Int), .v (8 + i))
      (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)
    simpa [Loc.val, WE.eval, hρ] using this.symm
  have hr := reduceG_val ρ (slotsFrom 8 8) 16 hH
  rw [show (reduceG (slotsFrom 8 8) 16).2 = xOuts from rfl, hx] at hr
  rw [hlhs, hr, reduceModel_val _ (by simp)]
  exact ⟨rfl, Nat.mod_lt _ (by rw [ed25519L_eq]; norm_num)⟩

/-! ## 10. The address machine -/

/-- The cells the canonical block reads or writes: the four output limbs, the eight input
    limbs, and the stack cells at offsets `-128` and `0, 8, …, 232`. -/
def scrCells : List (String × Int) :=
  (List.range 4).map (fun i => ("%rdi", ((8 * i : Nat) : Int))) ++
    (List.range 8).map (fun i => ("%rsi", ((8 * i : Nat) : Int))) ++
    (("%rsp", -128) :: (List.range 30).map (fun i => ("%rsp", ((8 * i : Nat) : Int))))


theorem scr_foot1 : footOK scrCells (canonFromD shippedBank {} ed25519ScReduceShippedPart01) =
    true := by native_decide
theorem scr_foot2 :
    footOK scrCells (canonFromD shippedBank (scrState 1) ed25519ScReduceShippedPart02) = true := by
  native_decide
theorem scr_foot3 :
    footOK scrCells (canonFromD shippedBank (scrState 2) ed25519ScReduceShippedPart03) = true := by
  native_decide
theorem scr_foot4 :
    footOK scrCells (canonFromD shippedBank (scrState 3) ed25519ScReduceShippedPart04) = true := by
  native_decide
theorem scr_foot5 :
    footOK scrCells (canonFromD shippedBank (scrState 4) ed25519ScReduceShippedPart05) = true := by
  native_decide
theorem scr_foot6 :
    footOK scrCells (canonFromD shippedBank (scrState 5) ed25519ScReduceShippedPart06) = true := by
  native_decide
theorem scr_foot7 :
    footOK scrCells (canonFromD shippedBank (scrState 6) ed25519ScReduceShippedPart07) = true := by
  native_decide
theorem scr_foot8 :
    footOK scrCells (canonFromD shippedBank (scrState 7) ed25519ScReduceShippedPart08) = true := by
  native_decide

theorem scr_foot : footOK scrCells (canonD shippedBank ed25519ScReduceShippedBlock) = true := by
  rw [canonD_scReduce]
  simp only [footOK_append, scr_foot1, scr_foot2, scr_foot3, scr_foot4, scr_foot5, scr_foot6,
    scr_foot7, scr_foot8, Bool.and_self]

/-- **The shipped block computes `x mod L`.** When the cells of `scrCells` (the four output
    limbs at `%rdi`, the eight input limbs at `%rsi`, and the stack cells at `%rsp` offsets
    `-128` and `0, 8, …, 232`) occupy pairwise disjoint eight-byte ranges, `runBlockA` of the
    imported block stores at `%rdi + 8i`, `i < 4`, the limbs of `x mod L`, where `x` is the
    eight-limb value read at `%rsi + 8i`, `i < 8`; the result is below `L`. -/
theorem scReduceShipped_correct_addr (sa : AState)
    (hsep : Separated shippedBank sa.regs scrCells) :
    bignumVal ((List.range 4).map fun i =>
        read64 (runBlockA sa ed25519ScReduceShippedBlock).mem
          (sa.regs "%rdi" + BitVec.ofInt 64 ((8 * i : Nat) : Int))) =
      bignumVal ((List.range 8).map fun i =>
        read64 sa.mem (sa.regs "%rsi" + BitVec.ofInt 64 ((8 * i : Nat) : Int))) % Ed25519L ∧
    bignumVal ((List.range 4).map fun i =>
        read64 (runBlockA sa ed25519ScReduceShippedBlock).mem
          (sa.regs "%rdi" + BitVec.ofInt 64 ((8 * i : Nat) : Int))) < Ed25519L := by
  obtain ⟨-, -, hK⟩ := runBlockA_simD_on shippedBank ed25519ScReduceShippedBlock scrCells
    ed25519ScReduce_disciplinedD
    (readsBeforeWritesFromB_of_reads _ (footOK_reads scr_foot) false)
    (footOK_writes scr_foot) sa hsep
  have hdi : shippedBank "%rdi" = some "%rdi" := by simp [shippedBank]
  have hsi : shippedBank "%rsi" = some "%rsi" := by simp [shippedBank]
  have hout : ((List.range 4).map fun i =>
        read64 (runBlockA sa ed25519ScReduceShippedBlock).mem
          (sa.regs "%rdi" + BitVec.ofInt 64 ((8 * i : Nat) : Int))) =
      (List.range 4).map fun i =>
        (runBlock (jOf shippedBank sa) (canonD shippedBank ed25519ScReduceShippedBlock)).mem
          "%rdi" ((8 * i : Nat) : Int) := by
    apply List.map_congr_left
    intro i hi
    have hmem : ("%rdi", ((8 * i : Nat) : Int)) ∈ scrCells :=
      List.mem_append_left _ (List.mem_append_left _ (List.mem_map.2 ⟨i, hi, rfl⟩))
    rw [← hK _ hmem, absMem_shipped _ _ _ _ hdi]
  have hin : ((List.range 8).map fun i =>
        read64 sa.mem (sa.regs "%rsi" + BitVec.ofInt 64 ((8 * i : Nat) : Int))) =
      (List.range 8).map fun i => (jOf shippedBank sa).mem "%rsi" ((8 * i : Nat) : Int) := by
    apply List.map_congr_left
    intro i _
    simp only [jOf]
    rw [absMem_shipped _ _ _ _ hsi]
  rw [hout, hin]
  exact scReduceCanon_correct (jOf shippedBank sa)

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof
