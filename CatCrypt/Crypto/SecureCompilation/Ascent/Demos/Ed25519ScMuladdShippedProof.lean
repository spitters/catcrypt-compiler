/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScMuladdCut01
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScMuladdCut02
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScMuladdCut03
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScMuladdCut04
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScMuladdCut05
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScMuladdCut06
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScMuladdCut07
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScMuladdCut08
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScMuladdCut09
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScMuladdModel
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PartChain
public meta import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519SymExec
public meta import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScMuladdModel
public meta import CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
public meta import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519ScMuladdShipped

/-!
# Correctness of the shipped `ed25519_sc_muladd` machine code

`Imported.Ed25519ScMuladdShipped.ed25519ScMuladdShippedBlock` is the body of
`ed25519_sc_muladd_x86_from_lean(u64 *s, const u64 *a, const u64 *b, const u64 *c)` as
printed by the owned backend. This module proves that it stores in the four limbs of `s`
the value `(a · b + c) mod L`, `L = 2^252 + 27742317777372353535851937790883648493`, for
every three four-limb inputs, first on the canonical block of `AddrMemDerived` under
`runBlock`, then on the address machine `runBlockA`.

The canonical block is checked part by part with the symbolic executor of
`Ed25519SymExec` (`partCheck`, `partCheck_sound`), over the nine parts of the imported
block and the abstract states `AddrMemDerived.scmState` between them. The twelve input
limbs are the slots `0 .. 11`, the constants of the reduction the slots `16 .. 24`, and the
statements of the model the slots `16 .. 433`. Each part check is cut in two at a
generated boundary certificate, in `Ed25519ScMuladdCut01` … `Cut09`, and the halves are
joined through `mapHolds_cat`; the footprint checks run by `native_decide`. The model and
the part maps are in `Ed25519ScMuladdModel`.

## Main results

* `scMuladdCanon_correct`: for every name-keyed state, the canonical block stores in the
  cells `(%rdi, 0)` … `(%rdi, 24)` the value `(a · b + c) mod L` of the four cells at each
  of `%rsi`, `%rdx` and `%rcx`.
* `scMuladdShipped_correct_addr`: the same for `runBlockA` on the imported block, when the
  cells of `scmCells` occupy pairwise disjoint eight-byte ranges.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false
set_option exponentiation.threshold 600

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScMuladdShippedProof

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519ScMuladdShipped
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof
open CatCrypt.Util (Ed25519L ed25519L_eq)


/-! ## 4. The canonical block -/

/-- The canonical block is the concatenation of the canonical parts, each from the abstract
    state after the previous part. -/
theorem canonD_scMuladd :
    canonD shippedBank ed25519ScMuladdShippedBlock =
      canonFromD shippedBank {} ed25519ScMuladdShippedPart01 ++
      (canonFromD shippedBank (scmState 1) ed25519ScMuladdShippedPart02 ++
      (canonFromD shippedBank (scmState 2) ed25519ScMuladdShippedPart03 ++
      (canonFromD shippedBank (scmState 3) ed25519ScMuladdShippedPart04 ++
      (canonFromD shippedBank (scmState 4) ed25519ScMuladdShippedPart05 ++
      (canonFromD shippedBank (scmState 5) ed25519ScMuladdShippedPart06 ++
      (canonFromD shippedBank (scmState 6) ed25519ScMuladdShippedPart07 ++
      (canonFromD shippedBank (scmState 7) ed25519ScMuladdShippedPart08 ++
      canonFromD shippedBank (scmState 8) ed25519ScMuladdShippedPart09))))))) := by
  unfold canonD ed25519ScMuladdShippedBlock
  simp only [List.append_assoc]
  rw [canonFromD_append, scMuladd_D_part01.2, canonFromD_append, scMuladd_D_part02.2,
    canonFromD_append, scMuladd_D_part03.2, canonFromD_append, scMuladd_D_part04.2,
    canonFromD_append, scMuladd_D_part05.2, canonFromD_append, scMuladd_D_part06.2,
    canonFromD_append, scMuladd_D_part07.2, canonFromD_append, scMuladd_D_part08.2]

/-- The entry slot values: slots `0 .. 3` are the cells of `%rsi`, slots `4 .. 7` those of
    `%rdx`, and slots `8 .. 11` those of `%rcx`. -/
def rhoIn (st : JState 64) (j : Nat) : BitVec 64 :=
  if j < 4 then st.mem "%rsi" ((8 * j : Nat) : Int)
  else if j < 8 then st.mem "%rdx" ((8 * (j - 4) : Nat) : Int)
  else if j < 12 then st.mem "%rcx" ((8 * (j - 8) : Nat) : Int)
  else 0

/-- The slot values of the multiply-add on the input cells of `st`. -/
def rhoM (st : JState 64) : Nat → BitVec 64 := wrun 16 mStmts (rhoIn st)

theorem mStmts_wf : wfB 16 mStmts = true := by decide +kernel

theorem mStmts_length : mStmts.length = 418 := by decide +kernel

theorem mOuts_eq : mOuts = [.v 430, .v 431, .v 432, .v 433] := by decide +kernel

theorem holds_rhoM (st : JState 64) : Holds (rhoM st) 16 mStmts :=
  holds_wrun _ _ _ mStmts_wf

theorem rhoM_const (st : JState 64) (j c : Nat) (h : cK j = some c) :
    rhoM st j = BitVec.ofNat 64 c := by
  have hH := holds_rhoM st
  have hs : mStmts = constStmts ++ (mStmts.drop 9) := by decide +kernel
  rw [hs, holds_append] at hH
  have hc : constStmts = cLits.map WE.lit := by
    simp only [constStmts, cLits, List.map_append]
  rw [hc] at hH
  unfold cK at h
  split_ifs at h with hj
  have := holds_lits_get _ cLits 16 (j - 16) c hH.1 h
  rwa [show 16 + (j - 16) = j by omega] at this

theorem scmIn_holds (st : JState 64) : MapHolds (rhoM st) scmIn st := by
  intro p hp
  simp only [scmIn, List.mem_append, List.mem_map, List.mem_range] at hp
  simp only [rhoM]
  rcases hp with (hp | hp) | hp <;> obtain ⟨k, hk, rfl⟩ := hp <;>
    simp only [Loc.val, WE.eval] <;> rw [wrun_below _ _ _ _ (by omega)] <;>
    simp only [rhoIn, Nat.add_sub_cancel_left] <;>
    [skip; skip; skip] <;> split_ifs <;> first | rfl | omega

/-- **The canonical block computes `(a · b + c) mod L`.** For every name-keyed state, the
    canonical block stores in the cells `(%rdi, 0)` … `(%rdi, 24)` the four limbs of
    `(a · b + c) mod L`, where `a`, `b` and `c` are the four-limb values of the cells at
    `%rsi`, `%rdx` and `%rcx`; the result is below `L`. -/
theorem scMuladdCanon_correct (st : JState 64) :
    bignumVal ((List.range 4).map fun i =>
        (runBlock st (canonD shippedBank ed25519ScMuladdShippedBlock)).mem "%rdi"
          ((8 * i : Nat) : Int)) =
      (bignumVal ((List.range 4).map fun i => st.mem "%rcx" ((8 * i : Nat) : Int)) +
        bignumVal ((List.range 4).map fun i => st.mem "%rsi" ((8 * i : Nat) : Int)) *
          bignumVal ((List.range 4).map fun i => st.mem "%rdx" ((8 * i : Nat) : Int)))
        % Ed25519L ∧
    bignumVal ((List.range 4).map fun i =>
        (runBlock st (canonD shippedBank ed25519ScMuladdShippedBlock)).mem "%rdi"
          ((8 * i : Nat) : Int)) < Ed25519L := by
  set ρ := rhoM st with hρ
  have hH := holds_rhoM st
  rw [← hρ] at hH
  have hK : ∀ a j c, j < a → cK j = some c → ρ j = BitVec.ofNat 64 c :=
    fun _ j c _ h => rhoM_const st j c h
  have hsl : ∀ a b, 16 ≤ a → a ≤ b → b ≤ 434 → Holds ρ a (mSlice a b) := fun a b h1 h2 h3 =>
    holds_slice ρ mStmts 16 a b hH h1 h2 (by rw [mStmts_length]; omega)
  have hK' : ∀ j c, cK j = some c → ρ j = BitVec.ofNat 64 c := fun j c h => rhoM_const st j c h
  have H := mapHolds_cat ρ
    (fun s h => scm_part01_of_halves ρ (hsl _ _ le_rfl (by omega) (by omega)) hK' s h)
    (mapHolds_cat ρ
    (fun s h => scm_part02_of_halves ρ (hsl _ _ (by omega) (by omega) (by omega)) hK' s h)
    (mapHolds_cat ρ
    (fun s h => scm_part03_of_halves ρ (hsl _ _ (by omega) (by omega) (by omega)) hK' s h)
    (mapHolds_cat ρ
    (fun s h => scm_part04_of_halves ρ (hsl _ _ (by omega) (by omega) (by omega)) hK' s h)
    (mapHolds_cat ρ
    (fun s h => scm_part05_of_halves ρ (hsl _ _ (by omega) (by omega) (by omega)) hK' s h)
    (mapHolds_cat ρ
    (fun s h => scm_part06_of_halves ρ (hsl _ _ (by omega) (by omega) (by omega)) hK' s h)
    (mapHolds_cat ρ
    (fun s h => scm_part07_of_halves ρ (hsl _ _ (by omega) (by omega) (by omega)) hK' s h)
    (mapHolds_cat ρ
    (fun s h => scm_part08_of_halves ρ (hsl _ _ (by omega) (by omega) (by omega)) hK' s h)
    (fun s h => scm_part09_of_halves ρ (hsl _ _ (by omega) (by omega) le_rfl) hK' s h))))))))
  have h9 := H st (scmIn_holds st)
  simp only [scmPart] at h9
  rw [← canonD_scMuladd] at h9
  generalize runBlock st (canonD shippedBank ed25519ScMuladdShippedBlock) = out at h9 ⊢
  have hmem : ∀ i, i < 4 → out.mem "%rdi" ((8 * i : Nat) : Int) = ρ (430 + i) := by
    intro i hi
    have := h9 (.cell "%rdi" ((8 * i : Nat) : Int), .v (430 + i))
      (by interval_cases i <;> simp [scmOut, dk])
    rw [Loc.val_cell, WE.eval_v] at this
    exact this
  have hlhs : ((List.range 4).map fun i => out.mem "%rdi" ((8 * i : Nat) : Int)) =
      mOuts.map (WE.eval ρ) := by
    rw [mOuts_eq]
    simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
      List.cons_append]
    rw [hmem 0 (by omega), hmem 1 (by omega), hmem 2 (by omega), hmem 3 (by omega)]
    simp only [WE.eval]
  have hk : (slotsFrom 0 4).map (WE.eval ρ) =
      (List.range 4).map fun i => st.mem "%rsi" ((8 * i : Nat) : Int) := by
    simp only [slotsFrom, List.map_map]
    apply List.map_congr_left
    intro i hi
    simp only [List.mem_range] at hi
    have := scmIn_holds st (.cell "%rsi" ((8 * i : Nat) : Int), .v i)
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.2 ⟨i, List.mem_range.2 hi,
        by simp⟩)))
    simpa [Loc.val, WE.eval, hρ] using this.symm
  have ha : (slotsFrom 4 4).map (WE.eval ρ) =
      (List.range 4).map fun i => st.mem "%rdx" ((8 * i : Nat) : Int) := by
    simp only [slotsFrom, List.map_map]
    apply List.map_congr_left
    intro i hi
    simp only [List.mem_range] at hi
    have := scmIn_holds st (.cell "%rdx" ((8 * i : Nat) : Int), .v (4 + i))
      (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨i, List.mem_range.2 hi,
        rfl⟩)))
    simpa [Loc.val, WE.eval, hρ] using this.symm
  have hr : (slotsFrom 8 4).map (WE.eval ρ) =
      (List.range 4).map fun i => st.mem "%rcx" ((8 * i : Nat) : Int) := by
    simp only [slotsFrom, List.map_map]
    apply List.map_congr_left
    intro i hi
    simp only [List.mem_range] at hi
    have := scmIn_holds st (.cell "%rcx" ((8 * i : Nat) : Int), .v (8 + i))
      (List.mem_append_right _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩))
    simpa [Loc.val, WE.eval, hρ] using this.symm
  have hm := muladdG_val ρ (slotsFrom 0 4) (slotsFrom 4 4) (slotsFrom 8 4) 16 hH
  rw [show (muladdG (slotsFrom 0 4) (slotsFrom 4 4) (slotsFrom 8 4) 16).2 = mOuts from rfl,
    hk, ha, hr] at hm
  rw [hlhs, hm, muladdModel_val _ _ _ (by simp) (by simp) (by simp)]
  exact ⟨rfl, Nat.mod_lt _ (by rw [ed25519L_eq]; norm_num)⟩

/-! ## 5. The address machine -/

/-- The cells the canonical block reads or writes: the four output limbs, the three times
    four input limbs, and the stack cells at offsets `-128`, `-16`, `-8` and
    `0, 8, …, 232`. -/
def scmCells : List (String × Int) :=
  (List.range 4).map (fun i => ("%rdi", ((8 * i : Nat) : Int))) ++
  (List.range 4).map (fun i => ("%rsi", ((8 * i : Nat) : Int))) ++
  (List.range 4).map (fun i => ("%rdx", ((8 * i : Nat) : Int))) ++
  (List.range 4).map (fun i => ("%rcx", ((8 * i : Nat) : Int))) ++
  (("%rsp", -128) :: ("%rsp", -16) :: ("%rsp", -8) ::
    (List.range 30).map (fun i => ("%rsp", ((8 * i : Nat) : Int))))

theorem scm_foot1 :
    footOK scmCells (canonFromD shippedBank {} ed25519ScMuladdShippedPart01) = true := by
  native_decide
theorem scm_foot2 :
    footOK scmCells (canonFromD shippedBank (scmState 1) ed25519ScMuladdShippedPart02)
      = true := by native_decide
theorem scm_foot3 :
    footOK scmCells (canonFromD shippedBank (scmState 2) ed25519ScMuladdShippedPart03)
      = true := by native_decide
theorem scm_foot4 :
    footOK scmCells (canonFromD shippedBank (scmState 3) ed25519ScMuladdShippedPart04)
      = true := by native_decide
theorem scm_foot5 :
    footOK scmCells (canonFromD shippedBank (scmState 4) ed25519ScMuladdShippedPart05)
      = true := by native_decide
theorem scm_foot6 :
    footOK scmCells (canonFromD shippedBank (scmState 5) ed25519ScMuladdShippedPart06)
      = true := by native_decide
theorem scm_foot7 :
    footOK scmCells (canonFromD shippedBank (scmState 6) ed25519ScMuladdShippedPart07)
      = true := by native_decide
theorem scm_foot8 :
    footOK scmCells (canonFromD shippedBank (scmState 7) ed25519ScMuladdShippedPart08)
      = true := by native_decide
theorem scm_foot9 :
    footOK scmCells (canonFromD shippedBank (scmState 8) ed25519ScMuladdShippedPart09)
      = true := by native_decide

theorem scm_foot : footOK scmCells (canonD shippedBank ed25519ScMuladdShippedBlock) = true := by
  rw [canonD_scMuladd]
  simp only [footOK_append, scm_foot1, scm_foot2, scm_foot3, scm_foot4, scm_foot5, scm_foot6,
    scm_foot7, scm_foot8, scm_foot9, Bool.and_self]

/-- **The shipped block computes `(a · b + c) mod L`.** When the cells of `scmCells` occupy
    pairwise disjoint eight-byte ranges, `runBlockA` of the imported block stores at
    `%rdi + 8i`, `i < 4`, the limbs of `(a · b + c) mod L`, where `a`, `b` and `c` are the
    four-limb values read at `%rsi + 8i`, `%rdx + 8i` and `%rcx + 8i`; the result is below
    `L`. -/
theorem scMuladdShipped_correct_addr (sa : AState)
    (hsep : Separated shippedBank sa.regs scmCells) :
    bignumVal ((List.range 4).map fun i =>
        read64 (runBlockA sa ed25519ScMuladdShippedBlock).mem
          (sa.regs "%rdi" + BitVec.ofInt 64 ((8 * i : Nat) : Int))) =
      (bignumVal ((List.range 4).map fun i =>
          read64 sa.mem (sa.regs "%rcx" + BitVec.ofInt 64 ((8 * i : Nat) : Int))) +
        bignumVal ((List.range 4).map fun i =>
          read64 sa.mem (sa.regs "%rsi" + BitVec.ofInt 64 ((8 * i : Nat) : Int))) *
        bignumVal ((List.range 4).map fun i =>
          read64 sa.mem (sa.regs "%rdx" + BitVec.ofInt 64 ((8 * i : Nat) : Int))))
        % Ed25519L ∧
    bignumVal ((List.range 4).map fun i =>
        read64 (runBlockA sa ed25519ScMuladdShippedBlock).mem
          (sa.regs "%rdi" + BitVec.ofInt 64 ((8 * i : Nat) : Int))) < Ed25519L := by
  obtain ⟨-, -, hK⟩ := runBlockA_simD_on shippedBank ed25519ScMuladdShippedBlock scmCells
    ed25519ScMuladd_disciplinedD
    (readsBeforeWritesFromB_of_reads _ (footOK_reads scm_foot) false)
    (footOK_writes scm_foot) sa hsep
  have hdi : shippedBank "%rdi" = some "%rdi" := by simp [shippedBank]
  have hout : ((List.range 4).map fun i =>
        read64 (runBlockA sa ed25519ScMuladdShippedBlock).mem
          (sa.regs "%rdi" + BitVec.ofInt 64 ((8 * i : Nat) : Int))) =
      (List.range 4).map fun i =>
        (runBlock (jOf shippedBank sa) (canonD shippedBank ed25519ScMuladdShippedBlock)).mem
          "%rdi" ((8 * i : Nat) : Int) := by
    apply List.map_congr_left
    intro i hi
    have hmem : ("%rdi", ((8 * i : Nat) : Int)) ∈ scmCells :=
      List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_map.2 ⟨i, hi, rfl⟩))))
    rw [← hK _ hmem, absMem_shipped _ _ _ _ hdi]
  have hin : ∀ b : String, shippedBank b = some b →
      ((List.range 4).map fun i =>
        read64 sa.mem (sa.regs b + BitVec.ofInt 64 ((8 * i : Nat) : Int))) =
      (List.range 4).map fun i => (jOf shippedBank sa).mem b ((8 * i : Nat) : Int) := by
    intro b hb
    apply List.map_congr_left
    intro i _
    simp only [jOf]
    rw [absMem_shipped _ _ _ _ hb]
  rw [hout, hin "%rsi" (by simp [shippedBank]), hin "%rdx" (by simp [shippedBank]),
    hin "%rcx" (by simp [shippedBank])]
  exact scMuladdCanon_correct (jOf shippedBank sa)

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScMuladdShippedProof
