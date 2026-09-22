/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof
public import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519ScMuladdShipped

/-!
# Correctness of the shipped `ed25519_sc_muladd` machine code

`Imported.Ed25519ScMuladdShipped.ed25519ScMuladdShippedBlock` is the body of
`ed25519_sc_muladd_x86_from_lean(u64 *s, const u64 *a, const u64 *b, const u64 *c)` as
printed by the owned backend. This module proves that it stores in the four limbs of `s`
the value `(a · b + c) mod L`, `L = 2^252 + 27742317777372353535851937790883648493`, for
every three four-limb inputs, first on the canonical block of `AddrMemDerived` under
`runBlock`, then on the address machine `runBlockA`.

## The algorithm

`muladdModel k a r` is the schoolbook product `r + k · a` on eight 64-bit words followed by
the Barrett reduction `reduceModel` of `Ed25519ScReduceShippedProof`. The word model and
its correctness statement are those of `CatCrypt.Crypto.EdDSA.Ed25519ScalarEmit`
(`muladdModel`, `muladdModel_val`), from which the machine code is compiled; the compiler
package does not depend on that module, so they are restated here over the definitions of
`Ed25519ScReduceShippedProof`.

`muladdG` produces the single-assignment word statements of the model over numbered slots:
the nine constant slots of `constStmts`, the multiply-accumulate sweep of the product, and
then the four phases of the reduction. `muladdG_val` states that the result handles denote
`muladdModel`.

## The machine code

The canonical block is checked part by part with the hash-consed value-table symbolic
executor of `Ed25519ScReduceShippedProof` (`partCheck`, `partCheck_sound`), over the nine
parts of the imported block and the abstract states `AddrMemDerived.scmState` between them.
The twelve input limbs are the slots `0 .. 11`, the constants of the reduction the slots
`16 .. 24`, and the statements of the model the slots `16 .. 433`; each part check is
closed by `decide +kernel`.

## Main results

* `muladdModel_val`: the word model computes `(r + k · a) mod L`.
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

/-! ## 1. The word model -/

/-- The multiply-add `r + k · a` followed by the Barrett reduction, on the word model. -/
def muladdModel (k a r : List (BitVec 64)) : List (BitVec 64) := reduceModel (mulRows k a r)

/-- The multiply-add model computes `(r + k · a) mod L`. -/
theorem muladdModel_val (k a r : List (BitVec 64)) (hk : k.length = 4) (ha : a.length = 4)
    (hr : r.length = 4) :
    bignumVal (muladdModel k a r) = (bignumVal r + bignumVal k * bignumVal a) % Ed25519L := by
  simp only [muladdModel]
  rw [reduceModel_val _ (by rw [mulRows_length _ _ _ (by omega)]; omega),
    mulRows_val _ _ _ (by omega) (by omega)]

/-! ## 2. The statement generator -/

/-- The generator of `muladdModel` over three times four input handles: the constant slots
    `n .. n + 8`, then the product from slot `n + 9`, then the reduction. -/
def muladdG (k a r : List WE) (n : Nat) : List WE × List WE :=
  let r0 := mulRowsG k a r (n + 9)
  let m0 := n + 9 + r0.1.length
  let r1 := mulRowsG r0.2 (slotsFrom n 5) (List.replicate 5 (.lit 0)) m0
  let m1 := m0 + r1.1.length
  let r2 := mulRowsG (r1.2.drop 8) (slotsFrom (n + 5) 4) (List.replicate 4 (.lit 0)) m1
  let m2 := m1 + r2.1.length
  let r3 := addLimbsG (r0.2.take 4) ((r2.2.take 4).map notW) (.lit 1) m2
  let m3 := m2 + r3.1.length
  let r4 := condSubG r3.2.dropLast (slotsFrom (n + 5) 4) m3
  (constStmts ++ (r0.1 ++ (r1.1 ++ (r2.1 ++ (r3.1 ++ r4.1)))), r4.2)

theorem muladdG_val (ρ : Nat → BitVec 64) (k a r : List WE) (n : Nat)
    (h : Holds ρ n (muladdG k a r n).1) :
    (muladdG k a r n).2.map (WE.eval ρ)
      = muladdModel (k.map (WE.eval ρ)) (a.map (WE.eval ρ)) (r.map (WE.eval ρ)) := by
  simp only [muladdG, muladdModel] at h ⊢
  rw [holds_append, holds_append, holds_append, holds_append, holds_append] at h
  obtain ⟨hc, h0, h1, h2, h3, h4⟩ := h
  rw [constStmts_length] at h0 h1 h2 h3 h4
  obtain ⟨hmu, hp⟩ := constStmts_eval ρ n hc
  rw [condSubG_val ρ _ _ _ h4, hp, List.map_dropLast, addLimbsG_val ρ _ _ _ _ h3,
    notW_map, List.map_take, List.map_take, mulRowsG_val ρ _ _ _ _ h2, List.map_drop,
    mulRowsG_val ρ _ _ _ _ h1, hmu, hp, zeros_eval, zeros_eval,
    mulRowsG_val ρ _ _ _ _ h0]
  rfl

/-! ## 3. The nine parts of `ed25519_sc_muladd` -/

/-- The statements of the multiply-add over the input slots `0 .. 11`, from slot `16`. -/
def mStmts : List WE := (muladdG (slotsFrom 0 4) (slotsFrom 4 4) (slotsFrom 8 4) 16).1

/-- The four result handles of the multiply-add. -/
def mOuts : List WE := (muladdG (slotsFrom 0 4) (slotsFrom 4 4) (slotsFrom 8 4) 16).2

/-- The statements of slots `a .. b - 1`. -/
def mSlice (a b : Nat) : List WE := (mStmts.drop (a - 16)).take (b - a)

/-- The twelve input limbs: cell `(%rsi, 8k)` holds slot `k`, cell `(%rdx, 8k)` slot
    `4 + k`, and cell `(%rcx, 8k)` slot `8 + k`. -/
def scmIn : List (Loc × WE) :=
  (List.range 4).map (fun k => (Loc.cell "%rsi" ((8 * k : Nat) : Int), WE.v k)) ++
  (List.range 4).map (fun k => (Loc.cell "%rdx" ((8 * k : Nat) : Int), WE.v (4 + k))) ++
  (List.range 4).map (fun k => (Loc.cell "%rcx" ((8 * k : Nat) : Int), WE.v (8 + k)))

/-- The four output limbs: cell `(%rdi, 8i)` holds slot `430 + i`. -/
def scmOut : List (Loc × WE) := [dk 0 430, dk 8 431, dk 16 432, dk 24 433]

/-- The stack cells holding the loop indices. -/
def scmIdx : List (Loc × WE) :=
  [sk 168 (.lit 3), sk 160 (.lit 2), sk 152 (.lit 1), sk 144 (.lit 0)]

/-- The stack cells holding the four limbs of `L`, the constant slots `21 .. 24`. -/
def scmL : List (Loc × WE) :=
  [sk 104 (.v 24), sk 112 (.v 23), sk 120 (.v 22), sk 128 (.v 21)]

/-- The stack cells holding the five limbs of the Barrett constant, the constant slots
    `16 .. 20`. -/
def scmMu : List (Loc × WE) :=
  [sk 40 (.v 20), sk 32 (.v 19), sk 24 (.v 18), sk 16 (.v 17), sk 8 (.v 16)]

/-- The locations after part 1. -/
def scmMap1 : List (Loc × WE) :=
  [rg "%rbx" (.v 67), rg "%rsi" (.v 66), rg "%rcx" (.v 65), rg "%rax" (.v 64),
    rg "%r9" (.v 63), rg "%r10" (.v 58), rg "%r12" (.v 53),
    sk 72 (.v 68), sk 64 (.v 48), sk 96 (.v 28), sk 128 (.v 7), sk 112 (.v 6),
    sk 104 (.v 5), sk 88 (.v 4), sk 120 (.v 3), sk 80 (.v 2)] ++ scmIdx

/-- The locations after part 2. The constant slot `19` is the all-ones word. -/
def scmMap2 : List (Loc × WE) :=
  [rg "%rax" (.and (.xor (.lit 0) (.v 112)) (notW (.v 113))),
    rg "%r8" (.and (.lit 0) (.v 112)),
    rg "%rbp" (.add (.v 111) (cw (.v 112) (.v 109) (.v 110))),
    rg "%rbx" (.v 113),
    rg "%rcx" (.add (.v 101) (cw (.v 102) (.v 99) (.v 100)))] ++ scmL ++ scmMu ++
  [sk 80 (.v 104), sk 56 (.v 103), sk 48 (.v 98), sk 0 (.v 93), sk 88 (.v 88),
    sk 72 (.v 68), sk 64 (.v 48), sk 96 (.v 28)] ++ scmIdx

/-- The locations after part 3. -/
def scmMap3 : List (Loc × WE) :=
  [rg "%rsi" (.v 164), rg "%r11" (.v 163), rg "%rax" (.v 154), rg "%r8" (.v 153),
    rg "%r9" (.v 148)] ++ scmL ++ scmMu ++
  [sk 80 (.v 104), sk 56 (.v 103), sk 48 (.v 98), sk 0 (.v 93), sk 88 (.v 88),
    sk 72 (.v 68), sk 64 (.v 48), sk 96 (.v 28)] ++ scmIdx

/-- The locations after part 4. -/
def scmMap4 : List (Loc × WE) :=
  [rg "%rcx" (.v 218), rg "%rbp" (.v 217), rg "%rdi" (.v 216), rg "%rsi" (.v 215),
    rg "%rbx" (.v 214), rg "%r11" (.v 213), rg "%rax" (.v 204), rg "%r8" (.v 203),
    rg "%r9" (.v 198)] ++ scmL ++ scmMu ++
  [sk 80 (.v 104), sk 56 (.v 103), sk 48 (.v 98), sk 0 (.v 93), sk 88 (.v 88),
    sk 72 (.v 68), sk 64 (.v 48), sk 96 (.v 28)] ++ scmIdx

/-- The locations after part 5. -/
def scmMap5 : List (Loc × WE) :=
  [rg "%rcx" (.v 266), rg "%rbx" (cw (.v 267) (.v 264) (.v 265)), rg "%r10" (.v 268),
    rg "%rbp" (.v 267), rg "%r11" (.v 263), rg "%rax" (.v 254), rg "%r8" (.v 253),
    rg "%r9" (.v 248)] ++ scmL ++ scmMu ++
  [sk 80 (.v 104), sk 56 (.v 103), sk 88 (.v 88), sk 72 (.v 68), sk 64 (.v 48),
    sk 96 (.v 28)] ++ scmIdx

/-- The locations after part 6. -/
def scmMap6 : List (Loc × WE) :=
  [rg "%rbp" (.v 317), rg "%rbx" (.lit 0), rg "%rdi" (.and (.lit 0) (.v 317)),
    rg "%rax" (.add (.v 316) (cw (.v 317) (.v 314) (.v 315))), rg "%rsi" (.v 318),
    rg "%rcx" (.v 313), rg "%r9" (.v 298), rg "%r10" (.v 293), rg "%r11" (.v 288),
    sk 80 (.v 308), sk 56 (.v 304), sk 40 (.v 303)] ++ scmL ++
  [sk 88 (.v 88), sk 72 (.v 68), sk 64 (.v 48), sk 96 (.v 28)] ++ scmIdx

/-- The locations after part 7. -/
def scmMap7 : List (Loc × WE) :=
  [rg "%rsi" (.xor (.and (.v 353) (.v 367)) (.and (.xor (.v 353) (.v 367)) (notW (.v 368)))),
    rg "%rdi" (.add (.v 366) (cw (.v 367) (.lit 0) (.v 365))),
    rg "%rax" (.v 364), rg "%r9" (.v 363), rg "%r11" (.v 358), rg "%rbp" (.v 348),
    sk 32 (.v 368), sk 48 (.v 328), sk 80 (.v 308), sk 56 (.v 304), sk 40 (.v 303)] ++
  scmL ++ [sk 88 (.v 88), sk 72 (.v 68), sk 64 (.v 48), sk 96 (.v 28)] ++ scmIdx

/-- The locations after part 8. -/
def scmMap8 : List (Loc × WE) :=
  [rg "%r9" (.xor (.v 88) (notW (.v 368))), rg "%rcx" (.and (.v 88) (notW (.v 368))),
    rg "%rbp" (.v 415), rg "%rsi" (.v 414), rg "%rbx" (.v 413), rg "%r8" (.v 412),
    rg "%rdi" (.v 409), rg "%rax" (.v 406)] ++ scmL ++ scmIdx

theorem scm_part1 :
    partCheck 16 (mSlice 16 69) scmIn scmMap1
      (canonFromD shippedBank {} ed25519ScMuladdShippedPart01) = true := by
  decide +kernel

theorem scm_part2 :
    partCheck 69 (mSlice 69 114) scmMap1 scmMap2
      (canonFromD shippedBank (scmState 1) ed25519ScMuladdShippedPart02) = true := by
  decide +kernel

theorem scm_part3 :
    partCheck 114 (mSlice 114 165) scmMap2 scmMap3
      (canonFromD shippedBank (scmState 2) ed25519ScMuladdShippedPart03) = true := by
  decide +kernel

theorem scm_part4 :
    partCheck 165 (mSlice 165 219) scmMap3 scmMap4
      (canonFromD shippedBank (scmState 3) ed25519ScMuladdShippedPart04) = true := by
  decide +kernel

theorem scm_part5 :
    partCheck 219 (mSlice 219 269) scmMap4 scmMap5
      (canonFromD shippedBank (scmState 4) ed25519ScMuladdShippedPart05) = true := by
  decide +kernel

theorem scm_part6 :
    partCheck 269 (mSlice 269 319) scmMap5 scmMap6
      (canonFromD shippedBank (scmState 5) ed25519ScMuladdShippedPart06) = true := by
  decide +kernel

theorem scm_part7 :
    partCheck 319 (mSlice 319 369) scmMap6 scmMap7
      (canonFromD shippedBank (scmState 6) ed25519ScMuladdShippedPart07) = true := by
  decide +kernel

theorem scm_part8 :
    partCheck 369 (mSlice 369 416) scmMap7 scmMap8
      (canonFromD shippedBank (scmState 7) ed25519ScMuladdShippedPart08) = true := by
  decide +kernel

theorem scm_part9 :
    partCheck 416 (mSlice 416 434) scmMap8 scmOut
      (canonFromD shippedBank (scmState 8) ed25519ScMuladdShippedPart09) = true := by
  decide +kernel

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
  have h1 := partCheck_sound _ _ _ _ _ scm_part1 ρ (hsl _ _ le_rfl (by omega) (by omega))
    (hK 16) st (scmIn_holds st)
  have h2 := partCheck_sound _ _ _ _ _ scm_part2 ρ (hsl _ _ (by omega) (by omega) (by omega))
    (hK 69) _ h1
  have h3 := partCheck_sound _ _ _ _ _ scm_part3 ρ (hsl _ _ (by omega) (by omega) (by omega))
    (hK 114) _ h2
  have h4 := partCheck_sound _ _ _ _ _ scm_part4 ρ (hsl _ _ (by omega) (by omega) (by omega))
    (hK 165) _ h3
  have h5 := partCheck_sound _ _ _ _ _ scm_part5 ρ (hsl _ _ (by omega) (by omega) (by omega))
    (hK 219) _ h4
  have h6 := partCheck_sound _ _ _ _ _ scm_part6 ρ (hsl _ _ (by omega) (by omega) (by omega))
    (hK 269) _ h5
  have h7 := partCheck_sound _ _ _ _ _ scm_part7 ρ (hsl _ _ (by omega) (by omega) (by omega))
    (hK 319) _ h6
  have h8 := partCheck_sound _ _ _ _ _ scm_part8 ρ (hsl _ _ (by omega) (by omega) (by omega))
    (hK 369) _ h7
  have h9 := partCheck_sound _ _ _ _ _ scm_part9 ρ (hsl _ _ (by omega) (by omega) le_rfl)
    (hK 416) _ h8
  clear h1 h2 h3 h4 h5 h6 h7 h8
  simp only [← runBlock_cat, List.append_assoc] at h9
  rw [← canonD_scMuladd] at h9
  generalize runBlock st (canonD shippedBank ed25519ScMuladdShippedBlock) = out at h9 ⊢
  have hmem : ∀ i, i < 4 → out.mem "%rdi" ((8 * i : Nat) : Int) = ρ (430 + i) := by
    intro i hi
    have := h9 (.cell "%rdi" ((8 * i : Nat) : Int), .v (430 + i))
      (by interval_cases i <;> simp [scmOut, dk])
    simpa only [Loc.val, WE.eval] using this
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
  decide +kernel
theorem scm_foot2 :
    footOK scmCells (canonFromD shippedBank (scmState 1) ed25519ScMuladdShippedPart02)
      = true := by decide +kernel
theorem scm_foot3 :
    footOK scmCells (canonFromD shippedBank (scmState 2) ed25519ScMuladdShippedPart03)
      = true := by decide +kernel
theorem scm_foot4 :
    footOK scmCells (canonFromD shippedBank (scmState 3) ed25519ScMuladdShippedPart04)
      = true := by decide +kernel
theorem scm_foot5 :
    footOK scmCells (canonFromD shippedBank (scmState 4) ed25519ScMuladdShippedPart05)
      = true := by decide +kernel
theorem scm_foot6 :
    footOK scmCells (canonFromD shippedBank (scmState 5) ed25519ScMuladdShippedPart06)
      = true := by decide +kernel
theorem scm_foot7 :
    footOK scmCells (canonFromD shippedBank (scmState 6) ed25519ScMuladdShippedPart07)
      = true := by decide +kernel
theorem scm_foot8 :
    footOK scmCells (canonFromD shippedBank (scmState 7) ed25519ScMuladdShippedPart08)
      = true := by decide +kernel
theorem scm_foot9 :
    footOK scmCells (canonFromD shippedBank (scmState 8) ed25519ScMuladdShippedPart09)
      = true := by decide +kernel

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
