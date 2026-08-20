/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontDenote
import CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelectAdequacy

/-!
# The 12-cell frame round trip of the secp256k1 point-op front

`Secp256k1PointOpFront.loadField` reads four `u64` cells of a memref frame and
splits each into two 32-bit half-limbs; `storeField` recombines eight half-limbs
into four `u64` cells and writes them back. This module runs both through the
scalar waist semantics `semScalar` and ties them together.

Each generator is a `seqAll` of a `List.map` / `List.flatMap` over
`List.range 4`, so each block is handled by one lemma over an arbitrary index
list, chained with `Secp256k1PointOpFrontDenote.semScalar_seqAll_cons`. No
command list is reduced to a literal.

## Main results

* `half_recombine`, `half_toNat` — the word and `Nat` forms of the 32-bit split
  `(u &&& 2^32-1) + ((u >>> 32) <<< 32) = u`.
* `semScalar_arrLoadList`, `semScalar_halfSplitList`,
  `semScalar_recombineStoreList` — the waist semantics of the three uniform
  command blocks the two generators emit, over an arbitrary index list.
* `semScalar_loadField` — `loadField`'s eight half-limb slots hold the low and
  high halves of the four cells it read.
* `semScalar_storeField` — `storeField` leaves `out` holding the fourfold
  `memSetDyn` of the recombined half-limbs.
* `loadField_storeField_frame` — `storeField` after `loadField` writes back the
  four cells `loadField` read.
* `feVal_of_halves`, `feVal_of_loadField` — the half-limb residue readout
  `feVal` of a loaded field element is the little-endian value of the four
  frame cells.
-/

namespace CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrameRoundTrip

open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr Located TowerType)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms (tmpName)
open CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelectAdequacy
  (semScalar_setExpr_eq)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFront
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontCovered
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront (seqAll sv mask32)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontDenote
  (feVal semScalar_seqAll_cons semScalar_seqAll_append)
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA (encodeTy)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (memGetDyn memSetDyn)

/-! ## 1. The two 32-bit halves of a 64-bit word -/

/-- The high half of a word, read as a `Nat`. -/
theorem half_hi (u : BitVec 64) : (u >>> 32).toNat = u.toNat / 2 ^ 32 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- The low half of a word, read as a `Nat`. -/
theorem half_lo (u : BitVec 64) :
    (u &&& BitVec.ofNat 64 mask32).toNat = u.toNat % 2 ^ 32 := by
  have hm : (BitVec.ofNat 64 mask32).toNat = 2 ^ 32 - 1 := by norm_num [mask32]
  rw [BitVec.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod]

/-- **The 32-bit split recombines.** Masking off the low half and shifting the
    high half back into place returns the word. -/
theorem half_recombine (u : BitVec 64) :
    (u &&& BitVec.ofNat 64 mask32) + ((u >>> 32) <<< 32) = u := by
  have hu : u.toNat < 2 ^ 64 := u.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, half_lo, half_hi, Nat.shiftLeft_eq]
  omega

/-- The `Nat` value of a word from its two 32-bit halves. -/
theorem half_toNat (u : BitVec 64) :
    (u &&& BitVec.ofNat 64 mask32).toNat + 2 ^ 32 * (u >>> 32).toNat = u.toNat := by
  rw [half_lo, half_hi, Nat.mod_add_div]

/-! ## 2. Reading and updating the scalar environment -/

theorem upd_ne {t : CryptoTy} {env : SEnvScalar} {y : String} {v : ⟦t⟧} {x : String}
    (h : x ≠ y) : (env.upd y v) x = env x := by
  simp only [SEnvScalar.upd, if_neg h]

theorem upd_self {t : CryptoTy} (env : SEnvScalar) (y : String) (v : ⟦t⟧) :
    (env.upd y v) y = some ⟨t, v⟩ := by
  simp [SEnvScalar.upd]

theorem envReadU64_of_bound {env : SEnvScalar} {x : String} {w : BitVec 64}
    (h : env x = some ⟨.sword 64, w⟩) : envReadU64 env x = some w := by
  simp only [envReadU64, h]

theorem envReader_of_bound {env : SEnvScalar} {x : String} {w : BitVec 64}
    (h : env x = some ⟨.sword 64, w⟩) : envReader env x = w := by
  simp only [envReader, h]

theorem envReadU64_upd_ne {t : CryptoTy} {env : SEnvScalar} {y : String} {v : ⟦t⟧}
    {x : String} (h : x ≠ y) : envReadU64 (env.upd y v) x = envReadU64 env x := by
  simp only [envReadU64, upd_ne h]

theorem envReadU64_upd_self (env : SEnvScalar) (y : String) (w : BitVec 64) :
    envReadU64 (env.upd y (t := .sword 64) w) y = some w := by
  simp only [envReadU64, upd_self]

/-! ## 3. The waist semantics of the arms the two generators emit -/

/-- `RArrLoad` of a `u64` destination out of a bound memref at a bound index. -/
theorem semScalar_arrLoad {dstN arrN idxN : String} {tw : TowerType} {n : Nat}
    {a : Fin n → BitVec 64} {i : BitVec 64} {env : SEnvScalar}
    (ha : env arrN = some ⟨.memref n, a⟩) (hi : env idxN = some ⟨.sword 64, i⟩) :
    ∃ env', semScalar (.RArrLoad ⟨dstN, .TU64⟩ ⟨arrN, tw⟩ idxN) env = some env'
      ∧ env' dstN = some ⟨.sword 64, memGetDyn a i.toNat⟩
      ∧ ∀ s, s ≠ dstN → env' s = env s := by
  refine ⟨env.upd dstN (t := .sword 64) (memGetDyn a i.toNat), ?_,
    upd_self _ _ _, fun s hs => upd_ne hs⟩
  simp only [semScalar, ha, hi]

/-- `RArrStore` of a `u64` source into a bound `.TBytes fw` memref at a bound
    index. -/
theorem semScalar_arrStore {arrN idxN srcN : String} {fw : Nat}
    {a : Fin ((fw + 7) / 8) → BitVec 64} {i v : BitVec 64} {env : SEnvScalar}
    (ha : env arrN = some ⟨.memref ((fw + 7) / 8), a⟩)
    (hi : env idxN = some ⟨.sword 64, i⟩)
    (hv : env srcN = some ⟨.sword 64, v⟩) :
    ∃ env', semScalar (.RArrStore ⟨arrN, .TBytes fw⟩ idxN ⟨srcN, .TU64⟩) env = some env'
      ∧ env' arrN = some ⟨.memref ((fw + 7) / 8), memSetDyn a i.toNat v⟩
      ∧ ∀ s, s ≠ arrN → env' s = env s := by
  refine ⟨env.upd arrN (t := .memref ((fw + 7) / 8)) (memSetDyn a i.toNat v), ?_,
    upd_self _ _ _, fun s hs => upd_ne hs⟩
  have hty : encodeTy (Located.mk arrN (TowerType.TBytes fw)).locDst
      = CryptoTy.memref ((fw + 7) / 8) := rfl
  simp only [semScalar, ha, hi, hv, dif_pos hty]
  rfl

/-- One `RScalarSetExpr` whose `SExpr` lowering makes progress: the destination
    holds the closed-form word evaluator, every other non-temporary slot is
    unchanged. -/
theorem semScalar_setExpr_run {y : String} {e : SExpr} {env : SEnvScalar}
    (h : (semLowerSExpr env 0 e).isSome) :
    ∃ env', semScalar (.RScalarSetExpr y e) env = some env'
      ∧ env' y = some ⟨.sword 64, SExpr.evalBV (envReader env) e⟩
      ∧ ∀ s, ¬ isTmpName s → s ≠ y → env' s = env s := by
  obtain ⟨⟨env2, nm, k⟩, hp⟩ := Option.isSome_iff_exists.mp h
  have hs : semScalar (.RScalarSetExpr y e) env
      = some (env2.upd y (t := .sword 64) (SExpr.evalBV (envReader env) e)) := by
    simp only [semScalar, hp]
  exact ⟨_, hs, (semScalar_setExpr_eq hs).1, (semScalar_setExpr_eq hs).2⟩

/-! ### Progress of the three `SExpr` shapes the frame generators use -/

theorem lower_and_lit {env : SEnvScalar} {x : String} {w : BitVec 64} (m : Nat)
    (hx : env x = some ⟨.sword 64, w⟩) (hnt : ¬ isTmpName x) :
    (semLowerSExpr env 0 (.SAnd (sv x) (.SLit m))).isSome := by
  have h0 : x ≠ tmpName 0 := fun h => hnt ⟨0, h⟩
  simp only [sv, semLowerSExpr, envReadU64_of_bound hx, binNode,
    envReadU64_upd_ne h0, envReadU64_upd_self]
  rfl

theorem lower_shr_lit {env : SEnvScalar} {x : String} {w : BitVec 64} (m : Nat)
    (hx : env x = some ⟨.sword 64, w⟩) (hnt : ¬ isTmpName x) :
    (semLowerSExpr env 0 (.SShr (sv x) (.SLit m))).isSome := by
  have h0 : x ≠ tmpName 0 := fun h => hnt ⟨0, h⟩
  simp only [sv, semLowerSExpr, envReadU64_of_bound hx, binNode,
    envReadU64_upd_ne h0, envReadU64_upd_self]
  rfl

theorem lower_add_shl {env : SEnvScalar} {x z : String} {wx wz : BitVec 64} (m : Nat)
    (hx : env x = some ⟨.sword 64, wx⟩) (hz : env z = some ⟨.sword 64, wz⟩)
    (hntx : ¬ isTmpName x) (hntz : ¬ isTmpName z) :
    (semLowerSExpr env 0 (.SAdd (sv x) (.SShl (sv z) (.SLit m)))).isSome := by
  have hx0 : x ≠ tmpName 0 := fun h => hntx ⟨0, h⟩
  have hx1 : x ≠ tmpName 1 := fun h => hntx ⟨1, h⟩
  have hz0 : z ≠ tmpName 0 := fun h => hntz ⟨0, h⟩
  simp only [sv, semLowerSExpr, envReadU64_of_bound hx, envReadU64_of_bound hz,
    binNode, envReadU64_upd_ne hz0, envReadU64_upd_ne hx0, envReadU64_upd_ne hx1,
    envReadU64_upd_self]
  rfl

/-- Peel the head of a `seqAll` whose head command steps. -/
theorem seqAll_step {c : LowCT} {l : List LowCT} {env e : SEnvScalar}
    (h : semScalar c env = some e) :
    semScalar (seqAll (c :: l)) env = semScalar (seqAll l) e := by
  rw [semScalar_seqAll_cons, h]
  rfl

/-! ## 4. The three uniform blocks

Each of `loadField` and `storeField` is a `seqAll` of a `List.map` /
`List.flatMap` over `List.range 4`, so each block is proved once over an
arbitrary index list `js`. -/

/-- **The frame loads.** Loading `f j` from the memref `arrN` at the index slot
    `g j`, for every `j` in `js`, leaves each `f j` holding the cell the index
    word `iw j` addresses, and every other name unchanged. -/
theorem semScalar_arrLoadList {n : Nat} {arrN : String} {tw : TowerType}
    {a : Fin n → BitVec 64} {iw : Nat → BitVec 64} {f g : Nat → String}
    (hfinj : Function.Injective f)
    (harr : ∀ j, arrN ≠ f j) (hgf : ∀ j j', g j ≠ f j') :
    ∀ (js : List Nat), js.Nodup → ∀ (env : SEnvScalar),
      env arrN = some ⟨.memref n, a⟩ →
      (∀ j ∈ js, env (g j) = some ⟨.sword 64, iw j⟩) →
      ∃ env', semScalar (seqAll (js.map (fun j =>
            (LowCT.RArrLoad ⟨f j, .TU64⟩ ⟨arrN, tw⟩ (g j))))) env = some env'
        ∧ (∀ j ∈ js, env' (f j) = some ⟨.sword 64, memGetDyn a (iw j).toNat⟩)
        ∧ (∀ s, (∀ j ∈ js, s ≠ f j) → env' s = env s) := by
  intro js
  induction js with
  | nil => intro _ env _ _; exact ⟨env, rfl, by simp, fun s _ => rfl⟩
  | cons j js ih =>
      intro hnd env ha hg
      have hjns : j ∉ js := (List.nodup_cons.mp hnd).1
      have hfne : ∀ j' ∈ js, f j ≠ f j' := by
        intro j' hj' hc
        apply hjns
        rw [hfinj hc]
        exact hj'
      obtain ⟨e1, hs1, hv1, hf1⟩ :=
        semScalar_arrLoad (dstN := f j) (tw := tw) ha (hg j (.head _))
      have ha1 : e1 arrN = some ⟨.memref n, a⟩ := by rw [hf1 _ (harr j)]; exact ha
      have hg1 : ∀ j' ∈ js, e1 (g j') = some ⟨.sword 64, iw j'⟩ := by
        intro j' hj'
        rw [hf1 _ (hgf j' j)]
        exact hg j' (.tail _ hj')
      obtain ⟨env', hsem, hval, hfr⟩ := ih (List.nodup_cons.mp hnd).2 e1 ha1 hg1
      refine ⟨env', ?_, ?_, ?_⟩
      · rw [List.map_cons, seqAll_step hs1]; exact hsem
      · intro j' hj'
        rcases List.mem_cons.mp hj' with rfl | hj'
        · rw [hfr _ hfne]; exact hv1
        · exact hval j' hj'
      · intro s hs
        rw [hfr _ (fun j' hj' => hs j' (.tail _ hj')), hf1 _ (hs j (.head _))]

/-- **The half-limb splits.** For every `j` in `js`, the two commands
    `hN (2j) := uN j &&& 2^32-1` and `hN (2j+1) := uN j >>> 32` bind the two
    32-bit halves of the word held in `uN j`. -/
theorem semScalar_halfSplitList {uN hN : Nat → String} {w : Nat → BitVec 64}
    (hhinj : Function.Injective hN)
    (huT : ∀ j, ¬ isTmpName (uN j)) (hhT : ∀ k, ¬ isTmpName (hN k))
    (hhu : ∀ k j, hN k ≠ uN j) :
    ∀ (js : List Nat), js.Nodup → ∀ (env : SEnvScalar),
      (∀ j ∈ js, env (uN j) = some ⟨.sword 64, w j⟩) →
      ∃ env', semScalar (seqAll (js.flatMap (fun j =>
            [(LowCT.RScalarSetExpr (hN (2 * j)) (.SAnd (sv (uN j)) (.SLit mask32))),
             (LowCT.RScalarSetExpr (hN (2 * j + 1)) (.SShr (sv (uN j)) (.SLit 32)))])))
          env = some env'
        ∧ (∀ j ∈ js, env' (hN (2 * j))
              = some ⟨.sword 64, w j &&& BitVec.ofNat 64 mask32⟩)
        ∧ (∀ j ∈ js, env' (hN (2 * j + 1))
              = some ⟨.sword 64, w j >>> (BitVec.ofNat 64 32).toNat⟩)
        ∧ (∀ s, ¬ isTmpName s → (∀ j ∈ js, s ≠ hN (2 * j) ∧ s ≠ hN (2 * j + 1)) →
              env' s = env s) := by
  intro js
  induction js with
  | nil => intro _ env _; exact ⟨env, rfl, by simp, by simp, fun s _ _ => rfl⟩
  | cons j js ih =>
      intro hnd env hu
      have hjns : j ∉ js := (List.nodup_cons.mp hnd).1
      have huj := hu j (.head _)
      obtain ⟨e1, hs1, hv1, hf1⟩ :=
        semScalar_setExpr_run (y := hN (2 * j)) (lower_and_lit mask32 huj (huT j))
      have hu1 : e1 (uN j) = some ⟨.sword 64, w j⟩ := by
        rw [hf1 _ (huT j) (fun hc => hhu (2 * j) j hc.symm)]; exact huj
      obtain ⟨e2, hs2, hv2, hf2⟩ :=
        semScalar_setExpr_run (y := hN (2 * j + 1)) (lower_shr_lit 32 hu1 (huT j))
      have hf12 : ∀ s, ¬ isTmpName s → s ≠ hN (2 * j) → s ≠ hN (2 * j + 1) →
          e2 s = env s := by
        intro s hsT h1 h2
        rw [hf2 s hsT h2, hf1 s hsT h1]
      have hu2 : ∀ j' ∈ js, e2 (uN j') = some ⟨.sword 64, w j'⟩ := by
        intro j' hj'
        rw [hf12 _ (huT j') (fun hc => hhu (2 * j) j' hc.symm)
          (fun hc => hhu (2 * j + 1) j' hc.symm)]
        exact hu j' (.tail _ hj')
      obtain ⟨env', hsem, hlo, hhi, hfr⟩ := ih (List.nodup_cons.mp hnd).2 e2 hu2
      have hkeyLo : ∀ j' ∈ js, hN (2 * j) ≠ hN (2 * j')
          ∧ hN (2 * j) ≠ hN (2 * j' + 1) := by
        intro j' hj'
        refine ⟨fun hc => ?_, fun hc => ?_⟩
        · have h2 := hhinj hc
          apply hjns
          have : j = j' := by omega
          rw [this]; exact hj'
        · have h2 := hhinj hc; omega
      have hkeyHi : ∀ j' ∈ js, hN (2 * j + 1) ≠ hN (2 * j')
          ∧ hN (2 * j + 1) ≠ hN (2 * j' + 1) := by
        intro j' hj'
        refine ⟨fun hc => ?_, fun hc => ?_⟩
        · have h2 := hhinj hc; omega
        · have h2 := hhinj hc
          apply hjns
          have : j = j' := by omega
          rw [this]; exact hj'
      have hlow : env' (hN (2 * j))
          = some ⟨.sword 64, w j &&& BitVec.ofNat 64 mask32⟩ := by
        rw [hfr _ (hhT (2 * j)) hkeyLo,
          hf2 _ (hhT (2 * j)) (fun hc => by have := hhinj hc; omega), hv1]
        simp only [SExpr.evalBV, sv, envReader_of_bound huj]
      have hhigh : env' (hN (2 * j + 1))
          = some ⟨.sword 64, w j >>> (BitVec.ofNat 64 32).toNat⟩ := by
        rw [hfr _ (hhT (2 * j + 1)) hkeyHi, hv2]
        simp only [SExpr.evalBV, sv, envReader_of_bound hu1]
      refine ⟨env', ?_, ?_, ?_, ?_⟩
      · simp only [List.flatMap_cons, List.cons_append, List.nil_append]
        rw [seqAll_step hs1, seqAll_step hs2]
        exact hsem
      · intro j' hj'
        rcases List.mem_cons.mp hj' with rfl | hj'
        · exact hlow
        · exact hlo j' hj'
      · intro j' hj'
        rcases List.mem_cons.mp hj' with rfl | hj'
        · exact hhigh
        · exact hhi j' hj'
      · intro s hsT hs
        rw [hfr s hsT (fun j' hj' => hs j' (.tail _ hj')),
          hf12 s hsT (hs j (.head _)).1 (hs j (.head _)).2]

/-- **The recombine-and-store steps.** For every `j` in `js`, the two commands
    `oN j := hN (2j) + (hN (2j+1) <<< 32)` and `outN[gN j] := oN j` write the
    recombined word into the frame. -/
theorem semScalar_recombineStoreList {fw : Nat} {outN : String}
    {iw : Nat → BitVec 64}
    {A B : Nat → BitVec 64} {hN oN gN : Nat → String}
    (houtT : ¬ isTmpName outN) (hhT : ∀ k, ¬ isTmpName (hN k))
    (hgT : ∀ j, ¬ isTmpName (gN j))
    (hout : ∀ j, outN ≠ oN j) (hho : ∀ k j, hN k ≠ oN j) (hgo : ∀ j j', gN j ≠ oN j')
    (hhOut : ∀ k, hN k ≠ outN) (hgOut : ∀ j, gN j ≠ outN) :
    ∀ (js : List Nat) (b : Fin ((fw + 7) / 8) → BitVec 64) (env : SEnvScalar),
      env outN = some ⟨.memref ((fw + 7) / 8), b⟩ →
      (∀ j ∈ js, env (gN j) = some ⟨.sword 64, iw j⟩) →
      (∀ j ∈ js, env (hN (2 * j)) = some ⟨.sword 64, A j⟩) →
      (∀ j ∈ js, env (hN (2 * j + 1)) = some ⟨.sword 64, B j⟩) →
      ∃ env', semScalar (seqAll (js.flatMap (fun j =>
            [(LowCT.RScalarSetExpr (oN j)
                (.SAdd (sv (hN (2 * j))) (.SShl (sv (hN (2 * j + 1))) (.SLit 32)))),
             (LowCT.RArrStore ⟨outN, .TBytes fw⟩ (gN j) ⟨oN j, .TU64⟩)])))
          env = some env'
        ∧ env' outN = some ⟨.memref ((fw + 7) / 8),
              js.foldl (fun arr j => memSetDyn arr (iw j).toNat
                (A j + B j <<< (BitVec.ofNat 64 32).toNat)) b⟩ := by
  intro js
  induction js with
  | nil => intro b env hb _ _ _; exact ⟨env, rfl, hb⟩
  | cons j js ih =>
      intro b env hb hgv hAv hBv
      obtain ⟨e1, hs1, hv1, hf1⟩ :=
        semScalar_setExpr_run (y := oN j)
          (lower_add_shl 32 (hAv j (.head _)) (hBv j (.head _))
            (hhT (2 * j)) (hhT (2 * j + 1)))
      have hb1 : e1 outN = some ⟨.memref ((fw + 7) / 8), b⟩ := by
        rw [hf1 _ houtT (hout j)]; exact hb
      have hg1 : e1 (gN j) = some ⟨.sword 64, iw j⟩ := by
        rw [hf1 _ (hgT j) (hgo j j)]; exact hgv j (.head _)
      have hval : e1 (oN j) = some ⟨.sword 64,
          A j + B j <<< (BitVec.ofNat 64 32).toNat⟩ := by
        rw [hv1]
        simp only [SExpr.evalBV, sv, envReader_of_bound (hAv j (.head _)),
          envReader_of_bound (hBv j (.head _))]
      obtain ⟨e2, hs2, hb2, hf2'⟩ := semScalar_arrStore (fw := fw) hb1 hg1 hval
      have hf2 : ∀ s, ¬ isTmpName s → s ≠ oN j → s ≠ outN → e2 s = env s := by
        intro s hsT h1 h2
        rw [hf2' s h2, hf1 s hsT h1]
      have hg2 : ∀ j' ∈ js, e2 (gN j') = some ⟨.sword 64, iw j'⟩ := by
        intro j' hj'
        rw [hf2 _ (hgT j') (hgo j' j) (hgOut j')]
        exact hgv j' (.tail _ hj')
      have hA2 : ∀ j' ∈ js, e2 (hN (2 * j')) = some ⟨.sword 64, A j'⟩ := by
        intro j' hj'
        rw [hf2 _ (hhT _) (hho _ j) (hhOut _)]
        exact hAv j' (.tail _ hj')
      have hB2 : ∀ j' ∈ js, e2 (hN (2 * j' + 1)) = some ⟨.sword 64, B j'⟩ := by
        intro j' hj'
        rw [hf2 _ (hhT _) (hho _ j) (hhOut _)]
        exact hBv j' (.tail _ hj')
      obtain ⟨env', hsem, hfin⟩ := ih _ e2 hb2 hg2 hA2 hB2
      refine ⟨env', ?_, ?_⟩
      · simp only [List.flatMap_cons, List.cons_append, List.nil_append]
        rw [seqAll_step hs1, seqAll_step hs2]
        exact hsem
      · rw [List.foldl_cons]; exact hfin

/-! ## 5. Slot-name hygiene

Every frame slot name is a prefix, a one-character tag and a decimal index. -/

theorem slot_toList (p u : String) (j : Nat) :
    ((p ++ u) ++ toString j).toList = p.toList ++ (u.toList ++ (toString j).toList) := by
  rw [String.toList_append, String.toList_append, List.append_assoc]

/-- Slot names sharing a prefix and a tag are equal only at equal indices. -/
theorem slot_inj {p u : String} {j k : Nat}
    (h : (p ++ u) ++ toString j = (p ++ u) ++ toString k) : j = k := by
  simp only [String.append_right_inj] at h
  exact repr_injective (by simpa [toString] using h)

/-- Slot names with distinct one-character tags are distinct. -/
theorem slot_ne_tag {p u v : String} {c d : Char} {j k : Nat}
    (hu : u.toList = [c]) (hv : v.toList = [d]) (hcd : c ≠ d) :
    (p ++ u) ++ toString j ≠ (p ++ v) ++ toString k := by
  intro h
  have h1 := congrArg String.toList h
  rw [slot_toList, slot_toList, hu, hv] at h1
  have h2 := List.append_cancel_left h1
  simp only [List.cons_append, List.nil_append] at h2
  injection h2 with h3 _
  exact hcd h3

/-- A name whose first character differs from a slot prefix's first character is
    not that slot. -/
theorem head_ne_slot {s p u : String} {c d : Char} {r q : List Char} {j : Nat}
    (hs : s.toList = c :: r) (hp : p.toList = d :: q) (hcd : c ≠ d) :
    s ≠ (p ++ u) ++ toString j := by
  intro h
  have h1 := congrArg String.toList h
  rw [hs, slot_toList, hp] at h1
  simp only [List.cons_append] at h1
  injection h1 with h2 _
  exact hcd h2

/-- Two names with distinct first characters are distinct. -/
theorem head_ne {s t : String} {c d : Char} {r q : List Char}
    (hs : s.toList = c :: r) (ht : t.toList = d :: q) (hcd : c ≠ d) : s ≠ t := by
  intro h
  have h1 : (c :: r : List Char) = d :: q := by rw [← hs, h, ht]
  injection h1 with h2 _
  exact hcd h2

/-- The index slots `ix{i}` begin with `'i'`. -/
theorem ix_toList (i : Nat) :
    (s!"ix{i}").toList = 'i' :: ('x' :: (toString i).toList) := by
  rw [String.toList_append]
  rfl

theorem out_toList : ("out" : String).toList = 'o' :: ['u', 't'] := rfl

theorem toNat_ofNat_32 : (BitVec.ofNat 64 32).toNat = 32 := by simp

/-! ## 6. `loadField` and `storeField` under the waist semantics -/

/-- **`loadField` splits four frame cells into eight half-limb slots.** The
    eight `h` slots of `fe` hold the low and high 32-bit halves of the four cells
    the index words `iw 0 … iw 3` address, and every other non-temporary name
    outside `fe`'s own slots is unchanged. -/
theorem semScalar_loadField {fw o n : Nat} {arrN fe : String} {cf ca : Char}
    {rf ra : List Char} {a : Fin n → BitVec 64} {iw : Nat → BitVec 64}
    {env : SEnvScalar}
    (hfe : fe.toList = cf :: rf) (hcf : cf ≠ '_') (hci : cf ≠ 'i')
    (harrH : arrN.toList = ca :: ra) (hca : ca ≠ cf)
    (ha : env arrN = some ⟨.memref n, a⟩)
    (hix : ∀ j, j < 4 → env s!"ix{o + j}" = some ⟨.sword 64, iw j⟩) :
    ∃ env', semScalar (seqAll (loadField fw arrN o fe)) env = some env'
      ∧ (∀ j, j < 4 → env' s!"{fe}h{2 * j}"
            = some ⟨.sword 64, memGetDyn a (iw j).toNat &&& BitVec.ofNat 64 mask32⟩)
      ∧ (∀ j, j < 4 → env' s!"{fe}h{2 * j + 1}"
            = some ⟨.sword 64,
                memGetDyn a (iw j).toNat >>> (BitVec.ofNat 64 32).toNat⟩)
      ∧ (∀ s, ¬ isTmpName s → (∀ j, j < 4 → s ≠ s!"{fe}u{j}") →
            (∀ k, k < 8 → s ≠ s!"{fe}h{k}") → env' s = env s) := by
  have hfeHead : HeadOk fe := ⟨cf, rf, hfe, hcf⟩
  have huT : ∀ j : Nat, ¬ isTmpName s!"{fe}u{j}" :=
    fun _ => HeadOk.notTmp (HeadOk.append (HeadOk.append hfeHead _) _)
  have hhT : ∀ k : Nat, ¬ isTmpName s!"{fe}h{k}" :=
    fun _ => HeadOk.notTmp (HeadOk.append (HeadOk.append hfeHead _) _)
  have huInj : Function.Injective (fun j : Nat => s!"{fe}u{j}") := fun _ _ h => slot_inj h
  have hhInj : Function.Injective (fun k : Nat => s!"{fe}h{k}") := fun _ _ h => slot_inj h
  have hhu : ∀ k j : Nat, s!"{fe}h{k}" ≠ s!"{fe}u{j}" :=
    fun _ _ => slot_ne_tag rfl rfl (by decide)
  have harrNe : ∀ j : Nat, arrN ≠ s!"{fe}u{j}" := fun _ => head_ne_slot harrH hfe hca
  have hixNe : ∀ i j : Nat, s!"ix{i}" ≠ s!"{fe}u{j}" :=
    fun i _ => head_ne_slot (ix_toList i) hfe (Ne.symm hci)
  obtain ⟨e1, hs1, hv1, hf1⟩ :=
    semScalar_arrLoadList (tw := .TBytes fw) (a := a) (iw := iw) huInj harrNe
      (fun j j' => hixNe (o + j) j') (List.range 4) List.nodup_range env ha
      (fun j hj => hix j (List.mem_range.mp hj))
  obtain ⟨env', hs2, hlo, hhi, hf2⟩ :=
    semScalar_halfSplitList (w := fun j => memGetDyn a (iw j).toNat) hhInj huT hhT hhu
      (List.range 4) List.nodup_range e1 hv1
  refine ⟨env', ?_, ?_, ?_, ?_⟩
  · simp only [loadField]
    rw [semScalar_seqAll_append, hs1]
    exact hs2
  · exact fun j hj => hlo j (List.mem_range.mpr hj)
  · exact fun j hj => hhi j (List.mem_range.mpr hj)
  · intro s hsT hsu hsh
    rw [hf2 s hsT (fun j hj =>
        ⟨hsh (2 * j) (by have := List.mem_range.mp hj; omega),
         hsh (2 * j + 1) (by have := List.mem_range.mp hj; omega)⟩),
      hf1 s (fun j hj => hsu j (List.mem_range.mp hj))]

/-- **`storeField` recombines eight half-limb slots into four frame cells.**
    The output frame `out` ends holding the fourfold `memSetDyn` of the
    recombined words. -/
theorem semScalar_storeField {fw o : Nat} {fe : String} {cf : Char} {rf : List Char}
    {b : Fin ((fw + 7) / 8) → BitVec 64} {iw A B : Nat → BitVec 64}
    {env : SEnvScalar}
    (hfe : fe.toList = cf :: rf) (hcf : cf ≠ '_') (hci : cf ≠ 'i') (hco : cf ≠ 'o')
    (hb : env "out" = some ⟨.memref ((fw + 7) / 8), b⟩)
    (hix : ∀ j, j < 4 → env s!"ix{o + j}" = some ⟨.sword 64, iw j⟩)
    (hA : ∀ j, j < 4 → env s!"{fe}h{2 * j}" = some ⟨.sword 64, A j⟩)
    (hB : ∀ j, j < 4 → env s!"{fe}h{2 * j + 1}" = some ⟨.sword 64, B j⟩) :
    ∃ env', semScalar (seqAll (storeField fw o fe)) env = some env'
      ∧ env' "out" = some ⟨.memref ((fw + 7) / 8),
          (List.range 4).foldl (fun arr j => memSetDyn arr (iw j).toNat
            (A j + B j <<< (BitVec.ofNat 64 32).toNat)) b⟩ := by
  have hfeHead : HeadOk fe := ⟨cf, rf, hfe, hcf⟩
  have hhT : ∀ k : Nat, ¬ isTmpName s!"{fe}h{k}" :=
    fun _ => HeadOk.notTmp (HeadOk.append (HeadOk.append hfeHead _) _)
  have hixHead : HeadOk "ix" := ⟨'i', ['x'], rfl, by decide⟩
  have hgT : ∀ j : Nat, ¬ isTmpName s!"ix{o + j}" :=
    fun _ => HeadOk.notTmp (HeadOk.append hixHead _)
  have houtT : ¬ isTmpName "out" := notTmp_of_len "out" (by decide)
  have hout : ∀ j : Nat, ("out" : String) ≠ s!"{fe}o{j}" :=
    fun _ => head_ne_slot out_toList hfe (Ne.symm hco)
  have hho : ∀ k j : Nat, s!"{fe}h{k}" ≠ s!"{fe}o{j}" :=
    fun _ _ => slot_ne_tag rfl rfl (by decide)
  have hgo : ∀ j j' : Nat, s!"ix{o + j}" ≠ s!"{fe}o{j'}" :=
    fun j _ => head_ne_slot (ix_toList (o + j)) hfe (Ne.symm hci)
  have hhOut : ∀ k : Nat, s!"{fe}h{k}" ≠ ("out" : String) :=
    fun k => Ne.symm (head_ne_slot (u := "h") (j := k) out_toList hfe (Ne.symm hco))
  have hgOut : ∀ j : Nat, s!"ix{o + j}" ≠ ("out" : String) :=
    fun j => head_ne (ix_toList (o + j)) out_toList (by decide)
  obtain ⟨env', hs, hfin⟩ :=
    semScalar_recombineStoreList (fw := fw) (iw := iw) (A := A) (B := B)
      houtT hhT hgT hout hho hgo hhOut hgOut (List.range 4) b env hb
      (fun j hj => hix j (List.mem_range.mp hj))
      (fun j hj => hA j (List.mem_range.mp hj))
      (fun j hj => hB j (List.mem_range.mp hj))
  exact ⟨env', by simpa only [storeField] using hs, hfin⟩

/-! ## 7. The round trip and the half-limb readout -/

/-- **The frame round trip.** `storeField` after `loadField` at the same cell
    offset writes back exactly the four cells `loadField` read. -/
theorem loadField_storeField_frame {fw o : Nat} {arrN fe : String} {cf ca : Char}
    {rf ra : List Char} {a b : Fin ((fw + 7) / 8) → BitVec 64} {iw : Nat → BitVec 64}
    {env : SEnvScalar}
    (hfe : fe.toList = cf :: rf) (hcf : cf ≠ '_') (hci : cf ≠ 'i') (hco : cf ≠ 'o')
    (harrH : arrN.toList = ca :: ra) (hca : ca ≠ cf)
    (ha : env arrN = some ⟨.memref ((fw + 7) / 8), a⟩)
    (hb : env "out" = some ⟨.memref ((fw + 7) / 8), b⟩)
    (hix : ∀ j, j < 4 → env s!"ix{o + j}" = some ⟨.sword 64, iw j⟩) :
    ∃ envF, semScalar (seqAll (loadField fw arrN o fe ++ storeField fw o fe)) env
        = some envF
      ∧ envF "out" = some ⟨.memref ((fw + 7) / 8),
          (List.range 4).foldl
            (fun arr j => memSetDyn arr (iw j).toNat (memGetDyn a (iw j).toNat)) b⟩ := by
  obtain ⟨e1, hs1, hlo, hhi, hf1⟩ :=
    semScalar_loadField hfe hcf hci harrH hca ha hix
  have huNe : ∀ j : Nat, ("out" : String) ≠ s!"{fe}u{j}" :=
    fun _ => head_ne_slot out_toList hfe (Ne.symm hco)
  have hhNe : ∀ k : Nat, ("out" : String) ≠ s!"{fe}h{k}" :=
    fun _ => head_ne_slot out_toList hfe (Ne.symm hco)
  have houtT : ¬ isTmpName "out" := notTmp_of_len "out" (by decide)
  have hixHead : HeadOk "ix" := ⟨'i', ['x'], rfl, by decide⟩
  have hixT : ∀ j : Nat, ¬ isTmpName s!"ix{o + j}" :=
    fun _ => HeadOk.notTmp (HeadOk.append hixHead _)
  have hixU : ∀ i j : Nat, s!"ix{i}" ≠ s!"{fe}u{j}" :=
    fun i _ => head_ne_slot (ix_toList i) hfe (Ne.symm hci)
  have hixH : ∀ i k : Nat, s!"ix{i}" ≠ s!"{fe}h{k}" :=
    fun i _ => head_ne_slot (ix_toList i) hfe (Ne.symm hci)
  have hb1 : e1 "out" = some ⟨.memref ((fw + 7) / 8), b⟩ := by
    rw [hf1 _ houtT (fun j _ => huNe j) (fun k _ => hhNe k)]; exact hb
  have hix1 : ∀ j, j < 4 → e1 s!"ix{o + j}" = some ⟨.sword 64, iw j⟩ := by
    intro j hj
    rw [hf1 _ (hixT j) (fun i _ => hixU (o + j) i) (fun k _ => hixH (o + j) k)]
    exact hix j hj
  obtain ⟨envF, hs2, hfin⟩ :=
    semScalar_storeField (fw := fw) hfe hcf hci hco hb1 hix1 hlo hhi
  refine ⟨envF, ?_, ?_⟩
  · rw [semScalar_seqAll_append, hs1]
    exact hs2
  · rw [hfin]
    simp only [toNat_ofNat_32, half_recombine]

/-- **The half-limb readout of a loaded field element is the frame value.**
    `feVal` of the eight half-limb slots is the little-endian value of the four
    `u64` cells the loads read. -/
theorem feVal_of_halves {fe : String} {u : Nat → BitVec 64} {env : SEnvScalar}
    (hlo : ∀ j, j < 4 → env s!"{fe}h{2 * j}"
        = some ⟨.sword 64, u j &&& BitVec.ofNat 64 mask32⟩)
    (hhi : ∀ j, j < 4 → env s!"{fe}h{2 * j + 1}"
        = some ⟨.sword 64, u j >>> (BitVec.ofNat 64 32).toNat⟩) :
    feVal env fe = (u 0).toNat + 2 ^ 64 * (u 1).toNat + 2 ^ 128 * (u 2).toNat
      + 2 ^ 192 * (u 3).toNat := by
  have e0 := envReader_of_bound (hlo 0 (by norm_num))
  have e1 := envReader_of_bound (hhi 0 (by norm_num))
  have e2 := envReader_of_bound (hlo 1 (by norm_num))
  have e3 := envReader_of_bound (hhi 1 (by norm_num))
  have e4 := envReader_of_bound (hlo 2 (by norm_num))
  have e5 := envReader_of_bound (hhi 2 (by norm_num))
  have e6 := envReader_of_bound (hlo 3 (by norm_num))
  have e7 := envReader_of_bound (hhi 3 (by norm_num))
  simp only [toNat_ofNat_32] at e0 e1 e2 e3 e4 e5 e6 e7
  norm_num only at e0 e1 e2 e3 e4 e5 e6 e7
  simp only [feVal, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from by decide,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    e0, e1, e2, e3, e4, e5, e6, e7, half_lo, half_hi]
  norm_num
  omega

/-- **`loadField`'s half-limb readout is the value of the four frame cells it
    read.** The `feVal` the schedule works on is the little-endian `u64` value of
    cells `iw 0 … iw 3` of the source frame. -/
theorem feVal_of_loadField {fw o n : Nat} {arrN fe : String} {cf ca : Char}
    {rf ra : List Char} {a : Fin n → BitVec 64} {iw : Nat → BitVec 64}
    {env : SEnvScalar}
    (hfe : fe.toList = cf :: rf) (hcf : cf ≠ '_') (hci : cf ≠ 'i')
    (harrH : arrN.toList = ca :: ra) (hca : ca ≠ cf)
    (ha : env arrN = some ⟨.memref n, a⟩)
    (hix : ∀ j, j < 4 → env s!"ix{o + j}" = some ⟨.sword 64, iw j⟩) :
    ∃ env', semScalar (seqAll (loadField fw arrN o fe)) env = some env'
      ∧ feVal env' fe
          = (memGetDyn a (iw 0).toNat).toNat
            + 2 ^ 64 * (memGetDyn a (iw 1).toNat).toNat
            + 2 ^ 128 * (memGetDyn a (iw 2).toNat).toNat
            + 2 ^ 192 * (memGetDyn a (iw 3).toNat).toNat := by
  obtain ⟨env', hs, hlo, hhi, _⟩ := semScalar_loadField hfe hcf hci harrH hca ha hix
  exact ⟨env', hs, feVal_of_halves hlo hhi⟩

end CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrameRoundTrip
