/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomEntrySlot

/-!
# The cell fold of a code whose cell accesses are at known indices

The stage `regionFoldB` of the region gate asks that the cell fold `cellFoldLR` of the code
behind the prefix succeeds at the cell arrays. The fold reads the code in order, keeping the
constants that immediate moves `MOV:64 x, $c` (at a register tag) write and forgetting a
register when an instruction writes it (`kstep`). It turns a load of a cell array at a known
index into a copy from the cell and an in-place store to a cell array at a known index into a
copy to the cell, keeps an operation that names no cell array and no cell (`keepB`), an
instruction of `keepRegB` and the control instructions of `ctlB`. So the fold succeeds when
each position of the code is one of these five cases, an access whose index register was
written by an immediate move below it and by no instruction in between (`KnownAt`).

## Main definitions

* `KnownAt`: the register `x` holds the constant `c` at position `k` of the code.
* `FoldPos`: the instruction at a position is a load or an in-place store of a cell array at a
  known index below its length, an instruction of `keepRegB`, or a control instruction.

## Main results

* `kval_knownAt`: the constants of the fold at a position give the known constant.
* `foldOne_of_keepB`: an operation that names no cell array and no cell is kept.
* `cellFoldLR_isSome_of_foldPos`: the fold succeeds on a code of `FoldPos` positions.
* `fieldDom_regionFoldB_of_foldPos`: the stage `G12` on the field domain when the code behind
  the prefix is of `FoldPos` positions at the cell arrays.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemStepFrame (dstNames)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (isLopnB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCellFold (Slots KEnv kval kstep foldOne
  isArrB isCellB lenOf keepB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CellFoldL (kstepL ctlB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CellFoldLReg (cellFoldLR foldOneLR foldOneR
  keepRegB)

/-! ## 1. Known constants -/

/-- **The register `x` holds the constant `c` at position `k` of the code `C`**: an immediate
    move `MOV:64 x, $c` at a register tag lies below `k`, and every instruction between it and
    `k` is an operation that does not write `x`. -/
def KnownAt (C : List LinstrRM) (k : Nat) (x : String) (c : Nat) : Prop :=
  ∃ j < k, C[j]? = some (.Lopn [.reg x] "MOV:64" [.imm c], .reg none) ∧
    ∀ j', j < j' → j' < k → ∀ i, C[j']? = some i →
      (∃ ds o ss, i.1 = .Lopn ds o ss) ∧ x ∉ dstNames i.1

/-- The constants of the fold after the prefix of length `k`. -/
def envAt (C : List LinstrRM) (k : Nat) : KEnv := (C.take k).foldl kstepL []

/-- A filter that keeps every pair at the name `x` keeps the constant at `x`. -/
theorem kval_filter {env : KEnv} {x : String} {p : String × Nat → Bool}
    (hp : ∀ a, a.1 = x → p a = true) : kval (env.filter p) x = kval env x := by
  unfold kval
  congr 1
  induction env with
  | nil => rfl
  | cons a env ih =>
      by_cases ha : a.1 = x
      · simp [hp a ha, ha]
      · cases hpa : p a <;> simp [hpa, ha, ih]

/-- The step of the constants forgets the names an instruction writes, and records at most
    one written name. -/
theorem kstep_cases (env : KEnv) (i : LinstrRM) :
    kstep env i = env.filter (fun p => !(dstNames i.1).contains p.1) ∨
      ∃ d kk, d ∈ dstNames i.1 ∧
        kstep env i = (d, kk) :: env.filter (fun p => !(dstNames i.1).contains p.1) := by
  unfold kstep
  split
  · split
    · right
      exact ⟨_, _, by simp_all [dstNames, JasminLsemExportRewrites.opNames], rfl⟩
    · exact .inl rfl
  · exact .inl rfl

/-- An operation that does not write `x` keeps the constant at `x`. -/
theorem kval_kstepL {env : KEnv} {i : LinstrRM} {x : String}
    (hl : ∃ ds o ss, i.1 = .Lopn ds o ss) (hx : x ∉ dstNames i.1) :
    kval (kstepL env i) x = kval env x := by
  obtain ⟨ds, o, ss, he⟩ := hl
  have hf : kval (env.filter fun p => !(dstNames i.1).contains p.1) x = kval env x :=
    kval_filter fun a ha => by simp [ha, hx]
  have hk : kstepL env i = kstep env i := by
    unfold kstepL
    rw [he]
  rw [hk]
  rcases kstep_cases env i with h | ⟨d, kk, hd, h⟩ <;> rw [h]
  · exact hf
  · have hdx : d ≠ x := fun e => hx (e ▸ hd)
    have hb : (d == x) = false := by simpa using hdx
    simp only [kval, List.find?_cons, hb] at hf ⊢
    exact hf

/-- Operations that do not write `x` keep the constant at `x`. -/
theorem kval_foldl_kstepL {x : String} :
    ∀ (l : List LinstrRM) (env : KEnv),
      (∀ i ∈ l, (∃ ds o ss, i.1 = .Lopn ds o ss) ∧ x ∉ dstNames i.1) →
      kval (l.foldl kstepL env) x = kval env x
  | [], _, _ => rfl
  | i :: l, env, h => by
      rw [List.foldl_cons, kval_foldl_kstepL l _ fun j hj => h j (List.mem_cons_of_mem _ hj)]
      exact kval_kstepL (h i List.mem_cons_self).1 (h i List.mem_cons_self).2

/-- The constants of the fold one position further. -/
theorem envAt_succ (C : List LinstrRM) (k : Nat) :
    envAt C (k + 1) = match C[k]? with
      | some i => kstepL (envAt C k) i
      | none => envAt C k := by
  unfold envAt
  rw [List.take_add_one]
  cases C[k]? <;> simp [List.foldl_append]

/-- **The constants of the fold at a position give the known constant.** -/
theorem kval_knownAt {C : List LinstrRM} {x : String} {c : Nat} :
    ∀ {k : Nat}, KnownAt C k x c → kval (envAt C k) x = some c
  | 0, ⟨j, hj, _⟩ => absurd hj (Nat.not_lt_zero _)
  | k + 1, ⟨j, hjk, hj, hmid⟩ => by
      rw [envAt_succ]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hjk with hlt | rfl
      · have ih := kval_knownAt (k := k) ⟨j, hlt, hj, fun j' h1 h2 i hi => hmid j' h1 (by omega) i hi⟩
        cases hk : C[k]? with
        | none => exact ih
        | some i =>
            dsimp only
            obtain ⟨hl, hx⟩ := hmid k hlt (by omega) i hk
            rw [kval_kstepL hl hx, ih]
      · rw [hj]
        dsimp only
        unfold kstepL kstep
        simp [kval]

/-! ## 2. The fold of a code of known accesses -/

/-- **The fold cases of the instruction at a position**: a load of a cell array at a known index
    below its length into a name that is no cell and no cell array, an in-place store to a cell
    array at a known index below its length of a name that is no cell, an operation that names
    no cell array and no cell (`keepB`), an instruction of `keepRegB`, or a control instruction
    of `ctlB`. -/
def FoldPos (R : Slots) (C : List LinstrRM) (k : Nat) (i : LinstrRM) : Prop :=
  (∃ d b x s n c, i = (.Lopn [.reg d] "LOADIDX" [.arrIdx b x s], .load 64 n) ∧
      isArrB R b = true ∧ lenOf R b = some n ∧ isCellB R d = false ∧ isArrB R d = false ∧
      c < n ∧ KnownAt C k x c)
  ∨ (∃ b x s v n c, i = (.Lopn [.reg b] "STOREIDX" [.arrIdx b x s, .reg v], .store 64 n) ∧
      isArrB R b = true ∧ lenOf R b = some n ∧ isCellB R v = false ∧ c < n ∧ KnownAt C k x c)
  ∨ keepB R i = true
  ∨ keepRegB R i = true
  ∨ (isLopnB i = false ∧ ctlB i = true)

/-- An operation that names no cell array and no cell is kept by `foldOne`. -/
theorem foldOne_of_keepB {R : Slots} {env : KEnv} {i : LinstrRM} (h : keepB R i = true) :
    foldOne R env i = some i := by
  have hn : ∀ r ∈ JasminLsemExportRewrites.instrNames i.1, isArrB R r = false := by
    intro r hr
    simp only [keepB, Bool.and_eq_true, List.all_eq_true, Bool.and_eq_true,
      Bool.not_eq_true'] at h
    exact (h.2 r hr).1
  obtain ⟨w, tag⟩ := i
  unfold foldOne
  split <;> simp_all [JasminLsemExportRewrites.instrNames, JasminLsemExportRewrites.opNames]


/-- One instruction of `FoldPos` folds under the constants of its position. -/
theorem foldOneLR_of_foldPos {R : Slots} {C : List LinstrRM} {k : Nat} {i : LinstrRM}
    (h : FoldPos R C k i) : (foldOneLR R (envAt C k) i).isSome = true := by
  rcases h with ⟨d, b, x, s, n, c, rfl, hb, hn, hd1, hd2, hc, hK⟩ |
      ⟨b, x, s, v, n, c, rfl, hb, hn, hv, hc, hK⟩ | hkb | hk | ⟨hl, hc⟩
  · have hx := kval_knownAt hK
    simp [foldOneLR, foldOneR, foldOne, isLopnB, hb, hn, hd1, hd2, hx, hc]
  · have hx := kval_knownAt hK
    simp [foldOneLR, foldOneR, foldOne, isLopnB, hb, hn, hv, hx, hc]
  · have hl : isLopnB i = true := by
      simp only [keepB, Bool.and_eq_true] at hkb
      exact hkb.1.1
    unfold foldOneLR foldOneR
    rw [ite_eq_left hl, foldOne_of_keepB hkb]
    rfl
  · have hl : isLopnB i = true := by
      simp only [keepRegB, Bool.and_eq_true] at hk
      exact hk.1.1.1.1
    unfold foldOneLR foldOneR
    rw [ite_eq_left hl]
    split
    · rfl
    · rw [ite_eq_left hk]
      rfl
  · unfold foldOneLR
    rw [ite_eq_right (by simp [hl]), ite_eq_left hc]
    rfl

/-- **The fold succeeds on a code of `FoldPos` positions.** -/
theorem cellFoldLR_isSome_of_foldPos {R : Slots} {C : List LinstrRM}
    (h : ∀ k i, C[k]? = some i → FoldPos R C k i) : (cellFoldLR R [] C).isSome = true := by
  suffices key : ∀ m k, k + m = C.length → (cellFoldLR R (envAt C k) (C.drop k)).isSome = true by
    simpa [envAt] using key C.length 0 (by omega)
  intro m
  induction m with
  | zero =>
      intro k hk
      rw [List.drop_eq_nil_of_le (by omega)]
      rfl
  | succ m ih =>
      intro k hk
      have hlt : k < C.length := by omega
      rw [List.drop_eq_getElem_cons hlt]
      have hi : C[k]? = some C[k] := List.getElem?_eq_getElem hlt
      have h1 := foldOneLR_of_foldPos (h k C[k] hi)
      have h2 := ih (k + 1) (by omega)
      rw [envAt_succ, hi] at h2
      dsimp only at h2
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp h1
      obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp h2
      unfold cellFoldLR
      rw [ha, hl]
      rfl

/-! ## 3. The stage `G12` -/

variable {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
  {r : Exported} {cert : List (String × String)}

/-- **Stage `G12` on the field domain** when the code behind the prefix of the parts is of
    `FoldPos` positions at their cell arrays. -/
theorem fieldDom_regionFoldB_of_foldPos (h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert)
    (hf : ∀ k i, ((regionCoParts σ exportReg b t r.code r.res cert).fused.drop
        (regionCoParts σ exportReg b t r.code r.res cert).pre.length)[k]? = some i →
      FoldPos (regionCoParts σ exportReg b t r.code r.res cert).cells
        ((regionCoParts σ exportReg b t r.code r.res cert).fused.drop
          (regionCoParts σ exportReg b t r.code r.res cert).pre.length) k i) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "regionFoldB" :=
  fieldDom_regionFoldB_of_cellFold h hB (.inr (cellFoldLR_isSome_of_foldPos hf))

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
