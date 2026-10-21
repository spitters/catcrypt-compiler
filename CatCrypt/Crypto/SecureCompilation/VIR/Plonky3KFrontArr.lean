/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3NttLayerDenote
public import CatCrypt.Crypto.Hax.HaxToLowCTWordOpsSim -- deprecated_module: ignore

/-!
# BabyBear butterfly networks over array parameters, generated through the front

`Plonky3NttLayerDenote.kFrontAt` compiles a butterfly network whose `N` values and `T`
twiddles are word parameters and whose outputs are `N` separate word results. This
module compiles the same network as a kernel over three array parameters: the values
`xs` (`N` words), the twiddles `ws` (`T` words) and the output buffer `ys` (`N` words).
The `LowCT` body reads `xs[i]` into `v{i}` and `ws[j]` into `tw{j}` by indexed loads,
sets the constants `MU` and `p`, runs the butterflies of `Plonky3NttLayerDenote`, and
writes `v{i}` into `ys[i]` by indexed stores; the program returns `ys`. The body goes
through the front `translateDialectControl`, and the result lowers to
`Com jasminDialect` through `cryptoDialectToJasminCom`.

## Main results

* `kFrontArr` — the front program of the array kernel.
* `kFrontArr_denote` — for every admissible butterfly list, canonical values and
  twiddles and any initial output buffer, `kFrontArr` returns a program that lowers to
  `Com jasminDialect` and whose returned array holds at entry `j < N` a canonical word
  encoding position `j` of the left fold of `LayeredNtt.bupd` over the list, applied to
  the field values of the inputs.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.Plonky3KFrontArr

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectTotality
open CatCrypt.Crypto.SecureCompilation.X86Backend.CombSelectFront
open CatCrypt.Crypto.SecureCompilation.VIR.Plonky3NttLayerEmit
open CatCrypt.Crypto.SecureCompilation.VIR.Plonky3NttLayerDenote
open CatCrypt.Crypto.SecureCompilation.VIR.Plonky3BarrettLaw (bbMU)
open CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2Emit (bbP)
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr Located TowerType)
open CatCrypt.Crypto.Optimizer.Lattice.LayeredNtt (bupd)

/-! ## 1. The source -/

/-- Indexed loads `f i := arr[i]` for the indices of `l`, through the index slot `k`. -/
def loadStmts (f : ℕ → String) (arr : String) (n : ℕ) (l : List ℕ) : List LowCT :=
  l.flatMap (fun i => [.RScalarSet "k" i, .RArrLoad ⟨f i, .TU64⟩ ⟨arr, .TArr n .TU64⟩ "k"])

/-- Indexed stores `ys[i] := v{i}` for the indices of `l`, through the index slot `k`. -/
def storeStmts (N : ℕ) (l : List ℕ) : List LowCT :=
  l.flatMap (fun i => [.RScalarSet "k" i, .RArrStore ⟨"ys", .TArr N .TU64⟩ "k" ⟨vN i, .TU64⟩])

/-- The constants `MU` and `p` of the Barrett butterfly. -/
def constStmts : List LowCT := [.RScalarSet "mu" 2290649223, .RScalarSet "p" 2013265921]

/-- The array kernel body: loads of the values and twiddles, the constants, the
butterflies of `l`, the stores of the values. -/
def kArrBody (N T : ℕ) (l : List (ℕ × ℕ × ℕ)) : LowCT :=
  seqL (loadStmts vN "xs" N (List.range N) ++ (loadStmts twN "ws" T (List.range T) ++
    (constStmts ++ (bflyStmtsOf l ++ storeStmts N (List.range N)))))

/-- The argument context, head first: `xs`, `ws`, `ys`. -/
abbrev kArrCtx (N T : ℕ) : Ctx := [.memref N, .memref T, .memref N]

/-- The argument `VarMap`: `ys` bound deepest, then `ws`, then `xs`. -/
def kArrVM (N T : ℕ) : VarMap (kArrCtx N T) :=
  ((VarMap.empty.bind (t := .memref N) "ys").bind (t := .memref T) "ws").bind
    (t := .memref N) "xs"

/-- **The array kernel through the front**: `translateDialectControl` on `kArrBody`,
closed by returning `ys`. -/
def kFrontArr (N T : ℕ) (l : List (ℕ × ℕ × ℕ)) :
    Option (Com catCryptDialect (kArrCtx N T) (.memref N)) :=
  match translateDialectControl (kArrVM N T) (kArrBody N T l) with
  | some r =>
      match r.vm.lookup "ys" with
      | some ⟨t, v⟩ => if h : t = .memref N then r.cont (Com.ret (toVIRVar (h ▸ v))) else none
      | none => none
  | none => none

/-- The argument valuation: `xs ↦ x`, `ws ↦ w`, `ys ↦ y`. -/
def kArrVal (N T : ℕ) (x : Fin N → BitVec 64) (w : Fin T → BitVec 64)
    (y : Fin N → BitVec 64) : Ctxt.Valuation (d := catCryptDialect) (kArrCtx N T) :=
  .cons x (.cons w (.cons y .nil))

/-- The environment a valuation induces through `kArrVM`. -/
def kArrEnv (N T : ℕ) (V : Ctxt.Valuation (d := catCryptDialect) (kArrCtx N T)) :
    SEnvScalar :=
  fun s => ((kArrVM N T).lookup s).map (fun p => ⟨p.1, (toVIRVar p.2).lookup V⟩)

/-! ## 2. Arrays and indices -/

theorem encodeTy_arr (N : ℕ) : encodeTy (.TArr N .TU64) = .memref N := by
  simp only [encodeTy, TowerType.storageBytes]
  congr 1
  omega

theorem ofNat_toNat_of_lt {i : ℕ} (h : i < 2 ^ 64) : (BitVec.ofNat 64 i).toNat = i := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- A dynamic-index store of a word into a bound `N`-word memref. -/
theorem arrStoreN_eq {N : ℕ} {arrN idxN srcN : String} {a : Fin N → BitVec 64}
    {i v : BitVec 64} {env : SEnvScalar}
    (ha : env arrN = some ⟨.memref N, a⟩) (hi : env idxN = some ⟨.sword 64, i⟩)
    (hv : env srcN = some ⟨.sword 64, v⟩) :
    semScalar (.RArrStore ⟨arrN, .TArr N .TU64⟩ idxN ⟨srcN, .TU64⟩) env
      = some (env.upd arrN (t := .memref N) (memSetDyn a i.toNat v)) := by
  have key : ∀ (t : CryptoTy) (h : t = .memref N) (x : ⟦CryptoTy.memref N⟧),
      (⟨t, h.symm ▸ x⟩ : (t : CryptoTy) × ⟦t⟧) = ⟨.memref N, x⟩ := by
    intro t h x; subst h; rfl
  simp only [semScalar, ha, hi, hv, dif_pos (encodeTy_arr N)]
  congr 1
  funext s
  simp only [SEnvScalar.upd]
  split
  · exact congrArg some (key _ (encodeTy_arr N) _)
  · rfl

/-! ## 3. The waist semantics of the loads, constants, butterflies and stores -/

theorem upd_self {env : SEnvScalar} {x : String} {t : CryptoTy} (v : ⟦t⟧) :
    (env.upd x v) x = some ⟨t, v⟩ := by
  simp [SEnvScalar.upd]

/-- The loads leave `memGetDyn a i` in `f i` for the indices of `l` and change no name
outside `k` and the destinations. -/
theorem loads_run (f : ℕ → String) (arr : String) (n : ℕ) {a : Fin n → BitVec 64}
    (hn : n < 2 ^ 64) (hfa : ∀ i, f i ≠ arr) (hfk : ∀ i, f i ≠ "k") (hak : arr ≠ "k")
    (hinj : ∀ i j, f i = f j → i = j) :
    ∀ (l : List ℕ) {env : SEnvScalar}, l.Nodup → (∀ i ∈ l, i < n) →
      env arr = some ⟨.memref n, a⟩ →
      ∃ env', semScalar (seqL (loadStmts f arr n l)) env = some env'
        ∧ (∀ i ∈ l, env' (f i) = some ⟨.sword 64, memGetDyn a i⟩)
        ∧ ∀ s, s ≠ "k" → (∀ i ∈ l, s ≠ f i) → env' s = env s := by
  intro l
  induction l with
  | nil =>
    intro env _ _ _
    exact ⟨env, semScalar_seqL_nil env, fun _ h => by simp at h, fun _ _ _ => rfl⟩
  | cons c l ih =>
    intro env hnd hl ha
    obtain ⟨hcl, hnd'⟩ := List.nodup_cons.mp hnd
    have hc : c < n := hl c (List.mem_cons_self ..)
    set e0 := env.upd "k" (t := .sword 64) (BitVec.ofNat 64 c) with he0
    have h0a : e0 arr = some ⟨.memref n, a⟩ := by rw [he0, upd_ne' hak]; exact ha
    have h0k : e0 "k" = some ⟨.sword 64, BitVec.ofNat 64 c⟩ := upd_self _
    set e1 := e0.upd (f c) (t := .sword 64) (memGetDyn a c) with he1
    have r1 : semScalar (.RArrLoad ⟨f c, .TU64⟩ ⟨arr, .TArr n .TU64⟩ "k") e0 = some e1 := by
      rw [arrLoad_eq h0a h0k, ofNat_toNat_of_lt (by omega)]
    have h1a : e1 arr = some ⟨.memref n, a⟩ := by rw [he1, upd_ne' (hfa c).symm]; exact h0a
    obtain ⟨e2, r2, v2, f2⟩ := ih hnd' (fun i hi => hl i (List.mem_cons_of_mem _ hi)) h1a
    refine ⟨e2, ?_, ?_, ?_⟩
    · simp only [loadStmts, List.flatMap_cons, List.cons_append, List.nil_append] at r2 ⊢
      rw [semScalar_seqL_cons rfl, semScalar_seqL_cons r1]
      exact r2
    · intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · rw [f2 _ (hfk i) (fun j hj h => hcl (by rw [hinj _ _ h]; exact hj))]
        exact upd_self _
      · exact v2 i hi
    · intro s hsk hs
      rw [f2 s hsk (fun i hi => hs i (List.mem_cons_of_mem _ hi)),
        he1, upd_ne' (hs c (List.mem_cons_self ..)), he0, upd_ne' hsk]

/-- The stores write into `ys` at every index of `l` a word satisfying `P` at that index,
when `v{i}` holds such a word, and keep every other entry of `ys`. -/
theorem stores_run (N : ℕ) (hN : N < 2 ^ 64) (P : ℕ → BitVec 64 → Prop) :
    ∀ (l : List ℕ) {env : SEnvScalar} {o : Fin N → BitVec 64}, l.Nodup →
      (∀ i ∈ l, i < N) →
      (∀ i ∈ l, ∃ w, env (vN i) = some ⟨.sword 64, w⟩ ∧ P i w) →
      env "ys" = some ⟨.memref N, o⟩ →
      ∃ env' o', semScalar (seqL (storeStmts N l)) env = some env'
        ∧ env' "ys" = some ⟨.memref N, o'⟩
        ∧ (∀ i ∈ l, P i (memGetDyn o' i))
        ∧ ∀ j, j < N → j ∉ l → memGetDyn o' j = memGetDyn o j := by
  have hvk : ∀ i, vN i ≠ "k" := fun i => ne_of_head (vN_toList i) (by decide)
  have hvy : ∀ i, vN i ≠ "ys" := fun i => ne_of_head (vN_toList i) (by decide)
  intro l
  induction l with
  | nil =>
    intro env o _ _ _ ho
    exact ⟨env, o, semScalar_seqL_nil env, ho, fun _ h => by simp at h, fun _ _ _ => rfl⟩
  | cons c l ih =>
    intro env o hnd hl hv ho
    obtain ⟨hcl, hnd'⟩ := List.nodup_cons.mp hnd
    have hc : c < N := hl c (List.mem_cons_self ..)
    obtain ⟨w, hw, pw⟩ := hv c (List.mem_cons_self ..)
    set e0 := env.upd "k" (t := .sword 64) (BitVec.ofNat 64 c) with he0
    have h0y : e0 "ys" = some ⟨.memref N, o⟩ := by
      rw [he0, upd_ne' (show ("ys" : String) ≠ "k" by decide)]; exact ho
    have h0k : e0 "k" = some ⟨.sword 64, BitVec.ofNat 64 c⟩ := upd_self _
    have h0v : e0 (vN c) = some ⟨.sword 64, w⟩ := by rw [he0, upd_ne' (hvk c)]; exact hw
    set e1 := e0.upd "ys" (t := .memref N) (memSetDyn o c w) with he1
    have r1 : semScalar (.RArrStore ⟨"ys", .TArr N .TU64⟩ "k" ⟨vN c, .TU64⟩) e0 = some e1 := by
      rw [arrStoreN_eq h0y h0k h0v, ofNat_toNat_of_lt (by omega)]
    obtain ⟨e2, o2, r2, y2, p2, f2⟩ := ih (env := e1) (o := memSetDyn o c w) hnd'
      (fun i hi => hl i (List.mem_cons_of_mem _ hi))
      (fun i hi => by
        obtain ⟨u, hu, pu⟩ := hv i (List.mem_cons_of_mem _ hi)
        exact ⟨u, by rw [he1, upd_ne' (hvy i), he0, upd_ne' (hvk i)]; exact hu, pu⟩)
      (upd_self _)
    refine ⟨e2, o2, ?_, y2, ?_, ?_⟩
    · simp only [storeStmts, List.flatMap_cons, List.cons_append, List.nil_append] at r2 ⊢
      rw [semScalar_seqL_cons rfl, semScalar_seqL_cons r1]
      exact r2
    · intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · rw [f2 i hc hcl, Hax.WordOpsSim.memGetDyn_memSetDyn o hc hc, if_pos rfl]; exact pw
      · exact p2 i hi
    · intro j hj hjl
      have hjc : j ≠ c := fun h => hjl (h ▸ List.mem_cons_self ..)
      rw [f2 j hj (fun h => hjl (List.mem_cons_of_mem _ h)), Hax.WordOpsSim.memGetDyn_memSetDyn o hc hj,
        if_neg hjc]

/-- The butterflies of `l` move the field values by the left fold of `bupd` and change no
source name outside the scratch names and the value slots. -/
theorem bfly_run_frame {N T : ℕ} {Tw : ℕ → BB} :
    ∀ (l : List (ℕ × ℕ × ℕ)) {env : SEnvScalar} {Y : ℕ → BB}, PairsOk N T l →
      FInv N T env Y Tw →
      ∃ env', semScalar (seqL (bflyStmtsOf l)) env = some env'
        ∧ FInv N T env' (l.foldl (bupd Tw) Y) Tw
        ∧ ∀ s, ¬ isTmpName s → s ∉ bflyTemps → (∀ i, s ≠ vN i) → env' s = env s := by
  intro l
  induction l with
  | nil => intro env Y _ hI; exact ⟨env, semScalar_seqL_nil env, hI, fun _ _ _ _ => rfl⟩
  | cons q l ih =>
    intro env Y hok hI
    obtain ⟨h1, h2, h3, h4⟩ := hok q (List.mem_cons_self ..)
    obtain ⟨e1, r1, i1⟩ := finv_step hI h1 h2 h3 h4
    obtain ⟨a, hA, -⟩ := hI.val _ h1
    obtain ⟨b, hB, -⟩ := hI.val _ h2
    obtain ⟨w, hW, -⟩ := hI.tw _ h4
    obtain ⟨e1', r1', -, -, fr1⟩ :=
      butterfly_run _ _ (twN q.2.2) (bflyNames_of h3 _) hA hB hW hI.mu hI.p
    rw [r1] at r1'
    cases r1'
    obtain ⟨e2, r2, i2, fr2⟩ := ih (fun q' hq' => hok q' (List.mem_cons_of_mem _ hq')) i1
    refine ⟨e2, ?_, i2, ?_⟩
    · simp only [bflyStmtsOf, List.flatMap_cons] at r2 ⊢
      rw [semScalar_seqL_append, r1, Option.bind_some]
      exact r2
    · intro s hs ht hv
      rw [fr2 s hs ht hv, fr1 s hs ht (hv _) (hv _)]

/-! ## 4. The source is in the front's reads-bound fragment -/

/-- A judged body never unbinds a name. -/
theorem transTotal_isSome_mono {σ σ' : NameTys} {c : LowCT} (h : TransTotal σ c σ') :
    ∀ y, (σ y).isSome → (σ' y).isSome := by
  induction h with
  | rSkip => exact fun _ h => h
  | rBlock _ ih => exact ih
  | rSeq _ _ ih₁ ih₂ => exact fun y h => ih₂ y (ih₁ y h)
  | _ =>
    intro y hy
    unfold NameTys.upd
    split <;> simp_all

theorem loads_tt (f : ℕ → String) (arr : String) (n : ℕ) (hfs : ∀ i, ¬ isTmpName (f i))
    (hak : arr ≠ "k") :
    ∀ (l : List ℕ) {σ : NameTys}, (σ arr).isSome →
      ∃ σ', TransTotal σ (seqL (loadStmts f arr n l)) σ'
        ∧ (∀ y, (σ y).isSome → (σ' y).isSome)
        ∧ (∀ y, σ y = some (.sword 64) → σ' y = some (.sword 64))
        ∧ ∀ i ∈ l, σ' (f i) = some (.sword 64) := by
  have nk : ¬ isTmpName "k" := notTmp_of_head (by decide)
  intro l
  induction l with
  | nil => intro σ _; exact ⟨σ, .rSkip, fun _ h => h, fun _ h => h, fun _ h => by simp at h⟩
  | cons c l ih =>
    intro σ ha
    have h0a : ((σ.upd "k" (.sword 64)) arr).isSome := by rw [nameTys_upd_ne hak]; exact ha
    have t1 : TransTotal (σ.upd "k" (.sword 64)) (.RArrLoad ⟨f c, .TU64⟩ ⟨arr, .TArr n .TU64⟩ "k")
        ((σ.upd "k" (.sword 64)).upd (f c) (.sword 64)) :=
      .rArrLoad _ _ _ (hfs c) h0a (by rw [nameTys_upd_self]; rfl)
    have h1a : (((σ.upd "k" (.sword 64)).upd (f c) (.sword 64)) arr).isSome :=
      transTotal_isSome_mono t1 _ h0a
    obtain ⟨σ2, t2, s2, w2, v2⟩ := ih h1a
    refine ⟨σ2, ?_, ?_, ?_, ?_⟩
    · simp only [loadStmts, List.flatMap_cons, List.cons_append, List.nil_append,
        seqL] at t2 ⊢
      exact .rSeq (.rScalarSet "k" c nk) (.rSeq t1 t2)
    · intro y hy
      exact s2 y (transTotal_isSome_mono t1 y
        (transTotal_isSome_mono (TransTotal.rScalarSet (σ := σ) "k" c nk) y hy))
    · intro y hy; exact w2 y (upd_word (upd_word hy))
    · intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact w2 _ (nameTys_upd_self _ _ _)
      · exact v2 i hi

theorem stores_tt (N : ℕ) :
    ∀ (l : List ℕ) {σ : NameTys}, (σ "ys").isSome →
      (∀ i ∈ l, σ (vN i) = some (.sword 64)) →
      ∃ σ', TransTotal σ (seqL (storeStmts N l)) σ' ∧ (σ' "ys").isSome := by
  have nk : ¬ isTmpName "k" := notTmp_of_head (by decide)
  have ny : ¬ isTmpName "ys" := notTmp_of_head (by decide)
  have hvk : ∀ i, vN i ≠ "k" := fun i => ne_of_head (vN_toList i) (by decide)
  have hvy : ∀ i, vN i ≠ "ys" := fun i => ne_of_head (vN_toList i) (by decide)
  intro l
  induction l with
  | nil => intro σ hy _; exact ⟨σ, .rSkip, hy⟩
  | cons c l ih =>
    intro σ hy hv
    have h0y : ((σ.upd "k" (.sword 64)) "ys").isSome := by
      rw [nameTys_upd_ne (by decide)]; exact hy
    have h0v : ((σ.upd "k" (.sword 64)) (vN c)).isSome := by
      rw [nameTys_upd_ne (hvk c), hv c (List.mem_cons_self ..)]; rfl
    have t1 : TransTotal (σ.upd "k" (.sword 64))
        (.RArrStore ⟨"ys", .TArr N .TU64⟩ "k" ⟨vN c, .TU64⟩)
        ((σ.upd "k" (.sword 64)).upd "ys" (encodeTy (.TArr N .TU64))) :=
      .rArrStore _ _ _ ny h0y h0v (by rw [nameTys_upd_self]; rfl)
    obtain ⟨σ2, t2, y2⟩ := ih (σ := (σ.upd "k" (.sword 64)).upd "ys" (encodeTy (.TArr N .TU64)))
      (transTotal_isSome_mono t1 _ h0y) (fun i hi => by
      rw [nameTys_upd_ne (hvy i), nameTys_upd_ne (hvk i)]
      exact hv i (List.mem_cons_of_mem _ hi))
    refine ⟨σ2, ?_, y2⟩
    simp only [storeStmts, List.flatMap_cons, List.cons_append, List.nil_append, seqL] at t2 ⊢
    exact .rSeq (.rScalarSet "k" c nk) (.rSeq t1 t2)

/-! ## 5. The entry map -/

/-- The entry name-to-type map: the three array parameters. -/
def kArrTys (N T : ℕ) : NameTys := fun s =>
  if s = "xs" then some (.memref N) else if s = "ws" then some (.memref T)
  else if s = "ys" then some (.memref N) else none

theorem kArrTys_src (N T : ℕ) : SrcTys (kArrTys N T) := by
  intro x hx
  simp only [kArrTys] at hx
  by_cases h1 : x = "xs"
  · subst h1; exact notTmp_of_head (by decide)
  · by_cases h2 : x = "ws"
    · subst h2; exact notTmp_of_head (by decide)
    · by_cases h3 : x = "ys"
      · subst h3; exact notTmp_of_head (by decide)
      · simp [h1, h2, h3] at hx

theorem kArrTys_vmApprox (N T : ℕ) : VmApprox (kArrTys N T) (kArrVM N T) := by
  intro x t hx
  simp only [kArrTys] at hx
  by_cases h1 : x = "xs"
  · subst h1
    simp only [if_true, Option.some.injEq] at hx
    subst hx
    exact ⟨.here, by simp [kArrVM, VarMap.bind]⟩
  · by_cases h2 : x = "ws"
    · subst h2
      simp only [if_neg h1, if_true, Option.some.injEq] at hx
      subst hx
      exact ⟨.there .here, by simp [kArrVM, VarMap.bind]⟩
    · by_cases h3 : x = "ys"
      · subst h3
        simp only [if_neg h1, if_neg h2, if_true, Option.some.injEq] at hx
        subst hx
        exact ⟨.there (.there .here), by simp [kArrVM, VarMap.bind, VarMap.empty]⟩
      · simp [h1, h2, h3] at hx

theorem kArrBody_tt (N T : ℕ) (l : List (ℕ × ℕ × ℕ)) (hl : PairsOk N T l) :
    ∃ σ', TransTotal (kArrTys N T) (kArrBody N T l) σ' ∧ (σ' "ys").isSome := by
  have hxk : ("xs" : String) ≠ "k" := by decide
  have hwk : ("ws" : String) ≠ "k" := by decide
  obtain ⟨σ1, t1, s1, -, v1⟩ := loads_tt vN "xs" N vN_src hxk (List.range N)
    (σ := kArrTys N T) (by simp [kArrTys])
  obtain ⟨σ2, t2, s2, w2, v2⟩ := loads_tt twN "ws" T twN_src hwk (List.range T)
    (s1 _ (by simp [kArrTys]))
  have nmu : ¬ isTmpName "mu" := notTmp_of_head (by decide)
  have np : ¬ isTmpName "p" := notTmp_of_head (by decide)
  have t3 : TransTotal σ2 (seqL constStmts) ((σ2.upd "mu" (.sword 64)).upd "p" (.sword 64)) :=
    .rSeq (.rScalarSet "mu" _ nmu) (.rSeq (.rScalarSet "p" _ np) .rSkip)
  have hTy : TyW N T ((σ2.upd "mu" (.sword 64)).upd "p" (.sword 64)) :=
    ⟨fun i hi => upd_word (upd_word (w2 _ (v1 i (List.mem_range.mpr hi)))),
     fun j hj => upd_word (upd_word (v2 j (List.mem_range.mpr hj))),
     upd_word (nameTys_upd_self _ _ _), nameTys_upd_self _ _ _⟩
  obtain ⟨σ4, t4, m4⟩ := butterflies_tt l hl hTy
  have hy3 : (((σ2.upd "mu" (.sword 64)).upd "p" (.sword 64)) "ys").isSome :=
    transTotal_isSome_mono t3 _ (s2 _ (s1 _ (by simp [kArrTys])))
  obtain ⟨σ5, t5, y5⟩ := stores_tt N (List.range N) (transTotal_isSome_mono t4 _ hy3)
    (fun i hi => m4 _ (hTy.val i (List.mem_range.mp hi)))
  exact ⟨σ5, transTotal_seqL_append t1 (transTotal_seqL_append t2
    (transTotal_seqL_append t3 (transTotal_seqL_append t4 t5))), y5⟩

/-! ## 6. The front program on all inputs -/

/-- **A butterfly network over array parameters, generated through the front, on all
inputs.** For any admissible list `l` of butterflies over `N` values and `T` twiddles,
canonical value and twiddle arrays `x`, `w` and any initial output buffer `y`, the front
program `kFrontArr N T l` exists, lowers to `Com jasminDialect`, and the array it returns
holds at every entry `j < N` a canonical word whose field value is position `j` of the
butterflies of `l` applied in order to the field values of `x` with twiddles `w`. -/
theorem kFrontArr_denote (N T : ℕ) (l : List (ℕ × ℕ × ℕ)) (hl : PairsOk N T l)
    (hN : N < 2 ^ 64) (hT : T < 2 ^ 64)
    (x : Fin N → BitVec 64) (w : Fin T → BitVec 64) (y : Fin N → BitVec 64)
    (hx : ∀ i, (x i).toNat < 2013265921) (hw : ∀ j, (w j).toNat < 2013265921) :
    ∃ com, kFrontArr N T l = some com
      ∧ (DialectToJasminCom.cryptoDialectToJasminCom com).isSome
      ∧ ∀ j, j < N → Enc (memGetDyn (com.denote (kArrVal N T x w y)) j)
          (l.foldl (bupd (fun k => ((memGetDyn w k).toNat : BB)))
            (fun i => ((memGetDyn x i).toNat : BB)) j) := by
  obtain ⟨σ', htt, hys⟩ := kArrBody_tt N T l hl
  obtain ⟨o, htr, happ, hcont⟩ :=
    translateDialectControl_total htt (kArrVM N T) (kArrTys_src N T) (kArrTys_vmApprox N T)
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hys
  obtain ⟨vq, hvq⟩ := happ "ys" t ht
  -- the waist semantics of the body
  set V := kArrVal N T x w y
  set env0 := kArrEnv N T V
  have hc : ConsistentS (kArrVM N T) V env0 := fun _ => rfl
  have hxs : env0 "xs" = some ⟨.memref N, x⟩ := by
    simp [env0, kArrEnv, kArrVM, VarMap.bind, V, kArrVal]; rfl
  have hws : env0 "ws" = some ⟨.memref T, w⟩ := by
    simp [env0, kArrEnv, kArrVM, VarMap.bind, V, kArrVal]; rfl
  have hyss : env0 "ys" = some ⟨.memref N, y⟩ := by
    simp [env0, kArrEnv, kArrVM, VarMap.bind, VarMap.empty, V, kArrVal]; rfl
  have hvx : ∀ i, vN i ≠ "xs" := fun i => ne_of_head (vN_toList i) (by decide)
  have hvk : ∀ i, vN i ≠ "k" := fun i => ne_of_head (vN_toList i) (by decide)
  have htx : ∀ i, twN i ≠ "ws" := fun i => ne_of_head (twN_toList i) (by decide)
  have htk : ∀ i, twN i ≠ "k" := fun i => ne_of_head (twN_toList i) (by decide)
  obtain ⟨e1, r1, v1, f1⟩ := loads_run vN "xs" N hN hvx hvk (by decide)
    (fun _ _ h => vN_inj h) (List.range N) List.nodup_range (fun i hi => List.mem_range.mp hi)
    hxs
  have h1w : e1 "ws" = some ⟨.memref T, w⟩ := by
    rw [f1 _ (by decide) (fun i _ h => ne_of_head (vN_toList i) (by decide) h.symm)]
    exact hws
  obtain ⟨e2, r2, v2, f2⟩ := loads_run twN "ws" T hT htx htk (by decide)
    (fun _ _ h => twN_inj h) (List.range T) List.nodup_range (fun i hi => List.mem_range.mp hi)
    h1w
  set e3 := (e2.upd "mu" (t := .sword 64) (BitVec.ofNat 64 2290649223)).upd "p"
    (t := .sword 64) (BitVec.ofNat 64 2013265921) with he3
  have r3 : semScalar (seqL constStmts) e2 = some e3 := by
    rw [constStmts, semScalar_seqL_cons rfl, semScalar_seqL_cons rfl, semScalar_seqL_nil]
  have hv_mu : ∀ i, vN i ≠ "mu" := fun i => ne_of_head (vN_toList i) (by decide)
  have hv_p : ∀ i, vN i ≠ "p" := fun i => ne_of_head (vN_toList i) (by decide)
  have htw_mu : ∀ i, twN i ≠ "mu" := fun i => ne_of_head (twN_toList i) (by decide)
  have htw_p : ∀ i, twN i ≠ "p" := fun i => ne_of_head (twN_toList i) (by decide)
  have hI : FInv N T e3 (fun i => ((memGetDyn x i).toNat : BB))
      (fun k => ((memGetDyn w k).toNat : BB)) := by
    refine ⟨fun i hi => ⟨memGetDyn x i, ?_, ?_, rfl⟩, fun j hj => ⟨memGetDyn w j, ?_, ?_, rfl⟩,
      ?_, ?_⟩
    · rw [he3, upd_ne' (hv_p i), upd_ne' (hv_mu i),
        f2 _ (hvk i) (fun j _ h => vN_ne_twN i j h), v1 i (List.mem_range.mpr hi)]
    · rw [memGetDyn_of_lt x hi]; exact hx _
    · rw [he3, upd_ne' (htw_p j), upd_ne' (htw_mu j), v2 j (List.mem_range.mpr hj)]
    · rw [memGetDyn_of_lt w hj]; exact hw _
    · rw [he3, upd_ne' (show ("mu" : String) ≠ "p" by decide)]; exact upd_self _
    · rw [he3]; exact upd_self _
  obtain ⟨e4, r4, i4, f4⟩ := bfly_run_frame l hl hI
  have h4y : e4 "ys" = some ⟨.memref N, y⟩ := by
    rw [f4 _ (notTmp_of_head (by decide)) (by decide)
        (fun i h => ne_of_head (vN_toList i) (by decide) h.symm),
      he3, upd_ne' (show ("ys" : String) ≠ "p" by decide),
      upd_ne' (show ("ys" : String) ≠ "mu" by decide),
      f2 _ (by decide) (fun i _ h => ne_of_head (twN_toList i) (by decide) h.symm),
      f1 _ (by decide) (fun i _ h => ne_of_head (vN_toList i) (by decide) h.symm)]
    exact hyss
  obtain ⟨e5, o', r5, y5, p5, -⟩ := stores_run N hN
    (fun i u => Enc u (l.foldl (bupd (fun k => ((memGetDyn w k).toNat : BB)))
      (fun i => ((memGetDyn x i).toNat : BB)) i))
    (List.range N) List.nodup_range (fun i hi => List.mem_range.mp hi)
    (fun i hi => i4.val i (List.mem_range.mp hi)) h4y
  have hsem : semScalar (kArrBody N T l) env0 = some e5 := by
    rw [kArrBody, semScalar_seqL_append, r1, Option.bind_some, semScalar_seqL_append, r2,
      Option.bind_some, semScalar_seqL_append, r3, Option.bind_some, semScalar_seqL_append, r4,
      Option.bind_some, r5]
  obtain ⟨V', hc', htail⟩ := translateDialectControl_denote htt.toIsCoveredS (kArrVM N T) V
    env0 e5 o hc htr hsem
  -- the type of `ys` at exit
  have hty := hc' "ys"
  rw [hvq, y5] at hty
  simp only [Option.map_some, Option.some.injEq, Sigma.mk.injEq] at hty
  obtain ⟨rfl, -⟩ := hty
  obtain ⟨com, hcom, hlow⟩ := hcont (Com.ret (toVIRVar vq)) (by rfl)
  replace hcom : o.cont (Com.ret (toVIRVar vq)) = some com := hcom
  obtain ⟨com', hcom', hden⟩ := htail (Com.ret (toVIRVar vq))
  rw [hcom] at hcom'
  cases hcom'
  refine ⟨com, ?_, hlow, fun j hj => ?_⟩
  · simp only [kFrontArr, htr, hvq]; exact hcom
  · rw [hden, show (Com.ret (toVIRVar vq)).denote V' = (toVIRVar vq).lookup V' from rfl,
      ConsistentS.lookup_eq hc' hvq y5]
    exact p5 j (List.mem_range.mpr hj)

end CatCrypt.Crypto.SecureCompilation.VIR.Plonky3KFrontArr
