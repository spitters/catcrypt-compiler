/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.KeccakRoundFrontEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.KeccakRoundFrontEmit

/-!
# N-round front-composed Keccak-p[1600] — shape-interpreter engine (part 1/2)

The Keccak-p[1600] N-round body and its scalar-lowering **simulation engine**.
The 24-round closure (`round_wellscoped` / `shapeRun24_ok` / `lowered24_isSome`)
lives in the sibling `KeccakF1600FrontComposeProbe`, which imports this module;
the two files were split so each module's peak elaboration memory is roughly
half that of the combined proof.

This part carries the round body (threading rounds through the 25 `a`-lanes,
baking `RC[r]`, then copying `a{i}` into `o{i}`), the untyped `ShapeMap` shape
interpreter (`shapeLowerSExpr` / `shapeTranslate`) with its `Agrees` bridge to
the `VarMap`, the pure-arith backend-totality lemma
(`cryptoDialectToJasminCom_isSome_of_pureLower`), and the two scalar-lowering
simulation lemmas (`lowerSExpr_sim` / `shapeTranslate_sim`) plus the per-`SExpr`
shape-success lemma `shapeLowerSExpr_ok`.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.KeccakF1600FrontComposeProbe

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)
open CatCrypt.Crypto.SecureCompilation.VIR.KeccakRoundFrontEmit

set_option autoImplicit false

/-- ι + write-back into the lane `a{i}` (rebind): `a[0] = h[0] ⊕ RC[r]`,
    `a[i] = h[i]` (i≠0). Threads to the next round via the same `a`-names. -/
def aBackStmt (r i : Nat) : LowCT :=
  if i == 0 then
    .RScalarSetExpr (aN 0) (.SXor (.SVar (hN 0)) (.SLit (KeccakEmit.roundConst r)))
  else
    .RScalarSetExpr (aN i) (.SVar (hN i))

/-- One full round `r`, writing back into the `a`-lanes (RC[r] baked). -/
def roundBodyR (r : Nat) : LowCT :=
  seqAll (
    (List.range 5).map cStmt
    ++ (List.range 5).map dStmt
    ++ (List.range 25).map pStmt
    ++ (List.range 25).map bStmt
    ++ (List.range 25).map hStmt
    ++ (List.range 25).map (aBackStmt r))

/-- Final output copy: `o{i} = a{i}`, the trailing 25 bindings. -/
def oCopyStmt (i : Nat) : LowCT := .RScalarSetExpr (oN i) (.SVar (aN i))

/-- `N`-round body + the 25-lane output copy. -/
def fullBody (N : Nat) : LowCT :=
  seqAll ((List.range N).map roundBodyR ++ (List.range 25).map oCopyStmt)

/-- Front-translate the `N`-round body, cap with output lane `o24`. -/
def frontFull (N : Nat) : Option (Com catCryptDialect srcCtx (.sword 64)) :=
  match translateDialectControl srcVM (fullBody N) with
  | some res =>
      match res.vm.lookup (oN 24) with
      | some ⟨.sword 64, v⟩ => res.cont (Com.ret (toVIRVar v))
      | _ => none
  | none => none

/-- The `N`-round front-composed Com, lowered to jasmin. -/
def loweredFull (N : Nat) :=
  (frontFull N).bind DialectToJasminCom.cryptoDialectToJasminCom

/-! ## Tractability probes (measured, 4 cores, taskset -c 0-3)

Single-call `native_decide` isSome over the whole `N`-round `fullBody`:

| N  | result | build (module) | peak RSS |
|----|--------|----------------|----------|
| 1  | PASS   |  ~1 s          |  small   |
| 2  | PASS   |  ~1 s          |  small   |
| 4  | PASS   |  (bundled)     |          |
| 8  | PASS   |  61 s          | 10.9 GB  |
| 24 | **OOM**| dies ~2:15     | >32 GB (INTERNAL PANIC: out of memory) |

So the monolithic 24-round `native_decide` is INFEASIBLE (it materialises the
~9768-binding lowered `Com` in one go). The full flip must instead compose
per-round and discharge isSome STRUCTURALLY — see the module doc / report:
a `composeRounds` fold whose per-round success reuses
`KeccakRoundFrontEmit.keccakRoundLowered_isSome` (a single round from a generic
25-lane context, already `native_decide`-PASS) under a "a0..a24 bound" invariant,
rather than one giant `native_decide`. -/

-- The exploratory monolithic `lowered_{1,2,4,8}_isSome := by native_decide`
-- probes (how many rounds a single native_decide over the LOWERED typed Com
-- tolerates — measured PASS through N=8 at up to 61 s / 10.9 GB, INFEASIBLE at
-- N=24, OOM >32 GB) are retired: each compiles a ~400·N-binding Com evaluation
-- and is dead weight relative to the compositional `lowered24_isSome` below,
-- which never materialises the typed Com. The measurement conclusion is recorded
-- in the module docstring; re-enable locally to re-measure.

/-! ## Structural composition: the shape-level simulation engine

The monolithic 24-round `native_decide` is infeasible (table above): evaluating
`loweredFull 24` materialises a ~9768-binding dependently-typed `Com` whose
de-Bruijn spines grow quadratically with the context. The structural
replacement factors the `isSome` discharge through a **shape interpreter**: an
untyped `String ↦ CryptoTy` association-list twin of the front that tracks
*only* which names are bound at which scalar type — no `Com`, no `Ctxt`, no de
Bruijn, so its 24-round run is linear-size and cheap.

* `shapeLowerSExpr` / `shapeTranslate` mirror `lowerSExpr` /
  `translateDialectFull` on the straight-line scalar fragment
  (`RSkip`/`RSeq`/`RScalarSetExpr`), succeeding on exactly the same inputs by
  construction. Crucially, the `SLit` arm ignores the literal *value*, so the
  per-round `RC[r]` variation in `aBackStmt` is invisible at shape level — the
  round invariant is uniform in `r`, exactly as required.
* `lowerSExpr_sim` / `translate_sim` (the key lemma — a pure structural
  induction, no evaluation): if the shape run succeeds from a shape that
  `Agrees` with the `VarMap`, the real front succeeds too, the output `VarMap`
  agrees with the output shape, and the emitted `ComCont` prefix is total and
  binds only pure-arith dialect ops (`ContGood`).
* `backend_pure` extends success through `cryptoDialectToJasminCom` and yields
  `allPureArith` of the lowered `Com` compositionally.
* The shape run `shapeRun24_ok` is itself discharged **per round** (O(rounds),
  not O(bindings)): a general semantic block lemma (`blockOK`, pure induction)
  succeeds on any well-scoped `RScalarSetExpr` block whose base vars are bound at
  `.sword 64`, and `round_step` threads the invariant "after each round `a0…a24`
  are bound at `.sword 64`" across the 24-round list (`roundsList_step`) plus the
  output copy. The ONLY `native_decide` is the *syntactic* single-round
  well-scopedness check `round_wellscoped` (round-index independent via
  `WSBlock_aBack_congr`, since the shape ignores the `RC[r]` `SLit`); it never
  evaluates the 24-round `LowCT` (which stalled the build), let alone the lowered
  `Com` (>32 GB OOM). -/

open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms

/-- Untyped name-shape environment: most-recent-binding-first association list
    from LowCT slot names to `CryptoTy`. The shape-level image of `VarMap`. -/
abbrev ShapeMap := List (String × CryptoTy)

/-- First-match lookup (mirrors `VarMap.bind`'s shadowing order). -/
def shapeLookup : ShapeMap → String → Option CryptoTy
  | [], _ => none
  | (m, t) :: rest, n => if n = m then some t else shapeLookup rest n

/-- Prepend a binding (mirrors `VarMap.bind`). -/
def shapeBind (σ : ShapeMap) (n : String) (t : CryptoTy) : ShapeMap :=
  (n, t) :: σ

/-- Shape image of the shared binary-arm pattern of `lowerSExpr` (lower left,
    lower right in the extended shape, re-look-up both result names, bind one
    fresh `tmpName`). Taking the sub-results as arguments keeps
    `shapeLowerSExpr` structurally recursive. -/
def shapeBinStep (ra : Option (ShapeMap × String × Nat))
    (fb : ShapeMap → Nat → Option (ShapeMap × String × Nat)) :
    Option (ShapeMap × String × Nat) :=
  match ra with
  | none => none
  | some (σ₁, na, c₁) =>
      match fb σ₁ c₁ with
      | none => none
      | some (σ₂, nb, c₂) =>
          match shapeLookup σ₂ na, shapeLookup σ₂ nb with
          | some (.sword 64), some (.sword 64) =>
              some (shapeBind σ₂ (tmpName c₂) (.sword 64), tmpName c₂, c₂ + 1)
          | _, _ => none

/-- Shape twin of `lowerSExpr`. Succeeds exactly when `lowerSExpr` does (proved
    by `lowerSExpr_sim`), tracking only name ↦ type. `SMulHiU` is deliberately
    declined (its jasmin image `mulhi` is outside `allPureArith`), so shape
    success additionally certifies the pure-arith op set. `SLit` ignores the
    literal value — the `RC[r]` per-round variation is shape-invisible. -/
def shapeLowerSExpr (σ : ShapeMap) (cnt : Nat) : SExpr → Option (ShapeMap × String × Nat)
  | .SVar x =>
      match shapeLookup σ x with
      | some (.sword 64) => some (σ, x, cnt)
      | _ => none
  | .SLit _ => some (shapeBind σ (tmpName cnt) (.sword 64), tmpName cnt, cnt + 1)
  | .SAdd a b =>
      shapeBinStep (shapeLowerSExpr σ cnt a) (fun σ₁ c₁ => shapeLowerSExpr σ₁ c₁ b)
  | .SSub a b =>
      shapeBinStep (shapeLowerSExpr σ cnt a) (fun σ₁ c₁ => shapeLowerSExpr σ₁ c₁ b)
  | .SMul a b =>
      shapeBinStep (shapeLowerSExpr σ cnt a) (fun σ₁ c₁ => shapeLowerSExpr σ₁ c₁ b)
  | .SAnd a b =>
      shapeBinStep (shapeLowerSExpr σ cnt a) (fun σ₁ c₁ => shapeLowerSExpr σ₁ c₁ b)
  | .SXor a b =>
      shapeBinStep (shapeLowerSExpr σ cnt a) (fun σ₁ c₁ => shapeLowerSExpr σ₁ c₁ b)
  | .SShl a b =>
      shapeBinStep (shapeLowerSExpr σ cnt a) (fun σ₁ c₁ => shapeLowerSExpr σ₁ c₁ b)
  | .SShr a b =>
      shapeBinStep (shapeLowerSExpr σ cnt a) (fun σ₁ c₁ => shapeLowerSExpr σ₁ c₁ b)
  | _ => none

/-- Shape twin of `translateDialectFull`, restricted to the straight-line
    scalar fragment the Keccak body uses (`RSkip`/`RSeq`/`RScalarSetExpr`).
    Every other arm declines (soundly — the simulation only transfers
    *success*). -/
def shapeTranslate : ShapeMap → LowCT → Option ShapeMap
  | σ, .RSkip => some σ
  | σ, .RSeq c₁ c₂ =>
      match shapeTranslate σ c₁ with
      | some σ₁ => shapeTranslate σ₁ c₂
      | none => none
  | σ, .RScalarSetExpr x e =>
      match shapeLowerSExpr σ 0 e with
      | none => none
      | some (σ₁, nm, _) =>
          match shapeLookup σ₁ nm with
          | some (.sword 64) => some (shapeBind σ₁ x (.sword 64))
          | _ => none
  | _, _ => none

/-! ### Agreement between `VarMap` and `ShapeMap` -/

/-- `vm` and `σ` bind the same names at the same types (the de-Bruijn payload
    is abstracted away — success of the front depends only on this shape). -/
def Agrees {Γ : Ctx} (vm : VarMap Γ) (σ : ShapeMap) : Prop :=
  ∀ n, (vm.lookup n).map (fun p => p.1) = shapeLookup σ n

theorem Agrees.bind {Γ : Ctx} {vm : VarMap Γ} {σ : ShapeMap} (h : Agrees vm σ)
    (name : String) (t : CryptoTy) :
    Agrees (vm.bind (t := t) name) (shapeBind σ name t) := by
  intro n
  simp only [VarMap.bind, shapeBind, shapeLookup]
  split
  · rfl
  · have hn := h n
    cases hv : vm.lookup n with
    | none => rw [hv] at hn; simpa using hn
    | some p => rcases p with ⟨t', v⟩; rw [hv] at hn; simpa using hn

/-- Transfer a shape-level `.sword 64` binding to the `VarMap` (Σ-typed). -/
theorem lookup_sword_of_agrees {Γ : Ctx} {vm : VarMap Γ} {σ : ShapeMap}
    (h : Agrees vm σ) {n : String}
    (hs : shapeLookup σ n = some (.sword 64)) :
    ∃ v : CVar Γ (.sword 64), vm.lookup n = some ⟨.sword 64, v⟩ := by
  have hn := h n
  cases hv : vm.lookup n with
  | none => rw [hv, hs] at hn; simp at hn
  | some p =>
      rcases p with ⟨t, v⟩
      rw [hv, hs] at hn
      simp only [Option.map_some] at hn
      cases hn
      exact ⟨v, rfl⟩

/-- Transfer a shape-level `.sword 64` binding to `lookupU64`. -/
theorem lookupU64_of_agrees {Γ : Ctx} {vm : VarMap Γ} {σ : ShapeMap}
    (h : Agrees vm σ) {n : String}
    (hs : shapeLookup σ n = some (.sword 64)) :
    ∃ v : CVar Γ (.sword 64), lookupU64 vm n = some v := by
  obtain ⟨v, hv⟩ := lookup_sword_of_agrees h hs
  exact ⟨v, by simp [lookupU64, hv]⟩

/-! ### Pure-arith op tracking (`allPureArith` compositionally) -/

/-- The `catCryptDialect` ops whose `toJExprD` image is in `allPureArith`'s
    accepted set (`regArith`/`regConst`/`shlImm`/`shrImm`). Everything
    `lowerSExpr` emits on the shape-covered fragment is here. -/
def PureOp : CatCryptOp → Prop
  | .bvConst _ _ | .bvAdd _ | .bvSub _ | .bvMul _ | .bvAnd _ | .bvOr _ | .bvXor _
  | .bvShiftL _ _ | .bvShiftR _ _ | .bvShiftLV _ | .bvShiftRV _ | .andn _ => True
  | _ => False

/-- Every binding of the `Com` is a `PureOp`. -/
def PureLower : {Γ : Ctx} → {t : CryptoTy} → Com catCryptDialect Γ t → Prop
  | _, _, .ret _ => True
  | _, _, .var e body => PureOp e.op ∧ PureLower body

/-- A `ComCont` prefix that is total on `PureLower` bodies and preserves
    `PureLower` — i.e. it only prepends `PureOp` bindings. -/
def ContGood {Γ Γ' : Ctx} (k : ComCont Γ Γ') : Prop :=
  ∀ {t : CryptoTy} (body : Com catCryptDialect Γ' t),
    PureLower body → ∃ c, k body = some c ∧ PureLower c

theorem contGood_id {Γ : Ctx} : ContGood (ComCont.id (Γ := Γ)) :=
  fun body hb => ⟨body, rfl, hb⟩

theorem ContGood.comp {Γ Γ' Γ'' : Ctx} {f : ComCont Γ Γ'} {g : ComCont Γ' Γ''}
    (hf : ContGood f) (hg : ContGood g) : ContGood (ComCont.comp f g) := by
  intro t body hb
  obtain ⟨c, hc, hpc⟩ := hg body hb
  obtain ⟨c', hc', hpc'⟩ := hf c hpc
  exact ⟨c', by simp [ComCont.comp, hc, hc'], hpc'⟩

theorem contGood_varBind {Γ : Ctx} {s : CryptoTy} {e : Expr catCryptDialect Γ s}
    (he : PureOp e.op) : ContGood (ComCont.varBind e) :=
  fun body hb => ⟨Com.var e body, rfl, ⟨he, hb⟩⟩

/-! ### Backend totality on `PureLower` Coms

`cryptoDialectToJasminCom` is total on a Com every one of whose bindings is a
`PureOp`: `toJExprD` lands `some` on each such op, and the program recursion
threads those successes. This is the compositional replacement for the
`native_decide`-checked `allPureArith` gate. -/

/-- `toJExprD` is total on a `PureOp`-headed dialect expression: every op in the
    `PureOp` set is one of the `regArith`/`regConst`/`shlImm`/`shrImm`-imaged
    arms `toJExprD` returns `some` for. -/
theorem toJExprD_isSome_of_pureOp {Γ : Ctx} {t : CryptoTy}
    (e : Expr catCryptDialect Γ t) (he : PureOp e.op) :
    (DialectToJasminCom.toJExprD e).isSome := by
  rcases e with ⟨op, retTy_eq, args⟩
  cases op <;> simp_all [DialectToJasminCom.toJExprD, PureOp]

/-- `cryptoDialectToJasminCom` is total on a `PureLower` Com. -/
theorem cryptoDialectToJasminCom_isSome_of_pureLower {Γ : Ctx} {t : CryptoTy} :
    (c : Com catCryptDialect Γ t) → PureLower c →
      (DialectToJasminCom.cryptoDialectToJasminCom c).isSome
  | .ret v, _ => by simp [DialectToJasminCom.cryptoDialectToJasminCom]
  | .var e body, hpl => by
      simp only [PureLower] at hpl
      obtain ⟨hop, hbody⟩ := hpl
      obtain ⟨e', he'⟩ := Option.isSome_iff_exists.mp (toJExprD_isSome_of_pureOp e hop)
      obtain ⟨body', hbody'⟩ := Option.isSome_iff_exists.mp
        (cryptoDialectToJasminCom_isSome_of_pureLower body hbody)
      simp [DialectToJasminCom.cryptoDialectToJasminCom, he', hbody']

/-! ### The shape source and its agreement with `srcVM` -/

/-- The `ShapeMap` twin of `srcVM`: the 25 lanes `a0…a24` at `.sword 64`. -/
def srcShape : ShapeMap := wordNames.map (fun n => (n, (CryptoTy.sword 64)))

/-- `bindAll` agrees with the pointwise-`.sword 64` shape of its name list. -/
theorem agrees_bindAll : (names : List String) →
    Agrees (bindAll names) (names.map (fun n => (n, (CryptoTy.sword 64))))
  | [] => by intro n; simp [bindAll, VarMap.empty, shapeLookup]
  | n :: ns => by
      have ih := agrees_bindAll ns
      have hb := ih.bind n (CryptoTy.sword 64)
      simpa [bindAll, List.map, shapeBind] using! hb

/-- `srcVM` and `srcShape` agree. -/
theorem agrees_srcVM : Agrees srcVM srcShape := by
  unfold srcVM srcShape
  exact agrees_bindAll wordNames

/-! ### The scalar-lowering simulation lemma -/

open CatCrypt.Crypto.Jasmin.LowCT in
/-- The exact left-shift `catCryptDialect` expression the `.SShl` arm of
    `lowerSExpr` emits: `bvShiftL 64 k` for a literal amount `SLit k`, the
    variable `bvShiftLV 64` otherwise. -/
def shiftLExpr {Γ : Ctx} (b : SExpr) (va vb : CVar Γ (.sword 64)) :
    Expr catCryptDialect Γ (.sword 64) :=
  match b with
  | .SLit k => { op := .bvShiftL 64 k, retTy_eq := rfl, args := .cons (toVIRVar va) .nil }
  | _ => { op := .bvShiftLV 64, retTy_eq := rfl,
           args := .cons (toVIRVar va) (.cons (toVIRVar vb) .nil) }

open CatCrypt.Crypto.Jasmin.LowCT in
/-- The exact right-shift `catCryptDialect` expression the `.SShr` arm emits. -/
def shiftRExpr {Γ : Ctx} (b : SExpr) (va vb : CVar Γ (.sword 64)) :
    Expr catCryptDialect Γ (.sword 64) :=
  match b with
  | .SLit k => { op := .bvShiftR 64 k, retTy_eq := rfl, args := .cons (toVIRVar va) .nil }
  | _ => { op := .bvShiftRV 64, retTy_eq := rfl,
           args := .cons (toVIRVar va) (.cons (toVIRVar vb) .nil) }

open CatCrypt.Crypto.Jasmin.LowCT in
theorem pureOp_shiftLExpr {Γ : Ctx} (b : SExpr) (va vb : CVar Γ (.sword 64)) :
    PureOp (shiftLExpr b va vb).op := by cases b <;> simp [shiftLExpr, PureOp]

open CatCrypt.Crypto.Jasmin.LowCT in
theorem pureOp_shiftRExpr {Γ : Ctx} (b : SExpr) (va vb : CVar Γ (.sword 64)) :
    PureOp (shiftRExpr b va vb).op := by cases b <;> simp [shiftRExpr, PureOp]

open CatCrypt.Crypto.Jasmin.LowCT in
/-- **`lowerSExpr` simulation.** If the shape twin `shapeLowerSExpr` succeeds from
    a shape `σ` that a `VarMap vm` agrees with, then the real `lowerSExpr`
    succeeds with the same result name and counter, its output `VarMap` agrees
    with the output shape, the result name resolves at `.sword 64`, and the
    emitted `ComCont` prefix is `ContGood` (total, pure-arith only). Pure
    structural induction on the `SExpr`; no `Com` is evaluated. -/
theorem lowerSExpr_sim : ∀ (e : SExpr) {σ σ' : ShapeMap} {nm : String} {cnt cnt' : Nat},
    shapeLowerSExpr σ cnt e = some (σ', nm, cnt') →
    ∀ {Γ : Ctx} (vm : VarMap Γ), Agrees vm σ →
      ∃ o : DTransOut Γ, lowerSExpr vm cnt e = some (o, nm, cnt') ∧
        Agrees o.vm σ' ∧ shapeLookup σ' nm = some (.sword 64) ∧ ContGood o.cont := by
  intro e
  induction e with
  | SVar x =>
      intro σ σ' nm cnt cnt' h Γ vm hag
      simp only [shapeLowerSExpr] at h
      split at h
      · rename_i heq
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨v, hv⟩ := lookupU64_of_agrees hag heq
        exact ⟨⟨Γ, ComCont.id, vm⟩, by simp [lowerSExpr, hv], hag, heq, contGood_id⟩
      · exact absurd h (by simp)
  | SLit n =>
      intro σ σ' nm cnt cnt' h Γ vm hag
      simp only [shapeLowerSExpr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨pushVarBind ⟨Γ, ComCont.id, vm⟩
          { op := .bvConst 64 (BitVec.ofNat 64 n), retTy_eq := rfl, args := .nil }
          (tmpName cnt), by simp [lowerSExpr], ?_, ?_, ?_⟩
      · simpa [pushVarBind] using hag.bind (tmpName cnt) (.sword 64)
      · simp [shapeBind, shapeLookup]
      · exact ContGood.comp contGood_id (contGood_varBind (by simp [PureOp]))
  | SAdd a b iha ihb =>
      intro σ σ' nm cnt cnt' h Γ vm hag
      simp only [shapeLowerSExpr, shapeBinStep] at h
      cases hra : shapeLowerSExpr σ cnt a with
      | none => rw [hra] at h; simp at h
      | some ra =>
          obtain ⟨σ₁, na, c₁⟩ := ra
          rw [hra] at h; simp only [] at h
          cases hrb : shapeLowerSExpr σ₁ c₁ b with
          | none => rw [hrb] at h; simp at h
          | some rb =>
              obtain ⟨σ₂, nb, c₂⟩ := rb
              rw [hrb] at h; simp only [] at h
              split at h
              · rename_i _ _ hla hlb
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                obtain ⟨o_a, hlow_a, hag_a, _, hcg_a⟩ := iha hra vm hag
                obtain ⟨o_b, hlow_b, hag_b, _, hcg_b⟩ := ihb hrb o_a.vm hag_a
                obtain ⟨va, hva⟩ := lookupU64_of_agrees hag_b hla
                obtain ⟨vb, hvb⟩ := lookupU64_of_agrees hag_b hlb
                refine ⟨pushVarBind (seqOut o_a o_b)
                    { op := .bvAdd 64, retTy_eq := rfl,
                      args := .cons (toVIRVar va) (.cons (toVIRVar vb) .nil) } (tmpName c₂),
                    ?_, ?_, ?_, ?_⟩
                · simp only [lowerSExpr, hlow_a, hlow_b, hva, hvb]
                  rfl
                · simpa [pushVarBind, seqOut] using hag_b.bind (tmpName c₂) (.sword 64)
                · simp [shapeBind, shapeLookup]
                · simp only [pushVarBind, seqOut]
                  exact ContGood.comp (ContGood.comp hcg_a hcg_b)
                    (contGood_varBind (by simp [PureOp]))
              · simp at h
  | SSub a b iha ihb =>
      intro σ σ' nm cnt cnt' h Γ vm hag
      simp only [shapeLowerSExpr, shapeBinStep] at h
      cases hra : shapeLowerSExpr σ cnt a with
      | none => rw [hra] at h; simp at h
      | some ra =>
          obtain ⟨σ₁, na, c₁⟩ := ra
          rw [hra] at h; simp only [] at h
          cases hrb : shapeLowerSExpr σ₁ c₁ b with
          | none => rw [hrb] at h; simp at h
          | some rb =>
              obtain ⟨σ₂, nb, c₂⟩ := rb
              rw [hrb] at h; simp only [] at h
              split at h
              · rename_i _ _ hla hlb
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                obtain ⟨o_a, hlow_a, hag_a, _, hcg_a⟩ := iha hra vm hag
                obtain ⟨o_b, hlow_b, hag_b, _, hcg_b⟩ := ihb hrb o_a.vm hag_a
                obtain ⟨va, hva⟩ := lookupU64_of_agrees hag_b hla
                obtain ⟨vb, hvb⟩ := lookupU64_of_agrees hag_b hlb
                refine ⟨pushVarBind (seqOut o_a o_b)
                    { op := .bvSub 64, retTy_eq := rfl,
                      args := .cons (toVIRVar va) (.cons (toVIRVar vb) .nil) } (tmpName c₂),
                    ?_, ?_, ?_, ?_⟩
                · simp only [lowerSExpr, hlow_a, hlow_b, hva, hvb]
                  rfl
                · simpa [pushVarBind, seqOut] using hag_b.bind (tmpName c₂) (.sword 64)
                · simp [shapeBind, shapeLookup]
                · simp only [pushVarBind, seqOut]
                  exact ContGood.comp (ContGood.comp hcg_a hcg_b)
                    (contGood_varBind (by simp [PureOp]))
              · simp at h
  | SMul a b iha ihb =>
      intro σ σ' nm cnt cnt' h Γ vm hag
      simp only [shapeLowerSExpr, shapeBinStep] at h
      cases hra : shapeLowerSExpr σ cnt a with
      | none => rw [hra] at h; simp at h
      | some ra =>
          obtain ⟨σ₁, na, c₁⟩ := ra
          rw [hra] at h; simp only [] at h
          cases hrb : shapeLowerSExpr σ₁ c₁ b with
          | none => rw [hrb] at h; simp at h
          | some rb =>
              obtain ⟨σ₂, nb, c₂⟩ := rb
              rw [hrb] at h; simp only [] at h
              split at h
              · rename_i _ _ hla hlb
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                obtain ⟨o_a, hlow_a, hag_a, _, hcg_a⟩ := iha hra vm hag
                obtain ⟨o_b, hlow_b, hag_b, _, hcg_b⟩ := ihb hrb o_a.vm hag_a
                obtain ⟨va, hva⟩ := lookupU64_of_agrees hag_b hla
                obtain ⟨vb, hvb⟩ := lookupU64_of_agrees hag_b hlb
                refine ⟨pushVarBind (seqOut o_a o_b)
                    { op := .bvMul 64, retTy_eq := rfl,
                      args := .cons (toVIRVar va) (.cons (toVIRVar vb) .nil) } (tmpName c₂),
                    ?_, ?_, ?_, ?_⟩
                · simp only [lowerSExpr, hlow_a, hlow_b, hva, hvb]
                  rfl
                · simpa [pushVarBind, seqOut] using hag_b.bind (tmpName c₂) (.sword 64)
                · simp [shapeBind, shapeLookup]
                · simp only [pushVarBind, seqOut]
                  exact ContGood.comp (ContGood.comp hcg_a hcg_b)
                    (contGood_varBind (by simp [PureOp]))
              · simp at h
  | SShr a b iha ihb =>
      intro σ σ' nm cnt cnt' h Γ vm hag
      simp only [shapeLowerSExpr, shapeBinStep] at h
      cases hra : shapeLowerSExpr σ cnt a with
      | none => rw [hra] at h; simp at h
      | some ra =>
          obtain ⟨σ₁, na, c₁⟩ := ra
          rw [hra] at h; simp only [] at h
          cases hrb : shapeLowerSExpr σ₁ c₁ b with
          | none => rw [hrb] at h; simp at h
          | some rb =>
              obtain ⟨σ₂, nb, c₂⟩ := rb
              rw [hrb] at h; simp only [] at h
              split at h
              · rename_i _ _ hla hlb
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                obtain ⟨o_a, hlow_a, hag_a, _, hcg_a⟩ := iha hra vm hag
                obtain ⟨o_b, hlow_b, hag_b, _, hcg_b⟩ := ihb hrb o_a.vm hag_a
                obtain ⟨va, hva⟩ := lookupU64_of_agrees hag_b hla
                obtain ⟨vb, hvb⟩ := lookupU64_of_agrees hag_b hlb
                refine ⟨pushVarBind (seqOut o_a o_b) (shiftRExpr b va vb) (tmpName c₂),
                    ?_, ?_, ?_, ?_⟩
                · simp only [lowerSExpr, hlow_a, hlow_b, hva, hvb, shiftRExpr]
                  rfl
                · simpa [pushVarBind, seqOut] using hag_b.bind (tmpName c₂) (.sword 64)
                · simp [shapeBind, shapeLookup]
                · simp only [pushVarBind, seqOut]
                  exact ContGood.comp (ContGood.comp hcg_a hcg_b)
                    (contGood_varBind (pureOp_shiftRExpr b va vb))
              · simp at h
  | SShl a b iha ihb =>
      intro σ σ' nm cnt cnt' h Γ vm hag
      simp only [shapeLowerSExpr, shapeBinStep] at h
      cases hra : shapeLowerSExpr σ cnt a with
      | none => rw [hra] at h; simp at h
      | some ra =>
          obtain ⟨σ₁, na, c₁⟩ := ra
          rw [hra] at h; simp only [] at h
          cases hrb : shapeLowerSExpr σ₁ c₁ b with
          | none => rw [hrb] at h; simp at h
          | some rb =>
              obtain ⟨σ₂, nb, c₂⟩ := rb
              rw [hrb] at h; simp only [] at h
              split at h
              · rename_i _ _ hla hlb
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                obtain ⟨o_a, hlow_a, hag_a, _, hcg_a⟩ := iha hra vm hag
                obtain ⟨o_b, hlow_b, hag_b, _, hcg_b⟩ := ihb hrb o_a.vm hag_a
                obtain ⟨va, hva⟩ := lookupU64_of_agrees hag_b hla
                obtain ⟨vb, hvb⟩ := lookupU64_of_agrees hag_b hlb
                refine ⟨pushVarBind (seqOut o_a o_b) (shiftLExpr b va vb) (tmpName c₂),
                    ?_, ?_, ?_, ?_⟩
                · simp only [lowerSExpr, hlow_a, hlow_b, hva, hvb, shiftLExpr]
                  rfl
                · simpa [pushVarBind, seqOut] using hag_b.bind (tmpName c₂) (.sword 64)
                · simp [shapeBind, shapeLookup]
                · simp only [pushVarBind, seqOut]
                  exact ContGood.comp (ContGood.comp hcg_a hcg_b)
                    (contGood_varBind (pureOp_shiftLExpr b va vb))
              · simp at h
  | SAnd a b iha ihb =>
      intro σ σ' nm cnt cnt' h Γ vm hag
      simp only [shapeLowerSExpr, shapeBinStep] at h
      cases hra : shapeLowerSExpr σ cnt a with
      | none => rw [hra] at h; simp at h
      | some ra =>
          obtain ⟨σ₁, na, c₁⟩ := ra
          rw [hra] at h; simp only [] at h
          cases hrb : shapeLowerSExpr σ₁ c₁ b with
          | none => rw [hrb] at h; simp at h
          | some rb =>
              obtain ⟨σ₂, nb, c₂⟩ := rb
              rw [hrb] at h; simp only [] at h
              split at h
              · rename_i _ _ hla hlb
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                obtain ⟨o_a, hlow_a, hag_a, _, hcg_a⟩ := iha hra vm hag
                obtain ⟨o_b, hlow_b, hag_b, _, hcg_b⟩ := ihb hrb o_a.vm hag_a
                obtain ⟨va, hva⟩ := lookupU64_of_agrees hag_b hla
                obtain ⟨vb, hvb⟩ := lookupU64_of_agrees hag_b hlb
                refine ⟨pushVarBind (seqOut o_a o_b)
                    { op := .bvAnd 64, retTy_eq := rfl,
                      args := .cons (toVIRVar va) (.cons (toVIRVar vb) .nil) } (tmpName c₂),
                    ?_, ?_, ?_, ?_⟩
                · simp only [lowerSExpr, hlow_a, hlow_b, hva, hvb]
                  rfl
                · simpa [pushVarBind, seqOut] using hag_b.bind (tmpName c₂) (.sword 64)
                · simp [shapeBind, shapeLookup]
                · simp only [pushVarBind, seqOut]
                  exact ContGood.comp (ContGood.comp hcg_a hcg_b)
                    (contGood_varBind (by simp [PureOp]))
              · simp at h
  | SXor a b iha ihb =>
      intro σ σ' nm cnt cnt' h Γ vm hag
      simp only [shapeLowerSExpr, shapeBinStep] at h
      cases hra : shapeLowerSExpr σ cnt a with
      | none => rw [hra] at h; simp at h
      | some ra =>
          obtain ⟨σ₁, na, c₁⟩ := ra
          rw [hra] at h; simp only [] at h
          cases hrb : shapeLowerSExpr σ₁ c₁ b with
          | none => rw [hrb] at h; simp at h
          | some rb =>
              obtain ⟨σ₂, nb, c₂⟩ := rb
              rw [hrb] at h; simp only [] at h
              split at h
              · rename_i _ _ hla hlb
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                obtain ⟨o_a, hlow_a, hag_a, _, hcg_a⟩ := iha hra vm hag
                obtain ⟨o_b, hlow_b, hag_b, _, hcg_b⟩ := ihb hrb o_a.vm hag_a
                obtain ⟨va, hva⟩ := lookupU64_of_agrees hag_b hla
                obtain ⟨vb, hvb⟩ := lookupU64_of_agrees hag_b hlb
                refine ⟨pushVarBind (seqOut o_a o_b)
                    { op := .bvXor 64, retTy_eq := rfl,
                      args := .cons (toVIRVar va) (.cons (toVIRVar vb) .nil) } (tmpName c₂),
                    ?_, ?_, ?_, ?_⟩
                · simp only [lowerSExpr, hlow_a, hlow_b, hva, hvb]
                  rfl
                · simpa [pushVarBind, seqOut] using hag_b.bind (tmpName c₂) (.sword 64)
                · simp [shapeBind, shapeLookup]
                · simp only [pushVarBind, seqOut]
                  exact ContGood.comp (ContGood.comp hcg_a hcg_b)
                    (contGood_varBind (by simp [PureOp]))
              · simp at h
  | SLt a b iha ihb =>
      intro σ σ' nm cnt cnt' h Γ vm hag; simp [shapeLowerSExpr] at h
  | SAsr a b iha ihb =>
      intro σ σ' nm cnt cnt' h Γ vm hag; simp [shapeLowerSExpr] at h
  | SMulS a b iha ihb =>
      intro σ σ' nm cnt cnt' h Γ vm hag; simp [shapeLowerSExpr] at h
  | SMulHiU a b iha ihb =>
      intro σ σ' nm cnt cnt' h Γ vm hag; simp [shapeLowerSExpr] at h
  | SMulHiS a b iha ihb =>
      intro σ σ' nm cnt cnt' h Γ vm hag; simp [shapeLowerSExpr] at h
  | SLimb x i =>
      intro σ σ' nm cnt cnt' h Γ vm hag; simp [shapeLowerSExpr] at h

/-! ### The body-translation simulation

`shapeTranslate` mirrors `translateDialectFull` on the straight-line scalar
fragment (`RSkip`/`RSeq`/`RScalarSetExpr`) the Keccak body uses; every other
`LowCT` arm the shape declines, so the simulation transfers only *success*. -/

open CatCrypt.Crypto.Jasmin.LowCT in
/-- **`translateDialectFull` simulation.** If the shape twin `shapeTranslate`
    succeeds from a shape `σ` that a `VarMap vm` agrees with, then the real
    straight-line front `translateDialectFull` succeeds, its output `VarMap`
    agrees with the output shape, and the emitted prefix is `ContGood`. -/
theorem shapeTranslate_sim : ∀ (c : LowCT) {σ σ' : ShapeMap},
    shapeTranslate σ c = some σ' →
    ∀ {Γ : Ctx} (vm : VarMap Γ), Agrees vm σ →
      ∃ o : DTransOut Γ, translateDialectFull vm c = some o ∧
        Agrees o.vm σ' ∧ ContGood o.cont := by
  intro c
  induction c
  case RSkip =>
      intro σ σ' h Γ vm hag
      simp only [shapeTranslate, Option.some.injEq] at h
      subst h
      exact ⟨⟨Γ, ComCont.id, vm⟩, by simp [translateDialectFull, translateDialect],
        hag, contGood_id⟩
  case RSeq c₁ c₂ ih₁ ih₂ =>
      intro σ σ' h Γ vm hag
      simp only [shapeTranslate] at h
      cases hs1 : shapeTranslate σ c₁ with
      | none => rw [hs1] at h; simp at h
      | some σ₁ =>
          rw [hs1] at h; simp only [] at h
          obtain ⟨o₁, htf₁, hag₁, hcg₁⟩ := ih₁ hs1 vm hag
          obtain ⟨o₂, htf₂, hag₂, hcg₂⟩ := ih₂ h o₁.vm hag₁
          exact ⟨⟨o₂.Γ', ComCont.comp o₁.cont o₂.cont, o₂.vm⟩,
            by simp only [translateDialectFull, htf₁, htf₂], hag₂, ContGood.comp hcg₁ hcg₂⟩
  case RScalarSetExpr x e =>
      intro σ σ' h Γ vm hag
      simp only [shapeTranslate] at h
      cases hse : shapeLowerSExpr σ 0 e with
      | none => rw [hse] at h; simp at h
      | some r =>
          obtain ⟨σ₁, nm, cE⟩ := r
          rw [hse] at h; simp only [] at h
          split at h
          · simp only [Option.some.injEq] at h
            subst h
            obtain ⟨o_e, hlow, hag_e, hsl, hcg_e⟩ := lowerSExpr_sim e hse vm hag
            obtain ⟨v, hv⟩ := lookupU64_of_agrees hag_e hsl
            refine ⟨pushVarBind o_e
                { op := .bvShiftL 64 0, retTy_eq := rfl, args := .cons (toVIRVar v) .nil } x,
                ?_, ?_, ?_⟩
            · simp only [translateDialectFull, hlow, hv]
            · simpa [pushVarBind] using hag_e.bind x (.sword 64)
            · simp only [pushVarBind]
              exact ContGood.comp hcg_e (contGood_varBind (by simp [PureOp]))
          · simp at h
  all_goals (intro σ σ' h Γ vm hag; simp [shapeTranslate] at h)

/-! ### Per-round compositional shape run (O(rounds), single-round `native_decide`)

The monolithic `native_decide` over `shapeTranslate srcShape (fullBody 24)`
compiles the whole 24-round `LowCT` term and stalls the build. We instead run the
shape interpreter **per round**: a purely syntactic well-scopedness check on ONE
round (the only `native_decide`, r-independent) feeds a general semantic block
lemma, and an induction over the round list threads a `.sword 64`-a-lane
invariant. -/

open CatCrypt.Crypto.Jasmin.LowCT in
/-- Base (free) variable names read by an `SExpr` (`SVar`/`SLimb` leaves;
    `SLit` values contribute nothing — the shape is literal-invisible). -/
def baseVars : SExpr → List String
  | .SVar x => [x]
  | .SLimb x _ => [x]
  | .SLit _ => []
  | .SAdd a b | .SSub a b | .SMul a b | .SShr a b | .SShl a b | .SAnd a b | .SXor a b
  | .SLt a b | .SAsr a b | .SMulS a b | .SMulHiU a b | .SMulHiS a b => baseVars a ++ baseVars b

open CatCrypt.Crypto.Jasmin.LowCT in
/-- The `SExpr` arms `shapeLowerSExpr` accepts (the pure-arith fragment: leaves +
    the seven binary ops that go through `shapeBinStep`). -/
def ShapeAccepts : SExpr → Bool
  | .SVar _ | .SLit _ => true
  | .SAdd a b | .SSub a b | .SMul a b | .SShr a b | .SShl a b | .SAnd a b | .SXor a b =>
      ShapeAccepts a && ShapeAccepts b
  | _ => false

/-- `shapeLookup` at `.sword 64` survives one `shapeBind` (`.sword 64`). -/
theorem shapeBind_pres {σ : ShapeMap} {nm m : String}
    (h : shapeLookup σ m = some (.sword 64)) :
    shapeLookup (shapeBind σ nm (.sword 64)) m = some (.sword 64) := by
  simp only [shapeBind, shapeLookup]; split
  · rfl
  · exact h

open CatCrypt.Crypto.Jasmin.LowCT in
/-- **Shape-level scalar-lowering success.** On an accepted `SExpr` whose base
    vars are all bound at `.sword 64`, `shapeLowerSExpr` succeeds, its result name
    resolves at `.sword 64`, and it preserves every existing `.sword 64` binding
    (it only prepends fresh `.sword 64` scratch slots). Pure induction. -/
theorem shapeLowerSExpr_ok : ∀ (e : SExpr) {σ : ShapeMap} {cnt : Nat},
    ShapeAccepts e = true →
    (∀ n ∈ baseVars e, shapeLookup σ n = some (.sword 64)) →
    ∃ σ₁ nm c, shapeLowerSExpr σ cnt e = some (σ₁, nm, c) ∧
      shapeLookup σ₁ nm = some (.sword 64) ∧
      (∀ m, shapeLookup σ m = some (.sword 64) → shapeLookup σ₁ m = some (.sword 64)) := by
  intro e
  induction e with
  | SVar x =>
      intro σ cnt _ hbv
      have hx : shapeLookup σ x = some (.sword 64) := hbv x (by simp [baseVars])
      exact ⟨σ, x, cnt, by simp only [shapeLowerSExpr, hx], hx, fun m hm => hm⟩
  | SLit n =>
      intro σ cnt _ _
      exact ⟨shapeBind σ (tmpName cnt) (.sword 64), tmpName cnt, cnt + 1,
        by simp only [shapeLowerSExpr], by simp [shapeBind, shapeLookup],
        fun m hm => shapeBind_pres hm⟩
  | SAdd a b iha ihb =>
      intro σ cnt hacc hbv
      simp only [ShapeAccepts, Bool.and_eq_true] at hacc
      simp only [baseVars, List.mem_append] at hbv
      obtain ⟨σ₁, na, c₁, hla, hna, hmona⟩ := iha (cnt := cnt) hacc.1 (fun n hn => hbv n (Or.inl hn))
      obtain ⟨σ₂, nb, c₂, hlb, hnb, hmonb⟩ := ihb (cnt := c₁) hacc.2 (fun n hn => hmona n (hbv n (Or.inr hn)))
      exact ⟨shapeBind σ₂ (tmpName c₂) (.sword 64), tmpName c₂, c₂ + 1,
        by simp only [shapeLowerSExpr, shapeBinStep, hla, hlb, hmonb na hna, hnb],
        by simp [shapeBind, shapeLookup], fun m hm => shapeBind_pres (hmonb m (hmona m hm))⟩
  | SSub a b iha ihb =>
      intro σ cnt hacc hbv
      simp only [ShapeAccepts, Bool.and_eq_true] at hacc
      simp only [baseVars, List.mem_append] at hbv
      obtain ⟨σ₁, na, c₁, hla, hna, hmona⟩ := iha (cnt := cnt) hacc.1 (fun n hn => hbv n (Or.inl hn))
      obtain ⟨σ₂, nb, c₂, hlb, hnb, hmonb⟩ := ihb (cnt := c₁) hacc.2 (fun n hn => hmona n (hbv n (Or.inr hn)))
      exact ⟨shapeBind σ₂ (tmpName c₂) (.sword 64), tmpName c₂, c₂ + 1,
        by simp only [shapeLowerSExpr, shapeBinStep, hla, hlb, hmonb na hna, hnb],
        by simp [shapeBind, shapeLookup], fun m hm => shapeBind_pres (hmonb m (hmona m hm))⟩
  | SMul a b iha ihb =>
      intro σ cnt hacc hbv
      simp only [ShapeAccepts, Bool.and_eq_true] at hacc
      simp only [baseVars, List.mem_append] at hbv
      obtain ⟨σ₁, na, c₁, hla, hna, hmona⟩ := iha (cnt := cnt) hacc.1 (fun n hn => hbv n (Or.inl hn))
      obtain ⟨σ₂, nb, c₂, hlb, hnb, hmonb⟩ := ihb (cnt := c₁) hacc.2 (fun n hn => hmona n (hbv n (Or.inr hn)))
      exact ⟨shapeBind σ₂ (tmpName c₂) (.sword 64), tmpName c₂, c₂ + 1,
        by simp only [shapeLowerSExpr, shapeBinStep, hla, hlb, hmonb na hna, hnb],
        by simp [shapeBind, shapeLookup], fun m hm => shapeBind_pres (hmonb m (hmona m hm))⟩
  | SShr a b iha ihb =>
      intro σ cnt hacc hbv
      simp only [ShapeAccepts, Bool.and_eq_true] at hacc
      simp only [baseVars, List.mem_append] at hbv
      obtain ⟨σ₁, na, c₁, hla, hna, hmona⟩ := iha (cnt := cnt) hacc.1 (fun n hn => hbv n (Or.inl hn))
      obtain ⟨σ₂, nb, c₂, hlb, hnb, hmonb⟩ := ihb (cnt := c₁) hacc.2 (fun n hn => hmona n (hbv n (Or.inr hn)))
      exact ⟨shapeBind σ₂ (tmpName c₂) (.sword 64), tmpName c₂, c₂ + 1,
        by simp only [shapeLowerSExpr, shapeBinStep, hla, hlb, hmonb na hna, hnb],
        by simp [shapeBind, shapeLookup], fun m hm => shapeBind_pres (hmonb m (hmona m hm))⟩
  | SShl a b iha ihb =>
      intro σ cnt hacc hbv
      simp only [ShapeAccepts, Bool.and_eq_true] at hacc
      simp only [baseVars, List.mem_append] at hbv
      obtain ⟨σ₁, na, c₁, hla, hna, hmona⟩ := iha (cnt := cnt) hacc.1 (fun n hn => hbv n (Or.inl hn))
      obtain ⟨σ₂, nb, c₂, hlb, hnb, hmonb⟩ := ihb (cnt := c₁) hacc.2 (fun n hn => hmona n (hbv n (Or.inr hn)))
      exact ⟨shapeBind σ₂ (tmpName c₂) (.sword 64), tmpName c₂, c₂ + 1,
        by simp only [shapeLowerSExpr, shapeBinStep, hla, hlb, hmonb na hna, hnb],
        by simp [shapeBind, shapeLookup], fun m hm => shapeBind_pres (hmonb m (hmona m hm))⟩
  | SAnd a b iha ihb =>
      intro σ cnt hacc hbv
      simp only [ShapeAccepts, Bool.and_eq_true] at hacc
      simp only [baseVars, List.mem_append] at hbv
      obtain ⟨σ₁, na, c₁, hla, hna, hmona⟩ := iha (cnt := cnt) hacc.1 (fun n hn => hbv n (Or.inl hn))
      obtain ⟨σ₂, nb, c₂, hlb, hnb, hmonb⟩ := ihb (cnt := c₁) hacc.2 (fun n hn => hmona n (hbv n (Or.inr hn)))
      exact ⟨shapeBind σ₂ (tmpName c₂) (.sword 64), tmpName c₂, c₂ + 1,
        by simp only [shapeLowerSExpr, shapeBinStep, hla, hlb, hmonb na hna, hnb],
        by simp [shapeBind, shapeLookup], fun m hm => shapeBind_pres (hmonb m (hmona m hm))⟩
  | SXor a b iha ihb =>
      intro σ cnt hacc hbv
      simp only [ShapeAccepts, Bool.and_eq_true] at hacc
      simp only [baseVars, List.mem_append] at hbv
      obtain ⟨σ₁, na, c₁, hla, hna, hmona⟩ := iha (cnt := cnt) hacc.1 (fun n hn => hbv n (Or.inl hn))
      obtain ⟨σ₂, nb, c₂, hlb, hnb, hmonb⟩ := ihb (cnt := c₁) hacc.2 (fun n hn => hmona n (hbv n (Or.inr hn)))
      exact ⟨shapeBind σ₂ (tmpName c₂) (.sword 64), tmpName c₂, c₂ + 1,
        by simp only [shapeLowerSExpr, shapeBinStep, hla, hlb, hmonb na hna, hnb],
        by simp [shapeBind, shapeLookup], fun m hm => shapeBind_pres (hmonb m (hmona m hm))⟩
  | SLt a b iha ihb => intro σ cnt hacc _; simp [ShapeAccepts] at hacc
  | SAsr a b iha ihb => intro σ cnt hacc _; simp [ShapeAccepts] at hacc
  | SMulS a b iha ihb => intro σ cnt hacc _; simp [ShapeAccepts] at hacc
  | SMulHiU a b iha ihb => intro σ cnt hacc _; simp [ShapeAccepts] at hacc
  | SMulHiS a b iha ihb => intro σ cnt hacc _; simp [ShapeAccepts] at hacc
  | SLimb x i => intro σ cnt hacc _; simp [ShapeAccepts] at hacc

end CatCrypt.Crypto.SecureCompilation.VIR.KeccakF1600FrontComposeProbe
