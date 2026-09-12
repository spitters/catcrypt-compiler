/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Hax.HaxToLowCTSim_Main_Full
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_Main_Full
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_Program
public meta import CatCrypt.Crypto.SecureCompilation.Ascent.KeystoneControl
public import CatCrypt.Crypto.SecureCompilation.Ascent.KeystoneControl

/-!
# Loop / array source tower: welding `haxToLowCT_simulates_full` to the ascent emit weld

The straight-line feSub tower (`Ascent/FeSubSourceTower.lean`) welded the source
leg through `RustSubsetToLowCT.lowerRefines`, which covers only the `if`-free
straight-line fragment.  The tower for the **loop / array / call** fragment is
`haxToLowCT_simulates_full` (`Hax/HaxToLowCTSim_Main_Full.lean`), which carries a
source `ImpExpr` to a `RustExec` run of its `haxToLowCT` image — the image that,
for the array and bounded-loop arms, is *not* straight-line.

This module deploys that tower for a concrete **array-write** kernel (`arrKernel`,
whose `haxToLowCT` image is headed by a dynamic-index `RArrStore` — the
smallest non-straight-line kernel the tower's array arm covers), and pairs it with
the bounded-loop ascent weld (`RFor`, via `keystone_for`).  It also records,
as theorems where possible, the two coverage gaps that keep a *single*
source-loop-to-bytes chain from closing today.

## The two legs

* **Source → `RustExec` (via the tower).**  `arrKernel_source_to_rustexec`
  invokes `haxToLowCT_simulates_full` at `arrKernel`.  From the source `evalImp`
  denotation and the input tower agreement, it delivers a `RustExec` run of the
  `RArrStore`-headed LowCT image.  This is the loop/array analogue of
  `feSubSrc_refines`.
* **Bounded `RFor` → clean spec (the ascent weld).**  `loop_keystone_emit`
  reuses `keystone_for` on the closed bounded-loop kernel `forClosedKernel`: the
  emitted output word is pinned to the clean `ZMod 2^64` loop spec `(v : ZMod
  2^64)`.  A bounded-`RFor` emit conclusion.

## The two walls (why the legs do not yet compose into one chain)

* **Loop source preimage.**  The only source `ImpExpr` constructor whose
  `haxToLowCT` image is the ascent-covered bounded `RFor` is `.forFold`, and its
  source semantics is empty: `evalImp bi fuel (.forFold …) env = none`
  (`evalImp_forFold_eq_none`, a post-phase error constructor).  So the tower never
  produces an inhabited `RustExec` over an `RFor` from a source loop.  The
  tower's one loop arm, `.whileLoop (.var _) _`, lowers to `RWhileNz` —
  a node `semScalar` (hence `Corres`) does not interpret at all — so it cannot
  reach the ascent weld either.  `loop_forFold_source_vacuous` witnesses the
  first half.
* **Array ascent leaf.**  `semScalar` *does* interpret `RArrStore`
  (`arrStore_executes`), but the ascent calculus (`Ascent/Corres.lean`,
  `Control.lean`, `Ascend.lean`) provides a `Corres` value-leaf only for
  `RScalarSet` / `RScalarSetExpr` / `RIfNz` / `RFor` — **none for
  `RArrStore` / `RArrLoad`**.  So the array-write image the tower delivers has no
  weld to attach to.

Part of the AutoCorres-in-Lean ascent begun by Sebastian Graf (`sgraf812/ascent`);
see `Corres.lean`.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Hax (ImpExpr Value Env Builtins)
open CatCrypt.Crypto.Hax
  (haxToLowCT evalImp HaxToLowCTSimulatesFull ValueTowerBridge FullSimPreconds
   envAgreesRustFull
   Hyp_match_full Hyp_whileLoop_full Hyp_arrayUpdate_full Hyp_index_full
   Hyp_letBindVarAlias_full Hyp_letBindProj_full Hyp_index_full_of_vacuity
   TowerFresh haxToLowCT_simulates_full towerOfCallName haxArgsToLocated
   ArgsTowerBound evalImp_forFold_eq_none
   ProgSim ProjPreconds ProgramSimArms TowerScope simScope isVar
   haxToLowCT_simulates_program progSim_index_of_vacuity)
open CatCrypt.Crypto.Jasmin.LowCT
  (LowCT RustState RustExec LeafSpec RustVal locatedLookup Located TowerType)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar (semScalar)

namespace CatCrypt.Crypto.SecureCompilation.Ascent

/-! ## §1  The concrete array-write source kernel and its `RArrStore` image -/

/-- The smallest array-write source kernel: `let _ = array_update(arr, idx, src)`
    (functional in-place store), returning unit.  Its `haxToLowCT` image is an
    `RSeq` headed by a dynamic-index `RArrStore` — a non-straight-line
    node, outside the `RustSubsetToLowCT` straight-line fragment the feSub tower
    used. -/
def arrKernel : ImpExpr :=
  .letBind "_" (.app "array_update" [.var "arr", .var "idx", .var "src"]) .unitVal

/-- The `haxToLowCT` image of `arrKernel` is `some c` with `c` headed by an
    `RArrStore` node.  This pins that the tower's source leg for this kernel
    lands on the array-write arm (not a straight-line fallback). -/
def headIsArrStoreOpt : Option LowCT → Bool
  | some (.RSeq (.RArrStore _ _ _) _) => true
  | _ => false

theorem arrKernel_image_headArrStore :
    headIsArrStoreOpt (haxToLowCT arrKernel) = true := by native_decide

/-- Any LowCT image of `arrKernel` is an `RSeq` headed by an `RArrStore` — the
    tower's array-write arm, not a straight-line fallback.  Follows from the
    (decidable) shape witness `arrKernel_image_headArrStore`. -/
theorem arrKernel_image_shape {c : LowCT} (hImg : haxToLowCT arrKernel = some c) :
    ∃ arr src idxVar tail, c = .RSeq (.RArrStore arr idxVar src) tail := by
  have h := arrKernel_image_headArrStore
  rw [hImg] at h
  match c, h with
  | .RSeq (.RArrStore arr idxVar src) tail, _ => exact ⟨arr, src, idxVar, tail, rfl⟩

/-! ## §2  Source → `RustExec` via `haxToLowCT_simulates_full` (the tower leg)

The loop/array analogue of `feSubSrc_refines`.  Every hypothesis is a
tower precondition; the array-store simulation hypothesis `hArrUpd` is the one the
kernel exercises (the dynamic-array-store semantic bridge, protocol
specific — see `Hyp_arrayUpdate_full`'s docstring).  The `index` arm hypothesis is
*discharged here* by vacuity (`Hyp_index_full_of_vacuity`), since `arrKernel` does
not index.  The remaining structural hypotheses (`hMatch`, `hWhileLoop`, `hAlias`,
`hProj`) are the globally-pending / non-exercised tower arms, carried as explicit
interface. -/

/-- **`arrKernel_source_to_rustexec`.**  Deploys `haxToLowCT_simulates_full` at the
    concrete array-write kernel `arrKernel`.  From the source `evalImp` denotation
    (`hEval`) and the input tower agreement (`hAgree`), the tower delivers a
    `RustExec` run of the image `c` (`RArrStore`-headed, by `arrKernel_image_shape`),
    with the output tower agreement preserved.  `hIndex` is discharged internally
    via vacuity; the
    remaining tower hypotheses are explicit named interface. -/
theorem arrKernel_source_to_rustexec
    (bridge : ValueTowerBridge) (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (hMatch : Hyp_match_full bridge bi fuel N leafSpec)
    (hWhileLoop : Hyp_whileLoop_full bridge bi fuel N leafSpec)
    (hArrUpd : Hyp_arrayUpdate_full bridge bi fuel N leafSpec)
    (hAlias : Hyp_letBindVarAlias_full bridge bi fuel N leafSpec)
    (hProj : Hyp_letBindProj_full bridge bi fuel N leafSpec)
    (hPre : FullSimPreconds bi leafSpec bridge)
    (hScalarFresh : ∀ (name : String) (rs : RustState), TowerFresh rs name)
    (hArgsEnvAll :
       ∀ (_f : String) (args : List ImpExpr) (env : Env),
         ∀ a ∈ args, ∃ n, a = .var n ∧ ∃ w, env n = some w)
    (hArgsBoundAll :
       ∀ (f : String) (args : List ImpExpr) (rs : RustState) args',
         haxArgsToLocated (towerOfCallName f) args = some args' →
         ArgsTowerBound rs args')
    (hArgsFreshAll :
       ∀ (f : String) (args : List ImpExpr) (name : String) args',
         haxArgsToLocated (towerOfCallName f) args = some args' →
         ∀ a ∈ args', a.locVar ≠ name)
    (hDestBoundAll :
       ∀ (f : String) (name : String) (rs : RustState),
         ∃ oldDestV : RustVal (towerOfCallName f),
           locatedLookup rs { locVar := name, locSrc := towerOfCallName f }
             = some oldDestV)
    (hIdxVac : ∀ vals, bi "index" vals = none)
    (c : LowCT) (hImg : haxToLowCT arrKernel = some c)
    (env env' : Env) (rs : RustState) (v : Value)
    (hEval : evalImp bi fuel arrKernel env = some (v, env'))
    (hAgree : envAgreesRustFull bridge env rs) :
    ∃ rs', RustExec N leafSpec c rs rs' ∧ envAgreesRustFull bridge env' rs' := by
  have hIndex : Hyp_index_full bridge bi fuel N leafSpec :=
    Hyp_index_full_of_vacuity bridge bi fuel N leafSpec hIdxVac
  have tower :=
    haxToLowCT_simulates_full bridge bi fuel N leafSpec
      hMatch hWhileLoop hArrUpd hIndex hAlias hProj hPre hScalarFresh
      hArgsEnvAll hArgsBoundAll hArgsFreshAll hDestBoundAll arrKernel
  exact tower c env env' rs v hImg hEval hAgree

/-! ### §2.1  The tower leg on the program-level simulation

`haxToLowCT_simulates_program` replaces the universally quantified call-side
conditions of `haxToLowCT_simulates_full` by the scope checker `simScope` on the
source program and two preconditions on the entry state.  `arrKernel` has no
scalar bindings and its only call is the array store, so the checker accepts it
from every entry scope with the empty scalar-name set, the entry-state
preconditions are trivial at the empty scope, and the array-store arm is the one
hypothesis the kernel exercises. -/

/-- The scope checker accepts `arrKernel` from every entry scope. -/
theorem simScope_arrKernel (Γ : TowerScope) : simScope [] Γ arrKernel = some Γ := by
  simp [simScope, arrKernel, isVar]

/-- **`arrKernel_source_to_rustexec_program`.**  `arrKernel_source_to_rustexec` on
    the program-level simulation: the array-store arm `hArrUpd` (per program, the
    inductive step from the body's simulation) and the vacuity of `index` are the
    only hypotheses beyond the bridge-level preconditions. -/
theorem arrKernel_source_to_rustexec_program
    (bridge : ValueTowerBridge) (bi : Builtins) (fuel N : Nat) (leafSpec : LeafSpec)
    (hPre : FullSimPreconds bi leafSpec bridge)
    (hProj : ProjPreconds bridge leafSpec)
    (hArrUpd : ∀ (name : String) (args : List ImpExpr) (body : ImpExpr),
       ProgSim bridge bi N leafSpec [] body →
       ProgSim bridge bi N leafSpec [] (.letBind name (.app "array_update" args) body))
    (hIdxVac : ∀ vals, bi "index" vals = none)
    (c : LowCT) (hImg : haxToLowCT arrKernel = some c)
    (env env' : Env) (rs : RustState) (v : Value)
    (hEval : evalImp bi fuel arrKernel env = some (v, env'))
    (hAgree : envAgreesRustFull bridge env rs) :
    ∃ rs', RustExec N leafSpec c rs rs' ∧ envAgreesRustFull bridge env' rs' := by
  have hArms : ProgramSimArms bridge bi N leafSpec [] :=
    { arrayUpdate := hArrUpd
      index := progSim_index_of_vacuity bridge bi N leafSpec [] hIdxVac }
  obtain ⟨rs', hExec, hAgree', _, _⟩ :=
    haxToLowCT_simulates_program bridge bi N leafSpec [] hPre hProj hArms arrKernel
      fuel [] [] c env env' rs v (simScope_arrKernel [])
      (fun _ _ h => by simp at h) (fun _ h => by simp at h) hImg hEval hAgree
  exact ⟨rs', hExec, hAgree'⟩

/-! ## §3  The bounded-`RFor` ascent weld (the ascent leg)

`keystone_for` (the control weld) joins `corres_for` (the bounded-loop ascent rule
over the real `semScalar` `RFor` arm) to the emit output word.  For the closed
bounded-loop kernel `forClosedKernel "i" "o" v (N'+1)` — `N'+1` trips each writing
the literal `v` into `o` and resetting the counter `i` — the emit output word is
pinned to the clean `ZMod 2^64` loop spec `(v : ZMod 2^64)`. -/

/-- **`loop_keystone_emit`.**  The bounded-loop analogue of the feSub weld: the
    emit output of the closed `RFor` kernel `forClosedKernel "i" "o" v (N'+1)` is
    `Emit (ofNat v)`, and that word's clean `ZMod 2^64` spec is the loop's fixed
    result `(v : ZMod 2^64)`.  A bounded-loop (`RFor`) emit
    conclusion — the ascent leaf the array image (below) lacks. -/
theorem loop_keystone_emit {β : Type} (Emit : BitVec 64 → β) (v N' : Nat)
    (jdenote : β) (hEmit : jdenote = Emit (BitVec.ofNat 64 v)) :
    jdenote = Emit (BitVec.ofNat 64 v)
      ∧ wEnc (BitVec.ofNat 64 v) = (v : ZMod (2 ^ 64)) :=
  keystone_for Emit "i" "o" v N' (by decide) jdenote hEmit

/-! ## §4  The two walls, as theorems where the coverage gap is decidable -/

/-- **Loop source-preimage wall.**  The only source constructor whose `haxToLowCT`
    image is the ascent-covered bounded `RFor` is `.forFold`, and its source
    semantics is empty — so the tower's loop simulation over an `RFor` is never
    reached with a non-`none` `evalImp`.  (The tower's loop arm,
    `.whileLoop`, lowers to the semScalar-uninterpreted `RWhileNz`.) -/
theorem loop_forFold_source_vacuous
    (bi : Builtins) (fuel : Nat) (var : String) (lo hi body : ImpExpr) (env : Env) :
    evalImp bi fuel (.forFold var lo hi body) env = none :=
  evalImp_forFold_eq_none bi fuel var lo hi body env

/-- **Array ascent-leaf wall (executability half).**  `semScalar`
    interprets a dynamic-index `RArrStore` node (here the shape-fallback branch,
    always `some`).  The array-write image the tower delivers is therefore a live
    LowCT program — yet the ascent calculus registers no `Corres` value-leaf for
    `RArrStore` / `RArrLoad`, so there is no weld to attach it to.  This exhibits
    the node the ascent leaf is missing, not a proof that a leaf is impossible. -/
theorem arrStore_executes (arr src : Located) (idxVar : String) :
    (semScalar (.RArrStore arr idxVar src) (fun _ => none)).isSome = true := by
  simp [semScalar]

end CatCrypt.Crypto.SecureCompilation.Ascent
