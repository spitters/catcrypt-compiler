/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module -- deprecated_module: ignore

public import CatCrypt.Crypto.Hax.HaxToLowCTAscentBridge
public import HaxLean.Phase.ContinueFlag

/-!
# The continue flag over the ascent judgment

`Hax.ContinueFlag.contFn c` rewrites the body of each loop of a function body with the
continue flag `c`; `haxToLowCTFnC c` lowers the rewritten body. The rewriting preserves
the outcome of every run from environments agreeing off `c`
(`Hax.ContinueFlag.contFn_run`), so it is a fuel-uniform simulation (`FuelSim`) from
the relation `ContEntry c` (agreement off `c`, from an environment holding no
control-flow value) to agreement off `c`. `corres_of_fuelSim` then carries a `Corres`
statement for a function body, or for one of its loops, to the rewritten form with the
same value.

A `cfContinue` in the source keeps its ascent reading `Hax.Ascent.corres_cfContinue`
(`HaxAscent/Ascent/Corres.lean`); the statements of this module move that reading
to the flag form the lowering accepts.

## Main results

* `ContEntry` — the entry relation of the rewriting
* `fuelSim_contLoop_forFold`, `fuelSim_contLoop_forFoldReturn`, `fuelSim_contFn` —
  the rewriting of a loop and of a function body as a `FuelSim`
* `corres_contLoop_forFold`, `corres_contLoop_forFoldReturn`, `corres_contFn` — the
  transport of a `Corres` statement to the rewritten form
-/

deprecated_module "haxToLowCT is the legacy hax front, outside compileA's path: compileA compiles \
  through haxToNF (Haxc.NFChain); this module remains for the SurfaceDeps bridges \
  (*HaxLowCTBridge) and the kernel producers that use it."
  (since := "2026-10-21")

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr Value Env Builtins)
open _root_.Hax.Ascent (Corres)
open _root_.Hax.ContinueFlag (AgreeOff EnvPlain BuiltinsPlain atomOk bodyOk fnOk
  contLoopBody contFn)

/-- The entry relation of the continue-flag rewriting: the environments agree off `c`,
    and the source environment holds no control-flow value. -/
def ContEntry (c : String) (env envF : Env) : Prop := AgreeOff c env envF ∧ EnvPlain env

variable {S : Type} {bi : Builtins}

/-- A `forFold` with atomic bounds and a body of `bodyOk c` is simulated by the same loop
    over `contLoopBody c body`. -/
theorem fuelSim_contLoop_forFold (hbi : BuiltinsPlain bi) {c i : String}
    {lo hi body : ImpExpr} (hlo : atomOk c lo = true) (hhi : atomOk c hi = true)
    (hok : bodyOk c body = true) (hic : i ≠ c) :
    FuelSim bi (ContEntry c) (AgreeOff c) (.forFold i lo hi body)
      (.forFold i lo hi (contLoopBody c body)) := by
  intro fuel env envF hR
  have h := _root_.Hax.ContinueFlag.denote'_contLoop_forFold hbi hlo hhi hok hic fuel hR.1 hR.2
  exact ⟨h.out.symm, h.agree⟩

/-- A `forFoldReturn` with atomic bounds and a body of `bodyOk c` is simulated by the
    same loop over `contLoopBody c body`. -/
theorem fuelSim_contLoop_forFoldReturn (hbi : BuiltinsPlain bi) {c i : String}
    {lo hi body : ImpExpr} (hlo : atomOk c lo = true) (hhi : atomOk c hi = true)
    (hok : bodyOk c body = true) (hic : i ≠ c) :
    FuelSim bi (ContEntry c) (AgreeOff c) (.forFoldReturn i lo hi body)
      (.forFoldReturn i lo hi (contLoopBody c body)) := by
  intro fuel env envF hR
  have h := _root_.Hax.ContinueFlag.denote'_contLoop_forFoldReturn hbi hlo hhi hok hic fuel
    hR.1 hR.2
  exact ⟨h.out.symm, h.agree⟩

/-- A function body of `fnOk c` is simulated by its rewriting `contFn c`. -/
theorem fuelSim_contFn (hbi : BuiltinsPlain bi) {c : String} {e : ImpExpr}
    (hfn : fnOk c e = true) : FuelSim bi (ContEntry c) (AgreeOff c) e (contFn c e) := by
  intro fuel env envF hR
  have h := _root_.Hax.ContinueFlag.contFn_run hbi e hfn fuel env envF hR.1 hR.2
  exact ⟨h.out.symm, h.agree⟩

/-- **Transport to the rewritten `forFold`.** -/
theorem corres_contLoop_forFold (hbi : BuiltinsPlain bi) {c i : String}
    {lo hi body : ImpExpr} (hlo : atomOk c lo = true) (hhi : atomOk c hi = true)
    (hok : bodyOk c body = true) (hic : i ≠ c)
    {P Q : Env → S → Prop} {G : S → Prop} {V : S → Value}
    (h : Corres bi P G (.forFold i lo hi body) V Q) :
    Corres bi (fun envF σ => ∃ env, P env σ ∧ ContEntry c env envF) G
      (.forFold i lo hi (contLoopBody c body)) V
      (fun envF σ => ∃ env, Q env σ ∧ AgreeOff c env envF) :=
  corres_of_fuelSim (fuelSim_contLoop_forFold hbi hlo hhi hok hic) h

/-- **Transport to the rewritten `forFoldReturn`.** -/
theorem corres_contLoop_forFoldReturn (hbi : BuiltinsPlain bi) {c i : String}
    {lo hi body : ImpExpr} (hlo : atomOk c lo = true) (hhi : atomOk c hi = true)
    (hok : bodyOk c body = true) (hic : i ≠ c)
    {P Q : Env → S → Prop} {G : S → Prop} {V : S → Value}
    (h : Corres bi P G (.forFoldReturn i lo hi body) V Q) :
    Corres bi (fun envF σ => ∃ env, P env σ ∧ ContEntry c env envF) G
      (.forFoldReturn i lo hi (contLoopBody c body)) V
      (fun envF σ => ∃ env, Q env σ ∧ AgreeOff c env envF) :=
  corres_of_fuelSim (fuelSim_contLoop_forFoldReturn hbi hlo hhi hok hic) h

/-- **Transport to the rewritten function body.** A `Corres` statement for a function
    body of `fnOk c` holds for `contFn c e`, the body `haxToLowCTFnC c` lowers. -/
theorem corres_contFn (hbi : BuiltinsPlain bi) {c : String} {e : ImpExpr}
    (hfn : fnOk c e = true) {P Q : Env → S → Prop} {G : S → Prop} {V : S → Value}
    (h : Corres bi P G e V Q) :
    Corres bi (fun envF σ => ∃ env, P env σ ∧ ContEntry c env envF) G (contFn c e) V
      (fun envF σ => ∃ env, Q env σ ∧ AgreeOff c env envF) :=
  corres_of_fuelSim (fuelSim_contFn hbi hfn) h

end CatCrypt.Crypto.Hax
