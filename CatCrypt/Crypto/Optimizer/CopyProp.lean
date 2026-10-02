/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Rewrite.Peephole
public import CatCrypt.Crypto.SecureCompilation.VIR.MergeCom
public import CatCrypt.Crypto.Optimizer.ComDCE

/-!
# Verified copy-propagation pass for `Com` (typed VIR `jasminDialect`)

A **denotation-preserving copy-propagation `Com → Com` pass** over the typed VIR
`jasminDialect`. Copy propagation rewrites uses of a variable that was bound to a
*pure copy* of an already-in-scope variable so that they refer to the copy's
*source* directly. After this rewrite the copy binding becomes dead and a later
dead-code-elimination pass can drop it; here we keep the binding (so the De
Bruijn shape and the cost/CT facts of the surrounding chain are undisturbed) and
only redirect the body's uses.

## What counts as a copy

In the carry-free `jasminDialect` alphabet a *register copy* of a variable `a`
can be written as the idempotent self-`or` binding

    let z = a ||| a      -- z denotes exactly `a`   (`a ||| a = a`)

`a ||| a` denotes `a.lookup V` bit-for-bit (`BitVec.or_self`), so the freshly
bound `z` (`Ctxt.Var.here`) and the *shifted* source `a` (`Ctxt.Var.there a`)
look up the **same** entry of the extended valuation `V.extend (a.lookup V)`.
Replacing `z` by `a.there` throughout the body is therefore denotation-preserving
— this is the soundness core of the pass.

## The pass

`copyProp` walks the let-chain (reusing the `peepCom`-style traversal in
`Optimizer/Rewrite/Peephole.lean`). At each `.var e body`:

* if `e` is a self-`or` copy `a ||| a`, it renames every use of the bound
  variable in `body` to the shifted source `a` (via the de-Bruijn renaming
  `copyHom`, built on the `Ctxt.Hom`/`Com.rename` machinery in `MergeCom.lean`),
  then recurses;
* otherwise it leaves the binding and recurses.

## Preservation theorem

* `copyProp_denote` : `(copyProp c).denote V = c.denote V`, by induction over the
  `Com` let-chain, using the de-Bruijn substitution laws
  (`Com.denote_rename`, `pullV`) proved here on top of `Expr.denote_rename`.
  **Not** `rfl`.
* `copyElim_denote` : the same for `copyElim`, which deletes each copy binding and
  maps its uses to the source in a single traversal carrying one renaming.
* `copyElimOut_denote`, `copyElimOut_outputs` : `copyElimOut nOut` deletes the copies
  outside the last `nOut` bindings and keeps those bindings, so it preserves the
  denotation and the last `nOut` binding values (`ComDCE.outputs`).
* `copyElimOut_ctLeak_eq` : for every leakage model, equal leakage of the input at two
  valuations gives equal leakage of the output.

## Any dialect

`Generic` states copy elimination for every dialect with a copy recogniser
(`Generic.CopyRecog`: `isCopy` with `isCopy_denote`): `Generic.copyElimGo_denote`,
`Generic.copyElimOut_denote`, `Generic.copyElimOut_outputs`, and the leakage theorems
`Generic.copyElimGo_ctLeak` (for every leakage model, equal input leakage at two
valuations gives equal output leakage) and `Generic.copyElimGo_ctLeak_of_silent`
(the leakage is unchanged when every recognised copy has no events). The
`jasminDialect` definitions are the instance at `jasminCopy`.

The pass is conservative: it propagates **only** through a provably
denotation-preserving copy (a variable-to-variable alias), never through an
arbitrary expression. All goals closed; no open goals.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.CopyProp

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Optimizer.Rewrite.Egraph
open CatCrypt.Crypto.Optimizer.Rewrite.Peephole

/-! ## 0. De-Bruijn substitution laws (pullback valuations)

Standard intrinsically-typed substitution lemmas: looking up a renamed variable
in `V` equals looking up the original in the **pullback** of `V` along the
renaming. `pullV` is the pullback at `jasminDialect`; it equals the dialect-generic
`Ctxt.Valuation.comap` (`pullV_eq_comap`), and the laws below are the generic ones
of `VIR/Peephole.lean` read through that equation. -/

/-- Pullback of a `Valuation Γ'` along a context homomorphism `h : Γ → Γ'`. -/
def pullV : {Γ : Ctxt jasminDialect} → {Γ' : Ctxt jasminDialect} →
    Ctxt.Hom Γ Γ' → Ctxt.Valuation Γ' → Ctxt.Valuation Γ
  | [], _, _, _ => HVector.nil
  | _ :: _, _, h, V =>
      HVector.cons ((h Ctxt.Var.here).lookup V)
        (pullV (fun v => h (.there v)) V)

/-- Looking up a renamed variable in `V` equals looking up the original variable
in the pullback of `V`. -/
theorem Ctxt.Var.lookup_rename {Γ Γ' : Ctxt jasminDialect}
    (h : Ctxt.Hom Γ Γ') {t : JasminTy} (v : Ctxt.Var Γ t)
    (V : Ctxt.Valuation Γ') :
    (h v).lookup V = v.lookup (pullV h V) := by
  induction v with
  | here => rfl
  | @there Γ₀ t s w ih =>
      simp only [pullV]
      exact ih (fun v => h (.there v))

/-- The pullback of a valuation along a renaming is its `comap`. -/
theorem pullV_eq_comap {Γ Γ' : Ctxt jasminDialect} (h : Ctxt.Hom Γ Γ')
    (V : Ctxt.Valuation Γ') : pullV h V = V.comap h :=
  Ctxt.Valuation.ext _ _ fun _ v => by
    rw [← Ctxt.Var.lookup_rename, Ctxt.Valuation.lookup_comap]

/-- Renaming arguments and looking them up against a valuation equals looking up
the original arguments against the pulled-back valuation. -/
theorem lookupArgs_renameVars {Γ Γ' : Ctxt jasminDialect}
    (h : Ctxt.Hom Γ Γ') {tys : List JasminTy}
    (args : HVector (fun ty => Ctxt.Var Γ ty) tys) (V : Ctxt.Valuation Γ') :
    Expr.lookupArgs (HVector.renameVars h args) V
      = Expr.lookupArgs args (pullV h V) := by
  rw [pullV_eq_comap]
  exact SecureCompilation.VIR.Expr.lookupArgs_renameVars h V args

/-- Renaming an `Expr` and denoting it against `V` equals denoting the original
expression against the pulled-back valuation. -/
theorem Expr.denote_rename {Γ Γ' : Ctxt jasminDialect}
    (h : Ctxt.Hom Γ Γ') {t : JasminTy} (e : Expr jasminDialect Γ t)
    (V : Ctxt.Valuation Γ') :
    (e.rename h).denote V = e.denote (pullV h V) := by
  rw [pullV_eq_comap]
  exact SecureCompilation.VIR.Expr.denote_rename h e V

/-! ## 1. `Com.denote_rename`: renaming commutes with denotation -/

/-- Pulling back along a renaming whose image is entirely *shifted* past a fresh
binding `s` ignores the fresh entry: `pullV (weakenOne ∘ g) (V.extend x) = pullV g V`. -/
theorem pullV_weaken {Γ Γ' : Ctxt jasminDialect} {s : JasminTy} (x : ⟦s⟧)
    (g : Ctxt.Hom Γ Γ') (V : Ctxt.Valuation Γ') :
    pullV (fun {_} v => Ctxt.Var.there (g v)) (V.extend x) = pullV g V := by
  rw [pullV_eq_comap, pullV_eq_comap]
  exact Ctxt.Valuation.ext _ _ fun _ v => by
    rw [Ctxt.Valuation.lookup_comap, Ctxt.Valuation.lookup_comap]; rfl

/-- Pulling back along the identity renaming is the identity on valuations. -/
theorem pullV_id {Γ : Ctxt jasminDialect} (V : Ctxt.Valuation Γ) :
    pullV (Ctxt.Hom.id Γ) V = V := by
  rw [pullV_eq_comap, Ctxt.Valuation.comap_id]

/-- Pulling a lifted renaming back through an extended valuation equals extending the
pulled-back valuation. -/
theorem pullV_lift {Γ Γ' : Ctxt jasminDialect} (h : Ctxt.Hom Γ Γ')
    {s : JasminTy} (V : Ctxt.Valuation Γ') (x : ⟦s⟧) :
    pullV (h.lift) (V.extend x) = (pullV h V).extend x := by
  rw [pullV_eq_comap, pullV_eq_comap, Ctxt.Valuation.extend_comap_lift]

/-- **Renaming commutes with `Com` denotation.** Denoting a renamed `Com`
against `V` equals denoting the original against the pulled-back valuation: the
generic `Com.denote_rename` of `VIR/Peephole.lean` at `jasminDialect`. -/
theorem Com.denote_rename {Γ Γ' : Ctxt jasminDialect} {τ : JasminTy}
    (h : Ctxt.Hom Γ Γ') (c : Com jasminDialect Γ τ) (V : Ctxt.Valuation Γ') :
    (c.rename h).denote V = c.denote (pullV h V) := by
  rw [pullV_eq_comap]
  exact SecureCompilation.VIR.Com.denote_rename h c V

/-! ## 2. Detecting a self-`or` copy

A `.var`-bound expression is a register copy of `a` when it is `binE .or a a`
(equivalently `a ||| a`). `isCopy` returns the source variable `a` if the
expression has that exact shape. -/

/-- If a `bs`-typed binding `e` is the self-`or` register copy `a ||| a`, return
`some a`. For any other binding type or expression shape, return `none`. The
return type matches the binding type `bs`, so the redirect renaming `copyHom`
applies directly. -/
def isCopy {Γ : Ctxt jasminDialect} {bs : JasminTy}
    (e : Expr jasminDialect Γ bs) : Option (Ctxt.Var Γ bs) :=
  match e with
  | ⟨.regArith bop _, hop, args⟩ =>
      match bop with
      | .or =>
          let a := args.head
          let b := args.tail.head
          if varEq a b then some (hop ▸ a) else none
      | _ => none
  | _ => none

/-- **Soundness of `isCopy`.** If `isCopy e = some a` then `e` denotes exactly
`a.lookup V` (the copy is a faithful alias of `a`). -/
theorem isCopy_denote {Γ : Ctxt jasminDialect} {bs : JasminTy}
    (e : Expr jasminDialect Γ bs) (a : Ctxt.Var Γ bs)
    (V : Ctxt.Valuation Γ) (he : isCopy e = some a) :
    e.denote V = a.lookup V := by
  rcases e with ⟨op, hop, args⟩
  cases op with
  | regArith bop w' =>
      cases hop
      match args, (rfl : args = args) with
      | .cons x (.cons y .nil), _ =>
        cases bop
        case or =>
          simp only [isCopy, HVector.head, HVector.tail] at he
          by_cases hv : varEq x y
          · have hxy : x = y := varEq_sound x y hv
            subst hxy
            simp only [hv, if_true, Option.some.injEq] at he
            subst he
            show (binE .or x x).denote V = x.lookup V
            rw [binE_denote]
            simp [JasminBinOp.apply]
          · simp only [hv, Bool.false_eq_true, if_false] at he
            exact absurd he (by simp)
        all_goals
          (simp only [isCopy] at he
           exact absurd he (by simp))
  | stackLoad w n => simp only [isCopy] at he; exact absurd he (by simp)
  | stackStore w n => simp only [isCopy] at he; exact absurd he (by simp)
  | castW w w' => simp only [isCopy] at he; exact absurd he (by simp)
  | extCall nm aa r => simp only [isCopy] at he; exact absurd he (by simp)
  | regConst w n => simp only [isCopy] at he; exact absurd he (by simp)
  | vpackZMM bop => simp only [isCopy] at he; exact absurd he (by simp)
  | vpackZMMd bop => simp only [isCopy] at he; exact absurd he (by simp)
  | vprordZMM n => simp only [isCopy] at he; exact absurd he (by simp)
  | vpslldq n => simp only [isCopy] at he; exact absurd he (by simp)
  | vpsrldq n => simp only [isCopy] at he; exact absurd he (by simp)
  | vsimd op => simp only [isCopy] at he; exact absurd he (by simp)
  | vymm op => simp only [isCopy] at he; exact absurd he (by simp)
  | mulhi w => simp only [isCopy] at he; exact absurd he (by simp)
  | addCarryLo w => simp only [isCopy] at he; exact absurd he (by simp)
  | addCarryHi w => simp only [isCopy] at he; exact absurd he (by simp)
  | rorImm w n => simp only [isCopy] at he; exact absurd he (by simp)
  | shrImm w n => simp only [isCopy] at he; exact absurd he (by simp)
  | sarImm w n => simp only [isCopy] at he; exact absurd he (by simp)
  | shlImm w n => simp only [isCopy] at he; exact absurd he (by simp)
  | select w => simp only [isCopy] at he; exact absurd he (by simp)
  | callN name argTys retTys => simp only [isCopy] at he; exact absurd he (by simp)
  | cmp c w => simp only [isCopy] at he; exact absurd he (by simp)
  | cmpImm c w n => simp only [isCopy] at he; exact absurd he (by simp)

/-! ## 3. The redirecting renaming

When the head binding `let z = a ||| a` is a copy of `a`, the body lives in
context `reg w :: Γ`. We redirect the bound variable `z` (`.here`) to the
shifted source `a.there`, leaving every other variable fixed. -/

/-- The de-Bruijn renaming that redirects the just-bound variable `.here` to the
shifted source `a.there`, and is the identity on every other variable. Stated
for an arbitrary binding type `bs` (the redirect logic does not depend on the
type being a register). -/
def copyHom {Γ : Ctxt jasminDialect} {bs : JasminTy}
    (a : Ctxt.Var Γ bs) : Ctxt.Hom (bs :: Γ) (bs :: Γ) := fun
  | .here => .there a
  | .there v => .there v

/-- **The redirect is a no-op on the aliasing valuation.** When the freshly
bound entry is `a.lookup V`, pulling back along `copyHom a` returns the same
extended valuation — the bound entry and `a.there` agree. -/
theorem pullV_copyHom {Γ : Ctxt jasminDialect} {bs : JasminTy}
    (a : Ctxt.Var Γ bs) (V : Ctxt.Valuation Γ) :
    pullV (copyHom a) (V.extend (a.lookup V)) = V.extend (a.lookup V) := by
  simp only [pullV, Ctxt.Valuation.extend]
  congr 1
  -- tail: pullV (fun v => copyHom a (.there v)) (V.extend (a.lookup V)) = V
  -- on `.there v`, `copyHom a` is `.there`, i.e. `weakenOne ∘ id`.
  show pullV (fun {_} v => Ctxt.Var.there (Ctxt.Hom.id Γ v))
        (V.extend (a.lookup V)) = V
  rw [pullV_weaken (a.lookup V) (Ctxt.Hom.id Γ) V]
  exact pullV_id V

/-! ## 4. The copy-propagation pass

`copyProp` walks the let-chain. At each `.var e body` whose return type is a
register `reg w`, if `e` is a self-`or` copy of some source variable `a`, it
renames every use of the bound variable in `body` to the shifted source
`a.there` (`copyHom a`) and recurses; otherwise it recurses unchanged. The copy
binding itself is retained (a later DCE pass drops it). -/

/-- One copy-propagation pass over a `Com`. At each `.var e body`: if `e` is a
register copy of a source variable `a`, redirect every use of the bound variable
in `body` to the shifted source `a` (via `copyHom a`) and recurse; otherwise
recurse unchanged. The copy binding is retained for a later DCE pass to drop. -/
def copyProp {Γ : Ctxt jasminDialect} {t : JasminTy} :
    Com jasminDialect Γ t → Com jasminDialect Γ t
  | .ret v => .ret v
  | .var e body =>
      match isCopy e with
      | some a => .var e ((copyProp body).rename (copyHom a))
      | none   => .var e (copyProp body)

/-- **Denotation preservation for copy propagation.** `copyProp c` denotes the
same function as `c`. By induction over the `Com` let-chain; the copy case uses
`isCopy_denote`, `Com.denote_rename` and `pullV_copyHom`. **Not** `rfl`. -/
theorem copyProp_denote {Γ : Ctxt jasminDialect} {t : JasminTy} :
    ∀ (c : Com jasminDialect Γ t) (V : Ctxt.Valuation Γ),
      (copyProp c).denote V = c.denote V
  | .ret v, _ => rfl
  | .var e body, V => by
      show (match isCopy e with
            | some a => Com.var e ((copyProp body).rename (copyHom a))
            | none   => Com.var e (copyProp body)).denote V
            = (Com.var e body).denote V
      rcases hc : isCopy e with _ | a
      · -- no copy: structural recurse
        simp only [Com.denote]
        exact copyProp_denote body (V.extend (e.denote V))
      · -- copy of `a`: e.denote V = a.lookup V, and the rename is a no-op
        simp only [Com.denote]
        rw [Com.denote_rename (copyHom a) (copyProp body) (V.extend (e.denote V))]
        rw [isCopy_denote e a V hc]
        rw [pullV_copyHom a V]
        exact copyProp_denote body (V.extend (a.lookup V))

/-! ## 5. Copy elimination in one traversal

`copyProp` renames the whole continuation at every copy, so it takes time proportional
to the number of copies times the length of the program. `copyElim` carries one
renaming `ρ` from the input context to the output context down the let-chain instead:
a copy `let z = a ||| a` is deleted and `z` is mapped to the image of `a`, and every
other binding is renamed by `ρ` and kept. A variable is re-indexed in time proportional
to its de Bruijn index in the input plus that of its image, so the pass is linear in the
size of the input and output programs.

The traversal and its proofs are stated in `Generic` for every dialect with a copy
recogniser (`Generic.CopyRecog`); the `jasminDialect` pass is the instance at
`jasminCopy`. -/

namespace Generic

open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck

/-- A recogniser of copy bindings of the dialect `d`: `isCopy e = some a` when the
    binding `e` denotes the value of the variable `a`. -/
structure CopyRecog (d : Dialect.{0, 0}) [TyDenote d.Ty] [DialectSignature d]
    [DialectDenote d] where
  /-- The source variable of a copy binding. -/
  isCopy : {Γ : Ctxt d} → {t : d.Ty} → Expr d Γ t → Option (Ctxt.Var Γ t)
  /-- A recognised copy denotes the value of its source. -/
  isCopy_denote : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t) (a : Ctxt.Var Γ t)
    (V : Ctxt.Valuation Γ), isCopy e = some a → e.denote V = a.lookup V

variable {d : Dialect.{0, 0}} [TyDenote d.Ty] [DialectSignature d] [DialectDenote d]
  (R : CopyRecog d)

/-- The value of the source of a recognised copy, read through a renaming. -/
theorem isCopy_denote_comap {Γ Δ : Ctxt d} {t : d.Ty} {e : Expr d Γ t}
    {a : Ctxt.Var Γ t} (hc : R.isCopy e = some a) (ρ : Ctxt.Hom Γ Δ)
    (V : Ctxt.Valuation Δ) : (ρ a).lookup V = e.denote (V.comap ρ) := by
  rw [R.isCopy_denote e a _ hc, Ctxt.Valuation.lookup_comap]

/-- Copy elimination under the renaming `ρ`: delete each recognised copy, map its
    variable to the image of its source, and rename every other binding by `ρ`. -/
def copyElimGo : {Γ Δ : Ctxt d} → {t : d.Ty} → Ctxt.Hom Γ Δ → Com d Γ t → Com d Δ t
  | _, _, _, ρ, .ret v => .ret (ρ v)
  | _, _, _, ρ, .var e body =>
      match R.isCopy e with
      | some a => copyElimGo (Rewrite.AegraphGeneric.consHom (ρ a) ρ) body
      | none => .var (e.rename ρ) (copyElimGo ρ.lift body)

theorem copyElimGo_denote : ∀ {Γ Δ : Ctxt d} {t : d.Ty}
    (ρ : Ctxt.Hom Γ Δ) (c : Com d Γ t) (V : Ctxt.Valuation Δ),
    (copyElimGo R ρ c).denote V = c.denote (V.comap ρ)
  | _, _, _, ρ, .ret v, V => (Ctxt.Valuation.lookup_comap ρ V v).symm
  | _, _, _, ρ, .var e body, V => by
      simp only [copyElimGo]
      rcases hc : R.isCopy e with _ | a
      · simp only [Com.denote]
        rw [copyElimGo_denote ρ.lift body, SecureCompilation.VIR.Expr.denote_rename ρ e V,
          Ctxt.Valuation.extend_comap_lift]
      · rw [copyElimGo_denote _ body, Rewrite.AegraphGeneric.comap_consHom,
          isCopy_denote_comap R hc ρ V]
        rfl

/-- **Leakage of copy elimination.** For every leakage model, equal leakage of the input
    at the pulled-back valuations gives equal leakage of the output. -/
theorem copyElimGo_ctLeak (L : LeakModel d) : ∀ {Γ Δ : Ctxt d} {t : d.Ty}
    (ρ : Ctxt.Hom Γ Δ) (c : Com d Γ t) (V₁ V₂ : Ctxt.Valuation Δ),
    Com.ctLeak L c (V₁.comap ρ) = Com.ctLeak L c (V₂.comap ρ) →
    Com.ctLeak L (copyElimGo R ρ c) V₁ = Com.ctLeak L (copyElimGo R ρ c) V₂
  | _, _, _, _, .ret _, _, _, _ => rfl
  | _, _, _, ρ, .var e body, V₁, V₂, h => by
      simp only [Com.ctLeak] at h
      obtain ⟨hE, hB⟩ :=
        List.append_inj h (Rewrite.AegraphGeneric.opLeak_length L e.op _ _)
      simp only [copyElimGo]
      rcases hc : R.isCopy e with _ | a
      · simp only [Com.ctLeak]
        rw [Rewrite.AegraphGeneric.Expr.ctLeak_rename,
          Rewrite.AegraphGeneric.Expr.ctLeak_rename, hE]
        congr 1
        refine copyElimGo_ctLeak L ρ.lift body _ _ ?_
        rw [Ctxt.Valuation.extend_comap_lift, Ctxt.Valuation.extend_comap_lift,
          SecureCompilation.VIR.Expr.denote_rename, SecureCompilation.VIR.Expr.denote_rename]
        exact hB
      · refine copyElimGo_ctLeak L _ body V₁ V₂ ?_
        rw [Rewrite.AegraphGeneric.comap_consHom, Rewrite.AegraphGeneric.comap_consHom,
          isCopy_denote_comap R hc ρ V₁, isCopy_denote_comap R hc ρ V₂]
        exact hB

/-- **Leakage of copy elimination when copies are silent.** If every recognised copy
    has no events, copy elimination keeps the leakage at every valuation. -/
theorem copyElimGo_ctLeak_of_silent (L : LeakModel d)
    (hs : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t) (a : Ctxt.Var Γ t)
      (V : Ctxt.Valuation Γ), R.isCopy e = some a → Expr.ctLeak L e V = []) :
    ∀ {Γ Δ : Ctxt d} {t : d.Ty} (ρ : Ctxt.Hom Γ Δ) (c : Com d Γ t)
      (V : Ctxt.Valuation Δ),
      Com.ctLeak L (copyElimGo R ρ c) V = Com.ctLeak L c (V.comap ρ)
  | _, _, _, _, .ret _, _ => rfl
  | _, _, _, ρ, .var e body, V => by
      simp only [copyElimGo]
      rcases hc : R.isCopy e with _ | a
      · simp only [Com.ctLeak]
        rw [Rewrite.AegraphGeneric.Expr.ctLeak_rename,
          copyElimGo_ctLeak_of_silent L hs ρ.lift body, Ctxt.Valuation.extend_comap_lift,
          SecureCompilation.VIR.Expr.denote_rename]
      · rw [copyElimGo_ctLeak_of_silent L hs _ body, Rewrite.AegraphGeneric.comap_consHom,
          isCopy_denote_comap R hc ρ V]
        simp only [Com.ctLeak, hs e a _ hc, List.nil_append]

/-- **Copy elimination**: every recognised copy is deleted and its uses read its
    source. One traversal. -/
def copyElim {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) : Com d Γ t :=
  copyElimGo R (Ctxt.Hom.id Γ) c

theorem copyElim_denote {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) (V : Ctxt.Valuation Γ) :
    (copyElim R c).denote V = c.denote V := by
  rw [copyElim, copyElimGo_denote, Ctxt.Valuation.comap_id]

theorem copyElim_ctLeak_eq (L : LeakModel d) {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t)
    (V₁ V₂ : Ctxt.Valuation Γ) (h : Com.ctLeak L c V₁ = Com.ctLeak L c V₂) :
    Com.ctLeak L (copyElim R c) V₁ = Com.ctLeak L (copyElim R c) V₂ :=
  copyElimGo_ctLeak R L _ c V₁ V₂ (by
    rw [Ctxt.Valuation.comap_id, Ctxt.Valuation.comap_id]; exact h)

/-- The source of the binding `e` when it is a copy outside the last `k` of `rem`
    remaining bindings. -/
def copyOutside {Γ : Ctxt d} {t : d.Ty} (k rem : Nat) (e : Expr d Γ t) :
    Option (Ctxt.Var Γ t) :=
  if k < rem then R.isCopy e else none

theorem copyOutside_some {Γ : Ctxt d} {t : d.Ty} {k rem : Nat} {e : Expr d Γ t}
    {a : Ctxt.Var Γ t} (h : copyOutside R k rem e = some a) :
    k < rem ∧ R.isCopy e = some a := by
  unfold copyOutside at h
  split at h
  · exact ⟨by assumption, h⟩
  · cases h

/-- Copy elimination under the renaming `ρ` outside the last `k` bindings: `rem` is the
    number of bindings of the program. -/
def copyElimOutGo (k : Nat) : {Γ Δ : Ctxt d} → {t : d.Ty} → Nat →
    Ctxt.Hom Γ Δ → Com d Γ t → Com d Δ t
  | _, _, _, _, ρ, .ret v => .ret (ρ v)
  | _, _, _, rem, ρ, .var e body =>
      match copyOutside R k rem e with
      | some a =>
          copyElimOutGo k (rem - 1) (Rewrite.AegraphGeneric.consHom (ρ a) ρ) body
      | none => .var (e.rename ρ) (copyElimOutGo k (rem - 1) ρ.lift body)

theorem copyElimOutGo_denote (k : Nat) : ∀ {Γ Δ : Ctxt d} {t : d.Ty}
    (rem : Nat) (ρ : Ctxt.Hom Γ Δ) (c : Com d Γ t) (V : Ctxt.Valuation Δ),
    (copyElimOutGo R k rem ρ c).denote V = c.denote (V.comap ρ)
  | _, _, _, _, ρ, .ret v, V => (Ctxt.Valuation.lookup_comap ρ V v).symm
  | _, _, _, rem, ρ, .var e body, V => by
      simp only [copyElimOutGo]
      rcases hc : copyOutside R k rem e with _ | a
      · simp only [Com.denote]
        rw [copyElimOutGo_denote k (rem - 1) ρ.lift body,
          SecureCompilation.VIR.Expr.denote_rename ρ e V, Ctxt.Valuation.extend_comap_lift]
      · rw [copyElimOutGo_denote k (rem - 1) _ body, Rewrite.AegraphGeneric.comap_consHom,
          isCopy_denote_comap R (copyOutside_some R hc).2 ρ V]
        rfl

/-- The binding values of `copyElimOutGo k` are those of the source with some entries
    outside the last `k` deleted. -/
theorem copyElimOutGo_tailAgree (k : Nat) : ∀ {Γ Δ : Ctxt d} {t : d.Ty}
    (ρ : Ctxt.Hom Γ Δ) (c : Com d Γ t) (V : Ctxt.Valuation Δ),
    ComDCE.TailAgree k (ComDCE.bindVals (copyElimOutGo R k (UncomputePass.comLen c) ρ c) V)
      (ComDCE.bindVals c (V.comap ρ))
  | _, _, _, _, .ret _, _ => ComDCE.TailAgree.refl k []
  | _, _, _, ρ, .var e body, V => by
      simp only [UncomputePass.comLen_var, copyElimOutGo, Nat.add_sub_cancel]
      rcases hc : copyOutside R k (UncomputePass.comLen body + 1) e with _ | a
      · simp only [ComDCE.bindVals]
        rw [SecureCompilation.VIR.Expr.denote_rename ρ e V]
        have ih := copyElimOutGo_tailAgree k ρ.lift body (V.extend (e.denote (V.comap ρ)))
        rw [Ctxt.Valuation.extend_comap_lift] at ih
        exact ih.cons _
      · obtain ⟨hk, ha⟩ := copyOutside_some R hc
        have ih := copyElimOutGo_tailAgree k (Rewrite.AegraphGeneric.consHom (ρ a) ρ) body V
        rw [Rewrite.AegraphGeneric.comap_consHom, isCopy_denote_comap R ha ρ V] at ih
        simp only [ComDCE.bindVals]
        refine ih.drop_left _ ?_
        rw [ComDCE.length_bindVals]
        omega

/-- **Leakage of copy elimination outside the last `k` bindings**, for every leakage
    model, in the form of `copyElimGo_ctLeak`. -/
theorem copyElimOutGo_ctLeak (L : LeakModel d) (k : Nat) : ∀ {Γ Δ : Ctxt d} {t : d.Ty}
    (rem : Nat) (ρ : Ctxt.Hom Γ Δ) (c : Com d Γ t) (V₁ V₂ : Ctxt.Valuation Δ),
    Com.ctLeak L c (V₁.comap ρ) = Com.ctLeak L c (V₂.comap ρ) →
    Com.ctLeak L (copyElimOutGo R k rem ρ c) V₁ = Com.ctLeak L (copyElimOutGo R k rem ρ c) V₂
  | _, _, _, _, _, .ret _, _, _, _ => rfl
  | _, _, _, rem, ρ, .var e body, V₁, V₂, h => by
      simp only [Com.ctLeak] at h
      obtain ⟨hE, hB⟩ :=
        List.append_inj h (Rewrite.AegraphGeneric.opLeak_length L e.op _ _)
      simp only [copyElimOutGo]
      rcases hc : copyOutside R k rem e with _ | a
      · simp only [Com.ctLeak]
        rw [Rewrite.AegraphGeneric.Expr.ctLeak_rename,
          Rewrite.AegraphGeneric.Expr.ctLeak_rename, hE]
        congr 1
        refine copyElimOutGo_ctLeak L k (rem - 1) ρ.lift body _ _ ?_
        rw [Ctxt.Valuation.extend_comap_lift, Ctxt.Valuation.extend_comap_lift,
          SecureCompilation.VIR.Expr.denote_rename, SecureCompilation.VIR.Expr.denote_rename]
        exact hB
      · have ha := (copyOutside_some R hc).2
        refine copyElimOutGo_ctLeak L k (rem - 1) _ body V₁ V₂ ?_
        rw [Rewrite.AegraphGeneric.comap_consHom, Rewrite.AegraphGeneric.comap_consHom,
          isCopy_denote_comap R ha ρ V₁, isCopy_denote_comap R ha ρ V₂]
        exact hB

/-- **Copy elimination that keeps the output bindings**: every recognised copy outside
    the last `nOut` bindings is deleted and its uses read its source; the last `nOut`
    bindings are kept. One traversal. -/
def copyElimOut (nOut : Nat) {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) : Com d Γ t :=
  copyElimOutGo R nOut (UncomputePass.comLen c) (Ctxt.Hom.id Γ) c

theorem copyElimOut_denote (nOut : Nat) {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t)
    (V : Ctxt.Valuation Γ) : (copyElimOut R nOut c).denote V = c.denote V := by
  rw [copyElimOut, copyElimOutGo_denote, Ctxt.Valuation.comap_id]

/-- `copyElimOut` preserves the outputs: the last `nOut` binding values. -/
theorem copyElimOut_outputs (nOut : Nat) {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t)
    (V : Ctxt.Valuation Γ) :
    ComDCE.outputs nOut (copyElimOut R nOut c) V = ComDCE.outputs nOut c V := by
  have h := (copyElimOutGo_tailAgree R nOut (Ctxt.Hom.id Γ) c V).drop_eq
  rw [Ctxt.Valuation.comap_id] at h
  exact h

theorem copyElimOut_ctLeak_eq (L : LeakModel d) (nOut : Nat) {Γ : Ctxt d} {t : d.Ty}
    (c : Com d Γ t) (V₁ V₂ : Ctxt.Valuation Γ) (h : Com.ctLeak L c V₁ = Com.ctLeak L c V₂) :
    Com.ctLeak L (copyElimOut R nOut c) V₁ = Com.ctLeak L (copyElimOut R nOut c) V₂ :=
  copyElimOutGo_ctLeak R L nOut _ _ c V₁ V₂ (by
    rw [Ctxt.Valuation.comap_id, Ctxt.Valuation.comap_id]; exact h)

end Generic

/-- The self-`or` copy recogniser of `jasminDialect`. -/
def jasminCopy : Generic.CopyRecog jasminDialect := ⟨isCopy, isCopy_denote⟩

/-- The renaming of `t :: Γ` that sends the head to `x` and the rest through `ρ`:
    `AegraphGeneric.consHom` at `jasminDialect`. -/
def consHom {Γ Δ : Ctxt jasminDialect} {t : JasminTy} (x : Ctxt.Var Δ t)
    (ρ : Ctxt.Hom Γ Δ) : Ctxt.Hom (t :: Γ) Δ :=
  Rewrite.AegraphGeneric.consHom x ρ

theorem pullV_consHom {Γ Δ : Ctxt jasminDialect} {t : JasminTy} (x : Ctxt.Var Δ t)
    (ρ : Ctxt.Hom Γ Δ) (V : Ctxt.Valuation Δ) :
    pullV (consHom x ρ) V = (pullV ρ V).extend (x.lookup V) := rfl

/-- Copy elimination under the renaming `ρ`: delete each self-`or` copy, map its
    variable to the image of its source, and rename every other binding by `ρ`. -/
def copyElimGo {Γ Δ : Ctxt jasminDialect} {t : JasminTy} (ρ : Ctxt.Hom Γ Δ)
    (c : Com jasminDialect Γ t) : Com jasminDialect Δ t :=
  Generic.copyElimGo jasminCopy ρ c

theorem copyElimGo_denote {Γ Δ : Ctxt jasminDialect} {t : JasminTy}
    (ρ : Ctxt.Hom Γ Δ) (c : Com jasminDialect Γ t) (V : Ctxt.Valuation Δ) :
    (copyElimGo ρ c).denote V = c.denote (pullV ρ V) := by
  rw [pullV_eq_comap]
  exact Generic.copyElimGo_denote jasminCopy ρ c V

/-- **Copy elimination**: every self-`or` copy is deleted and its uses read its
    source. One traversal. -/
def copyElim {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t) :
    Com jasminDialect Γ t :=
  copyElimGo (Ctxt.Hom.id Γ) c

/-- **Denotation preservation for `copyElim`.** -/
theorem copyElim_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (V : Ctxt.Valuation Γ) :
    (copyElim c).denote V = c.denote V := by
  rw [copyElim, copyElimGo_denote, pullV_id]

/-! ## 5a. Copy elimination that keeps the output bindings

An owned emitter stores the last `nOut` bindings of its program as its outputs, so a copy
among them must stay a binding. `copyElimOutGo k rem ρ c` carries the number `rem` of
bindings of `c`: a binding with more than `k` bindings after it and including it
(`k < rem`) is deleted when it is a copy, and every binding among the last `k` is kept. -/

/-- The source of the binding `e` when it is a copy outside the last `k` of `rem`
    remaining bindings. -/
def copyOutside {Γ : Ctxt jasminDialect} {bs : JasminTy} (k rem : Nat)
    (e : Expr jasminDialect Γ bs) : Option (Ctxt.Var Γ bs) :=
  Generic.copyOutside jasminCopy k rem e

theorem copyOutside_some {Γ : Ctxt jasminDialect} {bs : JasminTy} {k rem : Nat}
    {e : Expr jasminDialect Γ bs} {a : Ctxt.Var Γ bs} (h : copyOutside k rem e = some a) :
    k < rem ∧ isCopy e = some a :=
  Generic.copyOutside_some jasminCopy h

/-- Copy elimination under the renaming `ρ` outside the last `k` bindings: `rem` is the
    number of bindings of the program. -/
def copyElimOutGo (k : Nat) {Γ Δ : Ctxt jasminDialect} {t : JasminTy} (rem : Nat)
    (ρ : Ctxt.Hom Γ Δ) (c : Com jasminDialect Γ t) : Com jasminDialect Δ t :=
  Generic.copyElimOutGo jasminCopy k rem ρ c

theorem copyElimOutGo_denote (k : Nat) {Γ Δ : Ctxt jasminDialect} {t : JasminTy}
    (rem : Nat) (ρ : Ctxt.Hom Γ Δ) (c : Com jasminDialect Γ t) (V : Ctxt.Valuation Δ) :
    (copyElimOutGo k rem ρ c).denote V = c.denote (pullV ρ V) := by
  rw [pullV_eq_comap]
  exact Generic.copyElimOutGo_denote jasminCopy k rem ρ c V

/-- The binding values of `copyElimOutGo k` are those of the source with some entries
    outside the last `k` deleted. -/
theorem copyElimOutGo_tailAgree (k : Nat) {Γ Δ : Ctxt jasminDialect} {t : JasminTy}
    (ρ : Ctxt.Hom Γ Δ) (c : Com jasminDialect Γ t) (V : Ctxt.Valuation Δ) :
    ComDCE.TailAgree k (ComDCE.bindVals (copyElimOutGo k (UncomputePass.comLen c) ρ c) V)
      (ComDCE.bindVals c (pullV ρ V)) := by
  rw [pullV_eq_comap]
  exact Generic.copyElimOutGo_tailAgree jasminCopy k ρ c V

/-- **Copy elimination that keeps the output bindings**: every self-`or` copy outside the
    last `nOut` bindings is deleted and its uses read its source; the last `nOut`
    bindings are kept. One traversal. -/
def copyElimOut (nOut : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) : Com jasminDialect Γ t :=
  copyElimOutGo nOut (UncomputePass.comLen c) (Ctxt.Hom.id Γ) c

/-- **Denotation preservation for `copyElimOut`.** -/
theorem copyElimOut_denote (nOut : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (V : Ctxt.Valuation Γ) :
    (copyElimOut nOut c).denote V = c.denote V := by
  rw [copyElimOut, copyElimOutGo_denote, pullV_id]

/-- **`copyElimOut` preserves the outputs**: the last `nOut` binding values. -/
theorem copyElimOut_outputs (nOut : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (V : Ctxt.Valuation Γ) :
    ComDCE.outputs nOut (copyElimOut nOut c) V = ComDCE.outputs nOut c V := by
  have h := (copyElimOutGo_tailAgree nOut (Ctxt.Hom.id Γ) c V).drop_eq
  rw [pullV_id] at h
  exact h

/-- **Leakage of `copyElimOut`.** For every leakage model, equal leakage of `c` at two
    valuations gives equal leakage of `copyElimOut nOut c` there. -/
theorem copyElimOut_ctLeak_eq (L : ComLevelCheck.LeakModel jasminDialect) (nOut : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t)
    (V₁ V₂ : Ctxt.Valuation Γ)
    (h : ComLevelCheck.Com.ctLeak L c V₁ = ComLevelCheck.Com.ctLeak L c V₂) :
    ComLevelCheck.Com.ctLeak L (copyElimOut nOut c) V₁
      = ComLevelCheck.Com.ctLeak L (copyElimOut nOut c) V₂ :=
  Generic.copyElimOut_ctLeak_eq jasminCopy L nOut c V₁ V₂ h

/-! ## 6. Self-contained validation

A small `Com jasminDialect [reg 32] (reg 32)` exercising copy propagation:

    let z = x ||| x      -- z is a register copy of x  (`x ||| x = x`)
    let w = z + z        -- uses the copy z
    ret w

`copyProp` redirects the uses of `z` in the body to the shifted source `x`
(leaving the now-dead `z` binding in place for a later DCE pass). Denotation is
preserved: both programs map `x` to `x + x`. -/

/-- The copy demo: `let z = x ||| x; let w = z + z; ret w`. -/
def demoCopy : Com jasminDialect [.reg 32] (.reg 32) :=
  .var (binE .or .here .here)          -- z = x ||| x   (x is `.here`)
    (.var (binE .add .here .here)      -- w = z + z     (z is `.here`)
      (.ret .here))

/-- **Denotation preserved** for the copy demo, via `copyProp_denote`. -/
example (V : Ctxt.Valuation (d := jasminDialect) [.reg 32]) :
    (copyProp demoCopy).denote V = demoCopy.denote V :=
  copyProp_denote demoCopy V

/-- Concretely, on `x = 21`, both denote `42` (`= 21 + 21`). -/
example : demoCopy.denote (.cons (21 : BitVec 32) .nil) = (42 : BitVec 32) := rfl

example :
    (copyProp demoCopy).denote (.cons (21 : BitVec 32) .nil) = (42 : BitVec 32) :=
  rfl

/-- The pass actually redirects: in the rewritten body the `add` reads the
shifted source `x` (`.there .here`) rather than the copy `z` (`.here`). -/
example : copyProp demoCopy =
    Com.var (binE .or .here .here)
      (Com.var (binE .add (.there .here) (.there .here)) (.ret .here)) := by
  rfl

/-- A `ret` program is unchanged. -/
example : copyProp (Com.ret (Γ := [JasminTy.reg 8]) (t := JasminTy.reg 8) .here)
    = Com.ret .here := rfl

end CatCrypt.Crypto.Optimizer.CopyProp
