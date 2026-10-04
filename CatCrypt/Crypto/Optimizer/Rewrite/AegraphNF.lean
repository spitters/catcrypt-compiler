/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProg

/-!
# The acyclic e-graph over structured programs

The lifting of the aegraph pass `AegraphGeneric.aegraphOptOf` from straight-line programs
`Com d` to structured programs `NFProg d`, for every dialect `d` and every rule set
`R : RuleSet d`.

`nfGo R ρ S p` is the traversal `agGo` of `AegraphGeneric` extended by the region
constructors. A let-binding is processed exactly as by `agGo`: the renamed expression's
e-class is formed under the state `S` (node table and definition table) and the extracted
alternative is emitted. A counted loop, a branch and an exit-flag loop are kept, with
their variables renamed by `ρ`; each region body and the continuation are traversed with
`ρ` lifted through the variables the region binds (`homLiftApp`) and with the state `S`
of the enclosing program. Levels count from the bottom of the context, so the entries of
`S` stay valid in the extended contexts (`stSound_append`): a binding inside a region body
or after a region is merged with an equal binding before the region. The entries a
region body records are not passed to the continuation, and the results of a region
(the final carried tuple, the branch results) enter no table.

On a program without regions the traversal is `agGo` (`nfGo_ofCom`), so `aegraphOptNF R`
restricted to `NFProg.ofCom` is `aegraphOptOf R` (`aegraphOptNF_ofCom`).

## Main definitions

* `homLiftApp` — a renaming lifted through a prefix of bound variables.
* `nfGo` — the traversal of a structured program.
* `aegraphOptNF` — the pass: the traversal from the identity renaming and empty tables.

## Main results

* `nfGo_denote` — under a state sound for `V`, the output denotes the input at the
  valuation pulled back along the renaming, at every fuel.
* `aegraphOptNF_denote` — the pass preserves the `NFProg` denotation at every fuel, for
  every rule set.
* `nfGo_ofCom`, `aegraphOptNF_ofCom` — on an embedded straight-line program the pass is
  `aegraphOptOf`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric

/-! ## 1. Renamings and table soundness under a prefix of bindings -/

section Prefix

variable {d : Dialect.{0, 0}}

/-- The renaming `ρ` lifted through the prefix `cs` of bound variables. -/
def homLiftApp : (cs : List d.Ty) → {Γ Δ : Ctxt d} → Ctxt.Hom Γ Δ →
    Ctxt.Hom (cs ++ Γ) (cs ++ Δ)
  | [], _, _, ρ => ρ
  | _ :: cs, _, _, ρ => Ctxt.Hom.lift (homLiftApp cs ρ)

theorem comap_homLiftApp [TyDenote d.Ty] : ∀ (cs : List d.Ty) {Γ Δ : Ctxt d}
    (ρ : Ctxt.Hom Γ Δ) (A : Ctxt.Valuation cs) (V : Ctxt.Valuation Δ),
    Ctxt.Valuation.comap (homLiftApp cs ρ) (hvAppend A V : Ctxt.Valuation (cs ++ Δ)) =
      hvAppend A (V.comap ρ)
  | [], _, _, _, .nil, _ => rfl
  | _ :: cs, Γ, Δ, ρ, .cons a A, V => by
      show Ctxt.Valuation.comap (Ctxt.Hom.lift (homLiftApp cs ρ))
        (Ctxt.Valuation.extend (hvAppend A V : Ctxt.Valuation (cs ++ Δ)) a) = _
      rw [Ctxt.Valuation.extend_comap_lift, comap_homLiftApp cs ρ A V]
      rfl

variable [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectDenote d]

theorem stSound_extend {Γ : Ctxt d} {s : d.Ty} {V : Ctxt.Valuation Γ} (x : ⟦s⟧)
    {S : Tbl d × Defs d} (hS : StSound V S) : StSound (Γ := s :: Γ) (V.extend x) S :=
  ⟨sound_extend x hS.1, dsound_extend x hS.2⟩

/-- A state sound for `V` is sound for every extension of `V` by a prefix. -/
theorem stSound_append {S : Tbl d × Defs d} : ∀ {cs : List d.Ty} {Γ : Ctxt d}
    (A : Ctxt.Valuation cs) {V : Ctxt.Valuation Γ}, StSound V S →
    StSound (Γ := cs ++ Γ) (hvAppend A V) S
  | [], _, .nil, _, h => h
  | _ :: _, _, .cons a A, _, h => stSound_extend (Γ := _ ++ _) a (stSound_append A h)

end Prefix

/-! ## 2. The traversal -/

section Traversal

variable {d : Dialect.{0, 0}} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d]
  [DialectDenote d] [DecidableEq d.Op] [HasWord64 d] [HasBoolBit d]

/-- The aegraph traversal of a structured program at the rule set `R` under the renaming
    `ρ` and the state `S`: each let-binding as in `agGo`; each region with its variables
    renamed, its bodies and its continuation traversed under the lifted renaming and the
    state `S`. -/
def nfGo (R : RuleSet d) : {Γ Δ : Ctxt d} → {ts : List d.Ty} → Ctxt.Hom Γ Δ →
    Tbl d × Defs d → NFProg d Γ ts → NFProg d Δ ts
  | _, _, _, ρ, _, .ret vs => .ret (HVector.renameVars ρ vs)
  | _, Δ, _, ρ, S, .var e k =>
      match choose R S (e.rename ρ) with
      | .var w => nfGo R (consHom w ρ) (stVar R S (e.rename ρ) w) k
      | .one e2 => .var e2 (nfGo R (Ctxt.Hom.lift ρ) (stOne R S (e.rename ρ) e2 Δ.length) k)
      | .two e1 e2 =>
          .var e1 (.var e2
            (nfGo R (consHom .here (wk2 ρ)) (stTwo R S (e.rename ρ) e1 e2 Δ.length) k))
  | _, _, _, ρ, S, .forLoop (cs := cs) count inits body k =>
      .forLoop (ρ count) (HVector.renameVars ρ inits)
        (nfGo R (homLiftApp cs (Ctxt.Hom.lift ρ)) S body) (nfGo R (homLiftApp cs ρ) S k)
  | _, _, _, ρ, S, .ifThenElse (rs := rs) cond thn els k =>
      .ifThenElse (ρ cond) (nfGo R ρ S thn) (nfGo R ρ S els) (nfGo R (homLiftApp rs ρ) S k)
  | _, _, _, ρ, S, .whileLoop (cs := cs) inits body k =>
      .whileLoop (HVector.renameVars ρ inits) (nfGo R (homLiftApp cs ρ) S body)
        (nfGo R (homLiftApp cs ρ) S k)
  | _, _, _, ρ, S, .call (rs := rs) f args k =>
      .call f (HVector.renameVars ρ args) (nfGo R (homLiftApp rs ρ) S k)

/-- **Denotation of the traversal.** Under a state sound for `V`, the output denotes the
    input at the valuation pulled back along `ρ`, at every fuel. -/
theorem nfGo_denote [CallDenote d] (R : RuleSet d) (fuel : Nat) :
    ∀ {Γ Δ : Ctxt d} {ts : List d.Ty}
    (ρ : Ctxt.Hom Γ Δ) (S : Tbl d × Defs d) (p : NFProg d Γ ts) (V : Ctxt.Valuation Δ),
    StSound V S → (nfGo R ρ S p).denote fuel V = p.denote fuel (V.comap ρ)
  | _, _, _, ρ, _, .ret vs, V, _ => by
      simp only [nfGo, NFProg.denote, Expr.lookupArgs_renameVars]
  | _, Δ, _, ρ, S, .var (t := s) e k, V, hS => by
      simp only [nfGo]
      split
      · rename_i w hc
        obtain ⟨hS', hw⟩ := stVar_sound R hS _ hc
        rw [nfGo_denote R fuel _ _ k V hS', comap_consHom, hw, Expr.denote_rename]
        simp only [NFProg.denote, Expr.denoteM_option_eq_some, Option.bind_eq_bind,
          Option.bind_some]
      · rename_i e2 hc
        obtain ⟨hS', hw⟩ := stOne_sound R hS _ hc
        simp only [NFProg.denote, Expr.denoteM_option_eq_some, Option.bind_eq_bind,
          Option.bind_some]
        rw [nfGo_denote R fuel _ _ k _ hS', Ctxt.Valuation.extend_comap_lift, hw,
          Expr.denote_rename]
      · rename_i s1 e1 e2 hc
        obtain ⟨hS', hw⟩ := stTwo_sound R hS _ hc
        simp only [NFProg.denote, Expr.denoteM_option_eq_some, Option.bind_eq_bind,
          Option.bind_some]
        rw [nfGo_denote R fuel _ _ k _ hS', comap_consHom, comap_wk2] at *
        rw [Expr.denote_rename] at hw
        show k.denote fuel ((V.comap ρ).extend (e2.denote _)) = _
        rw [hw]
  | _, _, _, ρ, S, .forLoop (cs := cs) count inits body k, V, hS => by
      have hb : ∀ (acc : Ctxt.Valuation cs) (i : Nat),
          (nfGo R (homLiftApp cs (Ctxt.Hom.lift ρ)) S body).denote fuel
              (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) V)) =
            body.denote fuel
              (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) (V.comap ρ))) := by
        intro acc i
        refine (nfGo_denote R fuel _ S body _
            (stSound_append acc (stSound_extend (HasWord64.ofNat (d := d) i) hS))).trans ?_
        rw [comap_homLiftApp]
        exact congrArg (fun W => body.denote fuel (hvAppend acc W))
          (Ctxt.Valuation.extend_comap_lift ρ V _)
      have hk : ∀ acc : Ctxt.Valuation cs,
          (nfGo R (homLiftApp cs ρ) S k).denote fuel (hvAppend acc V) =
            k.denote fuel (hvAppend acc (V.comap ρ)) := by
        intro acc
        rw [nfGo_denote R fuel _ S k _ (stSound_append acc hS), comap_homLiftApp]
      simp only [nfGo, NFProg.denote, hb, hk, Ctxt.Valuation.lookup_comap,
        Expr.lookupArgs_renameVars]
  | _, _, _, ρ, S, .ifThenElse (rs := rs) cond thn els k, V, hS => by
      have hk : ∀ r : Ctxt.Valuation rs,
          (nfGo R (homLiftApp rs ρ) S k).denote fuel (hvAppend r V) =
            k.denote fuel (hvAppend r (V.comap ρ)) := by
        intro r
        rw [nfGo_denote R fuel _ S k _ (stSound_append r hS), comap_homLiftApp]
      simp only [nfGo, NFProg.denote, hk, Ctxt.Valuation.lookup_comap,
        nfGo_denote R fuel ρ S thn V hS, nfGo_denote R fuel ρ S els V hS]
  | _, _, _, ρ, S, .whileLoop (cs := cs) inits body k, V, hS => by
      have hb : ∀ acc : Ctxt.Valuation cs,
          (nfGo R (homLiftApp cs ρ) S body).denote fuel (hvAppend acc V) =
            body.denote fuel (hvAppend acc (V.comap ρ)) := by
        intro acc
        rw [nfGo_denote R fuel _ S body _ (stSound_append acc hS), comap_homLiftApp]
      have hk : ∀ acc : Ctxt.Valuation cs,
          (nfGo R (homLiftApp cs ρ) S k).denote fuel (hvAppend acc V) =
            k.denote fuel (hvAppend acc (V.comap ρ)) := by
        intro acc
        rw [nfGo_denote R fuel _ S k _ (stSound_append acc hS), comap_homLiftApp]
      simp only [nfGo, NFProg.denote, hb, hk, Expr.lookupArgs_renameVars]
  | _, _, _, ρ, S, .call (rs := rs) f args k, V, hS => by
      have hk : ∀ r : Ctxt.Valuation rs,
          (nfGo R (homLiftApp rs ρ) S k).denote fuel (hvAppend r V) =
            k.denote fuel (hvAppend r (V.comap ρ)) := by
        intro r
        rw [nfGo_denote R fuel _ S k _ (stSound_append r hS), comap_homLiftApp]
      simp only [nfGo, NFProg.denote, hk, Expr.lookupArgs_renameVars]

/-- **The aegraph pass on structured programs** at a rule set: the traversal from the
    identity renaming and the empty state. -/
def aegraphOptNF (R : RuleSet d) {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    NFProg d Γ ts :=
  nfGo R (Ctxt.Hom.id Γ) (∅, ∅) p

/-- **Denotation of the pass.** `aegraphOptNF R p` denotes the same function as `p` at every
    fuel, for every rule set `R`. -/
theorem aegraphOptNF_denote [CallDenote d] (R : RuleSet d) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) (fuel : Nat) :
    (aegraphOptNF R p).denote fuel = p.denote fuel :=
  funext fun V => by
    rw [aegraphOptNF, nfGo_denote R fuel _ _ p V (stSound_empty V), Ctxt.Valuation.comap_id]

/-- On an embedded straight-line program the traversal is `agGo`. -/
theorem nfGo_ofCom (R : RuleSet d) : ∀ {Γ Δ : Ctxt d} {t : d.Ty} (ρ : Ctxt.Hom Γ Δ)
    (S : Tbl d × Defs d) (c : Com d Γ t),
    nfGo R ρ S (NFProg.ofCom c) = NFProg.ofCom (agGo R ρ S c)
  | _, _, _, _, _, .ret _ => rfl
  | _, Δ, _, ρ, S, .var e body => by
      simp only [NFProg.ofCom, nfGo, agGo]
      cases choose R S (e.rename ρ) <;> simp only [NFProg.ofCom, nfGo_ofCom]

/-- On an embedded straight-line program the pass is `aegraphOptOf`. -/
theorem aegraphOptNF_ofCom (R : RuleSet d) {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) :
    aegraphOptNF R (NFProg.ofCom c) = NFProg.ofCom (aegraphOptOf R c) :=
  nfGo_ofCom R _ _ c

end Traversal

end CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF
