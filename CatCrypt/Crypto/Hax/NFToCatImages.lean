/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.NFToCat
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin
public import CatCrypt.Crypto.Optimizer.Rewrite.AegraphCat
public import CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF
public import CatCrypt.Crypto.Optimizer.Rewrite.AegraphFieldGood

/-!
# The conversion to the Jasmin dialect is defined on the programs of the typed front

`NFProg.map?` along `catToJasmin` is `some` exactly on the programs whose let-bound
expressions all have a block `toJBlockD` (`Convertible`). An operation of
`catCryptDialect` has an image (`HasImage`) when `toJBlockD` is `some` on every expression
with that operation. Every operation of a program `nfToCat` returns has an image, the
e-graph pass at `catRules` keeps this property, and a program with this property is
`Convertible`.

## Main definitions

* `Convertible` — every let-bound expression of a program has a block `toJBlockD`.
* `HasImage` — `toJBlockD` is `some` on every expression with the operation.
* `OpsHaveImages` — every let-bound expression of a program has an operation with an
  image.

## Main results

* `isSome_map?_catToJasmin_iff` — `map?` along `catToJasmin` is `some` exactly on the
  `Convertible` programs.
* `nfToCat_opsHaveImages` — every operation of a program `nfToCat` returns has an image.
* `nfGo_covered`, `catRules_opsIn`, `aegraphOptNF_catRules_opsHaveImages` — the e-graph
  traversal keeps coverage by an operation predicate that the rules keep; the rules of
  `catRules` keep every predicate that holds of the constants; the pass at `catRules` keeps
  `OpsHaveImages`.
* `isSome_map?_aegraphOptNF_nfToCat` — `map?` along `catToJasmin` is `some` on the e-graph
  pass of a program `nfToCat` returns.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax.NFToCatImages

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy Ctx)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom (toJBlockD)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphCat
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphFieldGood
open CatCrypt.Crypto.Optimizer.Rewrite.TraitRules
open Ctxt (Var Valuation)

/-! ## 1. The programs the conversion accepts -/

/-- The programs whose let-bound expressions all have a block `toJBlockD`, in every
    region. -/
def Convertible {Γ : Ctxt catCryptDialect} {ts : List CryptoTy}
    (p : NFProg catCryptDialect Γ ts) : Prop :=
  p.Covered (fun {_ _} e => (toJBlockD e).isSome = true)

/-- **The conversion returns a program exactly on the `Convertible` programs.** At every
    renaming, `map?` along `catToJasmin` is `some` on `p` if and only if every let-bound
    expression of `p` and of its regions has a block `toJBlockD`. -/
theorem isSome_map?_catToJasmin_iff {Γ : Ctxt catCryptDialect} {ts : List CryptoTy}
    (p : NFProg catCryptDialect Γ ts) {Δ : Ctxt JasminDialect.jasminDialect}
    (ren : Ctxt.Hom (catToJasmin.mapCtx Γ) Δ) :
    (NFProg.map? catToJasmin catToJasmin_regionTypes p ren).isSome ↔ Convertible p :=
  NFProg.isSome_map?_iff catToJasmin catToJasmin_regionTypes p ren

/-- An operation of `catCryptDialect` has an image in the Jasmin dialect: `toJBlockD` is
    `some` on every expression with this operation. -/
def HasImage (op : CatCryptOp) : Prop :=
  ∀ {Γ : Ctx} {t : CryptoTy} (e : Expr catCryptDialect Γ t), e.op = op →
    (toJBlockD e).isSome = true

/-- The programs whose let-bound expressions all have an operation with an image. -/
def OpsHaveImages {Γ : Ctxt catCryptDialect} {ts : List CryptoTy}
    (p : NFProg catCryptDialect Γ ts) : Prop :=
  p.Covered (fun {_ _} e => HasImage e.op)

/-- A program whose operations all have images is `Convertible`. -/
theorem OpsHaveImages.convertible {Γ : Ctxt catCryptDialect} {ts : List CryptoTy}
    {p : NFProg catCryptDialect Γ ts} (h : OpsHaveImages p) : Convertible p :=
  NFProg.Covered.mono (fun e he => he e rfl) h

/-- Closes `HasImage op` at an operation on which `toJBlockD` reduces to `some`. -/
local macro "image_op" : tactic =>
  `(tactic| (intro _ _ e h; obtain ⟨op, hr, args⟩ := e; dsimp only at h; subst h; rfl))

/-! ## 2. The operations of the typed front -/

/-- Every expression of the translation of an operation has an operation with an image. -/
def OpResImages : {Δ : Ctxt catCryptDialect} → {t : NfTy} → OpRes Δ t → Prop
  | _, _, .rd _ => True
  | _, _, .expr e => HasImage e.op
  | _, _, .expr1 _ e => HasImage e.op
  | _, _, .bind _ e k => HasImage e.op ∧ OpResImages k

theorem scalarCatExpr_image {Δ : Ctxt catCryptDialect} {f : String} {a b : Var Δ (.sword 64)}
    {e : Expr catCryptDialect Δ (.sword 64)} (h : scalarCatExpr f a b = some e) :
    HasImage e.op := by
  unfold scalarCatExpr at h
  split at h <;> first | (cases h; image_op) | cases h

theorem selectCat_image {Δ : Ctxt catCryptDialect} {f : String} {tc ta tb : NfTy}
    {args : HVector (fun t => Var Δ t) ([tc, ta, tb].map catTy)}
    {e : Expr catCryptDialect Δ (.sword 64)} (h : selectCat f tc ta tb args = some e) :
    HasImage e.op := by
  unfold selectCat at h
  split at h
  · obtain ⟨c, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨x, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨y, -, rfl⟩ := Option.map_eq_some_iff.mp h
    image_op
  · cases h

theorem catCall?_image {Δ : Ctxt catCryptDialect} {f : String} {as : List NfTy} {r : NfTy}
    {args : HVector (fun t => Var Δ t) (as.map catTy)} {e : Expr catCryptDialect Δ (catTy r)}
    (h : catCall? f as r args = some e) : HasImage e.op := by
  unfold catCall? at h
  split at h
  · split at h
    · obtain ⟨⟨n, a⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨i, -, rfl⟩ := Option.map_eq_some_iff.mp h
      image_op
    · obtain ⟨x, -, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨y, -, h⟩ := Option.bind_eq_some_iff.mp h
      exact scalarCatExpr_image h
  · split at h
    · obtain ⟨⟨n, m⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
      dsimp only at h
      split at h
      · obtain ⟨i, -, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨x, -, rfl⟩ := Option.map_eq_some_iff.mp h
        image_op
      · cases h
    · cases h
  · exact selectCat_image h
  · exact selectCat_image h
  · cases h

theorem shiftImm?_image {Δ : Ctxt catCryptDialect} {f : String} {as : List NfTy} {r : NfTy}
    {rs : HVector (fun t => Rd Δ t) as} {e : Expr catCryptDialect Δ (catTy r)}
    (h : shiftImm? f as r rs = some e) : HasImage e.op := by
  unfold shiftImm? at h
  split at h
  · split at h
    · split at h
      · obtain ⟨x, -, h⟩ := Option.bind_eq_some_iff.mp h
        split at h
        · cases h; image_op
        · split at h
          · cases h; image_op
          · cases h
      · cases h
    · cases h
  · cases h

theorem catCallRd0_image {Δ : Ctxt catCryptDialect} {f : String} {as : List NfTy} {r : NfTy}
    {rs : HVector (fun t => Rd Δ t) as} {res : OpRes Δ r}
    (h : catCallRd0 f as r rs = some res) : OpResImages res := by
  unfold catCallRd0 at h
  split at h
  · obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
    exact catCall?_image he
  · split at h
    · rename_i e he
      cases h
      exact shiftImm?_image he
    · exact pinRes_elim (M := fun _ res => OpResImages res)
        (fun _ _ _ _ he => by simp only [OpResImages]; exact catCall?_image he)
        (fun _ c _ _ ih => by
          simp only [OpResImages]
          exact ⟨(by image_op : HasImage (.bvConst 64 (BitVec.ofNat 64 c))), ih⟩) _ rs res h

theorem binE_image {Δ : Ctxt catCryptDialect} {o : ImpToNF.ScalarBin} {a b : Var Δ (.sword 64)}
    {e : Expr catCryptDialect Δ (.sword 64)} (h : binE o a b = some e) :
    HasImage e.op := by
  cases o <;> first | (cases h; image_op) | cases h

theorem maskRes_image {Δ : Ctxt catCryptDialect} (w : Nat)
    {e : Expr catCryptDialect Δ (.sword 64)} (h : HasImage e.op) :
    OpResImages (maskRes w e) := by
  unfold maskRes
  split
  · exact h
  · exact ⟨h, by image_op, by image_op⟩

theorem binChain_image {Δ : Ctxt catCryptDialect} {o : ImpToNF.ScalarBin} {w : Nat}
    {a b : Var Δ (.sword 64)} {res : OpRes Δ (.word 64)} (h : binChain o w a b = some res) :
    OpResImages res := by
  unfold binChain at h
  split at h
  · cases h
    exact ⟨by image_op, by image_op, by image_op⟩
  · obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
    exact maskRes_image w (binE_image he)

theorem rotChain_image {Δ : Ctxt catCryptDialect} (right : Bool) (w k : Nat)
    (a : Var Δ (.sword 64)) : OpResImages (rotChain right w k a) := by
  cases right <;>
    exact ⟨by image_op, by image_op, by image_op, by image_op, by image_op, by image_op⟩

theorem rotVarChain_image {Δ : Ctxt catCryptDialect} (right : Bool) (w : Nat)
    (a b : Var Δ (.sword 64)) : OpResImages (rotVarChain right w a b) := by
  cases right <;>
    exact ⟨by image_op, by image_op, by image_op, by image_op, by image_op, by image_op,
      by image_op, by image_op, by image_op, by image_op⟩

theorem notChain_image {Δ : Ctxt catCryptDialect} (w : Nat) (a : Var Δ (.sword 64)) :
    OpResImages (notChain w a) := by
  unfold notChain
  split
  · exact ⟨by image_op, by image_op⟩
  · exact ⟨by image_op, by image_op, by image_op⟩

theorem unChain_image {Δ : Ctxt catCryptDialect} (o : ImpToNF.ScalarUn) (w : Nat)
    (a : Var Δ (.sword 64)) : OpResImages (unChain o w a) := by
  cases o
  · exact notChain_image w a
  · exact ⟨by image_op, by image_op⟩
  · exact ⟨by image_op, by image_op⟩
  · exact ⟨by image_op, by image_op⟩

theorem geChain_image {Δ : Ctxt catCryptDialect} (c : BitVec 1) (x y : Var Δ (.sword 64)) :
    OpResImages (geChain c x y) :=
  ⟨by image_op, by image_op, by image_op, by image_op, by image_op, by image_op, by image_op⟩

theorem cmpChain_image {Δ : Ctxt catCryptDialect} (c : ImpToNF.ScalarCmp)
    (x y : Var Δ (.sword 64)) : OpResImages (cmpChain c x y) := by
  cases c
  case eq => exact (by image_op : HasImage (.bvEq 64))
  case ne => exact ⟨by image_op, by image_op⟩
  all_goals exact geChain_image _ _ _

theorem withVar1_image {Δ : Ctxt catCryptDialect} {r ta : NfTy} {ra : Rd Δ ta}
    {k : ∀ {Δ' : Ctxt catCryptDialect}, Var Δ' (.sword 64) → Option (OpRes Δ' r)}
    (hk : ∀ {Δ' : Ctxt catCryptDialect} (x : Var Δ' (.sword 64)) (res : OpRes Δ' r),
      k x = some res → OpResImages res)
    {res : OpRes Δ r} (h : withVar1 ta ra k = some res) : OpResImages res := by
  unfold withVar1 at h
  split at h
  · obtain ⟨x, -, h⟩ := Option.bind_eq_some_iff.mp h
    exact hk x _ h
  · obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨by image_op, hk _ _ hr⟩

theorem withVar2_image {Δ : Ctxt catCryptDialect} {r ta tb : NfTy} {ra : Rd Δ ta}
    {rb : Rd Δ tb}
    {k : ∀ {Δ' : Ctxt catCryptDialect}, Var Δ' (.sword 64) → Var Δ' (.sword 64) →
      Option (OpRes Δ' r)}
    (hk : ∀ {Δ' : Ctxt catCryptDialect} (x y : Var Δ' (.sword 64)) (res : OpRes Δ' r),
      k x y = some res → OpResImages res)
    {res : OpRes Δ r} (h : withVar2 ta tb ra rb k = some res) : OpResImages res := by
  unfold withVar2 at h
  split at h
  · obtain ⟨x, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨y, -, h⟩ := Option.bind_eq_some_iff.mp h
    exact hk x y _ h
  · obtain ⟨y, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨by image_op, hk _ _ _ hr⟩
  · obtain ⟨x, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨by image_op, hk _ _ _ hr⟩
  · obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨by image_op, by image_op, hk _ _ _ hr⟩

theorem bitRes2_image {Δ : Ctxt catCryptDialect} {f : String} {ta tb : NfTy} {ra : Rd Δ ta}
    {rb : Rd Δ tb} {res : OpRes Δ .bit} (h : bitRes2 f ta tb ra rb = some res) :
    OpResImages res := by
  unfold bitRes2 at h
  split at h
  · obtain ⟨x, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨y, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨o, -, h⟩ := Option.bind_eq_some_iff.mp h
    cases o <;> cases h
    · exact (by image_op : HasImage .and)
    · exact (by image_op : HasImage .or)
    · exact (by image_op : HasImage .eqBit)
    · exact (by image_op : HasImage .xor)
  · cases h

theorem bitRes1_image {Δ : Ctxt catCryptDialect} {f : String} {ta : NfTy} {ra : Rd Δ ta}
    {res : OpRes Δ .bit} (h : bitRes1 f ta ra = some res) : OpResImages res := by
  unfold bitRes1 at h
  split at h
  · obtain ⟨x, -, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases h
      exact (by image_op : HasImage .not)
    · cases h
  · cases h

theorem scalarRes2_image {Δ : Ctxt catCryptDialect} {f : String} {ta tb : NfTy} {ra : Rd Δ ta}
    {rb : Rd Δ tb} {r : NfTy} {res : OpRes Δ r} (h : scalarRes2 f ta tb ra rb r = some res) :
    OpResImages res := by
  unfold scalarRes2 at h
  split at h
  · obtain ⟨⟨o, w⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
    dsimp only at h
    split at h
    · split at h
      · exact withVar1_image (fun x res hx => by cases hx; exact rotChain_image _ _ _ _) h
      · exact withVar2_image (fun x y res hx => by cases hx; exact rotVarChain_image _ _ _ _) h
    · exact withVar2_image (fun x y res hx => binChain_image hx) h
  · split at h
    · exact bitRes2_image h
    obtain ⟨c, -, h⟩ := Option.bind_eq_some_iff.mp h
    exact withVar2_image (fun x y res hx => by cases hx; exact cmpChain_image _ _ _) h
  · cases h

theorem scalarRes1_image {Δ : Ctxt catCryptDialect} {f : String} {ta : NfTy} {ra : Rd Δ ta}
    {r : NfTy} {res : OpRes Δ r} (h : scalarRes1 f ta ra r = some res) : OpResImages res := by
  unfold scalarRes1 at h
  split at h
  · obtain ⟨⟨o, w⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
    dsimp only at h
    split at h
    · obtain ⟨r', -, rfl⟩ := Option.map_eq_some_iff.mp h
      trivial
    · exact withVar1_image (fun x res hx => by cases hx; exact unChain_image _ _ _) h
  · exact bitRes1_image h
  · cases h

theorem scalarRes?_image {Δ : Ctxt catCryptDialect} {f : String} {as : List NfTy} {r : NfTy}
    {rs : HVector (fun t => Rd Δ t) as} {res : OpRes Δ r}
    (h : scalarRes? f as r rs = some res) : OpResImages res := by
  rcases rs with _ | ⟨ra, _ | ⟨rb, _ | ⟨rc, rest⟩⟩⟩
  · cases h
  · exact scalarRes1_image h
  · exact scalarRes2_image h
  · cases h

theorem catCallRd_image {Δ : Ctxt catCryptDialect} {f : String} {as : List NfTy} {r : NfTy}
    {rs : HVector (fun t => Rd Δ t) as} {res : OpRes Δ r}
    (h : catCallRd f as r rs = some res) : OpResImages res := by
  unfold catCallRd at h
  split at h
  · rename_i res' h0
    cases h
    exact catCallRd0_image h0
  · exact scalarRes?_image h

theorem tripRes_image {Δ : Ctxt catCryptDialect} (r : Rd Δ (.word 64)) :
    OpResImages (tripRes r) := by
  cases r
  · trivial
  · exact (by image_op : HasImage (.bvConst 64 _))

theorem ctrRes_image {Δ : Ctxt catCryptDialect} {rlo : Rd Δ .int} {ri : Rd Δ (.word 64)}
    {res : OpRes Δ (.word 64)} (h : ctrRes rlo ri = some res) : OpResImages res :=
  withVar2_image (fun _ _ _ hk => by cases hk; exact (by image_op : HasImage (.bvAdd 64))) h

theorem satSubRes_image {Δ : Ctxt catCryptDialect} (x y : Var Δ (.sword 64)) :
    OpResImages (satSubRes x y) :=
  ⟨by image_op, by image_op, by image_op, by image_op, by image_op, by image_op, by image_op,
    by image_op, by image_op⟩

theorem tripSub_image {Δ : Ctxt catCryptDialect} {rlo : Rd Δ .int} {rhi : Rd Δ (.word 64)}
    {res : OpRes Δ (.word 64)} (h : tripSub rlo rhi = some res) : OpResImages res := by
  unfold tripSub at h
  split at h
  · cases h
    exact (by image_op : HasImage (.bvConst 64 _))
  · exact withVar2_image (fun x y _ hk => by cases hk; exact satSubRes_image x y) h

/-- Every expression of the translation `catOp` of an operation has an operation with an
    image. -/
theorem catOp_image {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ)
    (op : NfOp) (args : HVector (fun t => Var Γ t) op.sig) (res : OpRes Δ op.ret)
    (h : catOp σ op args = some res) : OpResImages res := by
  induction op with
  | named _ op ih => exact ih args res h
  | call f as r => exact catCallRd_image h
  | ilit t v =>
      unfold catOp at h
      split at h
      · cases h; trivial
      · unfold uintLit? at h
        split at h
        · split at h
          · cases h; exact (by image_op : HasImage (.bvConst 64 _))
          · cases h
        · cases h
  | ctr =>
      unfold catOp at h
      split at h
      · cases h; trivial
      · exact ctrRes_image h
  | trip t =>
      unfold catOp at h
      split at h
      · obtain ⟨r', -, rfl⟩ := Option.map_eq_some_iff.mp h
        exact tripRes_image r'
      · obtain ⟨r', -, h⟩ := Option.bind_eq_some_iff.mp h
        exact tripSub_image h
  | bin o w =>
      rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
      change binRes? o w (σ a) (σ b) = some res at h
      unfold binRes? at h
      split at h
      · obtain ⟨rfl, rfl⟩ := ‹_ ∧ _›
        exact withVar2_image (fun _ _ _ hk => binChain_image hk) h
      · cases h
  | constBit b =>
      cases h
      exact (by image_op : HasImage (.constBit b))
  | constUnit =>
      cases h
      exact (by image_op : HasImage .constUnit)
  | _ => cases h

/-- The bindings `emitRes` gives a translation whose operations have images, in front of a
    continuation whose programs have operations with images, form such a program. -/
theorem emitRes_opsHaveImages {Γ : Ctxt nfDialect} {s : NfTy} {ts : List NfTy}
    {cont : ∀ {Δ' : Ctxt catCryptDialect}, TRd (s :: Γ) Δ' →
      Option (NFProg catCryptDialect Δ' (ts.map catTy))}
    (hcont : ∀ {Δ' : Ctxt catCryptDialect} (σ' : TRd (s :: Γ) Δ')
      (q : NFProg catCryptDialect Δ' (ts.map catTy)), cont σ' = some q → OpsHaveImages q) :
    ∀ {Δ : Ctxt catCryptDialect} {t : NfTy} (h : t = s) (res : OpRes Δ t) (σ : TRd Γ Δ)
      (q : NFProg catCryptDialect Δ (ts.map catTy)), OpResImages res →
      emitRes cont h res σ = some q → OpsHaveImages q
  | _, _, _, .rd _, _, q, _, hq => hcont _ q hq
  | _, _, _, .expr _, _, _, hr, hq => by
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq
      exact And.intro hr (hcont _ k' hk')
  | _, _, _, .expr1 _ _, _, _, hr, hq => by
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq
      exact And.intro (by image_op) (And.intro hr (hcont _ k' hk'))
  | _, _, h, .bind _ _ rest, σ, _, hr, hq => by
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq
      exact And.intro hr.1 (emitRes_opsHaveImages hcont h rest σ.wk k' hr.2 hk')

/-- The `bvConst` bindings of `pinAll` in front of a program `k` gives whose operations have
    images form such a program. -/
theorem pinAll_opsHaveImages {Γ : Ctxt nfDialect} {us : List CryptoTy} {ts : List NfTy}
    {k : ∀ {Δ' : Ctxt catCryptDialect}, TRd Γ Δ' →
      HVector (fun t => Var Δ' t) (ts.map catTy) → Option (NFProg catCryptDialect Δ' us)}
    (hk : ∀ {Δ' : Ctxt catCryptDialect} (σ' : TRd Γ Δ')
      (ws : HVector (fun t => Var Δ' t) (ts.map catTy)) (q : NFProg catCryptDialect Δ' us),
      k σ' ws = some q → OpsHaveImages q)
    {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ) (rs : HVector (fun t => Rd Δ t) ts)
    (q : NFProg catCryptDialect Δ us) (h : pinAll k σ rs = some q) : OpsHaveImages q :=
  pinAll_elim (M := fun {_} _ _ q => OpsHaveImages q)
    (fun σ _ ws q _ hq => hk σ ws q hq)
    (fun _ _ _ _ _ ih => And.intro (by image_op) ih) σ rs q h

/-- **Every operation of a translated program has an image.** A program `nfToCat` returns
    has, at every let-binding of the program and of its regions, an operation on which the
    lowering `toJBlockD` to the Jasmin dialect is `some`. -/
theorem nfToCat_opsHaveImages {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) :
    ∀ {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ) (q : NFProg catCryptDialect Δ (ts.map catTy)),
      nfToCat p σ = some q → OpsHaveImages q := by
  induction p with
  | ret vs =>
      intro _ σ q h
      refine pinAll_opsHaveImages ?_ σ _ q h
      intro _ _ _ q' hq'
      cases hq'
      trivial
  | var e k ih =>
      intro _ σ q h
      rcases e with ⟨op, he, args⟩
      obtain ⟨res, hres, h⟩ := Option.bind_eq_some_iff.mp h
      exact emitRes_opsHaveImages (fun σ' q' hq' => ih σ' q' hq') he res σ q
        (catOp_image σ op args res hres) h
  | @forLoop _ cs _ count inits body k ihb ihk =>
      intro _ σ q h
      refine pinAll_opsHaveImages (ts := .word 64 :: cs) ?_ σ _ q h
      intro _ _ _ q' hq'
      obtain ⟨b', hb, hq'⟩ := Option.bind_eq_some_iff.mp hq'
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp hq'
      exact And.intro (ihb _ b' hb) (ihk _ k' hk)
  | ifThenElse cond thn els k iht ihe ihk =>
      intro _ σ q h
      simp only [nfToCat] at h
      split at h
      · obtain ⟨t', ht, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp h
        exact And.intro (iht _ t' ht) (And.intro (ihe _ e' he) (ihk _ k' hk))
      · cases h
  | whileLoop => intro _ σ q h; cases h
  | call => intro _ σ q h; cases h

/-! ## 3. The e-graph pass -/

section Traversal

variable {d : Dialect.{0, 0}} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d]
  [DialectDenote d] [DecidableEq d.Op] [HasWord64 d] [HasBoolBit d] {g : d.Op → Prop}

/-- **Coverage of the traversal of a structured program.** For a rule set satisfying
    `RulesOpsIn g`, under every renaming and state, `nfGo R` maps a program whose bindings
    have operations satisfying `g`, in every region, to such a program. -/
theorem nfGo_covered (R : RuleSet d) (hR : RulesOpsIn g R) :
    ∀ {Γ Δ : Ctxt d} {ts : List d.Ty} (ρ : Ctxt.Hom Γ Δ) (S : Tbl d × Defs d)
      (p : NFProg d Γ ts), p.Covered (fun {_ _} e => g e.op) →
      (nfGo R ρ S p).Covered (fun {_ _} e => g e.op)
  | _, _, _, _, _, .ret _, _ => trivial
  | _, _, _, ρ, S, .var e k, h => by
      obtain ⟨he, hk⟩ : g e.op ∧ k.Covered (fun {_ _} e => g e.op) := h
      have hc := choose_opsIn R hR S (e.rename ρ) he
      simp only [nfGo]
      split
      · exact nfGo_covered R hR _ _ k hk
      · rename_i e2 hce
        rw [hce] at hc
        exact And.intro hc (nfGo_covered R hR _ _ k hk)
      · rename_i s1 e1 e2 hce
        rw [hce] at hc
        exact And.intro hc.1 (And.intro hc.2 (nfGo_covered R hR _ _ k hk))
  | _, _, _, _, S, .forLoop _ _ body k, h =>
      And.intro (nfGo_covered R hR _ S body h.1) (nfGo_covered R hR _ S k h.2)
  | _, _, _, _, S, .ifThenElse _ thn els k, h =>
      And.intro (nfGo_covered R hR _ S thn h.1)
        (And.intro (nfGo_covered R hR _ S els h.2.1) (nfGo_covered R hR _ S k h.2.2))
  | _, _, _, _, S, .whileLoop _ body k, h =>
      And.intro (nfGo_covered R hR _ S body h.1) (nfGo_covered R hR _ S k h.2)
  | _, _, _, _, S, .call _ _ k, h => nfGo_covered R hR _ S k h

end Traversal

/-- **The rules of `catRules` keep every operation predicate that holds of the constants.**
    The bit-vector identities, the shift by zero, the involution and the idempotence rules
    emit existing variables and `bvConst`; the self-cancellation rule emits `constBit`;
    constant folding emits `bvConst`, `constBit` or `constUnit`. -/
theorem catRules_opsIn {g : CatCryptOp → Prop} (hc : ∀ w c, g (.bvConst w c))
    (hb : ∀ b, g (.constBit b)) (hu : g .constUnit) : RulesOpsIn g catRules := by
  refine rulesOpsIn_of_forall fun r hr => ?_
  simp only [catRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  iterate 7
    · intro D Δ s e _ alt ha
      rcases e with ⟨op, hop, args⟩
      cases op <;> simp only [xorRule, andRule, orRule, addRule, subRule, mulRule,
        shiftZeroRule, xorApply, andApply, orApply, addApply, subApply, mulApply,
        shiftZeroApply, List.not_mem_nil] at ha
      all_goals subst hop
      all_goals simp only [xorAlts, andAlts, orAlts, addAlts, subAlts, mulAlts, zeroAmtAlts,
        List.mem_append] at ha
      all_goals repeat' rcases ha with ha | ha
      all_goals split at ha <;> simp only [List.mem_singleton, List.not_mem_nil] at ha
      all_goals subst ha
      all_goals first | trivial | exact hc _ _
  · intro D Δ s e _ alt ha
    change alt ∈ invApply catInvolution D e at ha
    unfold invApply at ha
    split at ha
    · split at ha
      · split at ha
        · split at ha
          · obtain ⟨x, -, rfl⟩ := mem_varAlts ha
            trivial
          · simp at ha
        · simp at ha
      · simp at ha
    · simp at ha
  · intro D Δ s e _ alt ha
    change alt ∈ idemApply catIdempotent e at ha
    unfold idemApply at ha
    split at ha
    · split at ha
      · split at ha
        · obtain ⟨x, -, rfl⟩ := mem_varAlts ha
          trivial
        · simp at ha
      · simp at ha
    · simp at ha
  · intro D Δ s e _ alt ha
    change alt ∈ cancelApply catSelfCancel e at ha
    unfold cancelApply at ha
    split at ha
    · split at ha
      · split at ha
        · simp only [List.mem_singleton] at ha
          subst ha
          show g (catSelfCancel.zero e.op)
          simp only [catSelfCancel]
          split <;> exact hb _
        · simp at ha
      · simp at ha
    · simp at ha
  · intro D Δ s e _ alt ha
    change alt ∈ foldApply catReify (fun _ => true) D e at ha
    unfold foldApply at ha
    split at ha
    · split at ha
      · split at ha
        · split at ha
          · split at ha
            · rename_i c hc'
              simp only [List.mem_singleton] at ha
              subst ha
              show g c
              revert hc'
              cases s <;> simp only [catReify, catReifyOp, Option.some.injEq, reduceCtorEq,
                IsEmpty.forall_iff] <;> rintro rfl <;>
                first | exact hc _ _ | exact hb _ | exact hu
            · simp at ha
          · simp at ha
        · simp at ha
      · simp at ha
    · simp at ha

/-- **The e-graph pass at `catRules` keeps `OpsHaveImages`.** -/
theorem aegraphOptNF_catRules_opsHaveImages {Γ : Ctxt catCryptDialect} {ts : List CryptoTy}
    (p : NFProg catCryptDialect Γ ts) (h : OpsHaveImages p) :
    OpsHaveImages (aegraphOptNF catRules p) :=
  nfGo_covered catRules
    (catRules_opsIn (g := HasImage) (fun _ _ => by image_op) (fun _ => by image_op)
      (by image_op)) _ _ p h

/-! ## 4. The conversion after the front and the e-graph pass -/

/-- **The conversion is defined on the e-graph pass of a translated program.** For a
    program `q` that `nfToCat` returns, `map?` along `catToJasmin` is `some` on
    `aegraphOptNF catRules q`, at every renaming. -/
theorem isSome_map?_aegraphOptNF_nfToCat {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ)
    (q : NFProg catCryptDialect Δ (ts.map catTy)) (h : nfToCat p σ = some q)
    {Δ' : Ctxt JasminDialect.jasminDialect} (ren : Ctxt.Hom (catToJasmin.mapCtx Δ) Δ') :
    (NFProg.map? catToJasmin catToJasmin_regionTypes (aegraphOptNF catRules q) ren).isSome :=
  (isSome_map?_catToJasmin_iff _ ren).2
    (aegraphOptNF_catRules_opsHaveImages q (nfToCat_opsHaveImages p σ q h)).convertible

end CatCrypt.Crypto.Hax.NFToCatImages
