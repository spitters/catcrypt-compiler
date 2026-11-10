/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomPasses

/-!
# Splicing a block of the store-chain shape

The field dialect step replaces the call of the tagged head of a member of the field domain by
its lowered body, and the lowering of a raised body splices the template block of each field
operation before the lowering of its continuation. A block whose embedding has the shape
`LoadsChain` (loads and memory-free bindings, then one chain of stores ending in the return of
the last version), spliced before continuations that continue the chain at the returned version,
has the shape, and a renamed block keeps it.

## Main definitions

* `ChainTailAt`: a program continues the chain at a variable whose type equals an array type.

## Main results

* `chainTail_ofCom_rename`, `loadsChain_ofCom_rename`: a renamed block whose embedding has the
  shape has it.
* `chainTail_spliceNF?_ofCom`, `loadsChain_spliceNF?_ofCom`: the splice of a block whose
  embedding has the shape, before continuations that continue the chain, has the shape.
* `canonTemplateOf_wide`, `ofWordsBlock?_wide_comFree`, `toWordsBlock?_wide_ret`,
  `bodyBlock?_wide_loadsChain`: at a modulus with a wide template and no narrow representation,
  the casts of the limb template are returns of their arguments and the block of a method has
  the shape `LoadsChain`.
* `lowerArr_loadsChain`, `fieldBodyD_loadsChain`: the lowered body of a tagged head at such a
  modulus has the shape `LoadsChain`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldWideLeak (jMemFree)
open Ctxt (Var)

/-! ## 1. Splicing a block of the store-chain shape -/

/-- **A program continues the chain at `res`**: at every array type equal to the type of
    `res`, it is a chain tail at `res` read at that type. -/
def ChainTailAt {Γ : Ctxt jasminDialect} {a : JasminTy} {ts : List JasminTy} (res : Var Γ a)
    (q : NFProg jasminDialect Γ ts) : Prop :=
  ∀ (w m : Nat) (h : a = .stackArr w m), ChainTail (h ▸ res) q

/-- A chain tail at an array variable continues the chain there. -/
theorem chainTailAt_of_chainTail {Γ : Ctxt jasminDialect} {w m : Nat} {ts : List JasminTy}
    {res : Var Γ (.stackArr w m)} {q : NFProg jasminDialect Γ ts} (h : ChainTail res q) :
    ChainTailAt res q := by
  intro w' m' hw
  injection hw with h1 h2
  subst h1 h2
  exact h

/-- **A renamed block whose embedding is a chain tail** is a chain tail at the image of the
    current version. -/
theorem chainTail_ofCom_rename : ∀ {w' m' : Nat} {Γ Γ' : Ctxt jasminDialect} {a : JasminTy}
    (c : Com jasminDialect Γ a) (u : Var Γ (.stackArr w' m')) (f : Ctxt.Hom Γ Γ'),
    ChainTail u (NFProg.ofCom c) → ChainTail (f u) (NFProg.ofCom (c.rename f))
  | _, _, _, _, _, .ret v, u, f, h => by
      change ChainTail u (.ret (.cons v .nil)) at h
      cases h
      exact .ret _
  | w', m', Γ, _, _, .var (t := t) e c, u, f, h => by
      change ChainTail u (.var e (NFProg.ofCom c)) at h
      change ChainTail (f u) (.var (e.rename f) (NFProg.ofCom (c.rename f.lift)))
      have ih := fun (u' : Var (t :: Γ) (JasminTy.stackArr w' m'))
          (h' : ChainTail u' (NFProg.ofCom c)) => chainTail_ofCom_rename c u' f.lift h'
      cases h with
      | free _ _ _ he hb => exact .free _ _ _ he (ih _ hb)
      | store _ i x _ hb => exact .store _ (f i) (f x) _ (lift_here_chainTail f (ih .here hb))

/-- **A renamed block whose embedding has the shape `LoadsChain`** has the shape. -/
theorem loadsChain_ofCom_rename : ∀ {Γ Γ' : Ctxt jasminDialect} {a : JasminTy}
    (c : Com jasminDialect Γ a) (f : Ctxt.Hom Γ Γ'),
    LoadsChain (NFProg.ofCom c) → LoadsChain (NFProg.ofCom (c.rename f))
  | _, _, _, .ret _, _, _ => .ret _
  | _, _, _, .var e c, f, h => by
      change LoadsChain (.var e (NFProg.ofCom c)) at h
      change LoadsChain (.var (e.rename f) (NFProg.ofCom (c.rename f.lift)))
      have ih := fun h' => loadsChain_ofCom_rename c f.lift h'
      cases h with
      | free _ _ he hb => exact .free _ _ he (ih hb)
      | load a i _ hb => exact .load (f a) (f i) _ (ih hb)
      | store _ i x _ hb =>
          have h2 := chainTail_ofCom_rename c .here f.lift hb
          exact .store _ (f i) (f x) _ (lift_here_chainTail f h2)

/-- **The splice of a block whose embedding is a chain tail** at `u`, before continuations
    that continue the chain at the returned version, is a chain tail at `u`. -/
theorem chainTail_spliceNF?_ofCom {ts : List JasminTy} :
    ∀ {w' m' : Nat} {Δ : Ctxt jasminDialect} {a : JasminTy} (blk : Com jasminDialect Δ a)
      (K : {Δ' : Ctxt jasminDialect} → Ctxt.Hom Δ Δ' → Var Δ' a →
        Option (NFProg jasminDialect Δ' ts)) (u : Var Δ (.stackArr w' m')),
      ChainTail u (NFProg.ofCom blk) →
      (∀ {Δ' : Ctxt jasminDialect} (ren' : Ctxt.Hom Δ Δ') (res : Var Δ' a)
        (q' : NFProg jasminDialect Δ' ts), K ren' res = some q' → ChainTailAt res q') →
      ∀ {q : NFProg jasminDialect Δ ts}, NFProg.spliceNF? blk K = some q → ChainTail u q
  | _, _, _, _, .ret v, K, u, h, hK, _, hq => by
      change ChainTail u (.ret (.cons v .nil)) at h
      cases h
      exact hK _ _ _ hq _ _ rfl
  | w', m', Δ, _, .var (t := t) e blk, K, u, h, hK, _, hq => by
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
      change ChainTail u (.var e (NFProg.ofCom blk)) at h
      have ih := fun (u' : Var (t :: Δ) (JasminTy.stackArr w' m'))
          (h' : ChainTail u' (NFProg.ofCom blk)) =>
        chainTail_spliceNF?_ofCom blk _ u' h' (fun ren' res q'' hq'' => hK _ res q'' hq'') hq'
      cases h with
      | free _ _ _ he hb => exact .free _ _ _ he (ih _ hb)
      | store _ i x _ hb => exact .store _ _ _ _ (ih .here hb)

/-- **The splice of a block whose embedding has the shape `LoadsChain`**, before continuations
    that continue the chain at the returned version, has the shape `LoadsChain`. -/
theorem loadsChain_spliceNF?_ofCom {ts : List JasminTy} :
    ∀ {Δ : Ctxt jasminDialect} {a : JasminTy} (blk : Com jasminDialect Δ a)
      (K : {Δ' : Ctxt jasminDialect} → Ctxt.Hom Δ Δ' → Var Δ' a →
        Option (NFProg jasminDialect Δ' ts)),
      LoadsChain (NFProg.ofCom blk) →
      (∀ {Δ' : Ctxt jasminDialect} (ren' : Ctxt.Hom Δ Δ') (res : Var Δ' a)
        (q' : NFProg jasminDialect Δ' ts), K ren' res = some q' → ChainTailAt res q') →
      (∀ {Δ' : Ctxt jasminDialect} (ren' : Ctxt.Hom Δ Δ') (res : Var Δ' a)
        (q' : NFProg jasminDialect Δ' ts), K ren' res = some q' → LoadsChain q') →
      ∀ {q : NFProg jasminDialect Δ ts}, NFProg.spliceNF? blk K = some q → LoadsChain q
  | _, _, .ret v, K, _, _, hK', _, hq => hK' _ v _ hq
  | _, _, .var e blk, K, h, hK, hK', _, hq => by
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
      change LoadsChain (.var e (NFProg.ofCom blk)) at h
      have ih := fun h' => loadsChain_spliceNF?_ofCom blk _ h'
        (fun ren' res q'' hq'' => hK _ res q'' hq'') (fun ren' res q'' hq'' => hK' _ res q'' hq'')
        hq'
      cases h with
      | free _ _ he hb => exact .free _ _ he (ih hb)
      | load a i _ hb => exact .load _ _ _ (ih hb)
      | store v i x _ hb =>
          have h2 : ChainTail .here q' := chainTail_spliceNF?_ofCom blk _ .here hb
            (fun ren' res q'' hq'' => hK _ res q'' hq'') hq'
          exact .store _ _ _ _ h2

/-! ## 2. The blocks of the wide template -/

section Template

open CatCrypt.Crypto.SecureCompilation.Algebraic (ModArithLimbTemplate)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldWideInline (WideTemplate wideTemplateOf)
open CatCrypt.Crypto.SecureCompilation.Haxc.ModArithLimbs (canonTemplateOf ofWide optTy
  ofWordsBlock? toWordsBlock? bodyBlock?)
open _root_.Hax.FieldTag (fieldLimbs)

/-- **The limb template at a modulus without a narrow representation and with a wide
    template** is the template of the wide template. -/
theorem canonTemplateOf_wide {p : Nat} {W : WideTemplate p (fieldLimbs p)}
    (hn : narrowFieldOf p = none) (hw : wideTemplateOf p = some W) :
    canonTemplateOf p = some (ofWide W hw) := by
  unfold canonTemplateOf
  split
  · rename_i F hF
    rw [hn] at hF
    cases hF
  · split
    · rename_i W' hW'
      obtain rfl := Option.some.inj (hW'.symm.trans hw)
      rfl
    · rename_i hW'
      rw [hw] at hW'
      cases hW'

/-- **The cast block from words of the wide template is a return**, of no binding. -/
theorem ofWordsBlock?_wide_comFree {p : Nat} {W : WideTemplate p (fieldLimbs p)}
    {hw : wideTemplateOf p = some W} {Δ : Ctxt jasminDialect}
    (o : Option (ModArithLimbTemplate p .canon))
    (ho : o = some (ofWide W hw)) (w n : Nat) (a : Var Δ (.stackArr w n))
    {blk : Com jasminDialect Δ (optTy o)} (hb : ofWordsBlock? o w n a = some blk) :
    ComFree blk := by
  subst ho
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hb
  change ModArithLimbs.arrOfWords (fieldLimbs p) w n = some c at hc
  unfold ModArithLimbs.arrOfWords at hc
  split at hc
  · rename_i h
    cases hc
    injection h with h1 h2
    subst h1 h2
    exact comFree_rename (.ret _) _
  · cases hc

/-- **The cast block to words of the wide template returns its argument.** -/
theorem toWordsBlock?_wide_ret {p : Nat} {W : WideTemplate p (fieldLimbs p)}
    {hw : wideTemplateOf p = some W} {Δ : Ctxt jasminDialect}
    (o : Option (ModArithLimbTemplate p .canon))
    (ho : o = some (ofWide W hw)) (w n : Nat) (a : Var Δ (optTy o))
    {blk : Com jasminDialect Δ (.stackArr w n)} (hb : toWordsBlock? o w n a = some blk) :
    ∃ h : optTy o = .stackArr w n, blk = .ret (h ▸ a) := by
  subst ho
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hb
  change ModArithLimbs.arrToWords (fieldLimbs p) w n = some c at hc
  unfold ModArithLimbs.arrToWords at hc
  split at hc
  · rename_i h
    cases hc
    injection h with h1 h2
    subst h1 h2
    exact ⟨rfl, rfl⟩
  · cases hc

/-- **The block of a method of the wide template has the shape `LoadsChain`.** -/
theorem bodyBlock?_wide_loadsChain {p : Nat} {W : WideTemplate p (fieldLimbs p)}
    {hw : wideTemplateOf p = some W} {Δ : Ctxt jasminDialect}
    (o : Option (ModArithLimbTemplate p .canon)) (ho : o = some (ofWide W hw))
    (m : _root_.Hax.FieldTag.FieldMethod)
    (args : HVector (fun t => Var Δ t)
      (Algebraic.ModArithLimbTemplate.limbSig (ModArithLimbs.optTy o) m))
    {blk : Com jasminDialect Δ (optTy o)} (hb : bodyBlock? o m args = some blk) :
    LoadsChain (NFProg.ofCom blk) := by
  subst ho
  cases hb
  refine loadsChain_ofCom_rename (ModArithLimbs.wideLimbBody W m) _ ?_
  rw [← ModArithLimbs.wideBlockOf_eq]
  exact wideBlockOf_loadsChain hw m

end Template


/-! ## 3. The lowered bodies of the wide template -/

section Lowered

open CatCrypt.Crypto.SecureCompilation.Haxc.FieldWideInline (WideTemplate wideTemplateOf)
open _root_.Hax.FieldTag (fieldLimbs)

/-- A renaming commutes with the transport of a variable along an equality of types. -/
theorem hom_cast {Γ Δ : Ctxt jasminDialect} (f : Ctxt.Hom Γ Δ) {A B : JasminTy} (h : A = B)
    (v : Var Γ A) : f (h ▸ v) = h ▸ f v := by
  subst h
  rfl

/-- The return of a transport of `res` continues the chain at `res`. -/
theorem chainTailAt_ret {Γ : Ctxt jasminDialect} {a : JasminTy} {w m : Nat} (res : Var Γ a)
    (x : Var Γ (.stackArr w m)) (h : a = .stackArr w m) (hx : x = h ▸ res) :
    ChainTailAt res (.ret (.cons x .nil)) := by
  intro w' m' h'
  obtain ⟨rfl, rfl⟩ : w = w' ∧ m = m' := by
    have := h.symm.trans h'
    injection this with h1 h2
    exact ⟨h1, h2⟩
  subst hx
  exact .ret _

set_option hygiene false in
/-- The splice of a cast block from words of the wide template. -/
local macro "cast_in_tac" : tactic => `(tactic| (
  obtain ⟨b, hb, hq'⟩ := Option.bind_eq_some_iff.mp hq'
  refine loadsChain_spliceNF? _ _ (comFree_rename (ofWordsBlock?_wide_comFree _ hc _ _ _ hb) _)
    (fun ren' res q' hq' => ?_) hq'))

set_option hygiene false in
/-- The splice of the block of a method of the wide template before the cast to words and the
    return. -/
local macro "op_tail_tac" : tactic => `(tactic| (
  obtain ⟨b, hb, hq'⟩ := Option.bind_eq_some_iff.mp hq'
  have h3 : LoadsChain (NFProg.ofCom b) := by
    simp only [ModArithLimbs.modArithLimbsJ, ModArithLimbs.limbLowerBlock?, Expr.rename,
      ModArithLimbs.limbOpBlock?, ModArithLimbs.modBlock?] at hb
    first
      | exact bodyBlock?_wide_loadsChain _ hc _ _ hb
      | (split at hb <;> exact bodyBlock?_wide_loadsChain _ hc _ _ hb)
  refine loadsChain_spliceNF?_ofCom _ _ (loadsChain_ofCom_rename _ _ h3)
    (fun ren' res q' hq' => ?_) (fun ren' res q' hq' => ?_) hq'
  all_goals
    obtain ⟨b4, hb4, hq'⟩ := Option.bind_eq_some_iff.mp hq'
    simp only [ModArithLimbs.modArithLimbsJ, ModArithLimbs.limbLowerBlock?, Expr.rename,
      ModArithLimbs.limbOpBlock?, ModArithLimbs.limbCastBlock?] at hb4
    obtain ⟨h4, rfl⟩ := toWordsBlock?_wide_ret _ hc _ _ _ hb4
    simp only [Com.rename, NFProg.spliceNF?, Option.some.injEq] at hq'
    subst hq'
  · exact chainTailAt_ret res _ h4 (hom_cast (ModArithLimbs.modArithLimbsJ.bodyHom _ _ res) h4 _)
  · exact .ret _))

/-- **The raised body on arrays, lowered to `mod_arith` and to the wide template, has the shape
    `LoadsChain`**: the casts from words are returns of their arguments, the method is the
    template block, whose last store version the cast to words returns. -/
theorem lowerArr_loadsChain {p : Nat} {W : WideTemplate p (fieldLimbs p)}
    (hn : narrowFieldOf p = none) (hw : wideTemplateOf p = some W)
    (m : _root_.Hax.FieldTag.FieldMethod) {r₂ r₃}
    (h : NFProg.map? FieldToModArithChain.fieldToModArithJ FieldToModArithChain.regionTypes
      (FieldRaise.arrBody m p (fieldLimbs p)) (fun v => v) = some r₂)
    (h₃ : NFProg.map? ModArithLimbs.modArithLimbsJ ModArithLimbs.modArithLimbsJ_regionTypes r₂
      (fun v => v) = some r₃) : LoadsChain r₃ := by
  have hc := canonTemplateOf_wide hn hw
  cases m <;>
  simp only [NFProg.map?, FieldRaise.arrBody, FieldRaise.arrBody2, FieldRaise.arrBody1,
    FieldToModArithChain.fieldToModArithJ,
    FieldToModArithChain.lowerBlock?, FieldToModArithChain.opBlock?, FieldRaise.fromE,
    FieldRaise.toE, FieldRaise.opE, FieldToModArithChain.castBlock?, FieldToModArithChain.pfBlock?,
    FieldChainDialect.FieldRepr.Admits, ↓reduceIte, Option.bind_some, FieldToModArithChain.opB,
    Com.rename, NFProg.spliceNF?, Option.map_some] at h <;>
  obtain rfl := Option.some.inj h <;>
  have hq' := h₃ <;>
  simp only [NFProg.map?] at hq'
  · cast_in_tac; cast_in_tac; op_tail_tac
  · cast_in_tac; cast_in_tac; op_tail_tac
  · cast_in_tac; cast_in_tac; op_tail_tac
  · cast_in_tac; op_tail_tac
  · cast_in_tac; op_tail_tac
  · cast_in_tac; op_tail_tac

/-- **The lowered body of a tagged head at a modulus without a narrow representation and with
    a wide template has the shape `LoadsChain`.** -/
theorem fieldBodyD_loadsChain {f : String} {m : _root_.Hax.FieldTag.FieldMethod} {p : Nat}
    {W : WideTemplate p (fieldLimbs p)} (ht : _root_.Hax.FieldTag.fieldTag? f = some (m, p))
    (hn : narrowFieldOf p = none) (hw : wideTemplateOf p = some W) {as rs : List JasminTy}
    {b : NFProg jasminDialect as rs} (hb : FieldDialectStep.fieldBodyD f as rs = some b) :
    LoadsChain b := by
  obtain ⟨-, r₁, hr₁, hb⟩ := FieldDialectStep.fieldBodyD_some hb
  unfold FieldRaise.raiseBody at hr₁
  rw [ht] at hr₁
  simp only [hn, hw] at hr₁
  unfold FieldRaise.raiseArr at hr₁
  split at hr₁
  · rename_i hs
    obtain ⟨has, hrs⟩ := hs
    obtain rfl := List.map_injective_iff.mpr Sum.inl_injective has
    obtain rfl : rs = [JasminTy.stackArr 64 (fieldLimbs p)] :=
      List.map_injective_iff.mpr Sum.inl_injective (hrs.trans rfl)
    cases hr₁
    obtain ⟨s₂, hs₂, hf⟩ := Option.bind_eq_some_iff.mp hb
    obtain ⟨s₃, hs₃, rfl⟩ := Option.map_eq_some_iff.mp hf
    exact loadsChain_lowerBodyTail _ _ (lowerArr_loadsChain hn hw m hs₂ hs₃)
  · cases hr₁

end Lowered

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
