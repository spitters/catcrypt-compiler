/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakFactoring

/-!
# The dialect leak prefix of a lowered LowCT command, as a function of the source

`ComCont.LeakFactorsTrace f pre` (`CryptoDialectLeakFactoring`) states that the
front prefix `f` prepends the event list `pre` to every dialect tail it accepts.
The front-level theorems there give `pre` existentially. This module computes
it: `expand τ c` maps a source command `c` and a typing `τ` of the names in
scope to the event list the front's prefix prepends and the typing after `c`,
and `translateDialectFull_leakTrace_expand` proves that the prefix
`translateDialectFull` emits prepends exactly that list. The dialect leak trace
of the lowered program is therefore a function of the source command and the
entry typing, independent of the variable map's De Bruijn layout and of the
tail.

The typing enters because the front chooses its lowering by the types of the
operands: a word select (`RSelect` over three `.sword 64` slots) lowers to the
three-op comparison select `selectCmpCont`, a select over any other slots to one
opaque `extCall "select"`; a dynamic array load (`RArrLoad`) lowers to
`memrefGetDyn` when the array is a `memref` and the index a word, and to
`extCall "arrLoadDyn"` otherwise. The scalar assignment `RScalarSetExpr x e`
lowers to one op per node of `e` (`sexprLeak e`) followed by the copy into `x`,
and binds one fresh temporary per node (`Typing.updTemps`).

The LowCT structural trace `LowCTLeakTrace.LowCT.leakTrace` is not the domain of
such an expansion: it records `[]` for every `RScalarSetExpr`, so two scalar
assignments with different expressions share the LowCT trace while their
dialect prefixes differ.

## Main results

* `sexprLeak`, `lowerSExpr_leakTrace_expand` — the events of a lowered scalar
  expression, one per node, with the counter advance and the typing of the
  temporaries.
* `selectCmpLeak`, `selectCmpCont_leakFactorsTrace_eq` — the three events of
  the comparison select the `RSelect` arm emits.
* `selectMaskLeak`, `selectMaskCont_leakFactorsTrace_eq` — the eight events of
  the mask chain `selectMaskCont`.
* `arrLoadLeakTy`, `arrLoadCont_leakFactorsTrace_eq` — the one event of a
  dynamic array load, by the operand types.
* `expand`, `translateDialectFull_leakTrace_expand` — the compositional
  expansion over `RSkip`, `RAssert`, `RBlock`, `RSeq`, `RScalarSet`,
  `RLetU64Zero`, `RCall`, `RSelect`, `RArrLoad` and `RScalarSetExpr`, and the
  theorem that the front's prefix prepends exactly `expand`'s list; `expand` is
  `none` on the other constructors.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakExpansion

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA (VarMap encodeTy resolveLocatedArgs)
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakTrace
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakFactoring
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.Jasmin.LowCT (LowCT Located TowerType SExpr)

/-! ## 1. Typings -/

/-- A typing of the source names in scope: the `CryptoTy` a name is bound at,
    or `none` for an unbound name. -/
abbrev Typing := String → Option CryptoTy

/-- The typing a `VarMap` induces: the type component of each lookup. -/
def VarMap.tyOf {Γ : Ctx} (vm : VarMap Γ) : Typing :=
  fun y => (vm.lookup y).map Sigma.fst

/-- The typing after binding `x` at `t`. -/
def Typing.upd (τ : Typing) (x : String) (t : CryptoTy) : Typing :=
  fun y => if y = x then some t else τ y

theorem VarMap.tyOf_weaken {Γ : Ctx} {t : CryptoTy} (vm : VarMap Γ) :
    VarMap.tyOf (vm.weaken (t := t)) = VarMap.tyOf vm := by
  funext y
  simp only [VarMap.tyOf, VarMap.weaken]
  rcases vm.lookup y with _ | ⟨t', v⟩ <;> rfl

theorem VarMap.tyOf_bind {Γ : Ctx} {t : CryptoTy} (vm : VarMap Γ) (x : String) :
    VarMap.tyOf (vm.bind (t := t) x) = (VarMap.tyOf vm).upd x t := by
  funext y
  simp only [VarMap.tyOf, VarMap.bind, Typing.upd]
  by_cases hy : y = x
  · simp [hy]
  · simp only [hy, if_false]
    rcases vm.lookup y with _ | ⟨t', v⟩ <;> rfl

/-- The typing after the `n` fresh temporaries `tmpName lo, …, tmpName (lo + n - 1)`
    of a scalar-expression lowering, each bound at `.sword 64`. -/
def Typing.updTemps (τ : Typing) (lo : Nat) : Nat → Typing
  | 0 => τ
  | n + 1 => (Typing.updTemps τ lo n).upd (tmpName (lo + n)) (.sword 64)

theorem Typing.updTemps_comp (τ : Typing) (lo m n : Nat) :
    Typing.updTemps (Typing.updTemps τ lo m) (lo + m) n = Typing.updTemps τ lo (m + n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Typing.updTemps, ih, Nat.add_assoc]; rfl

/-! ## 2. Scalar expressions -/

/-- The event of a shift node: a literal count lowers to the immediate shift
    (`bvShiftL`/`bvShiftR`), a runtime count to the variable one
    (`bvShiftLV`/`bvShiftRV`). -/
def shiftEvent (left : Bool) : SExpr → LeakEvent
  | .SLit _ => .pureOp (if left then "bvShiftL" else "bvShiftR")
  | _ => .pureOp (if left then "bvShiftLV" else "bvShiftRV")

/-- The dialect events `lowerSExpr` emits for a scalar expression: one per node
    that binds a temporary, in evaluation order (left operand, right operand,
    the node's op). A variable read binds nothing; the arms `lowerSExpr` declines
    contribute nothing. -/
def sexprLeak : SExpr → LeakTrace
  | .SVar _ => []
  | .SLit _ => [.pureOp "bvConst"]
  | .SAdd a b => sexprLeak a ++ sexprLeak b ++ [.pureOp "bvAdd"]
  | .SSub a b => sexprLeak a ++ sexprLeak b ++ [.pureOp "bvSub"]
  | .SMul a b => sexprLeak a ++ sexprLeak b ++ [.pureOp "bvMul"]
  | .SAnd a b => sexprLeak a ++ sexprLeak b ++ [.pureOp "bvAnd"]
  | .SXor a b => sexprLeak a ++ sexprLeak b ++ [.pureOp "bvXor"]
  | .SShl a b => sexprLeak a ++ sexprLeak b ++ [shiftEvent true b]
  | .SShr a b => sexprLeak a ++ sexprLeak b ++ [shiftEvent false b]
  | .SMulHiU a b => sexprLeak a ++ sexprLeak b ++ [.pureOp "bvMulHi"]
  | _ => []

set_option hygiene false in
/-- The two-chain arms of `lowerSExpr` (`SAdd`, `SSub`, `SMul`, `SAnd`, `SXor`,
    `SShl`, `SShr`, `SMulHiU`): both operand chains, then one binding node. -/
local macro "sexpr_binary_case" h:ident iha:ident ihb:ident : tactic =>
  `(tactic| (
      simp only [lowerSExpr] at $h:ident
      split at $h:ident
      · exact absurd $h (by simp)
      · next r heqA =>
          obtain ⟨oa, na, cnt1⟩ := r
          split at $h:ident
          · exact absurd $h (by simp)
          · next s heqB =>
              obtain ⟨ob, nb, cnt2⟩ := s
              split at $h:ident <;> first
                | (simp only [Option.some.injEq, Prod.mk.injEq] at $h:ident
                   obtain ⟨ho, _, hc⟩ := $h:ident
                   subst ho
                   obtain ⟨pa, ca, ta⟩ := $iha _ _ heqA
                   obtain ⟨pb, cb, tb⟩ := $ihb _ _ heqB
                   subst ca; subst cb; subst hc
                   refine ⟨?_, ?_, ?_⟩
                   · first
                     | exact pushVarBind_leakFactorsTrace _ _ (seqOut_leakFactorsTrace pa pb)
                     | (cases b <;>
                          exact pushVarBind_leakFactorsTrace _ _ (seqOut_leakFactorsTrace pa pb))
                   · simp only [sexprLeak, List.length_append, List.length_singleton]; omega
                   · show VarMap.tyOf (ob.vm.bind _) = _
                     rw [VarMap.tyOf_bind, tb, ta, Typing.updTemps_comp]
                     simp only [sexprLeak, List.length_append, List.length_singleton,
                       Typing.updTemps, Nat.add_assoc]
                     try rfl)
                | exact absurd $h (by simp)))

/-- **The events of a lowered scalar expression.** When `lowerSExpr vm cnt e`
    succeeds, its prefix prepends `sexprLeak e`, the counter advances by one per
    event, and the map's typing gains the temporaries `tmpName cnt, …` at
    `.sword 64`. -/
theorem lowerSExpr_leakTrace_expand {Γ : Ctx} (vm : VarMap Γ) (cnt : Nat) (e : SExpr)
    {o : DTransOut Γ} {nm : String} {cnt' : Nat}
    (h : lowerSExpr vm cnt e = some (o, nm, cnt')) :
    ComCont.LeakFactorsTrace o.cont (sexprLeak e)
      ∧ cnt' = cnt + (sexprLeak e).length
      ∧ VarMap.tyOf o.vm = (VarMap.tyOf vm).updTemps cnt (sexprLeak e).length := by
  induction e generalizing Γ vm cnt o nm cnt' with
  | SVar x =>
      simp only [lowerSExpr] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨ho, _, hc⟩ := h; subst ho; subst hc
        exact ⟨ComCont.id_leakFactorsTrace, rfl, rfl⟩
      · exact absurd h (by simp)
  | SLit n =>
      simp only [lowerSExpr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨ho, _, hc⟩ := h; subst ho; subst hc
      refine ⟨pushVarBind_leakFactorsTrace (o := ⟨Γ, ComCont.id, vm⟩) _ (tmpName cnt)
        ComCont.id_leakFactorsTrace, rfl, ?_⟩
      show VarMap.tyOf (VarMap.bind _ _) = _
      rw [VarMap.tyOf_bind]; rfl
  | SAdd a b iha ihb => sexpr_binary_case h iha ihb
  | SSub a b iha ihb => sexpr_binary_case h iha ihb
  | SMul a b iha ihb => sexpr_binary_case h iha ihb
  | SAnd a b iha ihb => sexpr_binary_case h iha ihb
  | SXor a b iha ihb => sexpr_binary_case h iha ihb
  | SShl a b iha ihb => sexpr_binary_case h iha ihb
  | SShr a b iha ihb => sexpr_binary_case h iha ihb
  | SMulHiU a b iha ihb => sexpr_binary_case h iha ihb
  | SLt _ _ _ _ => simp only [lowerSExpr] at h; exact absurd h (by simp)
  | SAsr _ _ _ _ => simp only [lowerSExpr] at h; exact absurd h (by simp)
  | SMulS _ _ _ _ => simp only [lowerSExpr] at h; exact absurd h (by simp)
  | SMulHiS _ _ _ _ => simp only [lowerSExpr] at h; exact absurd h (by simp)
  | SLimb _ _ => simp only [lowerSExpr] at h; exact absurd h (by simp)

/-! ## 3. The word select -/

/-- The three events of the comparison select `selectCmpCont`: the zero
    constant, the equality comparison and the conditional select. -/
def selectCmpLeak : LeakTrace :=
  [.pureOp "bvConst", .pureOp "bvEq", .pureOp "ite"]

/-- **The comparison-select prefix prepends `selectCmpLeak`.** -/
theorem selectCmpCont_leakFactorsTrace_eq {Γ : Ctx} (sV aV cV : CVar Γ (.sword 64)) :
    ComCont.LeakFactorsTrace (selectCmpCont sV aV cV) selectCmpLeak := by
  unfold selectCmpCont
  exact ComCont.comp_leakFactorsTrace (ComCont.varBind_leakFactorsTrace _)
    (ComCont.comp_leakFactorsTrace (ComCont.varBind_leakFactorsTrace _)
      (ComCont.varBind_leakFactorsTrace _))

/-- The eight events of the word-select mask chain `selectMaskCont`: the zero
    constant, the negated selector, the or, the sign shift, the mask, the xor of
    the sources, the masked xor and the final xor. -/
def selectMaskLeak : LeakTrace :=
  [.pureOp "bvConst", .pureOp "bvSub", .pureOp "bvOr", .pureOp "bvShiftR",
   .pureOp "bvSub", .pureOp "bvXor", .pureOp "bvAnd", .pureOp "bvXor"]

/-- **The word-select prefix prepends `selectMaskLeak`.** -/
theorem selectMaskCont_leakFactorsTrace_eq {Γ : Ctx} (sV aV cV : CVar Γ (.sword 64)) :
    ComCont.LeakFactorsTrace (selectMaskCont sV aV cV) selectMaskLeak := by
  unfold selectMaskCont
  exact ComCont.comp_leakFactorsTrace (ComCont.varBind_leakFactorsTrace _)
    (ComCont.comp_leakFactorsTrace (ComCont.varBind_leakFactorsTrace _)
      (ComCont.comp_leakFactorsTrace (ComCont.varBind_leakFactorsTrace _)
        (ComCont.comp_leakFactorsTrace (ComCont.varBind_leakFactorsTrace _)
          (ComCont.comp_leakFactorsTrace (ComCont.varBind_leakFactorsTrace _)
            (ComCont.comp_leakFactorsTrace (ComCont.varBind_leakFactorsTrace _)
              (ComCont.comp_leakFactorsTrace (ComCont.varBind_leakFactorsTrace _)
                (ComCont.varBind_leakFactorsTrace _)))))))

/-! ## 4. The dynamic array load -/

/-- Is the type a `memref`? -/
def CryptoTy.isMemref : CryptoTy → Bool
  | .memref _ => true
  | _ => false

/-- The event of a dynamic array load by the destination's declared type and the
    types of the array and index operands: `memrefGetDyn` for a `u64` load from
    a `memref` at a word index, the opaque `extCall "arrLoadDyn"` otherwise. -/
def arrLoadLeakTy (dty : TowerType) (srcTy idxTy : Option CryptoTy) : LeakTrace :=
  if dty = .TU64 ∧ srcTy.any CryptoTy.isMemref ∧ idxTy = some (.sword 64) then
    [.pureOp "memrefGetDyn"]
  else [.pureOp "extCall:arrLoadDyn"]

set_option backward.isDefEq.respectTransparency.types false in
/-- Outside the `u64`-from-`memref`-at-word shape, the `RArrLoad` prefix is the
    opaque `extCall "arrLoadDyn"` binding and prepends its one event. -/
theorem arrLoadCont_fallback {Γ : Ctx} (dty : TowerType)
    (resolvedArgs : List ((t : CryptoTy) × CVar Γ t)) (idxSig : (t : CryptoTy) × CVar Γ t)
    {argTys : List CryptoTy} (hv : CHVector (fun t => CVar Γ t) argTys)
    (h : ¬ (dty = .TU64 ∧ ∃ (n : Nat) (arrV : CVar Γ (.memref n)) (idxV : CVar Γ (.sword 64)),
      resolvedArgs = [⟨.memref n, arrV⟩] ∧ idxSig = ⟨.sword 64, idxV⟩)) :
    ComCont.LeakFactorsTrace (arrLoadCont dty resolvedArgs idxSig hv)
      [.pureOp "extCall:arrLoadDyn"] := by
  unfold arrLoadCont
  split
  · next n arrV idxV => exact absurd ⟨rfl, n, arrV, idxV, rfl, rfl⟩ h
  · exact ComCont.varBind_leakFactorsTrace _

/-- **The `RArrLoad` prefix prepends `arrLoadLeakTy`** at the resolved operand
    types. -/
theorem arrLoadCont_leakFactorsTrace_eq {Γ : Ctx} (dty : TowerType)
    {t : CryptoTy} (v : CVar Γ t) {ti : CryptoTy} (vi : CVar Γ ti)
    {argTys : List CryptoTy} (hv : CHVector (fun t => CVar Γ t) argTys) :
    ComCont.LeakFactorsTrace (arrLoadCont dty [⟨t, v⟩] ⟨ti, vi⟩ hv)
      (arrLoadLeakTy dty (some t) (some ti)) := by
  unfold arrLoadLeakTy
  split
  · next hc =>
      obtain ⟨hd, hs, hi⟩ := hc
      subst hd
      simp only [Option.some.injEq] at hi
      subst hi
      cases t with
      | memref n => exact ComCont.varBind_leakFactorsTrace _
      | _ => simp [CryptoTy.isMemref] at hs
  · next hc =>
      refine arrLoadCont_fallback dty _ _ hv ?_
      rintro ⟨hd, n, arrV, idxV, hs, hi⟩
      simp only [List.cons.injEq, Sigma.mk.injEq, and_true] at hs
      obtain ⟨hs, _⟩ := hs
      simp only [Sigma.mk.injEq] at hi
      obtain ⟨hi, _⟩ := hi
      subst hs; subst hi
      exact hc ⟨hd, rfl, rfl⟩

/-! ## 5. The compositional expansion -/

/-- The dialect events the front prepends for a source command, with the
    typing after it, as a function of the command and the entry typing `τ`.
    `none` on the constructors this expansion does not cover. -/
def expand (τ : Typing) : LowCT → Option (LeakTrace × Typing)
  | .RSkip => some ([], τ)
  | .RAssert _ => some ([], τ)
  | .RBlock body => expand τ body
  | .RSeq c₁ c₂ =>
      match expand τ c₁ with
      | some (p₁, τ₁) =>
          match expand τ₁ c₂ with
          | some (p₂, τ₂) => some (p₁ ++ p₂, τ₂)
          | none => none
      | none => none
  | .RScalarSet x _ => some ([.pureOp "bvConst"], τ.upd x (.sword 64))
  | .RLetU64Zero x body =>
      match expand (τ.upd x (.sword 64)) body with
      | some (p, τ') => some (.pureOp "bvConst" :: p, τ')
      | none => none
  | .RCall f dest _ =>
      some ([.pureOp ("extCall:" ++ f)], τ.upd dest.locVar (encodeTy dest.locDst))
  | .RSelect dst sel src0 src1 =>
      if dst.locDst = .TU64 ∧ τ sel = some (.sword 64) ∧ τ src0.locVar = some (.sword 64)
          ∧ τ src1.locVar = some (.sword 64) then
        some (selectCmpLeak, τ.upd dst.locVar (encodeTy dst.locDst))
      else
        some ([.pureOp "extCall:select"], τ.upd dst.locVar (encodeTy dst.locDst))
  | .RArrLoad dst src idxVar =>
      some (arrLoadLeakTy dst.locDst (τ src.locVar) (τ idxVar),
        τ.upd dst.locVar (encodeTy dst.locDst))
  | .RScalarSetExpr x e =>
      some (sexprLeak e ++ [.pureOp "bvShiftL"],
        (τ.updTemps 0 (sexprLeak e).length).upd x (.sword 64))
  | .RLimbStore loc idx _ =>
      match τ loc.locVar with
      | some (.memref n) =>
          if idx < n then
            some ([.pureOp "bvConst", .pureOp "memrefSet"], τ.upd loc.locVar (.memref n))
          else none
      | none =>
          match encodeTy loc.locDst with
          | .memref n =>
              if idx < n then
                some ([.pureOp "bvConst", .pureOp ("extCall:" ++ limbLitLeafName idx)],
                  τ.upd loc.locVar (.memref n))
              else none
          | _ => none
      | some _ => none
  | _ => none

/-- **The front's prefix prepends `expand`'s event list.** For every command on
    which `expand` is defined at the map's typing, a successful
    `translateDialectFull vm c` emits a prefix that prepends exactly that list to
    any tail, and its map's typing is the one `expand` computes. -/
theorem translateDialectFull_leakTrace_expand {Γ : Ctx} (vm : VarMap Γ) (c : LowCT)
    {pre : LeakTrace} {τ' : Typing} {o : DTransOut Γ}
    (he : expand (VarMap.tyOf vm) c = some (pre, τ'))
    (h : translateDialectFull vm c = some o) :
    ComCont.LeakFactorsTrace o.cont pre ∧ VarMap.tyOf o.vm = τ' := by
  induction c generalizing Γ vm pre τ' o with
  | RSkip =>
      simp only [expand, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      simp only [translateDialectFull, translateDialect, Option.some.injEq] at h
      subst h
      exact ⟨ComCont.id_leakFactorsTrace, rfl⟩
  | RAssert _ =>
      simp only [expand, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      simp only [translateDialectFull, Option.some.injEq] at h
      subst h
      exact ⟨ComCont.id_leakFactorsTrace, rfl⟩
  | RBlock body ih =>
      exact ih vm he h
  | RSeq c₁ c₂ ih₁ ih₂ =>
      simp only [expand] at he
      split at he
      · next p₁ τ₁ he₁ =>
          split at he
          · next p₂ τ₂ he₂ =>
              simp only [Option.some.injEq, Prod.mk.injEq] at he
              obtain ⟨rfl, rfl⟩ := he
              simp only [translateDialectFull] at h
              split at h
              · next o₁ h₁ =>
                  split at h
                  · next o₂ h₂ =>
                      simp only [Option.some.injEq] at h
                      subst h
                      obtain ⟨t₁, ty₁⟩ := ih₁ vm he₁ h₁
                      obtain ⟨t₂, ty₂⟩ := ih₂ o₁.vm (by rw [ty₁]; exact he₂) h₂
                      exact ⟨ComCont.comp_leakFactorsTrace t₁ t₂, ty₂⟩
                  · exact absurd h (by simp)
              · exact absurd h (by simp)
          · exact absurd he (by simp)
      · exact absurd he (by simp)
  | RScalarSet x n =>
      simp only [expand, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      simp only [translateDialectFull, translateDialect, Option.some.injEq] at h
      subst h
      exact ⟨ComCont.varBind_leakFactorsTrace _, VarMap.tyOf_bind _ _⟩
  | RLetU64Zero x body ih =>
      simp only [expand] at he
      split at he
      · next p τ₁ he' =>
          simp only [Option.some.injEq, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          simp only [translateDialectFull] at h
          split at h
          · next o₁ h₁ =>
              simp only [Option.some.injEq] at h
              subst h
              obtain ⟨t₁, ty₁⟩ := ih (vm.bind x) (by rw [VarMap.tyOf_bind]; exact he') h₁
              exact ⟨ComCont.comp_leakFactorsTrace (ComCont.varBind_leakFactorsTrace _) t₁, ty₁⟩
          · exact absurd h (by simp)
      · exact absurd he (by simp)
  | RCall f dest args =>
      simp only [expand, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      simp only [translateDialectFull] at h
      split at h
      · exact absurd h (by simp)
      · next resolvedArgs _ =>
          simp only [Option.some.injEq] at h
          subst h
          exact ⟨ComCont.varBind_leakFactorsTrace _, VarMap.tyOf_bind _ _⟩
  | RSelect dst sel src0 src1 =>
      simp only [translateDialectFull] at h
      split at h
      · next sV aV cV hd hsel hs0 hs1 =>
          simp only [Option.some.injEq] at h
          subst h
          have hc : dst.locDst = .TU64 ∧ VarMap.tyOf vm sel = some (.sword 64)
              ∧ VarMap.tyOf vm src0.locVar = some (.sword 64)
              ∧ VarMap.tyOf vm src1.locVar = some (.sword 64) :=
            ⟨hd, by simp [VarMap.tyOf, hsel], by simp [VarMap.tyOf, hs0],
              by simp [VarMap.tyOf, hs1]⟩
          simp only [expand, if_pos hc, Option.some.injEq, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          refine ⟨selectCmpCont_leakFactorsTrace_eq sV aV cV, ?_⟩
          show VarMap.tyOf (VarMap.bind _ _) = _
          rw [VarMap.tyOf_bind, VarMap.tyOf_weaken, VarMap.tyOf_weaken, hd]
          rfl
      · next hne =>
          have hc : ¬ (dst.locDst = .TU64 ∧ VarMap.tyOf vm sel = some (.sword 64)
              ∧ VarMap.tyOf vm src0.locVar = some (.sword 64)
              ∧ VarMap.tyOf vm src1.locVar = some (.sword 64)) := by
            rintro ⟨hd, hsel, hs0, hs1⟩
            simp only [VarMap.tyOf, Option.map_eq_some_iff] at hsel hs0 hs1
            obtain ⟨⟨tS, sV⟩, hsel, hS⟩ := hsel
            obtain ⟨⟨t0, aV⟩, hs0, h0⟩ := hs0
            obtain ⟨⟨t1, cV⟩, hs1, h1⟩ := hs1
            cases hS; cases h0; cases h1
            exact hne sV aV cV hd hsel hs0 hs1
          simp only [expand, if_neg hc] at he
          split at h
          · exact absurd h (by simp)
          · next resolvedArgs _ =>
              simp only [Option.some.injEq] at h
              subst h
              simp only [Option.some.injEq, Prod.mk.injEq] at he
              obtain ⟨rfl, rfl⟩ := he
              exact ⟨ComCont.varBind_leakFactorsTrace _, VarMap.tyOf_bind _ _⟩
  | RArrLoad dst src idxVar =>
      simp only [expand, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      simp only [translateDialectFull] at h
      split at h
      · next resolvedArgs idxSig hres hidx =>
          simp only [Option.some.injEq] at h
          subst h
          simp only [resolveLocatedArgs] at hres
          split at hres
          · next r rs hsrc hrs =>
              simp only [Option.some.injEq] at hres
              subst hres
              simp only [Option.some.injEq] at hrs
              subst hrs
              obtain ⟨t, v⟩ := r
              obtain ⟨ti, vi⟩ := idxSig
              refine ⟨?_, VarMap.tyOf_bind _ _⟩
              have hsrcTy : VarMap.tyOf vm src.locVar = some t := by simp [VarMap.tyOf, hsrc]
              have hidxTy : VarMap.tyOf vm idxVar = some ti := by simp [VarMap.tyOf, hidx]
              rw [hsrcTy, hidxTy]
              show ComCont.LeakFactorsTrace (arrLoadCont dst.locDst [⟨t, v⟩] ⟨ti, vi⟩ _) _
              exact arrLoadCont_leakFactorsTrace_eq dst.locDst v vi _
          · exact absurd hres (by simp)
      · exact absurd h (by simp)
  | RScalarSetExpr x e =>
      simp only [expand, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      simp only [translateDialectFull] at h
      split at h
      · exact absurd h (by simp)
      · next r hr =>
          obtain ⟨o₁, nm, cnt'⟩ := r
          split at h
          · next v _ =>
              simp only [Option.some.injEq] at h
              subst h
              obtain ⟨t₁, _, ty₁⟩ := lowerSExpr_leakTrace_expand vm 0 e hr
              refine ⟨pushVarBind_leakFactorsTrace _ _ t₁, ?_⟩
              show VarMap.tyOf (VarMap.bind _ _) = _
              rw [VarMap.tyOf_bind, ty₁]
          · exact absurd h (by simp)
  | RLimbStore loc idx v =>
      simp only [expand] at he
      simp only [translateDialectFull] at h
      rcases hlk : vm.lookup loc.locVar with _ | ⟨mt, arr⟩
      · have hty : VarMap.tyOf vm loc.locVar = none := by simp [VarMap.tyOf, hlk]
        rw [hlk] at h
        rw [hty] at he
        dsimp only at h he
        rcases hen : encodeTy loc.locDst with _ | _ | _ | _ | _ | n
        all_goals (rw [hen] at h he; dsimp only at h he)
        case memrefW => exact absurd h (by simp)
        iterate 5 (exact absurd h (by simp))
        by_cases hlt : idx < n
        · rw [if_pos hlt] at h he
          simp only [Option.some.injEq, Prod.mk.injEq] at h he
          obtain ⟨rfl, rfl⟩ := he
          subst h
          refine ⟨ComCont.comp_leakFactorsTrace (ComCont.varBind_leakFactorsTrace _)
            (ComCont.varBind_leakFactorsTrace _), ?_⟩
          show VarMap.tyOf (VarMap.bind _ _) = _
          rw [VarMap.tyOf_bind, VarMap.tyOf_weaken]
        · rw [if_neg hlt] at h; exact absurd h (by simp)
      · have hty : VarMap.tyOf vm loc.locVar = some mt := by simp [VarMap.tyOf, hlk]
        rw [hlk] at h
        rw [hty] at he
        rcases mt with _ | _ | _ | _ | _ | n
        all_goals (dsimp only at h he)
        case memrefW => exact absurd h (by simp)
        iterate 5 (exact absurd h (by simp))
        by_cases hlt : idx < n
        · rw [dif_pos hlt] at h
          rw [if_pos hlt] at he
          simp only [Option.some.injEq, Prod.mk.injEq] at h he
          obtain ⟨rfl, rfl⟩ := he
          subst h
          refine ⟨ComCont.comp_leakFactorsTrace (ComCont.varBind_leakFactorsTrace _)
            (ComCont.varBind_leakFactorsTrace _), ?_⟩
          show VarMap.tyOf (VarMap.bind _ _) = _
          rw [VarMap.tyOf_bind, VarMap.tyOf_weaken]
        · rw [dif_neg hlt] at h; exact absurd h (by simp)
  | _ => simp [expand] at he

end CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakExpansion
