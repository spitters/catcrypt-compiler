/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NFProg
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgJasmin
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminOpInfo
public import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptOpInfo

/-!
# Branches of `NFProg` lowered to selects

`NFProg.lowerSelects p` replaces each `ifThenElse cond thn els k` of `p` whose two arms
pass the decidable test `NFProg.Lowerable` by the bindings of `thn`, then the bindings
of `els`, then one select on `cond` per result, followed by `k`. A branch whose arms
fail the test stays a branch. The recursion lowers the arms first, so a branch nested
in an arm is lowered before the arm is tested.

`NFProg.Lowerable thn els` holds when

* every result type of the branch has a select (`HasSelect.selects`), and
* each arm is straight-line (let-bindings and a return, no region constructor) and
  binds only ops that are speculatable (`HasSelect.speculatable`), whose `Option`
  denotation is `some` at every argument, and quiet (`HasSelect.quiet`), which emit no
  leakage event.

Under these conditions running the untaken arm cannot fail, so the denotation is
preserved exactly (`NFProg.denote_lowerSelects`), and it emits no event, so two runs with
equal events are lowered to two runs with equal events
(`NFProg.lowerSelects_ctRel` in `NFIfToSelectLeak`). A branch with an arm that loads or
stores is not lowered.

A dialect provides its select op, its speculatable ops and its quiet ops through
`HasSelect`. `catCryptDialect` selects at every type with `ite`, speculates every op and
lists no op quiet; `jasminDialect` selects at the register types `reg w` with
`select w`, speculates every op except the calls `extCall` and `callN`, and lists quiet
the ops of `jasminQuiet`.

`NFProg.ctSafeNF opCT` is the counterpart on `NFProg` of `ctSafeComR`: every let-bound
op satisfies `opCT` and no `ifThenElse` remains. `NFProg` carries no secrecy level, so
every branch counts as a secret-guarded one.

## Main definitions

* `HasSelect` — a dialect's select op and its speculatable ops.
* `NFProg.Lowerable` — the test on the arms of a branch.
* `NFProg.nodesOk` — every let-bound op satisfies a test and every branch satisfies a
  test on its arms, in every region.
* `NFProg.ctSafeNF`, `NFProg.ifFree`, `NFProg.allLowerable`, `NFProg.residual` —
  instances of `nodesOk`.
* `NFProg.lowerSel` — the lowering along a renaming; `NFProg.lowerSelects` at the
  identity.

## Main results

* `NFProg.denote_lowerSel`, `NFProg.denote_lowerSelects` — the lowering preserves the
  denotation at every fuel.
* `NFProg.ctSafeNF_lowerSel` — a program whose branches all pass the test, whose ops
  satisfy `opCT`, lowered with selects satisfying `opCT`, satisfies `ctSafeNF opCT`.
* `NFProg.ifFree_lowerSelects` — under the same test on every branch, no `ifThenElse`
  remains.
* `NFProg.residual_lowerSelects` — every `ifThenElse` that remains has arms failing the
  test.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Ctxt (Var Valuation)
open MultiBlockLowering (hvAppend)
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (CatCryptOp catCryptDialect)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminTy JasminOp jasminDialect)

/-! ## 1. The class -/

/-- A select op of the dialect `d` at the types `selects`, and the ops `speculatable`
    whose `Option` denotation never fails. `sel h c a b` reads `a` when the bit `c` reads
    as `true` and `b` otherwise. -/
class HasSelect (d : Dialect.{0, 0}) [DialectSignature d] [TyDenote d.Ty] [HasBoolBit d]
    [DialectDenoteM d Option] where
  /-- The types at which the dialect has a select. -/
  selects : d.Ty → Bool
  /-- The select at a type of `selects`. -/
  sel : {Γ : Ctxt d} → {t : d.Ty} → selects t = true →
    Var Γ (HasBitType.bit (d := d)) → Var Γ t → Var Γ t → Expr d Γ t
  /-- The select reads the first operand at a `true` bit and the second otherwise. -/
  denoteM_sel : ∀ {Γ : Ctxt d} {t : d.Ty} (h : selects t = true)
    (c : Var Γ (HasBitType.bit (d := d))) (a b : Var Γ t) (V : Valuation Γ),
    (sel h c a b).denoteM (M := Option) V =
      some (if HasBoolBit.toBool (d := d) (c.lookup V) then a.lookup V else b.lookup V)
  /-- The ops that may run in the untaken arm of a lowered branch. -/
  speculatable : d.Op → Bool
  /-- A speculatable op denotes `some` value at every argument. -/
  isSome_denoteM : ∀ (op : d.Op), speculatable op = true →
    ∀ args, (DialectDenoteM.denoteM (M := Option) op args).isSome
  /-- The ops that emit no leakage event: no memory access and no variable-time
      instruction, in the leakage models the lowering is certified for. -/
  quiet : d.Op → Bool

/-- Under the `Option` denotation of a dialect with a pure denotation
    (`instDialectDenoteMOptionOfPure`), every operation record satisfies the speculation
    law. -/
theorem SpecLaw.ofPure {d : Dialect} [TyDenote d.Ty] [DialectSignature d]
    [DialectDenote d] (T : OpTraits d) : SpecLaw T :=
  fun _ _ _ => rfl

/-- A speculatable jasmin operation denotes `some` value at every argument. -/
theorem jasminTraits_specLaw : SpecLaw jasminTraits := SpecLaw.ofPure jasminTraits

/-- A speculatable catCrypt operation denotes `some` value at every argument. -/
theorem catTraits_specLaw : SpecLaw catTraits := SpecLaw.ofPure catTraits

/-- `catCryptDialect` selects at every type with `ite t`, and every op is speculatable. No
    op is listed quiet: the class of an op of `catCryptDialect` depends on the parameters
    of its leakage model, and the linear route lowers branches at `jasminDialect`. -/
instance : HasSelect catCryptDialect where
  selects _ := true
  sel {_ t} _ c a b := ⟨CatCryptOp.ite t, rfl, .cons c (.cons a (.cons b .nil))⟩
  denoteM_sel _ _ _ _ _ := rfl
  speculatable := catTraits.speculatable
  isSome_denoteM := catTraits_specLaw
  quiet _ := false

/-- The register types of `jasminDialect`, at which it has the select `select w`. -/
def jasminSelects : JasminTy → Bool
  | .reg _ => true
  | _ => false

/-- The select of `jasminDialect` at a register type: `select w`. -/
def jasminSel {Γ : Ctxt jasminDialect} :
    {t : JasminTy} → jasminSelects t = true → Var Γ (JasminTy.reg 1) → Var Γ t →
    Var Γ t → Expr jasminDialect Γ t
  | .reg w, _, c, a, b => ⟨JasminOp.select w, rfl, .cons c (.cons a (.cons b .nil))⟩
  | .stackArr _ _, h, _, _, _ => absurd h Bool.false_ne_true
  | .inlineInt, h, _, _, _ => absurd h Bool.false_ne_true
  | .bool, h, _, _, _ => absurd h Bool.false_ne_true

/-- The select of `jasminDialect` at `reg w` reads `a` at the bit `1#1` and `b`
    otherwise. -/
theorem jasminSel_denoteM {Γ : Ctxt jasminDialect} {w : Nat}
    (h : jasminSelects (JasminTy.reg w) = true) (c : Var Γ (JasminTy.reg 1))
    (a b : Var Γ (JasminTy.reg w)) (V : Valuation Γ) :
    (jasminSel h c a b).denoteM (M := Option) V =
      some (JasminDialect.selectW (c.lookup V) (a.lookup V) (b.lookup V)) := rfl

/-- The ops of `jasminDialect` listed quiet: register arithmetic, the select, and a
    register constant below `2 ^ w`. A stack access (`stackLoad`, `stackStore`) emits its
    index and a leaf call may be variable time; neither is listed. -/
def jasminQuiet : JasminOp → Bool
  | .regArith .. => true
  | .select _ => true
  | .regConst w n => decide (n < 2 ^ w)
  | _ => false

open NFProgJasmin in
/-- `jasminDialect` selects at the register types with `select w` (`selectW`), every op
    except `extCall` and `callN` is speculatable, and the quiet ops are `jasminQuiet`. -/
instance : HasSelect jasminDialect where
  selects := jasminSelects
  sel h c a b := jasminSel h c a b
  denoteM_sel {_ t} h c a b V := by
    cases t with
    | reg w =>
        rw [jasminSel_denoteM h c a b V]
        show some (if _ then _ else _) = some (if decide _ = true then _ else _)
        simp only [decide_eq_true_eq]
    | _ => exact absurd h Bool.false_ne_true
  speculatable := jasminTraits.speculatable
  isSome_denoteM := jasminTraits_specLaw
  quiet := jasminQuiet

namespace NFProg

/-! ## 2. Renamings that relate two valuations -/

section Renaming

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty]

/-- `ren` relates `V` to `W`: each renamed variable reads in `W` what it reads in `V`. -/
def Agrees {Γ Δ : Ctxt d} (ren : Ctxt.Hom Γ Δ) (V : Valuation Γ) (W : Valuation Δ) : Prop :=
  ∀ {s : d.Ty} (v : Var Γ s), (ren v).lookup W = v.lookup V

omit [DialectSignature d] in
/-- The identity relates a valuation to itself. -/
theorem agrees_id {Γ : Ctxt d} (V : Valuation Γ) : Agrees (fun v => v) V V := fun _ => rfl

omit [DialectSignature d] in
/-- A lifted renaming relates the valuations extended by one value. -/
theorem agrees_lift {Γ Δ : Ctxt d} {t : d.Ty} {ren : Ctxt.Hom Γ Δ} {V : Valuation Γ}
    {W : Valuation Δ} (h : Agrees ren V W) (x : ⟦t⟧) :
    Agrees (Ctxt.Hom.lift (s := t) ren) (V.extend x) (W.extend x)
  | _, .here => rfl
  | _, .there v => h v

omit [DialectSignature d] in
/-- A renaming followed by one that relates its target valuations relates the sources. -/
theorem agrees_comp {Γ Δ Θ : Ctxt d} {ren : Ctxt.Hom Γ Δ} {r : Ctxt.Hom Δ Θ}
    {V : Valuation Γ} {W : Valuation Δ} {X : Valuation Θ} (h : Agrees ren V W)
    (hr : Agrees r W X) : Agrees (fun v => r (ren v)) V X :=
  fun v => (hr _).trans (h v)

/-- The renaming of `rs ++ Γ` into `rs ++ Δ` that keeps the prefix and acts as `ren` on
    the rest. -/
def appLift {Γ Δ : Ctxt d} : (rs : List d.Ty) → Ctxt.Hom Γ Δ → Ctxt.Hom (rs ++ Γ) (rs ++ Δ)
  | [], ren => ren
  | _ :: rs, ren => Ctxt.Hom.lift (appLift rs ren)

omit [DialectSignature d] in
/-- `appLift` relates the valuations `ren` relates, prefixed by the same tuple. -/
theorem agrees_appLift {Γ Δ : Ctxt d} {ren : Ctxt.Hom Γ Δ} {V : Valuation Γ}
    {W : Valuation Δ} (h : Agrees ren V W) :
    (rs : List d.Ty) → (A : Valuation rs) → Agrees (appLift rs ren) (hvAppend A V) (hvAppend A W)
  | [], .nil => h
  | _ :: rs, .cons a A => agrees_lift (agrees_appLift h rs A) a

/-- The renaming of `rs ++ Γ` into `Δ` that sends the prefix to the variables `res` and
    the rest through `ren`. -/
def bindHom {Γ Δ : Ctxt d} : {rs : List d.Ty} → HVector (fun t => Var Δ t) rs →
    Ctxt.Hom Γ Δ → {t : d.Ty} → Var (rs ++ Γ) t → Var Δ t
  | [], .nil, ren, _, v => ren v
  | _ :: _, .cons x _, _, _, .here => x
  | _ :: _, .cons _ xs, ren, _, .there v => bindHom xs ren v

omit [DialectSignature d] in
/-- `bindHom res ren` relates the valuation of `Γ` prefixed by the values of `res` to the
    valuation `ren` relates it to. -/
theorem agrees_bindHom {Γ Δ : Ctxt d} {ren : Ctxt.Hom Γ Δ} {V : Valuation Γ}
    {W : Valuation Δ} (h : Agrees ren V W) :
    {rs : List d.Ty} → (res : HVector (fun t => Var Δ t) rs) →
    Agrees (bindHom res ren) (hvAppend (Expr.lookupArgs res W) V) W
  | [], .nil, _, v => h v
  | _ :: _, .cons _ _, _, .here => rfl
  | _ :: _, .cons _ xs, _, .there v => agrees_bindHom h xs v

omit [DialectSignature d] in
/-- Renamed variables read in `W` what the source variables read in `V`. -/
theorem lookupArgs_renameVars {Γ Δ : Ctxt d} {ren : Ctxt.Hom Γ Δ} {V : Valuation Γ}
    {W : Valuation Δ} (h : Agrees ren V W) :
    {ts : List d.Ty} → (vs : HVector (fun t => Var Γ t) ts) →
    Expr.lookupArgs (HVector.renameVars ren vs) W = Expr.lookupArgs vs V
  | [], .nil => rfl
  | _ :: _, .cons v vs => by
      show HVector.cons _ _ = HVector.cons _ _
      rw [h v, lookupArgs_renameVars h vs]

/-- A renamed expression denotes in `W` what the source denotes in `V`. -/
theorem denoteM_rename [DialectDenoteM d Option] {Γ Δ : Ctxt d} {t : d.Ty}
    {ren : Ctxt.Hom Γ Δ} {V : Valuation Γ} {W : Valuation Δ} (h : Agrees ren V W)
    (e : Expr d Γ t) : (e.rename ren).denoteM (M := Option) W = e.denoteM V := by
  obtain ⟨op, rfl, args⟩ := e
  show DialectDenoteM.denoteM op (Expr.lookupArgs (HVector.renameVars ren args) W) = _
  rw [lookupArgs_renameVars h args]
  rfl

end Renaming

/-! ## 3. The test on the arms and the node predicates -/

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectDenoteM d Option] [HasSelect d]

/-- The straight-line programs (let-bindings and a return) whose let-bound ops are all
    speculatable and quiet. -/
def straightSpec : {Γ : Ctxt d} → {ts : List d.Ty} → NFProg d Γ ts → Bool
  | _, _, .ret _ => true
  | _, _, .var e k =>
      HasSelect.speculatable e.op && HasSelect.quiet e.op && straightSpec k
  | _, _, .forLoop .. => false
  | _, _, .ifThenElse .. => false
  | _, _, .whileLoop .. => false
  | _, _, .call .. => false

/-- **The test on the arms of a branch.** Every result type has a select and both arms
    are straight-line with ops that are speculatable and quiet (`HasSelect.quiet`). The
    lowering runs both arms, so an op that emits a leakage event must not be speculated:
    a branch with an arm that loads or stores fails the test and stays a branch. -/
def Lowerable {Γ : Ctxt d} {rs : List d.Ty} (thn els : NFProg d Γ rs) : Bool :=
  rs.all HasSelect.selects && straightSpec thn && straightSpec els

/-- Every let-bound op satisfies `opOk` and every branch satisfies `ifOk` on its arms, in
    every region. -/
def nodesOk (opOk : d.Op → Bool)
    (ifOk : ∀ {Γ : Ctxt d} {rs : List d.Ty}, NFProg d Γ rs → NFProg d Γ rs → Bool) :
    {Γ : Ctxt d} → {ts : List d.Ty} → NFProg d Γ ts → Bool
  | _, _, .ret _ => true
  | _, _, .var e k => opOk e.op && nodesOk opOk ifOk k
  | _, _, .forLoop _ _ body k => nodesOk opOk ifOk body && nodesOk opOk ifOk k
  | _, _, .ifThenElse _ thn els k =>
      ifOk thn els && nodesOk opOk ifOk thn && nodesOk opOk ifOk els && nodesOk opOk ifOk k
  | _, _, .whileLoop _ body k => nodesOk opOk ifOk body && nodesOk opOk ifOk k
  | _, _, .call _ _ k => nodesOk opOk ifOk k

/-- **The constant-time predicate on `NFProg`.** Every let-bound op satisfies `opCT` and
    no `ifThenElse` remains: the counterpart of `ctSafeComR` with every branch guarded
    by a secret. -/
def ctSafeNF (opCT : d.Op → Bool) {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    Bool :=
  nodesOk opCT (fun _ _ => false) p

/-- The programs without `ifThenElse`. -/
def ifFree {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) : Bool :=
  ctSafeNF (fun _ => true) p

/-- The programs every branch of which passes `Lowerable`. -/
def allLowerable {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) : Bool :=
  nodesOk (fun _ => true) (fun thn els => Lowerable thn els) p

/-- The programs every branch of which fails `Lowerable`. -/
def residual {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) : Bool :=
  nodesOk (fun _ => true) (fun thn els => !Lowerable thn els) p

/-! ## 4. The lowering -/

/-- The bindings of a straight-line program renamed by `ren`, then the continuation
    `kont` at the renaming into the extended context and at the returned variables;
    `none` on a region constructor or a call. -/
def emitArm? {ts : List d.Ty} : {Γ Δ : Ctxt d} → {rs : List d.Ty} → NFProg d Γ rs →
    Ctxt.Hom Γ Δ →
    ({Δ' : Ctxt d} → Ctxt.Hom Δ Δ' → HVector (fun t => Var Δ' t) rs →
      Option (NFProg d Δ' ts)) →
    Option (NFProg d Δ ts)
  | _, _, _, .ret vs, ren, kont => kont (fun v => v) (HVector.renameVars ren vs)
  | _, _, _, .var e k, ren, kont =>
      (emitArm? k (Ctxt.Hom.lift ren) (fun r res => kont (fun v => r (.there v)) res)).map
        (.var (e.rename ren))
  | _, _, _, .forLoop .., _, _ => none
  | _, _, _, .ifThenElse .., _, _ => none
  | _, _, _, .whileLoop .., _, _ => none
  | _, _, _, .call .., _, _ => none

omit [DialectSignature d] [TyDenote d.Ty] in
/-- A test that holds of every entry of a list holds of its head. -/
theorem selects_head {f : d.Ty → Bool} {r : d.Ty} {rs : List d.Ty}
    (h : (r :: rs).all f = true) : f r = true := by
  simp only [List.all_cons, Bool.and_eq_true] at h
  exact h.1

omit [DialectSignature d] [TyDenote d.Ty] in
/-- A test that holds of every entry of a list holds of every entry of its tail. -/
theorem selects_tail {f : d.Ty → Bool} {r : d.Ty} {rs : List d.Ty}
    (h : (r :: rs).all f = true) : rs.all f = true := by
  simp only [List.all_cons, Bool.and_eq_true] at h
  exact h.2

/-- One select on the bit `c` per pair of variables of `va` and `vb`, then the
    continuation `kont` at the renaming into the extended context and at the selected
    variables. -/
def emitSels {ts : List d.Ty} : {Δ : Ctxt d} → {rs : List d.Ty} →
    rs.all HasSelect.selects = true → Var Δ (HasBitType.bit (d := d)) →
    HVector (fun t => Var Δ t) rs → HVector (fun t => Var Δ t) rs →
    ({Δ' : Ctxt d} → Ctxt.Hom Δ Δ' → HVector (fun t => Var Δ' t) rs → NFProg d Δ' ts) →
    NFProg d Δ ts
  | _, [], _, _, .nil, .nil, kont => kont (fun v => v) .nil
  | _, _ :: _, h, c, .cons a va, .cons b vb, kont =>
      .var (HasSelect.sel (selects_head h) c a b)
        (emitSels (selects_tail h) (.there c) (shiftVars va) (shiftVars vb)
          (fun r res => kont (fun v => r (.there v)) (.cons (r .here) res)))

/-- A branch on `c` with the arms `thn` and `els` and the continuation `kont`, lowered to
    the bindings of `thn`, the bindings of `els` and the selects; `none` when the arms
    fail `Lowerable`. -/
def lowerIte? {ts : List d.Ty} {Δ : Ctxt d} {rs : List d.Ty}
    (c : Var Δ (HasBitType.bit (d := d))) (thn els : NFProg d Δ rs)
    (kont : {Δ' : Ctxt d} → Ctxt.Hom Δ Δ' → HVector (fun t => Var Δ' t) rs →
      NFProg d Δ' ts) : Option (NFProg d Δ ts) :=
  if h : Lowerable thn els = true then
    emitArm? thn (fun v => v) fun r1 va =>
      emitArm? els r1 fun r2 vb =>
        some (emitSels (by simp only [Lowerable, Bool.and_eq_true] at h; exact h.1.1)
          (r2 (r1 c)) (HVector.renameVars r2 va) vb
          fun r3 res => kont (fun v => r3 (r2 (r1 v))) res)
  else none

/-- **The lowering of branches to selects along the renaming `ren`.** Each branch whose
    lowered arms pass `Lowerable` becomes the bindings of both arms and the selects; the
    other constructors are kept, with their regions lowered. -/
def lowerSel : {Γ Δ : Ctxt d} → {ts : List d.Ty} → NFProg d Γ ts → Ctxt.Hom Γ Δ →
    NFProg d Δ ts
  | _, _, _, .ret vs, ren => .ret (HVector.renameVars ren vs)
  | _, _, _, .var e k, ren => .var (e.rename ren) (lowerSel k (Ctxt.Hom.lift ren))
  | _, _, _, .forLoop (cs := cs) count inits body k, ren =>
      .forLoop (ren count) (HVector.renameVars ren inits)
        (lowerSel body (appLift cs (Ctxt.Hom.lift ren))) (lowerSel k (appLift cs ren))
  | _, _, _, .ifThenElse (rs := rs) cond thn els k, ren =>
      match lowerIte? (ren cond) (lowerSel thn ren) (lowerSel els ren)
          (fun r res => lowerSel k (bindHom res (fun v => r (ren v)))) with
      | some q => q
      | none => .ifThenElse (ren cond) (lowerSel thn ren) (lowerSel els ren)
          (lowerSel k (appLift rs ren))
  | _, _, _, .whileLoop (cs := cs) inits body k, ren =>
      .whileLoop (HVector.renameVars ren inits) (lowerSel body (appLift cs ren))
        (lowerSel k (appLift cs ren))
  | _, _, _, .call (rs := rs) f args k, ren =>
      .call f (HVector.renameVars ren args) (lowerSel k (appLift rs ren))

/-- The lowering of branches to selects. -/
def lowerSelects {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) : NFProg d Γ ts :=
  lowerSel p (fun v => v)

/-! ## 5. Preservation of the denotation -/

section Denote

variable [CallDenote d]

/-- A straight-line program with speculatable ops denotes `some` tuple. -/
theorem isSome_denote_of_straightSpec (fuel : Nat) {Γ : Ctxt d} {rs : List d.Ty}
    (p : NFProg d Γ rs) (hp : straightSpec p = true) :
    ∀ V : Valuation Γ, (p.denote fuel V).isSome := by
  induction p with
  | ret => intro V; rfl
  | var e k ih =>
      intro V
      simp only [straightSpec, Bool.and_eq_true] at hp
      obtain ⟨op, rfl, args⟩ := e
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp
        (HasSelect.isSome_denoteM op hp.1.1 (Expr.lookupArgs args V))
      show (Option.bind (DialectDenoteM.denoteM (M := Option) op (Expr.lookupArgs args V))
        _).isSome = true
      rw [hx]
      exact ih hp.2 _
  | forLoop => simp [straightSpec] at hp
  | ifThenElse => simp [straightSpec] at hp
  | whileLoop => simp [straightSpec] at hp
  | call => simp [straightSpec] at hp

omit [HasSelect d] in
/-- **Denotation of `emitArm?`.** If every program the continuation returns at a
    renaming relating `W` to `W'` denotes `G` at the values of its variables, a program
    `emitArm? p ren kont` returns denotes the bind of the denotation of `p` with `G`. -/
theorem emitArm?_denote (fuel : Nat) {ts : List d.Ty} {Γ : Ctxt d} {rs : List d.Ty}
    (p : NFProg d Γ rs) :
    ∀ {Δ : Ctxt d} (ren : Ctxt.Hom Γ Δ)
      (kont : {Δ' : Ctxt d} → Ctxt.Hom Δ Δ' → HVector (fun t => Var Δ' t) rs →
        Option (NFProg d Δ' ts))
      (V : Valuation Γ) (W : Valuation Δ) (G : Valuation rs → Option (Valuation ts)),
      Agrees ren V W →
      (∀ {Δ' : Ctxt d} (r : Ctxt.Hom Δ Δ') (res : HVector (fun t => Var Δ' t) rs)
        (W' : Valuation Δ'), Agrees r W W' → ∀ q, kont r res = some q →
          q.denote fuel W' = G (Expr.lookupArgs res W')) →
      ∀ q, emitArm? p ren kont = some q → q.denote fuel W = p.denote fuel V >>= G := by
  induction p with
  | ret vs =>
      intro Δ ren kont V W G hren hk q hq
      rw [hk (fun v => v) _ W (agrees_id W) q hq, lookupArgs_renameVars hren]
      rfl
  | var e k ih =>
      intro Δ ren kont V W G hren hk q hq
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [denote, denoteM_rename hren, Option.bind_eq_bind, Option.bind_assoc]
      congr 1
      funext x
      exact ih _ _ _ _ G (agrees_lift hren x)
        (fun r res W' hr q hq => hk _ res W' (fun v => hr (.there v)) q hq) q' hq'
  | forLoop => intro _ _ _ _ _ _ _ _ q hq; simp [emitArm?] at hq
  | ifThenElse => intro _ _ _ _ _ _ _ _ q hq; simp [emitArm?] at hq
  | whileLoop => intro _ _ _ _ _ _ _ _ q hq; simp [emitArm?] at hq
  | call => intro _ _ _ _ _ _ _ _ q hq; simp [emitArm?] at hq

/-- **Denotation of `emitSels`.** If every program the continuation returns at a
    renaming relating `W` to `W'` denotes `G` at the values of its variables, the
    selects denote `G` at the values of `va` when `c` reads as `true` and at the values
    of `vb` otherwise. -/
theorem emitSels_denote (fuel : Nat) {ts : List d.Ty} : ∀ {Δ : Ctxt d} {rs : List d.Ty}
    (h : rs.all HasSelect.selects = true) (c : Var Δ (HasBitType.bit (d := d)))
    (va vb : HVector (fun t => Var Δ t) rs)
    (kont : {Δ' : Ctxt d} → Ctxt.Hom Δ Δ' → HVector (fun t => Var Δ' t) rs →
      NFProg d Δ' ts)
    (W : Valuation Δ) (G : Valuation rs → Option (Valuation ts)),
    (∀ {Δ' : Ctxt d} (r : Ctxt.Hom Δ Δ') (res : HVector (fun t => Var Δ' t) rs)
      (W' : Valuation Δ'), Agrees r W W' →
        (kont r res).denote fuel W' = G (Expr.lookupArgs res W')) →
    (emitSels h c va vb kont).denote fuel W =
      G (if HasBoolBit.toBool (d := d) (c.lookup W) then Expr.lookupArgs va W
        else Expr.lookupArgs vb W)
  | _, [], _, _, .nil, .nil, kont, W, G, hk => by
      rw [emitSels, hk _ _ W (agrees_id W)]
      split <;> rfl
  | _, _ :: _, h, c, .cons a va, .cons b vb, kont, W, G, hk => by
      rw [emitSels, denote_var, HasSelect.denoteM_sel]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [emitSels_denote fuel _ _ _ _ _ _
        (fun R => G (.cons (if HasBoolBit.toBool (d := d) (c.lookup W) then a.lookup W
          else b.lookup W) R)) (fun r res W' hr => ?_)]
      · rw [lookupArgs_shiftVars, lookupArgs_shiftVars]
        show G (HVector.cons _ (if HasBoolBit.toBool (d := d) (c.lookup W) then _ else _)) = _
        cases HasBoolBit.toBool (d := d) (c.lookup W) <;> rfl
      · rw [hk _ _ W' (fun v => hr (.there v))]
        show G (HVector.cons ((r .here).lookup W') _) = _
        rw [hr .here]
        rfl

/-- **Denotation of `lowerIte?`.** If every program the continuation returns at a
    renaming relating `W` to `W'` denotes `G` at the values of its variables, a program
    `lowerIte? c thn els kont` returns denotes the branch on `c` followed by `G`. -/
theorem lowerIte?_denote (fuel : Nat) {ts : List d.Ty} {Δ : Ctxt d} {rs : List d.Ty}
    (c : Var Δ (HasBitType.bit (d := d))) (thn els : NFProg d Δ rs)
    (kont : {Δ' : Ctxt d} → Ctxt.Hom Δ Δ' → HVector (fun t => Var Δ' t) rs →
      NFProg d Δ' ts)
    (W : Valuation Δ) (G : Valuation rs → Option (Valuation ts))
    (hk : ∀ {Δ' : Ctxt d} (r : Ctxt.Hom Δ Δ') (res : HVector (fun t => Var Δ' t) rs)
      (W' : Valuation Δ'), Agrees r W W' →
        (kont r res).denote fuel W' = G (Expr.lookupArgs res W'))
    (q : NFProg d Δ ts) (hq : lowerIte? c thn els kont = some q) :
    q.denote fuel W =
      (if HasBoolBit.toBool (d := d) (c.lookup W) then thn.denote fuel W
        else els.denote fuel W) >>= G := by
  unfold lowerIte? at hq
  split at hq
  next h =>
    simp only [Lowerable, Bool.and_eq_true] at h
    obtain ⟨A, hA⟩ := Option.isSome_iff_exists.mp
      (isSome_denote_of_straightSpec fuel thn h.1.2 W)
    obtain ⟨B, hB⟩ := Option.isSome_iff_exists.mp
      (isSome_denote_of_straightSpec fuel els h.2 W)
    rw [emitArm?_denote fuel thn _ _ W W
      (fun A => els.denote fuel W >>= fun B =>
        G (if HasBoolBit.toBool (d := d) (c.lookup W) then A else B)) (agrees_id W) ?_ q hq]
    · rw [hA, hB]
      cases HasBoolBit.toBool (d := d) (c.lookup W) <;> rfl
    · intro Δ1 r1 va W1 hr1 q1 hq1
      rw [emitArm?_denote fuel els r1 _ W W1
        (fun B => G (if HasBoolBit.toBool (d := d) (c.lookup W)
          then Expr.lookupArgs va W1 else B)) hr1 ?_ q1 hq1]
      intro Δ2 r2 vb W2 hr2 q2 hq2
      obtain rfl := Option.some.inj hq2
      rw [emitSels_denote fuel _ _ _ _ _ W2 G
        (fun r3 res W3 hr3 => hk _ res W3 (agrees_comp (agrees_comp hr1 hr2) hr3)),
        hr2 (r1 c), hr1 c, lookupArgs_renameVars hr2]
  next => cases hq

/-- **Preservation.** A program lowered along a renaming relating `V` to `W` denotes at
    `W`, at every fuel, what the source denotes at `V`. -/
theorem denote_lowerSel (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ {Δ : Ctxt d} (ren : Ctxt.Hom Γ Δ) (V : Valuation Γ) (W : Valuation Δ),
      Agrees ren V W → (lowerSel p ren).denote fuel W = p.denote fuel V := by
  induction p with
  | ret vs =>
      intro Δ ren V W h
      simp only [lowerSel, denote, lookupArgs_renameVars h]
  | var e k ih =>
      intro Δ ren V W h
      simp only [lowerSel, denote, denoteM_rename h]
      congr 1
      funext x
      exact ih _ _ _ (agrees_lift h x)
  | forLoop count inits body k ihb ihk =>
      intro Δ ren V W h
      have hb : ∀ acc i, (lowerSel body (appLift _ (Ctxt.Hom.lift ren))).denote fuel
          (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) W)) =
          body.denote fuel (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) V)) :=
        fun acc i => ihb _ _ _ (agrees_appLift (agrees_lift h _) _ acc)
      have hk : ∀ acc, (lowerSel k (appLift _ ren)).denote fuel (hvAppend acc W) =
          k.denote fuel (hvAppend acc V) :=
        fun acc => ihk _ _ _ (agrees_appLift h _ acc)
      simp only [lowerSel, denote, lookupArgs_renameVars h, h count, hb, hk]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ ren V W h
      have hk : ∀ r, (lowerSel k (appLift _ ren)).denote fuel (hvAppend r W) =
          k.denote fuel (hvAppend r V) :=
        fun r => ihk _ _ _ (agrees_appLift h _ r)
      have harms : (if HasBoolBit.toBool (d := d) ((ren cond).lookup W)
            then (lowerSel thn ren).denote fuel W else (lowerSel els ren).denote fuel W) =
          (if HasBoolBit.toBool (d := d) (cond.lookup V) then thn.denote fuel V
            else els.denote fuel V) := by
        rw [h cond, iht _ _ _ h, ihe _ _ _ h]
      rw [lowerSel]
      split
      next q hq =>
        rw [lowerIte?_denote fuel _ _ _ _ W (fun r => k.denote fuel (hvAppend r V))
          (fun r res W' hr => ihk _ _ _ (agrees_bindHom (agrees_comp h hr) res)) q hq, harms]
        rfl
      next =>
        rw [denote, harms]
        simp only [hk]
        rfl
  | whileLoop inits body k ihb ihk =>
      intro Δ ren V W h
      have hb : ∀ acc, (lowerSel body (appLift _ ren)).denote fuel (hvAppend acc W) =
          body.denote fuel (hvAppend acc V) :=
        fun acc => ihb _ _ _ (agrees_appLift h _ acc)
      have hk : ∀ acc, (lowerSel k (appLift _ ren)).denote fuel (hvAppend acc W) =
          k.denote fuel (hvAppend acc V) :=
        fun acc => ihk _ _ _ (agrees_appLift h _ acc)
      simp only [lowerSel, denote, lookupArgs_renameVars h, hb, hk]
  | call f args k ih =>
      intro Δ ren V W h
      have hk : ∀ r, (lowerSel k (appLift _ ren)).denote fuel (hvAppend r W) =
          k.denote fuel (hvAppend r V) :=
        fun r => ih _ _ _ (agrees_appLift h _ r)
      simp only [lowerSel, denote, lookupArgs_renameVars h, hk]

/-- **Preservation.** `lowerSelects p` denotes what `p` denotes, at every fuel and
    valuation. -/
theorem denote_lowerSelects (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts)
    (V : Valuation Γ) : (lowerSelects p).denote fuel V = p.denote fuel V :=
  denote_lowerSel fuel p _ V V (agrees_id V)

end Denote

/-! ## 6. What the lowering leaves -/

section Nodes

variable (opOk : d.Op → Bool)
  (ifOk : ∀ {Γ : Ctxt d} {rs : List d.Ty}, NFProg d Γ rs → NFProg d Γ rs → Bool)

omit [DialectDenoteM d Option] [HasSelect d] in
/-- A program `emitArm? p ren kont` returns satisfies `nodesOk` when `p` does and every
    program the continuation returns does. -/
theorem nodesOk_emitArm? {ts : List d.Ty} {Γ : Ctxt d} {rs : List d.Ty}
    (p : NFProg d Γ rs) (hp : nodesOk opOk ifOk p = true) :
    ∀ {Δ : Ctxt d} (ren : Ctxt.Hom Γ Δ)
      (kont : {Δ' : Ctxt d} → Ctxt.Hom Δ Δ' → HVector (fun t => Var Δ' t) rs →
        Option (NFProg d Δ' ts)),
      (∀ {Δ' : Ctxt d} (r : Ctxt.Hom Δ Δ') (res : HVector (fun t => Var Δ' t) rs) q,
        kont r res = some q → nodesOk opOk ifOk q = true) →
      ∀ q, emitArm? p ren kont = some q → nodesOk opOk ifOk q = true := by
  induction p with
  | ret vs => intro Δ ren kont hk q hq; exact hk _ _ q hq
  | var e k ih =>
      intro Δ ren kont hk q hq
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [nodesOk, Bool.and_eq_true] at hp
      simp only [nodesOk, Bool.and_eq_true]
      exact ⟨hp.1, ih hp.2 (Ctxt.Hom.lift ren) (fun r res => kont (fun v => r (.there v)) res)
        (fun r res q hq => hk _ res q hq) q' hq'⟩
  | forLoop => intro _ _ _ _ q hq; simp [emitArm?] at hq
  | ifThenElse => intro _ _ _ _ q hq; simp [emitArm?] at hq
  | whileLoop => intro _ _ _ _ q hq; simp [emitArm?] at hq
  | call => intro _ _ _ _ q hq; simp [emitArm?] at hq

variable {opOk} in
/-- The selects satisfy `nodesOk` when the select ops satisfy `opOk` and every program
    the continuation returns satisfies `nodesOk`. -/
theorem nodesOk_emitSels
    (hsel : ∀ {Γ : Ctxt d} {t : d.Ty} (h : HasSelect.selects t = true)
      (c : Var Γ (HasBitType.bit (d := d))) (a b : Var Γ t),
      opOk (HasSelect.sel h c a b).op = true)
    {ts : List d.Ty} : ∀ {Δ : Ctxt d} {rs : List d.Ty}
    (h : rs.all HasSelect.selects = true) (c : Var Δ (HasBitType.bit (d := d)))
    (va vb : HVector (fun t => Var Δ t) rs)
    (kont : {Δ' : Ctxt d} → Ctxt.Hom Δ Δ' → HVector (fun t => Var Δ' t) rs →
      NFProg d Δ' ts),
    (∀ {Δ' : Ctxt d} (r : Ctxt.Hom Δ Δ') (res : HVector (fun t => Var Δ' t) rs),
      nodesOk opOk ifOk (kont r res) = true) →
    nodesOk opOk ifOk (emitSels h c va vb kont) = true
  | _, [], _, _, .nil, .nil, _, hk => hk _ _
  | _, _ :: _, h, c, .cons a va, .cons b vb, kont, hk => by
      rw [emitSels, nodesOk, hsel, Bool.true_and]
      exact nodesOk_emitSels hsel _ _ _ _ _ (fun r res => hk _ _)

variable {opOk} in
/-- A program `lowerIte?` returns satisfies `nodesOk` when the arms, the select ops and
    every program the continuation returns do. -/
theorem nodesOk_lowerIte?
    (hsel : ∀ {Γ : Ctxt d} {t : d.Ty} (h : HasSelect.selects t = true)
      (c : Var Γ (HasBitType.bit (d := d))) (a b : Var Γ t),
      opOk (HasSelect.sel h c a b).op = true)
    {ts : List d.Ty} {Δ : Ctxt d} {rs : List d.Ty}
    (c : Var Δ (HasBitType.bit (d := d))) (thn els : NFProg d Δ rs)
    (kont : {Δ' : Ctxt d} → Ctxt.Hom Δ Δ' → HVector (fun t => Var Δ' t) rs →
      NFProg d Δ' ts)
    (ht : nodesOk opOk ifOk thn = true) (he : nodesOk opOk ifOk els = true)
    (hk : ∀ {Δ' : Ctxt d} (r : Ctxt.Hom Δ Δ') (res : HVector (fun t => Var Δ' t) rs),
      nodesOk opOk ifOk (kont r res) = true)
    (q : NFProg d Δ ts) (hq : lowerIte? c thn els kont = some q) :
    nodesOk opOk ifOk q = true := by
  unfold lowerIte? at hq
  split at hq
  next =>
    refine nodesOk_emitArm? opOk ifOk thn ht _ _ (fun r1 va q1 hq1 => ?_) q hq
    refine nodesOk_emitArm? opOk ifOk els he _ _ (fun r2 vb q2 hq2 => ?_) q1 hq1
    obtain rfl := Option.some.inj hq2
    exact nodesOk_emitSels ifOk hsel _ _ _ _ _ (fun r3 res => hk _ res)
  next => cases hq

end Nodes

/-- `emitArm?` on a straight-line program with a continuation that is `some` everywhere
    is `some`. -/
theorem isSome_emitArm? {ts : List d.Ty} {Γ : Ctxt d} {rs : List d.Ty} (p : NFProg d Γ rs)
    (hp : straightSpec p = true) :
    ∀ {Δ : Ctxt d} (ren : Ctxt.Hom Γ Δ)
      (kont : {Δ' : Ctxt d} → Ctxt.Hom Δ Δ' → HVector (fun t => Var Δ' t) rs →
        Option (NFProg d Δ' ts)),
      (∀ {Δ' : Ctxt d} (r : Ctxt.Hom Δ Δ') (res : HVector (fun t => Var Δ' t) rs),
        (kont r res).isSome) →
      (emitArm? p ren kont).isSome := by
  induction p with
  | ret vs => intro Δ ren kont hk; exact hk _ _
  | var e k ih =>
      intro Δ ren kont hk
      simp only [straightSpec, Bool.and_eq_true] at hp
      rw [emitArm?, Option.isSome_map]
      exact ih hp.2 _ _ (fun _ _ => hk _ _)
  | forLoop => simp [straightSpec] at hp
  | ifThenElse => simp [straightSpec] at hp
  | whileLoop => simp [straightSpec] at hp
  | call => simp [straightSpec] at hp

/-- `lowerIte?` is `some` exactly on arms that pass `Lowerable`. -/
theorem isSome_lowerIte?_iff {ts : List d.Ty} {Δ : Ctxt d} {rs : List d.Ty}
    (c : Var Δ (HasBitType.bit (d := d))) (thn els : NFProg d Δ rs)
    (kont : {Δ' : Ctxt d} → Ctxt.Hom Δ Δ' → HVector (fun t => Var Δ' t) rs →
      NFProg d Δ' ts) :
    (lowerIte? c thn els kont).isSome = Lowerable thn els := by
  unfold lowerIte?
  split
  next h =>
    rw [h]
    have h' := h
    simp only [Lowerable, Bool.and_eq_true] at h'
    exact isSome_emitArm? thn h'.1.2 _ _ (fun r1 va =>
      isSome_emitArm? els h'.2 _ _ (fun _ _ => rfl))
  next h => simpa using h

/-- Lowering keeps a straight-line program with speculatable ops straight-line with
    speculatable ops. -/
theorem straightSpec_lowerSel {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts)
    (hp : straightSpec p = true) :
    ∀ {Δ : Ctxt d} (ren : Ctxt.Hom Γ Δ), straightSpec (lowerSel p ren) = true := by
  induction p with
  | ret => intro _ _; rfl
  | var e k ih =>
      intro _ ren
      simp only [straightSpec, Bool.and_eq_true] at hp
      simp only [lowerSel, straightSpec, Bool.and_eq_true]
      exact ⟨hp.1, ih hp.2 _⟩
  | forLoop => simp [straightSpec] at hp
  | ifThenElse => simp [straightSpec] at hp
  | whileLoop => simp [straightSpec] at hp
  | call => simp [straightSpec] at hp

/-- Lowering keeps arms that pass `Lowerable` passing it. -/
theorem lowerable_lowerSel {Γ Δ : Ctxt d} {rs : List d.Ty} (thn els : NFProg d Γ rs)
    (h : Lowerable thn els = true) (ren : Ctxt.Hom Γ Δ) :
    Lowerable (lowerSel thn ren) (lowerSel els ren) = true := by
  simp only [Lowerable, Bool.and_eq_true] at h ⊢
  exact ⟨⟨h.1.1, straightSpec_lowerSel thn h.1.2 ren⟩, straightSpec_lowerSel els h.2 ren⟩

/-- **The constant-time predicate after the lowering.** A program every branch of which
    passes `Lowerable` and every op of which satisfies `opCT`, lowered with select ops
    that satisfy `opCT`, satisfies `ctSafeNF opCT`: no `ifThenElse` remains. -/
theorem ctSafeNF_lowerSel (opCT : d.Op → Bool)
    (hsel : ∀ {Γ : Ctxt d} {t : d.Ty} (h : HasSelect.selects t = true)
      (c : Var Γ (HasBitType.bit (d := d))) (a b : Var Γ t),
      opCT (HasSelect.sel h c a b).op = true)
    {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) (hL : allLowerable p = true)
    (hops : nodesOk opCT (fun _ _ => true) p = true) :
    ∀ {Δ : Ctxt d} (ren : Ctxt.Hom Γ Δ), ctSafeNF opCT (lowerSel p ren) = true := by
  unfold allLowerable at hL
  unfold ctSafeNF
  induction p with
  | ret => intro _ _; rfl
  | var e k ih =>
      intro _ ren
      simp only [nodesOk, Bool.and_eq_true] at hL hops
      simp only [lowerSel, nodesOk, Bool.and_eq_true]
      exact ⟨hops.1, ih hL.2 hops.2 _⟩
  | forLoop _ _ body k ihb ihk =>
      intro _ ren
      simp only [nodesOk, Bool.and_eq_true] at hL hops
      simp only [lowerSel, nodesOk, Bool.and_eq_true]
      exact ⟨ihb hL.1 hops.1 _, ihk hL.2 hops.2 _⟩
  | ifThenElse cond thn els k iht ihe ihk =>
      intro _ ren
      simp only [nodesOk, Bool.and_eq_true] at hL hops
      obtain ⟨⟨⟨hlow, hLt⟩, hLe⟩, hLk⟩ := hL
      obtain ⟨⟨⟨_, hot⟩, hoe⟩, hok⟩ := hops
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp
        ((isSome_lowerIte?_iff (ren cond) (lowerSel thn ren) (lowerSel els ren)
          (fun r res => lowerSel k (bindHom res (fun v => r (ren v))))).trans
          (lowerable_lowerSel thn els hlow ren))
      rw [lowerSel, hq]
      exact nodesOk_lowerIte? _ hsel _ _ _ _ (iht hLt hot ren) (ihe hLe hoe ren)
        (fun _ _ => ihk hLk hok _) q hq
  | whileLoop _ body k ihb ihk =>
      intro _ ren
      simp only [nodesOk, Bool.and_eq_true] at hL hops
      simp only [lowerSel, nodesOk, Bool.and_eq_true]
      exact ⟨ihb hL.1 hops.1 _, ihk hL.2 hops.2 _⟩
  | call _ _ k ih =>
      intro _ ren
      simp only [nodesOk] at hL hops
      simp only [lowerSel, nodesOk]
      exact ih hL hops _

/-- **No branch remains.** `lowerSelects p` has no `ifThenElse` when every branch of `p`
    passes `Lowerable`. -/
theorem ifFree_lowerSelects {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts)
    (hL : allLowerable p = true) : ifFree (lowerSelects p) = true :=
  ctSafeNF_lowerSel (fun _ => true) (fun _ _ _ _ => rfl) p hL
    (by
      clear hL
      induction p with
      | ret => rfl
      | var _ _ ih => simp only [nodesOk, ih, Bool.and_self]
      | forLoop _ _ _ _ ihb ihk => simp only [nodesOk, ihb, ihk, Bool.and_self]
      | ifThenElse _ _ _ _ iht ihe ihk => simp only [nodesOk, iht, ihe, ihk, Bool.and_self]
      | whileLoop _ _ _ ihb ihk => simp only [nodesOk, ihb, ihk, Bool.and_self]
      | call _ _ _ ih => simp only [nodesOk, ih])
    _

/-- **What remains.** Every `ifThenElse` of a lowered program has arms that fail
    `Lowerable`. -/
theorem residual_lowerSel {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ {Δ : Ctxt d} (ren : Ctxt.Hom Γ Δ), residual (lowerSel p ren) = true := by
  unfold residual
  induction p with
  | ret => intro _ _; rfl
  | var e k ih =>
      intro _ ren
      simp only [lowerSel, nodesOk, ih, Bool.and_self]
  | forLoop _ _ body k ihb ihk =>
      intro _ ren
      simp only [lowerSel, nodesOk, ihb, ihk, Bool.and_self]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro _ ren
      rw [lowerSel]
      split
      next q hq =>
        exact nodesOk_lowerIte? _ (fun _ _ _ _ => rfl) _ _ _ _ (iht ren) (ihe ren)
          (fun _ _ => ihk _) q hq
      next hq =>
        have hn := isSome_lowerIte?_iff (ren cond) (lowerSel thn ren) (lowerSel els ren)
          (fun r res => lowerSel k (bindHom res (fun v => r (ren v))))
        rw [hq, Option.isSome_none] at hn
        simp only [nodesOk, ← hn, iht, ihe, ihk, Bool.not_false, Bool.and_self]
  | whileLoop _ body k ihb ihk =>
      intro _ ren
      simp only [lowerSel, nodesOk, ihb, ihk, Bool.and_self]
  | call _ _ k ih =>
      intro _ ren
      simp only [lowerSel, nodesOk, ih]

/-- **What remains.** Every `ifThenElse` of `lowerSelects p` has arms that fail
    `Lowerable`. -/
theorem residual_lowerSelects {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    residual (lowerSelects p) = true :=
  residual_lowerSel p _

end NFProg

end CatCrypt.Crypto.SecureCompilation.VIR
