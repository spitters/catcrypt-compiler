/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Hax.ReifyImp
public import Mathlib.Data.ZMod.Basic
public import HaxLean.TExpr
public meta import Lean
public meta import HaxLean.Semantics

/-!
# A reifier for prime-field arithmetic over `ZMod n`

`reifyField% n f unfolding c₁ … cₖ` is `reifyImp% n f` on the body of `f` after four
rewrites of that body:

* every application of a constant `cᵢ` is unfolded and beta-reduced, so a function defined
  as a wrapper around a function over named operations is read at its field operations;
* a projection `Prod.fst`, `Prod.snd` (or `.1`, `.2`) of a `Prod.mk` is reduced to the
  component, a projection of a `let` is moved into its body, and a `let` whose variable is
  unused is dropped, so a function returning one component of a tuple-valued function is
  read without its other components;
* an application of `+`, `-`, `*` (as `HAdd.hAdd`, `HSub.hSub`, `HMul.hMul`, `Add.add`,
  `Sub.sub`, `Mul.mul`) or of `-` (as `Neg.neg`) at a type `ZMod n`, with `n` evaluated to a
  literal at least `2`, is read as the call of the tagged head `FieldTag.fieldHead m n` of
  the method `m`, the head `<method>#p<modulus>` of the builtin table `Hax.hax64Builtins`;
* a numeral `k : ZMod n` is read as the integer literal `.lit (.int (k % n))`.

Values of `ZMod p` are encoded as the integer of their canonical representative
(`HaxEnc (ZMod p)`, `enc x = .int x.val`), the encoding `Hax.hax64Builtins` reads at a modulus
below `2^64`. The leaf lemmas `hax64Builtins_zmod_add`, `_sub`, `_mul`, `_neg` state that the
table answers a tagged head on encoded elements by the encoding of the field operation.

`ImpExpr.toTExpr Γ e` lifts a literal to a typed expression whose erasure is `e`
(`erase_toTExpr`), typing a narrow field call as one `u64` word.

## Main definitions

* `reifyField%` — the reifier
* `instHaxEncZMod` — the encoding of `ZMod p`
* `Hax.ImpExpr.toTExpr` — the lift to typed expressions
* `mulAddLean`, `mulAddImp` — `x * y + x` over BabyBear, and its literal
* `affineLean`, `affineImp` — a wrapper around a function over named operations, with a
  numeral, a negation and a difference, and its literal

## Main results

* `hax64Builtins_zmod_add`, `hax64Builtins_zmod_sub`, `hax64Builtins_zmod_mul`,
  `hax64Builtins_zmod_neg` — the table answers the tagged heads on encoded elements
* `hax64Builtins_mul_babyBear` and its siblings — the same at the BabyBear heads, in the
  form the ascent generator indexes
* `erase_toTExpr` — the erasure of the lift is the literal
* `mulAddImp_eq`, `affineImp_eq` — the literals of the tests, stated in full
* `mulAddImp_toTExpr` — the lift of `mulAddImp`, every node a `u64` word
* `mulAdd_fnCorres` — the literal denotes `mulAddLean` under `Hax.hax64Builtins`
-/

@[expose] public section

set_option autoImplicit false

meta section

open Lean Meta Elab Term

namespace CatCrypt.Hax.ReifyField

/-- The modulus `n` of a type `ZMod n`, with `n` evaluated to a literal at least `2`. -/
def zmodModulus? (ty : Expr) : MetaM (Option Nat) := do
  let ty ← whnfR (← instantiateMVars ty)
  unless ty.isAppOfArity ``ZMod 1 do return none
  let n := ty.appArg!
  let k? ← match ← (evalNat n).run with
    | some k => pure (some k)
    | none => pure (← whnf n).rawNatLit?
  match k? with
  | some k => if 2 ≤ k then return some k else return none
  | none => return none

/-- The binary operations read as field methods, with their arity and method. -/
def binOps : List (Name × Nat × _root_.Hax.FieldTag.FieldMethod) :=
  [(``HAdd.hAdd, 6, .add), (``HSub.hSub, 6, .sub), (``HMul.hMul, 6, .mul),
   (``Add.add, 4, .add), (``Sub.sub, 4, .sub), (``Mul.mul, 4, .mul)]

/-- An application of a field operation at `ZMod n`: its method, the modulus `n`, the type
    `ZMod n` and the operands. -/
def fieldOp? (e : Expr) :
    MetaM (Option (_root_.Hax.FieldTag.FieldMethod × Nat × Expr × Array Expr)) := do
  for (c, k, m) in binOps do
    if e.isAppOfArity c k then
      let ty := e.getArg! 0
      if let some n ← zmodModulus? ty then
        return some (m, n, ty, #[e.getArg! (k - 2), e.getArg! (k - 1)])
  if e.isAppOfArity ``Neg.neg 3 then
    let ty := e.getArg! 0
    if let some n ← zmodModulus? ty then
      return some (.neg, n, ty, #[e.getArg! 2])
  return none

/-- A numeral `k : ZMod n`, as `k % n`. -/
def fieldNumeral? (e : Expr) : MetaM (Option Nat) := do
  unless e.isAppOfArity ``OfNat.ofNat 3 do return none
  let some k := (e.getArg! 1).rawNatLit? | return none
  let some n ← zmodModulus? (e.getArg! 0) | return none
  return some (k % n)

/-- The body `e` with every application of a constant of `cs` unfolded and beta-reduced. -/
def unfoldListed (cs : Array Name) (e : Expr) : MetaM Expr := do
  if cs.isEmpty then return e
  let e ← Meta.transform e (pre := fun t => do
    if let .const c _ := t.getAppFn then
      if cs.contains c then
        if let some t' ← unfoldDefinition? t then
          return .visit t'.headBeta
    return .continue)
  Core.betaReduce e

/-- The projection `i` of `x`: `x.i` when `ts` is `none`, and the application of the
    projection function `f` at the types `α`, `β` when `ts` is `some (f, α, β)`. -/
def mkProjAt (i : Nat) (ts : Option (Expr × Expr × Expr)) (x : Expr) : Expr :=
  match ts with
  | none => .proj ``Prod i x
  | some (f, α, β) => mkApp3 f α β x

/-- The component `i` (`0` for the first, `1` for the second) of `x`, with the projection
    reduced: the component of a `Prod.mk` is its argument, the projection of a `let` is the
    `let` of the projection of its body, dropped when that body does not use its variable,
    and any other argument keeps the projection `mkProjAt i ts x`. -/
partial def pushProj (i : Nat) (ts : Option (Expr × Expr × Expr)) (x : Expr) : Expr :=
  match x with
  | .mdata _ x => pushProj i ts x
  | .letE n t v b nd =>
    let ts' := ts.map fun (f, α, β) => (f, α.liftLooseBVars 0 1, β.liftLooseBVars 0 1)
    let b' := pushProj i ts' b
    if b'.hasLooseBVar 0 then .letE n t v b' nd else b'.lowerLooseBVars 1 1
  | _ =>
    if x.isAppOfArity ``Prod.mk 4 then x.getArg! (2 + i) else mkProjAt i ts x

/-- The projection `Prod.fst x`, `Prod.snd x`, `x.1` or `x.2`: its index, the form
    `mkProjAt` rebuilds it from, and its argument. -/
def projOf? (e : Expr) : Option (Nat × Option (Expr × Expr × Expr) × Expr) :=
  match e with
  | .proj ``Prod i x => some (i, none, x)
  | _ =>
    if e.isAppOfArity ``Prod.fst 3 then
      some (0, some (e.getAppFn, e.getArg! 0, e.getArg! 1), e.appArg!)
    else if e.isAppOfArity ``Prod.snd 3 then
      some (1, some (e.getAppFn, e.getArg! 0, e.getArg! 1), e.appArg!)
    else none

/-- The expression `e` with every projection of a `Prod.mk` reduced to the component, every
    projection of a `let` moved into its body, and every `let` whose variable is unused
    dropped. -/
partial def reduceProjs (e : Expr) : Expr :=
  match e with
  | .app .. =>
    let e' := mkAppN (reduceProjs e.getAppFn) (e.getAppArgs.map reduceProjs)
    match projOf? e' with
    | some (i, ts, x) => pushProj i ts x
    | none => e'
  | .proj s i x =>
    let e' := Expr.proj s i (reduceProjs x)
    match projOf? e' with
    | some (i, ts, x) => pushProj i ts x
    | none => e'
  | .letE n t v b nd =>
    let b' := reduceProjs b
    if b'.hasLooseBVar 0 then .letE n t (reduceProjs v) b' nd else b'.lowerLooseBVars 1 1
  | .lam n t b bi => .lam n t (reduceProjs b) bi
  | .mdata m x => .mdata m (reduceProjs x)
  | _ => e

/-- The field operations of `e`, without repetition: method, modulus and the type
    `ZMod n`. -/
def collectOps (e : Expr) :
    MetaM (Array (_root_.Hax.FieldTag.FieldMethod × Nat × Expr)) := do
  let r ← IO.mkRef (#[] : Array (_root_.Hax.FieldTag.FieldMethod × Nat × Expr))
  discard <| Meta.transform e (pre := fun t => do
    if let some (m, n, ty, _) ← fieldOp? t then
      unless (← r.get).any (fun (m', n', _) => m' == m && n' == n) do
        r.modify (·.push (m, n, ty))
    return .continue)
  r.get

/-- Run `k` with one local operation per entry of `ops`, of type `ty → ty → ty` for a
    method with two arguments and `ty → ty` for one; `k` receives the free variables and
    the tagged heads. -/
partial def withOps {α : Type}
    (ops : List (_root_.Hax.FieldTag.FieldMethod × Nat × Expr))
    (k : List (Expr × _root_.Hax.FieldTag.FieldMethod × Nat × String) → MetaM α) :
    MetaM α :=
  match ops with
  | [] => k []
  | (m, n, ty) :: rest => do
    let head := _root_.Hax.FieldTag.fieldHead m n
    let fty ← if m.binary then do mkArrow ty (← mkArrow ty ty) else mkArrow ty ty
    withLocalDeclD (Name.mkSimple head) fty fun x =>
      withOps rest fun xs => k ((x, m, n, head) :: xs)

/-- The body `e` with every field operation replaced by its local operation and every
    numeral `k : ZMod n` replaced by the integer numeral `k % n`. -/
def replaceOps (ops : List (Expr × _root_.Hax.FieldTag.FieldMethod × Nat × String))
    (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun t => do
    if let some (m, n, _, args) ← fieldOp? t then
      if let some (x, _) := ops.find? (fun (_, m', n', _) => m' == m && n' == n) then
        return .visit (mkAppN x args)
    if let some r ← fieldNumeral? t then
      return .done (← mkNumeral (mkConst ``Int) r)
    return .continue)

/-- The literal of the definition `c` over its last `n` explicit parameters, the binders
    before them read as operations, the constants of `us` unfolded, and the field
    operations at `ZMod n` read as tagged heads. -/
def reifyFieldConst (c : Name) (n : Nat) (us : Array Name) : MetaM Expr := do
  let info ← getConstInfo c
  let some v := info.value? | throwError "reifyField: {c} has no body"
  lambdaTelescope v fun xs body => do
    let mut rest : Array Expr := #[]
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.binderInfo.isInstImplicit then continue
      if (← whnfR d.type).isSort then continue
      rest := rest.push x
    unless n ≤ rest.size do
      throwError "reifyField: {c} has {rest.size} parameters, fewer than {n}"
    let nOps := rest.size - n
    let mut ctx : CatCrypt.Hax.ReifyImp.Ctx := {}
    let mut used : List String := []
    for x in rest, i in [0:rest.size] do
      let s := CatCrypt.Hax.ReifyImp.freshName used
        (CatCrypt.Hax.ReifyImp.nameStr (← x.fvarId!.getUserName))
      used := s :: used
      if i < nOps then
        ctx := { ctx with ops := ctx.ops.insert x.fvarId! s }
      else
        ctx := { ctx with vars := ctx.vars.insert x.fvarId! s }
    let body := reduceProjs (← unfoldListed us body)
    let fops ← collectOps body
    withOps fops.toList fun ops => do
      let body ← replaceOps ops body
      let mut ctx := ctx
      for (x, _, _, h) in ops do
        ctx := { ctx with ops := ctx.ops.insert x.fvarId! h }
      (CatCrypt.Hax.ReifyImp.reify ctx body).run' (used ++ ops.map (·.2.2.2))

/-- `reifyField% n f unfolding c₁ … cₖ` is the `ImpExpr` literal of the body of `f` over its
    last `n` explicit parameters, as `reifyImp%`, with the constants `cᵢ` unfolded, the
    projections of tuples and of `let`s reduced and unused `let`s dropped (`reduceProjs`), the
    operations `+`, `-`, `*` and negation at `ZMod p` read as the calls of the tagged heads
    `FieldTag.fieldHead m p`, and a numeral `k : ZMod p` read as the literal `k % p`. Without
    `n`, every explicit binder is a parameter. -/
syntax (name := reifyFieldStx) "reifyField% " (num)? ident (" unfolding " ident+)? : term

@[term_elab reifyFieldStx]
def elabReifyField : TermElab := fun stx _ => do
  match stx with
  | `(reifyField% $[$n?]? $f:ident $[unfolding $us*]?) =>
    let c ← realizeGlobalConstNoOverloadWithInfo f
    let us ← match us with
      | some us => us.mapM fun u => realizeGlobalConstNoOverloadWithInfo u
      | none => pure #[]
    let n ← match n? with
      | some n => pure n.getNat
      | none => do
        let v := (← getConstInfo c).value?.getD (mkConst ``Unit)
        lambdaTelescope v fun xs _ => do
          let ys ← xs.filterM fun x => do
            let d ← x.fvarId!.getDecl
            return !d.binderInfo.isInstImplicit && !(← whnfR d.type).isSort
          return ys.size
    reifyFieldConst c n us
  | _ => throwUnsupportedSyntax

end CatCrypt.Hax.ReifyField

end

/-! ## The encoding of `ZMod p` -/

namespace CatCrypt.Hax.ReifyField

open _root_.Hax _root_.Hax.Ascent _root_.Hax.FieldTag

/-- The encoding of an element of `ZMod p`: the integer of its canonical representative. -/
instance instHaxEncZMod {p : ℕ} : HaxEnc (ZMod p) := ⟨fun x => .int x.val⟩

theorem enc_zmod {p : ℕ} (x : ZMod p) : enc x = .int x.val := rfl

instance {p : ℕ} : HaxEnc.Plain (ZMod p) := ⟨fun _ => rfl⟩

instance {p : ℕ} [NeZero p] : HaxEnc.Inj (ZMod p) :=
  ⟨fun _ _ h => ZMod.val_injective _ (by exact_mod_cast Value.int.inj h)⟩

/-! ## The table at the tagged heads -/

section Leaves

variable {p : ℕ} [NeZero p] {f : String}

/-- At a tagged head of a method with two arguments at a modulus below `2^64`, the table
    `hax64Builtins` on encoded elements is the integer of `fieldVal`. -/
theorem hax64Builtins_zmod_binary {m : FieldMethod} (ht : fieldTag? f = some (m, p))
    (hp : p < 2 ^ 64) (hm : m.binary = true) (x y : ZMod p) :
    hax64Builtins f [enc x, enc y] = some (.int (fieldVal m p x.val y.val : ℕ)) := by
  have h := hax64Builtins_fieldArgs ht hp x.val y.val
  simp only [fieldArgs, hm, if_true] at h
  rw [enc_zmod, enc_zmod, h, fieldArm, if_pos ⟨ZMod.val_lt x, fun _ => ZMod.val_lt y⟩]

/-- At a tagged head of a method with one argument at a modulus below `2^64`, the table
    `hax64Builtins` on an encoded element is the integer of `fieldVal`. -/
theorem hax64Builtins_zmod_unary {m : FieldMethod} (ht : fieldTag? f = some (m, p))
    (hp : p < 2 ^ 64) (hm : m.binary = false) (x : ZMod p) :
    hax64Builtins f [enc x] = some (.int (fieldVal m p x.val 0 : ℕ)) := by
  have h := hax64Builtins_fieldArgs ht hp x.val 0
  simp only [fieldArgs, hm, Bool.false_eq_true, if_false] at h
  rw [enc_zmod, h, fieldArm, if_pos ⟨ZMod.val_lt x, fun h => absurd h (by simp [hm])⟩]

/-- The table answers the tagged head of `add` by the encoding of the sum. -/
theorem hax64Builtins_zmod_add (ht : fieldTag? f = some (.add, p)) (hp : p < 2 ^ 64)
    (x y : ZMod p) : hax64Builtins f [enc x, enc y] = some (enc (x + y)) := by
  rw [hax64Builtins_zmod_binary ht hp rfl, enc_zmod, ZMod.val_add]
  rfl

/-- The table answers the tagged head of `mul` by the encoding of the product. -/
theorem hax64Builtins_zmod_mul (ht : fieldTag? f = some (.mul, p)) (hp : p < 2 ^ 64)
    (x y : ZMod p) : hax64Builtins f [enc x, enc y] = some (enc (x * y)) := by
  rw [hax64Builtins_zmod_binary ht hp rfl, enc_zmod, ZMod.val_mul]
  rfl

/-- The canonical representative of `x - y` is `(x.val + p - y.val) % p`. -/
theorem val_sub_eq (x y : ZMod p) : (x - y).val = (x.val + p - y.val) % p := by
  have hy := (ZMod.val_lt y).le
  have hc : ((x.val + p - y.val : ℕ) : ZMod p) = x - y := by
    rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val, add_zero]
  rw [← hc, ZMod.val_natCast]

/-- The canonical representative of `-x` is `(p - x.val) % p`. -/
theorem val_neg_eq (x : ZMod p) : (-x).val = (p - x.val) % p := by
  have hx := (ZMod.val_lt x).le
  have hc : ((p - x.val : ℕ) : ZMod p) = -x := by
    rw [Nat.cast_sub hx, ZMod.natCast_self, ZMod.natCast_zmod_val, zero_sub]
  rw [← hc, ZMod.val_natCast]

/-- The table answers the tagged head of `sub` by the encoding of the difference. -/
theorem hax64Builtins_zmod_sub (ht : fieldTag? f = some (.sub, p)) (hp : p < 2 ^ 64)
    (x y : ZMod p) : hax64Builtins f [enc x, enc y] = some (enc (x - y)) := by
  rw [hax64Builtins_zmod_binary ht hp rfl, enc_zmod, val_sub_eq]
  rfl

/-- The table answers the tagged head of `neg` by the encoding of the negation. -/
theorem hax64Builtins_zmod_neg (ht : fieldTag? f = some (.neg, p)) (hp : p < 2 ^ 64)
    (x : ZMod p) : hax64Builtins f [enc x] = some (enc (-x)) := by
  rw [hax64Builtins_zmod_unary ht hp rfl, enc_zmod, val_neg_eq]
  rfl

end Leaves

end CatCrypt.Hax.ReifyField

/-! ## The lift to typed expressions -/

namespace Hax

/-- The type of a call of the head `f`: at a tagged head at a modulus below `2^64` one `u64`
    word, at a wider modulus an array of `fieldLimbs p` words, and `.unknown` at every other
    head. -/
def fieldCallTy (f : String) : ImpType :=
  match FieldTag.fieldTag? f with
  | some (_, p) => if p < 2 ^ 64 then .uint .w64 else .array (.uint .w64) (FieldTag.fieldLimbs p)
  | none => .unknown

/-- The type of a literal: an integer literal is one `u64` word. -/
def litTy : ImpLit → ImpType
  | .bool _ => .bool
  | .int _ => .uint .w64
  | .unit => .unit
  | .uintLit w _ => .uint w
  | .sintLit w _ => .sint w

/-- The type of the component `i` of a value of type `t`. -/
def projTy (t : ImpType) (i : Nat) : ImpType :=
  match t with
  | .tuple ts => ts.getD i .unknown
  | _ => .unknown

mutual

/-- **The lift of an `ImpExpr` to a typed expression**, under the types `Γ` of its free
    variables: each node carries the type of a literal (`litTy`), of a variable in `Γ` or of
    the `let` binding it, of a field call (`fieldCallTy`), of the components of a tuple, of
    a projection, of a `let` body or of a branch, and `.unknown` otherwise. The variables
    bound by a closure or a loop are removed from `Γ` in its body, and match arms are typed
    under the empty environment. A type ascription has no typed counterpart: the lift is
    `none` on an expression containing one. -/
def ImpExpr.toTExpr (Γ : List (String × ImpType)) : ImpExpr → Option TExpr
  | .lit v => some ⟨.lit v, litTy v⟩
  | .var x => some ⟨.var x, (Γ.lookup x).getD .unknown⟩
  | .letBind x v b => do
      let v' ← v.toTExpr Γ
      let b' ← b.toTExpr ((x, v'.ty) :: Γ)
      some ⟨.letBind x v' b', b'.ty⟩
  | .lam ps b => do
      let b' ← b.toTExpr (Γ.filter fun q => !ps.contains q.1)
      some ⟨.lam ps b', .unknown⟩
  | .app f args => do
      let as ← ImpExpr.toTExprList Γ args
      some ⟨.app f as, fieldCallTy f⟩
  | .tuple es => do
      let as ← ImpExpr.toTExprList Γ es
      some ⟨.tuple as, .tuple (as.map TExpr.ty)⟩
  | .proj e i => do
      let e' ← e.toTExpr Γ
      some ⟨.proj e' i, projTy e'.ty i⟩
  | .ifThenElse c t e => do
      let c' ← c.toTExpr Γ
      let t' ← t.toTExpr Γ
      let e' ← e.toTExpr Γ
      some ⟨.ifThenElse c' t' e', t'.ty⟩
  | .match_ s arms => do
      let s' ← s.toTExpr Γ
      let as ← ImpExpr.toTExprArms arms
      some ⟨.match_ s' as, .unknown⟩
  | .unitVal => some ⟨.unitVal, .unit⟩
  | .seq e1 e2 => do
      let a ← e1.toTExpr Γ
      let b ← e2.toTExpr Γ
      some ⟨.seq a b, b.ty⟩
  | .borrow e => do
      let a ← e.toTExpr Γ
      some ⟨.borrow a, .unknown⟩
  | .deref e => do
      let a ← e.toTExpr Γ
      some ⟨.deref a, .unknown⟩
  | .assign x e => do
      let a ← e.toTExpr Γ
      some ⟨.assign x a, .unit⟩
  | .forLoop x lo hi b => do
      let l ← lo.toTExpr Γ
      let h ← hi.toTExpr Γ
      let b' ← b.toTExpr (Γ.filter fun q => q.1 != x)
      some ⟨.forLoop x l h b', .unknown⟩
  | .forLoopRev x lo hi b => do
      let l ← lo.toTExpr Γ
      let h ← hi.toTExpr Γ
      let b' ← b.toTExpr (Γ.filter fun q => q.1 != x)
      some ⟨.forLoopRev x l h b', .unknown⟩
  | .whileLoop c b => do
      let c' ← c.toTExpr Γ
      let b' ← b.toTExpr Γ
      some ⟨.whileLoop c' b', .unknown⟩
  | .break_ none => some ⟨.break_ none, .unknown⟩
  | .break_ (some e) => do
      let a ← e.toTExpr Γ
      some ⟨.break_ (some a), .unknown⟩
  | .continue_ => some ⟨.continue_, .unknown⟩
  | .earlyReturn e => do
      let a ← e.toTExpr Γ
      some ⟨.earlyReturn a, .unknown⟩
  | .questionMark e => do
      let a ← e.toTExpr Γ
      some ⟨.questionMark a, .unknown⟩
  | .forFold x lo hi b => do
      let l ← lo.toTExpr Γ
      let h ← hi.toTExpr Γ
      let b' ← b.toTExpr (Γ.filter fun q => q.1 != x)
      some ⟨.forFold x l h b', .unknown⟩
  | .forFoldRev x lo hi b => do
      let l ← lo.toTExpr Γ
      let h ← hi.toTExpr Γ
      let b' ← b.toTExpr (Γ.filter fun q => q.1 != x)
      some ⟨.forFoldRev x l h b', .unknown⟩
  | .whileFold c b => do
      let c' ← c.toTExpr Γ
      let b' ← b.toTExpr Γ
      some ⟨.whileFold c' b', .unknown⟩
  | .forFoldReturn x lo hi b => do
      let l ← lo.toTExpr Γ
      let h ← hi.toTExpr Γ
      let b' ← b.toTExpr (Γ.filter fun q => q.1 != x)
      some ⟨.forFoldReturn x l h b', .unknown⟩
  | .forFoldRevReturn x lo hi b => do
      let l ← lo.toTExpr Γ
      let h ← hi.toTExpr Γ
      let b' ← b.toTExpr (Γ.filter fun q => q.1 != x)
      some ⟨.forFoldRevReturn x l h b', .unknown⟩
  | .whileFoldReturn c b => do
      let c' ← c.toTExpr Γ
      let b' ← b.toTExpr Γ
      some ⟨.whileFoldReturn c' b', .unknown⟩
  | .cfBreak e => do
      let a ← e.toTExpr Γ
      some ⟨.cfBreak a, .unknown⟩
  | .cfContinue e => do
      let a ← e.toTExpr Γ
      some ⟨.cfContinue a, .unknown⟩
  | .cfBreakContinue e => do
      let a ← e.toTExpr Γ
      some ⟨.cfBreakContinue a, .unknown⟩
  | .typeAscription _ _ => none

/-- The lift of a list of expressions, each under `Γ`. -/
def ImpExpr.toTExprList (Γ : List (String × ImpType)) : List ImpExpr → Option (List TExpr)
  | [] => some []
  | e :: es => do
      let a ← e.toTExpr Γ
      let as ← ImpExpr.toTExprList Γ es
      some (a :: as)

/-- The lift of the arms of a match, each under the empty environment. -/
def ImpExpr.toTExprArms : List (ImpPat × ImpExpr) → Option (List (ImpPat × TExpr))
  | [] => some []
  | (q, e) :: rest => do
      let a ← e.toTExpr []
      let as ← ImpExpr.toTExprArms rest
      some ((q, a) :: as)

end

set_option hygiene false in
/-- One case of `ImpExpr.erase_toTExpr`: unfold the lift in `h`, take the erasure of each
    lifted subterm from the recursive statements, and rewrite the erasure. -/
local macro "erase_lift_case" : tactic => `(tactic| (
  simp only [ImpExpr.toTExpr, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq, reduceCtorEq] at h
  all_goals
    repeat' (first
      | obtain ⟨_, hh, h⟩ := h
        first
          | have := ImpExpr.erase_toTExpr hh
          | have := ImpExpr.eraseList_toTExprList hh
          | have := ImpExpr.eraseArms_toTExprArms hh
        clear hh)
    subst h
    simp_all only [TExpr.erase, TExpr.eraseList_eq, TExpr.eraseArms_eq]))

mutual

/-- **The erasure of the lift is the expression.** -/
theorem ImpExpr.erase_toTExpr : ∀ {Γ : List (String × ImpType)} {e : ImpExpr} {te : TExpr},
    e.toTExpr Γ = some te → te.erase = e
  | Γ, e, te, h => by
    cases e
    case break_ o => cases o <;> erase_lift_case
    all_goals erase_lift_case

/-- The erasure of the lift of a list is the list. -/
theorem ImpExpr.eraseList_toTExprList : ∀ {Γ : List (String × ImpType)} {es : List ImpExpr}
    {tes : List TExpr}, ImpExpr.toTExprList Γ es = some tes → tes.map TExpr.erase = es
  | _, [], _, h => by simp only [ImpExpr.toTExprList, Option.some.injEq] at h; subst h; rfl
  | Γ, e :: es, tes, h => by
    simp only [ImpExpr.toTExprList, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨a, ha, as, has, rfl⟩ := h
    rw [List.map_cons, ImpExpr.erase_toTExpr ha, ImpExpr.eraseList_toTExprList has]

/-- The erasure of the lift of the arms of a match is the arms. -/
theorem ImpExpr.eraseArms_toTExprArms : ∀ {arms : List (ImpPat × ImpExpr)}
    {tas : List (ImpPat × TExpr)}, ImpExpr.toTExprArms arms = some tas →
    tas.map (fun (q, e) => (q, e.erase)) = arms
  | [], _, h => by simp only [ImpExpr.toTExprArms, Option.some.injEq] at h; subst h; rfl
  | (q, e) :: rest, tas, h => by
    simp only [ImpExpr.toTExprArms, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨a, ha, as, has, rfl⟩ := h
    rw [List.map_cons, ImpExpr.eraseArms_toTExprArms has]
    dsimp only
    rw [ImpExpr.erase_toTExpr ha]

end

end Hax

/-! ## Tests over BabyBear -/

namespace CatCrypt.Hax.ReifyField

open _root_.Hax _root_.Hax.Ascent _root_.Hax.FieldTag

/-- `x * y + x` over BabyBear, `p = 2013265921`. -/
def mulAddLean (x y : ZMod 2013265921) : ZMod 2013265921 := x * y + x

/-- The literal of `mulAddLean` over the parameters `x`, `y`. -/
def mulAddImp : ImpExpr := reifyField% mulAddLean

theorem mulAddImp_eq : mulAddImp =
    .letBind "t" (.app "mul#p2013265921" [.var "x", .var "y"])
    (.letBind "t_1" (.app "add#p2013265921" [.var "t", .var "x"]) (.var "t_1")) := rfl

/-- The table answers the BabyBear head of `mul` by the encoding of the product. -/
theorem hax64Builtins_mul_babyBear (x y : ZMod 2013265921) :
    hax64Builtins "mul#p2013265921" [enc x, enc y] = some (enc (x * y)) :=
  hax64Builtins_zmod_mul (by decide) (by norm_num) x y

/-- The table answers the BabyBear head of `add` by the encoding of the sum. -/
theorem hax64Builtins_add_babyBear (x y : ZMod 2013265921) :
    hax64Builtins "add#p2013265921" [enc x, enc y] = some (enc (x + y)) :=
  hax64Builtins_zmod_add (by decide) (by norm_num) x y

/-- The table answers the BabyBear head of `sub` by the encoding of the difference. -/
theorem hax64Builtins_sub_babyBear (x y : ZMod 2013265921) :
    hax64Builtins "sub#p2013265921" [enc x, enc y] = some (enc (x - y)) :=
  hax64Builtins_zmod_sub (by decide) (by norm_num) x y

/-- The table answers the BabyBear head of `neg` by the encoding of the negation. -/
theorem hax64Builtins_neg_babyBear (x : ZMod 2013265921) :
    hax64Builtins "neg#p2013265921" [enc x] = some (enc (-x)) :=
  hax64Builtins_zmod_neg (by decide) (by norm_num) x

/-- From the entry environment binding `x` and `y`, the literal `mulAddImp` returns the
    encoding of `mulAddLean` under the table `hax64Builtins`. -/
theorem mulAdd_fnCorres :
    FnCorres hax64Builtins mulAddImp (A := ZMod 2013265921 × ZMod 2013265921 × Unit)
      (fun a => bindParams [("x", enc a.1), ("y", enc a.2.1)]) (fun _ => True)
      (fun a => mulAddLean a.1 a.2.1) := by
  ascend_reified mulAddLean using [hax64Builtins_mul_babyBear, hax64Builtins_add_babyBear]

/-- A function over named operations: `add (mul c x) c`. -/
def affineOps {α : Type} (mul add : α → α → α) (c x : α) : α := add (mul c x) c

/-- `affineOps` at the BabyBear operations and the numeral `2013265924`, which is `3` in
    BabyBear, minus `-x`. -/
def affineLean (x : ZMod 2013265921) : ZMod 2013265921 :=
  affineOps (· * ·) (· + ·) 2013265924 x - -x

/-- The literal of `affineLean`, with `affineOps` unfolded. -/
def affineImp : ImpExpr := reifyField% affineLean unfolding affineOps

/-- The literal of `affineLean`: the numeral `2013265924` read as `3`, the operations of
    `affineOps` read at the tagged heads of `mul` and `add`, and the negation and the
    difference at the heads of `neg` and `sub`. -/
theorem affineImp_eq : affineImp =
    .letBind "t" (.lit (.int 3))
    (.letBind "t_1" (.app "mul#p2013265921" [.var "t", .var "x"])
    (.letBind "t_2" (.lit (.int 3))
    (.letBind "t_3" (.app "add#p2013265921" [.var "t_1", .var "t_2"])
    (.letBind "t_4" (.app "neg#p2013265921" [.var "x"])
    (.letBind "t_5" (.app "sub#p2013265921" [.var "t_3", .var "t_4"]) (.var "t_5")))))) :=
  rfl

/-- The lift of `mulAddImp` from `x` and `y` typed as `u64` words: every node is a `u64`
    word. -/
theorem mulAddImp_toTExpr :
    mulAddImp.toTExpr [("x", .uint .w64), ("y", .uint .w64)] = some
      ⟨.letBind "t" ⟨.app "mul#p2013265921"
          [⟨.var "x", .uint .w64⟩, ⟨.var "y", .uint .w64⟩], .uint .w64⟩
        ⟨.letBind "t_1" ⟨.app "add#p2013265921"
            [⟨.var "t", .uint .w64⟩, ⟨.var "x", .uint .w64⟩], .uint .w64⟩
          ⟨.var "t_1", .uint .w64⟩, .uint .w64⟩, .uint .w64⟩ := by
  rfl

end CatCrypt.Hax.ReifyField
