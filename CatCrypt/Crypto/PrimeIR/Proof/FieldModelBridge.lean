/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.PrimeIR.Proof.FieldModel
public import CatCrypt.Crypto.PrimeIR.Proof.Fp256Mont
public import CatCrypt.Hax.PrimeirNames
public import HaxLean.Phase.InlineLocalClosures

/-!
# From a field model to the reference builtins

A function of the `primeir-hax` library is extracted twice: as a surface definition generic in
`[Primeir.Field F]` and as a term `f_texpr` that the compiler reads under the reference
interpreter `denoteSpine` with a table of builtins (`primeirBuiltins p`, or
`defaultFieldTable.builtins p`). This file relates the two readings for the straight-line
field fragment along a field model `M : FieldModel F (ZMod p)`.

A field element `x : F` is represented in the interpreter by the value
`.int ((M.val x).val : Int)`, the canonical representative of the element it stands for; the
side condition on the surface arguments is the model's validity predicate `M.Valid`.

The fragment is given by syntax: an `FTerm` is a term over variables built from the six field
operations `add`, `sub`, `mul`, `neg`, `square`, `double` and the constants `ZERO`, `ONE`; an
`FProg` is a sequence of let-bindings of terms ending in a term. Each has a surface reading
`eval` through the methods of `Primeir.Field F` and an `ImpExpr` reading `toImp` with the call
heads `haxpipeT` emits. The builtins are required to compute the field operations on integer
representatives (`FieldOps`) and, for programs that use a constant, the constants
(`FieldConsts`); `primeirBuiltins p` satisfies `FieldOps`, and `defaultFieldTable.builtins p`
satisfies both.

## Main definitions

* `FieldOps`, `FieldConsts` — a builtin table computes the field operations and constants on
  integer representatives modulo `p`.
* `FTerm`, `FProg` — straight-line field terms and programs; `eval` and `toImp` are their
  surface and interpreter readings.
* `EnvAgree` — an environment binds the variables of a list to the canonical representatives
  of valid surface values.
* `feMulAddProg` — the program of `Primeir.fe_mul_add`.

## Main results

* `FTerm.toImp_run` — under `EnvAgree`, the interpreter returns the representative of the
  surface value of a term, and the surface value is valid.
* `FProg.toImp_run` — the same for a program under `denoteSpine`, the environment extended by
  each binding.
* `fe_mul_add_bridge` — for every model `M : FieldModel F (ZMod p)` and builtins with
  `FieldOps`, the reference reading of `fe_mul_add_texpr` on the representatives of valid
  `a`, `b`, `c` returns the representative of `fe_mul_add a b c`, which is valid.
* `fe_mul_add_bridge_fp256Mont` — the instance at `fp256MontCtModel` and
  `primeirBuiltins P256`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.PrimeIR.FieldModelBridge

open _root_.Hax (ImpExpr Value Env Builtins denote' denoteArgs')
open _root_.Hax.InlineLocalClosures (denoteSpine)
open CatCrypt.Hax (primeirBuiltins)
open CatCrypt.Hax.PrimeirNames (defaultFieldTable)

/-! ## 1. Builtins that compute the field operations -/

/-- A builtin table computes the six field operations on integer representatives, reduced
    modulo `p` by `Int.emod`, under the bare heads `haxpipeT` emits. -/
structure FieldOps (bi : Builtins) (p : Nat) : Prop where
  add : ∀ a b : Int, bi "add" [.int a, .int b] = some (.int ((a + b) % (p : Int)))
  sub : ∀ a b : Int, bi "sub" [.int a, .int b] = some (.int ((a - b) % (p : Int)))
  mul : ∀ a b : Int, bi "mul" [.int a, .int b] = some (.int ((a * b) % (p : Int)))
  neg : ∀ a : Int, bi "neg" [.int a] = some (.int ((-a) % (p : Int)))
  square : ∀ a : Int, bi "square" [.int a] = some (.int ((a * a) % (p : Int)))
  double : ∀ a : Int, bi "double" [.int a] = some (.int ((a + a) % (p : Int)))

/-- A builtin table computes the constants `ZERO` and `ONE` under the heads `haxpipeT` emits
    for the associated constants of `Field`. -/
structure FieldConsts (bi : Builtins) (p : Nat) : Prop where
  zero : bi "::clsitem::Field::ZERO::F" [] = some (.int 0)
  one : bi "::clsitem::Field::ONE::F" [] = some (.int (1 % (p : Int)))

/-- `primeirBuiltins p` computes the field operations. -/
theorem primeirBuiltins_fieldOps (p : Nat) : FieldOps (primeirBuiltins p) p :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- The builtins of the default field table compute the field operations. -/
theorem defaultFieldTable_fieldOps (p : Nat) : FieldOps (defaultFieldTable.builtins p) p :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- The builtins of the default field table compute the constants. -/
theorem defaultFieldTable_fieldConsts (p : Nat) :
    FieldConsts (defaultFieldTable.builtins p) p :=
  ⟨rfl, rfl⟩

/-! ## 2. Straight-line field terms and programs -/

/-- A term over variables built from the field operations and constants. -/
inductive FTerm where
  | var (x : String)
  | zero
  | one
  | add (a b : FTerm)
  | sub (a b : FTerm)
  | mul (a b : FTerm)
  | neg (a : FTerm)
  | square (a : FTerm)
  | double (a : FTerm)
  deriving Repr

/-- A sequence of let-bindings of terms ending in a term. -/
inductive FProg where
  | ret (t : FTerm)
  | bind (x : String) (t : FTerm) (k : FProg)
  deriving Repr

/-- The `ImpExpr` of a term, with the call heads `haxpipeT` emits. -/
def FTerm.toImp : FTerm → ImpExpr
  | .var x => .var x
  | .zero => .app "::clsitem::Field::ZERO::F" []
  | .one => .app "::clsitem::Field::ONE::F" []
  | .add a b => .app "add" [a.toImp, b.toImp]
  | .sub a b => .app "sub" [a.toImp, b.toImp]
  | .mul a b => .app "mul" [a.toImp, b.toImp]
  | .neg a => .app "neg" [a.toImp]
  | .square a => .app "square" [a.toImp]
  | .double a => .app "double" [a.toImp]

/-- The `ImpExpr` of a program: a chain of `letBind`. -/
def FProg.toImp : FProg → ImpExpr
  | .ret t => t.toImp
  | .bind x t k => .letBind x t.toImp k.toImp

/-- A term contains a constant. -/
def FTerm.usesConst : FTerm → Bool
  | .var _ => false
  | .zero | .one => true
  | .add a b | .sub a b | .mul a b => a.usesConst || b.usesConst
  | .neg a | .square a | .double a => a.usesConst

/-- A program contains a constant. -/
def FProg.usesConst : FProg → Bool
  | .ret t => t.usesConst
  | .bind _ t k => t.usesConst || k.usesConst

/-- The variables of a term belong to `xs`. -/
def FTerm.scoped (xs : List String) : FTerm → Bool
  | .var x => xs.contains x
  | .zero | .one => true
  | .add a b | .sub a b | .mul a b => a.scoped xs && b.scoped xs
  | .neg a | .square a | .double a => a.scoped xs

/-- Every term of a program reads only variables of `xs` or variables bound before it. -/
def FProg.scoped : List String → FProg → Bool
  | xs, .ret t => t.scoped xs
  | xs, .bind x t k => t.scoped xs && k.scoped (x :: xs)

/-- The update of a valuation at a name, with the comparison `==` of `Env.extend`. -/
def upd {F : Type} (σ : String → F) (x : String) (v : F) : String → F :=
  fun y => if y == x then v else σ y

section Surface

variable {F : Type} [Primeir.Field F]

/-- The surface value of a term: the methods of `Primeir.Field F` at the valuation `σ`. -/
def FTerm.eval (σ : String → F) : FTerm → F
  | .var x => σ x
  | .zero => Primeir.Field.ZERO
  | .one => Primeir.Field.ONE
  | .add a b => Primeir.Field.add (a.eval σ) (b.eval σ)
  | .sub a b => Primeir.Field.sub (a.eval σ) (b.eval σ)
  | .mul a b => Primeir.Field.mul (a.eval σ) (b.eval σ)
  | .neg a => Primeir.Field.neg (a.eval σ)
  | .square a => Primeir.Field.square (a.eval σ)
  | .double a => Primeir.Field.double (a.eval σ)

/-- The surface value of a program: each binding updates the valuation. -/
def FProg.eval : (String → F) → FProg → F
  | σ, .ret t => t.eval σ
  | σ, .bind x t k => k.eval (upd σ x (t.eval σ))

end Surface

/-! ## 3. Interpreter steps -/

section Steps

variable (bi : Builtins) (fuel : Nat)

theorem denote'_var_run (x : String) (env : Env) (v : Value) (h : env x = some v) :
    (denote' bi fuel (.var x)).run env = (.val v, env) := by
  simp [denote', h, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure, StateT.pure]

theorem denoteArgs'_nil_run (env : Env) : (denoteArgs' bi fuel []).run env = (some [], env) := by
  simp [denoteArgs', StateT.run, pure, StateT.pure]

theorem denoteArgs'_cons_run (e : ImpExpr) (es : List ImpExpr) (env : Env) (n : Int)
    (vs : List Value) (h1 : (denote' bi fuel e).run env = (.val (.int n), env))
    (h2 : (denoteArgs' bi fuel es).run env = (some vs, env)) :
    (denoteArgs' bi fuel (e :: es)).run env = (some (.int n :: vs), env) := by
  simp only [StateT.run] at h1 h2
  simp [denoteArgs', StateT.run, bind, StateT.bind, h1, h2, pure, StateT.pure]

theorem denote'_app_run (f : String) (args : List ImpExpr) (env : Env) (vs : List Value)
    (v : Value) (h : (denoteArgs' bi fuel args).run env = (some vs, env))
    (hb : bi f vs = some v) : (denote' bi fuel (.app f args)).run env = (.val v, env) := by
  simp only [StateT.run] at h
  simp [denote', _root_.Hax.denoteApp', StateT.run, bind, StateT.bind, h, hb, pure,
    StateT.pure]

/-- A call on two arguments that return integers, with the state unchanged. -/
theorem app₂_run (f : String) (a b : ImpExpr) (env : Env) (na nb z : Int)
    (ha : (denote' bi fuel a).run env = (.val (.int na), env))
    (hb : (denote' bi fuel b).run env = (.val (.int nb), env))
    (hf : bi f [.int na, .int nb] = some (.int z)) :
    (denote' bi fuel (.app f [a, b])).run env = (.val (.int z), env) :=
  denote'_app_run bi fuel f _ env _ _
    (denoteArgs'_cons_run bi fuel _ _ env na _ ha
      (denoteArgs'_cons_run bi fuel _ _ env nb _ hb (denoteArgs'_nil_run bi fuel env))) hf

/-- A call on one argument that returns an integer, with the state unchanged. -/
theorem app₁_run (f : String) (a : ImpExpr) (env : Env) (na z : Int)
    (ha : (denote' bi fuel a).run env = (.val (.int na), env))
    (hf : bi f [.int na] = some (.int z)) :
    (denote' bi fuel (.app f [a])).run env = (.val (.int z), env) :=
  denote'_app_run bi fuel f _ env _ _
    (denoteArgs'_cons_run bi fuel _ _ env na _ ha (denoteArgs'_nil_run bi fuel env)) hf

/-- A call without arguments. -/
theorem app₀_run (f : String) (env : Env) (z : Int) (hf : bi f [] = some (.int z)) :
    (denote' bi fuel (.app f [])).run env = (.val (.int z), env) :=
  denote'_app_run bi fuel f _ env _ _ (denoteArgs'_nil_run bi fuel env) hf

/-- On the `ImpExpr` of a term, `denoteSpine` is `denote'`. -/
theorem denoteSpine_toImp (t : FTerm) : denoteSpine bi fuel t.toImp = denote' bi fuel t.toImp := by
  cases t <;> rfl

/-- A binding of a term whose value is an integer extends the environment. -/
theorem denoteSpine_letBind_run (x : String) (t : FTerm) (k : ImpExpr) (env : Env) (n : Int)
    (ht : (denote' bi fuel t.toImp).run env = (.val (.int n), env)) :
    (denoteSpine bi fuel (.letBind x t.toImp k)).run env =
      (denoteSpine bi fuel k).run (env.extend x (.int n)) := by
  simp only [StateT.run] at ht
  cases t <;> simp only [FTerm.toImp] at ht ⊢ <;>
    simp only [denoteSpine, StateT.run, bind, StateT.bind, ht] <;> rfl

end Steps

/-! ## 4. Representatives -/

section Rep

variable {p : Nat}

/-- An integer reduced modulo `p` whose residue is `y` is the canonical representative of
    `y`. -/
theorem emod_eq_val [NeZero p] (w : Int) (y : ZMod p) (h : (w : ZMod p) = y) :
    w % (p : Int) = (y.val : Int) := by
  rw [← h, ZMod.val_intCast]

/-- The canonical representative of `y`, cast back to `ZMod p`, is `y`. -/
@[simp] theorem intCast_val [NeZero p] (y : ZMod p) : (((y.val : Int)) : ZMod p) = y := by
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

/-- The value of a builtin that reduces `w` modulo `p` is the canonical representative of the
    residue of `w`. -/
theorem some_int_emod [NeZero p] (w : Int) (y : ZMod p) (h : (w : ZMod p) = y) :
    some (Value.int (w % (p : Int))) = some (Value.int (y.val : Int)) := by
  rw [emod_eq_val w y h]

end Rep

/-! ## 5. The bridge -/

variable {p : Nat} [Fact p.Prime] {F : Type} [Primeir.Field F]

/-- The environment `env` binds each name of `xs` to the canonical representative of the
    surface value at `σ`, and these surface values are valid. -/
def EnvAgree (M : FieldModel F (ZMod p)) (σ : String → F) (env : Env) (xs : List String) :
    Prop :=
  ∀ x ∈ xs, M.Valid (σ x) ∧ env x = some (.int ((M.val (σ x)).val : Int))

/-- Agreement is preserved by a binding of a valid value. -/
theorem EnvAgree.extend {M : FieldModel F (ZMod p)} {σ : String → F} {env : Env}
    {xs : List String} (h : EnvAgree M σ env xs) (x : String) (v : F) (hv : M.Valid v) :
    EnvAgree M (upd σ x v) (env.extend x (.int ((M.val v).val : Int))) (x :: xs) := by
  intro y hy
  by_cases hyx : (y == x) = true
  · simp [upd, Env.extend, hyx, hv]
  · have hy' : y ∈ xs := by
      rcases List.mem_cons.mp hy with rfl | hy
      · simp at hyx
      · exact hy
    simpa [upd, Env.extend, hyx] using h y hy'

/-- **The bridge for a term.** Under `EnvAgree` on the variables of `t`, with builtins computing
    the field operations (and the constants when `t` uses one), the interpreter returns the
    canonical representative of the surface value of `t`, leaves the environment unchanged, and
    the surface value is valid. -/
theorem FTerm.toImp_run (M : FieldModel F (ZMod p)) (bi : Builtins) (hops : FieldOps bi p)
    (fuel : Nat) (σ : String → F) (env : Env) (xs : List String) (hag : EnvAgree M σ env xs) :
    ∀ t : FTerm, t.scoped xs = true → (t.usesConst = true → FieldConsts bi p) →
      M.Valid (t.eval σ) ∧
        (denote' bi fuel t.toImp).run env = (.val (.int ((M.val (t.eval σ)).val : Int)), env) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  intro t
  induction t with
  | var x =>
      intro hs _
      have hx : x ∈ xs := by simpa [FTerm.scoped] using hs
      obtain ⟨hv, he⟩ := hag x hx
      exact ⟨hv, denote'_var_run bi fuel x env _ he⟩
  | zero =>
      intro _ hc
      refine ⟨M.zero_valid, app₀_run bi fuel _ env _ ?_⟩
      rw [(hc rfl).zero]
      simp [FTerm.eval, M.zero_eq]
  | one =>
      intro _ hc
      refine ⟨M.one_valid, app₀_run bi fuel _ env _ ?_⟩
      rw [(hc rfl).one]
      exact some_int_emod _ _ (by simp [FTerm.eval, M.one_eq])
  | add a b iha ihb =>
      intro hs hc
      simp only [FTerm.scoped, FTerm.usesConst, Bool.and_eq_true, Bool.or_eq_true] at hs hc
      obtain ⟨va, ra⟩ := iha hs.1 (fun h => hc (Or.inl h))
      obtain ⟨vb, rb⟩ := ihb hs.2 (fun h => hc (Or.inr h))
      refine ⟨M.add_valid _ _ va vb, app₂_run bi fuel _ _ _ env _ _ _ ra rb ?_⟩
      rw [hops.add]
      exact some_int_emod _ _ (by simp [FTerm.eval, M.add_eq _ _ va vb])
  | sub a b iha ihb =>
      intro hs hc
      simp only [FTerm.scoped, FTerm.usesConst, Bool.and_eq_true, Bool.or_eq_true] at hs hc
      obtain ⟨va, ra⟩ := iha hs.1 (fun h => hc (Or.inl h))
      obtain ⟨vb, rb⟩ := ihb hs.2 (fun h => hc (Or.inr h))
      refine ⟨M.sub_valid _ _ va vb, app₂_run bi fuel _ _ _ env _ _ _ ra rb ?_⟩
      rw [hops.sub]
      exact some_int_emod _ _ (by simp [FTerm.eval, M.sub_eq _ _ va vb])
  | mul a b iha ihb =>
      intro hs hc
      simp only [FTerm.scoped, FTerm.usesConst, Bool.and_eq_true, Bool.or_eq_true] at hs hc
      obtain ⟨va, ra⟩ := iha hs.1 (fun h => hc (Or.inl h))
      obtain ⟨vb, rb⟩ := ihb hs.2 (fun h => hc (Or.inr h))
      refine ⟨M.mul_valid _ _ va vb, app₂_run bi fuel _ _ _ env _ _ _ ra rb ?_⟩
      rw [hops.mul]
      exact some_int_emod _ _ (by simp [FTerm.eval, M.mul_eq _ _ va vb])
  | neg a iha =>
      intro hs hc
      simp only [FTerm.scoped, FTerm.usesConst] at hs hc
      obtain ⟨va, ra⟩ := iha hs hc
      refine ⟨M.neg_valid _ va, app₁_run bi fuel _ _ env _ _ ra ?_⟩
      rw [hops.neg]
      exact some_int_emod _ _ (by simp [FTerm.eval, M.neg_eq _ va])
  | square a iha =>
      intro hs hc
      simp only [FTerm.scoped, FTerm.usesConst] at hs hc
      obtain ⟨va, ra⟩ := iha hs hc
      refine ⟨M.square_valid _ va, app₁_run bi fuel _ _ env _ _ ra ?_⟩
      rw [hops.square]
      exact some_int_emod _ _ (by simp [FTerm.eval, M.square_eq _ va, sq])
  | double a iha =>
      intro hs hc
      simp only [FTerm.scoped, FTerm.usesConst] at hs hc
      obtain ⟨va, ra⟩ := iha hs hc
      refine ⟨M.double_valid _ va, app₁_run bi fuel _ _ env _ _ ra ?_⟩
      rw [hops.double]
      exact some_int_emod _ _ (by simp [FTerm.eval, M.double_eq _ va, two_mul])

/-- **The bridge for a program.** Under `EnvAgree` on the names `xs`, for a program whose terms
    read only names of `xs` or names bound before them, with builtins computing the field
    operations (and the constants when the program uses one), the spine reading `denoteSpine`
    returns the canonical representative of the surface value of the program, and the surface
    value is valid. -/
theorem FProg.toImp_run (M : FieldModel F (ZMod p)) (bi : Builtins) (hops : FieldOps bi p)
    (fuel : Nat) :
    ∀ (k : FProg) (σ : String → F) (env : Env) (xs : List String), EnvAgree M σ env xs →
      k.scoped xs = true → (k.usesConst = true → FieldConsts bi p) →
      M.Valid (k.eval σ) ∧ ∃ env' : Env,
        (denoteSpine bi fuel k.toImp).run env =
          (.val (.int ((M.val (k.eval σ)).val : Int)), env')
  | .ret t, σ, env, xs, hag, hs, hc => by
      obtain ⟨hv, hr⟩ := FTerm.toImp_run M bi hops fuel σ env xs hag t hs hc
      exact ⟨hv, env, by rw [FProg.toImp, denoteSpine_toImp]; exact hr⟩
  | .bind x t k, σ, env, xs, hag, hs, hc => by
      simp only [FProg.scoped, FProg.usesConst, Bool.and_eq_true, Bool.or_eq_true] at hs hc
      obtain ⟨hv, hr⟩ := FTerm.toImp_run M bi hops fuel σ env xs hag t hs.1
        (fun h => hc (Or.inl h))
      obtain ⟨hk, env', hk'⟩ := FProg.toImp_run M bi hops fuel k (upd σ x (t.eval σ))
        (env.extend x (.int ((M.val (t.eval σ)).val : Int))) (x :: xs)
        (hag.extend x _ hv) hs.2 (fun h => hc (Or.inr h))
      exact ⟨hk, env', by rw [FProg.toImp, denoteSpine_letBind_run bi fuel x t _ env _ hr]; exact hk'⟩

/-! ## 6. The instance `fe_mul_add` -/

/-- The program of `Primeir.fe_mul_add`: the parameters `a`, `b`, `c` bound to themselves, then
    `add (mul a b) c`. -/
def feMulAddProg : FProg :=
  .bind "a" (.var "a") (.bind "b" (.var "b") (.bind "c" (.var "c")
    (.ret (.add (.mul (.var "a") (.var "b")) (.var "c")))))

/-- The `ImpExpr` of `feMulAddProg` is the erased extraction term of `fe_mul_add`. -/
theorem feMulAddProg_toImp : feMulAddProg.toImp = Primeir.fe_mul_add_texpr.erase := rfl

/-- The surface value of `feMulAddProg` is `fe_mul_add` of the values of `a`, `b`, `c`. -/
theorem feMulAddProg_eval [Inhabited F] (σ : String → F) :
    feMulAddProg.eval σ = Primeir.fe_mul_add (σ "a") (σ "b") (σ "c") := by
  simp [feMulAddProg, FProg.eval, FTerm.eval, upd, Primeir.fe_mul_add]

/-- **The bridge for `fe_mul_add`.** For a field model `M : FieldModel F (ZMod p)` and builtins
    computing the field operations, on an environment binding `a`, `b`, `c` to the canonical
    representatives of valid surface values, the spine reading of `fe_mul_add_texpr` returns the
    canonical representative of `fe_mul_add a b c`, and `fe_mul_add a b c` is valid. -/
theorem fe_mul_add_bridge [Inhabited F] (M : FieldModel F (ZMod p)) (bi : Builtins)
    (hops : FieldOps bi p) (fuel : Nat) (a b c : F) (ha : M.Valid a) (hb : M.Valid b)
    (hc : M.Valid c) (env : Env) (hea : env "a" = some (.int ((M.val a).val : Int)))
    (heb : env "b" = some (.int ((M.val b).val : Int)))
    (hec : env "c" = some (.int ((M.val c).val : Int))) :
    M.Valid (Primeir.fe_mul_add a b c) ∧ ∃ env' : Env,
      (denoteSpine bi fuel Primeir.fe_mul_add_texpr.erase).run env =
        (.val (.int ((M.val (Primeir.fe_mul_add a b c)).val : Int)), env') := by
  let σ : String → F := fun y => if y == "a" then a else if y == "b" then b else c
  have hag : EnvAgree M σ env ["a", "b", "c"] := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl <;> simp [σ, ha, hb, hc, hea, heb, hec]
  have h := FProg.toImp_run M bi hops fuel feMulAddProg σ env _ hag rfl (fun h => by
    simp [feMulAddProg, FProg.usesConst, FTerm.usesConst] at h)
  rw [feMulAddProg_toImp, feMulAddProg_eval] at h
  simpa [σ] using h

open CatCrypt.Crypto.PrimeIR.Fp256Mont (fp256MontCtModel Canon montVal) in
open CatCrypt.Util (P256) in
/-- **The bridge for `fe_mul_add` at the Montgomery P-256 instance.** On canonical limbs `a`,
    `b`, `c` whose Montgomery values have their canonical representatives bound in `env`, the
    reading of `fe_mul_add_texpr` under `primeirBuiltins P256` returns the canonical
    representative of the Montgomery value of `fe_mul_add a b c`, whose limbs are canonical. -/
theorem fe_mul_add_bridge_fp256Mont [Primeir.PrimeirDeps] (fuel : Nat) (a b c : Primeir.Fp256Mont_T) (ha : Canon a)
    (hb : Canon b) (hc : Canon c) (env : Env)
    (hea : env "a" = some (.int ((montVal a).val : Int)))
    (heb : env "b" = some (.int ((montVal b).val : Int)))
    (hec : env "c" = some (.int ((montVal c).val : Int))) :
    Canon (Primeir.fe_mul_add a b c) ∧ ∃ env' : Env,
      (denoteSpine (primeirBuiltins P256) fuel Primeir.fe_mul_add_texpr.erase).run env =
        (.val (.int ((montVal (Primeir.fe_mul_add a b c)).val : Int)), env') :=
  fe_mul_add_bridge fp256MontCtModel.toFieldModel (primeirBuiltins P256)
    (primeirBuiltins_fieldOps _) fuel a b c ha hb hc env hea heb hec

end CatCrypt.Crypto.PrimeIR.FieldModelBridge
