/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.Ascent.Builtins

/-!
# Leaves for calls to functions of the same extraction

`denote'` interprets `.app f args` only through the builtin table, which carries no
fuel, so a call to a function defined in the same extraction needs a table entry. The
leaf of a function `fn` under a table `bi` (`LocalFn.leaf`) is the eventual value
`haxEval bi fn.body` of its literal body, read at the entry environment that
`bindParams` builds from the parameter names and the argument values. Its transport
lemma `LocalFn.leaf_of_fnCorres` derives the `corres_app` equation
`leaf (encArgs a) = some (enc (g a))` from the callee's `FnCorres`.

Several functions are tabulated in dependency order (`localTable`): each function is
interpreted under the base table and the functions listed before it, so a function may
call any function listed earlier. `localTable_call` reads a call to a function out of
the table when no later function has the same name. The correspondence of each function
is stated under the table of the functions before it.

A recursive function, or a group of mutually recursive functions, is not covered: its
leaf would be evaluated under a table that contains the leaf itself. Such a table is a
fixpoint of the table operator, for instance the eventual value over a call-depth bound
in the way `haxEval` takes the eventual value over fuel.

## Main definitions

* `LocalFn`, `LocalFn.entry`, `LocalFn.leaf`
* `localStep`, `localTable`

## Main results

* `LocalFn.leaf_of_fnCorres` — the leaf equation from the callee's correspondence
* `localTable_of_not_mem` — a name no local function defines is read from the base table
* `localTable_call` — a call to a function of a dependency-ordered table
* `LocalCallsDemo.outer_fnCorres` — three functions, the last calling both others
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent

/-- A function defined in the same extraction: its name in the literal, its parameter
    names, and its literal body. -/
structure LocalFn where
  /-- The name the literal calls. -/
  name : String
  /-- The parameter names, in call order. -/
  params : List String
  /-- The literal of the body. -/
  body : ImpExpr

namespace LocalFn

/-- The entry environment of a call: each parameter bound to its argument value. -/
def entry (fn : LocalFn) (vs : List Value) : Env := bindParams (fn.params.zip vs)

/-- The leaf of a call to `fn` under the table `bi`: for an argument list of the
    parameter count, the eventual value of the body from the entry environment. -/
noncomputable def leaf (bi : Builtins) (fn : LocalFn) : Leaf := fun vs =>
  if vs.length = fn.params.length then haxEval bi fn.body (fn.entry vs) else none

/-- **Transport for a local call.** The correspondence of the callee's body with `g`
    gives the leaf equation for the encoding of an argument tuple. -/
theorem leaf_of_fnCorres {bi : Builtins} {fn : LocalFn} {A β : Type} [HaxArgs A]
    [HaxEnc β] {G : A → Prop} {g : A → β}
    (h : FnCorres bi fn.body (fun a => fn.entry (encArgs a)) G g) {a : A} (hG : G a)
    (hlen : (encArgs a).length = fn.params.length) :
    fn.leaf bi (encArgs a) = some (enc (g a)) := by
  obtain ⟨fuel₀, hrun⟩ := h a hG
  simp only [leaf, ite_eq_left hlen]
  exact haxEval_eq hrun

end LocalFn

/-- The table `bi` extended by the leaf of `fn` under `bi`. -/
noncomputable def localStep (bi : Builtins) (fn : LocalFn) : Builtins :=
  Table.over [(fn.name, fn.leaf bi)] bi

/-- The table of the local functions `fns` over `base`, in dependency order: each
    function is interpreted by its literal under `base` and the functions before it. -/
noncomputable def localTable (base : Builtins) (fns : List LocalFn) : Builtins :=
  fns.foldl localStep base

theorem localTable_nil (base : Builtins) : localTable base [] = base := rfl

theorem localTable_cons (base : Builtins) (fn : LocalFn) (fns : List LocalFn) :
    localTable base (fn :: fns) = localTable (localStep base fn) fns := rfl

theorem localTable_append (base : Builtins) (pre post : List LocalFn) :
    localTable base (pre ++ post) = localTable (localTable base pre) post :=
  List.foldl_append ..

theorem localStep_self (bi : Builtins) (fn : LocalFn) (vs : List Value) :
    localStep bi fn fn.name vs = fn.leaf bi vs :=
  Table.over_of_lookup (Table.lookup_cons_self _ _ _) vs

theorem localStep_of_ne {bi : Builtins} {fn : LocalFn} {f : String} (h : f ≠ fn.name)
    (vs : List Value) : localStep bi fn f vs = bi f vs :=
  Table.over_of_lookup_none (by rw [Table.lookup_cons_of_ne _ _ h]; rfl) vs

/-- A name that no function of `fns` defines is interpreted by the base table. -/
theorem localTable_of_not_mem {bi : Builtins} {f : String} :
    ∀ {fns : List LocalFn}, f ∉ fns.map LocalFn.name → ∀ vs,
      localTable bi fns f vs = bi f vs
  | [], _, _ => rfl
  | fn :: fns, h, vs => by
    rw [localTable_cons, localTable_of_not_mem (fun hm => h (List.mem_cons_of_mem _ hm)) vs,
      localStep_of_ne (fun e => h (by simp [e])) vs]

/-- **A call in a dependency-ordered table.** When `fn` is followed by functions of
    other names, the table of `pre ++ fn :: post` interprets a call to `fn` on the
    encoding of `a` as `enc (g a)`, given the correspondence of `fn`'s body with `g`
    under the table of the functions before it. -/
theorem localTable_call {base : Builtins} {pre post : List LocalFn} {fn : LocalFn}
    {A β : Type} [HaxArgs A] [HaxEnc β] {G : A → Prop} {g : A → β}
    (hfresh : fn.name ∉ post.map LocalFn.name)
    (h : FnCorres (localTable base pre) fn.body (fun a => fn.entry (encArgs a)) G g)
    {a : A} (hG : G a) (hlen : (encArgs a).length = fn.params.length) :
    localTable base (pre ++ fn :: post) fn.name (encArgs a) = some (enc (g a)) := by
  rw [localTable_append, localTable_cons, localTable_of_not_mem hfresh, localStep_self]
  exact LocalFn.leaf_of_fnCorres h hG hlen

/-! ### Three functions with calls between them -/

namespace LocalCallsDemo

/-- `dup x = (x, x)`. -/
def dupFn : LocalFn :=
  ⟨"dup", ["x"], .letBind "x" (.var "x") (.tuple [.var "x", .var "x"])⟩

/-- `twice y = dup y`. -/
def twiceFn : LocalFn :=
  ⟨"twice", ["y"], .letBind "y" (.var "y") (.app "dup" [.var "y"])⟩

/-- `outer z = (dup z, twice z, z)`. -/
def outerFn : LocalFn :=
  ⟨"outer", ["z"], .letBind "z" (.var "z")
    (.tuple [.app "dup" [.var "z"], .app "twice" [.var "z"], .var "z"])⟩

/-- The surface of `dupFn`. -/
def dup (x : Int) : Int × Int := (x, x)

/-- The surface of `twiceFn`. -/
def twice (y : Int) : Int × Int := dup y

/-- The surface of `outerFn`. -/
def outer (z : Int) : (Int × Int) × (Int × Int) × Int := (dup z, twice z, z)

/-- The base table: no builtins. -/
def base : Builtins := fun _ _ => none

/-- The relation of the environment after the parameter `x` is rebound. -/
abbrev Bound (x : String) (env : Env) (a : Int × Unit) : Prop := env x = some (enc a.1)

theorem rebind_corres (bi : Builtins) (fn : LocalFn) (x : String) (hx : fn.params = [x])
    {body : ImpExpr} {V : Int × Unit → Value} {Q : Env → Int × Unit → Prop}
    (h : Corres bi (Bound x) (fun _ => True) body V Q) :
    Corres bi (fun env a => env = fn.entry (encArgs a)) (fun _ => True)
      (.letBind x (.var x) body) V Q :=
  corres_letBind (V₁ := fun a => enc a.1) (Q₁ := fun env a => env = fn.entry (encArgs a))
    (corres_var fun env a he _ => by
      subst he
      obtain ⟨n, u⟩ := a
      simp only [LocalFn.entry, hx]
      exact Env.extend_same Env.empty x (enc n))
    (fun _ _ => rfl) (fun _ _ _ _ => Env.extend_same _ _ _) h

theorem dup_fnCorres :
    FnCorres base dupFn.body (fun a : Int × Unit => dupFn.entry (encArgs a)) (fun _ => True)
      (fun a => dup a.1) := by
  refine fnCorres_of_corres (Q := fun _ _ => True) (rebind_corres _ dupFn "x" rfl ?_)
  exact corres_conseq (corres_tuple (corresArgs_cons (corres_var fun _ _ h _ => h)
    (fun _ _ => rfl) (corresArgs_cons (corres_var fun _ _ h _ => h) (fun _ _ => rfl)
      (corresArgs_nil _ _)))) (fun _ _ h _ => h) (fun _ h => h) (fun _ _ => rfl)
    (fun _ _ _ _ => trivial)

theorem twice_fnCorres :
    FnCorres (localTable base [dupFn]) twiceFn.body
      (fun a : Int × Unit => twiceFn.entry (encArgs a)) (fun _ => True) (fun a => twice a.1) := by
  refine fnCorres_of_corres (Q := Bound "y") (rebind_corres _ twiceFn "y" rfl ?_)
  refine corres_app (Vs := fun a => [enc a.1])
    (corresArgs_cons (corres_var fun _ _ h _ => h) (fun _ _ => rfl) (corresArgs_nil _ _)) ?_
  intro a _
  exact localTable_call (pre := []) (post := []) (by simp) dup_fnCorres trivial rfl

theorem outer_fnCorres :
    FnCorres (localTable base [dupFn, twiceFn]) outerFn.body
      (fun a : Int × Unit => outerFn.entry (encArgs a)) (fun _ => True) (fun a => outer a.1) := by
  refine fnCorres_of_corres (Q := Bound "z") (rebind_corres _ outerFn "z" rfl ?_)
  have hz : CorresArgs (localTable base [dupFn, twiceFn]) (Bound "z") (fun _ => True)
      [.var "z"] (fun a => [enc a.1]) (Bound "z") :=
    corresArgs_cons (corres_var fun _ _ h _ => h) (fun _ _ => rfl) (corresArgs_nil _ _)
  refine corres_conseq (corres_tuple (corresArgs_cons (corres_app hz fun a _ => ?_)
    (fun _ _ => rfl) (corresArgs_cons (corres_app hz fun a _ => ?_) (fun _ _ => rfl)
      (corresArgs_cons (corres_var fun _ _ h _ => h) (fun _ _ => rfl)
        (corresArgs_nil _ _))))) (fun _ _ h _ => h) (fun _ h => h) (fun _ _ => rfl)
    (fun _ _ _ h => h)
  · exact localTable_call (pre := []) (post := [twiceFn]) (by decide) dup_fnCorres trivial rfl
  · exact localTable_call (pre := [dupFn]) (post := []) (by simp) twice_fnCorres trivial rfl

end LocalCallsDemo

end Hax.Ascent
