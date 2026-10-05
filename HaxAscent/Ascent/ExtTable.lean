/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.Ascent.TableCongr
public import HaxAscent.Ascent.RuntimeOps

/-!
# The builtin table of an extraction

The literal of a haxpipeT extraction calls four families of names: runtime operations,
struct constructors, projections and updates, methods of the `<X>Deps` class, and the
functions of the same extraction. `extBuiltins T fns` reads a name from the runtime table
(`runtimeBuiltins`), then from the struct and dependency table `T`, then from the local
functions `fns`.

A local function is an `ExtFn`: its name, parameter names, the constants of the
extraction its literal reads as variables (`globals`), and its literal. The leaf of a
call is the eventual value of the literal (`haxEval`) under the table of the functions
before it, from the environment binding the parameters to the arguments over the
constants, each read from that table as a call without arguments; an early return is read
as the returned value (`retVal`). The functions are listed in dependency order, so a
function may call any function listed before it; recursion is not covered.

A correspondence proved for a function under the table of the functions before it holds
under the table of all functions when its literal calls none of the later ones
(`fnCorres_extend`), by the table-extension lemma `denote'_congr`.

## Main definitions

* `ExtFn`, `ExtFn.globalVals`, `ExtFn.entry`, `ExtFn.leaf`, `retVal`, `mergeExcept`
* `extStep`, `extLocals`, `extBuiltins`, `notIn`

## Main results

* `extBuiltins_nil` — without local functions the table is `runtimeBuiltins T.toBuiltins`
* `extBuiltins_append_agree`, `fnCorres_extend`, `fnCorresX_extend`,
  `globalVals_extend` — extension of the table by later functions
* `extBuiltins_self`, `extBuiltins_call`, `extBuiltins_callX` — a call to a local function
  from its correspondence
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent

section ExtTable

/-- A function of an extraction: its name, its parameter names, the names of the
    constants of the extraction its literal reads as variables, and its literal. -/
structure ExtFn where
  /-- The name the literals call. -/
  name : String
  /-- The parameter names, in call order. -/
  params : List String
  /-- The constants the body reads as variables. -/
  globals : List String
  /-- The literal of the body. -/
  body : ImpExpr

/-- The value a call returns: the payload of an early return, any other value itself. -/
def retVal (v : Value) : Value :=
  match cfExcept v with
  | .error w => w
  | .ok v => v

namespace ExtFn

/-- The bindings of the constants: each read from the table as a call without
    arguments. -/
def globalVals (bi : Builtins) (fn : ExtFn) : List (String × Value) :=
  fn.globals.map fun g => (g, (bi g []).getD .unit)

/-- The entry environment of a call: the parameters bound to the arguments, over the
    constants. -/
def entry (bi : Builtins) (fn : ExtFn) (vs : List Value) : Env :=
  bindParams (fn.params.zip vs ++ fn.globalVals bi)

/-- The leaf of a call under `bi`: for an argument list of the parameter count, the
    eventual value of the body, an early return read as the returned value. -/
noncomputable def leaf (bi : Builtins) (fn : ExtFn) : Leaf := fun vs =>
  if vs.length = fn.params.length then (haxEval bi fn.body (fn.entry bi vs)).map retVal
  else none

theorem entry_eq {bi : Builtins} {fn : ExtFn} {gv : List (String × Value)}
    (h : fn.globalVals bi = gv) (vs : List Value) :
    fn.entry bi vs = bindParams (fn.params.zip vs ++ gv) := by
  rw [entry, h]

end ExtFn

/-- The local table `base` extended by the leaf of `fn`, evaluated under the runtime
    operations over the struct and dependency table `T` over `base`. -/
noncomputable def extStep (T : Table) (base : Builtins) (fn : ExtFn) : Builtins :=
  Table.over [(fn.name, fn.leaf (runtimeBuiltins (T.over base)))] base

/-- The local functions `fns`, in dependency order. -/
noncomputable def extLocals (T : Table) (fns : List ExtFn) : Builtins :=
  fns.foldl (extStep T) fun _ _ => none

/-- **The builtin table of an extraction.** A name is read from the runtime operations,
    then from the struct and dependency table `T`, then from the local functions
    `fns`. -/
noncomputable def extBuiltins (T : Table) (fns : List ExtFn) : Builtins :=
  runtimeBuiltins (T.over (extLocals T fns))

/-- The table of an extraction without local functions is the runtime operations over
    its struct and dependency table. -/
theorem extBuiltins_nil (T : Table) : extBuiltins T [] = runtimeBuiltins T.toBuiltins := rfl

theorem foldl_extStep_of_not_mem (T : Table) {f : String} :
    ∀ {fns : List ExtFn} (base : Builtins), f ∉ fns.map ExtFn.name →
      fns.foldl (extStep T) base f = base f
  | [], _, _ => rfl
  | fn :: fns, base, h => by
    have hne : f ≠ fn.name := fun e => h (by simp [e])
    rw [List.foldl_cons, foldl_extStep_of_not_mem T _ (fun hm => h (List.mem_cons_of_mem _ hm))]
    funext vs
    exact Table.over_of_lookup_none (by rw [Table.lookup_cons_of_ne _ _ hne]; rfl) vs

theorem runtimeBuiltins_congr {base base' : Builtins} {f : String} (h : base f = base' f) :
    runtimeBuiltins base f = runtimeBuiltins base' f := by
  funext vs
  simp only [runtimeBuiltins, h]

theorem Table.over_congr (T : Table) {base base' : Builtins} {f : String}
    (h : base f = base' f) : T.over base f = T.over base' f := by
  funext vs
  simp only [Table.over, h]

/-- A name that no function of `post` defines is read alike in the tables of `pre` and
    of `pre ++ post`. -/
theorem extBuiltins_append_agree {T : Table} {pre post : List ExtFn} {f : String}
    (h : f ∉ post.map ExtFn.name) :
    extBuiltins T (pre ++ post) f = extBuiltins T pre f := by
  unfold extBuiltins extLocals
  apply runtimeBuiltins_congr
  apply Table.over_congr
  rw [List.foldl_append, foldl_extStep_of_not_mem T _ h]

/-- The names that no function of `post` defines. -/
def notIn (post : List ExtFn) (f : String) : Bool := !(post.map ExtFn.name).contains f

theorem extBuiltins_agree_notIn {T : Table} {pre post : List ExtFn} :
    ∀ f, notIn post f = true → extBuiltins T pre f = extBuiltins T (pre ++ post) f := by
  intro f h
  refine (extBuiltins_append_agree ?_).symm
  simpa [notIn] using h

/-- **A function proved under a prefix of the table holds under the whole table**,
    when its literal calls no function defined after the prefix. -/
theorem fnCorres_extend {T : Table} {pre post : List ExtFn} {e : ImpExpr}
    (he : callsOK (notIn post) e = true) {A β : Type} [HaxEnc β] {entry : A → Env}
    {G : A → Prop} {g : A → β} (h : FnCorres (extBuiltins T pre) e entry G g) :
    FnCorres (extBuiltins T (pre ++ post)) e entry G g :=
  fnCorres_congr extBuiltins_agree_notIn he h

theorem fnCorresX_extend {T : Table} {pre post : List ExtFn} {e : ImpExpr}
    (he : callsOK (notIn post) e = true) {A R β : Type} [HaxEnc R] [HaxEnc β]
    {entry : A → Env} {G : A → Prop} {g : A → Except R β}
    (h : FnCorresX (extBuiltins T pre) e entry G g) :
    FnCorresX (extBuiltins T (pre ++ post)) e entry G g :=
  fnCorresX_congr extBuiltins_agree_notIn he h

theorem globalVals_extend {T : Table} {pre post : List ExtFn} {fn : ExtFn}
    (h : fn.globals.all (notIn post) = true) :
    fn.globalVals (extBuiltins T (pre ++ post)) = fn.globalVals (extBuiltins T pre) := by
  unfold ExtFn.globalVals
  refine List.map_congr_left fun g hg => ?_
  rw [extBuiltins_append_agree]
  have := List.all_eq_true.mp h g hg
  simpa [notIn] using this

/-- The leaf of `fn` read from the table of `pre ++ fn :: post`. -/
theorem extBuiltins_self {T : Table} {pre post : List ExtFn} {fn : ExtFn}
    (hrt : runtimeTable.lookup fn.name = none) (htag : parseTag fn.name = none)
    (hT : T.lookup fn.name = none)
    (hfresh : fn.name ∉ post.map ExtFn.name) (vs : List Value) :
    extBuiltins T (pre ++ fn :: post) fn.name vs = fn.leaf (extBuiltins T pre) vs := by
  unfold extBuiltins
  rw [runtimeBuiltins_of_base hrt htag, Table.over_of_lookup_none hT]
  unfold extLocals
  rw [List.foldl_append, List.foldl_cons, foldl_extStep_of_not_mem T _ hfresh]
  exact Table.over_of_lookup (Table.lookup_cons_self _ _ _) vs

theorem retVal_enc {β : Type} [HaxEnc β] [HaxEnc.Plain β] (b : β) : retVal (enc b) = enc b := by
  have h := HaxEnc.Plain.not_cf b
  unfold retVal
  generalize enc b = v at h ⊢
  cases v with
  | controlFlow c w => cases c <;> simp_all [Value.isControlFlow]
  | _ => rfl

/-- **A call to a function of the extraction.** The argument values are `ea a`, any
    function of the argument tuple; no injectivity of `ea` is assumed. -/
theorem extBuiltins_call {T : Table} {pre post : List ExtFn} {fn : ExtFn}
    (hrt : runtimeTable.lookup fn.name = none) (htag : parseTag fn.name = none)
    (hT : T.lookup fn.name = none)
    (hfresh : fn.name ∉ post.map ExtFn.name) {A β : Type} {ea : A → List Value} [HaxEnc β]
    [HaxEnc.Plain β] {G : A → Prop} {g : A → β}
    (h : FnCorres (extBuiltins T pre) fn.body
      (fun a => fn.entry (extBuiltins T pre) (ea a)) G g)
    {a : A} (hG : G a) (hlen : (ea a).length = fn.params.length) :
    extBuiltins T (pre ++ fn :: post) fn.name (ea a) = some (enc (g a)) := by
  rw [extBuiltins_self hrt htag hT hfresh]
  obtain ⟨fuel₀, hrun⟩ := h a hG
  simp only [ExtFn.leaf, if_pos hlen, haxEval_eq hrun, Option.map_some, retVal_enc]

/-- The value of an early-return result whose two sides have one type. -/
def mergeExcept {β : Type} : Except β β → β
  | .error b => b
  | .ok b => b

/-- **A call to a function of the extraction with early return.** -/
theorem extBuiltins_callX {T : Table} {pre post : List ExtFn} {fn : ExtFn}
    (hrt : runtimeTable.lookup fn.name = none) (htag : parseTag fn.name = none)
    (hT : T.lookup fn.name = none)
    (hfresh : fn.name ∉ post.map ExtFn.name) {A β : Type} {ea : A → List Value} [HaxEnc β]
    [HaxEnc.Plain β] {G : A → Prop} {g : A → Except β β}
    (h : FnCorresX (extBuiltins T pre) fn.body
      (fun a => fn.entry (extBuiltins T pre) (ea a)) G g)
    {a : A} (hG : G a) (hlen : (ea a).length = fn.params.length) :
    extBuiltins T (pre ++ fn :: post) fn.name (ea a) =
      some (enc (mergeExcept (g a))) := by
  rw [extBuiltins_self hrt htag hT hfresh]
  obtain ⟨fuel₀, hrun⟩ := h a hG
  have h₀ := hrun fuel₀ (Nat.le_refl _)
  rcases ho : (denote' (extBuiltins T pre) fuel₀ fn.body
    (fn.entry (extBuiltins T pre) (ea a))).1 with v | v | v | _ | m
  all_goals rw [ho] at h₀
  all_goals try simp [outcomeExceptCF] at h₀
  have hev : haxEval (extBuiltins T pre) fn.body (fn.entry (extBuiltins T pre) (ea a))
      = some v :=
    haxEval_eq (fuel₀ := fuel₀) fun fuel hf => by rw [denote'_val_mono _ ho hf, ho]
  simp only [ExtFn.leaf, if_pos hlen, hev, Option.map_some, Option.some.injEq]
  try simp only [outcomeExceptCF, Option.some.injEq] at h₀
  unfold retVal
  rw [h₀]
  cases hg : g a with
  | error b => rfl
  | ok b => rfl

end ExtTable

end Hax.Ascent
