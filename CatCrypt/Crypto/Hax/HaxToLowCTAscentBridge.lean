/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module -- deprecated_module: ignore

public import CatCrypt.Crypto.Hax.HaxToLowCTStruct
public import HaxAscent.Ascent.EarlyExit
public import HaxAscent.Ascent.Structs
public import HaxAscent.Ascent.ArrStructs
public import HaxAscent.Ascent.AscentOption
public import HaxAscent.Ascent.CorresRRel

/-!
# The descent relations over the ascent judgment

The descent (`haxToLowCTK`, the struct flattening `flatE`, the renaming
`renameVar`) and the ascent (`Hax.Ascent.Corres`) describe runs of the same
evaluator `Hax.denote'`.  This module states the descent relations in terms of
the ascent judgment.

**Transport.**  `FuelSim bi R Rx e e'` states that from `R`-related environments the
runs of `e` and `e'` have the same outcome at every fuel and end in `Rx`-related
environments.  `corres_of_fuelSim` carries a `Corres` statement for `e` to one for
`e'` with the same value, from the environments `R`-related to an entry environment
of `e` to those `Rx`-related to its exit environment; it is the relational refinement
`Hax.Ascent.rrelPT_wpAT_of_sim` composed with the correspondence by
`Hax.Ascent.corres_trans_of_rrelPT`.  `corres_transport` is the case
`R = Rx`, `corres_renameVar` its instance at the renaming relation `RenRel`
(`denote'_renameVar`), and `corres_flatProj` at the flattening relation
`StructFlatAt` for a field call (`flatProj_sim`).  `FuelSim.of_step` composes a
binding arm whose runs reduce to those of the continuations with a `FuelSim` for the
continuations: the `Option` bindings and match (`fuelSim_optBindSome`,
`fuelSim_optBindNone`, `fuelSim_optMatch`), the call result bindings
(`fuelSim_callBind`, `fuelSim_callBind1`), the update with a copy
(`fuelSim_flatUpdateCopy`) and the element write of an array of structs, whose stores
change the flat array (`fuelSim_flatArrUpdate`).  A returned tuple with the variables
`rs` is transported along the agreement `RetAt rs` (`fuelSim_retVars`,
`corres_retVars`).

**Leaves.**  The builtin premises `FieldSound` and `UpdateSound` of the struct
arms hold for a table whose field and update calls are the ascent leaves
`projLeaf` and `updateLeaf`, at every arity (`fieldSound_of_projLeaf`,
`updateSound_of_updateLeaf`); the update call name is hax-lean's `structUpdateHead`.
`OptionSound` holds for the runtime leaves of `Some` and `None`
(`optionSound_of_leaves`).  The array builtins of the arrays-of-structs
arms hold for the runtime leaves `indexLeaf`, `arrayUpdateLeaf`, `lenLeaf` and the
integer `Add`/`Mul` leaves (`arrIndexSound_of_indexLeaf`,
`arrUpdateSound_of_arrayUpdateLeaf`, `lenSound_of_lenLeaf`, `idxArithSound_of_leaves`);
an array variable holding `enc a` and `encFlat a` is flattened
(`arrStructFlatAt_encFlat`), and `corres_flatElemField` transports a `Corres` statement
for a field call on an element to the read of the flat array.

**`Option` returns.**  `Some y` and `None` in tail position and as an early return
correspond, as the source expression, to the `Option` of the value of `y` and, as
their lowering `optReturn T` or `optBreak T`, to the payload, with the tag in `T`
(`corres_optReturnSome`, `corres_optReturnNone`, `corresX_optBreakSome`,
`corresX_optBreakNone`).

**Exit.**  `ExitSim` takes a `denote'` run ending in a value; a `CorresX`
statement supplies one, with the value `excVal (R σ)`.  `exitSim_corresX` is the
composite for an expression, `haxToLowCTFn_corresX` and
`haxToLowCTFn_fnCorresX` for a function body: the result slot of the lowered
function holds the decoding of the thrown or returned value (`excPayload`).

## Main results

* `FuelSim`, `corres_of_fuelSim`, `FuelSim.of_step` — the fuel-uniform simulation, the
  transport of `Corres` along it, and its composition through a binding arm
* `corres_transport`, `corres_renameVar`, `corres_flatProj` — the transport along one
  relation, and its instances at `RenRel` and `StructFlatAt`
* `fieldSound_of_projLeaf`, `updateSound_of_updateLeaf`, `optionSound_of_leaves` — the
  struct and `Option` builtin premises from the ascent leaves
* `arrIndexSound_of_indexLeaf`, `arrUpdateSound_of_arrayUpdateLeaf`,
  `lenSound_of_lenLeaf`, `idxArithSound_of_leaves`, `arrStructFlatAt_encFlat`,
  `corres_flatElemField`, `fuelSim_flatArrUpdate` — the arrays-of-structs premises
  from the runtime leaves, the transport of a field call on an element to the flat
  read, and the element write
* `enc_encFlat_set_rows` — the rows after an element write are those of the typed
  array with the element replaced, under `enc` and `encFlat`
* `corres_flatFieldElemField` — the transport of a field call on an element of an
  array field of a struct to the read of the flat array
* `fuelSim_optBindSome`, `fuelSim_optBindNone`, `fuelSim_optMatch`,
  `corres_optReturnSome`, `corres_optReturnNone`, `corresX_optBreakSome`,
  `corresX_optBreakNone` — the `Option` arms
* `fuelSim_callBind`, `fuelSim_callBind1`, `fuelSim_flatUpdateCopy`,
  `fuelSim_retVars`, `corres_retVars` — call results, copies and named returns
* `exitSim_corresX` — an `ExitSim` expression under a `CorresX` statement
* `haxToLowCTFn_corresX`, `haxToLowCTFn_fnCorresX` — the lowered function's result
  slot under `CorresX` and `FnCorresX`
-/

deprecated_module "haxToLowCT is the legacy hax front, outside compileA's path: compileA compiles \
  through haxToNF (Haxc.NFChain); this module remains for the SurfaceDeps bridges \
  (*HaxLowCTBridge) and the kernel producers that use it."
  (since := "2026-10-21")

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpLit Value Env Outcome Builtins denote')
open _root_.Hax.Ascent (Corres CorresX excVal ExcPlain FnCorresX encExc projLeaf updateLeaf)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT RustState RustExec LeafSpec)

/-! ## Transport along an environment relation -/

section Transport

/-- The runs of `e` from `env` and `e'` from `envF` have the same outcome at every fuel
    from `R`-related environments and end in `Rx`-related environments. -/
def FuelSim (bi : Builtins) (R Rx : Env → Env → Prop) (e e' : ImpExpr) : Prop :=
  ∀ fuel env envF, R env envF →
    ((denote' bi fuel e).run env).1 = ((denote' bi fuel e').run envF).1 ∧
      Rx ((denote' bi fuel e).run env).2 ((denote' bi fuel e').run envF).2

variable {S : Type} {bi : Builtins}

/-- **Transport.**  Under a fuel-uniform simulation of `e` by `e'` from `R` to `Rx`, a
    `Corres` statement for `e` gives one for `e'` with the same value, from the
    environments `R`-related to the entry environments of `e` to those `Rx`-related to
    its exit environments. -/
theorem corres_of_fuelSim {R Rx : Env → Env → Prop} {e e' : ImpExpr}
    {P Q : Env → S → Prop} {G : S → Prop} {V : S → Value} (hsim : FuelSim bi R Rx e e')
    (h : Corres bi P G e V Q) :
    Corres bi (fun envF σ => ∃ env, P env σ ∧ R env envF) G e' V
      (fun envF σ => ∃ env, Q env σ ∧ Rx env envF) :=
  _root_.Hax.Ascent.corres_conseq
    (_root_.Hax.Ascent.corres_trans_of_rrelPT h (_root_.Hax.Ascent.rrelPT_wpAT_of_sim hsim))
    (fun _ _ ⟨env, hP, hR⟩ _ => ⟨env, hR, hP⟩) (fun _ h => h) (fun _ _ => rfl)
    (fun _ _ _ ⟨env, hR, hQ⟩ => ⟨env, hQ, hR⟩)

/-- **Binding arm.**  When at every fuel the runs of `e` and `e'` from `R`-related
    environments are the runs of `b` and `b'` from `R₂`-related environments, a
    fuel-uniform simulation of `b` by `b'` from `R₂` is one of `e` by `e'` from `R`. -/
theorem FuelSim.of_step {R R₂ Rx : Env → Env → Prop} {e e' b b' : ImpExpr}
    (hstep : ∀ fuel env envF, R env envF → ∃ env₂ envF₂,
      (denote' bi fuel e).run env = (denote' bi fuel b).run env₂ ∧
        (denote' bi fuel e').run envF = (denote' bi fuel b').run envF₂ ∧ R₂ env₂ envF₂)
    (hb : FuelSim bi R₂ Rx b b') : FuelSim bi R Rx e e' := by
  intro fuel env envF hR
  obtain ⟨env₂, envF₂, h1, h2, h3⟩ := hstep fuel env envF hR
  rw [h1, h2]
  exact hb fuel env₂ envF₂ h3

/-- **Transport along one relation.**  When from `R`-related environments the runs
    of `e` and `e'` have the same outcome and end in `R`-related environments at every
    fuel, a `Corres` statement for `e` gives one for `e'` with the same value, from
    and to the environments `R`-related to the entry and exit environments of `e`. -/
theorem corres_transport {R : Env → Env → Prop} {e e' : ImpExpr}
    {P Q : Env → S → Prop} {G : S → Prop} {V : S → Value}
    (hsim : ∀ fuel env envF, R env envF →
      ((denote' bi fuel e).run env).1 = ((denote' bi fuel e').run envF).1 ∧
        R ((denote' bi fuel e).run env).2 ((denote' bi fuel e').run envF).2)
    (h : Corres bi P G e V Q) :
    Corres bi (fun envF σ => ∃ env, P env σ ∧ R env envF) G e' V
      (fun envF σ => ∃ env, Q env σ ∧ R env envF) :=
  corres_of_fuelSim hsim h

/-- **Renaming.**  Under the side conditions of `denote'_renameVar`, a `Corres`
    statement for `e` holds for `renameVar v w e` from the `RenRel v w`-related
    environments. -/
theorem corres_renameVar {v w : String} {e : ImpExpr} (hs : renameSafe v w e = true)
    (ha : varAbsent w e = true) {P Q : Env → S → Prop} {G : S → Prop} {V : S → Value}
    (h : Corres bi P G e V Q) :
    Corres bi (fun envF σ => ∃ env, P env σ ∧ RenRel v w env envF) G (renameVar v w e) V
      (fun envF σ => ∃ env, Q env σ ∧ RenRel v w env envF) :=
  corres_transport (fun fuel env envF hR => denote'_renameVar bi v w e hs ha fuel env envF hR) h

/-- **Flattened projection.**  A `Corres` statement for the field call `c` on the
    struct variable `s` holds for the component variable `comp` the projection
    arm produces, from the environments in which `s` is flattened. -/
theorem corres_flatProj {L : StructLayout} {sv : StructVars} {c s comp : String}
    {fs : List String} (hp : projArm L sv c s = some comp)
    (hfs : structFields L sv s = some fs) (hF : FieldSound bi fs)
    {P Q : Env → S → Prop} {G : S → Prop} {V : S → Value}
    (h : Corres bi P G (.app c [.var s]) V Q) :
    Corres bi (fun envF σ => ∃ env, P env σ ∧ StructFlatAt fs s env envF) G (.var comp) V
      (fun envF σ => ∃ env, Q env σ ∧ StructFlatAt fs s env envF) := by
  refine corres_transport (fun fuel env envF hR => ?_) h
  obtain ⟨v, h1, h2⟩ := flatProj_sim bi fuel L sv c s comp fs env envF hp hfs hR hF
  rw [h1, h2]; exact ⟨rfl, hR⟩

end Transport

/-! ## The struct and `Option` builtins as ascent leaves -/

section Leaves

/-- The projection leaf of field `i` of an `n`-field struct reads component `i` of the
    struct value. -/
theorem projLeaf_structVal {i n : Nat} {vs : List Value} (hlen : vs.length = n) (hi : i < n) :
    projLeaf i n [structVal n vs] = vs[i]? := by
  by_cases hn : n = 1
  · subst hn
    obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp hlen
    obtain rfl : i = 0 := by omega
    rfl
  · rw [structVal_of_ne_one hn]
    simp [projLeaf, show ¬ n ≤ 1 by omega]

/-- The update leaf of field `i` of an `n`-field struct replaces component `i` of the
    struct value. -/
theorem updateLeaf_structVal {i n : Nat} {vs : List Value} (v : Value) (hlen : vs.length = n)
    (hi : i < n) : updateLeaf i n [structVal n vs, v] = some (structVal n (vs.set i v)) := by
  by_cases hn : n = 1
  · subst hn
    obtain ⟨w, rfl⟩ := List.length_eq_one_iff.mp hlen
    obtain rfl : i = 0 := by omega
    rfl
  · rw [structVal_of_ne_one hn, structVal_of_ne_one hn]
    simp [updateLeaf, show ¬ n ≤ 1 by omega, hlen, hi]

/-- The field calls of a struct, interpreted by the ascent leaves `projLeaf`, satisfy
    `FieldSound`. -/
theorem fieldSound_of_projLeaf {bi : Builtins} {fs : List String}
    (h : ∀ i f, fs[i]? = some f → ∀ vs, bi ("." ++ f) vs = projLeaf i fs.length vs) :
    FieldSound bi fs := by
  intro vs i f hlen hi
  rw [h i f hi]
  exact projLeaf_structVal hlen (List.getElem?_eq_some_iff.1 hi).1

/-- The update calls of a struct, interpreted by the ascent leaves `updateLeaf` under
    hax-lean's names `structUpdateHead`, satisfy `UpdateSound`. -/
theorem updateSound_of_updateLeaf {bi : Builtins} {S : String} {fs : List String}
    (h : ∀ i, i < fs.length → ∀ vs,
      bi (_root_.Hax.structUpdateHead S i fs.length) vs = updateLeaf i fs.length vs) :
    UpdateSound bi S fs := by
  intro vs i v hlen hi
  rw [h i hi]
  exact updateLeaf_structVal v hlen hi

/-- `Some` and `None` interpreted by the runtime leaves satisfy `OptionSound`. -/
theorem optionSound_of_leaves {bi : Builtins}
    (hS : ∀ vs, bi "Some" vs = _root_.Hax.Ascent.someLeaf vs)
    (hN : ∀ vs, bi "None" vs = _root_.Hax.Ascent.constLeaf (.option none) vs) :
    OptionSound bi :=
  ⟨fun v => by rw [hS]; simp only [_root_.Hax.Ascent.someLeaf],
    by rw [hN]; exact _root_.Hax.Ascent.constLeaf_nil _⟩

/-- `index` interpreted by the runtime leaf satisfies `ArrIndexSound`. -/
theorem arrIndexSound_of_indexLeaf {bi : Builtins}
    (h : ∀ vs, bi "index" vs = _root_.Hax.Ascent.indexLeaf vs) : ArrIndexSound bi :=
  fun vs m v hv => by rw [h]; exact _root_.Hax.Ascent.indexLeaf_nat vs m v hv

/-- `array_update` interpreted by the runtime leaf satisfies `ArrUpdateSound`. -/
theorem arrUpdateSound_of_arrayUpdateLeaf {bi : Builtins}
    (h : ∀ vs, bi "array_update" vs = _root_.Hax.Ascent.arrayUpdateLeaf vs) :
    ArrUpdateSound bi :=
  fun vs m v => by rw [h]; exact _root_.Hax.Ascent.arrayUpdateLeaf_nat vs m v

/-- `len` interpreted by the runtime leaf satisfies `LenSound`. -/
theorem lenSound_of_lenLeaf {bi : Builtins} (h : ∀ vs, bi "len" vs = _root_.Hax.Ascent.lenLeaf vs) :
    LenSound bi :=
  fun vs => by rw [h]; simp [_root_.Hax.Ascent.lenLeaf]

/-- `Add` and `Mul` interpreted by the runtime integer leaves satisfy
    `IdxArithSound`. -/
theorem idxArithSound_of_leaves {bi : Builtins}
    (hA : ∀ vs, bi "Add" vs = _root_.Hax.Ascent.intArrLeaf2 _root_.Hax.add _root_.Hax.add vs)
    (hM : ∀ vs, bi "Mul" vs = _root_.Hax.Ascent.intArrLeaf2 _root_.Hax.mul _root_.Hax.mul vs) :
    IdxArithSound bi := fun x y => by
  rw [hA, hM]
  exact ⟨_root_.Hax.Ascent.Leaf.orElse_of_some
      (_root_.Hax.Ascent.leaf2_apply (_root_.Hax.add : Int → Int → Int) x y),
    _root_.Hax.Ascent.Leaf.orElse_of_some
      (_root_.Hax.Ascent.leaf2_apply (_root_.Hax.mul : Int → Int → Int) x y)⟩

/-- An array variable holding the encoding of an array of structs with `k` fields in
    `env` and its flat encoding `encFlat` in `envF` is flattened, when each element
    encodes as the struct value of its components. -/
theorem arrStructFlatAt_encFlat {α : Type} [_root_.Hax.Ascent.HaxTupleEnc α]
    [_root_.Hax.Ascent.HaxEnc α] {k : Nat}
    (hk : ∀ p : α, (_root_.Hax.Ascent.HaxTupleEnc.encList p).length = k)
    (henc : ∀ p : α, (_root_.Hax.Ascent.HaxEnc.enc p : Value) =
      structVal k (_root_.Hax.Ascent.HaxTupleEnc.encList p))
    (a : Array α) (x : String) (env envF : Env)
    (h1 : env x = some (_root_.Hax.Ascent.HaxEnc.enc a))
    (h2 : envF x = some (_root_.Hax.Ascent.encFlat a)) : ArrStructFlatAt k x env envF := by
  refine ⟨a.toList.map _root_.Hax.Ascent.HaxTupleEnc.encList, ?_,
    _root_.Hax.Ascent.encFlat_rows hk a, h2⟩
  rw [h1, _root_.Hax.Ascent.enc_array_toList, List.map_map]
  congr 2
  exact List.map_congr_left fun p _ => henc p

/-- The array `a` rebound to the struct values of `rows` with row `j` replaced, over
    the flat array with row `j` replaced, is flattened. -/
theorem arrStructFlatAt_set {k : Nat} {a : String} {env envF : Env}
    {rows : List (List Value)} {j : Nat} {ws : List Value}
    (hrow : ∀ r ∈ rows, r.length = k) (hws : ws.length = k)
    (hF : envF a = some (.array (rows.set j ws).flatten)) :
    ArrStructFlatAt k a (env.extend a (.array ((rows.set j ws).map (structVal k)))) envF :=
  ⟨rows.set j ws, _root_.Hax.Env.extend_same _ _ _, fun r hr => by
    rcases List.mem_or_eq_of_mem_set hr with h | h
    · exact hrow r h
    · rw [h]; exact hws, hF⟩

/-- The rows of an array of structs with row `j` replaced by the components of `p`
    are the rows of the array with element `j` replaced by `p`: their struct values
    are its encoding and their concatenation its flat encoding. -/
theorem enc_encFlat_set_rows {α : Type} [_root_.Hax.Ascent.HaxTupleEnc α]
    [_root_.Hax.Ascent.HaxEnc α] {k : Nat}
    (henc : ∀ p : α, (_root_.Hax.Ascent.HaxEnc.enc p : Value) =
      structVal k (_root_.Hax.Ascent.HaxTupleEnc.encList p))
    (a : Array α) (j : Nat) (hj : j < a.size) (p : α) :
    Value.array (((a.toList.map _root_.Hax.Ascent.HaxTupleEnc.encList).set j
        (_root_.Hax.Ascent.HaxTupleEnc.encList p)).map (structVal k)) =
      _root_.Hax.Ascent.HaxEnc.enc (a.set j p) ∧
    Value.array ((a.toList.map _root_.Hax.Ascent.HaxTupleEnc.encList).set j
        (_root_.Hax.Ascent.HaxTupleEnc.encList p)).flatten =
      _root_.Hax.Ascent.encFlat (a.set j p) := by
  refine ⟨?_, _root_.Hax.Ascent.encFlat_set a j hj p⟩
  rw [_root_.Hax.Ascent.enc_array_toList, Array.toList_set, List.map_set, List.map_set,
    List.map_map]
  congr 2
  · exact List.map_congr_left fun q _ => (henc q).symm
  · exact (henc p).symm

end Leaves

/-! ## Arrays of structs under `Corres` -/

section ArrTransport

variable {S : Type} {bi : Builtins}

/-- The array variable `a` is flattened, its components are not control flow, and
    the index variable `x` holds the same in-range natural on both sides. -/
def ElemReadAt (k : Nat) (a x : String) (env envF : Env) : Prop :=
  ∃ (rows : List (List Value)) (j : Nat), env a = some (.array (rows.map (structVal k))) ∧
    (∀ r ∈ rows, r.length = k) ∧ (∀ r ∈ rows, ∀ w ∈ r, w.isControlFlow = false) ∧
    envF a = some (.array rows.flatten) ∧
    env x = some (.int j) ∧ envF x = some (.int j) ∧ j < rows.length

/-- **Flattened element field read.**  A `Corres` statement for the field call `c`
    on `index(a, x)` holds for the read of the flat array at `x * k + off`, from the
    environments in which `a` is flattened and `x` holds an in-range index. -/
theorem corres_flatElemField (hI : ArrIndexSound bi) (hA : IdxArithSound bi)
    {c a x : String} {fs : List String} {off : Nat} (hF : FieldSound bi fs)
    (hoff : fieldIdx fs c = some off) {P Q : Env → S → Prop} {G : S → Prop} {V : S → Value}
    (h : Corres bi P G (.app c [.app "index" [.var a, .var x]]) V Q) :
    Corres bi (fun envF σ => ∃ env, P env σ ∧ ElemReadAt fs.length a x env envF) G
      (.app "index" [.var a, flatIdx (.var x) fs.length off]) V
      (fun envF σ => ∃ env, Q env σ ∧ ElemReadAt fs.length a x env envF) := by
  refine corres_of_fuelSim (fun fuel env envF hR => ?_) h
  obtain ⟨rows, j, ha, hrow, hcf, haF, hx, hxF, hj⟩ := hR
  obtain ⟨w, h1, h2⟩ := flatElemField_sim bi fuel hI hA c a fs off (.var a) (.var x) (.var x)
    env envF rows j hF hoff hrow hj (hcf _ (List.getElem_mem hj)) (by rw [denote'_var_run, ha])
    haF (by rw [denote'_var_run, hx]) (by rw [denote'_var_run, hxF])
  rw [h1, h2]
  exact ⟨rfl, rows, j, ha, hrow, hcf, haF, hx, hxF, hj⟩

/-- **Element write.**  The element write `let a = array_update(a, i, x); body` and
    its lowering, the binding of `a#idx` and the stores of the field operands `vs`,
    are simulated from `R` when at every fuel `R` gives the flattened array, the index
    and the field values, and the environments after the write are `R₂`-related. -/
theorem fuelSim_flatArrUpdate (hU : ArrUpdateSound bi) (hA : IdxArithSound bi) {a : String}
    {k : Nat} {i i' x body body' : ImpExpr} {vs : List ImpExpr} (hlen : vs.length = k)
    (hat : ∀ v ∈ vs, storeAtom a (elemIdxName a) v = true) (hax : a ≠ elemIdxName a)
    {R R₂ Rx : Env → Env → Prop}
    (hR : ∀ fuel env envF, R env envF → ∃ (rows : List (List Value)) (j : Nat) (ws : List Value),
      (∀ r ∈ rows, r.length = k) ∧ j < rows.length ∧ ws.length = k ∧
      (∀ w ∈ ws, w.isControlFlow = false) ∧
      env a = some (.array (rows.map (structVal k))) ∧ envF a = some (.array rows.flatten) ∧
      (denote' bi fuel i).run env = (.val (.int j), env) ∧
      (denote' bi fuel i').run envF = (.val (.int j), envF) ∧
      (denote' bi fuel x).run env = (.val (structVal k ws), env) ∧
      (∀ s (h : s < vs.length), atomVal envF vs[s] = ws[s]?) ∧
      ∀ envF2, envF2 a = some (.array (rows.set j ws).flatten) →
        (∀ y, y ≠ a → y ≠ elemIdxName a → envF2 y = envF y) →
        R₂ (env.extend a (.array ((rows.set j ws).map (structVal k)))) envF2)
    (hb : FuelSim bi R₂ Rx body body') :
    FuelSim bi R Rx (.letBind a (.app "array_update" [.var a, i, x]) body)
      (.letBind (elemIdxName a) i' (storeElems a (elemIdxName a) k 0 vs body')) := by
  refine FuelSim.of_step (fun fuel env envF hR0 => ?_) hb
  obtain ⟨rows, j, ws, hrow, hj, hws, hcf, ha, haF, hi, hi', hx, hvs, hR₂⟩ := hR fuel env envF hR0
  obtain ⟨envF2, h1, h2, h3, h4⟩ := flatArrUpdate_sim bi fuel hU hA a k i i' x body body' vs
    env envF rows j ws hrow hj hws hcf ha haF hi hi' hx hlen hat hvs hax
  exact ⟨_, _, h1, h2, hR₂ envF2 h3 h4⟩

/-- **Flattened element field read through a struct field.**  A `Corres` statement
    for the field call `c` on `index(s.f, x)` holds for the read of the flat array in
    the component variable of `f` at `x * k + off`, from the environments in which the
    array field is flattened and `x` holds an in-range index. -/
theorem corres_flatFieldElemField (hI : ArrIndexSound bi) (hA : IdxArithSound bi)
    {c s f x : String} {fs gs : List String} {off : Nat} (hFo : FieldSound bi fs)
    (hFi : FieldSound bi gs) (hoff : fieldIdx gs c = some off)
    {P Q : Env → S → Prop} {G : S → Prop} {V : S → Value}
    (h : Corres bi P G (.app c [.app "index" [.app ("." ++ f) [.var s], .var x]]) V Q) :
    Corres bi (fun envF σ => ∃ env, P env σ ∧ FieldElemReadAt fs gs.length s f x env envF) G
      (.app "index" [.var (structCompName s f), flatIdx (.var x) gs.length off]) V
      (fun envF σ => ∃ env, Q env σ ∧ FieldElemReadAt fs gs.length s f x env envF) := by
  refine corres_of_fuelSim (fun fuel env envF hR => ?_) h
  obtain ⟨w, h1, h2⟩ := flatFieldElemField_sim bi fuel hI hA c s f x fs gs off env envF
    hFo hFi hoff hR
  rw [h1, h2]
  exact ⟨rfl, hR⟩

end ArrTransport

/-! ## `Option` arms -/

section OptionArms

variable {S : Type} {bi : Builtins}

/-- After `let o = Some v` and its lowering, `o` is flattened. -/
theorem optFlatAt_bindSome (o : String) (env envF : Env) (v : Value) :
    OptFlatAt o (env.extend o (.option (some v)))
      ((envF.extend (optValName o) v).extend (optTagName o) (.bool true)) := by
  refine ⟨some v, _root_.Hax.Env.extend_same _ _ _, _root_.Hax.Env.extend_same _ _ _, ?_⟩
  intro y hy
  cases hy
  rw [_root_.Hax.Env.extend_other _ _ _ _ (optTagName_ne_optValName o).symm,
    _root_.Hax.Env.extend_same]

/-- After `let o = None` and its lowering, `o` is flattened. -/
theorem optFlatAt_bindNone (o : String) (env envF : Env) :
    OptFlatAt o (env.extend o (.option none)) (envF.extend (optTagName o) (.bool false)) :=
  ⟨none, _root_.Hax.Env.extend_same _ _ _, _root_.Hax.Env.extend_same _ _ _,
    fun _ h => by cases h⟩

/-- **`let o = Some y`.**  The binding and its lowering `optBindArm` are simulated from
    `R` when `R` gives the same value of `y` on both sides and the environments after
    the binding are `R₂`-related. -/
theorem fuelSim_optBindSome {o y : String} {body body' e' : ImpExpr} (hO : OptionSound bi)
    (he : optBindArm o (.app "Some" [.var y]) (.app "Some" [.var y]) body' = some e')
    {R R₂ Rx : Env → Env → Prop}
    (hR : ∀ env envF, R env envF → ∃ v, env y = some v ∧ envF y = some v ∧
      v.isControlFlow = false ∧
      R₂ (env.extend o (.option (some v)))
        ((envF.extend (optValName o) v).extend (optTagName o) (.bool true)))
    (hb : FuelSim bi R₂ Rx body body') :
    FuelSim bi R Rx (.letBind o (.app "Some" [.var y]) body) e' := by
  refine FuelSim.of_step (fun fuel env envF hR0 => ?_) hb
  obtain ⟨v, hy, hyF, hv, h2⟩ := hR env envF hR0
  obtain ⟨h1, h1', -⟩ := optBind_some_sim bi fuel o (.var y) (.var y) body body' e' env env
    envF envF v hO he (by rw [denote'_var_run, hy]) hv (by rw [denote'_var_run, hyF])
  exact ⟨_, _, h1, h1', h2⟩

/-- **`let o = None`.**  The binding and its lowering `optBindArm` are simulated from
    `R` when the environments after the binding are `R₂`-related. -/
theorem fuelSim_optBindNone {o : String} {body body' e' : ImpExpr} (hO : OptionSound bi)
    (he : optBindArm o (.app "None" []) (.app "None" []) body' = some e')
    {R R₂ Rx : Env → Env → Prop}
    (hR : ∀ env envF, R env envF →
      R₂ (env.extend o (.option none)) (envF.extend (optTagName o) (.bool false)))
    (hb : FuelSim bi R₂ Rx body body') :
    FuelSim bi R Rx (.letBind o (.app "None" []) body) e' := by
  refine FuelSim.of_step (fun fuel env envF hR0 => ?_) hb
  obtain ⟨h1, h1', -⟩ := optBind_none_sim bi fuel o body body' e' env envF hO he
  exact ⟨_, _, h1, h1', hR env envF hR0⟩

/-- **`Option` match.**  The match and its lowering `optMatchArm`, the branch on the
    tag, are simulated from `R` when `R` flattens `o`, the `Some` arm is simulated by
    its renaming from the entry environment extended at the binder, and the `None` arm
    by its lowering. -/
theorem fuelSim_optMatch {ov : List String} {o v : String} {e2 e1 e2' e1' e' : ImpExpr}
    (h : optMatchArm ov o v e2' e1' = some e') {R Rx : Env → Env → Prop}
    (hR : ∀ env envF, R env envF → OptFlatAt o env envF)
    (hs : FuelSim bi (fun env₂ envF => ∃ env x, R env envF ∧ env o = some (.option (some x)) ∧
      env₂ = env.extend v x) Rx e2 (renameVar v (optValName o) e2'))
    (hn : FuelSim bi (fun env envF => R env envF ∧ env o = some (.option none)) Rx e1 e1') :
    FuelSim bi R Rx (.match_ (.var o) [(.somePat (.varPat v), e2), (.nonePat, e1)]) e' := by
  intro fuel env envF hR0
  obtain ⟨ox, hs0, h1, h2, -⟩ := optMatch_sim bi fuel ov o v e2 e1 e2' e1' e' env envF h
    (hR env envF hR0)
  rw [h1, h2]
  cases ox with
  | some x => exact hs fuel _ _ ⟨env, x, hR0, hs0, rfl⟩
  | none => exact hn fuel _ _ ⟨hR0, hs0⟩

/-- **`Option` tail value, `Some`.**  `Some y` corresponds to the `Option` of the value
    of `y`, and its lowering `optReturn T` to the value of `y`, with the tag `true`
    in `T`. -/
theorem corres_optReturnSome {T y : String} {e' : ImpExpr} (hO : OptionSound bi)
    (he : optReturn T (.app "Some" [.var y]) = some e') (hT : y ≠ T)
    {P : Env → S → Prop} {G : S → Prop} {Y : S → Value}
    (hy : ∀ env σ, P env σ → G σ → env y = some (Y σ))
    (hplain : ∀ σ, G σ → (Y σ).isControlFlow = false) :
    Corres bi P G (.app "Some" [.var y]) (fun σ => .option (some (Y σ))) P ∧
      Corres bi P G e' Y (fun envF σ => ∃ env, P env σ ∧ envF = env.extend T (.bool true)) :=
  ⟨_root_.Hax.Ascent.corres_some hO.1 (_root_.Hax.Ascent.corres_var hy) hplain,
    fun env σ hP hG => ⟨0, _, ⟨env, hP, rfl⟩, fun fuel _ =>
      (optReturn_some_sim bi fuel T y env (Y σ) e' hO (hy env σ hP hG) (hplain σ hG) hT he).2⟩⟩

/-- **`Option` tail value, `None`.**  `None` corresponds to the empty `Option`, and its
    lowering `optReturn T` to the word `0`, with the tag `false` in `T`. -/
theorem corres_optReturnNone {T : String} {e' : ImpExpr} (hO : OptionSound bi)
    (he : optReturn T (.app "None" []) = some e') (P : Env → S → Prop) (G : S → Prop) :
    Corres bi P G (.app "None" []) (fun _ => .option none) P ∧
      Corres bi P G e' (fun _ => Value.ofLit (.uintLit .w64 0))
        (fun envF σ => ∃ env, P env σ ∧ envF = env.extend T (.bool false)) :=
  ⟨_root_.Hax.Ascent.corres_none P G hO.2,
    fun env _ hP _ => ⟨0, _, ⟨env, hP, rfl⟩, fun fuel _ =>
      (optReturn_none_sim bi fuel T env e' hO he).2⟩⟩

/-- **`Option` early return, `Some`.**  `cfBreak (Some y)` throws the `Option` of the
    value of `y`, and its lowering `optBreak T` throws the value of `y`, with the tag
    `true` in `T`. -/
theorem corresX_optBreakSome {T y : String} {e' : ImpExpr} (hO : OptionSound bi)
    (he : optBreak T (.app "Some" [.var y]) = some e') (hT : y ≠ T)
    {P : Env → S → Prop} {G : S → Prop} {Y : S → Value}
    (hy : ∀ env σ, P env σ → G σ → env y = some (Y σ))
    (hplain : ∀ σ, G σ → (Y σ).isControlFlow = false) :
    CorresX bi P G (.cfBreak (.app "Some" [.var y])) (fun σ => .error (.option (some (Y σ)))) P ∧
      CorresX bi P G e' (fun σ => .error (Y σ))
        (fun envF σ => ∃ env, P env σ ∧ envF = env.extend T (.bool true)) :=
  ⟨_root_.Hax.Ascent.corresX_throw
      (_root_.Hax.Ascent.corres_some hO.1 (_root_.Hax.Ascent.corres_var hy) hplain)
      (fun _ _ => rfl),
    fun env σ hP hG => ⟨0, _, ⟨env, hP, rfl⟩, fun fuel _ =>
      (optBreak_some_sim bi fuel T y env (Y σ) e' hO (hy env σ hP hG) (hplain σ hG) hT he).2⟩⟩

/-- **`Option` early return, `None`.**  `cfBreak None` throws the empty `Option`, and
    its lowering `optBreak T` throws the word `0`, with the tag `false` in `T`. -/
theorem corresX_optBreakNone {T : String} {e' : ImpExpr} (hO : OptionSound bi)
    (he : optBreak T (.app "None" []) = some e') (P : Env → S → Prop) (G : S → Prop) :
    CorresX bi P G (.cfBreak (.app "None" [])) (fun _ => .error (.option none)) P ∧
      CorresX bi P G e' (fun _ => .error (Value.ofLit (.uintLit .w64 0)))
        (fun envF σ => ∃ env, P env σ ∧ envF = env.extend T (.bool false)) :=
  ⟨_root_.Hax.Ascent.corresX_throw (_root_.Hax.Ascent.corres_none P G hO.2) (fun _ _ => rfl),
    fun env _ hP _ => ⟨0, _, ⟨env, hP, rfl⟩, fun fuel _ =>
      (optBreak_none_sim bi fuel T env e' hO he).2⟩⟩

end OptionArms

/-! ## Call results, copies and named returns -/

section Calls

variable {S : Type} {bi : Builtins}

/-- **Call result.**  `let n = val; body` and its lowering, the binding of `n#tup` and
    the reads of its components, are simulated from `R` when at every fuel `val`
    returns the struct value and `val'` the tuple of the same components, and every
    environment in which `n` is then flattened, agreeing with the exit environment of
    `val'` off `n#tup` and the components of `n`, is `R₂`-related to the source. -/
theorem fuelSim_callBind {n : String} {fs : List String} (hnd : fs.Nodup)
    {val val' body body' : ImpExpr} {R R₂ Rx : Env → Env → Prop}
    (hval : ∀ fuel env envF, R env envF → ∃ (vs : List Value) (env1 envF1 : Env),
      vs.length = fs.length ∧ (∀ v ∈ vs, v.isControlFlow = false) ∧
      (denote' bi fuel val).run env = (.val (structVal fs.length vs), env1) ∧
      (denote' bi fuel val').run envF = (.val (.tuple vs), envF1) ∧
      ∀ envF2, StructFlatAt fs n (env1.extend n (structVal fs.length vs)) envF2 →
        (∀ x, x ≠ structTupName n → (∀ f ∈ fs, x ≠ structCompName n f) → envF2 x = envF1 x) →
        R₂ (env1.extend n (structVal fs.length vs)) envF2)
    (hb : FuelSim bi R₂ Rx body body') :
    FuelSim bi R Rx (.letBind n val body) (.letBind (structTupName n) val'
      (bindProjs (structTupName n) 0 (fs.map (structCompName n)) body')) := by
  refine FuelSim.of_step (fun fuel env envF hR => ?_) hb
  obtain ⟨vs, env1, envF1, hlen, hcf, hx, hx', hR₂⟩ := hval fuel env envF hR
  obtain ⟨envF2, h1, h2, h3, h4⟩ := callBind_sim bi fuel n fs val val' body body' env env1 envF
    envF1 vs hnd hlen hcf hx hx'
  exact ⟨_, _, h1, h2, hR₂ envF2 h3 h4⟩

/-- **Call result, one field.**  `let n = val; body` of a one-field struct and its
    lowering, the binding of the component variable to `val'`, are simulated from `R`
    when at every fuel `val` and `val'` return the same value and the environments
    after the binding are `R₂`-related. -/
theorem fuelSim_callBind1 {n f : String} {val val' body body' : ImpExpr}
    {R R₂ Rx : Env → Env → Prop}
    (hval : ∀ fuel env envF, R env envF → ∃ (v : Value) (env1 envF1 : Env),
      v.isControlFlow = false ∧ (denote' bi fuel val).run env = (.val v, env1) ∧
      (denote' bi fuel val').run envF = (.val v, envF1) ∧
      R₂ (env1.extend n v) (envF1.extend (structCompName n f) v))
    (hb : FuelSim bi R₂ Rx body body') :
    FuelSim bi R Rx (.letBind n val body) (.letBind (structCompName n f) val' body') := by
  refine FuelSim.of_step (fun fuel env envF hR => ?_) hb
  obtain ⟨v, env1, envF1, hv, hx, hx', hR₂⟩ := hval fuel env envF hR
  obtain ⟨h1, h2, -⟩ :=
    callBind1_sim bi fuel n f val val' body body' env env1 envF envF1 v hv hx hx'
  exact ⟨_, _, h1, h2, hR₂⟩

/-- **Update with a copy.**  `let s = struct_update#S#i#n(s, y); body` and its
    lowering, the copy of `y` into the component of field `f`, are simulated from `R`
    when `R` flattens `s` and gives the same value of `y` on both sides, and every
    pair of environments in which `s` is flattened is `R₂`-related. -/
theorem fuelSim_flatUpdateCopy {S' s f y : String} {fs : List String} {i : Nat}
    {body body' : ImpExpr} (hU : UpdateSound bi S' fs) (hi : fs[i]? = some f)
    (huniq : ∀ j, fs[j]? = some f → j = i) {R R₂ Rx : Env → Env → Prop}
    (hR : ∀ env envF, R env envF → StructFlatAt fs s env envF ∧ ∃ v, env y = some v ∧
      envF y = some v ∧ v.isControlFlow = false ∧
      ∀ env2 envF2, StructFlatAt fs s env2 envF2 → R₂ env2 envF2)
    (hb : FuelSim bi R₂ Rx body body') :
    FuelSim bi R Rx
      (.letBind s (.app (_root_.Hax.structUpdateHead S' i fs.length) [.var s, .var y]) body)
      (.letBind (structCompName s f) (.var y) body') := by
  refine FuelSim.of_step (fun fuel env envF hR0 => ?_) hb
  obtain ⟨hsf, v, hy, hyF, hv, hR₂⟩ := hR env envF hR0
  obtain ⟨env2, envF2, h1, h2, h3⟩ := flatUpdateCopy_sim bi fuel S' s f y fs i body body' env
    envF v hU hi huniq hsf hy hyF hv
  exact ⟨_, _, h1, h2, hR₂ env2 envF2 h3⟩

/-- **Named tuple return.**  A returned tuple with the variables `rs` evaluates to the
    same tuple from any two environments that agree on `rs`, changing neither. -/
theorem fuelSim_retVars {es : List ImpExpr} {rs : List String} (h : retVars es = some rs) :
    FuelSim bi (RetAt rs) (RetAt rs) (.tuple es) (.tuple es) := by
  intro fuel env envF hR
  obtain ⟨vals, h1, h2⟩ := denoteArgs'_retVars bi fuel es rs h env envF hR
  rw [denote'_tuple_run_some bi fuel es env env vals h1,
    denote'_tuple_run_some bi fuel es envF envF vals h2]
  exact ⟨rfl, hR⟩

/-- **Named tuple return under `Corres`.**  A `Corres` statement for a returned tuple
    with the variables `rs` holds from every environment agreeing on `rs` with an entry
    environment: the result `namedRet` leaves in `rs` reads back as the same value. -/
theorem corres_retVars {es : List ImpExpr} {rs : List String} (h : retVars es = some rs)
    {P Q : Env → S → Prop} {G : S → Prop} {V : S → Value}
    (hc : Corres bi P G (.tuple es) V Q) :
    Corres bi (fun envF σ => ∃ env, P env σ ∧ RetAt rs env envF) G (.tuple es) V
      (fun envF σ => ∃ env, Q env σ ∧ RetAt rs env envF) :=
  corres_of_fuelSim (fuelSim_retVars h) hc

end Calls

/-! ## The exit-flag lowering under `CorresX` -/

section Exit

variable {S : Type} {bi : Builtins} {N : Nat} {leafSpec : LeafSpec}

/-- **Expression.**  For an expression the lowering simulates, a `CorresX`
    statement gives, from every related entry environment and agreeing state, a
    related exit environment and a `RustExec` run of the lowered command ending in
    agreement with the outcome `val (excVal (R σ))`. -/
theorem exitSim_corresX {e : ImpExpr} (hsim : ExitSim bi N leafSpec e)
    {P Q : Env → S → Prop} {G : S → Prop} {R : S → Except Value Value}
    (hX : CorresX bi P G e R Q) {tl : Bool} {fl : Option String} {c : LowCT} {x : Bool}
    (hok : exitSimOk tl fl.isSome e = true) (hctx : RunCtx fl)
    (hK : haxToLowCTK true tl fl e = some (c, x)) {env : Env} {σ : S} (hP : P env σ)
    (hG : G σ) {rs : RustState} (hag : envAgreesOff env rs)
    (h0 : rs.rsScalar exitRetName = 0) :
    ∃ env', Q env' σ ∧ ∃ rs', RustExec N leafSpec c rs rs' ∧
      envAgreesExit tl (.val (excVal (R σ))) env' rs' ∧
      (x = false → rs'.rsScalar exitRetName = 0) := by
  obtain ⟨f₀, env', hQ, hrun⟩ := hX env σ hP hG
  obtain ⟨rs', h1, h2, h3⟩ := hsim tl fl f₀ env env' _ rs c x hok hctx hK
    (hrun f₀ (Nat.le_refl _)) ⟨_, rfl⟩ hag h0
  exact ⟨env', hQ, rs', h1, h2, h3⟩

/-- The value an exception result carries: the thrown value or the normal result. -/
def excPayload : Except Value Value → Value
  | .error w => w
  | .ok u => u

/-- The scalar of a value outcome is the scalar of the value its exception reading
    carries. -/
theorem outcomeScalar_val_cfExcept (v : Value) :
    outcomeScalar (.val v) = valueToScalar (excPayload (_root_.Hax.Ascent.cfExcept v)) := by
  cases v with
  | controlFlow b w => cases b <;> rfl
  | _ => rfl

/-- The scalar of the outcome `val (excVal r)` is the scalar of the value `r`
    carries. -/
theorem outcomeScalar_excVal {r : Except Value Value} (h : ExcPlain r) :
    outcomeScalar (.val (excVal r)) = valueToScalar (excPayload r) := by
  rw [outcomeScalar_val_cfExcept, _root_.Hax.Ascent.cfExcept_excVal h]

/-- **Function.**  For a function body in the fragment, a `CorresX` statement with
    plain normal results gives a run of the lowered function whose result slot
    holds the decoding of the thrown or returned value. -/
theorem haxToLowCTFn_corresX (hs : ScalarOpsSound bi) {e : ImpExpr} {c : LowCT}
    (hok : exitSimOk true true e = true) (hK : haxToLowCTFn e = some c)
    {P Q : Env → S → Prop} {G : S → Prop} {R : S → Except Value Value}
    (hX : CorresX bi P G e R Q) (hplain : ∀ σ, G σ → ExcPlain (R σ)) {env : Env} {σ : S}
    (hP : P env σ) (hG : G σ) {rs : RustState} (hag : envAgreesOff env rs) :
    ∃ rs', RustExec N leafSpec c rs rs' ∧
      valueToScalar (excPayload (R σ)) = some (rs'.rsScalar exitResName) := by
  obtain ⟨f₀, env', _, hrun⟩ := hX env σ hP hG
  obtain ⟨rs', h1, h2⟩ := haxToLowCTFn_simulates_exit bi N leafSpec hs e c hok hK f₀ env env'
    _ rs (hrun f₀ (Nat.le_refl _)) ⟨_, rfl⟩ hag
  exact ⟨rs', h1, by rw [← outcomeScalar_excVal (hplain σ hG)]; exact h2⟩

/-- **Function, top-level form.**  A `FnCorresX` statement for a function body in
    the fragment gives, for every argument meeting the guard, a run of the lowered
    function whose result slot holds the decoding of the encoded thrown or returned
    value. -/
theorem haxToLowCTFn_fnCorresX {A Rt β : Type} [_root_.Hax.Ascent.HaxEnc Rt]
    [_root_.Hax.Ascent.HaxEnc β] (hs : ScalarOpsSound bi) {e : ImpExpr} {c : LowCT}
    (hok : exitSimOk true true e = true) (hK : haxToLowCTFn e = some c)
    {entry : A → Env} {G : A → Prop} {f : A → Except Rt β}
    (h : FnCorresX bi e entry G f) {a : A} (hG : G a) {rs : RustState}
    (hag : envAgreesOff (entry a) rs) :
    ∃ rs', RustExec N leafSpec c rs rs' ∧
      valueToScalar (excPayload (encExc (f a))) = some (rs'.rsScalar exitResName) := by
  obtain ⟨f₀, hrun⟩ := h a hG
  have h₀ := hrun f₀ (Nat.le_refl _)
  rcases ho : denote' bi f₀ e (entry a) with ⟨o, env'⟩
  rw [ho] at h₀
  cases o with
  | val v =>
    obtain ⟨rs', h1, h2⟩ := haxToLowCTFn_simulates_exit bi N leafSpec hs e c hok hK f₀
      (entry a) env' (.val v) rs ho ⟨_, rfl⟩ hag
    refine ⟨rs', h1, ?_⟩
    have hc : _root_.Hax.Ascent.cfExcept v = encExc (f a) := Option.some.inj h₀
    rw [← hc, ← outcomeScalar_val_cfExcept]; exact h2
  | _ => cases h₀

end Exit

end CatCrypt.Crypto.Hax
