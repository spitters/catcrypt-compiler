/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Hax.PrimeirBuiltins
public import CatCrypt.Crypto.Hax.ImpToNF
public import CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect

/-!
# The name table of the `primeir-hax` library calls

A Rust function written against the `primeir-hax` library calls its trait methods by name;
`haxpipeT` emits such a call as `ImpExpr.app f args` with the head `f`. An `OpTable` is the
list of names through which these calls reach the dialect ops: each entry `OpEntry` gives
the name, the kinds of its arguments and of its result (`ArgKind`: a field element at the
modulus parameter `p`, an integer, a byte string), and the op key `OpKey` naming the
dialect op. Entries are keyed by name: the first entry of a name is the one a call reads.

From a table `T` three objects are derived.

* `T.sigOf` — the call typing passed to `impToNF`: a call of the name of an entry at the
  types of its argument kinds has the type of its result kind.
* `T.builtins p` — the reference semantics passed to the interpreter: a call of the name of
  an entry on values of its argument kinds is the operation of its key, for a field key the
  operation of `ZMod p` on representatives reduced by `Int.emod`; every other call is
  `defaultBuiltins`.
* `T.toOp p` — the translation of a call on field variables to the op of `fieldDialect` of
  its key. The dialect has dedicated ops for every field key: `add`, `sub`, `mul`, `neg`
  are `fAdd`, `fSub`, `fMul`, `fNeg`; `square` and `double` are `fieldSquare` and
  `fieldDouble`; the constants `zero` and `one` are `fConst p 0` and `fConst p 1`.

The per-entry hypothesis `OpEntry.ok` states that the kinds of an entry with a field key are
those of the key: as many field elements as the arity of the key, and a field element as
result. Under it, `OpTable.typedCalls` gives the typing hypothesis of `impToNF_sound`, and
`OpTable.toOp_sound` states that the builtin of a translated call, on integers whose
residues are the values of the field variables, returns an integer whose residue is the
denotation of the op.

The op keys of the ring, tower, binary-field and codec families (`OpKey.ring`,
`OpKey.tower`, `OpKey.gf2`, `OpKey.codec`) name ops without a semantics in this module:
their builtin is `none` on calls of their kinds and `toOp` does not translate them.

## Known limitation of bare heads

`defaultFieldTable` contains the bare heads the library exports today (`"add"`, `"mul"`,
…, and the constants `"::clsitem::Field::ZERO::F"`, `"::clsitem::Field::ONE::F"`). With bare
heads, an integer `mul` and a field `mul` share a name, and `T.builtins p` reads every call of
`"mul"` on two integers as the field product modulo `p`. The semantics of the table is the
intended one only for functions whose integer-typed calls with these names are field calls.
Qualified heads (`primeir_hax::Field::mul`, plan row PL-2) remove the ambiguity; the table
carries the same entries under these names.

## Main definitions

* `ArgKind`, `FieldKey`, `OpKey`, `OpEntry`, `OpTable` — the table.
* `OpTable.entry?`, `OpTable.sigOf`, `OpTable.builtins`, `OpTable.toOp` — the lookup, the call
  typing, the reference builtins and the translation to `fieldDialect`.
* `OpEntry.ok`, `OpTable.ok` — the per-entry hypothesis and its conjunction over a table.
* `fieldEntry`, `bareFieldEntries`, `qualifiedFieldEntries`, `defaultFieldTable` — the
  field table under bare and qualified heads.

## Main results

* `OpTable.typedCalls` — `TypedCalls (T.builtins p) T.sigOf` for every table with `T.ok`.
* `FieldKey.toExpr_sound`, `OpTable.toOp_sound` — a translated call computes the residue of
  the denotation of its op.
* `defaultFieldTable_ok`, `defaultFieldTable_typedCalls` — the hypothesis of the default
  table and its call typing.
* `defaultFieldTable_builtins_bare` — on the six bare op heads and every list of integers the
  builtins of the default table are `primeirBuiltins p`.
* `defaultFieldTable_builtins_qualified₂`, `defaultFieldTable_builtins_qualified₁` — a
  qualified op head, on integers of its arity, reads as its bare head.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Hax.PrimeirNames

open _root_.Hax (Value Builtins defaultBuiltins)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.Hax.ImpToNF (TypedCalls enc dec encAll)
open Ctxt (Var Valuation)

/-! ## 1. The table -/

/-- The kind of an argument or a result of a library call. -/
inductive ArgKind where
  /-- An element of the prime field of the modulus parameter, carried as an integer. -/
  | fp
  /-- An unbounded integer. -/
  | int
  /-- A byte string, carried as an array of `u8` values. -/
  | bytes
  deriving DecidableEq, Repr

/-- The type of `nfDialect` carrying a value of a kind. -/
def ArgKind.ty : ArgKind → NfTy
  | .fp => .int
  | .int => .int
  | .bytes => .slice (.uint .w8)

/-- A source value has the shape of a kind: an integer for `fp` and `int`, an array for
    `bytes`. -/
def ArgKind.fits : ArgKind → Value → Bool
  | .fp, .int _ => true
  | .int, .int _ => true
  | .bytes, .array _ => true
  | _, _ => false

/-- A list of source values has the shapes of a list of kinds, of the same length. -/
def ArgKind.fitsAll : List ArgKind → List Value → Bool
  | [], [] => true
  | k :: ks, v :: vs => k.fits v && fitsAll ks vs
  | _, _ => false

/-- The op keys of the prime-field family. -/
inductive FieldKey where
  | add
  | sub
  | mul
  | neg
  | square
  | double
  /-- The constant `0`. -/
  | zero
  /-- The constant `1`. -/
  | one
  deriving DecidableEq, Repr

/-- The op key of an entry: the dialect op a call of the entry denotes. -/
inductive OpKey where
  /-- An op of `fieldDialect`. -/
  | field (k : FieldKey)
  /-- A polynomial-ring op, named by its library method. -/
  | ring (op : String)
  /-- An extension-field op of `towerDialect`, named by its library method. -/
  | tower (op : String)
  /-- A binary-field op of `gf2Dialect`, named by its library method. -/
  | gf2 (op : String)
  /-- A codec op, named by its library method. -/
  | codec (op : String)
  deriving DecidableEq, Repr

/-- An entry of the name table: the call name, the kinds of its arguments and of its result,
    and its op key. -/
structure OpEntry where
  name : String
  args : List ArgKind
  res : ArgKind
  key : OpKey
  deriving DecidableEq, Repr

/-- A name table: a list of entries, keyed by name (the first entry of a name counts). -/
structure OpTable where
  entries : List OpEntry
  deriving Repr

/-! ## 2. The field keys -/

/-- The number of arguments of a field key. -/
def FieldKey.arity : FieldKey → Nat
  | .add | .sub | .mul => 2
  | .neg | .square | .double => 1
  | .zero | .one => 0

/-- The reference semantics of a field key on integer representatives: the operation of
    `ZMod p`, reduced by `Int.emod` to the canonical representative for `0 < p`. -/
def FieldKey.sem (p : Nat) : FieldKey → List Value → Option Value
  | .add, [.int a, .int b] => some (.int ((a + b) % (p : Int)))
  | .sub, [.int a, .int b] => some (.int ((a - b) % (p : Int)))
  | .mul, [.int a, .int b] => some (.int ((a * b) % (p : Int)))
  | .neg, [.int a] => some (.int ((-a) % (p : Int)))
  | .square, [.int a] => some (.int ((a * a) % (p : Int)))
  | .double, [.int a] => some (.int ((a + a) % (p : Int)))
  | .zero, [] => some (.int 0)
  | .one, [] => some (.int (1 % (p : Int)))
  | _, _ => none

/-- The expression of `fieldDialect` of a field key on field variables. -/
def FieldKey.toExpr (p : Nat) {Δ : Ctxt fieldDialect} :
    FieldKey → List (Var Δ (FieldTy.fp p)) → Option (Expr fieldDialect Δ (FieldTy.fp p))
  | .add, [a, b] => some ⟨.fAdd p, rfl, .cons a (.cons b .nil)⟩
  | .sub, [a, b] => some ⟨.fSub p, rfl, .cons a (.cons b .nil)⟩
  | .mul, [a, b] => some ⟨.fMul p, rfl, .cons a (.cons b .nil)⟩
  | .neg, [a] => some ⟨.fNeg p, rfl, .cons a .nil⟩
  | .square, [a] => some ⟨.fieldSquare p, rfl, .cons a .nil⟩
  | .double, [a] => some ⟨.fieldDouble p, rfl, .cons a .nil⟩
  | .zero, [] => some ⟨.fConst p 0, rfl, .nil⟩
  | .one, [] => some ⟨.fConst p 1, rfl, .nil⟩
  | _, _ => none

/-! ## 3. The objects derived from a table -/

/-- The semantics of an entry: the semantics of its key for a field key, `none` otherwise. -/
def OpEntry.sem (p : Nat) (e : OpEntry) : List Value → Option Value :=
  match e.key with
  | .field k => k.sem p
  | _ => fun _ => none

/-- **The per-entry hypothesis.** An entry with a field key takes as many field elements as
    the arity of its key and returns a field element. -/
def OpEntry.ok (e : OpEntry) : Bool :=
  match e.key with
  | .field k => e.args == List.replicate k.arity .fp && e.res == .fp
  | _ => true

/-- The per-entry hypothesis holds for every entry of a table. -/
def OpTable.ok (T : OpTable) : Bool := T.entries.all OpEntry.ok

/-- The entry of a name: the first entry of the table with this name. -/
def OpTable.entry? (T : OpTable) (f : String) : Option OpEntry :=
  T.entries.find? (·.name == f)

/-- **The call typing of a table.** A call of the name of an entry at the types of its
    argument kinds has the type of its result kind. -/
def OpTable.sigOf (T : OpTable) (f : String) (as : List NfTy) : Option NfTy :=
  (T.entry? f).bind fun e => if e.args.map ArgKind.ty = as then some e.res.ty else none

/-- **The reference builtins of a table.** A call of the name of an entry on values of the
    shapes of its argument kinds is the semantics of the entry; every other call is
    `defaultBuiltins`. -/
def OpTable.builtins (T : OpTable) (p : Nat) : Builtins := fun f vs =>
  match T.entry? f with
  | some e => if ArgKind.fitsAll e.args vs then e.sem p vs else defaultBuiltins f vs
  | none => defaultBuiltins f vs

/-- **The translation of a call to `fieldDialect`**: the op of the field key of the entry of
    the name, on the field variables `args`. -/
def OpTable.toOp (T : OpTable) (p : Nat) {Δ : Ctxt fieldDialect} (f : String)
    (args : List (Var Δ (FieldTy.fp p))) : Option (Expr fieldDialect Δ (FieldTy.fp p)) :=
  (T.entry? f).bind fun e =>
    match e.key with
    | .field k => k.toExpr p args
    | _ => none

/-! ## 4. Soundness -/

/-- The encodings of values of the types of a list of kinds have the shapes of the kinds. -/
theorem ArgKind.fitsAll_encAll :
    ∀ (ks : List ArgKind) (xs : HVector NfTy.denote (ks.map ArgKind.ty)),
      ArgKind.fitsAll ks (encAll _ xs) = true
  | [], .nil => rfl
  | k :: ks, .cons x xs => by
      change (k.fits (enc k.ty x) && ArgKind.fitsAll ks (encAll _ xs)) = true
      rw [ArgKind.fitsAll_encAll ks xs, Bool.and_true]
      cases k <;> rfl

/-- The encodings of values of the types of `n` field elements are `n` integers. -/
theorem encAll_replicate_fp :
    ∀ (n : Nat) (xs : HVector NfTy.denote ((List.replicate n ArgKind.fp).map ArgKind.ty)),
      ∃ zs : List Int, encAll _ xs = zs.map Value.int
  | 0, .nil => ⟨[], rfl⟩
  | n + 1, .cons x xs => by
      obtain ⟨zs, hzs⟩ := encAll_replicate_fp n xs
      exact ⟨x :: zs, by
        change enc .int x :: encAll _ xs = _
        rw [hzs]
        rfl⟩

/-- The semantics of a field key returns integers. -/
theorem FieldKey.sem_int (p : Nat) (k : FieldKey) (zs : List Int) (v : Value)
    (h : k.sem p (zs.map Value.int) = some v) : ∃ z, v = .int z := by
  cases k <;> rcases zs with _ | ⟨a, _ | ⟨b, _ | ⟨c, zs⟩⟩⟩ <;>
    simp [FieldKey.sem] at h <;> exact ⟨_, h.symm⟩

/-- A list of integers has the shapes of as many field elements. -/
theorem ArgKind.fitsAll_replicate_fp (zs : List Int) :
    ArgKind.fitsAll (List.replicate zs.length .fp) (zs.map Value.int) = true := by
  induction zs with
  | nil => rfl
  | cons z zs ih => simpa [List.replicate_succ, ArgKind.fitsAll, ArgKind.fits] using ih

/-- An entry found by name belongs to the table. -/
theorem OpTable.mem_of_entry? {T : OpTable} {f : String} {e : OpEntry}
    (h : T.entry? f = some e) : e ∈ T.entries :=
  List.mem_of_find?_eq_some h

/-- An entry of a table with `T.ok` satisfies the per-entry hypothesis. -/
theorem OpTable.ok_of_entry? {T : OpTable} (hT : T.ok = true) {f : String} {e : OpEntry}
    (h : T.entry? f = some e) : e.ok = true :=
  List.all_eq_true.mp hT e (T.mem_of_entry? h)

/-- **The call typing of a table is sound** for its builtins, for every table satisfying the
    per-entry hypothesis. -/
theorem OpTable.typedCalls (T : OpTable) (p : Nat) (hT : T.ok = true) :
    TypedCalls (T.builtins p) T.sigOf := by
  intro f as r h xs v hv
  obtain ⟨e, he, h⟩ := Option.bind_eq_some_iff.mp h
  split_ifs at h with has
  cases h
  subst has
  have hok := T.ok_of_entry? hT he
  have hv' : e.sem p (encAll _ xs) = some v := by
    simpa only [OpTable.builtins, he, ArgKind.fitsAll_encAll, ite_true] using hv
  obtain ⟨name, args, res, key⟩ := e
  cases key with
  | field k =>
      simp only [OpEntry.ok, Bool.and_eq_true, beq_iff_eq] at hok
      obtain ⟨rfl, rfl⟩ := hok
      obtain ⟨zs, hzs⟩ := encAll_replicate_fp k.arity xs
      rw [hzs] at hv'
      obtain ⟨z, rfl⟩ := FieldKey.sem_int p k zs v hv'
      exact ⟨z, rfl, rfl⟩
  | ring _ | tower _ | gf2 _ | codec _ => simp [OpEntry.sem] at hv'

/-- **A field key computes the residue of its op.** For the expression `e'` of a field key
    on field variables `args` and integers `zs` whose residues are the values of `args` at
    `W`, the semantics of the key on `zs` is an integer whose residue is the denotation of
    `e'` at `W`. -/
theorem FieldKey.toExpr_sound (p : Nat) {Δ : Ctxt fieldDialect} (k : FieldKey)
    (args : List (Var Δ (FieldTy.fp p))) (e' : Expr fieldDialect Δ (FieldTy.fp p))
    (h : k.toExpr p args = some e') (W : Valuation Δ) (zs : List Int)
    (hz : zs.map (Int.cast : Int → ZMod p) = args.map (fun v => v.lookup W)) :
    zs.length = k.arity ∧
      ∃ z, k.sem p (zs.map Value.int) = some (.int z) ∧ (z : ZMod p) = e'.denote W := by
  cases k <;> rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, args⟩⟩⟩ <;>
    simp only [FieldKey.toExpr, reduceCtorEq, Option.some.injEq] at h <;> subst h <;>
    rcases zs with _ | ⟨x, _ | ⟨y, _ | ⟨w, zs⟩⟩⟩ <;>
    simp at hz ⊢
  all_goals
    refine ⟨rfl, _, rfl, ?_⟩
    simp only [ZMod.intCast_mod, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg,
      Int.cast_zero, Int.cast_one]
    first
    | (obtain ⟨h1, h2⟩ := hz; rw [h1, h2]; rfl)
    | (rw [hz]; rfl)
    | rfl

/-- **A translated call computes the residue of its op**, for every table satisfying the
    per-entry hypothesis. For the expression `e'` of the call `f` on field variables `args`
    and integers `zs` whose residues are the values of `args` at `W`, the builtin `f` of the
    table on `zs` returns an integer whose residue is the denotation of `e'` at `W`. -/
theorem OpTable.toOp_sound (T : OpTable) (p : Nat) (hT : T.ok = true) {Δ : Ctxt fieldDialect}
    (f : String) (args : List (Var Δ (FieldTy.fp p))) (e' : Expr fieldDialect Δ (FieldTy.fp p))
    (h : T.toOp p f args = some e') (W : Valuation Δ) (zs : List Int)
    (hz : zs.map (Int.cast : Int → ZMod p) = args.map (fun v => v.lookup W)) :
    ∃ z, T.builtins p f (zs.map Value.int) = some (.int z) ∧ (z : ZMod p) = e'.denote W := by
  obtain ⟨e, he, h⟩ := Option.bind_eq_some_iff.mp h
  have hok := T.ok_of_entry? hT he
  obtain ⟨name, eargs, res, key⟩ := e
  cases key with
  | field k =>
      simp only [OpEntry.ok, Bool.and_eq_true, beq_iff_eq] at hok
      obtain ⟨rfl, rfl⟩ := hok
      obtain ⟨hlen, z, hsem, hzv⟩ := FieldKey.toExpr_sound p k args e' h W zs hz
      refine ⟨z, ?_, hzv⟩
      simp only [OpTable.builtins, he]
      rw [← hlen, ArgKind.fitsAll_replicate_fp, ite_eq_left rfl]
      exact hsem
  | ring _ | tower _ | gf2 _ | codec _ => cases h

/-! ## 5. The default field table -/

/-- The entry of a field key under a name: as many field elements as the arity of the key,
    and a field element as result. -/
def fieldEntry (name : String) (k : FieldKey) : OpEntry :=
  ⟨name, List.replicate k.arity .fp, .fp, .field k⟩

/-- An entry built by `fieldEntry` satisfies the per-entry hypothesis. -/
theorem fieldEntry_ok (name : String) (k : FieldKey) : (fieldEntry name k).ok = true := by
  simp [fieldEntry, OpEntry.ok]

/-- The field entries under the bare heads `haxpipeT` emits for the `primeir_hax::Field`
    methods and associated constants. -/
def bareFieldEntries : List OpEntry :=
  [fieldEntry "add" .add, fieldEntry "sub" .sub, fieldEntry "mul" .mul,
   fieldEntry "neg" .neg, fieldEntry "square" .square, fieldEntry "double" .double,
   fieldEntry "::clsitem::Field::ZERO::F" .zero, fieldEntry "::clsitem::Field::ONE::F" .one]

/-- The field entries under the qualified heads of the `primeir_hax::Field` methods and
    associated constants. -/
def qualifiedFieldEntries : List OpEntry :=
  [fieldEntry "primeir_hax::Field::add" .add, fieldEntry "primeir_hax::Field::sub" .sub,
   fieldEntry "primeir_hax::Field::mul" .mul, fieldEntry "primeir_hax::Field::neg" .neg,
   fieldEntry "primeir_hax::Field::square" .square,
   fieldEntry "primeir_hax::Field::double" .double,
   fieldEntry "primeir_hax::Field::ZERO" .zero, fieldEntry "primeir_hax::Field::ONE" .one]

/-- **The default field table**: the field entries under bare and under qualified heads. -/
def defaultFieldTable : OpTable := ⟨bareFieldEntries ++ qualifiedFieldEntries⟩

/-- **The per-entry hypothesis of the default field table.** -/
theorem defaultFieldTable_ok : defaultFieldTable.ok = true := by
  simp [OpTable.ok, defaultFieldTable, bareFieldEntries, qualifiedFieldEntries, fieldEntry_ok]

/-- The call typing of the default field table is sound for its builtins. -/
theorem defaultFieldTable_typedCalls (p : Nat) :
    TypedCalls (defaultFieldTable.builtins p) defaultFieldTable.sigOf :=
  defaultFieldTable.typedCalls p defaultFieldTable_ok

/-- **The default field table generalises `primeirBuiltins`.** On the six bare op heads and
    every list of integers, the builtins of the default field table are `primeirBuiltins p`. -/
theorem defaultFieldTable_builtins_bare (p : Nat) (f : String)
    (hf : f ∈ ["add", "sub", "mul", "neg", "square", "double"]) (zs : List Int) :
    defaultFieldTable.builtins p f (zs.map Value.int) =
      CatCrypt.Hax.primeirBuiltins p f (zs.map Value.int) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases zs with _ | ⟨a, _ | ⟨b, _ | ⟨c, zs⟩⟩⟩ <;> rfl

/-- A qualified binary op head reads, on two integers, as its bare head under
    `primeirBuiltins p`. -/
theorem defaultFieldTable_builtins_qualified₂ (p : Nat) (f : String)
    (hf : f ∈ ["add", "sub", "mul"]) (a b : Int) :
    defaultFieldTable.builtins p ("primeir_hax::Field::" ++ f) [.int a, .int b] =
      CatCrypt.Hax.primeirBuiltins p f [.int a, .int b] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl <;> rfl

/-- A qualified unary op head reads, on one integer, as its bare head under
    `primeirBuiltins p`. -/
theorem defaultFieldTable_builtins_qualified₁ (p : Nat) (f : String)
    (hf : f ∈ ["neg", "square", "double"]) (a : Int) :
    defaultFieldTable.builtins p ("primeir_hax::Field::" ++ f) [.int a] =
      CatCrypt.Hax.primeirBuiltins p f [.int a] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl <;> rfl

end CatCrypt.Hax.PrimeirNames
