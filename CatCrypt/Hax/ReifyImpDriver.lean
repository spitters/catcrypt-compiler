/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Hax.ReifyImpDecode

/-!
# Rust crates for `reifyImp%` literals

The read-back check of a `reifyImp%` literal compiles the Rust function that
`Crypto.Hax.ppImpRustFnRet` prints for it in a crate that also defines the leaf functions
the function calls. The hax frontend reads a call of a crate function as a call of its
name, and the end-to-end theorems interpret each call by the builtin table, so a leaf body
never enters a statement: a leaf is a stub with the signature the call needs.

`leafStubsText carrier rep leaves` is the Rust text of those stubs: the alias
`pub type carrier = rep;` of the carrier to a Rust type `rep` that is `Copy` (the printed
code reads a tuple parameter after projecting it), and one `pub fn` per entry of `leaves`,
each taking its arguments in the carrier, returning the carrier or the Rust type the entry
names, with body `unimplemented!()`. The entries name the builtins of the table the
end-to-end theorem uses, other than the Rust constructors `Some` and `None`.

`pilots` lists, for each pilot, the Rust function name, its printed text and its leaf
stubs; `CatCrypt.Hax.ReifyImpEmit` writes them for `scripts/reify-roundtrip.sh`.

## Main definitions

* `LeafSig` — the name, the arity and the return type of a leaf
* `leafStubsText` — the Rust leaf file of a crate
* `edLeaves`, `decLeaves` — the leaves of the two pilots
* `Pilot`, `pilots` — the printed pilots and their leaf files
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Hax.ReifyImp

/-! ## Leaf stubs -/

/-- A leaf function of a printed crate: its name, its number of arguments, each in the
    carrier, and its Rust return type, the carrier when `ret = none`. -/
structure LeafSig where
  /-- The builtin name, which is the Rust function name. -/
  name : String
  /-- The number of arguments. -/
  arity : Nat
  /-- The Rust return type, the carrier when `none`. -/
  ret : Option String := none

/-- The parameter list `a0: C, a1: C, …` of `n` arguments in the carrier `C`. -/
def leafParams (carrier : String) (n : Nat) : String :=
  ", ".intercalate ((List.range n).map fun i => s!"a{i}: {carrier}")

/-- The Rust stub of a leaf: `pub fn name(a0: C, …) -> R { unimplemented!() }`. -/
def leafStub (carrier : String) (l : LeafSig) : String :=
  s!"pub fn {l.name}({leafParams carrier l.arity}) -> {l.ret.getD carrier} \{\n" ++
  "    unimplemented!()\n}\n"

/-- The Rust leaf file of a crate: the alias of the carrier `carrier` to the `Copy` Rust
    type `rep`, followed by the stubs of `leaves`. -/
def leafStubsText (carrier rep : String) (leaves : List LeafSig) : String :=
  "/// The carrier of the leaf functions; the printed code copies its values.\n" ++
  s!"pub type {carrier} = {rep};\n\n" ++ "\n".intercalate (leaves.map (leafStub carrier))

/-! ## The pilots -/

/-- The leaves of `edwardsAddImp`: the builtins of `edBi` it calls. -/
def edLeaves : List LeafSig :=
  [{ name := "d", arity := 0 }, { name := "mul", arity := 2 }, { name := "add", arity := 2 },
   { name := "sub", arity := 2 }, { name := "double", arity := 1 }]

/-- The leaves of `decodeImp`: the builtins of `decBi` other than `Some` and `None`. -/
def decLeaves : List LeafSig :=
  [{ name := "mul", arity := 2 }, { name := "isZero", arity := 1, ret := some "bool" }]

/-- A printed pilot: the Rust function name, its text, and its leaf file. -/
structure Pilot where
  /-- The Rust function name. -/
  fn : String
  /-- The text `ppImpRustFnRet` prints, `none` outside the printed fragment. -/
  text : Option String
  /-- The Rust leaf file. -/
  leaves : String

/-- The pilots, with the carrier `Fe` an alias of `u64`. -/
def pilots : List Pilot :=
  [{ fn := "edwards_add"
     text := Crypto.Hax.ppImpRustFnRet "edwards_add" [("p", edPointTy), ("q", edPointTy)]
       edPointTy (fun _ => none) edwardsAddImp
     leaves := leafStubsText "Fe" "u64" edLeaves },
   { fn := "decode"
     text := Crypto.Hax.ppImpRustFnRet "decode" [("p", edPointTy)] decRetTy (fun _ => none)
       decodeImp
     leaves := leafStubsText "Fe" "u64" decLeaves }]

end CatCrypt.Hax.ReifyImp

end
