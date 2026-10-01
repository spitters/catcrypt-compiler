/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NFProg
public import HaxLean.ImpType

/-!
# The dialect of the normal form

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

`nfDialect` is the value-semantic dialect of the normal form `NF` of `HaxLean`: words
of a width with wrapping arithmetic, comparisons and casts, bits, arrays as values
read by `index` and written by `update`, pairs, and typed leaf calls. It has no
`memref` and no opaque external call. Its denotation is monadic in `Option`: an
out-of-range index, a zero divisor, an oversized shift and a missing leaf are `none`.
The leaves come from an `NfLeafTable`, the parameter of the denotation `nfDenote T`.

The types `uint W`, `sint W`, `int`, `tnil`/`tcons` and `slice` are the types of the
values of the source semantics of `HaxLean` (`.uint`, `.sint`, `.int`, `.tuple`,
`.array`); the front `impToNF` (`Hax/ImpToNF.lean`) types its bindings with them,
reads every call as a leaf, and uses the operations `ilit` (a typed integer literal),
`ctr` and `trip` (the counter and the trip count of a counted loop) and `tnilV`,
`tconsV`, `thead`, `ttail` (tuples).

The structured programs over the dialect are `NFProg nfDialect` (`VIR/NFProg.lean`);
`word 64` is the trip counter (`HasWord64`) and `bit` the branch condition
(`HasBoolBit`).

## Main definitions

* `NfTy`, `NfTy.denote` — the value types and their Lean types.
* `NfBinOp`, `NfUnOp`, `NfPred`, `NfOp` — the operations.
* `nfDialect` — the dialect, with its `DialectSignature`, `HasWord64` and
  `HasBoolBit` instances.
* `NfLeafTable` — the typed leaves of `call`.
* `NfTy.ofLit?`, `NfTy.toInt?` — a typed integer literal and the reading of a loop
  bound.
* `nfDenoteOp`, `nfDenote` — the `Option`-valued denotation of each operation.

## Main results

* `nfDenote_denoteM` — `nfDenote T` denotes an operation by `nfDenoteOp T`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.NFDialect

open CatCrypt.Crypto.SecureCompilation.VIR

/-! ## 1. Types -/

/-- The value types of `nfDialect`: a bit, the unit type, a word of a width, an array
    of a length, and a pair; and the types of the values of the source semantics of
    `HaxLean`: an unsigned and a signed integer of an `IntWidth`, an unbounded integer,
    a tuple, built from `tnil` by `tcons`, and a slice. -/
inductive NfTy where
  /-- A bit. -/
  | bit
  /-- The unit type. -/
  | unit
  /-- A word of `w` bits. -/
  | word (w : Nat)
  /-- An array of `n` values of type `t`, as a value. -/
  | arr (n : Nat) (t : NfTy)
  /-- A pair. -/
  | pair (a b : NfTy)
  /-- An unsigned integer of the width `W`, the source value `.uint W`. -/
  | uint (W : Hax.IntWidth)
  /-- A signed integer of the width `W`, the source value `.sint W`. -/
  | sint (W : Hax.IntWidth)
  /-- An unbounded integer, the source value `.int`. -/
  | int
  /-- The empty tuple, the source value `.tuple []`. -/
  | tnil
  /-- The tuple with the first component `h` and the remaining components of the tuple
      type `t`, the source value `.tuple (v :: vs)`. -/
  | tcons (h t : NfTy)
  /-- A slice of values of type `t`, the source value `.array`. -/
  | slice (t : NfTy)
  deriving DecidableEq, Repr, Inhabited

/-- The Lean type of an `NfTy`: `Bool`, `Unit`, `BitVec w`, `Fin n → ⟦t⟧`, a product,
    `BitVec W.bits` for both integers of a width, `Int`, `Unit` and a product for the
    tuples, and a list. -/
@[reducible] def NfTy.denote : NfTy → Type
  | .bit => Bool
  | .unit => Unit
  | .word w => BitVec w
  | .arr n t => Fin n → t.denote
  | .pair a b => a.denote × b.denote
  | .uint W => BitVec W.bits
  | .sint W => BitVec W.bits
  | .int => Int
  | .tnil => Unit
  | .tcons h t => h.denote × t.denote
  | .slice t => List t.denote

@[reducible] instance : TyDenote NfTy where
  denote := NfTy.denote

/-! ## 2. Operations -/

/-- The binary word operations. Arithmetic wraps; `udiv`, `urem`, `sdiv`, `srem` fail
    on a zero divisor and the signed ones on `intMin / -1`; `shl`, `lshr`, `ashr` fail
    on a shift amount of at least the width; `mulhi` is the high half of the unsigned
    double-width product. -/
inductive NfBinOp where
  | add | sub | mul | udiv | urem | sdiv | srem
  | and | or | xor | shl | lshr | ashr | rotl | rotr | mulhi
  deriving DecidableEq, Repr, Inhabited

/-- The unary word operations: bitwise complement and wrapping negation. -/
inductive NfUnOp where
  | not | neg
  deriving DecidableEq, Repr, Inhabited

/-- The word comparisons, unsigned and signed. -/
inductive NfPred where
  | eq | ne | ult | ule | ugt | uge | slt | sle | sgt | sge
  deriving DecidableEq, Repr, Inhabited

/-- The operations of `nfDialect`. -/
inductive NfOp where
  /-- A word constant. -/
  | const (w : Nat) (v : BitVec w)
  /-- A bit constant. -/
  | constBit (b : Bool)
  /-- The unit value. -/
  | constUnit
  /-- A binary word operation at width `w`. -/
  | bin (o : NfBinOp) (w : Nat)
  /-- A unary word operation at width `w`. -/
  | un (o : NfUnOp) (w : Nat)
  /-- Zero extension or truncation from width `w` to `w'`. -/
  | cast (w w' : Nat)
  /-- Sign extension or truncation from width `w` to `w'`. -/
  | scast (w w' : Nat)
  /-- A comparison at width `w`. -/
  | cmp (p : NfPred) (w : Nat)
  /-- Bit conjunction. -/
  | andB
  /-- Bit disjunction. -/
  | orB
  /-- Bit exclusive or. -/
  | xorB
  /-- Bit equality. -/
  | eqB
  /-- Bit negation. -/
  | notB
  /-- The element of an array at a 64-bit index. -/
  | index (n : Nat) (t : NfTy)
  /-- An array with one element replaced at a 64-bit index. -/
  | update (n : Nat) (t : NfTy)
  /-- An array of `n` listed elements. -/
  | arrLit (n : Nat) (t : NfTy)
  /-- An array of `n` copies of one element. -/
  | arrRepeat (n : Nat) (t : NfTy)
  /-- A pair of two values. -/
  | mkPair (a b : NfTy)
  /-- The first component of a pair. -/
  | fst (a b : NfTy)
  /-- The second component of a pair. -/
  | snd (a b : NfTy)
  /-- A call of the leaf `f` at the argument types `args` and result type `ret`. -/
  | call (f : String) (args : List NfTy) (ret : NfTy)
  /-- The integer literal `v` at the type `t` (`NfTy.ofLit?`). -/
  | ilit (t : NfTy) (v : Int)
  /-- The loop counter `lo + i` from the lower bound `lo` and the trip index `i`. -/
  | ctr
  /-- The trip count `hi - lo` of a counted loop from the lower bound `lo` and the
      upper bound `hi` of type `t`, as a 64-bit word. -/
  | trip (t : NfTy)
  /-- The empty tuple. -/
  | tnilV
  /-- The tuple of a first component and a tuple of the remaining components. -/
  | tconsV (h t : NfTy)
  /-- The first component of a tuple. -/
  | thead (h t : NfTy)
  /-- The tuple of the components after the first. -/
  | ttail (h t : NfTy)
  deriving Repr

/-- The argument types of an operation. -/
@[reducible] def NfOp.sig : NfOp → List NfTy
  | .const _ _ | .constBit _ | .constUnit => []
  | .bin _ w | .cmp _ w => [.word w, .word w]
  | .un _ w | .cast w _ | .scast w _ => [.word w]
  | .andB | .orB | .xorB | .eqB => [.bit, .bit]
  | .notB => [.bit]
  | .index n t => [.arr n t, .word 64]
  | .update n t => [.arr n t, .word 64, t]
  | .arrLit n t => List.replicate n t
  | .arrRepeat _ t => [t]
  | .mkPair a b => [a, b]
  | .fst a b | .snd a b => [.pair a b]
  | .call _ args _ => args
  | .ilit _ _ | .tnilV => []
  | .ctr => [.int, .word 64]
  | .trip t => [.int, t]
  | .tconsV h t => [h, t]
  | .thead h t | .ttail h t => [.tcons h t]

/-- The result type of an operation. -/
@[reducible] def NfOp.ret : NfOp → NfTy
  | .const w _ => .word w
  | .constBit _ | .cmp _ _ | .andB | .orB | .xorB | .eqB | .notB => .bit
  | .constUnit => .unit
  | .bin _ w | .un _ w => .word w
  | .cast _ w' | .scast _ w' => .word w'
  | .index _ t => t
  | .update n t | .arrLit n t | .arrRepeat n t => .arr n t
  | .mkPair a b => .pair a b
  | .fst a _ => a
  | .snd _ b => b
  | .call _ _ r => r
  | .ilit t _ => t
  | .ctr => .int
  | .trip _ => .word 64
  | .tnilV => .tnil
  | .tconsV h t => .tcons h t
  | .thead h _ => h
  | .ttail _ t => t

/-- The dialect of the normal form: value-semantic words, bits, arrays and pairs, and
    typed leaf calls. -/
@[reducible] def nfDialect : Dialect := { Op := NfOp, Ty := NfTy }

instance : DialectSignature nfDialect where
  sig := NfOp.sig
  ret := NfOp.ret

/-- The trip counter of `nfDialect` is `word 64`. -/
instance : HasWord64 nfDialect where
  word := NfTy.word 64
  toNat := BitVec.toNat
  ofNat := BitVec.ofNat 64

/-- The bit of `nfDialect` is `bit`, denoting `Bool`. -/
instance : HasBoolBit nfDialect where
  bit := NfTy.bit
  toBool := id

/-! ## 3. Denotation -/

/-- The typed leaves of a call: for a name, argument types and a result type, a
    partial function on the values. `none` is a missing entry or a failing leaf. -/
structure NfLeafTable where
  /-- The leaf `f` at the argument types `args` and the result type `ret`. -/
  call : (f : String) → (args : List NfTy) → (ret : NfTy) →
    HVector NfTy.denote args → Option ret.denote

/-- The table without entries. -/
def NfLeafTable.empty : NfLeafTable := ⟨fun _ _ _ _ => none⟩

/-- A binary word operation on its operands. -/
def NfBinOp.denote (w : Nat) : NfBinOp → BitVec w → BitVec w → Option (BitVec w)
  | .add, x, y => some (x + y)
  | .sub, x, y => some (x - y)
  | .mul, x, y => some (x * y)
  | .udiv, x, y => if y = 0 then none else some (x / y)
  | .urem, x, y => if y = 0 then none else some (x % y)
  | .sdiv, x, y =>
      if y = 0 ∨ (x = BitVec.intMin w ∧ y = BitVec.allOnes w) then none else some (x.sdiv y)
  | .srem, x, y =>
      if y = 0 ∨ (x = BitVec.intMin w ∧ y = BitVec.allOnes w) then none else some (x.srem y)
  | .and, x, y => some (x &&& y)
  | .or, x, y => some (x ||| y)
  | .xor, x, y => some (x ^^^ y)
  | .shl, x, y => if y.toNat < w then some (x <<< y.toNat) else none
  | .lshr, x, y => if y.toNat < w then some (x >>> y.toNat) else none
  | .ashr, x, y => if y.toNat < w then some (x.sshiftRight y.toNat) else none
  | .rotl, x, y => some (x.rotateLeft y.toNat)
  | .rotr, x, y => some (x.rotateRight y.toNat)
  | .mulhi, x, y => some (BitVec.ofNat w (x.toNat * y.toNat / 2 ^ w))

/-- A unary word operation on its operand. -/
def NfUnOp.denote {w : Nat} : NfUnOp → BitVec w → BitVec w
  | .not, x => ~~~x
  | .neg, x => -x

/-- A comparison on its operands. -/
def NfPred.denote {w : Nat} : NfPred → BitVec w → BitVec w → Bool
  | .eq, x, y => decide (x = y)
  | .ne, x, y => !decide (x = y)
  | .ult, x, y => x.ult y
  | .ule, x, y => x.ule y
  | .ugt, x, y => y.ult x
  | .uge, x, y => y.ule x
  | .slt, x, y => x.slt y
  | .sle, x, y => x.sle y
  | .sgt, x, y => y.slt x
  | .sge, x, y => y.sle x

/-- The value of the integer literal `v` at the type `t`: an unsigned integer of a width
    when `0 ≤ v < 2 ^ W.bits`, a signed integer of a width when
    `-2 ^ (W.bits - 1) ≤ v < 2 ^ (W.bits - 1)`, and an unbounded integer; `none`
    otherwise. -/
def NfTy.ofLit? : (t : NfTy) → Int → Option t.denote
  | .uint W, v => if 0 ≤ v ∧ v < 2 ^ W.bits then some (BitVec.ofInt W.bits v) else none
  | .sint W, v =>
      if -2 ^ (W.bits - 1) ≤ v ∧ v < 2 ^ (W.bits - 1) then some (BitVec.ofInt W.bits v)
      else none
  | .int, v => some v
  | _, _ => none

/-- The integer a word, an unsigned integer of a width or an unbounded integer denotes,
    the reading of a loop bound; `none` at every other type. -/
def NfTy.toInt? : (t : NfTy) → t.denote → Option Int
  | .word _, x => some x.toNat
  | .uint _, x => some x.toNat
  | .int, x => some x
  | _, _ => none

/-- The array of `n` listed values. -/
def hvReplicateFun {t : NfTy} : (n : Nat) → HVector NfTy.denote (List.replicate n t) →
    Fin n → t.denote
  | 0, _ => Fin.elim0
  | n + 1, xs => Fin.cases (motive := fun _ => t.denote) xs.head (hvReplicateFun n xs.tail)

/-- An operation of `nfDialect` on its arguments, with the leaves of `T`. -/
def nfDenoteOp (T : NfLeafTable) : (op : NfOp) → HVector NfTy.denote op.sig →
    Option op.ret.denote
  | .const _ v, _ => some v
  | .constBit b, _ => some b
  | .constUnit, _ => some ()
  | .bin o w, args => o.denote w args.head args.tail.head
  | .un o _, args => some (o.denote args.head)
  | .cast _ w', args => some (BitVec.setWidth w' args.head)
  | .scast _ w', args => some (BitVec.signExtend w' args.head)
  | .cmp p _, args => some (p.denote args.head args.tail.head)
  | .andB, args => some (args.head && args.tail.head)
  | .orB, args => some (args.head || args.tail.head)
  | .xorB, args => some (Bool.xor args.head args.tail.head)
  | .eqB, args => some (args.head == args.tail.head)
  | .notB, args => some (!args.head)
  | .index n t, args =>
      let a : Fin n → t.denote := args.head
      let i : BitVec 64 := args.tail.head
      if h : i.toNat < n then some (a ⟨i.toNat, h⟩) else none
  | .update n t, args =>
      let a : Fin n → t.denote := args.head
      let i : BitVec 64 := args.tail.head
      let v : t.denote := args.tail.tail.head
      if h : i.toNat < n then some (Function.update a ⟨i.toNat, h⟩ v) else none
  | .arrLit n _, args => some (hvReplicateFun n args)
  | .arrRepeat _ _, args => some (fun _ => args.head)
  | .mkPair _ _, args => some (args.head, args.tail.head)
  | .fst _ _, args => some args.head.1
  | .snd _ _, args => some args.head.2
  | .call f as r, args => T.call f as r args
  | .ilit t v, _ => NfTy.ofLit? t v
  | .ctr, args =>
      let lo : Int := args.head
      let i : BitVec 64 := args.tail.head
      some (lo + (i.toNat : Int))
  | .trip t, args =>
      let lo : Int := args.head
      (NfTy.toInt? t args.tail.head).map fun hi => BitVec.ofNat 64 (hi - lo).toNat
  | .tnilV, _ => some ()
  | .tconsV _ _, args => some (args.head, args.tail.head)
  | .thead _ _, args => some args.head.1
  | .ttail _ _, args => some args.head.2

/-- The `Option`-valued denotation of `nfDialect` with the leaves of `T`. -/
@[instance_reducible] def nfDenote (T : NfLeafTable) : DialectDenoteM nfDialect Option where
  denoteM := nfDenoteOp T

/-- Under `nfDenote T`, an operation denotes by `nfDenoteOp T`. -/
@[simp] theorem nfDenote_denoteM (T : NfLeafTable) (op : NfOp)
    (args : HVector NfTy.denote op.sig) :
    (nfDenote T).denoteM op args = nfDenoteOp T op args := rfl

end CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
