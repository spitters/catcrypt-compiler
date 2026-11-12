/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Entry

/-!
# Structures of scalars at the Aeneas entry

A Rust structure is, in the output of the Aeneas Lean backend, a Lean structure. A structure
of scalars enters the layout field by field: each field is one scalar parameter, and a
structure result is the array of its field words, written into an out-region of words that
the caller passes as the first argument (the System V hidden-pointer return). The class
`AeStruct S` gives the codes of the fields of `S` and the bijection between `S` and the
argument tuple of these codes; a source of a function with a structure argument and a
structure result is then an `AeSrc.ofFn` of a composed function, and `AeSrc`, `aeneasRuns` and
`aeneasEntry` are those of `AeneasFront.Entry`.

## Main definitions

* `AeTy.isScalar`, `AeTy.word`: scalar codes and the word of a scalar value
* `AeTy.Args.append`, `AeTy.Args.split`: argument tuples of a concatenation of codes
* `AeTy.argWords`: the words of an argument tuple
* `AeStruct`: a structure of scalars, as the argument tuple of its field codes
* `wordsArr`, `AeStruct.words`, `AeStruct.toWords`: the field words of a structure value
* `AeTy.outArr`: the code of the out-region of `k` words
* `AeStruct.argFn`, `AeStruct.resFn`: a function on a structure as a function on the field
  tuple, and a function with a structure result as a function writing the out-region
* `AeSrc.ofStructFn`: the source of a function from a structure and further arguments to a
  structure

## Main results

* `AeTy.Args.split_append`, `AeTy.Args.append_split`: `split` and `append` are inverse
* `enc_val_wordsArr`: the read-back of the out-region is the list of the field words
* `aeneasRuns_struct`: a run of a structure source reads the fields of a structure `s` off the
  layout, the Aeneas function returns `ok y` at `s`, and the value of the run is the list of
  the field words of `y`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.AeneasFront

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt (Valuation)
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.Haxc
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute (abiEntry)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.Hax.ImpToNF (enc PDenP entryCtx EntryVals)
open CatCrypt.Crypto.Hax (hax64WExit)
open _root_.Hax (Value Env)
open Aeneas.Std (RustM UScalar UScalarTy U64 Usize)

/-! ## Scalar codes and argument tuples -/

/-- A scalar code: every code but an array. -/
def AeTy.isScalar : AeTy → Bool
  | .arr _ _ => false
  | _ => true

/-- The word of a value of a code: the word of `64` bits of an unsigned scalar, the bit pattern
    of a signed scalar, `1` or `0` for a Boolean, and `0` for an array. -/
def AeTy.word : (τ : AeTy) → τ.denote → BitVec 64
  | .u _ _, x => BitVec.ofNat 64 x.val
  | .i _ _, x => BitVec.ofNat 64 x.bv.toNat
  | .bool, b => BitVec.ofNat 64 b.toNat
  | .arr _ _, _ => 0

/-- The argument tuple of `xs ++ ys` of two argument tuples. -/
def AeTy.Args.append : {xs ys : List AeTy} → AeTy.Args xs → AeTy.Args ys → AeTy.Args (xs ++ ys)
  | [], _, _, b => b
  | _ :: _, _, (x, a), b => (x, AeTy.Args.append a b)

/-- The two parts of an argument tuple of `xs ++ ys`. -/
def AeTy.Args.split : {xs ys : List AeTy} → AeTy.Args (xs ++ ys) → AeTy.Args xs × AeTy.Args ys
  | [], _, a => ((), a)
  | _ :: _, _, (x, a) => ((x, (AeTy.Args.split a).1), (AeTy.Args.split a).2)

theorem AeTy.Args.split_append : ∀ {xs ys : List AeTy} (a : AeTy.Args xs) (b : AeTy.Args ys),
    AeTy.Args.split (AeTy.Args.append a b) = (a, b)
  | [], _, (), _ => rfl
  | _ :: _, _, (x, a), b => by
    simp only [AeTy.Args.append, AeTy.Args.split, AeTy.Args.split_append a b]

theorem AeTy.Args.append_split : ∀ {xs ys : List AeTy} (a : AeTy.Args (xs ++ ys)),
    AeTy.Args.append (AeTy.Args.split a).1 (AeTy.Args.split a).2 = a
  | [], _, _ => rfl
  | _ :: _, _, (x, a) => by
    simp only [AeTy.Args.split, AeTy.Args.append, AeTy.Args.append_split a]

/-- The words of an argument tuple, one per argument, by `AeTy.word`. -/
def AeTy.argWords : (τs : List AeTy) → AeTy.Args τs → List (BitVec 64)
  | [], _ => []
  | τ :: τs, (x, xs) => τ.word x :: AeTy.argWords τs xs

theorem AeTy.length_argWords : ∀ (τs : List AeTy) (a : AeTy.Args τs),
    (AeTy.argWords τs a).length = τs.length
  | [], _ => rfl
  | _ :: τs, (_, a) => by
    simp only [AeTy.argWords, List.length_cons, AeTy.length_argWords τs a]

/-! ## Structures of scalars -/

/-- **A structure of scalars**: the codes of its fields, all scalar, and the bijection between
    the structure and the argument tuple of the field codes. -/
class AeStruct (S : Type) where
  /-- The codes of the fields, in declaration order. -/
  fields : List AeTy
  /-- Every field is a scalar. -/
  scalar : fields.all AeTy.isScalar = true
  /-- The fields of a value. -/
  toArgs : S → AeTy.Args fields
  /-- The value of the fields. -/
  ofArgs : AeTy.Args fields → S
  /-- A value is the value of its fields. -/
  ofArgs_toArgs : ∀ s, ofArgs (toArgs s) = s
  /-- The fields of the value of a tuple are the tuple. -/
  toArgs_ofArgs : ∀ a, toArgs (ofArgs a) = a

/-- The field words of a structure value. -/
def AeStruct.words {S : Type} [AeStruct S] (s : S) : List (BitVec 64) :=
  AeTy.argWords _ (AeStruct.toArgs s)

/-- The array of `k` `u64` words of a list of `k` words. -/
def wordsArr (k : Usize) (bs : List (BitVec 64)) (h : bs.length = k.val) :
    Aeneas.Std.Array U64 k :=
  ⟨bs.map fun b => ⟨b⟩, by rw [List.length_map, h]⟩

/-- The array of the field words of a structure value, at `k` fields. -/
def AeStruct.toWords {R : Type} [AeStruct R] (k : Usize)
    (hk : k.val = (AeStruct.fields R).length) (y : R) : Aeneas.Std.Array U64 k :=
  wordsArr k (AeStruct.words y) (by rw [AeStruct.words, AeTy.length_argWords, hk])

/-- The code of an out-region of `k` words. -/
abbrev AeTy.outArr (k : Usize) : AeTy := .arr k (.u .U64 (by decide))

/-- A function on a structure and further arguments, as a function on the field tuple of the
    structure followed by the further arguments. -/
def AeStruct.argFn {S : Type} [AeStruct S] {rest : List AeTy} {β : Type}
    (f : S → AeTy.Args rest → RustM β) : AeTy.Args (AeStruct.fields S ++ rest) → RustM β :=
  fun a => f (AeStruct.ofArgs (AeTy.Args.split a).1) (AeTy.Args.split a).2

/-- A function with a structure result, as a function of an out-region of `k` words and the
    arguments whose result is the array of the field words; the out-region is a ghost
    argument the function does not read. -/
def AeStruct.resFn {R : Type} [AeStruct R] (k : Usize) (hk : k.val = (AeStruct.fields R).length)
    {args : List AeTy} (f : AeTy.Args args → RustM R) :
    AeTy.Args (AeTy.outArr k :: args) → RustM (AeTy.outArr k).denote :=
  fun a => f a.2 >>= fun y => .ok (AeStruct.toWords k hk y)

/-- **The source of a function from a structure to a structure**: the function `f` on a
    structure `S` and the further arguments `rest`, with a result structure `R` of `k` fields,
    is the source of `AeSrc.ofFn` at the parameters out-region, fields of `S`, `rest`, and the
    result the out-region. -/
def AeSrc.ofStructFn (S R : Type) [AeStruct S] [AeStruct R] (rest : List AeTy) (k : Usize)
    (hk : k.val = (AeStruct.fields R).length) (f : S → AeTy.Args rest → RustM R)
    (prog : NFProg nfDialect ((AeTy.outArr k :: (AeStruct.fields S ++ rest)).map AeTy.nf)
      [(AeTy.outArr k).nf])
    (cert : ∀ a y, AeStruct.resFn k hk (AeStruct.argFn f) a = .ok y → ∃ fuel,
      PDenP hax64WExit fuel prog (AeTy.vals _ a) =
        some (.cons ((AeTy.outArr k).val y) .nil)) : AeSrc :=
  AeSrc.ofFn _ (AeTy.outArr k) (AeStruct.resFn k hk (AeStruct.argFn f)) prog cert

/-! ## The read-back -/

/-- **The read-back of an out-region**: the encoding of the image of the array of a list of
    words is the list of the integers of the words. -/
theorem enc_val_wordsArr (k : Usize) (bs : List (BitVec 64)) (h : bs.length = k.val) :
    enc (AeTy.outArr k).nf ((AeTy.outArr k).val (wordsArr k bs h)) =
      .array (bs.map fun b => .int (b.toNat : Int)) := by
  simp only [AeTy.nf, AeTy.val, enc, wordsArr, Value.array.injEq]
  apply List.ext_getElem
  · simp [h]
  · intro j h1 h2
    simp_all

/-- **A structure source reads a structure and returns its result's field words**: a run of
    `AeSrc.ofStructFn` reads off the layout the image of an out-region `o`, the fields of a
    structure `s` and further arguments `q`; the Aeneas function returns `ok y` at `s` and `q`,
    and the value of the run is the list of the integers of the field words of `y`. -/
theorem aeneasRuns_struct {σ : AbiLayout} {S R : Type} [AeStruct S] [AeStruct R]
    {rest : List AeTy} {k : Usize} {hk : k.val = (AeStruct.fields R).length}
    {f : S → AeTy.Args rest → RustM R}
    {prog : NFProg nfDialect ((AeTy.outArr k :: (AeStruct.fields S ++ rest)).map AeTy.nf)
      [(AeTy.outArr k).nf]}
    {cert : ∀ a y, AeStruct.resFn k hk (AeStruct.argFn f) a = .ok y → ∃ fuel,
      PDenP hax64WExit fuel prog (AeTy.vals _ a) =
        some (.cons ((AeTy.outArr k).val y) .nil)}
    {sa : AState} {v : Value}
    (hr : aeneasRuns σ (AeSrc.ofStructFn S R rest k hk f prog cert) sa v) :
    ∃ (o : Aeneas.Std.Array U64 k) (s : S) (q : AeTy.Args rest) (y : R),
      (∃ (h : entryCtx (abiEntry σ) =
          (AeTy.outArr k :: (AeStruct.fields S ++ rest)).map AeTy.nf)
        (e : Env) (V : Valuation (entryCtx (abiEntry σ))),
        σ.EnvOf sa e ∧ EntryVals e (abiEntry σ) V ∧
          h ▸ V = AeTy.vals _ (o, AeTy.Args.append (AeStruct.toArgs s) q)) ∧
      f s q = .ok y ∧ v = .array ((AeStruct.words y).map fun b => .int (b.toNat : Int)) := by
  obtain ⟨h, e, V, ⟨o, a⟩, y', he, hV, hVa, hfn, hv⟩ := hr
  have hfn' : (f (AeStruct.ofArgs (AeTy.Args.split a).1) (AeTy.Args.split a).2 >>= fun y =>
      RustM.ok (AeStruct.toWords k hk y)) = .ok y' := hfn
  cases hf : f (AeStruct.ofArgs (AeTy.Args.split a).1) (AeTy.Args.split a).2 with
  | ok y =>
    rw [hf] at hfn'
    cases hfn'
    refine ⟨o, AeStruct.ofArgs (AeTy.Args.split a).1, (AeTy.Args.split a).2, y,
      ⟨h, e, V, he, hV, ?_⟩, hf, ?_⟩
    · rw [AeStruct.toArgs_ofArgs, AeTy.Args.append_split]
      exact hVa
    · exact hv.trans (enc_val_wordsArr k _ _)
  | fail err => rw [hf] at hfn'; cases hfn'
  | div => rw [hf] at hfn'; cases hfn'

end CatCrypt.Crypto.SecureCompilation.AeneasFront
