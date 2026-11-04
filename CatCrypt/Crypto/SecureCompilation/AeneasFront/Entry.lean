/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.ComposeV1
public import HaxLean.Rust

/-!
# The Aeneas front as an entry of the compiler

The Aeneas Lean backend prints a Rust function as a Lean function into the result monad of
the Aeneas `Std` library. Over the vendored model of that library (`HaxLean.Rust`, with the
flat monad `Aeneas.Std.RustM`) such a function, uncurried, is
`fn : AeTy.Args args → RustM res.denote` for codes `args`, `res` of its argument and result
types. This module makes these functions a source of the front-independent entry `NFEntry`
of the compiler, so the compiler `NFEntry.compileR` and its correctness theorem
`NFEntry.compileR_correct` apply to them with no further proof.

* The codes `AeTy` and the value map `AeTy.val`: an unsigned scalar of a width of at most
  64 bits is the word of 64 bits of its value, a boolean is the word `0` or `1` that the
  System V layout passes in a scalar register (its layout entry is a scalar of the bound
  `1`, its read-back the integer of the register), and an array of `n`
  values is the array of their images; one clause covers every width. `AeTy.vals` maps an
  argument tuple to a valuation of the parameter context `args.map AeTy.nf`.
* A source `AeSrc` is the codes, a parameter context `Γ`, a result type `t`, value maps
  into them, the function `fn`, a program `prog : NFProg nfDialect Γ [t]`, and the
  certificate `cert`: every value `ok y` of `fn a` is the value, at some fuel, of `prog` at
  the image of `a` under the `u64` table `hax64WExit`. The certificate is the forward
  simulation the reader of Aeneas output establishes for the program it emits.
* `aeneasRuns σ s sa v`: the layout `σ` reads off the entry state `sa` an environment holding
  the encodings of a valuation `V` of the parameters, `V` is the image of an argument `a`,
  `fn a` returns `ok y`, and `v` is the encoding of the image of `y`.
* `aeneasToNF σ s`: the program of `s`, when the parameter context of the layout is `Γ`.

## Main definitions

* `AeTy`, `AeTy.val`, `AeTy.vals` — the codes of the Aeneas types and the value map.
* `AeSrc` — a source of the Aeneas front.
* `aeneasRuns`, `aeneasToNF` — its semantics and its translation.
* `aeneasEntry : NFEntry` — the entry, at the table `hax64WExit`, the export names
  `nfAbiNames`, no declared procedure. Its soundness is the certificate; its fields
  `fieldCalls` and `fieldCallsWide` are those of `hax64WExit` (`fieldCalls_hax64WExit`,
  `fieldCallsWideEq_hax64WExit`).

## Main results

* `aeneasToNF_sound` — a run of a source is a run of its program.
* `enc_val_bool`, `aeneasRuns_bool` — a Boolean result is read back as the integer `0` or `1`.

The correctness of the compiled bytes is `aeneasEntry.compileR_correct`, which is
`NFEntry.compileR_correct aeneasEntry`.
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
open Aeneas.Std (RustM UScalar UScalarTy)

/-! ## The value map -/

/-- The types of the Aeneas values the front reads, as codes: an unsigned scalar of a width
    of at most 64 bits, a boolean, an array of `n` values. -/
inductive AeTy where
  /-- `UScalar ty`, of at most 64 bits. -/
  | u (ty : UScalarTy) (h : ty.numBits ≤ 64)
  /-- `Bool`. -/
  | bool
  /-- `Array τ n`. -/
  | arr (n : Aeneas.Std.Usize) (τ : AeTy)

/-- The Aeneas type of a code. -/
@[reducible] def AeTy.denote : AeTy → Type
  | .u ty _ => UScalar ty
  | .bool => Bool
  | .arr n τ => Aeneas.Std.Array τ.denote n

/-- The NF type of a code: a scalar is a word of 64 bits, a boolean the word of 64 bits of
    the layout, an array of `n` values an array of length `n.val`. -/
def AeTy.nf : AeTy → NfTy
  | .u _ _ => .word 64
  | .bool => .word 64
  | .arr n τ => .arr n.val τ.nf

/-- **The value map**: an unsigned scalar of at most 64 bits is the word of 64 bits of its
    value, a boolean is the word `1` or `0`, and an array is the array of the images of its
    elements. One clause covers every width. -/
def AeTy.val : (τ : AeTy) → τ.denote → τ.nf.denote
  | .u _ _, x => BitVec.ofNat 64 x.val
  | .bool, b => BitVec.ofNat 64 b.toNat
  | .arr _ τ, a => fun i => τ.val (a.val[i.val]'(by rw [a.property]; exact i.isLt))

/-- The argument tuple of a list of codes: the unit for no argument, a pair of the first
    argument and the remaining ones otherwise. -/
@[reducible] def AeTy.Args : List AeTy → Type
  | [] => Unit
  | τ :: τs => τ.denote × AeTy.Args τs

/-- The valuation of the parameter context `τs.map AeTy.nf` that an argument tuple denotes;
    the first argument is the newest variable. -/
def AeTy.vals : (τs : List AeTy) → AeTy.Args τs → Valuation (d := nfDialect) (τs.map AeTy.nf)
  | [], _ => .nil
  | τ :: τs, (x, xs) => .cons (τ.val x) (AeTy.vals τs xs)

/-! ## Sources -/

/-- **A source of the Aeneas front**: an Aeneas function `fn` over the vendored `RustM`, from
    the argument tuple of the codes `args` to the type of the code `res`; a program of
    `NFProg nfDialect` over the parameter context `Γ` with the result type `t`; the
    valuation `argVal` and the value `resVal` an argument tuple and a result denote; and the
    certificate that every value `ok y` of `fn a` is a value of the program at the image of
    `a`, at some fuel, under the `u64` table `hax64WExit`. `AeSrc.ofFn` takes the value
    maps `AeTy.vals` and `AeTy.val`. -/
structure AeSrc where
  /-- The codes of the argument types. -/
  args : List AeTy
  /-- The code of the result type. -/
  res : AeTy
  /-- The parameter context. -/
  Γ : List NfTy
  /-- The result type. -/
  t : NfTy
  /-- The valuation an argument tuple denotes. -/
  argVal : AeTy.Args args → Valuation (d := nfDialect) Γ
  /-- The value a result denotes. -/
  resVal : res.denote → t.denote
  /-- The Aeneas function. -/
  fn : AeTy.Args args → RustM res.denote
  /-- The program of `NFProg nfDialect`. -/
  prog : NFProg nfDialect Γ [t]
  /-- Every value of `fn` is a value of `prog` at the image of its argument. -/
  cert : ∀ a y, fn a = .ok y →
    ∃ fuel, PDenP hax64WExit fuel prog (argVal a) = some (.cons (resVal y) .nil)

/-- The source of an Aeneas function at the value maps `AeTy.vals` and `AeTy.val`. -/
def AeSrc.ofFn (args : List AeTy) (res : AeTy) (fn : AeTy.Args args → RustM res.denote)
    (prog : NFProg nfDialect (args.map AeTy.nf) [res.nf])
    (cert : ∀ a y, fn a = .ok y → ∃ fuel,
      PDenP hax64WExit fuel prog (AeTy.vals args a) = some (.cons (res.val y) .nil)) :
    AeSrc :=
  ⟨args, res, args.map AeTy.nf, res.nf, AeTy.vals args, res.val, fn, prog, cert⟩

/-- **The translation of a source**: its program, when the parameter context of the layout
    is the context of the program. -/
def aeneasToNF (σ : AbiLayout) (s : AeSrc) :
    Option (Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]) :=
  if h : entryCtx (abiEntry σ) = s.Γ then some ⟨s.t, h ▸ s.prog⟩ else none

/-- **The source semantics**: the layout reads off the entry state an environment that holds
    the encodings of a valuation `V` of the parameters, `V` is the image of an argument `a`,
    the Aeneas function returns `ok y` at `a`, and `v` is the encoding of the image of `y`. -/
def aeneasRuns (σ : AbiLayout) (s : AeSrc) (sa : AState) (v : Value) : Prop :=
  ∃ (h : entryCtx (abiEntry σ) = s.Γ) (e : Env) (V : Valuation (entryCtx (abiEntry σ)))
    (a : AeTy.Args s.args) (y : s.res.denote),
    σ.EnvOf sa e ∧ EntryVals e (abiEntry σ) V ∧ h ▸ V = s.argVal a ∧ s.fn a = .ok y ∧
      v = enc s.t (s.resVal y)

/-- At a source the translation accepts, the program is the program of the source over the
    parameter context of the layout, and a run of the source is a run of the program. -/
theorem aeneasToNF_sound (σ : AbiLayout) (s : AeSrc)
    (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t])
    (hq : aeneasToNF σ s = some q) (sa : AState) (v : Value) (hrun : aeneasRuns σ s sa v) :
    ∃ (k : Nat) (e : Env) (V : Valuation (entryCtx (abiEntry σ))) (y : q.1.denote),
      σ.EnvOf sa e ∧ EntryVals e (abiEntry σ) V ∧
        PDenP hax64WExit k q.2 V = some (HVector.cons y .nil) ∧ v = enc q.1 y := by
  obtain ⟨args, res, Γ, t, argVal, resVal, fn, prog, cert⟩ := s
  obtain ⟨h, e, V, a, y, he, hV, hVa, hfn, rfl⟩ := hrun
  dsimp only at h hVa hfn ⊢
  subst h
  simp only [aeneasToNF, dite_true, Option.some.injEq] at hq
  subst hq
  obtain ⟨k, hk⟩ := cert a y hfn
  have hVa' : V = argVal a := hVa
  subst hVa'
  exact ⟨k, e, _, resVal y, he, hV, hk, rfl⟩

/-- **The read-back of a Boolean**: the encoding of the image of a Boolean under the value map
    is the integer `1` or `0`. -/
theorem enc_val_bool (b : Bool) : enc AeTy.bool.nf (AeTy.val .bool b) = .int (b.toNat : Int) := by
  cases b <;> rfl

/-- **A Boolean result is read back as `0` or `1`**: at a source of the result code
    `AeTy.bool`, the value of a run is the integer of the Boolean that the Aeneas function
    returns. -/
theorem aeneasRuns_bool {σ : AbiLayout} {args : List AeTy}
    {fn : AeTy.Args args → RustM Bool}
    {prog : NFProg nfDialect (args.map AeTy.nf) [AeTy.bool.nf]}
    {cert : ∀ a y, fn a = .ok y → ∃ fuel,
      PDenP hax64WExit fuel prog (AeTy.vals args a) = some (.cons (AeTy.val .bool y) .nil)}
    {sa : AState} {v : Value} (h : aeneasRuns σ (AeSrc.ofFn args .bool fn prog cert) sa v) :
    ∃ a y, fn a = .ok y ∧ v = .int (y.toNat : Int) := by
  obtain ⟨_, _, _, a, y, _, _, _, hfn, hv⟩ := h
  exact ⟨a, y, hfn, hv.trans (enc_val_bool y)⟩

/-! ## The entry -/

/-- **The Aeneas front as an entry**: the sources `AeSrc` with the semantics `aeneasRuns`,
    the translation `aeneasToNF`, the export names `nfAbiNames`, the table `hax64WExit` at
    every fuel, and no declared procedure. Its soundness is `aeneasToNF_sound`, at the fuel
    the certificate gives; the table is a sub-table of the `u64` table
    (`hax64WExit_subTable`), agrees with every call environment on no declarations
    (`extAgree_nil`), answers the tagged field heads by their arms (`fieldCalls_hax64WExit`)
    and is the `u64` table at the wide tagged heads (`fieldCallsWideEq_hax64WExit`). -/
def aeneasEntry : NFEntry where
  Src := AeSrc
  Runs := aeneasRuns
  names := nfAbiNames
  toNF := aeneasToNF
  bi _ _ := hax64WExit
  sound σ s q hq sa v _ hrun := by
    obtain ⟨k, e, V, y, he, hV, hk, hv⟩ := aeneasToNF_sound σ s q hq sa v hrun
    exact ⟨k, [], e, V, y, fun _ _ _ => rfl, CatCrypt.Crypto.Hax.hax64WExit_subTable,
      CatCrypt.Crypto.Hax.NFToCat.extAgree_nil _ _, he, hV, ⟨k, le_rfl, hk⟩, hv⟩
  fieldCalls _ _ _ _ _ := fieldCalls_hax64WExit
  fieldCallsWide _ _ _ _ _ := fieldCallsWideEq_hax64WExit

end CatCrypt.Crypto.SecureCompilation.AeneasFront
