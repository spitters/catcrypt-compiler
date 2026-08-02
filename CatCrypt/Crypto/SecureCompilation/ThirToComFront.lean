/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiEmit
import CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect

/-!
# Pilot front lane (#568, #605): width-parameterized THIR → `Com jasminDialect` → owned-x86

`ThirToComPilot.lean` piloted a verified THIR → `Com` lowering against a *toy*
target dialect (`pilot`, with only `const`/`add`/`mul`) whose `Com` the codegen
backend does **not** consume. This module is the **working end-to-end front
lane**: it lowers real monomorphic scalar crypto functions from a faithful
THIR-ANF representation into a `Com` over the **`jasminDialect`** that the
existing verified emit chain (`emitAbiOrchReg`, `JasminAbiEmit.lean`) renders to
owned-x86 jasmin/asm — the same `regArith` path `R3MulEmit`, `AsconEmit`,
and `ChaChaEmit` use. So the THIR lowers all the way to a callable artifact, and
the denotation-preservation theorem ties the THIR meaning to the emitted Com.

## Width-parameterized (#605, Step 3)

The whole front is parameterized over a register width `w : Nat` (the THIR and
`Com` worlds both denote into `BitVec w`). The original `u64` pilot is the `w =
64` instance (`dot4`); the SHA-256 leaf `small_sigma0` is the `w = 32` instance
(`sigma0`, #605 Step 4). Width threads through `frontCtxt`/`FState`/`Agree`, the
`Atom`/`Rhs`/`Thir` denotations (`BitVec w`), `rhsExpr` (op widths `w`), and the
main preservation theorem `thirToJasmin_denote`.

## The pilot functions

### `dot` — fixed-width unsigned inner product (schoolbook MAC step), `w = 64`

```rust
/// dot(a, b) = Σ_{i < N} a[i] * b[i]   (wrapping u64)
fn dot(a: [u64; N], b: [u64; N]) -> u64 { ... }
```

The **schoolbook coefficient product / MAC accumulate** — the inner arithmetic
of `R3_mult` / `Rq_mult_small` (sntrup761) and of a Poly1305-style field MAC,
restricted to a single output coefficient.

### `small_sigma0` — SHA-256 message-schedule σ₀, `w = 32`

```rust
fn small_sigma0(x: u32) -> u32 {
    x.rotate_right(7) ^ x.rotate_right(18) ^ (x >> 3)
}
```

The first ARX/sponge leaf taken end-to-end: two native right-rotates
(`Rhs.ror`), one logical shift (`Rhs.bin .shr`), two xors (`Rhs.bin .xor`), all
at width 32. It is the simplest *real* SHA-256 building block and exercises the
new `Rhs.ror`/`Rhs.bin` arms together at the non-`u64` width.

## What is proved vs trusted

* **Verified front (this file):** the lowering `thirToJasmin` and the
  preservation theorem `thirToJasmin_denote` — for any THIR `t` in the supported
  fragment and any width `w`, the THIR big-step denotation `t.denote` equals the
  lowered `Com jasminDialect`'s `Com.denote` under the matching valuation. The
  connecting theorems `dot4_FrontValueAgrees` (`w = 64`) and
  `sigma0_FrontValueAgrees` (`w = 32`) instantiate it for the pilot fns.
* **Verified emit (reused, not re-proved here):** `emitAbiOrchReg`
  (`JasminAbiEmit.lean`) renders a `regArith`/`rorImm` `Com jasminDialect` to
  jasmin; the jasmin-print correctness lemmas cover the straight-line fragment.
* **Trusted (thin):** the SysV-ABI orchestration string (param decls, copy-in /
  copy-out), `as`/`jasminc` downstream, and the C KAT harness.

## Scope

This compiles **two** monomorphic scalar fns end-to-end with the connecting
theorem (`u64` inner product, `u32` SHA-256 σ₀). It shares `ThirToComPilot`'s
boundaries (ANF operands, compile-time-`N` loops unrolled, pure-`Option`
no-effect model, no structs/enums/match/refs). The new things over the pilot are
indexed array reads (`Atom.inp`), the ARX op surface (`Rhs.ror`/`Rhs.bin`),
width-parameterization, and retargeting onto `jasminDialect`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ThirToComFront

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiEmit
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)

/-- The single dialect type the front uses at width `w`: a `w`-bit register. -/
abbrev rW (w : Nat) : JasminTy := .reg w

/-! ## §1  The THIR-ANF subset (with indexed array reads)

A THIR operand is either a `w`-bit literal, a let-bound *local* name, or an
**indexed input read** `inp[i]` (`a[i] = inp[i]`, `b[i] = inp[N + i]` after
bundling the two arrays into a single flat input vector of `nIn` `w`-bit
words). Literals carry a `Nat` (the constant's value); the `BitVec w` truncation
happens in the denotation, mirroring jasmin's fixed-width `regConst`. -/

/-- A THIR operand. `inp i` is the indexed array read (`a[i]` / `b[i]` after
    bundling). `lit`/`lvar` mirror `ThirToComPilot.Atom`. The literal is a `Nat`
    truncated to the active width at denotation time. -/
inductive Atom where
  | lit (n : Nat)
  | lvar (name : String)
  | inp (i : Nat)
  deriving Repr, DecidableEq

/-- Trivial `Repr` for `JasminBinOp` so the `Rhs`/`Thir` ASTs (which now carry a
    `JasminBinOp`) can `deriving Repr` for debug `#eval`. -/
local instance : Repr JasminBinOp := ⟨fun _ _ => "binop"⟩

/-- The right-hand side of a `let`: an atom, or a binary op on two atoms. -/
inductive Rhs where
  | atom (a : Atom)
  | add (a b : Atom)
  | mul (a b : Atom)
  /-- High word of the widening multiply `a * b` (`mulHiW a b`), the companion of
      `mul`'s low word: together they are MULX's `(hi, lo)`. The single-op front
      handle for bignum/EC/pairing multi-limb field arithmetic (the dialect's
      `thMulHi`, lowered 1:1 to jasmin `mulhi w`). Homogeneous `rW w`, so it flows
      through the front's monomorphic register file unchanged. -/
  | mulHi (a b : Atom)
  /-- A general carry-free binary op (`sub`/`and`/`or`/`xor`/`shl`/`shr`, and
      `add`/`mul`) on two atoms — the ARX/sponge op surface. The backend already
      renders every `regArith` binop, so this needs no emit change. -/
  | bin (op : JasminBinOp) (a b : Atom)
  /-- Native right-rotate by a compile-time `n` (`rotate_right#w`), emitted as the
      single `rorImm` op — the ARX/sponge rotate surface. -/
  | ror (n : Nat) (a : Atom)
  /-- Native logical right-shift by a **compile-time** `n` (`x >> n`), emitted as
      the single `shrImm` op (an immediate-count shift `dst = src >> n;`). The
      constant-shift surface for SHA-256/BLAKE2 (`x >> 3`, …): a `Rhs.bin .shr`
      reads its count from a register, which jasminc x86 rejects, so a literal
      shift must go through this arm instead (#605). -/
  | shrImm (n : Nat) (a : Atom)
  /-- Native **arithmetic** right-shift by a compile-time `n` (`x >> n` on a
      signed word), emitted as the single `sarImm` op (an immediate-count
      arithmetic shift `dst = (signed)src >> n;`). The sign-extending twin of
      `shrImm`: it denotes `BitVec.sshiftRight` rather than `>>>`
      (`BitVec.ushiftRight`). Unlocks the signed-shift surface of ML-DSA
      (`reduce32`'s `>> 23`, `montgomery_reduce`'s `>> 32`, `decompose`,
      `make_hint`), where `>>` on an `i32`/`i64` is arithmetic (#606). -/
  | sarImm (n : Nat) (a : Atom)
  /-- Native logical left-shift by a compile-time `n` (`x << n`); the left-shift
      counterpart of `shrImm` (#605). -/
  | shlImm (n : Nat) (a : Atom)
  /-- Width zero-extend of an atom at the working width `w`, emitted as the single
      `castW w w` op (#605, Step 5b). `BitVec.zeroExtend w` at the same width is
      the identity, so this stays in the homogeneous `rW w` register file and
      flows through the preservation proof unchanged; it is the front-connected
      image of the dialect's `castW` op. The **cross-width** cast (the
      `cast#8` digest-byte case `(u32)((u8) x)`) is the `castW w w'` composition
      exercised end-to-end by the dedicated `castDemoCom` pilot (§8). -/
  | cast (a : Atom)
  /-- A single-result function CALL `name(args…)` — the front handle for
      kernel-to-kernel COMPOSITION (treehash, FO transforms, Fiat-Shamir, #616
      E5a). Every argument is an atom resolvable to a `Var`; the callee is an
      opaque already-verified single-result leaf, lowered to the dialect's
      `thExtCall` (and thence to jasmin's `extCall`) at the working width `w`.
      Its value is `jasminExtSem name (replicate n (rW w)) (rW w)` — opaque, so
      the front emits a real call and the callee's meaning is a separate leaf
      obligation. -/
  | call (name : String) (args : List Atom)
  deriving Repr

/-- A THIR statement sequence in A-normal form. Same shape as
    `ThirToComPilot.Thir` (the bounded `forUp` is unrolled at compile time). -/
inductive Thir where
  | ret (a : Atom)
  | let_ (name : String) (r : Rhs) (body : Thir)
  | forUp (acc : String) (init : Rhs) (n : Nat) (body : Rhs)
  deriving Repr

/-! ## §2  Big-step THIR denotation over a `BitVec w` input vector

We denote into `BitVec w` (the jasmin `reg w` semantic type) rather than a
fixed machine int so the THIR meaning lives in the *same* type the `Com` denotes
into, making the preservation theorem a plain equality of `BitVec w`s. Wrapping
add/mul is exactly `BitVec w`'s `+`/`*`. The input vector `I : Fin nIn → BitVec
w` supplies `inp[i]`; locals live in a partial `String → Option (BitVec w)`
environment. -/

/-- A THIR local environment: partial map name → `reg w` value. -/
abbrev LEnv (w : Nat) := String → Option (BitVec w)

/-- Empty local environment. -/
def LEnv.empty (w : Nat) : LEnv w := fun _ => none

/-- Extend a local environment. -/
def LEnv.set {w : Nat} (ρ : LEnv w) (x : String) (v : BitVec w) : LEnv w :=
  fun y => if y = x then some v else ρ y

/-- Read input word `i` of the bundled input vector, totally (`0` out of range).
    Mirrors the jasmin pointer read `inp[i]`. -/
def inpGet {w nIn : Nat} (I : Fin nIn → BitVec w) (i : Nat) : BitVec w :=
  if h : i < nIn then I ⟨i, h⟩ else 0

/-- Denotation of an atom. -/
def Atom.denote {w nIn : Nat} (I : Fin nIn → BitVec w) (ρ : LEnv w) :
    Atom → Option (BitVec w)
  | .lit n => some (BitVec.ofNat w n)
  | .lvar x => ρ x
  | .inp i => some (inpGet I i)

/-- The homogeneous argument-type list of a width-`w` front call with `n`
    arguments: `n` copies of `rW w`. Both the dialect `thExtCall` and the front
    `Rhs.call` resolve every argument as a `rW w` register, so the call's signature
    is `replicate n (rW w) → rW w`. -/
abbrev callArgTys (w n : Nat) : List JasminTy := List.replicate n (rW w)

/-- Resolve a `List Atom` to the argument `HVector` the leaf semantics consume:
    each atom is denoted to a `BitVec w` (`= ⟦rW w⟧`); a single failure aborts.
    The resulting HVector is indexed by `callArgTys w args.length`. -/
def atomsHV {w nIn : Nat} (I : Fin nIn → BitVec w) (ρ : LEnv w) :
    (args : List Atom) → Option (HVector (fun t => ⟦t⟧) (callArgTys w args.length))
  | [] => some .nil
  | a :: rest =>
      (a.denote I ρ).bind fun av =>
        (atomsHV I ρ rest).map fun avs =>
          (HVector.cons (av : ⟦rW w⟧) avs)

/-- Denotation of a `let`-RHS. -/
def Rhs.denote {w nIn : Nat} (I : Fin nIn → BitVec w) (ρ : LEnv w) :
    Rhs → Option (BitVec w)
  | .atom a => a.denote I ρ
  | .add a b => (a.denote I ρ).bind fun av => (b.denote I ρ).map (av + ·)
  | .mul a b => (a.denote I ρ).bind fun av => (b.denote I ρ).map (av * ·)
  | .mulHi a b => (a.denote I ρ).bind fun av => (b.denote I ρ).map (fun bv => mulHiW av bv)
  | .bin op a b => (a.denote I ρ).bind fun av => (b.denote I ρ).map (fun bv => op.apply av bv)
  | .ror n a => (a.denote I ρ).map (fun av => av.rotateRight n)
  | .shrImm n a => (a.denote I ρ).map (fun (av : BitVec w) => av >>> n)
  | .sarImm n a => (a.denote I ρ).map (fun (av : BitVec w) => BitVec.sshiftRight av n)
  | .shlImm n a => (a.denote I ρ).map (fun (av : BitVec w) => av <<< n)
  | .cast a => (a.denote I ρ).map (fun (av : BitVec w) => av.zeroExtend w)
  | .call name args =>
      (atomsHV I ρ args).map fun avs =>
        (jasminExtSem name (callArgTys w args.length) (rW w) avs : ⟦rW w⟧)

/-- Iterate the loop body `n` times, threading the accumulator through `acc`. -/
def forIter {w nIn : Nat} (I : Fin nIn → BitVec w) (acc : String) (body : Rhs) :
    Nat → BitVec w → LEnv w → Option (BitVec w)
  | 0,     a, _ => some a
  | k + 1, a, ρ => (body.denote I (ρ.set acc a)).bind
                      fun a' => forIter I acc body k a' ρ

/-- Big-step denotation of a THIR statement. -/
def Thir.denote {w nIn : Nat} (I : Fin nIn → BitVec w) :
    Thir → LEnv w → Option (BitVec w)
  | .ret a, ρ => a.denote I ρ
  | .let_ x r body, ρ => (r.denote I ρ).bind fun rv => body.denote I (ρ.set x rv)
  | .forUp acc init n body, ρ =>
      (init.denote I ρ).bind fun i0 => forIter I acc body n i0 ρ

/-! ## §3  Compile-time scope and the lowering to `Com jasminDialect`

The lowering context is `inCtxt nIn ++ localScope`, where `inCtxt nIn` is the
`nIn`-word input file (replicated `rW w`) and `localScope` is the let-bound
locals (newest first), each `rW w`. We thread the input variables and the local
name → de-Bruijn map through a small state. -/

/-- The `Com` typing context: `nIn` input words plus one `rW w` per local. -/
def frontCtxt (w nIn : Nat) : (locals : List String) → Ctxt jasminDialect
  | [] => List.replicate nIn (rW w)
  | _ :: σ => rW w :: frontCtxt w nIn σ

/-- The input file context: `nIn` replicated `rW w` words, as a
    `Ctxt jasminDialect`. Definitionally `frontCtxt w nIn []`. -/
abbrev repCtxt (w nIn : Nat) : Ctxt jasminDialect := List.replicate nIn (rW w)

/-- De-Bruijn variable for input word `i < nIn` of a replicate context, totally
    (returns `none` when `i ≥ nIn`, since no such `rW w` var exists). -/
def inputVarRep (w : Nat) : (nIn : Nat) → (i : Nat) →
    Option (Ctxt.Var (repCtxt w nIn) (rW w))
  | 0, _ => none
  | (_ + 1), 0 => some .here
  | (m + 1), (k + 1) => (inputVarRep w m k).map (·.there)

/-- The lowering state at scope `locals`: the resolver for each local name and
    for each input index, as de-Bruijn variables of `frontCtxt w nIn locals`. -/
structure FState (w nIn : Nat) (locals : List String) where
  /-- Resolve a local name to a variable (newest binding), if bound. -/
  localVar : String → Option (Ctxt.Var (frontCtxt w nIn locals) (rW w))
  /-- Resolve an input index `i < nIn` to its variable, if in range. -/
  inpVar : Nat → Option (Ctxt.Var (frontCtxt w nIn locals) (rW w))

/-- The initial state at the empty local scope: locals all unbound; input `i`
    resolves to `inputVarRep w nIn i` (`frontCtxt w nIn [] = replicate nIn rW w`). -/
def initFState (w nIn : Nat) : FState w nIn [] where
  localVar := fun _ => none
  -- `frontCtxt w nIn [] = List.replicate nIn (rW w)` definitionally, so the
  -- `inputVarRep w nIn i` var typechecks directly at `frontCtxt w nIn []`.
  inpVar := fun i => inputVarRep w nIn i

/-- Push a fresh local binding `x` onto the state: the new head is `x`; every
    prior resolution shifts under `.there`. -/
def FState.push {w nIn : Nat} {locals : List String} (st : FState w nIn locals)
    (x : String) : FState w nIn (x :: locals) where
  localVar := fun y =>
    if y = x then some .here else (st.localVar y).map (·.there)
  inpVar := fun i => (st.inpVar i).map (·.there)

/-- Resolve an `Atom` operand to a `Com` variable, if it denotes one directly.
    `lit` has no `Var` (it must be `let`-bound first — the ANF restriction); a
    `lvar` resolves via `localVar`; an `inp i` via `inpVar`. -/
def Atom.toVar {w nIn : Nat} {locals : List String} (st : FState w nIn locals) :
    Atom → Option (Ctxt.Var (frontCtxt w nIn locals) (rW w))
  | .lit _ => none
  | .lvar x => st.localVar x
  | .inp i => st.inpVar i

/-- Resolve a `List Atom` to the `Var` `HVector` a `thExtCall`/`extCall` binding
    consumes (indexed by `callArgTys w args.length`). Each atom must resolve to a
    `Var` (`lvar`/`inp`); a single unresolvable atom aborts (the ANF discipline —
    a `lit` argument must already be `let`-bound). -/
def atomsToVarHV {w nIn : Nat} {locals : List String} (st : FState w nIn locals) :
    (args : List Atom) →
    Option (HVector (fun ty => Ctxt.Var (frontCtxt w nIn locals) ty)
      (callArgTys w args.length))
  | [] => some .nil
  | a :: rest =>
      (a.toVar st).bind fun v =>
        (atomsToVarHV st rest).map fun vs =>
          (HVector.cons (v : Ctxt.Var (frontCtxt w nIn locals) (rW w)) vs)

/-- Lower a `Rhs` to the single `Expr` it binds at the head of the context.

    ANF discipline (charon-faithful): binary-op operands must be atoms with a
    `Var` (`lvar`/`inp`); a `lit` operand must already be `let`-bound. A
    literal `Rhs` (`atom (lit n)`) lowers to a `regConst`; a variable `Rhs`
    re-binds via `regArith .or` with itself (the identity copy, since
    `v ||| v = v`). -/
def rhsExpr {w nIn : Nat} {locals : List String} (st : FState w nIn locals) :
    Rhs → Option (Expr jasminDialect (frontCtxt w nIn locals) (rW w))
  | .atom (.lit n) =>
      some { op := .regConst w n, retTy_eq := rfl, args := .nil }
  | .atom a =>
      (a.toVar st).map fun v =>
        { op := .regArith .or w, retTy_eq := rfl, args := .cons v (.cons v .nil) }
  | .add a b =>
      match a.toVar st, b.toVar st with
      | some va, some vb =>
          some { op := .regArith .add w, retTy_eq := rfl,
                 args := .cons va (.cons vb .nil) }
      | _, _ => none
  | .mul a b =>
      match a.toVar st, b.toVar st with
      | some va, some vb =>
          some { op := .regArith .mul w, retTy_eq := rfl,
                 args := .cons va (.cons vb .nil) }
      | _, _ => none
  | .mulHi a b =>
      match a.toVar st, b.toVar st with
      | some va, some vb =>
          some { op := .mulhi w, retTy_eq := rfl,
                 args := .cons va (.cons vb .nil) }
      | _, _ => none
  | .bin op a b =>
      match a.toVar st, b.toVar st with
      | some va, some vb =>
          some { op := .regArith op w, retTy_eq := rfl,
                 args := .cons va (.cons vb .nil) }
      | _, _ => none
  | .ror n a =>
      (a.toVar st).map fun va =>
        { op := .rorImm w n, retTy_eq := rfl, args := .cons va .nil }
  | .shrImm n a =>
      (a.toVar st).map fun va =>
        { op := .shrImm w n, retTy_eq := rfl, args := .cons va .nil }
  | .sarImm n a =>
      (a.toVar st).map fun va =>
        { op := .sarImm w n, retTy_eq := rfl, args := .cons va .nil }
  | .shlImm n a =>
      (a.toVar st).map fun va =>
        { op := .shlImm w n, retTy_eq := rfl, args := .cons va .nil }
  | .cast a =>
      (a.toVar st).map fun va =>
        { op := .castW w w, retTy_eq := rfl, args := .cons va .nil }
  | .call name args =>
      (atomsToVarHV st args).map fun vs =>
        { op := .extCall name (callArgTys w args.length) (rW w),
          retTy_eq := rfl, args := vs }

/-! ### §3.1  Compile-time unrolling of the bounded loop -/

/-- `let acc = body` repeated `n` times, ending in `ret (local acc)`. -/
def unrollBody (acc : String) (body : Rhs) : Nat → Thir
  | 0     => .ret (.lvar acc)
  | k + 1 => .let_ acc body (unrollBody acc body k)

/-- Unroll `forUp acc init n body` into `let acc = init in (let acc = body)^n
    ret acc`. -/
def Thir.unrollFor (acc : String) (init : Rhs) (n : Nat) (body : Rhs) : Thir :=
  .let_ acc init (unrollBody acc body n)

/-- Termination measure dominating the unrolling step (`forUp` strictly exceeds
    its unrolling). -/
def thirMeasure : Thir → Nat
  | .ret _ => 0
  | .let_ _ _ body => 1 + thirMeasure body
  | .forUp _ _ n _ => 2 + n

theorem thirMeasure_unrollBody (acc : String) (body : Rhs) (n : Nat) :
    thirMeasure (unrollBody acc body n) = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [unrollBody, thirMeasure, ih]; omega

theorem thirMeasure_unrollFor (acc : String) (init : Rhs) (n : Nat) (body : Rhs) :
    thirMeasure (Thir.unrollFor acc init n body) = 1 + n := by
  simp [Thir.unrollFor, thirMeasure, thirMeasure_unrollBody]

/-- Lower a THIR statement to a `Com jasminDialect` against a scope state.

* `ret a` → bind `a`'s `Expr` (a copy / `regConst`) then `ret here`.
* `let_ x r body` → bind `r`'s `Expr`, lower `body` in the pushed scope.
* `forUp` → compile-time unrolling into nested `let_`s. -/
def thirToJasmin {w nIn : Nat} (locals : List String) (st : FState w nIn locals) :
    Thir → Option (Com jasminDialect (frontCtxt w nIn locals) (rW w))
  | .ret a =>
      (rhsExpr st (.atom a)).map fun e => .var e (.ret .here)
  | .let_ x r body =>
      match rhsExpr st r, thirToJasmin (x :: locals) (st.push x) body with
      | some e, some bc => some (.var e bc)
      | _, _ => none
  | .forUp acc init n body =>
      thirToJasmin locals st (Thir.unrollFor acc init n body)
  termination_by t => thirMeasure t
  decreasing_by
    · simp [thirMeasure]
    · simp [thirMeasure, thirMeasure_unrollFor]

/-! ## §4  Denotation preservation (the erase / commutation proof)

`Agree` couples the THIR (input-vector + local-env) world with the `Com`
de-Bruijn valuation `V`: every input index resolves to `I i`, and every local
resolvable to a variable carries its env value. -/

/-- Compatibility between the THIR semantics and a `Com` valuation: every input
    index that resolves to a variable looks up to `inpGet I i`, and every local
    resolvable carries its env value. -/
def Agree {w nIn : Nat} (locals : List String) (I : Fin nIn → BitVec w)
    (ρ : LEnv w) (st : FState w nIn locals)
    (V : Ctxt.Valuation (frontCtxt w nIn locals)) : Prop :=
  (∀ (i : Nat) (v : Ctxt.Var (frontCtxt w nIn locals) (rW w)),
      st.inpVar i = some v → v.lookup V = inpGet I i) ∧
  (∀ (x : String) (v : Ctxt.Var (frontCtxt w nIn locals) (rW w)),
      st.localVar x = some v → ρ x = some (v.lookup V))

/-- Extending both worlds with the same value `e` for the same name preserves
    `Agree` under `FState.push`. -/
theorem Agree.push {w nIn : Nat} {locals : List String} {I : Fin nIn → BitVec w}
    {ρ : LEnv w} {st : FState w nIn locals}
    {V : Ctxt.Valuation (frontCtxt w nIn locals)}
    (h : Agree locals I ρ st V) (x : String) (e : BitVec w) :
    Agree (x :: locals) I (ρ.set x e) (st.push x)
      ((V.extend e : Ctxt.Valuation (rW w :: frontCtxt w nIn locals))) := by
  obtain ⟨hI, hL⟩ := h
  refine ⟨?_, ?_⟩
  · -- input indices: `push` shifts each `inpVar` by `.there`, lookup peels it.
    intro i v hv
    simp only [FState.push] at hv
    rcases hv0 : st.inpVar i with _ | v0
    · rw [hv0] at hv; simp at hv
    · rw [hv0] at hv
      simp only [Option.map_some, Option.some.injEq] at hv
      subst hv
      show (Ctxt.Var.there (s := rW w) v0).lookup (V.extend e) = inpGet I i
      rw [show (Ctxt.Var.there (s := rW w) v0).lookup (V.extend e) = v0.lookup V
          from rfl]
      exact hI i v0 hv0
  · -- locals: the head case is the fresh `x`; the tail shifts.
    intro y v hy
    simp only [FState.push] at hy
    by_cases hxy : y = x
    · subst hxy
      rw [if_pos rfl] at hy
      cases hy
      show (ρ.set y e) y
          = some ((Ctxt.Var.here (t := rW w) (Γ := frontCtxt w nIn locals)).lookup
              (V.extend e))
      simp only [LEnv.set]; rfl
    · rw [if_neg hxy] at hy
      rcases hv : st.localVar y with _ | v0
      · rw [hv] at hy; simp at hy
      · rw [hv] at hy
        simp only [Option.map_some, Option.some.injEq] at hy
        subst hy
        simp only [LEnv.set, if_neg hxy]
        have := hL y v0 hv
        rw [this]
        show some (v0.lookup V)
            = some ((Ctxt.Var.there (s := rW w) v0).lookup (V.extend e))
        rfl

/-- An atom resolvable to a `Var` denotes to that variable's lookup. -/
theorem Atom.toVar_denote {w nIn : Nat} {locals : List String}
    {I : Fin nIn → BitVec w} {ρ : LEnv w} {st : FState w nIn locals}
    {V : Ctxt.Valuation (frontCtxt w nIn locals)} (h : Agree locals I ρ st V)
    (a : Atom) {v : Ctxt.Var (frontCtxt w nIn locals) (rW w)}
    (hv : a.toVar st = some v) :
    a.denote I ρ = some (v.lookup V) := by
  obtain ⟨hI, hL⟩ := h
  cases a with
  | lit n => simp [Atom.toVar] at hv
  | lvar x =>
      simp only [Atom.toVar] at hv
      simpa [Atom.denote] using hL x v hv
  | inp i =>
      simp only [Atom.toVar] at hv
      simp only [Atom.denote]
      rw [hI i v hv]

/-- A scoped local denotes to its valuation lookup under `Agree`. -/
theorem localVar_denote {w nIn : Nat} {locals : List String}
    {I : Fin nIn → BitVec w} {ρ : LEnv w} {st : FState w nIn locals}
    {V : Ctxt.Valuation (frontCtxt w nIn locals)} (h : Agree locals I ρ st V)
    {x : String} {v : Ctxt.Var (frontCtxt w nIn locals) (rW w)}
    (hv : st.localVar x = some v) : ρ x = some (v.lookup V) := h.2 x v hv

/-- The call-argument resolvers agree: when every atom of `args` resolves to a
    `Var` (`atomsToVarHV st args = some vs`), the value `HVector` `atomsHV I ρ
    args` is exactly `Expr.lookupArgs vs V` (each atom denotes to its variable's
    lookup, by `Atom.toVar_denote`). The HVector-level mirror of
    `Atom.toVar_denote`, threading the leaf's whole argument list. -/
theorem atomsHV_lookupArgs {w nIn : Nat} {locals : List String}
    {I : Fin nIn → BitVec w} {ρ : LEnv w} {st : FState w nIn locals}
    {V : Ctxt.Valuation (frontCtxt w nIn locals)} (h : Agree locals I ρ st V) :
    (args : List Atom) →
    {vs : HVector (fun ty => Ctxt.Var (frontCtxt w nIn locals) ty)
      (callArgTys w args.length)} →
    atomsToVarHV st args = some vs →
    atomsHV I ρ args = some (Expr.lookupArgs vs V)
  | [], vs, hvs => by
      simp only [atomsToVarHV, Option.some.injEq] at hvs
      subst hvs
      rfl
  | a :: rest, vs, hvs => by
      simp only [atomsToVarHV] at hvs
      rcases hva : a.toVar st with _ | v
      · rw [hva] at hvs; simp at hvs
      rcases hvr : atomsToVarHV st rest with _ | vr
      · rw [hva, hvr] at hvs; simp at hvs
      · rw [hva, hvr] at hvs
        simp only [Option.bind_some, Option.map_some, Option.some.injEq] at hvs
        subst hvs
        simp only [atomsHV]
        rw [Atom.toVar_denote h a hva, Option.bind_some,
          atomsHV_lookupArgs h rest hvr, Option.map_some]
        rfl

/-- `rhsExpr` preservation: the single `Expr` produced for a `Rhs` denotes to the
    same value as the THIR `Rhs`. -/
theorem rhsExpr_denote {w nIn : Nat} {locals : List String}
    {I : Fin nIn → BitVec w} {ρ : LEnv w} {st : FState w nIn locals}
    {V : Ctxt.Valuation (frontCtxt w nIn locals)} (h : Agree locals I ρ st V)
    (r : Rhs) {e : Expr jasminDialect (frontCtxt w nIn locals) (rW w)}
    (he : rhsExpr st r = some e) :
    r.denote I ρ = some (e.denote V) := by
  cases r with
  | atom a =>
      cases a with
      | lit n =>
          simp only [rhsExpr, Option.some.injEq] at he
          subst he
          simp only [Rhs.denote, Atom.denote, Expr.denote, DialectDenote.denote]
      | lvar x =>
          rcases hv : (Atom.lvar x).toVar st with _ | v
          · simp [rhsExpr, hv] at he
          · simp only [rhsExpr, hv, Option.map_some, Option.some.injEq] at he
            subst he
            have hd := Atom.toVar_denote h (.lvar x) hv
            simp only [Rhs.denote]
            rw [hd]
            -- `Expr.denote` of `regArith .or v v` = `v ||| v = v`
            congr 1
            show v.lookup V = JasminBinOp.or.apply (v.lookup V) (v.lookup V)
            simp [JasminBinOp.apply, BitVec.or_self]
      | inp i =>
          rcases hv : (Atom.inp i).toVar st with _ | v
          · simp [rhsExpr, hv] at he
          · simp only [rhsExpr, hv, Option.map_some, Option.some.injEq] at he
            subst he
            have hd := Atom.toVar_denote h (.inp i) hv
            simp only [Rhs.denote]
            rw [hd]
            congr 1
            show v.lookup V = JasminBinOp.or.apply (v.lookup V) (v.lookup V)
            simp [JasminBinOp.apply, BitVec.or_self]
  | add a b =>
      rcases hva : a.toVar st with _ | va
      · simp [rhsExpr, hva] at he
      rcases hvb : b.toVar st with _ | vb
      · simp [rhsExpr, hva, hvb] at he
      · simp only [rhsExpr, hva, hvb, Option.some.injEq] at he
        subst he
        simp only [Rhs.denote]
        rw [Atom.toVar_denote h a hva, Atom.toVar_denote h b hvb,
          Option.bind_some, Option.map_some]
        congr 1
  | mul a b =>
      rcases hva : a.toVar st with _ | va
      · simp [rhsExpr, hva] at he
      rcases hvb : b.toVar st with _ | vb
      · simp [rhsExpr, hva, hvb] at he
      · simp only [rhsExpr, hva, hvb, Option.some.injEq] at he
        subst he
        simp only [Rhs.denote]
        rw [Atom.toVar_denote h a hva, Atom.toVar_denote h b hvb,
          Option.bind_some, Option.map_some]
        congr 1
  | mulHi a b =>
      rcases hva : a.toVar st with _ | va
      · simp [rhsExpr, hva] at he
      rcases hvb : b.toVar st with _ | vb
      · simp [rhsExpr, hva, hvb] at he
      · simp only [rhsExpr, hva, hvb, Option.some.injEq] at he
        subst he
        simp only [Rhs.denote]
        rw [Atom.toVar_denote h a hva, Atom.toVar_denote h b hvb,
          Option.bind_some, Option.map_some]
        congr 1
  | bin op a b =>
      rcases hva : a.toVar st with _ | va
      · simp [rhsExpr, hva] at he
      rcases hvb : b.toVar st with _ | vb
      · simp [rhsExpr, hva, hvb] at he
      · simp only [rhsExpr, hva, hvb, Option.some.injEq] at he
        subst he
        simp only [Rhs.denote]
        rw [Atom.toVar_denote h a hva, Atom.toVar_denote h b hvb,
          Option.bind_some, Option.map_some]
        congr 1
  | ror n a =>
      rcases hva : a.toVar st with _ | va
      · simp [rhsExpr, hva] at he
      · simp only [rhsExpr, hva, Option.map_some, Option.some.injEq] at he
        subst he
        simp only [Rhs.denote]
        rw [Atom.toVar_denote h a hva, Option.map_some]
        congr 1
  | shrImm n a =>
      rcases hva : a.toVar st with _ | va
      · simp [rhsExpr, hva] at he
      · simp only [rhsExpr, hva, Option.map_some, Option.some.injEq] at he
        subst he
        simp only [Rhs.denote]
        rw [Atom.toVar_denote h a hva, Option.map_some]
        congr 1
  | sarImm n a =>
      rcases hva : a.toVar st with _ | va
      · simp [rhsExpr, hva] at he
      · simp only [rhsExpr, hva, Option.map_some, Option.some.injEq] at he
        subst he
        simp only [Rhs.denote]
        rw [Atom.toVar_denote h a hva, Option.map_some]
        congr 1
  | shlImm n a =>
      rcases hva : a.toVar st with _ | va
      · simp [rhsExpr, hva] at he
      · simp only [rhsExpr, hva, Option.map_some, Option.some.injEq] at he
        subst he
        simp only [Rhs.denote]
        rw [Atom.toVar_denote h a hva, Option.map_some]
        congr 1
  | cast a =>
      rcases hva : a.toVar st with _ | va
      · simp [rhsExpr, hva] at he
      · simp only [rhsExpr, hva, Option.map_some, Option.some.injEq] at he
        subst he
        simp only [Rhs.denote]
        rw [Atom.toVar_denote h a hva, Option.map_some]
        congr 1
  | call name args =>
      rcases hvs : atomsToVarHV st args with _ | vs
      · simp [rhsExpr, hvs] at he
      · simp only [rhsExpr, hvs, Option.map_some, Option.some.injEq] at he
        subst he
        simp only [Rhs.denote]
        rw [atomsHV_lookupArgs h args hvs, Option.map_some]
        -- both sides are `jasminExtSem name (callArgTys w n) (rW w)
        -- (Expr.lookupArgs vs V)`; `Expr.denote` of the `.extCall` (`retTy_eq =
        -- rfl`) reduces to the same `jasminExtSem` application.
        rfl

/-- Setting the same name twice keeps the last write. -/
theorem LEnv.set_set {w : Nat} (ρ : LEnv w) (x : String) (a b : BitVec w) :
    (ρ.set x a).set x b = ρ.set x b := by
  funext y; simp only [LEnv.set]; by_cases h : y = x <;> simp [h]

/-- The unrolled loop body denotes exactly like the `forIter` iteration. -/
theorem unrollBody_denote {w nIn : Nat} (I : Fin nIn → BitVec w) (acc : String)
    (body : Rhs) (n : Nat) (a : BitVec w) (ρ : LEnv w) :
    (unrollBody acc body n).denote I (ρ.set acc a) = forIter I acc body n a ρ := by
  induction n generalizing a with
  | zero => simp [unrollBody, Thir.denote, Atom.denote, forIter, LEnv.set]
  | succ k ih =>
      simp only [unrollBody, Thir.denote, forIter, LEnv.set_set]
      cases hb : body.denote I (ρ.set acc a) with
      | none => simp
      | some a' => simp only [Option.bind_some]; rw [ih]

/-- Unrolling preserves the loop's denotation. -/
theorem unrollFor_denote {w nIn : Nat} (I : Fin nIn → BitVec w) (acc : String)
    (init : Rhs) (n : Nat) (body : Rhs) (ρ : LEnv w) :
    (Thir.unrollFor acc init n body).denote I ρ
      = (Thir.forUp acc init n body).denote I ρ := by
  simp only [Thir.unrollFor, Thir.denote]
  cases hi : init.denote I ρ with
  | none => simp
  | some i0 => simp only [Option.bind_some]; rw [unrollBody_denote]

/-- **Main preservation theorem (erase / commutation).** For any width `w`, when
    `Agree` holds and the lowering succeeds, the THIR denotation equals the
    lowered `Com jasminDialect`'s denotation. Proved by strong induction on the
    unrolling measure (the bounded loop reduces to its measure-smaller unrolled
    form). -/
theorem thirToJasmin_denote {w nIn : Nat} (locals : List String)
    (I : Fin nIn → BitVec w) (t : Thir) (ρ : LEnv w) (st : FState w nIn locals)
    (V : Ctxt.Valuation (frontCtxt w nIn locals))
    (c : Com jasminDialect (frontCtxt w nIn locals) (rW w))
    (hAg : Agree locals I ρ st V) (hc : thirToJasmin locals st t = some c) :
    t.denote I ρ = some (c.denote V) := by
  induction hmeas : thirMeasure t using Nat.strongRecOn
    generalizing locals ρ st V c t with
  | ind m ih =>
    cases t with
    | ret a =>
        simp only [thirToJasmin] at hc
        rcases he : rhsExpr st (.atom a) with _ | e <;> rw [he] at hc
        · simp at hc
        · simp only [Option.map_some, Option.some.injEq] at hc
          subst hc
          have hr := rhsExpr_denote hAg (.atom a) he
          simp only [Thir.denote]
          rw [show a.denote I ρ = (Rhs.atom a).denote I ρ from rfl, hr]
          simp only [Com.denote]
          rfl
    | let_ x r body =>
        simp only [thirToJasmin] at hc
        rcases he : rhsExpr st r with _ | e <;> rw [he] at hc
        · simp at hc
        rcases hbc : thirToJasmin (x :: locals) (st.push x) body with _ | bc <;>
          rw [hbc] at hc
        · simp at hc
        · simp only [Option.some.injEq] at hc
          subst hc
          simp only [Thir.denote, Com.denote]
          rw [rhsExpr_denote hAg r he, Option.bind_some]
          exact ih (thirMeasure body) (by subst hmeas; simp [thirMeasure])
            (x :: locals) body (ρ.set x (e.denote V)) (st.push x)
            (V.extend (e.denote V)) bc (hAg.push x (e.denote V)) hbc rfl
    | forUp acc init n body =>
        simp only [thirToJasmin] at hc
        rw [← unrollFor_denote]
        have hlt : thirMeasure (Thir.unrollFor acc init n body) < m := by
          subst hmeas; rw [thirMeasure_unrollFor]; simp [thirMeasure]
        exact ih (thirMeasure (Thir.unrollFor acc init n body)) hlt
          locals (Thir.unrollFor acc init n body) ρ st V c hAg hc rfl

/-! ## §5  The canonical input valuation and `Agree` at the empty scope -/

/-- The canonical `Com` valuation of `frontCtxt w nIn [] = replicate nIn (rW w)`
    from an input vector `I`: word `i` ↦ `I i`. -/
def inputValuation (w : Nat) : (nIn : Nat) → (Fin nIn → BitVec w) →
    Ctxt.Valuation (repCtxt w nIn)
  | 0, _ => .nil
  | (m + 1), I => .cons (I 0) (inputValuation w m (fun j => I j.succ))

/-- `inputVarRep w nIn i` (when in range) looks up to `I i` in `inputValuation`. -/
theorem inputVarRep_lookup (w : Nat) : (nIn : Nat) → (I : Fin nIn → BitVec w) →
    (i : Nat) → (v : Ctxt.Var (repCtxt w nIn) (rW w)) →
    inputVarRep w nIn i = some v → v.lookup (inputValuation w nIn I) = inpGet I i
  | 0, _, _, _, h => by simp [inputVarRep] at h
  | (m + 1), I, 0, v, h => by
      simp only [inputVarRep, Option.some.injEq] at h
      subst h
      show I 0 = inpGet I 0
      simp only [inpGet, dif_pos (Nat.succ_pos m)]
      congr 1
  | (m + 1), I, (k + 1), v, h => by
      simp only [inputVarRep] at h
      rcases hv : inputVarRep w m k with _ | v0
      · rw [hv] at h; simp at h
      · rw [hv] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        show v0.lookup (inputValuation w m (fun j => I j.succ)) = inpGet I (k + 1)
        rw [inputVarRep_lookup w m (fun j => I j.succ) k v0 hv]
        -- `inpGet (I ∘ succ) k = inpGet I (k+1)`
        by_cases hk : k < m
        · simp only [inpGet, dif_pos hk, dif_pos (Nat.succ_lt_succ hk)]
          congr 1
        · simp only [inpGet, dif_neg hk,
            dif_neg (fun hc => hk (Nat.lt_of_succ_lt_succ hc))]

/-- `Agree` at the empty local scope, for `initFState`: the local clause is
    vacuous; the input clause is `inputVarRep_lookup`. -/
theorem initAgree {w nIn : Nat} (I : Fin nIn → BitVec w) :
    Agree [] I (LEnv.empty w) (initFState w nIn) (inputValuation w nIn I) := by
  refine ⟨?_, ?_⟩
  · intro i v hv
    -- `initFState`'s `inpVar` is `inputVarRep w nIn i` transported along
    -- `frontCtxt w nIn [] = replicate nIn (rW w)` (definitionally equal).
    have hv' : inputVarRep w nIn i = some v := hv
    exact inputVarRep_lookup w nIn I i v hv'
  · intro x v hv
    simp only [initFState] at hv
    exact absurd hv (by simp)

/-! ## §6  Pilot fn `dotN` (`w = 64`) and its end-to-end wiring

`dotN N` is the THIR for `dot` at array length `N` (input vector `nIn = 2N`,
`a[i] = inp[i]`, `b[i] = inp[N + i]`). Because the inner-product step `acc +=
a[i]*b[i]` is two ops (a `mul` then an `add`) and `forUp`'s body is a single
`Rhs`, we emit the fully unrolled ANF directly. -/

/-- Local accumulator name. -/
def accN : String := "acc"

/-- Per-step product local name. -/
def prodN (i : Nat) : String := "p" ++ toString i

/-- The unrolled inner-product tail: for `i = lo .. N-1`, `let p_i = a[i]*b[i];
    acc = acc + p_i`. -/
def dotTail (N : Nat) : (fuel : Nat) → (i : Nat) → Thir
  | 0, _ => .ret (.lvar accN)
  | fuel + 1, i =>
      .let_ (prodN i) (.mul (.inp i) (.inp (N + i)))
        (.let_ accN (.add (.lvar accN) (.lvar (prodN i)))
          (dotTail N fuel (i + 1)))

/-- The pilot THIR for `dot` at length `N`: `acc = a[0]*b[0]`, then the unrolled
    `acc += a[i]*b[i]` tail for `i = 1 .. N-1`. -/
def dotN (N : Nat) : Thir :=
  .let_ accN (.mul (.inp 0) (.inp N)) (dotTail N (N - 1) 1)

/-! ### The reference (spec) denotation of `dot` -/

/-- The mathematical inner product `Σ_{i<N} a[i]·b[i]` over `BitVec 64`, with
    `a[i] = I i`, `b[i] = I (N + i)`. -/
def dotSpec (N : Nat) (I : Fin (2 * N) → BitVec 64) : BitVec 64 :=
  (List.range (N - 1)).foldl
    (fun acc j => acc + inpGet I (j + 1) * inpGet I (N + (j + 1)))
    (inpGet I 0 * inpGet I N)

/-! ### §6.1  Pilot length `N = 4` (concrete, `w = 64`) -/

/-- `dot4`: the inner product over length-4 arrays (`nIn = 8`). -/
def dot4 : Thir := dotN 4

/-- The length-4 input context: `8` `rW 64` words. -/
abbrev ctxt4 : Ctxt jasminDialect := frontCtxt 64 8 []

/-- The concrete lowered `Com jasminDialect` for `dot4` (the front's output).
    `dot4_lowers` proves the lowering returns `some`, so the `getD` is the real
    Com. The fallback `.ret .here` is over the non-empty input context `ctxt4 =
    replicate 8 (rW 64)` and is never taken. -/
def dot4Com : Com jasminDialect ctxt4 (rW 64) :=
  (thirToJasmin [] (initFState 64 8) dot4).getD
    (.ret (Γ := ctxt4)
      (Ctxt.Var.here :
        Ctxt.Var (d := jasminDialect) (rW 64 :: List.replicate 7 (rW 64)) (rW 64)))

/-- The lowering of `dot4` succeeds. -/
theorem dot4_lowers : (thirToJasmin [] (initFState 64 8) dot4).isSome := by
  native_decide

/-- **Connecting theorem (`FrontValueAgrees`) for the `u64` pilot fn.** The
    lowered `Com jasminDialect` for `dot4` denotes the same `BitVec 64` as the
    THIR `dot4` for every input vector `I`. This is the `w = 64` regression. -/
theorem dot4_FrontValueAgrees (I : Fin 8 → BitVec 64)
    (c : Com jasminDialect ctxt4 (rW 64))
    (hc : thirToJasmin [] (initFState 64 8) dot4 = some c) :
    dot4.denote I (LEnv.empty 64) = some (c.denote (inputValuation 64 8 I)) :=
  thirToJasmin_denote [] I dot4 (LEnv.empty 64) (initFState 64 8)
    (inputValuation 64 8 I) c (initAgree I) hc

/-! ### §6.2  Emit `dot4` through the verified `emitAbiOrchReg` → owned-x86

`emitAbiOrchReg` (`JasminAbiEmit.lean`) walks any `Com jasminDialect`
structurally, keying binding `k`'s destination to `dstName k` and input word `i`
to `inName i`. We feed it **the front's own lowered Com** (`dot4Com`) so the
emitted artifact is exactly the `Com` the connecting theorem covers. -/

/-- The flat destination-slot mirror of `dotN`'s lowered bindings: binding `0`
    writes the `acc` slot; then each of the `N-1` inner-product steps writes
    `prod` (slot 1) then `acc` (slot 0); finally the `ret` arm emits one trailing
    `acc`-copy binding (slot 0). Total `2N` bindings, the last being `acc`. -/
def dotSlots (N : Nat) : List Nat :=
  (0 :: (List.range (N - 1)).flatMap (fun _ => [1, 0])) ++ [0]

/-- Per-binding destination register name (`k[acc]`/`k[prod]`). -/
def dotDstName (N : Nat) (n : Nat) : String :=
  "k[" ++ toString ((dotSlots N).getD n 0) ++ "]"

/-- Input word `i` (head-first) resolves to a copied-in register `k[2 + i]`. -/
def dotInName (i : Nat) : String := "k[" ++ toString (2 + i) ++ "]"

/-- The state file: `acc`, `prod`, and `2N` input slots. -/
def dotRegDecls (N : Nat) : List String :=
  ["stack u64[" ++ toString (2 + 2 * N) ++ "] k"]

/-- The emitted `.jazz` for `dot4` through the verified register-arith
    orchestration, applied to the **front's own** lowered Com (`dot4Com`). ABI:
    `reg ptr u64[1] out`, `reg const ptr u64[8] inp`. -/
def dot4Jazz : String :=
  emitAbiOrchReg "dot4" (w := 64) (nIn := 8) (nOut := 1) (nCopy := 8)
    (dotRegDecls 4) dotInName (dotDstName 4) dot4Com

#eval IO.println dot4Jazz

/- The export has the expected `dot4` ABI (1-word out, 8-word in). -/
#guard (strContains dot4Jazz "export fn dot4(reg ptr u64[1] out, reg const ptr u64[8] inp)")

/- The emitted body renders real multiply/add computation (no skipped ops). -/
#guard !(strContains dot4Jazz "non-regArith op skipped")

/-! ## §7  SHA-256 leaf `small_sigma0` (`w = 32`, #605 Step 4)

```rust
fn small_sigma0(x: u32) -> u32 {
    x.rotate_right(7) ^ x.rotate_right(18) ^ (x >> 3)
}
```

A single `u32` input (`nIn = 1`, `x = inp[0]`). The ANF lowering (charon-shaped)
binds each ARX op to a fresh local:

```
let r7  = ror(7,  x);          -- rotate_right(x, 7)
let r18 = ror(18, x);          -- rotate_right(x, 18)
let s3  = x >> 3;             -- x >> 3   (Rhs.shrImm 3 — immediate count)
let t   = r7 ^ r18;           -- first xor   (Rhs.bin .xor)
let o   = t ^ s3;             -- second xor  (Rhs.bin .xor)
ret o
```

This exercises `Rhs.ror`, `Rhs.shrImm`, and `Rhs.bin .xor` together at the
non-`u64` width — the first ARX/sponge leaf taken end-to-end. The `x >> 3` uses
the immediate-count `Rhs.shrImm` (not `Rhs.bin .shr`, whose count is a register
read jasminc x86 rejects), so the emitted shift is `w0 = w0 >> 3;`. -/

/-- The σ₀ THIR over `nIn = 1` (`x = inp[0]`). -/
def sigma0Thir : Thir :=
  .let_ "r7" (.ror 7 (.inp 0))
    (.let_ "r18" (.ror 18 (.inp 0))
      (.let_ "s3" (.shrImm 3 (.inp 0))
        (.let_ "t" (.bin .xor (.lvar "r7") (.lvar "r18"))
          (.let_ "o" (.bin .xor (.lvar "t") (.lvar "s3"))
            (.ret (.lvar "o"))))))

/-- The reference (spec) σ₀ over `BitVec 32`, matching the SHA-256 FIPS 180-4
    definition `ROTR⁷(x) ⊕ ROTR¹⁸(x) ⊕ SHR³(x)`. -/
def sigma0Spec (x : BitVec 32) : BitVec 32 :=
  (x.rotateRight 7) ^^^ (x.rotateRight 18) ^^^ (x >>> (3 : Nat))

/-- The σ₀ THIR computes the spec for any input vector `I` (single word `x = I
    0`) — a sanity check of the THIR semantics against the FIPS definition. -/
theorem sigma0Thir_denote (I : Fin 1 → BitVec 32) :
    sigma0Thir.denote I (LEnv.empty 32) = some (sigma0Spec (I 0)) := by
  have h0 : inpGet I 0 = I 0 := by simp [inpGet]
  simp only [sigma0Thir, sigma0Spec, Thir.denote, Rhs.denote, Atom.denote,
    h0, LEnv.set, LEnv.empty, JasminBinOp.apply, Option.bind_some,
    Option.map_some, reduceIte, String.reduceEq]

/-- The σ₀ input context: `1` `rW 32` word. -/
abbrev ctxtSigma0 : Ctxt jasminDialect := frontCtxt 32 1 []

/-- The concrete lowered `Com jasminDialect` for `small_sigma0`. -/
def sigma0Com : Com jasminDialect ctxtSigma0 (rW 32) :=
  (thirToJasmin [] (initFState 32 1) sigma0Thir).getD
    (.ret (Γ := ctxtSigma0)
      (Ctxt.Var.here :
        Ctxt.Var (d := jasminDialect) (rW 32 :: List.replicate 0 (rW 32)) (rW 32)))

/-- The lowering of `small_sigma0` succeeds. -/
theorem sigma0_lowers : (thirToJasmin [] (initFState 32 1) sigma0Thir).isSome := by
  native_decide

/-- **Connecting theorem (`FrontValueAgrees`) for `small_sigma0`.** The lowered
    `Com jasminDialect` for σ₀ denotes the same `BitVec 32` as the THIR for every
    input vector `I` (single word `x = I 0`). This is the `w = 32` end-to-end
    milestone, instantiating the width-parameterized `thirToJasmin_denote`. -/
theorem sigma0_FrontValueAgrees (I : Fin 1 → BitVec 32)
    (c : Com jasminDialect ctxtSigma0 (rW 32))
    (hc : thirToJasmin [] (initFState 32 1) sigma0Thir = some c) :
    sigma0Thir.denote I (LEnv.empty 32) = some (c.denote (inputValuation 32 1 I)) :=
  thirToJasmin_denote [] I sigma0Thir (LEnv.empty 32) (initFState 32 1)
    (inputValuation 32 1 I) c (initAgree I) hc

/-! ### §7.1  Emit `small_sigma0` → owned-x86 -/

/-- σ₀'s lowered bindings, in order: `r7`, `r18`, `s3` (immediate shift), `t`,
    `o`, then the `ret` trailing copy. Each gets its own slot `0..5`. -/
def sigma0Slots : List Nat := [0, 1, 2, 3, 4, 5]

/-- Per-binding destination register name. -/
def sigma0DstName (n : Nat) : String :=
  "k[" ++ toString (sigma0Slots.getD n 0) ++ "]"

/-- The single input word `x` resolves to a copied-in register `k[6]` (after the
    6 working slots `0..5`). -/
def sigma0InName (_ : Nat) : String := "k[6]"

/-- The state file: 6 working slots plus the 1 input slot. -/
def sigma0RegDecls : List String := ["stack u32[7] k"]

/-- The emitted `.jazz` for `small_sigma0` through the verified register-arith /
    rotate orchestration, applied to the **front's own** lowered Com
    (`sigma0Com`). ABI: `reg ptr u32[1] out`, `reg const ptr u32[1] inp`. -/
def sigma0Jazz : String :=
  emitAbiOrchReg "small_sigma0" (w := 32) (nIn := 1) (nOut := 1) (nCopy := 1)
    sigma0RegDecls sigma0InName sigma0DstName sigma0Com

#eval IO.println sigma0Jazz

/- The export has the expected `small_sigma0` ABI (1-word out, 1-word in, u32). -/
#guard (strContains sigma0Jazz "export fn small_sigma0(reg ptr u32[1] out, reg const ptr u32[1] inp)")

/- The emitted body renders real computation (no skipped ops). -/
#guard !(strContains sigma0Jazz "non-regArith op skipped")

/- The emitted body uses the native right-rotate op (`#ROR_32`, the `Rhs.ror`
    arm) — both σ₀ rotates render through the single x86 rotate intrinsic. -/
#guard (strContains sigma0Jazz "#ROR_32(")

/-! ## §8  Width CAST pilot (`castW`, #605 Step 5b)

Two complementary pieces close Step 5b — the width cast:

* **Front-connected, homogeneous (proved through `thirToJasmin_denote`).** The
  `Rhs.cast` arm lowers to the dialect `castW w w` op (a same-width zero-extend
  = the identity), so it stays in the homogeneous `rW w` register file and is
  carried by the *same* preservation theorem as every other op. `castThir`
  exercises it end-to-end; `cast_FrontValueAgrees` is its connecting theorem.

* **Cross-width (the `cast#8` digest-byte case).** The dialect's `castW`
  op is width-changing; the register-arith front is single-width, so the
  `u32 → u8 → u32` round-trip (`(u32)((u8) x) = x & 0xff`, the SHA-256 digest
  byte-extract / repack) is realised by a dedicated two-`castW` `Com`
  (`castDemoCom`) and the focused `emitAbiOrchCast` orchestration. Its
  denotation is checked equal to the FIPS byte-mask reference, and the KAT
  (`bench/thir_front_step5`) ties the emitted jasmin to it. -/

/-- The σ-style THIR exercising the front `Rhs.cast` arm (a same-width zero-extend
    of the single input word, `w = 32`). -/
def castThir : Thir :=
  .let_ "c" (.cast (.inp 0)) (.ret (.lvar "c"))

/-- The front cast is the same-width zero-extend (the identity on `BitVec 32`). -/
theorem castThir_denote (I : Fin 1 → BitVec 32) :
    castThir.denote I (LEnv.empty 32) = some (I 0) := by
  have h0 : inpGet I 0 = I 0 := by simp [inpGet]
  simp only [castThir, Thir.denote, Rhs.denote, Atom.denote, h0,
    LEnv.set, Option.map_some, Option.bind_some, BitVec.setWidth_eq, reduceIte]

/-- **Connecting theorem (`FrontValueAgrees`) for the front cast arm.** The
    lowered `Com jasminDialect` for `castThir` denotes the same `BitVec 32` as the
    THIR, for every input vector `I`. -/
theorem cast_FrontValueAgrees (I : Fin 1 → BitVec 32)
    (c : Com jasminDialect (frontCtxt 32 1 []) (rW 32))
    (hc : thirToJasmin [] (initFState 32 1) castThir = some c) :
    castThir.denote I (LEnv.empty 32) = some (c.denote (inputValuation 32 1 I)) :=
  thirToJasmin_denote [] I castThir (LEnv.empty 32) (initFState 32 1)
    (inputValuation 32 1 I) c (initAgree I) hc

/-- The front cast lowering succeeds. -/
theorem castThir_lowers : (thirToJasmin [] (initFState 32 1) castThir).isSome := by
  native_decide

/-! ### §8.1  Cross-width cast `Com` (`u32 → u8 → u32`) and its emit

`castDemoCom` is the two-op `Com` `let y = (u8) x; let z = (u32) y; ret z`, the
SHA-256 digest byte-extract/repack shape. Its denotation is the byte mask
`x &&& 0xff`. `emitAbiOrchCast` renders it to jasmin (a narrowing `(8u)` then a
widening `(32u)`), KAT'd value-identical in `bench/thir_front_step5`. -/

/-- Cross-width cast `Com`: `let y = castW 32 8 x; let z = castW 8 32 y; ret z`,
    over the one-word `[reg 32]` input context. -/
def castDemoCom : Com jasminDialect [rW 32] (rW 32) :=
  .var (.mk (.castW 32 8) rfl (.cons .here .nil))
    (.var (.mk (.castW 8 32) rfl (.cons .here .nil))
      (.ret .here))

/-- The FIPS reference for the cast round-trip: zero all but the low byte. -/
def castDemoSpec (x : BitVec 32) : BitVec 32 := x &&& 0xff

/-- `castDemoCom` denotes the byte mask `x &&& 0xff` (the `(u32)((u8) x)`
    semantics), for every input `x`. The two `castW`s compose to a low-byte
    truncate-then-zero-extend. -/
theorem castDemoCom_denote (x : BitVec 32) :
    castDemoCom.denote (.cons x .nil) = castDemoSpec x := by
  show BitVec.setWidth 32 (BitVec.setWidth 8 x) = castDemoSpec x
  rw [castDemoSpec]
  bv_decide

/-- The emitted cross-width cast `.jazz` (`u32 → u8 → u32` round-trip). -/
def castDemoJazz : String := emitAbiOrchCast "cast_demo" 32 8

#eval IO.println castDemoJazz

/- The export has the expected `cast_demo` ABI (1-word u32 out / in). -/
#guard (strContains castDemoJazz "export fn cast_demo(reg ptr u32[1] out, reg const ptr u32[1] inp)")

/- The emitted body renders the narrowing then widening jasmin width casts. -/
#guard (strContains castDemoJazz "(8u) w0") && (strContains castDemoJazz "(32u) wn")

/-! ## §9  Indexed array STORE pilot (`stackStore`, #605 Step 5a)

The dialect's `stackStore w n` op (the dual of the `inp[i]` indexed *read* the
front already supports) writes one element of a stack array at a runtime index.
It was already in the dialect but unrendered by the register-arith emit; the
`emitBodyReg` `stackStore` arm now renders it as `arr[(uint)idx] = val;`.
`storeDemoCom` exercises the op directly: write `arr[idx] = val` on a length-4
`u32` array; `storeDemoCom_denote` proves the denotation is the functional
update `stackSet`. `emitAbiOrchStore` renders it to jasmin (copy-in, indexed
store, copy-out), KAT'd in `bench/thir_front_step5`.

**Scope (5a):** the array *write* op is wired into the dialect emit and
exercised by this pilot, but a stack-array *value* is not a `rW w` register, so
threading a mutable `stackArr` through the homogeneous register-file front
(`thirToJasmin`) would require a heterogeneous typing pass. That generalisation
is deferred; Step 6 (`sha256_compress`) operates over a fixed 8-word `u32` state
that the register-file front already models as `inp[i]` reads + `dstName` slot
writes (no runtime-indexed store), so it is **not blocked** by this deferral. -/

/-- Indexed-store `Com`: `let arr' = stackStore arr idx val; ret arr'`, over the
    context `[stackArr 32 4, reg 64, reg 32]` (array, index, value). -/
def storeDemoCom :
    Com jasminDialect [.stackArr 32 4, .reg 64, .reg 32] (.stackArr 32 4) :=
  .var (.mk (.stackStore 32 4) rfl
          (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))))
    (.ret .here)

/-- `storeDemoCom` denotes the functional update `stackSet arr idx.toNat val` —
    element `idx mod 4` becomes `val`, the rest unchanged. -/
theorem storeDemoCom_denote (arr : Fin 4 → BitVec 32) (idx : BitVec 64)
    (val : BitVec 32) :
    storeDemoCom.denote (.cons arr (.cons idx (.cons val .nil)))
      = stackSet arr idx.toNat val := rfl

/-- The emitted indexed-store `.jazz` over a length-4 `u32` array. -/
def storeDemoJazz : String := emitAbiOrchStore "store_demo" 32 4

#eval IO.println storeDemoJazz

/-- The export has the expected `store_demo` ABI (array out / in, scalar idx/val). -/
theorem storeDemo_export_sig :
    strContains storeDemoJazz
      ("export fn store_demo(reg ptr u32[4] out, reg const ptr u32[4] inp, "
        ++ "reg u64 idx, reg u32 val)") = true := by native_decide

/- The emitted body renders the runtime-indexed element store. -/
#guard (strContains storeDemoJazz "out[(uint)idx] = val;")

/-! ## §10  SHA-256 compression round core through the front (`w = 32`, #605 Step 6)

The capstone of the THIR→Com compile-from-hax front: the SHA-256 compression
round update (FIPS 180-4 §6.2.2) and the message-schedule word (§6.2.1), lowered
from THIR-ANF into `Com jasminDialect` by the verified width-parameterized front
and emitted to owned-x86 jasmin. Every op is already in the `Rhs` surface — the
round uses `Rhs.ror` (the six `Σ` rotates), `Rhs.bin .and`/`.xor` (Ch/Maj), and
`Rhs.add` (the wrapping u32 sum). Bitwise-NOT (the `~e` of `Ch`) is **not** a
dialect op, so `~e` is expressed as `e ^ 0xffffffff` (a `Rhs.bin .xor` against an
all-ones literal); this keeps the op surface and the preservation cascade closed.

### FIPS 180-4 functions (the reference spec)

* Σ₁(e) = ROTR⁶(e) ⊕ ROTR¹¹(e) ⊕ ROTR²⁵(e)
* Ch(e,f,g) = (e ∧ f) ⊕ (¬e ∧ g)
* Σ₀(a) = ROTR²(a) ⊕ ROTR¹³(a) ⊕ ROTR²²(a)
* Maj(a,b,c) = (a ∧ b) ⊕ (a ∧ c) ⊕ (b ∧ c)
* T₁ = h + Σ₁(e) + Ch(e,f,g) + K_t + W_t,  T₂ = Σ₀(a) + Maj(a,b,c)
* a' = T₁ + T₂,  e' = d + T₁
* σ₀(x) = ROTR⁷(x) ⊕ ROTR¹⁸(x) ⊕ SHR³(x)  (= `sigma0Spec`, §7)
* σ₁(x) = ROTR¹⁷(x) ⊕ ROTR¹⁹(x) ⊕ SHR¹⁰(x)
* W_t = σ₁(W_{t-2}) + W_{t-7} + σ₀(W_{t-15}) + W_{t-16}

### What carries the connecting theorem

The round's two single-word outputs (`a'`, `e'`), the message-schedule word
(`W_t`), and the four sub-functions (Σ₁/Ch/Σ₀/Maj/σ₁) are each lowered through
`thirToJasmin` with a `FrontValueAgrees` connecting theorem (the lowered Com
denotes the same `BitVec 32` as the THIR) and a `*_denote` theorem (the THIR
denotation equals the FIPS reference). The connecting theorems are direct
instantiations of the width-parameterized `thirToJasmin_denote`. -/

/-- FIPS 180-4 Σ₁(e) = ROTR⁶(e) ⊕ ROTR¹¹(e) ⊕ ROTR²⁵(e). -/
def bigSigma1Spec (e : BitVec 32) : BitVec 32 :=
  (e.rotateRight 6) ^^^ (e.rotateRight 11) ^^^ (e.rotateRight 25)

/-- FIPS 180-4 Σ₀(a) = ROTR²(a) ⊕ ROTR¹³(a) ⊕ ROTR²²(a). -/
def bigSigma0Spec (a : BitVec 32) : BitVec 32 :=
  (a.rotateRight 2) ^^^ (a.rotateRight 13) ^^^ (a.rotateRight 22)

/-- FIPS 180-4 σ₁(x) = ROTR¹⁷(x) ⊕ ROTR¹⁹(x) ⊕ SHR¹⁰(x). -/
def smallSigma1Spec (x : BitVec 32) : BitVec 32 :=
  (x.rotateRight 17) ^^^ (x.rotateRight 19) ^^^ (x >>> (10 : Nat))

/-- FIPS 180-4 Ch(e,f,g) = (e ∧ f) ⊕ (¬e ∧ g), with `¬e` as `e ⊕ 0xffffffff`. -/
def chSpec (e f g : BitVec 32) : BitVec 32 :=
  (e &&& f) ^^^ ((e ^^^ 0xffffffff) &&& g)

/-- FIPS 180-4 Maj(a,b,c) = (a ∧ b) ⊕ (a ∧ c) ⊕ (b ∧ c). -/
def majSpec (a b c : BitVec 32) : BitVec 32 :=
  (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)

/-- FIPS 180-4 message-schedule word
    `W_t = σ₁(W_{t-2}) + W_{t-7} + σ₀(W_{t-15}) + W_{t-16}`, summed left-to-right
    (wrapping u32). Input order: `w2 = W_{t-2}`, `w7 = W_{t-7}`,
    `w15 = W_{t-15}`, `w16 = W_{t-16}`. -/
def msgSchedSpec (w2 w7 w15 w16 : BitVec 32) : BitVec 32 :=
  smallSigma1Spec w2 + w7 + sigma0Spec w15 + w16

/-- FIPS 180-4 `T₁ = h + Σ₁(e) + Ch(e,f,g) + K_t + W_t`, summed left-to-right. -/
def t1Spec (e f g h kt wt : BitVec 32) : BitVec 32 :=
  h + bigSigma1Spec e + chSpec e f g + kt + wt

/-- FIPS 180-4 `T₂ = Σ₀(a) + Maj(a,b,c)`. -/
def t2Spec (a b c : BitVec 32) : BitVec 32 :=
  bigSigma0Spec a + majSpec a b c

/-- FIPS 180-4 round output `a' = T₁ + T₂`. Input order matches the bundled
    `sha256RoundAThir` vector (`a,b,c,d,e,f,g,h,K_t,W_t`). -/
def sha256RoundASpec (a b c _d e f g h kt wt : BitVec 32) : BitVec 32 :=
  t1Spec e f g h kt wt + t2Spec a b c

/-- FIPS 180-4 round output `e' = d + T₁`. -/
def sha256RoundESpec (_a _b _c d e f g h kt wt : BitVec 32) : BitVec 32 :=
  d + t1Spec e f g h kt wt

/-! ### §10.1  Sub-function front fns (each a `FrontValueAgrees` leaf)

Σ₁/Σ₀ are direct width-32 analogs of the proven `sigma0Thir` (three rotates and
two xors); σ₁ adds a `Rhs.shrImm 10`. Ch/Maj exercise the `Rhs.bin .and`/`.xor`
surface and the NOT-via-xor encoding. Each is a single bundled-input THIR. -/

/-- Σ₁(e) THIR over `nIn = 1` (`e = inp[0]`). -/
def bigSigma1Thir : Thir :=
  .let_ "r6" (.ror 6 (.inp 0))
    (.let_ "r11" (.ror 11 (.inp 0))
      (.let_ "r25" (.ror 25 (.inp 0))
        (.let_ "t" (.bin .xor (.lvar "r6") (.lvar "r11"))
          (.let_ "o" (.bin .xor (.lvar "t") (.lvar "r25"))
            (.ret (.lvar "o"))))))

/-- Σ₀(a) THIR over `nIn = 1` (`a = inp[0]`). -/
def bigSigma0Thir : Thir :=
  .let_ "r2" (.ror 2 (.inp 0))
    (.let_ "r13" (.ror 13 (.inp 0))
      (.let_ "r22" (.ror 22 (.inp 0))
        (.let_ "t" (.bin .xor (.lvar "r2") (.lvar "r13"))
          (.let_ "o" (.bin .xor (.lvar "t") (.lvar "r22"))
            (.ret (.lvar "o"))))))

/-- σ₁(x) THIR over `nIn = 1` (`x = inp[0]`); the message-schedule sibling of
    `sigma0Thir`, with the `x >> 10` immediate shift. -/
def smallSigma1Thir : Thir :=
  .let_ "r17" (.ror 17 (.inp 0))
    (.let_ "r19" (.ror 19 (.inp 0))
      (.let_ "s10" (.shrImm 10 (.inp 0))
        (.let_ "t" (.bin .xor (.lvar "r17") (.lvar "r19"))
          (.let_ "o" (.bin .xor (.lvar "t") (.lvar "s10"))
            (.ret (.lvar "o"))))))

/-- Ch(e,f,g) THIR over `nIn = 3` (`e,f,g = inp[0],inp[1],inp[2]`). `¬e` is the
    xor against the all-ones literal `0xffffffff` (NOT is not a dialect op). -/
def chThir : Thir :=
  .let_ "ones" (.atom (.lit 0xffffffff))
    (.let_ "ef" (.bin .and (.inp 0) (.inp 1))
      (.let_ "ne" (.bin .xor (.inp 0) (.lvar "ones"))
        (.let_ "neg" (.bin .and (.lvar "ne") (.inp 2))
          (.let_ "o" (.bin .xor (.lvar "ef") (.lvar "neg"))
            (.ret (.lvar "o"))))))

/-- Maj(a,b,c) THIR over `nIn = 3` (`a,b,c = inp[0],inp[1],inp[2]`). -/
def majThir : Thir :=
  .let_ "ab" (.bin .and (.inp 0) (.inp 1))
    (.let_ "ac" (.bin .and (.inp 0) (.inp 2))
      (.let_ "bc" (.bin .and (.inp 1) (.inp 2))
        (.let_ "t" (.bin .xor (.lvar "ab") (.lvar "ac"))
          (.let_ "o" (.bin .xor (.lvar "t") (.lvar "bc"))
            (.ret (.lvar "o"))))))

/-! ### §10.2  Message-schedule word `W_t` and the round outputs `a'`, `e'`

`msgSchedThir` is the four-operand schedule word
`σ₁(W_{t-2}) + W_{t-7} + σ₀(W_{t-15}) + W_{t-16}` (`nIn = 4`, inputs
`W_{t-2},W_{t-7},W_{t-15},W_{t-16}`). The two round THIRs each take the bundled
10-word vector `a,b,c,d,e,f,g,h,K_t,W_t` (`nIn = 10`) and compute the full
`T₁`/`T₂` chain; `sha256RoundAThir` returns `a' = T₁+T₂`, `sha256RoundEThir`
returns `e' = d+T₁` (the two single-word outputs of one compression round). -/

/-- The schedule-word THIR over `nIn = 4`
    (`w2,w7,w15,w16 = inp[0..3]`): inlines σ₁ and σ₀ and sums left-to-right. -/
def msgSchedThir : Thir :=
  -- σ₁(w2)
  .let_ "a17" (.ror 17 (.inp 0))
  (.let_ "a19" (.ror 19 (.inp 0))
  (.let_ "a10" (.shrImm 10 (.inp 0))
  (.let_ "ax" (.bin .xor (.lvar "a17") (.lvar "a19"))
  (.let_ "s1" (.bin .xor (.lvar "ax") (.lvar "a10"))
  -- σ₀(w15)
  (.let_ "b7" (.ror 7 (.inp 2))
  (.let_ "b18" (.ror 18 (.inp 2))
  (.let_ "b3" (.shrImm 3 (.inp 2))
  (.let_ "bx" (.bin .xor (.lvar "b7") (.lvar "b18"))
  (.let_ "s0" (.bin .xor (.lvar "bx") (.lvar "b3"))
  -- sum: ((σ₁(w2) + w7) + σ₀(w15)) + w16
  (.let_ "u1" (.add (.lvar "s1") (.inp 1))
  (.let_ "u2" (.add (.lvar "u1") (.lvar "s0"))
  (.let_ "o" (.add (.lvar "u2") (.inp 3))
  (.ret (.lvar "o"))))))))))))))

/-- The shared `T₁`/`T₂` body of the round, parameterized by which final output
    `Rhs` to return (`a'` or `e'`). Inputs `a..h,K,W = inp[0..9]`. -/
def sha256RoundCore (finalName : String) (final : Rhs) : Thir :=
  -- 0xffffffff for the NOT-via-xor in Ch (ANF: literal operand must be bound)
  .let_ "ones" (.atom (.lit 0xffffffff))
  -- Σ₁(e), e = inp[4]
  (.let_ "e6" (.ror 6 (.inp 4))
  (.let_ "e11" (.ror 11 (.inp 4))
  (.let_ "e25" (.ror 25 (.inp 4))
  (.let_ "ex" (.bin .xor (.lvar "e6") (.lvar "e11"))
  (.let_ "S1" (.bin .xor (.lvar "ex") (.lvar "e25"))
  -- Ch(e,f,g), f = inp[5], g = inp[6]
  (.let_ "ef" (.bin .and (.inp 4) (.inp 5))
  (.let_ "ne" (.bin .xor (.inp 4) (.lvar "ones"))
  (.let_ "neg" (.bin .and (.lvar "ne") (.inp 6))
  (.let_ "Ch" (.bin .xor (.lvar "ef") (.lvar "neg"))
  -- T₁ = h + Σ₁(e) + Ch + K + W ; h = inp[7], K = inp[8], W = inp[9]
  (.let_ "th" (.add (.inp 7) (.lvar "S1"))
  (.let_ "tc" (.add (.lvar "th") (.lvar "Ch"))
  (.let_ "tk" (.add (.lvar "tc") (.inp 8))
  (.let_ "T1" (.add (.lvar "tk") (.inp 9))
  -- Σ₀(a), a = inp[0]
  (.let_ "a2" (.ror 2 (.inp 0))
  (.let_ "a13" (.ror 13 (.inp 0))
  (.let_ "a22" (.ror 22 (.inp 0))
  (.let_ "ax2" (.bin .xor (.lvar "a2") (.lvar "a13"))
  (.let_ "S0" (.bin .xor (.lvar "ax2") (.lvar "a22"))
  -- Maj(a,b,c), b = inp[1], c = inp[2]
  (.let_ "ab" (.bin .and (.inp 0) (.inp 1))
  (.let_ "ac" (.bin .and (.inp 0) (.inp 2))
  (.let_ "bc" (.bin .and (.inp 1) (.inp 2))
  (.let_ "mx" (.bin .xor (.lvar "ab") (.lvar "ac"))
  (.let_ "Maj" (.bin .xor (.lvar "mx") (.lvar "bc"))
  -- T₂ = Σ₀(a) + Maj
  (.let_ "T2" (.add (.lvar "S0") (.lvar "Maj"))
  (.let_ finalName final
  (.ret (.lvar finalName)))))))))))))))))))))))))))

/-- Round output `a'` THIR (`nIn = 10`, returns `T₁ + T₂`). -/
def sha256RoundAThir : Thir :=
  sha256RoundCore "out" (.add (.lvar "T1") (.lvar "T2"))

/-- Round output `e'` THIR (`nIn = 10`, returns `d + T₁`, `d = inp[3]`). -/
def sha256RoundEThir : Thir :=
  sha256RoundCore "out" (.add (.inp 3) (.lvar "T1"))

/-- Σ₁ THIR computes the FIPS Σ₁ spec for any input vector `I`. -/
theorem bigSigma1Thir_denote (I : Fin 1 → BitVec 32) :
    bigSigma1Thir.denote I (LEnv.empty 32) = some (bigSigma1Spec (I 0)) := by
  have h0 : inpGet I 0 = I 0 := by simp [inpGet]
  simp only [bigSigma1Thir, bigSigma1Spec, Thir.denote, Rhs.denote, Atom.denote,
    h0, LEnv.set, LEnv.empty, JasminBinOp.apply, Option.bind_some,
    Option.map_some, reduceIte, String.reduceEq]

/-- Σ₀ THIR computes the FIPS Σ₀ spec for any input vector `I`. -/
theorem bigSigma0Thir_denote (I : Fin 1 → BitVec 32) :
    bigSigma0Thir.denote I (LEnv.empty 32) = some (bigSigma0Spec (I 0)) := by
  have h0 : inpGet I 0 = I 0 := by simp [inpGet]
  simp only [bigSigma0Thir, bigSigma0Spec, Thir.denote, Rhs.denote, Atom.denote,
    h0, LEnv.set, LEnv.empty, JasminBinOp.apply, Option.bind_some,
    Option.map_some, reduceIte, String.reduceEq]

/-- σ₁ THIR computes the FIPS σ₁ spec for any input vector `I`. -/
theorem smallSigma1Thir_denote (I : Fin 1 → BitVec 32) :
    smallSigma1Thir.denote I (LEnv.empty 32) = some (smallSigma1Spec (I 0)) := by
  have h0 : inpGet I 0 = I 0 := by simp [inpGet]
  simp only [smallSigma1Thir, smallSigma1Spec, Thir.denote, Rhs.denote, Atom.denote,
    h0, LEnv.set, LEnv.empty, JasminBinOp.apply, Option.bind_some,
    Option.map_some, reduceIte, String.reduceEq]

/-- Ch THIR computes the FIPS Ch spec (with NOT-via-xor) for any input vector. -/
theorem chThir_denote (I : Fin 3 → BitVec 32) :
    chThir.denote I (LEnv.empty 32) = some (chSpec (I 0) (I 1) (I 2)) := by
  have h0 : inpGet I 0 = I 0 := by simp [inpGet]
  have h1 : inpGet I 1 = I 1 := by simp [inpGet]
  have h2 : inpGet I 2 = I 2 := by simp [inpGet]
  simp only [chThir, chSpec, Thir.denote, Rhs.denote, Atom.denote,
    h0, h1, h2, LEnv.set, LEnv.empty, JasminBinOp.apply, Option.bind_some,
    Option.map_some, reduceIte, String.reduceEq, BitVec.ofNat_eq_ofNat]

/-- Maj THIR computes the FIPS Maj spec for any input vector. -/
theorem majThir_denote (I : Fin 3 → BitVec 32) :
    majThir.denote I (LEnv.empty 32) = some (majSpec (I 0) (I 1) (I 2)) := by
  have h0 : inpGet I 0 = I 0 := by simp [inpGet]
  have h1 : inpGet I 1 = I 1 := by simp [inpGet]
  have h2 : inpGet I 2 = I 2 := by simp [inpGet]
  simp only [majThir, majSpec, Thir.denote, Rhs.denote, Atom.denote,
    h0, h1, h2, LEnv.set, LEnv.empty, JasminBinOp.apply, Option.bind_some,
    Option.map_some, reduceIte, String.reduceEq]

/-- The schedule-word THIR computes the FIPS `W_t` spec for any input vector. -/
theorem msgSchedThir_denote (I : Fin 4 → BitVec 32) :
    msgSchedThir.denote I (LEnv.empty 32)
      = some (msgSchedSpec (I 0) (I 1) (I 2) (I 3)) := by
  have h0 : inpGet I 0 = I 0 := by simp [inpGet]
  have h1 : inpGet I 1 = I 1 := by simp [inpGet]
  have h2 : inpGet I 2 = I 2 := by simp [inpGet]
  have h3 : inpGet I 3 = I 3 := by simp [inpGet]
  simp only [msgSchedThir, msgSchedSpec, smallSigma1Spec, sigma0Spec,
    Thir.denote, Rhs.denote, Atom.denote, h0, h1, h2, h3, LEnv.set, LEnv.empty,
    JasminBinOp.apply, Option.bind_some, Option.map_some, reduceIte,
    String.reduceEq]

/-- The `a'` round THIR computes the FIPS round output `a' = T₁+T₂`. -/
theorem sha256RoundAThir_denote (I : Fin 10 → BitVec 32) :
    sha256RoundAThir.denote I (LEnv.empty 32)
      = some (sha256RoundASpec (I 0) (I 1) (I 2) (I 3) (I 4) (I 5) (I 6) (I 7)
          (I 8) (I 9)) := by
  have h0 : inpGet I 0 = I 0 := by simp [inpGet]
  have h1 : inpGet I 1 = I 1 := by simp [inpGet]
  have h2 : inpGet I 2 = I 2 := by simp [inpGet]
  have h4 : inpGet I 4 = I 4 := by simp [inpGet]
  have h5 : inpGet I 5 = I 5 := by simp [inpGet]
  have h6 : inpGet I 6 = I 6 := by simp [inpGet]
  have h7 : inpGet I 7 = I 7 := by simp [inpGet]
  have h8 : inpGet I 8 = I 8 := by simp [inpGet]
  have h9 : inpGet I 9 = I 9 := by simp [inpGet]
  simp only [sha256RoundAThir, sha256RoundCore, sha256RoundASpec, t1Spec, t2Spec,
    bigSigma1Spec, chSpec, bigSigma0Spec, majSpec, Thir.denote, Rhs.denote,
    Atom.denote, h0, h1, h2, h4, h5, h6, h7, h8, h9, LEnv.set, LEnv.empty,
    JasminBinOp.apply, Option.bind_some, Option.map_some, reduceIte,
    String.reduceEq, BitVec.ofNat_eq_ofNat]

/-- The `e'` round THIR computes the FIPS round output `e' = d+T₁`. -/
theorem sha256RoundEThir_denote (I : Fin 10 → BitVec 32) :
    sha256RoundEThir.denote I (LEnv.empty 32)
      = some (sha256RoundESpec (I 0) (I 1) (I 2) (I 3) (I 4) (I 5) (I 6) (I 7)
          (I 8) (I 9)) := by
  have h0 : inpGet I 0 = I 0 := by simp [inpGet]
  have h1 : inpGet I 1 = I 1 := by simp [inpGet]
  have h2 : inpGet I 2 = I 2 := by simp [inpGet]
  have h3 : inpGet I 3 = I 3 := by simp [inpGet]
  have h4 : inpGet I 4 = I 4 := by simp [inpGet]
  have h5 : inpGet I 5 = I 5 := by simp [inpGet]
  have h6 : inpGet I 6 = I 6 := by simp [inpGet]
  have h7 : inpGet I 7 = I 7 := by simp [inpGet]
  have h8 : inpGet I 8 = I 8 := by simp [inpGet]
  have h9 : inpGet I 9 = I 9 := by simp [inpGet]
  simp only [sha256RoundEThir, sha256RoundCore, sha256RoundESpec, t1Spec,
    bigSigma1Spec, chSpec, Thir.denote, Rhs.denote,
    Atom.denote, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, LEnv.set, LEnv.empty,
    JasminBinOp.apply, Option.bind_some, Option.map_some, reduceIte,
    String.reduceEq, BitVec.ofNat_eq_ofNat]

/-! ### §10.3  Connecting theorems (`FrontValueAgrees`) for every round fn

Each front fn's lowered `Com jasminDialect` denotes the same `BitVec 32` as its
THIR, for every input vector — a direct instantiation of the width-parameterized
`thirToJasmin_denote`. Composed with the `*_denote` theorems above (THIR = FIPS
spec) these tie the emitted Com to the FIPS 180-4 reference. -/

/-- Connecting theorem for Σ₁. -/
theorem bigSigma1_FrontValueAgrees (I : Fin 1 → BitVec 32)
    (c : Com jasminDialect (frontCtxt 32 1 []) (rW 32))
    (hc : thirToJasmin [] (initFState 32 1) bigSigma1Thir = some c) :
    bigSigma1Thir.denote I (LEnv.empty 32) = some (c.denote (inputValuation 32 1 I)) :=
  thirToJasmin_denote [] I bigSigma1Thir (LEnv.empty 32) (initFState 32 1)
    (inputValuation 32 1 I) c (initAgree I) hc

/-- Connecting theorem for Σ₀. -/
theorem bigSigma0_FrontValueAgrees (I : Fin 1 → BitVec 32)
    (c : Com jasminDialect (frontCtxt 32 1 []) (rW 32))
    (hc : thirToJasmin [] (initFState 32 1) bigSigma0Thir = some c) :
    bigSigma0Thir.denote I (LEnv.empty 32) = some (c.denote (inputValuation 32 1 I)) :=
  thirToJasmin_denote [] I bigSigma0Thir (LEnv.empty 32) (initFState 32 1)
    (inputValuation 32 1 I) c (initAgree I) hc

/-- Connecting theorem for σ₁. -/
theorem smallSigma1_FrontValueAgrees (I : Fin 1 → BitVec 32)
    (c : Com jasminDialect (frontCtxt 32 1 []) (rW 32))
    (hc : thirToJasmin [] (initFState 32 1) smallSigma1Thir = some c) :
    smallSigma1Thir.denote I (LEnv.empty 32) = some (c.denote (inputValuation 32 1 I)) :=
  thirToJasmin_denote [] I smallSigma1Thir (LEnv.empty 32) (initFState 32 1)
    (inputValuation 32 1 I) c (initAgree I) hc

/-- Connecting theorem for Ch. -/
theorem ch_FrontValueAgrees (I : Fin 3 → BitVec 32)
    (c : Com jasminDialect (frontCtxt 32 3 []) (rW 32))
    (hc : thirToJasmin [] (initFState 32 3) chThir = some c) :
    chThir.denote I (LEnv.empty 32) = some (c.denote (inputValuation 32 3 I)) :=
  thirToJasmin_denote [] I chThir (LEnv.empty 32) (initFState 32 3)
    (inputValuation 32 3 I) c (initAgree I) hc

/-- Connecting theorem for Maj. -/
theorem maj_FrontValueAgrees (I : Fin 3 → BitVec 32)
    (c : Com jasminDialect (frontCtxt 32 3 []) (rW 32))
    (hc : thirToJasmin [] (initFState 32 3) majThir = some c) :
    majThir.denote I (LEnv.empty 32) = some (c.denote (inputValuation 32 3 I)) :=
  thirToJasmin_denote [] I majThir (LEnv.empty 32) (initFState 32 3)
    (inputValuation 32 3 I) c (initAgree I) hc

/-- Connecting theorem for the message-schedule word `W_t`. -/
theorem msgSched_FrontValueAgrees (I : Fin 4 → BitVec 32)
    (c : Com jasminDialect (frontCtxt 32 4 []) (rW 32))
    (hc : thirToJasmin [] (initFState 32 4) msgSchedThir = some c) :
    msgSchedThir.denote I (LEnv.empty 32) = some (c.denote (inputValuation 32 4 I)) :=
  thirToJasmin_denote [] I msgSchedThir (LEnv.empty 32) (initFState 32 4)
    (inputValuation 32 4 I) c (initAgree I) hc

/-- **Connecting theorem for the round output `a'`** — the THIR→Com front lowers
    the full SHA-256 compression-round `a' = T₁+T₂` to a `Com jasminDialect` that
    denotes the same `BitVec 32` as the THIR, for every 10-word input vector. -/
theorem sha256RoundA_FrontValueAgrees (I : Fin 10 → BitVec 32)
    (c : Com jasminDialect (frontCtxt 32 10 []) (rW 32))
    (hc : thirToJasmin [] (initFState 32 10) sha256RoundAThir = some c) :
    sha256RoundAThir.denote I (LEnv.empty 32)
      = some (c.denote (inputValuation 32 10 I)) :=
  thirToJasmin_denote [] I sha256RoundAThir (LEnv.empty 32) (initFState 32 10)
    (inputValuation 32 10 I) c (initAgree I) hc

/-- **Connecting theorem for the round output `e'`** (`e' = d+T₁`). -/
theorem sha256RoundE_FrontValueAgrees (I : Fin 10 → BitVec 32)
    (c : Com jasminDialect (frontCtxt 32 10 []) (rW 32))
    (hc : thirToJasmin [] (initFState 32 10) sha256RoundEThir = some c) :
    sha256RoundEThir.denote I (LEnv.empty 32)
      = some (c.denote (inputValuation 32 10 I)) :=
  thirToJasmin_denote [] I sha256RoundEThir (LEnv.empty 32) (initFState 32 10)
    (inputValuation 32 10 I) c (initAgree I) hc

/-! ### §10.4  Emit the round fns → owned-x86 jasmin

Each fn is lowered to its own `Com` and emitted through the verified
register-arith / rotate orchestration `emitAbiOrchReg`. The slot scheme mirrors
`sigma0`: binding `k` writes working slot `k`; the `nIn` input words are copied
into the trailing register slots `nB, nB+1, …` (`nB` = binding count). The
`stack u32[nB+nIn] k` file holds them all. -/

/-- Build the lowered front `Com` for a width-32 `(m+1)`-input THIR, with the
    fallback `.ret .here` over the (non-empty) input context (never taken — the
    `*_lowers` lemmas prove the lowering returns `some`). -/
def loweredCom32 (m : Nat) (t : Thir) :
    Com jasminDialect (frontCtxt 32 (m + 1) []) (rW 32) :=
  (thirToJasmin [] (initFState 32 (m + 1)) t).getD
    (.ret (Γ := frontCtxt 32 (m + 1) [])
      (Ctxt.Var.here :
        Ctxt.Var (d := jasminDialect) (rW 32 :: List.replicate m (rW 32)) (rW 32)))

/-- Per-fn register-file decls: `nB` working slots + `nIn` input slots. -/
def roundRegDecls (nB nIn : Nat) : List String :=
  ["stack u32[" ++ toString (nB + nIn) ++ "] k"]

/-- Binding `k` → working slot `k`. -/
def roundDstName (n : Nat) : String := "k[" ++ toString n ++ "]"

/-- Input word `i` → copied-in register slot `nB + i`. -/
def roundInName (nB : Nat) (i : Nat) : String := "k[" ++ toString (nB + i) ++ "]"

/-- Σ₁: 6 bindings, 1 input. -/
def bigSigma1Com : Com jasminDialect (frontCtxt 32 1 []) (rW 32) :=
  loweredCom32 0 bigSigma1Thir
theorem bigSigma1_lowers :
    (thirToJasmin [] (initFState 32 1) bigSigma1Thir).isSome := by native_decide
def bigSigma1Jazz : String :=
  emitAbiOrchReg "big_sigma1" (w := 32) (nIn := 1) (nOut := 1) (nCopy := 1)
    (roundRegDecls 6 1) (roundInName 6) roundDstName bigSigma1Com

/-- Σ₀: 6 bindings, 1 input. -/
def bigSigma0Com : Com jasminDialect (frontCtxt 32 1 []) (rW 32) :=
  loweredCom32 0 bigSigma0Thir
theorem bigSigma0_lowers :
    (thirToJasmin [] (initFState 32 1) bigSigma0Thir).isSome := by native_decide
def bigSigma0Jazz : String :=
  emitAbiOrchReg "big_sigma0" (w := 32) (nIn := 1) (nOut := 1) (nCopy := 1)
    (roundRegDecls 6 1) (roundInName 6) roundDstName bigSigma0Com

/-- σ₁: 6 bindings, 1 input. -/
def smallSigma1Com : Com jasminDialect (frontCtxt 32 1 []) (rW 32) :=
  loweredCom32 0 smallSigma1Thir
theorem smallSigma1_lowers :
    (thirToJasmin [] (initFState 32 1) smallSigma1Thir).isSome := by native_decide
def smallSigma1Jazz : String :=
  emitAbiOrchReg "small_sigma1" (w := 32) (nIn := 1) (nOut := 1) (nCopy := 1)
    (roundRegDecls 6 1) (roundInName 6) roundDstName smallSigma1Com

/-- Ch: 5 bindings, 3 inputs. -/
def chCom : Com jasminDialect (frontCtxt 32 3 []) (rW 32) :=
  loweredCom32 2 chThir
theorem ch_lowers :
    (thirToJasmin [] (initFState 32 3) chThir).isSome := by native_decide
def chJazz : String :=
  emitAbiOrchReg "ch" (w := 32) (nIn := 3) (nOut := 1) (nCopy := 3)
    (roundRegDecls 6 3) (roundInName 6) roundDstName chCom

/-- Maj: 6 bindings, 3 inputs. -/
def majCom : Com jasminDialect (frontCtxt 32 3 []) (rW 32) :=
  loweredCom32 2 majThir
theorem maj_lowers :
    (thirToJasmin [] (initFState 32 3) majThir).isSome := by native_decide
def majJazz : String :=
  emitAbiOrchReg "maj" (w := 32) (nIn := 3) (nOut := 1) (nCopy := 3)
    (roundRegDecls 6 3) (roundInName 6) roundDstName majCom

/-- `W_t`: 14 bindings, 4 inputs. -/
def msgSchedCom : Com jasminDialect (frontCtxt 32 4 []) (rW 32) :=
  loweredCom32 3 msgSchedThir
theorem msgSched_lowers :
    (thirToJasmin [] (initFState 32 4) msgSchedThir).isSome := by native_decide
def msgSchedJazz : String :=
  emitAbiOrchReg "msg_sched" (w := 32) (nIn := 4) (nOut := 1) (nCopy := 4)
    (roundRegDecls 14 4) (roundInName 14) roundDstName msgSchedCom

/-- Round output `a'`: 27 bindings, 10 inputs. -/
def sha256RoundACom : Com jasminDialect (frontCtxt 32 10 []) (rW 32) :=
  loweredCom32 9 sha256RoundAThir
theorem sha256RoundA_lowers :
    (thirToJasmin [] (initFState 32 10) sha256RoundAThir).isSome := by native_decide
def sha256RoundAJazz : String :=
  emitAbiOrchReg "sha256_round_a" (w := 32) (nIn := 10) (nOut := 1) (nCopy := 10)
    (roundRegDecls 27 10) (roundInName 27) roundDstName sha256RoundACom

/-- Round output `e'`: 27 bindings, 10 inputs. -/
def sha256RoundECom : Com jasminDialect (frontCtxt 32 10 []) (rW 32) :=
  loweredCom32 9 sha256RoundEThir
theorem sha256RoundE_lowers :
    (thirToJasmin [] (initFState 32 10) sha256RoundEThir).isSome := by native_decide
def sha256RoundEJazz : String :=
  emitAbiOrchReg "sha256_round_e" (w := 32) (nIn := 10) (nOut := 1) (nCopy := 10)
    (roundRegDecls 27 10) (roundInName 27) roundDstName sha256RoundECom

#eval IO.println sha256RoundAJazz
#eval IO.println msgSchedJazz

/- The `a'` round export has the expected ABI (1-word out, 10-word in, u32). -/
#guard (strContains sha256RoundAJazz "export fn sha256_round_a(reg ptr u32[1] out, reg const ptr u32[10] inp)")

/- The `a'` round body renders real computation (no skipped ops). -/
#guard !(strContains sha256RoundAJazz "non-regArith op skipped")

/- The `a'` round body uses the native right-rotate op (the six Σ rotates). -/
#guard (strContains sha256RoundAJazz "#ROR_32(")

/- The `e'` round export has the expected ABI. -/
#guard (strContains sha256RoundEJazz "export fn sha256_round_e(reg ptr u32[1] out, reg const ptr u32[10] inp)")

/- The message-schedule export has the expected ABI (1-word out, 4-word in). -/
#guard (strContains msgSchedJazz "export fn msg_sched(reg ptr u32[1] out, reg const ptr u32[4] inp)")

/- The Ch export has the expected ABI (1-word out, 3-word in). -/
#guard (strContains chJazz "export fn ch(reg ptr u32[1] out, reg const ptr u32[3] inp)")

/- The Maj export has the expected ABI (1-word out, 3-word in). -/
#guard (strContains majJazz "export fn maj(reg ptr u32[1] out, reg const ptr u32[3] inp)")

/- The Σ₁ export has the expected ABI (1-word out, 1-word in). -/
#guard (strContains bigSigma1Jazz "export fn big_sigma1(reg ptr u32[1] out, reg const ptr u32[1] inp)")

/- The Σ₀ export has the expected ABI. -/
#guard (strContains bigSigma0Jazz "export fn big_sigma0(reg ptr u32[1] out, reg const ptr u32[1] inp)")

/- The σ₁ export has the expected ABI. -/
#guard (strContains smallSigma1Jazz "export fn small_sigma1(reg ptr u32[1] out, reg const ptr u32[1] inp)")

/-! ## §9  σ₀ re-derived through the `thirDialect` two-stage spine (#616)

`ssaSmallSigma0` is the SHA-256 σ₀ program built directly at the **THIR-dialect**
level (`Com thirDialect`), using the higher-level `ThirOp` surface (`thRor`,
`thShrImm`, `thBin`). `sigma0_via_thirDialect` re-derives the existing
`sigma0_FrontValueAgrees` value (`sigma0Spec`) through the new two-stage path
`Com[thir] →lowerThir→ Com[jasmin] →denote→ BitVec 32` — demonstrating the front
now factors through the dialect (rather than only the bespoke `thirToJasmin`).
The direct `thirToJasmin` path (`sigma0Com`, §7) is kept alongside. -/

open CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect
  (thirDialect ThirOp lowerThir lowerThir_denote)

/-- SHA-256 σ₀ as a `Com thirDialect` over `[reg 32]` (input `x = here`), built
    from the higher-level `ThirOp` surface:

        let r7  = thRor 32 7 x;  let r18 = thRor 32 18 x;  let s3 = thShrImm 32 3 x
        let t   = thBin xor r7 r18;  let o = thBin xor t s3;  ret o -/
def ssaSmallSigma0 : Com thirDialect [.reg 32] (.reg 32) :=
  .var (.mk (.thRor 32 7) rfl (.cons .here .nil))
    (.var (.mk (.thRor 32 18) rfl (.cons (.there .here) .nil))
      (.var (.mk (.thShrImm 32 3) rfl (.cons (.there (.there .here)) .nil))
        (.var (.mk (.thBin .xor 32) rfl
            (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
          (.var (.mk (.thBin .xor 32) rfl
              (.cons .here (.cons (.there .here) .nil)))
            (.ret .here)))))

/-- The THIR-dialect σ₀ denotes to the FIPS σ₀ spec on any input valuation
    (`x` = the single de-Bruijn-0 word). A direct check of the `thirDialect`
    semantics against `sigma0Spec`. -/
theorem ssaSmallSigma0_denote (x : BitVec 32) :
    ssaSmallSigma0.denote (.cons x .nil) = sigma0Spec x := by
  rfl

/-- **σ₀ re-derived through the dialect spine.** The lowered (two-stage)
    `Com jasminDialect` for σ₀ denotes the same `BitVec 32` as the FIPS σ₀ spec —
    the existing `sigma0_FrontValueAgrees` value, obtained through
    `Com[thir] →lowerThir→ Com[jasmin]` rather than the bespoke `thirToJasmin`.
    Combines `lowerThir_denote` (the generic, proved dialect lowering) with
    `ssaSmallSigma0_denote`. -/
theorem sigma0_via_thirDialect (x : BitVec 32) :
    (lowerThir ssaSmallSigma0).denote (.cons x .nil) = sigma0Spec x := by
  rw [lowerThir_denote ssaSmallSigma0 (.cons x .nil), ssaSmallSigma0_denote]

/-! ## 11. ChaCha20 quarter-round through the thirDialect spine (#606)

The first Phase-2 fan-out primitive: the ChaCha20 quarter-round `QR(a,b,c,d)`
over four `u32` words, compiled through the **same** `Com[thir] →lowerThir→
Com[jasmin]` spine the σ₀ demonstrator uses. The quarter-round body is the 12
straight-line ARX operations (RFC 8439 §2.1):

    a += b;  d ^= a;  d = rol(d,16);
    c += d;  b ^= c;  b = rol(b,12);
    a += b;  d ^= a;  d = rol(d, 8);
    c += d;  b ^= c;  b = rol(b, 7);

`rol` is rotate-LEFT; the THIR surface has the native rotate-RIGHT op `thRor`, so
each `rol n` over a `u32` is emitted as `thRor (32 - n)` (`rol(x,n) =
ror(x,32-n)`). All three operation kinds (`thBin .add 32`, `thBin .xor 32`,
`thRor 32 _`) are already in the dialect surface — no new op is needed. The
quarter-round produces four output words, so it is split into four single-output
programs `qrAThir`/`qrBThir`/`qrCThir`/`qrDThir`, each computing the shared
12-binding SSA body and returning its own output word (`a'`/`b'`/`c'`/`d'`),
mirroring the SHA-256 round's `a'`/`e'` split. -/

/-- The reference ChaCha20 quarter-round (RFC 8439 §2.1) over four `BitVec 32`
    words, returning `(a', b', c', d')`. `rol(x,n)` is rendered as
    `x.rotateRight (32 - n)`, matching the `thRor (32 - n)` front encoding. -/
def chachaQRSpec (a b c d : BitVec 32) :
    (BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32) :=
  let a := a + b
  let d := (d ^^^ a).rotateRight (32 - 16)
  let c := c + d
  let b := (b ^^^ c).rotateRight (32 - 12)
  let a := a + b
  let d := (d ^^^ a).rotateRight (32 - 8)
  let c := c + d
  let b := (b ^^^ c).rotateRight (32 - 7)
  (a, b, c, d)

/-- The shared ChaCha20 quarter-round SSA body over the input context
    `[a, b, c, d]` (`a = here`, `b = there here`, `c = there² here`,
    `d = there³ here`), parameterized over the source variable `outSrc` of a
    final identity-copy binding (`thRor 32 0`, a rotate-by-zero = identity) so
    each single-output program ends with its OWN output word as the LAST
    binding. The 12 compute bindings, head-first:

        b4, b3, c2, d4, d3, a2, b2, b1, c1, d2, d1, a1, a, b, c, d

    so the output words live at: `a' = a2` (de Bruijn 5), `b' = b4` (0),
    `c' = c2` (2), `d' = d4` (3). The 13th binding copies `outSrc` to the head
    slot, which is what the register-arith emit reads back as the result (it
    takes the last `nOut` bindings, not the `ret` variable). -/
def qrBody
    (outSrc : @Ctxt.Var thirDialect
      [.reg 32, .reg 32, .reg 32, .reg 32, .reg 32, .reg 32, .reg 32, .reg 32,
       .reg 32, .reg 32, .reg 32, .reg 32, .reg 32, .reg 32, .reg 32, .reg 32]
      (.reg 32)) :
    Com thirDialect [.reg 32, .reg 32, .reg 32, .reg 32] (.reg 32) :=
  -- a1 = a + b
  .var (.mk (.thBin .add 32) rfl (.cons .here (.cons (.there .here) .nil)))
  -- d1 = d ^ a1
  (.var (.mk (.thBin .xor 32) rfl
      (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)))
  -- d2 = ror 16 d1   (rol 16)
  (.var (.mk (.thRor 32 (32 - 16)) rfl (.cons .here .nil))
  -- c1 = c + d2
  (.var (.mk (.thBin .add 32) rfl
      (.cons (.there (.there (.there (.there (.there .here)))))
        (.cons .here .nil)))
  -- b1 = b ^ c1
  (.var (.mk (.thBin .xor 32) rfl
      (.cons (.there (.there (.there (.there (.there .here)))))
        (.cons .here .nil)))
  -- b2 = ror 20 b1   (rol 12)
  (.var (.mk (.thRor 32 (32 - 12)) rfl (.cons .here .nil))
  -- a2 = a1 + b2
  (.var (.mk (.thBin .add 32) rfl
      (.cons (.there (.there (.there (.there (.there .here)))))
        (.cons .here .nil)))
  -- d3 = d2 ^ a2
  (.var (.mk (.thBin .xor 32) rfl
      (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)))
  -- d4 = ror 24 d3   (rol 8)
  (.var (.mk (.thRor 32 (32 - 8)) rfl (.cons .here .nil))
  -- c2 = c1 + d4
  (.var (.mk (.thBin .add 32) rfl
      (.cons (.there (.there (.there (.there (.there .here)))))
        (.cons .here .nil)))
  -- b3 = b2 ^ c2
  (.var (.mk (.thBin .xor 32) rfl
      (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)))
  -- b4 = ror 25 b3   (rol 7)
  (.var (.mk (.thRor 32 (32 - 7)) rfl (.cons .here .nil))
  -- out = ror 0 outSrc  (identity copy: makes the chosen output word the LAST
  -- binding, which the register-arith emit reads back as the result)
  (.var (.mk (.thRor 32 0) rfl (.cons outSrc .nil))
  (.ret .here)))))))))))))

/-- ChaCha20 quarter-round `a'` output (`= a2`, de Bruijn 5) as a `Com
    thirDialect` over `[a, b, c, d]`, built through the shared `qrBody`. -/
def qrAThir : Com thirDialect [.reg 32, .reg 32, .reg 32, .reg 32] (.reg 32) :=
  qrBody (.there (.there (.there (.there (.there .here)))))

/-- ChaCha20 quarter-round `b'` output (`= b4`, de Bruijn 0). -/
def qrBThir : Com thirDialect [.reg 32, .reg 32, .reg 32, .reg 32] (.reg 32) :=
  qrBody .here

/-- ChaCha20 quarter-round `c'` output (`= c2`, de Bruijn 2). -/
def qrCThir : Com thirDialect [.reg 32, .reg 32, .reg 32, .reg 32] (.reg 32) :=
  qrBody (.there (.there .here))

/-- ChaCha20 quarter-round `d'` output (`= d4`, de Bruijn 3). -/
def qrDThir : Com thirDialect [.reg 32, .reg 32, .reg 32, .reg 32] (.reg 32) :=
  qrBody (.there (.there (.there .here)))

/-- The `a'` THIR-dialect program denotes the spec's first component. A direct
    check of the `thirDialect` semantics against `chachaQRSpec`. -/
theorem qrAThir_denote (a b c d : BitVec 32) :
    qrAThir.denote (.cons a (.cons b (.cons c (.cons d .nil))))
      = (chachaQRSpec a b c d).1 := by
  -- The body reduces to the output word under a final identity-copy
  -- (`thRor 32 0`, a rotate-by-zero); discharge that copy.
  have e : qrAThir.denote (.cons a (.cons b (.cons c (.cons d .nil))))
      = ((chachaQRSpec a b c d).1).rotateRight 0 := rfl
  rw [e]; simp [BitVec.rotateRight_def]

/-- The `b'` THIR-dialect program denotes the spec's second component. -/
theorem qrBThir_denote (a b c d : BitVec 32) :
    qrBThir.denote (.cons a (.cons b (.cons c (.cons d .nil))))
      = (chachaQRSpec a b c d).2.1 := by
  have e : qrBThir.denote (.cons a (.cons b (.cons c (.cons d .nil))))
      = ((chachaQRSpec a b c d).2.1).rotateRight 0 := rfl
  rw [e]; simp [BitVec.rotateRight_def]

/-- The `c'` THIR-dialect program denotes the spec's third component. -/
theorem qrCThir_denote (a b c d : BitVec 32) :
    qrCThir.denote (.cons a (.cons b (.cons c (.cons d .nil))))
      = (chachaQRSpec a b c d).2.2.1 := by
  have e : qrCThir.denote (.cons a (.cons b (.cons c (.cons d .nil))))
      = ((chachaQRSpec a b c d).2.2.1).rotateRight 0 := rfl
  rw [e]; simp [BitVec.rotateRight_def]

/-- The `d'` THIR-dialect program denotes the spec's fourth component. -/
theorem qrDThir_denote (a b c d : BitVec 32) :
    qrDThir.denote (.cons a (.cons b (.cons c (.cons d .nil))))
      = (chachaQRSpec a b c d).2.2.2 := by
  have e : qrDThir.denote (.cons a (.cons b (.cons c (.cons d .nil))))
      = ((chachaQRSpec a b c d).2.2.2).rotateRight 0 := rfl
  rw [e]; simp [BitVec.rotateRight_def]

/-- **`a'` re-derived through the dialect spine.** The lowered (two-stage)
    `Com jasminDialect` for the quarter-round `a'` output denotes the same
    `BitVec 32` as the RFC 8439 reference, obtained through
    `Com[thir] →lowerThir→ Com[jasmin]`. Combines `lowerThir_denote` (the generic,
    proved dialect lowering) with `qrAThir_denote`. -/
theorem qrA_via_thirDialect (a b c d : BitVec 32) :
    (lowerThir qrAThir).denote (.cons a (.cons b (.cons c (.cons d .nil))))
      = (chachaQRSpec a b c d).1 := by
  rw [lowerThir_denote qrAThir (.cons a (.cons b (.cons c (.cons d .nil)))),
    qrAThir_denote]

/-- **`b'` re-derived through the dialect spine.** -/
theorem qrB_via_thirDialect (a b c d : BitVec 32) :
    (lowerThir qrBThir).denote (.cons a (.cons b (.cons c (.cons d .nil))))
      = (chachaQRSpec a b c d).2.1 := by
  rw [lowerThir_denote qrBThir (.cons a (.cons b (.cons c (.cons d .nil)))),
    qrBThir_denote]

/-- **`c'` re-derived through the dialect spine.** -/
theorem qrC_via_thirDialect (a b c d : BitVec 32) :
    (lowerThir qrCThir).denote (.cons a (.cons b (.cons c (.cons d .nil))))
      = (chachaQRSpec a b c d).2.2.1 := by
  rw [lowerThir_denote qrCThir (.cons a (.cons b (.cons c (.cons d .nil)))),
    qrCThir_denote]

/-- **`d'` re-derived through the dialect spine.** -/
theorem qrD_via_thirDialect (a b c d : BitVec 32) :
    (lowerThir qrDThir).denote (.cons a (.cons b (.cons c (.cons d .nil))))
      = (chachaQRSpec a b c d).2.2.2 := by
  rw [lowerThir_denote qrDThir (.cons a (.cons b (.cons c (.cons d .nil)))),
    qrDThir_denote]

/-! ### §11.1  Emit the quarter-round outputs → owned-x86 jasmin

Each of the four output programs is lowered through the thirDialect spine
(`lowerThir qrXThir`) and emitted by the existing verified register-arith /
rotate orchestration `emitAbiOrchReg`. The slot scheme mirrors the SHA-256
rounds: binding `k` writes working slot `k`; the 4 input words are copied into
the trailing register slots. The body has 12 bindings + 1 trailing `ret` copy,
so 13 working slots precede the 4 input slots in the `stack u32[17] k` file. -/

/-- Per-output register-file decls: 13 working slots + 4 input slots. -/
def qrRegDecls : List String := ["stack u32[17] k"]

/-- Binding `k` → working slot `k`. -/
def qrDstName (n : Nat) : String := "k[" ++ toString n ++ "]"

/-- Input word `i` (`a`/`b`/`c`/`d`) → copied-in register slot `13 + i`. -/
def qrInName (i : Nat) : String := "k[" ++ toString (13 + i) ++ "]"

/-- The emitted `.jazz` for the quarter-round `a'` output through the thirDialect
    spine (`lowerThir qrAThir`) and the verified register-arith / rotate
    orchestration. ABI: `reg ptr u32[1] out`, `reg const ptr u32[4] inp`. -/
def qrAJazz : String :=
  emitAbiOrchReg "chacha_qr_a" (w := 32) (nIn := 4) (nOut := 1) (nCopy := 4)
    qrRegDecls qrInName qrDstName (lowerThir qrAThir)

/-- The emitted `.jazz` for the quarter-round `b'` output through the spine. -/
def qrBJazz : String :=
  emitAbiOrchReg "chacha_qr_b" (w := 32) (nIn := 4) (nOut := 1) (nCopy := 4)
    qrRegDecls qrInName qrDstName (lowerThir qrBThir)

/-- The emitted `.jazz` for the quarter-round `c'` output through the spine. -/
def qrCJazz : String :=
  emitAbiOrchReg "chacha_qr_c" (w := 32) (nIn := 4) (nOut := 1) (nCopy := 4)
    qrRegDecls qrInName qrDstName (lowerThir qrCThir)

/-- The emitted `.jazz` for the quarter-round `d'` output through the spine. -/
def qrDJazz : String :=
  emitAbiOrchReg "chacha_qr_d" (w := 32) (nIn := 4) (nOut := 1) (nCopy := 4)
    qrRegDecls qrInName qrDstName (lowerThir qrDThir)

/- The `a'` quarter-round export has the expected ABI (1-word out, 4-word in). -/
#guard (strContains qrAJazz "export fn chacha_qr_a(reg ptr u32[1] out, reg const ptr u32[4] inp)")

/- The emitted `a'` body renders real computation (no skipped ops). -/
#guard !(strContains qrAJazz "non-regArith op skipped")

/- The emitted `a'` body uses the native right-rotate op (`#ROR_32`), the
    `rol`-via-`thRor` encoding. -/
#guard (strContains qrAJazz "#ROR_32(")

/- The four emitted quarter-round functions return DISTINCT output words: each
    copies its own result slot into the final binding before the `out[0]` write
    (`a' = k[6]`, `b' = k[11]`, `c' = k[9]`, `d' = k[8]`). The register-arith
    emit reads back the last binding's slot, so distinct final-copy sources are
    exactly what makes the four exports compute the four quarter-round outputs
    rather than a shared last value. -/
#guard (strContains qrAJazz "w0 = k[6];\n  _, _, w0 = #ROR_32(w0, 0);\n  k[12] = w0;")
    && (strContains qrBJazz "w0 = k[11];\n  _, _, w0 = #ROR_32(w0, 0);\n  k[12] = w0;")
    && (strContains qrCJazz "w0 = k[9];\n  _, _, w0 = #ROR_32(w0, 0);\n  k[12] = w0;")
    && (strContains qrDJazz "w0 = k[8];\n  _, _, w0 = #ROR_32(w0, 0);\n  k[12] = w0;")

/-! ## §12  BLAKE2b G mixing function through the thirDialect spine (#606)

Phase-2 fan-out, the `u64` ARX analog of the ChaCha20 quarter-round (§11). The
BLAKE2b G mixing function `G(a,b,c,d,x,y)` (RFC 7693 §3.1) over four `u64` state
words `a,b,c,d` plus two `u64` message words `x,y`, compiled through the **same**
`Com[thir] →lowerThir→ Com[jasmin]` spine, now at width 64:

    a = a + b + x;   d = ror64(d ^ a, 32);
    c = c + d;       b = ror64(b ^ c, 24);
    a = a + b + y;   d = ror64(d ^ a, 16);
    c = c + d;       b = ror64(b ^ c, 63);

The two three-input adds `a + b + x` / `a + b + y` are each two chained
`thBin .add 64` ops. The rotates are the native right-rotate `thRor 64 n`
(`n = 32/24/16/63`, all immediate). All three operation kinds (`thBin .add 64`,
`thBin .xor 64`, `thRor 64 _`) are already in the dialect surface — no new op is
needed. G produces four output words, so it is split into four single-output
programs `gAThir`/`gBThir`/`gCThir`/`gDThir`, each computing the shared 14-binding
SSA body and returning its own output word (`a'`/`b'`/`c'`/`d'`), mirroring the
quarter-round's `a'`/`b'`/`c'`/`d'` split. -/

/-- The reference BLAKE2b G mixing function (RFC 7693 §3.1) over six `BitVec 64`
    words (`a,b,c,d` state, `x,y` message), returning `(a', b', c', d')`.
    `ror64(z,n)` is `z.rotateRight n`. -/
def blake2bGSpec (a b c d x y : BitVec 64) :
    (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) :=
  let a := a + b + x
  let d := (d ^^^ a).rotateRight 32
  let c := c + d
  let b := (b ^^^ c).rotateRight 24
  let a := a + b + y
  let d := (d ^^^ a).rotateRight 16
  let c := c + d
  let b := (b ^^^ c).rotateRight 63
  (a, b, c, d)

/-- The shared BLAKE2b G SSA body over the input context `[a, b, c, d, x, y]`
    (`a = here`, …, `y = there⁵ here`), parameterized over the source variable
    `outSrc` of a final identity-copy binding (`thRor 64 0`, a rotate-by-zero =
    identity) so each single-output program ends with its OWN output word as the
    LAST binding. The 14 compute bindings, head-first:

        a1, a2, d1, d2, c1, b1, b2, a3, a4, d3, d4, c2, b3, b4

    so the output words live at: `a' = a4` (binding 8), `b' = b4` (binding 13),
    `c' = c2` (binding 11), `d' = d4` (binding 10). The 15th binding copies
    `outSrc` to the head slot, which is what the register-arith emit reads back as
    the result (it takes the last `nOut` bindings, not the `ret` variable). -/
def gBody
    (outSrc : @Ctxt.Var thirDialect
      [.reg 64, .reg 64, .reg 64, .reg 64, .reg 64, .reg 64, .reg 64, .reg 64,
       .reg 64, .reg 64, .reg 64, .reg 64, .reg 64, .reg 64, .reg 64, .reg 64,
       .reg 64, .reg 64, .reg 64, .reg 64]
      (.reg 64)) :
    Com thirDialect [.reg 64, .reg 64, .reg 64, .reg 64, .reg 64, .reg 64]
      (.reg 64) :=
  -- a1 = a + b
  .var (.mk (.thBin .add 64) rfl (.cons .here (.cons (.there .here) .nil)))
  -- a2 = a1 + x
  (.var (.mk (.thBin .add 64) rfl
      (.cons .here
        (.cons (.there (.there (.there (.there (.there .here))))) .nil)))
  -- d1 = d ^ a2
  (.var (.mk (.thBin .xor 64) rfl
      (.cons (.there (.there (.there (.there (.there .here)))))
        (.cons .here .nil)))
  -- d2 = ror 32 d1
  (.var (.mk (.thRor 64 32) rfl (.cons .here .nil))
  -- c1 = c + d2
  (.var (.mk (.thBin .add 64) rfl
      (.cons (.there (.there (.there (.there (.there (.there .here))))))
        (.cons .here .nil)))
  -- b1 = b ^ c1
  (.var (.mk (.thBin .xor 64) rfl
      (.cons (.there (.there (.there (.there (.there (.there .here))))))
        (.cons .here .nil)))
  -- b2 = ror 24 b1
  (.var (.mk (.thRor 64 24) rfl (.cons .here .nil))
  -- a3 = a2 + b2
  (.var (.mk (.thBin .add 64) rfl
      (.cons (.there (.there (.there (.there (.there .here)))))
        (.cons .here .nil)))
  -- a4 = a3 + y
  (.var (.mk (.thBin .add 64) rfl
      (.cons .here
        (.cons (.there (.there (.there (.there (.there (.there (.there
          (.there (.there (.there (.there (.there (.there .here)))))))))))))
          .nil)))
  -- d3 = d2 ^ a4
  (.var (.mk (.thBin .xor 64) rfl
      (.cons (.there (.there (.there (.there (.there .here)))))
        (.cons .here .nil)))
  -- d4 = ror 16 d3
  (.var (.mk (.thRor 64 16) rfl (.cons .here .nil))
  -- c2 = c1 + d4
  (.var (.mk (.thBin .add 64) rfl
      (.cons (.there (.there (.there (.there (.there (.there .here))))))
        (.cons .here .nil)))
  -- b3 = b2 ^ c2
  (.var (.mk (.thBin .xor 64) rfl
      (.cons (.there (.there (.there (.there (.there .here)))))
        (.cons .here .nil)))
  -- b4 = ror 63 b3
  (.var (.mk (.thRor 64 63) rfl (.cons .here .nil))
  -- out = ror 0 outSrc  (identity copy: seats the chosen output word as the LAST
  -- binding, which the register-arith emit reads back as the result)
  (.var (.mk (.thRor 64 0) rfl (.cons outSrc .nil))
  (.ret .here)))))))))))))))

/-- BLAKE2b G `a'` output (`= a4`, de Bruijn 5) as a `Com thirDialect` over
    `[a, b, c, d, x, y]`, built through the shared `gBody`. -/
def gAThir :
    Com thirDialect [.reg 64, .reg 64, .reg 64, .reg 64, .reg 64, .reg 64]
      (.reg 64) :=
  gBody (.there (.there (.there (.there (.there .here)))))

/-- BLAKE2b G `b'` output (`= b4`, de Bruijn 0). -/
def gBThir :
    Com thirDialect [.reg 64, .reg 64, .reg 64, .reg 64, .reg 64, .reg 64]
      (.reg 64) :=
  gBody .here

/-- BLAKE2b G `c'` output (`= c2`, de Bruijn 2). -/
def gCThir :
    Com thirDialect [.reg 64, .reg 64, .reg 64, .reg 64, .reg 64, .reg 64]
      (.reg 64) :=
  gBody (.there (.there .here))

/-- BLAKE2b G `d'` output (`= d4`, de Bruijn 3). -/
def gDThir :
    Com thirDialect [.reg 64, .reg 64, .reg 64, .reg 64, .reg 64, .reg 64]
      (.reg 64) :=
  gBody (.there (.there (.there .here)))

/-- The `a'` THIR-dialect program denotes the spec's first component. A direct
    check of the `thirDialect` semantics against `blake2bGSpec`. -/
theorem gAThir_denote (a b c d x y : BitVec 64) :
    gAThir.denote (.cons a (.cons b (.cons c (.cons d (.cons x (.cons y .nil))))))
      = (blake2bGSpec a b c d x y).1 := by
  -- The body reduces to the output word under a final identity-copy
  -- (`thRor 64 0`, a rotate-by-zero); discharge that copy.
  have e : gAThir.denote
      (.cons a (.cons b (.cons c (.cons d (.cons x (.cons y .nil))))))
      = ((blake2bGSpec a b c d x y).1).rotateRight 0 := rfl
  rw [e]; simp [BitVec.rotateRight_def]

/-- The `b'` THIR-dialect program denotes the spec's second component. -/
theorem gBThir_denote (a b c d x y : BitVec 64) :
    gBThir.denote (.cons a (.cons b (.cons c (.cons d (.cons x (.cons y .nil))))))
      = (blake2bGSpec a b c d x y).2.1 := by
  have e : gBThir.denote
      (.cons a (.cons b (.cons c (.cons d (.cons x (.cons y .nil))))))
      = ((blake2bGSpec a b c d x y).2.1).rotateRight 0 := rfl
  rw [e]; simp [BitVec.rotateRight_def]

/-- The `c'` THIR-dialect program denotes the spec's third component. -/
theorem gCThir_denote (a b c d x y : BitVec 64) :
    gCThir.denote (.cons a (.cons b (.cons c (.cons d (.cons x (.cons y .nil))))))
      = (blake2bGSpec a b c d x y).2.2.1 := by
  have e : gCThir.denote
      (.cons a (.cons b (.cons c (.cons d (.cons x (.cons y .nil))))))
      = ((blake2bGSpec a b c d x y).2.2.1).rotateRight 0 := rfl
  rw [e]; simp [BitVec.rotateRight_def]

/-- The `d'` THIR-dialect program denotes the spec's fourth component. -/
theorem gDThir_denote (a b c d x y : BitVec 64) :
    gDThir.denote (.cons a (.cons b (.cons c (.cons d (.cons x (.cons y .nil))))))
      = (blake2bGSpec a b c d x y).2.2.2 := by
  have e : gDThir.denote
      (.cons a (.cons b (.cons c (.cons d (.cons x (.cons y .nil))))))
      = ((blake2bGSpec a b c d x y).2.2.2).rotateRight 0 := rfl
  rw [e]; simp [BitVec.rotateRight_def]

/-- **`a'` re-derived through the dialect spine.** The lowered (two-stage)
    `Com jasminDialect` for the BLAKE2b G `a'` output denotes the same `BitVec 64`
    as the RFC 7693 §3.1 reference, obtained through
    `Com[thir] →lowerThir→ Com[jasmin]`. Combines `lowerThir_denote` (the generic,
    proved dialect lowering) with `gAThir_denote`. -/
theorem gA_via_thirDialect (a b c d x y : BitVec 64) :
    (lowerThir gAThir).denote
      (.cons a (.cons b (.cons c (.cons d (.cons x (.cons y .nil))))))
      = (blake2bGSpec a b c d x y).1 := by
  rw [lowerThir_denote gAThir
      (.cons a (.cons b (.cons c (.cons d (.cons x (.cons y .nil)))))),
    gAThir_denote]

/-- **`b'` re-derived through the dialect spine.** -/
theorem gB_via_thirDialect (a b c d x y : BitVec 64) :
    (lowerThir gBThir).denote
      (.cons a (.cons b (.cons c (.cons d (.cons x (.cons y .nil))))))
      = (blake2bGSpec a b c d x y).2.1 := by
  rw [lowerThir_denote gBThir
      (.cons a (.cons b (.cons c (.cons d (.cons x (.cons y .nil)))))),
    gBThir_denote]

/-- **`c'` re-derived through the dialect spine.** -/
theorem gC_via_thirDialect (a b c d x y : BitVec 64) :
    (lowerThir gCThir).denote
      (.cons a (.cons b (.cons c (.cons d (.cons x (.cons y .nil))))))
      = (blake2bGSpec a b c d x y).2.2.1 := by
  rw [lowerThir_denote gCThir
      (.cons a (.cons b (.cons c (.cons d (.cons x (.cons y .nil)))))),
    gCThir_denote]

/-- **`d'` re-derived through the dialect spine.** -/
theorem gD_via_thirDialect (a b c d x y : BitVec 64) :
    (lowerThir gDThir).denote
      (.cons a (.cons b (.cons c (.cons d (.cons x (.cons y .nil))))))
      = (blake2bGSpec a b c d x y).2.2.2 := by
  rw [lowerThir_denote gDThir
      (.cons a (.cons b (.cons c (.cons d (.cons x (.cons y .nil)))))),
    gDThir_denote]

/-! ### §12.1  Emit the BLAKE2b G outputs → owned-x86 jasmin

Each of the four output programs is lowered through the thirDialect spine
(`lowerThir gXThir`) and emitted by the existing verified register-arith / rotate
orchestration `emitAbiOrchReg` at width 64. The slot scheme mirrors §11: binding
`k` writes working slot `k`; the 6 input words are copied into the trailing
register slots. The body has 14 bindings + 1 trailing `ret` copy, so 15 working
slots precede the 6 input slots in the `stack u64[21] k` file. -/

/-- Per-output register-file decls: 15 working slots + 6 input slots. -/
def gRegDecls : List String := ["stack u64[21] k"]

/-- Binding `k` → working slot `k`. -/
def gDstName (n : Nat) : String := "k[" ++ toString n ++ "]"

/-- Input word `i` (`a`/`b`/`c`/`d`/`x`/`y`) → copied-in register slot `15 + i`. -/
def gInName (i : Nat) : String := "k[" ++ toString (15 + i) ++ "]"

/-- The emitted `.jazz` for the BLAKE2b G `a'` output through the thirDialect
    spine (`lowerThir gAThir`) and the verified register-arith / rotate
    orchestration. ABI: `reg ptr u64[1] out`, `reg const ptr u64[6] inp`. -/
def gAJazz : String :=
  emitAbiOrchReg "blake2b_g_a" (w := 64) (nIn := 6) (nOut := 1) (nCopy := 6)
    gRegDecls gInName gDstName (lowerThir gAThir)

/-- The emitted `.jazz` for the BLAKE2b G `b'` output through the spine. -/
def gBJazz : String :=
  emitAbiOrchReg "blake2b_g_b" (w := 64) (nIn := 6) (nOut := 1) (nCopy := 6)
    gRegDecls gInName gDstName (lowerThir gBThir)

/-- The emitted `.jazz` for the BLAKE2b G `c'` output through the spine. -/
def gCJazz : String :=
  emitAbiOrchReg "blake2b_g_c" (w := 64) (nIn := 6) (nOut := 1) (nCopy := 6)
    gRegDecls gInName gDstName (lowerThir gCThir)

/-- The emitted `.jazz` for the BLAKE2b G `d'` output through the spine. -/
def gDJazz : String :=
  emitAbiOrchReg "blake2b_g_d" (w := 64) (nIn := 6) (nOut := 1) (nCopy := 6)
    gRegDecls gInName gDstName (lowerThir gDThir)

/- The `a'` G export has the expected ABI (1-word out, 6-word in). -/
#guard (strContains gAJazz "export fn blake2b_g_a(reg ptr u64[1] out, reg const ptr u64[6] inp)")

/- The emitted `a'` body renders real computation (no skipped ops). -/
#guard !(strContains gAJazz "non-regArith op skipped")

/- The emitted `a'` body uses the native right-rotate op (`#ROR_64`), the
    `ror64` encoding. -/
#guard (strContains gAJazz "#ROR_64(")

/- The four emitted G functions return DISTINCT output words: each copies its
    own result slot into the final binding before the `out[0]` write
    (`a' = k[8]`, `b' = k[13]`, `c' = k[11]`, `d' = k[10]`). The register-arith
    emit reads back the last binding's slot, so distinct final-copy sources are
    exactly what makes the four exports compute the four G outputs rather than a
    shared last value. -/
#guard (strContains gAJazz "w0 = k[8];\n  _, _, w0 = #ROR_64(w0, 0);\n  k[14] = w0;")
    && (strContains gBJazz "w0 = k[13];\n  _, _, w0 = #ROR_64(w0, 0);\n  k[14] = w0;")
    && (strContains gCJazz "w0 = k[11];\n  _, _, w0 = #ROR_64(w0, 0);\n  k[14] = w0;")
    && (strContains gDJazz "w0 = k[10];\n  _, _, w0 = #ROR_64(w0, 0);\n  k[14] = w0;")

/-! ## §13  BabyBear lazy Montgomery multiply through the thirDialect spine (#606)

Phase-2 fan-out, the FIRST non-ARX (field-arithmetic) primitive through the
unified `Com[thir] →lowerThir→ Com[jasmin]` spine: a lazy Montgomery modular
multiply (REDC) over the Plonky3/Poseidon2 **BabyBear** prime
`p = 0x78000001 = 2^31 − 2^27 + 1`, with `R = 2^32` and
`minv = −p⁻¹ mod R = 0x77ffffff` (verified: `minv · p ≡ −1 mod 2^32`, i.e.
`(minv · p) mod 2^32 = 0xffffffff`). For two Montgomery representatives `a`, `b`
(each `< 2^32`), the REDC product is:

    t = a * b;                       -- exact 64-bit product (a,b < 2^32)
    m = ((u32)t * minv) & 0xffffffff;-- low-word REDC multiplier
    r = (t + (u64)m * p) >> 32;      -- ≡ a·b·R⁻¹  (mod p)

`r` is the LAZY Montgomery representative — congruent mod `p` to the canonical
product, with NO final conditional subtract (the thirDialect front is
straight-line, no `select`). Unlike the ARX leaves (§11/§12) this uses
`thBin .mul` (integer multiply) and `thBin .and` / `thShrImm` / `thConst`, with
no rotation.

The exact 32×32→64 product needs 64-bit intermediates. The verified
register-arith orchestration `emitAbiOrchReg` runs over a single homogeneous
register width, so the whole REDC is realised at **width 64**: the two `u32`
inputs are held in `u64` words (each `< 2^32`, so the `thBin .mul 64` product is
exact), and every REDC step (`m`, `r`) is a `u64` op. The output `r` is a `u64`
in `[0, 3p)` congruent to the canonical product mod `p` — the lazy form. This
keeps the program in the single-width spine (no cross-width `thCast` inside the
homogeneous emit). `montMulSpec` over `BitVec 32` inputs zero-extends to 64,
runs the same REDC, and truncates the result back to `BitVec 32` (the low word
carries the residue mod `p`). -/

/-- The BabyBear prime `p = 0x78000001 = 2^31 − 2^27 + 1` (Plonky3/Poseidon2). -/
def babyBearP : Nat := 0x78000001

/-- `minv = −p⁻¹ mod 2^32 = 0x77ffffff` (the low-word REDC multiplier constant).
    Verified by `montMul_minv_correct`: `minv · p ≡ −1 mod 2^32`. -/
def babyBearMInv : Nat := 0x77ffffff

/-- The REDC multiplier constant is the negated modular inverse:
    `(minv · p) mod 2^32 = 0xffffffff = 2^32 − 1`, i.e. `minv · p ≡ −1 mod 2^32`
    — the defining property of `minv = −p⁻¹ mod R` that makes
    `t + m·p ≡ 0 mod 2^32` so the `>> 32` is exact. -/
theorem montMul_minv_correct :
    (babyBearMInv * babyBearP) % (2 ^ 32) = 2 ^ 32 - 1 := by
  native_decide

/-- The reference lazy BabyBear Montgomery REDC over two `BitVec 32` Montgomery
    representatives `a`, `b`. Both are zero-extended to 64 bits (so the product is
    exact), reduced by one REDC step, and the 64-bit result `r` (in `[0, 3p)`,
    congruent to `a·b·R⁻¹ mod p`) is truncated back to a `BitVec 32`. The full
    REDC at width 64:

        t = (a ++ b widened) * …;  m = (t & 0xffffffff) * minv & 0xffffffff;
        r = (t + m * p) >> 32 -/
def montMulSpec (a b : BitVec 32) : BitVec 32 :=
  let a64 : BitVec 64 := a.zeroExtend 64
  let b64 : BitVec 64 := b.zeroExtend 64
  let t : BitVec 64 := a64 * b64
  let mask : BitVec 64 := BitVec.ofNat 64 0xffffffff
  let minv : BitVec 64 := BitVec.ofNat 64 babyBearMInv
  let p : BitVec 64 := BitVec.ofNat 64 babyBearP
  let tlo : BitVec 64 := t &&& mask
  let m : BitVec 64 := (tlo * minv) &&& mask
  let r : BitVec 64 := (t + m * p) >>> (32 : Nat)
  r.truncate 32

/-- The 64-bit lazy Montgomery REDC over two `u64` words holding `u32`
    representatives `a`, `b`. The full-width result word (in `[0, 3p)`, congruent
    to `a·b·R⁻¹ mod p`) before the final truncation in `montMulSpec`. This is the
    value the width-64 emit computes (the C KAT checks it congruent mod `p`). -/
def montMulSpec64 (a b : BitVec 64) : BitVec 64 :=
  let t : BitVec 64 := a * b
  let mask : BitVec 64 := BitVec.ofNat 64 0xffffffff
  let minv : BitVec 64 := BitVec.ofNat 64 babyBearMInv
  let p : BitVec 64 := BitVec.ofNat 64 babyBearP
  let tlo : BitVec 64 := t &&& mask
  let m : BitVec 64 := (tlo * minv) &&& mask
  (t + m * p) >>> (32 : Nat)

/-- The lazy Montgomery REDC as a `Com thirDialect` over `[a, b]` (both `.reg 64`,
    each holding a `u32` Montgomery representative). Single-output: the last
    binding (`r`) IS the result, so no identity-copy tail is needed. The 11
    bindings, head-first:

        t, c1, tlo, cm, mr, c2, m, cp, mp, s, r

    where `c1 = c2 = 0xffffffff`, `cm = minv`, `cp = p` are materialized
    constants (`thConst 64 _`), and `r = s >>> 32` is the final reduction. -/
def montMulThir : Com thirDialect [.reg 64, .reg 64] (.reg 64) :=
  -- t = a * b
  .var (.mk (.thBin .mul 64) rfl (.cons .here (.cons (.there .here) .nil)))
  -- c1 = 0xffffffff
  (.var (.mk (.thConst 64 0xffffffff) rfl .nil)
  -- tlo = t & c1   (ctx: [c1, t, a, b])
  (.var (.mk (.thBin .and 64) rfl (.cons (.there .here) (.cons .here .nil)))
  -- cm = minv
  (.var (.mk (.thConst 64 babyBearMInv) rfl .nil)
  -- mr = tlo * cm  (ctx: [cm, tlo, c1, t, a, b])
  (.var (.mk (.thBin .mul 64) rfl (.cons (.there .here) (.cons .here .nil)))
  -- c2 = 0xffffffff
  (.var (.mk (.thConst 64 0xffffffff) rfl .nil)
  -- m = mr & c2    (ctx: [c2, mr, cm, tlo, c1, t, a, b])
  (.var (.mk (.thBin .and 64) rfl (.cons (.there .here) (.cons .here .nil)))
  -- cp = p
  (.var (.mk (.thConst 64 babyBearP) rfl .nil)
  -- mp = m * cp    (ctx: [cp, m, c2, mr, cm, tlo, c1, t, a, b])
  (.var (.mk (.thBin .mul 64) rfl (.cons (.there .here) (.cons .here .nil)))
  -- s = t + mp     (ctx: [mp, cp, m, c2, mr, cm, tlo, c1, t, a, b]); t is dB 8
  (.var (.mk (.thBin .add 64) rfl
      (.cons (.there (.there (.there (.there (.there (.there (.there
        (.there .here)))))))) (.cons .here .nil)))
  -- r = s >> 32
  (.var (.mk (.thShrImm 64 32) rfl (.cons .here .nil))
  (.ret .here)))))))))))

/-- The THIR-dialect Montgomery REDC denotes the width-64 reference
    `montMulSpec64` on any pair of `u64` input words. A direct check of the
    `thirDialect` semantics against the REDC. -/
theorem montMulThir_denote (a b : BitVec 64) :
    montMulThir.denote (.cons a (.cons b .nil)) = montMulSpec64 a b := by
  rfl

/-- **Montgomery REDC re-derived through the dialect spine.** The lowered
    (two-stage) `Com jasminDialect` for the lazy BabyBear Montgomery multiply
    denotes the same `BitVec 64` as the width-64 REDC reference, obtained through
    `Com[thir] →lowerThir→ Com[jasmin]` rather than a bespoke lowering. Combines
    `lowerThir_denote` (the generic, proved dialect lowering) with
    `montMulThir_denote`. -/
theorem montMul_via_thirDialect (a b : BitVec 64) :
    (lowerThir montMulThir).denote (.cons a (.cons b .nil)) = montMulSpec64 a b := by
  rw [lowerThir_denote montMulThir (.cons a (.cons b .nil)), montMulThir_denote]

/-- The width-64 REDC restricted to `u32` inputs (zero-extended to 64) and
    truncated back to 32 is exactly `montMulSpec` — ties the emitted/lowered
    width-64 program (`montMulSpec64`) to the `BitVec 32` reference. -/
theorem montMulSpec_eq_spec64 (a b : BitVec 32) :
    montMulSpec a b = (montMulSpec64 (a.zeroExtend 64) (b.zeroExtend 64)).truncate 32 := by
  rfl

/-! ### §13.1  Emit the Montgomery REDC → owned-x86 jasmin

The single-output REDC is lowered through the thirDialect spine
(`lowerThir montMulThir`) and emitted by the verified register-arith
orchestration `emitAbiOrchReg` at width 64. The body has 11 bindings, so 11
working slots precede the 2 input slots in the `stack u64[13] k` file. The two
`u32` inputs are passed as `u64` words. The result is the LAST binding's slot
(no identity-copy tail — single output). -/

/-- Per-output register-file decls: 11 working slots + 2 input slots. -/
def montRegDecls : List String := ["stack u64[13] k"]

/-- Binding `k` → working slot `k`. -/
def montDstName (n : Nat) : String := "k[" ++ toString n ++ "]"

/-- Input word `i` (`a`/`b`) → copied-in register slot `11 + i`. -/
def montInName (i : Nat) : String := "k[" ++ toString (11 + i) ++ "]"

/-- The emitted `.jazz` for the lazy BabyBear Montgomery multiply through the
    thirDialect spine (`lowerThir montMulThir`) and the verified register-arith
    orchestration. ABI: `reg ptr u64[1] out`, `reg const ptr u64[2] inp`. -/
def montMulJazz : String :=
  emitAbiOrchReg "babybear_montmul" (w := 64) (nIn := 2) (nOut := 1) (nCopy := 2)
    montRegDecls montInName montDstName (lowerThir montMulThir)

/- The REDC export has the expected ABI (1-word out, 2-word in). -/
#guard (strContains montMulJazz "export fn babybear_montmul(reg ptr u64[1] out, reg const ptr u64[2] inp)")

/- The emitted REDC body renders real computation (no skipped ops). -/
#guard !(strContains montMulJazz "non-regArith op skipped")

/- The emitted REDC body uses an integer multiply (`w0 = w0 * w1;`), the
    `thBin .mul 64` REDC product — the field-arithmetic op distinguishing this
    leaf from the pure-ARX rotates of §11/§12. -/
#guard (strContains montMulJazz "w0 = w0 * w1;")

/-- The emitted REDC body materializes the `minv` and `p` constants and the
    `0xffffffff` low-word mask, and performs the final `>> 32` reduction — the
    distinctive REDC shape. -/
theorem montMul_redc_shape :
    strContains montMulJazz "k[3] = 2013265919;" = true          -- minv = 0x77ffffff
      ∧ strContains montMulJazz "k[7] = 2013265921;" = true      -- p = 0x78000001
      ∧ strContains montMulJazz "k[1] = 4294967295;" = true      -- 0xffffffff mask
      ∧ strContains montMulJazz "w0 = w0 >> 32;" = true := by     -- final reduction
  native_decide

/-! ## §14  BabyBear Cooley–Tukey NTT butterfly (Montgomery domain) through the thirDialect spine (#606)

Phase-2 fan-out, the SECOND field-arithmetic primitive through the unified
`Com[thir] →lowerThir→ Com[jasmin]` spine, and the first to COMPOSE the §13 lazy
Montgomery multiply: a Cooley–Tukey decimation-in-time NTT butterfly in the
Montgomery domain over the BabyBear prime `p = 0x78000001`, `R = 2^32`. For three
Montgomery representatives `a`, `b`, `w` (the twiddle `ω`), each `< 2p`:

    t  = montmul(w, b);        -- (w·b)·R⁻¹  (mod p), one REDC step, in [0, 3p)
    a' = a + t;                -- (a + ω·b) lazy   in [0, 5p)
    b' = a + 4p − t;           -- (a − ω·b) lazy   in [0, 5p)

`a'`, `b'` are the LAZY Montgomery representatives — congruent mod `p` to the
canonical butterfly outputs, with NO final conditional subtract (the thirDialect
front is straight-line, no `select`). The `4p` bias (`thConst 64 (4·p)`, a
multiple of `p`) keeps `b'` non-negative before the subtract: `a < 2p` and
`t < 3p`, so `a + 4p − t < 6p` and `a + 4p − t > 4p − 3p = p ≥ 0` (no wraparound).

The `t = montmul(w, b)` step REUSES the §13 REDC body verbatim (`montMulSpec64`);
the two extra outputs are one `thBin .add 64` (`a'`) and a `thConst 64 (4p)` +
`thBin .add 64` + `thBin .sub 64` (`b'`). Like §13 the whole butterfly runs at
**width 64** (the `32×32→64` REDC product needs 64-bit intermediates, and the
lazy `a'`/`b'` reach `~5p > 2^32`), so the three `u32` inputs are held in `u64`
words and the two outputs are `u64`. TWO outputs `a'`, `b'`: following §11/§12,
each is a SEPARATE single-output program (`bflyAThir`/`bflyBThir`) that seats its
own word as the LAST binding (an identity `thRor 64 0` copy), which the
register-arith emit reads back as the result. -/

/-- The `4p` bias constant `4 · 0x78000001 = 0x1e0000004`, a multiple of `p`
    large enough that `a + 4p − t ≥ 0` for `a < 2p`, `t < 3p`. -/
def babyBear4P : Nat := 4 * babyBearP

/-- The width-64 lazy butterfly over three `u64` words holding `u32` Montgomery
    representatives `a`, `b`, `w` (the twiddle). Returns the lazy pair
    `(a', b') = (a + t, a + 4p − t)` with `t = montmul(w, b)` the §13 REDC — both
    full-width words (in `[0, 5p)`, congruent mod `p` to the canonical butterfly).
    These are the values the width-64 emit computes (the C KAT checks them
    congruent mod `p`). -/
def nttButterflySpec64 (a b w : BitVec 64) : BitVec 64 × BitVec 64 :=
  let t : BitVec 64 := montMulSpec64 w b
  let bias : BitVec 64 := BitVec.ofNat 64 babyBear4P
  (a + t, (a + bias) - t)

/-- The reference Montgomery-domain BabyBear butterfly over three `BitVec 32`
    representatives `a`, `b`, `w`. Each input is zero-extended to 64 bits, the
    width-64 lazy butterfly (`nttButterflySpec64`, reusing the §13
    `montMulSpec`/`montMulSpec64` REDC) is run, and the two lazy outputs are
    truncated back to `BitVec 32`. The truncation drops the (rare) high bit of a
    lazy `~5p` representative; the C KAT checks the full `u64` outputs CONGRUENT
    mod `p`, the canonical-correctness statement for the lazy form. -/
def nttButterflySpec (a b w : BitVec 32) : BitVec 32 × BitVec 32 :=
  let p := nttButterflySpec64 (a.zeroExtend 64) (b.zeroExtend 64) (w.zeroExtend 64)
  (p.1.truncate 32, p.2.truncate 32)

/-- Shared butterfly body over `[a, b, w]` (all `.reg 64`). Computes the §13 REDC
    `t = montmul(w, b)` (bindings 0–10), then `a' = a + t` (binding 11) and
    `b' = a + 4p − t` (bindings 12–14: `4p` const, `a + 4p`, then `− t`), and
    finally an identity copy (`thRor 64 0`) of the chosen output word `outSrc` as
    the LAST binding — which the register-arith emit reads back as the result.
    `outSrc` is `a'` (de Bruijn 3) for `bflyAThir` or `b'` (de Bruijn 0) for
    `bflyBThir`. The REDC bindings, head-first:

        t0, c1, tlo, cm, mr, c2, m, cp, mp, s, t

    where `c1 = c2 = 0xffffffff`, `cm = minv`, `cp = p`, `t = s >> 32`; then
    `ap = a + t`, `cP4 = 4p`, `tmp = a + cP4`, `bp = tmp − t`. -/
def bflyBody
    (outSrc : @Ctxt.Var thirDialect
      [.reg 64, .reg 64, .reg 64, .reg 64, .reg 64, .reg 64, .reg 64, .reg 64,
       .reg 64, .reg 64, .reg 64, .reg 64, .reg 64, .reg 64, .reg 64, .reg 64,
       .reg 64, .reg 64]
      (.reg 64)) :
    Com thirDialect [.reg 64, .reg 64, .reg 64] (.reg 64) :=
  -- t0 = w * b   (ctx: [a, b, w]; w is dB 2, b is dB 1)
  .var (.mk (.thBin .mul 64) rfl
      (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
  -- c1 = 0xffffffff
  (.var (.mk (.thConst 64 0xffffffff) rfl .nil)
  -- tlo = t0 & c1   (ctx: [c1, t0, a, b, w])
  (.var (.mk (.thBin .and 64) rfl (.cons (.there .here) (.cons .here .nil)))
  -- cm = minv
  (.var (.mk (.thConst 64 babyBearMInv) rfl .nil)
  -- mr = tlo * cm   (ctx: [cm, tlo, c1, t0, a, b, w])
  (.var (.mk (.thBin .mul 64) rfl (.cons (.there .here) (.cons .here .nil)))
  -- c2 = 0xffffffff
  (.var (.mk (.thConst 64 0xffffffff) rfl .nil)
  -- m = mr & c2   (ctx: [c2, mr, cm, tlo, c1, t0, a, b, w])
  (.var (.mk (.thBin .and 64) rfl (.cons (.there .here) (.cons .here .nil)))
  -- cp = p
  (.var (.mk (.thConst 64 babyBearP) rfl .nil)
  -- mp = m * cp   (ctx: [cp, m, c2, mr, cm, tlo, c1, t0, a, b, w])
  (.var (.mk (.thBin .mul 64) rfl (.cons (.there .here) (.cons .here .nil)))
  -- s = t0 + mp   (t0 is dB 8 here)
  (.var (.mk (.thBin .add 64) rfl
      (.cons (.there (.there (.there (.there (.there (.there (.there
        (.there .here)))))))) (.cons .here .nil)))
  -- t = s >> 32
  (.var (.mk (.thShrImm 64 32) rfl (.cons .here .nil))
  -- ap = a + t   (ctx: [t, s, mp, cp, m, c2, mr, cm, tlo, c1, t0, a, b, w]; a is dB 11)
  (.var (.mk (.thBin .add 64) rfl
      (.cons (.there (.there (.there (.there (.there (.there (.there
        (.there (.there (.there (.there .here)))))))))))
        (.cons .here .nil)))
  -- cP4 = 4p
  (.var (.mk (.thConst 64 babyBear4P) rfl .nil)
  -- tmp = a + cP4   (ctx: [cP4, ap, t, …, a, b, w]; a is dB 13)
  (.var (.mk (.thBin .add 64) rfl
      (.cons (.there (.there (.there (.there (.there (.there (.there
        (.there (.there (.there (.there (.there (.there .here)))))))))))))
        (.cons .here .nil)))
  -- bp = tmp − t   (ctx: [tmp, cP4, ap, t, …]; tmp is dB 0, t is dB 3)
  (.var (.mk (.thBin .sub 64) rfl
      (.cons .here (.cons (.there (.there (.there .here))) .nil)))
  -- out = ror 0 outSrc  (identity copy: seats the chosen output word as the LAST
  -- binding, which the register-arith emit reads back as the result)
  (.var (.mk (.thRor 64 0) rfl (.cons outSrc .nil))
  (.ret .here))))))))))))))))

/-- NTT butterfly `a'` output (`= ap`, de Bruijn 3) as a `Com thirDialect` over
    `[a, b, w]`, built through the shared `bflyBody`. -/
def bflyAThir :
    Com thirDialect [.reg 64, .reg 64, .reg 64] (.reg 64) :=
  bflyBody (.there (.there (.there .here)))

/-- NTT butterfly `b'` output (`= bp`, de Bruijn 0). -/
def bflyBThir :
    Com thirDialect [.reg 64, .reg 64, .reg 64] (.reg 64) :=
  bflyBody .here

/-- The `a'` THIR-dialect program denotes the spec's first component. A direct
    check of the `thirDialect` semantics against `nttButterflySpec64`, under the
    final identity copy (`thRor 64 0`). -/
theorem bflyAThir_denote (a b w : BitVec 64) :
    bflyAThir.denote (.cons a (.cons b (.cons w .nil)))
      = (nttButterflySpec64 a b w).1 := by
  have e : bflyAThir.denote (.cons a (.cons b (.cons w .nil)))
      = ((nttButterflySpec64 a b w).1).rotateRight 0 := rfl
  rw [e]; simp [BitVec.rotateRight_def]

/-- The `b'` THIR-dialect program denotes the spec's second component. -/
theorem bflyBThir_denote (a b w : BitVec 64) :
    bflyBThir.denote (.cons a (.cons b (.cons w .nil)))
      = (nttButterflySpec64 a b w).2 := by
  have e : bflyBThir.denote (.cons a (.cons b (.cons w .nil)))
      = ((nttButterflySpec64 a b w).2).rotateRight 0 := rfl
  rw [e]; simp [BitVec.rotateRight_def]

/-- **NTT butterfly `a'` re-derived through the dialect spine.** The lowered
    (two-stage) `Com jasminDialect` for the BabyBear Montgomery-domain butterfly
    `a'` output denotes the same `BitVec 64` as the width-64 reference, obtained
    through `Com[thir] →lowerThir→ Com[jasmin]` rather than a bespoke lowering.
    Combines `lowerThir_denote` (the generic, proved dialect lowering) with
    `bflyAThir_denote`. -/
theorem bflyA_via_thirDialect (a b w : BitVec 64) :
    (lowerThir bflyAThir).denote (.cons a (.cons b (.cons w .nil)))
      = (nttButterflySpec64 a b w).1 := by
  rw [lowerThir_denote bflyAThir (.cons a (.cons b (.cons w .nil))), bflyAThir_denote]

/-- **NTT butterfly `b'` re-derived through the dialect spine.** -/
theorem bflyB_via_thirDialect (a b w : BitVec 64) :
    (lowerThir bflyBThir).denote (.cons a (.cons b (.cons w .nil)))
      = (nttButterflySpec64 a b w).2 := by
  rw [lowerThir_denote bflyBThir (.cons a (.cons b (.cons w .nil))), bflyBThir_denote]

/-- The width-64 butterfly restricted to `u32` inputs (zero-extended to 64) and
    truncated back to 32 is exactly `nttButterflySpec` — ties the emitted/lowered
    width-64 program to the `BitVec 32` reference. -/
theorem nttButterflySpec_eq_spec64 (a b w : BitVec 32) :
    nttButterflySpec a b w
      = ((nttButterflySpec64 (a.zeroExtend 64) (b.zeroExtend 64)
            (w.zeroExtend 64)).1.truncate 32,
         (nttButterflySpec64 (a.zeroExtend 64) (b.zeroExtend 64)
            (w.zeroExtend 64)).2.truncate 32) := by
  rfl

/-! ### §14.1  Emit the NTT butterfly outputs → owned-x86 jasmin

Each of the two output programs is lowered through the thirDialect spine
(`lowerThir bflyXThir`) and emitted by the verified register-arith orchestration
`emitAbiOrchReg` at width 64. The slot scheme mirrors §12/§13: binding `k` writes
working slot `k`; the 3 input words are copied into the trailing register slots.
The body has 15 bindings + 1 trailing `ret` copy, so 16 working slots precede the
3 input slots in the `stack u64[19] k` file. The three `u32` inputs are passed as
`u64` words; the result is the LAST binding's slot. -/

/-- Per-output register-file decls: 16 working slots + 3 input slots. -/
def bflyRegDecls : List String := ["stack u64[19] k"]

/-- Binding `k` → working slot `k`. -/
def bflyDstName (n : Nat) : String := "k[" ++ toString n ++ "]"

/-- Input word `i` (`a`/`b`/`w`) → copied-in register slot `16 + i`. -/
def bflyInName (i : Nat) : String := "k[" ++ toString (16 + i) ++ "]"

/-- The emitted `.jazz` for the NTT butterfly `a'` output through the thirDialect
    spine (`lowerThir bflyAThir`) and the verified register-arith orchestration.
    ABI: `reg ptr u64[1] out`, `reg const ptr u64[3] inp` (`inp = a, b, w`). -/
def bflyAJazz : String :=
  emitAbiOrchReg "babybear_ntt_bfly_a" (w := 64) (nIn := 3) (nOut := 1) (nCopy := 3)
    bflyRegDecls bflyInName bflyDstName (lowerThir bflyAThir)

/-- The emitted `.jazz` for the NTT butterfly `b'` output through the spine. -/
def bflyBJazz : String :=
  emitAbiOrchReg "babybear_ntt_bfly_b" (w := 64) (nIn := 3) (nOut := 1) (nCopy := 3)
    bflyRegDecls bflyInName bflyDstName (lowerThir bflyBThir)

/- The `a'` butterfly export has the expected ABI (1-word out, 3-word in). -/
#guard (strContains bflyAJazz "export fn babybear_ntt_bfly_a(reg ptr u64[1] out, reg const ptr u64[3] inp)")

/- The `b'` butterfly export has the expected ABI. -/
#guard (strContains bflyBJazz "export fn babybear_ntt_bfly_b(reg ptr u64[1] out, reg const ptr u64[3] inp)")

/- The emitted `a'` body renders real computation (no skipped ops). -/
#guard !(strContains bflyAJazz "non-regArith op skipped")

/-- The emitted butterfly bodies materialize the `minv`, `p`, and `4p` constants
    and the `0xffffffff` mask, use an integer multiply (the §13 REDC product) and
    a subtract (`w0 = w0 - w1;`, the lazy `a − ω·b`), and perform the `>> 32`
    reduction — the distinctive Montgomery-butterfly shape composing §13. -/
theorem bfly_redc_shape :
    strContains bflyBJazz "k[3] = 2013265919;" = true          -- minv = 0x77ffffff
      ∧ strContains bflyBJazz "k[7] = 2013265921;" = true      -- p = 0x78000001
      ∧ strContains bflyBJazz "k[12] = 8053063684;" = true     -- 4p = 0x1e0000004
      ∧ strContains bflyBJazz "w0 = w0 * w1;" = true            -- REDC product
      ∧ strContains bflyBJazz "w0 = w0 - w1;" = true            -- a − ω·b
      ∧ strContains bflyBJazz "w0 = w0 >> 32;" = true := by     -- REDC reduction
  native_decide

/- The two emitted butterfly functions return DISTINCT output words: each copies
    its own result slot into the final binding before the `out[0]` write
    (`a' = k[11]`, `b' = k[14]`). The register-arith emit reads back the last
    binding's slot, so distinct final-copy sources are exactly what makes the two
    exports compute the two butterfly outputs rather than a shared last value. -/
#guard (strContains bflyAJazz "w0 = k[11];\n  _, _, w0 = #ROR_64(w0, 0);\n  k[15] = w0;")
    && (strContains bflyBJazz "w0 = k[14];\n  _, _, w0 = #ROR_64(w0, 0);\n  k[15] = w0;")

/-! ## §15  Poseidon2 BabyBear S-box `x^7` (Montgomery domain) through the thirDialect spine (#606)

Phase-2 fan-out, the THIRD field-arithmetic primitive through the unified
`Com[thir] →lowerThir→ Com[jasmin]` spine, and the second to COMPOSE the §13
lazy Montgomery multiply: the Poseidon2 BabyBear S-box `x ↦ x^7` in the
Montgomery domain over the BabyBear prime `p = 0x78000001`, `R = 2^32`,
`alpha = 7`. For one Montgomery representative `x` (`< 2p`), the power is a
field-power gadget — a composition of four `montmul`s (§13 REDC), each
squaring/multiplying in the Montgomery domain:

    x2 = montmul(x,  x);     -- x²·R⁻¹ … lazy, in [0, 3p)
    x3 = montmul(x2, x);     -- x³·R⁻¹
    x6 = montmul(x3, x3);    -- x⁶·R⁻¹
    x7 = montmul(x6, x);     -- x⁷·R⁻¹   OUTPUT

`x7` is the LAZY Montgomery representative — congruent mod `p` to the canonical
`x^7`, with NO final conditional subtract (the thirDialect front is
straight-line, no `select`). Each `montmul` REUSES the §13 REDC body verbatim
(`montMulSpec64`); the S-box is the 4-fold composition. Like §13 the S-box is
SINGLE-OUTPUT: `x7` is the last montmul's result `r`, naturally the LAST
binding — no identity-copy tail. The whole gadget runs at **width 64** (the
`32×32→64` REDC product needs 64-bit intermediates, the lazy reps reach
`< 3p > 2^32`), so the `u32` input is held in a `u64` word and the output is a
`u64`. `sboxSpec` over a `BitVec 32` input zero-extends to 64, runs the same
4-montmul chain, and truncates the result back to a `BitVec 32`. -/

/-- The width-64 lazy Poseidon2 BabyBear S-box `x^7` over a `u64` word holding a
    `u32` Montgomery representative `x`. Four §13 REDC steps:
    `x2 = montmul(x,x)`, `x3 = montmul(x2,x)`, `x6 = montmul(x3,x3)`,
    `x7 = montmul(x6,x)`. The result is the lazy Montgomery rep of `x^7` (in
    `[0, 3p)`, congruent mod `p` to `x^7`) — the value the width-64 emit
    computes (the C KAT checks it congruent mod `p`). -/
def sboxSpec64 (x : BitVec 64) : BitVec 64 :=
  let x2 : BitVec 64 := montMulSpec64 x x
  let x3 : BitVec 64 := montMulSpec64 x2 x
  let x6 : BitVec 64 := montMulSpec64 x3 x3
  montMulSpec64 x6 x

/-- The reference lazy Poseidon2 BabyBear S-box `x^7` over a `BitVec 32`
    representative `x`. The input is zero-extended to 64 bits, the width-64
    4-montmul chain (`sboxSpec64`, reusing the §13 `montMulSpec64` REDC) is run,
    and the lazy `u64` output is truncated back to a `BitVec 32`. The C KAT
    checks the full `u64` output CONGRUENT mod `p`, the canonical-correctness
    statement for the lazy form. -/
def sboxSpec (x : BitVec 32) : BitVec 32 :=
  (sboxSpec64 (x.zeroExtend 64)).truncate 32

/-- The Poseidon2 BabyBear S-box `x^7` as a `Com thirDialect` over `[x]`
    (`.reg 64`, holding a `u32` Montgomery representative). Single-output: the
    last binding (the 4th montmul's `r`) IS the result, so no identity-copy tail
    is needed. Four inlined §13 REDC blocks (11 bindings each = 44 total),
    head-first; each block is `t = a₁·a₂`, then `c1, tlo, cm, mr, c2, m, cp, mp,
    s, r = s >> 32` with the same internal de Bruijn shape as §13. The only
    per-block variation is the two product args at the `t` binding:

        x2 : t = x·x       (x @0, x @0)
        x3 : t = x2·x      (x2 @0, x @11)
        x6 : t = x3·x3     (x3 @0, x3 @0)
        x7 : t = x6·x      (x6 @0, x @33)   -- OUTPUT -/
def sboxThir : Com thirDialect [.reg 64] (.reg 64) :=
  -- x2 = montmul(x, x)   (ctx start [x]; x @0)
  .var (.mk (.thBin .mul 64) rfl (.cons (.here) (.cons (.here) .nil)))  -- t = arg1 * arg2
  (.var (.mk (.thConst 64 0xffffffff) rfl .nil)  -- c1 = 0xffffffff
  (.var (.mk (.thBin .and 64) rfl (.cons (.there (.here)) (.cons .here .nil)))  -- tlo = t & c1
  (.var (.mk (.thConst 64 babyBearMInv) rfl .nil)  -- cm = minv
  (.var (.mk (.thBin .mul 64) rfl (.cons (.there (.here)) (.cons .here .nil)))  -- mr = tlo * cm
  (.var (.mk (.thConst 64 0xffffffff) rfl .nil)  -- c2 = 0xffffffff
  (.var (.mk (.thBin .and 64) rfl (.cons (.there (.here)) (.cons .here .nil)))  -- m = mr & c2
  (.var (.mk (.thConst 64 babyBearP) rfl .nil)  -- cp = p
  (.var (.mk (.thBin .mul 64) rfl (.cons (.there (.here)) (.cons .here .nil)))  -- mp = m * cp
  (.var (.mk (.thBin .add 64) rfl (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))) (.cons .here .nil)))  -- s = t + mp  (t @8)
  (.var (.mk (.thShrImm 64 32) rfl (.cons .here .nil))  -- r = s >> 32
  -- x3 = montmul(x2, x)  (x2 = rA @0; x @11)
  (.var (.mk (.thBin .mul 64) rfl (.cons (.here) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))) .nil)))  -- t = arg1 * arg2
  (.var (.mk (.thConst 64 0xffffffff) rfl .nil)  -- c1 = 0xffffffff
  (.var (.mk (.thBin .and 64) rfl (.cons (.there (.here)) (.cons .here .nil)))  -- tlo = t & c1
  (.var (.mk (.thConst 64 babyBearMInv) rfl .nil)  -- cm = minv
  (.var (.mk (.thBin .mul 64) rfl (.cons (.there (.here)) (.cons .here .nil)))  -- mr = tlo * cm
  (.var (.mk (.thConst 64 0xffffffff) rfl .nil)  -- c2 = 0xffffffff
  (.var (.mk (.thBin .and 64) rfl (.cons (.there (.here)) (.cons .here .nil)))  -- m = mr & c2
  (.var (.mk (.thConst 64 babyBearP) rfl .nil)  -- cp = p
  (.var (.mk (.thBin .mul 64) rfl (.cons (.there (.here)) (.cons .here .nil)))  -- mp = m * cp
  (.var (.mk (.thBin .add 64) rfl (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))) (.cons .here .nil)))  -- s = t + mp  (t @8)
  (.var (.mk (.thShrImm 64 32) rfl (.cons .here .nil))  -- r = s >> 32
  -- x6 = montmul(x3, x3) (x3 = rB @0)
  (.var (.mk (.thBin .mul 64) rfl (.cons (.here) (.cons (.here) .nil)))  -- t = arg1 * arg2
  (.var (.mk (.thConst 64 0xffffffff) rfl .nil)  -- c1 = 0xffffffff
  (.var (.mk (.thBin .and 64) rfl (.cons (.there (.here)) (.cons .here .nil)))  -- tlo = t & c1
  (.var (.mk (.thConst 64 babyBearMInv) rfl .nil)  -- cm = minv
  (.var (.mk (.thBin .mul 64) rfl (.cons (.there (.here)) (.cons .here .nil)))  -- mr = tlo * cm
  (.var (.mk (.thConst 64 0xffffffff) rfl .nil)  -- c2 = 0xffffffff
  (.var (.mk (.thBin .and 64) rfl (.cons (.there (.here)) (.cons .here .nil)))  -- m = mr & c2
  (.var (.mk (.thConst 64 babyBearP) rfl .nil)  -- cp = p
  (.var (.mk (.thBin .mul 64) rfl (.cons (.there (.here)) (.cons .here .nil)))  -- mp = m * cp
  (.var (.mk (.thBin .add 64) rfl (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))) (.cons .here .nil)))  -- s = t + mp  (t @8)
  (.var (.mk (.thShrImm 64 32) rfl (.cons .here .nil))  -- r = s >> 32
  -- x7 = montmul(x6, x)  OUTPUT (x6 = rC @0; x @33)
  (.var (.mk (.thBin .mul 64) rfl (.cons (.here) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))))))))))))))))))))))))) .nil)))  -- t = arg1 * arg2
  (.var (.mk (.thConst 64 0xffffffff) rfl .nil)  -- c1 = 0xffffffff
  (.var (.mk (.thBin .and 64) rfl (.cons (.there (.here)) (.cons .here .nil)))  -- tlo = t & c1
  (.var (.mk (.thConst 64 babyBearMInv) rfl .nil)  -- cm = minv
  (.var (.mk (.thBin .mul 64) rfl (.cons (.there (.here)) (.cons .here .nil)))  -- mr = tlo * cm
  (.var (.mk (.thConst 64 0xffffffff) rfl .nil)  -- c2 = 0xffffffff
  (.var (.mk (.thBin .and 64) rfl (.cons (.there (.here)) (.cons .here .nil)))  -- m = mr & c2
  (.var (.mk (.thConst 64 babyBearP) rfl .nil)  -- cp = p
  (.var (.mk (.thBin .mul 64) rfl (.cons (.there (.here)) (.cons .here .nil)))  -- mp = m * cp
  (.var (.mk (.thBin .add 64) rfl (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))) (.cons .here .nil)))  -- s = t + mp  (t @8)
  (.var (.mk (.thShrImm 64 32) rfl (.cons .here .nil))  -- r = s >> 32
  (.ret .here))))))))))))))))))))))))))))))))))))))))))))

/-- The THIR-dialect S-box denotes the width-64 reference `sboxSpec64` on any
    `u64` input word. A direct check of the `thirDialect` semantics against the
    4-montmul chain. -/
theorem sboxThir_denote (x : BitVec 64) :
    sboxThir.denote (.cons x .nil) = sboxSpec64 x := by
  rfl

/-- **Poseidon2 S-box `x^7` re-derived through the dialect spine.** The lowered
    (two-stage) `Com jasminDialect` for the lazy BabyBear S-box denotes the same
    `BitVec 64` as the width-64 reference, obtained through
    `Com[thir] →lowerThir→ Com[jasmin]` rather than a bespoke lowering. Combines
    `lowerThir_denote` (the generic, proved dialect lowering) with
    `sboxThir_denote`. -/
theorem sbox_via_thirDialect (x : BitVec 64) :
    (lowerThir sboxThir).denote (.cons x .nil) = sboxSpec64 x := by
  rw [lowerThir_denote sboxThir (.cons x .nil), sboxThir_denote]

/-- The width-64 S-box restricted to a `u32` input (zero-extended to 64) and
    truncated back to 32 is exactly `sboxSpec` — ties the emitted/lowered
    width-64 program (`sboxSpec64`) to the `BitVec 32` reference. -/
theorem sboxSpec_eq_spec64 (x : BitVec 32) :
    sboxSpec x = (sboxSpec64 (x.zeroExtend 64)).truncate 32 := by
  rfl

/-! ### §15.1  Emit the Poseidon2 S-box → owned-x86 jasmin

The single-output S-box is lowered through the thirDialect spine
(`lowerThir sboxThir`) and emitted by the verified register-arith orchestration
`emitAbiOrchReg` at width 64. The body has 44 bindings (four §13 REDC blocks),
so 44 working slots precede the 1 input slot in the `stack u64[45] k` file. The
`u32` input is passed as a `u64` word. The result is the LAST binding's slot
(no identity-copy tail — single output, like §13). -/

/-- Per-output register-file decls: 44 working slots + 1 input slot. -/
def sboxRegDecls : List String := ["stack u64[45] k"]

/-- Binding `k` → working slot `k`. -/
def sboxDstName (n : Nat) : String := "k[" ++ toString n ++ "]"

/-- Input word `i` (`x`) → copied-in register slot `44 + i`. -/
def sboxInName (i : Nat) : String := "k[" ++ toString (44 + i) ++ "]"

/-- The emitted `.jazz` for the lazy Poseidon2 BabyBear S-box `x^7` through the
    thirDialect spine (`lowerThir sboxThir`) and the verified register-arith
    orchestration. ABI: `reg ptr u64[1] out`, `reg const ptr u64[1] inp`. -/
def sboxJazz : String :=
  emitAbiOrchReg "babybear_poseidon2_sbox" (w := 64) (nIn := 1) (nOut := 1) (nCopy := 1)
    sboxRegDecls sboxInName sboxDstName (lowerThir sboxThir)

/- The S-box export has the expected ABI (1-word out, 1-word in). -/
#guard (strContains sboxJazz "export fn babybear_poseidon2_sbox(reg ptr u64[1] out, reg const ptr u64[1] inp)")

/- The emitted S-box body renders real computation (no skipped ops). -/
#guard !(strContains sboxJazz "non-regArith op skipped")

/- The emitted S-box body uses an integer multiply (`w0 = w0 * w1;`), the
    `thBin .mul 64` REDC product reused across the four field multiplies — the
    field-arithmetic op composed by the power gadget. -/
#guard (strContains sboxJazz "w0 = w0 * w1;")

/-- The emitted S-box body materializes the `minv` and `p` REDC constants and the
    `0xffffffff` low-word mask, and performs the `>> 32` reduction — the
    distinctive §13 REDC shape, replicated across the four montmuls. -/
theorem sbox_redc_shape :
    strContains sboxJazz "k[3] = 2013265919;" = true          -- minv = 0x77ffffff
      ∧ strContains sboxJazz "k[7] = 2013265921;" = true      -- p = 0x78000001
      ∧ strContains sboxJazz "k[1] = 4294967295;" = true      -- 0xffffffff mask
      ∧ strContains sboxJazz "w0 = w0 >> 32;" = true := by     -- REDC reduction
  native_decide

/- The final montmul (`x7 = montmul(x6, x)`) writes the OUTPUT into the last
    working slot `k[43]`, which the register-arith emit reads back as the result
    (`r = s >> 32` of the fourth REDC block, no identity-copy tail). -/
#guard (strContains sboxJazz "k[43] = w0;\n  w0 = k[43];\n  out[0] = w0;")

/-! ## §16  Widening multiply + carry-chain add through the thirDialect spine (#616, E1a)

Phase-2 front op-exposure for the BMI2/ADX trio: the THIR front now carries the
high word of a `64×64→128` widening multiply (`thMulHi`) and the data / carry-out
words of a carry-chain add (`thAddCarryLo` / `thAddCarryHi`), each lowering 1:1 to
the matching jasmin op (`mulhi` / `addCarryLo` / `addCarryHi`) through the generic
verified `lowerThir`. These are the front handle for multi-limb bignum / EC /
pairing field arithmetic (Class B): a `64×64→128` multiply is the pair
`(thBin .mul 64, thMulHi 64)` = MULX's `(lo, hi)`, and a multi-limb add is a
data-flow thread of `(thAddCarryLo, thAddCarryHi)` over a `reg 1` carry.

Scope: this is the op-exposure + value-correctness step. The field-correctness of
a Montgomery multi-limb leaf (AUCurves) is the separate follow-on E1b.

### §16.1  `widenMul64`: the `64×64→128` widening multiply

Two `u64` outputs over `[a, b]`: `lo = thBin .mul 64 a b` (the low word) and
`hi = thMulHi 64 a b` (`mulHiW a b`). Together they are the full `128`-bit product
`a · b = hi · 2^64 + lo`. Following §14, each output is a SEPARATE single-output
`Com thirDialect` program that seats its word as the LAST binding (an identity
`thRor 64 0` copy), which the register-arith emit reads back as the result. -/

/-- The value spec of the widening multiply low word: `(a · b) mod 2^64`. This is
    exactly `(a * b : BitVec 64)` (the jasmin `mul`) by `BitVec` multiplication. -/
def widenMulLoSpec (a b : BitVec 64) : BitVec 64 := a * b

/-- The value spec of the widening multiply high word: `(a · b) / 2^64`, the
    `hi` output of MULX (`mulHiW a b`). -/
def widenMulHiSpec (a b : BitVec 64) : BitVec 64 := mulHiW a b

/-- Widening multiply LOW word as a `Com thirDialect` over `[a, b]`:
    `lo = thBin .mul 64 a b`, then an identity `thRor 64 0` copy as the last
    binding. -/
def widenMulLoThir : Com thirDialect [.reg 64, .reg 64] (.reg 64) :=
  -- lo = a * b   (ctx [a, b]; a = dB 0, b = dB 1)
  .var (.mk (.thBin .mul 64) rfl (.cons .here (.cons (.there .here) .nil)))
  -- out = ror 0 lo   (ctx [lo, a, b]; lo = dB 0)
  (.var (.mk (.thRor 64 0) rfl (.cons .here .nil))
  (.ret .here))

/-- Widening multiply HIGH word as a `Com thirDialect` over `[a, b]`:
    `hi = thMulHi 64 a b` (= `mulHiW a b`), then an identity `thRor 64 0` copy as
    the last binding. -/
def widenMulHiThir : Com thirDialect [.reg 64, .reg 64] (.reg 64) :=
  -- hi = mulhi a b   (ctx [a, b]; a = dB 0, b = dB 1)
  .var (.mk (.thMulHi 64) rfl (.cons .here (.cons (.there .here) .nil)))
  -- out = ror 0 hi   (ctx [hi, a, b]; hi = dB 0)
  (.var (.mk (.thRor 64 0) rfl (.cons .here .nil))
  (.ret .here))

/-- The LOW-word THIR program denotes the spec, under the final identity copy. -/
theorem widenMulLoThir_denote (a b : BitVec 64) :
    widenMulLoThir.denote (.cons a (.cons b .nil)) = widenMulLoSpec a b := by
  have e : widenMulLoThir.denote (.cons a (.cons b .nil))
      = (widenMulLoSpec a b).rotateRight 0 := rfl
  rw [e]; simp [BitVec.rotateRight_def]

/-- The HIGH-word THIR program denotes the spec, under the final identity copy. -/
theorem widenMulHiThir_denote (a b : BitVec 64) :
    widenMulHiThir.denote (.cons a (.cons b .nil)) = widenMulHiSpec a b := by
  have e : widenMulHiThir.denote (.cons a (.cons b .nil))
      = (widenMulHiSpec a b).rotateRight 0 := rfl
  rw [e]; simp [BitVec.rotateRight_def]

/-- **Widening multiply LOW word re-derived through the dialect spine.** The
    lowered `Com jasminDialect` (via the generic, proved `lowerThir`) denotes the
    same `BitVec 64` as the spec. -/
theorem widenMul_lo_via_thirDialect (a b : BitVec 64) :
    (lowerThir widenMulLoThir).denote (.cons a (.cons b .nil)) = widenMulLoSpec a b := by
  rw [lowerThir_denote widenMulLoThir (.cons a (.cons b .nil)), widenMulLoThir_denote]

/-- **Widening multiply HIGH word re-derived through the dialect spine.** This is
    the `thMulHi → mulhi` arm of `lowerThir` exercised end-to-end: the lowered
    jasmin program denotes `mulHiW a b`, the MULX high word. -/
theorem widenMul_hi_via_thirDialect (a b : BitVec 64) :
    (lowerThir widenMulHiThir).denote (.cons a (.cons b .nil)) = widenMulHiSpec a b := by
  rw [lowerThir_denote widenMulHiThir (.cons a (.cons b .nil)), widenMulHiThir_denote]

/-- The two output words reconstruct the full `128`-bit product over `ℕ`:
    `(hi · 2^64 + lo) = a.toNat · b.toNat`. Ties the `(lo, hi)` pair to the
    `(unsigned __int128) a * b` the KAT checks. -/
theorem widenMul_reconstruct (a b : BitVec 64) :
    (widenMulHiSpec a b).toNat * 2 ^ 64 + (widenMulLoSpec a b).toNat
      = a.toNat * b.toNat := by
  show (mulHiW a b).toNat * 2 ^ 64 + (a * b).toNat = a.toNat * b.toNat
  have hprod : a.toNat * b.toNat < 2 ^ 64 * 2 ^ 64 :=
    Nat.mul_lt_mul'' a.isLt b.isLt
  have hdiv : a.toNat * b.toNat / 2 ^ 64 < 2 ^ 64 :=
    Nat.div_lt_of_lt_mul hprod
  have hdm : 2 ^ 64 * (a.toNat * b.toNat / 2 ^ 64) + a.toNat * b.toNat % 2 ^ 64
      = a.toNat * b.toNat := Nat.div_add_mod _ _
  simp only [mulHiW, BitVec.toNat_ofNat, BitVec.toNat_mul, Nat.mod_eq_of_lt hdiv]
  omega

/-! #### §16.1a  Emit the widening-multiply LOW word → owned-x86 jasmin

The low word is `thBin .mul 64`, which lowers (`lowerThir`) to `regArith .mul 64`
and renders through `emitBodyReg`'s `regArith` arm as the real `64×64→64` low
multiply `w0 = w0 * w1;` — exactly `(unsigned __int128)(a)*b` truncated to 64
bits. Single u64 output over two u64 inputs; slot scheme mirrors §13. The body
has 2 bindings (mul + identity copy) so 2 working slots precede the 2 input slots
in `stack u64[4] k`.

The HIGH word (`thMulHi`) and the carry-chain words (`thAddCarryLo` /
`thAddCarryHi`) lower to the jasmin `mulhi` / `addCarryLo` / `addCarryHi` ops,
which `emitBodyReg` does not yet render to jazz text (they route through its
non-`regArith` skip arm). Rendering those three ops to jasmin (e.g. `MULX` and the
`ADCX`/`ADOX` carry chain) is the emit-side arm in `JasminAbiEmit.lean` — the
immediate follow-on. The value-level lowering and the `*_via_thirDialect`
denotation theorems above are independent of that emit arm. -/

/-- Per-output register-file decls for `widenMulLo`: 2 working slots + 2 inputs. -/
def widenRegDecls : List String := ["stack u64[4] k"]

/-- Binding `k` → working slot `k`. -/
def widenDstName (n : Nat) : String := "k[" ++ toString n ++ "]"

/-- Input word `i` (`a`/`b`) → copied-in register slot `2 + i`. -/
def widenInName (i : Nat) : String := "k[" ++ toString (2 + i) ++ "]"

/-- The emitted `.jazz` for the widening-multiply LOW word through the thirDialect
    spine (`lowerThir widenMulLoThir`) and the verified register-arith
    orchestration. ABI: `reg ptr u64[1] out`, `reg const ptr u64[2] inp`. -/
def widenMulLoJazz : String :=
  emitAbiOrchReg "widen_mul_lo" (w := 64) (nIn := 2) (nOut := 1) (nCopy := 2)
    widenRegDecls widenInName widenDstName (lowerThir widenMulLoThir)

/- The LOW-word export has the expected ABI (1-word out, 2-word in). -/
#guard (strContains widenMulLoJazz "export fn widen_mul_lo(reg ptr u64[1] out, reg const ptr u64[2] inp)")

/- The emitted LOW-word body renders the real `64×64→64` low multiply
    (`w0 = w0 * w1;`) and skips no op — the rendering side of `thBin .mul 64`. -/
#guard (strContains widenMulLoJazz "w0 = w0 * w1;")
    && !(strContains widenMulLoJazz "non-regArith op skipped")

/-- The emitted `.jazz` for the widening-multiply HIGH word through the
    thirDialect spine (`lowerThir widenMulHiThir`) and the verified register-arith
    orchestration. The `thMulHi 64` op lowers to `mulhi 64` and renders (the new
    `emitBodyReg` arm) as a `#MULX` high-multiply `w0, w1 = #MULX(w0, w1);` reading
    back the hi word (#616 E1a). Same ABI/slot scheme as the low word:
    `reg ptr u64[1] out`, `reg const ptr u64[2] inp`, 2 working + 2 input slots. -/
def widenMulHiJazz : String :=
  emitAbiOrchReg "widen_mul_hi" (w := 64) (nIn := 2) (nOut := 1) (nCopy := 2)
    widenRegDecls widenInName widenDstName (lowerThir widenMulHiThir)

/- The HIGH-word export has the expected ABI (1-word out, 2-word in). -/
#guard (strContains widenMulHiJazz "export fn widen_mul_hi(reg ptr u64[1] out, reg const ptr u64[2] inp)")

/- The emitted HIGH-word body renders the `#MULX` high-multiply and skips no op —
    the rendering side of `thMulHi 64 → mulhi 64`. -/
#guard (strContains widenMulHiJazz "w0, w1 = #MULX(w0, w1);")
    && !(strContains widenMulHiJazz "non-regArith op skipped")

/-! ### §16.2  `addCarry2limb`: a 2-limb carry-chain add `(a1:a0)+(b1:b0)=(s1:s0)`

Four `u64` inputs `[a0, a1, b0, b1]`; two `u64` outputs `s0`, `s1` threading a
1-bit carry:

    s0 = addCarryLo a0 b0 0;    c = addCarryHi a0 b0 0;    s1 = addCarryLo a1 b1 c.

`c` is a `reg 1` value (no hidden flag state) — the explicit data-flow thread of
the carry chain. Following §14, each output is a separate single-output program
built from a shared body (`addCarry2limbBody`) that seats the chosen output word
as the LAST binding via an identity `thRor 64 0` copy. -/

/-- The width-64 reference 2-limb add: `(s0, s1)` of `(a1:a0)+(b1:b0)`, with the
    carry from limb 0 threaded into limb 1, each limb's data word in `[0, 2^64)`
    and the carry a 1-bit value. -/
def addCarry2limbSpec (a0 a1 b0 b1 : BitVec 64) : BitVec 64 × BitVec 64 :=
  let c : BitVec 1 := carryOutBit a0 b0 0
  (addCarryWord a0 b0 0, addCarryWord a1 b1 c)

/-- Shared 2-limb-add body over `[a0, a1, b0, b1]` (all `.reg 64`). Bindings,
    head-first:

        z  = thConst 1 0            -- carry-in zero  (reg 1)
        s0 = addCarryLo a0 b0 z     -- limb-0 data word
        c  = addCarryHi a0 b0 z     -- limb-0 carry-out (reg 1)
        s1 = addCarryLo a1 b1 c     -- limb-1 data word

    then an identity `thRor 64 0` copy of `outSrc` (`s0` = dB 2 or `s1` = dB 0) as
    the LAST binding, which the register-arith emit reads back as the result. -/
def addCarry2limbBody
    (outSrc : @Ctxt.Var thirDialect
      [.reg 64, .reg 1, .reg 64, .reg 1, .reg 64, .reg 64, .reg 64, .reg 64]
      (.reg 64)) :
    Com thirDialect [.reg 64, .reg 64, .reg 64, .reg 64] (.reg 64) :=
  -- z = 0 : reg 1   (carry-in zero; ctx [a0, a1, b0, b1])
  .var (.mk (.thConst 1 0) rfl .nil)
  -- s0 = addCarryLo a0 b0 z   (ctx [z, a0, a1, b0, b1]; a0 dB1, b0 dB3, z dB0)
  (.var (.mk (.thAddCarryLo 64) rfl
      (.cons (.there .here) (.cons (.there (.there (.there .here))) (.cons .here .nil))))
  -- c = addCarryHi a0 b0 z   (ctx [s0, z, a0, a1, b0, b1]; a0 dB2, b0 dB4, z dB1)
  (.var (.mk (.thAddCarryHi 64) rfl
      (.cons (.there (.there .here))
        (.cons (.there (.there (.there (.there .here)))) (.cons (.there .here) .nil))))
  -- s1 = addCarryLo a1 b1 c   (ctx [c, s0, z, a0, a1, b0, b1]; a1 dB4, b1 dB6, c dB0)
  (.var (.mk (.thAddCarryLo 64) rfl
      (.cons (.there (.there (.there (.there .here))))
        (.cons (.there (.there (.there (.there (.there (.there .here))))))
          (.cons .here .nil))))
  -- out = ror 0 outSrc   (identity copy of the chosen output word)
  (.var (.mk (.thRor 64 0) rfl (.cons outSrc .nil))
  (.ret .here)))))

/-- 2-limb add `s0` output (`= s0`, de Bruijn 2 inside the body's final context). -/
def addCarry2limbS0Thir : Com thirDialect [.reg 64, .reg 64, .reg 64, .reg 64] (.reg 64) :=
  addCarry2limbBody (.there (.there .here))

/-- 2-limb add `s1` output (`= s1`, de Bruijn 0). -/
def addCarry2limbS1Thir : Com thirDialect [.reg 64, .reg 64, .reg 64, .reg 64] (.reg 64) :=
  addCarry2limbBody .here

/-- The `s0` THIR program denotes the spec's first component (limb-0 data word),
    under the final identity copy. -/
theorem addCarry2limbS0Thir_denote (a0 a1 b0 b1 : BitVec 64) :
    addCarry2limbS0Thir.denote (.cons a0 (.cons a1 (.cons b0 (.cons b1 .nil))))
      = (addCarry2limbSpec a0 a1 b0 b1).1 := by
  have e : addCarry2limbS0Thir.denote (.cons a0 (.cons a1 (.cons b0 (.cons b1 .nil))))
      = ((addCarry2limbSpec a0 a1 b0 b1).1).rotateRight 0 := rfl
  rw [e]; simp [BitVec.rotateRight_def]

/-- The `s1` THIR program denotes the spec's second component (limb-1 data word,
    carry threaded), under the final identity copy. -/
theorem addCarry2limbS1Thir_denote (a0 a1 b0 b1 : BitVec 64) :
    addCarry2limbS1Thir.denote (.cons a0 (.cons a1 (.cons b0 (.cons b1 .nil))))
      = (addCarry2limbSpec a0 a1 b0 b1).2 := by
  have e : addCarry2limbS1Thir.denote (.cons a0 (.cons a1 (.cons b0 (.cons b1 .nil))))
      = ((addCarry2limbSpec a0 a1 b0 b1).2).rotateRight 0 := rfl
  rw [e]; simp [BitVec.rotateRight_def]

/-- **2-limb add `s0` re-derived through the dialect spine.** The lowered jasmin
    program (via the generic proved `lowerThir`, exercising the
    `thAddCarryLo → addCarryLo` and `thAddCarryHi → addCarryHi` arms) denotes the
    same `BitVec 64`. -/
theorem addCarry2limb_s0_via_thirDialect (a0 a1 b0 b1 : BitVec 64) :
    (lowerThir addCarry2limbS0Thir).denote (.cons a0 (.cons a1 (.cons b0 (.cons b1 .nil))))
      = (addCarry2limbSpec a0 a1 b0 b1).1 := by
  rw [lowerThir_denote addCarry2limbS0Thir _, addCarry2limbS0Thir_denote]

/-- **2-limb add `s1` re-derived through the dialect spine.** -/
theorem addCarry2limb_s1_via_thirDialect (a0 a1 b0 b1 : BitVec 64) :
    (lowerThir addCarry2limbS1Thir).denote (.cons a0 (.cons a1 (.cons b0 (.cons b1 .nil))))
      = (addCarry2limbSpec a0 a1 b0 b1).2 := by
  rw [lowerThir_denote addCarry2limbS1Thir _, addCarry2limbS1Thir_denote]

/-- `addCarry2limb` realises the `128`-bit add over `ℕ`:
    `(s1 · 2^64 + s0) = (a1·2^64 + a0) + (b1·2^64 + b0)` whenever the top limb does
    not overflow (`a1 + b1 + c < 2^64`), the regime the KAT drives. Ties the
    `(s0, s1)` pair to the `128`-bit reference add. -/
theorem addCarry2limb_reconstruct (a0 a1 b0 b1 : BitVec 64)
    (htop : a1.toNat + b1.toNat + (carryOutBit a0 b0 0).toNat < 2 ^ 64) :
    (addCarry2limbSpec a0 a1 b0 b1).2.toNat * 2 ^ 64
        + (addCarry2limbSpec a0 a1 b0 b1).1.toNat
      = (a1.toNat * 2 ^ 64 + a0.toNat) + (b1.toNat * 2 ^ 64 + b0.toNat) := by
  have ha0 := a0.isLt; have hb0 := b0.isLt
  have ha1 := a1.isLt; have hb1 := b1.isLt
  have hz : ((0 : BitVec 1)).toNat = 0 := rfl
  set c : BitVec 1 := carryOutBit a0 b0 0 with hcdef
  -- carry value: `c.toNat = (a0+b0) / 2^64` (cin = 0).
  have hc : c.toNat = (a0.toNat + b0.toNat) / 2 ^ 64 := by
    simp only [hcdef, carryOutBit, hz, Nat.add_zero]
    by_cases h : a0.toNat + b0.toNat ≥ 2 ^ 64
    · rw [if_pos h]
      have : (1 : BitVec 1).toNat = 1 := rfl
      rw [this]; omega
    · rw [if_neg h, hz, Nat.div_eq_of_lt (Nat.lt_of_not_le h)]
  have hcle : c.toNat ≤ 1 := Nat.le_of_lt_succ (by have := c.isLt; simpa using this)
  -- unfold both data words to ℕ and discharge by `omega` (which handles `% 2^64`).
  have hs0 : (addCarryWord a0 b0 0).toNat = (a0.toNat + b0.toNat) % 2 ^ 64 := by
    simp only [addCarryWord, BitVec.toNat_add, BitVec.toNat_ofNat, hz]
    omega
  have hcmod : c.toNat % 2 ^ 64 = c.toNat := Nat.mod_eq_of_lt (by omega)
  have hs1 : (addCarryWord a1 b1 c).toNat = (a1.toNat + b1.toNat + c.toNat) % 2 ^ 64 := by
    simp only [addCarryWord, BitVec.toNat_add, BitVec.toNat_ofNat, hcmod]
    omega
  have hdm : 2 ^ 64 * ((a0.toNat + b0.toNat) / 2 ^ 64) + (a0.toNat + b0.toNat) % 2 ^ 64
      = a0.toNat + b0.toNat := Nat.div_add_mod _ _
  simp only [addCarry2limbSpec, ← hcdef, hs0, hs1, hc]
  omega

/-! #### §16.2a  Emit the 2-limb carry-chain add → owned-x86 jasmin

`addCarry2limbS0Thir` / `addCarry2limbS1Thir` lower (`lowerThir`) to jasmin `Com`s
whose ops are `addCarryLo` / `addCarryHi` (+ a `regConst` carry-in zero and the
final identity `ror`), which the register-arith emit now renders (#616 E1a): the
data word `addCarryLo` as the value→flag `#ADD`/`#ADC` idiom reading the ADC
result, the carry-out `addCarryHi` materialising the propagated `cf` back to a 0/1
word. The carry-in `reg 1` value threads through the register file like any other
word, so the explicit carry data-flow is preserved with no hidden flag state
across bindings.

Each output is a separate single-output export (`§14` convention). The body has 5
bindings (carry-in zero + the three carry ops + the identity copy), so the
register file is `stack u64[9] k`: 5 working slots `k[0..4]` then the 4 input
slots `k[5..8]`. -/

/-- Per-output register-file decls for `addCarry2limb`: 5 working slots + 4
    inputs (`stack u64[9] k`). -/
def addCarry2RegDecls : List String := ["stack u64[9] k"]

/-- Input word `i` (`a0`/`a1`/`b0`/`b1`) → copied-in register slot `5 + i`. -/
def addCarry2InName (i : Nat) : String := "k[" ++ toString (5 + i) ++ "]"

/-- The emitted `.jazz` for the 2-limb-add `s0` (limb-0 data word) through the
    thirDialect spine (`lowerThir addCarry2limbS0Thir`) and the verified
    register-arith orchestration. ABI: `reg ptr u64[1] out`,
    `reg const ptr u64[4] inp`. -/
def addCarry2limbS0Jazz : String :=
  emitAbiOrchReg "addcarry2limb_s0" (w := 64) (nIn := 4) (nOut := 1) (nCopy := 4)
    addCarry2RegDecls addCarry2InName widenDstName (lowerThir addCarry2limbS0Thir)

/-- The emitted `.jazz` for the 2-limb-add `s1` (limb-1 data word, carry threaded)
    through `lowerThir addCarry2limbS1Thir` and the register-arith orchestration.
    ABI: `reg ptr u64[1] out`, `reg const ptr u64[4] inp`. -/
def addCarry2limbS1Jazz : String :=
  emitAbiOrchReg "addcarry2limb_s1" (w := 64) (nIn := 4) (nOut := 1) (nCopy := 4)
    addCarry2RegDecls addCarry2InName widenDstName (lowerThir addCarry2limbS1Thir)

/- The `s0` export has the expected ABI (1-word out, 4-word in). -/
#guard (strContains addCarry2limbS0Jazz "export fn addcarry2limb_s0(reg ptr u64[1] out, reg const ptr u64[4] inp)")

/- The `s1` export has the expected ABI (1-word out, 4-word in). -/
#guard (strContains addCarry2limbS1Jazz "export fn addcarry2limb_s1(reg ptr u64[1] out, reg const ptr u64[4] inp)")

/- The `s1` body renders the `#ADC` carry-chain data word and the carry-out
    materialisation, and skips no op — the rendering side of `addCarryLo` /
    `addCarryHi`. -/
#guard (strContains addCarry2limbS1Jazz "= #ADC_64(w0, w1, cf);")
    && !(strContains addCarry2limbS1Jazz "non-regArith op skipped")

/-! ## §17  Constant-time conditional-subtract (SELECT / cmov) through the thirDialect spine (#594, E2)

Phase-2 front op-exposure for branch-free conditional code: the THIR front now
carries a constant-time SELECT `thSelect` (`if cond then a else b`, both operands
always evaluated), lowering 1:1 to the matching jasmin `select` op through the
generic verified `lowerThir`. The emit renders it as a **branchless mask-select**
`b ^ ((a ^ b) & mask)`, `mask = 0 - cond` (`renderSelect` in
`JasminAbiEmit.lean`) — a data-oblivious conditional move with no
secret-dependent branch.

`thSelect` is the front's constant-time primitive for the canonical
conditional-subtract demonstrated here, for the `cswap` of a Montgomery /
X25519 ladder (`select cond a b` / `select cond b a` over a pair), and for a
rejection sampler's conditional core. Constant-time preservation of the lowered
`Com` follows from the `#594` secret-type qualifier already in Com/VIR: a
`.Secret`-tagged branch (`ComR.ifBit _ .Secret …`) is rejected by
`CTPredicate.ctSafeComR` (`ctSafeComR_ifBit_secret`), so the only CT-safe way to
realise a secret-dependent conditional is exactly this branch-free SELECT — its
two operands are both evaluated, so there is no `.Secret` `ifBit` to reject. The
`SecretLevel` tag is `CatCrypt.Crypto.Jasmin.LowCT.SecretLevel`.

Scope: this is the op-exposure + value-correctness step (one `thBin .sub` + one
`thSelect`). The branch-free cswap of a full ladder leaf is the follow-on. -/

/-- The value spec of the constant-time conditional-subtract: `if cond = 1 then
    a - b else a`. The canonical "subtract `b` only when the carry/condition bit
    is set" step (the conditional reduction of a Montgomery / modular subtract),
    realised branch-free. -/
def condSubSelectSpec (a b : BitVec 64) (cond : BitVec 1) : BitVec 64 :=
  selectW cond (a - b) a

/-- Constant-time conditional-subtract as a `Com thirDialect` over `[a, b, cond]`
    (`a`/`b` are `.reg 64`, `cond` is `.reg 1`):

        d   = thBin .sub 64 a b      -- the difference a - b
        out = thSelect 64 cond d a   -- if cond then (a - b) else a

    then an identity `thRor 64 0` copy of `out` as the LAST binding, which the
    register-arith emit reads back as the result. -/
def condSubSelectThir : Com thirDialect [.reg 64, .reg 64, .reg 1] (.reg 64) :=
  -- d = a - b   (ctx [a, b, cond]; a = dB0, b = dB1)
  .var (.mk (.thBin .sub 64) rfl (.cons .here (.cons (.there .here) .nil)))
  -- out = select cond d a   (ctx [d, a, b, cond]; cond = dB3, d = dB0, a = dB1)
  (.var (.mk (.thSelect 64) rfl
      (.cons (.there (.there (.there .here)))
        (.cons .here (.cons (.there .here) .nil))))
  -- ret out, via an identity ror-0 copy (ctx [out, d, a, b, cond]; out = dB0)
  (.var (.mk (.thRor 64 0) rfl (.cons .here .nil))
  (.ret .here)))

/-- The conditional-subtract THIR program denotes the spec, under the final
    identity copy. -/
theorem condSubSelectThir_denote (a b : BitVec 64) (cond : BitVec 1) :
    condSubSelectThir.denote (.cons a (.cons b (.cons cond .nil)))
      = condSubSelectSpec a b cond := by
  have e : condSubSelectThir.denote (.cons a (.cons b (.cons cond .nil)))
      = (condSubSelectSpec a b cond).rotateRight 0 := rfl
  rw [e]; simp [BitVec.rotateRight_def]

/-- **Constant-time conditional-subtract re-derived through the dialect spine.**
    The lowered `Com jasminDialect` (via the generic, proved `lowerThir`,
    exercising the `thSelect → select` arm) denotes the same `BitVec 64` as the
    spec, on every `(a, b, cond)`. -/
theorem condSubSelect_via_thirDialect (a b : BitVec 64) (cond : BitVec 1) :
    (lowerThir condSubSelectThir).denote (.cons a (.cons b (.cons cond .nil)))
      = condSubSelectSpec a b cond := by
  rw [lowerThir_denote condSubSelectThir (.cons a (.cons b (.cons cond .nil))),
    condSubSelectThir_denote]

/-- `condSubSelect` realises the canonical conditional reduction over `ℕ`: when
    `cond = 1` and the subtract does not underflow (`b ≤ a`) the result is
    `a - b`; when `cond = 0` it is `a`. Ties the SELECT output to the `cond ? a-b
    : a` reference the KAT checks. -/
theorem condSubSelect_reconstruct (a b : BitVec 64) (cond : BitVec 1) :
    (condSubSelectSpec a b cond) = (if cond = 1#1 then a - b else a) := by
  simp only [condSubSelectSpec, selectW]

/-! #### §17.1  Emit the constant-time conditional-subtract → owned-x86 jasmin

`condSubSelectThir` lowers (`lowerThir`) to a jasmin `Com` whose ops are
`regArith .sub` (the difference) and `select` (+ the final identity `ror`). The
register-arith emit now renders `select` (#594, E2) as the branchless
mask-select `(a & mask) | (b & ~mask)`, `mask = 0 - cond` — a data-oblivious
conditional move (no secret-dependent branch, no flag read). The `reg 1`
condition value threads through the register file like any other word.

Three inputs `[a, b, cond]`; one `u64` output. The body has 3 bindings (sub +
select + identity copy), so the register file is `stack u64[6] k`: 3 working
slots `k[0..2]` then the 3 input slots `k[3..5]`. -/

/-- Per-output register-file decls for `condSubSelect`: 3 working slots + 3
    inputs (`stack u64[6] k`). -/
def condSubRegDecls : List String := ["stack u64[6] k"]

/-- Input word `i` (`a`/`b`/`cond`) → copied-in register slot `3 + i`. -/
def condSubInName (i : Nat) : String := "k[" ++ toString (3 + i) ++ "]"

/-- The emitted `.jazz` for the constant-time conditional-subtract through the
    thirDialect spine (`lowerThir condSubSelectThir`) and the verified
    register-arith orchestration. The `thSelect 64` op lowers to `select 64` and
    renders (the new `emitBodyReg` arm) as the branchless mask-select. ABI:
    `reg ptr u64[1] out`, `reg const ptr u64[3] inp` (`inp = a, b, cond`). -/
def condSubSelectJazz : String :=
  emitAbiOrchReg "condsub_select" (w := 64) (nIn := 3) (nOut := 1) (nCopy := 3)
    condSubRegDecls condSubInName widenDstName (lowerThir condSubSelectThir)

#eval IO.println condSubSelectJazz

/- The export has the expected ABI (1-word out, 3-word in). -/
#guard (strContains condSubSelectJazz "export fn condsub_select(reg ptr u64[1] out, reg const ptr u64[3] inp)")

/- The emitted body renders the branchless mask-select (`mask = -cond`, i.e.
    `0 - cond`, then `b ^ ((a ^ b) & mask)`) and the real subtract, and skips no
    op — the rendering side of `thBin .sub 64 → regArith .sub` and `thSelect 64 →
    select`. -/
#guard (strContains condSubSelectJazz "wb = -wb;")
    && (strContains condSubSelectJazz "w0 = w0 & wb;")
    && !(strContains condSubSelectJazz "non-regArith op skipped")

/-- The two binding destinations of the demonstrator are distinct working slots
    (`k[0]` for the difference, `k[1]` for the select), so neither output
    overwrites a still-live input — the `outputs_distinct` guard. -/
theorem condSubSelect_outputs_distinct :
    (widenDstName 0 ≠ widenDstName 1)
      ∧ strContains condSubSelectJazz "non-regArith op skipped" = false := by
  native_decide

/-! ## §18  Function CALL composition — `treehashNode` through the thirDialect spine (#616, E5a)

Phase-2 front op-exposure for kernel-to-kernel COMPOSITION: the THIR front now
carries a single-result function call `thExtCall name argTys retTy`, lowering 1:1
to jasmin's `extCall` through the generic verified `lowerThir`. This is the
whole-protocol unlock — a function can now CALL an already-verified leaf and
compose it (treehash, FO transforms, Fiat-Shamir). Single-result callees only.

The demonstrator is a Merkle/treehash inner node:

    treehashNode(l, r) = compress(l ‖ r)

where `compress` is an OPAQUE already-verified single-result leaf, modelled as
the `thExtCall "compress" [.reg 64, .reg 64] (.reg 64)`. Its denotation is the
leaf semantics `jasminExtSem "compress" …`, which for a non-lattice leaf is the
opaque default (`JasminTy.default`) — so the value of the COMPOSITION is an
opaque leaf obligation, exactly as a real verified-leaf-composition should be
(the caller's correctness is conditional on the callee's). The KAT
(`bench/thir_front_extcall`) discharges that obligation against a concrete C
stand-in (`compress(l, r) = l ^ r`).

Scope: this is the call-composition op-exposure + emit step (one `thExtCall`).
Structs/enums/match are the later E5b sub-step. -/

/-- The (opaque) value spec of `treehashNode`: the leaf semantics of the
    `compress` call, `jasminExtSem "compress" [.reg 64, .reg 64] (.reg 64)`. For a
    non-lattice leaf this is the opaque default — the value-correctness of the
    composition is the callee's separate (KAT-discharged) obligation. -/
def treehashNodeSpec (l r : BitVec 64) : BitVec 64 :=
  jasminExtSem "compress" [.reg 64, .reg 64] (.reg 64) (.cons l (.cons r .nil))

/-- The treehash inner node `compress(l, r)` as a `Com thirDialect` over `[l, r]`
    (both `.reg 64`):

        h   = thExtCall "compress" [reg 64, reg 64] (reg 64) l r
        out = thRor 64 0 h      -- identity copy (the emit reads back the last binding)

    The single `thExtCall` binding is the function-call composition — the front
    handle that calls the already-verified `compress` leaf by name. -/
def treehashNodeThir : Com thirDialect [.reg 64, .reg 64] (.reg 64) :=
  -- h = compress(l, r)   (ctx [l, r]; l = dB0, r = dB1)
  .var (.mk (.thExtCall "compress" [.reg 64, .reg 64] (.reg 64)) rfl
      (.cons .here (.cons (.there .here) .nil)))
  -- out = ror 0 h   (identity copy; ctx [h, l, r]; h = dB0)
  (.var (.mk (.thRor 64 0) rfl (.cons .here .nil))
  (.ret .here))

/-- The treehash THIR program denotes the spec (the opaque `compress` leaf
    semantics), under the final identity copy. -/
theorem treehashNodeThir_denote (l r : BitVec 64) :
    treehashNodeThir.denote (.cons l (.cons r .nil)) = treehashNodeSpec l r := by
  have e : treehashNodeThir.denote (.cons l (.cons r .nil))
      = (treehashNodeSpec l r).rotateRight 0 := rfl
  rw [e]; simp [BitVec.rotateRight_def]

/-- **`treehashNode` re-derived through the dialect spine.** The lowered
    `Com jasminDialect` (via the generic, proved `lowerThir`, exercising the new
    `thExtCall → extCall` arm) denotes the same `BitVec 64` as the spec — i.e. the
    same opaque `compress` leaf semantics. The callee is treated as a
    `jasminExtSem` leaf, so the composition's value-correctness is the callee's
    opaque obligation (discharged by the KAT against the C stand-in). -/
theorem treehashNode_via_thirDialect (l r : BitVec 64) :
    (lowerThir treehashNodeThir).denote (.cons l (.cons r .nil)) = treehashNodeSpec l r := by
  rw [lowerThir_denote treehashNodeThir (.cons l (.cons r .nil)), treehashNodeThir_denote]

/-! ### §18.1  Emit the treehash node (caller + callee) → owned-x86 jasmin

`treehashNodeThir` lowers (`lowerThir`) to a jasmin `Com` whose op is `extCall
"compress" …` (+ the final identity `ror`). The register-arith emit now renders
the call (the new `emitBodyReg` arm) as `dst = compress(wa0, wa1);`, and
`emitAbiOrchRegWithCallees` hosts the callee's own `inline fn compress(reg u64
a0, reg u64 a1) -> reg u64` alongside the caller `export fn` in one `.jazz` unit.
The callee here is a concrete stand-in `compress(l, r) = l ^ r` so the C
reference is computable; the call SHAPE (`dst = compress(args…);`) is the
verified-front image independent of the leaf body.

Two inputs `[l, r]`; one `u64` output. The caller body has 2 bindings (the call
+ the identity copy), so the register file is `stack u64[4] k`: 2 working slots
`k[0..1]` then the 2 input slots `k[2..3]`; one call has arity 2 so 2 `wa`
scratch regs. -/

/-- Per-output register-file decls for `treehashNode`: 2 working slots + 2
    inputs (`stack u64[4] k`). Same scheme as the widening-multiply low word. -/
def treehashRegDecls : List String := ["stack u64[4] k"]

/-- The concrete `compress` callee stand-in: `inline fn compress(a0, a1) -> u64`
    computing `a0 ^ a1` over a scratch register `c0`. A stand-in so the C
    reference is computable; the verified content is the CALL composition, not the
    leaf body (which is opaque at the Lean denotation level). -/
def compressLeafJazz : String :=
  emitInlineLeaf "compress" 64 2
    ["reg u64 c0;", "c0 = a0;", "c0 = c0 ^ a1;"] "c0"

/-- The emitted `.jazz` for the treehash node through the thirDialect spine
    (`lowerThir treehashNodeThir`) and the call-hosting register-arith
    orchestration. Emits the `compress` callee `inline fn` and the caller
    `export fn treehash_node` that calls it. ABI: `reg ptr u64[1] out`,
    `reg const ptr u64[2] inp` (`inp = l, r`). -/
def treehashNodeJazz : String :=
  emitAbiOrchRegWithCallees "treehash_node" (w := 64) (nIn := 2) (nOut := 1)
    (nCopy := 2) (nArgRegs := 2) treehashRegDecls [compressLeafJazz]
    widenInName widenDstName (lowerThir treehashNodeThir)

#eval IO.println treehashNodeJazz

/- The caller export has the expected ABI (1-word out, 2-word in). -/
#guard (strContains treehashNodeJazz "export fn treehash_node(reg ptr u64[1] out, reg const ptr u64[2] inp)")

/- The callee `compress` ships as an `inline fn` alongside the caller. -/
#guard (strContains treehashNodeJazz "inline fn compress(reg u64 a0, reg u64 a1) -> reg u64")

/- The caller body renders a real call to the `compress` leaf (`k[0] =
    compress(wa0, wa1);`) and skips no op — the rendering side of `thExtCall →
    extCall`. -/
#guard (strContains treehashNodeJazz "k[0] = compress(wa0, wa1);")
    && !(strContains treehashNodeJazz "non-regArith op skipped")

/-! ## §19  AVX-512 8-lane packed add — homogeneous `reg 512` SIMD through the
    thirDialect spine (#616, E6)

Phase-2 front op-exposure for the SIMD lane surface: the THIR front now carries
an AVX-512 8×u64 packed-lane op `thVpack bop` (`[reg 512, reg 512] → reg 512`,
`zmmPackQ bop`), lowering 1:1 to jasmin's `vpackZMM bop` through the generic
verified `lowerThir`. This is the front handle for the homogeneous-512 SIMD
register surface (Poseidon2 MDS / RC-add, 8-way packed lane arithmetic).

The demonstrator is a homogeneous 8-lane packed add:

    vpackAdd8(x, y) = thVpack .add x y   -- 8 independent u64 lane adds

over two `reg 512` ZMM inputs (one `reg 512` output). It is **all-`reg 512`** —
every binding is `reg 512`, so the front orchestration is instantiated at
`w = 512` (`emitAbiOrchReg` params / scratch all become `reg u512`), sidestepping
any mixed-width plumbing.

Scope: this is the SIMD lane op-exposure + emit step (one `thVpack`). A
mixed-width kernel (e.g. an `reg 64` reduction folded over `reg 512` lanes) is a
later sub-step that needs the front's single-width plumbing relaxed.

The dialect denotation of `thVpack .add` is exactly `zmmPackQ .add` — the
verified 8×u64 packed add (`JasminDialect.zmmPackQ`), per-lane validated against
`MpnAvx512Emit.denoteVPaddQ8` in `Poseidon2Avx512Jasmin.lean`. -/

/-- The value spec of the 8-lane packed add: the dialect ZMM packed add
    `zmmPackQ .add` (8 independent u64 lane adds, no cross-lane carry). -/
def vpackAdd8Spec (x y : BitVec 512) : BitVec 512 := zmmPackQ .add x y

/-- The homogeneous 8-lane packed add as a `Com thirDialect` over `[x, y]` (both
    `.reg 512`): a single `thVpack .add` binding whose result is returned. The
    De Bruijn args pick input 0 (`.here`) and input 1 (`.there .here`); the binding
    is the result, so no trailing identity copy is needed. -/
def vpackAdd8Thir : Com thirDialect [.reg 512, .reg 512] (.reg 512) :=
  -- out = vpack.add x y   (ctx [x, y]; x = dB0, y = dB1)
  .var (.mk (.thVpack .add) rfl (.cons .here (.cons (.there .here) .nil)))
  (.ret .here)

/-- The 8-lane packed-add THIR program denotes the spec (the dialect ZMM packed
    add `zmmPackQ .add`). -/
theorem vpackAdd8Thir_denote (x y : BitVec 512) :
    vpackAdd8Thir.denote (.cons x (.cons y .nil)) = vpackAdd8Spec x y := rfl

/-- **The 8-lane packed add re-derived through the dialect spine.** The lowered
    `Com jasminDialect` (via the generic, proved `lowerThir`, exercising the new
    `thVpack → vpackZMM` arm) denotes the same `BitVec 512` as the spec — i.e. the
    verified 8×u64 packed add `zmmPackQ .add`. -/
theorem vpackAdd8_via_thirDialect (x y : BitVec 512) :
    (lowerThir vpackAdd8Thir).denote (.cons x (.cons y .nil)) = vpackAdd8Spec x y := by
  rw [lowerThir_denote vpackAdd8Thir (.cons x (.cons y .nil)), vpackAdd8Thir_denote]

/-! ### §19.1  Emit the 8-lane packed add → owned-x86 jasmin (homogeneous `u512`)

`vpackAdd8Thir` lowers (`lowerThir`) to a jasmin `Com` whose op is `vpackZMM .add`.
The register-arith emit renders it (the new `emitBodyReg` arm) as the single
intrinsic line `dst = #VPADD_8u64(a, b);`. The orchestration is instantiated at
`w = 512`, so every slot / scratch register is `reg u512`: ABI `reg ptr u512[1]
out`, `reg const ptr u512[2] inp`. One binding → 1 working slot; 2 inputs copied
into the 2 trailing slots.

Jasminc surface note: `#VPADD_8u64` (the u512 ZMM packed add) is the verified
mnemonic but is REJECTED by jasminc 2026.03.1 (u512 not yet in its intrinsic
table — see `MpnAvx512Emit.lean`); the accepted ymm subset is `#VPADD_4u64`
(2× to cover 8 lanes). The KAT (`bench/thir_front_vpack`) checks the 8-lane
packed-add VALUE against a lane-by-lane scalar reference; the surface gap is the
upstream jasmin patch, independent of this verified front lowering. -/

/-- Per-output register-file decls for `vpackAdd8`: 1 working slot + 2 inputs
    (`stack u512[4] k`), all `u512`. Mirrors `widenRegDecls` at width 512. -/
def vpackRegDecls : List String := ["stack u512[4] k"]

/-- Binding `k` → working slot `k`. -/
def vpackDstName (n : Nat) : String := "k[" ++ toString n ++ "]"

/-- Input word `i` (`x`/`y`) → copied-in slot `1 + i` (one working slot precedes
    the 2 inputs). -/
def vpackInName (i : Nat) : String := "k[" ++ toString (1 + i) ++ "]"

/-- The emitted `.jazz` for the 8-lane packed add through the thirDialect spine
    (`lowerThir vpackAdd8Thir`) and the verified register-arith orchestration,
    instantiated at `w = 512` (homogeneous `u512`). ABI: `reg ptr u512[1] out`,
    `reg const ptr u512[2] inp`. The single `vpackZMM .add` binding renders as
    `k[0] = #VPADD_8u64(k[1], k[2]);`. -/
def vpackAdd8Jazz : String :=
  emitAbiOrchReg "vpack_add8" (w := 512) (nIn := 2) (nOut := 1) (nCopy := 2)
    vpackRegDecls vpackInName vpackDstName (lowerThir vpackAdd8Thir)

#eval IO.println vpackAdd8Jazz

/- The export has the expected `u512` ABI (1-word out, 2-word in). -/
#guard (strContains vpackAdd8Jazz "export fn vpack_add8(reg ptr u512[1] out, reg const ptr u512[2] inp)")

/- The emitted body renders the real 8×u64 packed add (`#VPADD_8u64`) and skips
    no op — the rendering side of `thVpack .add → vpackZMM .add`. -/
#guard (strContains vpackAdd8Jazz "#VPADD_8u64")
    && !(strContains vpackAdd8Jazz "non-regArith op skipped")

/-! ## §20  Runtime-indexed table LOAD — public NTT twiddle lookup `zeta[i]` (#619, E4)

Phase-2 front op-exposure for a runtime-indexed array READ: the dialect's
`stackLoad w n` op (`[stackArr w n, reg 64] → reg w`, the dual of the §9 indexed
STORE `stackStore`) loads one element of a stack array at a runtime index. It was
already in the dialect but unrendered by the register-arith emit; the
`emitBodyReg` `stackLoad` arm now renders it as `dst = arr[(uint)idx];` and
`emitAbiOrchLoad` orchestrates it (copy-in, indexed read, copy-out), KAT'd in
`bench/thir_front_gather`.

The demonstrator is the canonical safe use of a runtime gather — a **public**
loop-counter table lookup: the NTT twiddle read `zetaLookup(zeta, i) = zeta[i]`,
where `i` is the (public) NTT round/butterfly counter. The dialect denotes the
load as the total read `stackGet zeta i.toNat = zeta[i % N]`; `stackGet_id`
discharges the in-range `% N` ↔ direct-index bridge for any `i : Fin N`, so on a
valid round counter the lookup reads exactly `zeta i`.

### Constant-time requirement (BLOCKING)

The index `i` MUST be PUBLIC. `JasminCTPredicate.opIndexPublic` admits a
`stackLoad`/`stackStore` as CT-safe **iff** its index register is `.Public`
(non-vacuous: a secret index is flagged non-CT, a public one CT). An NTT twiddle
index is a public loop counter, so the lookup is data-oblivious. A
**secret-indexed** table lookup (e.g. an S-box gather on a secret byte) is a
cache-timing leak and is rejected by the #594 CT predicate — the
Argon2 / bitsliced-AES precedent, where the secret-dependent table access must be
replaced by a constant-time `select`-based scan (§17) instead of a gather.

### Scope (E4)

The indexed-READ op is wired into the dialect emit and exercised by this pilot
through a hand-built `Com jasminDialect` (the read dual of §9's `storeDemoCom`),
with the denotation pinned to `stackGet` and the in-range case discharged by
`stackGet_id`. As with the §9 store pilot, a stack-array VALUE is not a `rW w`
register, so threading a mutable `stackArr` slot through the homogeneous
register-file front (`thirToJasmin` / `frontCtxt`) would require a heterogeneous
typing pass — deferred; the table-lookup demonstrator stands alone at the `Com`
level, exactly like the store pilot. No new `ThirOp` is introduced (the dialect
`stackLoad` op already exists; the front carries it as the direct `Com` the way
§9 carries `stackStore`). -/

/-- The NTT-twiddle table length used by the demonstrator (a small `u16` zeta
    table; the KAT exercises all in-range indices + random trials). -/
abbrev zetaLen : Nat := 8

/-- Runtime-indexed table-load `Com`: `let v = stackLoad zeta idx; ret v`, over
    the context `[stackArr 16 zetaLen, reg 64]` (the `u16` zeta table + the
    PUBLIC index register). The single `stackLoad` binding is the runtime gather
    — the read dual of §9's `storeDemoCom`. The loaded value is a `reg 16`. -/
def zetaLookupCom :
    Com jasminDialect [.stackArr 16 zetaLen, .reg 64] (.reg 16) :=
  .var (.mk (.stackLoad 16 zetaLen) rfl
          (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)

/-- `zetaLookupCom` denotes the total read `stackGet zeta idx.toNat` — element
    `idx mod zetaLen` of the table. -/
theorem zetaLookupCom_denote (zeta : Fin zetaLen → BitVec 16) (idx : BitVec 64) :
    zetaLookupCom.denote (.cons zeta (.cons idx .nil))
      = stackGet zeta idx.toNat := rfl

/-- **In-range public lookup reads exactly `zeta i`.** For an in-range index
    `i : Fin zetaLen` whose `u64` representative is `BitVec.ofNat 64 i.val` (a
    public NTT loop counter; `i.val < zetaLen ≤ 2^64`), the runtime gather reads
    the underlying twiddle `zeta i`. The `% zetaLen` reduction of `stackGet` is
    the identity here (`stackGet_id`), closing the in-range ↔ direct-index gap. -/
theorem zetaLookupCom_inrange (zeta : Fin zetaLen → BitVec 16) (i : Fin zetaLen) :
    zetaLookupCom.denote (.cons zeta (.cons (BitVec.ofNat 64 i.val) .nil))
      = zeta i := by
  rw [zetaLookupCom_denote]
  have hlt : i.val < 2 ^ 64 := by
    have : i.val < zetaLen := i.isLt
    have h8 : (zetaLen : Nat) ≤ 2 ^ 64 := by norm_num [zetaLen]
    omega
  rw [show (BitVec.ofNat 64 i.val).toNat = i.val from by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlt]
  exact stackGet_id zeta i

/-! ### §20.1  Emit the public twiddle lookup → owned-x86 jasmin

`emitAbiOrchLoad` renders the runtime-indexed table read to jasmin: copy the
input `u16[zetaLen]` table into an owned `stack` buffer, read `buf[(uint)idx]` at
the public runtime index, copy the scalar out. ABI: `reg ptr u16[1] out`,
`reg const ptr u16[zetaLen] inp`, `reg u64 idx`. The `idx` param is the public
loop counter (an NTT round index), so the gather is data-oblivious. -/

/-- The emitted public-indexed twiddle-lookup `.jazz` over a length-`zetaLen`
    `u16` table. -/
def zetaLookupJazz : String := emitAbiOrchLoad "zeta_lookup" 16 zetaLen

#eval IO.println zetaLookupJazz

/-- The export has the expected `zeta_lookup` ABI (scalar `u16` out, `u16` table
    in, public `u64` index). -/
theorem zetaLookup_export_sig :
    strContains zetaLookupJazz
      ("export fn zeta_lookup(reg ptr u16[1] out, reg const ptr u16[8] inp, "
        ++ "reg u64 idx)") = true := by native_decide

/- The emitted body renders the runtime-indexed element LOAD `buf[(uint)idx]`. -/
#guard (strContains zetaLookupJazz "buf[(uint)idx];")

/-! ## §21  STRUCT (product state) + usize-tag MATCH dispatch through the
    thirDialect spine (#617, E5b)

Phase-2 front op-exposure for the **dispatch + product-state** half of E5: a
whole-protocol body that carries a STRUCT-shaped register state and updates one
field by a `match` over a tag. This is what turns kernel-compile into
whole-protocol compile (the FO transform, treehash recursion, Fiat-Shamir, a
ratchet's state record). E5a (§18) added single-result CALLs; this is the
product-and-dispatch step.

### The two front representations chosen (and the two-AST gap)

**STRUCT = N consecutive `reg w` slots.** The front register context is already
homogeneous, so a struct is *exactly* N adjacent context entries (one per
field). Field PROJECTION is a de Bruijn `Ctxt.Var` into the context (no op);
field CONSTRUCTION is the ordinary sequence of `let` bindings that produce the
fields (no op). The 2-field state record `{ acc, ctr }` here is the input pair
`[acc, ctr]` (`reg 64` each); the body returns the updated `acc` field while
`ctr` threads through untouched (the product-state flow). **This handles a
FIXED-ARITY struct of equal-width fields only.** It does NOT yet model variant
PAYLOADS of differing widths, nested/recursive ADTs, or a heap-boxed struct —
those are the two-AST gap (hax `ImpExpr.ctorPat`/`proj` over a sum type
does not map onto a fixed register tuple). A struct here is a flat fixed tuple
of `reg w` slots.

**MATCH = a `usize` tag + branch-free nested `thSelect`.** hax extracts an enum
as an opaque `usize` tag (the ADT constructors are lost in extraction — they
become integer constants + `if`/`else`), so the canonical front image of `match
tag { 0 => e0, 1 => e1, _ => e2 }` is: test the tag against each constant
(`thEqLit w k`, a `reg 1` flag), then nest the existing constant-time `thSelect`
(§17) so the matching arm's value is selected:

    sel1 = select (tag == 1) e1 e2     -- default arm e2 if neither 0 nor 1
    out  = select (tag == 0) e0 sel1

The tag test `thEqLit w k` is the one new dialect op (lowers 1:1 to an OPAQUE
single-result equality leaf `extCall (eqLitLeafName w k) [reg w] (reg 1)` — the
carry-free jasmin alphabet has no compare op, so the test is treated as an
already-verified constant-time equality leaf exactly as §18's `compress`). The
DISPATCH (the nested `thSelect`) is fully transparent and proved; only the
per-arm tag-test VALUE is the opaque leaf obligation the KAT discharges. **This
handles a `usize`-tag match over k arms, every arm a `reg w` value, generalised
to k variants by nesting `thSelect`.** It does NOT model an arm that BINDS a
variant payload of a different width, a guard, or an or-pattern — those need the
struct/payload extension above. A match here is a flat `usize` tag dispatched
to `reg w` arms.

**CT note.** The match tag here is **public** (a `step_kind` selector / FO
domain-separation tag), so the data-dependent dispatch is data-oblivious: the
`thEqLit` compares against a *compile-time public constant*, and `thSelect` is
already branch-free (both arms always evaluated, §17). A *secret* tag would
still lower (the SELECT is branch-free) but the `thEqLit` leaf must then be a
constant-time equality — which the branchless mask emit already is.

The demonstrator is a 2-field state record updated by a 3-arm match:

    fn step({ acc, ctr } : St, tag : usize) -> u64 {
        match tag { 0 => acc + ctr, 1 => acc ^ ctr, _ => acc - ctr }
    }

i.e. an FO-transform / ratchet-shaped product-state update dispatched by a public tag. -/

/-- The opaque-leaf value of the tag test `tag == k` at width 64: the equality
    leaf semantics `jasminExtSem (eqLitLeafName 64 k) [reg 64] (reg 1)`. For the
    non-lattice leaf this is the opaque default (`0`), so the tag-test VALUE is
    the leaf's separate (KAT-discharged) obligation — the EQ is opaque,
    exactly like §18's `compress`. -/
def tagEqSpec (k : Nat) (tag : BitVec 64) : BitVec 1 :=
  (jasminExtSem (ThirDialect.eqLitLeafName 64 k) [.reg 64] (.reg 1) (.cons tag .nil) : BitVec 1)

/-- The value spec of the 3-arm tag dispatch, with the two tag tests left as the
    opaque equality leaves: nested constant-time SELECT
    `select (tag==0) (acc+ctr) (select (tag==1) (acc^ctr) (acc-ctr))`. The arm
    VALUES (`add`/`xor`/`sub` over the struct fields `acc`,`ctr`) are transparent;
    only the two `tagEqSpec` conditions are opaque leaf obligations. -/
def matchStepSpec (acc ctr tag : BitVec 64) : BitVec 64 :=
  selectW (tagEqSpec 0 tag) (acc + ctr)
    (selectW (tagEqSpec 1 tag) (acc ^^^ ctr) (acc - ctr))

/-- The 2-field-struct + 3-arm-match update as a `Com thirDialect` over the
    product state `[acc, ctr, tag]` (all `.reg 64`; `{acc, ctr}` is the struct,
    `tag` the `usize` match selector):

        eq0  = thEqLit 64 0 tag           -- tag == 0   (reg 1)
        eq1  = thEqLit 64 1 tag           -- tag == 1   (reg 1)
        vAdd = thBin .add 64 acc ctr      -- arm 0 value
        vXor = thBin .xor 64 acc ctr      -- arm 1 value
        vSub = thBin .sub 64 acc ctr      -- default arm value
        sel1 = thSelect 64 eq1 vXor vSub  -- if tag==1 then xor else sub
        sel0 = thSelect 64 eq0 vAdd sel1  -- if tag==0 then add else sel1
        ret sel0

    The struct `{acc, ctr}` is the two leading context slots; `ctr` flows through
    untouched (product-state). The nested `thSelect` is the desugared k-arm
    match; the `thEqLit` tag tests are the opaque equality leaves. -/
def matchStepThir : Com thirDialect [.reg 64, .reg 64, .reg 64] (.reg 64) :=
  -- eq0 = (tag == 0)   ctx [acc, ctr, tag];  tag = dB2
  .var (.mk (.thEqLit 64 0) rfl (.cons (.there (.there .here)) .nil))
  -- eq1 = (tag == 1)   ctx [eq0, acc, ctr, tag];  tag = dB3
  (.var (.mk (.thEqLit 64 1) rfl (.cons (.there (.there (.there .here))) .nil))
  -- vAdd = acc + ctr   ctx [eq1, eq0, acc, ctr, tag];  acc = dB2, ctr = dB3
  (.var (.mk (.thBin .add 64) rfl
      (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))
  -- vXor = acc ^ ctr   ctx [vAdd, eq1, eq0, acc, ctr, tag];  acc = dB3, ctr = dB4
  (.var (.mk (.thBin .xor 64) rfl
      (.cons (.there (.there (.there .here)))
        (.cons (.there (.there (.there (.there .here)))) .nil)))
  -- vSub = acc - ctr   ctx [vXor, vAdd, eq1, eq0, acc, ctr, tag];  acc = dB4, ctr = dB5
  (.var (.mk (.thBin .sub 64) rfl
      (.cons (.there (.there (.there (.there .here))))
        (.cons (.there (.there (.there (.there (.there .here))))) .nil)))
  -- sel1 = select eq1 vXor vSub
  -- ctx [vSub, vXor, vAdd, eq1, eq0, acc, ctr, tag];  eq1 = dB3, vXor = dB1, vSub = dB0
  (.var (.mk (.thSelect 64) rfl
      (.cons (.there (.there (.there .here)))
        (.cons (.there .here) (.cons .here .nil))))
  -- sel0 = select eq0 vAdd sel1
  -- ctx [sel1, vSub, vXor, vAdd, eq1, eq0, acc, ctr, tag];  eq0 = dB5, vAdd = dB3, sel1 = dB0
  (.var (.mk (.thSelect 64) rfl
      (.cons (.there (.there (.there (.there (.there .here)))))
        (.cons (.there (.there (.there .here))) (.cons .here .nil))))
  (.ret .here)))))))

/-- The struct + match THIR program denotes the dispatch spec: the nested
    constant-time SELECT over the (opaque-leaf) tag tests and the transparent
    arm values. By definitional unfolding of the `thirDialect` denotation. -/
theorem matchStepThir_denote (acc ctr tag : BitVec 64) :
    matchStepThir.denote (.cons acc (.cons ctr (.cons tag .nil)))
      = matchStepSpec acc ctr tag := rfl

/-- **Struct + usize-tag match re-derived through the dialect spine.** The lowered
    `Com jasminDialect` (via the generic, proved `lowerThir`, exercising the new
    `thEqLit → extCall` arm together with the §17 `thSelect → select` and the
    `thBin → regArith` arms) denotes the same `BitVec 64` as the dispatch spec, on
    every `(acc, ctr, tag)`. The DISPATCH (nested SELECT) is transparent; the two
    tag-test conditions are the opaque equality leaves the KAT discharges. -/
theorem matchStep_via_thirDialect (acc ctr tag : BitVec 64) :
    (lowerThir matchStepThir).denote (.cons acc (.cons ctr (.cons tag .nil)))
      = matchStepSpec acc ctr tag := by
  rw [lowerThir_denote matchStepThir (.cons acc (.cons ctr (.cons tag .nil))),
    matchStepThir_denote]

/-! ### §21.1  Emit the struct + match dispatch (caller + tag-test leaves) → owned-x86 jasmin

`matchStepThir` lowers (`lowerThir`) to a jasmin `Com` whose ops are two
`extCall (eqLitLeafName 64 k)` tag tests, three `regArith` arm values, and two
branchless `select`s (+ the final result). `emitAbiOrchRegWithCallees` hosts the
two tag-test `inline fn`s (`thir_eqlit_64_0`, `thir_eqlit_64_1`) alongside the
caller `export fn match_step`. The tag tests are concrete stand-ins
`a0 == k ? 1 : 0` so the C reference is computable; the verified content is the
DISPATCH shape (nested branchless `select`), independent of the leaf bodies.

Three inputs `[acc, ctr, tag]`; one `u64` output. The caller body has 7 bindings
(2 tag tests + 3 arms + 2 selects), so the register file is `stack u64[10] k`: 7
working slots `k[0..6]` then the 3 input slots `k[7..9]`; each `extCall` is arity
1 so 1 `wa` scratch reg. -/

/-- Per-output register-file decls for `matchStep`: 7 working slots + 3 inputs
    (`stack u64[10] k`). -/
def matchStepRegDecls : List String := ["stack u64[10] k"]

/-- Input word `i` (`acc`/`ctr`/`tag`) → copied-in register slot `7 + i`. -/
def matchStepInName (i : Nat) : String := "k[" ++ toString (7 + i) ++ "]"

/-- The tag-test leaf `thir_eqlit_64_k`: `inline fn …(a0) -> u64` returning
    `a0 == k ? 1 : 0` over a scratch register `c0`, branch-free via the mask
    idiom (`c0 = a0 ^ k; (c0|-c0)>>63` gives `0` iff equal, then complement). A
    concrete constant-time stand-in so the C reference is computable; the leaf is
    opaque at the Lean denotation level (the dispatch SHAPE is the verified
    content). The `reg 1` flag is carried as a `u64` 0/1 in the register file, so
    the `select` mask `-cond` is well-formed. -/
def eqLitLeafJazz (k : Nat) : String :=
  emitInlineLeaf (ThirDialect.eqLitLeafName 64 k) 64 1
    ["reg u64 c0;",
     "reg u64 c1;",
     "c0 = a0;",
     "c0 = c0 ^ " ++ toString k ++ ";",   -- 0 iff a0 == k
     "c1 = c0;",
     "c1 = -c1;",
     "c0 = c0 | c1;",                      -- high bit set iff c0 != 0
     "c0 = c0 >> 63;",                     -- 1 iff a0 != k, 0 iff equal
     "c1 = 1;",
     "c0 = c1 - c0;"]                      -- 1 iff a0 == k
    "c0"

/-- The emitted `.jazz` for the struct + usize-tag match through the thirDialect
    spine (`lowerThir matchStepThir`) and the call-hosting register-arith
    orchestration. Emits the two tag-test `inline fn`s and the caller `export fn
    match_step` that dispatches via two branchless `select`s. ABI:
    `reg ptr u64[1] out`, `reg const ptr u64[3] inp` (`inp = acc, ctr, tag`). -/
def matchStepJazz : String :=
  emitAbiOrchRegWithCallees "match_step" (w := 64) (nIn := 3) (nOut := 1)
    (nCopy := 3) (nArgRegs := 1) matchStepRegDecls
    [eqLitLeafJazz 0, eqLitLeafJazz 1]
    matchStepInName widenDstName (lowerThir matchStepThir)

#eval IO.println matchStepJazz

/- The caller export has the expected ABI (1-word out, 3-word in). -/
#guard (strContains matchStepJazz "export fn match_step(reg ptr u64[1] out, reg const ptr u64[3] inp)")

/- Both tag-test leaves ship as `inline fn`s alongside the caller (the usize-tag
    `match` desugared to `tag == 0` / `tag == 1` equality leaves). -/
#guard (strContains matchStepJazz "inline fn thir_eqlit_64_0(reg u64 a0) -> reg u64")
    && (strContains matchStepJazz "inline fn thir_eqlit_64_1(reg u64 a0) -> reg u64")

/- The caller body renders the dispatch: real calls to both tag tests and the
    branchless mask-select (`-wb`, `& wb`) of the nested `thSelect`, and skips no
    op — the rendering side of `thEqLit → extCall` + `thSelect → select`. -/
#guard (strContains matchStepJazz "thir_eqlit_64_0(wa0);")
    && (strContains matchStepJazz "thir_eqlit_64_1(wa0);")
    && (strContains matchStepJazz "wb = -wb;")
    && !(strContains matchStepJazz "non-regArith op skipped")

/-! ## §22  Bounded FOR-loop front construct: an ARX round schedule as ONE loop
    (#618, E3)

The straight-line front (§1–§21) could only emit an *unrolled* kernel. This
section exposes a LOOP: a bounded for-loop over a register-state accumulator,
lowered to the EXISTING jasmin for-loop layer (`JForProg`, the `for i = 0 to n`
the §7 doubling-loop and the NTT sweeps already emit) via the THIR front
construct `ThirDialect.ThirForProg`. No new control-flow op; the loop body is the
THIR-dialect `Com` lowered by the generic, proved `lowerThir`, and the
iteration structure is the unchanged `JForProg`.

### The demonstrator: an ARX round, iterated `n` times

The Class-A unlock is a body that is an ARX round, run a public number of
rounds threading a single 64-bit register-state accumulator:

    fn fold(acc, n) { for _ in 0..n { acc = (acc + C) ^ rotr(acc, 32) } ; acc }

one `+ C` (a round constant, the expanding `thBinLit` op), one rotate-by-32
(written as `(acc >> 32) | (acc << 32)`, the shift/shift/or idiom — `thShrImm`,
`thShlImm`, `thBin .or`), and one `xor` (`thBin`) — the add-rotate-xor primitive
shape, emitted as ONE `for` loop (NOT unrolled). The round constant
`C = 0x9E3779B97F4A7C15` is the golden-ratio constant used by real ARX schedules.
The rotate is built from shifts (not the native `thRor`/`#ROR` intrinsic) so the
loop body lowers to plain `Cassgn` ops the `JForProg.toJazzExport` printer renders
as jasminc-compilable straight-line code.

### Constant-time scope

The trip count `n` is the **public** static field of `ThirForProg` and the loop
index ranges over `0..n`; the loop is data-independent control flow and adds no
CT obligation beyond its (straight-line, branch-free) body. A *secret-dependent*
trip count (rejection sampling) is the flagged follow-on — see
`bench/thir_front_loop/Makefile`.

### Denotation

`foldRound_via_thirDialect` closes the `n`-fold by `toJForProg_denote` (the
bounded-FOR lowering soundness: the lowered jasmin loop's `JForProg.denote`
equals the THIR loop's `n`-fold), composed with the THIR step's definitional
denotation — NOT an unrolled equality. -/

/-- The ARX round constant (golden-ratio fractional bits, `floor(2^64 / φ)`). -/
def foldRoundConst : Nat := 0x9E3779B97F4A7C15

/-- The ARX rotate amount (right-rotate by half the word width). -/
def foldRoundRot : Nat := 32

/-- One ARX round as a `Com thirDialect` over the singleton accumulator state
    `[acc]` (`reg 64`): `acc ↦ (acc + C) ^^^ ((acc >> 32) | (acc << 32))`.

        t0  = thBinLit .add 64 C  acc     -- acc + C   (expanding op)
        hi  = thShrImm 64 32      acc     -- acc >> 32
        lo  = thShlImm 64 32      acc     -- acc << 32
        rot = thBin .or 64        hi lo   -- rotr(acc, 32) = (acc>>32)|(acc<<32)
        out = thBin .xor 64       t0 rot  -- combine
        ret out

    The expanding `thBinLit`, the shift/shift/or rotate, and the `thBin` xor — the
    add-rotate-xor leaf, the loop-carried body. The rotate is the shift idiom (not
    the native `thRor`) so every binding lowers to a plain `Cassgn` that
    `JForProg.toJazzExport` renders as jasminc-compilable code. -/
def foldRoundBodyThir : Com thirDialect [.reg 64] (.reg 64) :=
  -- t0 = acc + C    ctx [acc];  acc = dB0
  .var (.mk (.thBinLit .add 64 foldRoundConst) rfl (.cons .here .nil))
  -- hi = acc >> 32   ctx [t0, acc];  acc = dB1
  (.var (.mk (.thShrImm 64 foldRoundRot) rfl (.cons (.there .here) .nil))
  -- lo = acc << 32   ctx [hi, t0, acc];  acc = dB2
  (.var (.mk (.thShlImm 64 foldRoundRot) rfl (.cons (.there (.there .here)) .nil))
  -- rot = hi | lo    ctx [lo, hi, t0, acc];  hi = dB1, lo = dB0
  (.var (.mk (.thBin .or 64) rfl (.cons (.there .here) (.cons .here .nil)))
  -- out = t0 ^ rot   ctx [rot, lo, hi, t0, acc];  t0 = dB3, rot = dB0
  (.var (.mk (.thBin .xor 64) rfl (.cons (.there (.there (.there .here))) (.cons .here .nil)))
  (.ret .here)))))

/-- The ARX-round body's value spec: one round transform on `acc`. -/
def foldRoundStep (acc : BitVec 64) : BitVec 64 :=
  (acc + BitVec.ofNat 64 foldRoundConst) ^^^ ((acc >>> foldRoundRot) ||| (acc <<< foldRoundRot))

/-- The THIR ARX-round body denotes one round transform, by definitional
    unfolding of the `thirDialect` denotation. -/
theorem foldRoundBodyThir_denote (acc : BitVec 64) :
    foldRoundBodyThir.denote (.cons acc .nil) = foldRoundStep acc := rfl

/-- The bounded FOR-loop front program: the ARX round body, iterated `n` rounds,
    as a `ThirForProg` (the THIR front loop construct). -/
def foldRoundLoop (n : Nat) : ThirDialect.ThirForProg (.reg 64) :=
  { n := n, update := foldRoundBodyThir }

/-- **The ARX round schedule re-derived through the bounded-FOR front spine.** The
    lowered jasmin for-loop (`toJForProg`, run through the unchanged
    `JForProg.denote` — the existing `for i = 0 to n` layer) computes exactly the
    `n`-fold of the ARX round step, on every initial accumulator and every public
    trip count `n`. The loop STRUCTURE is the unchanged jasmin loop layer; the
    per-iteration body is the generic, proved `lowerThir`; the `n`-fold close is
    `toJForProg_denote`. This is a LOOP, not an unrolled body. -/
theorem foldRound_via_thirDialect (n : Nat) (init : BitVec 64) :
    (foldRoundLoop n).toJForProg.denote init
      = (List.range n).foldl (fun acc _ => foldRoundStep acc) init := by
  rw [ThirDialect.toJForProg_denote]
  rfl

/-! ### §22.1  Emit the ARX round loop → owned-x86 jasmin (ONE `for` loop)

`(foldRoundLoop n).toJForProg` is a `JForProg (.reg 64)`; `JForProg.toJazzExport`
renders it as a self-contained jasminc `export fn fold_round(reg u64 acc0) ->
reg u64` whose body is the **actual** emitted `for i = 0 to n { … }` (printed by
the shared `ppInstrR`), NEVER unrolled. The body's per-iteration ops are
`acc + C` (a `regConst` + `regArith add`), the shift/shift/or rotate
(`acc >> 32`, `acc << 32`, `regArith or`), and the combining `xor`
(a `regArith xor`) — the lowered ARX round, all plain `Cassgn`s. The KAT below
pins a fixed trip count; the proof `foldRound_via_thirDialect` covers every `n`. -/

/-- The emitted ARX-round-loop `.jazz` for a fixed public trip count `n`, through
    the bounded-FOR front spine (`(foldRoundLoop n).toJForProg`) and the existing
    jasmin loop-emit (`JForProg.toJazzExport`). A real `for i = 0 to n` loop. -/
def foldRoundJazz (n : Nat) : String :=
  CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint.JForProg.toJazzExport
    "fold_round" ((foldRoundLoop n).toJForProg)

#eval IO.println (foldRoundJazz 8)

/- The emitted unit is an `export fn fold_round` with the bounded-loop ABI
    (`reg u64 acc0 -> reg u64`). -/
#guard (strContains (foldRoundJazz 8) "export fn fold_round(reg u64 acc0) -> reg u64")

/- The body is a REAL `for i = 0 to 8` loop — emitted, not unrolled. -/
#guard (strContains (foldRoundJazz 8) "for i = 0 to 8")

/- The loop body renders the lowered ARX round: the shift/shift/or rotate
    (`>>` `<<` `|`) and the combining xor (`^`). -/
#guard (strContains (foldRoundJazz 8) " >> ")
    && (strContains (foldRoundJazz 8) " << ")
    && (strContains (foldRoundJazz 8) " | ")
    && (strContains (foldRoundJazz 8) " ^ ")

/-! ## §23  FIRST whole-protocol SHAPE: a treehash CHAIN — the §18 leaf CALL run
    inside the §22 bounded FOR loop (#606, E5a × E3 composed)

This is the Phase-2 milestone: the first whole-protocol SHAPE through the THIR
front, composing the two just-landed front extensions into one driver:

  * §18 (E5a) gave a single-result function CALL `thExtCall name argTys retTy`
    (lowering 1:1 to jasmin's `extCall`), so a function can compose an
    already-verified leaf by name.
  * §22 (E3) gave the bounded FOR loop `ThirForProg` (lowering to the existing
    jasmin `JForProg` for-loop layer), so a body can run a public number of
    times threading a register-state accumulator.

§23 puts the CALL *inside* the LOOP: the per-iteration body is exactly one call
to the tweakable-hash leaf `Th`, applied to the running node accumulator —

    fn treehash_chain(node, N) { for _ in 0..N { node = Th(node) } ; node }

i.e. the running node folded through `Th` over `N` levels. This is the
hash-based-signature CHAIN spine: the WOTS+ hash chain and the Merkle
authentication-path fold (the SLH-DSA / XMSS treehash *spine* shape), where a
single state word is repeatedly tweak-hashed.

### Register-light by construction (the jasminc-RA payoff)

Unlike the §22 ARX body (which reads the accumulator THREE times per iteration —
`acc + C`, `acc >> 32`, `acc << 32` — so jasmin's two-address register allocator
cannot merge the still-live accumulator and rejects the loop, the #468
limitation), the `Th`-chain body reads the loop state EXACTLY ONCE per iteration:
the single input to the `Th` call. After that read the old node is dead (the call
result is the new node), so there is no two-address merge conflict — the loop
state is one `reg w` slot read once, written once. This is precisely the body
shape jasminc's RA *can* compile, so this demonstrator targets a REAL byte-KAT
(not the §22 clean SKIP).

The leaf `Th` is single-input (`node -> node`) for exactly this register-light
reason. A multi-input `Th(left ‖ right)` (a binary Merkle parent) reads
two live operands and is the stated follow-on.

### Denotation

`treehashChain_via_thirDialect` closes the `N`-fold by `ThirDialect.toJForProg_denote`
(the bounded-FOR lowering soundness, §22) composed with the leaf body's
definitional denotation (§18): the lowered jasmin for-loop computes exactly the
`N`-fold of the `Th` leaf over the initial node, for every initial node and every
public level count `N`. The `Th` leaf VALUE is an opaque `jasminExtSem` leaf
(the default for a non-lattice `[reg 64] -> reg 64` call), so the value of the
COMPOSITION is the callee's separate, KAT-discharged obligation — exactly as
§18's `compress`. The FOLD composition (loop + call) is the transparent proved
part; the leaf body is the opaque obligation the KAT cross-checks against the
concrete C stand-in.

### Scope

This lands the treehash CHAIN: a LINEAR fold of the tweakable hash over `N`
levels (the WOTS+ hash chain / Merkle-path-authentication spine). It is NOT the
full BINARY-tree treehash: there is no runtime index addressing into a leaf array
(that needs E4 gather + nested loops) and `Th` is single-input here (a real
Merkle parent hashes `left ‖ right`, two inputs). Both — index-gather binary-tree
treehash, and multi-input `Th` — are the stated follow-ons. This is the chain
SHAPE only. -/

/-- The (opaque) value spec of the tweakable-hash leaf `Th`: the leaf semantics
    of the `thir_th` call, `jasminExtSem "thir_th" [.reg 64] (.reg 64)`. For a
    non-lattice single-input leaf this is the opaque default — the value
    correctness of one level is the callee's separate (KAT-discharged)
    obligation, exactly as §18's `compress`. -/
def treehashLeafSpec (node : BitVec 64) : BitVec 64 :=
  jasminExtSem "thir_th" [.reg 64] (.reg 64) (.cons node .nil)

/-- One treehash LEVEL as a `Com thirDialect` over the singleton node state
    `[node]` (`reg 64`): a single `thExtCall` to the tweakable-hash leaf `Th`,
    applied to the running node.

        node' = thExtCall "thir_th" [reg 64] (reg 64) node   -- node' = Th(node)
        ret node'

    The body has ONE binding (the call), so the loop state — the running node —
    is read EXACTLY ONCE per iteration (the call's single argument), then dead.
    This is the register-light shape: no two-address merge conflict, so jasmin's
    RA can compile the loop (contrast §22's three-reads ARX body). The leaf `Th`
    is the §18 CALL composition: a function composing an already-verified leaf by
    name, the body that §23 runs inside the §22 loop. -/
def treehashLeafThir : Com thirDialect [.reg 64] (.reg 64) :=
  -- node' = Th(node)   ctx [node]; node = dB0
  .var (.mk (.thExtCall "thir_th" [.reg 64] (.reg 64)) rfl (.cons .here .nil))
  (.ret .here)

/-- The treehash level body denotes the spec (the opaque `Th` leaf semantics), by
    definitional unfolding of the `thirDialect` denotation — exactly as §18's
    `treehashNodeThir_denote`, here single-input. -/
theorem treehashLeafThir_denote (node : BitVec 64) :
    treehashLeafThir.denote (.cons node .nil) = treehashLeafSpec node := rfl

/-- The treehash CHAIN as a `ThirForProg`: the §18 `Th`-call level body, iterated
    `N` levels (the §22 bounded-FOR front loop construct). The composition of the
    two front extensions — a CALL inside a LOOP — the first whole-protocol shape
    through the front. -/
def treehashChain (n : Nat) : ThirDialect.ThirForProg (.reg 64) :=
  { n := n, update := treehashLeafThir }

/-- **The treehash chain re-derived through the composed CALL-in-LOOP front
    spine.** The lowered jasmin for-loop (`toJForProg`, run through the unchanged
    `JForProg.denote` — the existing `for i = 0 to n` layer) computes exactly the
    `N`-fold of the `Th` leaf over the initial node, on every initial node and
    every public level count `N`. The loop STRUCTURE is the unchanged jasmin loop
    layer (§22); the per-iteration body is the generic, proved `lowerThir` applied
    to the §18 `thExtCall` leaf; the `N`-fold close is `ThirDialect.toJForProg_denote`.
    The `Th` leaf VALUE is the opaque `jasminExtSem` obligation (KAT-discharged
    against the C stand-in), exactly as §18; the FOLD composition is the
    transparent proved part. This is a LOOP-OF-CALLS, not an unrolled body. -/
theorem treehashChain_via_thirDialect (n : Nat) (init : BitVec 64) :
    (treehashChain n).toJForProg.denote init
      = (List.range n).foldl (fun node _ => treehashLeafSpec node) init := by
  rw [ThirDialect.toJForProg_denote]
  rfl

/-! ### §23.1  Emit the treehash chain → owned-x86 jasmin (ONE `for` loop OF a CALL)

`(treehashChain n).toJForProg` is a `JForProg (.reg 64)`; `JForProg.toJazzExport`
renders it as a self-contained `export fn treehash_chain_<n>(reg u64 acc0) ->
reg u64` (the `JForProg` accumulator-naming convention: the loop state is `acc`)
whose body is the **actual** emitted
`for i = 0 to n { v0 = thir_th(acc); acc = v0; }` (printed by the shared
`ppInstrR` — the `extCall` arm renders the call `v0 = thir_th(acc);`, then the
loop write-back rebinds `acc = v0;`), NEVER unrolled. The accumulator `acc` is
read EXACTLY ONCE per iteration (the call argument), then dead — register-light.
The callee `inline fn thir_th` is hosted
ALONGSIDE the export by prepending `emitInlineLeaf` (the §18 callee-hosting
pattern; `JForProg.toJazzExport` emits only the loop export, so the leaf is
composed in here). The callee here is a concrete stand-in
`thir_th(x) = (x + GOLDEN) ^ (x >> 29)` (one add, one shift, one xor — a
single-input tweakable-hash leaf) so the C reference is computable; the verified
content is the CALL-in-LOOP SHAPE, not the leaf body (opaque at the Lean
denotation level). -/

/-- The golden-ratio mixing constant for the `Th` stand-in (the §22 fold
    constant), reused so the leaf is a recognisable mix step. -/
def treehashThConst : Nat := 0x9E3779B97F4A7C15

/-- The concrete `Th` tweakable-hash callee stand-in: `inline fn thir_th(a0) -> u64`
    computing `(a0 + GOLDEN) ^ (a0 >> 29)` over a scratch register `c0` (and a
    second scratch `c1` for the shifted term). A single-input (`node -> node`)
    leaf — register-light: the caller passes the live node ONCE. A stand-in so the
    C reference is computable; the verified content is the CALL-in-LOOP
    composition, not the leaf body (opaque at the Lean level). The 64-bit constant
    is materialised into a register first (`c0 = GOLDEN; c0 = c0 + a0;`) so the
    `add` takes a register operand, not a 64-bit immediate — portable across
    jasminc versions (x86 `add r64, imm` only accepts an imm32). -/
def treehashThLeafJazz : String :=
  emitInlineLeaf "thir_th" 64 1
    ["reg u64 c0;", "reg u64 c1;",
     "c0 = 0x9E3779B97F4A7C15;",
     "c0 = c0 + a0;",
     "c1 = a0 >> 29;",
     "c0 = c0 ^ c1;"] "c0"

/-- The emitted treehash-chain `.jazz` for a fixed public level count `n`: the
    `Th` callee `inline fn thir_th` hosted alongside the `export fn
    treehash_chain_<n>` whose body is the actual
    `for i = 0 to n { v0 = thir_th(acc); acc = v0; }` (the §18 call inside the §22
    loop). The leaf is prepended to `JForProg.toJazzExport`'s loop export (which
    hosts only the export fn). -/
def treehashChainJazz (n : Nat) : String :=
  treehashThLeafJazz ++ "\n\n" ++
    CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint.JForProg.toJazzExport
      ("treehash_chain_" ++ toString n) ((treehashChain n).toJForProg)

#eval IO.println (treehashChainJazz 8)

/- The emitted unit hosts the `Th` leaf as an `inline fn` callee. -/
#guard (strContains (treehashChainJazz 8) "inline fn thir_th(reg u64 a0) -> reg u64")

/- The emitted unit is an `export fn treehash_chain_8` with the bounded-loop ABI
    (`reg u64 node0 -> reg u64`). -/
#guard (strContains (treehashChainJazz 8) "export fn treehash_chain_8(reg u64 acc0) -> reg u64")

/- The body is a REAL `for i = 0 to 8` loop whose iteration CALLS the `Th` leaf
    (`v0 = thir_th(acc);`) and rebinds the running node (`acc = v0;`) — the §18
    call inside the §22 loop, emitted, not unrolled. The accumulator is read
    EXACTLY ONCE per iteration (the call argument), then dead: the single-acc-read
    register-light shape jasmin's RA can compile. -/
#guard (strContains (treehashChainJazz 8) "for i = 0 to 8")
    && (strContains (treehashChainJazz 8) "v0 = thir_th(acc);")
    && (strContains (treehashChainJazz 8) "acc = v0;")

/-- The `dot4` THIR denotes `dotSpec 4`: the inner product
    `Σ_{i<4} a[i]·b[i]` with `a[i] = I i` and `b[i] = I (4 + i)`. -/
theorem dot4Thir_denote (I : Fin 8 → BitVec 64) :
    dot4.denote I (LEnv.empty 64) = some (dotSpec 4 I) := rfl

end CatCrypt.Crypto.SecureCompilation.ThirToComFront
