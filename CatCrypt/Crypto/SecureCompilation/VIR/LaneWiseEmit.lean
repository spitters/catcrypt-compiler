/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Batch8Emit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# Lane-wise 32-bit programs, widened eight ways by `batch8`

A builder for straight-line programs over 32-bit words that apply the same
arithmetic to many independent values, and the lattice-coefficient kernels
written with it. A program is written once for one 32-bit lane; `batch8`
(`Optimizer.Batch8`) widens every covered op to the packed YMM op computing it on
eight lanes, and `batch8ToLprogPhysAbi` takes the result through the owned
backend. Correctness of the widening is `Batch8.batch8_denote`, which holds for
every program in the covered fragment.

The input context is `List.replicate n (reg 32)`. Input `i` is the De Bruijn
variable `laneInput (n - 1) i`, so it sits at argument slot `n - 1 - i` of the
exported function; `slotOf` inverts that. Results are read by the export's
last-`N` convention: the final `N` bindings are stored, in binding order, to the
targets of the `OutStoreMap`.

A 256-bit constant is not an immediate operand, and the export lowers
`regConst` to a move of an immediate, so constants enter as inputs loaded from a
table of pre-broadcast words at a second pointer.

## Main definitions

* `LEnv`, `LSrc`, `lBin`, `lSar`: the builder.
* `polyAddCom`, `polySubCom`, `polyReduceCom`, `polyCaddqCom`: the ML-DSA
  coefficient kernels over `groups` YMM words of eight coefficients each.
* `polyAsm`: the owned AT&T text of one kernel.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.LaneWiseEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (InLoadMap OutStoreMap)
open CatCrypt.Crypto.Optimizer.Batch8Emit (batch8ToLprogPhysAbi)

/-! ## 1. The builder -/

/-- A 32-bit lane. -/
abbrev R32 : JasminTy := .reg 32

/-- `n` input lanes. -/
abbrev laneCtxt (n : Nat) : Ctxt jasminDialect := List.replicate n R32

/-- Input `i` of a context of `m + 1` lanes (input `0` is `.here`); out-of-range
    indices saturate at `.here`. -/
def laneInput : (m : Nat) → Nat → @Ctxt.Var jasminDialect (laneCtxt (m + 1)) R32
  | _, 0 => .here
  | 0, _ => .here
  | (m + 1), (k + 1) => (laneInput m k).there

/-- The argument slot of input `i` in a context of `n` lanes. -/
def slotOf (n i : Nat) : Nat := n - 1 - i

/-- The builder environment: `slot i` is the variable last written to result
    slot `i`; `inp i` is input `i`. -/
structure LEnv (Γ : Ctxt jasminDialect) where
  /-- Current variable of result slot `i`. -/
  slot : Nat → Ctxt.Var Γ R32
  /-- Input `i`. -/
  inp  : Nat → Ctxt.Var Γ R32

/-- An operand: a result slot or an input. -/
inductive LSrc where
  /-- The current value of result slot `i`. -/
  | sl (i : Nat)
  /-- Input `i`. -/
  | iw (i : Nat)
  deriving Repr

/-- The variable an operand names. -/
def LSrc.var {Γ : Ctxt jasminDialect} (e : LEnv Γ) : LSrc → Ctxt.Var Γ R32
  | .sl i => e.slot i
  | .iw i => e.inp i

/-- A builder continuation, polymorphic in the extended context. -/
abbrev LCont (s : JasminTy) := {Γ' : Ctxt jasminDialect} → LEnv Γ' → Com jasminDialect Γ' s

/-- The environment after one binding written to slot `dst`. -/
def LEnv.push {Γ : Ctxt jasminDialect} (e : LEnv Γ) (dst : Nat) : LEnv (R32 :: Γ) where
  slot := fun i => if i = dst then .here else (e.slot i).there
  inp  := fun i => (e.inp i).there

/-- `dst := a op b` at width 32. -/
def lBin {Γ : Ctxt jasminDialect} {s : JasminTy} (e : LEnv Γ) (op : JasminBinOp)
    (dst : Nat) (a b : LSrc) (k : LCont s) : Com jasminDialect Γ s :=
  .var (Γ := Γ) (t := R32)
    { op := .regArith op 32, retTy_eq := rfl, args := .cons (a.var e) (.cons (b.var e) .nil) }
    (k (e.push dst))

/-- `dst := a >>ₛ n`, the arithmetic shift right by the immediate `n`. -/
def lSar {Γ : Ctxt jasminDialect} {s : JasminTy} (e : LEnv Γ) (dst : Nat) (a : LSrc)
    (n : Nat) (k : LCont s) : Com jasminDialect Γ s :=
  .var (Γ := Γ) (t := R32)
    { op := .sarImm 32 n, retTy_eq := rfl, args := .cons (a.var e) .nil }
    (k (e.push dst))

/-- Run `step` for every element of a list, threading the environment. -/
def lEach {s : JasminTy} (step : Nat → {Γ : Ctxt jasminDialect} → LEnv Γ → LCont s →
    Com jasminDialect Γ s) : List Nat → {Γ : Ctxt jasminDialect} → LEnv Γ → LCont s →
    Com jasminDialect Γ s
  | [], _, e, k => k e
  | x :: rest, _, e, k => step x e fun e1 => lEach step rest e1 k

/-- The initial environment over `n` inputs; every slot starts at input `0` and
    is written before it is read. -/
def initLEnv (n : Nat) : LEnv (laneCtxt (n + 1)) where
  slot := fun _ => laneInput n 0
  inp  := fun i => laneInput n i

/-! ## 2. ML-DSA coefficient kernels

Each kernel works on `groups` YMM words of eight 32-bit coefficients. Result
slots are numbered by group; the kernels whose result needs intermediate steps
emit every intermediate first and the results last, so the final `groups`
bindings are the results in group order. -/

/-- FIPS 204 modulus. -/
def dsaQ : Nat := 8380417

/-- Slot bases for the intermediates of a multi-step kernel. -/
def tA (g : Nat) : Nat := 1000 + g
def tB (g : Nat) : Nat := 2000 + g
def tC (g : Nat) : Nat := 3000 + g

/-- `a[i] := a[i] + b[i]`: inputs `0 .. groups-1` are `a` and the next `groups`
    are `b`. Input `2·groups` is unused; it gives the context the `n + 1` shape
    `initLEnv` builds. -/
def polyAddCom (groups : Nat) : Com jasminDialect (laneCtxt (2 * groups + 1)) R32 :=
  lEach (fun g _ e k => lBin e .add g (.iw g) (.iw (groups + g)) k) (List.range groups)
    (initLEnv (2 * groups)) fun e => .ret (e.slot (groups - 1))

/-- `a[i] := a[i] - b[i]`, with the input layout of `polyAddCom`. -/
def polySubCom (groups : Nat) : Com jasminDialect (laneCtxt (2 * groups + 1)) R32 :=
  lEach (fun g _ e k => lBin e .sub g (.iw g) (.iw (groups + g)) k) (List.range groups)
    (initLEnv (2 * groups)) fun e => .ret (e.slot (groups - 1))

/-- PQClean `reduce32`: `t := (a + 2²²) >>ₛ 23; a := a - t·Q`. Inputs `0 ..
    groups-1` are `a`; input `groups` is `2²²` and input `groups + 1` is `Q`,
    each broadcast. -/
def polyReduceCom (groups : Nat) : Com jasminDialect (laneCtxt (groups + 2)) R32 :=
  let c22 := groups
  let cq := groups + 1
  lEach (fun g _ e k =>
      lBin e .add (tA g) (.iw g) (.iw c22) fun e1 =>
      lSar e1 (tB g) (.sl (tA g)) 23 fun e2 =>
      lBin e2 .mul (tC g) (.sl (tB g)) (.iw cq) k) (List.range groups)
    (initLEnv (groups + 1)) fun e =>
  lEach (fun g _ e k => lBin e .sub g (.iw g) (.sl (tC g)) k) (List.range groups)
    e fun e2 => .ret (e2.slot (groups - 1))

/-- PQClean `caddq`: `a := a + ((a >>ₛ 31) & Q)`. Input `groups` is `Q`. -/
def polyCaddqCom (groups : Nat) : Com jasminDialect (laneCtxt (groups + 1)) R32 :=
  let cq := groups
  lEach (fun g _ e k =>
      lSar e (tA g) (.iw g) 31 fun e1 =>
      lBin e1 .and (tB g) (.sl (tA g)) (.iw cq) k) (List.range groups)
    (initLEnv groups) fun e =>
  lEach (fun g _ e k => lBin e .add g (.iw g) (.sl (tB g)) k) (List.range groups)
    e fun e2 => .ret (e2.slot (groups - 1))

/-! ## 3. Every program the builder writes is in `batch8`'s covered fragment

`Batch8.batch8_denote` holds for programs satisfying `Batch8Covered`. Every
`JasminBinOp` at width 32 and `sarImm 32 n` are covered, so `lBin` and `lSar`
preserve coverage for any continuation that does, and `lEach` does by induction
on the list. A kernel written with the builder that ends in `.ret` is therefore
covered for every size, and the lane-preservation theorem applies to it. -/

open CatCrypt.Crypto.Optimizer.Batch8 (Batch8Covered CoveredExpr)

/-- A continuation whose every instance is covered. -/
abbrev ContCovered {s : JasminTy} (k : LCont s) : Prop :=
  ∀ {Γ' : Ctxt jasminDialect} (e : LEnv Γ'), Batch8Covered (k e)

theorem lBin_covered {Γ : Ctxt jasminDialect} {s : JasminTy} (e : LEnv Γ) (op : JasminBinOp)
    (dst : Nat) (a b : LSrc) (k : LCont s) (hk : ContCovered k) :
    Batch8Covered (lBin e op dst a b k) := by
  refine ⟨?_, hk _⟩
  cases op <;> rfl

theorem lSar_covered {Γ : Ctxt jasminDialect} {s : JasminTy} (e : LEnv Γ) (dst : Nat)
    (a : LSrc) (n : Nat) (k : LCont s) (hk : ContCovered k) :
    Batch8Covered (lSar e dst a n k) :=
  ⟨rfl, hk _⟩

theorem lEach_covered {s : JasminTy}
    (step : Nat → {Γ : Ctxt jasminDialect} → LEnv Γ → LCont s → Com jasminDialect Γ s)
    (hstep : ∀ (x : Nat) {Γ : Ctxt jasminDialect} (e : LEnv Γ) (k : LCont s),
      ContCovered k → Batch8Covered (step x e k)) :
    ∀ (xs : List Nat) {Γ : Ctxt jasminDialect} (e : LEnv Γ) (k : LCont s),
      ContCovered k → Batch8Covered (lEach step xs e k)
  | [], _, e, _, hk => hk e
  | x :: rest, _, e, k, hk => hstep x e _ (fun e1 => lEach_covered step hstep rest e1 k hk)

theorem ret_covered {s : JasminTy} (f : ∀ {Γ' : Ctxt jasminDialect}, LEnv Γ' → Ctxt.Var Γ' s) :
    ContCovered (fun e => Com.ret (f e)) := fun _ => trivial

/-- **Coefficient add is covered**, for every number of groups. -/
theorem polyAdd_covered (groups : Nat) : Batch8Covered (polyAddCom groups) :=
  lEach_covered _ (fun _ _ e k hk => lBin_covered e _ _ _ _ k hk) _ _ _
    (ret_covered (fun e => e.slot (groups - 1)))

/-- **Coefficient subtract is covered**, for every number of groups. -/
theorem polySub_covered (groups : Nat) : Batch8Covered (polySubCom groups) :=
  lEach_covered _ (fun _ _ e k hk => lBin_covered e _ _ _ _ k hk) _ _ _
    (ret_covered (fun e => e.slot (groups - 1)))

/-- **`reduce32` is covered**, for every number of groups. -/
theorem polyReduce_covered (groups : Nat) : Batch8Covered (polyReduceCom groups) := by
  apply lEach_covered
  · intro _ _ e k hk
    apply lBin_covered; intro _ e1
    apply lSar_covered; intro _ e2
    exact lBin_covered e2 _ _ _ _ k hk
  · intro _ e
    apply lEach_covered
    · intro _ _ e' k' hk'
      exact lBin_covered e' _ _ _ _ k' hk'
    · exact fun _ => trivial

/-- **`caddq` is covered**, for every number of groups. -/
theorem polyCaddq_covered (groups : Nat) : Batch8Covered (polyCaddqCom groups) := by
  apply lEach_covered
  · intro _ _ e k hk
    apply lSar_covered; intro _ e1
    exact lBin_covered e1 _ _ _ _ k hk
  · intro _ e
    apply lEach_covered
    · intro _ _ e' k' hk'
      exact lBin_covered e' _ _ _ _ k' hk'
    · exact fun _ => trivial

/-! ## 4. ABI maps and the owned render

`RDI` points at the 256 coefficients, read and written in place; `RSI` points at
the second operand (add, sub) or at the pre-broadcast constant table (reduce,
caddq). Every YMM word is 32 bytes. -/

/-- Load map for a two-array kernel over `groups` words, whose context has
    `2·groups + 1` inputs: input `i < groups` from `RDI`, input `groups + j` from
    `RSI`, and the unused last input not loaded. -/
def twoArrayIn (groups : Nat) : InLoadMap := fun slot =>
  let i := 2 * groups - slot
  if i < groups then some ("RDI", 32 * i)
  else if i < 2 * groups then some ("RSI", 32 * (i - groups))
  else none

/-- Load map for a one-array kernel with `nConst` broadcast constants. -/
def oneArrayIn (groups nConst : Nat) : InLoadMap := fun slot =>
  let i := groups + nConst - 1 - slot
  if i < groups then some ("RDI", 32 * i) else some ("RSI", 32 * (i - groups))

/-- The results, group `g` to `RDI + 32·g`. -/
def storeOut (groups : Nat) : OutStoreMap := (List.range groups).map (fun g => ("RDI", 32 * g))

/-- The owned AT&T text of a widened lane-wise program. -/
def polyAsm {Γ : Ctxt jasminDialect} (com : Com jasminDialect Γ R32) (name : String)
    (inMap : InLoadMap) (groups : Nat) : String :=
  CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwnedReserveVecScratch
    (batch8ToLprogPhysAbi com name (fun _ => none) (fun _ => none) inMap (storeOut groups)
      (abiW := 256))

/-- YMM words per call: 4 words are 32 coefficients, and a polynomial is 8 calls.
    The export loads every input in the prologue and stores every result in the
    epilogue, so a call keeps its inputs and results live at once; four words
    keep that under the fifteen allocatable vector registers. -/
def dsaGroups : Nat := 4

/-- The four kernels, with their symbol names. -/
def dsaPolyKernels : List (String × String) :=
  [ ("mldsa_poly_add_x8", polyAsm (polyAddCom dsaGroups) "mldsa_poly_add_x8"
        (twoArrayIn dsaGroups) dsaGroups)
  , ("mldsa_poly_sub_x8", polyAsm (polySubCom dsaGroups) "mldsa_poly_sub_x8"
        (twoArrayIn dsaGroups) dsaGroups)
  , ("mldsa_poly_reduce_x8", polyAsm (polyReduceCom dsaGroups) "mldsa_poly_reduce_x8"
        (oneArrayIn dsaGroups 2) dsaGroups)
  , ("mldsa_poly_caddq_x8", polyAsm (polyCaddqCom dsaGroups) "mldsa_poly_caddq_x8"
        (oneArrayIn dsaGroups 1) dsaGroups) ]

end CatCrypt.Crypto.SecureCompilation.VIR.LaneWiseEmit
