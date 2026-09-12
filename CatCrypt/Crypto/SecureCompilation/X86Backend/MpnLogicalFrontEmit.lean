/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# The `mpn` bitwise-logical kernels as front-generated runtime-trip loops

`mpn_and_n(rp, ap, bp, n)`, `mpn_ior_n`, `mpn_xor_n` set
`rp[i] = ap[i] OP bp[i]` for `i < n`, one bit operation per limb and no carry.
This module sources the family through the verified runtime-loop front: the
per-limb body is covered `LowCT` (`RArrLoad` / `RScalarSetExpr` / `RArrStore`
over the runtime loop index), and
`Dialects.TranslateDialectRuntimeLoop.rolledForLoopNRt` front-compiles it
(`translateDialectControl` + `cryptoDialectToJasminCom`) and wraps it in a
`ComL.forLoopNRt` — one body copy behind a `jne` back-edge, the trip counter
seeded from the runtime `n` register.

```
  logicBodyLowCT comb (RArrLoad ap/bp at idx, RScalarSetExpr comb, RArrStore rp at idx)
    --(rolledForLoopNRt)--> JLoopBodyN.update : Com jasminDialect [AL, reg 64, AL, AL] AL
    --(ComL.forLoopNRt update n rp [ap, bp] (ret rp))--> ComL
    --(ComL.toLprogPhysAbi / renderLprogAtt)-----------> AT&T .s
```

## One body, one combiner

The three kernels differ only in the `SExpr` that combines the two loaded limbs,
so `logicBodyLowCT` takes that combiner as a parameter and each kernel is one
instance of it.

## The covered scalar fragment has no disjunction and no complement

`Dialects.TranslateDialectScalarDenote.srcClean` admits `SVar`, `SLit`, `SAdd`,
`SSub`, `SMul`, `SAnd`, `SXor`, `SShl`, `SShr` and `SMulHiU`. There is no `SOr`
and no `SNot`, so:

* `and` is `SAnd` and `xor` is `SXor` directly;
* `ior` is `MpnMul1FrontEmit.orE`, the identity `a ||| b = (a ^^^ b) ^^^ (a &&& b)`;
* complement is `MpnMul1FrontEmit.notE`, the identity `~~~a = a ^^^ allOnes`, with
  the all-ones word an `SLit`.

`orE_evalBV` and `notE_evalBV` below discharge those two identities against
`SExpr.evalBV`, the wrapping-`u64` evaluator, and the rest of the GMP logical
family (`andn`, `iorn`, `nand`, `nior`, `xnor`, `com`) is derived from them.

## ABI

```c
extern uint64_t *mpn_and_n_rt(uint64_t *rp, const uint64_t *ap,
                              const uint64_t *bp, uint64_t n);
```

`rp` (RDI), `ap` (RSI), `bp` (RDX), `n` (RCX). All three arrays hold `n` words.

## Main results

* `bvOr_of_xor_and`: `(x ^^^ y) ^^^ (x &&& y) = x ||| y` on `BitVec 64`.
* `orE_evalBV`, `notE_evalBV`: the synthesised `SExpr` combiners denote `|||`
  and `~~~` under `SExpr.evalBV`.
* `logicFold_get`: cell `j` of the emitted fold after `n` trips is
  `f ap[j] bp[j]`, for every `NR` / `NA` / `NB` and every `j < n ≤ NR`.
* `logicFold_cells`: the emitted fold's first `n` cells are the elementwise
  `List.zipWith f` of the two source limb lists.
* `andFold_cells`, `iorFold_cells`, `xorFold_cells`: the three GMP readings.
* `logicRtProg_denote`: the runtime-trip loop program's denotation as the fold.

## Scope

`logicFold_get` and `logicFold_cells` hold for every array width; `NL` fixes only
the memref width of the concrete front-compiled instances below, whose rendered
SIB accesses are byte-offset and so size-agnostic.

`logicRtProg_denote` carries the front-compilation hypothesis
`frontLoopBodyJ … = some update` and concludes at `JLoopBodyN.denote` of that
`update`. Identifying that denotation with `logicFoldStep` — so that
`logicFold_cells` reads as a statement about the emitted kernel — is the separate
source-preservation step (`translateDialectControl_denote_ctl` composed with
`cryptoDialectToJasminCom`), not established here.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLogicalFrontEmit

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
  (cells cells_length memGetDyn_memSetDyn_ne memGetDyn_memSetDyn_self
   sv seqAll ones notE orE)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType Located)

/-! ## 1. Disjunction and complement from conjunction and exclusive-or

The two word identities the covered `SExpr` fragment forces, proved bit by bit. -/

/-- Disjunction from exclusive-or and conjunction: the exclusive-or carries the
    bits set in exactly one operand and the conjunction the bits set in both. -/
theorem bvOr_of_xor_and (x y : BitVec 64) : (x ^^^ y) ^^^ (x &&& y) = x ||| y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_or]
  cases x.getLsbD i <;> cases y.getLsbD i <;> decide

/-- The all-ones `SLit` used by `notE` is the all-ones word. -/
theorem ofNat_ones_eq_allOnes : (BitVec.ofNat 64 ones) = BitVec.allOnes 64 := by
  decide

/-- **The synthesised disjunction denotes `|||`.** `orE a b` is the `SExpr` the
    covered fragment admits in place of the absent `SOr`. -/
theorem orE_evalBV (β : String → BitVec 64) (a b : SExpr) :
    (orE a b).evalBV β = a.evalBV β ||| b.evalBV β := by
  simp only [orE, SExpr.evalBV]
  exact bvOr_of_xor_and (a.evalBV β) (b.evalBV β)

/-- **The synthesised complement denotes `~~~`.** `notE e` is the `SExpr` the
    covered fragment admits in place of the absent `SNot`. -/
theorem notE_evalBV (β : String → BitVec 64) (e : SExpr) :
    (notE e).evalBV β = ~~~ (e.evalBV β) := by
  simp only [notE, SExpr.evalBV, ofNat_ones_eq_allOnes, BitVec.xor_allOnes]

/-! ## 2. The GMP logical family as `SExpr` combiners

Each kernel of the family is one combiner. `andSE` and `xorSE` are the covered
operations directly; the rest go through `orE` / `notE`. -/

/-- The `mpn_and_n` combiner. -/
def andSE (a b : SExpr) : SExpr := .SAnd a b

/-- The `mpn_xor_n` combiner. -/
def xorSE (a b : SExpr) : SExpr := .SXor a b

/-- The `mpn_ior_n` combiner. -/
def iorSE (a b : SExpr) : SExpr := orE a b

/-- The `mpn_com` combiner, on the first operand. -/
def comSE (a : SExpr) : SExpr := notE a

/-- The `mpn_andn_n` combiner: `a &&& ~~~b`. -/
def andnSE (a b : SExpr) : SExpr := .SAnd a (notE b)

/-- The `mpn_iorn_n` combiner: `a ||| ~~~b`. -/
def iornSE (a b : SExpr) : SExpr := orE a (notE b)

/-- The `mpn_nand_n` combiner: `~~~(a &&& b)`. -/
def nandSE (a b : SExpr) : SExpr := notE (.SAnd a b)

/-- The `mpn_nior_n` combiner: `~~~(a ||| b)`. -/
def niorSE (a b : SExpr) : SExpr := notE (orE a b)

/-- The `mpn_xnor_n` combiner: `~~~(a ^^^ b)`. -/
def xnorSE (a b : SExpr) : SExpr := notE (.SXor a b)

/-- `andSE` denotes conjunction. -/
theorem andSE_evalBV (β : String → BitVec 64) (a b : SExpr) :
    (andSE a b).evalBV β = a.evalBV β &&& b.evalBV β := rfl

/-- `xorSE` denotes exclusive-or. -/
theorem xorSE_evalBV (β : String → BitVec 64) (a b : SExpr) :
    (xorSE a b).evalBV β = a.evalBV β ^^^ b.evalBV β := rfl

/-- `iorSE` denotes disjunction. -/
theorem iorSE_evalBV (β : String → BitVec 64) (a b : SExpr) :
    (iorSE a b).evalBV β = a.evalBV β ||| b.evalBV β := orE_evalBV β a b

/-- `comSE` denotes complement. -/
theorem comSE_evalBV (β : String → BitVec 64) (a : SExpr) :
    (comSE a).evalBV β = ~~~ (a.evalBV β) := notE_evalBV β a

/-- `andnSE` denotes conjunction with the second operand complemented. -/
theorem andnSE_evalBV (β : String → BitVec 64) (a b : SExpr) :
    (andnSE a b).evalBV β = a.evalBV β &&& ~~~ (b.evalBV β) := by
  simp only [andnSE, notE, SExpr.evalBV, notE_evalBV, ofNat_ones_eq_allOnes,
    BitVec.xor_allOnes]

/-- `iornSE` denotes disjunction with the second operand complemented. -/
theorem iornSE_evalBV (β : String → BitVec 64) (a b : SExpr) :
    (iornSE a b).evalBV β = a.evalBV β ||| ~~~ (b.evalBV β) := by
  simp only [iornSE, orE, notE, SExpr.evalBV, orE_evalBV, notE_evalBV,
    ofNat_ones_eq_allOnes, BitVec.xor_allOnes, bvOr_of_xor_and]

/-- `nandSE` denotes the complement of conjunction. -/
theorem nandSE_evalBV (β : String → BitVec 64) (a b : SExpr) :
    (nandSE a b).evalBV β = ~~~ (a.evalBV β &&& b.evalBV β) := by
  simp only [nandSE, notE, SExpr.evalBV, notE_evalBV, ofNat_ones_eq_allOnes,
    BitVec.xor_allOnes]

/-- `niorSE` denotes the complement of disjunction. -/
theorem niorSE_evalBV (β : String → BitVec 64) (a b : SExpr) :
    (niorSE a b).evalBV β = ~~~ (a.evalBV β ||| b.evalBV β) := by
  simp only [niorSE, orE, notE, SExpr.evalBV, orE_evalBV, notE_evalBV,
    ofNat_ones_eq_allOnes, BitVec.xor_allOnes, bvOr_of_xor_and]

/-- `xnorSE` denotes the complement of exclusive-or. -/
theorem xnorSE_evalBV (β : String → BitVec 64) (a b : SExpr) :
    (xnorSE a b).evalBV β = ~~~ (a.evalBV β ^^^ b.evalBV β) := by
  simp only [xnorSE, notE, SExpr.evalBV, notE_evalBV, ofNat_ones_eq_allOnes,
    BitVec.xor_allOnes]

/-! ## 3. The elementwise fold over the memref carrier

The emitted loop carries the output array as its accumulator and folds one body
copy over the trip indices. `logicFoldStep` is that body's word-level effect and
`logicFold` the `(List.range n).foldl` shape `JLoopBodyN.denote` uses. -/

/-- One trip of the emitted loop on the accumulator array: read `ap[t]` and
    `bp[t]`, combine them with `f`, write the result to cell `t`. -/
def logicFoldStep {NR NA NB : Nat} (f : BitVec 64 → BitVec 64 → BitVec 64)
    (ap : Fin NA → BitVec 64) (bp : Fin NB → BitVec 64)
    (acc : Fin NR → BitVec 64) (t : Nat) : Fin NR → BitVec 64 :=
  memSetDyn acc t (f (memGetDyn ap t) (memGetDyn bp t))

/-- The `n`-fold of `logicFoldStep` over the trip indices `0, …, n-1`: the
    `(List.range n).foldl` shape `JLoopBodyN.denote` folds the emitted loop body
    in, at accumulator type `.stackArr 64 NR`. -/
def logicFold {NR NA NB : Nat} (f : BitVec 64 → BitVec 64 → BitVec 64)
    (ap : Fin NA → BitVec 64) (bp : Fin NB → BitVec 64)
    (n : Nat) (acc : Fin NR → BitVec 64) : Fin NR → BitVec 64 :=
  (List.range n).foldl (logicFoldStep f ap bp) acc

/-- The fold peels its last trip. -/
theorem logicFold_succ {NR NA NB : Nat} (f : BitVec 64 → BitVec 64 → BitVec 64)
    (ap : Fin NA → BitVec 64) (bp : Fin NB → BitVec 64)
    (n : Nat) (acc : Fin NR → BitVec 64) :
    logicFold f ap bp (n + 1) acc
      = logicFoldStep f ap bp (logicFold f ap bp n acc) n := by
  simp [logicFold, List.range_succ, List.foldl_append]

/-- **The elementwise loop invariant, cell by cell.** After `n` trips every cell
    below the trip count holds the combiner applied to the two source cells at
    the same index. -/
theorem logicFold_get {NR NA NB : Nat} (f : BitVec 64 → BitVec 64 → BitVec 64)
    (ap : Fin NA → BitVec 64) (bp : Fin NB → BitVec 64) (acc : Fin NR → BitVec 64) :
    ∀ n : Nat, n ≤ NR → ∀ j : Nat, j < n →
      memGetDyn (logicFold f ap bp n acc) j = f (memGetDyn ap j) (memGetDyn bp j) := by
  intro n
  induction n with
  | zero => intro _ j hj; exact absurd hj (Nat.not_lt_zero j)
  | succ k ih =>
      intro hk j hj
      rw [logicFold_succ]
      by_cases hlt : j < k
      · rw [logicFoldStep,
          memGetDyn_memSetDyn_ne _ k j _ (by omega) (by omega) (by omega)]
        exact ih (by omega) j hlt
      · have heq : j = k := by omega
        rw [logicFoldStep, heq]
        exact memGetDyn_memSetDyn_self _ k _ (by omega)

/-- `zipWith` of two maps over one list is the map of the combined function. -/
theorem zipWith_map_map {α : Type} (f : BitVec 64 → BitVec 64 → BitVec 64)
    (g h : α → BitVec 64) (l : List α) :
    List.zipWith f (l.map g) (l.map h) = l.map (fun j => f (g j) (h j)) := by
  induction l with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons, List.zipWith_cons_cons, ih]

/-- **The emitted fold is the elementwise operation on the limb lists.** After
    `n` trips the accumulator's first `n` cells are `List.zipWith f` of the two
    source arrays' first `n` cells, for every array width. -/
theorem logicFold_cells {NR NA NB : Nat} (f : BitVec 64 → BitVec 64 → BitVec 64)
    (ap : Fin NA → BitVec 64) (bp : Fin NB → BitVec 64) (acc : Fin NR → BitVec 64)
    (n : Nat) (hn : n ≤ NR) :
    cells (logicFold f ap bp n acc) n = List.zipWith f (cells ap n) (cells bp n) := by
  simp only [cells, zipWith_map_map, List.map_inj_left, List.mem_range]
  intro j hj
  exact logicFold_get f ap bp acc n hn j hj

/-- **`mpn_and_n` reading.** -/
theorem andFold_cells {NR NA NB : Nat} (ap : Fin NA → BitVec 64)
    (bp : Fin NB → BitVec 64) (acc : Fin NR → BitVec 64) (n : Nat) (hn : n ≤ NR) :
    cells (logicFold (fun x y => x &&& y) ap bp n acc) n
      = List.zipWith (fun x y => x &&& y) (cells ap n) (cells bp n) :=
  logicFold_cells _ ap bp acc n hn

/-- **`mpn_ior_n` reading.** -/
theorem iorFold_cells {NR NA NB : Nat} (ap : Fin NA → BitVec 64)
    (bp : Fin NB → BitVec 64) (acc : Fin NR → BitVec 64) (n : Nat) (hn : n ≤ NR) :
    cells (logicFold (fun x y => x ||| y) ap bp n acc) n
      = List.zipWith (fun x y => x ||| y) (cells ap n) (cells bp n) :=
  logicFold_cells _ ap bp acc n hn

/-- **`mpn_xor_n` reading.** -/
theorem xorFold_cells {NR NA NB : Nat} (ap : Fin NA → BitVec 64)
    (bp : Fin NB → BitVec 64) (acc : Fin NR → BitVec 64) (n : Nat) (hn : n ≤ NR) :
    cells (logicFold (fun x y => x ^^^ y) ap bp n acc) n
      = List.zipWith (fun x y => x ^^^ y) (cells ap n) (cells bp n) :=
  logicFold_cells _ ap bp acc n hn

/-- **`mpn_nand_n` reading.** -/
theorem nandFold_cells {NR NA NB : Nat} (ap : Fin NA → BitVec 64)
    (bp : Fin NB → BitVec 64) (acc : Fin NR → BitVec 64) (n : Nat) (hn : n ≤ NR) :
    cells (logicFold (fun x y => ~~~ (x &&& y)) ap bp n acc) n
      = List.zipWith (fun x y => ~~~ (x &&& y)) (cells ap n) (cells bp n) :=
  logicFold_cells _ ap bp acc n hn

/-- The output has one cell per trip. -/
theorem logicFold_cells_length {NR NA NB : Nat} (f : BitVec 64 → BitVec 64 → BitVec 64)
    (ap : Fin NA → BitVec 64) (bp : Fin NB → BitVec 64) (acc : Fin NR → BitVec 64)
    (n : Nat) : (cells (logicFold f ap bp n acc) n).length = n :=
  cells_length _ n

/-! ## 4. The loop body as covered `LowCT`

The body runs over the catCryptDialect context
`Gbody = [rp : .memref NL, idx : .sword 64, ap : .memref NL, bp : .memref NL]` —
the accumulator array, the runtime loop index, then the two source arrays as
invariants. -/

/-- Limb count of the three arrays in the denotation model. The rendered SIB
    accesses use byte offsets, so the assembly is size-agnostic; this only bounds
    the in-Lean model. The results of §3 are stated for every width. -/
abbrev NL : Nat := 8

/-- The output-array slot `rp`, the loop accumulator. -/
def rpLoc : Located := ⟨"rp", .TBytes (8 * NL)⟩

/-- The first source-array slot `ap`, a loop invariant. -/
def apLoc : Located := ⟨"ap", .TBytes (8 * NL)⟩

/-- The second source-array slot `bp`, a loop invariant. -/
def bpLoc : Located := ⟨"bp", .TBytes (8 * NL)⟩

/-- One limb at the runtime loop index `idx`: read `ap[idx]` and `bp[idx]`,
    combine them with `comb`, store the result to `rp[idx]`. -/
def logicBodyLowCT (comb : SExpr → SExpr → SExpr) : LowCT := seqAll
  [ .RArrLoad ⟨"x", .TU64⟩ apLoc "idx"
  , .RArrLoad ⟨"y", .TU64⟩ bpLoc "idx"
  , .RScalarSetExpr "z" (comb (sv "x") (sv "y"))
  , .RArrStore rpLoc "idx" ⟨"z", .TU64⟩ ]

/-- The loop-body context: accumulator `rp`, runtime loop index, then the two
    source arrays as invariants. -/
def Gbody : Ctx := [.memref NL, .sword 64, .memref NL, .memref NL]

/-- The body `VarMap`: `bp` bound deepest, then `ap`, then `idx`, then `rp` at
    `.here`. -/
def vmBody : VarMap Gbody :=
  ((((VarMap.empty.bind (t := .memref NL) "bp").bind
      (t := .memref NL) "ap").bind
      (t := .sword 64) "idx").bind (t := .memref NL) "rp")

/-! ## 5. The runtime-trip loop program

Outer argument context `[n, bp, ap, rp]` (newest first), routing
`rp → RDI`, `ap → RSI`, `bp → RDX`, `n → RCX`. -/

/-- The `reg 64` dialect type. -/
abbrev r64 : JasminTy := .reg 64

/-- The common array jasmin type. -/
abbrev AL : JasminTy := .stackArr 64 NL

/-- The kernel's outer argument context, newest first. -/
abbrev Gouter : Ctxt jasminDialect := [r64, AL, AL, AL]

/-- The runtime trip count `n` (RCX). -/
def logicCount : Ctxt.Var Gouter r64 := .here

/-- The accumulator seed: the output array `rp` (RDI). -/
def logicInit : Ctxt.Var Gouter AL := .there (.there (.there .here))

/-- The loop invariants: the two source arrays `ap` (RSI) and `bp` (RDX). The
    list is in ABI order, so the export's positional invariant-to-ABI-register
    zip (`ComL.loopArgBaseNames` feeding `ComL.toLfundefPhysAbi`'s reload map)
    pairs `ap` with `RSI` and `bp` with `RDX`. -/
def logicInvs : HVector (fun ty => Ctxt.Var Gouter ty) [AL, AL] :=
  .cons (.there (.there .here)) (.cons (.there .here) .nil)

/-- The front-compiled runtime-trip elementwise kernel for a combiner: one body
    copy behind a `jne` back-edge, the trip counter seeded from the runtime `n`
    register, the output array threaded as the loop accumulator and `ap`/`bp` as
    loop invariants. `none` if the front declines. -/
def logicRtProgOpt (comb : SExpr → SExpr → SExpr) : Option (ComL Gouter AL) :=
  rolledForLoopNRt (Γouter := Gouter) (accCTy := .memref NL)
    (invCTys := [.memref NL, .memref NL])
    vmBody "rp" (logicBodyLowCT comb) logicCount logicInit logicInvs

-- The front accepts each body and wraps it in a `ComL.forLoopNRt`.
#guard (logicRtProgOpt andSE).isSome
#guard (logicRtProgOpt iorSE).isSome
#guard (logicRtProgOpt xorSE).isSome
#guard (logicRtProgOpt nandSE).isSome

/-- **The emitted loop's denotation is the `JLoopBodyN` fold of the front body.**
    Whenever the front compiles `logicBodyLowCT comb` to `update`, the
    runtime-trip program's denotation at any valuation is the `n`-fold of
    `update` over the trip indices, seeded by the `rp` argument and threading
    `ap` and `bp`. The instance of `rolledForLoopNRt_denote` at this kernel. -/
theorem logicRtProg_denote (comb : SExpr → SExpr → SExpr)
    {update : Com jasminDialect
      (CryptoToJasminCom.mapCtx (CryptoTy.memref NL :: .sword 64 ::
        [CryptoTy.memref NL, CryptoTy.memref NL]))
      (CryptoToJasminCom.mapTy (CryptoTy.memref NL))}
    (hupd : Dialects.TranslateDialectRolledLoop.frontLoopBodyJ
      (accCTy := .memref NL) vmBody "rp" (logicBodyLowCT comb) = some update)
    (V : Ctxt.Valuation Gouter) :
    (logicRtProgOpt comb).map (fun c => ComL.denote c V)
      = some (JLoopBodyN.denote ⟨(logicCount.lookup V).toNat, update⟩
          (Expr.lookupArgs logicInvs V) (logicInit.lookup V)) :=
  rolledForLoopNRt_denote vmBody "rp" (logicBodyLowCT comb) logicCount logicInit
    logicInvs hupd V

/-! ## 6. The owned `Lprog` and the rendered `.s` -/

/-- The rolled, owned-RA 4-argument-ABI `Lprog` for a runtime-trip elementwise
    kernel under the C symbol `fname`
    (`RDI = rp`, `RSI = ap`, `RDX = bp`, `RCX = n`). -/
def logicRtLprogOpt (comb : SExpr → SExpr → SExpr) (fname : String) : Option Lprog :=
  (logicRtProgOpt comb).map (fun c =>
    ComL.toLprogPhysAbi c fname (argName 0) [argName 1, argName 2]
      (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX", "RCX"] [64, 64, 64, 64])

/-- The owned AT&T `.s` text for a runtime-trip elementwise kernel. -/
def logicRtAsmOpt (comb : SExpr → SExpr → SExpr) (fname : String) : Option String :=
  (logicRtLprogOpt comb fname).map CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned

/-- The `mpn_and_n` render. -/
def andRtAsmOpt : Option String := logicRtAsmOpt andSE "mpn_and_n_rt"

/-- The `mpn_ior_n` render. -/
def iorRtAsmOpt : Option String := logicRtAsmOpt iorSE "mpn_ior_n_rt"

/-- The `mpn_xor_n` render. -/
def xorRtAsmOpt : Option String := logicRtAsmOpt xorSE "mpn_xor_n_rt"

/-- The `mpn_nand_n` render, the family member that goes through `notE`. -/
def nandRtAsmOpt : Option String := logicRtAsmOpt nandSE "mpn_nand_n_rt"

/-- The 4-argument-ABI physical body of the front-compiled runtime-count loop. -/
def logicRtPhysBodyOpt (comb : SExpr → SExpr → SExpr) : Option Lcmd :=
  (logicRtProgOpt comb).map (fun c =>
    (ComL.toLfundefPhysAbi c (argName 0) [argName 1, argName 2]
      (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX", "RCX"]
      [64, 64, 64, 64]).lfd_body)

/-- Whether a physical body carries a real back-edge: an internal label and a
    conditional jump, so the emit is a counted loop and not an unrolled chain. -/
def hasBackEdge (comb : SExpr → SExpr → SExpr) : Option Bool :=
  (logicRtPhysBodyOpt comb).map (fun body =>
    (body.any (fun i => match i.li_i with | .Lcond _ _ => true | _ => false))
      && (body.any (fun i => match i.li_i with | .Llabel _ _ => true | _ => false)))

#guard hasBackEdge andSE = some true
#guard hasBackEdge iorSE = some true
#guard hasBackEdge xorSE = some true
#guard hasBackEdge nandSE = some true

/-- The red-zone qsave slot each streaming memref access reloads its SIB base
    from, in body order. Each `LOADIDX`/`STOREIDX` is preceded by the reload of
    its base into `R14`, so the slot names read off the pairs are the array
    argument each access addresses through. -/
def logicRtReloads (comb : SExpr → SExpr → SExpr) : List String :=
  match logicRtPhysBodyOpt comb with
  | none => []
  | some body =>
      (body.zip (body.drop 1)).filterMap (fun (prev, cur) =>
        match cur.li_i, prev.li_i with
        | .Lopn _ "LOADIDX" (.arrIdx "R14" _ _ :: _), .Lopn [.reg "R14"] _ [.reg q] =>
            some q
        | .Lopn _ "STOREIDX" (.arrIdx "R14" _ _ :: _), .Lopn [.reg "R14"] _ [.reg q] =>
            some q
        | _, _ => none)

-- `rp` (RDI), `ap` (RSI) and `bp` (RDX) are the three pointer arguments; `n`
-- (RCX) is a scalar, so no access may reload its base from its qsave slot. Both
-- source loads reach their array through the slot of that array's own ABI
-- register.
#guard (logicRtReloads andSE).contains "qsave.RSI"
#guard (logicRtReloads andSE).contains "qsave.RDX"
#guard (logicRtReloads andSE).all
  (fun q => q == "qsave.RDI" || q == "qsave.RSI" || q == "qsave.RDX")
#guard (logicRtReloads xorSE).all
  (fun q => q == "qsave.RDI" || q == "qsave.RSI" || q == "qsave.RDX")

-- Rendered-asm correctness is the external C KAT; an in-Lean occursIn check would
-- re-evaluate the optimizing back-end renderOwned at elaboration.

/-! ## 7. Emit driver

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

/-- Write the owned-backend `.s` files for the elementwise logical kernels into
    the `bench/mpn_logical_front_compare/gen_com` harness directory. -/
def emitMain : IO Unit := do
  let dir := "bench/mpn_logical_front_compare/gen_com"
  IO.FS.createDirAll dir
  let kernels : List (String × Option String) :=
    [ ("mpn_and_n_rt", andRtAsmOpt)
    , ("mpn_ior_n_rt", iorRtAsmOpt)
    , ("mpn_xor_n_rt", xorRtAsmOpt)
    , ("mpn_nand_n_rt", nandRtAsmOpt) ]
  for (nm, asm) in kernels do
    match asm with
    | some s =>
        IO.FS.writeFile (dir ++ "/" ++ nm ++ "_owned.s") s
        IO.println ("WROTE " ++ dir ++ "/" ++ nm ++ "_owned.s")
    | none => throw (IO.userError ("the runtime-loop front declined " ++ nm))

-- #eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLogicalFrontEmit
