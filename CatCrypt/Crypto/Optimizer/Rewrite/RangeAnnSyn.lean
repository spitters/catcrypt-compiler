/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Optimizer.Rewrite.RangeNFLoop
public import CatCrypt.Crypto.Optimizer.Rewrite.RangeNFLoop

/-!
# Synthesis of the loop annotation of the range stage, and entry environments

The stage `RangeNFLoop.loopRange` takes an annotation `RangeNFLoop.CarriedAnn` that proposes
one interval per variable a loop carries, and checks each proposal
(`RangeNFLoop.forInductive`, `RangeNFLoop.whileInductive`). This file computes an annotation
from the program, gives the stage at the computed annotation (`synRange`, the range stage of
the chains `extChain` and `nfChain`), and states the stage from an abstract environment of
the inputs. The selections of `RangeSelNF.rangeSel` at the same annotation are in
`RangeSelSyn.lean`.

## The synthesiser

`inferLoops A len p` traverses `p` with the interval analysis of the range stage
(`ComPipeline.stageAbs`) from the abstract environment `A`, and returns an annotation of
`p` with the intervals of the variables `p` returns. At a loop with carried types `cs` it
solves for the carried intervals with `solveCarried`, where `f is` is the analysis of the
body from the carried intervals `is`:

1. start from the lane intervals of the start variables under `A`;
2. `ascendIvs`: at most `joinRounds` rounds, each replacing an entry that the result of
   the body leaves by its hull with the lane interval of that result, and stopping when
   every result lies within its entry;
3. `widenRounds`: at most `cs.length` rounds, each replacing an entry that the result of
   the body leaves by the full lane range of its type;
4. `descendIvs`: at most `joinRounds` rounds, each proposing the hull of the start
   intervals with the result of the body, and keeping the proposal when the result of the
   body from it lies within it.

The annotation of the body is the one synthesised from the solved intervals. The
continuation of a loop is analysed in the environment the traversals use: the carried
variables at the solved intervals when the checker accepts them, at the full lane range
otherwise. The number of analyses of a loop body is at most
`2 * joinRounds + cs.length + 2` per analysis of the loop.

The synthesiser carries no theorem of its own. Every theorem of the stage holds for every
annotation, and the stage checks each proposal.

## Entry environments

`entryRange A a p` is the traversal `RangeNFLoop.carriedGo` from the abstract environment
`A` of the inputs. Its denotation theorem holds at every valuation `V` with `EnvOK A V`. The
certificate `inputRangeCert` has the input relation `V = W ∧ EnvOK A V` and equality of
results as output relation.

## Main results

* `synAnn`: the annotation synthesised from the full lane range of every input.
* `entryAnn`: the annotation synthesised from an abstract environment of the inputs.
* `synRange`: `loopRange` at `synAnn p`, the range stage of the chains.
* `synRange_denote`: `synRange p` denotes what `p` denotes.
* `synRangeStep`, `synRangeCert`: the chain step of the stage at `synAnn`, with its
  certificate.
* `entryRange`: the stage from an abstract environment of the inputs.
* `entryRange_denote`: under `EnvOK A V` the output denotes at `V` what the input denotes
  at `V`.
* `entryRange_topEnv`: at `topEnv` the entry form is `loopRange`.
* `inputRangeStep`, `inputRangeCert`: the chain step of the entry form, with a certificate
  whose input relation is `V = W ∧ EnvOK A V`.
* `acceptedLoops`: the number of loops of a program whose proposal the checker accepts.
* On `RangeNFLoop.lazyAddLoop` the synthesised interval of the carried word is
  `[0, p - 1]`, the checker accepts it, and `loopRange` keeps one `and` operation, as under
  `RangeNFLoop.lazyAddAnn` (`#kat`).
* On `plainAddLoop`, whose body does not mask the carried word, the entry form from
  `plainAddEnv` (the input below the BabyBear prime) keeps one of the two `and` operations;
  from the full lane range both `and` operations stay (`#kat`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.RangeAnnSyn

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.RangeDomain
open CatCrypt.Crypto.SecureCompilation.VIR.ComRange
open CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline
open CatCrypt.Crypto.Optimizer.Rewrite.RangeNF
open CatCrypt.Crypto.Optimizer.Rewrite.RangeNFLoop

/-! ## 1. Operations on lists of intervals -/

/-- The lane interval of an interval at a register type; the full lane range of the type
    at every other type. -/
def laneIv : JasminTy → Iv → Iv
  | .reg w, i => ivLane w i
  | t, _ => tyTop t

/-- The intervals of the variables `vs` under `A`. -/
def varIvs {Γ : JCtxt} (A : AEnv Γ) : {ts : List JasminTy} →
    HVector (fun t => Ctxt.Var Γ t) ts → List Iv
  | [], .nil => []
  | _ :: _, .cons v vs => (hget A v).1 :: varIvs A vs

/-- The lane intervals of a list of intervals at the types `cs`. -/
def laneIvs : List JasminTy → List Iv → List Iv
  | t :: cs, i :: is => laneIv t i :: laneIvs cs is
  | _, _ => []

/-- Each interval of `rs` lies within its interval of `is`, at the types `cs`. -/
def stableIvs : List JasminTy → List Iv → List Iv → Bool
  | t :: cs, r :: rs, i :: is => tyWithin t r i && stableIvs cs rs is
  | _, _, _ => true

/-- The intervals `is` with each entry that its interval of `rs` leaves replaced by the
    hull of the entry and the lane interval of `rs`. -/
def hullIvs : List JasminTy → List Iv → List Iv → List Iv
  | t :: cs, i :: is, r :: rs =>
      (if tyWithin t r i then i else ivHull i (laneIv t r)) :: hullIvs cs is rs
  | _, is, _ => is

/-- The intervals `is` with each entry that its interval of `rs` leaves replaced by the
    full lane range of its type. -/
def widenIvs : List JasminTy → List Iv → List Iv → List Iv
  | t :: cs, i :: is, r :: rs =>
      (if tyWithin t r i then i else tyTop t) :: widenIvs cs is rs
  | _, is, _ => is

/-! ## 2. The bounded iteration for one loop -/

/-- The number of rounds of the ascending and of the descending phase. -/
def joinRounds : Nat := 3

/-- The ascending phase: at most `n` rounds of `hullIvs` with the result `f is` of the
    body, stopping when the result lies within `is`. -/
def ascendIvs (cs : List JasminTy) (f : List Iv → List Iv) : Nat → List Iv → List Iv
  | 0, is => is
  | n + 1, is =>
      let rs := f is
      if stableIvs cs rs is then is else ascendIvs cs f n (hullIvs cs is rs)

/-- The widening phase: at most `n` rounds of `widenIvs` with the result `f is` of the
    body, stopping when the result lies within `is`. -/
def widenRounds (cs : List JasminTy) (f : List Iv → List Iv) : Nat → List Iv → List Iv
  | 0, is => is
  | n + 1, is =>
      let rs := f is
      if stableIvs cs rs is then is else widenRounds cs f n (widenIvs cs is rs)

/-- The descending phase: at most `n` rounds, each proposing the hull `c` of the start
    intervals `init` with the result `f is` of the body and moving to `c` when it differs
    from `is` and the result `f c` lies within `c`. -/
def descendIvs (cs : List JasminTy) (f : List Iv → List Iv) (init : List Iv) :
    Nat → List Iv → List Iv
  | 0, is => is
  | n + 1, is =>
      let c := hullIvs cs init (f is)
      if c == is then is
      else if stableIvs cs (f c) c then descendIvs cs f init n c else is

/-- The carried intervals proposed for a loop with carried types `cs`, start intervals
    `init` and body analysis `f`: the ascending phase from the lane intervals of `init`,
    the widening phase, and the descending phase. -/
def solveCarried (cs : List JasminTy) (f : List Iv → List Iv) (init : List Iv) : List Iv :=
  let start := laneIvs cs init
  descendIvs cs f start joinRounds
    (widenRounds cs f cs.length (ascendIvs cs f joinRounds start))

/-! ## 3. The synthesiser -/

/-- The annotation synthesised for `p` from the abstract environment `A` of a context of
    length `len`, with the intervals of the variables `p` returns when the range analysis
    runs under that annotation. -/
def inferLoops : {Γ : JCtxt} → {ts : List JasminTy} → AEnv Γ → Nat →
    NFProg jasminDialect Γ ts → CarriedAnn × List Iv
  | _, _, A, _, .ret vs => (.empty, varIvs A vs)
  | _, _, A, len, .var e k =>
      inferLoops (HVector.cons (f := fun _ => AVal) (stageAbs A e len) A) (len + 1) k
  | _, _, A, len, .forLoop (cs := cs) _ inits body k =>
      let is := solveCarried cs
        (fun is => (inferLoops (invApp cs is (topCons (HasWord64.word (d := jasminDialect)) A))
          (cs.length + (len + 1)) body).2) (varIvs A inits)
      let ab := (inferLoops (invApp cs is (topCons (HasWord64.word (d := jasminDialect)) A))
        (cs.length + (len + 1)) body).1
      let r := inferLoops
        (carriedEnv (forInductive A len (.loop is ab .empty) inits body) cs is A)
        (cs.length + len) k
      (.loop is ab r.1, r.2)
  | _, _, A, len, .ifThenElse (rs := rs) _ thn els k =>
      let r := inferLoops (topApp rs A) (rs.length + len) k
      (.branch (inferLoops A len thn).1 (inferLoops A len els).1 r.1, r.2)
  | _, _, A, len, .whileLoop (cs := cs) inits body k =>
      let is := solveCarried cs
        (fun is => (inferLoops (invApp cs is A) (cs.length + len) body).2.tail)
        (varIvs A inits)
      let ab := (inferLoops (invApp cs is A) (cs.length + len) body).1
      let r := inferLoops
        (carriedEnv (whileInductive A len (.loop is ab .empty) inits body) cs is A)
        (cs.length + len) k
      (.loop is ab r.1, r.2)
  | _, _, A, len, .call (rs := rs) _ _ k => inferLoops (topApp rs A) (rs.length + len) k

/-- The annotation synthesised for `p` from the abstract environment `A` of its inputs. -/
def entryAnn {Γ : JCtxt} {ts : List JasminTy} (A : AEnv Γ)
    (p : NFProg jasminDialect Γ ts) : CarriedAnn :=
  (inferLoops A Γ.length p).1

/-- **The synthesiser**: the annotation synthesised for `p` from the full lane range of
    every input. -/
def synAnn {Γ : JCtxt} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) : CarriedAnn :=
  entryAnn (topEnv Γ) p

/-! ## 4. The range stage at the synthesised annotation -/

/-- **The range stage of the chains**: `loopRange` at the annotation synthesised for `p`.
    The annotation is not trusted: the stage checks each proposed interval. -/
def synRange {Γ : JCtxt} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) :
    NFProg jasminDialect Γ ts :=
  loopRange (synAnn p) p

/-- `synRange p` denotes what `p` denotes. -/
theorem synRange_denote [CallDenote jasminDialect] {Γ : JCtxt} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (fuel : Nat) :
    (synRange p).denote fuel = p.denote fuel :=
  loopRange_denote (synAnn p) p fuel

open NFProgPasses (nfSem)

/-- The stage `loopRange` at the synthesised annotation, as a chain step. -/
def synRangeStep (Γ : JCtxt) (ts : List JasminTy) :
    PassChain.Step (NFProg jasminDialect Γ ts) (NFProg jasminDialect Γ ts) :=
  carriedStep Γ ts synAnn

/-- The certificate of `synRangeStep`: the output has the denotation of its input. -/
def synRangeCert [CallDenote jasminDialect] (fuel : Nat) (Γ : JCtxt) (ts : List JasminTy) :
    PassChain.StepCert (synRangeStep Γ ts).run (nfSem fuel jasminDialect Γ ts)
      (nfSem fuel jasminDialect Γ ts) :=
  carriedCert fuel Γ ts synAnn

/-! ## 5. The stage from an abstract environment of the inputs -/

/-- The range stage with checked carried intervals, from the abstract environment `A` of
    the inputs. -/
def entryRange {Γ : JCtxt} {ts : List JasminTy} (A : AEnv Γ) (a : CarriedAnn)
    (p : NFProg jasminDialect Γ ts) : NFProg jasminDialect Γ ts :=
  carriedGo A Γ.length a p

/-- **Denotation of the range stage from an entry environment.** At a valuation of which
    `A` holds, `entryRange A a p` denotes what `p` denotes, at every fuel and for every
    annotation. -/
theorem entryRange_denote [CallDenote jasminDialect] {Γ : JCtxt} {ts : List JasminTy}
    (A : AEnv Γ) (a : CarriedAnn) (p : NFProg jasminDialect Γ ts) (fuel : Nat)
    (V : Ctxt.Valuation Γ) (hA : EnvOK A V) :
    (entryRange A a p).denote fuel V = p.denote fuel V :=
  carriedGo_denote fuel A Γ.length a p V rfl hA

/-- At the full lane range of every input the entry form is `loopRange`. -/
theorem entryRange_topEnv {Γ : JCtxt} {ts : List JasminTy} (a : CarriedAnn)
    (p : NFProg jasminDialect Γ ts) : entryRange (topEnv Γ) a p = loopRange a p :=
  rfl

/-- The stage `entryRange A` as a chain step, at the annotation `syn p` computed from the
    input `p`. -/
def inputRangeStep {Γ : JCtxt} (ts : List JasminTy) (A : AEnv Γ)
    (syn : NFProg jasminDialect Γ ts → CarriedAnn) :
    PassChain.Step (NFProg jasminDialect Γ ts) (NFProg jasminDialect Γ ts) :=
  ⟨"range-carried-entry", fun p => some (entryRange A (syn p) p)⟩

/-- The certificate of `inputRangeStep`. The input relation is equality of the two
    valuations together with `EnvOK A` of the valuation; the output relation is equality.
    A successful run of the input at a valuation of which `A` holds is a run of the output
    with the same result. -/
def inputRangeCert [CallDenote jasminDialect] (fuel : Nat) {Γ : JCtxt} (ts : List JasminTy)
    (A : AEnv Γ) (syn : NFProg jasminDialect Γ ts → CarriedAnn) :
    PassChain.StepCert (inputRangeStep ts A syn).run (nfSem fuel jasminDialect Γ ts)
      (nfSem fuel jasminDialect Γ ts) where
  relIn V W := V = W ∧ EnvOK A V
  relOut := Eq
  sound := by
    intro p q V W o hf hVW hd
    obtain ⟨rfl, hA⟩ := hVW
    cases hf
    exact ⟨o, (entryRange_denote A (syn p) p fuel V hA).trans hd, rfl⟩

/-! ## 6. Instances

`acceptedLoops A len a p` counts the loops of `p` whose proposal in `a` the checker
accepts, in the environments of the traversal `carriedGo A len a p`.

`plainAddLoop` carries one 64-bit word `x` from the input `x₀` through `n` trips. Each trip
adds the constant `5` and subtracts the BabyBear prime `p = 2013265921` conditionally in
mask form, as `RangeNFLoop.lazyAddLoop` does, without the 31-bit mask of `x`. The
continuation masks the final word to 31 bits. The program has two `and` operations: the
mask with `p` and the 31-bit mask.

From the full lane range of `x₀` the body returns the full lane range, no interval below
it is inductive, and both `and` operations stay. Under `plainAddEnv`, with `x₀` in
`[0, p - 1]`, the start interval `[0, p - 1]` is inductive: the analysis gives the sum in
`[5, p + 4]`, the difference in `[5 - p, 4]` and the conditional add in `[0, p - 1]`. The
31-bit mask of the continuation becomes a copy (and the conditional add an unsigned minimum
under `RangeSelSyn.entrySel`). -/

/-- The number of loops of `p` whose proposed intervals the checker accepts, in the
    environments of `carriedGo A len a p`. -/
def acceptedLoops : {Γ : JCtxt} → {ts : List JasminTy} → AEnv Γ → Nat → CarriedAnn →
    NFProg jasminDialect Γ ts → Nat
  | _, _, _, _, _, .ret _ => 0
  | _, _, A, len, a, .var e k =>
      acceptedLoops (HVector.cons (f := fun _ => AVal) (stageAbs A e len) A) (len + 1) a k
  | _, _, A, len, a, .forLoop (cs := cs) _ inits body k =>
      (if forInductive A len a inits body then 1 else 0) +
        acceptedLoops
          (carriedEnv (forInductive A len a inits body) cs a.ivs
            (topCons (HasWord64.word (d := jasminDialect)) A))
          (cs.length + (len + 1)) a.inner body +
        acceptedLoops (carriedEnv (forInductive A len a inits body) cs a.ivs A)
          (cs.length + len) a.rest k
  | _, _, A, len, a, .ifThenElse (rs := rs) _ thn els k =>
      acceptedLoops A len a.inner thn + acceptedLoops A len a.other els +
        acceptedLoops (topApp rs A) (rs.length + len) a.rest k
  | _, _, A, len, a, .whileLoop (cs := cs) inits body k =>
      (if whileInductive A len a inits body then 1 else 0) +
        acceptedLoops (carriedEnv (whileInductive A len a inits body) cs a.ivs A)
          (cs.length + len) a.inner body +
        acceptedLoops (carriedEnv (whileInductive A len a inits body) cs a.ivs A)
          (cs.length + len) a.rest k
  | _, _, A, len, a, .call (rs := rs) _ _ k =>
      acceptedLoops (topApp rs A) (rs.length + len) a k

/-- The counted loop of this section over the start word `x₀` and the trip count `n`. -/
def plainAddLoop :
    NFProg jasminDialect [JasminTy.reg 64, JasminTy.reg 64] [JasminTy.reg 64] :=
  let body : NFProg jasminDialect
      [JasminTy.reg 64, JasminTy.reg 64, JasminTy.reg 64, JasminTy.reg 64]
      [JasminTy.reg 64] :=
    .var ⟨JasminOp.regConst 64 5, rfl, .nil⟩
    (.var ⟨JasminOp.regArith .add 64, rfl, .cons (.there .here) (.cons .here .nil)⟩
    (.var ⟨JasminOp.regConst 64 2013265921, rfl, .nil⟩
    (.var ⟨JasminOp.regConst 64 63, rfl, .nil⟩
    (.var ⟨JasminOp.regConst 64 0, rfl, .nil⟩
    (.var ⟨JasminOp.regArith .sub 64, rfl,
      .cons (.there (.there (.there .here))) (.cons (.there (.there .here)) .nil)⟩
    (.var ⟨JasminOp.regArith .shr 64, rfl,
      .cons .here (.cons (.there (.there .here)) .nil)⟩
    (.var ⟨JasminOp.regArith .sub 64, rfl,
      .cons (.there (.there .here)) (.cons .here .nil)⟩
    (.var ⟨JasminOp.regArith .and 64, rfl,
      .cons .here (.cons (.there (.there (.there (.there (.there .here))))) .nil)⟩
    (.var ⟨JasminOp.regArith .add 64, rfl,
      .cons (.there (.there (.there .here))) (.cons .here .nil)⟩
    (.ret (.cons .here .nil)))))))))))
  let k : NFProg jasminDialect [JasminTy.reg 64, JasminTy.reg 64, JasminTy.reg 64]
      [JasminTy.reg 64] :=
    .var ⟨JasminOp.regConst 64 2147483647, rfl, .nil⟩
    (.var ⟨JasminOp.regArith .and 64, rfl, .cons (.there .here) (.cons .here .nil)⟩
    (.ret (.cons .here .nil)))
  NFProg.forLoop (d := jasminDialect) (cs := [JasminTy.reg 64])
    (Γ := [JasminTy.reg 64, JasminTy.reg 64])
    (.there .here) (.cons .here .nil) body k

/-- The abstract environment of the inputs of `plainAddLoop`: the start word in
    `[0, p - 1]`, the trip count at the full lane range. -/
def plainAddEnv : AEnv [JasminTy.reg 64, JasminTy.reg 64] :=
  HVector.cons (f := fun _ => AVal) ((0, 2013265920), .none)
    (HVector.cons (f := fun _ => AVal) (tyTop (JasminTy.reg 64), .none) .nil)

/- On `lazyAddLoop` the synthesised interval of the carried word is `[0, p - 1]`, the
   interval of `lazyAddAnn`. The budget covers the start of the evaluator at the first
   check of the file. -/

/- On `lazyAddLoop` the synthesised interval of the carried word is `[0, p - 1]`, the
   interval of `lazyAddAnn`. The budget covers the start of the evaluator at the first
   check of the file. -/
set_option kat.ms 3000 in
#kat (synAnn lazyAddLoop).ivs == [(0, 2013265920)]

/- The checker accepts the synthesised annotation of the one loop of `lazyAddLoop`. -/
#kat acceptedLoops (topEnv _) 1 (synAnn lazyAddLoop) lazyAddLoop == 1

/- Under the synthesised annotation `loopRange` keeps one `and` operation, as under
   `lazyAddAnn`. -/
#kat andCount (synRange lazyAddLoop) == 1

/- `plainAddLoop` has two `and` operations. From the full lane range the synthesised
   interval is the full lane range and both operations stay. -/
#kat andCount plainAddLoop == 2
#kat (synAnn plainAddLoop).ivs == [tyTop (JasminTy.reg 64)]
#kat andCount (synRange plainAddLoop) == 2

/- From `plainAddEnv` the synthesised interval is `[0, p - 1]`, the checker accepts it, and
   one `and` operation stays. -/
#kat (entryAnn plainAddEnv plainAddLoop).ivs == [(0, 2013265920)]
#kat acceptedLoops plainAddEnv 2 (entryAnn plainAddEnv plainAddLoop) plainAddLoop == 1
#kat andCount (entryRange plainAddEnv (entryAnn plainAddEnv plainAddLoop) plainAddLoop) == 1

end CatCrypt.Crypto.Optimizer.Rewrite.RangeAnnSyn
