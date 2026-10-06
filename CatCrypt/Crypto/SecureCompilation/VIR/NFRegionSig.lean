/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NFProg

/-!
# The control signature of structured programs

A region signature lists, for each control operation, its argument types, its
regions and its output types, in the style of the MLIR dialects `scf` and `func`.
The four region constructors of `NFProg` (`forLoop`, `whileLoop`, `ifThenElse`,
`call`) are the operations of the sum of the signatures `RegionSig.scf` and
`RegionSig.func`; `NFProg.region` builds the constructor of an operation, and
`NFProg.regionCases` and `NFProg.regionRec` eliminate a program with one case for
all four.

A region binds a list of segments of types in front of the enclosing context. The
segments keep the context of a region definitionally equal to the context of the
corresponding constructor: the body of `forLoop` runs over `cs ++ word :: Γ`, which
is `RegionSig.scope [cs, [word]] Γ` by computation, whereas `(cs ++ [word]) ++ Γ`
equals it only propositionally.

| operation | `args` | `regs` (bound segments, results) | `outs` |
|---|---|---|---|
| `ScfOp.for cs` | `word :: cs` | `[([cs, [word]], cs)]` | `cs` |
| `ScfOp.while cs` | `cs` | `[([cs], bit :: cs)]` | `cs` |
| `ScfOp.if rs` | `[bit]` | `[([], rs), ([], rs)]` | `rs` |
| `FuncOp.call f as rs` | `as` | `[]` | `rs` |

## Main definitions

* `RegionSig` — a control signature over a type alphabet; `RegionSig.scope` — the
  context of a region.
* `RegionSig.ScfOp`, `RegionSig.scf` — the operations and the signature of the
  counted loop, the exit-flag loop and the branch.
* `RegionSig.FuncOp`, `RegionSig.func` — the operation and the signature of the call.
* `RegionSig.sum` — the sum of two signatures over one type alphabet.
* `RegionVal`, `RegionDenote` — the denotation of a region, and the fuelled
  denotation of the operations of a signature from the argument valuation and the
  region denotations; instances for `scf`, `func` and sums.
* `NFProg.regionSig` — the signature `scf + func` of a dialect.
* `NFProg.Regions`, `NFProg.region` — the regions of an operation as programs, and
  the constructor of an operation.
* `NFProg.scopeVal`, `NFProg.denoteRegions` — the valuation of a region context and
  the denotations of the regions of an operation.
* `NFProg.regionCases` — case analysis with one region case.
* `NFProg.RegionsHyps`, `NFProg.regionRec` — the recursor with one region case.

## Main results

* `NFProg.region_for`, `NFProg.region_while`, `NFProg.region_if`,
  `NFProg.region_call` — `region` at each operation is the constructor.
* `NFProg.denote_region_for`, `NFProg.denote_region_while`, `NFProg.denote_region_if`,
  `NFProg.denote_region_call` — the denotation of `region` at each operation is the
  operation denotation followed by the continuation, by `rfl`.
* `NFProg.denote_region` — the same equation for an arbitrary operation.
* `NFProg.regionCases_forLoop` and its three siblings, `NFProg.regionRec_forLoop` and
  its three siblings — the eliminators compute on the four constructors.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Ctxt (Var Valuation)
open MultiBlockLowering (hvAppend)

universe u

/-! ## 1. Region signatures -/

/-- A control signature over the type alphabet `T`: operations with argument types,
    regions and output types. A region is a list of segments of bound types and a
    list of result types. -/
structure RegionSig (T : Type) where
  /-- The control operations. -/
  Op : Type
  /-- The argument types of an operation. -/
  args : Op → List T
  /-- The regions of an operation: bound segments and result types. -/
  regs : Op → List (List (List T) × List T)
  /-- The output types of an operation. -/
  outs : Op → List T

namespace RegionSig

variable {T : Type}

/-- The context of a region with bound segments `bs` inside the context `Γ`: the
    segments in order, followed by `Γ`. -/
def scope : List (List T) → List T → List T
  | [], Γ => Γ
  | b :: bs, Γ => b ++ scope bs Γ

/-- The operations of structured control flow: a counted loop carrying `cs`, a loop
    in exit-flag form carrying `cs`, and a two-armed branch with results `rs`. -/
inductive ScfOp (T : Type) where
  /-- A counted loop carrying the tuple `cs`. -/
  | for (cs : List T)
  /-- A loop in exit-flag form carrying the tuple `cs`. -/
  | while (cs : List T)
  /-- A two-armed branch with the results `rs`. -/
  | if (rs : List T)

/-- The call operation: a symbol with its argument and result types. -/
inductive FuncOp (T : Type) where
  /-- A call of the symbol `f` at the signature `as → rs`. -/
  | call (f : String) (as rs : List T)

/-- The signature of structured control flow with trip-counter type `word` and bit
    type `bit`. The counted loop takes the trip count and the initial tuple, and its
    body binds the carried tuple and the trip index. The exit-flag loop takes the
    initial tuple, and its body binds the carried tuple and returns a bit in front of
    the next tuple. The branch takes a bit, and its two arms bind nothing. -/
def scf (word bit : T) : RegionSig T where
  Op := ScfOp T
  args
    | .for cs => word :: cs
    | .while cs => cs
    | .if _ => [bit]
  regs
    | .for cs => [([cs, [word]], cs)]
    | .while cs => [([cs], bit :: cs)]
    | .if rs => [([], rs), ([], rs)]
  outs
    | .for cs => cs
    | .while cs => cs
    | .if rs => rs

/-- The signature of calls: a call takes the arguments `as`, has no region and
    returns `rs`. -/
def func : RegionSig T where
  Op := FuncOp T
  args | .call _ as _ => as
  regs _ := []
  outs | .call _ _ rs => rs

/-- The sum of two signatures over one type alphabet: the operations are the tagged
    sum, and each component is that of the summand. -/
def sum (S₁ S₂ : RegionSig T) : RegionSig T where
  Op := S₁.Op ⊕ S₂.Op
  args := Sum.elim S₁.args S₂.args
  regs := Sum.elim S₁.regs S₂.regs
  outs := Sum.elim S₁.outs S₂.outs

end RegionSig

/-! ## 2. Denotation of the operations -/

/-- The denotation of a region: a partial function from the valuations of its bound
    segments to the valuation of its results. -/
abbrev RegionVal {d : Dialect.{0, 0}} [TyDenote d.Ty] (r : List (List d.Ty) × List d.Ty) :
    Type :=
  HVector (fun b : List d.Ty => Valuation (d := d) b) r.1 → Option (Valuation (d := d) r.2)

/-- The denotation of the operations of the signature `S` over the type denotation of
    the dialect `d`: at a fuel bound, from the valuation of the arguments and the
    denotations of the regions to the valuation of the outputs. -/
class RegionDenote (d : Dialect.{0, 0}) [TyDenote d.Ty] (S : RegionSig d.Ty) where
  /-- The denotation of the operation `o` at the fuel `fuel`. -/
  denote : (o : S.Op) → (fuel : Nat) → Valuation (d := d) (S.args o) →
    HVector (RegionVal (d := d)) (S.regs o) → Option (Valuation (d := d) (S.outs o))

section Instances

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

/-- Structured control flow denotes as the constructors of `NFProg` do: the counted
    loop is the `List.range` fold of its body, the exit-flag loop is `NFProg.whileIter`
    at the fuel, and the branch selects an arm by its bit. -/
instance RegionDenote.scf :
    RegionDenote d (RegionSig.scf (HasWord64.word (d := d)) (HasBitType.bit (d := d))) where
  denote
    | .for _, _, a, .cons body .nil =>
        (List.range (HasWord64.toNat (d := d) a.head)).foldlM
          (fun acc i => body (.cons acc (.cons (.cons (HasWord64.ofNat (d := d) i) .nil) .nil)))
          a.tail
    | .while _, fuel, a, .cons body .nil =>
        NFProg.whileIter (d := d) (fun acc => body (.cons acc .nil)) fuel a
    | .if _, _, a, .cons thn (.cons els .nil) =>
        if HasBoolBit.toBool (d := d) a.head then thn .nil else els .nil

/-- A call denotes the callee of the environment `CallDenote.env`. -/
instance RegionDenote.func [CallDenote d] : RegionDenote d (RegionSig.func (T := d.Ty)) where
  denote
    | .call f as rs, _, a, _ => (CallDenote.env (d := d)).call f as rs a

/-- A sum of signatures denotes each operation in its summand. -/
instance RegionDenote.sum {S₁ S₂ : RegionSig d.Ty} [RegionDenote d S₁] [RegionDenote d S₂] :
    RegionDenote d (S₁.sum S₂) where
  denote
    | .inl o => RegionDenote.denote (d := d) (S := S₁) o
    | .inr o => RegionDenote.denote (d := d) (S := S₂) o

end Instances

namespace NFProg

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

/-! ## 3. The constructor of an operation -/

variable (d) in
/-- The control signature of the structured programs of `d`: structured control flow
    at the dialect's word and bit types, and calls. -/
abbrev regionSig : RegionSig d.Ty :=
  (RegionSig.scf (HasWord64.word (d := d)) (HasBitType.bit (d := d))).sum RegionSig.func

/-- The regions `rs` as programs inside the context `Γ`: one program per region, over
    the region's context and returning its results. -/
abbrev Regions (d : Dialect.{0, 0}) [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
    [HasBoolBit d] (Γ : Ctxt d) (rs : List (List (List d.Ty) × List d.Ty)) : Type :=
  HVector (fun r => NFProg d (RegionSig.scope r.1 Γ) r.2) rs

/-- The program of the operation `o` on the arguments `args` with the regions `regs`
    and the continuation `k` over the outputs: the corresponding constructor of
    `NFProg`. -/
def region {Γ : Ctxt d} {ts : List d.Ty} : (o : (regionSig d).Op) →
    HVector (fun t => Var Γ t) ((regionSig d).args o) → Regions d Γ ((regionSig d).regs o) →
    NFProg d ((regionSig d).outs o ++ Γ) ts → NFProg d Γ ts
  | .inl (.for _), .cons count inits, .cons body .nil, k => .forLoop count inits body k
  | .inl (.while _), inits, .cons body .nil, k => .whileLoop inits body k
  | .inl (.if _), .cons cond .nil, .cons thn (.cons els .nil), k => .ifThenElse cond thn els k
  | .inr (.call f _ _), args, .nil, k => .call f args k

/-- `region` at the counted loop is `forLoop`. -/
theorem region_for {Γ : Ctxt d} {cs ts : List d.Ty}
    (count : Var Γ (HasWord64.word (d := d))) (inits : HVector (fun t => Var Γ t) cs)
    (body : NFProg d (cs ++ HasWord64.word (d := d) :: Γ) cs) (k : NFProg d (cs ++ Γ) ts) :
    region (.inl (.for cs)) (.cons count inits) (.cons body .nil) k =
      .forLoop count inits body k := rfl

/-- `region` at the exit-flag loop is `whileLoop`. -/
theorem region_while {Γ : Ctxt d} {cs ts : List d.Ty} (inits : HVector (fun t => Var Γ t) cs)
    (body : NFProg d (cs ++ Γ) (HasBitType.bit (d := d) :: cs)) (k : NFProg d (cs ++ Γ) ts) :
    region (.inl (.while cs)) inits (.cons body .nil) k = .whileLoop inits body k := rfl

/-- `region` at the branch is `ifThenElse`. -/
theorem region_if {Γ : Ctxt d} {rs ts : List d.Ty} (cond : Var Γ (HasBitType.bit (d := d)))
    (thn els : NFProg d Γ rs) (k : NFProg d (rs ++ Γ) ts) :
    region (.inl (.if rs)) (.cons cond .nil) (.cons thn (.cons els .nil)) k =
      .ifThenElse cond thn els k := rfl

/-- `region` at the call is `call`. -/
theorem region_call {Γ : Ctxt d} {as rs ts : List d.Ty} (f : String)
    (args : HVector (fun t => Var Γ t) as) (k : NFProg d (rs ++ Γ) ts) :
    region (.inr (.call f as rs)) args .nil k = .call f args k := rfl

/-! ## 4. Denotation of the constructor of an operation -/

/-- The valuation of a region context: the valuations of the bound segments in order,
    followed by the valuation of the enclosing context. -/
def scopeVal {Γ : Ctxt d} : {bs : List (List d.Ty)} →
    HVector (fun b : List d.Ty => Valuation (d := d) b) bs → Valuation Γ →
    Valuation (d := d) (RegionSig.scope bs Γ)
  | [], .nil, V => V
  | _ :: _, .cons b B, V => hvAppend b (scopeVal B V)

variable [DialectDenoteM d Option] [CallDenote d]

/-- The denotations of the regions `regs` at the fuel `fuel` inside the valuation `V`
    of the enclosing context. -/
def denoteRegions (fuel : Nat) {Γ : Ctxt d} (V : Valuation Γ) :
    {rs : List (List (List d.Ty) × List d.Ty)} → Regions d Γ rs →
    HVector (RegionVal (d := d)) rs
  | [], .nil => .nil
  | _ :: _, .cons p ps => .cons (fun B => p.denote fuel (scopeVal B V)) (denoteRegions fuel V ps)

/-- The counted loop built by `region` denotes the operation denotation, then its
    continuation at the final tuple. -/
theorem denote_region_for {Γ : Ctxt d} {cs ts : List d.Ty}
    (count : Var Γ (HasWord64.word (d := d))) (inits : HVector (fun t => Var Γ t) cs)
    (body : NFProg d (cs ++ HasWord64.word (d := d) :: Γ) cs) (k : NFProg d (cs ++ Γ) ts)
    (fuel : Nat) (V : Valuation Γ) :
    (region (.inl (.for cs)) (.cons count inits) (.cons body .nil) k).denote fuel V =
      RegionDenote.denote (d := d) (S := regionSig d) (.inl (.for cs)) fuel
          (Expr.lookupArgs (HVector.cons count inits) V)
          (denoteRegions fuel V (.cons body .nil)) >>= fun acc =>
        k.denote fuel (hvAppend acc V) := rfl

/-- The exit-flag loop built by `region` denotes the operation denotation, then its
    continuation at the final tuple. -/
theorem denote_region_while {Γ : Ctxt d} {cs ts : List d.Ty}
    (inits : HVector (fun t => Var Γ t) cs)
    (body : NFProg d (cs ++ Γ) (HasBitType.bit (d := d) :: cs)) (k : NFProg d (cs ++ Γ) ts)
    (fuel : Nat) (V : Valuation Γ) :
    (region (.inl (.while cs)) inits (.cons body .nil) k).denote fuel V =
      RegionDenote.denote (d := d) (S := regionSig d) (.inl (.while cs)) fuel
          (Expr.lookupArgs inits V) (denoteRegions fuel V (.cons body .nil)) >>= fun acc =>
        k.denote fuel (hvAppend acc V) := rfl

/-- The branch built by `region` denotes the operation denotation, then its
    continuation at the results. -/
theorem denote_region_if {Γ : Ctxt d} {rs ts : List d.Ty}
    (cond : Var Γ (HasBitType.bit (d := d))) (thn els : NFProg d Γ rs)
    (k : NFProg d (rs ++ Γ) ts) (fuel : Nat) (V : Valuation Γ) :
    (region (.inl (.if rs)) (.cons cond .nil) (.cons thn (.cons els .nil)) k).denote fuel V =
      RegionDenote.denote (d := d) (S := regionSig d) (.inl (.if rs)) fuel
          (Expr.lookupArgs (HVector.cons cond .nil) V)
          (denoteRegions fuel V (.cons thn (.cons els .nil))) >>= fun r =>
        k.denote fuel (hvAppend r V) := rfl

/-- The call built by `region` denotes the operation denotation, then its continuation
    at the results. -/
theorem denote_region_call {Γ : Ctxt d} {as rs ts : List d.Ty} (f : String)
    (args : HVector (fun t => Var Γ t) as) (k : NFProg d (rs ++ Γ) ts)
    (fuel : Nat) (V : Valuation Γ) :
    (region (.inr (.call f as rs)) args .nil k).denote fuel V =
      RegionDenote.denote (d := d) (S := regionSig d) (.inr (.call f as rs)) fuel
          (Expr.lookupArgs args V) (denoteRegions fuel V .nil) >>= fun r =>
        k.denote fuel (hvAppend r V) := rfl

/-- The program of an operation denotes the operation denotation at the valuation of
    its arguments and the denotations of its regions, then its continuation at the
    outputs. -/
theorem denote_region {Γ : Ctxt d} {ts : List d.Ty} (o : (regionSig d).Op)
    (args : HVector (fun t => Var Γ t) ((regionSig d).args o))
    (regs : Regions d Γ ((regionSig d).regs o))
    (k : NFProg d ((regionSig d).outs o ++ Γ) ts) (fuel : Nat) (V : Valuation Γ) :
    (region o args regs k).denote fuel V =
      RegionDenote.denote (d := d) (S := regionSig d) o fuel (Expr.lookupArgs args V)
          (denoteRegions fuel V regs) >>= fun r =>
        k.denote fuel (hvAppend r V) := by
  rcases o with (cs | cs | rs) | ⟨f, as, rs⟩
  · match args, regs with
    | .cons count inits, .cons body .nil => rfl
  · match regs with
    | .cons body .nil => rfl
  · match args, regs with
    | .cons cond .nil, .cons thn (.cons els .nil) => rfl
  · match regs with
    | .nil => rfl

end NFProg

/-! ## 5. Eliminators with one region case -/

namespace NFProg

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

section Cases

variable {motive : (Γ : Ctxt d) → (ts : List d.Ty) → NFProg d Γ ts → Sort u}
  (ret : ∀ {Γ ts} (vs : HVector (fun t => Var Γ t) ts), motive Γ ts (.ret vs))
  (var : ∀ {Γ t ts} (e : Expr d Γ t) (k : NFProg d (t :: Γ) ts), motive Γ ts (.var e k))
  (region : ∀ {Γ ts} (o : (regionSig d).Op)
    (args : HVector (fun t => Var Γ t) ((regionSig d).args o))
    (regs : Regions d Γ ((regionSig d).regs o))
    (k : NFProg d ((regionSig d).outs o ++ Γ) ts), motive Γ ts (NFProg.region o args regs k))

/-- Case analysis on a structured program with one case for the four region
    constructors: a return, a let-binding, or the program of an operation. -/
def regionCases :
    {Γ : Ctxt d} → {ts : List d.Ty} → (p : NFProg d Γ ts) → motive Γ ts p
  | _, _, .ret vs => ret vs
  | _, _, .var e k => var e k
  | _, _, .forLoop (cs := cs) count inits body k =>
      region (.inl (.for cs)) (.cons count inits) (.cons body .nil) k
  | _, _, .ifThenElse (rs := rs) cond thn els k =>
      region (.inl (.if rs)) (.cons cond .nil) (.cons thn (.cons els .nil)) k
  | _, _, .whileLoop (cs := cs) inits body k =>
      region (.inl (.while cs)) inits (.cons body .nil) k
  | _, _, .call (as := as) (rs := rs) f args k =>
      region (.inr (.call f as rs)) args .nil k

/-- `regionCases` at `forLoop` is the region case at the counted loop. -/
theorem regionCases_forLoop {Γ : Ctxt d} {cs ts : List d.Ty}
    (count : Var Γ (HasWord64.word (d := d))) (inits : HVector (fun t => Var Γ t) cs)
    (body : NFProg d (cs ++ HasWord64.word (d := d) :: Γ) cs) (k : NFProg d (cs ++ Γ) ts) :
    regionCases (motive := motive) ret var region (.forLoop count inits body k) =
      region (.inl (.for cs)) (.cons count inits) (.cons body .nil) k := rfl

/-- `regionCases` at `whileLoop` is the region case at the exit-flag loop. -/
theorem regionCases_whileLoop {Γ : Ctxt d} {cs ts : List d.Ty}
    (inits : HVector (fun t => Var Γ t) cs)
    (body : NFProg d (cs ++ Γ) (HasBitType.bit (d := d) :: cs)) (k : NFProg d (cs ++ Γ) ts) :
    regionCases (motive := motive) ret var region (.whileLoop inits body k) =
      region (.inl (.while cs)) inits (.cons body .nil) k := rfl

/-- `regionCases` at `ifThenElse` is the region case at the branch. -/
theorem regionCases_ifThenElse {Γ : Ctxt d} {rs ts : List d.Ty}
    (cond : Var Γ (HasBitType.bit (d := d))) (thn els : NFProg d Γ rs)
    (k : NFProg d (rs ++ Γ) ts) :
    regionCases (motive := motive) ret var region (.ifThenElse cond thn els k) =
      region (.inl (.if rs)) (.cons cond .nil) (.cons thn (.cons els .nil)) k := rfl

/-- `regionCases` at `call` is the region case at the call. -/
theorem regionCases_call {Γ : Ctxt d} {as rs ts : List d.Ty} (f : String)
    (args : HVector (fun t => Var Γ t) as) (k : NFProg d (rs ++ Γ) ts) :
    regionCases (motive := motive) ret var region (.call (rs := rs) f args k) =
      region (.inr (.call f as rs)) args .nil k := rfl

end Cases

/-- The motive at every region of `regs`: the iterated product of the motive at each
    program. It is the induction hypothesis for the regions of an operation. -/
def RegionsHyps (motive : (Γ : Ctxt d) → (ts : List d.Ty) → NFProg d Γ ts → Sort u)
    {Γ : Ctxt d} : {rs : List (List (List d.Ty) × List d.Ty)} → Regions d Γ rs → Sort (max 1 u)
  | [], .nil => PUnit
  | _ :: _, .cons p ps => motive _ _ p ×' RegionsHyps motive ps

section Rec

variable {motive : (Γ : Ctxt d) → (ts : List d.Ty) → NFProg d Γ ts → Sort u}
  (ret : ∀ {Γ ts} (vs : HVector (fun t => Var Γ t) ts), motive Γ ts (.ret vs))
  (var : ∀ {Γ t ts} (e : Expr d Γ t) (k : NFProg d (t :: Γ) ts), motive (t :: Γ) ts k →
    motive Γ ts (.var e k))
  (region : ∀ {Γ ts} (o : (regionSig d).Op)
    (args : HVector (fun t => Var Γ t) ((regionSig d).args o))
    (regs : Regions d Γ ((regionSig d).regs o))
    (k : NFProg d ((regionSig d).outs o ++ Γ) ts), RegionsHyps motive regs → motive _ ts k →
    motive Γ ts (NFProg.region o args regs k))

/-- The recursor of structured programs with one case for the four region
    constructors: the region case receives the motive at every region and at the
    continuation. -/
def regionRec :
    {Γ : Ctxt d} → {ts : List d.Ty} → (p : NFProg d Γ ts) → motive Γ ts p
  | _, _, .ret vs => ret vs
  | _, _, .var e k => var e k (regionRec k)
  | _, _, .forLoop (cs := cs) count inits body k =>
      region (.inl (.for cs)) (.cons count inits) (.cons body .nil) k
        ⟨regionRec body, ⟨⟩⟩ (regionRec k)
  | _, _, .ifThenElse (rs := rs) cond thn els k =>
      region (.inl (.if rs)) (.cons cond .nil) (.cons thn (.cons els .nil)) k
        ⟨regionRec thn, regionRec els, ⟨⟩⟩ (regionRec k)
  | _, _, .whileLoop (cs := cs) inits body k =>
      region (.inl (.while cs)) inits (.cons body .nil) k
        ⟨regionRec body, ⟨⟩⟩ (regionRec k)
  | _, _, .call (as := as) (rs := rs) f args k =>
      region (.inr (.call f as rs)) args .nil k ⟨⟩ (regionRec k)

/-- `regionRec` at `forLoop` is the region case at the counted loop, with the
    recursive values at the body and the continuation. -/
theorem regionRec_forLoop {Γ : Ctxt d} {cs ts : List d.Ty}
    (count : Var Γ (HasWord64.word (d := d))) (inits : HVector (fun t => Var Γ t) cs)
    (body : NFProg d (cs ++ HasWord64.word (d := d) :: Γ) cs) (k : NFProg d (cs ++ Γ) ts) :
    regionRec (motive := motive) ret var region (.forLoop count inits body k) =
      region (.inl (.for cs)) (.cons count inits) (.cons body .nil) k
        ⟨regionRec ret var region body, ⟨⟩⟩ (regionRec ret var region k) := rfl

/-- `regionRec` at `whileLoop` is the region case at the exit-flag loop, with the
    recursive values at the body and the continuation. -/
theorem regionRec_whileLoop {Γ : Ctxt d} {cs ts : List d.Ty}
    (inits : HVector (fun t => Var Γ t) cs)
    (body : NFProg d (cs ++ Γ) (HasBitType.bit (d := d) :: cs)) (k : NFProg d (cs ++ Γ) ts) :
    regionRec (motive := motive) ret var region (.whileLoop inits body k) =
      region (.inl (.while cs)) inits (.cons body .nil) k
        ⟨regionRec ret var region body, ⟨⟩⟩ (regionRec ret var region k) := rfl

/-- `regionRec` at `ifThenElse` is the region case at the branch, with the recursive
    values at the two arms and the continuation. -/
theorem regionRec_ifThenElse {Γ : Ctxt d} {rs ts : List d.Ty}
    (cond : Var Γ (HasBitType.bit (d := d))) (thn els : NFProg d Γ rs)
    (k : NFProg d (rs ++ Γ) ts) :
    regionRec (motive := motive) ret var region (.ifThenElse cond thn els k) =
      region (.inl (.if rs)) (.cons cond .nil) (.cons thn (.cons els .nil)) k
        ⟨regionRec ret var region thn, regionRec ret var region els, ⟨⟩⟩
        (regionRec ret var region k) := rfl

/-- `regionRec` at `call` is the region case at the call, with the recursive value at
    the continuation. -/
theorem regionRec_call {Γ : Ctxt d} {as rs ts : List d.Ty} (f : String)
    (args : HVector (fun t => Var Γ t) as) (k : NFProg d (rs ++ Γ) ts) :
    regionRec (motive := motive) ret var region (.call (rs := rs) f args k) =
      region (.inr (.call f as rs)) args .nil k ⟨⟩ (regionRec ret var region k) := rfl

end Rec

end NFProg

end CatCrypt.Crypto.SecureCompilation.VIR
