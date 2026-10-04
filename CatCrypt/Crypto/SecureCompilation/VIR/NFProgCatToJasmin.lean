/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgMap
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgJasmin
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgToComL
public import CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLJLeak

/-!
# The translation of `catCryptDialect` to `jasminDialect` as a partial block lowering

`catToJasmin` is the partial block lowering from `catCryptDialect` to `jasminDialect`
whose type, context and variable maps are `mapTy`, `mapCtx` and `toJVarD`, and whose
block of an expression `e` is the one-binding block of `toJExprD e`, or `none` where
`toJExprD` refuses `e`. Its leaves are the existing theorems of
`DialectToJasminComCorrect`: `ctMapValD_lookup`, `ctMapValD_extend` and
`dialectJasminLeafAgrees_holds`, which has no side condition. `NFProg.map?` along it
lowers an `NFProg catCryptDialect` to an `NFProg jasminDialect`.

`jasminNFToComLAt` maps an `NFProg jasminDialect` program with one result, built from
let-bindings, a return and counted loops carrying one value with a straight-line body,
to `ComL`, selecting the invariants of a loop with `usedSel` and restricting its body
with `comRestrict`; every other program is `none`. `nfToComLVia` is `NFProg.map?` along
`catToJasmin` followed by `jasminNFToComLAt`.

`jasminNFToComLJAt` maps an `NFProg jasminDialect` program with one result, built from
let-bindings, a return, counted loops and do-whiles carrying any tuple with a straight-line
body (`NFProg.toMulti?`), to `ComLJ`: a counted loop to `ComLJ.forLoopRegs`, a do-while to
`ComLJ.whileRegs`, each body restricted (`MultiReturnCom.restrict?`) to the outer variables
it reads (`MultiReturnCom.usedSelM`). A branch, and a loop whose body contains a region, is
`none`. `nfToComLJVia` is the lifted `nfToComLVia` program where that exists, and otherwise
`NFProg.map?` along `catToJasmin` followed by `jasminNFToComLJAt`.

## Main definitions

* `catToJasmin` — the partial block lowering.
* `jasminNFToComLAt`, `jasminNFToComL` — the lowering of the one-carried fragment of
  `NFProg jasminDialect` to `ComL`.
* `nfToComLVia` — the lowering of `NFProg catCryptDialect` to `ComL` through
  `NFProg jasminDialect`.
* `jforNodeJ`, `jwhileNodeJ`, `jasminNFToComLJAt` — the lowering of the carried-register
  fragment of `NFProg jasminDialect` to `ComLJ`.
* `nfToComLJVia` — the lowering of `NFProg catCryptDialect` to `ComLJ`.

## Main results

* `catToJasmin_map?_denote` — `map?` along `catToJasmin` preserves denotation.
* `jasminNFToComLAt_denote` — `jasminNFToComLAt` preserves denotation.
* `nfToComLVia_denote` — `nfToComLVia` preserves denotation, in the statement of
  `NFProgToComL.nfToComL_denote`.
* `nfToComLVia_agrees` — where `nfToComLVia` and `nfToComL` both return a program, the
  two programs denote the same value on every transported valuation.
* `multiRestrict_ctLeak` — the restriction of a multi-result program keeps its events.
* `jasminNFToComLJAt_denote`, `jasminNFToComLJAt_leakRun`, `jasminNFToComLJAt_ctLeak` —
  `jasminNFToComLJAt` preserves the denotation, the leakage run and the events at equal
  fuel, both sides failing together.
* `nfToComLJVia_denote` — `nfToComLJVia` preserves denotation at equal fuel.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgToComL
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)

/-! ## 1. The partial block lowering -/

/-- **The translation of `catCryptDialect` to `jasminDialect` as a partial block
    lowering.** An expression lowers to the one-binding block of `toJExprD`, and is
    refused where `toJExprD` is `none`. -/
def catToJasmin : PartialBlockLowering catCryptDialect jasminDialect where
  mapTy := mapTy
  mapCtx := mapCtx
  mapCtx_cons _ _ := rfl
  mapVar := toJVarD
  lowerExprBlock? e := (toJExprD e).map fun e' => .var e' (.ret .here)

/-- The trip counter `sword 64` maps to `reg 64` and the bit `bit` to `reg 1`. -/
theorem catToJasmin_regionTypes : catToJasmin.RegionTypes := ⟨rfl, rfl⟩

/-- The variable leaf of `catToJasmin` is `ctMapValD_lookup`. -/
theorem catToJasmin_varTransports :
    catToJasmin.VarTransports (fun x => ctTransTy x) ctMapValD :=
  fun v V => ctMapValD_lookup v V

/-- The binding-threading leaf of `catToJasmin` is `ctMapValD_extend`. -/
theorem catToJasmin_mapValExtends :
    catToJasmin.MapValExtends (fun x => ctTransTy x) ctMapValD :=
  fun V x => ctMapValD_extend V x

/-- The block leaf of `catToJasmin` is `dialectJasminLeafAgrees_holds`: a block the
    lowering gives an expression denotes, on the transported valuation, the transport
    of the expression's value. -/
theorem catToJasmin_block {Γ : Ctx} {t : CryptoTy} (e : Expr catCryptDialect Γ t)
    (blk : Com jasminDialect (mapCtx Γ) (mapTy t))
    (hblk : catToJasmin.lowerExprBlock? e = some blk)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) :
    blk.denote (ctMapValD V) = ctTransTy (e.denote V) := by
  obtain ⟨e', he, rfl⟩ := Option.map_eq_some_iff.mp hblk
  exact dialectJasminLeafAgrees_holds e V e' he

/-- The value transport `ctTransTy` keeps the trip count, sends the trip index to the
    trip index, and reads a transported bit as the source bit. -/
theorem catToJasmin_regionTransports :
    catToJasmin.RegionTransports catToJasmin_regionTypes (fun x => ctTransTy x) where
  toNat_trans _ := rfl
  ofNat_trans _ := rfl
  toBool_trans b := by cases b <;> rfl

/-- **Preservation along `catToJasmin`.** A program that `map?` returns for an
    `NFProg catCryptDialect` program, at a renaming relating `W` to `ctMapValD V`,
    denotes at every fuel the `ctTransTy` transport of the source denotation. -/
theorem catToJasmin_map?_denote (fuel : Nat) {Γ : Ctx} {ts : List CryptoTy}
    (p : NFProg catCryptDialect Γ ts) {Δ : Ctxt jasminDialect}
    (ren : Ctxt.Hom (mapCtx Γ) Δ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
    (W : Ctxt.Valuation Δ) (hren : FieldDialectBlockDescent.pullV ren W = ctMapValD V)
    (q : NFProg jasminDialect Δ (ts.map mapTy))
    (hq : NFProg.map? catToJasmin catToJasmin_regionTypes p ren = some q) :
    q.denote fuel W = (p.denote fuel V).map (BlockLoweringExtend.transArgs mapTy (fun x => ctTransTy x)) :=
  NFProg.map?_denote catToJasmin (fun x => ctTransTy x) ctMapValD catToJasmin_regionTypes
    (fun _ => True) catToJasmin_varTransports
    (fun e _ blk hblk V => catToJasmin_block e blk hblk V)
    catToJasmin_mapValExtends catToJasmin_regionTransports fuel p
    (NFProg.covered_of_forall _ (fun _ => trivial) p) ren V W hren q hq

/-! ## 2. The one-carried fragment of `NFProg jasminDialect` to `ComL` -/

/-- The `ComL.forLoopNRt` node of a counted loop of `NFProg jasminDialect` carrying the
    tuple `cs`, with the lowered continuation `k'`: `none` unless `cs` is one type and
    the body is straight-line (`NFProg.toCom?`). The invariants are the outer variables
    the body reads (`usedSel`), and the body is restricted to them (`comRestrict`). -/
def jforNode {Γ : Ctxt jasminDialect} {t : JasminTy} : {cs : List JasminTy} →
    Ctxt.Var Γ (HasWord64.word (d := jasminDialect)) →
    HVector (fun ty => Ctxt.Var Γ ty) cs →
    NFProg jasminDialect (cs ++ HasWord64.word (d := jasminDialect) :: Γ) cs →
    ComL (cs ++ Γ) t → Option (ComL Γ t)
  | [], _, .nil, _, _ => none
  | [_], count, .cons init .nil, body, k' =>
      body.toCom?.bind fun bc =>
        (comRestrict bc (VMap.lift (VMap.lift (findIn (usedSel bc).2)))).map fun bc' =>
          ComL.forLoopNRt (invTys := (usedSel bc).1) bc' count init (usedSel bc).2 k'
  | _ :: _ :: _, _, .cons _ (.cons _ _), _, _ => none

/-- Lower an `NFProg jasminDialect` program with the one result `t` (`ts = [t]`) to
    `ComL`. `none` on a branch, an exit-flag loop, a call, and a counted loop carrying other
    than one value or with a body that is not straight-line. -/
def jasminNFToComLAt : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} →
    NFProg jasminDialect Γ ts → (t : JasminTy) → ts = [t] → Option (ComL Γ t)
  | _, _, .ret vs, _, h => by
      subst h
      exact match vs with
        | .cons v .nil => some (.ret v)
  | _, _, .var e k, t, h => (jasminNFToComLAt k t h).map fun k' => .var e k'
  | _, _, .forLoop count inits body k, t, h =>
      (jasminNFToComLAt k t h).bind (jforNode count inits body)
  | _, _, .ifThenElse .., _, _ => none
  | _, _, .whileLoop .., _, _ => none
  | _, _, .call .., _, _ => none

/-- Lower an `NFProg jasminDialect` program with one result to `ComL`
    (`jasminNFToComLAt` at `ts = [t]`). -/
def jasminNFToComL {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) : Option (ComL Γ t) :=
  jasminNFToComLAt p t rfl

/-- **Preservation.** When `jasminNFToComLAt p t h = some c`, the program `p` denotes,
    at every fuel, `some` of the one value `c` denotes. -/
theorem jasminNFToComLAt_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (t : JasminTy) (h : ts = [t]) (c : ComL Γ t)
    (hc : jasminNFToComLAt p t h = some c) (fuel : Nat) (W : Ctxt.Valuation Γ) :
    p.denote fuel W = some (h ▸ .cons (c.denote W) .nil) := by
  induction p with
  | ret vs =>
      subst h
      rcases vs with _ | ⟨v, _ | _⟩
      have hr : jasminNFToComLAt (.ret (.cons v .nil)) t rfl = some (.ret v) := rfl
      rw [hr, Option.some.injEq] at hc
      subst hc
      rfl
  | var e k ih =>
      subst h
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hc
      simp only [NFProg.denote, Expr.denoteM_option_eq_some, Option.bind_eq_bind,
        Option.bind_some]
      exact ih rfl k' hk' _
  | forLoop count inits body k _ ihk =>
      obtain ⟨k', hk, hc⟩ := Option.bind_eq_some_iff.mp hc
      rcases inits with _ | ⟨init, _ | _⟩
      · simp [jforNode] at hc
      · obtain ⟨bc, hbc, hc⟩ := Option.bind_eq_some_iff.mp hc
        obtain ⟨bc', hr, rfl⟩ := Option.map_eq_some_iff.mp hc
        have hsel : ∀ (a : ⟦_⟧) (i : Nat),
            bc'.denote (.cons a (.cons (BitVec.ofNat 64 i) (Expr.lookupArgs (usedSel bc).2 W))) =
              bc.denote (.cons a (.cons (BitVec.ofNat 64 i) W)) := fun a i =>
          comRestrict_denote bc _ bc' hr _ _
            (VMap.agree_lift (VMap.agree_lift (findIn_agree W (usedSel bc).2) _) _)
        have hfold := NFProg.foldlM_single (d := jasminDialect)
          (fun acc i => body.denote fuel
            (MultiBlockLowering.hvAppend acc
              (.cons (HasWord64.ofNat (d := jasminDialect) i) W)))
          (fun a i => bc.denote (.cons a (.cons (BitVec.ofNat 64 i) W)))
          (fun a i => NFProg.denote_of_toCom? body hbc fuel _)
          (List.range (count.lookup W).toNat) (init.lookup W)
        have hX : (List.range (count.lookup W).toNat).foldl
            (fun acc t => JLoopBodyN.stepC bc' (Expr.lookupArgs (usedSel bc).2 W) t acc)
            (init.lookup W) =
            (List.range (count.lookup W).toNat).foldl
              (fun a i => bc.denote (.cons a (.cons (BitVec.ofNat 64 i) W)))
              (init.lookup W) := by
          simp only [JLoopBodyN.stepC, hsel]
        rw [NFProg.denote_forLoop]
        refine (congrArg (· >>= _) hfold).trans ?_
        refine Eq.trans (ihk h k' hk _) ?_
        simp only [ComL.denote, hX]
        rfl
      · simp [jforNode] at hc
  | ifThenElse => simp [jasminNFToComLAt] at hc
  | whileLoop => simp [jasminNFToComLAt] at hc
  | call => simp [jasminNFToComLAt] at hc

/-! ## 3. The carried-register fragment of `NFProg jasminDialect` to `ComLJ` -/

section ComLJExport

open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLJLeak

/-- **Restriction keeps the events** of a multi-result program: a program restricted along
    `f` emits, at a valuation `f` relates, the events of the program. -/
theorem multiRestrict_ctLeak {d : Dialect} [DialectSignature d] [TyDenote d.Ty]
    [DialectDenote d] (M : LeakModel d) : {Γ Γ' : Ctxt d} → {ts : List d.Ty} →
    (m : MultiReturnCom d Γ ts) → (f : VMap Γ Γ') → (m' : MultiReturnCom d Γ' ts) →
    m.restrict? f = some m' → (V : Ctxt.Valuation Γ) → (V' : Ctxt.Valuation Γ') →
    VMap.Agree f V V' → m'.ctLeak M V' = m.ctLeak M V
  | _, _, _, .ret vs, f, m', h, V, V', _ => by
      obtain ⟨ws, _, rfl⟩ := Option.map_eq_some_iff.mp h
      rfl
  | _, _, _, .var e k, f, m', h, V, V', hag => by
      obtain ⟨as, has, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp h
      have hargs := VMap.lookupArgs_args hag e.args as has
      have he : (⟨e.op, e.retTy_eq, as⟩ : Expr d _ _).denote V' = e.denote V := by
        unfold Expr.denote
        rw [hargs]
      change Expr.ctLeak M (⟨e.op, e.retTy_eq, as⟩ : Expr d _ _) V' ++
          MultiReturnCom.ctLeak M k'
            (V'.extend ((⟨e.op, e.retTy_eq, as⟩ : Expr d _ _).denote V')) =
        Expr.ctLeak M e V ++ MultiReturnCom.ctLeak M k (V.extend (e.denote V))
      rw [he, multiRestrict_ctLeak M k (VMap.lift f) k' hk' _ _ (VMap.agree_lift hag _)]
      unfold Expr.ctLeak
      rw [hargs]

/-- The outer variables the straight-line body `m` of a counted loop over
    `cs ++ word :: Γ` reads (`MultiReturnCom.usedSelM` at `cs.length + 1` local binders). -/
abbrev forSelJ {Γ : Ctxt jasminDialect} {cs : List JasminTy}
    (m : MultiReturnCom jasminDialect (cs ++ HasWord64.word (d := jasminDialect) :: Γ) cs) :
    Σ Γ' : Ctxt jasminDialect, HVector (fun ty => Ctxt.Var Γ ty) Γ' :=
  MultiReturnCom.usedSelM Γ (cs.length + 1) m

/-- The outer variables the straight-line body `m` of a do-while over `cs ++ Γ` reads
    (`MultiReturnCom.usedSelM` at `cs.length` local binders). -/
abbrev whileSelJ {Γ : Ctxt jasminDialect} {cs : List JasminTy}
    (m : MultiReturnCom jasminDialect (cs ++ Γ) (HasBitType.bit (d := jasminDialect) :: cs)) :
    Σ Γ' : Ctxt jasminDialect, HVector (fun ty => Ctxt.Var Γ ty) Γ' :=
  MultiReturnCom.usedSelM Γ cs.length m

/-- The `ComLJ.forLoopRegs` node of a counted loop of `NFProg jasminDialect` carrying the
    tuple `cs`, with the lowered continuation `k'`: `none` unless the body is straight-line
    (`NFProg.toMulti?`). The invariants are the outer variables the body reads
    (`forSelJ`), and the body is restricted to them (`MultiReturnCom.restrict?`). -/
def jforNodeJ {Γ : Ctxt jasminDialect} {t : JasminTy} {cs : List JasminTy}
    (count : Ctxt.Var Γ (HasWord64.word (d := jasminDialect)))
    (inits : HVector (fun ty => Ctxt.Var Γ ty) cs)
    (body : NFProg jasminDialect (cs ++ HasWord64.word (d := jasminDialect) :: Γ) cs)
    (k' : ComLJ (cs ++ Γ) t) : Option (ComLJ Γ t) :=
  body.toMulti?.bind fun m =>
    (m.restrict? (VMap.liftApp (VMap.lift (findIn (forSelJ m).2)) cs)).map fun m' =>
      ComLJ.forLoopRegs (invTys := (forSelJ m).1) m' count inits (forSelJ m).2 k'

/-- The `ComLJ.whileRegs` node of a do-while of `NFProg jasminDialect` carrying the tuple
    `cs`, with the lowered continuation `k'`: `none` unless the body is straight-line
    (`NFProg.toMulti?`). The invariants are the outer variables the body reads
    (`whileSelJ`), and the body is restricted to them (`MultiReturnCom.restrict?`). -/
def jwhileNodeJ {Γ : Ctxt jasminDialect} {t : JasminTy} {cs : List JasminTy}
    (inits : HVector (fun ty => Ctxt.Var Γ ty) cs)
    (body : NFProg jasminDialect (cs ++ Γ) (HasBitType.bit (d := jasminDialect) :: cs))
    (k' : ComLJ (cs ++ Γ) t) : Option (ComLJ Γ t) :=
  body.toMulti?.bind fun m =>
    (m.restrict? (VMap.liftApp (findIn (whileSelJ m).2) cs)).map fun m' =>
      ComLJ.whileRegs (invTys := (whileSelJ m).1) m' inits (whileSelJ m).2 k'

/-- Lower an `NFProg jasminDialect` program with the one result `t` (`ts = [t]`) to
    `ComLJ`: let-bindings to `ComLJ.var`, the return to a lifted `ComL.ret`, a counted
    loop with a straight-line body to `ComLJ.forLoopRegs` (`jforNodeJ`), and a do-while
    with a straight-line body to `ComLJ.whileRegs` (`jwhileNodeJ`), for every carried
    tuple. `none` on a branch, on a call and on a loop whose body is not straight-line. -/
def jasminNFToComLJAt : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} →
    NFProg jasminDialect Γ ts → (t : JasminTy) → ts = [t] → Option (ComLJ Γ t)
  | _, _, .ret vs, _, h => by
      subst h
      exact match vs with
        | .cons v .nil => some (.lift (.ret v))
  | _, _, .var e k, t, h => (jasminNFToComLJAt k t h).map fun k' => .var e k'
  | _, _, .forLoop count inits body k, t, h =>
      (jasminNFToComLJAt k t h).bind (jforNodeJ count inits body)
  | _, _, .ifThenElse .., _, _ => none
  | _, _, .whileLoop inits body k, t, h =>
      (jasminNFToComLJAt k t h).bind (jwhileNodeJ inits body)
  | _, _, .call .., _, _ => none

/-- **Preservation, bisimulation form.** When `jasminNFToComLJAt p t h = some c`, the
    program `p` and the `ComLJ` program `c` at the same fuel both fail or both succeed,
    and `p` returns the one value `c` returns. -/
theorem jasminNFToComLJAt_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (t : JasminTy) (h : ts = [t]) (c : ComLJ Γ t)
    (hc : jasminNFToComLJAt p t h = some c) (fuel : Nat) (W : Ctxt.Valuation Γ) :
    p.denote fuel W = (c.denote fuel W).map (fun x => h ▸ HVector.cons x .nil) := by
  induction p with
  | ret vs =>
      subst h
      rcases vs with _ | ⟨v, _ | _⟩
      have hr : jasminNFToComLJAt (.ret (.cons v .nil)) t rfl = some (.lift (.ret v)) := rfl
      rw [hr, Option.some.injEq] at hc
      subst hc
      rfl
  | var e k ih =>
      subst h
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hc
      simp only [NFProg.denote, Expr.denoteM_option_eq_some, Option.bind_eq_bind,
        Option.bind_some]
      exact ih rfl k' hk' _
  | @forLoop Γ' cs ts' count inits body k _ ihk =>
      obtain ⟨k', hk, hc⟩ := Option.bind_eq_some_iff.mp hc
      obtain ⟨m, hm, hc⟩ := Option.bind_eq_some_iff.mp hc
      obtain ⟨m', hr, rfl⟩ := Option.map_eq_some_iff.mp hc
      have hstep : (fun acc i => body.denote fuel
            (hvAppend acc (.cons (HasWord64.ofNat (d := jasminDialect) i) W))) =
          fun acc i => some (ComLJ.forStep m' (Expr.lookupArgs (forSelJ m).2 W) acc i) := by
        funext acc i
        rw [NFProg.denote_of_toMulti? body hm]
        exact congrArg some (MultiReturnCom.restrict?_denote m _ m' hr _ _
          (VMap.agree_liftApp (VMap.agree_lift (findIn_agree W (forSelJ m).2) _) cs acc)).symm
      rw [NFProg.denote_forLoop, hstep, foldlM_some_eq]
      exact ihk h k' hk _
  | @whileLoop Γ' cs ts' inits body k _ ihk =>
      obtain ⟨k', hk, hc⟩ := Option.bind_eq_some_iff.mp hc
      obtain ⟨m, hm, hc⟩ := Option.bind_eq_some_iff.mp hc
      obtain ⟨m', hr, rfl⟩ := Option.map_eq_some_iff.mp hc
      have hstep : (fun acc => body.denote fuel (hvAppend acc W)) =
          ComLJ.whileStep m' (Expr.lookupArgs (whileSelJ m).2 W) := by
        funext acc
        rw [NFProg.denote_of_toMulti? body hm]
        exact congrArg some (MultiReturnCom.restrict?_denote m _ m' hr _ _
          (VMap.agree_liftApp (findIn_agree W (whileSelJ m).2) cs acc)).symm
      rw [NFProg.denote_whileLoop, hstep]
      show _ = (NFProg.whileIter (d := jasminDialect)
        (ComLJ.whileStep m' (Expr.lookupArgs (whileSelJ m).2 W)) fuel
          (Expr.lookupArgs inits W) >>= _).map _
      rcases NFProg.whileIter (d := jasminDialect)
        (ComLJ.whileStep m' (Expr.lookupArgs (whileSelJ m).2 W)) fuel
          (Expr.lookupArgs inits W) with _ | acc
      · rfl
      · exact ihk h k' hk _
  | ifThenElse => simp [jasminNFToComLJAt] at hc
  | call => simp [jasminNFToComLJAt] at hc

/-- **Preservation of the leakage run, bisimulation form.** When
    `jasminNFToComLJAt p t h = some c`, the leakage runs of `p` and of `c` at the same fuel
    both fail or both succeed, with the same one value and the same events. -/
theorem jasminNFToComLJAt_leakRun (M : LeakModel jasminDialect) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (t : JasminTy) (h : ts = [t])
    (c : ComLJ Γ t) (hc : jasminNFToComLJAt p t h = some c) (fuel : Nat)
    (W : Ctxt.Valuation Γ) :
    NFProg.leakRun M fuel p W =
      (ComLJ.leakRun M fuel c W).map (fun r => (h ▸ HVector.cons r.1 .nil, r.2)) := by
  induction p with
  | ret vs =>
      subst h
      rcases vs with _ | ⟨v, _ | _⟩
      have hr : jasminNFToComLJAt (.ret (.cons v .nil)) t rfl = some (.lift (.ret v)) := rfl
      rw [hr, Option.some.injEq] at hc
      subst hc
      rfl
  | var e k ih =>
      subst h
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hc
      simp only [NFProg.leakRun, ComLJ.leakRun, ih rfl k' hk', Option.map_map]
      rfl
  | @forLoop Γ' cs ts' count inits body k _ ihk =>
      obtain ⟨k', hk, hc⟩ := Option.bind_eq_some_iff.mp hc
      obtain ⟨m, hm, hc⟩ := Option.bind_eq_some_iff.mp hc
      obtain ⟨m', hr, rfl⟩ := Option.map_eq_some_iff.mp hc
      have hstep : (fun i acc => NFProg.leakRun M fuel body
            (hvAppend acc (.cons (HasWord64.ofNat (d := jasminDialect) i) W))) =
          ComLJ.forStepLeak M m' (Expr.lookupArgs (forSelJ m).2 W) := by
        funext i acc
        have hag : VMap.Agree (VMap.liftApp (VMap.lift (findIn (forSelJ m).2)) cs)
            (hvAppend acc (.cons (HasWord64.ofNat (d := jasminDialect) i) W))
            (hvAppend acc (.cons (BitVec.ofNat 64 i) (Expr.lookupArgs (forSelJ m).2 W))) :=
          VMap.agree_liftApp (VMap.agree_lift (findIn_agree W (forSelJ m).2) _) cs acc
        rw [NFProg.leakRun_of_toMulti? M body hm, ComLJ.forStepLeak, ComLJ.forStep,
          MultiReturnCom.restrict?_denote m _ m' hr _ _ hag,
          multiRestrict_ctLeak M m _ m' hr _ _ hag]
      simp only [NFProg.leakRun, ComLJ.leakRun]
      rw [hstep]
      rcases forIterLeak (d := jasminDialect)
        (ComLJ.forStepLeak M m' (Expr.lookupArgs (forSelJ m).2 W))
          (List.range (count.lookup W).toNat) (Expr.lookupArgs inits W) with _ | ⟨a, tr⟩
      · rfl
      · simp only [Option.bind_some, ihk h k' hk, Option.map_map]
        rfl
  | @whileLoop Γ' cs ts' inits body k _ ihk =>
      obtain ⟨k', hk, hc⟩ := Option.bind_eq_some_iff.mp hc
      obtain ⟨m, hm, hc⟩ := Option.bind_eq_some_iff.mp hc
      obtain ⟨m', hr, rfl⟩ := Option.map_eq_some_iff.mp hc
      have hstep : (fun acc => NFProg.leakRun M fuel body (hvAppend acc W)) =
          ComLJ.whileStepLeak M m' (Expr.lookupArgs (whileSelJ m).2 W) := by
        funext acc
        have hag := VMap.agree_liftApp (findIn_agree W (whileSelJ m).2) cs acc
        rw [NFProg.leakRun_of_toMulti? M body hm, ComLJ.whileStepLeak,
          MultiReturnCom.restrict?_denote m _ m' hr _ _ hag,
          multiRestrict_ctLeak M m _ m' hr _ _ hag]
      simp only [NFProg.leakRun, ComLJ.leakRun]
      rw [hstep]
      rcases whileIterLeak (d := jasminDialect)
        (ComLJ.whileStepLeak M m' (Expr.lookupArgs (whileSelJ m).2 W)) fuel
          (Expr.lookupArgs inits W) with _ | ⟨a, tr⟩
      · rfl
      · simp only [Option.bind_some, ihk h k' hk, Option.map_map]
        rfl
  | ifThenElse => simp [jasminNFToComLJAt] at hc
  | call => simp [jasminNFToComLJAt] at hc

/-- **Preservation of the events.** When `jasminNFToComLJAt p t h = some c`, the events of
    `p` at a fuel are the events of `c` at the same fuel (both `none` when a do-while runs
    out of fuel). -/
theorem jasminNFToComLJAt_ctLeak (M : LeakModel jasminDialect) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (t : JasminTy) (h : ts = [t])
    (c : ComLJ Γ t) (hc : jasminNFToComLJAt p t h = some c) (fuel : Nat)
    (W : Ctxt.Valuation Γ) :
    (NFProg.leakRun M fuel p W).map Prod.snd = ComLJ.ctLeak M fuel c W := by
  rw [jasminNFToComLJAt_leakRun M p t h c hc fuel W, Option.map_map]
  rfl

end ComLJExport

/-! ## 4. The composite lowering -/

/-- Lower an `NFProg catCryptDialect` program with one result to `ComL`: `NFProg.map?`
    along `catToJasmin` at the identity renaming, then `jasminNFToComLAt`. -/
def nfToComLVia {Γ : Ctx} {t : CryptoTy} (p : NFProg catCryptDialect Γ [t]) :
    Option (ComL (mapCtx Γ) (mapTy t)) :=
  (NFProg.map? catToJasmin catToJasmin_regionTypes p (fun v => v)).bind fun q =>
    jasminNFToComLAt q (mapTy t) rfl

/-- **Preservation** for `nfToComLVia`: when `nfToComLVia p = some jcom`, the source
    program denotes `some` of one value `x`, at every fuel, and the lowered program on
    the transported valuation denotes `ctTransTy x`. -/
theorem nfToComLVia_denote {Γ : Ctx} {t : CryptoTy} (p : NFProg catCryptDialect Γ [t])
    (jcom : ComL (mapCtx Γ) (mapTy t)) (hj : nfToComLVia p = some jcom) (fuel : Nat)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) :
    ∃ x : CryptoTy.denote t, p.denote fuel V = some (.cons x .nil) ∧
      jcom.denote (ctMapValD V) = ctTransTy x := by
  obtain ⟨q, hq, hj⟩ := Option.bind_eq_some_iff.mp hj
  have h1 := jasminNFToComLAt_denote q (mapTy t) rfl jcom hj fuel (ctMapValD V)
  have h2 := catToJasmin_map?_denote fuel p (fun v => v) V (ctMapValD V)
    (FieldDialectBlockDescent.pullV_id _) q hq
  have h3 := h1.symm.trans h2
  rcases hp : p.denote fuel V with _ | r
  · rw [hp] at h3
    cases h3
  · rcases r with _ | ⟨x, _ | _⟩
    rw [hp] at h3
    refine ⟨x, rfl, ?_⟩
    exact (HVector.cons.inj (Option.some.inj h3)).1

/-- Where `nfToComLVia` and `nfToComL` both return a program, the two programs denote
    the same value on every transported valuation. -/
theorem nfToComLVia_agrees {Γ : Ctx} {t : CryptoTy} (p : NFProg catCryptDialect Γ [t])
    (j' j : ComL (mapCtx Γ) (mapTy t)) (h' : nfToComLVia p = some j')
    (h : nfToComL p = some j) (V : Ctxt.Valuation (d := catCryptDialect) Γ) :
    j'.denote (ctMapValD V) = j.denote (ctMapValD V) := by
  obtain ⟨x', hx', hj'⟩ := nfToComLVia_denote p j' h' 0 V
  obtain ⟨x, hx, hj⟩ := nfToComL_denote p j h 0 V
  rw [hx] at hx'
  have hxx := (HVector.cons.inj (Option.some.inj hx')).1
  rw [hj', hj, hxx]

/-- Lower an `NFProg catCryptDialect` program with one result to `ComLJ`: the lifted
    `nfToComLVia` program where `nfToComLVia` returns one, and otherwise `NFProg.map?` along
    `catToJasmin` at the identity renaming followed by `jasminNFToComLJAt`. -/
def nfToComLJVia {Γ : Ctx} {t : CryptoTy} (p : NFProg catCryptDialect Γ [t]) :
    Option (ComLJ (mapCtx Γ) (mapTy t)) :=
  match nfToComLVia p with
  | some c => some (.lift c)
  | none => (NFProg.map? catToJasmin catToJasmin_regionTypes p (fun v => v)).bind fun q =>
      jasminNFToComLJAt q (mapTy t) rfl

/-- **Preservation, bisimulation form**, for `nfToComLJVia`: when
    `nfToComLJVia p = some jcom`, the lowered program on the transported valuation and the
    source program at the same fuel both fail or both succeed, and the lowered program
    returns the `ctTransTy` transport of the source result. -/
theorem nfToComLJVia_denote {Γ : Ctx} {t : CryptoTy} (p : NFProg catCryptDialect Γ [t])
    (jcom : ComLJ (mapCtx Γ) (mapTy t)) (hj : nfToComLJVia p = some jcom) (fuel : Nat)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) :
    jcom.denote fuel (ctMapValD V) = (p.denote fuel V).map fun r => ctTransTy r.head := by
  unfold nfToComLJVia at hj
  split at hj
  · rename_i c hc
    cases hj
    obtain ⟨x, hx, hcx⟩ := nfToComLVia_denote p c hc fuel V
    rw [hx]
    exact congrArg some hcx
  · obtain ⟨q, hq, hj⟩ := Option.bind_eq_some_iff.mp hj
    have h1 : q.denote fuel (ctMapValD V) =
        (jcom.denote fuel (ctMapValD V)).map (fun x => HVector.cons x .nil) :=
      jasminNFToComLJAt_denote q (mapTy t) rfl jcom hj fuel (ctMapValD V)
    have h2 := catToJasmin_map?_denote fuel p (fun v => v) V (ctMapValD V)
      (FieldDialectBlockDescent.pullV_id _) q hq
    have h3 := h1.symm.trans h2
    revert h3
    rcases jcom.denote fuel (ctMapValD V) with _ | y <;>
      rcases p.denote fuel V with _ | ⟨x, _ | _⟩ <;> intro h3 <;>
      simp only [Option.map_none, Option.map_some, reduceCtorEq] at h3 ⊢
    exact congrArg some (HVector.cons.inj (Option.some.inj h3)).1

end CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin
