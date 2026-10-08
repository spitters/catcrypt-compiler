/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgMap
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgJasmin
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgToComL
public import CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgToMulti
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportLoopsJ

/-!
# The translation of `catCryptDialect` to `jasminDialect` as a partial block lowering

`catToJasmin` is the partial block lowering from `catCryptDialect` to `jasminDialect`
whose type, context and variable maps are `mapTy`, `mapCtx` and `toJVarD`, and whose
block of an expression `e` is `toJBlockD e`: the one-binding block of `toJExprD e`, the
block of several bindings `toJMultiD e` for `bvNot` and `bitToSword`, or `none` where
both refuse `e`. Its leaves are the theorems of
`DialectToJasminComCorrect`: `ctMapValD_lookup`, `ctMapValD_extend` and
`toJBlockD_denote`, which has no side condition. `NFProg.map?` along it
lowers an `NFProg catCryptDialect` to an `NFProg jasminDialect`.

`jasminNFToComLAt` maps an `NFProg jasminDialect` program with one result, built from
let-bindings, a return and counted loops carrying one value with a straight-line body,
to `ComL`, selecting the invariants of a loop with `usedSel` and restricting its body
with `comRestrict`; every other program is `none`. `nfToComLVia` is `NFProg.map?` along
`catToJasmin` followed by `jasminNFToComLAt`.

## Main definitions

* `catToJasmin` — the partial block lowering.
* `twoSymEnvC`, `twoSymEnvJ`, `twoSymProg` — two call environments with the symbols
  `"add"` and `"dbl"` on 64-bit words, and a program that calls both.
* `jasminNFToComLAt`, `jasminNFToComL` — the lowering of the one-carried fragment of
  `NFProg jasminDialect` to `ComL`.
* `nfToComLVia` — the lowering of `NFProg catCryptDialect` to `ComL` through
  `NFProg jasminDialect`.

## Main results

* `catToJasmin_map?_denote` — `map?` along `catToJasmin` preserves denotation;
  `catToJasmin_map?_denoteAt` — the same at call environments that agree along
  `ctTransTy` at the calls of the program.
* `twoSymProg_catToJasmin` — the program `twoSymProg`, which calls the two symbols of
  `twoSymEnvC`, lowers along `catToJasmin` to a program that denotes at `twoSymEnvJ` the
  transport of its denotation.
* `jasminNFToComLAt_of_toComAt`, `jasminNFToComL_of_toCom?` — a straight-line program
  lowers to its embedding `comToComL`.
* `jasminNFToComLAt_denote` — `jasminNFToComLAt` preserves denotation.
* `nfToComLVia_denote` — `nfToComLVia` preserves denotation: the source program denotes
  `some` of one value, and the lowered program on the transported valuation denotes its
  `ctTransTy` transport.
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
    lowering.** An expression lowers to its block `toJBlockD`: the one-binding block of
    `toJExprD`, or the block of several bindings `toJMultiD`; it is refused where both
    are `none`. -/
def catToJasmin : PartialBlockLowering catCryptDialect jasminDialect where
  mapTy := mapTy
  mapCtx := mapCtx
  mapCtx_cons _ _ := rfl
  mapVar := toJVarD
  lowerExprBlock? := toJBlockD

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

/-- The block leaf of `catToJasmin` is `toJBlockD_denote`: a block the
    lowering gives an expression denotes, on the transported valuation, the transport
    of the expression's value. -/
theorem catToJasmin_block {Γ : Ctx} {t : CryptoTy} (e : Expr catCryptDialect Γ t)
    (blk : Com jasminDialect (mapCtx Γ) (mapTy t))
    (hblk : catToJasmin.lowerExprBlock? e = some blk)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) :
    blk.denote (ctMapValD V) = ctTransTy (e.denote V) :=
  toJBlockD_denote e V blk hblk

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
  NFProg.map?_denote_call catToJasmin (fun x => ctTransTy x) ctMapValD catToJasmin_regionTypes
    (fun _ => True) catToJasmin_varTransports
    (fun e _ blk hblk V => catToJasmin_block e blk hblk V)
    catToJasmin_mapValExtends catToJasmin_regionTransports fuel p
    (NFProg.covered_of_forall _ (fun _ => trivial) p) (CallEnv.transports_empty _ _ _)
    ren V W hren q hq

/-- **Preservation along `catToJasmin` at explicit call environments.** Under the
    agreement of `E` and `E'` along `ctTransTy` at every call of `p`, a program that `map?`
    returns for `p` at a renaming relating `W` to `ctMapValD V` denotes at `E'` and every
    fuel the `ctTransTy` transport of the denotation of `p` at `E`. -/
theorem catToJasmin_map?_denoteAt (E : CallEnv catCryptDialect) (E' : CallEnv jasminDialect)
    (fuel : Nat) {Γ : Ctx} {ts : List CryptoTy} (p : NFProg catCryptDialect Γ ts)
    (hCall : E.Transports E' (fun as => as.map mapTy)
      (fun x => BlockLoweringExtend.transArgs mapTy (fun x => ctTransTy x) x) p.Calls)
    {Δ : Ctxt jasminDialect} (ren : Ctxt.Hom (mapCtx Γ) Δ)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) (W : Ctxt.Valuation Δ)
    (hren : FieldDialectBlockDescent.pullV ren W = ctMapValD V)
    (q : NFProg jasminDialect Δ (ts.map mapTy))
    (hq : NFProg.map? catToJasmin catToJasmin_regionTypes p ren = some q) :
    q.denoteAt E' fuel W =
      (p.denoteAt E fuel V).map (BlockLoweringExtend.transArgs mapTy (fun x => ctTransTy x)) :=
  NFProg.map?_denoteAt catToJasmin (fun x => ctTransTy x) ctMapValD catToJasmin_regionTypes
    (fun _ => True) catToJasmin_varTransports
    (fun e _ blk hblk V => catToJasmin_block e blk hblk V)
    catToJasmin_mapValExtends catToJasmin_regionTransports E E' fuel p
    (NFProg.covered_of_forall _ (fun _ => trivial) p) hCall ren V W hren q hq

/-! ## 1a. A program with two symbols -/

/-- The call environment of `catCryptDialect` with two symbols on 64-bit words: `"add"`
    returns the sum of its two arguments and `"dbl"` twice its argument. -/
def twoSymEnvC : CallEnv catCryptDialect where
  call
    | "add", [.sword 64, .sword 64], [.sword 64], .cons a (.cons b .nil) =>
        some (.cons (BitVec.add (n := 64) a b) .nil)
    | "dbl", [.sword 64], [.sword 64], .cons a .nil => some (.cons (BitVec.add (n := 64) a a) .nil)
    | _, _, _, _ => none

/-- The call environment of `jasminDialect` with the symbols of `twoSymEnvC` on 64-bit
    registers. -/
def twoSymEnvJ : CallEnv jasminDialect where
  call
    | "add", [.reg 64, .reg 64], [.reg 64], .cons a (.cons b .nil) =>
        some (.cons (BitVec.add (n := 64) a b) .nil)
    | "dbl", [.reg 64], [.reg 64], .cons a .nil => some (.cons (BitVec.add (n := 64) a a) .nil)
    | _, _, _, _ => none

/-- The program over two 64-bit words `x, y` that calls `"add"` on `y, x` and `"dbl"` on
    the result, and returns the result of `"dbl"`. -/
def twoSymProg :
    NFProg catCryptDialect [CryptoTy.sword 64, CryptoTy.sword 64] [CryptoTy.sword 64] :=
  .call (as := [CryptoTy.sword 64, CryptoTy.sword 64]) (rs := [CryptoTy.sword 64]) "add"
    (.cons (by exact .here) (.cons (by exact .there .here) .nil))
    (.call (as := [CryptoTy.sword 64]) (rs := [CryptoTy.sword 64]) "dbl"
      (.cons (by exact .here) .nil) (.ret (.cons (by exact .here) .nil)))

/-- `twoSymEnvC` and `twoSymEnvJ` agree along `ctTransTy` at the two calls of
    `twoSymProg`. -/
theorem twoSymProg_transports :
    twoSymEnvC.Transports twoSymEnvJ (fun as => as.map mapTy)
      (fun x => BlockLoweringExtend.transArgs mapTy (fun x => ctTransTy x) x)
      twoSymProg.Calls := by
  intro f as rs x h
  simp only [twoSymProg, NFProg.Calls, or_false] at h
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · match x with
    | .cons _ (.cons _ .nil) => rfl
  · match x with
    | .cons _ .nil => rfl

/-- **The two-symbol program through `catToJasmin`.** `map?` along `catToJasmin` lowers
    `twoSymProg` to a program that denotes at `twoSymEnvJ`, on `ctMapValD V` and at every
    fuel, the `ctTransTy` transport of the denotation of `twoSymProg` at `twoSymEnvC`. -/
theorem twoSymProg_catToJasmin :
    ∃ q, NFProg.map? catToJasmin catToJasmin_regionTypes twoSymProg (fun v => v) = some q ∧
      ∀ (fuel : Nat)
        (V : Ctxt.Valuation (d := catCryptDialect) [CryptoTy.sword 64, CryptoTy.sword 64]),
        q.denoteAt twoSymEnvJ fuel (ctMapValD V) =
          (twoSymProg.denoteAt twoSymEnvC fuel V).map
            (BlockLoweringExtend.transArgs mapTy (fun x => ctTransTy x)) := by
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp
    (show (NFProg.map? catToJasmin catToJasmin_regionTypes twoSymProg (fun v => v)).isSome
      from rfl)
  exact ⟨q, hq, fun fuel V => catToJasmin_map?_denoteAt twoSymEnvC twoSymEnvJ fuel twoSymProg
    twoSymProg_transports _ V _ (FieldDialectBlockDescent.pullV_id _) q hq⟩

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

/-- A program `NFProg.toComAt` reads as the straight-line program `c` lowers to the
    embedding `comToComL c`. -/
theorem jasminNFToComLAt_of_toComAt {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (t : JasminTy) (h : ts = [t])
    {c : Com jasminDialect Γ t} (hc : p.toComAt t h = some c) :
    jasminNFToComLAt p t h = some (comToComL c) := by
  induction p with
  | ret vs =>
      subst h
      rcases vs with _ | ⟨v, _ | _⟩
      simp only [NFProg.toComAt, Option.some.injEq] at hc
      subst hc
      rfl
  | var e k ih =>
      simp only [NFProg.toComAt, Option.map_eq_some_iff] at hc
      obtain ⟨c', hk, rfl⟩ := hc
      simp only [jasminNFToComLAt, ih h hk, Option.map_some, comToComL]
  | forLoop => simp [NFProg.toComAt] at hc
  | ifThenElse => simp [NFProg.toComAt] at hc
  | whileLoop => simp [NFProg.toComAt] at hc
  | call => simp [NFProg.toComAt] at hc

/-- A program `NFProg.toCom?` reads as the straight-line program `c` lowers to the
    embedding `comToComL c`. -/
theorem jasminNFToComL_of_toCom? {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) {c : Com jasminDialect Γ t} (hc : p.toCom? = some c) :
    jasminNFToComL p = some (comToComL c) :=
  jasminNFToComLAt_of_toComAt p t rfl hc

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

/-! ## 3. The composite lowering -/

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

end CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin
