/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomSplice
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomFoldPos

/-!
# Loads and stores at constant indices

The shape `LoadsChainK` is the shape `LoadsChain` in which the index of every load and every
store is a word variable bound by a constant `regConst 64 c` below the length of the accessed
array. The constants of the word variables in scope are an index of the shape (`KCtx`): a
binding of `regConst 64 c` records `c` at its variable, every other binding records nothing.

The templates of the field route bind each limb index by `regConst 64 j`, `j` below the number
of limbs, right before the load or the store of that limb (`FieldToJasminLimbs.loadLimbs`,
`storeLimbs`), so the body of a wide tagged call has the shape (`wideBlockOf_loadsChainK`).

The export of a binding of `regConst 64 c` at depth `d` is the immediate move
`MOV:64 (regName d), $c` at the register tag `.reg none`, and every binding of a program of the
shape exports to one operation that writes the slot name of its depth. So in the export of a
program of the shape, the index register of every array access holds a constant below the
length of the array in the sense of `KnownAt` (`loadsChainK_export_knownAt`).

## Main definitions

* `KCtx`, `KCtx.snoc`: the known constants of the word variables of a context, and their
  extension by a binding.
* `ChainTailK`, `LoadsChainK`: the shapes `ChainTail` and `LoadsChain` with every index bound
  by a constant below the length of its array.
* `LoadsThenStoresK`: the shape `LoadsThenStores` of a multi-result program in which every load
  reads at a constant bound right before it.
* `AccIdx`: an exported instruction accesses an array of a given length at an index register.

## Main results

* `ChainTailK.chainTail`, `LoadsChainK.loadsChain`: the shapes are cases of `ChainTail` and
  `LoadsChain`.
* `loadsChainK_of_loadsThenStoresK`, `wideBlockOf_loadsChainK`: the body of a wide tagged call
  has the shape `LoadsChainK`.
* `loadsChainK_export_shape`: the export of a program of the shape has at each position one
  operation writing the slot name of its depth.
* `loadsChainK_export_knownAt`: in that export, the index register of every array access holds
  a constant below the length of the array (`KnownAt`).
* `loadsChainK_rename?`, `loadsChainK_dce`, `loadsChainK_fwdLoad1Go`,
  `loadsChainK_lowerBodyTail`: a partial renaming that carries the known constants,
  dead-binding elimination and the forwarding of loads keep the shape.
* `loadsChainK_ofCom_rename`, `loadsChainK_spliceNF?_ofCom`, `loadsChainK_spliceNF?`: renamed
  and spliced blocks keep the shape.
* `lowerArr_loadsChainK`, `fieldBodyD_loadsChainK`: the lowered body `fieldBodyD` of a tagged
  head at a modulus without a narrow representation and with a wide template has the shape
  `LoadsChainK` at every known constants.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.Algebraic
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont (LimbParams)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519 (w64 MC bindK eConst)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs (arrTy loadLimbs loadArgs
  storeLimbs eLoad eStore)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldWideLeak (jMemFree MemFree PrefixClosed
  lowerR_q exprBlock_memFree solinasExprBlock_memFree twistOp_coveredArith)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldWideInline
open Ctxt (Var)

/-! ## 1. The shapes -/

/-- **The known constants of the word variables of a context**: `some c` at a variable bound
    by `regConst 64 c`, `none` at a variable of unknown value. -/
abbrev KCtx (Γ : Ctxt jasminDialect) : Type := Var Γ (.reg 64) → Option Nat

/-- The known constant of a variable of type `τ = reg 64` after a binding whose variable has
    the known constant `o`. -/
def KCtx.snocAt {Γ : Ctxt jasminDialect} {t : JasminTy} (K : KCtx Γ) (o : Option Nat) :
    {τ : JasminTy} → Var (t :: Γ) τ → τ = .reg 64 → Option Nat
  | _, .here, _ => o
  | _, .there v, h => K (h ▸ v)

/-- The known constants after a binding whose variable has the known constant `o`. -/
def KCtx.snoc {Γ : Ctxt jasminDialect} {t : JasminTy} (K : KCtx Γ) (o : Option Nat) :
    KCtx (t :: Γ) := fun v => K.snocAt o v rfl

/-- The known constant of the new variable (unfolding lemma of `KCtx.snoc`). -/
@[simp] theorem KCtx.snoc_here {Γ : Ctxt jasminDialect} (K : KCtx Γ) (o : Option Nat) :
    K.snoc (t := .reg 64) o .here = o := rfl

/-- The known constant of an earlier variable (unfolding lemma of `KCtx.snoc`). -/
@[simp] theorem KCtx.snoc_there {Γ : Ctxt jasminDialect} {t : JasminTy} (K : KCtx Γ)
    (o : Option Nat) (v : Var Γ (.reg 64)) : K.snoc (t := t) o v.there = K v := rfl

/-- The binding of the constant `c` as a `64`-bit word. -/
abbrev eConst64 {Γ : Ctxt jasminDialect} (c : Nat) : Expr jasminDialect Γ (.reg 64) :=
  ⟨.regConst 64 c, rfl, .nil⟩

/-- **The tail of a chain of stores at constant indices**: `ChainTail` at the known constants
    `K`, in which the index of every store is a variable of known constant below the length of
    the array. -/
inductive ChainTailK : {Γ : Ctxt jasminDialect} → KCtx Γ → {w m : Nat} →
    Var Γ (.stackArr w m) → {ts : List JasminTy} → NFProg jasminDialect Γ ts → Prop
  /-- A binding of a constant word. -/
  | const {Γ : Ctxt jasminDialect} (K : KCtx Γ) {w m : Nat} {ts : List JasminTy}
      (v : Var Γ (.stackArr w m)) (c : Nat) (k : NFProg jasminDialect (.reg 64 :: Γ) ts) :
      ChainTailK (K.snoc (some c)) v.there k → ChainTailK K v (.var (eConst64 c) k)
  /-- A memory-free binding. -/
  | free {Γ : Ctxt jasminDialect} (K : KCtx Γ) {w m : Nat} {t : JasminTy} {ts : List JasminTy}
      (v : Var Γ (.stackArr w m)) (e : Expr jasminDialect Γ t)
      (k : NFProg jasminDialect (t :: Γ) ts) :
      jMemFree e.op = true → ChainTailK (K.snoc none) v.there k → ChainTailK K v (.var e k)
  /-- A store into the current version at a known constant index below the length. -/
  | store {Γ : Ctxt jasminDialect} (K : KCtx Γ) {w m : Nat} {ts : List JasminTy}
      (v : Var Γ (.stackArr w m)) (i : Var Γ (.reg 64)) (x : Var Γ (.reg w)) (c : Nat)
      (k : NFProg jasminDialect (.stackArr w m :: Γ) ts) :
      K i = some c → c < m → ChainTailK (K.snoc none) .here k →
        ChainTailK K v (.var ⟨.stackStore w m, rfl, .cons v (.cons i (.cons x .nil))⟩ k)
  /-- The return of the current version. -/
  | ret {Γ : Ctxt jasminDialect} (K : KCtx Γ) {w m : Nat} (v : Var Γ (.stackArr w m)) :
      ChainTailK K v (.ret (.cons v .nil))

/-- **Loads, then one chain of stores, at constant indices**: `LoadsChain` at the known
    constants `K`, in which the index of every load and every store is a variable of known
    constant below the length of the accessed array. -/
inductive LoadsChainK : {Γ : Ctxt jasminDialect} → KCtx Γ → {ts : List JasminTy} →
    NFProg jasminDialect Γ ts → Prop
  /-- A binding of a constant word. -/
  | const {Γ : Ctxt jasminDialect} (K : KCtx Γ) {ts : List JasminTy} (c : Nat)
      (k : NFProg jasminDialect (.reg 64 :: Γ) ts) :
      LoadsChainK (K.snoc (some c)) k → LoadsChainK K (.var (eConst64 c) k)
  /-- A memory-free binding. -/
  | free {Γ : Ctxt jasminDialect} (K : KCtx Γ) {t : JasminTy} {ts : List JasminTy}
      (e : Expr jasminDialect Γ t) (k : NFProg jasminDialect (t :: Γ) ts) :
      jMemFree e.op = true → LoadsChainK (K.snoc none) k → LoadsChainK K (.var e k)
  /-- A load at a known constant index below the length. -/
  | load {Γ : Ctxt jasminDialect} (K : KCtx Γ) {w m : Nat} {ts : List JasminTy}
      (a : Var Γ (.stackArr w m)) (i : Var Γ (.reg 64)) (c : Nat)
      (k : NFProg jasminDialect (.reg w :: Γ) ts) :
      K i = some c → c < m → LoadsChainK (K.snoc none) k →
        LoadsChainK K (.var ⟨.stackLoad w m, rfl, .cons a (.cons i .nil)⟩ k)
  /-- The first store, at a known constant index below the length, whose result starts the
      chain. -/
  | store {Γ : Ctxt jasminDialect} (K : KCtx Γ) {w m : Nat} {ts : List JasminTy}
      (v : Var Γ (.stackArr w m)) (i : Var Γ (.reg 64)) (x : Var Γ (.reg w)) (c : Nat)
      (k : NFProg jasminDialect (.stackArr w m :: Γ) ts) :
      K i = some c → c < m → ChainTailK (K.snoc none) .here k →
        LoadsChainK K (.var ⟨.stackStore w m, rfl, .cons v (.cons i (.cons x .nil))⟩ k)
  /-- A return without a store. -/
  | ret {Γ : Ctxt jasminDialect} (K : KCtx Γ) {ts : List JasminTy}
      (vs : HVector (fun t => Var Γ t) ts) : LoadsChainK K (.ret vs)

/-- **A chain tail at constant indices is a chain tail.** -/
theorem ChainTailK.chainTail {Γ : Ctxt jasminDialect} {K : KCtx Γ} {w m : Nat}
    {ts : List JasminTy} {v : Var Γ (.stackArr w m)} {k : NFProg jasminDialect Γ ts}
    (h : ChainTailK K v k) : ChainTail v k := by
  induction h with
  | const K v c k _ ih => exact .free _ _ _ rfl ih
  | free K v e k he _ ih => exact .free _ _ _ he ih
  | store K v i x c k _ _ _ ih => exact .store _ _ _ _ ih
  | ret K v => exact .ret _

/-- **A program of the shape `LoadsChainK` has the shape `LoadsChain`.** -/
theorem LoadsChainK.loadsChain {Γ : Ctxt jasminDialect} {K : KCtx Γ} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChainK K p) : LoadsChain p := by
  induction h with
  | const K c k _ ih => exact .free _ _ rfl ih
  | free K e k he _ ih => exact .free _ _ he ih
  | load K a i c k _ _ _ ih => exact .load _ _ _ ih
  | store K v i x c k _ _ hk => exact .store _ _ _ _ hk.chainTail
  | ret K vs => exact .ret _

/-! ## 2. The template bodies -/

variable {n : Nat}

/-- **Loads at constant indices, then one chain of stores at constant indices**: the shape
    `LoadsThenStores` in which every load reads at a constant below `n` bound right before it,
    and the chain of stores `storeLimbs m j o h` writes the indices `j` to `j + m - 1`, all
    below `n`. -/
inductive LoadsThenStoresK : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} → MC Γ ts → Prop
  /-- The chain of stores into `o`. -/
  | stores {Γ : Ctxt jasminDialect} (m j : Nat) (o : Var Γ (arrTy n))
      (h : Ctxt.Hom (Mont.Rn m) Γ) : j + m ≤ n → LoadsThenStoresK (storeLimbs m j o h)
  /-- A memory-free binding in front. -/
  | free {Γ : Ctxt jasminDialect} {t : JasminTy} {ts : List JasminTy}
      (e : Expr jasminDialect Γ t) (k : MC (t :: Γ) ts) :
      jMemFree e.op = true → LoadsThenStoresK k → LoadsThenStoresK (.var e k)
  /-- A constant index below `n`, then a load of a limb at it, in front. -/
  | load {Γ : Ctxt jasminDialect} {ts : List JasminTy} (c : Nat) (a : Var Γ (arrTy n))
      (k : MC (w64 :: w64 :: Γ) ts) : c < n → LoadsThenStoresK k →
        LoadsThenStoresK (.var (eConst c) (.var (eLoad a.there .here) k))

/-- The shape `LoadsThenStoresK` is closed under a memory-free binding in front. -/
theorem loadsThenStoresK_prefixClosed :
    PrefixClosed (fun {Γ} {ts} m => LoadsThenStoresK (n := n) (Γ := Γ) (ts := ts) m) :=
  fun e k he hk => .free e k he hk

/-- **The loads of limbs at constant indices keep the shape of every continuation**, for the
    indices `j` to `j + m - 1` below `n`. -/
theorem loadLimbs_loadsThenStoresK {bs : List JasminTy} :
    ∀ {Δ : Ctxt jasminDialect} (m j : Nat) (a : Var Δ (arrTy n))
      {k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → Ctxt.Hom (Mont.Rn m) Δ' → MC Δ' bs},
      j + m ≤ n →
      (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') h, LoadsThenStoresK (n := n) (k r h)) →
      LoadsThenStoresK (n := n) (loadLimbs m j a k)
  | _, 0, _, _, _, _, hk => by rw [loadLimbs]; exact hk _ _
  | _, m + 1, j, a, _, hj, hk => by
      rw [loadLimbs, bindK, bindK]
      exact .load j a _ (by omega)
        (loadLimbs_loadsThenStoresK m (j + 1) _ (by omega) fun _ _ => hk _ _)

/-- **The loads of the limbs of every array keep the shape of every continuation.** -/
theorem loadArgs_loadsThenStoresK {bs : List JasminTy} :
    ∀ (Γ : Ctxt fieldDialect) {Δ : Ctxt jasminDialect}
      (src : Ctxt.Hom (FieldToJasminLimbs.arrCtx n Γ) Δ)
      {k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' →
        Ctxt.Hom (MultiBlockLowering.ctxFlat (FieldToJasminLimbs.mapTysL n) Γ) Δ' → MC Δ' bs},
      (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') h, LoadsThenStoresK (n := n) (k r h)) →
      LoadsThenStoresK (n := n) (loadArgs Γ src k)
  | [], _, _, _, hk => by rw [loadArgs]; exact hk _ _
  | _ :: Γ, _, _, _, hk => by
      rw [loadArgs]
      exact loadLimbs_loadsThenStoresK _ _ _ (by omega) fun _ _ =>
        loadArgs_loadsThenStoresK Γ _ fun _ _ => hk _ _

/-- **The lowered field program over word arrays loads and stores at constant indices**, for a
    covered program whose blocks are memory-free. -/
theorem fieldBodyOf_loadsThenStoresK (lo : FieldToJasminLimbs.LimbBlocks n)
    {Good : ∀ {Γ : Ctxt fieldDialect} {t : FieldTy}, Expr fieldDialect Γ t → Prop}
    (hB : ∀ {Γ : Ctxt fieldDialect} {t : FieldTy} (e : Expr fieldDialect Γ t), Good e →
      MemFree ((FieldToJasminLimbs.loweringOf lo).exprBlock e))
    {Γ : Ctxt fieldDialect} {t : FieldTy} (c : Com fieldDialect Γ t)
    (hc : BlockLoweringCPS.CoveredCom Good c) :
    LoadsThenStoresK (n := n) (FieldToJasminLimbs.fieldBodyOf lo c) := by
  rw [FieldToJasminLimbs.fieldBodyOf]
  exact loadArgs_loadsThenStoresK Γ _ fun _ _ =>
    lowerR_q loadsThenStoresK_prefixClosed _ hB _ c hc fun _ _ => .stores _ _ _ _ (by omega)

/-- **The blocks of a wide template load and store at constant indices**: the block of every
    operation of `arithOpB p` is the head projection of a program of the shape
    `LoadsThenStoresK`. -/
def WideLoadsThenStoresK {p m : Nat} (W : WideTemplate p m) : Prop :=
  ∀ op : fieldDialect.Op, FieldLower.arithOpB p op = true →
    ∃ body : MC (FieldToJasminLimbs.arrCtx m (DialectSignature.sig op) ++ [arrTy m]) [arrTy m],
      @FieldLower.FieldLowerTemplate.block W.α m W.inst W.P op = body.toComHead
        ∧ LoadsThenStoresK (n := m) body

/-- The canonical Montgomery template of a record loads and stores at constant indices. -/
theorem ofMont_loadsThenStoresK (P : LimbParams n) (hn : n < 2 ^ 64) :
    WideLoadsThenStoresK (WideTemplate.ofMont P hn) := fun op hop =>
  ⟨FieldToJasminLimbs.fieldBodyOf (FieldToJasminLimbs.lowerOpL P) (twistOp n op), rfl,
    fieldBodyOf_loadsThenStoresK _ (exprBlock_memFree P) _ (twistOp_coveredArith P op hop)⟩

/-- The shape of the blocks is kept by the cast of the number of limbs. -/
theorem castN_loadsThenStoresK {p m : Nat} (h : n = m) {W : WideTemplate p n}
    (hW : WideLoadsThenStoresK W) : WideLoadsThenStoresK (W.castN h) := by
  subst h
  exact hW

/-- The shape of the blocks is kept by the cast of the modulus. -/
theorem castP_loadsThenStoresK {p q : Nat} (h : p = q)
    {W : WideTemplate p (_root_.Hax.FieldTag.fieldLimbs p)} (hW : WideLoadsThenStoresK W) :
    WideLoadsThenStoresK (W.castP h) := by
  subst h
  exact hW

/-- The Solinas template of a record loads and stores at constant indices. -/
theorem ofSolinasAt_loadsThenStoresK (S : Solinas.SolinasParams n)
    (hn : n = _root_.Hax.FieldTag.fieldLimbs (Solinas.p S)) (h64 : n < 2 ^ 64) :
    WideLoadsThenStoresK (WideTemplate.ofSolinasAt S hn h64) := by
  refine castN_loadsThenStoresK hn fun op hop => ⟨FieldToJasminLimbs.fieldBodyOf
    (FieldToJasminLimbsSolinas.lowerOpL S) (FieldLower.opCom op), rfl,
    fieldBodyOf_loadsThenStoresK _ (solinasExprBlock_memFree S) _
      (FieldLower.coveredCom_opCom (fun h => h) op hop)⟩

/-- **The blocks of a registered wide template load and store at constant indices**, at
    every modulus. -/
theorem wideTemplateOf_loadsThenStoresK {p : Nat}
    {W : WideTemplate p (_root_.Hax.FieldTag.fieldLimbs p)} (h : wideTemplateOf p = some W) :
    WideLoadsThenStoresK W := by
  rcases wideTemplateOf_cases h with ⟨_, S, hn, h64, hp, rfl⟩ | ⟨_, _, _, rfl⟩
  · exact castP_loadsThenStoresK hp (ofSolinasAt_loadsThenStoresK S hn h64)
  · exact ofMont_loadsThenStoresK _ _

/-! ## 3. The embedded templates -/

/-- A chain tail at constant indices at the image of the newest variable under a lifted
    renaming is one at the newest variable. -/
theorem lift_here_chainTailK {Γ Γ' : Ctxt jasminDialect} {w m : Nat} {ts : List JasminTy}
    (f : Ctxt.Hom Γ Γ') {K : KCtx (.stackArr w m :: Γ')}
    {k : NFProg jasminDialect (.stackArr w m :: Γ') ts}
    (h : ChainTailK K (Ctxt.Hom.lift f (Var.here : Var (JasminTy.stackArr w m :: Γ) _)) k) :
    ChainTailK K .here k := by
  simpa [Ctxt.Hom.lift] using h

/-- The chain of stores `storeLimbs` at the indices `j` to `j + m - 1` below `n`, renamed and
    embedded, is a chain tail at constant indices at the image of its base array, at every
    known constants. -/
theorem storeLimbs_chainTailK : ∀ {Δ Γ' : Ctxt jasminDialect} (m j : Nat)
    (o : Var Δ (arrTy n)) (h : Ctxt.Hom (Mont.Rn m) Δ) (f : Ctxt.Hom Δ Γ') (K : KCtx Γ'),
    j + m ≤ n → ChainTailK K (f o) (NFProg.ofCom (Com.rename f (storeLimbs m j o h).toComHead))
  | _, _, 0, _, _, _, f, K, _ => by
      rw [storeLimbs, ofCom_rename_toComHead_ret]
      exact .ret _ _
  | _, _, m + 1, j, _, _, f, K, hj => by
      rw [storeLimbs, bindK, bindK, ofCom_rename_toComHead_var, ofCom_rename_toComHead_var]
      exact .const _ _ j _ (.store _ _ _ _ j _ rfl (by omega)
        (lift_here_chainTailK _ (storeLimbs_chainTailK m (j + 1) Var.here _
          (Ctxt.Hom.lift (Ctxt.Hom.lift f)) _ (by omega))))

/-- The chain of stores `storeLimbs`, renamed and embedded, has the shape `LoadsChainK`. -/
theorem storeLimbs_loadsChainK {Δ Γ' : Ctxt jasminDialect} (m j : Nat) (o : Var Δ (arrTy n))
    (h : Ctxt.Hom (Mont.Rn m) Δ) (f : Ctxt.Hom Δ Γ') (K : KCtx Γ') (hj : j + m ≤ n) :
    LoadsChainK K (NFProg.ofCom (Com.rename f (storeLimbs m j o h).toComHead)) := by
  cases m with
  | zero =>
      rw [storeLimbs, ofCom_rename_toComHead_ret]
      exact .ret _ _
  | succ m =>
      rw [storeLimbs, bindK, bindK, ofCom_rename_toComHead_var, ofCom_rename_toComHead_var]
      exact .const _ j _ (.store _ _ _ _ j _ rfl (by omega)
        (lift_here_chainTailK _ (storeLimbs_chainTailK m (j + 1) Var.here _
          (Ctxt.Hom.lift (Ctxt.Hom.lift f)) _ (by omega))))

/-- **The head projection of a program that loads and stores at constant indices, renamed and
    embedded as a structured program, has the shape `LoadsChainK`**, at every known
    constants. -/
theorem loadsChainK_of_loadsThenStoresK : ∀ {Γ : Ctxt jasminDialect} {t : JasminTy}
    {ts : List JasminTy} {body : MC Γ (t :: ts)}, LoadsThenStoresK (n := n) body →
    ∀ {Γ' : Ctxt jasminDialect} (f : Ctxt.Hom Γ Γ') (K : KCtx Γ'),
      LoadsChainK K (NFProg.ofCom (Com.rename f body.toComHead))
  | _, _, _, _, .stores m j o h hj, _, f, K => storeLimbs_loadsChainK m j o h f K hj
  | _, _, _, _, .free _ _ he hk, _, f, K => by
      rw [ofCom_rename_toComHead_var]
      exact .free _ _ _ he (loadsChainK_of_loadsThenStoresK hk f.lift _)
  | _, _, _, _, .load c _ _ hc hk, _, f, K => by
      rw [ofCom_rename_toComHead_var, ofCom_rename_toComHead_var]
      exact .const _ c _ (.load _ _ _ c _ rfl hc
        (loadsChainK_of_loadsThenStoresK hk (Ctxt.Hom.lift (Ctxt.Hom.lift f)) _))

/-- **The body of a wide tagged call loads and stores at constant indices**: at every modulus
    with a registered wide template and every method, `wideBlockOf W m` has the shape
    `LoadsChainK` at every known constants. -/
theorem wideBlockOf_loadsChainK {p : Nat}
    {W : WideTemplate p (_root_.Hax.FieldTag.fieldLimbs p)} (h : wideTemplateOf p = some W)
    (m : _root_.Hax.FieldTag.FieldMethod) (K : KCtx (wideSig _ m)) :
    LoadsChainK K (wideBlockOf W m) := by
  obtain ⟨body, hb, hs⟩ := wideTemplateOf_loadsThenStoresK h (fieldOpOf m p)
    (arithOpB_fieldOpOf m p)
  unfold wideBlockOf templateCall
  exact (congrArg (fun c => LoadsChainK K (NFProg.ofCom (Com.rename _ c))) hb).mpr
    (loadsChainK_of_loadsThenStoresK hs _ K)

/-! ## 4. The export: known constants at every array access -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM MemTag)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN (operandName)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemStepFrame (dstNames)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation (regName_injective)

section Export

variable {nArgs : Nat} {fn : String}

/-- The exported binding of a constant word at depth `d` is the immediate move
    `MOV:64 (regName d), $c` at the register tag `.reg none`. -/
theorem bindOps_const (nArgs d : Nat) {Γ : Ctxt jasminDialect} (c : Nat) :
    bindOps nArgs (eConst64 (Γ := Γ) c) d =
      [(.Lopn [.reg (regName d)] "MOV:64" [.imm c], .reg none)] := by
  simp [bindOps, JasminLsemMem.straightOpsMem, opToLinstrR, withWidthTag,
    JasminLsemCast.regConstDescr]

/-- The exported load at depth `d`: a `LOADIDX` from the array named by `a` at the index
    register named by `i`, at the tag `.load w m`. -/
theorem bindOps_load_eq (nArgs d : Nat) {Γ : Ctxt jasminDialect} {w m : Nat}
    (a : Var Γ (.stackArr w m)) (i : Var Γ (.reg 64)) :
    bindOps nArgs (⟨.stackLoad w m, rfl, .cons a (.cons i .nil)⟩ :
        Expr jasminDialect Γ (.reg w)) d =
      [(.Lopn [.reg (regName d)] "LOADIDX"
          [.arrIdx (operandName (resolveVar d nArgs argName (fun _ => none) a))
            (operandName (resolveVar d nArgs argName (fun _ => none) i)) (w / 8)],
        .load w m)] := by
  have hgo : exprArgs.go d nArgs argName (fun _ => none)
      (HVector.cons a (HVector.cons i HVector.nil)) =
      [resolveVar d nArgs argName (fun _ => none) a,
        resolveVar d nArgs argName (fun _ => none) i] := rfl
  rw [bindOps, JasminLsemMem.straightOpsMem_load]
  simp only [exprArgs, hgo]
  rw [resolveVar_reg d nArgs a, resolveVar_reg d nArgs i]
  rfl

/-- The exported store at depth `d`: a `STOREIDX` into the array named by `v` at the index
    register named by `i`, at the tag `.store w m`. -/
theorem bindOps_store_eq (nArgs d : Nat) {Γ : Ctxt jasminDialect} {w m : Nat}
    (v : Var Γ (.stackArr w m)) (i : Var Γ (.reg 64)) (x : Var Γ (.reg w)) :
    bindOps nArgs (⟨.stackStore w m, rfl, .cons v (.cons i (.cons x .nil))⟩ :
        Expr jasminDialect Γ (.stackArr w m)) d =
      [(.Lopn [.reg (regName d)] "STOREIDX"
          [.arrIdx (operandName (resolveVar d nArgs argName (fun _ => none) v))
            (operandName (resolveVar d nArgs argName (fun _ => none) i)) (w / 8),
            .reg (operandName (resolveVar d nArgs argName (fun _ => none) x))],
        .store w m)] := by
  have hgo : exprArgs.go d nArgs argName (fun _ => none)
      (HVector.cons v (HVector.cons i (HVector.cons x HVector.nil))) =
      [resolveVar d nArgs argName (fun _ => none) v, resolveVar d nArgs argName (fun _ => none) i,
        resolveVar d nArgs argName (fun _ => none) x] := rfl
  rw [bindOps, JasminLsemMem.straightOpsMem_store]
  simp only [exprArgs, hgo]
  rw [resolveVar_reg d nArgs v, resolveVar_reg d nArgs i, resolveVar_reg d nArgs x]
  rfl

/-- The exported binding of a memory-free operation is one instruction at a register tag. -/
theorem bindOps_memFree_reg (nArgs d : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (he : jMemFree e.op = true) :
    ∃ wire c, bindOps nArgs e d = [(wire, .reg c)] := by
  obtain ⟨op, rfl, args⟩ := e
  cases op <;> simp only [jMemFree, Bool.false_eq_true] at he <;> exact ⟨_, _, rfl⟩

/-- **Every position of the code `C` holds one operation writing the slot name of its depth**,
    the code starting at the depth `D`. -/
def SlotCode (D : Nat) (C : List LinstrRM) : Prop :=
  ∀ (j : Nat) (i : LinstrRM), C[j]? = some i →
    ∃ o ss, i.1 = LinstrR.Lopn [LOperand.reg (regName (D + j))] o ss

/-- The slot shape of the export of a binding in front of a code of the slot shape. -/
theorem slotCode_prepend {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t)
    {D : Nat} {rk : Exported} (h : SlotCode (D + 1) rk.code) :
    SlotCode D (Exported.prepend (bindOps nArgs e D) rk).code := by
  obtain ⟨o, ss, tag, hb, -⟩ := RegionExportDefInit.bindOps_shape nArgs e D
  simp only [Exported.prepend, hb, List.singleton_append]
  unfold SlotCode; intro j i hj
  cases j with
  | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      exact ⟨o, ss, by simp⟩
  | succ j =>
      obtain ⟨o', ss', h'⟩ := h j i (by simpa using hj)
      exact ⟨o', ss', by rw [h', show D + 1 + j = D + (j + 1) by omega]⟩

/-- The export of a chain tail at constant indices has the slot shape. -/
theorem chainTailK_export_slot {Γ : Ctxt jasminDialect} {K : KCtx Γ} {w m : Nat}
    {ts : List JasminTy} {v : Var Γ (.stackArr w m)} {k : NFProg jasminDialect Γ ts}
    (h : ChainTailK K v k) {D n : Nat} {r : Exported}
    (hr : exportR nArgs fn k D n = some r) : SlotCode D r.code := by
  induction h generalizing D n r with
  | ret K v =>
      simp only [exportR, Option.some.injEq] at hr
      subst hr
      unfold SlotCode; intro j i hj
      simp at hj
  | const K v c k _ ih | free K v _ k _ _ ih | store K v _ _ _ k _ _ _ ih =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      exact slotCode_prepend _ (ih hk')

/-- **The export of a program of the shape `LoadsChainK` has the slot shape**: its position
    `j` holds one operation writing `regName (D + j)`. -/
theorem loadsChainK_export_shape {Γ : Ctxt jasminDialect} {K : KCtx Γ} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChainK K p) {D n : Nat} {r : Exported}
    (hr : exportR nArgs fn p D n = some r) : SlotCode D r.code := by
  induction h generalizing D n r with
  | ret K vs =>
      simp only [exportR, Option.some.injEq] at hr
      subst hr
      unfold SlotCode; intro j i hj
      simp at hj
  | store K v _ _ _ k _ _ hk =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      exact slotCode_prepend _ (chainTailK_export_slot hk hk')
  | const K c k _ ih | free K _ k _ _ ih | load K _ _ _ k _ _ _ ih =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      exact slotCode_prepend _ (ih hk')

/-- **The instruction `ins` accesses an array of length `m` at the index register `x`**: its
    first source is an indexed operand at `x`, at the tag of a load or a store of length `m`. -/
def AccIdx (ins : LinstrRM) (x : String) (m : Nat) : Prop :=
  ∃ ds o b s ss w, ins.1 = .Lopn ds o (.arrIdx b x s :: ss) ∧
    (ins.2 = .load w m ∨ ins.2 = .store w m)

/-- An instruction at a register tag accesses no array. -/
theorem not_accIdx_reg {wire : LinstrR} {c : Option Nat} {x : String} {m : Nat} :
    ¬ AccIdx (wire, .reg c) x m := by
  rintro ⟨_, _, _, _, _, _, -, h | h⟩ <;> cases h

/-- **The index facts of a code at the known constants `K`**: the index register of every
    array access holds a constant below the length of the array, set by an immediate move
    earlier in the code or the name of a variable of that known constant. -/
def IdxFacts (nArgs : Nat) {Γ : Ctxt jasminDialect} (K : KCtx Γ) (C : List LinstrRM) : Prop :=
  ∀ (k : Nat) (ins : LinstrRM) (x : String) (m : Nat), C[k]? = some ins → AccIdx ins x m →
    ∃ c < m, (∃ j < k, C[j]? = some (LinstrR.Lopn [LOperand.reg x] "MOV:64" [LOperand.imm c],
      MemTag.reg none)) ∨
      ∃ v, K v = some c ∧ x = curName nArgs v

/-- **The index facts of a code with one instruction in front**, the instruction binding the
    variable of known constant `o`. -/
theorem idxFacts_cons {Γ : Ctxt jasminDialect} {t : JasminTy} {K : KCtx Γ} {o : Option Nat}
    {ins0 : LinstrRM} {C : List LinstrRM} (hn : nArgs ≤ Γ.length)
    (hC : IdxFacts nArgs (K.snoc (t := t) o) C)
    (h0 : ∀ x m, AccIdx ins0 x m → ∃ c < m, ∃ v, K v = some c ∧ x = curName nArgs v)
    (ho : ∀ c, o = some c →
      ins0 = (.Lopn [.reg (regName Γ.length)] "MOV:64" [.imm c], .reg none)) :
    IdxFacts nArgs K (ins0 :: C) := by
  unfold IdxFacts at hC ⊢
  intro k ins x m hk hacc
  cases k with
  | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      obtain ⟨c, hc, hv⟩ := h0 x m hacc
      exact ⟨c, hc, .inr hv⟩
  | succ k =>
      simp only [List.getElem?_cons_succ] at hk
      obtain ⟨c, hc, ⟨j, hj, hj'⟩ | ⟨v, hv, hx⟩⟩ := hC k ins x m hk hacc
      · exact ⟨c, hc, .inl ⟨j + 1, by omega, by simpa using hj'⟩⟩
      · cases v with
        | here =>
            have h1 := ho c hv
            refine ⟨c, hc, .inl ⟨0, by omega, ?_⟩⟩
            rw [hx, curName_here hn, h1]
            rfl
        | there v =>
            refine ⟨c, hc, .inr ⟨v, hv, ?_⟩⟩
            rw [hx, curName, curName, List.length_cons, resolveVar_there]

/-- The index facts of the export of a store at a known constant index. -/
theorem idxFacts_store {Γ : Ctxt jasminDialect} {K : KCtx Γ} {w m : Nat}
    (v : Var Γ (.stackArr w m)) (i : Var Γ (.reg 64)) (x : Var Γ (.reg w)) {c : Nat}
    (hi : K i = some c) (hc : c < m) :
    ∀ y m', AccIdx (.Lopn [.reg (regName Γ.length)] "STOREIDX"
          [.arrIdx (operandName (resolveVar Γ.length nArgs argName (fun _ => none) v))
            (operandName (resolveVar Γ.length nArgs argName (fun _ => none) i)) (w / 8),
            .reg (operandName (resolveVar Γ.length nArgs argName (fun _ => none) x))],
        .store w m) y m' → ∃ c < m', ∃ v, K v = some c ∧ y = curName nArgs v := by
  rintro y m' ⟨ds, o, b, s, ss, w', h1, h2 | h2⟩
  · cases h2
  · simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.arrIdx.injEq] at h1
    simp only [MemTag.store.injEq] at h2
    obtain ⟨-, -, ⟨-, rfl, -⟩, -⟩ := h1
    obtain ⟨-, rfl⟩ := h2
    exact ⟨c, hc, i, hi, rfl⟩

/-- The index facts of the export of a chain tail at constant indices. -/
theorem chainTailK_export_idx {Γ : Ctxt jasminDialect} {K : KCtx Γ} {w m : Nat}
    {ts : List JasminTy} {v : Var Γ (.stackArr w m)} {k : NFProg jasminDialect Γ ts}
    (h : ChainTailK K v k) (hn : nArgs ≤ Γ.length) {n : Nat} {r : Exported}
    (hr : exportR nArgs fn k Γ.length n = some r) : IdxFacts nArgs K r.code := by
  induction h generalizing n r with
  | ret K v =>
      simp only [exportR, Option.some.injEq] at hr
      subst hr
      unfold IdxFacts; intro j i x m hj
      simp at hj
  | @const Γ K w m ts v c k _ ih =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      simp only [Exported.prepend, bindOps_const, List.singleton_append]
      exact idxFacts_cons hn (ih (by simp only [List.length_cons]; omega) hk')
        (fun _ _ h => absurd h not_accIdx_reg) (fun _ h => by cases h; rfl)
  | @free Γ K w m t ts v e k he _ ih =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      obtain ⟨wire, c, hb⟩ := bindOps_memFree_reg nArgs Γ.length e he
      simp only [Exported.prepend, hb, List.singleton_append]
      exact idxFacts_cons hn (ih (by simp only [List.length_cons]; omega) hk')
        (fun _ _ h => absurd h not_accIdx_reg) (fun _ h => by cases h)
  | @store Γ K w m ts v i x c k hi hc _ ih =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      simp only [Exported.prepend]
      rw [bindOps_store_eq]
      exact idxFacts_cons hn (ih (by simp only [List.length_cons]; omega) hk')
        (idxFacts_store v i x hi hc) (fun _ h => by cases h)

/-- The index facts of the export of a program of the shape `LoadsChainK`. -/
theorem loadsChainK_export_idx {Γ : Ctxt jasminDialect} {K : KCtx Γ} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChainK K p) (hn : nArgs ≤ Γ.length) {n : Nat}
    {r : Exported} (hr : exportR nArgs fn p Γ.length n = some r) : IdxFacts nArgs K r.code := by
  induction h generalizing n r with
  | ret K vs =>
      simp only [exportR, Option.some.injEq] at hr
      subst hr
      unfold IdxFacts; intro j i x m hj
      simp at hj
  | @const Γ K ts c k _ ih =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      simp only [Exported.prepend, bindOps_const, List.singleton_append]
      exact idxFacts_cons hn (ih (by simp only [List.length_cons]; omega) hk')
        (fun _ _ h => absurd h not_accIdx_reg) (fun _ h => by cases h; rfl)
  | @free Γ K t ts e k he _ ih =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      obtain ⟨wire, c, hb⟩ := bindOps_memFree_reg nArgs Γ.length e he
      simp only [Exported.prepend, hb, List.singleton_append]
      exact idxFacts_cons hn (ih (by simp only [List.length_cons]; omega) hk')
        (fun _ _ h => absurd h not_accIdx_reg) (fun _ h => by cases h)
  | @load Γ K w m ts a i c k hi hc _ ih =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      simp only [Exported.prepend]
      rw [bindOps_load_eq]
      refine idxFacts_cons hn (ih (by simp only [List.length_cons]; omega) hk') ?_
        (fun _ h => by cases h)
      rintro y m' ⟨ds, o, b, s, ss, w', h1, h2 | h2⟩
      · simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.arrIdx.injEq] at h1
        simp only [MemTag.load.injEq] at h2
        obtain ⟨-, -, ⟨-, rfl, -⟩, -⟩ := h1
        obtain ⟨-, rfl⟩ := h2
        exact ⟨c, hc, i, hi, rfl⟩
      · cases h2
  | @store Γ K w m ts v i x c k hi hc hk =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      simp only [Exported.prepend]
      rw [bindOps_store_eq]
      exact idxFacts_cons hn
        (chainTailK_export_idx hk (by simp only [List.length_cons]; omega) hk')
        (idxFacts_store v i x hi hc) (fun _ h => by cases h)

/-- **In the export of a program of the shape `LoadsChainK`, the index register of every array
    access holds a constant below the length of the array**: at every position `k` whose
    instruction accesses an array of length `m` at the index register `x`, there is `c < m`
    with `KnownAt r.code k x c`, an immediate move `MOV:64 x, $c` below `k` and no write of `x`
    in between. -/
theorem loadsChainK_export_knownAt {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChainK (fun _ => none) p) (hn : nArgs ≤ Γ.length)
    {n : Nat} {r : Exported} (hr : exportR nArgs fn p Γ.length n = some r) :
    ∀ k ins x m, r.code[k]? = some ins → AccIdx ins x m → ∃ c < m, KnownAt r.code k x c := by
  intro k ins x m hk hacc
  have hI := loadsChainK_export_idx h hn hr
  unfold IdxFacts at hI
  obtain ⟨c, hc, ⟨j, hj, hJ⟩ | ⟨v, hv, -⟩⟩ := hI k ins x m hk hacc
  · have hS := loadsChainK_export_shape h hr
    unfold SlotCode at hS
    obtain ⟨o0, ss0, h0⟩ := hS j _ hJ
    simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq, and_true] at h0
    refine ⟨c, hc, j, hj, hJ, fun j' h1 _ i hi => ?_⟩
    obtain ⟨o, ss, hi'⟩ := hS j' i hi
    refine ⟨⟨_, _, _, hi'⟩, .inl ?_⟩
    rw [hi', h0.1]
    simp only [dstNames, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      JasminLsemExportRewrites.opNames, List.mem_singleton]
    intro he
    have := regName_injective he
    omega
  · cases hv

end Export

/-! ## 5. The lowered body of a tagged head -/

/-- **A renaming carries known constants**: every variable of known constant `c` under `K` is
    sent to a variable of known constant `c` under `K'`. -/
def KCtx.Maps {Γ Δ : Ctxt jasminDialect} (f : Ctxt.Hom Γ Δ) (K : KCtx Γ) (K' : KCtx Δ) : Prop :=
  ∀ v c, K v = some c → K' (f v) = some c

/-- **A partial renaming carries known constants.** -/
def KCtx.MapsP {Γ Δ : Ctxt jasminDialect} (f : PRen Γ Δ) (K : KCtx Γ) (K' : KCtx Δ) : Prop :=
  ∀ v v' c, f v = some v' → K v = some c → K' v' = some c

/-- No known constant is carried by every renaming. -/
theorem KCtx.maps_none {Γ Δ : Ctxt jasminDialect} (f : Ctxt.Hom Γ Δ) (K' : KCtx Δ) :
    KCtx.Maps f (fun _ => none) K' := fun _ _ h => by cases h

/-- A lifted renaming carries the extended known constants. -/
theorem KCtx.maps_lift {Γ Δ : Ctxt jasminDialect} {t : JasminTy} {f : Ctxt.Hom Γ Δ}
    {K : KCtx Γ} {K' : KCtx Δ} (h : KCtx.Maps f K K') (o : Option Nat) :
    KCtx.Maps (Ctxt.Hom.lift (s := t) f) (K.snoc o) (K'.snoc o) := by
  intro v c hv
  cases v with
  | here => exact hv
  | there v => exact h v c hv

/-- The renaming that sends the new variable to `x` carries the known constants of a binding of
    unknown value. -/
theorem KCtx.maps_bind {Γ Δ : Ctxt jasminDialect} {t : JasminTy} {ren : Ctxt.Hom Γ Δ}
    {K : KCtx Γ} {K' : KCtx Δ} (h : KCtx.Maps ren K K') (x : Var Δ t) :
    KCtx.Maps (Γ := t :: Γ) (NFProg.bindHom (.cons x .nil) ren) (K.snoc none) K' := by
  intro v c hv
  cases v with
  | here => cases hv
  | there v => exact h v c hv

/-- A lifted partial renaming carries the extended known constants. -/
theorem KCtx.mapsP_lift {Γ Δ : Ctxt jasminDialect} {t : JasminTy} {f : PRen Γ Δ}
    {K : KCtx Γ} {K' : KCtx Δ} (h : KCtx.MapsP f K K') (o : Option Nat) :
    KCtx.MapsP (PRen.lift (s := t) f) (K.snoc o) (K'.snoc o) := by
  intro v v' c hv hc
  cases v with
  | here =>
      cases hv
      exact hc
  | there v =>
      simp only [PRen.lift, Option.map_eq_some_iff] at hv
      obtain ⟨w, hw, rfl⟩ := hv
      exact h v w c hw hc

/-- The strengthening carries the known constants of the remaining variables. -/
theorem KCtx.mapsP_drop {Γ : Ctxt jasminDialect} {t : JasminTy} (K : KCtx Γ) (o : Option Nat) :
    KCtx.MapsP (@PRen.drop jasminDialect Γ t) (K.snoc o) K := by
  intro v v' c hv hc
  cases v with
  | here => cases hv
  | there v =>
      cases hv
      exact hc

/-- A partial renaming of a constant binding is the constant binding. -/
theorem rename?_const {Γ Δ : Ctxt jasminDialect} {f : PRen Γ Δ} {c : Nat}
    {e' : Expr jasminDialect Δ (.reg 64)} (he : Expr.rename? f (eConst64 (Γ := Γ) c) = some e') :
    e' = eConst64 c := by
  cases he
  rfl

/-- A partial renaming of a store binding renames its three arguments. -/
theorem rename?_store' {Γ Δ : Ctxt jasminDialect} {w m : Nat} (f : PRen Γ Δ)
    (v : Var Γ (.stackArr w m)) (i : Var Γ (.reg 64)) (x : Var Γ (.reg w))
    {e' : Expr jasminDialect Δ (.stackArr w m)}
    (he : Expr.rename? f (⟨.stackStore w m, rfl, .cons v (.cons i (.cons x .nil))⟩ :
      Expr jasminDialect Γ (.stackArr w m)) = some e') :
    ∃ v' i' x', f v = some v' ∧ f i = some i' ∧
      e' = ⟨.stackStore w m, rfl, .cons v' (.cons i' (.cons x' .nil))⟩ := by
  simp only [Expr.rename?, Option.map_eq_some_iff] at he
  obtain ⟨args, hargs, rfl⟩ := he
  change ((f v).bind fun v' => ((f i).bind fun i' => ((f x).bind fun x' =>
    (some HVector.nil).map (HVector.cons x')).map (HVector.cons i')).map (HVector.cons v')) =
      some args at hargs
  cases hv : f v <;> cases hi : f i <;> cases hx : f x <;>
    simp only [hv, hi, hx, Option.bind_none, Option.bind_some, Option.map_none, Option.map_some,
      reduceCtorEq, Option.some.injEq] at hargs
  subst hargs
  exact ⟨_, _, _, rfl, rfl, rfl⟩

/-- A partial renaming of a load binding renames its two arguments. -/
theorem rename?_load' {Γ Δ : Ctxt jasminDialect} {w m : Nat} (f : PRen Γ Δ)
    (a : Var Γ (.stackArr w m)) (i : Var Γ (.reg 64))
    {e' : Expr jasminDialect Δ (.reg w)}
    (he : Expr.rename? f (⟨.stackLoad w m, rfl, .cons a (.cons i .nil)⟩ :
      Expr jasminDialect Γ (.reg w)) = some e') :
    ∃ a' i', f i = some i' ∧ e' = ⟨.stackLoad w m, rfl, .cons a' (.cons i' .nil)⟩ := by
  simp only [Expr.rename?, Option.map_eq_some_iff] at he
  obtain ⟨args, hargs, rfl⟩ := he
  change ((f a).bind fun a' => ((f i).bind fun i' =>
    (some HVector.nil).map (HVector.cons i')).map (HVector.cons a')) = some args at hargs
  cases ha : f a <;> cases hi : f i <;>
    simp only [ha, hi, Option.bind_none, Option.bind_some, Option.map_none, Option.map_some,
      reduceCtorEq, Option.some.injEq] at hargs
  subst hargs
  exact ⟨_, _, rfl, rfl⟩

/-- **A partial renaming that carries the known constants keeps a chain tail at constant
    indices**, at the image of its current version. -/
theorem chainTailK_rename? {Γ : Ctxt jasminDialect} {K : KCtx Γ} {w m : Nat}
    {ts : List JasminTy} {v : Var Γ (.stackArr w m)} {k : NFProg jasminDialect Γ ts}
    (h : ChainTailK K v k) :
    ∀ {Δ : Ctxt jasminDialect} {f : PRen Γ Δ} {K' : KCtx Δ} {v' : Var Δ (.stackArr w m)}
      {k' : NFProg jasminDialect Δ ts}, KCtx.MapsP f K K' → f v = some v' →
      NFProg.rename? f k = some k' → ChainTailK K' v' k' := by
  induction h with
  | const K v c k _ ih =>
      intro Δ f K' v' k' hK hv hr
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
      obtain ⟨e', he', k'', hk', rfl⟩ := hr
      obtain rfl := rename?_const he'
      exact .const _ _ _ _ (ih (KCtx.mapsP_lift hK _) (by simp [PRen.lift, hv]) hk')
  | free K v e k he _ ih =>
      intro Δ f K' v' k' hK hv hr
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
      obtain ⟨e', he', k'', hk', rfl⟩ := hr
      exact .free _ _ _ _ ((rename?_op he').symm ▸ he)
        (ih (KCtx.mapsP_lift hK _) (by simp [PRen.lift, hv]) hk')
  | store K v i x c k hi hc _ ih =>
      intro Δ f K' v' k' hK hv hr
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
      obtain ⟨e', he', k'', hk', rfl⟩ := hr
      obtain ⟨v'', i', x', hv', hi', rfl⟩ := rename?_store' f v i x he'
      rw [hv] at hv'
      cases hv'
      exact .store _ _ _ _ c _ (hK i i' c hi' hi) hc (ih (KCtx.mapsP_lift hK _) rfl hk')
  | ret K v =>
      intro Δ f K' v' k' hK hv hr
      change Option.map NFProg.ret ((f v).bind fun v' =>
        (some HVector.nil).map (HVector.cons v')) = some k' at hr
      simp only [hv, Option.bind_some, Option.map_some, Option.some.injEq] at hr
      subst hr
      exact .ret _ _

/-- **A partial renaming that carries the known constants keeps the shape `LoadsChainK`.** -/
theorem loadsChainK_rename? {Γ : Ctxt jasminDialect} {K : KCtx Γ} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChainK K p) :
    ∀ {Δ : Ctxt jasminDialect} {f : PRen Γ Δ} {K' : KCtx Δ} {p' : NFProg jasminDialect Δ ts},
      KCtx.MapsP f K K' → NFProg.rename? f p = some p' → LoadsChainK K' p' := by
  induction h with
  | const K c k _ ih =>
      intro Δ f K' p' hK hr
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
      obtain ⟨e', he', k', hk', rfl⟩ := hr
      obtain rfl := rename?_const he'
      exact .const _ _ _ (ih (KCtx.mapsP_lift hK _) hk')
  | free K e k he _ ih =>
      intro Δ f K' p' hK hr
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
      obtain ⟨e', he', k', hk', rfl⟩ := hr
      exact .free _ _ _ ((rename?_op he').symm ▸ he) (ih (KCtx.mapsP_lift hK _) hk')
  | load K a i c k hi hc _ ih =>
      intro Δ f K' p' hK hr
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
      obtain ⟨e', he', k', hk', rfl⟩ := hr
      obtain ⟨a', i', hi', rfl⟩ := rename?_load' f a i he'
      exact .load _ _ _ c _ (hK i i' c hi' hi) hc (ih (KCtx.mapsP_lift hK _) hk')
  | store K v i x c k hi hc hk =>
      intro Δ f K' p' hK hr
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
      obtain ⟨e', he', k', hk', rfl⟩ := hr
      obtain ⟨v', i', x', -, hi', rfl⟩ := rename?_store' f v i x he'
      exact .store _ _ _ _ c _ (hK i i' c hi' hi) hc
        (chainTailK_rename? hk (KCtx.mapsP_lift hK _) rfl hk')
  | ret K vs =>
      intro Δ f K' p' hK hr
      simp only [NFProg.rename?, Option.map_eq_some_iff] at hr
      obtain ⟨ws, -, rfl⟩ := hr
      exact .ret _ _

/-- **Dead-binding elimination keeps a chain tail at constant indices.** -/
theorem chainTailK_dce {Γ : Ctxt jasminDialect} {K : KCtx Γ} {w m : Nat} {ts : List JasminTy}
    {v : Var Γ (.stackArr w m)} {k : NFProg jasminDialect Γ ts} (h : ChainTailK K v k) :
    ChainTailK K v (NFProg.dce k) := by
  induction h with
  | const K v c k _ ih =>
      simp only [NFProg.dce]
      split
      · rename_i k' hr
        exact chainTailK_rename? ih (KCtx.mapsP_drop _ _) (by simp [PRen.drop]) hr
      · exact .const _ _ _ _ ih
  | free K v e k he _ ih =>
      simp only [NFProg.dce]
      split
      · rename_i k' hr
        exact chainTailK_rename? ih (KCtx.mapsP_drop _ _) (by simp [PRen.drop]) hr
      · exact .free _ _ _ _ he ih
  | store K v i x c k hi hc _ ih =>
      have hn : NFProg.rename? PRen.drop (NFProg.dce k) = none :=
        rename?_chainTail_none ih.chainTail (by simp [PRen.drop])
      simp only [NFProg.dce, hn]
      exact .store _ _ _ _ _ _ hi hc ih
  | ret K v => exact .ret _ _

/-- **Dead-binding elimination keeps the shape `LoadsChainK`.** -/
theorem loadsChainK_dce {Γ : Ctxt jasminDialect} {K : KCtx Γ} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChainK K p) : LoadsChainK K (NFProg.dce p) := by
  induction h with
  | const K c k _ ih =>
      simp only [NFProg.dce]
      split
      · rename_i k' hr
        exact loadsChainK_rename? ih (KCtx.mapsP_drop _ _) hr
      · exact .const _ _ _ ih
  | free K e k he _ ih =>
      simp only [NFProg.dce]
      split
      · rename_i k' hr
        exact loadsChainK_rename? ih (KCtx.mapsP_drop _ _) hr
      · exact .free _ _ _ he ih
  | load K a i c k hi hc _ ih =>
      simp only [NFProg.dce]
      split
      · rename_i k' hr
        exact loadsChainK_rename? ih (KCtx.mapsP_drop _ _) hr
      · exact .load _ _ _ _ _ hi hc ih
  | store K v i x c k hi hc hk =>
      have hk' := chainTailK_dce hk
      have hn : NFProg.rename? PRen.drop (NFProg.dce k) = none :=
        rename?_chainTail_none hk'.chainTail (by simp [PRen.drop])
      simp only [NFProg.dce, hn]
      exact .store _ _ _ _ _ _ hi hc hk'
  | ret K vs => exact .ret _ _

/-- **The forwarding of loads keeps a chain tail at constant indices**, along every renaming
    that carries the known constants. -/
theorem chainTailK_fwdLoad1Go {Γ : Ctxt jasminDialect} {K : KCtx Γ} {w m : Nat}
    {ts : List JasminTy} {v : Var Γ (.stackArr w m)} {k : NFProg jasminDialect Γ ts}
    (h : ChainTailK K v k) :
    ∀ {Δ : Ctxt jasminDialect} (FK : NFFwdLoad1.StoreFacts Γ) (ren : Ctxt.Hom Γ Δ)
      (K' : KCtx Δ), KCtx.Maps ren K K' →
      ChainTailK K' (ren v) (NFFwdLoad1.fwdLoad1Go k FK ren) := by
  induction h with
  | const K v c k _ ih =>
      intro Δ FK ren K' hK
      simp only [NFFwdLoad1.fwdLoad1Go, loadArr1?_of_memFree (eConst64 c) rfl]
      exact .const _ _ _ _ (ih _ (Ctxt.Hom.lift ren) _ (KCtx.maps_lift hK _))
  | free K v e k he _ ih =>
      intro Δ FK ren K' hK
      simp only [NFFwdLoad1.fwdLoad1Go, loadArr1?_of_memFree e he]
      exact .free _ _ _ _ he (ih _ (Ctxt.Hom.lift ren) _ (KCtx.maps_lift hK _))
  | store K v i x c k hi hc _ ih =>
      intro Δ FK ren K' hK
      exact .store _ _ _ _ c _ (hK i c hi) hc (ih _ (Ctxt.Hom.lift ren) _ (KCtx.maps_lift hK _))
  | ret K v =>
      intro Δ FK ren K' hK
      exact .ret _ _

/-- **The forwarding of loads keeps the shape `LoadsChainK`**, along every renaming that
    carries the known constants. -/
theorem loadsChainK_fwdLoad1Go {Γ : Ctxt jasminDialect} {K : KCtx Γ} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChainK K p) :
    ∀ {Δ : Ctxt jasminDialect} (FK : NFFwdLoad1.StoreFacts Γ) (ren : Ctxt.Hom Γ Δ)
      (K' : KCtx Δ), KCtx.Maps ren K K' → LoadsChainK K' (NFFwdLoad1.fwdLoad1Go p FK ren) := by
  induction h with
  | const K c k _ ih =>
      intro Δ FK ren K' hK
      simp only [NFFwdLoad1.fwdLoad1Go, loadArr1?_of_memFree (eConst64 c) rfl]
      exact .const _ _ _ (ih _ (Ctxt.Hom.lift ren) _ (KCtx.maps_lift hK _))
  | free K e k he _ ih =>
      intro Δ FK ren K' hK
      simp only [NFFwdLoad1.fwdLoad1Go, loadArr1?_of_memFree e he]
      exact .free _ _ _ he (ih _ (Ctxt.Hom.lift ren) _ (KCtx.maps_lift hK _))
  | load K a i c k hi hc _ ih =>
      intro Δ FK ren K' hK
      simp only [NFFwdLoad1.fwdLoad1Go]
      split
      · split
        · exact ih _ _ _ (KCtx.maps_bind hK _)
        · exact .load _ _ _ c _ (hK i c hi) hc (ih _ (Ctxt.Hom.lift ren) _ (KCtx.maps_lift hK _))
      · exact .load _ _ _ c _ (hK i c hi) hc (ih _ (Ctxt.Hom.lift ren) _ (KCtx.maps_lift hK _))
  | store K v i x c k hi hc hk =>
      intro Δ FK ren K' hK
      exact .store _ _ _ _ c _ (hK i c hi) hc
        (chainTailK_fwdLoad1Go hk _ (Ctxt.Hom.lift ren) _ (KCtx.maps_lift hK _))
  | ret K vs =>
      intro Δ FK ren K' hK
      exact .ret _ _

/-- **The end of the lowering of a raised body keeps the shape `LoadsChainK`**: the carried
    form, the forwarding of loads and dead-binding elimination. -/
theorem loadsChainK_lowerBodyTail {as rs : List JasminTy} {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (hΓ : Γ = as) (hts : ts = rs) {r : NFProg jasminDialect Γ ts}
    (h : ∀ K : KCtx Γ, LoadsChainK K r) (K : KCtx as) :
    LoadsChainK K (NFProg.dce (NFFwdLoad1.fwdLoad1 (FieldDialectStep.castNF hΓ hts r))) := by
  subst hΓ hts
  exact loadsChainK_dce (loadsChainK_fwdLoad1Go (h K) _ _ K fun _ _ hv => hv)

/-- **A renamed block whose embedding is a chain tail at constant indices** is one at the image
    of the current version, under known constants carried by the renaming. -/
theorem chainTailK_ofCom_rename : ∀ {w' m' : Nat} {Γ Γ' : Ctxt jasminDialect} {a : JasminTy}
    (c : Com jasminDialect Γ a) (u : Var Γ (.stackArr w' m')) (f : Ctxt.Hom Γ Γ')
    {K : KCtx Γ} {K' : KCtx Γ'}, KCtx.Maps f K K' →
    ChainTailK K u (NFProg.ofCom c) → ChainTailK K' (f u) (NFProg.ofCom (c.rename f))
  | _, _, _, _, _, .ret v, u, f, K, K', _, h => by
      change ChainTailK K u (.ret (.cons v .nil)) at h
      cases h
      exact .ret _ _
  | w', m', Γ, _, _, .var (t := t) e c, u, f, K, K', hK, h => by
      change ChainTailK K u (.var e (NFProg.ofCom c)) at h
      change ChainTailK K' (f u) (.var (e.rename f) (NFProg.ofCom (c.rename f.lift)))
      have ih := fun (u' : Var (t :: Γ) (JasminTy.stackArr w' m')) (o : Option Nat)
          (h' : ChainTailK (K.snoc o) u' (NFProg.ofCom c)) =>
        chainTailK_ofCom_rename c u' f.lift (KCtx.maps_lift (K' := K') hK o) h'
      cases h with
      | const _ _ c' _ hb => exact .const _ _ c' _ (ih _ _ hb)
      | free _ _ _ _ he hb => exact .free _ _ _ _ he (ih _ _ hb)
      | store _ _ i x c' _ hi hc hb =>
          exact .store _ _ (f i) (f x) c' _ (hK i c' hi) hc (lift_here_chainTailK f (ih .here _ hb))

/-- **A renamed block whose embedding has the shape `LoadsChainK`** has the shape, under known
    constants carried by the renaming. -/
theorem loadsChainK_ofCom_rename : ∀ {Γ Γ' : Ctxt jasminDialect} {a : JasminTy}
    (c : Com jasminDialect Γ a) (f : Ctxt.Hom Γ Γ') {K : KCtx Γ} {K' : KCtx Γ'},
    KCtx.Maps f K K' → LoadsChainK K (NFProg.ofCom c) → LoadsChainK K' (NFProg.ofCom (c.rename f))
  | _, _, _, .ret _, _, _, _, _, _ => .ret _ _
  | _, _, _, .var e c, f, K, K', hK, h => by
      change LoadsChainK K (.var e (NFProg.ofCom c)) at h
      change LoadsChainK K' (.var (e.rename f) (NFProg.ofCom (c.rename f.lift)))
      have ih := fun (o : Option Nat) (h' : LoadsChainK (K.snoc o) (NFProg.ofCom c)) =>
        loadsChainK_ofCom_rename c f.lift (KCtx.maps_lift (K' := K') hK o) h'
      cases h with
      | const _ c' _ hb => exact .const _ c' _ (ih _ hb)
      | free _ _ _ he hb => exact .free _ _ _ he (ih _ hb)
      | load _ a i c' _ hi hc hb => exact .load _ (f a) (f i) c' _ (hK i c' hi) hc (ih _ hb)
      | store _ _ i x c' _ hi hc hb =>
          exact .store _ _ (f i) (f x) c' _ (hK i c' hi) hc (lift_here_chainTailK f
            (chainTailK_ofCom_rename c .here f.lift (KCtx.maps_lift hK _) hb))

/-- **A program continues the chain at `res` at constant indices**: at every known constants
    and every array type equal to the type of `res`, it is a chain tail at constant indices at
    `res` read at that type. -/
def ChainTailAtK {Γ : Ctxt jasminDialect} {a : JasminTy} {ts : List JasminTy} (res : Var Γ a)
    (q : NFProg jasminDialect Γ ts) : Prop :=
  ∀ (K : KCtx Γ) (w m : Nat) (h : a = .stackArr w m), ChainTailK K (h ▸ res) q

/-- The return of a transport of `res` continues the chain at `res` at constant indices. -/
theorem chainTailAtK_ret {Γ : Ctxt jasminDialect} {a : JasminTy} {w m : Nat} (res : Var Γ a)
    (x : Var Γ (.stackArr w m)) (h : a = .stackArr w m) (hx : x = h ▸ res) :
    ChainTailAtK res (.ret (.cons x .nil)) := by
  intro K w' m' h'
  obtain ⟨rfl, rfl⟩ : w = w' ∧ m = m' := by
    have := h.symm.trans h'
    injection this with h1 h2
    exact ⟨h1, h2⟩
  subst hx
  exact .ret _ _

/-- **The splice of a block whose embedding is a chain tail at constant indices**, before
    continuations that continue the chain at constant indices at the returned version, is a
    chain tail at constant indices. -/
theorem chainTailK_spliceNF?_ofCom {ts : List JasminTy} :
    ∀ {w' m' : Nat} {Δ : Ctxt jasminDialect} {a : JasminTy} (blk : Com jasminDialect Δ a)
      (kont : {Δ' : Ctxt jasminDialect} → Ctxt.Hom Δ Δ' → Var Δ' a →
        Option (NFProg jasminDialect Δ' ts)) (u : Var Δ (.stackArr w' m')) (K : KCtx Δ),
      ChainTailK K u (NFProg.ofCom blk) →
      (∀ {Δ' : Ctxt jasminDialect} (ren' : Ctxt.Hom Δ Δ') (res : Var Δ' a)
        (q' : NFProg jasminDialect Δ' ts), kont ren' res = some q' → ChainTailAtK res q') →
      ∀ {q : NFProg jasminDialect Δ ts}, NFProg.spliceNF? blk kont = some q → ChainTailK K u q
  | _, _, _, _, .ret v, kont, u, K, h, hK, _, hq => by
      change ChainTailK K u (.ret (.cons v .nil)) at h
      cases h
      exact hK _ _ _ hq K _ _ rfl
  | w', m', Δ, _, .var (t := t) e blk, kont, u, K, h, hK, _, hq => by
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
      change ChainTailK K u (.var e (NFProg.ofCom blk)) at h
      have ih := fun (u' : Var (t :: Δ) (JasminTy.stackArr w' m')) (K'' : KCtx (t :: Δ))
          (h' : ChainTailK K'' u' (NFProg.ofCom blk)) =>
        chainTailK_spliceNF?_ofCom blk _ u' K'' h' (fun ren' res q'' hq'' => hK _ res q'' hq'')
          hq'
      cases h with
      | const _ _ c _ hb => exact .const _ _ _ _ (ih _ _ hb)
      | free _ _ _ _ he hb => exact .free _ _ _ _ he (ih _ _ hb)
      | store _ _ i x c _ hi hc hb => exact .store _ _ _ _ _ _ hi hc (ih .here _ hb)

/-- **The splice of a block whose embedding has the shape `LoadsChainK`**, before continuations
    that continue the chain at constant indices at the returned version, has the shape. -/
theorem loadsChainK_spliceNF?_ofCom {ts : List JasminTy} :
    ∀ {Δ : Ctxt jasminDialect} {a : JasminTy} (blk : Com jasminDialect Δ a)
      (kont : {Δ' : Ctxt jasminDialect} → Ctxt.Hom Δ Δ' → Var Δ' a →
        Option (NFProg jasminDialect Δ' ts)) (K : KCtx Δ),
      LoadsChainK K (NFProg.ofCom blk) →
      (∀ {Δ' : Ctxt jasminDialect} (ren' : Ctxt.Hom Δ Δ') (res : Var Δ' a)
        (q' : NFProg jasminDialect Δ' ts), kont ren' res = some q' → ChainTailAtK res q') →
      (∀ {Δ' : Ctxt jasminDialect} (ren' : Ctxt.Hom Δ Δ') (res : Var Δ' a)
        (q' : NFProg jasminDialect Δ' ts), kont ren' res = some q' →
          ∀ K' : KCtx Δ', LoadsChainK K' q') →
      ∀ {q : NFProg jasminDialect Δ ts}, NFProg.spliceNF? blk kont = some q → LoadsChainK K q
  | _, _, .ret v, kont, K, _, _, hK', _, hq => hK' _ v _ hq K
  | _, _, .var e blk, kont, K, h, hK, hK', _, hq => by
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
      change LoadsChainK K (.var e (NFProg.ofCom blk)) at h
      have ih := fun K'' h' => loadsChainK_spliceNF?_ofCom blk _ K'' h'
        (fun ren' res q'' hq'' => hK _ res q'' hq'')
        (fun ren' res q'' hq'' => hK' _ res q'' hq'') hq'
      cases h with
      | const _ c _ hb => exact .const _ _ _ (ih _ hb)
      | free _ _ _ he hb => exact .free _ _ _ he (ih _ hb)
      | load _ a i c _ hi hc hb => exact .load _ _ _ _ _ hi hc (ih _ hb)
      | store _ v i x c _ hi hc hb =>
          exact .store _ _ _ _ _ _ hi hc (chainTailK_spliceNF?_ofCom blk _ .here _ hb
            (fun ren' res q'' hq'' => hK _ res q'' hq'') hq')

/-- **The splice of a block of memory-free operations**, before continuations of the shape
    `LoadsChainK` at every known constants, has the shape at every known constants. -/
theorem loadsChainK_spliceNF? {ts : List JasminTy} :
    ∀ {Δ : Ctxt jasminDialect} {a : JasminTy} (blk : Com jasminDialect Δ a)
      (kont : {Δ' : Ctxt jasminDialect} → Ctxt.Hom Δ Δ' → Var Δ' a →
        Option (NFProg jasminDialect Δ' ts)),
      ComFree blk →
      (∀ {Δ' : Ctxt jasminDialect} (ren' : Ctxt.Hom Δ Δ') (res : Var Δ' a)
        (q' : NFProg jasminDialect Δ' ts), kont ren' res = some q' →
          ∀ K' : KCtx Δ', LoadsChainK K' q') →
      ∀ {q : NFProg jasminDialect Δ ts}, NFProg.spliceNF? blk kont = some q →
        ∀ K : KCtx Δ, LoadsChainK K q
  | _, _, .ret v, kont, _, hK, _, h, K => hK _ v _ h K
  | _, _, .var e blk, kont, .var _ _ he hb, hK, _, h, K => by
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp h
      exact .free _ _ _ he (loadsChainK_spliceNF? blk _ hb
        (fun ren' res q'' hq => hK _ res q'' hq) hq' _)

section Template

open CatCrypt.Crypto.SecureCompilation.Algebraic (ModArithLimbTemplate)
open CatCrypt.Crypto.SecureCompilation.Haxc.ModArithLimbs (canonTemplateOf ofWide optTy
  ofWordsBlock? toWordsBlock? bodyBlock?)
open _root_.Hax.FieldTag (fieldLimbs)

/-- **The block of a method of the wide template has the shape `LoadsChainK`**, at every known
    constants. -/
theorem bodyBlock?_wide_loadsChainK {p : Nat} {W : WideTemplate p (fieldLimbs p)}
    {hw : wideTemplateOf p = some W} {Δ : Ctxt jasminDialect}
    (o : Option (ModArithLimbTemplate p .canon)) (ho : o = some (ofWide W hw))
    (m : _root_.Hax.FieldTag.FieldMethod)
    (args : HVector (fun t => Var Δ t)
      (Algebraic.ModArithLimbTemplate.limbSig (ModArithLimbs.optTy o) m))
    {blk : Com jasminDialect Δ (optTy o)} (hb : bodyBlock? o m args = some blk) (K : KCtx Δ) :
    LoadsChainK K (NFProg.ofCom blk) := by
  subst ho
  cases hb
  refine loadsChainK_ofCom_rename (ModArithLimbs.wideLimbBody W m) _
    (KCtx.maps_none _ K) ?_
  rw [← ModArithLimbs.wideBlockOf_eq]
  exact wideBlockOf_loadsChainK hw m _

set_option hygiene false in
/-- The splice of a cast block from words of the wide template. -/
local macro "cast_in_tacK" : tactic => `(tactic| (
  obtain ⟨b, hb, hq'⟩ := Option.bind_eq_some_iff.mp hq'
  refine loadsChainK_spliceNF? _ _
    (comFree_rename (ofWordsBlock?_wide_comFree _ hc _ _ _ hb) _)
    (fun ren' res q' hq' => ?_) hq'))

set_option hygiene false in
/-- The splice of the block of a method of the wide template before the cast to words and the
    return. -/
local macro "op_tail_tacK" : tactic => `(tactic| (
  obtain ⟨b, hb, hq'⟩ := Option.bind_eq_some_iff.mp hq'
  have h3 : ∀ K : KCtx _, LoadsChainK K (NFProg.ofCom b) := by
    simp only [ModArithLimbs.modArithLimbsJ, ModArithLimbs.limbLowerBlock?, Expr.rename,
      ModArithLimbs.limbOpBlock?, ModArithLimbs.modBlock?] at hb
    first
      | exact bodyBlock?_wide_loadsChainK _ hc _ _ hb
      | (split at hb <;> exact bodyBlock?_wide_loadsChainK _ hc _ _ hb)
  intro K
  refine loadsChainK_spliceNF?_ofCom _ _ K
    (loadsChainK_ofCom_rename _ _ (KCtx.maps_none _ K) (h3 _))
    (fun ren' res q' hq' => ?_) (fun ren' res q' hq' => ?_) hq'
  all_goals
    obtain ⟨b4, hb4, hq'⟩ := Option.bind_eq_some_iff.mp hq'
    simp only [ModArithLimbs.modArithLimbsJ, ModArithLimbs.limbLowerBlock?, Expr.rename,
      ModArithLimbs.limbOpBlock?, ModArithLimbs.limbCastBlock?] at hb4
    obtain ⟨h4, rfl⟩ := toWordsBlock?_wide_ret _ hc _ _ _ hb4
    simp only [Com.rename, NFProg.spliceNF?, Option.some.injEq] at hq'
    subst hq'
  · exact chainTailAtK_ret res _ h4
      (hom_cast (ModArithLimbs.modArithLimbsJ.bodyHom _ _ res) h4 _)
  · exact fun _ => .ret _ _))

/-- **The raised body on arrays, lowered to `mod_arith` and to the wide template, has the shape
    `LoadsChainK`** at every known constants. -/
theorem lowerArr_loadsChainK {p : Nat} {W : WideTemplate p (fieldLimbs p)}
    (hn : narrowFieldOf p = none) (hw : wideTemplateOf p = some W)
    (m : _root_.Hax.FieldTag.FieldMethod) {r₂ r₃}
    (h : NFProg.map? FieldToModArithChain.fieldToModArithJ FieldToModArithChain.regionTypes
      (FieldRaise.arrBody m p (fieldLimbs p)) (fun v => v) = some r₂)
    (h₃ : NFProg.map? ModArithLimbs.modArithLimbsJ ModArithLimbs.modArithLimbsJ_regionTypes r₂
      (fun v => v) = some r₃) : ∀ K, LoadsChainK K r₃ := by
  have hc := canonTemplateOf_wide hn hw
  cases m <;>
  simp only [NFProg.map?, FieldRaise.arrBody, FieldRaise.arrBody2, FieldRaise.arrBody1,
    FieldToModArithChain.fieldToModArithJ,
    FieldToModArithChain.lowerBlock?, FieldToModArithChain.opBlock?, FieldRaise.fromE,
    FieldRaise.toE, FieldRaise.opE, FieldToModArithChain.castBlock?, FieldToModArithChain.pfBlock?,
    FieldChainDialect.FieldRepr.Admits, ↓reduceIte, Option.bind_some, FieldToModArithChain.opB,
    Com.rename, NFProg.spliceNF?, Option.map_some] at h <;>
  obtain rfl := Option.some.inj h <;>
  have hq' := h₃ <;>
  simp only [NFProg.map?] at hq'
  · cast_in_tacK; cast_in_tacK; op_tail_tacK
  · cast_in_tacK; cast_in_tacK; op_tail_tacK
  · cast_in_tacK; cast_in_tacK; op_tail_tacK
  · cast_in_tacK; op_tail_tacK
  · cast_in_tacK; op_tail_tacK
  · cast_in_tacK; op_tail_tacK

/-- **The lowered body of a tagged head at a modulus without a narrow representation and with
    a wide template loads and stores at constant indices**: `fieldBodyD` has the shape
    `LoadsChainK` at every known constants. -/
theorem fieldBodyD_loadsChainK {f : String} {m : _root_.Hax.FieldTag.FieldMethod} {p : Nat}
    {W : WideTemplate p (fieldLimbs p)} (ht : _root_.Hax.FieldTag.fieldTag? f = some (m, p))
    (hn : narrowFieldOf p = none) (hw : wideTemplateOf p = some W) {as rs : List JasminTy}
    {b : NFProg jasminDialect as rs} (hb : FieldDialectStep.fieldBodyD f as rs = some b)
    (K : KCtx as) : LoadsChainK K b := by
  obtain ⟨-, r₁, hr₁, hb⟩ := FieldDialectStep.fieldBodyD_some hb
  unfold FieldRaise.raiseBody at hr₁
  rw [ht] at hr₁
  simp only [hn, hw] at hr₁
  unfold FieldRaise.raiseArr at hr₁
  split at hr₁
  · rename_i hs
    obtain ⟨has, hrs⟩ := hs
    obtain rfl := List.map_injective_iff.mpr Sum.inl_injective has
    obtain rfl : rs = [JasminTy.stackArr 64 (fieldLimbs p)] :=
      List.map_injective_iff.mpr Sum.inl_injective (hrs.trans rfl)
    cases hr₁
    obtain ⟨s₂, hs₂, hf⟩ := Option.bind_eq_some_iff.mp hb
    obtain ⟨s₃, hs₃, rfl⟩ := Option.map_eq_some_iff.mp hf
    exact loadsChainK_lowerBodyTail _ _ (lowerArr_loadsChainK hn hw m hs₂ hs₃) K
  · cases hr₁

end Template

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
