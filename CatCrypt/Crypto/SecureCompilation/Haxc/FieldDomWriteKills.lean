/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomLetsOnly
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldWideLeak

/-!
# Write-kills from the store-chain shape, and the shape of the field templates

The coalescing stages `G2` and `G3` hold on the field domain once every write of the exported
code kills its storage class (`WriteKills`, `fieldDom_coalesce_of_writeKills`). The argument
has a code-level end and a template end.

At the level of code, a straight body whose array writes form one chain per storage class has
the property: when every name is read only after its writes, a name that a store consumes (reads
as its base while writing another name) is not read after the store, and every name of the class
of a written name that is not written from that write on has been consumed by the time of the
write or is not read after it, then every write kills its class (`writeKills_of_chain`). The exported code of a field
template has this shape: the version of the output array that a store reads is never read again,
and the parameters are read before the first store.

At the level of structured programs the shape is `LoadsChain`: loads and memory-free bindings,
then a chain of stores in which each store reads the result of the previous one, ending in the
return of the last stored array. The body of a wide tagged call has it (`wideBlockOf_loadsChain`);
it is the invariant that the passes after the inlining of that body keep.

At the level of the templates, the block of every arithmetic operation of a registered wide
template is a multi-result program that loads limbs and runs memory-free bindings, then stores
the result limbs into the output array in one chain (`LoadsThenStores`,
`wideTemplateOf_loadsThenStores`). The Montgomery and the Solinas limb blocks, at every record,
bind no load, store, zeroed array or leaf call (`montBlocks_memFree`, `solinasBlocks_memFree`).

## Main definitions

* `CoalesceComplete.WrAt`, `CoalesceComplete.ConsumedAt`: a write of an array name at a
  position, and the consumption of a name by an instruction that reads it and writes another.
* `CoalesceComplete.ChainShape`: reads follow writes, a consumed name is dead, and the names of
  a written class that exist before the write are consumed by it.
* `InScope`, `ExportFacts`: the names in scope at a depth of the export, and the facts of
  the export of a program of loads, then one chain of stores.
* `FieldChainShape`: the store-chain shape of the code with the result copies of the webs of a
  member of the field domain.
* `LoadsThenStores`: a multi-result program of loads and memory-free bindings followed by the
  chain of stores `storeLimbs`.
* `ChainTail`, `LoadsChain`: the same shape on a structured program, by operation: loads and
  memory-free bindings, then stores each of which reads the result of the previous one, and the
  return of the last stored array.

## Main results

* `CoalesceComplete.writeKills_of_chain`: a body of the chain shape kills its classes at every
  write.
* `CoalesceComplete.interf_of_chain`: no interference on a straight body of the chain shape.
* `montBlocks_memFree`, `solinasBlocks_memFree`: the limb blocks of the Montgomery and Solinas
  templates bind memory-free operations only, at every record.
* `fieldBodyOf_loadsThenStores`: the lowered field program over word arrays has the shape
  `LoadsThenStores` when its blocks are memory-free.
* `wideTemplateOf_loadsThenStores`: the block of every arithmetic operation of a registered wide
  template is the head projection of a program of that shape.
* `loadsChain_of_loadsThenStores`: a renamed head projection of such a program, embedded as a
  structured program, has the shape `LoadsChain`.
* `wideBlockOf_loadsChain`: the body of a wide tagged call has the shape `LoadsChain`, at every
  modulus with a registered wide template and every method.
* `fieldDom_coalesce_of_chainShape`, `fieldDom_coCfgB_of_chainShape`,
  `fieldDom_coEntryFix_of_chainShape`: the stages `G2` and `G3` on the field domain from the
  store-chain shape of the code (`FieldChainShape`), at the types of the fields of
  `FieldDomStages` under that hypothesis.
* `bindOps_store`, `bindOps_load`, `bindOps_memFree`: the export of a binding of a store, a
  load or a memory-free operation is one instruction, which writes the array of its slot and
  reads its base array, reads its base array only, or reads and writes no array.
* `chainTail_export`, `loadsChain_export`: the export of a program of the shape `LoadsChain`
  reads names in scope, writes at each store the name of its slot, and does not read a name
  after the store that consumes it (`ExportFacts`).
* `loadsChain_export_chainShape₁₂`: the first two conjuncts of `ChainShape` on that export.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)

/-! ## 1. Write-kills from the store-chain shape -/

/-- The instruction of `body` at the position `k` writes the array name `d`. -/
def WrAt (body : List LinstrRM) (ao : String → Option Nat) (k : Nat) (d : String) : Prop :=
  ∃ i, body[k]? = some i ∧ wrArr ao i = some d

/-- **The instruction at `c` consumes the name `r`**: it reads `r` and writes an array name
    other than `r` (a store reading its base array and writing the next version). -/
def ConsumedAt (body : List LinstrRM) (aa : String → Nat → Option Nat)
    (ao : String → Option Nat) (c : Nat) (r : String) : Prop :=
  ∃ i d, body[c]? = some i ∧ r ∈ rdArr aa i ∧ wrArr ao i = some d ∧ d ≠ r

/-- **The store-chain shape of a body under the alias map `σ`**: every name is read only after
    each of its writes; a consumed name is not read after the instruction that consumes it (nor
    after the body); and at a write of `d` at `k`, every other name of the class of `d` whose
    writes all precede `k` (a parameter, or an earlier version of the chain) is consumed at a
    position up to `k` or is not read after `k`. -/
def ChainShape (σ : String → String) (body : List LinstrRM) (aa : String → Nat → Option Nat)
    (ao : String → Option Nat) (obs : List String) : Prop :=
  (∀ j r w, ReadAt body aa obs j r → WrAt body ao w r → w < j)
    ∧ (∀ c r j, ConsumedAt body aa ao c r → ReadAt body aa obs j r → j ≤ c)
    ∧ ∀ k d r, WrAt body ao k d → σ r = σ d → r ≠ d → (∀ w, WrAt body ao w r → w < k) →
      (∃ c, c ≤ k ∧ ConsumedAt body aa ao c r) ∨ ∀ j, k < j → ¬ ReadAt body aa obs j r

/-- **A body of the store-chain shape kills its classes at every write.** A name `r ≠ d` of the
    class of a name `d` written at `k`, read at `j > k` and not written in `[k + 1, j)`, has all
    its writes before `k` (they precede its read at `j`, and the write at `k` is of `d`); so it
    was consumed at a position up to `k`, and is not read after that, or it is not read after
    `k` at all. -/
theorem writeKills_of_chain {σ : String → String} {body : List LinstrRM}
    {aa : String → Nat → Option Nat} {ao : String → Option Nat} {obs : List String}
    (h : ChainShape σ body aa ao obs) : WriteKills σ body aa ao obs := by
  obtain ⟨hrw, hdead, hcls⟩ := h
  intro k i d hk hd r hne heq j hkj hR hN
  have hbefore : ∀ w, WrAt body ao w r → w < k := by
    intro w hw
    have hwj := hrw j r w hR hw
    obtain ⟨i', hi', hw'⟩ := hw
    rcases Nat.lt_or_ge w k with hlt | hge
    · exact hlt
    · rcases Nat.eq_or_lt_of_le hge with rfl | hgt
      · rw [hk] at hi'
        cases hi'
        rw [hd] at hw'
        cases hw'
        exact absurd rfl hne
      · exact absurd hw' (hN w i' hgt hwj hi')
  rcases hcls k d r ⟨i, hk, hd⟩ heq hne hbefore with ⟨c, hck, hc⟩ | hnr
  · have := hdead c r j hc hR
    omega
  · exact hnr j hkj hR

/-- **No interference on a straight body of the store-chain shape.** -/
theorem interf_of_chain {σ : String → String} {body : List LinstrRM}
    {aa : String → Nat → Option Nat} {ao : String → Option Nat} {obs : List String}
    (hs : Straight body) (h : ChainShape σ body aa ao obs) :
    Interf σ body ao (PLive body aa ao obs) :=
  interf_of_writeKills hs (writeKills_of_chain h)

end CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.Algebraic
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont (LimbParams)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519 (w64 MC bindK)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs (arrTy loadLimbs loadArgs
  storeLimbs eLoad eStore)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldWideLeak (jMemFree MemFree PrefixClosed
  lowerR_q lowerOpL_memFree solinasLowerOpL_memFree exprBlock_memFree solinasExprBlock_memFree
  twistOp_coveredArith)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldWideInline
open CatCrypt.Crypto.SecureCompilation.VIR.TowerToLimbs (montBlocks solinasBlocks)
open Ctxt (Var)

/-! ## 2. The limb blocks of the templates -/

/-- **The Montgomery limb blocks bind memory-free operations only**: at every record `P`, the
    block of every arithmetic operation at `P.p` binds no load, store, zeroed array or leaf
    call. -/
theorem montBlocks_memFree {n : Nat} (P : LimbParams n) (op : fieldDialect.Op)
    (hop : FieldLower.arithOpB (montBlocks P).p op = true) :
    MemFree ((montBlocks P).blocks op) :=
  lowerOpL_memFree P op hop

/-- **The Solinas limb blocks bind memory-free operations only**: at every record `S`, the
    block of every arithmetic operation at the modulus of `S` binds no load, store, zeroed array
    or leaf call. -/
theorem solinasBlocks_memFree {n : Nat} (S : Solinas.SolinasParams n) (op : fieldDialect.Op)
    (hop : FieldLower.arithOpB (solinasBlocks S).p op = true) :
    MemFree ((solinasBlocks S).blocks op) :=
  solinasLowerOpL_memFree S op hop

/-! ## 3. The shape of the template bodies -/

variable {n : Nat}

/-- **Loads, then one chain of stores**: a multi-result program built of loads `eLoad` of limbs
    and of memory-free bindings, ending in the chain of stores `storeLimbs m j o h` of the limbs
    `h` into the array `o` from the index `j`. -/
inductive LoadsThenStores : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} → MC Γ ts → Prop
  /-- The chain of stores into `o`. -/
  | stores {Γ : Ctxt jasminDialect} (m j : Nat) (o : Var Γ (arrTy n))
      (h : Ctxt.Hom (Mont.Rn m) Γ) : LoadsThenStores (storeLimbs m j o h)
  /-- A memory-free binding in front. -/
  | free {Γ : Ctxt jasminDialect} {t : JasminTy} {ts : List JasminTy}
      (e : Expr jasminDialect Γ t) (k : MC (t :: Γ) ts) :
      jMemFree e.op = true → LoadsThenStores k → LoadsThenStores (.var e k)
  /-- A load of a limb in front. -/
  | load {Γ : Ctxt jasminDialect} {ts : List JasminTy} (a : Var Γ (arrTy n)) (i : Var Γ w64)
      (k : MC (w64 :: Γ) ts) : LoadsThenStores k → LoadsThenStores (.var (eLoad a i) k)

/-- The shape `LoadsThenStores` is closed under a memory-free binding in front. -/
theorem loadsThenStores_prefixClosed :
    PrefixClosed (fun {Γ} {ts} m => LoadsThenStores (n := n) (Γ := Γ) (ts := ts) m) :=
  fun e k he hk => .free e k he hk

/-- **The loads of limbs keep the shape of every continuation.** -/
theorem loadLimbs_loadsThenStores {bs : List JasminTy} :
    ∀ {Δ : Ctxt jasminDialect} (m j : Nat) (a : Var Δ (arrTy n))
      {k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → Ctxt.Hom (Mont.Rn m) Δ' → MC Δ' bs},
      (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') h, LoadsThenStores (n := n) (k r h)) →
      LoadsThenStores (n := n) (loadLimbs m j a k)
  | _, 0, _, _, _, hk => by rw [loadLimbs]; exact hk _ _
  | _, m + 1, j, a, _, hk => by
      rw [loadLimbs, bindK, bindK]
      exact .free _ _ rfl (.load _ _ _
        (loadLimbs_loadsThenStores m (j + 1) _ fun _ _ => hk _ _))

/-- **The loads of the limbs of every array keep the shape of every continuation.** -/
theorem loadArgs_loadsThenStores {bs : List JasminTy} :
    ∀ (Γ : Ctxt fieldDialect) {Δ : Ctxt jasminDialect}
      (src : Ctxt.Hom (FieldToJasminLimbs.arrCtx n Γ) Δ)
      {k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' →
        Ctxt.Hom (MultiBlockLowering.ctxFlat (FieldToJasminLimbs.mapTysL n) Γ) Δ' → MC Δ' bs},
      (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') h, LoadsThenStores (n := n) (k r h)) →
      LoadsThenStores (n := n) (loadArgs Γ src k)
  | [], _, _, _, hk => by rw [loadArgs]; exact hk _ _
  | _ :: Γ, _, _, _, hk => by
      rw [loadArgs]
      exact loadLimbs_loadsThenStores _ _ _ fun _ _ =>
        loadArgs_loadsThenStores Γ _ fun _ _ => hk _ _

/-- **The lowered field program over word arrays loads, then stores in one chain**, for a
    covered program whose blocks are memory-free: the loads of the limbs of the input arrays,
    the memory-free lowered blocks, and the chain of stores into the output array. -/
theorem fieldBodyOf_loadsThenStores (lo : FieldToJasminLimbs.LimbBlocks n)
    {Good : ∀ {Γ : Ctxt fieldDialect} {t : FieldTy}, Expr fieldDialect Γ t → Prop}
    (hB : ∀ {Γ : Ctxt fieldDialect} {t : FieldTy} (e : Expr fieldDialect Γ t), Good e →
      MemFree ((FieldToJasminLimbs.loweringOf lo).exprBlock e))
    {Γ : Ctxt fieldDialect} {t : FieldTy} (c : Com fieldDialect Γ t)
    (hc : BlockLoweringCPS.CoveredCom Good c) :
    LoadsThenStores (n := n) (FieldToJasminLimbs.fieldBodyOf lo c) := by
  rw [FieldToJasminLimbs.fieldBodyOf]
  exact loadArgs_loadsThenStores Γ _ fun _ _ =>
    lowerR_q loadsThenStores_prefixClosed _ hB _ c hc fun _ _ => .stores _ _ _ _

/-- **The blocks of a wide template load, then store in one chain**: the block of every
    operation of `arithOpB p` is the head projection of a program of the shape
    `LoadsThenStores`. -/
def WideLoadsThenStores {p m : Nat} (W : WideTemplate p m) : Prop :=
  ∀ op : fieldDialect.Op, FieldLower.arithOpB p op = true →
    ∃ body : MC (FieldToJasminLimbs.arrCtx m (DialectSignature.sig op) ++ [arrTy m]) [arrTy m],
      @FieldLower.FieldLowerTemplate.block W.α m W.inst W.P op = body.toComHead
        ∧ LoadsThenStores (n := m) body

/-- The canonical Montgomery template of a record loads, then stores in one chain. -/
theorem ofMont_loadsThenStores (P : LimbParams n) (hn : n < 2 ^ 64) :
    WideLoadsThenStores (WideTemplate.ofMont P hn) := fun op hop =>
  ⟨FieldToJasminLimbs.fieldBodyOf (FieldToJasminLimbs.lowerOpL P) (twistOp n op), rfl,
    fieldBodyOf_loadsThenStores _ (exprBlock_memFree P) _ (twistOp_coveredArith P op hop)⟩

theorem castN_loadsThenStores {p m : Nat} (h : n = m) {W : WideTemplate p n}
    (hW : WideLoadsThenStores W) : WideLoadsThenStores (W.castN h) := by
  subst h
  exact hW

theorem castP_loadsThenStores {p q : Nat} (h : p = q)
    {W : WideTemplate p (_root_.Hax.FieldTag.fieldLimbs p)} (hW : WideLoadsThenStores W) :
    WideLoadsThenStores (W.castP h) := by
  subst h
  exact hW

/-- The Solinas template of a record loads, then stores in one chain. -/
theorem ofSolinasAt_loadsThenStores (S : Solinas.SolinasParams n)
    (hn : n = _root_.Hax.FieldTag.fieldLimbs (Solinas.p S)) (h64 : n < 2 ^ 64) :
    WideLoadsThenStores (WideTemplate.ofSolinasAt S hn h64) := by
  refine castN_loadsThenStores hn fun op hop => ⟨FieldToJasminLimbs.fieldBodyOf
    (FieldToJasminLimbsSolinas.lowerOpL S) (FieldLower.opCom op), rfl,
    fieldBodyOf_loadsThenStores _ (solinasExprBlock_memFree S) _
      (FieldLower.coveredCom_opCom (fun h => h) op hop)⟩

/-- **The blocks of a registered wide template load, then store in one chain**, at every
    modulus. -/
theorem wideTemplateOf_loadsThenStores {p : Nat}
    {W : WideTemplate p (_root_.Hax.FieldTag.fieldLimbs p)} (h : wideTemplateOf p = some W) :
    WideLoadsThenStores W := by
  rcases wideTemplateOf_cases h with ⟨_, S, hn, h64, hp, rfl⟩ | ⟨_, _, _, rfl⟩
  · exact castP_loadsThenStores hp (ofSolinasAt_loadsThenStores S hn h64)
  · exact ofMont_loadsThenStores _ _

/-! ## 4. The shape at the level of structured programs -/

/-- **The tail of a chain of stores at the current version `v`**: memory-free bindings and
    stores, each store reading the current version as its base and making its result the next
    version, ending in the return of the last version alone. -/
inductive ChainTail : {Γ : Ctxt jasminDialect} → {w m : Nat} → Var Γ (.stackArr w m) →
    {ts : List JasminTy} → NFProg jasminDialect Γ ts → Prop
  /-- A memory-free binding. -/
  | free {Γ : Ctxt jasminDialect} {w m : Nat} {t : JasminTy} {ts : List JasminTy}
      (v : Var Γ (.stackArr w m)) (e : Expr jasminDialect Γ t)
      (k : NFProg jasminDialect (t :: Γ) ts) :
      jMemFree e.op = true → ChainTail v.there k → ChainTail v (.var e k)
  /-- A store into the current version, whose result is the next version. -/
  | store {Γ : Ctxt jasminDialect} {w m : Nat} {ts : List JasminTy}
      (v : Var Γ (.stackArr w m)) (i : Var Γ (.reg 64)) (x : Var Γ (.reg w))
      (k : NFProg jasminDialect (.stackArr w m :: Γ) ts) :
      ChainTail .here k →
        ChainTail v (.var ⟨.stackStore w m, rfl, .cons v (.cons i (.cons x .nil))⟩ k)
  /-- The return of the current version. -/
  | ret {Γ : Ctxt jasminDialect} {w m : Nat} (v : Var Γ (.stackArr w m)) :
      ChainTail v (.ret (.cons v .nil))

/-- **Loads, then one chain of stores**, on a structured program: loads and memory-free
    bindings, then a first store, whose result starts a `ChainTail`. -/
inductive LoadsChain : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} →
    NFProg jasminDialect Γ ts → Prop
  /-- A memory-free binding. -/
  | free {Γ : Ctxt jasminDialect} {t : JasminTy} {ts : List JasminTy}
      (e : Expr jasminDialect Γ t) (k : NFProg jasminDialect (t :: Γ) ts) :
      jMemFree e.op = true → LoadsChain k → LoadsChain (.var e k)
  /-- A load. -/
  | load {Γ : Ctxt jasminDialect} {w m : Nat} {ts : List JasminTy}
      (a : Var Γ (.stackArr w m)) (i : Var Γ (.reg 64))
      (k : NFProg jasminDialect (.reg w :: Γ) ts) :
      LoadsChain k → LoadsChain (.var ⟨.stackLoad w m, rfl, .cons a (.cons i .nil)⟩ k)
  /-- The first store, whose result starts the chain. -/
  | store {Γ : Ctxt jasminDialect} {w m : Nat} {ts : List JasminTy}
      (v : Var Γ (.stackArr w m)) (i : Var Γ (.reg 64)) (x : Var Γ (.reg w))
      (k : NFProg jasminDialect (.stackArr w m :: Γ) ts) :
      ChainTail .here k →
        LoadsChain (.var ⟨.stackStore w m, rfl, .cons v (.cons i (.cons x .nil))⟩ k)
  /-- A return without a store. -/
  | ret {Γ : Ctxt jasminDialect} {ts : List JasminTy} (vs : HVector (fun t => Var Γ t) ts) :
      LoadsChain (.ret vs)

/-- The embedding of a renamed head projection of a binding (unfolding lemma). -/
theorem ofCom_rename_toComHead_var {Γ Γ' : Ctxt jasminDialect} {t u : JasminTy}
    {ts : List JasminTy} (f : Ctxt.Hom Γ Γ') (e : Expr jasminDialect Γ t)
    (k : MC (t :: Γ) (u :: ts)) :
    NFProg.ofCom (Com.rename f (MultiReturnCom.var e k).toComHead) =
      .var (e.rename f) (NFProg.ofCom (Com.rename f.lift k.toComHead)) := by
  rw [MultiReturnCom.toComHead.eq_2]
  rfl

/-- The embedding of a renamed head projection of a return (unfolding lemma). -/
theorem ofCom_rename_toComHead_ret {Γ Γ' : Ctxt jasminDialect} {u : JasminTy}
    {ts : List JasminTy} (f : Ctxt.Hom Γ Γ') (v : Var Γ u) (vs : HVector (fun t => Var Γ t) ts) :
    NFProg.ofCom (Com.rename f (MultiReturnCom.ret (.cons v vs)).toComHead) =
      .ret (.cons (f v) .nil) := by
  rw [MultiReturnCom.toComHead.eq_1]
  rfl

/-- A chain tail at the image of the newest variable under a lifted renaming is a chain tail
    at the newest variable. -/
theorem lift_here_chainTail {Γ Γ' : Ctxt jasminDialect} {w m : Nat} {ts : List JasminTy}
    (f : Ctxt.Hom Γ Γ') {k : NFProg jasminDialect (.stackArr w m :: Γ') ts}
    (h : ChainTail (Ctxt.Hom.lift f (Var.here : Var (JasminTy.stackArr w m :: Γ) _)) k) :
    ChainTail .here k := by
  simpa [Ctxt.Hom.lift] using h

/-- The chain of stores `storeLimbs`, renamed and embedded, is a chain tail at the image of
    its base array. -/
theorem storeLimbs_chainTail : ∀ {Δ Γ' : Ctxt jasminDialect} (m j : Nat) (o : Var Δ (arrTy n))
    (h : Ctxt.Hom (Mont.Rn m) Δ) (f : Ctxt.Hom Δ Γ'),
    ChainTail (f o) (NFProg.ofCom (Com.rename f (storeLimbs m j o h).toComHead))
  | _, _, 0, _, _, _, f => by
      rw [storeLimbs, ofCom_rename_toComHead_ret]
      exact .ret _
  | _, _, m + 1, j, _, _, f => by
      rw [storeLimbs, bindK, bindK, ofCom_rename_toComHead_var, ofCom_rename_toComHead_var]
      exact .free _ _ _ rfl (.store _ _ _ _
        (lift_here_chainTail _ (storeLimbs_chainTail m (j + 1) Var.here _
          (Ctxt.Hom.lift (Ctxt.Hom.lift f)))))

/-- The chain of stores `storeLimbs`, renamed and embedded, loads, then stores in one
    chain. -/
theorem storeLimbs_loadsChain {Δ Γ' : Ctxt jasminDialect} (m j : Nat) (o : Var Δ (arrTy n))
    (h : Ctxt.Hom (Mont.Rn m) Δ) (f : Ctxt.Hom Δ Γ') :
    LoadsChain (NFProg.ofCom (Com.rename f (storeLimbs m j o h).toComHead)) := by
  cases m with
  | zero =>
      rw [storeLimbs, ofCom_rename_toComHead_ret]
      exact .ret _
  | succ m =>
      rw [storeLimbs, bindK, bindK, ofCom_rename_toComHead_var, ofCom_rename_toComHead_var]
      exact .free _ _ rfl (.store _ _ _ _
        (lift_here_chainTail _ (storeLimbs_chainTail m (j + 1) Var.here _
          (Ctxt.Hom.lift (Ctxt.Hom.lift f)))))

/-- **The head projection of a program that loads, then stores in one chain, renamed and
    embedded as a structured program, loads, then stores in one chain.** -/
theorem loadsChain_of_loadsThenStores : ∀ {Γ : Ctxt jasminDialect} {t : JasminTy}
    {ts : List JasminTy} {body : MC Γ (t :: ts)}, LoadsThenStores (n := n) body →
    ∀ {Γ' : Ctxt jasminDialect} (f : Ctxt.Hom Γ Γ'),
      LoadsChain (NFProg.ofCom (Com.rename f body.toComHead))
  | _, _, _, _, .stores m j o h, _, f => storeLimbs_loadsChain m j o h f
  | _, _, _, _, .free _ _ he hk, _, f => by
      rw [ofCom_rename_toComHead_var]
      exact .free _ _ he (loadsChain_of_loadsThenStores hk f.lift)
  | _, _, _, _, .load _ _ _ hk, _, f => by
      rw [ofCom_rename_toComHead_var]
      exact .load _ _ _ (loadsChain_of_loadsThenStores hk f.lift)

/-- **The body of a wide tagged call loads, then stores in one chain**: at every modulus with a
    registered wide template and every method, `wideBlockOf W m` is a structured program of the
    shape `LoadsChain`. -/
theorem wideBlockOf_loadsChain {p : Nat}
    {W : WideTemplate p (_root_.Hax.FieldTag.fieldLimbs p)} (h : wideTemplateOf p = some W)
    (m : _root_.Hax.FieldTag.FieldMethod) : LoadsChain (wideBlockOf W m) := by
  obtain ⟨body, hb, hs⟩ := wideTemplateOf_loadsThenStores h (fieldOpOf m p)
    (arithOpB_fieldOpOf m p)
  unfold wideBlockOf templateCall
  exact (congrArg (fun c => LoadsChain (NFProg.ofCom (Com.rename _ c))) hb).mpr
    (loadsChain_of_loadsThenStores hs _)

/-! ## 5. The stages from the store-chain shape of the code -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete (ChainShape
  writeKills_of_chain)

/-- **The store-chain shape of the code of a member of the field domain**: the code with the
    result copies of its webs, under the coalescing alias map, with the names read after the
    code the returned arrays. -/
def FieldChainShape (σ : AbiLayout) (t : JasminTy) (r : Exported) : Prop :=
  ChainShape (canonMemrefName (regionAliasTab σ exportReg t none r.res
      (regionCoCode σ exportReg t r.code r.res (regionCopy σ exportReg t none r.code r.res))))
    (regionCoCode σ exportReg t r.code r.res (regionCopy σ exportReg t none r.code r.res))
    (calleeAAT none) (calleeAOT none)
    (regionCoObs t (regionOut (regionCopy σ exportReg t none r.code r.res) r.res))

/-- **Stages `G2` and `G3` from the store-chain shape**: on a member of the field domain whose
    code has the shape `FieldChainShape`, the gate refuses neither at `coCfgB` nor at
    `coEntryFix`. -/
theorem fieldDom_coalesce_of_chainShape {e : _root_.Hax.TExpr} {σ : AbiLayout}
    {fname : String} {b : Lcmd} {t : JasminTy} {r : Exported} {cert : List (String × String)}
    (h : fieldDomB e σ = true) (hB : FieldBody e σ fname b t r cert)
    (hC : FieldChainShape σ t r) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "coCfgB" ∧
      regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "coEntryFix" :=
  fieldDom_coalesce_of_writeKills h hB (writeKills_of_chain hC)

/-- **Stage `G2`** when the code of every member of the field domain has the store-chain
    shape. -/
theorem fieldDom_coCfgB_of_chainShape
    (hS : ∀ {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd}
      {t : JasminTy} {r : Exported} {cert : List (String × String)},
      fieldDomB e σ = true → FieldBody e σ fname b t r cert → FieldChainShape σ t r)
    {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
    {r : Exported} {cert : List (String × String)} (h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "coCfgB" :=
  (fieldDom_coalesce_of_chainShape h hB (hS h hB)).1

/-- **Stage `G3`** when the code of every member of the field domain has the store-chain
    shape. -/
theorem fieldDom_coEntryFix_of_chainShape
    (hS : ∀ {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd}
      {t : JasminTy} {r : Exported} {cert : List (String × String)},
      fieldDomB e σ = true → FieldBody e σ fname b t r cert → FieldChainShape σ t r)
    {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
    {r : Exported} {cert : List (String × String)} (h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "coEntryFix" :=
  (fieldDom_coalesce_of_chainShape h hB (hS h hB)).2

example (S : FieldDomStages)
    (hS : ∀ {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd}
      {t : JasminTy} {r : Exported} {cert : List (String × String)},
      fieldDomB e σ = true → FieldBody e σ fname b t r cert → FieldChainShape σ t r) :
    type_of% @S.coCfgB := @fieldDom_coCfgB_of_chainShape hS

example (S : FieldDomStages)
    (hS : ∀ {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd}
      {t : JasminTy} {r : Exported} {cert : List (String × String)},
      fieldDomB e σ = true → FieldBody e σ fname b t r cert → FieldChainShape σ t r) :
    type_of% @S.coEntryFix := @fieldDom_coEntryFix_of_chainShape hS

/-! ## 6. The exported instructions of loads, stores and memory-free bindings -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete (rdArr wrArr)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN (operandName)

/-- A variable resolves to a register operand when no slot is an immediate. -/
theorem resolveVar_reg (d nArgs : Nat) {Γ : Ctxt jasminDialect} {τ : JasminTy} (v : Var Γ τ) :
    resolveVar d nArgs argName (fun _ => none) v =
      .reg (operandName (resolveVar d nArgs argName (fun _ => none) v)) := by
  simp only [resolveVar]
  split <;> rfl

/-- **The exported store**: the binding of a store of `x` at the index `i` into the array `v`
    at the depth `d` is one instruction, which writes the array `regName d` and reads the array
    named by the operand of `v`. -/
theorem bindOps_store (nArgs d : Nat) {Γ : Ctxt jasminDialect} {w m : Nat}
    (v : Var Γ (.stackArr w m)) (i : Var Γ (.reg 64)) (x : Var Γ (.reg w))
    (aa : String → Nat → Option Nat) (ao : String → Option Nat) :
    ∃ ins, bindOps nArgs (⟨.stackStore w m, rfl, .cons v (.cons i (.cons x .nil))⟩ :
        Expr jasminDialect Γ (.stackArr w m)) d = [ins]
      ∧ wrArr ao ins = some (regName d)
      ∧ rdArr aa ins = [operandName (resolveVar d nArgs argName (fun _ => none) v)] := by
  have hgo : exprArgs.go d nArgs argName (fun _ => none)
      (HVector.cons v (HVector.cons i (HVector.cons x HVector.nil))) =
      [resolveVar d nArgs argName (fun _ => none) v, resolveVar d nArgs argName (fun _ => none) i,
        resolveVar d nArgs argName (fun _ => none) x] := rfl
  refine ⟨_, rfl, ?_⟩
  simp only [exprArgs, hgo]
  rw [resolveVar_reg d nArgs v, resolveVar_reg d nArgs i, resolveVar_reg d nArgs x]
  simp only [opToLinstrR, wrArr, rdArr, X86Backend.CoalesceComplete.armOf,
    X86Backend.CoalesceComplete.wrArrA, X86Backend.CoalesceComplete.rdArrA,
    LprogIsa.shadowCall?, X86Backend.ImageCoalesceCfg.arrShapeB, JasminLsemMem.storeStruct?,
    X86Backend.ImageStraightRoute.arrWrite, X86Backend.ImageStraightRoute.arrReads]
  simp
  rfl

/-- **The exported load**: the binding of a load at the index `i` from the array `a` at the
    depth `d` is one instruction, which writes no array and reads the array named by the
    operand of `a`. -/
theorem bindOps_load (nArgs d : Nat) {Γ : Ctxt jasminDialect} {w m : Nat}
    (a : Var Γ (.stackArr w m)) (i : Var Γ (.reg 64))
    (aa : String → Nat → Option Nat) (ao : String → Option Nat) :
    ∃ ins, bindOps nArgs (⟨.stackLoad w m, rfl, .cons a (.cons i .nil)⟩ :
        Expr jasminDialect Γ (.reg w)) d = [ins]
      ∧ wrArr ao ins = none
      ∧ rdArr aa ins = [operandName (resolveVar d nArgs argName (fun _ => none) a)] := by
  have hgo : exprArgs.go d nArgs argName (fun _ => none) (HVector.cons a (HVector.cons i HVector.nil)) =
      [resolveVar d nArgs argName (fun _ => none) a, resolveVar d nArgs argName (fun _ => none) i] :=
    rfl
  refine ⟨_, rfl, ?_⟩
  simp only [exprArgs, hgo]
  rw [resolveVar_reg d nArgs a, resolveVar_reg d nArgs i]
  simp only [opToLinstrR, wrArr, rdArr, X86Backend.CoalesceComplete.armOf,
    X86Backend.CoalesceComplete.wrArrA, X86Backend.CoalesceComplete.rdArrA,
    LprogIsa.shadowCall?, X86Backend.ImageCoalesceCfg.arrShapeB, JasminLsemMem.loadStruct?,
    X86Backend.ImageStraightRoute.arrWrite, X86Backend.ImageStraightRoute.arrReads]
  simp
  rfl

/-- **An instruction with a register tag reads and writes no array**, at array positions and
    result lengths that no symbol has. -/
theorem rdArr_wrArr_regTag (wire : LinstrR) (c : Option Nat)
    (aa : String → Nat → Option Nat) (ao : String → Option Nat)
    (haa : ∀ f j, aa f j = none) (hao : ∀ f, ao f = none) :
    rdArr aa (wire, .reg c) = [] ∧ wrArr ao (wire, .reg c) = none := by
  have hc : ∀ (j : Nat) (os : List LOperand) (f : String),
      X86Backend.CoalesceComplete.callArrRegs (aa f) j os = [] := by
    intro j os f
    induction os generalizing j with
    | nil => rfl
    | cons o os ih =>
        cases o <;> simp [X86Backend.CoalesceComplete.callArrRegs, haa, ih]
  unfold rdArr wrArr
  cases X86Backend.CoalesceComplete.armOf (wire, .reg c) <;>
    simp [X86Backend.CoalesceComplete.rdArrA, X86Backend.CoalesceComplete.wrArrA, hc, hao,
      X86Backend.ImageStraightRoute.arrWrite, X86Backend.ImageStraightRoute.arrReads]

/-- **The exported memory-free binding** at the depth `d` is one instruction, which reads and
    writes no array, at array positions and result lengths that no symbol has. -/
theorem bindOps_memFree (nArgs d : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (he : jMemFree e.op = true)
    (aa : String → Nat → Option Nat) (ao : String → Option Nat)
    (haa : ∀ f j, aa f j = none) (hao : ∀ f, ao f = none) :
    ∃ ins, bindOps nArgs e d = [ins] ∧ rdArr aa ins = [] ∧ wrArr ao ins = none := by
  obtain ⟨op, rfl, args⟩ := e
  refine ⟨_, rfl, ?_⟩
  cases op <;> simp only [jMemFree, Bool.false_eq_true] at he <;>
    exact rdArr_wrArr_regTag _ _ aa ao haa hao

/-! ## 7. The export of a program of loads, then one chain of stores -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete (ReadAt WrAt ConsumedAt)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation (regName_injective
  regName_ne_argName)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)

section ExportChain

variable {nArgs : Nat} {fn : String} {aa : String → Nat → Option Nat}
  {ao : String → Option Nat}

/-- The array name `x` is in scope at the depth `D` under `nArgs` arguments: an argument name
    `argName s` with `s < nArgs`, or a slot name `regName s` with `nArgs ≤ s < D`. -/
def InScope (nArgs D : Nat) (x : String) : Prop :=
  (∃ s, s < nArgs ∧ x = argName s) ∨ ∃ s, nArgs ≤ s ∧ s < D ∧ x = regName s

theorem InScope.mono {D D' : Nat} {x : String} (h : InScope nArgs D x) (hD : D ≤ D') :
    InScope nArgs D' x := by
  rcases h with h | ⟨s, h1, h2, h3⟩
  · exact .inl h
  · exact .inr ⟨s, h1, by omega, h3⟩

/-- The name of a variable of the context `Γ`, resolved at the depth `Γ.length`, is in scope
    there. -/
theorem inScope_resolveVar {Γ : Ctxt jasminDialect} {τ : JasminTy} (v : Var Γ τ) :
    InScope nArgs Γ.length (operandName (resolveVar Γ.length nArgs argName (fun _ => none) v)) := by
  have hv := FieldRoute.varIndex_lt_length v
  simp only [resolveVar]
  split
  · exact .inl ⟨_, by assumption, rfl⟩
  · exact .inr ⟨_, by omega, by omega, rfl⟩

/-- A weakened variable resolves, one binding deeper, to the same operand. -/
theorem resolveVar_there (D : Nat) {Γ : Ctxt jasminDialect} {τ σ : JasminTy} (v : Var Γ τ) :
    resolveVar (D + 1) nArgs argName (fun _ => none) (Var.there (Γ := Γ) (s := σ) v) =
      resolveVar D nArgs argName (fun _ => none) v := by
  have : D + 1 - 1 - varIndex (Var.there (Γ := Γ) (s := σ) v) = D - 1 - varIndex v := by
    simp only [varIndex]
    omega
  simp only [resolveVar, this]

theorem readAt_cons_zero {i : LinstrRM} {body : List LinstrRM} {obs : List String}
    {x : String} : ReadAt (i :: body) aa obs 0 x ↔ x ∈ rdArr aa i := by
  simp [ReadAt]

theorem readAt_cons_succ {i : LinstrRM} {body : List LinstrRM} {obs : List String}
    {j : Nat} {x : String} : ReadAt (i :: body) aa obs (j + 1) x ↔ ReadAt body aa obs j x := by
  simp [ReadAt]

theorem wrAt_cons_zero {i : LinstrRM} {body : List LinstrRM} {x : String} :
    WrAt (i :: body) ao 0 x ↔ wrArr ao i = some x := by
  simp [WrAt]

theorem wrAt_cons_succ {i : LinstrRM} {body : List LinstrRM} {w : Nat} {x : String} :
    WrAt (i :: body) ao (w + 1) x ↔ WrAt body ao w x := by
  simp [WrAt]

theorem consumedAt_cons_zero {i : LinstrRM} {body : List LinstrRM} {x : String} :
    ConsumedAt (i :: body) aa ao 0 x ↔ x ∈ rdArr aa i ∧ ∃ d, wrArr ao i = some d ∧ d ≠ x := by
  simp [ConsumedAt]

theorem consumedAt_cons_succ {i : LinstrRM} {body : List LinstrRM} {c : Nat} {x : String} :
    ConsumedAt (i :: body) aa ao (c + 1) x ↔ ConsumedAt body aa ao c x := by
  simp [ConsumedAt]

/-- The facts of the export of a chain of stores, or of loads followed by one: the names read
    at a position are in scope there, the name written at a position is its slot, and a name
    consumed at a position is not read after it. -/
def ExportFacts (D : Nat) (r : Exported) : Prop :=
  (∀ j x, ReadAt r.code aa (r.res.map operandName) j x → InScope nArgs (D + j) x)
    ∧ (∀ w x, WrAt r.code ao w x → x = regName (D + w))
    ∧ (∀ c x j, ConsumedAt r.code aa ao c x → ReadAt r.code aa (r.res.map operandName) j x →
      j ≤ c)

/-- **The facts of an export with one instruction in front**: when the instruction reads names
    in scope, writes only its slot, and a name it consumes is not read by the rest. -/
theorem exportFacts_cons {D : Nat} (ins : LinstrRM) (rk : Exported)
    (hk : ExportFacts (nArgs := nArgs) (aa := aa) (ao := ao) (D + 1) rk)
    (hread : ∀ x ∈ rdArr aa ins, InScope nArgs D x)
    (hwrite : ∀ x, wrArr ao ins = some x → x = regName D)
    (hdead : ∀ x, x ∈ rdArr aa ins → (∃ d, wrArr ao ins = some d ∧ d ≠ x) →
      ∀ j, ¬ ReadAt rk.code aa (rk.res.map operandName) j x) :
    ExportFacts (nArgs := nArgs) (aa := aa) (ao := ao) D { rk with code := ins :: rk.code } := by
  obtain ⟨hR, hW, hC⟩ := hk
  refine ⟨fun j x hx => ?_, fun w x hx => ?_, fun c x j hc hx => ?_⟩
  · cases j with
    | zero => exact (hread x (readAt_cons_zero.mp hx)).mono (by omega)
    | succ j => exact (hR j x (readAt_cons_succ.mp hx)).mono (by omega)
  · cases w with
    | zero => exact hwrite x (wrAt_cons_zero.mp hx)
    | succ w =>
        rw [hW w x (wrAt_cons_succ.mp hx)]
        congr 1
        omega
  · cases c with
    | zero =>
        obtain ⟨h1, h2⟩ := consumedAt_cons_zero.mp hc
        cases j with
        | zero => exact le_rfl
        | succ j => exact absurd (readAt_cons_succ.mp hx) (hdead x h1 h2 j)
    | succ c =>
        cases j with
        | zero => omega
        | succ j => exact Nat.succ_le_succ (hC c x j (consumedAt_cons_succ.mp hc)
            (readAt_cons_succ.mp hx))

/-- The name of the current version `v` of a chain at the depth `Γ.length`. -/
abbrev curName (nArgs : Nat) {Γ : Ctxt jasminDialect} {τ : JasminTy} (v : Var Γ τ) : String :=
  operandName (resolveVar Γ.length nArgs argName (fun _ => none) v)

/-- A name in scope at the depth `D` is no slot name from `D` on. -/
theorem InScope.ne_regName {D s : Nat} {x : String} (h : InScope nArgs D x) (hs : D ≤ s) :
    x ≠ regName s := by
  rintro rfl
  rcases h with ⟨s', -, h⟩ | ⟨s', -, h1, h⟩
  · exact regName_ne_argName s s' h
  · have := regName_injective h
    omega

/-- The newest variable, resolved at the depth of its context, is the slot name of its
    binding. -/
theorem curName_here {Γ : Ctxt jasminDialect} {τ : JasminTy} (hn : nArgs ≤ Γ.length) :
    curName nArgs (Var.here : Var (τ :: Γ) τ) = regName Γ.length := by
  have h : (τ :: Γ).length - 1 - varIndex (Var.here : Var (τ :: Γ) τ) = Γ.length := by
    simp [varIndex]
  simp only [curName, resolveVar, h]
  simp [show ¬ Γ.length < nArgs by omega, operandName]

/-- **The export of a chain tail**: it has the facts `ExportFacts`, and it reads only the
    current version and slot names from its depth on. -/
theorem chainTail_export (haa : ∀ f j, aa f j = none) (hao : ∀ f, ao f = none)
    {Γ : Ctxt jasminDialect} {w m : Nat} {ts : List JasminTy} {v : Var Γ (.stackArr w m)}
    {k : NFProg jasminDialect Γ ts} (h : ChainTail v k) (hn : nArgs ≤ Γ.length) {n : Nat}
    {r : Exported} (hr : exportR nArgs fn k Γ.length n = some r) :
    ExportFacts (nArgs := nArgs) (aa := aa) (ao := ao) Γ.length r ∧
      ∀ j x, ReadAt r.code aa (r.res.map operandName) j x →
        x = curName nArgs v ∨ ∃ s, Γ.length ≤ s ∧ x = regName s := by
  induction h generalizing n r with
  | @free Γ w m t ts v e k he hk ih =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      obtain ⟨ins, hb, hrd, hwr⟩ := bindOps_memFree nArgs Γ.length e he aa ao haa hao
      obtain ⟨hF, hC⟩ := ih (by simp only [List.length_cons]; omega) hk'
      have hcode : (Exported.prepend (bindOps nArgs e Γ.length) rk) =
          { rk with code := ins :: rk.code } := by
        simp [Exported.prepend, hb]
      rw [hcode]
      refine ⟨exportFacts_cons ins rk hF (by simp [hrd]) (by simp [hwr]) (by simp [hrd]),
        fun j x hx => ?_⟩
      cases j with
      | zero => simp [readAt_cons_zero, hrd] at hx
      | succ j =>
          rcases hC j x (readAt_cons_succ.mp hx) with h | ⟨s, hs, rfl⟩
          · left
            rw [h, curName, curName, List.length_cons, resolveVar_there]
          · exact .inr ⟨s, by simp only [List.length_cons] at hs; omega, rfl⟩
  | @store Γ w m ts v i x k hk ih =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      obtain ⟨ins, hb, hwr, hrd⟩ := bindOps_store nArgs Γ.length v i x aa ao
      obtain ⟨hF, hC⟩ := ih (by simp only [List.length_cons]; omega) hk'
      rw [curName_here hn] at hC
      have hcode : (Exported.prepend (bindOps nArgs (⟨.stackStore w m, rfl,
          .cons v (.cons i (.cons x .nil))⟩ : Expr jasminDialect Γ (.stackArr w m)) Γ.length) rk) =
          { rk with code := ins :: rk.code } := by
        simp [Exported.prepend, hb]
      rw [hcode]
      have hv := inScope_resolveVar (nArgs := nArgs) v
      refine ⟨exportFacts_cons ins rk hF ?_ (by simp [hwr]) ?_, fun j y hy => ?_⟩
      · intro y hy
        rw [hrd, List.mem_singleton] at hy
        exact hy ▸ hv
      · intro y hy _ j hj
        rw [hrd, List.mem_singleton] at hy
        subst hy
        rcases hC j _ hj with h | ⟨s, hs, h⟩
        · exact hv.ne_regName le_rfl h
        · exact hv.ne_regName (by simp only [List.length_cons] at hs; omega) h
      · cases j with
        | zero =>
            rw [readAt_cons_zero, hrd, List.mem_singleton] at hy
            exact .inl hy
        | succ j =>
            rcases hC j y (readAt_cons_succ.mp hy) with h | ⟨s, hs, h⟩
            · exact .inr ⟨_, le_rfl, h⟩
            · exact .inr ⟨s, by simp only [List.length_cons] at hs; omega, h⟩
  | @ret Γ w m v =>
      simp only [exportR, Option.some.injEq] at hr
      subst hr
      have hv := inScope_resolveVar (nArgs := nArgs) v
      have hobs : ∀ j y, ReadAt [] aa [curName nArgs v] j y → j = 0 ∧ y = curName nArgs v := by
        intro j y hy
        rcases hy with ⟨_, h, -⟩ | ⟨h1, h2⟩
        · simp at h
        · exact ⟨h1, List.mem_singleton.mp h2⟩
      refine ⟨⟨fun j y hy => ?_, fun w y hy => ?_, fun c y j hc _ => ?_⟩, fun j y hy => ?_⟩
      · obtain ⟨rfl, rfl⟩ := hobs j y hy
        exact hv
      · obtain ⟨_, h, -⟩ := hy
        simp at h
      · obtain ⟨_, _, h, -⟩ := hc
        simp at h
      · exact .inl (hobs j y hy).2

/-- The names of the returned operands of variables of `Γ`, resolved at the depth
    `Γ.length`, are in scope there. -/
theorem inScope_exprArgsHV {Γ : Ctxt jasminDialect} :
    ∀ {tys : List JasminTy} (vs : HVector (fun t => Var Γ t) tys),
      ∀ y ∈ (exprArgsHV Γ.length nArgs argName (fun _ => none) vs).map operandName,
        InScope nArgs Γ.length y
  | [], .nil => by simp [exprArgsHV]
  | _ :: _, .cons v vs => by
      intro y hy
      change y ∈ operandName (resolveVar Γ.length nArgs argName (fun _ => none) v) ::
        (exprArgsHV Γ.length nArgs argName (fun _ => none) vs).map operandName at hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact inScope_resolveVar v
      · exact inScope_exprArgsHV vs y hy

/-- **The export of a program of loads, then one chain of stores** has the facts
    `ExportFacts`. -/
theorem loadsChain_export (haa : ∀ f j, aa f j = none) (hao : ∀ f, ao f = none)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    (h : LoadsChain p) (hn : nArgs ≤ Γ.length) {n : Nat} {r : Exported}
    (hr : exportR nArgs fn p Γ.length n = some r) :
    ExportFacts (nArgs := nArgs) (aa := aa) (ao := ao) Γ.length r := by
  induction h generalizing n r with
  | @free Γ t ts e k he hk ih =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      obtain ⟨ins, hb, hrd, hwr⟩ := bindOps_memFree nArgs Γ.length e he aa ao haa hao
      have hcode : (Exported.prepend (bindOps nArgs e Γ.length) rk) =
          { rk with code := ins :: rk.code } := by
        simp [Exported.prepend, hb]
      rw [hcode]
      exact exportFacts_cons ins rk (ih (by simp only [List.length_cons]; omega) hk')
        (by simp [hrd]) (by simp [hwr]) (by simp [hrd])
  | @load Γ w m ts a i k hk ih =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      obtain ⟨ins, hb, hwr, hrd⟩ := bindOps_load nArgs Γ.length a i aa ao
      have hcode : (Exported.prepend (bindOps nArgs (⟨.stackLoad w m, rfl,
          .cons a (.cons i .nil)⟩ : Expr jasminDialect Γ (.reg w)) Γ.length) rk) =
          { rk with code := ins :: rk.code } := by
        simp [Exported.prepend, hb]
      rw [hcode]
      refine exportFacts_cons ins rk (ih (by simp only [List.length_cons]; omega) hk') ?_
        (by simp [hwr]) (by simp [hwr])
      intro y hy
      rw [hrd, List.mem_singleton] at hy
      exact hy ▸ inScope_resolveVar a
  | @store Γ w m ts v i x k hk =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      obtain ⟨ins, hb, hwr, hrd⟩ := bindOps_store nArgs Γ.length v i x aa ao
      obtain ⟨hF, hC⟩ := chainTail_export haa hao hk (by simp only [List.length_cons]; omega) hk'
      rw [curName_here hn] at hC
      have hcode : (Exported.prepend (bindOps nArgs (⟨.stackStore w m, rfl,
          .cons v (.cons i (.cons x .nil))⟩ : Expr jasminDialect Γ (.stackArr w m)) Γ.length) rk) =
          { rk with code := ins :: rk.code } := by
        simp [Exported.prepend, hb]
      rw [hcode]
      have hv := inScope_resolveVar (nArgs := nArgs) v
      refine exportFacts_cons ins rk hF ?_ (by simp [hwr]) ?_
      · intro y hy
        rw [hrd, List.mem_singleton] at hy
        exact hy ▸ hv
      · intro y hy _ j hj
        rw [hrd, List.mem_singleton] at hy
        subst hy
        rcases hC j _ hj with h | ⟨s, hs, h⟩
        · exact hv.ne_regName le_rfl h
        · exact hv.ne_regName (by simp only [List.length_cons] at hs; omega) h
  | @ret Γ ts vs =>
      simp only [exportR, Option.some.injEq] at hr
      subst hr
      refine ⟨fun j y hy => ?_, fun w y hy => ?_, fun c y j hc _ => ?_⟩
      · rcases hy with ⟨_, h, -⟩ | ⟨rfl, h⟩
        · simp at h
        · exact inScope_exprArgsHV vs y h
      · obtain ⟨_, h, -⟩ := hy
        simp at h
      · obtain ⟨_, _, h, -⟩ := hc
        simp at h

/-- **Reads follow writes and consumed names are dead in the export of a program of loads,
    then one chain of stores**: the first two conjuncts of `ChainShape` on the exported code,
    with the names of the returned operands read after it. -/
theorem loadsChain_export_chainShape₁₂ (haa : ∀ f j, aa f j = none) (hao : ∀ f, ao f = none)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    (h : LoadsChain p) (hn : nArgs ≤ Γ.length) {n : Nat} {r : Exported}
    (hr : exportR nArgs fn p Γ.length n = some r) :
    (∀ j x w, ReadAt r.code aa (r.res.map operandName) j x → WrAt r.code ao w x → w < j)
      ∧ ∀ c x j, ConsumedAt r.code aa ao c x → ReadAt r.code aa (r.res.map operandName) j x →
        j ≤ c := by
  obtain ⟨hR, hW, hC⟩ := loadsChain_export haa hao h hn hr
  refine ⟨fun j x w hx hw => ?_, hC⟩
  have h1 := hW w x hw
  by_contra hlt
  exact (hR j x hx).ne_regName (by omega) h1

end ExportChain

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
