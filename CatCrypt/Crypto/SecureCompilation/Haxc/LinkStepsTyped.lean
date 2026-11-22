/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.ModuleCalls
public import CatCrypt.Crypto.SecureCompilation.Haxc.LinkedKernel
public import CatCrypt.Crypto.SecureCompilation.Haxc.AccessBytes
-- the body of `String.toUpper`, which `Init.Data.String.Modify` does not expose
import all Init.Data.String.Modify

/-!
# Linked functions against source bodies at typed arguments

A linked function agrees with the function of a module that it replaces when its meaning
returns the values of the reference meaning of that function on the argument lists of its
parameter types (`argsTypedB`, `LinkAgrees`). No agreement is asked on other lists, on which
the meaning of a linked kernel is undefined when their kinds differ (`LinkedKernel.sem_kinds`)
and on which the reference reading of a body may return a value, since `paramsEnv` binds
positionally and reads no type.

The compiled code calls a linked function only at words and word arrays: a declared procedure
(`linkedDecls`) is implemented on argument values related to machine words
(`ExtDecl.ImplementedBy`), and these are values of the parameter types (`argsTypedB_encAll`).
The compiler theorem therefore holds at every module whose linked functions answer the
argument lists of other types by any table `X` (`widen X m`, `haxc_correct_widen`). A source
run of a module before linking is a run of such a module after linking, at the table of the
values of its own functions (`refAnswers`). So `compileModule_correct` holds from the source
runs `haxRuns` of the module before linking, with `LinkAgrees` as linking hypothesis.

On a program without a call of a linked function, the compiler theorems of this module bound
the memory accesses of the decoded bytes by the memory of the layout (`HaltsIn`), which is
`compileR_correct_linked_access` at an entry.

## Main definitions

* `argsTypedB`: an argument list of the types of a list of parameters.
* `LinkAgrees`: the linking hypothesis.
* `widenFn`, `widen`: linked functions answered by a table at arguments of other types.
* `refAnswers`: the values of the reference tables of a module at all depths.

## Main results

* `argsTypedB_kinds`: typed arguments have the kinds of the parameters.
* `runs_foldl_linkFn`, `haxRuns_foldl_linkFn`: a source run of a module is a run of the
  linked module widened by `refAnswers`.
* `compileR_correct_linked_access`: the compiler theorem at an entry with linked functions,
  with the accesses of the decoded program in the case without calls.
* `haxc_correct_widen`: the compiler theorem from a run of a widened module.
* `haxc_correct_linked_source`, `compileModule_correct`: the compiler theorems from a source
  run of the module before linking.
* `Witness`: an addition of two words with code, a linked kernel that satisfies `LinkAgrees`
  with the body it replaces, and the source runs of a module that calls it.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.LinkStepsTyped

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect (NfTy)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Lprog)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts HaltsC)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (HaltsO)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLink (shiftProg)
open CatCrypt.Crypto.SecureCompilation.Haxc.AccessBytes (HaltsIn compileR_haltsIn)
open CatCrypt.Crypto.SecureCompilation.SepLogic.X86 (wordsLocs frameWords regionWords)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall (tabOracle LinkedKernel)
open CatCrypt.Crypto.SecureCompilation.Haxc.ModuleCalls
  (foldl_linkFn callOrder CalleePlan compileCallee compileModule SameData compileModule_eq)
open CatCrypt.Crypto.Hax
  (HaxModule LinkedFn ModFn refBi refBi_of_find_none refBi_succ_refSem linkBi
    linkBi_of_find_none linkBi_of_find_some denoteSpine_val_of_le hax64WExit)
open CatCrypt.Crypto.Hax.ImpToNF (dec enc encAll tableOf)
open CatCrypt.Crypto.Hax.NFToCat (VRel VRelL ExtAgree catTy)
open _root_.Hax (Value Builtins)

/-! ## 1. Arguments of the parameter types -/

/-- **An argument list of the types of the parameters `ps`**: as many values as parameters,
    and each value decodes at the type of its parameter. -/
def argsTypedB : List (String × NfTy) → List Value → Bool
  | [], [] => true
  | p :: ps, v :: vs => (dec p.2 v).isSome && argsTypedB ps vs
  | _, _ => false

/-- The encoding of a `64`-bit word list decodes to the list. -/
theorem mapM_dec_enc_word : ∀ xs : List (BitVec 64),
    (xs.map (enc (.word 64))).mapM (dec (.word 64)) = some xs
  | [] => by simp
  | x :: xs => by
      have hx : dec (.word 64) (enc (.word 64) x) = some x :=
        CatCrypt.Crypto.Hax.dec_wordVal x
      simp [hx, mapM_dec_enc_word xs]

/-- A source argument related to a machine value, at a type of a signature variant of the
    parameter type `t`, decodes at `t`. -/
theorem dec_enc_of_vrel {t a : NfTy} (ht : linkResOk t = true)
    (ha : a ∈ if CatCrypt.Crypto.Hax.ImpToNF.hax64NFWordTy t then [NfTy.word 64, NfTy.int]
      else [t])
    {x : a.denote} {y : (catTy a).denote} (h : VRel a x y) :
    (dec t (enc a x)).isSome = true := by
  rcases linkResOk_iff.mp ht with rfl | ⟨n, rfl⟩
  · obtain rfl | rfl : a = .word 64 ∨ a = .int := by
      simpa [CatCrypt.Crypto.Hax.ImpToNF.hax64NFWordTy] using ha
    · simp [enc, dec, x.isLt]
    · change x = (y.toNat : Int) at h
      subst h
      simp [enc, dec, y.isLt]
  · obtain rfl : a = .arr n (.word 64) := by
      simpa [CatCrypt.Crypto.Hax.ImpToNF.hax64NFWordTy] using ha
    have h' := mapM_dec_enc_word (List.ofFn x)
    simp [List.map_ofFn, Function.comp_def] at h'
    grind [enc, dec]

/-- **The arguments of a declared procedure at machine words are of the parameter types.** -/
theorem argsTypedB_encAll : ∀ {ps : List (String × NfTy)} {as : List NfTy},
    (∀ p ∈ ps, linkResOk p.2 = true) → as ∈ sigVariants (ps.map (·.2)) →
    ∀ (xs : Ctxt.Valuation (d := NFDialect.nfDialect) as)
      (ws : Ctxt.Valuation (d := CatCryptDialect.catCryptDialect) (as.map catTy)),
      VRelL as xs ws → argsTypedB ps (encAll as xs) = true
  | [], as, _, ha => by
      obtain rfl : as = [] := by simpa [sigVariants] using ha
      rintro ⟨⟩ _ _
      rfl
  | p :: ps, as, hp, ha => by
      simp only [List.map_cons, sigVariants, List.mem_flatMap, List.mem_map] at ha
      obtain ⟨a, ha, as', has, rfl⟩ := ha
      rintro (_ | ⟨x, xs⟩) (_ | ⟨w, ws⟩) ⟨hv, hr⟩
      simp only [encAll, argsTypedB, Bool.and_eq_true]
      exact ⟨dec_enc_of_vrel (hp p List.mem_cons_self) ha hv,
        argsTypedB_encAll (fun q hq => hp q (List.mem_cons_of_mem _ hq)) has xs ws hr⟩

/-- A value of a type of words or word arrays has the kind of the type. -/
theorem valKind_of_dec {t : NfTy} (ht : linkResOk t = true) {v : Value}
    (h : (dec t v).isSome = true) :
    valKind v = kindOfTy (CryptoToJasminCom.mapTy (catTy t)) := by
  rcases linkResOk_iff.mp ht with rfl | ⟨n, rfl⟩
  · cases v <;> simp_all [dec, valKind]
    rfl
  · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨vs, rfl, hl⟩ := dec_arr_eq_some hy
    simp [valKind, hl]
    rfl

/-- **Typed arguments have the kinds of the parameters** at a signature of words and word
    arrays (`linkSigOk`, which `compileA` checks): the argument lists of `LinkAgrees` are
    among those at which `LinkedKernel.sem_kinds` allows a value. -/
theorem argsTypedB_kinds {l : LinkedFn} (hl : linkSigOk l = true) {vals : List Value}
    (h : argsTypedB l.params vals = true) : vals.map valKind = linkedKinds l := by
  simp only [linkSigOk, Bool.and_eq_true, List.all_eq_true] at hl
  have key : ∀ (ps : List (String × NfTy)) (vs : List Value),
      (∀ p ∈ ps, linkResOk p.2 = true) → argsTypedB ps vs = true →
      vs.map valKind = ps.map fun p => kindOfTy (CryptoToJasminCom.mapTy (catTy p.2)) := by
    intro ps
    induction ps with
    | nil => intro vs _ hv; cases vs <;> simp_all [argsTypedB]
    | cons p ps ih => intro vs hp hv; cases vs <;> grind [argsTypedB, valKind_of_dec]
  exact key _ _ hl.1 h

/-! ## 2. The linking hypothesis -/

/-- **The linked functions `ls` agree with the functions of `m` they replace, at typed
    arguments**: the module has a function `f` of the name and result type of each `l`, and
    on an argument list of the parameter types of `l` the meaning of `l` returns every value
    that the reference meaning of `f` returns at the reference tables of `m`. -/
def LinkAgrees (bi : Builtins) (m : HaxModule) (ls : List LinkedFn) : Prop :=
  ∀ l ∈ ls, ∃ f, m.fns.find? (·.name == l.name) = some f ∧ f.res = l.res ∧
    ∀ fuelC n vals v, argsTypedB l.params vals = true →
      f.refSem (refBi m.fns (m.linkTable bi) fuelC n) fuelC vals = some v → l.sem vals = some v

/-! ## 3. Linked functions answered by a table at arguments of other types -/

/-- **A linked function widened by the table `X`**: the meaning of `l` at arguments of its
    parameter types, and at other arguments the value of `X` at the name of `l` when it
    decodes at the result type. It is the source meaning of a call in the compiler theorem;
    the code of `l` is described by `l`, and the widened record has no return state. -/
def widenFn (X : Builtins) (l : LinkedFn) : LinkedFn :=
  { l with
    sem := fun vals =>
      if argsTypedB l.params vals then l.sem vals
      else (X l.name vals).filter fun v => (dec l.res v).isSome
    sem_res := fun vals v h => by grind [l.sem_res, Option.filter_eq_some_iff]
    post := fun _ _ => False
    post_sem := fun _ _ _ _ h => h.elim }

/-- **A module with its linked functions widened by the table `X`.** -/
def widen (X : Builtins) (m : HaxModule) : HaxModule :=
  { m with linked := m.linked.map (widenFn X) }

/-- Widening keeps the callees of the linked functions. -/
theorem linkedFns_widen (X : Builtins) (m : HaxModule) :
    (widen X m).linkedFns = m.linkedFns := by
  simp [HaxModule.linkedFns, widen, widenFn, LinkedFn.callee, Function.comp_def]

/-- Widening keeps `narrowOk`. -/
theorem narrowOk_widen (X : Builtins) (m : HaxModule) (σ : AbiLayout) :
    narrowOk (widen X m) σ = narrowOk m σ := by
  simp [narrowOk, widen, widenFn, Function.comp_def]

/-- Widening commutes with the stages before the front. -/
theorem pairStage_widen (X : Builtins) (m : HaxModule) (σ : AbiLayout) :
    pairStage (widen X m) σ = (widen X (pairStage m σ).1, (pairStage m σ).2) := by
  have hn : narrowStage (widen X m) σ = (widen X (narrowStage m σ).1, (narrowStage m σ).2) := by
    unfold narrowStage
    rw [narrowOk_widen]
    split <;> rfl
  have hp : ∀ n τ, pairTailOf (widen X n) τ = pairTailOf n τ := fun n τ => by
    simp [pairTailOf, indexFreeB, widen, widenFn, Function.comp_def]
  simp only [pairStage, hn, pairTailStage, hp]
  split <;> rfl

/-- Widening keeps the translation of the front. -/
theorem haxToNF_widen (X : Builtins) (m : HaxModule) (σ : AbiLayout) :
    haxToNF σ (widen X m) = haxToNF σ m := by
  simp only [haxToNF, HaxModule.inline?, HaxModule.linkSig, linkedFns_widen]
  have h₁ : (widen X m).linked.all (fun l => linkNameOk l.name)
      = m.linked.all (fun l => linkNameOk l.name) := List.all_map
  have h₂ : (widen X m).linked.all linkSigOk = m.linked.all linkSigOk := List.all_map
  rw [h₁, h₂]
  rfl

/-- The first function of a name among widened functions is the first one, widened. -/
theorem find?_map_widenFn (X : Builtins) (ls : List LinkedFn) (g : String) :
    (ls.map (widenFn X)).find? (·.name == g) = (ls.find? (·.name == g)).map (widenFn X) := by
  rw [List.find?_map]
  rfl

/-- Widening keeps the declared procedures. -/
theorem linkedDecls_widen (X : Builtins) (m : HaxModule) (bi : Builtins) :
    linkedDecls (widen X m) bi = linkedDecls m bi :=
  ModuleCalls.linkedDecls_eq_of_callees (by
    simp [widen, widenFn, LinkedFn.callee, Function.comp_def]) bi

/-- **The hax entry at the runs of widened modules**: the sources are the modules whose
    linked functions have distinct names, the translation, the declared procedures and the
    linked functions are those of `haxEntry`, and the runs and the table are those of the
    module widened by `X`. The environment of the linked functions alone implements the
    declared procedures at that table, since their arguments at machine words are of the
    parameter types (`argsTypedB_encAll`). -/
def widenEntry (X : Builtins) : NFEntry where
  Src := { m : HaxModule // (m.linked.map (·.name)).Nodup }
  Runs σ s sa v := haxRunsW σ (widen X s.1) sa v
  names := nfAbiNames
  toNF σ s := haxToNF σ s.1
  bi s _ := (widen X s.1).linkTable hax64WExit
  env s _ := tableEnv ((widen X s.1).linkTable hax64WExit)
  decls s := linkedDecls s.1 hax64WExit
  sound σ s q hq sa v hsep hrun := by
    obtain ⟨k, D, e, V, y, hD, h⟩ :=
      haxEntry.sound σ (widen X s.1) q ((haxToNF_widen X s.1 σ).trans hq) sa v hsep hrun
    refine ⟨k, D, e, V, y, fun f as r => (hD f as r).trans ?_, h⟩
    exact congrArg (fun D => CatCrypt.Crypto.Hax.NFToCat.declared D f as r)
      (linkedDecls_widen X s.1 hax64WExit)
  fieldCalls σ s q hq :=
    haxEntry.fieldCalls σ (widen X s.1) q ((haxToNF_widen X s.1 σ).trans hq)
  fieldCallsWide σ s q hq :=
    haxEntry.fieldCallsWide σ (widen X s.1) q ((haxToNF_widen X s.1 σ).trans hq)
  linked s := s.1.linked
  linkedAgree σ s q hq k := by
    rw [linkedDecls_map_atTable]
    intro d hd
    obtain ⟨l, hl, hd⟩ := List.mem_flatMap.mp hd
    obtain ⟨as, has, rfl⟩ := List.mem_map.mp hd
    obtain ⟨hl, hok⟩ := List.mem_filter.mp hl
    obtain ⟨has, hwa⟩ := List.mem_filter.mp has
    have hr : linkResOk l.res = true := (Bool.and_eq_true_iff.mp hok).2
    have hsig : linkSigOk l = true := (haxToNF_eq_some_sig hq).1 l hl
    have hf : s.1.linked.find? (·.name == l.name) = some l := by
      obtain ⟨l', hl'⟩ : ∃ l', s.1.linked.find? (·.name == l.name) = some l' :=
        Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨l, hl, beq_self_eq_true _⟩)
      rw [hl', List.inj_on_of_nodup_map s.2 (List.mem_of_find?_eq_some hl') hl
        (by simpa using List.find?_some hl')]
    have hf' : (s.1.linked.map (widenFn X)).find? (·.name == l.name) = some (widenFn X l) := by
      rw [find?_map_widenFn, hf]
      rfl
    refine ⟨fun _ => rfl, fun xs ws y hws hy => ?_⟩
    have ht : argsTypedB l.params (encAll as xs) = true :=
      argsTypedB_encAll (fun p hp => List.all_eq_true.mp (Bool.and_eq_true_iff.mp hsig).1 p hp)
        has xs ws hws
    refine implementedBy_tableEnv (linkBi s.1.linked fun _ _ => none) l.name as l.res hr
      (List.all_eq_true.mp hwa) xs ws y hws ?_
    simpa [tableOf, HaxModule.linkTable, widen, linkBi_of_find_some _ _ hf,
      linkBi_of_find_some _ _ hf', widenFn, ht] using hy

/-- **The compiler theorem at an entry with linked functions, with the accesses of the
    emitted bytes.** The hypotheses are those of `NFEntry.compileR_correct_linked`. In the
    case of a program without `call`, the run of the decoded program accesses only
    `layoutMem σ sa` (`AccessBytes.HaltsIn`, by `AccessBytes.compileR_haltsIn`); a program
    with a `call` is the case of `NFEntry.call_halts_multi`. -/
theorem compileR_correct_linked_access (E : NFEntry) (s : E.Src) (σ : AbiLayout)
    (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : E.compileR s σ fname ((E.linked s).filterMap LinkedFn.calleeData) = some (P, bytes))
    (sa : AState) (hsep : σ.Regions sa) (v : Value) (hrun : E.Runs σ s sa v)
    (hnd : ((E.linked s).map (·.name)).Nodup) (hk : ∀ l ∈ E.linked s, LinkedKernel l) :
    ∃ prog, decodeLprog bytes = some prog ∧
      ((∃ sa', Halts aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' v
        ∧ sa'.regs "%rsp" = sa.regs "%rsp"
        ∧ (∀ x, SepLogic.X86.Loc.mem x
            ∉ wordsLocs (frameWords (sa.regs "%rsp") σ.frameLo σ.frameHi) →
          (∀ p ∈ σ.regions,
            SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
          sa'.mem x = sa.mem x)
        ∧ HaltsIn (layoutMem σ sa) prog 0 sa sa')
      ∨ ∃ cs : List CalleeData, cs.Sublist ((E.linked s).filterMap LinkedFn.calleeData)
          ∧ cs ≠ [] ∧ (cs.map (·.name)).Nodup
          ∧ ∃ (pc Q : List RInstr) (k : String → Nat) (q : String → List RInstr),
            (∀ c ∈ cs, decodeLprog c.bytes = some (q c.name))
            ∧ decodeLprog (cs.flatMap (·.bytes)) = some Q
            ∧ (∀ c ∈ cs, ∃ A B, Q = A ++ shiftProg A.length (q c.name) ++ B
              ∧ A.length = k c.name)
            ∧ prog = pc ++ shiftProg pc.length Q
            ∧ (∃ sa', HaltsC aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' v)
            ∧ ∃ sa', HaltsO aMachine (tabOracle cs pc.length k q) pc 0 sa sa'
              ∧ σ.ResultOf sa sa' v) := by
  rw [NFEntry.compileR_eq_bind] at hc
  obtain ⟨q0, hq0, hc⟩ := Option.bind_eq_some_iff.mp hc
  obtain ⟨p, hp, hc⟩ := Option.bind_eq_some_iff.mp hc
  cases hcf : p.callFree with
  | true =>
      rw [compileRegion_of_callFree _ _ hcf] at hc
      have hc' : E.compileR s σ fname = some (P, bytes) := by
        simp only [NFEntry.compileR, NFEntry.chainNF, hq0, Option.bind_some, hp, Option.map_some]
        exact hc
      obtain ⟨prog, sa', hd, hh, hR, hsp, hkeep, -⟩ :=
        E.compileR_correct s σ fname P bytes hc' sa hsep v hrun
      obtain ⟨prog', sa'', hd', hA⟩ := compileR_haltsIn E s σ fname P bytes hc' sa hsep v hrun
      obtain rfl := Option.some.inj (hd.symm.trans hd')
      exact ⟨prog, hd, .inl ⟨sa', hh, hR, hsp, hkeep, hA.of_halts hh⟩⟩
  | false =>
      obtain ⟨cs, hsub, hne, hndc, pc, Q, k, q, hq, hQ, hB, hdec, hC, hO⟩ :=
        E.call_halts_multi hnd hk hq0 hp hcf hc sa hsep v hrun
      exact ⟨_, hdec, .inr ⟨cs, hsub, hne, hndc, pc, Q, k, q, hq, hQ, hB, rfl, hC, hO⟩⟩

/-- **The compiler theorem from a run of a widened module.** The hypotheses are those of
    `haxc_correct_auto_access`, with the run taken in the module whose linked functions answer
    the arguments of other types by a table `X`. The conclusion is that of
    `haxc_correct_auto_access`: in the case without calls, every memory access of the run of
    the decoded program lies in `layoutMem σ sa`. -/
theorem haxc_correct_widen (X : Builtins) (m : HaxModule) (σ : AbiLayout) (fname : String)
    (P : Lprog) (bytes : List (BitVec 8)) (hc : compileA m σ fname = some (P, bytes))
    (sa : AState) (hsep : σ.Regions sa) (v : Value) (hrun : haxRuns σ (widen X m) sa v)
    (hnd : (m.linked.map (·.name)).Nodup) (hk : ∀ l ∈ m.linked, LinkedKernel l) :
    ∃ prog, decodeLprog bytes = some prog ∧
      ((∃ sa', Halts aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' v
        ∧ sa'.regs "%rsp" = sa.regs "%rsp"
        ∧ (∀ x, SepLogic.X86.Loc.mem x
            ∉ wordsLocs (frameWords (sa.regs "%rsp") σ.frameLo σ.frameHi) →
          (∀ p ∈ σ.regions,
            SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
          sa'.mem x = sa.mem x)
        ∧ HaltsIn (layoutMem σ sa) prog 0 sa sa')
      ∨ ∃ cs : List CalleeData, cs.Sublist (m.linked.filterMap LinkedFn.calleeData)
          ∧ cs ≠ [] ∧ (cs.map (·.name)).Nodup
          ∧ ∃ (pc Q : List RInstr) (k : String → Nat) (q : String → List RInstr),
            (∀ c ∈ cs, decodeLprog c.bytes = some (q c.name))
            ∧ decodeLprog (cs.flatMap (·.bytes)) = some Q
            ∧ (∀ c ∈ cs, ∃ A B, Q = A ++ shiftProg A.length (q c.name) ++ B
              ∧ A.length = k c.name)
            ∧ prog = pc ++ shiftProg pc.length Q
            ∧ (∃ sa', HaltsC aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' v)
            ∧ ∃ sa', HaltsO aMachine (tabOracle cs pc.length k q) pc 0 sa sa'
              ∧ σ.ResultOf sa sa' v) := by
  obtain ⟨x, hrun', hback⟩ := haxRuns_pairStage hrun
  rw [pairStage_widen] at hrun' hback
  have hl : (pairStage m σ).1.linked = m.linked := pairStage_linked m σ
  obtain ⟨hlo, hhi, hrg⟩ := pairStage_frame m σ
  have hnd' : ((pairStage m σ).1.linked.map (·.name)).Nodup := by rw [hl]; exact hnd
  have hk' : ∀ l ∈ (pairStage m σ).1.linked, LinkedKernel l := by rw [hl]; exact hk
  obtain ⟨prog, hd, h⟩ := compileR_correct_linked_access (widenEntry X)
    ⟨(pairStage m σ).1, hnd'⟩ _ fname P bytes hc sa
    ((pairStage_regions m σ sa).2 hsep) x hrun' hnd' hk'
  refine ⟨prog, hd, ?_⟩
  rcases h with ⟨sa', hh, hR, hsp, hkeep, hA⟩
    | ⟨cs, hsub, hne, hndc, pc, Q, k, q, hq, hQ, hB, hp, ⟨sa', hC, hR⟩, sa'', hO, hR'⟩
  · rw [hlo, hhi, hrg] at hkeep
    rw [layoutMem_pairStage] at hA
    exact .inl ⟨sa', hh, hback _ hR, hsp, hkeep, hA⟩
  · exact .inr ⟨cs, (by rw [← hl]; exact hsub), hne, hndc, pc, Q, k, q, hq, hQ, hB, hp,
      ⟨sa', hC, hback _ hR⟩, sa'', hO, hback _ hR'⟩

/-! ## 4. A run of a module is a run of the widened linked module -/

/-- The reference tables of a module grow with the depth. -/
theorem refBi_mono_depth (fs : List ModFn) (bi : Builtins) (fuel : Nat) {n k : Nat}
    (hnk : n ≤ k) : ∀ g vals v, refBi fs bi fuel n g vals = some v →
      refBi fs bi fuel k g vals = some v := by
  have step : ∀ j g vals v, refBi fs bi fuel j g vals = some v →
      refBi fs bi fuel (j + 1) g vals = some v := by
    intro j
    induction j with
    | zero =>
        intro g vals v h
        cases hg : fs.find? (·.name == g) with
        | none => grind [refBi_of_find_none]
        | some f => simp [refBi, hg] at h
    | succ j ih =>
        intro g vals v h
        cases hg : fs.find? (·.name == g) with
        | none => grind [refBi_of_find_none]
        | some f =>
            rw [refBi_succ_refSem _ _ _ _ hg] at h ⊢
            exact f.refSem_le ih fuel vals v h
  induction hnk with
  | refl => exact fun _ _ _ h => h
  | step _ ih => exact fun g vals v h => step _ g vals v (ih g vals v h)

open Classical in
/-- **The values of the reference tables of a module at all depths**, at the fuel `fuelC` of
    the callees: the table that widens the linked functions in the simulation of a run of
    the module before linking. -/
noncomputable def refAnswers (m : HaxModule) (bi : Builtins) (fuelC : Nat) : Builtins :=
  fun g vals =>
    if h : ∃ v n, refBi m.fns (m.linkTable bi) fuelC n g vals = some v then some h.choose
    else none

/-- A value of the reference table at some depth is the value of `refAnswers`. -/
theorem refAnswers_eq {m : HaxModule} {bi : Builtins} {fuelC n : Nat} {g : String}
    {vals : List Value} {v : Value}
    (h : refBi m.fns (m.linkTable bi) fuelC n g vals = some v) :
    refAnswers m bi fuelC g vals = some v := by
  have hex : ∃ v n, refBi m.fns (m.linkTable bi) fuelC n g vals = some v := ⟨v, n, h⟩
  obtain ⟨k, hk⟩ := hex.choose_spec
  have h₁ := refBi_mono_depth m.fns _ fuelC (Nat.le_max_left n k) _ _ _ h
  have h₂ := refBi_mono_depth m.fns _ fuelC (Nat.le_max_right n k) _ _ _ hk
  rw [refAnswers, dite_eq_left_of_eq_true (eq_true hex), ← h₁, h₂]

/-- The first function of a name among the functions whose names pass `p`. -/
theorem find?_filter_names (fs : List ModFn) (p : String → Bool) (g : String) :
    (fs.filter fun f => p f.name).find? (·.name == g) =
      if p g then fs.find? (·.name == g) else none := by
  induction fs with
  | nil => simp
  | cons f fs ih => grind

/-- **The reference tables of a module are below those of the linked module widened by
    `refAnswers`**, under `LinkAgrees`. -/
theorem refBi_le_widen {bi : Builtins} {m : HaxModule} {ls : List LinkedFn}
    (hs : LinkAgrees bi m ls) (fuelC : Nat) :
    ∀ n g vals v, refBi m.fns (m.linkTable bi) fuelC n g vals = some v →
      refBi (widen (refAnswers m bi fuelC) (ls.foldl HaxModule.linkFn m)).fns
        ((widen (refAnswers m bi fuelC) (ls.foldl HaxModule.linkFn m)).linkTable bi)
        fuelC n g vals = some v := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro g vals v h
    have hX : refAnswers m bi fuelC g vals = some v := refAnswers_eq h
    rw [foldl_linkFn]
    simp only [widen, HaxModule.linkTable]
    have hfind := find?_filter_names m.fns (fun a => ls.all fun l => a != l.name) g
    cases hp : ls.all (fun l => g != l.name) with
    | false =>
        -- the name is that of a linked function, whose body `f` answers at a successor depth
        rw [hp, ite_eq_right Bool.false_ne_true] at hfind
        rw [refBi_of_find_none _ _ _ _ hfind]
        obtain ⟨l, hl⟩ : ∃ l, ls.reverse.find? (·.name == g) = some l :=
          Option.isSome_iff_exists.mp (by grind [List.find?_isSome, List.all_eq_false])
        have hlg : l.name = g := by simpa using List.find?_some hl
        obtain ⟨f, hf, hres, hsem⟩ := hs l (by grind)
        rw [hlg] at hf
        rw [linkBi_of_find_some _ _ (l := widenFn (refAnswers m bi fuelC) l)
          (by rw [find?_map_widenFn, List.find?_append, hl]; rfl)]
        cases n with
        | zero => simp [refBi, hf] at h
        | succ k =>
            rw [refBi_succ_refSem _ _ _ _ hf] at h
            have hdec : (dec l.res v).isSome = true := by
              rw [← hres]
              grind [ModFn.refSem]
            cases ht : argsTypedB l.params vals with
            | true => simpa [widenFn, ht] using hsem fuelC k vals v ht h
            | false => simp [widenFn, ht, hlg, hX, hdec]
    | true =>
        rw [hp, ite_eq_left rfl] at hfind
        cases hf : m.fns.find? (·.name == g) with
        | none =>
            rw [refBi_of_find_none _ _ _ _ hf] at h
            rw [refBi_of_find_none _ _ _ _ (hfind.trans hf)]
            have hrev : ls.reverse.find? (·.name == g) = none := by
              grind [List.find?_eq_none, List.all_eq_true]
            cases hl : m.linked.find? (·.name == g) with
            | none =>
                rw [HaxModule.linkTable, linkBi_of_find_none _ _ hl] at h
                rw [linkBi_of_find_none _ _ (by
                  rw [find?_map_widenFn, List.find?_append, hrev, hl]; rfl)]
                exact h
            | some l =>
                have hlg : l.name = g := by simpa using List.find?_some hl
                rw [HaxModule.linkTable, linkBi_of_find_some _ _ hl] at h
                rw [linkBi_of_find_some _ _ (l := widenFn (refAnswers m bi fuelC) l) (by
                  rw [find?_map_widenFn, List.find?_append, hrev, hl]; rfl)]
                have hdec := l.sem_res _ _ h
                cases ht : argsTypedB l.params vals with
                | true => simpa [widenFn, ht] using h
                | false => simp [widenFn, ht, hlg, hX, hdec]
        | some f =>
            cases n with
            | zero => simp [refBi, hf] at h
            | succ k =>
                rw [refBi_succ_refSem _ _ _ _ hf] at h
                rw [refBi_succ_refSem _ _ _ _ (hfind.trans hf)]
                refine f.refSem_le (fun g' vals' v' h' => ?_) fuelC vals v h
                simpa [foldl_linkFn, widen, HaxModule.linkTable] using
                  ih k (Nat.lt_succ_self k) g' vals' v' h'

/-- **A run of a module is a run of the linked module widened by the values of the module**,
    under `LinkAgrees`. -/
theorem runs_foldl_linkFn (bi : Builtins) (σ : AbiLayout) (ls : List LinkedFn) (m : HaxModule)
    (hs : LinkAgrees bi m ls) {sa : AState} {v : Value} (h : HaxModule.Runs bi σ m sa v) :
    ∃ X, HaxModule.Runs bi σ (widen X (ls.foldl HaxModule.linkFn m)) sa v := by
  obtain ⟨env, fuel, fuelC, env', henv, hrun, hcf⟩ := h
  refine ⟨refAnswers m bi fuelC, env, fuel, fuelC, env', henv, ?_, hcf⟩
  have hle := refBi_le_widen hs fuelC m.depth
  simp only [HaxModule.table, foldl_linkFn, widen] at hle hrun ⊢
  exact denoteSpine_val_of_le fuel _ _ hle _ _ _ hrun

/-- Linking functions that the module has keeps `narrowOk`. -/
theorem narrowOk_foldl_linkFn (bi : Builtins) (σ : AbiLayout) (ls : List LinkedFn)
    (m : HaxModule) (hs : LinkAgrees bi m ls) :
    narrowOk (ls.foldl HaxModule.linkFn m) σ = narrowOk m σ := by
  have hmem : ∀ l ∈ ls, ∃ f ∈ m.fns, f.name = l.name := fun l hl => by
    obtain ⟨f, hf, -⟩ := hs l hl
    exact ⟨f, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩
  rw [Bool.eq_iff_iff, foldl_linkFn]
  simp only [narrowOk, Bool.and_eq_true, List.all_eq_true, List.mem_filter, List.mem_append,
    List.mem_reverse, bne_iff_ne]
  grind

/-- **A source run of a module is a source run of the linked module widened by the values of
    the module**: `runs_foldl_linkFn` at the entry state `narrowEntry`. -/
theorem haxRuns_foldl_linkFn (σ : AbiLayout) (ls : List LinkedFn) (m : HaxModule)
    (hs : LinkAgrees hax64WExit m ls) {sa : AState} {v : Value} (h : haxRuns σ m sa v) :
    ∃ X, haxRuns σ (widen X (ls.foldl HaxModule.linkFn m)) sa v := by
  obtain ⟨X, hX⟩ := runs_foldl_linkFn _ σ ls m hs h
  refine ⟨X, ?_⟩
  rw [haxRuns, narrowEntry, narrowOk_widen, narrowOk_foldl_linkFn _ σ ls m hs, ← narrowEntry]
  exact hX

/-! ## 5. Correctness against the source runs before linking -/

/-- **The compiler theorem on a linked module against the source runs of the module before
    linking.** Let the linked functions of the module with `ls` linked in turn have distinct
    names and be linked kernels, and let `ls` agree with the functions they replace at typed
    arguments. For a result of `compileA` on the linked module, the conclusion of
    `haxc_correct_auto_access` holds from every source run of `m`. -/
theorem haxc_correct_linked_source (m : HaxModule) (ls : List LinkedFn) (σ : AbiLayout)
    (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA (ls.foldl HaxModule.linkFn m) σ fname = some (P, bytes))
    (hnd : ((ls.foldl HaxModule.linkFn m).linked.map (·.name)).Nodup)
    (hk : ∀ l ∈ (ls.foldl HaxModule.linkFn m).linked, LinkedKernel l)
    (hs : LinkAgrees hax64WExit m ls)
    (sa : AState) (hsep : σ.Regions sa) (v : Value) (hrun : haxRuns σ m sa v) :
    ∃ prog, decodeLprog bytes = some prog ∧
      ((∃ sa', Halts aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' v
        ∧ sa'.regs "%rsp" = sa.regs "%rsp"
        ∧ (∀ x, SepLogic.X86.Loc.mem x
            ∉ wordsLocs (frameWords (sa.regs "%rsp") σ.frameLo σ.frameHi) →
          (∀ p ∈ σ.regions,
            SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
          sa'.mem x = sa.mem x)
        ∧ HaltsIn (layoutMem σ sa) prog 0 sa sa')
      ∨ ∃ cs : List CalleeData,
          cs.Sublist ((ls.foldl HaxModule.linkFn m).linked.filterMap LinkedFn.calleeData)
          ∧ cs ≠ [] ∧ (cs.map (·.name)).Nodup
          ∧ ∃ (pc Q : List RInstr) (k : String → Nat) (q : String → List RInstr),
            (∀ c ∈ cs, decodeLprog c.bytes = some (q c.name))
            ∧ decodeLprog (cs.flatMap (·.bytes)) = some Q
            ∧ (∀ c ∈ cs, ∃ A B, Q = A ++ shiftProg A.length (q c.name) ++ B
              ∧ A.length = k c.name)
            ∧ prog = pc ++ shiftProg pc.length Q
            ∧ (∃ sa', HaltsC aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' v)
            ∧ ∃ sa', HaltsO aMachine (tabOracle cs pc.length k q) pc 0 sa sa'
              ∧ σ.ResultOf sa sa' v) := by
  obtain ⟨X, hX⟩ := haxRuns_foldl_linkFn σ ls m hs hrun
  exact haxc_correct_widen X _ σ fname P bytes hc sa hsep v hX hnd hk

/-- **Correctness of the driver against the source runs of the inlining module.** Let
    `compileModule` return `(P, bytes)` on the module `m`. Then the functions of `m` have a
    call order and compiled callees `ks`, and for every list `ls` of linked functions with
    the callees and the data of the stubs of `ks` such that

    * the linked functions of the module with `ls` linked in turn have distinct names and
      are linked kernels (`LinkedKernel`), and
    * the meaning of each function of `ls` returns, on the arguments of its parameter types,
      the values of the reference meaning of the function it replaces (`LinkAgrees`),

    the bytes decode to a program `prog`, and from every entry state `sa` satisfying
    `σ.Regions`, every value `v` of a source run of `m` from `sa` is read back by `σ` as in
    `haxc_correct_auto`. The bytes are those of `compileA` on the linked module
    (`compileModule_eq`), and the runs are `haxc_correct_linked_source`. -/
theorem compileModule_correct {m : HaxModule} {σ : AbiLayout} {fname : String}
    {plan : String → Option CalleePlan} {P : Lprog} {bytes : List (BitVec 8)}
    (h : compileModule m σ fname plan = some (P, bytes)) :
    ∃ order ks, callOrder m.fns = some order
      ∧ order.mapM (fun f => (plan f.name).bind fun pl => compileCallee pl f) = some ks
      ∧ ∀ ls : List LinkedFn, List.Forall₂ SameData ks ls →
        ((ls.foldl HaxModule.linkFn m).linked.map (·.name)).Nodup →
        (∀ l ∈ (ls.foldl HaxModule.linkFn m).linked, LinkedKernel l) →
        LinkAgrees hax64WExit m ls →
        ∀ (sa : AState), σ.Regions sa → ∀ v, haxRuns σ m sa v →
          ∃ prog, decodeLprog bytes = some prog ∧
            ((∃ sa', Halts aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' v)
            ∨ ∃ cs : List CalleeData,
              cs.Sublist ((ls.foldl HaxModule.linkFn m).linked.filterMap LinkedFn.calleeData)
              ∧ cs ≠ [] ∧ (cs.map (·.name)).Nodup
              ∧ ∃ (pc Q : List RInstr) (k : String → Nat) (q : String → List RInstr),
                (∀ c ∈ cs, decodeLprog c.bytes = some (q c.name))
                ∧ decodeLprog (cs.flatMap (·.bytes)) = some Q
                ∧ (∀ c ∈ cs, ∃ A B, Q = A ++ shiftProg A.length (q c.name) ++ B
                  ∧ A.length = k c.name)
                ∧ prog = pc ++ shiftProg pc.length Q
                ∧ (∃ sa', HaltsC aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' v)
                ∧ ∃ sa', HaltsO aMachine (tabOracle cs pc.length k q) pc 0 sa sa'
                  ∧ σ.ResultOf sa sa' v) := by
  obtain ⟨order, ks, ho, hks, hc⟩ := compileModule_eq h
  refine ⟨order, ks, ho, hks, fun ls hls hnd hk hs sa hsep v hrun => ?_⟩
  obtain ⟨prog, hd, h⟩ :=
    haxc_correct_linked_source m ls σ fname P bytes (hc ls hls) hnd hk hs sa hsep v hrun
  rcases h with ⟨sa', hh, hR, -⟩ | h
  · exact ⟨prog, hd, .inl ⟨sa', hh, hR⟩⟩
  · exact ⟨prog, hd, .inr h⟩

/-! ## 6. An instance of the hypotheses -/

namespace Witness

open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (CalleeSpec runOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (phys gpOk)
open _root_.Hax.ContinueFlag (app_run var_run args_cons_run args_nil_run)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall (LinkedWordKernel)
open CatCrypt.Crypto.Hax (wordVal)
open _root_.Hax (TExpr TExprKind ImpType)

/-- The extraction `a + b` of a checked addition of two `u64` parameters. -/
def addBody : TExpr :=
  .mk (.app "Add#64" [.mk (.var "a") (.uint .w64), .mk (.var "b") (.uint .w64)]) (.uint .w64)

/-- The source function `add_words(a, b) = a + b` at two `64`-bit words. -/
def addFn : ModFn :=
  ⟨"add_words", [("a", .word 64), ("b", .word 64)], .word 64, addBody⟩

/-- The module whose entry calls `add_words(a, b)`. -/
def addModule : HaxModule where
  entry :=
    .mk (.app "add_words" [.mk (.var "a") (.uint .w64), .mk (.var "b") (.uint .w64)])
      (.uint .w64)
  fns := [addFn]
  depth := 1

/-- The word of an argument value, `0` at a value that is no word. -/
def wordOf (v : Value) : BitVec 64 := (dec (.word 64) v).getD 0

/-- The meaning of the kernel: the wrapping sum, defined at two scalar arguments. -/
def addSem (vals : List Value) : Option Value :=
  if vals.map valKind = [.scalar, .scalar] then
    some (wordVal (wordOf (vals.getD 0 .unit) + wordOf (vals.getD 1 .unit)))
  else none

/-- The layout of the entry and of the kernel: `a` in `%rdi`, `b` in `%rsi`, the result in
    `%rdi`. -/
def addLayout : AbiLayout where
  args := [⟨"a", "%rdi", .scalar⟩, ⟨"b", "%rsi", .scalar⟩]
  consts := []
  result := .reg "%rdi"
  bounds := []
  frameLo := 0
  frameHi := -8

/-- The decoded code of the kernel: `add %rsi, %rdi; ret`. -/
def addCode : List RInstr := [.op (.add "%rdi" (.reg "%rsi")), .ret]

/-- The kernel of the addition of two words, with its machine code. -/
def addKernel : LinkedFn where
  name := "add_words"
  params := [("a", .word 64), ("b", .word 64)]
  res := .word 64
  sem := addSem
  sem_res := fun vals v h => by
    unfold addSem at h
    split at h
    · cases h
      rw [CatCrypt.Crypto.Hax.dec_wordVal]
      rfl
    · cases h
  layout := addLayout
  pre := fun _ => True
  foot := fun _ _ => False
  post := fun s s' => s'.regs "%rdi" = s.regs "%rdi" + s.regs "%rsi"
  pub := fun _ _ => True
  pub_of_regs := fun _ _ _ _ => trivial
  post_sem := fun sa sa' v _ hp h => by
    have hw : ∀ x : BitVec 64, wordOf (.int x.toNat) = x := fun x => by
      rw [wordOf, show Value.int x.toNat = wordVal x from rfl, CatCrypt.Crypto.Hax.dec_wordVal]
      rfl
    simp [addSem, addLayout, AbiArg.read, valKind, hw] at h
    simp [AbiLayout.ResultOf, addLayout, ResultKind.read, hp, ← h, wordVal]
  clob := ["%rdi"]
  frame := 0
  bytes := [0x48, 0x01, 0xF7, 0xC3]

/-- The meaning of the kernel is defined exactly at the kinds of its parameters. -/
theorem addKernel_sem_isSome (vals : List Value) :
    (addKernel.sem vals).isSome = true ↔ vals.map valKind = linkedKinds addKernel := by
  have hk : linkedKinds addKernel = [.scalar, .scalar] := rfl
  rw [hk]
  change (addSem vals).isSome = true ↔ _
  unfold addSem
  split <;> simp_all

/-- The bytes of the kernel decode to its code. -/
theorem decode_addKernel : decodeLprog addKernel.bytes = some addCode := by rfl

/-- The kernel has data, so the fields `kinds` and `code` of `LinkedKernel` apply to it. -/
theorem addKernel_calleeData : addKernel.calleeData.isSome = true := by rfl

/-- A run of the code has the empty trace and ends after the addition. -/
theorem run_addCode {s s' : AState} {t : List CT.CTLeak} (h : runOf ctRegime addCode s t s') :
    t = [] ∧ s' = Ascent.AddrMem.evalInstrA s (.add "%rdi" (.reg "%rsi")) := by
  cases h with
  | ret h => simp [addCode] at h
  | jcc h => simp [addCode] at h
  | call h => simp [addCode] at h
  | stack h hops =>
      obtain rfl := by simpa [addCode] using h
      cases hops
  | op h _ hr =>
      obtain rfl := by simpa [addCode] using h
      cases hr with
      | ret => exact ⟨rfl, rfl⟩
      | op h => simp [addCode] at h
      | jcc h => simp [addCode] at h
      | call h => simp [addCode] at h
      | stack h hops =>
          obtain rfl := by simpa [addCode] using h
          cases hops

/-- The upper-case names of the two argument registers, computed on their lists of
    characters (`String.toList_map`, `String.toList_copy_drop`). -/
theorem regNames :
    ("%rdi".drop 1).copy.toUpper = "RDI" ∧ ("%rsi".drop 1).copy.toUpper = "RSI" := by
  simp [String.toUpper, ← String.toList_inj, String.toList_map, String.toList_copy_drop]

/-- **The kernel is a linked kernel.** -/
theorem addKernel_kernel : LinkedKernel addKernel := by
  refine LinkedWordKernel.toKernel ?_ rfl (by simp [addKernel, addLayout]) (by simp [addKernel])
  refine
    { params_scalar := fun q hq => ?_
      res_arr := fun n t => by simp [addKernel]
      res_slice := fun t => by simp [addKernel]
      sem_kinds := fun vals v h => (addKernel_sem_isSome vals).mp (by simp [h])
      callSite := fun _ _ _ _ => trivial
      layout := fun c hc => ?_
      arity := rfl
      code := fun c hc => ?_ }
  · obtain rfl | rfl : q = ("a", .word 64) ∨ q = ("b", .word 64) := by
      simpa [addKernel] using hq
    all_goals rfl
  · obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hc
    cases hr
    have hi : phys "RDI" = "%rdi" ∧ phys "RSI" = "%rsi" := by decide
    have hg : gpOk "RDI" = true ∧ gpOk "RSI" = true := by decide
    constructor <;>
      simp [addKernel, addLayout, CalleeData.resReg, regNames, hi, hg]
  · obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hc
    refine ⟨addCode, decode_addKernel, ?_, fun _ _ h => h.elim⟩
    constructor
    · exact fun s _ => ⟨_, _, .op rfl trivial (.ret rfl)⟩
    · intro s t s' _ h
      obtain ⟨-, rfl⟩ := run_addCode h
      rfl
    · intro s t s' _ h x hx
      obtain ⟨-, rfl⟩ := run_addCode h
      refine X86Backend.DecodedCT.evalInstrA_regs_of_not_dst _ _ x ?_
      simp [X86Backend.LinkedFnCallee.wordSig, addKernel] at hx
      simpa [X86Backend.MachineConstantTime.dstRegs] using hx
    · intro s t s' _ h x _
      obtain ⟨-, rfl⟩ := run_addCode h
      rfl
    · intro s t s' _ h
      obtain ⟨-, rfl⟩ := run_addCode h
      rfl
    · intro s₁ s₂ t₁ t₂ s₁' s₂' _ _ _ h₁ h₂
      rw [(run_addCode h₁).1, (run_addCode h₂).1]

/-- The reference meaning of `add_words` at two integers is the call of `Add#64` of the
    table. -/
theorem addFn_refSem (T : Builtins) (fuel : Nat) (a b : Int) :
    addFn.refSem T fuel [.int a, .int b] =
      (T "Add#64" [.int a, .int b]).filter fun v => (dec (.word 64) v).isSome := by
  cases h : T "Add#64" [.int a, .int b] <;>
    simp [ModFn.refSem, addFn, addBody, TExpr.erase, TExpr.erase.eraseList,
      _root_.Hax.InlineLocalClosures.denoteSpine, app_run, var_run, args_cons_run, args_nil_run,
      Hax.ImpToNF.paramsEnv, Option.filter_some, h]
  rfl

/-- The table of the module at `Add#64`, at every depth. -/
theorem addModule_table_add (fuelC n : Nat) (vals : List Value) :
    refBi addModule.fns (addModule.linkTable hax64WExit) fuelC n "Add#64" vals
      = hax64WExit "Add#64" vals :=
  refBi_of_find_none _ _ _ _ (by decide) vals

/-- **The kernel agrees with the body of `add_words` at typed arguments.** -/
theorem addKernel_agrees : LinkAgrees hax64WExit addModule [addKernel] := by
  intro l hl
  obtain rfl : l = addKernel := by simpa using hl
  refine ⟨addFn, rfl, rfl, fun fuelC n vals v ht h => ?_⟩
  obtain ⟨a, b, rfl, ha, hb⟩ : ∃ a b : Int, vals = [.int a, .int b]
      ∧ (0 ≤ a ∧ a < 2 ^ 64) ∧ (0 ≤ b ∧ b < 2 ^ 64) := by
    rcases vals with _ | ⟨x, _ | ⟨y, _ | ⟨z, zs⟩⟩⟩ <;>
      simp [addKernel, argsTypedB] at ht
    cases x <;> cases y <;> simp_all [dec]
  rw [addFn_refSem, addModule_table_add, Option.filter_eq_some_iff,
    CatCrypt.Crypto.Hax.hax64WExit_of_ne (by decide) (by decide) (by decide) (by decide)] at h
  have hadd : (_root_.Hax.uintAddOp 64 a b <|> none) = some v :=
    CatCrypt.Crypto.Hax.hax64Exit_sub h.1
  rw [Hax.ImpToNF.orElse_none_eq, _root_.Hax.uintAddOp] at hadd
  split at hadd
  · cases hadd
    rename_i hr
    have hka : wordOf (.int a) = BitVec.ofNat 64 a.toNat := by
      simp only [wordOf, dec, ite_eq_left ha, Option.getD_some]
    have hkb : wordOf (.int b) = BitVec.ofNat 64 b.toNat := by
      simp only [wordOf, dec, ite_eq_left hb, Option.getD_some]
    simp [addKernel, addSem, valKind, hka, hkb, wordVal]
    omega
  · cases hadd

/-- The linked functions of the linked module have distinct names and are linked kernels. -/
theorem addModule_linked :
    (([addKernel].foldl HaxModule.linkFn addModule).linked.map (·.name)).Nodup
      ∧ ∀ l ∈ ([addKernel].foldl HaxModule.linkFn addModule).linked, LinkedKernel l := by
  simp [HaxModule.linkFn, addModule, addKernel_kernel]

/-- The layout of the module has its entry conditions at every state. -/
theorem addLayout_regions (sa : AState) : addLayout.Regions sa :=
  ModuleCalls.regions_of_free rfl rfl (by decide) sa

/-- **A source run of the module that calls `add_words`**: from a state whose argument words
    have a sum below `2 ^ 64`, the module returns the sum. -/
theorem addModule_run (sa : AState)
    (h : (sa.regs "%rdi").toNat + (sa.regs "%rsi").toNat < 2 ^ 64) :
    haxRuns addLayout addModule sa
      (.int ((sa.regs "%rdi").toNat + (sa.regs "%rsi").toNat : Nat)) := by
  rw [haxRuns_iff_of_widths_nil rfl]
  refine ⟨addLayout.canonEnv sa, 0, 0, addLayout.canonEnv sa,
    addLayout.envOf_canonEnv (by decide) sa, ?_, rfl⟩
  generalize hx : (sa.regs "%rdi").toNat = x at h
  generalize hy : (sa.regs "%rsi").toNat = y at h
  have hcall : addModule.table hax64WExit 0 "add_words" [.int x, .int y]
      = some (.int (x + y : Nat)) := by
    change refBi addModule.fns (addModule.linkTable hax64WExit) 0 1 _ _ = _
    rw [refBi_succ_refSem _ _ _ _ (f := addFn) rfl, addFn_refSem, addModule_table_add,
      CatCrypt.Crypto.Hax.hax64WExit_of_ne (by decide) (by decide) (by decide) (by decide)]
    have hb : _root_.Hax.hax64Builtins "Add#64" [.int x, .int y] = some (.int (x + y : Nat)) := by
      have hadd : ∀ a b : Int, _root_.Hax.hax64Builtins "Add#64" [.int a, .int b]
          = (_root_.Hax.uintAddOp 64 a b <|> none) := fun _ _ => rfl
      rw [hadd, Hax.ImpToNF.orElse_none_eq, _root_.Hax.uintAddOp, ite_eq_left (by omega)]
      simp
    have hadm : CatCrypt.Crypto.Hax.hax64ScalarAdmit "Add#64" [.int x, .int y]
        (.int (x + y : Nat)) = true := by
      have hs : CatCrypt.Crypto.Hax.exitScalarRes "Add#64" = true := by
        simp [CatCrypt.Crypto.Hax.exitScalarRes, CatCrypt.Crypto.Hax.exitScalarCall]
      have ho : CatCrypt.Crypto.Hax.hax64ScalarOp "Add#64" = true := by decide
      rw [CatCrypt.Crypto.Hax.hax64ScalarAdmit,
        CatCrypt.Crypto.Hax.exitMarshalOk_of_arrCtorLen (by decide)]
      simp [hs, ho, CatCrypt.Crypto.Hax.hax64ArgsShape, CatCrypt.Crypto.Hax.scalarValNB]
      omega
    rw [CatCrypt.Crypto.Hax.hax64Exit_of_scalarAdmit hb rfl hadm]
    simp [dec]
    omega
  have hea : addLayout.canonEnv sa "a" = some (.int x) := by rw [← hx]; rfl
  have heb : addLayout.canonEnv sa "b" = some (.int y) := by rw [← hy]; rfl
  simp [addModule, TExpr.erase, TExpr.erase.eraseList,
    _root_.Hax.InlineLocalClosures.denoteSpine, app_run, var_run, args_cons_run, args_nil_run,
    hea, heb] at hcall ⊢
  simp [hcall]

/-- **A run of the linked module**: from the zero state the call of the kernel returns `0`,
    the hypothesis on runs of `haxc_correct_auto` at a module with a linked function. -/
theorem addLinked_run :
    haxRuns addLayout ([addKernel].foldl HaxModule.linkFn addModule)
      { regs := fun _ => 0, mem := fun _ => 0 } (.int 0) := by
  rw [haxRuns_iff_of_widths_nil rfl]
  let sa : AState := { regs := fun _ => 0, mem := fun _ => 0 }
  refine ⟨addLayout.canonEnv sa, 0, 0, addLayout.canonEnv sa,
    addLayout.envOf_canonEnv (by decide) sa, ?_, rfl⟩
  have hcall : ([addKernel].foldl HaxModule.linkFn addModule).table hax64WExit 0 "add_words"
      [.int 0, .int 0] = some (.int 0) := by rfl
  have hea : addLayout.canonEnv sa "a" = some (.int 0) := by rfl
  have heb : addLayout.canonEnv sa "b" = some (.int 0) := by rfl
  simp [addModule, HaxModule.linkFn, TExpr.erase, TExpr.erase.eraseList,
    _root_.Hax.InlineLocalClosures.denoteSpine, app_run, var_run, args_cons_run, args_nil_run,
    hea, heb] at hcall ⊢
  simp [hcall]

/-- **The hypotheses on linked functions and on runs hold together**, with a call at which
    the kernel has a value: at some entry state satisfying the layout, the module has a run,
    the kernel agrees with the body it replaces and is a linked kernel, and the names are
    distinct. -/
theorem hypotheses_satisfiable :
    LinkAgrees hax64WExit addModule [addKernel]
      ∧ (([addKernel].foldl HaxModule.linkFn addModule).linked.map (·.name)).Nodup
      ∧ (∀ l ∈ ([addKernel].foldl HaxModule.linkFn addModule).linked, LinkedKernel l)
      ∧ addKernel.sem [.int 0, .int 0] = some (.int 0)
      ∧ ∃ sa, addLayout.Regions sa ∧ haxRuns addLayout addModule sa (.int 0) :=
  ⟨addKernel_agrees, addModule_linked.1, addModule_linked.2, by rfl,
    { regs := fun _ => 0, mem := fun _ => 0 }, addLayout_regions _,
    addModule_run _ (by simp)⟩

end Witness

end CatCrypt.Crypto.SecureCompilation.Haxc.LinkStepsTyped
