/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomExportClass
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomCallShape
import CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapDom

/-!
# The store-chain shape of the code of the field domain

The code the gate reads on a member of the field domain is the export of a program of the shape
`LoadsChain`, renamed by its webs when the webs check accepts, followed by the result copy when
one is taken. The export is one chain of stores from a root (`loadsChain_export_class`); its
names are argument and slot names, without `#`, each written once, and none reads what it
writes. The renaming by webs keeps the store-chain shape (`chainShape_webRen`), the copy versions
`D#c<j>` of the result buffer are names of neither code, and the result buffer, an argument
name, is never written. When the copy is taken the root of the returned array is not the result
buffer, which then is not consumed by the code; so the code with the copy has the store-chain
shape (`chainShape_regionCoCode`). Every member of the field domain therefore has the shape
`FieldChainShape`, and the stages `G2` and `G3` hold without hypothesis.

## Main results

* `chainShape_mono_obs`: the store-chain shape holds at fewer names read after the body.
* `regionCopy_alias`: the copy decision holds only when the root of the returned array is not
  the result buffer.
* `chainShape_regionCoCode_root`: the store-chain shape in the form of the gate, from the shape
  of the code under its alias table, its root, and the facts on the argument names.
* `chainShape_regionCoCode_export`, `chainShape_regionCoCode_webs`: the same for the export of
  one chain of stores and for its renaming by webs.
* `fieldDom_fieldChainShape`: every member of the field domain has the shape
  `FieldChainShape`.
* `fieldDom_coCfgB'`, `fieldDom_coEntryFix'`: the stages `G2` and `G3` on the field domain.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN (operandName)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (aliasStepO zeroDst?)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg (renArr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete (ReadAt WrAt ConsumedAt
  ChainConsume ChainShape rdArr wrArr)

/-! ## 1. The form of the gate from the root of the code -/

/-- **The store-chain shape holds at fewer names read after the body.** -/
theorem chainShape_mono_obs {σ : String → String} {body : List LinstrRM}
    {aa : String → Nat → Option Nat} {ao : String → Option Nat} {obs obs' : List String}
    (h : ChainShape σ body aa ao obs) (hsub : ∀ y ∈ obs', y ∈ obs) :
    ChainShape σ body aa ao obs' := by
  have hR : ∀ j r, ReadAt body aa obs' j r → ReadAt body aa obs j r := by
    rintro j r (h | ⟨hj, hr⟩)
    · exact .inl h
    · exact .inr ⟨hj, hsub r hr⟩
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun j r w hr hw => h1 j r w (hR j r hr) hw, fun c r j hc hr => h2 c r j hc (hR j r hr),
    fun k d r hw hσ hne hb => ?_⟩
  rcases h3 k d r hw hσ hne hb with h | h
  · exact .inl h
  · exact .inr fun j hj hr => h j hj (hR j r hr)

/-- The returned names of an array result are among the returned names. -/
theorem regionCoObs_sub (t : JasminTy) (res : List LOperand) :
    ∀ y ∈ regionCoObs t res, y ∈ res.map operandName := by
  intro y hy
  unfold regionCoObs at hy
  split at hy
  · exact hy
  · cases hy

/-- **The copy decision reads the root of the returned array**: a copy `(src, D, m)` is taken
    on code without a zeroing only when the alias table of the code sends `src` to a name other
    than `D`. -/
theorem regionCopy_alias {σ : AbiLayout} {nm : String → String} {t : JasminTy}
    {C : List LinstrRM} {res : List LOperand} {src D : String} {m : Nat}
    (h : regionCopy σ nm t none C res = some (src, D, m)) (hz : ∀ i ∈ C, zeroDst? i = none) :
    (C.foldl (aliasStepO []) {}).getD src src ≠ D := by
  unfold regionCopy at h
  split at h
  · simp only [Option.filter_eq_some_iff] at h
    obtain ⟨hc, -⟩ := h
    rw [resCopyOf_eq_of_noZero _ _ _ hz] at hc
    split at hc
    · split at hc
      · rename_i hcond
        simp only [Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl, -⟩ := hc
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hcond
        exact hcond.1.1.2
      · cases hc
    · cases hc
  · cases h

/-- Without a register result in the layout there is no result move. -/
theorem regionRet_words {σ : AbiLayout} {nm : String → String} {t : JasminTy}
    {res : List LOperand} {R : String} {n : Nat} (h : σ.result = .words R n) :
    regionRet σ nm t res = none := by
  unfold regionRet
  split
  · rw [h]
  · rfl

/-- The copy version `copyName D (k + 1)` is no name without `#`. -/
theorem ne_copyName_of_hash {r : String} (hr : '#' ∉ r.toList) (D : String) (k : Nat) :
    r ≠ copyName D (k + 1) := by
  intro e
  apply hr
  rw [e]
  simp [copyName]

/-- The copy version `copyName D (k + 1)` of a name `D` without `#` is no name without `#`
    and no web name of one. -/
theorem webLook_ne_copyName (tab : X86Backend.ArrWebs.WebSt × Std.HashSet Nat × Std.HashSet Nat)
    {r D : String} (hr : '#' ∉ r.toList) (hD : '#' ∉ D.toList) (j k : Nat) :
    X86Backend.ArrWebs.webLook tab j r ≠ copyName D (k + 1) ∧ r ≠ copyName D (k + 1) := by
  have hc : copyName D (k + 1) = D ++ "#c" ++ toString (k + 1) := by
    simp [copyName]
  have hpc : hashPrefix (copyName D (k + 1)) = D.toList := by
    rw [hc]
    unfold hashPrefix
    rw [String.toList_append, String.toList_append, List.append_assoc, takeWhile_noHash _ hD]
    simp
  have hne : ∀ s : String, r ++ "#w" ++ s ≠ D ++ "#c" ++ toString (k + 1) := by
    intro s e
    have h1 : hashPrefix (r ++ "#w" ++ s) = r.toList := hashPrefix_web hr s
    rw [e, ← hc, hpc] at h1
    obtain rfl := String.toList_injective h1.symm
    have h2 := congrArg String.toList e
    simp only [String.toList_append, List.append_assoc] at h2
    have h3 := List.append_cancel_left h2
    simp at h3
  have hplain : r ≠ copyName D (k + 1) := by
    intro e
    apply hr
    rw [e, hc]
    simp
  refine ⟨?_, hplain⟩
  rcases X86Backend.ArrWebs.webLook_cases tab j r with e | ⟨s, e⟩ <;> rw [e]
  · exact hplain
  · rw [hc]; exact hne _

/-- **The store-chain shape in the form of the gate, from the root of the code.** Let the code
    `C` zero no array and have the store-chain shape under its alias table with its returned
    names read after it; let the table send every written name to the root `z` and fix every
    other name; let `C` write no array or return one name it writes; and let no argument name be
    written, the root be every argument name that `C` consumes, and the copy versions of the
    argument names be neither read nor written in `C`. Then the code with the result copy of a
    region export without a register result has the shape under the alias table of the gate. -/
theorem chainShape_regionCoCode_root {σ : AbiLayout} {nm : String → String} {t : JasminTy}
    {C : List LinstrRM} {res : List LOperand} {z : String}
    (hret : regionRet σ nm t res = none) (hz : ∀ i ∈ C, zeroDst? i = none)
    (hS : ChainShape (fun n => (C.foldl (aliasStepO []) {}).getD n n) C (fun _ _ => none)
      (fun _ => none) (res.map operandName))
    (hW1 : ∀ w d, WrAt C (fun _ => none) w d → (C.foldl (aliasStepO []) {}).getD d d = z)
    (hW2 : ∀ n, (∀ w, ¬ WrAt C (fun _ => none) w n) →
      (C.foldl (aliasStepO []) {}).getD n n = n)
    (hRet : (∀ w d, ¬ WrAt C (fun _ => none) w d) ∨
      ∃ y, res.map operandName = [y] ∧ ∃ w, WrAt C (fun _ => none) w y)
    (hAw : ∀ (j w : Nat), ¬ WrAt C (fun _ => none) w (argName j))
    (hAc : ∀ (j c : Nat), ConsumedAt C (fun _ _ => none) (fun _ => none) c (argName j) →
      z = argName j)
    (hAr : ∀ (j c : Nat) (i : LinstrRM) (r : String) (k : Nat), C[c]? = some i →
      r ∈ rdArr (fun _ _ => none) i →
      r ≠ copyName (argName j) (k + 1))
    (hAwr : ∀ (j w : Nat) (r : String) (k : Nat), WrAt C (fun _ => none) w r →
      r ≠ copyName (argName j) (k + 1)) :
    ChainShape (canonMemrefName (regionAliasTab σ nm t none res
        (regionCoCode σ nm t C res (regionCopy σ nm t none C res))))
      (regionCoCode σ nm t C res (regionCopy σ nm t none C res)) (calleeAAT none)
      (calleeAOT none) (regionCoObs t (regionOut (regionCopy σ nm t none C res) res)) := by
  cases hcp : regionCopy σ nm t none C res with
  | none =>
      have hcode : regionCoCode σ nm t C res none = C := by
        simp [regionCoCode, hret, JasminLsemRenameLoop.movesOf]
      rw [hcode, regionAliasTab_eq_of_noZero _ _ _ _ _ hz]
      exact chainShape_mono_obs hS (regionCoObs_sub t res)
  | some c =>
      obtain ⟨src, D, m⟩ := c
      have hal := regionCopy_alias hcp hz
      obtain ⟨-, rfl, ⟨op, rfl, hop⟩, ⟨j, a, -, -, rfl⟩, -, -⟩ := regionCopy_some hcp
      subst hop
      have hD : (C.foldl (aliasStepO []) {}).getD (argName j) (argName j) = argName j :=
        hW2 _ (hAw j)
      have hzD : (∃ w d, WrAt C (fun _ => none) w d) → z ≠ argName j := by
        rintro ⟨w, d, hw⟩
        rcases hRet with hn | ⟨y, hy, w', hy'⟩
        · exact absurd hw (hn w d)
        · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hy
          subst hy
          rw [← hW1 _ _ hy']
          exact hal
      have hS' : ChainShape (fun n => (C.foldl (aliasStepO []) {}).getD n n) C (fun _ _ => none)
          (fun _ => none) [operandName op] := hS
      refine chainShape_regionCoCode hcp hz hS' (fun c i r k hi hr => hAr j c i r k hi hr)
        (fun w r k hw => hAwr j w r k hw) (fun e => hal (by rw [e, hD])) (fun c hc => ?_)
        (fun w d hw => ?_) (by rw [hD]; exact hal)
      · have hzj := hAc j c hc
        obtain ⟨i, d, hi, -, hd, -⟩ := hc
        exact hzD ⟨c, d, i, hi, hd⟩ hzj
      · rw [hW1 w d hw, hD]
        exact hzD ⟨w, d, hw⟩

/-- A web name of a name without `#` that is a name without `#` is that name. -/
theorem webLook_eq_plain (tab : X86Backend.ArrWebs.WebSt × Std.HashSet Nat × Std.HashSet Nat)
    {k : Nat} {a b : String} (ha : '#' ∉ a.toList) (hb : '#' ∉ b.toList)
    (h : X86Backend.ArrWebs.webLook tab k a = b) : a = b := by
  have hpa : hashPrefix (X86Backend.ArrWebs.webLook tab k a) = a.toList := by
    rcases X86Backend.ArrWebs.webLook_cases tab k a with e | ⟨r, e⟩ <;> rw [e]
    · exact hashPrefix_of_not_mem ha
    · exact hashPrefix_web ha _
  rw [h, hashPrefix_of_not_mem hb] at hpa
  exact String.toList_injective hpa.symm

/-! ## 2. The export of one chain, and its webs -/

section ExportGate

variable {nArgs : Nat} {fn : String}

/-- The root of the export of one chain is every argument name that a store consumes. -/
theorem consumed_argName_root {C : List LinstrRM} {x : String} (hE : ExportClass C x)
    (hAw : ∀ (j w : Nat), ¬ WrAt C (fun _ => none) w (argName j)) {j c : Nat}
    (hc : ConsumedAt C (fun _ _ => none) (fun _ => none) c (argName j)) : x = argName j := by
  obtain ⟨i, d, hi, hr, hd, -⟩ := hc
  obtain ⟨b, hb, -, hx⟩ := (hE c i hi).2.2.2.2 d hd
  rw [hb, List.mem_singleton] at hr
  subst hr
  rcases hx with rfl | ⟨k₀, -, hW⟩
  · rfl
  · exact absurd hW (hAw j k₀)

/-- **The store-chain shape of the export of one chain of stores in the form of the gate**,
    without a register result. -/
theorem chainShape_regionCoCode_export {σ : AbiLayout} {nm : String → String} {t : JasminTy}
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    (h : LoadsChain p) (hn : nArgs ≤ Γ.length) {n : Nat} {r : Exported}
    (hr : exportR nArgs fn p Γ.length n = some r) (hret : regionRet σ nm t r.res = none) :
    ChainShape (canonMemrefName (regionAliasTab σ nm t none r.res
        (regionCoCode σ nm t r.code r.res (regionCopy σ nm t none r.code r.res))))
      (regionCoCode σ nm t r.code r.res (regionCopy σ nm t none r.code r.res)) (calleeAAT none)
      (calleeAOT none)
      (regionCoObs t (regionOut (regionCopy σ nm t none r.code r.res) r.res)) := by
  obtain ⟨x, -, -, hAl, hE, hRet⟩ := loadsChain_export_class (fn := fn) h hn hr
  obtain ⟨hR, hW, -⟩ := loadsChain_export (fn := fn) (aa := fun _ _ => none)
    (ao := fun _ => none) (fun _ _ => rfl) (fun _ => rfl) h hn hr
  have hS := loadsChain_export_chainShape_alias (fn := fn) (ao := fun _ => none) (fun _ => rfl)
    h hn hr
  have hAw : ∀ j w, ¬ WrAt r.code (fun _ => none) w (argName j) := fun j w hw =>
    JasminLsemSimulation.regName_ne_argName _ j (hW w _ hw).symm
  have hnh : ∀ c i y, r.code[c]? = some i → y ∈ rdArr (fun _ _ => none) i →
      '#' ∉ y.toList :=
    fun c i y hi hy => (hR c y (.inl ⟨i, hi, hy⟩)).hash_not_mem
  refine chainShape_regionCoCode_root (z := x) hret (fun i hi => ?_) hS
    (fun w d hw => ?_) (fun y hy => ?_) hRet hAw
    (fun j c hc => consumed_argName_root hE hAw hc)
    (fun j c i y k hi hy => ?_) (fun j w y k hw => ?_)
  · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hi
    exact (hE k i hk).2.2.1
  · rw [(hAl {}).1 w d hw]
    simp
  · rw [(hAl {}).2 y hy]
    simp
  · exact ne_copyName_of_hash (hnh c i y hi hy) _ k
  · rw [hW w y hw]
    exact ne_copyName_of_hash (hash_not_mem_regName _) _ k

open CatCrypt.Crypto.SecureCompilation.X86Backend.ArrWebs (webLook webRen webB stepRen
  webB_obs webB_exit)

/-- **The store-chain shape of the webs of the export of one chain of stores in the form of the
    gate**, at a position map of web tables that `webB` accepts with the returned names among the
    names it checks after the body, when no exported instruction is the shadow of a call and
    the layout has no register result. -/
theorem chainShape_regionCoCode_webs {σ : AbiLayout} {nm : String → String} {t : JasminTy}
    (tab : X86Backend.ArrWebs.WebSt × Std.HashSet Nat × Std.HashSet Nat)
    {L : Nat → List String} {obsW : List String}
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    (h : LoadsChain p) (hn : nArgs ≤ Γ.length) {n : Nat} {r : Exported}
    (hr : exportR nArgs fn p Γ.length n = some r)
    (hsh : ∀ i ∈ r.code, LprogIsa.shadowCall? i.1 = none)
    (hacc : webB (webLook tab) r.code L obsW (fun _ _ => none) (fun _ => none) = true)
    (hobs : ∀ y ∈ r.res.map operandName, y ∈ obsW) (hret : regionRet σ nm t r.res = none) :
    ChainShape (canonMemrefName (regionAliasTab σ nm t none r.res
        (regionCoCode σ nm t (webRen (webLook tab) (fun _ => none) r.code) r.res
          (regionCopy σ nm t none (webRen (webLook tab) (fun _ => none) r.code) r.res))))
      (regionCoCode σ nm t (webRen (webLook tab) (fun _ => none) r.code) r.res
        (regionCopy σ nm t none (webRen (webLook tab) (fun _ => none) r.code) r.res))
      (calleeAAT none) (calleeAOT none)
      (regionCoObs t (regionOut (regionCopy σ nm t none
        (webRen (webLook tab) (fun _ => none) r.code) r.res) r.res)) := by
  obtain ⟨x, hx, hC, -, hE, hRet⟩ := loadsChain_export_class (fn := fn) h hn hr
  obtain ⟨hR, hW, -⟩ := loadsChain_export (fn := fn) (aa := fun _ _ => none)
    (ao := fun _ => none) (fun _ _ => rfl) (fun _ => rfl) h hn hr
  obtain ⟨h1, h2⟩ := loadsChain_export_chainShape₁₂ (fn := fn) (aa := fun _ _ => none)
    (ao := fun _ => none) (fun _ _ => rfl) (fun _ => rfl) h hn hr
  have hidx : ∀ i ∈ r.code, ∃ k, r.code[k]? = some i := fun i hi =>
    List.mem_iff_getElem?.mp hi
  have hplain : ∀ i ∈ r.code, PlainTag i := fun i hi => by
    obtain ⟨k, hk⟩ := hidx i hi
    exact (hE k i hk).1
  have hst : ∀ (k : Nat) (i : LinstrRM), r.code[k]? = some i → StraightOp i := fun k i hk =>
    straightOp_of_lopn (hsh i (List.mem_of_getElem? hk)) (hE k i hk).2.1
  have hself : ∀ (k : Nat) (i : LinstrRM) (d : String), r.code[k]? = some i →
      wrArr (fun _ => none) i = some d → d ∉ rdArr (fun _ _ => none) i := by
    intro k i d hi hd hr'
    have h1 := hW k d ⟨i, hi, hd⟩
    exact (hR k d (.inl ⟨i, hi, hr'⟩)).ne_regName le_rfl h1
  have hfix : ∀ y ∈ r.res.map operandName, webLook tab r.code.length y = y :=
    fun y hy => webB_exit hacc y (hobs y hy)
  have hhR : ∀ j y, ReadAt r.code (fun _ _ => none) (r.res.map operandName) j y →
      '#' ∉ y.toList := fun j y hy => (hR j y hy).hash_not_mem
  have hhW : ∀ k d, WrAt r.code (fun _ => none) k d → '#' ∉ d.toList := fun k d hd => by
    rw [hW k d hd]
    exact hash_not_mem_regName _
  have hssa : ∀ k₁ k₂ d, WrAt r.code (fun _ => none) k₁ d →
      WrAt r.code (fun _ => none) k₂ d →
      k₁ = k₂ := fun k₁ k₂ d h₁ h₂ => by
    have := JasminLsemSimulation.regName_injective ((hW k₁ d h₁).symm.trans (hW k₂ d h₂))
    omega
  have hA1 : ∀ (k : Nat) (i : LinstrRM), r.code[k]? = some i →
      wrArr (fun _ => none) i = none →
      ∀ M ρ, aliasStepO [] M (renArr ρ i) = M := fun k i hi => (hE k i hi).2.2.2.1
  have hA2 := fun k i d hi => (hE k i hi).2.2.2.2 d
  have hS := chainShape_webRen tab hacc hst hplain hself hfix hhR hhW hssa h1 h2 hx hC hA1 hA2
  have hal := getD_foldl_webRen tab hacc hst hplain hself hhW hssa hx hC.1 hA1 hA2
  have hAw0 : ∀ j w, ¬ WrAt r.code (fun _ => none) w (argName j) := fun j w hw =>
    JasminLsemSimulation.regName_ne_argName _ j (hW w _ hw).symm
  have hlen : ∀ w y, WrAt r.code (fun _ => none) w y → w < r.code.length := by
    rintro w y ⟨i, hi, -⟩
    exact (List.getElem?_eq_some_iff.mp hi).1
  refine chainShape_regionCoCode_root (z := webLook tab 0 x) hret (fun i hi => ?_) hS
    (fun w d hw => (hal d).1 w hw) (fun y hy => (hal y).2 hy) ?_ (fun j w hw => ?_)
    (fun j c hc => ?_) (fun j c i y k hi hy => ?_) (fun j w y k hw => ?_)
  · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hi
    rw [getElem?_webRen] at hk
    obtain ⟨i0, hi0, rfl⟩ := Option.map_eq_some_iff.mp hk
    exact zeroDst?_renArr _ (hE k i0 hi0).1 (hsh i0 (List.mem_of_getElem? hi0))
      (hE k i0 hi0).2.2.1
  · rcases hRet with hn0 | ⟨y, hy, w, hW⟩
    · left
      intro w d hw
      obtain ⟨d', hd', -⟩ := wrAt_webRen hplain hw
      exact hn0 w d' hd'
    · right
      refine ⟨y, hy, w, ?_⟩
      have hyobs : y ∈ r.res.map operandName := by rw [hy]; exact List.mem_singleton_self _
      have hw' := wrAt_webRen_of (w := webLook tab) hplain hW
      have hwl := hlen w y hW
      have hc := webB_const' hacc hst (a := w + 1) (r := y) r.code.length (by omega) le_rfl
        (webB_obs hacc y (hobs y hyobs)) (fun j' i' hj' _ hi' hw'' => by
          have := hssa j' w y ⟨i', hi', hw''⟩ hW
          omega)
      rw [hc.2, hfix y hyobs] at hw'
      exact hw'
  · obtain ⟨d, hd, he⟩ := wrAt_webRen hplain hw
    obtain rfl := webLook_eq_plain tab (hhW w d hd) (hash_not_mem_argName j) he.symm
    exact hAw0 j w hd
  · obtain ⟨y, hy, he⟩ := consumedAt_webRen hplain hself hc
    have hyn : '#' ∉ y.toList := by
      obtain ⟨i, d, hi, hr', -, -⟩ := hy
      exact hhR c y (.inl ⟨i, hi, hr'⟩)
    obtain rfl := webLook_eq_plain tab hyn (hash_not_mem_argName j) he.symm
    obtain rfl := consumed_argName_root hE hAw0 hy
    obtain ⟨i, d, hi, hr', -, -⟩ := hy
    have hlive := (webB_live hacc hi (hst c i hi).1).1 _ hr'
    have hc := webB_const' hacc hst (a := 0) (r := argName j) c (Nat.zero_le _)
      (List.getElem?_eq_some_iff.mp hi).1.le hlive
      (fun j' i' _ _ hi' hw' => hAw0 j j' ⟨i', hi', hw'⟩)
    rw [hc.2]
    exact he.symm
  · rw [getElem?_webRen] at hi
    obtain ⟨i0, hi0, rfl⟩ := Option.map_eq_some_iff.mp hi
    rw [(rdArr_wrArr_renArr _ i0 (hplain i0 (List.mem_of_getElem? hi0))).1] at hy
    obtain ⟨y0, hy0, rfl⟩ := List.mem_map.mp hy
    have hyn := hhR c y0 (.inl ⟨i0, hi0, hy0⟩)
    unfold stepRen
    split
    · exact (webLook_ne_copyName tab hyn (hash_not_mem_argName j) _ k).1
    · exact (webLook_ne_copyName tab hyn (hash_not_mem_argName j) _ k).1
  · obtain ⟨d, hd, rfl⟩ := wrAt_webRen hplain hw
    exact (webLook_ne_copyName tab (hhW w d hd) (hash_not_mem_argName j) _ k).1

end ExportGate

/-! ## 3. The field domain -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.ArrWebs (webLook webRen webB)
open CatCrypt.Crypto.Hax (HaxModule)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapDom (exportR_mnemDom
  shadowCall?_of_shapeB)

/-- **The webs of an export without callee** are the export, or its code renamed by the
    position map of web tables that `webB` accepts at the names `regionWebsObs`. -/
theorem regionWebsAt_cases (ex : List String) (r0 : Exported) :
    regionWebsAt ex none r0 = r0 ∨
      ∃ (tab : X86Backend.ArrWebs.WebSt × Std.HashSet Nat × Std.HashSet Nat)
        (L : Nat → List String),
        webB (webLook tab) r0.code L (regionWebsObs ex r0) (fun _ _ => none) (fun _ => none) = true
          ∧ regionWebsAt ex none r0 =
            { r0 with code := webRen (webLook tab) (fun _ => none) r0.code } := by
  rw [regionWebsAt_none]
  unfold regionWebs
  split
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    exact .inr ⟨_, _, hc.1, rfl⟩
  · exact .inl rfl

variable {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
  {r : Exported} {cert : List (String × String)}

/-- **Every member of the field domain has the store-chain shape `FieldChainShape`.** -/
theorem fieldDom_fieldChainShape (h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert) : FieldChainShape σ t r := by
  obtain ⟨t0, q, q', r0, P, hq, hq', hr0, rfl, -, -, rfl⟩ := hB
  have hL := fieldDom_legalize_loadsChain h hq hq'
  have hret : ∀ res, regionRet σ exportReg (NarrowWords.wideTy t0) res = none := by
    obtain ⟨-, R, n, hR⟩ := fieldDomB_abi h
    exact fun _ => regionRet_words hR
  have hE0 : regionExportableB q = true := fieldDom_exportable (fieldDom_refusal h) hq
  obtain ⟨q'', hq'', hE1⟩ := NarrowWords.narrowPrep_of_exportable q hE0
  rw [hq'] at hq''
  cases hq''
  have hcf : (legalizeRegion q').callFree = true :=
    legalizeRegion_callFree ((NarrowWords.callFree_narrowPrep hq').trans (fieldDom_callFree h hq))
  have hsh : ∀ i ∈ r0.code, LprogIsa.shadowCall? i.1 = none := fun i hi =>
    shadowCall?_of_shapeB (exportR_mnemDom _ _ _ (fieldDom_legalize hE1) hcf _ _ _ hr0 i hi).2.2
  unfold FieldChainShape
  rcases regionWebsAt_cases (regionWebsEx σ exportReg) r0 with he | ⟨tab, L, hacc, he⟩
  · rw [he]
    exact chainShape_regionCoCode_export hL le_rfl hr0 (hret _)
  · rw [he]
    dsimp only
    exact chainShape_regionCoCode_webs tab hL le_rfl hr0 hsh hacc
      (fun y hy => by unfold regionWebsObs; exact List.mem_append_left _ hy) (hret _)

/-- **Stage `G2` on the field domain**: the gate does not refuse at `coCfgB`. -/
theorem fieldDom_coCfgB' (h : fieldDomB e σ = true) (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "coCfgB" :=
  fieldDom_coCfgB_of_chainShape (fun h' hB' => fieldDom_fieldChainShape h' hB') h hB

/-- **Stage `G3` on the field domain**: the gate does not refuse at `coEntryFix`. -/
theorem fieldDom_coEntryFix' (h : fieldDomB e σ = true) (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "coEntryFix" :=
  fieldDom_coEntryFix_of_chainShape (fun h' hB' => fieldDom_fieldChainShape h' hB') h hB

example (S : FieldDomStages) : type_of% @S.coCfgB := @fieldDom_coCfgB'

example (S : FieldDomStages) : type_of% @S.coEntryFix := @fieldDom_coEntryFix'

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
