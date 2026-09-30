/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanon
public import CatCrypt.Crypto.SecureCompilation.VIR.LoopNameDistinct
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLift

@[expose] public section

set_option autoImplicit false

/-!
# Boolean certificates for the export of a runtime-count loop node

`JasminLsemMemSourceTieEmitted.forLoopLcmdNRtRM_export_faithful_comL` states that the
renamed export node of an `ArrMemN` update realises `ComL.forLoopNRt`, under a loop renaming
`σ` (`LoopRen`), a node renaming `ρ` (`NodeRen`), the return condition `hret`, and the
canonicalisation certificates `CanonRen (ρ ∘ σ)` and `ThreadCert (ρ ∘ σ)`. This module fixes
the two renamings as functions of the node's names and computes the certificates with a
Boolean check.

* `certSigma d nInv acc invRegs` is the loop renaming: the accumulator argument to `acc`, the
  index argument to the loop index, the invariant arguments to their base registers, each
  chain register to the body temporary of its slot, every other name to itself.
* `certRho d acc out Sl` is the node renaming: `acc` and the body temporaries of the store
  slots `Sl` to `out`, every other name to itself.
* `storeSlots` computes the store slots of the model chain.
* `threadCertB` decides `ThreadCert` for a renaming given by a partial computable function
  (`sigmaC` composed with `certRho`) on the names the chain reads as arrays.
* `exportCertB` is the conjunction of the name-distinctness checks, the return condition and
  `threadCertB` on the model chain of the update.

No name is fixed to a program: every statement is over the loop depth, the accumulator,
output and count registers, the invariant operands and the update.

## Main results

* `certSigma_loopRen` — `certSigma` is a `LoopRen`.
* `resolvedB_sound`, `sigmaC_sound`, `threadCertB_sound` — soundness of the pieces.
* `exportCertB_sound` — an accepted node has `LoopRen`, `NodeRen`, the return condition,
  `CanonRen` and `ThreadCert` at the two computed renamings, with the store-slot set `Sl`.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCert

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanon
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLift (invRegsOf)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond (accRegMN)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond (loopBodyRetArrMN)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation
  (argName_injective argName_ne regName_injective regName_ne_argName)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (ne_empty_of_head?)
open CatCrypt.Crypto.SecureCompilation.VIR.LoopNameDistinct
  (loopIdx_ne_loopReg loopCtr_ne_loopReg loopIdx_ne_loopCtr)

/-! ## 1. The two renamings -/

/-- The node renaming: the accumulator register `acc` and the body temporaries of the store
    slots `Sl` go to `out`, every other name to itself. -/
def certRho (d : Nat) (acc out : String) (Sl : List Nat) (r : String) : String :=
  if (r == acc || Sl.any (fun k => r == loopReg d k)) = true then out else r

theorem certRho_acc (d : Nat) (acc out : String) (Sl : List Nat) :
    certRho d acc out Sl acc = out := by
  simp [certRho]

theorem certRho_slot {d : Nat} {acc out : String} {Sl : List Nat} {k : Nat} (hk : k ∈ Sl) :
    certRho d acc out Sl (loopReg d k) = out := by
  unfold certRho
  rw [if_pos]
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
  exact Or.inr ⟨k, hk, by simp⟩

theorem certRho_fix {d : Nat} {acc out : String} {Sl : List Nat} {r : String} (h1 : r ≠ acc)
    (h2 : ∀ k ∈ Sl, r ≠ loopReg d k) : certRho d acc out Sl r = r := by
  unfold certRho
  rw [if_neg]
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, not_or, not_exists, not_and]
  exact ⟨h1, fun k hk he => h2 k hk (by simpa using he)⟩

theorem certRho_self (d : Nat) (acc out : String) (Sl : List Nat) :
    certRho d acc out Sl out = out := by
  unfold certRho
  split <;> rfl

attribute [local instance] Classical.propDecidable in
/-- The loop renaming: the accumulator argument `argName (nInv + 1)` to `acc`, the index
    argument `argName nInv` to the loop index, an invariant argument `argName j` to its base
    register in `invRegs` (in the order `LoopRen.inv` reads them), a chain register
    `regName k` to the body temporary `loopReg d k`, every other name to itself. -/
noncomputable def certSigma (d nInv : Nat) (acc : String) (invRegs : List String)
    (r : String) : String :=
  if r = argName (nInv + 1) then acc
  else if r = argName nInv then loopIdx d
  else if h : ∃ j, j < nInv ∧ r = argName j then
    invRegs.getD (nInv - 1 - h.choose) ("Linv" ++ toString d ++ "_" ++ toString h.choose)
  else if h : ∃ k, r = regName k then loopReg d h.choose
  else r

section Sigma

variable {d nInv : Nat} {acc : String} {invRegs : List String}

theorem certSigma_acc : certSigma d nInv acc invRegs (argName (nInv + 1)) = acc := by
  simp [certSigma]

theorem certSigma_idx : certSigma d nInv acc invRegs (argName nInv) = loopIdx d := by
  simp [certSigma, argName_ne (show nInv ≠ nInv + 1 by omega)]

theorem certSigma_inv {j : Nat} (hj : j < nInv) : certSigma d nInv acc invRegs (argName j)
    = invRegs.getD (nInv - 1 - j) ("Linv" ++ toString d ++ "_" ++ toString j) := by
  have hex : ∃ j', j' < nInv ∧ argName j = argName j' := ⟨j, hj, rfl⟩
  rw [certSigma, if_neg (argName_ne (by omega)), if_neg (argName_ne (by omega)), dif_pos hex]
  have := argName_injective hex.choose_spec.2
  rw [← this]

theorem certSigma_reg (k : Nat) : certSigma d nInv acc invRegs (regName k) = loopReg d k := by
  have hex : ∃ k', regName k = regName k' := ⟨k, rfl⟩
  have hna : ¬ ∃ j, j < nInv ∧ regName k = argName j := fun ⟨j, _, h⟩ =>
    regName_ne_argName k j h
  rw [certSigma, if_neg (regName_ne_argName k _), if_neg (regName_ne_argName k _), dif_neg hna,
    dif_pos hex, regName_injective hex.choose_spec.symm]

theorem certSigma_other {r : String} (ha : ∀ j, r ≠ argName j) (hr : ∀ k, r ≠ regName k) :
    certSigma d nInv acc invRegs r = r := by
  rw [certSigma, if_neg (ha _), if_neg (ha _), dif_neg (fun ⟨j, _, h⟩ => ha j h),
    dif_neg (fun ⟨k, h⟩ => hr k h)]

/-- `certSigma` is the export's loop renaming. -/
theorem certSigma_loopRen (hlen : invRegs.length = nInv) :
    LoopRen (certSigma d nInv acc invRegs) d nInv acc invRegs where
  acc := certSigma_acc
  idx := certSigma_idx
  inv := fun _ hj => certSigma_inv hj
  reg := certSigma_reg
  len := hlen

end Sigma

/-! ## 2. The thread certificate, decided -/

/-- `certSigma` on the argument names below `nInv + 2` and the chain registers below
    `bound`, and `none` elsewhere. -/
def sigmaC (d nInv : Nat) (acc : String) (invRegs : List String) (bound : Nat) (b : String) :
    Option String :=
  if b == argName (nInv + 1) then some acc
  else if b == argName nInv then some (loopIdx d)
  else match (List.range nInv).find? (fun j => b == argName j) with
    | some j => some (invRegs.getD (nInv - 1 - j) ("Linv" ++ toString d ++ "_" ++ toString j))
    | none => match (List.range bound).find? (fun k => b == regName k) with
      | some k => some (loopReg d k)
      | none => none

theorem sigmaC_sound {d nInv : Nat} {acc : String} {invRegs : List String} {bound : Nat}
    {b t : String} (h : sigmaC d nInv acc invRegs bound b = some t) :
    certSigma d nInv acc invRegs b = t := by
  unfold sigmaC at h
  by_cases h1 : b = argName (nInv + 1)
  · subst h1; simp only [beq_self_eq_true, if_true, Option.some.injEq] at h
    rw [certSigma_acc, h]
  rw [if_neg (by simpa using h1)] at h
  by_cases h2 : b = argName nInv
  · subst h2; simp only [beq_self_eq_true, if_true, Option.some.injEq] at h
    rw [certSigma_idx, h]
  rw [if_neg (by simpa using h2)] at h
  cases hf : (List.range nInv).find? (fun j => b == argName j) with
  | some j =>
      rw [hf] at h
      obtain rfl := Option.some.inj h
      have hb : b = argName j := by simpa using List.find?_some hf
      have hj : j < nInv := List.mem_range.mp (List.mem_of_find?_eq_some hf)
      subst hb
      exact certSigma_inv hj
  | none =>
      rw [hf] at h
      cases hg : (List.range bound).find? (fun k => b == regName k) with
      | none => rw [hg] at h; cases h
      | some k =>
          rw [hg] at h
          obtain rfl := Option.some.inj h
          have hb : b = regName k := by simpa using List.find?_some hg
          subst hb
          exact certSigma_reg k

/-- A decision of `Resolved nArgs cd n`. -/
def resolvedB (nArgs cd : Nat) (n : String) : Bool :=
  n == "" || (List.range nArgs).any (fun j => n == argName j)
    || (List.range cd).any (fun k => decide (nArgs ≤ k) && n == regName k)

theorem resolvedB_sound {nArgs cd : Nat} {n : String} (h : resolvedB nArgs cd n = true) :
    Resolved nArgs cd n := by
  unfold resolvedB at h
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at h
  rcases h with (h | ⟨j, hj, h⟩) | ⟨k, hk, hk', h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨j, hj, h⟩)
  · exact Or.inr (Or.inr ⟨k, hk', hk, h⟩)

/-- A decision of `ThreadCert τ nArgs (· ∈ Sl) out`, for a renaming `τ` that `tauC` computes
    on the array names the chain reads: every read name is resolved, an array read whose
    image is `out` reads the thread head, and each instruction is either a register binding
    of a slot outside `Sl` or a store of a slot in `Sl`. -/
def threadCertB (tauC : String → Option String) (nArgs : Nat) (Sl : List Nat) (out : String) :
    List LinstrRM → Nat → String → String → Bool
  | [], _, h, hE => h == hE
  | i :: is, cd, h, hE =>
      (useNames i.1).all (resolvedB nArgs cd)
      && (match arrUse? i with
          | none => true
          | some b => b == h || (match tauC b with | some t => t != out | none => false))
      && (match storeHit? i with
          | none => defNames i.1 == [regName cd] && !(Sl.contains cd)
              && threadCertB tauC nArgs Sl out is (cd + 1) h hE
          | some x => x == regName cd && Sl.contains cd
              && threadCertB tauC nArgs Sl out is (cd + 1) (regName cd) hE)

theorem threadCertB_sound {tauC : String → Option String} {τ : String → String}
    (hτ : ∀ b t, tauC b = some t → τ b = t) {nArgs : Nat} {Sl : List Nat} {out : String} :
    ∀ (chain : List LinstrRM) (cd : Nat) (h hE : String),
      threadCertB tauC nArgs Sl out chain cd h hE = true →
      ThreadCert τ nArgs (· ∈ Sl) out chain cd h hE := by
  intro chain
  induction chain with
  | nil =>
      intro cd h hE hc
      exact (by simpa [threadCertB] using hc : h = hE)
  | cons i is ih =>
      intro cd h hE hc
      simp only [threadCertB, Bool.and_eq_true, List.all_eq_true] at hc
      obtain ⟨⟨hu, harr⟩, hst⟩ := hc
      refine ⟨fun n hn => resolvedB_sound (hu n hn), ?_, ?_⟩
      · intro b hb hbo
        rw [hb] at harr
        simp only [Bool.or_eq_true, beq_iff_eq] at harr
        rcases harr with harr | harr
        · exact harr
        · cases ht : tauC b with
          | none => rw [ht] at harr; cases harr
          | some t =>
              rw [ht] at harr
              rw [hτ b t ht] at hbo
              simp [hbo] at harr
      · cases hs : storeHit? i with
        | none =>
            rw [hs] at hst
            simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hst
            obtain ⟨⟨hd, hS⟩, hr⟩ := hst
            exact Or.inl ⟨rfl, hd, fun hm => by simp at hS; exact hS hm,
              ih (cd + 1) h hE hr⟩
        | some x =>
            rw [hs] at hst
            simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hst
            obtain ⟨⟨rfl, hS⟩, hr⟩ := hst
            exact Or.inr ⟨rfl, hS, ih (cd + 1) _ hE hr⟩

/-- The chain slots, from depth `cd`, whose instruction is a store. -/
def storeSlots : List LinstrRM → Nat → List Nat
  | [], _ => []
  | i :: is, cd => (if (storeHit? i).isSome then [cd] else []) ++ storeSlots is (cd + 1)

/-! ## 3. The certificate of a loop node -/

/-- A name whose first character is not `L` is no body temporary. -/
def notLoopRegB (r : String) : Bool := r.toList.head? != some 'L'

theorem ne_loopReg_of_notLoopRegB {r : String} (h : notLoopRegB r = true) (d k : Nat) :
    r ≠ loopReg d k := by
  intro he
  subst he
  simp [notLoopRegB, head?_loopReg] at h

/-- `certRho d acc out Sl` fixes `r`: `r` is neither `acc` nor a store slot's body
    temporary. -/
def fixB (d : Nat) (acc : String) (Sl : List Nat) (r : String) : Bool :=
  r != acc && Sl.all (fun k => r != loopReg d k)

theorem certRho_of_fixB {d : Nat} {acc out : String} {Sl : List Nat} {r : String}
    (h : fixB d acc Sl r = true) : certRho d acc out Sl r = r := by
  simp only [fixB, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true] at h
  exact certRho_fix h.1 fun k hk => h.2 k hk

section Cert

variable {w n : Nat} {invTys : Ctxt jasminDialect}

/-- The model chain of an update, at the argument count of its loop. -/
abbrev certChain (update : Com jasminDialect
    (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n)) :
    List LinstrRM :=
  straightOpsMem (invTys.length + 2) update (invTys.length + 2)

/-- The store slots of the model chain of an update. -/
abbrev certSlots (update : Com jasminDialect
    (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n)) :
    List Nat :=
  storeSlots (certChain update) (invTys.length + 2)

/-- **The export certificate of a loop node** at depth `d`, accumulator register `acc`,
    output register `out`, count register `c` and invariant operands `invOps`: one base
    register per invariant; `acc`, `out` and every invariant base register are no body
    temporary; `certRho` fixes the loop index, the counter, `c` and the invariant base
    registers; `out`, the loop index, the counter and the invariant base registers are
    pairwise distinct as `CanonRen` asks; `certRho` sends the body walk's return register to
    `out`; and the model chain has a thread certificate from the accumulator argument to
    the chain's return array, with the computed store slots. -/
def exportCertB (d : Nat) (acc out c : String)
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (invOps : List LOperand) : Bool :=
  let nInv := invTys.length
  let invRegs := invRegsOf invOps
  let Sl := certSlots update
  (invRegs.length == nInv)
  && acc != "" && notLoopRegB acc
  && notLoopRegB out && out != loopIdx d && out != loopCtr d
  && fixB d acc Sl (loopIdx d) && fixB d acc Sl (loopCtr d) && fixB d acc Sl c
  && c != loopIdx d
  && invRegs.all (fun r => notLoopRegB r && fixB d acc Sl r && r != out && r != loopIdx d
      && r != loopCtr d)
  && certRho d acc out Sl
      (loopBodyWalkN d acc (loopIdx d) invRegs (fun _ => none) update (2 + nInv)).2 == out
  && threadCertB
      (fun b => (sigmaC d nInv acc invRegs ((certChain update).length + nInv + 2) b).map
        (certRho d acc out Sl))
      (nInv + 2) Sl out (certChain update) (nInv + 2) (accRegMN invTys)
      (loopBodyRetArrMN update)

/-- The facts `forLoopLcmdNRtRM_export_faithful_comL` asks of the renamings, at the loop
    renaming `σ`, the node renaming `ρ` and the store-slot list `Sl`. -/
structure ExportCert (d : Nat) (acc out c : String)
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (invOps : List LOperand) (σ ρ : String → String) (Sl : List Nat) : Prop where
  /-- The loop renaming. -/
  loopRen : LoopRen σ d invTys.length acc (invRegsOf invOps)
  /-- The node renaming. -/
  nodeRen : NodeRen ρ d acc out c (invRegsOf invOps)
  /-- The body walk's return register goes to `out`. -/
  ret : ρ (loopBodyWalkN d acc (loopIdx d) (invRegsOf invOps) (fun _ => none) update
      (2 + invTys.length)).2 = out
  /-- The canonicalisation renaming. -/
  canon : CanonRen (ρ ∘ σ) d invTys.length (· ∈ Sl) out
  /-- The thread certificate of the model chain. -/
  thread : ThreadCert (ρ ∘ σ) (invTys.length + 2) (· ∈ Sl) out
      (straightOpsMem (invTys.length + 2) update (invTys.length + 2)) (invTys.length + 2)
      (accRegMN invTys) (loopBodyRetArrMN update)
  /-- The count register is not the loop index. -/
  cntIdx : c ≠ loopIdx d

theorem getD_mem_of_lt {l : List String} {i : Nat} (hi : i < l.length) (dflt : String) :
    l.getD i dflt ∈ l := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

/-- **Soundness of the export certificate.** An accepted loop node has the loop renaming
    `certSigma`, the node renaming `certRho` over the computed store slots, and every
    renaming hypothesis of `forLoopLcmdNRtRM_export_faithful_comL` at them. -/
theorem exportCertB_sound {d : Nat} {acc out c : String}
    {update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n)}
    {invOps : List LOperand} (h : exportCertB d acc out c update invOps = true) :
    ExportCert d acc out c update invOps
      (certSigma d invTys.length acc (invRegsOf invOps))
      (certRho d acc out (certSlots update)) (certSlots update) := by
  simp only [exportCertB, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hlen, hacc⟩, haccL⟩, houtL⟩, houtI⟩, houtC⟩, hfI⟩, hfC⟩, hfc⟩, hcI⟩,
    hinv⟩, hret⟩, hthr⟩ := h
  set Sl := certSlots update
  set σ := certSigma d invTys.length acc (invRegsOf invOps)
  set ρ := certRho d acc out Sl
  have hinv' : ∀ r ∈ invRegsOf invOps, notLoopRegB r = true ∧ ρ r = r ∧ r ≠ out
      ∧ r ≠ loopIdx d ∧ r ≠ loopCtr d := by
    intro r hr
    have := hinv r hr
    exact ⟨this.1.1.1.1, certRho_of_fixB this.1.1.1.2, this.1.1.2, this.1.2, this.2⟩
  have hσacc : σ (argName (invTys.length + 1)) = acc := certSigma_acc
  have hσidx : σ (argName invTys.length) = loopIdx d := certSigma_idx
  have hσreg : ∀ k, σ (regName k) = loopReg d k := certSigma_reg
  have hρacc : ρ acc = out := certRho_acc d acc out Sl
  have hσinv : ∀ j, j < invTys.length → σ (argName j) ∈ invRegsOf invOps := by
    intro j hj
    show certSigma _ _ _ _ _ ∈ _
    rw [certSigma_inv hj]
    exact getD_mem_of_lt (by rw [hlen]; omega) _
  have hidx : ρ (loopIdx d) = loopIdx d := certRho_of_fixB hfI
  have hctr : ρ (loopCtr d) = loopCtr d := certRho_of_fixB hfC
  have hσctr : σ (loopCtr d) = loopCtr d :=
    certSigma_other (fun j => loopCtr_ne_argName d j) (fun k => loopCtr_ne_regName d k)
  have hempty : (ρ ∘ σ) "" = "" := by
    show ρ (σ "") = ""
    rw [show σ "" = "" from certSigma_other
      (fun j he => ne_empty_of_head? (head?_argName j) he.symm)
      (fun k he => ne_empty_of_head? (head?_regName k) he.symm)]
    exact certRho_fix (fun he => hacc he.symm)
      (fun k _ he => ne_empty_of_head? (head?_loopReg d k) he.symm)
  refine
    { loopRen := certSigma_loopRen hlen
      nodeRen := ?_
      ret := hret
      canon := ?_
      thread := threadCertB_sound (τ := ρ ∘ σ) (fun b t hb => ?_) _ _ _ _ hthr
      cntIdx := hcI }
  · exact
      { accOut := certRho_acc d acc out Sl
        outFix := certRho_self d acc out Sl
        idxFix := hidx
        ctrFix := hctr
        cntFix := certRho_of_fixB hfc
        invFix := fun r hr => (hinv' r hr).2.1 }
  · exact
      { fix := hempty
        tmp := fun k _ hS => by
          show ρ (σ (regName k)) = _
          rw [hσreg]
          exact certRho_fix (ne_loopReg_of_notLoopRegB haccL d k).symm
            (fun k' hk' he => hS (by rw [loopReg_injective d he]; exact hk'))
        thr := fun k _ hS => by
          show ρ (σ (regName k)) = _
          rw [hσreg]
          exact certRho_slot hS
        arg := fun j k hj => by
          show ρ (σ (argName j)) ≠ _
          by_cases h1 : j = invTys.length + 1
          · subst h1
            rw [hσacc, hρacc]
            exact ne_loopReg_of_notLoopRegB houtL d k
          by_cases h2 : j = invTys.length
          · subst h2
            rw [hσidx, hidx]
            exact loopIdx_ne_loopReg d d k
          have hj' : j < invTys.length := by omega
          have hm := hσinv j hj'
          rw [(hinv' _ hm).2.1]
          exact ne_loopReg_of_notLoopRegB (hinv' _ hm).1 d k
        outL := ne_loopReg_of_notLoopRegB houtL d
        acc := by
          show ρ (σ (argName (invTys.length + 1))) = _
          rw [hσacc, hρacc]
        idx := by
          show ρ (σ (argName invTys.length)) = _
          rw [hσidx, hidx]
        ctr := by
          show ρ (σ (loopCtr d)) = _
          rw [hσctr, hctr]
        argOut := fun j hj => by
          show ρ (σ (argName j)) ≠ _
          by_cases h2 : j = invTys.length
          · subst h2
            rw [hσidx, hidx]
            exact fun he => houtI he.symm
          have hm := hσinv j (by omega)
          rw [(hinv' _ hm).2.1]
          exact (hinv' _ hm).2.2.1
        invIdx := fun j hj => by
          show ρ (σ (argName j)) ≠ _
          have hm := hσinv j hj
          rw [(hinv' _ hm).2.1]
          exact (hinv' _ hm).2.2.2.1
        invCtr := fun j hj => by
          show ρ (σ (argName j)) ≠ _
          have hm := hσinv j hj
          rw [(hinv' _ hm).2.1]
          exact (hinv' _ hm).2.2.2.2
        outIdx := houtI
        outCtr := houtC
        idxCtr := loopIdx_ne_loopCtr d
        ctrL := loopCtr_ne_loopReg d d }
  · obtain ⟨t0, ht0, rfl⟩ := Option.map_eq_some_iff.mp hb
    exact congrArg ρ (sigmaC_sound ht0)

end Cert

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCert
