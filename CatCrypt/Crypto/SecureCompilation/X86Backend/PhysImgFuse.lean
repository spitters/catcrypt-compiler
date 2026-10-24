/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgPass
public import CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi

/-!
# The image class under the high-product fusion

The fusion `FuseMulHi.fuseMulHiAux` reads a body from left to right and rewrites a
`MULXHI` that pairs with a pending low `MUL` into a sequence of moves around a two-output
`MULX` (a fusion site); every other instruction passes unchanged. A site has no indexed
access, and its destinations are the reload scratches `R15` and `R14`, `RDX`, the high
destination of the `MULXHI` and the home of the paired low `MUL`
(`fuseMulHiAux_cons_step`).

A site keeps the class `physImgB slotArr` by `PhysImgPass.physImgB_replace` when the rest of
the body behind it writes no array slot and no reload scan of a base of the rest leaves the
rest (`fuseSiteOkB`), and when no destination of the site is an array slot. The home of a
low `MUL` is read through the scratch environment of the fusion; `homeOkB` checks it along
the environment of the unfused body, which agrees with the fused one up to names of reload
scratches (`EnvAgree`).

## Main results

* `scratchResolve_scratchBind`, `scratchResolve_scratchKill`, `scratchResolve_scratchStep`:
  the name a scratch environment resolves after one update.
* `EnvAgree.step`, `EnvAgree.killAll`: the agreement of two environments is kept by a common
  step and by forgetting scratches on the left.
* `fuseMulHiAux_cons_step`: one step of the fusion passes its instruction, or rewrites a
  `MULXHI` into a site without access whose destinations are scratches, `RDX`, the high
  destination and a pending home.
* `physImgB_fuseMulHiAux`, `physImgB_fuseMulHiBody`: the fused body of a body in the class
  is in the class under `fuseSiteOkB` and `homeOkB`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgFuse

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgPass
open CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi

/-! ## 1. Scratch environments -/

theorem find?_filter_ne (e : ScratchEnv) {dn r : String} (h : ¬ r = dn) :
    (e.filter (fun p => p.1 != dn)).find? (fun p => p.1 == r) =
      e.find? (fun p => p.1 == r) := by
  induction e with
  | nil => rfl
  | cons p e ih =>
    by_cases hp : p.1 = dn
    · have : (dn == r) = false := by simp [Ne.symm h]
      simp [hp, this, ih]
    · simp [hp, List.find?_cons, ih]

theorem scratchResolve_scratchBind (e : ScratchEnv) (dn v r : String) :
    scratchResolve (scratchBind e dn v) r = if r = dn then v else scratchResolve e r := by
  unfold scratchResolve scratchBind
  by_cases h : r = dn
  · subst h; simp
  · simp [h, Ne.symm h, find?_filter_ne e h]

theorem scratchResolve_scratchKill (e : ScratchEnv) (dn r : String) :
    scratchResolve (scratchKill e dn) r = if r = dn then r else scratchResolve e r := by
  unfold scratchResolve scratchKill
  by_cases h : r = dn
  · subst h
    have : (e.filter (fun p => p.1 != r)).find? (fun p => p.1 == r) = none := by
      rw [List.find?_eq_none]
      intro p hp
      have := (List.mem_filter.mp hp).2
      simpa using this
    simp [this]
  · simp [h, find?_filter_ne e h]

/-- A scratch environment that records only the reserved reload scratches (the statement
    `PhysAbiShape.EnvScratch`, whose module lies above this one). -/
def EnvScratch (env : ScratchEnv) : Prop := ∀ p ∈ env, p.1 ∈ fuseReloadScratches

theorem scratchResolve_of_envScratch {env : ScratchEnv} (h : EnvScratch env) {r : String}
    (hr : r ∉ fuseReloadScratches) : scratchResolve env r = r := by
  unfold scratchResolve
  split
  · rename_i p v hp
    obtain ⟨hmem, heq⟩ := List.mem_of_find?_eq_some hp, List.find?_some hp
    have : p = r := by simpa using heq
    exact absurd (this ▸ h _ hmem) hr
  · rfl

/-- The update of one destination in `scratchStep`, at the environment `env` in front of the
    instruction. -/
def stepUpd (env : ScratchEnv) (opn : String) (srcs : List LOperand) (e : ScratchEnv)
    (d : LOperand) : ScratchEnv :=
  match d with
  | .reg dn =>
      if fuseReloadScratches.contains dn then
        match srcs with
        | [.reg sn] =>
            if "MOV".isPrefixOf (stripWidthTag opn) then
              scratchBind e dn (scratchResolve env sn)
            else scratchKill e dn
        | _ => scratchKill e dn
      else e
  | _ => e

theorem scratchStep_eq (env : ScratchEnv) (i : Linstr) :
    scratchStep env i = match i.li_i with
      | .Lopn dsts opn srcs => dsts.foldl (stepUpd env opn srcs) env
      | _ => env := by
  unfold scratchStep stepUpd
  rfl

/-- The name a scratch receives from an instruction with sources `srcs` under the mnemonic
    `opn`: the resolved source of a move, the scratch itself otherwise. -/
def stepVal (env : ScratchEnv) (opn : String) (srcs : List LOperand) (r : String) : String :=
  match srcs with
  | [.reg sn] => if "MOV".isPrefixOf (stripWidthTag opn) then scratchResolve env sn else r
  | _ => r

theorem scratchResolve_stepUpd (env : ScratchEnv) (opn : String) (srcs : List LOperand)
    (e : ScratchEnv) (d : LOperand) (r : String) :
    (d = .reg r ∧ r ∈ fuseReloadScratches →
      scratchResolve (stepUpd env opn srcs e d) r = stepVal env opn srcs r) ∧
    (¬ (d = .reg r ∧ r ∈ fuseReloadScratches) →
      scratchResolve (stepUpd env opn srcs e d) r = scratchResolve e r) := by
  constructor
  · rintro ⟨rfl, hr⟩
    have hc : fuseReloadScratches.contains r = true := by simpa using hr
    unfold stepUpd stepVal
    simp only [hc, ite_true]
    split
    · split <;> simp [scratchResolve_scratchBind, scratchResolve_scratchKill]
    · simp [scratchResolve_scratchKill]
  · intro hn
    unfold stepUpd
    cases d with
    | reg dn =>
      by_cases hc : fuseReloadScratches.contains dn = true
      · have hne : r ≠ dn := by
          rintro rfl
          exact hn ⟨rfl, by simpa using hc⟩
        simp only [hc, ite_true]
        split
        · split <;> simp [scratchResolve_scratchBind, scratchResolve_scratchKill, hne]
        · simp [scratchResolve_scratchKill, hne]
      · have hc' : dn ∉ fuseReloadScratches := by simpa using hc
        simp [hc']
    | _ => rfl

theorem scratchResolve_foldl_stepUpd (env : ScratchEnv) (opn : String) (srcs : List LOperand)
    (r : String) : ∀ (ds : List LOperand) (e : ScratchEnv),
    (LOperand.reg r ∈ ds ∧ r ∈ fuseReloadScratches →
      scratchResolve (ds.foldl (stepUpd env opn srcs) e) r = stepVal env opn srcs r) ∧
    (¬ (LOperand.reg r ∈ ds ∧ r ∈ fuseReloadScratches) →
      scratchResolve (ds.foldl (stepUpd env opn srcs) e) r = scratchResolve e r)
  | [], e => ⟨fun h => by simp at h, fun _ => rfl⟩
  | d :: ds, e => by
    obtain ⟨ih1, ih2⟩ := scratchResolve_foldl_stepUpd env opn srcs r ds
      (stepUpd env opn srcs e d)
    obtain ⟨h1, h2⟩ := scratchResolve_stepUpd env opn srcs e d r
    simp only [List.foldl_cons, List.mem_cons]
    refine ⟨fun ⟨hm, hr⟩ => ?_, fun hn => ?_⟩
    · by_cases hds : LOperand.reg r ∈ ds
      · exact ih1 ⟨hds, hr⟩
      · rw [ih2 (fun h => hds h.1)]
        rcases hm with hm | hm
        · exact h1 ⟨hm.symm, hr⟩
        · exact absurd hm hds
    · have hds : ¬ (LOperand.reg r ∈ ds ∧ r ∈ fuseReloadScratches) :=
        fun h => hn ⟨Or.inr h.1, h.2⟩
      rw [ih2 hds]
      exact h2 fun h => hn ⟨Or.inl h.1.symm, h.2⟩

/-- **The name resolved after one step.** A reserved scratch named among the destinations of
    an operation resolves to the name the operation moves into it (`stepVal`); every other
    name resolves as in front of the instruction. -/
theorem scratchResolve_scratchStep (env : ScratchEnv) (i : Linstr) (r : String) :
    (∀ ds opn srcs, i.li_i = .Lopn ds opn srcs → LOperand.reg r ∈ ds →
      r ∈ fuseReloadScratches →
      scratchResolve (scratchStep env i) r = stepVal env opn srcs r) ∧
    ((∀ ds opn srcs, i.li_i = .Lopn ds opn srcs →
      ¬ (LOperand.reg r ∈ ds ∧ r ∈ fuseReloadScratches)) →
      scratchResolve (scratchStep env i) r = scratchResolve env r) := by
  rw [scratchStep_eq]
  constructor
  · intro ds opn srcs hi hm hr
    rw [hi]
    exact (scratchResolve_foldl_stepUpd env opn srcs r ds env).1 ⟨hm, hr⟩
  · intro hn
    split
    · rename_i ds opn srcs hi
      exact (scratchResolve_foldl_stepUpd env opn srcs r ds env).2 (hn ds opn srcs hi)
    · rfl

theorem EnvScratch.kill {env : ScratchEnv} (h : EnvScratch env) (dst : String) :
    EnvScratch (scratchKill env dst) := fun p hp =>
  h p (List.mem_of_mem_filter hp)

theorem EnvScratch.killAll {env : ScratchEnv} (h : EnvScratch env) :
    ∀ ks : List String, EnvScratch (ks.foldl scratchKill env)
  | [] => h
  | k :: ks => EnvScratch.killAll (h.kill k) ks

theorem EnvScratch.step {env : ScratchEnv} (h : EnvScratch env) (i : Linstr) :
    EnvScratch (scratchStep env i) := by
  rw [scratchStep_eq]
  split
  · rename_i ds opn srcs _
    suffices ∀ (ds : List LOperand) (e : ScratchEnv), EnvScratch e →
        EnvScratch (ds.foldl (stepUpd env opn srcs) e) from this ds env h
    intro ds
    induction ds with
    | nil => exact fun _ he => he
    | cons d ds ih =>
      intro e he
      refine ih _ ?_
      unfold stepUpd
      cases d with
      | reg dn =>
        by_cases hc : fuseReloadScratches.contains dn = true
        · simp only [hc, ite_true]
          have hb : ∀ v, EnvScratch (scratchBind e dn v) := by
            intro v p hp
            simp only [scratchBind, List.mem_cons] at hp
            rcases hp with rfl | hp
            · simpa using hc
            · exact he p (List.mem_of_mem_filter hp)
          split
          · split
            · exact hb _
            · exact he.kill dn
          · exact he.kill dn
        · simp only [hc]; exact he
      | _ => exact he
  · exact h

/-- Two scratch environments agree up to reserved scratches: every name resolves under the
    left one as under the right one, or to a reserved reload scratch. -/
def EnvAgree (ef ep : ScratchEnv) : Prop :=
  ∀ r, scratchResolve ef r = scratchResolve ep r ∨ scratchResolve ef r ∈ fuseReloadScratches

theorem EnvAgree.refl (e : ScratchEnv) : EnvAgree e e := fun _ => Or.inl rfl

theorem EnvAgree.step {ef ep : ScratchEnv} (h : EnvAgree ef ep) (i : Linstr) :
    EnvAgree (scratchStep ef i) (scratchStep ep i) := by
  intro r
  by_cases hit : ∃ ds opn srcs, i.li_i = .Lopn ds opn srcs ∧ LOperand.reg r ∈ ds ∧
      r ∈ fuseReloadScratches
  · obtain ⟨ds, opn, srcs, hi, hm, hr⟩ := hit
    rw [(scratchResolve_scratchStep ef i r).1 ds opn srcs hi hm hr,
      (scratchResolve_scratchStep ep i r).1 ds opn srcs hi hm hr]
    unfold stepVal
    split
    · split
      · exact h _
      · exact Or.inl rfl
    · exact Or.inl rfl
  · have hn : ∀ ds opn srcs, i.li_i = .Lopn ds opn srcs →
        ¬ (LOperand.reg r ∈ ds ∧ r ∈ fuseReloadScratches) :=
      fun ds opn srcs hi hm => hit ⟨ds, opn, srcs, hi, hm⟩
    rw [(scratchResolve_scratchStep ef i r).2 hn, (scratchResolve_scratchStep ep i r).2 hn]
    exact h r

theorem EnvAgree.kill {ef ep : ScratchEnv} (h : EnvAgree ef ep) (hs : EnvScratch ef)
    (dn : String) : EnvAgree (scratchKill ef dn) ep := by
  intro r
  rw [scratchResolve_scratchKill]
  by_cases hr : r = dn
  · subst hr
    simp only [ite_true]
    by_cases hc : r ∈ fuseReloadScratches
    · exact Or.inr hc
    · have h1 := h r
      rw [scratchResolve_of_envScratch hs hc] at h1
      exact h1
  · simp only [hr, ite_false]; exact h r

theorem EnvAgree.killAll {ef ep : ScratchEnv} (h : EnvAgree ef ep) (hs : EnvScratch ef) :
    ∀ ks : List String, EnvAgree (ks.foldl scratchKill ef) ep
  | [] => h
  | k :: ks => EnvAgree.killAll (h.kill hs k) (hs.kill k) ks

/-! ## 2. One step of the fusion -/

/-- The block `L` written by a fusion site of a `MULXHI` with high destination `d`, paired with
    a low `MUL` of home `lo`: no instruction is an indexed access or a constant-index array
    write, and every destination of an operation is a register among the reload scratches,
    `RDX`, `d` and `lo`. -/
def SiteOut (d lo : String) (L : Lcmd) : Prop :=
  ∀ r ∈ L, isAccB r.li_i = false ∧ isArrImmB r.li_i = false ∧ ∀ ds o ss, r.li_i = .Lopn ds o ss → ∀ x ∈ ds,
    ∃ n, x = .reg n ∧ (n ∈ fuseReloadScratches ∨ n = "RDX" ∨ n = d ∨ n = lo)

theorem site_assoc {α : Type} (a b c e t : List α) (x y : α) :
    a ++ x :: (b ++ y :: ((c ++ e) ++ t)) = (a ++ x :: (b ++ y :: (c ++ e))) ++ t := by
  simp

theorem fuseMulHiAux_cons_step (s : Bool) (env : ScratchEnv) (pend : List (String × String))
    (i : Linstr) (rest : Lcmd) :
    ∃ L env' pend', fuseMulHiAux s env pend (i :: rest) = L ++ fuseMulHiAux s env' pend' rest ∧
      (∃ ks : List String, env' = ks.foldl scratchKill (scratchStep env i)) ∧
      ((L = [i] ∧ (pend' = pend ∨ ∃ d opn s1 s2,
          i.li_i = .Lopn [.reg d] opn [.reg s1, .reg s2] ∧ isLowMulMnem opn = true ∧
          pend' = ((if s then lowHome env d s2 else d), scratchResolve env s2) :: pend)) ∨
        ∃ d opn s1 s2, i.li_i = .Lopn [.reg d] opn [.reg s1, .reg s2] ∧
          isMulHiMnem opn = true ∧ (∀ p ∈ pend', p ∈ pend) ∧
          ∃ lo k, (lo, k) ∈ pend ∧ SiteOut d lo L) := by
  rw [fuseMulHiAux]
  split
  · rename_i d opn s1 s2 heq
    by_cases hlo : isLowMulMnem opn = true
    · simp only [hlo, ite_true]
      exact ⟨[i], _, _, rfl, ⟨[], rfl⟩, Or.inl ⟨rfl, Or.inr ⟨d, opn, s1, s2, heq, hlo, rfl⟩⟩⟩
    · simp only [hlo, ite_false, Bool.false_eq_true]
      by_cases hhi : isMulHiMnem opn = true
      · simp only [hhi, ite_true]
        split
        · rename_i before loDst k after hspan
          have hpe : pend = before ++ (loDst, k) :: after := by
            have := congrArg (fun q => q.1 ++ q.2) hspan
            simpa [List.span_eq_takeWhile_dropWhile, List.takeWhile_append_dropWhile] using this
          have hmem : (loDst, k) ∈ pend := by rw [hpe]; simp
          have hsub : ∀ p ∈ before ++ after, p ∈ pend := by
            intro p hp; rw [hpe]; simp at hp ⊢; tauto
          have hscr : ∀ n, n = reloadScratch ∨ n = reloadScratch2 → n ∈ fuseReloadScratches := by
            rintro n (rfl | rfl) <;> simp [fuseReloadScratches]
          split
          · split
            · refine ⟨squareSite i.li_ii loDst d s1, _, _, rfl, ⟨[reloadScratch, reloadScratch2],
                rfl⟩, Or.inr ⟨d, opn, s1, s2, heq, hhi, hsub, loDst, k, hmem, ?_⟩⟩
              intro r hr
              unfold squareSite at hr
              split at hr <;>
                simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
                  or_false] at hr <;>
                rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
                refine ⟨by simp [isAccB], by simp [isArrImmB], ?_⟩ <;> rintro ds o ss ⟨⟩ <;>
                simp [fuseReloadScratches, reloadScratch, reloadScratch2]
            · exact ⟨[i], _, _, rfl, ⟨[], rfl⟩, Or.inl ⟨rfl, Or.inl rfl⟩⟩
          · split
            · exact ⟨[i], _, _, rfl, ⟨[], rfl⟩, Or.inl ⟨rfl, Or.inl rfl⟩⟩
            · rename_i hsp hdR
              generalize hs2r : (if (s && s2 == "RDX") = true then reloadScratch
                else if (LOperand.reg s2).isSpill = true then reloadScratch2 else s2) = s2r
              have hsr : (!(s && s2 == "RDX") && (LOperand.reg s2).isSpill) = true →
                  s2r = reloadScratch2 := by
                intro h; subst hs2r
                simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
                simp [h.1, h.2]
              generalize hh : (if (LOperand.reg d).isSpill = true then
                (if (s2r == reloadScratch) = true then reloadScratch2 else reloadScratch)
                else d) = hiReg
              have hhiR : hiReg = reloadScratch ∨ hiReg = reloadScratch2 ∨ hiReg = d := by
                subst hh; split_ifs <;> simp
              generalize hl : (if (LOperand.reg loDst).isSpill = true then hiReg else loDst)
                = loReg
              have hloR : loReg = hiReg ∨ loReg = loDst := by
                subst hl; split_ifs <;> simp
              refine ⟨_, _, _, site_assoc _ _ _ _ _ _ _, ⟨_, rfl⟩,
                Or.inr ⟨d, opn, s1, s2, heq, hhi, hsub, loDst, k, hmem, ?_⟩⟩
              intro r hr
              simp only [List.mem_append, List.mem_cons] at hr
              have key : ∀ n, (n = reloadScratch ∨ n = reloadScratch2 ∨ n = "RDX" ∨ n = d ∨
                  n = loDst) → n ∈ fuseReloadScratches ∨ n = "RDX" ∨ n = d ∨ n = loDst := by
                rintro n (h | h | h)
                · exact Or.inl (hscr n (Or.inl h))
                · exact Or.inl (hscr n (Or.inr h))
                · exact Or.inr h
              suffices hs : ∃ L o ss, r.li_i = .Lopn L o ss ∧
                  (o = "MOVQ" ∨ o = "MOV:64" ∨ o = "MULX") ∧ ∀ x ∈ L, ∃ n, x = .reg n ∧
                    (n = reloadScratch ∨ n = reloadScratch2 ∨ n = "RDX" ∨ n = d ∨ n = loDst) by
                obtain ⟨L, o, ss, hr, ho, hL⟩ := hs
                refine ⟨?_, ?_, fun ds o' ss' he x hx => ?_⟩
                · rw [hr]; rcases ho with rfl | rfl | rfl <;> rfl
                · rw [hr]; rcases ho with rfl | rfl | rfl <;> rfl
                · rw [hr] at he; cases he
                  obtain ⟨n, rfl, hn⟩ := hL x hx
                  exact ⟨n, rfl, key n hn⟩
              have hhi' : hiReg = reloadScratch ∨ hiReg = reloadScratch2 ∨ hiReg = "RDX" ∨
                  hiReg = d ∨ hiReg = loDst := by
                rcases hhiR with h | h | h <;> simp [h]
              have hlo' : loReg = reloadScratch ∨ loReg = reloadScratch2 ∨ loReg = "RDX" ∨
                  loReg = d ∨ loReg = loDst := by
                rcases hloR with h | h
                · rw [h]; exact hhi'
                · simp [h]
              rcases hr with h | rfl | h | rfl | h | h
              · split at h
                · simp only [List.mem_singleton] at h; subst h
                  exact ⟨_, _, _, rfl, by simp, by simp [reloadScratch]⟩
                · simp at h
              · exact ⟨_, _, _, rfl, by simp, by simp [reloadScratch]⟩
              · split at h
                · rename_i hc
                  simp only [List.mem_singleton] at h; subst h
                  exact ⟨_, _, _, rfl, by simp, by simp [hsr hc]⟩
                · simp at h
              · refine ⟨_, _, _, rfl, by simp, ?_⟩
                simp only [List.mem_cons, List.not_mem_nil, or_false]
                rintro x (rfl | rfl)
                · exact ⟨_, rfl, hlo'⟩
                · exact ⟨_, rfl, hhi'⟩
              · split at h
                · simp only [List.mem_singleton] at h; subst h
                  exact ⟨_, _, _, rfl, by simp, by simp [reloadScratch]⟩
                · simp at h
              · split at h
                · simp only [List.mem_singleton] at h; subst h
                  exact ⟨_, _, _, rfl, by simp, by simp [reloadScratch]⟩
                · simp at h
        · exact ⟨[i], _, _, rfl, ⟨[], rfl⟩, Or.inl ⟨rfl, Or.inl rfl⟩⟩
      · simp only [hhi, ite_false, Bool.false_eq_true]
        exact ⟨[i], _, _, rfl, ⟨[], rfl⟩, Or.inl ⟨rfl, Or.inl rfl⟩⟩
  · exact ⟨[i], _, _, rfl, ⟨[], rfl⟩, Or.inl ⟨rfl, Or.inl rfl⟩⟩

/-! ## 3. The side conditions -/

variable {slotArr : String → Option (String × Nat)}

/-- The instruction has the form of a `MULXHI` the fusion may rewrite. -/
def mulHiSiteB (i : Linstr) : Bool :=
  match i.li_i with
  | .Lopn [.reg _] opn [.reg _, .reg _] => isMulHiMnem opn
  | _ => false

/-- The Boolean test for `OperandOk`. -/
def operandOkB (slotArr : String → Option (String × Nat)) : LOperand → Bool
  | .reg q => (slotArr q).isNone
  | .arr q _ => (slotArr q).isNone
  | .arrIdx q _ _ => (slotArr q).isNone
  | .imm _ => true

/-- The Boolean test for `DstOk`. -/
def dstOkB (slotArr : String → Option (String × Nat)) : LinstrR → Bool
  | .Lopn ds _ _ => ds.all (operandOkB slotArr)
  | _ => true

theorem dstOk_of_dstOkB {r : LinstrR} (h : dstOkB slotArr r = true) : DstOk slotArr r := by
  intro ds o ss he x hx
  subst he
  have := List.all_eq_true.mp h x hx
  refine ⟨?_, ?_, ?_⟩
  · rintro q rfl; simpa [operandOkB] using this
  · rintro q n rfl; simpa [operandOkB] using this
  · rintro q j sc rfl; simpa [operandOkB] using this

/-- No reload scan of a base (`AccBase`) of `c` leaves `c`: at every instruction whose first
    source is an element at stride `8` of base `x`, and at every `ZEROARR` or `STOREIMM` whose
    first source is `.reg x`, the scan of `x` ends inside `c` (`scanExit`). -/
def scanStaysB (slotArr : String → Option (String × Nat)) (c : Lcmd) : Bool :=
  (List.range c.length).all fun k =>
    match c[k]? with
    | some i =>
        match i.li_i with
        | .Lopn _ _ (.arrIdx x _ sc :: _) => sc != 8 || (scanExit slotArr c k x).isNone
        | .Lopn _ _ (.reg x :: _) => !isArrImmB i.li_i || (scanExit slotArr c k x).isNone
        | _ => true
    | none => true

theorem scanExit_of_scanStaysB {c : Lcmd} (h : scanStaysB slotArr c = true) {k : Nat}
    {i : Linstr} (hk : c[k]? = some i) {x : String} (hx : AccBase x i.li_i) :
    scanExit slotArr c k x = none := by
  have hlt : k < c.length := (List.getElem?_eq_some_iff.mp hk).1
  have := List.all_eq_true.mp h k (List.mem_range.mpr hlt)
  rcases hx with ⟨ds, o, y, ss, hx⟩ | ⟨ds, o, ss, hx, hai⟩
  · simp only [hk, hx, bne_self_eq_false, Bool.false_or, Option.isNone_iff_eq_none] at this
    exact this
  · rw [hx] at hai
    simp only [hk, hx, hai, Bool.not_true, Bool.false_or, Option.isNone_iff_eq_none] at this
    exact this

/-- A scan that resolves to an array ends inside the body. -/
theorem scanExit_of_accArr {c : Lcmd} {k : Nat} {x : String}
    (h : (accArr slotArr c k x).isSome = true) : scanExit slotArr c k x = none := by
  have e := reloadOf_append_scanExit slotArr [] c k x
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at e
  cases hs : scanExit slotArr c k x with
  | none => rfl
  | some y =>
    rw [hs] at e
    simp [accArr, e, reloadOf_zero] at h

/-- The base register of a `ZEROARR` or `STOREIMM` with an image by `arrImmImg` holds the
    pointer of an array. -/
theorem accArr_of_arrImmImg {c : Lcmd} {k : Nat} {ds : List LOperand} {o x : String}
    {ss : List LOperand} (h : (arrImmImg slotArr c k (.Lopn ds o (.reg x :: ss))).isSome = true) :
    (accArr slotArr c k x).isSome = true := by
  unfold arrImmImg at h
  split at h
  · rename_i b n' w' he
    simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq] at he
    obtain ⟨-, -, rfl, -⟩ := he
    split_ifs at h
    · split at h
      · rename_i A n hA; rw [hA]; rfl
      · cases h
    · cases h
  · rename_i d b v j he
    simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq] at he
    obtain ⟨-, -, rfl, -⟩ := he
    split_ifs at h
    · split at h
      · rename_i A n hA; rw [hA]; rfl
      · cases h
    · cases h
  · cases h

/-- A body that resolves its accesses locally, and whose instructions with a first source at
    stride `8` are accesses, satisfies `scanStaysB`. -/
theorem scanStaysB_of_accLocal {c : Lcmd} (hacc : AccLocal slotArr c)
    (hform : ∀ r ∈ c, ∀ ds o x y ss, r.li_i = .Lopn ds o (.arrIdx x y 8 :: ss) →
      o = "LOADIDX" ∨ o = "STOREIDX") : scanStaysB slotArr c = true := by
  unfold scanStaysB
  refine List.all_eq_true.mpr fun k hk => ?_
  have hlt := List.mem_range.mp hk
  have hget := List.getElem?_eq_getElem hlt
  rw [hget]
  simp only
  split
  · rename_i ds o x y sc ss hx
    by_cases h8 : sc = 8
    · subst h8
      have ha := hacc k _ hget
      rw [hx] at ha
      simp only [bne_self_eq_false, Bool.false_or, Option.isNone_iff_eq_none]
      refine scanExit_of_accArr ?_
      rcases hform _ (List.getElem_mem hlt) ds o x y ss hx with rfl | rfl
      · unfold accOkB at ha
        simp only [ite_true] at ha
        split at ha
        · rename_i heq; cases heq; exact ha
        · cases ha
      · unfold accOkB at ha
        simp only [ite_true] at ha
        simp at ha
        split at ha
        · rename_i heq; cases heq
          simp only [Bool.and_eq_true] at ha
          exact ha.2
        · cases ha
    · simp [h8]
  · rename_i ds o x ss hx
    cases hai : isArrImmB c[k].li_i
    · simp
    · have ha := hacc k _ hget
      rw [hx] at ha hai
      have ho : o = "ZEROARR" ∨ o = "STOREIMM" := by simpa [isArrImmB] using hai
      have hl : o ≠ "LOADIDX" ∧ o ≠ "STOREIDX" := by
        rcases ho with rfl | rfl <;> decide
      simp only [accOkB, hl.1, hl.2, ho, ite_false, ite_true] at ha
      simp only [Bool.not_true, Bool.false_or, Option.isNone_iff_eq_none]
      exact scanExit_of_accArr (accArr_of_arrImmImg ha)
  · rfl

/-- **The site condition of the fusion.** At every instruction of the form of a rewritten
    `MULXHI` (`mulHiSiteB`), the instruction and the rest of the body write no array slot, and
    no reload scan of a base of the rest leaves the rest: no site lies between the reload of
    a base and its access. -/
def fuseSiteOkB (slotArr : String → Option (String × Nat)) : Lcmd → Bool
  | [] => true
  | i :: rest =>
      (!mulHiSiteB i || (dstOkB slotArr i.li_i && rest.all (fun r => dstOkB slotArr r.li_i) &&
        scanStaysB slotArr rest)) && fuseSiteOkB slotArr rest

/-- **The home condition of the fusion.** Along the scratch environment of the body (`env`,
    advanced by `scratchStep`), the destination of every low `MUL`, and the name it resolves
    to, are no array slots. -/
def homeOkB (slotArr : String → Option (String × Nat)) : ScratchEnv → Lcmd → Bool
  | _, [] => true
  | env, i :: rest =>
      (match i.li_i with
        | .Lopn [.reg d] opn [.reg _, .reg _] =>
            !isLowMulMnem opn ||
              ((slotArr d).isNone && (slotArr (scratchResolve env d)).isNone)
        | _ => true) && homeOkB slotArr (scratchStep env i) rest

/-! ## 4. The image class of the fused body -/

theorem slotArr_scratch (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true)
    {n : String} (hn : n ∈ fuseReloadScratches ∨ n = "RDX") : slotArr n = none := by
  refine slotArr_none_of_prefix hq ?_
  simp only [fuseReloadScratches, reloadScratch, reloadScratch2, List.mem_cons,
    List.not_mem_nil, or_false] at hn
  rcases hn with (rfl | rfl) | rfl <;> decide +kernel

theorem fuseMulHiAux_nil (s : Bool) (env : ScratchEnv) (pend : List (String × String)) :
    fuseMulHiAux s env pend [] = [] := by
  rw [fuseMulHiAux]

/-- **The fusion keeps the image class**, from any position: let `A ++ rest` be in the class,
    let `rest` satisfy the site and home conditions at an environment `ep` with which the
    environment `ef` of the fusion agrees, and let every pending home be no array slot. Then
    `A` followed by the fusion of `rest` is in the class. -/
theorem physImgB_fuseMulHiAux (s : Bool)
    (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) :
    ∀ (rest A : Lcmd) (ef ep : ScratchEnv) (pend : List (String × String)),
      physImgB slotArr (A ++ rest) = true → fuseSiteOkB slotArr rest = true →
      homeOkB slotArr ep rest = true → EnvAgree ef ep → EnvScratch ef →
      (∀ p ∈ pend, slotArr p.1 = none) →
      physImgB slotArr (A ++ fuseMulHiAux s ef pend rest) = true
  | [], A, _, _, _, h, _, _, _, _, _ => by rw [fuseMulHiAux_nil]; simpa using h
  | i :: rest, A, ef, ep, pend, h, hs, hh, hag, hes, hp => by
    obtain ⟨L, env', pend', he, ⟨ks, rfl⟩, hcase⟩ := fuseMulHiAux_cons_step s ef pend i rest
    simp only [fuseSiteOkB, homeOkB, Bool.and_eq_true] at hs hh
    have hag' := (hag.step i).killAll (hes.step i) ks
    have hes' := (hes.step i).killAll ks
    rw [he, ← List.append_assoc]
    rcases hcase with ⟨rfl, hpd⟩ | ⟨d, opn, s1, s2, heq, hhi, hsub, lo, k, hlo, hout⟩
    · refine physImgB_fuseMulHiAux s hq rest (A ++ [i]) _ _ pend' (by simpa using h) hs.2 hh.2
        hag' hes' ?_
      rcases hpd with rfl | ⟨d, opn, s1, s2, heq, hlow, rfl⟩
      · exact hp
      · have h1 := hh.1
        rw [heq] at h1
        simp only [hlow, Bool.not_true, Bool.false_or, Bool.and_eq_true,
          Option.isNone_iff_eq_none] at h1
        intro p hp'
        simp only [List.mem_cons] at hp'
        rcases hp' with rfl | hp'
        · cases s
          · exact h1.1
          · simp only [ite_true, lowHome]
            split
            · rcases hag d with he' | he'
              · rw [he']; exact h1.2
              · exact slotArr_scratch hq (Or.inl he')
            · exact h1.1
        · exact hp p hp'
    · refine physImgB_fuseMulHiAux s hq rest (A ++ L) _ _ pend' ?_ hs.2 hh.2 hag' hes'
        (fun p hp' => hp p (hsub p hp'))
      have hsite : mulHiSiteB i = true := by simp [mulHiSiteB, heq, hhi]
      have h1 := hs.1
      simp only [hsite, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h1
      obtain ⟨⟨hdi, hrest⟩, hstay⟩ := h1
      have hd : slotArr d = none := by
        rw [heq] at hdi
        simpa [dstOkB, operandOkB] using hdi
      have hlo' : slotArr lo = none := hp (lo, k) hlo
      refine physImgB_replace (L := [i]) (by simpa using h) (fun r hr => ?_)
        (fun r hr => dstOk_of_dstOkB (List.all_eq_true.mp hrest r hr)) ?_
      · obtain ⟨hacc, hai, hds⟩ := hout r hr
        refine ⟨hacc, hai, fun ds o ss hr' x hx => ?_⟩
        obtain ⟨n, rfl, hn⟩ := hds ds o ss hr' x hx
        have : slotArr n = none := by
          rcases hn with hn | hn | rfl | rfl
          · exact slotArr_scratch hq (Or.inl hn)
          · exact slotArr_scratch hq (Or.inr hn)
          · exact hd
          · exact hlo'
        exact ⟨fun q hq' => by cases hq'; exact this, nofun, nofun⟩
      · intro k' i' x hk hb y hy
        rw [scanExit_of_scanStaysB hstay hk hb] at hy
        cases hy

/-- **The fused body is in the image class.** A body in the class `physImgB slotArr`, whose
    array slots are `qsave.` slots, keeps the class under the fusion `fuseMulHiBody` in either
    mode when it satisfies the site condition `fuseSiteOkB` and the home condition `homeOkB`
    from the empty environment. -/
theorem physImgB_fuseMulHiBody (s : Bool)
    (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) {b : Lcmd}
    (h : physImgB slotArr b = true) (hsite : fuseSiteOkB slotArr b = true)
    (hhome : homeOkB slotArr [] b = true) :
    physImgB slotArr (fuseMulHiBody b s) = true := by
  have := physImgB_fuseMulHiAux s hq b [] [] [] [] (by simpa using h) hsite hhome
    (EnvAgree.refl _) (fun _ hp => by cases hp) (fun _ hp => by cases hp)
  simpa [fuseMulHiBody] using this

end CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgFuse
