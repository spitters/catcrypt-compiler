/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.PrintedCoveredLower

/-!
# Covered instructions under the high-product fusion

The fusion half `FuseMulHi.fuseMulHiAux` of the region post-pass `Haxc.regionPostFuse` keeps
every instruction of its input other than a fused high-word binding `MULXHI`, and replaces a
fused binding by moves through `RDX`, `R14` and `R15`, a two-output `MULX` and a store of the
high word to a spilled destination. This module proves that each instruction of its output is
covered in the output body or is an unfused high-word binding, when the same holds of the
input, the operands of the products and of the reloads into the reserved scratch registers
are names the moves of the fused site address, and the output agrees with the input on its
frame.

The two-address legaliser `TwoAddrLegalize.twoAddrBody` keeps every covered instruction, since
each satisfies the printer's two-address precondition `tiedOk`, and rewrites a three-address
operation `M D, [A, S]` over general-purpose names (`ThreeAddrAlu`) into the copy
`MOV:64 D, A` and the tied operation `M D, [D, S]`, or into `M D, [D, A]` when `S = D` and `M`
commutes. A body of covered instructions and three-address operations therefore has a covered
legalised body, when the legalised body agrees with it on its frame.

## Main definitions

* `StoreOk b n`: `n` is a general-purpose name or a frame slot that a 64-bit store of the body
  `b` addresses.
* `HomeOk b n`: `n` is a frame slot of `StoreOk b` when it is a spill slot, and a
  general-purpose name otherwise.
* `SrcOk b n`: `n` is a name a 64-bit load of `b` reads, and a general-purpose name when it is
  no spill slot.
* `FuseInputOk b`: the operands of the products of `b` and the sources of its moves into a
  reserved scratch register satisfy these conditions.
* `ThreeAddrAlu i`: `i` is a three-address 64-bit group-1 operation or product over
  general-purpose names.

## Main results

* `mem_fuseMulHiAux`: an instruction of the output of the fusion is an instruction of its input
  or a gate form of the input body.
* `mem_fuseMulHiAux_of_not_lopn`: the fusion keeps every instruction that is no operation, in
  particular every label.
* `covered_fuseMulHiBody`: every instruction of the fused body is covered in it or is an
  unfused high-word binding.
* `tiedOk_of_covered`: every covered instruction satisfies the two-address precondition.
* `legalizeInstr_threeAddr`: the legaliser rewrites a three-address operation into gate forms.
* `covered_twoAddrBody`: every instruction of the legalised body of a body of covered
  instructions and three-address operations is covered in it.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.PrintedCoveredFuse

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun (labelAt isLabelB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (spillQsaveOff isSpillOrQsave)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (Params)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpOk slotOff)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW (kOk)
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder (dispOk32)
open CatCrypt.Crypto.SecureCompilation.X86Backend.GateOfLegal (GateForm)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PrintedCompleteLegal (Covered UnfusedMulHi)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PrintedCoveredPasses (FrameAgree
  gateForm_of_frameAgree covered_of_frameAgree)
open CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi

/-! ## 1. Names of the fused site -/

/-- **A store target of a body**: a general-purpose name, or a frame slot whose offset the
    parameters of `b` resolve to a `rel32` displacement. -/
def StoreOk (b : Lcmd) (n : String) : Prop :=
  gpOk n = true ∨ (isSpillOrQsave n = true ∧
    (spillQsaveOff (Params.ofBody b).frame (Params.ofBody b).spillW n
      (Params.ofBody b).qsaveB).isSome = true ∧ dispOk32 (slotOff (Params.ofBody b) n) = true)

/-- **A home of a product word**: a spill slot that is a store target of `b`, or a
    general-purpose name. -/
def HomeOk (b : Lcmd) (n : String) : Prop :=
  ((LOperand.reg n).isSpill = true → StoreOk b n) ∧
    ((LOperand.reg n).isSpill = false → gpOk n = true)

/-- **A multiplicand of a body**: a name a 64-bit load of `b` reads, a general-purpose name
    when it is no spill slot. -/
def SrcOk (b : Lcmd) (n : String) : Prop :=
  kOk (Params.ofBody b) n = true ∧ ((LOperand.reg n).isSpill = false → gpOk n = true)

/-- **The input conditions of the fusion** on a body `b`: the destination of every low product
    is a home; the destination of every high-word binding is a home, its first source is read
    by a load and its second source is a multiplicand; the source of every move into a reserved
    reload scratch register is a home. -/
def FuseInputOk (b : Lcmd) : Prop :=
  (∀ x ∈ b, ∀ (d opn s1 s2 : String), x.li_i = .Lopn [.reg d] opn [.reg s1, .reg s2] →
    (isLowMulMnem opn = true → HomeOk b d) ∧
    (isMulHiMnem opn = true → HomeOk b d ∧ kOk (Params.ofBody b) s1 = true ∧ SrcOk b s2)) ∧
  (∀ x ∈ b, ∀ (ds : List LOperand) (opn dn sn : String),
    x.li_i = .Lopn ds opn [.reg sn] → LOperand.reg dn ∈ ds → dn ∈ fuseReloadScratches →
    "MOV".isPrefixOf (stripWidthTag opn) = true → HomeOk b sn)

/-- `RDX` is a general-purpose name of the gate. -/
theorem gpOk_RDX : gpOk "RDX" = true := by decide
/-- `R14` is a general-purpose name of the gate. -/
theorem gpOk_R14 : gpOk "R14" = true := by decide
/-- `R15` is a general-purpose name of the gate. -/
theorem gpOk_R15 : gpOk "R15" = true := by decide

/-- A general-purpose name is a home. -/
theorem homeOk_of_gpOk {b : Lcmd} {n : String} (h : gpOk n = true) : HomeOk b n :=
  ⟨fun _ => Or.inl h, fun _ => h⟩

/-- The 64-bit move between general-purpose names is a gate form. -/
theorem gateForm_movRR (b : Lcmd) {m d s : String} (hm : m ∈ ["MOV:64", "MOVQ"])
    (hd : gpOk d = true) (hs : gpOk s = true) : GateForm b (.Lopn [.reg d] m [.reg s]) :=
  .movRR m d s hm hd hs

/-- A 64-bit move into a general-purpose name from a name a load reads is a gate form. -/
theorem gateForm_movLoad (b : Lcmd) {d s : String} (hd : gpOk d = true)
    (hs : kOk (Params.ofBody b) s = true) : GateForm b (.Lopn [.reg d] "MOV:64" [.reg s]) := by
  cases hg : gpOk s
  · have hq : isSpillOrQsave s = true := by
      simp only [kOk, hg, Bool.false_or, Bool.and_eq_true] at hs
      exact hs.1
    exact .movLoad _ d s (by simp) hd hq hs
  · exact .movRR _ d s (by simp) hd hg

/-- A 64-bit move of a general-purpose name into a store target is a gate form. -/
theorem gateForm_movStore (b : Lcmd) {q s : String} (hq : StoreOk b q) (hs : gpOk s = true) :
    GateForm b (.Lopn [.reg q] "MOV:64" [.reg s]) := by
  rcases hq with hq | ⟨h1, h2, h3⟩
  · exact .movRR _ q s (by simp) hq hs
  · exact .movStore _ q s (by simp) h1 h2 h3 hs

/-! ## 2. The fused sites -/

/-- **The squaring site** of the looped-body mode consists of gate forms of `b`. -/
theorem squareSite_gateForm (b : Lcmd) {ii : Nat} {loDst d s1 : String}
    (hlo : HomeOk b loDst) (hd : StoreOk b d) (hs1 : kOk (Params.ofBody b) s1 = true) :
    ∀ y ∈ squareSite ii loDst d s1, GateForm b y.li_i := by
  intro y hy
  unfold squareSite at hy
  split at hy
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
    · exact gateForm_movRR b (by simp) gpOk_R15 gpOk_RDX
    · exact gateForm_movLoad b gpOk_RDX hs1
    · exact .mulx _ _ _ gpOk_RDX gpOk_R14 gpOk_RDX
    · exact gateForm_movStore b (hlo.1 ‹_›) gpOk_RDX
    · exact gateForm_movStore b hd gpOk_R14
    · exact gateForm_movRR b (by simp) gpOk_RDX gpOk_R15
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact gateForm_movRR b (by simp) gpOk_R15 gpOk_RDX
    · exact gateForm_movLoad b gpOk_RDX hs1
    · exact .mulx _ _ _ (hlo.2 (by grind)) gpOk_R14 gpOk_RDX
    · exact gateForm_movStore b hd gpOk_R14
    · exact gateForm_movRR b (by simp) gpOk_RDX gpOk_R15

/-- **The fused site of a high-word binding** `MULXHI d, [s1, s2]` paired with a low product of
    home `loDst`: the save of `RDX`, the pin of `s1` in `RDX`, the reload of a spilled `s2`, the
    `MULX`, the store of a spilled high word and the restore of `RDX` are gate forms of `b`. -/
theorem fusedSite_mem (b : Lcmd) (saveRdx : Bool) (ii : Nat) {d s1 s2 loDst : String}
    (R : Lcmd) (hd : HomeOk b d) (hs1 : kOk (Params.ofBody b) s1 = true) (hs2 : SrcOk b s2)
    (hlo : HomeOk b loDst) :
    let save : List Linstr :=
      if saveRdx then [⟨ii, .Lopn [.reg "R15"] "MOVQ" [.reg "RDX"]⟩] else []
    let rdxSaved := saveRdx && s2 == "RDX"
    let s2Spill := (LOperand.reg s2).isSpill
    let s2r := if rdxSaved then reloadScratch else if s2Spill then reloadScratch2 else s2
    let srcReload : List Linstr :=
      if !rdxSaved && s2Spill then [⟨ii, .Lopn [.reg s2r] "MOV:64" [.reg s2]⟩] else []
    let movRdx : Linstr := ⟨ii, .Lopn [.reg "RDX"] "MOV:64" [.reg s1]⟩
    let hiReg :=
      if (LOperand.reg d).isSpill then
        (if s2r == reloadScratch then reloadScratch2 else reloadScratch)
      else d
    let loReg := if (LOperand.reg loDst).isSpill then hiReg else loDst
    let mulx : Linstr := ⟨ii, .Lopn [.reg loReg, .reg hiReg] "MULX" [.reg s2r]⟩
    let hiStore : List Linstr :=
      if (LOperand.reg d).isSpill then [⟨ii, .Lopn [.reg d] "MOV:64" [.reg hiReg]⟩] else []
    let restore : List Linstr :=
      if saveRdx && loDst != "RDX" then [⟨ii, .Lopn [.reg "RDX"] "MOVQ" [.reg "R15"]⟩] else []
    ∀ y ∈ save ++ movRdx :: (srcReload ++ mulx :: (hiStore ++ restore ++ R)),
      y ∈ R ∨ GateForm b y.li_i := by
  intro save rdxSaved s2Spill s2r srcReload movRdx hiReg loReg mulx hiStore restore
  have hs2r : gpOk s2r = true := by
    simp only [s2r]
    split
    · exact gpOk_R15
    · split
      · exact gpOk_R14
      · exact hs2.2 (by grind)
  have hhi : gpOk hiReg = true := by
    simp only [hiReg]
    split
    · split
      · exact gpOk_R14
      · exact gpOk_R15
    · exact hd.2 (by grind)
  have hloR : gpOk loReg = true := by
    simp only [loReg]
    split
    · exact hhi
    · exact hlo.2 (by grind)
  have hsave : ∀ y ∈ save, GateForm b y.li_i := by
    simp only [save]
    split <;> simp only [List.mem_cons, List.not_mem_nil, or_false] <;> intro y hy
    · subst hy; exact gateForm_movRR b (by simp) gpOk_R15 gpOk_RDX
    · exact hy.elim
  have hrel : ∀ y ∈ srcReload, GateForm b y.li_i := by
    simp only [srcReload]
    split <;> simp only [List.mem_cons, List.not_mem_nil, or_false] <;> intro y hy
    · subst hy; exact gateForm_movLoad b hs2r hs2.1
    · exact hy.elim
  have hst : ∀ y ∈ hiStore, GateForm b y.li_i := by
    simp only [hiStore]
    split <;> simp only [List.mem_cons, List.not_mem_nil, or_false] <;> intro y hy
    · subst hy; exact gateForm_movStore b (hd.1 ‹_›) hhi
    · exact hy.elim
  have hres : ∀ y ∈ restore, GateForm b y.li_i := by
    simp only [restore]
    split <;> simp only [List.mem_cons, List.not_mem_nil, or_false] <;> intro y hy
    · subst hy; exact gateForm_movRR b (by simp) gpOk_RDX gpOk_R15
    · exact hy.elim
  have hmov : GateForm b movRdx.li_i := gateForm_movLoad b gpOk_RDX hs1
  have hmx : GateForm b mulx.li_i := .mulx _ _ _ hloR hhi hs2r
  intro y hy
  simp only [List.mem_append, List.mem_cons] at hy
  grind

/-! ## 3. The fusion worker -/

/-- The names the reserved reload scratch registers hold in `env` are homes of `b`. -/
def EnvOk (b : Lcmd) (env : ScratchEnv) : Prop := ∀ p ∈ env, HomeOk b p.2

/-- The homes of the pending low products in `pend` are homes of `b`. -/
def PendOk (b : Lcmd) (pend : List (String × String)) : Prop := ∀ p ∈ pend, HomeOk b p.1

/-- A home resolves through the scratch environment to a home. -/
theorem homeOk_scratchResolve {b : Lcmd} {env : ScratchEnv} {n : String} (he : EnvOk b env)
    (hn : HomeOk b n) : HomeOk b (scratchResolve env n) := by
  unfold scratchResolve
  split
  · next v h => exact he _ (List.mem_of_find?_eq_some h)
  · exact hn

/-- Forgetting a scratch register keeps the environment invariant. -/
theorem envOk_scratchKill {b : Lcmd} {env : ScratchEnv} (he : EnvOk b env) (dn : String) :
    EnvOk b (scratchKill env dn) := by
  intro p hp
  exact he p (List.mem_filter.1 hp).1

/-- Forgetting several scratch registers keeps the environment invariant. -/
theorem envOk_foldl_scratchKill {b : Lcmd} (l : List String) :
    ∀ {env : ScratchEnv}, EnvOk b env → EnvOk b (l.foldl scratchKill env) := by
  induction l with
  | nil => intro env he; exact he
  | cons x l ih => intro env he; exact ih (envOk_scratchKill he x)

/-- A left fold keeps an invariant that each step over an element of a list `L` keeps. -/
theorem foldl_inv {α β : Type} (P : β → Prop) (f : β → α → β) (L : List α)
    (hf : ∀ e a, a ∈ L → P e → P (f e a)) :
    ∀ (ds : List α), (∀ a ∈ ds, a ∈ L) → ∀ e, P e → P (ds.foldl f e) := by
  intro ds
  induction ds with
  | nil => intro _ e h; exact h
  | cons a ds ih =>
    intro hsub e h
    exact ih (fun a' ha' => hsub a' (List.mem_cons_of_mem _ ha')) _
      (hf e a (hsub a List.mem_cons_self) h)

/-- The scratch step over an instruction of `b` keeps the environment invariant. -/
theorem envOk_scratchStep {b : Lcmd} (hin : FuseInputOk b) {x : Linstr} (hx : x ∈ b)
    {env : ScratchEnv} (he : EnvOk b env) : EnvOk b (scratchStep env x) := by
  unfold scratchStep
  split
  · next dsts opn srcs hxi =>
    refine foldl_inv (EnvOk b) _ dsts ?_ dsts (fun _ h => h) env he
    intro e o ho h
    cases o with
    | reg dn =>
      simp only
      split
      · next hdn =>
        split
        · rename_i _ sn
          split
          · next hmov =>
            intro p hp
            rcases List.mem_cons.1 hp with rfl | hp
            · exact homeOk_scratchResolve he (hin.2 x hx dsts opn dn sn hxi ho
                (by simpa using hdn) hmov)
            · exact h p (List.mem_filter.1 hp).1
          · exact envOk_scratchKill h dn
        · exact envOk_scratchKill h dn
      · exact h
    | _ => exact h
  · exact he

/-- The span of the pending list at a match splits it around the matched entry. -/
theorem pendOk_span {b : Lcmd} {pend before after : List (String × String)}
    {p : String × String} {q : String × String → Bool} (hp : PendOk b pend)
    (h : pend.span q = (before, p :: after)) : HomeOk b p.1 ∧ PendOk b (before ++ after) := by
  have he : before ++ p :: after = pend := by
    rw [List.span_eq_takeWhile_dropWhile] at h
    simp only [Prod.mk.injEq] at h
    rw [← h.1, ← h.2, List.takeWhile_append_dropWhile]
  subst he
  refine ⟨hp p (by simp), fun r hr => hp r ?_⟩
  simp only [List.mem_append, List.mem_cons] at hr ⊢
  tauto

/-- **The output of the fusion worker** on a part `c` of `b`, from an environment and a
    pending list of homes: every instruction is an instruction of `c` or a gate form of `b`. -/
theorem mem_fuseMulHiAux {b : Lcmd} (hin : FuseInputOk b) (saveRdx : Bool) :
    ∀ (c : Lcmd) (env : ScratchEnv) (pend : List (String × String)), (∀ x ∈ c, x ∈ b) →
      EnvOk b env → PendOk b pend →
      ∀ y ∈ fuseMulHiAux saveRdx env pend c, y ∈ c ∨ GateForm b y.li_i := by
  intro c
  induction c with
  | nil => intro env pend _ _ _ y hy; simp [fuseMulHiAux] at hy
  | cons i rest ih =>
    intro env pend hsub he hp y hy
    have hi : i ∈ b := hsub i List.mem_cons_self
    have hrest : ∀ x ∈ rest, x ∈ b := fun x hx => hsub x (List.mem_cons_of_mem _ hx)
    have he' : EnvOk b (scratchStep env i) := envOk_scratchStep hin hi he
    have hrec : ∀ env'' pend'', EnvOk b env'' → PendOk b pend'' →
        y ∈ fuseMulHiAux saveRdx env'' pend'' rest → y ∈ i :: rest ∨ GateForm b y.li_i :=
      fun env'' pend'' h1 h2 h3 =>
        (ih env'' pend'' hrest h1 h2 y h3).imp (List.mem_cons_of_mem _) id
    have hcons : y ∈ i :: fuseMulHiAux saveRdx (scratchStep env i) pend rest →
        y ∈ i :: rest ∨ GateForm b y.li_i := by
      intro h
      rcases List.mem_cons.1 h with rfl | h
      · exact Or.inl List.mem_cons_self
      · exact hrec _ _ he' hp h
    rw [fuseMulHiAux] at hy
    split at hy
    · next d opn s1 s2 hxi =>
      have hI := hin.1 i hi d opn s1 s2 hxi
      split at hy
      · next hlow =>
        rcases List.mem_cons.1 hy with rfl | hy
        · exact Or.inl List.mem_cons_self
        · refine hrec _ _ he' ?_ hy
          intro p hp'
          rcases List.mem_cons.1 hp' with rfl | hp'
          · have hd := hI.1 hlow
            dsimp only
            split
            · unfold lowHome
              split
              · exact homeOk_scratchResolve he hd
              · exact hd
            · exact hd
          · exact hp p hp'
      · split at hy
        · next hhi =>
          obtain ⟨hd, hs1, hs2⟩ := hI.2 hhi
          split at hy
          · next hsq =>
            dsimp only at hy
            split at hy
            · next before loDst k after hspan =>
              obtain ⟨hlo, hpa⟩ := pendOk_span hp hspan
              split at hy
              · rcases List.mem_append.1 hy with hy | hy
                · refine Or.inr (squareSite_gateForm b hlo (hd.1 ?_) hs1 y hy)
                  simp only [Bool.and_eq_true] at hsq
                  exact hsq.2
                · exact hrec _ _ (envOk_foldl_scratchKill _ he') hpa hy
              · exact hcons hy
            · exact hcons hy
          · dsimp only at hy
            split at hy
            · next before loDst k after hspan =>
              obtain ⟨hlo, hpa⟩ := pendOk_span hp hspan
              split at hy
              · exact hcons hy
              · rcases fusedSite_mem b saveRdx i.li_ii (fuseMulHiAux saveRdx _ _ rest) hd hs1 hs2
                  hlo y hy with h | h
                · exact hrec _ _ (envOk_foldl_scratchKill _ he') hpa h
                · exact Or.inr h
            · exact hcons hy
        · exact hcons hy
    · exact hcons hy

/-- **The fusion keeps every instruction that is no operation**, in particular every label. -/
theorem mem_fuseMulHiAux_of_not_lopn (saveRdx : Bool) :
    ∀ (c : Lcmd) (env : ScratchEnv) (pend : List (String × String)) (x : Linstr), x ∈ c →
      (∀ ds o ss, x.li_i ≠ .Lopn ds o ss) → x ∈ fuseMulHiAux saveRdx env pend c := by
  intro c
  induction c with
  | nil => intro _ _ x hx; cases hx
  | cons i rest ih =>
    intro env pend x hx hn
    rcases List.mem_cons.1 hx with rfl | hx
    · rw [fuseMulHiAux]
      split
      · next hxi => exact absurd hxi (hn _ _ _)
      · exact List.mem_cons_self
    · have hr := fun e p => ih e p x hx hn
      rw [fuseMulHiAux]
      try dsimp only
      repeat' split
      all_goals simp [hr]

/-- **Covered instructions under the fusion**: on a body `b` whose instructions are covered or
    unfused high-word bindings, under the input conditions `FuseInputOk b`, every instruction of
    the fused body is covered in it or is an unfused high-word binding, when the fused body
    agrees with `b` on its frame. -/
theorem covered_fuseMulHiBody {b : Lcmd} (saveRdx : Bool) (hin : FuseInputOk b)
    (hcov : ∀ x ∈ b, Covered b x.li_i ∨ UnfusedMulHi x.li_i)
    (hf : FrameAgree b (fuseMulHiBody b saveRdx)) :
    ∀ y ∈ fuseMulHiBody b saveRdx,
      Covered (fuseMulHiBody b saveRdx) y.li_i ∨ UnfusedMulHi y.li_i := by
  have hl : ∀ l, (labelAt b l).isSome = true →
      (labelAt (fuseMulHiBody b saveRdx) l).isSome = true := by
    intro l h
    simp only [labelAt, List.findIdx?_isSome, List.any_eq_true] at h ⊢
    obtain ⟨x, hx, hxl⟩ := h
    refine ⟨x, mem_fuseMulHiAux_of_not_lopn saveRdx b [] [] x hx ?_, hxl⟩
    intro ds o ss he
    rw [he] at hxl
    simp [isLabelB] at hxl
  intro y hy
  rcases mem_fuseMulHiAux hin saveRdx b [] [] (fun _ h => h) (by simp [EnvOk])
    (by simp [PendOk]) y hy with h | h
  · rcases hcov y h with h | h
    · exact Or.inl (covered_of_frameAgree h hf hl)
    · exact Or.inr h
  · exact Or.inl (Or.inl (gateForm_of_frameAgree h hf hl))

/-! ## 4. The two-address legaliser -/

section TwoAddr

open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (isMemOperand)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogLeak (opNames)

/-- **A three-address operation** of the lowering: `M D, [A, S]` over general-purpose names for
    a 64-bit group-1 operation or product `M`, the second source distinct from the destination
    unless `M` commutes. -/
def ThreeAddrAlu (i : LinstrR) : Prop :=
  ∃ (m d a s : String), m ∈ ["ADD:64", "SUB:64", "AND:64", "OR:64", "XOR:64", "MUL:64"] ∧
    gpOk d = true ∧ gpOk a = true ∧ gpOk s = true ∧ (s ≠ d ∨ m ≠ "SUB:64") ∧
    i = .Lopn [.reg d] m [.reg a, .reg s]

/-- A general-purpose name is no memory operand. -/
theorem isMemOperand_of_gpOk {d : String} (h : gpOk d = true) :
    isMemOperand (.reg d) = false := by
  simp only [gpOk, DecodePrinted.gpList, List.contains_eq_mem, List.mem_cons,
    List.not_mem_nil, decide_eq_true_eq, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> simp [isMemOperand, PhysAbiShape.isPrefixOf_eq_list, List.isPrefixOf]

/-- Every covered instruction satisfies the printer's two-address precondition. -/
theorem tiedOk_of_covered {b : Lcmd} {i : LinstrR} (h : Covered b i) : tiedOk i = true := by
  rcases h with h | h | h
  · cases h
    all_goals first
      | (simp [tiedOk]; done)
      | (simp [tiedOk, needsTie, tieBase, tiedBases]; done)
      | (simp only [List.mem_cons, List.not_mem_nil, or_false] at *
         rcases ‹_ ∨ _› with rfl | rfl <;> simp [tiedOk, needsTie, tieBase, tiedBases])
  · rcases h with ⟨n, R, A, B, -, -, -, rfl⟩ | ⟨n, R, A, v, -, -, -, rfl⟩ |
      ⟨l, R, A, B, -, -, -, rfl⟩ | ⟨R, -, rfl⟩ <;> (try cases n) <;> (try cases l) <;>
      simp [tiedOk, needsTie, tieBase, tiedBases]
  · rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨_, _, _, _, -, -, -, -, rfl⟩ <;> simp [tiedOk]

/-- The legaliser rewrites a three-address operation into gate forms of every body. -/
theorem legalizeInstr_threeAddr (b : Lcmd) (ok : Bool) (x : Linstr) (h : ThreeAddrAlu x.li_i) :
    ∀ y ∈ legalizeInstr ok x, GateForm b y.li_i := by
  obtain ⟨m, d, a, s, hm, hd, ha, hs, hsd, hx⟩ := h
  intro y hy
  by_cases had : a = d
  · subst had
    rw [legalizeInstr_of_tiedOk ok x (by rw [hx]; simp [tiedOk]), List.mem_singleton] at hy
    subst hy
    rw [hx]
    refine .alu m a s ?_ ha hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
    tauto
  · unfold legalizeInstr at hy
    rw [hx] at hy
    have hmd : isMemOperand (.reg d) = false := isMemOperand_of_gpOk hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [needsTie, tiedBases, tieBase, ↓Char.isValue, String.reduceToList,
        Char.reduceBNe, Bool.and_self, List.takeWhile_cons_of_pos, bne_self_eq_false,
        Bool.and_true, Bool.false_eq_true, not_false_eq_true, List.takeWhile_cons_of_neg,
        String.ofList_cons, String.reduceSingleton, String.ofList_nil, String.append_empty,
        String.reduceAppend, List.contains_eq_mem, List.mem_cons, String.reduceEq,
        List.not_mem_nil, or_self, or_false, or_true, decide_true, String.reduceBEq, Bool.or_self,
        Bool.or_false, Bool.true_and, bne_iff_ne, ne_eq, LOperand.reg.injEq, had, ↓reduceIte,
        movFor, BEq.rfl, isRegOrImm, Bool.not_true, opNames, hmd, Bool.false_and, Bool.not_false,
        Bool.not_eq_eq_eq_not, decide_eq_false_iff_not, Bool.and_eq_true, decide_eq_true_eq,
        beq_iff_eq, ite_not] at hy
    all_goals
      by_cases hds : d = s
      · subst hds
        first
          | (simp at hsd; done)
          | (simp only [↓reduceIte, commBases, List.mem_cons, String.reduceEq, List.not_mem_nil,
               or_self, or_false, or_true, and_self] at hy
             subst hy
             exact .alu _ _ _ (by simp) hd ha)
      · simp only [hds, ite_false, List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl
        · exact .movRR _ d a (by simp) hd ha
        · exact .alu _ d s (by simp) hd hs

/-- **Covered output of the two-address legaliser**: on a body each of whose instructions is
    covered in it or a three-address operation, every instruction of the legalised body is
    covered in it, when the legalised body agrees with the input on its frame. -/
theorem covered_twoAddrBody {b : Lcmd}
    (hcov : ∀ x ∈ b, Covered b x.li_i ∨ ThreeAddrAlu x.li_i)
    (hf : FrameAgree b (twoAddrBody b)) :
    ∀ y ∈ twoAddrBody b, Covered (twoAddrBody b) y.li_i := by
  have hl : ∀ l, (labelAt b l).isSome = true → (labelAt (twoAddrBody b) l).isSome = true := by
    intro l h
    simp only [labelAt, List.findIdx?_isSome, List.any_eq_true] at h ⊢
    obtain ⟨x, hx, hxl⟩ := h
    refine ⟨x, ?_, hxl⟩
    have hlx : legalizeInstr (bodyAvoids b) x = [x] := by
      unfold legalizeInstr
      split
      · next hxi => rw [hxi] at hxl; simp [isLabelB] at hxl
      · rfl
    simp only [twoAddrBody, LegalizeShiftImm.legalizeBody, List.mem_flatMap]
    exact ⟨x, hx, by simp [hlx]⟩
  intro y hy
  simp only [twoAddrBody, LegalizeShiftImm.legalizeBody, List.mem_flatMap] at hy
  obtain ⟨x, hx, hy⟩ := hy
  rcases hcov x hx with h | h
  · rw [legalizeInstr_of_tiedOk _ x (tiedOk_of_covered h), List.mem_singleton] at hy
    subst hy
    exact covered_of_frameAgree h hf hl
  · exact Or.inl (legalizeInstr_threeAddr _ _ x h y hy)

end TwoAddr

end CatCrypt.Crypto.SecureCompilation.X86Backend.PrintedCoveredFuse
