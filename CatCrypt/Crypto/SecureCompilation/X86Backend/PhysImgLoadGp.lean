/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSideOpt

/-!
# The 64-bit moves of the allocator output

The side condition `PhysImgOpt.loadSideB` of the load CSE asks that every 64-bit move into a
general-purpose name is a move of `slotMov?` (`wideMovB`), and the load-CSE comparison of
gate 22 asks that no 64-bit move is between two memory names (`PhysImgSidePass.memMovFreeB`).
Both follow from one property of every instruction, `WideOk`: a 64-bit move has a
general-purpose or memory destination, is no move between two memory names and, into a
general-purpose name, is a move of `slotMov?`.

`WideOk` is closed under the source rewrites of the copy propagation, which write a
general-purpose register or an immediate. The fusion of the high products writes moves
between `RDX`, `R14`, `R15`, a source of the `MULXHI` and a spilled destination, so it keeps
`WideOk` when no `MULXHI` source is a cell name `mem.B.off`. The register-allocated expansion
`physExpand` writes moves between names of the operand map, the scratch registers and the
save slots, with a copy between two spill slots routed through `R15`, so it keeps `WideOk`
when the operand map renders every register as a general-purpose register or a spill slot
`k.N`. A register-indexed store of a spilled value at an index in `R15` writes through
`MOV:64 mem.R14.0, R15`, a move into a cell name from a general-purpose name.

## Main results

* `wideOk_rwClosed`, `memMovFreeB_of_wideOk`, `wideMovB_of_wideOk`: the closure under the
  copy propagation and the two checks of the load CSE.
* `wideOk_fuseMulHiBody`: the fusion keeps `WideOk`.
* `physExpand_wideOk`, `physExpand_noCell`: `WideOk` on every instruction of one expansion,
  and no two-source operation of an expansion reads a cell name.
* `wideOk_lfundefPhysAbiOfVirtCert`: `WideOk` on the fused body of the looped physical ABI
  export.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgLoadGp

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (gpNameB)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem (slotMov? cellParts?)
open CatCrypt.Crypto.Optimizer.LoadCSE (asWideReload isMemName isMemToMemMov isMov64Mnem
  asWideReload_eq)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSidePass (RwClosed OpRw memMovFreeB
  memMovFreeB_iff)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgOpt (wideMovB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape (physExpand physRmap notLivePin)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (x86Abi)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSideAlloc
  (lfundefPhysAbiOfVirtCert_body)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgEmit (extraSaves mem_extraSaves
  abiSaveOfExt_spec)

/-! ## 1. The predicate -/

/-- A 64-bit move `MOV d ← s` of the instruction has a general-purpose or memory destination,
    is no move between two memory names and, into a general-purpose name, is a move of
    `slotMov?`. -/
def WideOkR (i : LinstrR) : Prop :=
  ∀ d s mn, asWideReload i = some (d, s, mn) →
    (gpNameB d = true ∨ isMemName d = true) ∧ isMemToMemMov i = false ∧
      (gpNameB d = true → (slotMov? i).isSome = true)

/-- `WideOkR` of the instruction. -/
def WideOk (j : Linstr) : Prop := WideOkR j.li_i

/-- `WideOkR` of an operation from the condition on its 64-bit move shape, with a source that
    is no cell name for a `MOV:64` into a general-purpose name. -/
theorem wideOkR_lopn_gp {ds : List LOperand} {o : String} {ss : List LOperand}
    (h : ∀ d s, ds = [.reg d] → ss = [.reg s] → isMov64Mnem o = true →
      (gpNameB d = true ∨ isMemName d = true) ∧ (isMemName d && isMemName s) = false ∧
        (o = "MOV:64" → gpNameB d = true → cellParts? s = none)) :
    WideOkR (.Lopn ds o ss) := by
  intro d s mn hw
  obtain ⟨he, hm⟩ := asWideReload_eq hw
  simp only [LinstrR.Lopn.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  obtain ⟨h1, h2, h3⟩ := h d s rfl rfl hm
  refine ⟨h1, by simp [isMemToMemMov, hw, h2], fun hgp => ?_⟩
  simp only [isMov64Mnem, Bool.or_eq_true, beq_iff_eq] at hm
  rcases hm with rfl | rfl
  · have c1 : cellParts? d = none :=
      PhysImgOpt.cellParts?_physGP (by rwa [PhysImgFold.isPhysGP_eq_gpNameB])
    simp [slotMov?, c1, h3 rfl hgp]
  · simp [slotMov?]

/-- `WideOkR` of an operation from the condition on its 64-bit move shape. -/
theorem wideOkR_lopn {ds : List LOperand} {o : String} {ss : List LOperand}
    (h : ∀ d s, ds = [.reg d] → ss = [.reg s] → isMov64Mnem o = true →
      (gpNameB d = true ∨ isMemName d = true) ∧ (isMemName d && isMemName s) = false ∧
        (o = "MOV:64" → cellParts? d = none ∧ cellParts? s = none)) :
    WideOkR (.Lopn ds o ss) :=
  wideOkR_lopn_gp fun d s h1 h2 hm =>
    (h d s h1 h2 hm).imp_right fun k => k.imp_right fun k3 ho _ => (k3 ho).2

/-- An instruction that is no operation has no 64-bit move. -/
theorem wideOkR_of_not_lopn {i : LinstrR} (h : ∀ ds o ss, i ≠ .Lopn ds o ss) : WideOkR i := by
  intro d s mn hw
  exact absurd (asWideReload_eq hw).1 (h _ _ _)

/-! ## 2. The names -/

/-- A name the operand map of the allocator renders: a general-purpose register or a spill
    slot `k.N`. -/
def NameOk (n : String) : Prop := gpNameB n = true ∨ hasPrefix n "k." = true

theorem hasPrefix_mem_of_k {n : String} (h : hasPrefix n "k." = true) :
    hasPrefix n "mem." = false := by
  unfold hasPrefix at h ⊢
  rcases hl : n.toList with _ | ⟨c, _ | ⟨c', t⟩⟩ <;> simp_all [List.isPrefixOf]
  obtain ⟨rfl, rfl⟩ := h
  intro h'
  exact absurd h' (by decide)

theorem cellParts?_of_not_mem {n : String} (h : hasPrefix n "mem." = false) :
    cellParts? n = none := by
  simp [cellParts?, h]

theorem isMemName_eq_hasPrefix (n : String) :
    isMemName n = (hasPrefix n "k." || hasPrefix n "qsave." || hasPrefix n "mem.") :=
  LcmdReloadElim.isSlotName_eq_hasPrefix n

theorem isMemName_of_gp {n : String} (h : gpNameB n = true) : isMemName n = false := by
  cases hm : isMemName n with
  | false => rfl
  | true =>
    have := PhysImgSidePass.gpNameB_of_isSlotName (n := n) hm
    rw [h] at this
    cases this

theorem hasPrefix_k_of_gp {n : String} (h : gpNameB n = true) : hasPrefix n "k." = false := by
  have := isMemName_of_gp h
  rw [isMemName_eq_hasPrefix] at this
  simp only [Bool.or_eq_false_iff] at this
  exact this.1.1

theorem hasPrefix_mem_of_gp {n : String} (h : gpNameB n = true) :
    hasPrefix n "mem." = false := by
  have := isMemName_of_gp h
  rw [isMemName_eq_hasPrefix] at this
  simp only [Bool.or_eq_false_iff] at this
  exact this.2

theorem NameOk.cell {n : String} (h : NameOk n) : cellParts? n = none :=
  cellParts?_of_not_mem (h.elim hasPrefix_mem_of_gp hasPrefix_mem_of_k)

theorem NameOk.noMem {n : String} (h : NameOk n) : hasPrefix n "mem." = false :=
  h.elim hasPrefix_mem_of_gp hasPrefix_mem_of_k

/-- On a name of the operand map the memory class is the spill class. -/
theorem NameOk.isMem {n : String} (h : NameOk n) :
    Optimizer.LoadCSE.isMemName n = hasPrefix n "k." := by
  rcases h with h | h
  · rw [isMemName_of_gp h, hasPrefix_k_of_gp h]
  · rw [isMemName_eq_hasPrefix, h]; rfl

theorem NameOk.dst {n : String} (h : NameOk n) : gpNameB n = true ∨ isMemName n = true := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (by rw [isMemName_eq_hasPrefix, h]; rfl)

theorem nameOk_R15 : NameOk reloadScratch := Or.inl (by decide +kernel)
theorem nameOk_R14 : NameOk reloadScratch2 := Or.inl (by decide +kernel)
theorem nameOk_RDX : NameOk "RDX" := Or.inl (by decide +kernel)

/-- **A move between two names of the operand map** that are not both spill slots. -/
theorem wideOkR_names {d s o : String} (hd : NameOk d) (hs : NameOk s)
    (h : (hasPrefix d "k." && hasPrefix s "k.") = false) :
    WideOkR (.Lopn [.reg d] o [.reg s]) := by
  refine wideOkR_lopn fun d' s' h1 h2 _ => ?_
  simp only [List.cons.injEq, LOperand.reg.injEq, and_true] at h1 h2
  subst h1 h2
  exact ⟨hd.dst, by rw [hd.isMem, hs.isMem, h], fun _ => ⟨hd.cell, hs.cell⟩⟩

/-- A `MOVQ` into a general-purpose register. -/
theorem wideOkR_movq_gp {d s : String} (hd : gpNameB d = true) :
    WideOkR (.Lopn [.reg d] "MOVQ" [.reg s]) := by
  refine wideOkR_lopn fun d' s' h1 h2 _ => ?_
  simp only [List.cons.injEq, LOperand.reg.injEq, and_true] at h1 h2
  subst h1 h2
  exact ⟨Or.inl hd, by rw [isMemName_of_gp hd]; rfl, fun h => absurd h (by decide)⟩

/-- A `MOVQ` into a memory name from a general-purpose register. -/
theorem wideOkR_movq_mem {d s : String} (hd : isMemName d = true) (hs : gpNameB s = true) :
    WideOkR (.Lopn [.reg d] "MOVQ" [.reg s]) := by
  refine wideOkR_lopn fun d' s' h1 h2 _ => ?_
  simp only [List.cons.injEq, LOperand.reg.injEq, and_true] at h1 h2
  subst h1 h2
  exact ⟨Or.inr hd, by rw [isMemName_of_gp hs]; simp, fun h => absurd h (by decide)⟩

/-! ## 3. The checks of the load CSE -/

/-- The condition of `WideOkR` on a 64-bit move. -/
theorem WideOkR.mov {d s o : String} (h : WideOkR (.Lopn [.reg d] o [.reg s]))
    (hm : isMov64Mnem o = true) :
    (gpNameB d = true ∨ isMemName d = true) ∧ (isMemName d && isMemName s) = false ∧
      (o = "MOV:64" → gpNameB d = true → cellParts? s = none) := by
  have hw : asWideReload (.Lopn [.reg d] o [.reg s]) = some (d, s, o) := by
    simp [asWideReload, hm]
  obtain ⟨h1, h2, h3⟩ := h d s o hw
  refine ⟨h1, by simpa [isMemToMemMov, hw] using h2, fun ho hgp => ?_⟩
  subst ho
  have h3 := h3 hgp
  revert h3
  simp only [slotMov?]
  split_ifs with hc hc'
  · simp
  · intro _
    exact (by simpa [Option.isSome_iff_ne_none] using hc' :
      cellParts? d = none ∧ cellParts? s = none).2
  · simp at hc

/-- **`WideOk` is closed under the source rewrites of the copy propagation**: a rewritten
    source is a general-purpose register or an immediate. -/
theorem wideOk_rwClosed : RwClosed WideOk := by
  intro i dsts opn srcs g hi he hg
  show WideOkR _
  unfold WideOk at hi
  rw [he] at hi
  refine wideOkR_lopn_gp fun d s h1 h2 hm => ?_
  subst h1
  rcases srcs with _ | ⟨a, _ | ⟨_, _⟩⟩ <;>
    simp only [List.map_cons, List.map_nil, List.cons.injEq, reduceCtorEq, and_false,
      and_true] at h2
  rcases hg a with ha | ⟨u, rfl, hf, -⟩
  · rw [ha] at h2
    subst h2
    exact hi.mov hm
  · rw [h2] at hf
    have hgp : LcmdCopyPropagate.isPhysGP s = true := by simpa [LcmdCopyPropagate.isFactSrc] using hf
    obtain ⟨k1, -, -⟩ := hi.mov hm
    refine ⟨k1, by rw [PhysImgSidePass.isMemName_of_isPhysGP hgp]; simp,
      fun _ _ => PhysImgOpt.cellParts?_physGP hgp⟩

theorem memMovFreeB_of_wideOk {b : Lcmd} (h : ∀ j ∈ b, WideOk j) : memMovFreeB b = true := by
  refine memMovFreeB_iff.mpr fun j hj => ?_
  cases hw : asWideReload j.li_i with
  | none => simp [isMemToMemMov, hw]
  | some p =>
    obtain ⟨d, s, mn⟩ := p
    exact (h j hj d s mn hw).2.1

theorem wideMovB_of_wideOk {b : Lcmd} (h : ∀ j ∈ b, WideOk j) : wideMovB b = true := by
  refine List.all_eq_true.mpr fun j hj => ?_
  cases hw : asWideReload j.li_i with
  | none => simp
  | some p =>
    obtain ⟨d, s, mn⟩ := p
    cases hg : gpNameB d with
    | false => simp [hg]
    | true => simp [hg, (h j hj d s mn hw).2.2 hg]

/-! ## 4. The high-product fusion -/

/-- A move into a general-purpose register or a spill slot from a name that is no cell name,
    one of the two a general-purpose register. -/
theorem wideOkR_mov {d s o : String} (hd : NameOk d) (hs : hasPrefix s "mem." = false)
    (hg : gpNameB d = true ∨ gpNameB s = true) : WideOkR (.Lopn [.reg d] o [.reg s]) := by
  refine wideOkR_lopn fun d' s' h1 h2 _ => ?_
  simp only [List.cons.injEq, LOperand.reg.injEq, and_true] at h1 h2
  subst h1 h2
  refine ⟨hd.dst, ?_, fun _ => ⟨hd.cell, cellParts?_of_not_mem hs⟩⟩
  rcases hg with hg | hg <;> simp [isMemName_of_gp hg]

/-- An operation with other than one destination register has no 64-bit move. -/
theorem wideOkR_multi {ds : List LOperand} {o : String} {ss : List LOperand}
    (h : ds.length ≠ 1) : WideOkR (.Lopn ds o ss) :=
  wideOkR_lopn fun _ _ h1 _ _ => absurd (by rw [h1]; rfl) h

theorem nameOk_of_isSpill {n : String} (h : (LOperand.reg n).isSpill = true) : NameOk n :=
  Or.inr (by rwa [PhysAbiShape.isSpill_eq] at h)

/-- Closes `WideOk` of one instruction of a fusion site. -/
local macro "site_one" : tactic => `(tactic|
  (show WideOkR _
   dsimp only
   first
    | (refine wideOkR_multi ?_; simp; done)
    | exact wideOkR_mov
        (by first
          | exact nameOk_R15 | exact nameOk_R14 | exact nameOk_RDX
          | exact nameOk_of_isSpill (by assumption))
        (by first
          | assumption
          | decide +kernel
          | exact (nameOk_of_isSpill (by assumption)).noMem)
        (by first | exact Or.inl (by decide +kernel) | exact Or.inr (by decide +kernel))))

/-- Closes `WideOk` of every instruction of a fusion site. -/
local macro "site_fin" : tactic => `(tactic|
  (split_ifs <;>
    simp only [List.forall_mem_cons, List.forall_mem_append, List.nil_append,
      List.cons_append, List.singleton_append, List.not_mem_nil, IsEmpty.forall_iff,
      forall_const, implies_true, and_true, true_and] <;>
    (try and_intros) <;> site_one))

open CatCrypt.Crypto.SecureCompilation.X86Backend.FheMontMulEmit in
/-- The paired site of the fusion of `MULXHI d, [s1, s2]` with a register high destination
    or outside the looped-body mode: the save and the pin of `RDX`, the reload of a spilled
    `s2`, the `MULX`, the store of a spilled high word and the restore of `RDX`. -/
theorem wideOk_pairSite (s : Bool) (ii : Nat) (d s1 s2 loDst : String)
    (hs1 : hasPrefix s1 "mem." = false) :
    ∀ r ∈ (if s = true then [(⟨ii, .Lopn [.reg "R15"] "MOVQ" [.reg "RDX"]⟩ : Linstr)]
        else []) ++
        (⟨ii, .Lopn [.reg "RDX"] "MOV:64" [.reg s1]⟩ : Linstr) ::
          ((if (!(s && s2 == "RDX") && (LOperand.reg s2).isSpill) = true then
              [(⟨ii, .Lopn [.reg (if (s && s2 == "RDX") = true then reloadScratch
                  else if (LOperand.reg s2).isSpill = true then reloadScratch2 else s2)]
                  "MOV:64" [.reg s2]⟩ : Linstr)]
            else []) ++
            (⟨ii, .Lopn
                [.reg (if (LOperand.reg loDst).isSpill = true then
                    if (LOperand.reg d).isSpill = true then
                      if ((if (s && s2 == "RDX") = true then reloadScratch
                          else if (LOperand.reg s2).isSpill = true then reloadScratch2 else s2) ==
                          reloadScratch) = true then reloadScratch2
                      else reloadScratch
                    else d
                  else loDst),
                  .reg (if (LOperand.reg d).isSpill = true then
                    if ((if (s && s2 == "RDX") = true then reloadScratch
                        else if (LOperand.reg s2).isSpill = true then reloadScratch2 else s2) ==
                        reloadScratch) = true then reloadScratch2
                    else reloadScratch
                  else d)]
                "MULX"
                [.reg (if (s && s2 == "RDX") = true then reloadScratch
                  else if (LOperand.reg s2).isSpill = true then reloadScratch2 else s2)]⟩ :
              Linstr) ::
              ((if (LOperand.reg d).isSpill = true then
                  [(⟨ii, .Lopn [.reg d] "MOV:64"
                    [.reg (if (LOperand.reg d).isSpill = true then
                      if ((if (s && s2 == "RDX") = true then reloadScratch
                          else if (LOperand.reg s2).isSpill = true then reloadScratch2 else s2) ==
                          reloadScratch) = true then reloadScratch2
                      else reloadScratch
                    else d)]⟩ : Linstr)]
                else []) ++
                if (s && loDst != "RDX") = true then
                  [(⟨ii, .Lopn [.reg "RDX"] "MOVQ" [.reg "R15"]⟩ : Linstr)]
                else [])),
      WideOk r := by
  simp only [List.forall_mem_cons, List.forall_mem_append]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · split_ifs <;> simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true]
    all_goals site_one
  · site_one
  · split_ifs <;> simp only [List.forall_mem_cons, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, and_true] <;> first | site_one | simp_all
  · exact wideOkR_multi (by simp)
  · split_ifs with h1 h2 <;> simp only [List.forall_mem_cons, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, and_true]
    all_goals site_one
  · split_ifs <;> simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true]
    all_goals site_one

open CatCrypt.Crypto.SecureCompilation.X86Backend.FheMontMulEmit in
/-- **One step of the fusion keeps `WideOk`**: it writes the instruction itself, or a fusion
    site of a `MULXHI` whose sources have no prefix `mem.`, whose every instruction
    satisfies `WideOk`. -/
theorem fuseMulHiAux_cons_wide (s : Bool) (env : ScratchEnv) (pend : List (String × String))
    (i : Linstr) (rest : Lcmd)
    (hi : ∀ d opn s1 s2, i.li_i = .Lopn [.reg d] opn [.reg s1, .reg s2] →
      isMulHiMnem opn = true → hasPrefix s1 "mem." = false ∧ hasPrefix s2 "mem." = false) :
    ∃ L env' pend', fuseMulHiAux s env pend (i :: rest) = L ++ fuseMulHiAux s env' pend' rest ∧
      (L = [i] ∨ ∀ r ∈ L, WideOk r) := by
  rw [fuseMulHiAux]
  split
  · rename_i d opn s1 s2 heq
    split
    · exact ⟨[i], _, _, rfl, Or.inl rfl⟩
    · rename_i hlo
      by_cases hhi : isMulHiMnem opn = true
      · obtain ⟨hs1, hs2⟩ := hi d opn s1 s2 heq hhi
        simp only [hhi, if_true]
        split
        · split
          · split
            · rename_i hsp _
              refine ⟨_, _, _, rfl, Or.inr ?_⟩
              have hd : (LOperand.reg d).isSpill = true := by
                simp only [Bool.and_eq_true] at hsp; exact hsp.2
              unfold squareSite
              site_fin
            · exact ⟨[i], _, _, rfl, Or.inl rfl⟩
          · split
            · exact ⟨[i], _, _, rfl, Or.inl rfl⟩
            · have hassoc : ∀ (a b c e t : Lcmd) (x y : Linstr),
                  a ++ x :: (b ++ y :: ((c ++ e) ++ t)) =
                    (a ++ x :: (b ++ y :: (c ++ e))) ++ t := by
                intros; simp
              refine ⟨_, _, _, hassoc _ _ _ _ _ _ _, Or.inr ?_⟩
              exact wideOk_pairSite s i.li_ii d s1 s2 _ hs1
        · exact ⟨[i], _, _, rfl, Or.inl rfl⟩
      · simp only [hhi, if_false, Bool.false_eq_true]
        exact ⟨[i], _, _, rfl, Or.inl rfl⟩
  · exact ⟨[i], _, _, rfl, Or.inl rfl⟩

/-- No `MULXHI` of the body has a source with the prefix `mem.`. -/
def MulHiNoCell (b : Lcmd) : Prop :=
  ∀ i ∈ b, ∀ d opn s1 s2, i.li_i = .Lopn [.reg d] opn [.reg s1, .reg s2] →
    FheMontMulEmit.isMulHiMnem opn = true →
      hasPrefix s1 "mem." = false ∧ hasPrefix s2 "mem." = false

open CatCrypt.Crypto.SecureCompilation.X86Backend.FheMontMulEmit in
theorem wideOk_fuseMulHiAux (s : Bool) :
    ∀ (b : Lcmd) (env : ScratchEnv) (pend : List (String × String)), (∀ j ∈ b, WideOk j) →
      MulHiNoCell b → ∀ j ∈ fuseMulHiAux s env pend b, WideOk j
  | [], env, pend, _, _, r, hr => by rw [fuseMulHiAux] at hr; cases hr
  | i :: rest, env, pend, h, hm, r, hr => by
    obtain ⟨L, env', pend', he, hL⟩ :=
      fuseMulHiAux_cons_wide s env pend i rest (hm i List.mem_cons_self)
    rw [he, List.mem_append] at hr
    rcases hr with hr | hr
    · rcases hL with rfl | hL
      · simp only [List.mem_singleton] at hr
        subst hr
        exact h _ List.mem_cons_self
      · exact hL r hr
    · exact wideOk_fuseMulHiAux s rest env' pend' (fun j hj => h j (List.mem_cons_of_mem _ hj))
        (fun j hj => hm j (List.mem_cons_of_mem _ hj)) r hr

/-- **The fusion keeps `WideOk`** on a body none of whose `MULXHI`s has a source with the
    prefix `mem.`: every move of a fusion site is between `RDX`, `R14`, `R15`, a source of
    the `MULXHI` and a spilled destination. -/
theorem wideOk_fuseMulHiBody {b : Lcmd} (s : Bool) (h : ∀ j ∈ b, WideOk j)
    (hm : MulHiNoCell b) : ∀ j ∈ FheMontMulEmit.fuseMulHiBody b s, WideOk j :=
  wideOk_fuseMulHiAux s b [] [] h hm

/-! ## 5. The expansion -/

/-- An operand of the operand map: a register named by `NameOk`, or an indexed operand whose
    base and index have no prefix `mem.`. -/
def OpOk : LOperand → Prop
  | .reg n => NameOk n
  | .arrIdx b y _ => hasPrefix b "mem." = false ∧ hasPrefix y "mem." = false
  | _ => True

theorem opOk_R15 : OpOk (.reg reloadScratch) := nameOk_R15
theorem opOk_R14 : OpOk (.reg reloadScratch2) := nameOk_R14
theorem opOk_imm (v : Nat) : OpOk (.imm v) := trivial

theorem isSpill_R15 : (LOperand.reg reloadScratch).isSpill = false := by
  rw [PhysAbiShape.isSpill_eq]; decide +kernel

theorem isSpill_R14 : (LOperand.reg reloadScratch2).isSpill = false := by
  rw [PhysAbiShape.isSpill_eq]; decide +kernel

theorem isSpill_imm (v : Nat) : (LOperand.imm v).isSpill = false := rfl

/-- **A one-source operation on operands of the operand map** that are not both spill
    slots. -/
theorem wideOkR_ops {d s : LOperand} {o : String} (hd : OpOk d) (hs : OpOk s)
    (h : (d.isSpill && s.isSpill) = false) : WideOkR (.Lopn [d] o [s]) := by
  refine wideOkR_lopn fun d' s' h1 h2 _ => ?_
  simp only [List.cons.injEq, and_true] at h1 h2
  subst h1 h2
  simp only [PhysAbiShape.isSpill_eq] at h
  exact ⟨hd.dst, by rw [hd.isMem, hs.isMem, h], fun _ => ⟨hd.cell, hs.cell⟩⟩

theorem isMov64Mnem_strip {o : String} (h : isMov64Mnem o = true) :
    stripWidthTag o = "MOV" ∨ stripWidthTag o = "MOVQ" := by
  simp only [isMov64Mnem, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | rfl
  · exact Or.inl (by decide +kernel)
  · exact Or.inr (by decide +kernel)

/-- An operation whose mnemonic is no 64-bit move has no 64-bit move. -/
theorem wideOkR_nonmov {ds : List LOperand} {o : String} {ss : List LOperand}
    (h : isMov64Mnem o = false) : WideOkR (.Lopn ds o ss) :=
  wideOkR_lopn fun _ _ _ _ hm => absurd hm (by rw [h]; simp)

theorem nameOk_of_sib {n : String} (h : sibNameSpill n = true) : NameOk n :=
  Or.inr (by rwa [PhysAbiShape.sibNameSpill_eq] at h)

/-- An operation with other than one source has no 64-bit move. -/
theorem wideOkR_multiSrc {ds : List LOperand} {o : String} {ss : List LOperand}
    (h : ss.length ≠ 1) : WideOkR (.Lopn ds o ss) :=
  wideOkR_lopn fun _ _ _ h2 _ => absurd (by rw [h2]; rfl) h

/-- An operation with a source that is no register has no 64-bit move. -/
theorem wideOkR_nonreg {ds : List LOperand} {o : String} {x : LOperand}
    (h : ∀ n, x ≠ .reg n) : WideOkR (.Lopn ds o [x]) :=
  wideOkR_lopn fun _ s _ h2 _ => absurd (by simpa using h2) (h s)

/-- Closes `WideOkR` of one instruction of an expansion. -/
local macro "w_one" : tactic => `(tactic|
  first
    | trivial
    | (refine wideOkR_multi ?_; simp; done)
    | (refine wideOkR_multiSrc ?_; simp; done)
    | (refine wideOkR_nonreg ?_; simp; done)
    | (refine wideOkR_nonmov ?_; decide +kernel)
    | (refine wideOkR_ops ?_ ?_ ?_ <;>
        first
          | assumption | exact opOk_R15 | exact opOk_R14 | exact opOk_imm _
          | exact nameOk_of_isSpill (by assumption)
          | exact nameOk_of_sib (by assumption)
          | simp_all [isSpill_R15, isSpill_R14, isSpill_imm]))

/-- Closes `WideOkR` of every instruction of an expansion. -/
local macro "w_fin" : tactic => `(tactic|
  (simp only [List.forall_mem_cons, List.forall_mem_append, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, and_true, forall_const] <;>
    (try and_intros) <;> w_one))

theorem wide_legalizeMov {d s : LOperand} (mov : String) (hd : OpOk d) (hs : OpOk s) :
    ∀ r ∈ legalizeMov d s mov, WideOkR r := by
  unfold legalizeMov
  split_ifs <;> w_fin

theorem wide_legalizeBinop {d s : LOperand} (opn mov : String) (hd : OpOk d) (hs : OpOk s) :
    ∀ r ∈ legalizeBinop d s opn mov, WideOkR r := by
  unfold legalizeBinop
  split <;> w_fin

theorem wide_materializeWideImm {s : LOperand} (mov : String) (hs : OpOk s) :
    (∀ r ∈ (materializeWideImm s mov).1, WideOkR r) ∧ OpOk (materializeWideImm s mov).2 := by
  unfold materializeWideImm
  split
  · split
    · exact ⟨by w_fin, opOk_R14⟩
    · exact ⟨by simp, hs⟩
  · exact ⟨by simp, hs⟩

theorem wide_legalizeSibElem {o : LOperand} (ho : OpOk o) :
    (∀ r ∈ (legalizeSibElem o).1, WideOkR r) ∧ OpOk (legalizeSibElem o).2 := by
  cases o with
  | arrIdx b y sc =>
    obtain ⟨hb, hy⟩ := ho
    simp only [legalizeSibElem]
    refine ⟨?_, ?_⟩
    · split_ifs <;> w_fin
    · split_ifs <;> exact ⟨by first | assumption | decide +kernel,
        by first | assumption | decide +kernel⟩
  | _ => exact ⟨by simp [legalizeSibElem], by simp only [legalizeSibElem]; exact ho⟩

theorem wide_reloadMemrefBase (mbr : String → Option String) {o : LOperand} (ho : OpOk o) :
    (∀ r ∈ (reloadMemrefBase mbr o).1, WideOkR r) ∧ OpOk (reloadMemrefBase mbr o).2 := by
  cases o with
  | arrIdx b y sc =>
    simp only [reloadMemrefBase]
    split
    · refine ⟨?_, ⟨by decide +kernel, ho.2⟩⟩
      simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
        and_true]
      exact wideOkR_movq_gp (by decide +kernel)
    · exact ⟨by simp, ho⟩
  | _ => exact ⟨by simp [reloadMemrefBase], by simp only [reloadMemrefBase]; exact ho⟩

theorem wide_legalizeMemLoad {d s : LOperand} (opn mov : String) (hd : OpOk d) (hs : OpOk s) :
    ∀ r ∈ legalizeMemLoad d s opn mov, WideOkR r := by
  obtain ⟨h1, h2⟩ := wide_legalizeSibElem hs
  unfold legalizeMemLoad
  rcases he : legalizeSibElem s with ⟨pre, s'⟩
  rw [he] at h1 h2
  simp only at h1 h2 ⊢
  rw [List.forall_mem_append]
  exact ⟨h1, by split_ifs <;> w_fin⟩

theorem wide_lowerTwoAddr {d s0 s1 : LOperand} (opn mov : String) (hd : OpOk d) (h0 : OpOk s0)
    (h1 : OpOk s1) : ∀ r ∈ lowerTwoAddr d s0 s1 opn mov, WideOkR r := by
  obtain ⟨w1, w2⟩ := wide_materializeWideImm mov h1
  unfold lowerTwoAddr
  rcases he : materializeWideImm s1 mov with ⟨pre, s1'⟩
  rw [he] at w1 w2
  simp only at w1 w2 ⊢
  split <;> simp only [List.forall_mem_append]
  · exact ⟨w1, wide_legalizeBinop _ _ hd w2⟩
  · exact ⟨⟨wide_legalizeMov _ hd h0, w1⟩, wide_legalizeBinop _ _ hd w2⟩

theorem wide_lowerTwoAddrShiftImm {d s0 : LOperand} (v : Nat) (opn mov : String) (hd : OpOk d)
    (h0 : OpOk s0) : ∀ r ∈ lowerTwoAddrShiftImm d s0 v opn mov, WideOkR r := by
  unfold lowerTwoAddrShiftImm
  split_ifs
  · w_fin
  · w_fin
  · rw [List.forall_mem_append]
    exact ⟨wide_legalizeMov _ hd h0, by w_fin⟩

theorem wide_lowerNativeShiftRotate {d s : LOperand} (opn mov : String) (hd : OpOk d)
    (hs : OpOk s) : ∀ r ∈ lowerNativeShiftRotate d s opn mov, WideOkR r := by
  unfold lowerNativeShiftRotate
  split_ifs <;> w_fin

theorem wide_legalizeOneSrc (u64 : Bool) (opn : String) {d s : LOperand} (hd : OpOk d)
    (hs : OpOk s) : ∀ r ∈ legalizeOneSrc u64 opn d s, WideOkR r := by
  unfold legalizeOneSrc
  split
  · exact wide_legalizeMov _ hd hs
  · rename_i hc
    simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
      and_true]
    cases s with
    | reg n =>
      have hm : spillImmMovMnem u64 opn d (.reg n) = opn := rfl
      rw [hm]
      refine wideOkR_nonmov ?_
      cases h : isMov64Mnem opn with
      | false => rfl
      | true =>
        rcases isMov64Mnem_strip h with e | e <;> simp [e] at hc
    | _ => exact wideOkR_nonreg (by simp)

theorem wide_legalizeSpillDst {dsts srcs : List LOperand} (opn : String)
    (hd : ∀ x ∈ dsts, OpOk x) (hs : ∀ x ∈ srcs, OpOk x) (hn : srcs.length ≠ 1) :
    ∀ r ∈ legalizeSpillDst dsts opn srcs, WideOkR r := by
  unfold legalizeSpillDst
  split
  · next l h =>
    unfold cmovSpillDst? at h
    split at h
    · split at h
      · cases h
        simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
          and_true] at hd hs
        unfold cmovSpillSeq
        split_ifs <;> w_fin
      · cases h
    · cases h
  · split
    · next l _ h =>
      unfold setccSpill? at h
      split at h
      · split at h
        · cases h
          simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
            and_true] at hd hs
          w_fin
        · cases h
      · cases h
    · intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      exact wideOkR_multiSrc hn

/-- The store of `R15` into the cell `mem.R14.0`: a move into a memory name that is no
    general-purpose name, from a general-purpose name. -/
theorem wideOkR_cellR14 (o : String) :
    WideOkR (.Lopn [.reg ("mem." ++ reloadScratch2 ++ ".0")] o [.reg reloadScratch]) := by
  intro d s mn hw
  obtain ⟨he, -⟩ := asWideReload_eq hw
  simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq, and_true] at he
  obtain ⟨rfl, -, rfl⟩ := he
  refine ⟨Or.inr ?_, by simp [isMemToMemMov, hw, isMemName_of_gp (show gpNameB reloadScratch = true by decide +kernel)], fun h =>
    absurd h (by decide +kernel)⟩
  rw [isMemName_eq_hasPrefix]
  simp [hasPrefix, List.isPrefixOf, reloadScratch2]

theorem wide_legalizeMemStoreK (k : Option Nat) (dArr : LOperand) {addr val : LOperand}
    (opn mov : String) (ha : OpOk addr) (hv : OpOk val) :
    ∀ r ∈ legalizeMemStoreK k dArr addr val opn mov, WideOkR r := by
  unfold legalizeMemStoreK
  split
  · next l hc =>
    unfold constIdxStore? at hc
    split at hc
    · rcases k with _ | c <;> simp at hc
      obtain ⟨-, -, rfl⟩ := hc
      split_ifs <;> w_fin
    · cases hc
  · unfold legalizeMemStore
    obtain ⟨h1, h2⟩ := wide_legalizeSibElem ha
    rcases he : legalizeSibElem addr with ⟨pre, a'⟩
    rw [he] at h1 h2
    simp only at h1 h2 ⊢
    split
    · split_ifs
      · rw [List.forall_mem_append]
        refine ⟨h1, ?_⟩
        simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
          and_true]
        refine ⟨wideOkR_nonmov (by decide +kernel), ?_, wideOkR_cellR14 _⟩
        w_one
      · rw [List.forall_mem_append]; exact ⟨h1, by w_fin⟩
    · rw [List.forall_mem_append]; exact ⟨h1, by w_fin⟩
    · rw [List.forall_mem_append]; exact ⟨h1, by w_fin⟩

/-- **`WideOk` of every instruction of one expansion.** When the operand map sends every
    register to a general-purpose register or a spill slot `k.N` and the base and index of
    every indexed operand to names without the prefix `mem.`, every 64-bit move of
    `physExpand` has a general-purpose or memory destination, is no move between two memory
    names and, into a general-purpose name, is a move of `slotMov?`. -/
theorem physExpand_wideOk (shiftImm : ShiftImmOracle) (u64 : Bool) (rm : LOperand → LOperand)
    (mbr : String → Option String) (i : Linstr) (hg : ∀ x, OpOk (rm x)) :
    ∀ r ∈ physExpand shiftImm u64 rm mbr i, WideOk r := by
  obtain ⟨ii, w⟩ := i
  have hmap : ∀ (l : List LinstrR), (∀ r ∈ l, WideOkR r) →
      ∀ r ∈ l.map (fun r => (⟨ii, r⟩ : Linstr)), WideOk r := by
    intro l hl r hr
    obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
    exact hl r' hr'
  cases w with
  | Lopn ds o ss =>
    unfold physExpand
    dsimp only
    split
    · rename_i d _ opn s0 s1 _ heq
      cases heq
      have hd := hg d
      have h0 := hg s0
      have h1 := hg s1
      split
      · split
        · exact hmap _ (wide_lowerTwoAddrShiftImm _ _ _ hd h0)
        · exact hmap _ (wide_lowerTwoAddr _ _ hd h0 h1)
      · split
        · rename_i d' opn' addr val heq
          cases heq
          split
          · obtain ⟨k1, k2⟩ := wide_reloadMemrefBase mbr h0
            intro r hr
            rcases List.mem_append.mp hr with hr | hr
            · exact hmap _ k1 r hr
            · exact hmap _ (wide_legalizeMemStoreK _ _ _ _ k2 h1) r hr
          · exact hmap _ (wide_legalizeSpillDst _ (by simp [hd]) (by simp [h0, h1])
              (by simp))
        · rename_i heq
          cases heq
          refine hmap _ (wide_legalizeSpillDst _ (by simp [hg]) (by simp [hg]) (by simp))
        · rename_i hno
          exact absurd rfl (hno _ _ _)
    · rename_i d opn s heq
      cases heq
      have hd := hg d
      have hs := hg s
      split
      · exact hmap _ (wide_lowerNativeShiftRotate _ _ hd hs)
      · split
        · obtain ⟨k1, k2⟩ := wide_reloadMemrefBase mbr hs
          intro r hr
          rcases List.mem_append.mp hr with hr | hr
          · exact hmap _ k1 r hr
          · exact hmap _ (wide_legalizeMemLoad _ _ hd k2) r hr
        · exact hmap _ (wide_legalizeOneSrc _ _ hd hs)
    · rename_i dsts opn srcs h1 h2 heq
      cases heq
      intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      refine wideOkR_lopn fun d s e1 e2 _ => ?_
      obtain ⟨x, rfl, -⟩ := List.map_eq_singleton_iff.mp e1
      obtain ⟨y, rfl, -⟩ := List.map_eq_singleton_iff.mp e2
      exact absurd (h2 x y rfl rfl) id
    · rename_i hno
      exact absurd rfl (hno _ _ _)
  | _ =>
    intro r hr
    simp only [physExpand, List.mem_singleton] at hr
    subst hr
    exact wideOkR_of_not_lopn (by intro ds o ss h; cases h)

/-- The names with the prefix `mem.`, as a slot map. -/
def memSlots (n : String) : Option (String × Nat) :=
  if hasPrefix n "mem." = true then some ("", 0) else none

/-- **No two-source operation of an expansion reads a name with the prefix `mem.`** when
    the operand map sends every operand to one of `OpOk`. -/
theorem physExpand_noCell (shiftImm : ShiftImmOracle) (u64 : Bool) (rm : LOperand → LOperand)
    (mbr : String → Option String) (i : Linstr) (hg : ∀ x, OpOk (rm x)) :
    ∀ r ∈ physExpand shiftImm u64 rm mbr i, ∀ d opn s1 s2,
      r.li_i = .Lopn [.reg d] opn [.reg s1, .reg s2] →
        hasPrefix s1 "mem." = false ∧ hasPrefix s2 "mem." = false := by
  have hn : ∀ n, memSlots n = none ↔ hasPrefix n "mem." = false := by
    intro n; cases h : hasPrefix n "mem." <;> simp [memSlots, h]
  refine PhysImgSideOpt.physExpand_forall (slotArr := memSlots)
    (fun r => ∀ d opn s1 s2, r = .Lopn [.reg d] opn [.reg s1, .reg s2] →
      hasPrefix s1 "mem." = false ∧ hasPrefix s2 "mem." = false)
    (fun ds o ss hss d opn s1 s2 he => ?_) (fun q d opn s1 s2 he => by simp at he)
    (fun r hr d opn s1 s2 he => absurd he (hr _ _ _)) shiftImm u64 rm mbr i (fun x => ?_)
    ((hn _).mpr (by decide +kernel)) ((hn _).mpr (by decide +kernel))
  · simp only [LinstrR.Lopn.injEq] at he
    obtain ⟨-, -, rfl⟩ := he
    exact ⟨(hn _).mp (hss (.reg s1) (by simp)), (hn _).mp (hss (.reg s2) (by simp))⟩
  · have := hg x
    generalize rm x = o at this ⊢
    cases o with
    | reg n => exact (hn n).mpr this.noMem
    | arrIdx b y sc => exact ⟨(hn b).mpr this.1, (hn y).mpr this.2⟩
    | _ => trivial

/-! ## 6. The export -/

theorem gp_of_nameOk {n : String} (h : NameOk n) (hs : (LOperand.reg n).isSpill = false) :
    gpNameB n = true := by
  rcases h with h | h
  · exact h
  · rw [PhysAbiShape.isSpill_eq] at hs
    simp only at hs
    rw [h] at hs
    cases hs

theorem isMem_of_isSpill {n : String} (h : (LOperand.reg n).isSpill = true) :
    isMemName n = true := by
  rw [PhysAbiShape.isSpill_eq] at h
  simp only at h
  rw [isMemName_eq_hasPrefix, h]; rfl

/-- A `MOVQ` into a name of the operand map, from `R15` when the name is a spill slot. -/
theorem wideOkR_movq_name {n s : String} (h : NameOk n)
    (hs : (LOperand.reg n).isSpill = true → gpNameB s = true) :
    WideOkR (.Lopn [.reg n] "MOVQ" [.reg s]) := by
  cases hsp : (LOperand.reg n).isSpill with
  | true => exact wideOkR_movq_mem (isMem_of_isSpill hsp) (hs hsp)
  | false => exact wideOkR_movq_gp (gp_of_nameOk h hsp)

/-- `WideOk` of the instruction, and no two-source operation of it reads a name with the
    prefix `mem.`. -/
def LoadGpOk (j : Linstr) : Prop :=
  WideOk j ∧ ∀ d opn s1 s2, j.li_i = .Lopn [.reg d] opn [.reg s1, .reg s2] →
    hasPrefix s1 "mem." = false ∧ hasPrefix s2 "mem." = false

theorem loadGpOk_movq {j : Linstr} {d s : String} (he : j.li_i = .Lopn [.reg d] "MOVQ" [.reg s])
    (h : WideOkR (.Lopn [.reg d] "MOVQ" [.reg s])) : LoadGpOk j := by
  refine ⟨by unfold WideOk; rw [he]; exact h, fun d' opn s1 s2 he' => ?_⟩
  rw [he] at he'
  simp at he'

theorem gp_R15 : gpNameB reloadScratch = true := by decide +kernel

theorem isMemName_qsave (R : String) : isMemName ("qsave." ++ R) = true := by
  rw [isMemName_eq_hasPrefix]
  simp [hasPrefix, List.isPrefixOf]

/-- The prologue and the saves of the further argument registers: `MOVQ` moves of a
    general-purpose register into a save slot, and of `RSI` into `R14`. -/
theorem prologue_loadGpOk (virt : Lfundef) (tbl : Array Nat) (abiArgs : List String) :
    ∀ j ∈ buildPrologue virt tbl (fun _ => none) ++ extraSaves abiArgs, LoadGpOk j := by
  intro j hj
  rcases List.mem_append.mp hj with hj | hj
  · simp only [buildPrologue, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      refine loadGpOk_movq rfl ?_
    · exact wideOkR_movq_mem (isMemName_qsave "RDI") (by decide +kernel)
    · exact wideOkR_movq_mem (isMemName_qsave "RSI") (by decide +kernel)
    · exact wideOkR_movq_mem (isMemName_qsave "RBX") (by decide +kernel)
    · exact wideOkR_movq_mem (isMemName_qsave "RBP") (by decide +kernel)
    · exact wideOkR_movq_mem (isMemName_qsave "R12") (by decide +kernel)
    · exact wideOkR_movq_mem (isMemName_qsave "R13") (by decide +kernel)
    · exact wideOkR_movq_mem (isMemName_qsave "R14") (by decide +kernel)
    · exact wideOkR_movq_mem (isMemName_qsave "R15") (by decide +kernel)
    · exact wideOkR_movq_gp (by decide +kernel)
  · obtain ⟨r, s, hs, rfl⟩ := mem_extraSaves hj
    obtain ⟨rfl, hr⟩ := abiSaveOfExt_spec hs
    refine loadGpOk_movq rfl (wideOkR_movq_mem (isMemName_qsave r) ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

/-- The argument materialization: `MOVQ` moves into a materialized argument name, through
    `R15` when the name is a spill slot. -/
theorem materialize_loadGpOk (virt : Lfundef) (tbl : Array Nat) (abiArgs : List String)
    (hmat : ∀ j, NameOk (physNameForBody virt.lfd_body tbl (argName j))) :
    ∀ j ∈ buildArgPtrMaterialize virt tbl abiArgs (fun _ => none), LoadGpOk j := by
  intro j hj
  unfold buildArgPtrMaterialize at hj
  obtain ⟨⟨abiReg, k⟩, -, hj⟩ := List.mem_flatMap.mp hj
  have hk := hmat k
  simp only at hj
  split at hj
  · simp at hj
  · generalize physNameForBody virt.lfd_body tbl (argName k) = p at hj hk
    split_ifs at hj <;>
      rcases hs : abiSlotOfExt abiReg with _ | s <;>
      simp only [hs, List.mem_cons, List.not_mem_nil, or_false] at hj
    all_goals rcases hj with rfl | rfl
    all_goals refine loadGpOk_movq rfl ?_
    all_goals first
      | exact wideOkR_movq_gp gp_R15
      | exact wideOkR_movq_name hk (fun _ => gp_R15)
      | exact wideOkR_movq_name hk (fun h => absurd h (by assumption))

/-- The callee-saved restores: `MOVQ` moves of a save slot into a general-purpose
    register. -/
theorem epilogue_loadGpOk : ∀ j ∈ calleeSaveRestoreEpilogue, LoadGpOk j := by
  intro j hj
  simp only [calleeSaveRestoreEpilogue, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact loadGpOk_movq rfl (wideOkR_movq_gp (by decide +kernel))

/-- **`WideOk` on the fused export body.** Under the hypotheses of
    `PhysImgSideAlloc.lfundefPhysAbiOfVirtCert_body`, when every name the allocation table
    renders for the body is a general-purpose register or a spill slot `k.N` (`hname`), so is
    every materialized argument name (`hmat`), every 64-bit move of the looped-body fusion of
    the export body has a general-purpose or memory destination, is no move between two memory
    names and, into a general-purpose name, is a move of `slotMov?`. -/
theorem wideOk_lfundefPhysAbiOfVirtCert
    (virt0 : Lfundef) (outArg' : String) (inArgs' accRegs : List String)
    (shiftImm : ShiftImmOracle) (abiArgs : List String) (abiTyin : List Nat)
    (posBind : Bool) (body1 : Lcmd)
    (hb1 : body1 = (if abiArgs.length ≥ 4 then
        [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
          ((List.range abiArgs.length).map (fun j => (.reg (argName j) : LOperand)))⟩]
        else []) ++ canonicalizeMemrefThread
          (accRegs.foldl (fun b r => aliasRegBody r outArg' b) virt0.lfd_body))
    (mbr : String → Option String)
    (hmbr : mbr = fun base =>
      (((argBasePairs posBind outArg' inArgs' abiArgs).filterMap (fun p =>
        match abiSaveOfExt p.2 with
        | some saveName => some (physNameForBody body1 (physTableOut body1 []) p.1, saveName)
        | none => none)).find? (fun p => p.1 == base)).map Prod.snd)
    (hcf : bodyHasCall body1 = false)
    (hname : ∀ n, NameOk (physRegName (physMapTabled
      (straightCallComposeTable body1 (physTableOut body1 [] [])) (nameSlot body1 n))))
    (hmat : ∀ j, NameOk (physNameForBody body1 (physTableOut body1 []) (argName j))) :
    let b0 := (lfundefPhysAbiOfVirtCert virt0 outArg' inArgs' accRegs shiftImm abiArgs
      abiTyin x86Abi posBind).1.lfd_body
    ∀ j ∈ FheMontMulEmit.fuseMulHiBody b0 true, WideOk j := by
  intro b0
  have hrmE : physRmap body1 [] =
      fun o =>
        remapOperand body1 (straightCallComposeTable body1 (physTableOut body1 [] [])) o := by
    simp only [physRmap, hcf, Bool.false_eq_true, if_false]
  have hg : ∀ x, OpOk (physRmap body1 [] x) := by
    intro x
    rw [hrmE]
    cases x with
    | reg n => exact hname n
    | arrIdx b y sc => exact ⟨(hname b).noMem, (hname y).noMem⟩
    | _ => trivial
  have hparts : (∀ j ∈ b0, WideOk j) ∧ MulHiNoCell b0 := by
    simp only [b0]
    rw [lfundefPhysAbiOfVirtCert_body virt0 outArg' inArgs' accRegs shiftImm abiArgs abiTyin
      posBind body1 hb1 mbr hmbr hcf]
    have key : ∀ j ∈ (buildPrologue { virt0 with lfd_body := body1 } (physTableOut body1 [])
          (fun _ => none) ++ extraSaves abiArgs) ++
        (buildArgPtrMaterialize { virt0 with lfd_body := body1 } (physTableOut body1 [])
            abiArgs (fun _ => none) ++
          insertEpilogue ((body1.flatMap (physExpand (PhysImgSideAlloc.certShiftImm shiftImm body1)
              (LprogAsmPrinter.bodyIsU64 body1) (physRmap body1 []) mbr)).filter notLivePin)
            calleeSaveRestoreEpilogue), LoadGpOk j := by
      intro j hj
      rcases List.mem_append.mp hj with hj | hj
      · exact prologue_loadGpOk _ _ abiArgs j hj
      · rcases List.mem_append.mp hj with hj | hj
        · exact materialize_loadGpOk _ _ abiArgs hmat j hj
        · unfold insertEpilogue at hj
          simp only [List.mem_append, List.mem_singleton] at hj
          rcases hj with (hj | hj) | rfl
          · obtain ⟨i, -, hj⟩ := List.mem_flatMap.mp
              (List.mem_of_mem_filter (List.dropLast_subset _ hj))
            exact ⟨physExpand_wideOk _ _ _ mbr i hg j hj,
              physExpand_noCell _ _ _ mbr i hg j hj⟩
          · exact epilogue_loadGpOk j hj
          · exact ⟨wideOkR_of_not_lopn (by intro ds o ss h; cases h),
              fun _ _ _ _ h => by cases h⟩
    exact ⟨fun j hj => (key j hj).1, fun j hj d opn s1 s2 he _ => (key j hj).2 d opn s1 s2 he⟩
  exact wideOk_fuseMulHiBody true hparts.1 hparts.2

end CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgLoadGp
