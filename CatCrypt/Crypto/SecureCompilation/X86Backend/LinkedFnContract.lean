/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.SepLogic.ContractX86
public import CatCrypt.Crypto.SecureCompilation.SepLogic.Abi
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnCallee
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCallProbe

/-!
# The fixed contract of a linked function

The contract `LinkedFn.contract l` of a linked function `l` is derived from its layout, its
meaning, its clobbered registers and its frame size. Its logical variables (`CallVar`) are
the register file at entry `rv`, the argument values `vals` and the return index `ret`; the
stack register at entry is `rv "%rsp"`.

* The precondition (`LinkedFn.entryAt` with the definedness of the meaning at `vals`): the
  registers `abiRegs` of the layout hold their values under `rv`; the words of the pointer
  regions of the layout are owned and pairwise separated, and the layout reads `vals` from
  them; the return word at the stack register holds `ret`; the clobbered registers outside
  `abiRegs`, the flags and the `frame` bytes below the stack register are owned; and, joined
  by `SAssert.conj`, the stack parameters at entry and the locations of the result read-back.
* The postcondition: the locations of the precondition are owned, the stack register and the
  return word hold their entry values, and the read-back of the result from the entry
  registers is the value of the meaning at `vals`.
* The write set (`LinkedFn.contractWrites`): the clobbered registers other than `%rsp`, the
  flags, the `frame` bytes below the stack register and the memory locations of the result
  read-back.
* The public relation: `AbiLayout.PubAgree` of the layout.

The write set and the footprint of the postcondition lie in the footprint of the
precondition (`contractWrites_subset`, `contractPost_fp_subset`), so `SContract.frame`
applies to the contract with every frame separated from the precondition (`Meets.frame`).

`LinkedFn.Meets l` states that the bytes of `l` decode to a block whose leaky runs under
the constant-time regime `.doitm` meet the contract. The interface `LinkedFn.contractSig` reads the contract as a
`CalleeSig`; a function that meets its contract meets that interface
(`calleeSpec_of_meets`), is a `WordCallee` under a word layout (`wordCallee_of_meets`) and an
`OutCallee` under an out layout (`outCallee_of_meets`).

## Main definitions

* `CallVar`: the logical variables of a call.
* `LinkedFn.entryAt`, `LinkedFn.contractPre`, `LinkedFn.contractPost`,
  `LinkedFn.contractWrites`, `LinkedFn.contract`: the contract.
* `LinkedFn.Meets`: the code of a linked function meets its contract.
* `LinkedFn.contractSig`, `LinkedFn.Room`: the interface of the contract, and the entry
  states at which its precondition holds once the meaning is defined.

## Main results

* `holds_entryAt`: the facts of the precondition used by the adapters.
* `entryOf_popRet`: an entry state whose stack register addresses the return word `ret` is the
  entry state of a call with return index `ret`.
* `meets_of_calleeSpec`, `meets_of_wordSig`: the contract from a specification of an
  interface, and from the word interface `wordSig` of the record.
* `contractWrites_subset`, `contractPost_fp_subset`, `Meets.frame`: the footprint lemmas and
  the frame rule at the contract.
* `calleeSpec_of_meets`, `footBelow_contractSig`, `footBelowOut_contractSig`: the interface
  of the contract.
* `wordCallee_of_meets`, `outCallee_of_meets`: the readings of the interface.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Crypto.SecureCompilation.SepLogic
open CatCrypt.Crypto.SecureCompilation.SepLogic.X86
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpOk phys evalInstrA_leaFrame)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape (leaFrame)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (cellAt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee
  (CalleeRun CalleeSig CalleeSpec InFrame runOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall (WordCallee FootBelow)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallOut (OutCallee FootBelowOut)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCallProbe (entryOf retWord entryOf_eq
  entryOf_regs)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnCallee
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
  (AState AMem read64 write64 InRange8 write64_add write64_of_not_inRange)
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout AbiArg ArgKind ResultKind wordsAt)
open CatCrypt.Crypto.Hax (LinkedFn wordVal dec_wordVal insVals)
open CatCrypt.Crypto.Hax.ImpToNF (dec)
open _root_.Hax (Value)
open Footprinted SAssert

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnContract

/-! ## 1. The return word at the entry of a call -/

/-- Writing back the word read at an address keeps the memory. -/
theorem write64_read64_self (m : AMem) (a : BitVec 64) : write64 m a (read64 m a) = m := by
  funext x
  by_cases hx : InRange8 a x
  · obtain ⟨k, hk, rfl⟩ : ∃ k, k < 8 ∧ x = a + BitVec.ofNat 64 k :=
      ⟨(x - a).toNat, hx, by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
        omega⟩
    rw [write64_add m a _ k hk]
    apply BitVec.eq_of_toNat_eq
    have h0 := (m a).isLt
    have h1 := (m (a + BitVec.ofNat 64 1)).isLt
    have h2 := (m (a + BitVec.ofNat 64 2)).isLt
    have h3 := (m (a + BitVec.ofNat 64 3)).isLt
    have h4 := (m (a + BitVec.ofNat 64 4)).isLt
    have h5 := (m (a + BitVec.ofNat 64 5)).isLt
    have h6 := (m (a + BitVec.ofNat 64 6)).isLt
    have h7 := (m (a + BitVec.ofNat 64 7)).isLt
    simp only [read64, BitVec.toNat_ofNat]
    interval_cases k <;> simp <;> omega
  · exact write64_of_not_inRange m a _ x hx

/-- The memory at the entry of a call is the memory before the call with the return index
    stored in the return word. -/
theorem entryOf_mem_eq (ret : Nat) (s : AState) :
    (entryOf ret s).mem = write64 s.mem (retWord s) (BitVec.ofNat 64 ret) := by
  have h1 := (evalInstrA_leaFrame s (-8)).1 "%rsp"
  have h2 := (evalInstrA_leaFrame s (-8)).2
  rw [if_pos rfl] at h1
  rw [entryOf_eq]
  show write64 (CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem.evalInstrA s (leaFrame (-8))).mem
    ((CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem.evalInstrA s (leaFrame (-8))).regs "%rsp"
      + BitVec.ofInt 64 0) _ = _
  rw [h1, h2]
  simp [retWord]
  rfl

/-- The state before a call whose entry state is `s`: the stack register raised by eight. -/
def popRet (s : AState) : AState :=
  { s with regs := Function.update s.regs "%rsp" (s.regs "%rsp" + 8) }

/-- **An entry state is the entry state of a call.** If the stack register of `s` addresses a
    word holding the return index `ret`, then `s` is the state at the callee's entry of the
    call with return index `ret` from `popRet s`. -/
theorem entryOf_popRet {ret : Nat} {s : AState}
    (h : read64 s.mem (s.regs "%rsp") = BitVec.ofNat 64 ret) : entryOf ret (popRet s) = s := by
  obtain ⟨rs, fl, m⟩ := s
  have hsp : rs "%rsp" + 8#64 + 18446744073709551608#64 = rs "%rsp" := by bv_omega
  have hr : (entryOf ret (popRet ⟨rs, fl, m⟩)).regs = rs := by
    funext r
    rw [entryOf_regs]
    by_cases hr : r = "%rsp"
    · subst hr
      simp [popRet, retWord, hsp]
    · simp [popRet, hr]
  have hm : (entryOf ret (popRet ⟨rs, fl, m⟩)).mem = m := by
    rw [entryOf_mem_eq]
    have hw : retWord (popRet ⟨rs, fl, m⟩) = rs "%rsp" := by simp [popRet, retWord, hsp]
    rw [hw]
    change write64 m (rs "%rsp") (BitVec.ofNat 64 ret) = m
    rw [← show read64 m (rs "%rsp") = BitVec.ofNat 64 ret from h]
    exact write64_read64_self m _
  have hf : (entryOf ret (popRet ⟨rs, fl, m⟩)).flags = fl := rfl
  cases he : entryOf ret (popRet ⟨rs, fl, m⟩)
  simp_all

/-! ## 2. The assertions of the contract -/

/-- **The logical variables of a call**: the register file at the callee's entry, the
    argument values and the return index. -/
structure CallVar where
  /-- The register file at entry. -/
  rv : String → BitVec 64
  /-- The argument values. -/
  vals : List Value
  /-- The return index stored in the return word. -/
  ret : Nat

/-- The stack register at entry of the logical variables `a`. -/
def CallVar.sp (a : CallVar) : BitVec 64 := a.rv "%rsp"

/-- The address state with the register file `rv` and zero memory, the entry state at which
    a result read-back reads the entry registers. -/
def entryRegs (rv : String → BitVec 64) : AState := { regs := rv, mem := fun _ => 0 }

/-- The locations of the five flags. -/
def flagLocs : Set Loc := Set.range Loc.flag

/-- The memory locations of the `F` bytes below the address `sp`. -/
def stackRoom (sp : BitVec 64) (F : Nat) : Set Loc := Loc.mem '' {x | InFrame sp F x}

/-- The memory locations of the pointer regions of the layout `σ` at the registers `rv`. -/
def regionLocs (σ : AbiLayout) (rv : String → BitVec 64) : Set Loc :=
  ⋃ p ∈ σ.regions, wordsLocs (regionWords (rv p.1) p.2)

/-- The pointer regions of the layout `σ` at the registers `rv`, owned and pairwise
    separated. -/
def regionsOwn (σ : AbiLayout) (rv : String → BitVec 64) : SAssert AState Loc :=
  bigSep (σ.regions.map fun p => own (wordsLocs (regionWords (rv p.1) p.2)))

/-- A pointer region of a parameter. -/
theorem mem_regions_of_words {σ : AbiLayout} {a : AbiArg} (ha : a ∈ σ.args) {n : Nat}
    (hk : a.kind = .words n) : (a.reg, n) ∈ σ.regions :=
  List.mem_filterMap.2 ⟨a, ha, by simp [AbiArg.region, hk]⟩

/-- **The argument values at entry**: the layout `σ` reads the values `vals` from the
    registers `rv` and the memory of the state, whose words it reads in its pointer
    regions. -/
def inputsAt (σ : AbiLayout) (rv : String → BitVec 64) (vals : List Value) :
    SAssert AState Loc where
  fp := regionLocs σ rv
  holds s := σ.args.map (·.read { s with regs := rv }) = vals
  supp s t h hs := by
    rw [← hs]
    refine List.map_congr_left fun a ha => ?_
    unfold AbiArg.read
    split
    · rfl
    · rename_i n hk
      simp only [wordsAt]
      congr 1
      refine List.map_congr_left fun j hj => ?_
      rw [read64_congr (agreeOn_anti (fun x hx => ?_) h)]
      exact Set.mem_biUnion (x := (a.reg, n)) (mem_regions_of_words ha hk)
        (Set.mem_biUnion (x := rv a.reg + BitVec.ofNat 64 (8 * j))
          ⟨j, List.mem_range.1 hj, rfl⟩ hx)

/-- The return word at the address `sp` holds the return index `ret`. -/
def retAt (sp : BitVec 64) (ret : Nat) : SAssert AState Loc :=
  memPts 8 sp (BitVec.ofNat 64 ret)

/-- **The result at the exit state**: the read-back of the result of the layout `σ` from the
    entry registers `rv` is the value of the meaning `sem` at `vals`. -/
def resultAt (σ : AbiLayout) (sem : List Value → Option Value) (rv : String → BitVec 64)
    (vals : List Value) : SAssert AState Loc where
  fp := resLocs (entryRegs rv) σ.result
  holds s' := ∃ v, sem vals = some v ∧ σ.ResultOf (entryRegs rv) s' v
  supp _ _ h := fun ⟨v, hv, hr⟩ => ⟨v, hv, hr.trans (read_congr (entryRegs rv) σ.result h)⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnContract

open CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnContract

namespace CatCrypt.Crypto.Hax.LinkedFn

/-- The clobbered registers of a linked function outside the registers its layout reads. -/
def scratch (l : LinkedFn) : Set Loc :=
  Loc.reg '' {r | r ∈ l.clob ∧ r ∉ abiRegs l.layout}

/-- **The resources at the entry of a call** of the linked function `l` at the logical
    variables `a`, without the definedness of the meaning. -/
def entryAt (l : LinkedFn) (a : CallVar) : SAssert AState Loc :=
  conj
    (regsAt (abiRegs l.layout) a.rv ∗ conj (regionsOwn l.layout a.rv) (inputsAt l.layout a.rv a.vals)
      ∗ retAt a.sp a.ret ∗ own l.scratch ∗ own flagLocs ∗ own (stackRoom a.sp l.frame))
    (conj (stackAt l.layout a.rv) (own (resLocs (entryRegs a.rv) l.layout.result)))

/-- **The precondition of the contract**: the resources at entry, and the meaning defined at
    the argument values. -/
def contractPre (l : LinkedFn) (a : CallVar) : SAssert AState Loc :=
  l.entryAt a ∗ ⌜(l.sem a.vals).isSome = true⌝

/-- **The postcondition of the contract**: the locations of the precondition owned, the stack
    register and the return word at their entry values, and the result of the meaning. -/
def contractPost (l : LinkedFn) (a : CallVar) : SAssert AState Loc :=
  conj (own (l.contractPre a).fp)
    (conj (regPts "%rsp" a.sp)
      (conj (retAt a.sp a.ret) (resultAt l.layout l.sem a.rv a.vals)))

/-- **The write set of the contract**: the clobbered registers other than `%rsp`, the flags,
    the `frame` bytes below the stack register, and the memory locations of the result. -/
def contractWrites (l : LinkedFn) (a : CallVar) : Set Loc := fun x =>
  match x with
  | .reg r => r ∈ l.clob ∧ r ≠ "%rsp"
  | .flag _ => True
  | .mem y => InFrame a.sp l.frame y ∨ Loc.mem y ∈ resLocs (entryRegs a.rv) l.layout.result

/-- **The contract of a linked function**, derived from its layout, meaning, clobbered
    registers and frame size. -/
def contract (l : LinkedFn) : ContractSpec AState Loc CallVar where
  pre := l.contractPre
  post := l.contractPost
  writes a _ := l.contractWrites a
  pub := l.layout.PubAgree

/-- **The code of a linked function meets its contract**: the bytes decode to a block whose
    leaky runs under the regime `.doitm` meet `LinkedFn.contract`. -/
structure Meets (l : LinkedFn) : Prop where
  /-- The code meets the contract. -/
  code : ∃ q, decodeLprog l.bytes = some q ∧ SContract (runOf .doitm q) l.contract

/-- **The interface of the contract** at the argument names `args` and the result name
    `res`: the clobbered registers of the record; as precondition, the precondition of the
    contract at some logical variables; as footprint, the memory of the write set; as
    postcondition, the postcondition at logical variables whose precondition holds at entry;
    and the public relation of the contract. -/
def contractSig (l : LinkedFn) (args : List String) (res : Option String) : CalleeSig where
  args := args
  res := res
  clob := fun x => l.clob.contains x
  pre s := ∃ a, (l.contractPre a).holds s
  foot s x := ∃ a, (l.contractPre a).holds s ∧ l.contractWrites a (.mem x)
  post s s' := ∃ a, (l.contractPre a).holds s ∧ (l.contractPost a).holds s'
  pub := l.layout.PubAgree

/-- The entry states at which the resources of a call hold at some logical variables. -/
def Room (l : LinkedFn) (s : AState) : Prop := ∃ a, (l.entryAt a).holds s

end CatCrypt.Crypto.Hax.LinkedFn

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnContract

/-! ## 3. The facts of the precondition -/

/-- The layout reads, at a state whose registers of `abiRegs` hold their values under `rv`,
    the values it reads with the register file `rv`. -/
theorem map_read_of_regs {σ : AbiLayout} {rv : String → BitVec 64} {s : AState}
    (h : ∀ r ∈ abiRegs σ, s.regs r = rv r) :
    σ.args.map (·.read { s with regs := rv }) = σ.args.map (·.read s) := by
  refine List.map_congr_left fun a ha => ?_
  have hr : s.regs a.reg = rv a.reg :=
    h _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map_of_mem ha)))
  unfold AbiArg.read
  split <;> simp [hr]

/-- **The facts of the resources at entry**: the registers of `abiRegs` hold their values,
    the stack register is `a.sp`, the layout reads the argument values, the return word holds
    the return index, and the return word lies outside the `frame` bytes below the stack
    register. -/
theorem holds_entryAt {l : LinkedFn} {a : CallVar} {s : AState} (h : (l.entryAt a).holds s) :
    (∀ r ∈ abiRegs l.layout, s.regs r = a.rv r) ∧ s.regs "%rsp" = a.sp
      ∧ l.layout.args.map (·.read s) = a.vals
      ∧ read64 s.mem a.sp = BitVec.ofNat 64 a.ret
      ∧ ∀ x, InRange8 a.sp x → ¬ InFrame a.sp l.frame x := by
  obtain ⟨⟨-, hregs, -, ⟨-, hin⟩, hd, hret, -⟩, -⟩ := h
  have hregs' : ∀ r ∈ abiRegs l.layout, s.regs r = a.rv r := hregs
  refine ⟨hregs', hregs' _ List.mem_cons_self, (map_read_of_regs hregs').symm.trans hin,
    (readLE_eight_eq_addrMem_read64 _ _).symm.trans hret, fun x hx hF => ?_⟩
  exact Set.disjoint_left.1 hd (show Loc.mem x ∈ (retAt a.sp a.ret).fp from ⟨x, hx, rfl⟩)
    (Or.inr (Or.inr ⟨x, hF, rfl⟩))

/-- The resources at entry from the precondition of the contract. -/
theorem entryAt_of_pre {l : LinkedFn} {a : CallVar} {s : AState}
    (h : (l.contractPre a).holds s) : (l.entryAt a).holds s := h.2.1

/-- The meaning is defined at the argument values of a state satisfying the precondition. -/
theorem sem_isSome_of_pre {l : LinkedFn} {a : CallVar} {s : AState}
    (h : (l.contractPre a).holds s) : (l.sem a.vals).isSome = true := h.2.2

/-! ## 4. The contract from a callee specification -/

/-- **The contract from a specification of an interface.** Let the bytes of `l` decode to
    `q`, whose leaky runs meet an interface `c` whose precondition holds wherever the
    precondition of the contract does, whose clobbered registers are among those of `l`,
    whose footprint is among the `frame` bytes below the entry stack register, whose
    postcondition gives the result of the contract, and whose public relation follows from
    agreement on the public data of the layout. Then `l` meets its contract. -/
theorem meets_of_calleeSpec {l : LinkedFn} {q : List RInstr}
    (hq : decodeLprog l.bytes = some q) {c : CalleeSig} (hX : CalleeSpec (runOf .doitm q) c)
    (hpre : ∀ a s, (l.contractPre a).holds s → c.pre s)
    (hclob : ∀ r, c.clob r = true → r ∈ l.clob)
    (hfoot : ∀ s x, c.pre s → c.foot s x → InFrame (s.regs "%rsp") l.frame x)
    (hpost : ∀ a s s', (l.contractPre a).holds s → c.post s s' →
      (resultAt l.layout l.sem a.rv a.vals).holds s')
    (hpub : ∀ s₁ s₂, l.layout.PubAgree s₁ s₂ → c.pub s₁ s₂) : l.Meets := by
  refine ⟨q, hq, ⟨fun a s hs => hX.halts s (hpre a s hs), ?_, ?_, ?_⟩⟩
  · intro a s t s' hs hr
    have hc := hpre a s hs
    obtain ⟨-, hsp, -, -, hout⟩ := holds_entryAt (entryAt_of_pre hs)
    have hret : (retAt a.sp a.ret).holds s := hs.2.1.1.2.2.2.2.2.1
    refine ⟨trivial, (hX.rsp s t s' hc hr).trans hsp, ?_, hpost a s s' hs (hX.post s t s' hc hr)⟩
    refine (retAt a.sp a.ret).supp s s' ?_ hret
    rintro _ ⟨x, hx, rfl⟩
    exact (hX.frame s t s' hc hr x fun hf => hout x hx (hsp ▸ hfoot s x hc hf)).symm
  · intro a s t s' hs hr
    have hc := hpre a s hs
    obtain ⟨-, hsp, -, -, -⟩ := holds_entryAt (entryAt_of_pre hs)
    rintro (r | f | x) hl
    · change ¬ (r ∈ l.clob ∧ r ≠ "%rsp") at hl
      change s.regs r = s'.regs r
      by_cases hr' : r = "%rsp"
      · subst hr'
        exact (hX.rsp s t s' hc hr).symm
      · refine (hX.keep s t s' hc hr r ?_).symm
        cases h : c.clob r
        · rfl
        · exact absurd ⟨hclob r h, hr'⟩ hl
    · exact absurd trivial hl
    · change ¬ (InFrame a.sp l.frame x ∨ _) at hl
      exact (hX.frame s t s' hc hr x fun hf => hl (Or.inl (hsp ▸ hfoot s x hc hf))).symm
  · intro a₁ a₂ s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp hX₁ hX₂
    exact hX.ct s₁ s₂ t₁ t₂ s₁' s₂' (hpre a₁ s₁ h₁) (hpre a₂ s₂ h₂) (hpub s₁ s₂ hp) hX₁ hX₂

/-- **The contract from the word interface.** Let `l` have a word layout at the names `ws`
    and `res`, let every value that decodes at the result type of `l` decode as a word, and
    let the precondition of the record hold wherever the precondition of the contract does.
    If the bytes of `l` decode to `q`, whose leaky runs meet `wordSig l ws res` with a
    footprint among the `frame` bytes below the entry stack register, then `l` meets its
    contract. -/
theorem meets_of_wordSig {l : LinkedFn} {ws : List String} {res : String}
    (hL : WordLayout l ws res)
    (hdec : ∀ v, (dec l.res v).isSome = true → (dec (.word 64) v).isSome = true)
    (hpre : ∀ a s, (l.contractPre a).holds s → l.pre s) {q : List RInstr}
    (hq : decodeLprog l.bytes = some q) (hX : CalleeSpec (runOf .doitm q) (wordSig l ws res))
    (hF : FootBelow (wordSig l ws res) l.frame) : l.Meets := by
  refine meets_of_calleeSpec hq hX (fun a s hs => ⟨hpre a s hs, ?_⟩) (fun r hr => ?_)
    (fun s x _ hx => hF s x hx) (fun a s s' hs hp => ?_)
    (fun s₁ s₂ hp => l.pub_of_regs s₁ s₂ hp.rsp hp.regs)
  · obtain ⟨-, -, hvals, -, -⟩ := holds_entryAt (entryAt_of_pre hs)
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (sem_isSome_of_pre hs)
    have hw : (l.sem ((ws.map fun a => s.regs (phys a)).map wordVal)) = some v := by
      rw [← read_wordLayout hL s, hvals, hv]
    show ((l.sem ((ws.map fun a => s.regs (phys a)).map wordVal)).bind (dec (.word 64))).isSome
    rw [hw, Option.bind_some]
    exact hdec v (l.sem_res _ v hv)
  · simpa [wordSig] using hr
  · obtain ⟨-, -, hvals, -, -⟩ := holds_entryAt (entryAt_of_pre hs)
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (sem_isSome_of_pre hs)
    have h := l.post_sem s s' v (hpre a s hs) hp (by rw [hvals]; exact hv)
    refine ⟨v, hv, ?_⟩
    simp only [AbiLayout.ResultOf, hL.result, ResultKind.read] at h ⊢
    exact h

/-! ## 5. The footprint lemmas and the frame rule -/

/-- **The write set lies in the footprint of the precondition.** -/
theorem contractWrites_subset (l : LinkedFn) (a : CallVar) :
    l.contractWrites a ⊆ (l.contractPre a).fp := by
  rintro (r | f | y) hx
  · obtain ⟨hc, -⟩ := hx
    by_cases hm : r ∈ abiRegs l.layout
    · exact Or.inl (Or.inl (Or.inl ⟨r, hm, rfl⟩))
    · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, ⟨hc, hm⟩, rfl⟩)))))
  · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, rfl⟩))))))
  · rcases hx with hx | hx
    · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨y, hx, rfl⟩))))))
    · exact Or.inl (Or.inr (Or.inr hx))

/-- **The footprint of the postcondition lies in that of the precondition.** -/
theorem contractPost_fp_subset (l : LinkedFn) (a : CallVar) :
    (l.contractPost a).fp ⊆ (l.contractPre a).fp := by
  rintro x (hx | hx | hx | hx)
  · exact hx
  · rw [Set.mem_singleton_iff.1 hx]
    exact Or.inl (Or.inl (Or.inl ⟨"%rsp", List.mem_cons_self, rfl⟩))
  · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl hx))))
  · exact Or.inl (Or.inr (Or.inr hx))

/-- **The frame rule at the contract.** A linked function that meets its contract meets the
    contract with a frame `R` added to both conditions; the precondition of the framed
    contract asks the frame to be separated from the precondition. -/
theorem Meets.frame {l : LinkedFn} (h : l.Meets) (R : CallVar → SAssert AState Loc) :
    ∃ q, decodeLprog l.bytes = some q ∧ SContract (runOf .doitm q) (l.contract.frame R) := by
  obtain ⟨q, hq, hC⟩ := h.code
  exact ⟨q, hq, hC.frame R (fun a _ _ => contractWrites_subset l a)
    (fun a => contractPost_fp_subset l a)⟩

/-! ## 6. The interface of the contract -/

/-- **A linked function that meets its contract meets the interface of the contract**, at
    every argument names and result name. -/
theorem calleeSpec_of_meets {l : LinkedFn} (h : l.Meets) (args : List String)
    (res : Option String) :
    ∃ q, decodeLprog l.bytes = some q ∧ CalleeSpec (runOf .doitm q) (l.contractSig args res) := by
  obtain ⟨q, hq, hC⟩ := h.code
  refine ⟨q, hq, calleeSpec_of_contract hC (fun s ⟨a, ha⟩ => ⟨a, ha, fun s' h' => ⟨a, ha, h'⟩,
    ?_⟩) (fun _ _ hp => hp)⟩
  rintro (r | f | y) hx
  · exact ⟨by simpa [LinkedFn.contractSig] using hx.1, hx.2⟩
  · trivial
  · exact ⟨a, ha, hx⟩

/-- **The footprint of the interface of a register result** is among the `frame` bytes below
    the entry stack register. -/
theorem footBelow_contractSig {l : LinkedFn} {r : String} (hr : l.layout.result = .reg r)
    (args : List String) (res : Option String) :
    FootBelow (l.contractSig args res) l.frame := by
  rintro s x ⟨a, ha, hx | hx⟩
  · obtain ⟨-, hsp, -⟩ := holds_entryAt (entryAt_of_pre ha)
    rw [hsp]
    exact hx
  · rw [hr] at hx
    cases hx

/-- **A linked function with a word layout that meets its contract is a word callee** at the
    interface of the contract, the summary `wordSummary` and the entry states at which the
    resources of a call hold. -/
theorem wordCallee_of_meets {l : LinkedFn} {ws : List String} {res : String}
    (hL : WordLayout l ws res) :
    WordCallee (l.contractSig ws (some res)) res (wordSummary l) l.Room where
  args_gp := hL.ws_gp
  res_eq := rfl
  res_gp := hL.res_gp
  res_clob := hL.res_clob
  pre s := by
    rintro ⟨a, ha⟩ hd
    obtain ⟨-, -, hvals, -, -⟩ := holds_entryAt ha
    refine ⟨a, Set.disjoint_empty _, ha, ?_⟩
    change ((l.sem ((ws.map fun a => s.regs (phys a)).map wordVal)).bind
      (dec (.word 64))).isSome = true at hd
    rw [← read_wordLayout hL s, hvals] at hd
    exact Option.isSome_of_isSome_bind hd
  post s s' _ := by
    rintro ⟨a, ha, hp⟩
    obtain ⟨-, -, hvals, -, -⟩ := holds_entryAt (entryAt_of_pre ha)
    obtain ⟨v, hv, hR⟩ := hp.2.2.2
    simp only [AbiLayout.ResultOf, hL.result, ResultKind.read] at hR
    change (l.sem ((ws.map fun a => s.regs (phys a)).map wordVal)).bind (dec (.word 64)) = _
    rw [← read_wordLayout hL s, hvals, hv, Option.bind_some, hR]
    exact dec_wordVal _

/-- Under an out layout, the register of the pointer name is the register of a parameter. -/
theorem phys_mem_abiRegs_of_outLayout {l : LinkedFn} {ins : List (String × ArgKind)} {po : String}
    {n : Nat} (hL : OutLayout l ins po n) : phys po ∈ abiRegs l.layout := by
  have hm : (phys po, ArgKind.words n) ∈ l.layout.args.map fun a => (a.reg, a.kind) := by
    rw [hL.args]
    exact List.mem_map.2 ⟨_, hL.dest, rfl⟩
  obtain ⟨a, ha, he⟩ := List.mem_map.1 hm
  have hr : a.reg = phys po := congrArg Prod.fst he
  exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.2 ⟨a, ha, hr⟩))

/-- **The footprint of the interface of an out result** is among the `frame` bytes below the
    entry stack register and the `n` words at the pointer of the destination. -/
theorem footBelowOut_contractSig {l : LinkedFn} {ins : List (String × ArgKind)} {po : String}
    {n : Nat} (hL : OutLayout l ins po n) (args : List String) (res : Option String) :
    FootBelowOut (l.contractSig args res) l.frame po n := by
  rintro s x ⟨a, ha, hx | hx⟩
  · obtain ⟨-, hsp, -⟩ := holds_entryAt (entryAt_of_pre ha)
    rw [hsp]
    exact Or.inl hx
  · obtain ⟨hregs, -⟩ := holds_entryAt (entryAt_of_pre ha)
    rw [hL.result] at hx
    obtain ⟨w, ⟨k, hk, rfl⟩, hw⟩ := Set.mem_iUnion₂.1 hx
    obtain ⟨y, hy, hyx⟩ := hw
    cases hyx
    refine Or.inr ⟨k, hk, ?_⟩
    have he : s.regs (phys po) = a.rv (phys po) := hregs _ (phys_mem_abiRegs_of_outLayout hL)
    rw [he]
    exact hy

/-- **A linked function with an out layout that meets its contract is an out callee** at the
    interface of the contract, the summary `outSummary` and the entry states at which the
    resources of a call hold. -/
theorem outCallee_of_meets {l : LinkedFn} {ins : List (String × ArgKind)} {po : String}
    {n : Nat} (hL : OutLayout l ins po n) :
    OutCallee (l.contractSig (ins.map (·.1)) none) (readIns ins) po n (outSummary l ins n)
      l.Room where
  po_gp := hL.po_gp
  res_none := rfl
  len := rfl
  pre s := by
    rintro ⟨a, ha⟩ hd
    obtain ⟨-, -, hvals, -, -⟩ := holds_entryAt ha
    refine ⟨a, Set.disjoint_empty _, ha, ?_⟩
    change ((l.sem (insVals (ins.map (·.2)) (readIns ins s))).bind
      (dec (.arr n (.word 64)))).isSome = true at hd
    rw [← read_outLayout hL s, hvals] at hd
    exact Option.isSome_of_isSome_bind hd
  post s s' _ := by
    rintro ⟨a, ha, hp⟩
    obtain ⟨hregs, -, hvals, -, -⟩ := holds_entryAt (entryAt_of_pre ha)
    obtain ⟨v, hv, hR⟩ := hp.2.2.2
    simp only [AbiLayout.ResultOf, hL.result, ResultKind.read] at hR
    have he : (entryRegs a.rv).regs (phys po) = s.regs (phys po) :=
      (hregs _ (phys_mem_abiRegs_of_outLayout hL)).symm
    rw [he] at hR
    change (l.sem (insVals (ins.map (·.2)) (readIns ins s))).bind (dec (.arr n (.word 64))) = _
    rw [← read_outLayout hL s, hvals, hv, Option.bind_some, hR]
    exact dec_arr_wordsAt _ _ _

end CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnContract
