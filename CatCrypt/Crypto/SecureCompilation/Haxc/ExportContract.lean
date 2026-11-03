/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
public import CatCrypt.Crypto.SecureCompilation.SepLogic.Abi
public import CatCrypt.Crypto.SecureCompilation.SepLogic.Contract
public import CatCrypt.Crypto.SecureCompilation.Haxc.LtuFacts

/-!
# The compiler theorem as a contract with a frame

For a module without linked functions, the compiler theorem `haxc_correct_auto` is a
contract `SContract` of the halting runs of the decoded bytes over the address machine. The
logical variables are the entry register values `rv` and the source value `v`.

* The precondition `exportSpec σ m (rv, v)` is the conjunction of the precondition
  `abiPre σ rv` of the layout, the source run `srcAt σ m rv v` of `m` from the entry state to
  `v`, the entry values of the registers the read-back of the result reads (`resultRegs`), and
  the ownership of the write set.
* The postcondition `valAtR σ rv v` is the read-back of `v` at the entry registers `rv`.
* The write set `exportWrites σ rv` is every register other than `%rsp`, the flags, the stack
  words `%rsp + o`, `frameLo ≤ o ≤ frameHi`, from the entry `%rsp`, and the words of each
  pointer region of the layout at the entry registers.
* The public relation is trivial and the trace is `Unit`.

The source run reads the entry state only through the parameter registers and the words of
the pointer regions (`haxRuns_congr`), so `srcAt` is an assertion with these locations as its
footprint.

## Main definitions

* `exportWrites`, `srcLocs`, `srcAt`, `resultRegs`, `valAtR`, `exportSpec`.

## Main results

* `haxRuns_congr`: the source run depends only on the parameter registers and the words of
  the pointer regions.
* `read_entry_congr`: the read-back of a result depends on the entry state only at the
  registers of `resultRegs`.
* `exportPre_of`: the precondition holds at every entry state satisfying `σ.Regions` with a
  source run, at its own registers.
* `haxc_contract`: the decoded bytes of a module without linked functions meet `exportSpec`.
* `haxc_contract_frame`: the frame rule at `exportSpec`.
* `ltu_contract`, `ltu_contract_frame`, `ltu_exportPre`: the contract at the compiled `ltu`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.SepLogic
open CatCrypt.Crypto.SecureCompilation.SepLogic.SAssert (conj own)
open CatCrypt.Crypto.SecureCompilation.SepLogic.X86 (Loc wordsLocs wordLocs frameWords
  regionWords abiPre regsAt valAt resLocs read64_congr mem_regions holds_abiPre
  regions_iff_abiPre valAt_holds_iff abiRegs)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState read64)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Lprog)
open CatCrypt.Crypto.Hax (HaxModule)

/-! ## The write set -/

/-- The words of the pointer regions of `σ` at the register values `rv`. -/
def regionLocs (σ : AbiLayout) (rv : String → BitVec 64) : Set Loc :=
  ⋃ p ∈ σ.regions, wordsLocs (regionWords (rv p.1) p.2)

/-- **The locations the compiled bytes may change**, at the entry register values `rv`:
    every register other than `%rsp`, the flags, the stack words `%rsp + o`,
    `frameLo ≤ o ≤ frameHi`, from the entry `%rsp`, and the words of each pointer region. -/
def exportWrites (σ : AbiLayout) (rv : String → BitVec 64) : Set Loc :=
  Loc.reg '' {r | r ≠ "%rsp"} ∪ Set.range Loc.flag
    ∪ wordsLocs (frameWords (rv "%rsp") σ.frameLo σ.frameHi) ∪ regionLocs σ rv

/-! ## The source run as an assertion -/

/-- The value a parameter denotes depends on the state only at its register and, for an
    array parameter, at the words of its region. -/
theorem abiArg_read_congr {σ : AbiLayout} {a : AbiArg} (ha : a ∈ σ.args) {s t : AState}
    (hr : s.regs a.reg = t.regs a.reg)
    (hm : Footprinted.AgreeOn (regionLocs σ s.regs) s t) : a.read s = a.read t := by
  unfold AbiArg.read
  split
  · rw [hr]
  · rename_i n hk
    have hreg : (a.reg, n) ∈ σ.regions :=
      List.mem_filterMap.2 ⟨a, ha, by simp [AbiArg.region, hk]⟩
    simp only [wordsAt]
    rw [← hr]
    congr 1
    refine List.map_congr_left fun j hj => ?_
    rw [read64_congr (Footprinted.agreeOn_anti ?_ hm)]
    intro l hl
    exact Set.mem_biUnion hreg (Set.mem_biUnion (t := wordLocs)
      (show s.regs a.reg + BitVec.ofNat 64 (8 * j) ∈ regionWords (s.regs a.reg) n from
        ⟨j, List.mem_range.1 hj, rfl⟩) hl)

/-- **The source run reads the entry state only at the parameter registers and the words of
    the pointer regions**: `EnvOf` reads the state through `AbiArg.read`. -/
theorem haxRuns_congr {σ : AbiLayout} {m : HaxModule} {s t : AState} {v : _root_.Hax.Value}
    (hr : ∀ a ∈ σ.args, s.regs a.reg = t.regs a.reg)
    (hm : Footprinted.AgreeOn (regionLocs σ s.regs) s t) (h : haxRuns σ m s v) :
    haxRuns σ m t v := by
  obtain ⟨env, fuel, fuelC, env', ⟨h1, h2, h3⟩, hrun, hcf⟩ := h
  exact ⟨env, fuel, fuelC, env',
    ⟨fun a ha => (h1 a ha).trans (congrArg some (abiArg_read_congr ha (hr a ha) hm)), h2, h3⟩,
    hrun, hcf⟩

/-- The locations the source run reads at the entry register values `rv`: the parameter
    registers and the words of the pointer regions. -/
def srcLocs (σ : AbiLayout) (rv : String → BitVec 64) : Set Loc :=
  Loc.reg '' {r | ∃ a ∈ σ.args, a.reg = r} ∪ regionLocs σ rv

/-- **The source run of `m` from the entry state to `v`** at the entry register values `rv`:
    the parameter registers hold their values under `rv` and `haxRuns σ m s v`, with the
    parameter registers and the words of the pointer regions as footprint. -/
def srcAt (σ : AbiLayout) (m : HaxModule) (rv : String → BitVec 64) (v : _root_.Hax.Value) :
    SAssert AState Loc where
  fp := srcLocs σ rv
  holds s := (∀ a ∈ σ.args, s.regs a.reg = rv a.reg) ∧ haxRuns σ m s v
  supp s t h hs := by
    have hr : ∀ a ∈ σ.args, s.regs a.reg = t.regs a.reg := fun a ha =>
      h (.reg a.reg) (Or.inl ⟨a.reg, ⟨a, ha, rfl⟩, rfl⟩)
    have hrv : regionLocs σ s.regs = regionLocs σ rv := by
      unfold regionLocs
      refine Set.iUnion_congr fun p => Set.iUnion_congr fun hp => ?_
      obtain ⟨a, ha, e⟩ := mem_regions hp
      rw [← e, hs.1 a ha]
    refine ⟨fun a ha => (hr a ha).symm.trans (hs.1 a ha), haxRuns_congr hr ?_ hs.2⟩
    rw [hrv]
    exact Footprinted.agreeOn_anti Set.subset_union_right h

/-! ## The read-back at the entry registers -/

mutual
/-- The registers whose entry values the read-back `κ` reads. -/
def resultRegs : ResultKind → List String
  | .reg _ => []
  | .words r _ => [r]
  | .wordAt r i => [r, i]
  | .tuple ks => resultRegsList ks
/-- `resultRegs` of each entry of a list, joined. -/
def resultRegsList : List ResultKind → List String
  | [] => []
  | k :: ks => resultRegs k ++ resultRegsList ks
end

mutual
/-- **The read-back depends on the entry state only at the registers of `resultRegs`.** -/
theorem read_entry_congr {sa sb sa' : AState} :
    (κ : ResultKind) → (∀ r ∈ resultRegs κ, sa.regs r = sb.regs r) →
      κ.read sa sa' = κ.read sb sa'
  | .reg _, _ => rfl
  | .words r n, h => by
    simp only [ResultKind.read, h r (by simp [resultRegs])]
  | .wordAt r i, h => by
    simp only [ResultKind.read, h r (by simp [resultRegs]), h i (by simp [resultRegs])]
  | .tuple ks, h => by
    simp only [ResultKind.read]
    rw [readList_entry_congr ks (fun r hr => h r (by simpa [resultRegs] using hr))]
/-- `read_entry_congr` on each entry of a list. -/
theorem readList_entry_congr {sa sb sa' : AState} :
    (ks : List ResultKind) → (∀ r ∈ resultRegsList ks, sa.regs r = sb.regs r) →
      ResultKind.readList sa sa' ks = ResultKind.readList sb sa' ks
  | [], _ => rfl
  | k :: ks, h => by
    simp only [ResultKind.readList]
    rw [read_entry_congr k (fun r hr => h r (by simp [resultRegsList, hr])),
      readList_entry_congr ks (fun r hr => h r (by simp [resultRegsList, hr]))]
end

/-- The address state with the register file `rv` and the zero memory. -/
def regsState (rv : String → BitVec 64) : AState where
  regs := rv
  mem _ := 0

/-- **The result value `v` read back at the entry register values `rv`**: `valAt` at the
    state with the register file `rv`. -/
def valAtR (σ : AbiLayout) (rv : String → BitVec 64) (v : _root_.Hax.Value) :
    SAssert AState Loc :=
  valAt σ (regsState rv) v

/-- `valAtR` holds at the exit state `sa'` exactly when `σ` reads back `v` from every entry
    state whose registers of `resultRegs σ.result` hold their values under `rv`. -/
theorem valAtR_holds_iff {σ : AbiLayout} {rv : String → BitVec 64} {v : _root_.Hax.Value}
    {sa sa' : AState} (h : ∀ r ∈ resultRegs σ.result, sa.regs r = rv r) :
    (valAtR σ rv v).holds sa' ↔ σ.ResultOf sa sa' v := by
  rw [valAtR, valAt_holds_iff]
  unfold AbiLayout.ResultOf
  rw [read_entry_congr (sb := regsState rv) σ.result h]

/-! ## The contract -/

/-- **The contract of the compiled bytes of `m` under the layout `σ`**, at the entry register
    values `rv` and the source value `v`: the precondition is the conjunction of `abiPre σ rv`,
    the source run `srcAt σ m rv v`, the entry values of the registers of the read-back and the
    ownership of the write set; the postcondition is the read-back `valAtR σ rv v`; the write
    set is `exportWrites σ rv`; the public relation is trivial. -/
def exportSpec (σ : AbiLayout) (m : HaxModule) :
    ContractSpec AState Loc ((String → BitVec 64) × _root_.Hax.Value) where
  pre p := conj (conj (conj (abiPre σ p.1) (srcAt σ m p.1 p.2))
    (regsAt (resultRegs σ.result) p.1)) (own (exportWrites σ p.1))
  post p := valAtR σ p.1 p.2
  writes p _ := exportWrites σ p.1
  pub _ _ := True

/-- **The precondition is satisfiable**: at every entry state `sa` satisfying `σ.Regions`
    with a source run of `m` to `v`, the precondition holds at the registers of `sa`. -/
theorem exportPre_of {σ : AbiLayout} {m : HaxModule} {sa : AState} {v : _root_.Hax.Value}
    (hsep : σ.Regions sa) (hrun : haxRuns σ m sa v) :
    ((exportSpec σ m).pre (sa.regs, v)).holds sa :=
  ⟨⟨⟨(holds_abiPre σ sa.regs sa).2 ⟨fun _ _ => rfl, hsep⟩, fun _ _ => rfl, hrun⟩,
    fun _ _ => rfl⟩, trivial⟩

/-- **The compiler theorem as a contract.** For the result of `compileA` on a module `m`
    with `m.linked = []`, every program decoded from the bytes meets `exportSpec σ m` with the
    halting runs of the address machine from the program counter `0` as run relation: from
    every state satisfying the precondition the program halts, the final state reads back the
    source value at the entry registers, and every location outside `exportWrites` holds its
    entry value. The proof is `haxc_correct_auto` and the determinism of the decoded
    machine (`halts_det`). -/
theorem haxc_contract (m : HaxModule) (σ : AbiLayout) (fname : String) (P : Lprog)
    (bytes : List (BitVec 8)) (hc : compileA m σ fname = some (P, bytes))
    (hlink : m.linked = []) (prog : List X86Backend.LprogBytesDecode.RInstr)
    (hd : decodeLprog bytes = some prog) :
    SContract (fun sa (_ : Unit) sa' => Halts aMachine prog 0 sa sa') (exportSpec σ m) := by
  have key : ∀ (p : (String → BitVec 64) × _root_.Hax.Value) (sa : AState),
      ((exportSpec σ m).pre p).holds sa → ∃ sa', Halts aMachine prog 0 sa sa'
        ∧ σ.ResultOf sa sa' p.2 ∧ sa'.regs "%rsp" = sa.regs "%rsp"
        ∧ ∀ x, Loc.mem x ∉ wordsLocs (frameWords (sa.regs "%rsp") σ.frameLo σ.frameHi) →
          (∀ p ∈ σ.regions, Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
          sa'.mem x = sa.mem x := by
    rintro ⟨rv, v⟩ sa ⟨⟨⟨hA, -, hrun⟩, -⟩, -⟩
    obtain ⟨prog', hd', ⟨sa', hh, hR, hsp, hkeep, -⟩ | ⟨cs, hsub, hne, -⟩⟩ :=
      haxc_correct_auto m σ fname P bytes hc sa ((regions_iff_abiPre σ sa).2 ⟨rv, hA⟩) v hrun
        (by simp [hlink]) (by simp [hlink]) (by simp [hlink])
    · obtain rfl : prog' = prog := Option.some.inj (hd'.symm.trans hd)
      exact ⟨sa', hh, hR, hsp, hkeep⟩
    · simp [hlink] at hsub
      exact absurd hsub hne
  refine ⟨fun p sa hs => ?_, fun p sa t sa₁ hs hX => ?_, fun p sa t sa₁ hs hX => ?_,
    fun _ _ _ _ t₁ t₂ _ _ _ _ _ _ _ => rfl⟩
  · obtain ⟨sa', hh, -⟩ := key p sa hs
    exact ⟨(), sa', hh⟩
  · obtain ⟨sa', hh, hR, -⟩ := key p sa hs
    obtain rfl := halts_det hX hh
    exact (valAtR_holds_iff hs.1.2).2 hR
  · obtain ⟨sa', hh, -, hsp, hkeep⟩ := key p sa hs
    obtain rfl := halts_det hX hh
    obtain ⟨rv, v⟩ := p
    have hregs := ((holds_abiPre σ rv sa).1 hs.1.1.1).1
    have hrsp : sa.regs "%rsp" = rv "%rsp" := hregs _ List.mem_cons_self
    have hrg : ∀ q ∈ σ.regions, sa.regs q.1 = rv q.1 := fun q hq => by
      obtain ⟨a, ha, e⟩ := mem_regions hq
      rw [← e]
      exact hregs _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map_of_mem ha)))
    intro l hl
    simp only [exportSpec, exportWrites, Set.mem_compl_iff, Set.mem_union, not_or] at hl
    obtain ⟨⟨⟨hreg, hfl⟩, hfr⟩, hrgn⟩ := hl
    cases l with
    | reg r =>
      have : r = "%rsp" := by
        by_contra hne
        exact hreg ⟨r, hne, rfl⟩
      subst this
      exact hsp.symm
    | flag f => exact absurd ⟨f, rfl⟩ hfl
    | mem x =>
      refine (hkeep x (by rwa [hrsp]) fun q hq hx => hrgn ?_).symm
      rw [hrg q hq] at hx
      exact Set.mem_biUnion hq hx

/-- **The frame rule at the compiler contract.** For the result of `compileA` on a module
    without linked functions whose read-back reads only locations of the write set, every
    decoded program meets `exportSpec σ m` with a frame `R` separated from the precondition:
    the frame holds in the final state. -/
theorem haxc_contract_frame (m : HaxModule) (σ : AbiLayout) (fname : String) (P : Lprog)
    (bytes : List (BitVec 8)) (hc : compileA m σ fname = some (P, bytes))
    (hlink : m.linked = []) (prog : List X86Backend.LprogBytesDecode.RInstr)
    (hd : decodeLprog bytes = some prog)
    (hres : ∀ rv, resLocs (regsState rv) σ.result ⊆ exportWrites σ rv)
    (R : (String → BitVec 64) × _root_.Hax.Value → SAssert AState Loc) :
    SContract (fun sa (_ : Unit) sa' => Halts aMachine prog 0 sa sa')
      ((exportSpec σ m).frame R) :=
  (haxc_contract m σ fname P bytes hc hlink prog hd).frame R
    (fun _ _ _ => Set.subset_union_right)
    (fun p _ hl => Or.inr (hres p.1 hl))

/-! ## The contract at `ltu` -/

open LtuCorrect (ltuAbi)

/-- **The contract at the compiled `ltu`**: every program decoded from the bytes `compileA`
    returns on `ltu` under `ltuAbi` meets `exportSpec`. -/
theorem ltu_contract (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA Mpn.ltu_texpr ltuAbi "ltu" = some (P, bytes))
    (prog : List X86Backend.LprogBytesDecode.RInstr) (hd : decodeLprog bytes = some prog) :
    SContract (fun sa (_ : Unit) sa' => Halts aMachine prog 0 sa sa')
      (exportSpec ltuAbi Mpn.ltu_texpr) :=
  haxc_contract _ _ _ P bytes hc rfl prog hd

/-- **The frame rule at the compiled `ltu`**: the read-back of `ltu` reads the register
    `%rax`, which is in the write set. -/
theorem ltu_contract_frame (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA Mpn.ltu_texpr ltuAbi "ltu" = some (P, bytes))
    (prog : List X86Backend.LprogBytesDecode.RInstr) (hd : decodeLprog bytes = some prog)
    (R : (String → BitVec 64) × _root_.Hax.Value → SAssert AState Loc) :
    SContract (fun sa (_ : Unit) sa' => Halts aMachine prog 0 sa sa')
      ((exportSpec ltuAbi Mpn.ltu_texpr).frame R) :=
  haxc_contract_frame _ _ _ P bytes hc rfl prog hd
    (fun _ l hl => Or.inl (Or.inl (Or.inl ⟨"%rax", by simp, hl.symm⟩))) R

/-- **The precondition at `ltu` holds at every entry state with a source run**: `ltuAbi` has
    no pointer region and passes `regCarriedB`, so every state satisfies `ltuAbi.Regions`. -/
theorem ltu_exportPre (sa : AState) (v : _root_.Hax.Value)
    (hrun : haxRuns ltuAbi Mpn.ltu_texpr sa v) :
    ((exportSpec ltuAbi Mpn.ltu_texpr).pre (sa.regs, v)).holds sa :=
  have e : ltuAbi.regions = [] := rfl
  exportPre_of ⟨fun b hb => by simp [ltuAbi] at hb, fun i _ p _ _ hp => by
      rw [e] at hp; simp at hp,
    fun p hp => by rw [e] at hp; simp at hp,
    AbiLayout.stackIn_of_regCarriedB (by decide) _⟩ hrun

end CatCrypt.Crypto.SecureCompilation.Haxc
