/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.ExportContract

/-!
# The memory accessed by a compiled export

For a module without linked functions, the address machine runs the body of the compiled
export from the entry state to a halt, and every store and every load of that run lies in the
memory that the precondition `SepLogic.X86.abiPre σ rv` of the layout owns: the stack words
`%rsp + o`, `frameLo ≤ o ≤ frameHi`, the words of each pointer region and the stack parameter
words, at the entry register values `rv`.

## Main definitions

* `abiMem`: the bytes of the memory locations of the footprint of `abiPre σ rv`.

## Main results

* `layoutMem_subset_abiMem`: the stack words and the pointer regions at the registers of a
  state satisfying `abiPre σ rv` lie in `abiMem σ rv`.
* `haxc_safe`: a compiled export accesses only the memory its precondition owns.
* `haxc_contract_safe`: the contract `haxc_contract` together with the access bound.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.SepLogic
open CatCrypt.Crypto.SecureCompilation.SepLogic.SAssert (mem_fp_bigSep)
open CatCrypt.Crypto.SecureCompilation.SepLogic.X86 (Loc abiPre holds_abiPre mem_regions
  abiRegs regions_iff_abiPre)
open CatCrypt.Crypto.SecureCompilation.SepLogic.Addr (AccessIn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (RunSafe)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (entryA)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun (runA haltedA haltedA_of_runA)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Lprog)
open CatCrypt.Crypto.Hax (HaxModule)

/-- The bytes `x` whose memory location `Loc.mem x` is in the footprint of the precondition
    `abiPre σ rv` of the layout `σ` at the entry register values `rv`. -/
def abiMem (σ : AbiLayout) (rv : String → BitVec 64) : Set (BitVec 64) :=
  {x | Loc.mem x ∈ (abiPre σ rv).fp}

/-- At a state whose registers of `abiRegs σ` hold their values under `rv`, the bytes of the
    stack words and of the pointer regions of `σ` lie in `abiMem σ rv`. -/
theorem layoutMem_subset_abiMem {σ : AbiLayout} {rv : String → BitVec 64} {sa : AState}
    (h : ∀ r ∈ abiRegs σ, sa.regs r = rv r) : layoutMem σ sa ⊆ abiMem σ rv := by
  have hrsp : sa.regs "%rsp" = rv "%rsp" := h _ List.mem_cons_self
  rintro x (hx | ⟨p, hp, hx⟩)
  · rw [hrsp] at hx
    exact Or.inl (Or.inr (Or.inr (Or.inl hx)))
  · obtain ⟨a, ha, e⟩ := mem_regions hp
    have hp1 : sa.regs p.1 = rv p.1 := by
      rw [← e]
      exact h _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map_of_mem ha)))
    rw [hp1] at hx
    exact Or.inl (Or.inr (Or.inr (Or.inr (mem_fp_bigSep.2 ⟨_, List.mem_map.2 ⟨p, hp, rfl⟩, hx⟩))))

/-- **A compiled export accesses only the memory its precondition owns.** For the result of
    `compileA` on a module `m` with `m.linked = []`, at every entry state `sa` satisfying the
    precondition `abiPre σ rv` with a source run of `m` to a value, some run of the address
    machine on a body from the entry state `entryA σ sa` halts, and every store and every load
    of each of its steps lies in `abiMem σ rv`. The proof is `haxc_correct_auto` and
    `layoutMem_subset_abiMem`. -/
theorem haxc_safe (m : HaxModule) (σ : AbiLayout) (fname : String) (P : Lprog)
    (bytes : List (BitVec 8)) (hc : compileA m σ fname = some (P, bytes))
    (hlink : m.linked = []) (rv : String → BitVec 64) (sa : AState)
    (hpre : (abiPre σ rv).holds sa) (v : _root_.Hax.Value) (hrun : haxRuns σ m sa v) :
    ∃ body frame fuel s zf, runA frame body fuel (entryA σ sa) false = some (s, zf)
      ∧ haltedA body s = true
      ∧ RunSafe frame body (AccessIn (abiMem σ rv) frame body) fuel (entryA σ sa) false := by
  have hregs := ((holds_abiPre σ rv sa).1 hpre).1
  obtain ⟨-, -, ⟨-, -, -, -, -, body, frame, fuel, s, zf, hrA, hacc⟩ | ⟨c, hcm, -⟩⟩ :=
    haxc_correct_auto m σ fname P bytes hc sa ((regions_iff_abiPre σ sa).2 ⟨rv, hpre⟩) v hrun
      (by simp [hlink]) (by simp [hlink])
  swap
  · simp [hlink] at hcm
  have hsub := layoutMem_subset_abiMem (σ := σ) (sa := sa) hregs
  exact ⟨body, frame, fuel, s, zf, hrA,
    haltedA_of_runA _ body fuel (entryA σ sa) false (s, zf) hrA,
    hacc.mono fun _ h => ⟨fun x hx => hsub (h.1 x hx), fun x hx => hsub (h.2 x hx)⟩⟩

/-- **The compiler contract with the access bound.** For the result of `compileA` on a module
    `m` with `m.linked = []`, every program decoded from the bytes meets `exportSpec σ m`
    (`haxc_contract`), and from every state satisfying the precondition at the entry register
    values `rv` some halting run of the address machine on a body from `entryA σ sa` stores to
    and loads from `abiMem σ rv` only (`haxc_safe`). -/
theorem haxc_contract_safe (m : HaxModule) (σ : AbiLayout) (fname : String) (P : Lprog)
    (bytes : List (BitVec 8)) (hc : compileA m σ fname = some (P, bytes))
    (hlink : m.linked = []) (prog : List X86Backend.LprogBytesDecode.RInstr)
    (hd : decodeLprog bytes = some prog) :
    SContract (fun sa (_ : Unit) sa' => Halts aMachine prog 0 sa sa') (exportSpec σ m)
      ∧ ∀ (p : (String → BitVec 64) × _root_.Hax.Value) (sa : AState),
        ((exportSpec σ m).pre p).holds sa →
        ∃ body frame fuel s zf, runA frame body fuel (entryA σ sa) false = some (s, zf)
          ∧ haltedA body s = true
          ∧ RunSafe frame body (AccessIn (abiMem σ p.1) frame body) fuel (entryA σ sa) false := by
  refine ⟨haxc_contract m σ fname P bytes hc hlink prog hd, ?_⟩
  rintro ⟨rv, v⟩ sa ⟨⟨⟨hA, -, hrun⟩, -⟩, -⟩
  exact haxc_safe m σ fname P bytes hc hlink rv sa hA v hrun

end CatCrypt.Crypto.SecureCompilation.Haxc
