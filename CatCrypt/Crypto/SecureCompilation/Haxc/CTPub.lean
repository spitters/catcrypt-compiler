/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT
public import CatCrypt.Crypto.SecureCompilation.Haxc.AbiLayout

@[expose] public section

set_option autoImplicit false

/-!
# The constant-time gate of the hax compiler, from the System V layout

The public entry data of a compiled function, read off its layout `σ : AbiLayout`, and the
byte-level constant-time checker `DecodedCT.bytesCTCheckFast` run as a gate on the bytes.

A parameter is public (`AbiLayout.argPub`, defined with `AbiLayout.PubAgree` beside the
layout) when it is an array parameter, whose register holds
an address, or a scalar parameter whose register carries a bound of the layout, a runtime
count; the other scalar parameters, the memory, the other registers and the flags are secret.
`σ.pubA` is the public set of the checker: `%rsp` and the register of each public parameter,
no frame word, no flag, and the public array regions `σ.pubRegions` (register and length of
each array parameter whose register is in `σ.pubWords`). `σ.PubAgree s₁ s₂` states that two
entry states agree on the stack pointer, on the register of each public parameter and on the
words of each public array; `pubA_agree_iff` identifies it with the agreement `PubA.Agree` of
the checker on `σ.pubA`.

`σ.ctGateB bytes` decodes the bytes and runs `bytesCTCheckFast` under the regime `ctRegime`
(DOITM) from `σ.pubA`. `σ.ctFrame prog` is the list of frame words of the inferred certificate
(`fastFrame`), which the separation side condition `FrameSep` of the leakage semantics refers
to.

## Main results

* `AbiLayout.pubRegs`, `AbiLayout.pubA` — the public registers and the public entry set of
  the checker for a layout.
* `AbiLayout.pubA_agree_of_pubAgree` — `σ.PubAgree` implies agreement on `σ.pubA`.
* `AbiLayout.wordsAt_eq_iff_wordAt` — equal `wordsAt` lists are equal `wordAt` words.
* `AbiLayout.pubA_agree_iff` — agreement on `σ.pubA` is `σ.PubAgree`.
* `AbiLayout.ctGateB` — the gate on the bytes.
* `AbiLayout.ctGateB_sound` — the bytes that pass the gate decode to a program whose runs
  from entry states agreeing on the public data of `σ`, with every step satisfying
  `FrameSep (σ.ctFrame prog)`, have equal leakage traces.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.CT (ConstantTimeRel DoitRegime)

/-- The hardware regime of the gate: DOITM, under which an instruction makes its data operands
    observable exactly when its timing class is variable. -/
def ctRegime : DoitRegime := .doitm

namespace AbiLayout

/-- The public registers of a layout: `%rsp` and the register of each public parameter. -/
def pubRegs (σ : AbiLayout) : List String :=
  "%rsp" :: (σ.args.filter σ.argPub).map (·.reg)

/-- The public entry set of the checker for a layout: the public registers, no frame word,
    no flag, and the public array regions `σ.pubRegions`. -/
def pubA (σ : AbiLayout) : PubA := ⟨σ.pubRegs, [], false, σ.pubRegions⟩

/-- The words of a region read by `wordsAt` agree in two states exactly when the checker's
    words `wordAt` of the region agree at every index below its length. -/
theorem wordsAt_eq_iff_wordAt {s₁ s₂ : AState} {b : String} {n : Nat} :
    wordsAt s₁.mem (s₁.regs b) n = wordsAt s₂.mem (s₂.regs b) n ↔
      ∀ j < n, wordAt s₁ b j = wordAt s₂ b j := by
  unfold wordsAt wordAt
  constructor
  · intro h j hj
    have := congrArg (fun l => l[j]?) h
    simp only [List.getElem?_map, List.getElem?_range hj, Option.map_some, Option.some.injEq,
      _root_.Hax.Value.int.injEq, Int.natCast_inj] at this
    exact BitVec.eq_of_toNat_eq this
  · intro h
    refine List.map_congr_left fun j hj => ?_
    rw [h j (List.mem_range.mp hj)]

/-- Agreement on the public data of the layout implies agreement on the public entry set of
    the checker. -/
theorem pubA_agree_of_pubAgree {σ : AbiLayout} {s₁ s₂ : AState} (h : σ.PubAgree s₁ s₂) :
    σ.pubA.Agree s₁ s₂ := by
  refine ⟨fun x hx => ?_, fun o ho => by simp [pubA] at ho, fun hf => by simp [pubA] at hf,
    fun q hq => wordsAt_eq_iff_wordAt.mp (h.wordsAt_eq hq)⟩
  simp only [pubA, pubRegs, List.mem_cons, List.mem_map, List.mem_filter] at hx
  rcases hx with rfl | ⟨a, ⟨ha, hp⟩, rfl⟩
  · exact h.rsp
  · exact h.regs a ha hp

/-- Agreement on the public entry set of the checker is agreement on the public data of the
    layout. -/
theorem pubA_agree_iff {σ : AbiLayout} (s₁ s₂ : AState) :
    σ.pubA.Agree s₁ s₂ ↔ σ.PubAgree s₁ s₂ := by
  refine ⟨?_, pubA_agree_of_pubAgree⟩
  rintro ⟨hr, -, -, hw⟩
  refine ⟨hr _ (List.mem_cons_self ..), fun a ha hp => hr _ ?_, fun a ha n hk hm => ?_⟩
  · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨ha, hp⟩, rfl⟩)
  · refine wordsAt_eq_iff_wordAt.mpr (hw (a.reg, n) ?_)
    refine List.mem_filterMap.mpr ⟨a, List.mem_filter.mpr ⟨ha, by simpa using hm⟩, ?_⟩
    simp [AbiArg.region, hk]

/-- The frame words of the certificate the gate infers for `prog` from `σ.pubA`. -/
def ctFrame (σ : AbiLayout) (prog : List RInstr) : List Int :=
  fastFrame prog (fastCert prog σ.pubA).1 (fastCert prog σ.pubA).2

/-- **The constant-time gate on bytes**: the bytes decode, and `bytesCTCheckFast` accepts the
    decoded program under `ctRegime` from the public entry set `σ.pubA`. -/
def ctGateB (σ : AbiLayout) (bytes : List (BitVec 8)) : Bool :=
  match decodeLprog bytes with
  | some prog => bytesCTCheckFast ctRegime σ.pubA prog
  | none => false

/-- **Soundness of the gate.** Bytes that pass `σ.ctGateB` decode to a program `prog` whose
    runs from index `0`, with every step satisfying `FrameSep (σ.ctFrame prog)`, from entry
    states agreeing on the public data of `σ`, have equal leakage traces. -/
theorem ctGateB_sound {σ : AbiLayout} {bytes : List (BitVec 8)} (h : σ.ctGateB bytes = true) :
    ∃ prog, decodeLprog bytes = some prog ∧
      ConstantTimeRel σ.PubAgree
        (fun sa t => ∃ sa', RunL ctRegime (FrameSep (σ.ctFrame prog)) prog 0 sa t sa') := by
  unfold ctGateB at h
  split at h
  · rename_i prog hd
    refine ⟨prog, hd, fun s₁ s₂ t₁ t₂ hag h₁ h₂ => ?_⟩
    exact bytesCTCheckFast_sound h s₁ s₂ t₁ t₂ (pubA_agree_of_pubAgree hag) h₁ h₂
  · cases h

end AbiLayout

end CatCrypt.Crypto.SecureCompilation.Haxc
