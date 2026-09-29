/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT

/-!
# Preservation of the callee-saved registers by decoded programs

A checker on decoded programs (`List RInstr`) whose acceptance gives the System V
guarantee of the function at index `0`: on every run on the address machine that reaches
its `ret`, `%rsp` and the callee-saved registers `DecodedCT.calleeSaved` (`%rbx`, `%rbp`,
`%r12`–`%r15`) hold their entry values.

The checker is the preservation analysis of `DecodedCT` (§4b there) run on its own,
without the public sets of the constant-time check. A register is preserved when every
write to it is covered: a `push` popped back into it, or a store to a frame word at an
offset from the entry `%rsp` followed by a reload of that word into it, with `%rsp`
changed only by `lea k(%rsp), %rsp`, `push`, `pop`, `call` and `ret`, and back at its entry
value at every `ret`.

## Main definitions

* `abiCtx prog`: the preservation data of `prog`: for a program with calls, that of
  `DecodedCT.presCtxOfA` with no public frame word; for a program without calls, the
  certificate `DecodedCT.inferPresA` of the single function and the registers it keeps at
  every reached `ret`.
* `abiFrame prog`: the frame words the certificate keeps through a store with a base other
  than `%rsp`.
* `calleeSavedPreserved prog`: the certificate holds the entry fact at index `0`, the
  function at `0` keeps every register of `calleeSaved`, and `DecodedCT.presCert` passes.
* `abiFailure prog`: the first reason the checker rejects, with an index.

## Main results

* `calleeSavedPreserved_sound`: if `calleeSavedPreserved prog` holds, every run of `prog`
  from index `0` whose steps satisfy `FrameSep (abiFrame prog)` ends with `%rsp` and each
  register of `calleeSaved` at its entry value.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedABI

open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak DoitRegime)

/-- The owner map of a decoded program: each index mapped to the entry of the function
    it belongs to, among the call targets. -/
def abiOwn (prog : List RInstr) : Nat → Nat := ownerOf (callTargets prog).eraseDups

/-- The preservation data of `prog` for the ABI check. With calls, `presCtxOfA` with no
    public frame word, so that each callee is asked to keep only the frame words holding
    its callers' saved registers. Without calls, the certificate of the single function,
    and as its preserved registers those of `calleeSaved` it keeps at every reached
    `ret`. -/
def abiCtx (prog : List RInstr) : PresCtx :=
  let pa := prog.toArray
  if (callTargets prog).isEmpty then
    let own : Nat → Nat := fun _ => 0
    let rets := retIdxA pa
    let D := inferPresA own (fun _ => []) [] rets pa
    let R := ((presPostA? own D rets calleeSaved [] 0).getD ([], [])).1
    { Rp := fun _ => R, Pp := fun _ => [], D := D.toList }
  else presCtxOfA pa #[]

/-- The frame words, as offsets from the current `%rsp`, that the certificate of
    `abiCtx` keeps through a store with a base other than `%rsp`. -/
def abiFrame (prog : List RInstr) : List Int := presCells prog (abiCtx prog).D

/-- **The ABI check.** The certificate of `abiCtx prog` holds the entry fact at index
    `0`, the function at `0` keeps every register of `calleeSaved`, and the preservation
    check `presCert` passes under the frame words `abiFrame prog`. -/
def calleeSavedPreserved (prog : List RInstr) : Bool :=
  let K := abiCtx prog
  presEntry K.D 0 && calleeSaved.all (K.Rp (abiOwn prog 0)).contains
    && presCert (abiFrame prog) (abiOwn prog) K.Rp K.Pp prog K.D

/-- **Soundness of the ABI check.** If `calleeSavedPreserved prog` holds, every run of
    `prog` from index `0` whose steps satisfy `FrameSep (abiFrame prog)` ends at its `ret`
    with `%rsp` and every register of `calleeSaved` at its entry value. -/
theorem calleeSavedPreserved_sound {prog : List RInstr} (h : calleeSavedPreserved prog = true)
    {r : DoitRegime} {s : AState} {t : List CTLeak} {s' : AState}
    (hr : RunL r (FrameSep (abiFrame prog)) prog 0 s t s') :
    s'.regs "%rsp" = s.regs "%rsp" ∧ ∀ x ∈ calleeSaved, s'.regs x = s.regs x := by
  simp only [calleeSavedPreserved, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem]
    at h
  obtain ⟨⟨hent, hR⟩, hc⟩ := h
  obtain ⟨Q, hQ, hQe⟩ := presEntry_spec hent
  obtain ⟨hrsp, hregs, -⟩ := presCert_sound hc hr hQ (isEntryPres_inv hQe s)
  exact ⟨hrsp, fun x hx => hregs x (hR x hx)⟩

/-- The first reason `calleeSavedPreserved prog` fails, with an index: no entry fact at
    `0`, registers of `calleeSaved` the function at `0` does not keep, or the first index
    at which `presAt` fails. `none` when the check passes. -/
def abiFailure (prog : List RInstr) : Option (Nat × String) :=
  let K := abiCtx prog
  let own := abiOwn prog
  if !presEntry K.D 0 then some (0, "no entry fact at the entry")
  else
    let lost := calleeSaved.filter fun x => !(K.Rp (own 0)).contains x
    if !lost.isEmpty then some (0, s!"callee-saved registers not preserved: {lost}")
    else
      ((List.range prog.length).find? fun pc =>
        !presAt (abiFrame prog) own K.Rp K.Pp prog K.D pc).map
        fun pc => (pc, "preservation check fails")

end CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedABI
