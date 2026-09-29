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

* `abiCtx prog`: the preservation data of `prog`: the certificate `DecodedCT.inferPresA`
  for frame-word requests seeded by `seedFix`, an analysis that assumes every callee keeps
  everything, so that a caller's saved registers are requested from its callees even when
  a loop around the calls joins the facts after them with those before; and the
  registers and frame words each function keeps at every reached `ret`.
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

open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr callOps retOps)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak DoitRegime)

/-- The owner map of a decoded program: each index mapped to the entry of the function
    it belongs to, among the call targets. -/
def abiOwn (prog : List RInstr) : Nat → Nat := ownerOf (callTargets prog).eraseDups

/-- The successors of `pc` in the seed analysis with the facts each receives: those of
    `succsPresA`, except that a call enters its callee with the entry fact and returns
    with the facts after `callOps` and `retOps`, as if the callee kept every register and
    frame word. -/
def seedSuccs (pa : Array RInstr) (pc : Nat) (P : PresA) : List (Nat × PresA) :=
  match pa[pc]? with
  | some (.call t) =>
      (t, entryPres []) ::
        (((presBlock (fun _ => true) P (callOps (pc + 1))).bind fun P1 =>
          presBlock (fun _ => true) P1 retOps).map fun P3 => (pc + 1, P3)).toList
  | _ => succsPresA (fun _ => true) (fun _ => 0) (fun _ => []) (fun _ => none) pa pc P

/-- One forward pass of the seed analysis, with a flag recording whether any fact
    changed. -/
def seedSweep (pa : Array RInstr) (D : Array (Option PresA)) : Array (Option PresA) × Bool :=
  (List.range pa.size).foldl (fun acc pc =>
    let (B, ch) := acc
    match B.getD pc none with
    | none => (B, ch)
    | some P => (seedSuccs pa pc P).foldl (fun acc so =>
        let (B, ch) := acc
        let old := B.getD so.1 none
        let new := presMeetO old so.2
        if so.1 < B.size ∧ new ≠ old then (B.setIfInBounds so.1 new, true) else (B, ch))
        (B, ch))
    (D, false)

/-- Passes of `seedSweep` until one changes nothing, at most `fuel` of them. -/
def seedFix (pa : Array RInstr) : Nat → Array (Option PresA) → Array (Option PresA)
  | 0, D => D
  | fuel + 1, D =>
    let (D', ch) := seedSweep pa D
    if ch then seedFix pa fuel D' else D'

/-- The preservation data of `prog` for the ABI check. The frame words each callee is
    asked to keep start from those its callers' facts track at each call in the seed
    analysis (`seedFix`), which assumes every callee keeps everything; the requests then
    grow over one round per callee by those the certificate for the current requests
    tracks at each call. The certificate is `inferPresA` for the final requests, and each
    function's preserved registers and frame words are those of `calleeSaved` and of its
    requests it keeps at every reached `ret`. -/
def abiCtx (prog : List RInstr) : PresCtx :=
  let pa := prog.toArray
  let es := (callTargets prog).eraseDups
  let own := ownerOf es
  let rets := retIdxA pa
  let calls := callIdxA pa
  let tbl : List (Nat × List Int) → Nat → List Int := fun t e => (t.lookup e).getD []
  let grow (D : Array (Option PresA)) (t : List (Nat × List Int)) : List (Nat × List Int) :=
    es.map fun e => (e, (tbl t e ++ presRequestsA calls own #[] D e).eraseDups)
  let init := (Array.replicate pa.size none).setIfInBounds 0 (some (entryPres []))
  let seed := grow (seedFix pa pa.size init) []
  let reqs := (List.range (es.length + 1)).foldl
    (fun t _ => grow (inferPresA own (tbl t) es rets pa) t) seed
  let D := inferPresA own (tbl reqs) es rets pa
  let post : Nat → List String × List Int := fun e =>
    (presPostA? own D rets calleeSaved (tbl reqs e) e).getD ([], [])
  { Rp := fun e => (post e).1, Pp := fun e => (post e).2, D := D.toList }

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
