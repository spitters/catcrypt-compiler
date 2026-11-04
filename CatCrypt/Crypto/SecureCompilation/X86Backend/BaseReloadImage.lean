/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage

@[expose] public section

set_option autoImplicit false

/-!
# The image of a base reload and the width guard of an address computation

The allocated body of `compileRegion` reaches an array through its pointer: it reloads the
pointer from the save slot of its argument register into a scratch register `b`
(`MOVQ b, qsave.R`), indexes through `b`, and computes the address of a cell with
`LEA:64 D, (b, X, 8)`. The symbolic step of the address computation guards `b` with the width
`64` (`OwnedLprogTV.symN`). The reference block holds no such word, so the check `guardsT` of
`ownedCheckMC` accepts the guard only when the image of the reload gives `b` a word whose width
the term fixes: the image reads a reload of the base of an address computation
(`JasminLsemAddrImage.baseReload?`) as the cast `CASTW_64_64 b, q` at the tag `.reg (some 64)`.

The passes after the allocation (the constant-index fold, which rewrites the store through the
cell into a constant-index store, and the scheduling of the gathered blocks) place indexed
accesses through `b` and other instructions between the reload and the address computation.
`baseReload?` used to recognise the reload only with the address computation two positions
later, so in such a block the reload was read as a copy of the word of `q`, a word of unknown
width, and the width guard of the address computation on it matched no reference guard. It
now finds the address computation as the first instruction naming `b` other than an indexed
access through `b` (`JasminLsemAddrImage.leaFirst`).

This module states the completeness of the check at this construct, for every body.

## Main results

* `leaFirst_of_lea`: an address computation based at `b`, preceded only by indexed accesses
  through `b` and instructions that do not name `b`, is found by `leaFirst`.
* `baseReload?_of_leaFirst`: a reload of a name that holds an array pointer, whose next use
  other than an indexed access is an address computation, is a base reload.
* `imgInstr_baseReload_of_leaFirst`: its image is the cast at the tag `.reg (some 64)`.
* `guardsT_castW64`: the width guard on the cast word adds no obligation to `guardsT`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.BaseReloadImage

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV

/-- An address computation based at `b`, preceded only by indexed accesses through `b` and
    instructions that do not name `b`, is found by `leaFirst`. -/
theorem leaFirst_of_lea (b : String) :
    ∀ (pre : List Linstr) (l : Linstr) (post : List Linstr),
      (∀ j ∈ pre, idxBaseUseB b j.li_i = true ∨ namesB b j.li_i = false) →
      leaBaseUseB b l.li_i = true → leaFirst b (pre ++ l :: post) = true
  | [], l, post, _, hl => by simp [leaFirst, hl]
  | j :: js, l, post, hp, hl => by
      have hj := hp j (by simp)
      have ih := leaFirst_of_lea b js l post (fun x hx => hp x (by simp [hx])) hl
      simp only [List.cons_append, leaFirst, ih, Bool.and_true]
      rcases hj with h | h <;> simp [h]

/-- **A base reload by its next use**: a move `MOVQ b, q` or `MOV:64 b, q` from a name `q`
    that holds an array pointer, followed by indexed accesses through `b` and instructions that
    do not name `b` and then by an address computation based at `b`, is a base reload. -/
theorem baseReload?_of_leaFirst (slotArr : String → Option (String × Nat)) {body : Lcmd}
    {k : Nat} {b o q : String} (ho : o = "MOVQ" ∨ o = "MOV:64")
    (hq : (slotArr q).isSome = true) (hf : leaFirst b (body.drop (k + 1)) = true) :
    baseReload? slotArr body k (.Lopn [.reg b] o [.reg q]) = some (b, q) := by
  simp [baseReload?, ho, hq, hf]

/-- **The image of a base reload found by its next use**: the reload `MOVQ b, q` of an array
    pointer, whose next use other than an indexed access is an address computation, is imaged
    as the cast `CASTW_64_64 b, q` at the tag `.reg (some 64)`. -/
theorem imgInstr_baseReload_of_leaFirst (slotArr : String → Option (String × Nat))
    {body : Lcmd} {k : Nat} {b q : String}
    (hq : (slotArr q).isSome = true) (hf : leaFirst b (body.drop (k + 1)) = true) :
    imgInstr slotArr body k (.Lopn [.reg b] "MOVQ" [.reg q])
      = (.Lopn [.reg b] "CASTW_64_64" [.reg q], .reg (some 64)) := by
  have hr := baseReload?_of_leaFirst slotArr (Or.inl rfl) hq hf
  have h1 : bitStore? body k (.Lopn [.reg b] "MOVQ" [.reg q]) = none := by
    simp [bitStore?]
  have h3 : arrImmImg slotArr body k (.Lopn [.reg b] "MOVQ" [.reg q]) = none := by
    simp [arrImmImg]
  have h2 : cellIdxStore? slotArr body k (.Lopn [.reg b] "MOVQ" [.reg q]) = none := by
    cases hc : cellIdxStore? slotArr body k (.Lopn [.reg b] "MOVQ" [.reg q]) with
    | none => rfl
    | some p =>
        obtain ⟨c, -, -, -, -, -, -, -, -, he, -⟩ := cellIdxStore?_spec hc
        simp at he
  exact imgInstr_baseReload slotArr hr h1 h2 h3

/-- **The width guard on a cast word adds no obligation**: inserted anywhere among the guards
    of the allocated block, the guard that the cast `castT 64 t` has width `64` leaves `guardsT`
    unchanged. -/
theorem guardsT_castW64 (E : Array TEnt) (L : List String × Bool) (gs gs₁ gs₂ : List SG)
    (t : STerm) (ht : t.refsLt E.size = true) :
    guardsT E L gs (gs₁ ++ .wid (castT 64 t) 64 :: gs₂) = guardsT E L gs (gs₁ ++ gs₂) := by
  simp [guardsT, normGT, List.flatMap_append, SG.normT, castT, STerm.wbkT, SG.refsLt,
    STerm.refsLt, List.all_append, ht]

end CatCrypt.Crypto.SecureCompilation.X86Backend.BaseReloadImage
