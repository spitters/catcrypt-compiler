/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi

@[expose] public section

/-!
# A single-pass implementation of the fusion check

`fuseOKL` checks every position `k` of the source body against the symbolic state `blk c k`,
which it recomputes from the start of the block, and it locates the block start by
`bstart`, a recursion over `k` that indexes the list at every step. `fuseOKLFast` walks the
body once, carrying the symbolic state of the current position and the remaining low
destinations, and keeps no guards, which `posOK` does not read. The equality
`fuseOKL_eq_fast` is registered with `@[csimp]`, so compiled code runs `fuseOKLFast`
whenever it calls `fuseOKL`; the definition `fuseOKL` and its theorems are unchanged.

## Main definitions

* `fuseOKLFast` — the fusion check in one forward pass over the body.

## Main results

* `posPass_drop` — the forward pass from position `k` equals the per-position checks from `k`.
* `fuseOKL_eq_fast` — `fuseOKL = fuseOKLFast`, registered with `@[csimp]`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV

/-- The symbolic outcome with its guards dropped. -/
def forgetG : SOut → SOut
  | .ok ss _ => .ok ss []
  | .fail => .fail
  | .unk => .unk

/-- The check of `posOK` at a position with the low-destination entry `l`, the instruction
    `ci` and the symbolic outcome `o`. -/
def posAt (E : List String) (l : Option (Option String)) (ci : Option LinstrRM) (o : SOut) :
    Bool :=
  match o with
  | .ok ss _ =>
      E.all (fun x => w64 E (ss.regs x)) &&
        (match l with
         | some (some d) => ci.any (fun i => siteOK E d i ss)
         | _ => true)
  | .fail => true
  | .unk => false

/-- The symbolic outcome after the instruction `i`, guards dropped: the start state after a
    control instruction, the symbolic step otherwise. -/
def nextS (o : SOut) (i : LinstrRM) : SOut :=
  if isCtlB i then .ok SSt.start [] else forgetG (symSnoc o i)

/-- The positions of a body from the current one on, checked in one forward pass: `Ls` and
    `cs` are the remaining low destinations and instructions, `o` the symbolic outcome at the
    current position. -/
def posPass (E : List String) : List (Option String) → List LinstrRM → SOut → Bool
  | Ls, [], o => posAt E Ls.head? none o
  | Ls, i :: cs, o => posAt E Ls.head? (some i) o && posPass E Ls.tail cs (nextS o i)

/-- **The fusion check in one pass**: the instruction-class conjunct of `fuseOKL`, and
    `posPass` from the start state. -/
def fuseOKLFast (E : List String) (L : List (Option String)) (c : List LinstrRM) : Bool :=
  c.all (fun i => clsB i && wireOK i.1 && JasminLsemExportRewrites.mulxFree i)
    && posPass E L c (.ok SSt.start [])

theorem posAt_forgetG (E : List String) (l : Option (Option String)) (ci : Option LinstrRM)
    (o : SOut) : posAt E l ci (forgetG o) = posAt E l ci o := by
  cases o <;> rfl

theorem forgetG_symSnoc_forgetG (o : SOut) (i : LinstrRM) :
    forgetG (symSnoc (forgetG o) i) = forgetG (symSnoc o i) := by
  cases o with
  | ok ss g => simp only [forgetG, symSnoc]; cases symStep i ss <;> rfl
  | fail => rfl
  | unk => rfl

theorem posOK_eq_posAt (E : List String) (L : List (Option String)) (c : List LinstrRM)
    (k : Nat) : posOK E L c k = posAt E L[k]? c[k]? (blk c k) := rfl

theorem nextS_blk {c : List LinstrRM} {k : Nat} {i : LinstrRM} (hk : c[k]? = some i) :
    nextS (forgetG (blk c k)) i = forgetG (blk c (k + 1)) := by
  unfold nextS
  cases hc : isCtlB i
  · rw [blk_succ_lopn hk hc, forgetG_symSnoc_forgetG]; rfl
  · rw [blk_succ_ctl hk hc]; rfl

theorem posPass_drop (E : List String) (L : List (Option String)) (c : List LinstrRM) :
    ∀ (n k : Nat), k + n = c.length →
      posPass E (L.drop k) (c.drop k) (forgetG (blk c k))
        = (List.range' k (n + 1)).all (posOK E L c)
  | 0, k, h => by
      have hc : c.drop k = [] := List.drop_eq_nil_of_le (by omega)
      have hk : c[k]? = none := List.getElem?_eq_none (by omega)
      rw [hc, posPass, List.head?_drop, posAt_forgetG]
      simp [posOK_eq_posAt, hk]
  | n + 1, k, h => by
      have hlt : k < c.length := by omega
      rw [List.drop_eq_getElem_cons hlt, posPass, List.head?_drop, posAt_forgetG,
        List.tail_drop, nextS_blk (List.getElem?_eq_getElem hlt),
        posPass_drop E L c n (k + 1) (by omega), List.range'_succ (s := k), List.all_cons,
        posOK_eq_posAt E L c k, List.getElem?_eq_getElem hlt]

/-- **The single-pass fusion check equals `fuseOKL`**; compiled code runs `fuseOKLFast`. -/
@[csimp] theorem fuseOKL_eq_fast : @fuseOKL = @fuseOKLFast := by
  funext E L c
  unfold fuseOKL fuseOKLFast
  congr 1
  have h := posPass_drop E L c c.length 0 (by omega)
  rw [List.drop_zero, List.drop_zero, blk_zero] at h
  rw [List.range_eq_range']
  exact h.symm

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi
