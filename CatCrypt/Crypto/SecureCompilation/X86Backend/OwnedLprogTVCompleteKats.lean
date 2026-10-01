/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.KatGuard
public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVComplete
public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVKernels
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVComplete
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVKernels
public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVDeadImm
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CombSelectFront
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVDeadImm
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.CombSelectFront

/-!
# The hypotheses of the two-address completeness theorem on shipped bodies

`OwnedLprogTV.twoAddr_ownedCheckM_complete` states that `ownedCheckM` accepts a non-empty
straight-line body against its legalisation `TwoAddrLegalize.twoAddrBody` when every
instruction satisfies `OwnedLprogTV.twoAddrWF` and the symbolic run of the body lies inside
the described fragment. This module evaluates the hypotheses on two bodies, with the wire
typing `OwnedLprogTVKernels.tagOf`:

* `OptimizeBasicBlocksCT.cpSubBody`, whose subtraction and addition violate the printer's
  two-address precondition and are legalised by the copy route;
* the 1058-instruction X25519 ladder step `Fe25519LfundefBridge.monoStepLcmd` without its
  trailing `Lret`, which satisfies the precondition at every instruction.

On both, the symbolic run succeeds (it is neither outside the fragment nor failing from
every state), so the theorem applies with a comparison of values, and the evaluated check
agrees with it. The optimisation of `cpSubBody` is outside the hypotheses: its subtraction
`RAX := RBX - RAX` reads its destination as the second source, which the copy route does
not legalise.

`OwnedLprogTV.foldIndexed_ownedCheckM_complete` states that `ownedCheckM` accepts the spelled
fold of a body against `ConstIndexFold.foldIndexedBody` when the eliminated immediate moves are
dead at the level of the symbolic step (`OwnedLprogTV.dropOk`). On the comb select over four
table entries (`CombSelectFront.combSelectLprog`, 290 instructions), the elimination removes
four immediate moves, the hypotheses hold with a succeeding symbolic run, and the evaluated
check agrees.

## Main definitions

* `straightWF`: the hypotheses of the theorem on a body, with a succeeding symbolic run.
* `copyCount`: the number of instructions the copy route legalises.
* `combSelectBody`, `foldWF`, `deadCount`: the comb select body, the hypotheses of the
  dead-move theorem on a body, and the number of eliminated moves.

## Main results

* `tagOf_firstSrc`: the wire typing gives a two-source operation one tag whatever its first
  source.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVCompleteKats

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM MemTag)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVKernels (tagOf cpOuts)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline (optimizeBasicBlocks)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OptimizeBasicBlocksCT (cpSubBody)
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize (twoAddrBody tiedOk)

theorem tagOf_firstSrc : TagFirstSrc tagOf := by
  intro d opn a a' b
  unfold tagOf
  split <;> split <;> simp_all

/-- The hypotheses of `twoAddr_ownedCheckM_complete` on a body at the typing `tg`, with a
    symbolic run that succeeds. -/
def straightWF (tg : LinstrR → MemTag) (body : Lcmd) : Bool :=
  !body.isEmpty && body.all (fun i => straightR i.li_i) &&
    body.all (fun i => twoAddrWF i.li_i) &&
    match symRun (typeBody tg body) SSt.start with
    | .ok _ _ => true
    | _ => false

/-- The number of instructions of a body that violate the printer's two-address
    precondition. -/
def copyCount (body : Lcmd) : Nat := (body.filter fun i => !tiedOk i.li_i).length

/-- The X25519 ladder step without its trailing `Lret`. -/
def monoStepBody : Lcmd := Fe25519LfundefBridge.monoStepLcmd.dropLast

set_option kat.ms 1000 in
#kat straightWF tagOf cpSubBody && copyCount cpSubBody == 2
#kat ownedCheckM cpOuts (typeBody tagOf cpSubBody) (typeBody tagOf (twoAddrBody cpSubBody))
#kat !(optimizeBasicBlocks cpSubBody).all (fun i => twoAddrWF i.li_i)
set_option kat.ms 1500 in
#kat straightWF tagOf monoStepBody && copyCount monoStepBody == 0
set_option kat.ms 1500 in
#kat ownedCheckM ["RDI"] (typeBody tagOf monoStepBody)
  (typeBody tagOf (twoAddrBody monoStepBody))

open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFold
  (constIndexFoldBody dropDeadImmBody spellMemBody foldIndexedBody)

/-- The body of the exported comb select over `N` table entries, without its `Lret`. -/
def combSelectBody (N : Nat) : Lcmd :=
  match CombSelectFront.combSelectLprog "f" N with
  | some lp =>
      match lp.lp_funcs with
      | f :: _ => f.2.lfd_body.filter fun i => match i.li_i with
          | .Lret => false
          | _ => true
      | [] => []
  | none => []

/-- The hypotheses of `foldIndexed_ownedCheckM_complete` on a body at the typing `tg`, with
    a succeeding symbolic run. -/
def foldWF (tg : LinstrR → MemTag) (body : Lcmd) : Bool :=
  let f := constIndexFoldBody body
  !(dropDeadImmBody f).isEmpty && (spellMemBody f).all (fun i => straightR i.li_i) &&
    dropOk [] (typeMarks tg (spellMarks (dropDeadImmMarks f))) &&
    match symRun (typeBody tg (spellMemBody f)) SSt.start with
    | .ok _ _ => true
    | _ => false

/-- The number of immediate moves the dead-move elimination removes from the folded body. -/
def deadCount (body : Lcmd) : Nat :=
  ((dropDeadImmMarks (constIndexFoldBody body)).filter (·.2)).length

#kat foldWF tagOf (combSelectBody 4) && deadCount (combSelectBody 4) == 4
#kat ownedCheckM ["RDX"] (typeBody tagOf (spellMemBody (constIndexFoldBody (combSelectBody 4))))
  (typeBody tagOf (foldIndexedBody (combSelectBody 4)))

end CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVCompleteKats
