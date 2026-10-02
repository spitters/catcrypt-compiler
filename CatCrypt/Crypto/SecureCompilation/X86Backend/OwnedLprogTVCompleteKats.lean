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
public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVBlocks
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVBlocks

/-!
# The hypotheses of the two-address completeness theorem on shipped bodies

`OwnedLprogTV.twoAddr_ownedCheckM_complete_of_twoAddrWF` states that `ownedCheckM` accepts a
non-empty straight-line body against its legalisation `TwoAddrLegalize.twoAddrBody` when every
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

The theorems for bodies with several blocks, `OwnedLprogTV.twoAddr_ownedCheckM_complete_blocks`
and `OwnedLprogTV.dropOk_ownedCheckM_complete_blocks`, are evaluated on the three-block loops
`MpnLoopFrontEmit.andLprog` and `MpnLoopFrontEmit.addLprogFront`. Two-address legalisation
receives the loops tied (no copy-route instruction), so the first theorem applies with the
identity chunks. On the optimised `mpn_add_n` loop the dead-move elimination removes six
immediate moves; the marks are dead within every block, the live sets converge, and the
evaluated check agrees. The loop `rotBody 80`, which moves eighty registers one place down and
branches back, is rejected against itself: its live sets need eighty rounds, more than the
`4 · 2 + 64` rounds `ownedCheckM` iterates (`liveConvB` fails); `rotBody 60` is accepted.

## Main definitions

* `straightWF`: the hypotheses of the theorem on a body, with a succeeding symbolic run.
* `copyCount`: the number of instructions the copy route legalises.
* `combSelectBody`, `foldWF`, `deadCount`: the comb select body, the hypotheses of the
  dead-move theorem on a body, and the number of eliminated moves.
* `preTwoAddr`, `twoAddrBlocksWF`: the body two-address legalisation receives in
  `LprogOptPipeline.ownedLprog`, and the hypotheses of the theorem for several blocks.
* `loopMarks`, `dropBlocksWF`: the marks of the dead-move elimination, and the hypotheses of
  the dead-move theorem for several blocks.
* `rotBody`: a loop whose live sets converge after as many rounds as it moves registers.

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

/-- The hypotheses of `twoAddr_ownedCheckM_complete_of_twoAddrWF` on a body at the typing
    `tg`, with a symbolic run that succeeds. -/
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

/-! ## Bodies with several blocks -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG (cfgOf isLeader)

/-- The body of the first function of a program. -/
def firstBody (p : Option Lprog) : Lcmd :=
  match p with
  | some P => match P.lp_funcs with
      | f :: _ => f.2.lfd_body
      | [] => []
  | none => []

/-- The names `ownedCheckTy` observes for the first function of a program. -/
def firstOuts (p : Option Lprog) : List String :=
  match p with
  | some P => match P.lp_funcs with
      | f :: _ => resOuts f.2
      | [] => []
  | none => []

/-- The body of the first function of a program as two-address legalisation receives it in
    `LprogOptPipeline.ownedLprog`. -/
def preTwoAddr (p : Option Lprog) : Lcmd :=
  firstBody ((p.map LprogOptPipeline.optimizeLprogBasicBlocks).map
    (fun P => LprogGpRealloc.reallocLprog (ConstIndexFold.foldIndexedLprog P)))

/-- The number of blocks of a typed body. -/
def blockCount (B : List LinstrRM) : Nat :=
  match cfgOf (B.map Prod.fst) with
  | some G => G.blocks.size
  | none => 0

/-- `cfgOf` accepts the typed body, and the symbolic run of every block not ending in `Lret`
    lies inside the fragment. -/
def blocksFrag (B : List LinstrRM) : Bool :=
  match cfgOf (B.map Prod.fst) with
  | some G => (List.range G.blocks.size).all fun k =>
      (G.blk k).term == .ret ||
        match symRun (bodyAt B (G.blk k) (G.blk k).term) SSt.start with
        | .unk => false
        | _ => true
  | none => false

/-- The hypotheses of `twoAddr_ownedCheckM_complete_blocks` on a body at the typing `tg`. -/
def twoAddrBlocksWF (outs : List String) (tg : LinstrR → MemTag) (body : Lcmd) : Bool :=
  !body.isEmpty && body.all (fun i => twoAddrWF i.li_i) && blocksFrag (typeBody tg body) &&
    liveConvB outs (typeBody tg body) (typeBody tg (twoAddrBody body))

/-- The marks of the dead-move elimination on the folded body, spelled and typed. -/
def loopMarks (b : Lcmd) : List (LinstrRM × Bool) :=
  typeMarks tagOf (spellMarks (dropDeadImmMarks (constIndexFoldBody b)))

/-- The marks are dead immediate moves within every block. -/
def blocksDropOk (M : List (LinstrRM × Bool)) : Bool :=
  match cfgOf ((srcOf M).map Prod.fst) with
  | some G => (List.range G.blocks.size).all fun k =>
      (G.blk k).term == .ret ||
        dropOk [] ((M.drop (G.blk k).start).take
          (bstopOf (G.blk k).term (G.blk k) - (G.blk k).start))
  | none => false

/-- The hypotheses of `dropOk_ownedCheckM_complete_blocks` on a marked body. -/
def dropBlocksWF (outs : List String) (M : List (LinstrRM × Bool)) : Bool :=
  !M.isEmpty && M.all (fun p => !p.2 || straightR p.1.1) &&
    (List.range M.length).all (fun pc =>
      !isLeader (M.map fun p => p.1.1).toArray pc || !(M.getD pc ((.Lret, .reg none), false)).2) &&
    blocksDropOk M && blocksFrag (srcOf M) && liveConvB outs (srcOf M) (keptOf M)

/-- A loop whose block moves each of the registers `r1`, …, `rn` one place down to `r0`, …,
    `r(n-1)` and branches back on `r0`. -/
def rotBody (n : Nat) : Lcmd :=
  [⟨0, .Llabel .internal 1⟩] ++
    (List.range n).map (fun i => ⟨0, .Lopn [.reg s!"r{i}"] "MOV:64" [.reg s!"r{i+1}"]⟩) ++
    [⟨0, .Lcond (.reg "r0") 1⟩, ⟨0, .Lret⟩]

#kat twoAddrBlocksWF (firstOuts (MpnLoopFrontEmit.andLprog ())) tagOf
    (preTwoAddr (MpnLoopFrontEmit.andLprog ())) &&
  blockCount (typeBody tagOf (preTwoAddr (MpnLoopFrontEmit.andLprog ()))) == 3
#kat ownedCheckM (firstOuts (MpnLoopFrontEmit.andLprog ()))
  (typeBody tagOf (preTwoAddr (MpnLoopFrontEmit.andLprog ())))
  (typeBody tagOf (twoAddrBody (preTwoAddr (MpnLoopFrontEmit.andLprog ()))))
#kat twoAddrBlocksWF (firstOuts (MpnLoopFrontEmit.addLprogFront ())) tagOf
    (preTwoAddr (MpnLoopFrontEmit.addLprogFront ())) &&
  blockCount (typeBody tagOf (preTwoAddr (MpnLoopFrontEmit.addLprogFront ()))) == 3 &&
  copyCount (preTwoAddr (MpnLoopFrontEmit.addLprogFront ())) == 0
#kat ownedCheckM (firstOuts (MpnLoopFrontEmit.addLprogFront ()))
  (typeBody tagOf (preTwoAddr (MpnLoopFrontEmit.addLprogFront ())))
  (typeBody tagOf (twoAddrBody (preTwoAddr (MpnLoopFrontEmit.addLprogFront ()))))
#kat dropBlocksWF (firstOuts (MpnLoopFrontEmit.addLprogFront ()))
    (loopMarks (optimizeBasicBlocks (firstBody (MpnLoopFrontEmit.addLprogFront ())))) &&
  ((loopMarks (optimizeBasicBlocks (firstBody (MpnLoopFrontEmit.addLprogFront ())))).filter
    (·.2)).length == 6 &&
  blockCount (srcOf (loopMarks (optimizeBasicBlocks (firstBody (MpnLoopFrontEmit.addLprogFront ())))))
    == 3
#kat keptOf (loopMarks (optimizeBasicBlocks (firstBody (MpnLoopFrontEmit.addLprogFront ())))) ==
  typeBody tagOf (foldIndexedBody (optimizeBasicBlocks (firstBody (MpnLoopFrontEmit.addLprogFront ()))))
#kat ownedCheckM (firstOuts (MpnLoopFrontEmit.addLprogFront ()))
  (srcOf (loopMarks (optimizeBasicBlocks (firstBody (MpnLoopFrontEmit.addLprogFront ())))))
  (keptOf (loopMarks (optimizeBasicBlocks (firstBody (MpnLoopFrontEmit.addLprogFront ())))))
set_option kat.ms 1000 in
#kat blocksFrag (typeBody tagOf (rotBody 80)) &&
  blockCount (typeBody tagOf (rotBody 80)) == 2 &&
  !liveConvB [] (typeBody tagOf (rotBody 80)) (typeBody tagOf (rotBody 80)) &&
  !ownedCheckM [] (typeBody tagOf (rotBody 80)) (typeBody tagOf (rotBody 80))
set_option kat.ms 500 in
#kat liveConvB [] (typeBody tagOf (rotBody 60)) (typeBody tagOf (rotBody 60)) &&
  ownedCheckM [] (typeBody tagOf (rotBody 60)) (typeBody tagOf (rotBody 60))

end CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVCompleteKats
