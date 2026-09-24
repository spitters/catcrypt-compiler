/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopNestDepth
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopNestDepth

@[expose] public section

set_option autoImplicit false

/-!
# Multi-output-buffer mutation with ping-pong (ConvertToVole front-gap 4)

`ConvertToVoleV204FrontEmit.lean` (gap 4, lines 74–78) records the last of the four
front walls blocking a whole-`convert_to_vole_v` emit: the committed runtime-trip
front `rolledForLoopNRt` folds **one** accumulator `accTy` and returns it, whereas
`convert_to_vole` mutates **several** distinct output buffers per iteration (`v`, the
two ping-pong halves of `r`, `u`) with cross-iteration pointer swaps — the GGM
Phase-3 tree reads one half of `r` and writes the other, swapping each level.

This module isolates the two mechanisms that gap needs and shows the **backend loop
state already supports them**, so the residual is purely a missing *front combinator*,
not a state-model gap:

* **Multi-output.**  A1's `LstateM` array carrier is `larr : String → ArrCell` — a
  *named* multi-array carrier.  A loop body may `STOREIDX` to **several distinct array
  slots** per pass (`lsemStepMem`'s store arm writes `s.setArr dst …` at the wire's
  result name), and `runBoundedLoopMem` / `lsemFuelMemL` thread the whole carrier
  (every named array) through — so a body writing `"r"` *and* `"v"` mutates two
  buffers per iteration.  No single folded `accTy`.

* **Ping-pong.**  The emitted `STOREIDX`/`LOADIDX` wire (`.arrIdx base idx scale`)
  bakes the array **name** statically, so ping-pong cannot swap the *name*.  It swaps
  the *index*: one named array `"r"` of width `2N` holds region A `[0,N)` and region B
  `[N,2N)`; two base registers `sb`/`db` hold the source/dest region offsets and are
  **swapped branch-free each pass** by an XOR-swap (`sb^=db; db^=sb; sb^=db`, no
  branch).  Pass `jd+1` reads exactly the cells pass `jd` wrote — the source/dest
  regions alternate.

The kernel here is authored at the A1 loop-lowering target (`loopLinstrRM` over a
general `List LinstrRM`, the compiler-infra loop node A1 exposes for exactly this —
"the body is a general `List LinstrRM` … so a loop body can later carry a call (A2)
or nest (A3)"), NOT through `rolledForLoopNRt`, precisely because a multi-output
ping-pong front arm is the missing capability (gap 4).  `denote = spec` is pinned by
`native_decide` against a pure ping-pong reduction fold; the branch-free swap is
proven faithful as a `BitVec` algebra lemma.

**All goals closed, axioms ⊆ {propext, Classical.choice, Quot.sound} (+ `Lean.ofReduceBool`
for the `native_decide` validates).**

Invoke:  lake env lean CatCrypt/Crypto/SecureCompilation/Dialects/TranslateDialectMultiOutPingPong.lean
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectMultiOutPingPong

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop

/-! ## 0. Dimensions

Region width `N = 2`; the ping-pong array `"r"` has width `2N = 4` (region A `[0,2)`,
region B `[2,4)`).  A second output array `"v"` (width 2).  Small for `native_decide`. -/

/-- Region width in 64-bit words. -/
def regionN : Nat := 2

/-! ## 1. The pure ping-pong reduction spec

Each pass reduces the current *source* region `(s0, s1)` to the *dest* region
`(s0 ^ s1, s0)` (the XOR-tree combine `dst[0] = src[0]^src[1]` plus a carry
`dst[1] = src[0]` keeping the region populated), and the dest region becomes the next
pass's source region — the ping-pong.  `ppPure m` is the source-region contents after
`m` passes. -/

/-- One ping-pong pass on a source region `(s0, s1)`: the dest region `(s0^s1, s0)`. -/
def ppStep (p : BitVec 64 × BitVec 64) : BitVec 64 × BitVec 64 :=
  (p.1 ^^^ p.2, p.1)

/-- The pure ping-pong fold: the live region contents after `m` passes. -/
def ppPure : Nat → BitVec 64 × BitVec 64 → BitVec 64 × BitVec 64
  | 0, p => p
  | k + 1, p => ppPure k (ppStep p)

/-! ## 2. The multi-output ping-pong loop body (a general `List LinstrRM`)

Per pass, over source region `[sb, sb+2)` and dest region `[db, db+2)` of the one
named array `"r"`:
* read `t0 = r[sb]`, `t1 = r[sb+1]`;
* `x = t0 XOR t1`;                                (the XOR-tree combine)
* write `r[db] = x`, `r[db+1] = t0`;             (**output buffer 1** — region dst of `r`)
* write `v[0] = x`;                               (**output buffer 2** — the `"v"` array)
* XOR-swap `sb`/`db` (branch-free pointer swap);  (the ping-pong)
* `n -= 1`.                                        (loop counter, `loopLinstrRM` back-edge)

Two `STOREIDX`s to **distinct** array names (`"r"`, `"v"`) = two buffers mutated per
pass; the `sb`/`db` swap makes pass `jd+1` read the region pass `jd` wrote. -/
def pingPongBody : List LinstrRM :=
  [ -- t0 = r[sb]
    (LinstrR.Lopn [.reg "t0"] "LOADIDX" [.arrIdx "r" "sb" 8], MemTag.load 64 4)
    -- i1 = sb + 1
  , (LinstrR.Lopn [.reg "i1"] "ADD:64" [.reg "sb", .imm 1], MemTag.reg none)
    -- t1 = r[sb+1]
  , (LinstrR.Lopn [.reg "t1"] "LOADIDX" [.arrIdx "r" "i1" 8], MemTag.load 64 4)
    -- x = t0 XOR t1
  , (LinstrR.Lopn [.reg "x"] "XOR:64" [.reg "t0", .reg "t1"], MemTag.reg none)
    -- r[db] = x      (output buffer 1, dest region of r)
  , (LinstrR.Lopn [.reg "r"] "STOREIDX" [.arrIdx "r" "db" 8, .reg "x"], MemTag.store 64 4)
    -- d1 = db + 1
  , (LinstrR.Lopn [.reg "d1"] "ADD:64" [.reg "db", .imm 1], MemTag.reg none)
    -- r[db+1] = t0   (carry, keeps the dest region populated)
  , (LinstrR.Lopn [.reg "r"] "STOREIDX" [.arrIdx "r" "d1" 8, .reg "t0"], MemTag.store 64 4)
    -- v[0] = x       (output buffer 2, the second named array)
  , (LinstrR.Lopn [.reg "v"] "STOREIDX" [.arrIdx "v" "z" 8, .reg "x"], MemTag.store 64 2)
    -- ping-pong: XOR-swap sb, db (branch-free)
  , (LinstrR.Lopn [.reg "sb"] "XOR:64" [.reg "sb", .reg "db"], MemTag.reg none)
  , (LinstrR.Lopn [.reg "db"] "XOR:64" [.reg "sb", .reg "db"], MemTag.reg none)
  , (LinstrR.Lopn [.reg "sb"] "XOR:64" [.reg "sb", .reg "db"], MemTag.reg none)
    -- n -= 1  (loop counter)
  , (LinstrR.Lopn [.reg "n"] "SUB:64" [.reg "n", .imm 1], MemTag.reg none) ]

/-- The looped multi-output ping-pong program: `pingPongBody` wrapped in the back-edge
    on counter `"n"`, top label `0`. -/
def pingPongProg : LprogM := singletonProgM "f" (loopLinstrRM 0 "n" pingPongBody)

/-- A start state carrying `m` passes and the four-cell array `"r"` (region A =
    `[r0,r1]`, region B = `[rb0,rb1]`), the second output array `"v" = [0,0]`, the
    base registers `sb=0` (region A), `db=2` (region B), the v-index `z=0`, and the
    pass counter `n=m`.  pc at the loop label `0`. -/
def mkStart (m : Nat) (r0 r1 rb0 rb1 : BitVec 64) : LstatePM :=
  { base :=
      ((((((({} : LstateM).setReg "sb" (0#64)).setReg "db" (2#64)).setReg "z" (0#64)).setReg
        "n" (BitVec.ofNat 64 m)).setArr "r"
          (![r0, r1, rb0, rb1] : Fin 4 → BitVec 64)).setArr "v"
            (![0#64, 0#64] : Fin 2 → BitVec 64))
    lfn := "f" }

/-! ## 3. Denote = the ping-pong reduction (native_decide) -/

/-- Read the live (region-A) contents `(r[0], r[1])` after a run. -/
def liveRegionA (t : LstatePM) : Option (BitVec 64 × BitVec 64) :=
  (t.base.getArr "r" 64 4).map (fun arr => (stackGet arr 0, stackGet arr 1))

/-- Read region B `(r[2], r[3])` after a run. -/
def regionB (t : LstatePM) : Option (BitVec 64 × BitVec 64) :=
  (t.base.getArr "r" 64 4).map (fun arr => (stackGet arr 2, stackGet arr 3))

/-- Read the second output buffer `v[0]` after a run. -/
def outV0 (t : LstatePM) : Option (BitVec 64) :=
  (t.base.getArr "v" 64 2).map (fun arr => stackGet arr 0)

/-- **Denote = spec (2-pass ping-pong reduction).**  Running the multi-output
    ping-pong loop for `m = 2` passes over the initial region A `(5,6)` lands the live
    region A on the pure ping-pong fold `ppPure 2 (5,6)` — the interpreter followed the
    real back-edge twice, ping-ponging the two halves of `"r"`. -/
theorem pingpong_denote_2 :
    (lsemFuelMemL pingPongProg 200 (mkStart 2 5 6 0 0)).bind liveRegionA
      = some (ppPure 2 (5#64, 6#64)) := by native_decide

/-- The same at a different input (7, 12): denote = `ppPure 2 (7,12)`, so the fold is
    read from the data, not baked in. -/
theorem pingpong_denote_2' :
    (lsemFuelMemL pingPongProg 200 (mkStart 2 7 12 0 0)).bind liveRegionA
      = some (ppPure 2 (7#64, 12#64)) := by native_decide

/-- **Denote = spec (3-pass).**  With `m = 3` the live region lands on `ppPure 3`; after
    an odd number of passes the live region is B (dst of the last, odd, pass), and the
    interpreter agrees with the fold there too. -/
theorem pingpong_denote_3 :
    (lsemFuelMemL pingPongProg 300 (mkStart 3 5 6 0 0)).bind regionB
      = some (ppPure 3 (5#64, 6#64)) := by native_decide

/-! ## 4. Multi-output: two distinct buffers mutated per pass (native_decide) -/

/-- **Two buffers mutated per pass.**  After one pass, BOTH the `"r"` dest region
    (region B) AND the second array `"v"` change from their initial `(0,0)` / `0`:
    region B becomes `ppStep (5,6) = (3,5)`, and `v[0] = 3`.  Two distinct named
    output buffers written in the single loop body — not one folded accumulator. -/
theorem pingpong_multiOutput :
    ((lsemFuelMemL pingPongProg 200 (mkStart 1 5 6 0 0)).bind regionB
      = some (ppStep (5#64, 6#64)))
    ∧ ((lsemFuelMemL pingPongProg 200 (mkStart 1 5 6 0 0)).bind outV0
        = some ((5#64) ^^^ (6#64))) := by native_decide

/-! ## 5. Ping-pong alternation: pass `jd+1` reads what pass `jd` wrote -/

/-- **Pass 0 writes region B.**  After one pass, region B `(r[2], r[3])` holds
    `ppStep (a0,a1)` — pass 0's output, distinct from the initial region B. -/
theorem alt_pass0_writes_B :
    (lsemFuelMemL pingPongProg 200 (mkStart 1 5 6 99 99)).bind regionB
      = some (ppStep (5#64, 6#64)) := by native_decide

/-- **Pass 1 reads pass 0's output, not the initial region B.**  The 2-pass live
    result is **identical** whether region B starts at `(0,0)` or garbage `(99,99)`:
    pass 0 overwrites region B before pass 1 reads it, so the initial B is dead.  This
    is exactly the source/dest alternation — pass 1's source region *is* pass 0's dest
    region. -/
theorem alt_pass1_reads_prev :
    (lsemFuelMemL pingPongProg 200 (mkStart 2 5 6 0 0)).bind liveRegionA
      = (lsemFuelMemL pingPongProg 200 (mkStart 2 5 6 99 99)).bind liveRegionA := by
  native_decide

/-- Sanity: if the initial region B *did* leak into the 2-pass result (i.e. if there
    were no ping-pong and pass 1 read the initial B), the two starts would differ.  They
    do not (`alt_pass1_reads_prev`) — confirming the alternation takes effect. -/
theorem alt_result_independent_of_initial_B :
    (lsemFuelMemL pingPongProg 200 (mkStart 2 5 6 0 0)).bind liveRegionA
      = some (ppPure 2 (5#64, 6#64))
    ∧ (lsemFuelMemL pingPongProg 200 (mkStart 2 5 6 99 99)).bind liveRegionA
        = some (ppPure 2 (5#64, 6#64)) := by native_decide

/-! ## 6. The branch-free swap is faithful (proven `BitVec` algebra)

The ping-pong pointer swap is `sb^=db; db^=sb; sb^=db`.  This lemma proves the
three-XOR sequence swaps the pair — no branch, no temp register — so the interpreter's
faithful application of `XOR:64` (validated above) alternates the source/dest
bases each pass. -/

/-- **XOR-swap faithfulness.**  From `(sb, db)`, the sequence `sb := sb^db`,
    `db := sb^db`, `sb := sb^db` yields `(db, sb)` — the swapped pair. -/
theorem xorSwap_swaps (sb db : BitVec 64) :
    let sb1 := sb ^^^ db
    let db1 := sb1 ^^^ db
    let sb2 := sb1 ^^^ db1
    (sb2, db1) = (db, sb) := by
  simp only []
  refine Prod.ext ?_ ?_ <;> bv_decide

/-! ## 7. Interpreter realises the `runBoundedLoopMem` fold (native_decide)

As in A1's validate, the labeled interpreter's decoded result equals the
`runBoundedLoopMem` fold of the same body over the same start — the interpreter
realises the multi-buffer/ping-pong fold, both output arrays threaded. -/

/-- **Fold agreement.**  The interpreter's live region equals the `runBoundedLoopMem`
    fold's live region (two body-folds), so the interpreter realises the fold over the
    full multi-array carrier. -/
theorem pingpong_realises_fold :
    (lsemFuelMemL pingPongProg 200 (mkStart 2 5 6 0 0)).bind liveRegionA
      = (runBoundedLoopMem pingPongBody 2 (mkStart 2 5 6 0 0).base).map
          (fun b => (fun arr => (stackGet arr 0, stackGet arr 1))
            ((b.getArr "r" 64 4).getD (fun _ => 0#64))) := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectMultiOutPingPong
