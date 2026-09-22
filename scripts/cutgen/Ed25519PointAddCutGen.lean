/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddShippedParts

/-!
# The boundary certificate at a cut inside a part

A part check reduces a symbolic run of a whole part in the kernel, and its memory is the
whole run at once. Cutting a part in two needs the symbolic locations at the cut, which
this tool computes with the compiled evaluator and prints as Lean source.

The locations are held in the symbolic state as node indices into the hash-consed table,
so printing them needs the inverse of interning: `weOf` reads a node back as a word
expression, mapping a node that is the node of a statement slot to that slot. A location
whose node reads back to no expression — an entry register or cell the run never
determines — is dropped, as the part maps drop it.

Run it as a tool, not as part of a build:

    lake env lean scripts/cutgen/Ed25519PointAddCutGen.lean
-/

set_option autoImplicit false
set_option maxRecDepth 100000

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519PointAddShipped
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddShippedProof

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddCutGen

/-- The slot a node stands for, when it is the node interned for a statement slot.
    `internS` conses, so the node of slot `j` sits at index `n - 1 - j` of `σ`, where `n`
    is one past the last slot — this inverts `sget`. -/
def slotOf (σ : List Nat) (n : Nat) (j : Nat) : Option Nat :=
  match σ.idxOf? j with
  | some k => if k < n then some (n - 1 - k) else none
  | none => none

/-- The word expression a node denotes: a statement slot when the node is that slot's,
    an input slot or a literal at a leaf, and the operation at a node. A register or cell
    leaf has no expression. -/
partial def weOf (T : Tb) (σ : List Nat) (n : Nat) (j : Nat) : Option WE :=
  match slotOf σ n j with
  | some s => some (.v s)
  | none =>
    match nodeAt T.nodes j with
    | some (.inp i) => some (.v i)
    | some (.lit v) => some (.lit v)
    | some (.add p q) => (weOf T σ n p).bind fun x => (weOf T σ n q).map fun y => .add x y
    | some (.sub p q) => (weOf T σ n p).bind fun x => (weOf T σ n q).map fun y => .sub x y
    | some (.and p q) => (weOf T σ n p).bind fun x => (weOf T σ n q).map fun y => .and x y
    | some (.xor p q) => (weOf T σ n p).bind fun x => (weOf T σ n q).map fun y => .xor x y
    | some (.mul p q) => (weOf T σ n p).bind fun x => (weOf T σ n q).map fun y => .mul x y
    | some (.mulhi p q) =>
        (weOf T σ n p).bind fun x => (weOf T σ n q).map fun y => .mulhi x y
    | some (.shr p k) => (weOf T σ n p).map fun x => .shr x k
    | _ => none

/-- The locations of a symbolic state that read back, as a part map does. -/
def mapOf (T : Tb) (σ : List Nat) (n : Nat) (S : SSt) : List (Loc × WE) :=
  let regs := S.regs.filterMap fun p =>
    (weOf T σ n p.2).map fun e => (Loc.reg p.1, e)
  let cells := S.mem.filterMap fun p =>
    (weOf T σ n p.2).map fun e => (Loc.cell p.1.1 p.1.2, e)
  regs ++ cells

/-- The certificate at a cut: the locations, the carry expression and the zero
    expression. -/
structure Cut where
  locs : List (Loc × WE)
  cf : Option WE
  zf : Option WE

/-- The first eight segments of part 1, the natural cut: the hand-picked part boundaries
    are segment boundaries, where the live locations are the nodes of statement slots
    rather than nodes inside a statement's expression. Reading a node back expands the
    shared graph below it into a tree, so a cut inside a computation is expensive to
    print even though it is cheap to run. -/
def half1 : List (JInstr 64) :=
  ed25519PointAddShippedSeg001 ++ ed25519PointAddShippedSeg002 ++
  ed25519PointAddShippedSeg003 ++ ed25519PointAddShippedSeg004 ++
  ed25519PointAddShippedSeg005 ++ ed25519PointAddShippedSeg006 ++
  ed25519PointAddShippedSeg007 ++ ed25519PointAddShippedSeg008

/-- The certificate after `k` instructions of part 1, and the abstract state there. -/
def cutAt (k : Nat) : Option (Cut × DState) :=
  match enterF 57 Tb.empty {} paIn none none with
  | none => none
  | some (T₀, S₀) =>
    match internS 57 [] 57 T₀ paSl1 with
    | none => none
    | some (T₁, σ) =>
      let blk := canonFromD shippedBank {} ed25519PointAddShippedPart01
      match symRun2 T₁ S₀ (blk.take k) with
      | none => none
      | some (T₂, S₂) =>
        some (⟨mapOf T₂ σ 239 S₂.base,
               S₂.cfw.bind (weOf T₂ σ 239),
               S₂.zfn.bind (weOf T₂ σ 239)⟩,
              runD shippedBank {} ((ed25519PointAddShippedPart01).take k))

/-- The greatest slot an expression mentions. -/
def maxSlot : WE → Nat
  | .v j => j
  | .lit _ => 0
  | .add a b | .sub a b | .and a b | .xor a b | .mul a b | .mulhi a b =>
      max (maxSlot a) (maxSlot b)
  | .shr a _ => maxSlot a

/-- The base slot of the second half: one past the last slot its entry map mentions.
    `enterF` interns an entry map with no statements in scope, so a part's entry map may
    mention only slots below its base — which is why each part starts where its own
    statements do. -/
def baseOf (c : Cut) : Nat :=
  let s := c.locs.foldl (fun m p => max m (maxSlot p.2)) 0
  let s := match c.cf with | some e => max s (maxSlot e) | none => s
  let s := match c.zf with | some e => max s (maxSlot e) | none => s
  s + 1

/-- The check the certificate is meant to satisfy, evaluated rather than reduced: the
    first half against the cut, and the cut against the map after part 1. -/
def verify (k : Nat) : IO Unit := do
  match cutAt k with
  | none => IO.println "-- no certificate"
  | some (c, A) => do
    let blk := canonFromD shippedBank {} ed25519PointAddShippedPart01
    let a₂ := baseOf c
    IO.println s!"-- locations: {c.locs.length}, base slot of the second half: {a₂}"
    let h1 := partCheck2 57 (paSl1.take (a₂ - 57)) paIn none none c.locs c.cf c.zf
      (blk.take k)
    IO.println s!"-- first half against the certificate: {h1}"
    let h2 := partCheck2 a₂ (paSl1.drop (a₂ - 57)) c.locs c.cf c.zf paMap1
      (some (aoWE (.v 238))) none
      (canonFromD shippedBank A ((ed25519PointAddShippedPart01).drop k))
    IO.println s!"-- certificate against the map after part 1: {h2}"

/-- Where the certificate disagrees with the state it was read from: the flags as raw
    nodes beside their readback, and the first location whose expression interns to a
    different node than the state holds. -/
def diagnose (k : Nat) : IO Unit := do
  match enterF 57 Tb.empty {} paIn none none with
  | none => IO.println "-- no entry"
  | some (T₀, S₀) =>
    match internS 57 [] 57 T₀ paSl1 with
    | none => IO.println "-- no statements"
    | some (T₁, σ) =>
      let blk := canonFromD shippedBank {} ed25519PointAddShippedPart01
      match symRun2 T₁ S₀ (blk.take k) with
      | none => IO.println "-- the run did not complete"
      | some (T₂, S₂) => do
        IO.println s!"-- carry node: {repr S₂.cfw}  reads back: {(S₂.cfw.bind (weOf T₂ σ 239)).isSome}"
        IO.println s!"-- zero node:  {repr S₂.zfn}  reads back: {(S₂.zfn.bind (weOf T₂ σ 239)).isSome}"
        let locs := mapOf T₂ σ 239 S₂.base
        let bad := locs.filter fun p =>
          match internE 57 σ 239 T₂ p.2, p.1.node S₂.base with
          | some (_, y), some x => x != y
          | _, _ => true
        IO.println s!"-- locations: {locs.length}, disagreeing: {bad.length}"
        match bad.head? with
        | some p => IO.println s!"-- first disagreement: {repr p.1} := {repr p.2}"
        | none => IO.println "-- every location agrees"

/-- Print the certificate at a cut as Lean source. -/
def report (k : Nat) : IO Unit := do
  match cutAt k with
  | none => IO.println s!"-- cut at {k}: the symbolic run did not complete"
  | some (c, A) => do
    IO.println s!"-- cut at {k} instructions of part 1, base slot {baseOf c}"
    IO.println s!"def paCut : List (Loc × WE) :="
    IO.println s!"  {repr c.locs}"
    IO.println s!"def paCutCarry : Option WE := {repr c.cf}"
    IO.println s!"def paCutZero : Option WE := {repr c.zf}"
    IO.println "def paCutState : DState :="
    IO.println s!"  ⟨{repr A.entry}, {repr A.regs}, {repr A.cells}⟩"
    IO.println s!"def paCutBase : Nat := {baseOf c}"

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddCutGen

open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddCutGen in
#eval report half1.length

open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddCutGen in
