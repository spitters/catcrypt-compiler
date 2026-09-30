/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG

/-!
# An allocation checker over a control-flow graph

A forward dataflow analysis that validates register-allocation decisions over the whole
control-flow graph of a body. It is written once over an abstract instruction type `I`,
described by an instruction signature `Sig I` (the operands an instruction reads and
writes, the ties between them, the locations it clobbers), and an allocation `Alloc`
(the location of every operand, the moves inserted around every instruction and on
every edge, and the instructions not materialised).

The abstract state at a program point is a `Fact`: a map from locations to sets of
virtual names, `n ∈ S ℓ` stating that location `ℓ` holds the value of `n`. A location of
kind `pinned` is its own name's location and nothing else's; it is outside the fact.
The state of a block not yet reached is `⊤` (`none`). The merge at a block entry is the
pointwise intersection, and the analysis iterates from `⊤` downwards with a worklist
of blocks.

The transfer of one instruction (`stepInstr`) applies the moves before it, checks that
every use finds its name at the chosen location under the operand's constraint, checks
the ties, requires the instruction's implicitly read locations to hold their home names,
empties the clobbered locations, removes every defined name from every location and
places it at its chosen location (joining the source's set for a coalesced copy), and
applies the moves after it. An instruction the allocation deletes must be pure; its
defined names are removed and placed nowhere. No liveness is computed: a value
overwritten while still needed is detected at the later use that fails to find it.

## Main definitions

* `LocKind`, `Loc`, `Constraint`, `Operand`, `Sig`: the instruction signature interface.
* `Edit`, `Alloc`: the allocation.
* `Fact`, `join`: the lattice.
* `stepInstr`, `stepBlock`: the transfer functions.
* `AllocFailure`: the reason and place of a rejection.
* `allocCheckE`, `allocCheck`: the worklist fixpoint, with and without the reason.
* `lineCFG`: the one-block graph of a straight-line body.

## Main results

* `allocCheck`: an executable decision procedure; its soundness is not stated here.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.Check

open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG

/-! ## 1. The instruction signature interface -/

/-- The kind of a location: a general-purpose register, a vector register, a spill-frame
    cell, a scratch register withheld from residence, or a pinned name that is its own
    location (flags, memory cells, sentinels). -/
inductive LocKind where
  | gp
  | ymm
  | frame
  | scratch
  | pinned
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- A location: its kind and its identifier. -/
structure Loc where
  /-- The kind. -/
  kind : LocKind
  /-- The identifier (a register name, a frame cell's name or offset). -/
  id : String
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- The constraint an operand places on its location. -/
inductive Constraint where
  /-- A location the instance admits for the operand's name (`Sig.anyOk`). -/
  | any
  /-- A location of the given kind. -/
  | kind (k : LocKind)
  /-- Exactly the given location. -/
  | at (ℓ : Loc)
  deriving DecidableEq, Repr, Inhabited

/-- An operand: a virtual name and its constraint. -/
structure Operand where
  /-- The virtual name. -/
  name : String
  /-- The constraint. -/
  con : Constraint
  deriving DecidableEq, Repr, Inhabited

/-- An instruction signature over the instruction type `I`. -/
structure Sig (I : Type) where
  /-- The operands an instruction reads, in order. -/
  uses : I → List Operand
  /-- The operands an instruction writes, in order. -/
  defs : I → List Operand
  /-- Pairs `(i, j)`: definition `i` is placed where use `j` is. -/
  ties : I → List (Nat × Nat)
  /-- Locations an instruction overwrites with no named value. -/
  clobbers : I → List Loc
  /-- The instruction copies its single use to its single definition. -/
  isCopy : I → Bool
  /-- The instruction has no effect beyond its definitions. -/
  isPure : I → Bool
  /-- The instruction names a spill-frame cell as program memory. -/
  frameRef : I → Bool
  /-- Locations the instruction may read without naming them; each must hold its home
      name. -/
  atHome : I → List Loc
  /-- The locations the constraint `any` admits for a name. -/
  anyOk : String → Loc → Bool
  /-- Only the home name may be placed at the location. -/
  homeOnly : Loc → Bool
  /-- The name the source program uses for a location. -/
  home : Loc → String
  /-- A move from the first location to the second can be materialised. -/
  moveOk : Loc → Loc → Bool

/-! ## 2. The allocation -/

/-- A move inserted by the allocation. -/
inductive Edit where
  /-- Copy location `src` to location `dst`. -/
  | move (dst src : Loc)
  deriving DecidableEq, Repr, Inhabited

/-- The allocator's output, indexed by instruction index `k` and operand index `j`. -/
structure Alloc where
  /-- The location of use `j` of instruction `k`. -/
  useLoc : Nat → Nat → Loc
  /-- The location of definition `j` of instruction `k`. -/
  defLoc : Nat → Nat → Loc
  /-- Moves inserted before instruction `k`. -/
  before : Nat → List Edit
  /-- Moves inserted after instruction `k`. -/
  after : Nat → List Edit
  /-- Moves inserted on the edge from block `b` to block `b'`. -/
  onEdge : Nat → Nat → List Edit
  /-- Instruction `k` is not materialised. -/
  deleted : Nat → Bool

/-! ## 3. The lattice -/

/-- A set of virtual names. -/
abbrev NameSet := Std.HashSet String

/-- A fact: the names each location holds; an absent location holds none. -/
abbrev Fact := Std.HashMap Loc NameSet

namespace Fact

/-- The names location `ℓ` holds. -/
def get (S : Fact) (ℓ : Loc) : NameSet := S.getD ℓ {}

/-- Set the names of location `ℓ`; an empty set removes the entry. -/
def put (S : Fact) (ℓ : Loc) (A : NameSet) : Fact :=
  if A.isEmpty then S.erase ℓ else S.insert ℓ A

/-- Remove name `n` from every location. -/
def kill (S : Fact) (n : String) : Fact :=
  S.fold (fun acc ℓ A => if A.contains n then acc.put ℓ (A.erase n) else acc) S

/-- The number of `(location, name)` pairs. -/
def card (S : Fact) : Nat := S.fold (fun a _ A => a + A.size) 0

/-- The pointwise intersection. -/
def meet (a b : Fact) : Fact :=
  a.fold (fun acc ℓ A =>
    let B := b.get ℓ
    acc.put ℓ (A.filter (fun n => B.contains n))) {}

end Fact

/-- The state at a block entry: `none` is `⊤`, the point no path has reached. -/
abbrev AState := Option Fact

/-- The merge of two states. -/
def join : AState → AState → AState
  | none, s => s
  | s, none => s
  | some a, some b => some (a.meet b)

/-! ## 4. The transfer functions -/

/-- The reason and place of a rejection. Instruction and block indices are those of the
    body and the graph. -/
inductive AllocFailure where
  /-- Use `n` of instruction `k` is not held by location `ℓ`. -/
  | use (k : Nat) (n : String) (ℓ : Loc)
  /-- Operand `n` of instruction `k` violates its constraint at `ℓ`. -/
  | constraint (k : Nat) (n : String) (ℓ : Loc)
  /-- The tie `(i, j)` of instruction `k` is not respected. -/
  | tie (k : Nat) (i j : Nat)
  /-- Instruction `k` names a frame cell as memory. -/
  | frameRef (k : Nat)
  /-- Name `n` is placed at location `ℓ` reserved for its home name, at instruction `k`. -/
  | homeOnly (k : Nat) (n : String) (ℓ : Loc)
  /-- A move from `src` to `dst` around instruction `k` is not materialisable. -/
  | move (k : Nat) (dst src : Loc)
  /-- Instruction `k` is deleted but not pure. -/
  | impure (k : Nat)
  /-- Location `ℓ` does not hold its home name at instruction `k`. -/
  | atHome (k : Nat) (ℓ : Loc)
  /-- The exit of block `b` does not hold live-out name `n` at `ℓ`. -/
  | exit (b : Nat) (n : String) (ℓ : Loc)
  /-- The fixpoint ran out of fuel. -/
  | fuel
  deriving DecidableEq, Repr, Inhabited

/-- The failure's instruction index, when it has one. -/
def AllocFailure.instr? : AllocFailure → Option Nat
  | .use k .. | .constraint k .. | .tie k .. | .frameRef k | .homeOnly k ..
  | .move k .. | .impure k | .atHome k _ => some k
  | .exit .. | .fuel => none

variable {I : Type}

/-- Location `ℓ` holds name `n`: a pinned location holds exactly its own name. -/
def holds (S : Fact) (ℓ : Loc) (n : String) : Bool :=
  if ℓ.kind = .pinned then ℓ.id == n else (S.get ℓ).contains n

/-- Constraint `c` admits location `ℓ` for name `n`. -/
def conOk (sig : Sig I) (n : String) (ℓ : Loc) : Constraint → Bool
  | .any => sig.anyOk n ℓ
  | .kind k => ℓ.kind == k
  | .at ℓ' => ℓ == ℓ'

/-- Apply a list of moves at instruction `k`. -/
def applyEdits (sig : Sig I) (k : Nat) (es : List Edit) (S : Fact) :
    Except AllocFailure Fact :=
  es.foldlM (fun S e =>
    match e with
    | .move dst src =>
        let A := S.get src
        if !sig.moveOk src dst then .error (.move k dst src)
        else if sig.homeOnly dst && !A.toList.all (· == sig.home dst) then
          .error (.move k dst src)
        else .ok (S.put dst A)) S

/-- Check the uses of instruction `k`. -/
def checkUses (sig : Sig I) (A : Alloc) (k : Nat) (i : I) (S : Fact) :
    Except AllocFailure Unit := do
  let mut j := 0
  for op in sig.uses i do
    let ℓ := A.useLoc k j
    if !conOk sig op.name ℓ op.con then throw (.constraint k op.name ℓ)
    if !holds S ℓ op.name then throw (.use k op.name ℓ)
    j := j + 1

/-- Place the definitions of instruction `k`. -/
def placeDefs (sig : Sig I) (A : Alloc) (k : Nat) (i : I) (S : Fact) :
    Except AllocFailure Fact := do
  let copyLoc : Option Loc :=
    if sig.isCopy i && !(sig.uses i).isEmpty then some (A.useLoc k 0) else none
  let mut S := S
  let mut j := 0
  for op in sig.defs i do
    let ℓ := A.defLoc k j
    if !conOk sig op.name ℓ op.con then throw (.constraint k op.name ℓ)
    if sig.homeOnly ℓ && op.name != sig.home ℓ then throw (.homeOnly k op.name ℓ)
    S := S.kill op.name
    if ℓ.kind != .pinned then
      let base : NameSet := if copyLoc == some ℓ then S.get ℓ else {}
      S := S.put ℓ (base.insert op.name)
    j := j + 1
  return S

/-- The transfer of instruction `k` (the instruction `i`) on fact `S`. -/
def stepInstr (sig : Sig I) (A : Alloc) (k : Nat) (i : I) (S : Fact) :
    Except AllocFailure Fact := do
  let S ← applyEdits sig k (A.before k) S
  if A.deleted k then
    if !sig.isPure i then throw (.impure k)
    let S := (sig.defs i).foldl (fun S op => S.kill op.name) S
    return ← applyEdits sig k (A.after k) S
  if sig.frameRef i then throw (.frameRef k)
  checkUses sig A k i S
  for (a, b) in sig.ties i do
    if A.defLoc k a != A.useLoc k b then throw (.tie k a b)
  for ℓ in sig.atHome i do
    if !holds S ℓ (sig.home ℓ) then throw (.atHome k ℓ)
  let S := (sig.clobbers i).foldl (fun S ℓ => S.erase ℓ) S
  let S ← placeDefs sig A k i S
  applyEdits sig k (A.after k) S

/-- The transfer of the instructions at indices `start ≤ k < stop` of `body`. -/
def stepRange (sig : Sig I) (A : Alloc) (body : Array I) (start stop : Nat) (S : Fact) :
    Except AllocFailure Fact := do
  let mut S := S
  for k in [start:stop] do
    match body[k]? with
    | some i => S ← stepInstr sig A k i S
    | none => pure ()
  return S

/-- The transfer of block `b` of `G`. -/
def stepBlock (sig : Sig I) (A : Alloc) (body : Array I) (G : CFG) (b : Nat) (S : Fact) :
    Except AllocFailure Fact :=
  stepRange sig A body (G.blk b).start (G.blk b).stop S

/-- The live-out names are at their boundary locations at the exit of block `b`. -/
def checkExit (b : Nat) (outReq : List (String × Loc)) (S : Fact) :
    Except AllocFailure Unit := do
  for (n, ℓ) in outReq do
    if !holds S ℓ n then throw (.exit b n ℓ)

/-- The block ends the body: an `Lret`, or a fall-through out of the body. -/
def isExit (t : Term) : Bool :=
  match t with
  | .ret => true
  | _ => t.halts

/-! ## 5. The fixpoint -/

/-- The entry fact of a list of `(location, name)` pairs. -/
def factOf (ps : List (Loc × String)) : Fact :=
  ps.foldl (fun S (ℓ, n) => S.insert ℓ ((S.get ℓ).insert n)) {}

/-- The worklist fixpoint with `fuel` iterations: blocks are popped from `work`, stepped
    from their entry state, the exit condition checked at an exit, and every successor
    whose entry state strictly decreases under the merge is pushed. -/
def fixLoop (sig : Sig I) (A : Alloc) (body : Array I) (G : CFG)
    (outReq : List (String × Loc)) :
    Nat → List Nat → Array AState → Except AllocFailure Unit
  | _, [], _ => .ok ()
  | 0, _ :: _, _ => .error .fuel
  | fuel + 1, b :: work, In =>
      match In.getD b none with
      | none => fixLoop sig A body G outReq fuel work In
      | some S => do
          let S' ← stepBlock sig A body G b S
          let t := (G.blk b).term
          if isExit t then checkExit b outReq S'
          let mut In := In
          let mut work := work
          for b' in t.succs do
            let T ← applyEdits sig (G.blk b).stop (A.onEdge b b') S'
            let old := In.getD b' none
            let J := join old (some T)
            let changed := match old, J with
              | none, _ => true
              | some o, some j => j.card != o.card
              | some _, none => false
            if changed then
              In := In.set! b' J
              if !work.contains b' then work := work ++ [b']
          fixLoop sig A body G outReq fuel work In

/-- The number of `(location, name)` pairs an allocation over `body` can mention: the
    distinct locations times the distinct names of the entry fact, the operands and the
    moves, plus the live-out requirements. -/
def pairBound (sig : Sig I) (A : Alloc) (body : Array I) (entry : List (Loc × String))
    (outReq : List (String × Loc)) : Nat := Id.run do
  let mut locs : Std.HashSet Loc := {}
  let mut names : Std.HashSet String := {}
  for (ℓ, n) in entry do
    locs := locs.insert ℓ
    names := names.insert n
  for (n, ℓ) in outReq do
    locs := locs.insert ℓ
    names := names.insert n
  let mut k := 0
  for i in body do
    let mut j := 0
    for op in sig.uses i do
      locs := locs.insert (A.useLoc k j)
      names := names.insert op.name
      j := j + 1
    j := 0
    for op in sig.defs i do
      locs := locs.insert (A.defLoc k j)
      names := names.insert op.name
      j := j + 1
    for e in A.before k ++ A.after k do
      match e with
      | .move d s => locs := (locs.insert d).insert s
    k := k + 1
  return locs.size * names.size

/-- **The allocation check with its failure.** The entry block starts from the fact of
    `entry`; every other block starts at `⊤`. `outReq` lists each live-out name with its
    location at an exit. The fuel is the number of blocks times one more than the number
    of `(location, name)` pairs the allocation can mention, plus one: each push of a block
    other than the first strictly decreases its entry state. -/
def allocCheckE (sig : Sig I) (G : CFG) (body : Array I) (A : Alloc)
    (entry : List (Loc × String)) (outReq : List (String × Loc)) :
    Except AllocFailure Unit :=
  let S₀ := factOf entry
  if G.blocks.size = 0 then checkExit 0 outReq S₀
  else
    let fuel := G.blocks.size * (pairBound sig A body entry outReq + 2) + 1
    let In : Array AState := (Array.replicate G.blocks.size none).set! 0 (some S₀)
    fixLoop sig A body G outReq fuel [0] In

/-- **The allocation check.** -/
def allocCheck (sig : Sig I) (G : CFG) (body : Array I) (A : Alloc)
    (entry : List (Loc × String)) (outReq : List (String × Loc)) : Bool :=
  (allocCheckE sig G body A entry outReq).toBool

/-- The one-block graph of a straight-line body of `n` instructions: the block falls
    through out of the body. -/
def lineCFG (n : Nat) : CFG :=
  if n = 0 then { blocks := #[], blockOf := #[], preds := #[] }
  else { blocks := #[{ start := 0, stop := n, term := .fall none }],
         blockOf := Array.replicate n 0, preds := #[[]] }

end CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.Check
