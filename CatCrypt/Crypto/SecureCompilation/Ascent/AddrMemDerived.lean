/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
public import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.CallSeg
public import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.ShippedCT
public import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519PointAddShipped

/-!
# Address memory for derived pointers

`AddrMem.disciplinedB` accepts a block only when every memory base holds, at the access,
the entry value of a fixed register. This module accepts blocks whose bases are computed:
copied, offset by `lea` or by an immediate `add`/`sub`, stored to memory and loaded back,
and indexed by registers holding known constants.

## The abstract domain

`DState` assigns to each register and to some memory cells an abstract value `AVal`:
`ptr b δ`, the base address of bank `b` plus `δ` (`keyAddr bank P (b, δ)`), or `const v`,
the word `v`. A register without a value is untracked. At the entry state a register `r`
with `bank r = some r` holds `ptr r 0`, and every other register is untracked
(`DState.entry = true`); after a call only the listed registers are tracked
(`DState.entry = false`).

`stepD` is the transfer function:

* `mov d, s` gives `d` the value of `s`; `mov d, $n` gives `const n`.
* `lea d, off(b, x, sc)` gives `ptr e (δ + off)` when `sc = 0` and `b` holds `ptr e δ`,
  `ptr e (δ + sc·c + off)` when `x` holds `const c`, and `const` when both are constants.
* `add d, $n` and `sub d, $n` shift the value of `d` by `n`.
* A load gives `d` the value of the loaded cell; a store gives the cell the value of the
  stored operand, or untracks it; `addToMem` untracks its cell.
* Every other register write untracks the register.

A memory operand `off(b)` is accepted when `b` holds `ptr e δ`; its cell is
`(e, δ + off)`. An indexed operand `(b, x, sc)` is accepted when `b` holds `ptr e δ` and
`x` holds `const c`; its cell is `(e, δ + sc·c)`. `loadSym` is rejected.
`disciplinedD bank blk` runs the check from the entry state.

## The canonical block

`canonD bank blk` rewrites every accepted memory operand to its cell: `off(b)` becomes
`o(e)` for the cell `(e, o)`, and an indexed load or store becomes the displacement load
or store at its cell. The canonical block has displacement operands only, and its
name-keyed memory at bank `e` is the address memory at the base address of `e`.

## Calls

`disciplinedSegsD bank saved keep A segs` checks each body of a `List CallSeg` and, after
each call, continues from `afterCallD bank saved keep`: a register keeps its value iff it
is in `saved`, a cell keeps its value iff it is in `keep`, and every other register and
cell is untracked. `afterCallD_inv` states the rule is sound for a callee that preserves
the registers of `saved` and the eight bytes of each cell of `keep`.

## Main definitions

* `AVal`, `DState`, `stepD`, `runD`, `accessOKD`, `disciplinedFromD`, `disciplinedD`.
* `memCell`, `canonI`, `canonStep`, `canonFromD`, `canonD`: the canonical block.
* `afterCallD`, `disciplinedSegsD`, `canonSegsD`: the checker and the canonical form of a
  function with calls.
* `RegInvD`, `CellInvD`, `jOfD`: the invariant relating a state to the abstract state,
  and the name-keyed state of an address state at given entry pointers.

## Main results

* `runBlockA_simD_from`: under the check from an abstract state `A` whose invariant holds,
  for a pairwise separated cell set `K` that contains the cells tracked by `A`, every cell
  the canonical block writes, and every cell it reads after its first write,
  `runBlockA sa blk` and `runBlock (jOfD bank P sa) (canonFromD bank A blk)` end with equal
  registers and flags and agree on `K`; the invariant holds at the end.
* `runBlockA_simD_on`, `runBlockA_simD`, `runBlockA_simD_readsBeforeWrites`: the entry-state
  forms, with `K` given, the canonical footprint, and the canonical written cells.
* `runBlockA_mem_frameD`: a byte outside every canonical written cell keeps its value.
* `afterCallD_inv`: the call rule.
* `disciplinedFromD_append`, `disciplinedSegsD_append`: the checks split at a concatenation.
* `fe25519Mul_disciplinedD` … `ed25519PointAdd_disciplinedD`: the check passes on each of
  the thirteen imported shipped blocks, with the bank `shippedBank`.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported (CallSeg)

/-! ## The abstract domain -/

/-- An abstract word: the base address of bank `b` plus `δ`, or a constant. -/
inductive AVal where
  /-- The base address of bank `b` plus `δ`. -/
  | ptr (b : String) (δ : Int)
  /-- The word `v`. -/
  | const (v : BitVec 64)
  deriving DecidableEq, Repr

/-- The word an abstract value denotes at the entry pointers `P`. -/
def AVal.denote (bank : String → Option String) (P : String → BitVec 64) : AVal → BitVec 64
  | .ptr b δ => basePtr bank P b + BitVec.ofInt 64 δ
  | .const v => v

/-- The abstract value shifted by `c`. -/
def AVal.shift (c : Int) : AVal → AVal
  | .ptr b δ => .ptr b (δ + c)
  | .const v => .const (v + BitVec.ofInt 64 c)

theorem AVal.denote_shift (bank : String → Option String) (P : String → BitVec 64) (c : Int)
    (v : AVal) : (v.shift c).denote bank P = v.denote bank P + BitVec.ofInt 64 c := by
  cases v <;> simp [AVal.shift, AVal.denote, BitVec.ofInt_add, BitVec.add_assoc]

/-- An abstract state: values of the listed registers, values of the listed cells, and
    whether an unlisted register holds its entry value. -/
structure DState where
  /-- Unlisted registers hold their entry values. -/
  entry : Bool := true
  /-- The listed registers and their values (`none`: untracked). -/
  regs : List (String × Option AVal) := []
  /-- The tracked cells and their values. -/
  cells : List ((String × Int) × AVal) := []
  deriving DecidableEq, Repr

/-- The first entry of `r` in a register list. -/
def lookupR : List (String × Option AVal) → String → Option (Option AVal)
  | [], _ => none
  | (k, v) :: t, r => if r = k then some v else lookupR t r

/-- The first entry of `c` in a cell list. -/
def lookupC : List ((String × Int) × AVal) → (String × Int) → Option AVal
  | [], _ => none
  | (k, v) :: t, c => if c = k then some v else lookupC t c

/-- The entry value of register `r`: `ptr r 0` when `r` is a bank based at itself. -/
def entryVal (bank : String → Option String) (r : String) : Option AVal :=
  if bank r = some r then some (.ptr r 0) else none

/-- The abstract value of register `r`. -/
def DState.get (bank : String → Option String) (A : DState) (r : String) : Option AVal :=
  match lookupR A.regs r with
  | some v => v
  | none => if A.entry then entryVal bank r else none

/-- An unlisted register `d` reads as untracked. -/
def DState.dfltNone (bank : String → Option String) (A : DState) (d : String) : Bool :=
  !A.entry || (entryVal bank d).isNone

/-- Set the value of register `d`. An untracked value is not listed when an unlisted `d`
    already reads as untracked. -/
def DState.setR (bank : String → Option String) (A : DState) (d : String)
    (v : Option AVal) : DState :=
  { A with regs :=
      match v with
      | none => if A.dfltNone bank d then A.regs.filter (fun p => !decide (p.1 = d))
          else (d, none) :: A.regs.filter (fun p => !decide (p.1 = d))
      | some w => (d, some w) :: A.regs.filter (fun p => !decide (p.1 = d)) }

/-- Set the value of cell `k`, or untrack it. -/
def DState.setC (A : DState) (k : String × Int) (v : Option AVal) : DState :=
  { A with cells :=
      match v with
      | some w => (k, w) :: A.cells.filter (fun p => !decide (p.1 = k))
      | none => A.cells.filter (fun p => !decide (p.1 = k)) }

/-- Untrack the registers `ds`. -/
def DState.killAll (bank : String → Option String) (A : DState) (ds : List String) :
    DState :=
  ds.foldl (fun A d => A.setR bank d none) A

/-- The tracked cells. -/
def DState.cellKeys (A : DState) : List (String × Int) := A.cells.map (·.1)

theorem lookupR_filter (t : List (String × Option AVal)) (d r : String) (h : r ≠ d) :
    lookupR (t.filter (fun p => !decide (p.1 = d))) r = lookupR t r := by
  induction t with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨k, v⟩ := p
    by_cases hk : k = d
    · subst hk
      have hrk : r ≠ k := h
      simp [List.filter, lookupR, hrk, ih]
    · rw [List.filter_cons_of_pos (by simpa using hk)]
      simp only [lookupR, ih]

theorem lookupC_filter (t : List ((String × Int) × AVal)) (d c : String × Int) (h : c ≠ d) :
    lookupC (t.filter (fun p => !decide (p.1 = d))) c = lookupC t c := by
  induction t with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨k, v⟩ := p
    by_cases hk : k = d
    · subst hk
      have hck : c ≠ k := h
      simp [List.filter, lookupC, hck, ih]
    · rw [List.filter_cons_of_pos (by simpa using hk)]
      simp only [lookupC, ih]

theorem lookupC_filter_self (t : List ((String × Int) × AVal)) (d : String × Int) :
    lookupC (t.filter (fun p => !decide (p.1 = d))) d = none := by
  induction t with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨k, v⟩ := p
    by_cases hk : k = d
    · subst hk
      simp [List.filter, ih]
    · rw [List.filter_cons_of_pos (by simpa using hk)]
      simp only [lookupC, ih, if_neg (Ne.symm hk)]

theorem lookupR_filter_self (t : List (String × Option AVal)) (d : String) :
    lookupR (t.filter (fun p => !decide (p.1 = d))) d = none := by
  induction t with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨k, v⟩ := p
    by_cases hk : k = d
    · subst hk
      simp [List.filter, ih]
    · rw [List.filter_cons_of_pos (by simpa using hk)]
      simp only [lookupR, ih, if_neg (Ne.symm hk)]

theorem lookupR_setR (bank : String → Option String) (A : DState) (d r : String)
    (v : Option AVal) :
    lookupR (A.setR bank d v).regs r =
      if r = d then (if v.isNone && A.dfltNone bank d then none else some v)
      else lookupR A.regs r := by
  unfold DState.setR
  by_cases h : r = d
  · subst h
    cases v with
    | some w => simp [lookupR]
    | none =>
      by_cases hn : A.dfltNone bank r = true
      · simp [hn, lookupR_filter_self]
      · simp [hn, lookupR]
  · cases v with
    | some w => simp [lookupR, h, lookupR_filter _ _ _ h]
    | none =>
      by_cases hn : A.dfltNone bank d = true
      · simp [hn, h, lookupR_filter _ _ _ h]
      · simp [hn, h, lookupR, lookupR_filter _ _ _ h]

theorem DState.get_setR (bank : String → Option String) (A : DState) (d r : String)
    (v : Option AVal) : (A.setR bank d v).get bank r = if r = d then v else A.get bank r := by
  have he : (A.setR bank d v).entry = A.entry := rfl
  unfold DState.get
  rw [lookupR_setR, he]
  by_cases h : r = d
  · subst h
    cases v with
    | some w => simp
    | none =>
      by_cases hn : A.dfltNone bank r = true
      · simp only [DState.dfltNone, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
          Option.isNone_iff_eq_none] at hn
        rcases hn with hn | hn <;> simp [hn, DState.dfltNone]
      · simp [hn]
  · simp [h]

theorem DState.cells_setR (bank : String → Option String) (A : DState) (d : String)
    (v : Option AVal) : (A.setR bank d v).cells = A.cells := rfl

theorem DState.get_killAll (bank : String → Option String) (ds : List String) (A : DState)
    (r : String) :
    (A.killAll bank ds).get bank r = if r ∈ ds then none else A.get bank r := by
  induction ds generalizing A with
  | nil => simp [DState.killAll]
  | cons d ds ih =>
    have e : A.killAll bank (d :: ds) = (A.setR bank d none).killAll bank ds := rfl
    rw [e, ih, DState.get_setR]
    by_cases h1 : r ∈ ds <;> by_cases h2 : r = d <;> simp [h1, h2]

theorem DState.cells_killAll (bank : String → Option String) (ds : List String)
    (A : DState) : (A.killAll bank ds).cells = A.cells := by
  induction ds generalizing A with
  | nil => rfl
  | cons d ds ih => exact ih (A.setR bank d none)

theorem DState.lookupC_setC (A : DState) (k c : String × Int) (v : Option AVal) :
    lookupC (A.setC k v).cells c = if c = k then v else lookupC A.cells c := by
  by_cases h : c = k
  · subst h
    cases v <;> simp [DState.setC, lookupC, lookupC_filter_self]
  · rw [if_neg h]
    cases v <;> simp only [DState.setC, lookupC, if_neg h, lookupC_filter _ _ _ h]

theorem DState.get_setC (bank : String → Option String) (A : DState) (k : String × Int)
    (v : Option AVal) (r : String) : (A.setC k v).get bank r = A.get bank r := rfl

theorem mem_cellKeys_of_lookupC {t : List ((String × Int) × AVal)} {c : String × Int}
    {v : AVal} (h : lookupC t c = some v) : c ∈ t.map (·.1) := by
  induction t with
  | nil => simp [lookupC] at h
  | cons p t ih =>
    obtain ⟨k, w⟩ := p
    simp only [lookupC] at h
    by_cases hc : c = k
    · simp [hc]
    · rw [if_neg hc] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem cellKeys_setC (A : DState) (k : String × Int) (v : Option AVal) (c : String × Int)
    (h : c ∈ (A.setC k v).cellKeys) : c = k ∨ c ∈ A.cellKeys := by
  unfold DState.cellKeys DState.setC at h
  cases v with
  | none =>
    simp only [List.mem_map, List.mem_filter] at h
    obtain ⟨p, ⟨hp, -⟩, rfl⟩ := h
    exact Or.inr (List.mem_map_of_mem hp)
  | some w =>
    simp only [List.map_cons, List.mem_cons, List.mem_map, List.mem_filter] at h
    rcases h with rfl | ⟨p, ⟨hp, -⟩, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (List.mem_map_of_mem hp)

/-! ## Values of operands and cells of memory operands -/

/-- The abstract value of an operand. -/
def DState.opVal (bank : String → Option String) (A : DState) : JOperand → Option AVal
  | .reg r => A.get bank r
  | .imm n => some (.const (BitVec.ofNat 64 n))

/-- The value `lea` writes for `off(b, x, sc)`. -/
def DState.leaVal (bank : String → Option String) (A : DState) (b x : String) (sc : Nat)
    (off : Int) : Option AVal :=
  if sc = 0 then (A.get bank b).map (AVal.shift off)
  else match A.get bank b, A.get bank x with
    | some v, some (.const c) => some (v.shift (((c.toNat * sc : Nat) : Int) + off))
    | _, _ => none

/-- The cell of the displacement operand `off(b)`. -/
def DState.cell (bank : String → Option String) (A : DState) (b : String) (off : Int) :
    Option (String × Int) :=
  match A.get bank b with
  | some (.ptr e δ) => some (e, δ + off)
  | _ => none

/-- The cell of the indexed operand `(b, x, sc)`. -/
def DState.cellIdx (bank : String → Option String) (A : DState) (b x : String) (sc : Nat) :
    Option (String × Int) :=
  match A.get bank b, A.get bank x with
  | some (.ptr e δ), some (.const c) => some (e, δ + ((sc * c.toNat : Nat) : Int))
  | _, _ => none

/-- The base, index and scale of an indexed memory operand. -/
def idxOf : JInstr 64 → Option (String × String × Nat)
  | .loadMemIdx _ b x sc => some (b, x, sc)
  | .storeMemIdx b x sc _ => some (b, x, sc)
  | _ => none

/-- The cell `(base, offset)` of a displacement memory operand, read or written. -/
def dispKey (i : JInstr 64) : Option (String × Int) := (readKey i).or (writeKey i)

/-- The canonical cell of the instruction's memory operand, when the abstract state
    determines it. -/
def memCell (bank : String → Option String) (A : DState) (i : JInstr 64) :
    Option (String × Int) :=
  match idxOf i with
  | some (b, x, sc) => A.cellIdx bank b x sc
  | none => (dispKey i).bind fun c => A.cell bank c.1 c.2

/-- `loadSym`, which has no address meaning. -/
def isLoadSym : JInstr 64 → Bool
  | .loadSym .. => true
  | _ => false

/-- The instruction is accepted: it is not `loadSym`, and if it accesses memory its
    canonical cell is determined. -/
def accessOKD (bank : String → Option String) (A : DState) (i : JInstr 64) : Bool :=
  !isLoadSym i && (((idxOf i).isNone && (dispKey i).isNone) || (memCell bank A i).isSome)

/-- The instruction with its memory operand replaced by the displacement operand of cell
    `k`; an indexed load or store becomes a displacement load or store. -/
def canonI (i : JInstr 64) (k : String × Int) : JInstr 64 :=
  match i with
  | .loadMem d _ _ => .loadMem d k.1 k.2
  | .storeMem _ _ s => .storeMem k.1 k.2 s
  | .loadMemIdx d _ _ _ => .loadMem d k.1 k.2
  | .storeMemIdx _ _ _ s => .storeMem k.1 k.2 s
  | .mulxMem h l a _ _ => .mulxMem h l a k.1 k.2
  | .addMem d _ _ => .addMem d k.1 k.2
  | .addToMem _ _ s => .addToMem k.1 k.2 s
  | .adcxMem d _ _ => .adcxMem d k.1 k.2
  | .adoxMem d _ _ => .adoxMem d k.1 k.2
  | .imulMem d _ _ => .imulMem d k.1 k.2
  | .imulriMem d _ _ n => .imulriMem d k.1 k.2 n
  | i => i

/-- The canonical form of an instruction under the abstract state `A`. -/
def canonStep (bank : String → Option String) (A : DState) (i : JInstr 64) : JInstr 64 :=
  match memCell bank A i with
  | some k => canonI i k
  | none => i

/-- The register value a load gives: the value of the loaded cell. -/
def DState.loadVal (bank : String → Option String) (A : DState) (i : JInstr 64) :
    Option AVal :=
  (memCell bank A i).bind (lookupC A.cells)

/-- The transfer function of the abstract domain. -/
def stepD (bank : String → Option String) (A : DState) (i : JInstr 64) : DState :=
  match i with
  | .mov d s => A.setR bank d (A.opVal bank s)
  | .lea d b x sc off => A.setR bank d (A.leaVal bank b x sc off)
  | .add d (.imm n) => A.setR bank d ((A.get bank d).map (AVal.shift (n : Int)))
  | .sub d (.imm n) => A.setR bank d ((A.get bank d).map (AVal.shift (-(n : Int))))
  | .loadMem d b o => A.setR bank d (A.loadVal bank (.loadMem d b o))
  | .loadMemIdx d b x sc => A.setR bank d (A.loadVal bank (.loadMemIdx d b x sc))
  | .storeMem b o s =>
      match memCell bank A (.storeMem b o s) with
      | some k => A.setC k (A.opVal bank s)
      | none => A
  | .storeMemIdx b x sc s =>
      match memCell bank A (.storeMemIdx b x sc s) with
      | some k => A.setC k (A.opVal bank s)
      | none => A
  | .addToMem b o s =>
      match memCell bank A (.addToMem b o s) with
      | some k => A.setC k none
      | none => A
  | i => A.killAll bank (dsts i)

/-- The abstract state after a block. -/
def runD (bank : String → Option String) : DState → List (JInstr 64) → DState
  | A, [] => A
  | A, i :: is => runD bank (stepD bank A i) is

/-- `accessOKD` at every instruction, with the abstract state propagated by `stepD`. -/
def disciplinedFromD (bank : String → Option String) : DState → List (JInstr 64) → Bool
  | _, [] => true
  | A, i :: is => accessOKD bank A i && disciplinedFromD bank (stepD bank A i) is

/-- The check from the entry state. -/
def disciplinedD (bank : String → Option String) (blk : List (JInstr 64)) : Bool :=
  disciplinedFromD bank {} blk

/-- The canonical block from the abstract state `A`. -/
def canonFromD (bank : String → Option String) : DState → List (JInstr 64) → List (JInstr 64)
  | _, [] => []
  | A, i :: is => canonStep bank A i :: canonFromD bank (stepD bank A i) is

/-- The canonical block from the entry state. -/
def canonD (bank : String → Option String) (blk : List (JInstr 64)) : List (JInstr 64) :=
  canonFromD bank {} blk

/-! ## Calls -/

/-- The abstract state after a call: the registers of `saved` keep their values, the cells
    of `keep` keep their values, and every other register and cell is untracked. -/
def afterCallD (bank : String → Option String) (saved : List String)
    (keep : List (String × Int)) (A : DState) : DState where
  entry := false
  regs := saved.map fun r => (r, A.get bank r)
  cells := A.cells.filter fun p => decide (p.1 ∈ keep)

/-- The abstract state after a segment and its call. -/
def segNext (bank : String → Option String) (saved : List String)
    (keep : List (String × Int)) (A : DState) (g : CallSeg) : DState :=
  match g.callee with
  | none => runD bank A g.body
  | some _ => afterCallD bank saved keep (runD bank A g.body)

/-- The check of a function with calls: each body from the abstract state after the
    previous segment and its call. -/
def disciplinedSegsD (bank : String → Option String) (saved : List String)
    (keep : List (String × Int)) : DState → List CallSeg → Bool
  | _, [] => true
  | A, g :: gs => disciplinedFromD bank A g.body &&
      disciplinedSegsD bank saved keep (segNext bank saved keep A g) gs

/-- The canonical form of a function with calls: each body canonicalised from the abstract
    state at its start. -/
def canonSegsD (bank : String → Option String) (saved : List String)
    (keep : List (String × Int)) : DState → List CallSeg → List CallSeg
  | _, [] => []
  | A, g :: gs => { body := canonFromD bank A g.body, callee := g.callee } ::
      canonSegsD bank saved keep (segNext bank saved keep A g) gs

theorem runD_append (bank : String → Option String) (A : DState) (xs ys : List (JInstr 64)) :
    runD bank A (xs ++ ys) = runD bank (runD bank A xs) ys := by
  induction xs generalizing A with
  | nil => rfl
  | cons i is ih => exact ih _

theorem disciplinedFromD_append {bank : String → Option String} {A B : DState}
    {xs ys : List (JInstr 64)}
    (hx : disciplinedFromD bank A xs = true ∧ runD bank A xs = B)
    (hy : disciplinedFromD bank B ys = true) : disciplinedFromD bank A (xs ++ ys) = true := by
  induction xs generalizing A with
  | nil => obtain ⟨-, rfl⟩ := hx; exact hy
  | cons i is ih =>
    obtain ⟨h1, h2⟩ := hx
    simp only [disciplinedFromD, Bool.and_eq_true] at h1
    simp only [List.cons_append, disciplinedFromD, Bool.and_eq_true]
    exact ⟨h1.1, ih ⟨h1.2, h2⟩⟩

theorem canonFromD_append (bank : String → Option String) (A : DState)
    (xs ys : List (JInstr 64)) :
    canonFromD bank A (xs ++ ys) = canonFromD bank A xs ++ canonFromD bank (runD bank A xs) ys := by
  induction xs generalizing A with
  | nil => rfl
  | cons i is ih => simp only [List.cons_append, canonFromD, runD, ih]

/-- The abstract state after a list of segments and their calls. -/
def runSegsD (bank : String → Option String) (saved : List String)
    (keep : List (String × Int)) : DState → List CallSeg → DState
  | A, [] => A
  | A, g :: gs => runSegsD bank saved keep (segNext bank saved keep A g) gs

theorem disciplinedSegsD_append {bank : String → Option String} {saved : List String}
    {keep : List (String × Int)} {A B : DState} {xs ys : List CallSeg}
    (hx : disciplinedSegsD bank saved keep A xs = true ∧ runSegsD bank saved keep A xs = B)
    (hy : disciplinedSegsD bank saved keep B ys = true) :
    disciplinedSegsD bank saved keep A (xs ++ ys) = true := by
  induction xs generalizing A with
  | nil => obtain ⟨-, rfl⟩ := hx; exact hy
  | cons g gs ih =>
    obtain ⟨h1, h2⟩ := hx
    simp only [disciplinedSegsD, Bool.and_eq_true] at h1
    simp only [List.cons_append, disciplinedSegsD, Bool.and_eq_true]
    exact ⟨h1.1, ih ⟨h1.2, h2⟩⟩

/-! ## The invariant -/

/-- Every register with an abstract value holds the word it denotes. -/
def RegInvD (bank : String → Option String) (P : String → BitVec 64) (A : DState)
    (R : String → BitVec 64) : Prop :=
  ∀ r v, A.get bank r = some v → R r = v.denote bank P

/-- Every tracked cell holds, at its address, the word its value denotes. -/
def CellInvD (bank : String → Option String) (P : String → BitVec 64) (A : DState)
    (m : AMem) : Prop :=
  ∀ c v, lookupC A.cells c = some v → read64 m (keyAddr bank P c) = v.denote bank P

theorem regInvD_entry (bank : String → Option String) (P : String → BitVec 64) :
    RegInvD bank P {} P := by
  intro r v h
  simp only [DState.get, lookupR, if_true, entryVal] at h
  split at h
  · rename_i hb
    cases h
    simp [AVal.denote, basePtr, hb]
  · cases h

theorem cellInvD_entry (bank : String → Option String) (P : String → BitVec 64) (m : AMem) :
    CellInvD bank P {} m := by
  intro c v h
  cases h

/-- The name-keyed state of an address state at the entry pointers `P`. -/
def jOfD (bank : String → Option String) (P : String → BitVec 64) (sa : AState) :
    JState 64 :=
  { regs := sa.regs, flags := sa.flags, mem := absMem bank P sa.mem }

/-! ## One instruction and its canonical form -/

theorem readKey_canonI (i : JInstr 64) (k : String × Int) (hf : addrFormB i = true) :
    readKey (canonI i k) = (readKey i).map fun _ => k := by
  cases i <;> simp only [addrFormB, Bool.false_eq_true] at hf <;> rfl

theorem writeKey_canonI (i : JInstr 64) (k : String × Int) (hf : addrFormB i = true) :
    writeKey (canonI i k) = (writeKey i).map fun _ => k := by
  cases i <;> simp only [addrFormB, Bool.false_eq_true] at hf <;> rfl

theorem addrFormB_canonI (i : JInstr 64) (k : String × Int) (hf : isLoadSym i = false) :
    addrFormB (canonI i k) = true := by
  cases i <;> simp only [isLoadSym, Bool.true_eq_false] at hf <;> rfl

/-- A displacement instruction and its canonical form compute the same registers, flags
    and stored word from two states with equal registers and flags, when the cell the
    first reads holds in the first state what cell `k` holds in the second. -/
theorem evalInstr_canonI (s s' : JState 64) (i : JInstr 64) (k : String × Int)
    (hf : addrFormB i = true) (hr : s.regs = s'.regs) (hfl : s.flags = s'.flags)
    (hm : ∀ c, readKey i = some c → s.mem c.1 c.2 = s'.mem k.1 k.2) :
    (evalInstr s i).regs = (evalInstr s' (canonI i k)).regs ∧
      (evalInstr s i).flags = (evalInstr s' (canonI i k)).flags ∧
      writeVal s i = writeVal s' (canonI i k) := by
  obtain ⟨R, F, M⟩ := s
  obtain ⟨R', F', M'⟩ := s'
  simp only at hr hfl
  subst hr hfl
  cases i <;> simp only [addrFormB, readKey, Option.some.injEq, forall_eq',
      Bool.false_eq_true] at hf hm <;>
    first
    | exact ⟨rfl, rfl, rfl⟩
    | (refine ⟨?_, ?_, ?_⟩ <;> simp only [evalInstr, writeVal, JState.load, canonI, hm] <;> rfl)

theorem addrFormB_of (i : JInstr 64) (hl : isLoadSym i = false) (hx : idxOf i = none) :
    addrFormB i = true := by
  cases i <;> simp_all [isLoadSym, idxOf, addrFormB]

theorem readKey_eq_none_of_dispKey (i : JInstr 64) (h : dispKey i = none) : readKey i = none := by
  unfold dispKey at h
  cases hr : readKey i <;> simp_all

theorem writeKey_eq_none_of_dispKey (i : JInstr 64) (h : dispKey i = none) :
    writeKey i = none := by
  unfold dispKey at h
  cases hr : readKey i <;> simp_all

theorem dispKey_of_readKey {i : JInstr 64} {c : String × Int} (h : readKey i = some c) :
    dispKey i = some c := by
  simp [dispKey, h]

theorem dispKey_of_writeKey {i : JInstr 64} {c : String × Int} (h : writeKey i = some c) :
    dispKey i = some c := by
  cases i <;> simp_all [dispKey, readKey, writeKey]

theorem regs_of_get {bank : String → Option String} {P : String → BitVec 64} {A : DState}
    {R : String → BitVec 64} (hinv : RegInvD bank P A R) {r : String} {v : AVal}
    (h : A.get bank r = some v) : R r = v.denote bank P := hinv r v h

theorem addr_of_cell {bank : String → Option String} {P : String → BitVec 64} {A : DState}
    {R : String → BitVec 64} (hinv : RegInvD bank P A R) {b : String} {o : Int}
    {k : String × Int} (h : A.cell bank b o = some k) :
    R b + BitVec.ofInt 64 o = keyAddr bank P k := by
  unfold DState.cell at h
  split at h
  · rename_i e δ hg
    cases h
    rw [hinv b _ hg]
    simp [AVal.denote, keyAddr, BitVec.ofInt_add, BitVec.add_assoc]
  · cases h

theorem addr_of_cellIdx {bank : String → Option String} {P : String → BitVec 64}
    {A : DState} {R : String → BitVec 64} (hinv : RegInvD bank P A R) {b x : String}
    {sc : Nat} {k : String × Int} (h : A.cellIdx bank b x sc = some k) :
    R b + BitVec.ofInt 64 ((sc * (R x).toNat : Nat) : Int) = keyAddr bank P k := by
  unfold DState.cellIdx at h
  split at h
  · rename_i e δ c hg hx
    cases h
    rw [hinv b _ hg, hinv x _ hx]
    simp [AVal.denote, keyAddr, BitVec.ofInt_add, BitVec.add_assoc]
  · cases h

theorem ofInt_natCast_mul (sc t : Nat) :
    BitVec.ofInt 64 ((sc : Int) * (t : Int)) = BitVec.ofInt 64 ((sc * t : Nat) : Int) := by
  push_cast; rfl

/-- **One instruction.** Under the check and the register invariant, the address machine's
    step on `i` computes the registers and flags of the name-keyed step on the canonical
    instruction from `jOfD bank P sa`, and stores that step's word at the address of the
    canonical written cell. -/
theorem evalInstrA_canonStep (bank : String → Option String) (P : String → BitVec 64)
    (A : DState) (sa : AState) (i : JInstr 64) (hok : accessOKD bank A i = true)
    (hinv : RegInvD bank P A sa.regs) :
    addrFormB (canonStep bank A i) = true ∧
      (evalInstrA sa i).regs = (evalInstr (jOfD bank P sa) (canonStep bank A i)).regs ∧
      (evalInstrA sa i).flags = (evalInstr (jOfD bank P sa) (canonStep bank A i)).flags ∧
      (evalInstrA sa i).mem = match writeKey (canonStep bank A i) with
        | some k => write64 sa.mem (keyAddr bank P k)
            (writeVal (jOfD bank P sa) (canonStep bank A i))
        | none => sa.mem := by
  simp only [accessOKD, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    Bool.or_eq_true, Option.isNone_iff_eq_none, Option.isSome_iff_exists] at hok
  obtain ⟨hls, hacc⟩ := hok
  unfold canonStep
  cases hmc : memCell bank A i with
  | none =>
    have ⟨hx, hd⟩ : idxOf i = none ∧ dispKey i = none := by
      rcases hacc with h | ⟨k, hk⟩
      · exact h
      · rw [hmc] at hk; cases hk
    have hf := addrFormB_of i hls hx
    have hrk := readKey_eq_none_of_dispKey i hd
    have hwk := writeKey_eq_none_of_dispKey i hd
    obtain ⟨h1, h2, -⟩ := evalInstr_congr sa.view (jOfD bank P sa) i hf rfl rfl
      (fun k hk => by rw [hrk] at hk; cases hk)
    refine ⟨hf, h1, h2, ?_⟩
    simp only [hwk, evalInstrA, writeAddr_eq sa i hf, Option.map_none]
  | some k =>
    simp only
    unfold memCell at hmc
    cases hix : idxOf i with
    | some bxs =>
      obtain ⟨b, x, sc⟩ := bxs
      rw [hix] at hmc
      simp only at hmc
      have ha := addr_of_cellIdx hinv hmc
      cases i <;> simp only [idxOf, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hix
      · obtain ⟨rfl, rfl, rfl⟩ := hix
        refine ⟨rfl, ?_, rfl, rfl⟩
        simp only [evalInstrA, canonI, evalInstr, JState.setReg, JState.loadIdx, JState.load,
          JState.get, AState.view, jOfD, absMem, x86_MOV, ofInt_natCast_mul, ha]
      · obtain ⟨rfl, rfl, rfl⟩ := hix
        rename_i src
        refine ⟨rfl, rfl, rfl, ?_⟩
        simp only [evalInstrA, canonI, writeKey, writeAddr, ha, writeVal]
        cases src <;> rfl
    | none =>
      rw [hix] at hmc
      simp only at hmc
      cases hdk : dispKey i with
      | none => rw [hdk] at hmc; cases hmc
      | some c =>
        rw [hdk] at hmc
        simp only [Option.bind_some] at hmc
        have ha := addr_of_cell hinv hmc
        have hf := addrFormB_of i hls hix
        obtain ⟨h1, h2, h3⟩ := evalInstr_canonI sa.view (jOfD bank P sa) i k hf rfl rfl
          (fun c' hc' => by
            have := dispKey_of_readKey hc'
            rw [hdk] at this
            cases this
            simp only [AState.view, jOfD, absMem, ha])
        refine ⟨addrFormB_canonI i k hls, h1, h2, ?_⟩
        simp only [evalInstrA, writeAddr_eq sa i hf, writeKey_canonI i k hf]
        cases hw : writeKey i with
        | none => rfl
        | some c' =>
          have := dispKey_of_writeKey hw
          rw [hdk] at this
          cases this
          simp only [Option.map_some, ha, h3]

theorem mul_ofNat_eq_ofInt (c : BitVec 64) (sc : Nat) :
    c * BitVec.ofNat 64 sc = BitVec.ofInt 64 ((c.toNat * sc : Nat) : Int) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofInt_natCast, Nat.mul_mod_mod]

/-- The value a load gives a register is the word at the address of the loaded cell. -/
theorem load_regs (bank : String → Option String) (P : String → BitVec 64) (A : DState)
    (sa : AState) (i : JInstr 64) (d : String) (k : String × Int)
    (hok : accessOKD bank A i = true) (hinv : RegInvD bank P A sa.regs)
    (hmc : memCell bank A i = some k) (hc : canonI i k = .loadMem d k.1 k.2) :
    (evalInstrA sa i).regs d = read64 sa.mem (keyAddr bank P k) := by
  obtain ⟨-, h1, -, -⟩ := evalInstrA_canonStep bank P A sa i hok hinv
  rw [h1]
  simp only [canonStep, hmc, hc, evalInstr, JState.setReg, JState.load, x86_MOV, if_true,
    jOfD, absMem]

/-- `stepD` preserves the register invariant. -/
theorem regInvD_step (bank : String → Option String) (P : String → BitVec 64) (A : DState)
    (sa : AState) (i : JInstr 64) (hok : accessOKD bank A i = true)
    (hinv : RegInvD bank P A sa.regs) (hcell : CellInvD bank P A sa.mem) :
    RegInvD bank P (stepD bank A i) (evalInstrA sa i).regs := by
  intro r v hv
  have hdef : ∀ i' : JInstr 64, i' = i → stepD bank A i = A.killAll bank (dsts i) →
      (evalInstrA sa i).regs r = v.denote bank P := by
    intro _ _ he
    rw [he, DState.get_killAll] at hv
    split at hv
    · cases hv
    · exact (evalInstr_regs_of_not_mem_dsts sa.view i r ‹_›).trans (hinv r v hv)
  have hload : ∀ d, (stepD bank A i) = A.setR bank d (A.loadVal bank i) →
      (∀ k, memCell bank A i = some k → canonI i k = .loadMem d k.1 k.2) →
      dsts i = [d] → (evalInstrA sa i).regs r = v.denote bank P := by
    intro d he hc hds
    rw [he, DState.get_setR] at hv
    by_cases hrd : r = d
    · rw [if_pos hrd] at hv
      subst hrd
      simp only [DState.loadVal, Option.bind_eq_some_iff] at hv
      obtain ⟨k, hk, hl⟩ := hv
      rw [load_regs bank P A sa i r k hok hinv hk (hc k hk)]
      exact hcell k v hl
    · rw [if_neg hrd] at hv
      have hnd : r ∉ dsts i := by simp [hds, hrd]
      exact (evalInstr_regs_of_not_mem_dsts sa.view i r hnd).trans (hinv r v hv)
  cases i
  case mov d s =>
    simp only [stepD, DState.get_setR] at hv
    simp only [evalInstrA, evalInstr, JState.setReg, x86_MOV, AState.view]
    by_cases hrd : r = d
    · rw [if_pos hrd] at hv ⊢
      cases s with
      | reg s' => exact hinv s' v hv
      | imm n => cases hv; rfl
    · rw [if_neg hrd] at hv ⊢
      exact hinv r v hv
  case lea d b x sc off =>
    simp only [stepD, DState.get_setR] at hv
    simp only [evalInstrA, evalInstr, JState.setReg, x86_LEA, AState.view, JState.get]
    by_cases hrd : r = d
    · rw [if_pos hrd] at hv ⊢
      unfold DState.leaVal at hv
      by_cases hsc : sc = 0
      · rw [if_pos hsc] at hv
        subst hsc
        obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 hv
        rw [AVal.denote_shift, ← hinv b w hw]
        simp
      · rw [if_neg hsc] at hv
        split at hv
        · rename_i w c hw hc
          cases hv
          rw [AVal.denote_shift, ← hinv b w hw, hinv x _ hc]
          simp only [AVal.denote, mul_ofNat_eq_ofInt, BitVec.ofInt_add, BitVec.add_assoc]
        · cases hv
    · rw [if_neg hrd] at hv ⊢
      exact hinv r v hv
  case add d s =>
    cases s with
    | reg s' => exact hdef _ rfl rfl
    | imm n =>
      simp only [stepD, DState.get_setR] at hv
      simp only [evalInstrA, evalInstr, JState.writeB5W, x86_ADD, rflags_of_aluop,
        AState.view, JState.get, JOperand.eval]
      by_cases hrd : r = d
      · rw [if_pos hrd] at hv ⊢
        subst hrd
        obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 hv
        rw [AVal.denote_shift, ← hinv r w hw, BitVec.ofInt_natCast]
      · rw [if_neg hrd] at hv ⊢
        exact hinv r v hv
  case sub d s =>
    cases s with
    | reg s' => exact hdef _ rfl rfl
    | imm n =>
      simp only [stepD, DState.get_setR] at hv
      simp only [evalInstrA, evalInstr, JState.writeB5W, x86_SUB,
        AState.view, JState.get, JOperand.eval]
      by_cases hrd : r = d
      · rw [if_pos hrd] at hv ⊢
        subst hrd
        obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 hv
        rw [AVal.denote_shift, ← hinv r w hw, BitVec.ofInt_neg, BitVec.ofInt_natCast,
          BitVec.sub_eq_add_neg]
      · rw [if_neg hrd] at hv ⊢
        exact hinv r v hv
  case loadMem d b o => exact hload d rfl (fun _ _ => rfl) rfl
  case loadMemIdx d b x sc => exact hload d rfl (fun _ _ => rfl) rfl
  case storeMem b o s =>
    have : (stepD bank A (.storeMem b o s)).get bank r = A.get bank r := by
      simp only [stepD]; split <;> rfl
    rw [this] at hv
    exact hinv r v hv
  case storeMemIdx b x sc s =>
    have : (stepD bank A (.storeMemIdx b x sc s)).get bank r = A.get bank r := by
      simp only [stepD]; split <;> rfl
    rw [this] at hv
    exact hinv r v hv
  case addToMem b o s =>
    have : (stepD bank A (.addToMem b o s)).get bank r = A.get bank r := by
      simp only [stepD]; split <;> rfl
    rw [this] at hv
    exact hinv r v hv
  all_goals exact hdef _ rfl rfl

theorem memCell_some_of_access {bank : String → Option String} {A : DState} {i : JInstr 64}
    (hok : accessOKD bank A i = true) (h : (idxOf i).isSome ∨ (dispKey i).isSome) :
    ∃ k, memCell bank A i = some k := by
  simp only [accessOKD, Bool.and_eq_true, Bool.or_eq_true] at hok
  rcases hok.2 with h' | h'
  · simp only [Option.isNone_iff_eq_none] at h'
    rcases h with h | h <;> simp_all
  · exact Option.isSome_iff_exists.1 h'

theorem opVal_eval {bank : String → Option String} {P : String → BitVec 64} {A : DState}
    {sa : AState} (hinv : RegInvD bank P A sa.regs) (s : JOperand) (w : AVal)
    (h : A.opVal bank s = some w) : s.eval (jOfD bank P sa) = w.denote bank P := by
  cases s with
  | reg r => exact hinv r w h
  | imm n => cases h; rfl

/-- How `stepD` changes the tracked cells: not at all when the canonical instruction writes
    no cell, and by `setC` at the written cell otherwise, with a value that denotes the
    stored word. -/
theorem stepD_cells (bank : String → Option String) (P : String → BitVec 64) (A : DState)
    (sa : AState) (i : JInstr 64) (hok : accessOKD bank A i = true)
    (hinv : RegInvD bank P A sa.regs) :
    match writeKey (canonStep bank A i) with
    | none => (stepD bank A i).cells = A.cells
    | some k => ∃ v, stepD bank A i = A.setC k v ∧
        ∀ w, v = some w → writeVal (jOfD bank P sa) (canonStep bank A i) = w.denote bank P := by
  have hnone : ∀ j : JInstr 64, writeKey j = none →
      (∀ b x sc s, j ≠ .storeMemIdx b x sc s) → writeKey (canonStep bank A j) = none := by
    intro j hj hx
    unfold canonStep
    split
    · cases j <;> first | exact absurd rfl (hx _ _ _ _) | simp_all [canonI, writeKey]
    · exact hj
  cases i
  case storeMem b o s =>
    obtain ⟨k, hk⟩ := memCell_some_of_access hok (Or.inr rfl)
    simp only [canonStep, hk, canonI, writeKey, stepD]
    exact ⟨_, rfl, fun w hw => by simp only [writeVal]; exact opVal_eval hinv s w hw⟩
  case storeMemIdx b x sc s =>
    obtain ⟨k, hk⟩ := memCell_some_of_access hok (Or.inl rfl)
    simp only [canonStep, hk, canonI, writeKey, stepD]
    exact ⟨_, rfl, fun w hw => by simp only [writeVal]; exact opVal_eval hinv s w hw⟩
  case addToMem b o s =>
    obtain ⟨k, hk⟩ := memCell_some_of_access hok (Or.inr rfl)
    simp only [canonStep, hk, canonI, writeKey, stepD]
    exact ⟨_, rfl, fun w hw => by cases hw⟩
  all_goals
    rw [hnone _ rfl (by intro _ _ _ _ h; cases h)]
    first
    | rfl
    | exact DState.cells_killAll _ _
    | (rename_i s; cases s <;> rfl)

theorem cellKeys_stepD (bank : String → Option String) (P : String → BitVec 64) (A : DState)
    (sa : AState) (i : JInstr 64) (hok : accessOKD bank A i = true)
    (hinv : RegInvD bank P A sa.regs) (c : String × Int)
    (hc : c ∈ (stepD bank A i).cellKeys) :
    c ∈ A.cellKeys ∨ writeKey (canonStep bank A i) = some c := by
  have h := stepD_cells bank P A sa i hok hinv
  cases hw : writeKey (canonStep bank A i) with
  | none =>
    rw [hw] at h
    simp only at h
    left
    simpa [DState.cellKeys, h] using hc
  | some k =>
    rw [hw] at h
    obtain ⟨v, hs, -⟩ := h
    rw [hs] at hc
    rcases cellKeys_setC A k v c hc with rfl | h'
    · exact Or.inr rfl
    · exact Or.inl h'

/-- `stepD` preserves the cell invariant, when the written cell is disjoint from every
    other tracked cell. -/
theorem cellInvD_step (bank : String → Option String) (P : String → BitVec 64) (A : DState)
    (sa : AState) (i : JInstr 64) (hok : accessOKD bank A i = true)
    (hinv : RegInvD bank P A sa.regs) (hcell : CellInvD bank P A sa.mem)
    (hsep : ∀ k, writeKey (canonStep bank A i) = some k → ∀ c ∈ A.cellKeys, c ≠ k →
      Disjoint8 (keyAddr bank P k) (keyAddr bank P c)) :
    CellInvD bank P (stepD bank A i) (evalInstrA sa i).mem := by
  obtain ⟨-, -, -, h4⟩ := evalInstrA_canonStep bank P A sa i hok hinv
  have hc := stepD_cells bank P A sa i hok hinv
  intro c w hl
  cases hw : writeKey (canonStep bank A i) with
  | none =>
    rw [hw] at h4 hc
    simp only at h4 hc
    rw [h4]
    rw [hc] at hl
    exact hcell c w hl
  | some k =>
    rw [hw] at h4 hc
    simp only at h4 hc
    obtain ⟨v, hs, hv⟩ := hc
    rw [h4]
    rw [hs, DState.lookupC_setC] at hl
    by_cases hck : c = k
    · subst hck
      rw [if_pos rfl] at hl
      rw [read64_write64_same, hv w hl]
    · rw [if_neg hck] at hl
      rw [read64_write64_of_disjoint _ _ _ _
        (hsep k hw c (mem_cellKeys_of_lookupC hl) hck)]
      exact hcell c w hl

/-! ## The simulation -/

/-- **Simulation from an abstract state.** Under the check from `A`, with the invariant of
    `A` at the entry pointers `P`, let `K` be a pairwise separated set of cells containing
    the cells `A` tracks, every cell the canonical block writes, and every cell it reads
    after its first write (counting from `seen`). Then the address run of `blk` and the
    name-keyed run of the canonical block end with equal registers and flags and agree on
    `K`, and the invariant of `runD bank A blk` holds at the end. -/
theorem runBlockA_simD_core (bank : String → Option String) (P : String → BitVec 64)
    (K : List (String × Int)) (hsep : Separated bank P K) :
    ∀ (blk : List (JInstr 64)) (A : DState) (seen : Bool) (sa : AState) (js : JState 64),
      disciplinedFromD bank A blk = true →
      readsBeforeWritesFromB K seen (canonFromD bank A blk) = true →
      (∀ k ∈ writeKeys (canonFromD bank A blk), k ∈ K) →
      (∀ k ∈ A.cellKeys, k ∈ K) →
      sa.regs = js.regs → sa.flags = js.flags →
      RegInvD bank P A sa.regs → CellInvD bank P A sa.mem →
      (∀ k ∈ K, absMem bank P sa.mem k.1 k.2 = js.mem k.1 k.2) →
      (seen = false → js.mem = absMem bank P sa.mem) →
      (runBlockA sa blk).regs = (runBlock js (canonFromD bank A blk)).regs ∧
        (runBlockA sa blk).flags = (runBlock js (canonFromD bank A blk)).flags ∧
        (∀ k ∈ K, absMem bank P (runBlockA sa blk).mem k.1 k.2 =
          (runBlock js (canonFromD bank A blk)).mem k.1 k.2) ∧
        RegInvD bank P (runD bank A blk) (runBlockA sa blk).regs ∧
        CellInvD bank P (runD bank A blk) (runBlockA sa blk).mem := by
  intro blk
  induction blk with
  | nil =>
    intro _ _ _ _ _ _ _ _ hr hf hinv hcell hK _
    exact ⟨hr, hf, hK, hinv, hcell⟩
  | cons i is ih =>
    intro A seen sa js hd hrw hW hA hr hf hinv hcell hK hpre
    simp only [disciplinedFromD, Bool.and_eq_true] at hd
    obtain ⟨hok, hd⟩ := hd
    simp only [canonFromD, readsBeforeWritesFromB, Bool.and_eq_true] at hrw
    obtain ⟨hrd, hrw⟩ := hrw
    simp only [canonFromD] at hW
    have hW' : ∀ k ∈ writeKeys (canonFromD bank (stepD bank A i) is), k ∈ K :=
      fun k hk => hW k (mem_writeKeys_cons.2 (Or.inr hk))
    obtain ⟨hform, h1, h2, h4⟩ := evalInstrA_canonStep bank P A sa i hok hinv
    have hread : ∀ k, readKey (canonStep bank A i) = some k →
        (jOfD bank P sa).mem k.1 k.2 = js.mem k.1 k.2 := by
      intro k hk
      rw [hk] at hrd
      cases seen with
      | false => rw [hpre rfl]; rfl
      | true =>
        simp only [readOKB, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hrd
        exact hK k hrd
    obtain ⟨hcr, hcf, hcw⟩ := evalInstr_congr (jOfD bank P sa) js _ hform hr hf hread
    simp only [runBlockA_cons, canonFromD, runBlock_cons, runD]
    have hWk : ∀ k, writeKey (canonStep bank A i) = some k → k ∈ K :=
      fun k hk => hW k (mem_writeKeys_cons.2 (Or.inl hk))
    refine ih (stepD bank A i) _ (evalInstrA sa i) _ hd hrw hW' ?_ (h1.trans hcr)
      (h2.trans hcf) (regInvD_step bank P A sa i hok hinv hcell)
      (cellInvD_step bank P A sa i hok hinv hcell ?_) ?_ ?_
    · intro c hc
      rcases cellKeys_stepD bank P A sa i hok hinv c hc with h | h
      · exact hA c h
      · exact hWk c h
    · intro k hk c hc hck
      exact hsep k (hWk k hk) c (hA c hc) (Ne.symm hck)
    · intro k' hk'
      rw [evalInstr_mem js _ hform, h4]
      cases hwi : writeKey (canonStep bank A i) with
      | none => exact hK k' hk'
      | some k =>
        simp only
        rw [← hcw]
        rw [absMem_write bank P sa.mem _ hsep (hWk k hwi) hk']
        by_cases h : k' = k
        · subst h
          simp
        · have h' : ¬ (k'.1 = k.1 ∧ k'.2 = k.2) := fun ⟨e1, e2⟩ => h (Prod.ext e1 e2)
          rw [if_neg h, if_neg h']
          exact hK k' hk'
    · intro hs
      simp only [Bool.or_eq_false_iff] at hs
      obtain ⟨rfl, hnw⟩ := hs
      have hnone : writeKey (canonStep bank A i) = none :=
        Option.not_isSome_iff_eq_none.1 (by simp [hnw])
      rw [evalInstr_mem js _ hform, h4]
      simp only [hnone]
      exact hpre rfl

/-- **Simulation from an abstract state**, with the name-keyed run started from
    `jOfD bank P sa`. -/
theorem runBlockA_simD_from (bank : String → Option String) (P : String → BitVec 64)
    (A : DState) (blk : List (JInstr 64)) (K : List (String × Int))
    (hd : disciplinedFromD bank A blk = true)
    (hrw : readsBeforeWritesFromB K false (canonFromD bank A blk) = true)
    (hW : ∀ k ∈ writeKeys (canonFromD bank A blk), k ∈ K) (hA : ∀ k ∈ A.cellKeys, k ∈ K)
    (sa : AState) (hsep : Separated bank P K) (hinv : RegInvD bank P A sa.regs)
    (hcell : CellInvD bank P A sa.mem) :
    (runBlockA sa blk).regs = (runBlock (jOfD bank P sa) (canonFromD bank A blk)).regs ∧
      (runBlockA sa blk).flags = (runBlock (jOfD bank P sa) (canonFromD bank A blk)).flags ∧
      (∀ k ∈ K, absMem bank P (runBlockA sa blk).mem k.1 k.2 =
        (runBlock (jOfD bank P sa) (canonFromD bank A blk)).mem k.1 k.2) ∧
      RegInvD bank P (runD bank A blk) (runBlockA sa blk).regs ∧
      CellInvD bank P (runD bank A blk) (runBlockA sa blk).mem :=
  runBlockA_simD_core bank P K hsep blk A false sa _ hd hrw hW hA rfl rfl hinv hcell
    (fun _ _ => rfl) (fun _ => rfl)

theorem jOfD_self (bank : String → Option String) (sa : AState) :
    jOfD bank sa.regs sa = jOf bank sa := rfl

/-- **Simulation on a cell set.** Under `disciplinedD`, for a pairwise separated cell set
    `K` containing every cell the canonical block writes and every cell it reads after its
    first write, `runBlockA sa blk` and `runBlock (jOf bank sa) (canonD bank blk)` end with
    equal registers and flags, and agree on every cell of `K`. -/
theorem runBlockA_simD_on (bank : String → Option String) (blk : List (JInstr 64))
    (K : List (String × Int)) (hd : disciplinedD bank blk = true)
    (hrw : readsBeforeWritesFromB K false (canonD bank blk) = true)
    (hW : ∀ k ∈ writeKeys (canonD bank blk), k ∈ K)
    (sa : AState) (hsep : Separated bank sa.regs K) :
    (runBlockA sa blk).regs = (runBlock (jOf bank sa) (canonD bank blk)).regs ∧
      (runBlockA sa blk).flags = (runBlock (jOf bank sa) (canonD bank blk)).flags ∧
      ∀ k ∈ K, absMem bank sa.regs (runBlockA sa blk).mem k.1 k.2 =
        (runBlock (jOf bank sa) (canonD bank blk)).mem k.1 k.2 := by
  obtain ⟨h1, h2, h3, -, -⟩ := runBlockA_simD_from bank sa.regs {} blk K hd hrw hW
    (fun _ h => by simp [DState.cellKeys] at h) sa hsep (regInvD_entry bank sa.regs)
    (cellInvD_entry bank sa.regs sa.mem)
  exact ⟨h1, h2, h3⟩

/-- **Simulation for a separated canonical footprint.** Under `disciplinedD`, when the
    cells the canonical block reads or writes occupy pairwise disjoint ranges, the address
    run and the name-keyed run of the canonical block end with equal registers and flags
    and agree on the footprint. -/
theorem runBlockA_simD (bank : String → Option String) (blk : List (JInstr 64))
    (hd : disciplinedD bank blk = true) (sa : AState)
    (hsep : Separated bank sa.regs (footprint (canonD bank blk))) :
    (runBlockA sa blk).regs = (runBlock (jOf bank sa) (canonD bank blk)).regs ∧
      (runBlockA sa blk).flags = (runBlock (jOf bank sa) (canonD bank blk)).flags ∧
      ∀ k ∈ footprint (canonD bank blk), absMem bank sa.regs (runBlockA sa blk).mem k.1 k.2 =
        (runBlock (jOf bank sa) (canonD bank blk)).mem k.1 k.2 :=
  runBlockA_simD_on bank blk _ hd
    (readsBeforeWritesFromB_of_reads _ (fun _ hk => List.mem_append_left _ hk) false)
    (fun _ hk => List.mem_append_right _ hk) sa hsep

/-- **Simulation when reads come first.** Under `disciplinedD`, when the canonical block
    passes `readsBeforeWritesB`, only its written cells need to be separated from one
    another; an input cell may coincide with or partly overlap an output cell. -/
theorem runBlockA_simD_readsBeforeWrites (bank : String → Option String)
    (blk : List (JInstr 64)) (hd : disciplinedD bank blk = true)
    (hrw : readsBeforeWritesB (canonD bank blk) = true) (sa : AState)
    (hsep : Separated bank sa.regs (writeKeys (canonD bank blk))) :
    (runBlockA sa blk).regs = (runBlock (jOf bank sa) (canonD bank blk)).regs ∧
      (runBlockA sa blk).flags = (runBlock (jOf bank sa) (canonD bank blk)).flags ∧
      ∀ k ∈ writeKeys (canonD bank blk),
        absMem bank sa.regs (runBlockA sa blk).mem k.1 k.2 =
          (runBlock (jOf bank sa) (canonD bank blk)).mem k.1 k.2 :=
  runBlockA_simD_on bank blk _ hd hrw (fun _ hk => hk) sa hsep

/-- **Frame from an abstract state.** Under the check from `A` with the register invariant,
    a byte outside the range of every cell the canonical block writes keeps its value. -/
theorem runBlockA_mem_frameD_from (bank : String → Option String) (P : String → BitVec 64)
    (x : BitVec 64) :
    ∀ (blk : List (JInstr 64)) (A : DState) (sa : AState),
      disciplinedFromD bank A blk = true → RegInvD bank P A sa.regs →
      CellInvD bank P A sa.mem →
      (∀ k ∈ writeKeys (canonFromD bank A blk), ¬ InRange8 (keyAddr bank P k) x) →
      (∀ k ∈ writeKeys (canonFromD bank A blk), ∀ c ∈ A.cellKeys ++
        writeKeys (canonFromD bank A blk), c ≠ k →
        Disjoint8 (keyAddr bank P k) (keyAddr bank P c)) →
      (runBlockA sa blk).mem x = sa.mem x := by
  intro blk
  induction blk with
  | nil => intro _ _ _ _ _ _ _; rfl
  | cons i is ih =>
    intro A sa hd hinv hcell hx hsep
    simp only [disciplinedFromD, Bool.and_eq_true] at hd
    obtain ⟨hok, hd⟩ := hd
    simp only [canonFromD] at hx hsep
    obtain ⟨-, -, -, h4⟩ := evalInstrA_canonStep bank P A sa i hok hinv
    have hWk : ∀ k, writeKey (canonStep bank A i) = some k →
        k ∈ writeKeys (canonStep bank A i :: canonFromD bank (stepD bank A i) is) :=
      fun k hk => mem_writeKeys_cons.2 (Or.inl hk)
    simp only [runBlockA_cons]
    rw [ih (stepD bank A i) (evalInstrA sa i) hd (regInvD_step bank P A sa i hok hinv hcell)
      (cellInvD_step bank P A sa i hok hinv hcell (fun k hk c hc hck =>
        hsep k (hWk k hk) c (List.mem_append_left _ hc) hck))
      (fun k hk => hx k (mem_writeKeys_cons.2 (Or.inr hk)))
      (fun k hk c hc hck => hsep k (mem_writeKeys_cons.2 (Or.inr hk)) c (by
        rcases List.mem_append.1 hc with h | h
        · rcases cellKeys_stepD bank P A sa i hok hinv c h with h' | h'
          · exact List.mem_append_left _ h'
          · exact List.mem_append_right _ (mem_writeKeys_cons.2 (Or.inl h'))
        · exact List.mem_append_right _ (mem_writeKeys_cons.2 (Or.inr h))) hck)]
    rw [h4]
    cases hwi : writeKey (canonStep bank A i) with
    | none => rfl
    | some k => exact write64_of_not_inRange _ _ _ _ (hx k (hWk k hwi))

/-- **Frame.** Under `disciplinedD`, when the canonical written cells are pairwise
    separated, a byte outside the range of every one of them keeps its value. -/
theorem runBlockA_mem_frameD (bank : String → Option String) (blk : List (JInstr 64))
    (hd : disciplinedD bank blk = true) (sa : AState) (x : BitVec 64)
    (hsep : Separated bank sa.regs (writeKeys (canonD bank blk)))
    (hx : ∀ k ∈ writeKeys (canonD bank blk), ¬ InRange8 (keyAddr bank sa.regs k) x) :
    (runBlockA sa blk).mem x = sa.mem x :=
  runBlockA_mem_frameD_from bank sa.regs x blk {} sa hd (regInvD_entry bank sa.regs)
    (cellInvD_entry bank sa.regs sa.mem) hx
    (fun k hk c hc hck => hsep k hk c (by simpa [DState.cellKeys, canonD] using hc)
      (Ne.symm hck))

/-! ## The call rule -/

theorem lookupR_map_saved (bank : String → Option String) (A : DState) (saved : List String)
    (r : String) :
    lookupR (saved.map fun r => (r, A.get bank r)) r =
      if r ∈ saved then some (A.get bank r) else none := by
  induction saved with
  | nil => simp [lookupR]
  | cons s ss ih =>
    simp only [List.map_cons, lookupR, ih, List.mem_cons]
    by_cases h : r = s
    · subst h; simp
    · simp [h]

theorem lookupC_filter_keep (t : List ((String × Int) × AVal)) (keep : List (String × Int))
    (c : String × Int) (v : AVal)
    (h : lookupC (t.filter fun p => decide (p.1 ∈ keep)) c = some v) :
    c ∈ keep ∧ lookupC t c = some v := by
  induction t with
  | nil => simp [lookupC] at h
  | cons p t ih =>
    obtain ⟨k, w⟩ := p
    by_cases hk : k ∈ keep
    · rw [List.filter_cons_of_pos (by simpa using hk)] at h
      simp only [lookupC] at h ⊢
      by_cases hc : c = k
      · subst hc; simp only [if_true] at h ⊢; exact ⟨hk, h⟩
      · rw [if_neg hc] at h ⊢; exact ih h
    · rw [List.filter_cons_of_neg (by simpa using hk)] at h
      obtain ⟨hck, hl⟩ := ih h
      have : c ≠ k := fun e => hk (e ▸ hck)
      simp only [lookupC, if_neg this]
      exact ⟨hck, hl⟩

theorem DState.get_afterCallD (bank : String → Option String) (saved : List String)
    (keep : List (String × Int)) (A : DState) (r : String) :
    (afterCallD bank saved keep A).get bank r = if r ∈ saved then A.get bank r else none := by
  show (match lookupR (saved.map fun r => (r, A.get bank r)) r with
    | some v => v
    | none => if false = true then entryVal bank r else none) = _
  rw [lookupR_map_saved]
  by_cases h : r ∈ saved <;> simp [h]

/-- **The call rule.** If the callee returns registers `R'` and memory `m'` that agree
    with the caller's `R` and `m` on the registers of `saved` and on the eight bytes at
    the address of each cell of `keep`, the invariant of `A` before the call gives the
    invariant of `afterCallD bank saved keep A` after it. -/
theorem afterCallD_inv (bank : String → Option String) (P : String → BitVec 64)
    (saved : List String) (keep : List (String × Int)) (A : DState)
    (R R' : String → BitVec 64) (m m' : AMem)
    (hinv : RegInvD bank P A R) (hcell : CellInvD bank P A m)
    (hR : ∀ r ∈ saved, R' r = R r)
    (hm : ∀ c ∈ keep, read64 m' (keyAddr bank P c) = read64 m (keyAddr bank P c)) :
    RegInvD bank P (afterCallD bank saved keep A) R' ∧
      CellInvD bank P (afterCallD bank saved keep A) m' := by
  constructor
  · intro r v hv
    rw [DState.get_afterCallD] at hv
    by_cases hr : r ∈ saved
    · rw [if_pos hr] at hv
      rw [hR r hr]
      exact hinv r v hv
    · rw [if_neg hr] at hv
      cases hv
  · intro c v hv
    obtain ⟨hk, hl⟩ := lookupC_filter_keep A.cells keep c v hv
    rw [hm c hk]
    exact hcell c v hl

theorem cellKeys_afterCallD (bank : String → Option String) (saved : List String)
    (keep : List (String × Int)) (A : DState) (c : String × Int)
    (h : c ∈ (afterCallD bank saved keep A).cellKeys) : c ∈ A.cellKeys := by
  simp only [DState.cellKeys, afterCallD, List.mem_map, List.mem_filter] at h ⊢
  obtain ⟨p, ⟨hp, -⟩, rfl⟩ := h
  exact ⟨p, hp, rfl⟩

/-! ## The shipped Ed25519 and fe25519 kernels

Each imported block passes the check with `shippedBank`. The kernels with calls pass
`disciplinedSegsD` with the SysV callee-saved registers as `saved`; `ed25519_madd` keeps the
cell `(%rsp, 584)`, where it stores its first argument before the calls and from which it
reloads the output pointer after them, and the other two keep no cell. The scalar kernels and
`ed25519_point_add` are checked part by part, with the abstract state between parts stated. -/

section Shipped
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.ShippedCT (sysvSaved rspCells)

/-- The banks of the shipped kernels: the SysV argument registers and `%rsp`, each based at
    its own entry value. -/
def shippedBank (b : String) : Option String :=
  if b ∈ ["%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%r9", "%rsp"] then some b else none

theorem fe25519Mul_disciplinedD :
    disciplinedD shippedBank Fe25519MulShipped.fe25519MulShippedBlock = true := by
  decide +kernel

theorem fe25519Sqr_disciplinedD :
    disciplinedD shippedBank Fe25519SqrShipped.fe25519SqrShippedBlock = true := by
  decide +kernel

theorem fe25519Add_disciplinedD :
    disciplinedD shippedBank Fe25519AddShipped.fe25519AddShippedBlock = true := by
  decide +kernel

theorem fe25519Sub_disciplinedD :
    disciplinedD shippedBank Fe25519SubShipped.fe25519SubShippedBlock = true := by
  decide +kernel

theorem ed25519CombSelect_disciplinedD :
    disciplinedD shippedBank Ed25519CombSelectShipped.ed25519CombSelectShippedBlock = true := by
  decide +kernel

theorem ed25519Join16_disciplinedD :
    disciplinedD shippedBank Ed25519Join16Shipped.ed25519Join16ShippedBlock = true := by
  decide +kernel

theorem ed25519PackSign_disciplinedD :
    disciplinedD shippedBank Ed25519PackSignShipped.ed25519PackSignShippedBlock = true := by
  decide +kernel

theorem ed25519Madd_disciplinedD :
    disciplinedSegsD shippedBank sysvSaved (rspCells [584]) {}
      Ed25519MaddShipped.ed25519MaddShippedBlock = true := by
  decide +kernel

theorem ed25519Compress_disciplinedD :
    disciplinedSegsD shippedBank sysvSaved [] {}
      Ed25519CompressShipped.ed25519CompressShippedBlock = true := by
  decide +kernel

theorem ed25519Invert_disciplinedD :
    disciplinedSegsD shippedBank sysvSaved [] {}
      Ed25519InvertShipped.ed25519InvertShippedBlock = true := by
  decide +kernel

/-! ### Abstract states between parts -/

/-- The constant `n` as an abstract value. -/
def cst (n : Nat) : AVal := .const (BitVec.ofNat 64 n)

/-- The tracked cell `(%rsp, o)` with value `v`. -/
def rc (o : Int) (v : AVal) : (String × Int) × AVal := (("%rsp", o), v)

/-- The word `2^64 - 1`. -/
def wMax : Nat := 18446744073709551615

/-- The word `2^64 - 21`. -/
def wEB : Nat := 18446744073709551595

/-- The `%rsp` cells at offsets 24, 16, 8 that both scalar kernels fill with constants. -/
def scMid : List ((String × Int) × AVal) :=
  [rc 24 (cst wEB), rc 16 (cst 2379626136568277415), rc 8 (cst 17121812371768873755)]

/-- The `%rsp` cells at offsets 168 to 144 holding the indices 3 to 0. -/
def scIdx : List ((String × Int) × AVal) := [rc 168 (cst 3), rc 160 (cst 2), rc 152 (cst 1),
  rc 144 (cst 0)]

/-- The four constants the scalar kernels store at the offsets `os`. -/
def scHead (o₁ o₂ o₃ o₄ : Int) : List ((String × Int) × AVal) :=
  [rc o₁ (cst 1152921504606846976), rc o₂ (cst 0), rc o₃ (cst 1503914060200516822),
    rc o₄ (cst 6346243789798364141)]

/-- The pointer cells of `ed25519_sc_reduce`. -/
def scrPtrs : List ((String × Int) × AVal) :=
  [rc 136 (.ptr "%rdi" 0), rc 224 (.ptr "%rsi" 0), rc 232 (.ptr "%rdi" 0)]

/-- The index and pointer cells of `ed25519_sc_muladd`. -/
def scmTail : List ((String × Int) × AVal) :=
  scIdx ++ [rc 136 (.ptr "%rdi" 0), rc (-16) (.ptr "%rcx" 0), rc (-8) (.ptr "%rdx" 0),
    rc 224 (.ptr "%rsi" 0), rc 232 (.ptr "%rdi" 0)]

/-- `%rsp` cells tracked by `ed25519_sc_reduce` with both cells 40 and 32. -/
def scrCellsA : List ((String × Int) × AVal) :=
  scHead 88 96 104 112 ++ [rc 40 (cst 15), rc 32 (cst wMax)] ++ scMid ++ scIdx ++ scrPtrs

/-- `%rsp` cells tracked by `ed25519_sc_reduce` without cell 40. -/
def scrCellsB : List ((String × Int) × AVal) :=
  scHead 88 96 104 112 ++ [rc 32 (cst wMax)] ++ scMid ++ scIdx ++ scrPtrs

/-- `%rsp` cells tracked by `ed25519_sc_reduce` without cells 40 and 32. -/
def scrCellsC : List ((String × Int) × AVal) :=
  scHead 88 96 104 112 ++ scMid ++ scIdx ++ scrPtrs

/-- The `%rsp` offsets part 7 of `ed25519_sc_reduce` sets to zero, in the order
    the stack-clearing pass stores them. -/
def scrZeroed : List Int :=
  [56, 48, 0, 128, 120, 80, 72, 168, 160, 152, 144, 136, 176, 184, 192, 200, 208, 216, 224, 232]

/-- `%rsp` cells tracked by `ed25519_sc_reduce` after part 7: the twenty the
    stack-clearing pass has set to zero, then the seven constants part 6 leaves
    at offsets the pass has not yet reached. -/
def scrCellsE : List ((String × Int) × AVal) :=
  scrZeroed.map (fun o => rc o (cst 0)) ++ scHead 88 96 104 112 ++ scMid

/-- `%rsp` cells tracked by `ed25519_sc_muladd` with both cells 40 and 32. -/
def scmCellsA : List ((String × Int) × AVal) :=
  scHead 104 112 120 128 ++ [rc 40 (cst 15), rc 32 (cst wMax)] ++ scMid ++ scmTail

/-- `%rsp` cells tracked by `ed25519_sc_muladd` without cell 40. -/
def scmCellsB : List ((String × Int) × AVal) :=
  scHead 104 112 120 128 ++ [rc 32 (cst wMax)] ++ scMid ++ scmTail

/-- `%rsp` cells tracked by `ed25519_sc_muladd` without cells 40 and 32. -/
def scmCellsC : List ((String × Int) × AVal) :=
  scHead 104 112 120 128 ++ scMid ++ scmTail

/-- The abstract states of `ed25519_sc_reduce` after parts 1 to 7. -/
def scrState : Nat → DState
  | 1 => ⟨true, [("%rbp", some (cst wMax)), ("%rdi", none), ("%rcx", none), ("%rsi", none),
      ("%r9", none), ("%r8", none), ("%r14", some (cst wEB)), ("%rdx", none),
      ("%r15", some (cst wEB))], scrCellsA⟩
  | 2 => ⟨true, [("%rsi", none), ("%rcx", none), ("%r15", some (cst wMax)), ("%rdi", none),
      ("%r14", some (cst wEB)), ("%rdx", none), ("%r8", none), ("%r9", none)], scrCellsA⟩
  | 3 => ⟨true, [("%rcx", none), ("%r9", none), ("%rdi", none), ("%rsi", none),
      ("%r14", some (cst wMax)), ("%rdx", none), ("%r15", some (cst wMax)), ("%r8", none)],
      scrCellsA⟩
  | 4 => ⟨true, [("%rsi", none), ("%rcx", none), ("%r9", none), ("%rdi", none),
      ("%r14", some (cst wMax)), ("%rdx", none), ("%r15", some (cst wMax)), ("%r8", none)],
      scrCellsA⟩
  | 5 => ⟨true, [("%rcx", none), ("%rdi", none), ("%rsi", none),
      ("%r14", some (cst 6346243789798364141)), ("%rdx", none),
      ("%r15", some (cst 6346243789798364141)), ("%r8", none), ("%r9", none)], scrCellsB⟩
  | 6 => ⟨true, [("%rsi", none), ("%rdi", none), ("%r8", none), ("%rcx", none), ("%r9", none),
      ("%r14", some (cst 0)), ("%rdx", none), ("%r15", some (cst 0))], scrCellsC⟩
  | _ => ⟨true, [("%rsi", none), ("%rdi", none), ("%rcx", none), ("%r9", none),
      ("%r8", some (cst wMax)), ("%rdx", none)], scrCellsE⟩

/-- The abstract states of `ed25519_sc_muladd` after parts 1 to 8. -/
def scmState : Nat → DState
  | 1 => ⟨true, [("%rdi", none), ("%rsi", none), ("%rcx", none), ("%rdx", none), ("%r9", none),
      ("%r8", none)], scmTail⟩
  | 2 => ⟨true, [("%r8", none), ("%rcx", none), ("%r14", some (cst 2379626136568277415)),
      ("%rdx", none), ("%r15", some (cst 2379626136568277415)), ("%rsi", none),
      ("%rdi", none), ("%r9", none)], scmCellsA⟩
  | 3 => ⟨true, [("%rsi", none), ("%rdi", none), ("%rcx", none),
      ("%r14", some (cst 2379626136568277415)), ("%rdx", none),
      ("%r15", some (cst 2379626136568277415)), ("%r8", none), ("%r9", none)], scmCellsA⟩
  | 4 => ⟨true, [("%rcx", none), ("%rdi", none), ("%rsi", none), ("%r14", some (cst wEB)),
      ("%rdx", none), ("%r15", some (cst wEB)), ("%r8", none), ("%r9", none)], scmCellsA⟩
  | 5 => ⟨true, [("%rcx", none), ("%rsi", none), ("%rdi", none), ("%r14", some (cst wEB)),
      ("%rdx", none), ("%r15", some (cst wEB)), ("%r8", none), ("%r9", none)], scmCellsA⟩
  | 6 => ⟨true, [("%rbx", some (cst 0)), ("%rdi", none), ("%rsi", none), ("%rcx", none),
      ("%r14", some (cst 0)), ("%rdx", none), ("%r15", some (cst 0)), ("%r9", none),
      ("%r8", none)], scmCellsB⟩
  | 7 => ⟨true, [("%rsi", none), ("%rcx", none), ("%rdi", none),
      ("%r14", some (cst 6346243789798364141)), ("%rdx", none), ("%r9", none), ("%r8", none)],
      scmCellsC⟩
  | _ => ⟨true, [("%r9", none), ("%rcx", none), ("%rsi", none), ("%r8", none), ("%rdi", none),
      ("%r14", some (cst 1152921504606846976)), ("%rdx", none),
      ("%r15", some (cst 1152921504606846976))], scmCellsC⟩

/-- The pointer cells of `ed25519_point_add`. -/
def paPtrs : List ((String × Int) × AVal) :=
  [rc 384 (.ptr "%rsi" 0), rc 392 (.ptr "%rdi" 0)]

/-- The abstract states of `ed25519_point_add` after parts 1 to 9. -/
def paState : Nat → DState
  | 1 => ⟨true, [("%r9", some (cst 0)), ("%rdi", none), ("%rsi", none), ("%rcx", none),
      ("%r8", none), ("%rbx", some (cst 0)), ("%rdx", none)], rc (-128) (cst 0) :: paPtrs⟩
  | 2 => ⟨true, [("%rcx", none), ("%r8", none), ("%rdx", none), ("%r9", none),
      ("%rax", some (cst 0)), ("%rdi", none), ("%rsi", none)], paPtrs⟩
  | 3 => ⟨true, [("%rdx", none), ("%rsi", none), ("%rcx", some (cst 0)),
      ("%rbx", some (cst 38)), ("%r9", none), ("%rdi", none), ("%r8", none),
      ("%r14", some (cst 2596001775599221991)), ("%r15", some (cst 2596001775599221991))],
      rc 168 (cst 2596001775599221991) :: paPtrs⟩
  | 4 => ⟨true, [("%r9", none), ("%r8", none), ("%rdx", none), ("%rbp", some (cst 0)),
      ("%rdi", none), ("%rcx", none), ("%rsi", none), ("%rbx", some (cst 0)),
      ("%rax", some (cst 38))], rc (-128) (cst 0) :: paPtrs⟩
  | 5 => ⟨true, [("%r9", none), ("%r8", none), ("%rdi", none), ("%rsi", none),
      ("%rcx", some (cst 0)), ("%rdx", none), ("%rbx", some (cst 38))], paPtrs⟩
  | 6 => ⟨true, [("%r8", none), ("%rsi", none), ("%rbx", some (cst 0)), ("%rcx", none),
      ("%rdx", none), ("%r9", none), ("%rdi", none)], paPtrs⟩
  | 7 => ⟨true, [("%rsi", none), ("%rdx", none), ("%r9", none), ("%rcx", none), ("%r8", none),
      ("%rdi", none)], rc (-128) (cst 0) :: paPtrs⟩
  | 8 => ⟨true, [("%rdx", none), ("%r8", none), ("%rax", some (cst 0)), ("%rcx", none),
      ("%rsi", none), ("%r9", none), ("%rdi", none)], paPtrs⟩
  | _ => ⟨true, [("%r9", some (cst 0)), ("%rsi", none), ("%rdi", none), ("%rcx", none),
      ("%r8", none), ("%rax", some (cst 0)), ("%rdx", none)], rc (-128) (cst 0) :: paPtrs⟩

/-! ### `ed25519_sc_reduce` -/

section ScReduce
open Ed25519ScReduceShipped

theorem scReduce_D_part01 : disciplinedFromD shippedBank {} ed25519ScReduceShippedPart01 = true ∧
    runD shippedBank {} ed25519ScReduceShippedPart01 = scrState 1 := by decide +kernel
theorem scReduce_D_part02 :
    disciplinedFromD shippedBank (scrState 1) ed25519ScReduceShippedPart02 = true ∧
      runD shippedBank (scrState 1) ed25519ScReduceShippedPart02 = scrState 2 := by
  decide +kernel
theorem scReduce_D_part03 :
    disciplinedFromD shippedBank (scrState 2) ed25519ScReduceShippedPart03 = true ∧
      runD shippedBank (scrState 2) ed25519ScReduceShippedPart03 = scrState 3 := by
  decide +kernel
theorem scReduce_D_part04 :
    disciplinedFromD shippedBank (scrState 3) ed25519ScReduceShippedPart04 = true ∧
      runD shippedBank (scrState 3) ed25519ScReduceShippedPart04 = scrState 4 := by
  decide +kernel
theorem scReduce_D_part05 :
    disciplinedFromD shippedBank (scrState 4) ed25519ScReduceShippedPart05 = true ∧
      runD shippedBank (scrState 4) ed25519ScReduceShippedPart05 = scrState 5 := by
  decide +kernel
theorem scReduce_D_part06 :
    disciplinedFromD shippedBank (scrState 5) ed25519ScReduceShippedPart06 = true ∧
      runD shippedBank (scrState 5) ed25519ScReduceShippedPart06 = scrState 6 := by
  decide +kernel
theorem scReduce_D_part07 :
    disciplinedFromD shippedBank (scrState 6) ed25519ScReduceShippedPart07 = true ∧
      runD shippedBank (scrState 6) ed25519ScReduceShippedPart07 = scrState 7 := by
  decide +kernel
theorem scReduce_D_part08 :
    disciplinedFromD shippedBank (scrState 7) ed25519ScReduceShippedPart08 = true := by
  decide +kernel

theorem ed25519ScReduce_disciplinedD :
    disciplinedD shippedBank ed25519ScReduceShippedBlock = true := by
  unfold disciplinedD ed25519ScReduceShippedBlock
  simp only [List.append_assoc]
  have h7 := disciplinedFromD_append (xs := ed25519ScReduceShippedPart07)
    (ys := ed25519ScReduceShippedPart08) scReduce_D_part07 scReduce_D_part08
  have h6 := disciplinedFromD_append (xs := ed25519ScReduceShippedPart06) scReduce_D_part06 h7
  have h5 := disciplinedFromD_append (xs := ed25519ScReduceShippedPart05) scReduce_D_part05 h6
  have h4 := disciplinedFromD_append (xs := ed25519ScReduceShippedPart04) scReduce_D_part04 h5
  have h3 := disciplinedFromD_append (xs := ed25519ScReduceShippedPart03) scReduce_D_part03 h4
  have h2 := disciplinedFromD_append (xs := ed25519ScReduceShippedPart02) scReduce_D_part02 h3
  exact disciplinedFromD_append (xs := ed25519ScReduceShippedPart01) scReduce_D_part01 h2

end ScReduce

/-! ### `ed25519_sc_muladd` -/

section ScMuladd
open Ed25519ScMuladdShipped

theorem scMuladd_D_part01 : disciplinedFromD shippedBank {} ed25519ScMuladdShippedPart01 = true ∧
    runD shippedBank {} ed25519ScMuladdShippedPart01 = scmState 1 := by decide +kernel
theorem scMuladd_D_part02 :
    disciplinedFromD shippedBank (scmState 1) ed25519ScMuladdShippedPart02 = true ∧
      runD shippedBank (scmState 1) ed25519ScMuladdShippedPart02 = scmState 2 := by
  decide +kernel
theorem scMuladd_D_part03 :
    disciplinedFromD shippedBank (scmState 2) ed25519ScMuladdShippedPart03 = true ∧
      runD shippedBank (scmState 2) ed25519ScMuladdShippedPart03 = scmState 3 := by
  decide +kernel
theorem scMuladd_D_part04 :
    disciplinedFromD shippedBank (scmState 3) ed25519ScMuladdShippedPart04 = true ∧
      runD shippedBank (scmState 3) ed25519ScMuladdShippedPart04 = scmState 4 := by
  decide +kernel
theorem scMuladd_D_part05 :
    disciplinedFromD shippedBank (scmState 4) ed25519ScMuladdShippedPart05 = true ∧
      runD shippedBank (scmState 4) ed25519ScMuladdShippedPart05 = scmState 5 := by
  decide +kernel
theorem scMuladd_D_part06 :
    disciplinedFromD shippedBank (scmState 5) ed25519ScMuladdShippedPart06 = true ∧
      runD shippedBank (scmState 5) ed25519ScMuladdShippedPart06 = scmState 6 := by
  decide +kernel
theorem scMuladd_D_part07 :
    disciplinedFromD shippedBank (scmState 6) ed25519ScMuladdShippedPart07 = true ∧
      runD shippedBank (scmState 6) ed25519ScMuladdShippedPart07 = scmState 7 := by
  decide +kernel
theorem scMuladd_D_part08 :
    disciplinedFromD shippedBank (scmState 7) ed25519ScMuladdShippedPart08 = true ∧
      runD shippedBank (scmState 7) ed25519ScMuladdShippedPart08 = scmState 8 := by
  decide +kernel
theorem scMuladd_D_part09 :
    disciplinedFromD shippedBank (scmState 8) ed25519ScMuladdShippedPart09 = true := by
  decide +kernel

theorem ed25519ScMuladd_disciplinedD :
    disciplinedD shippedBank ed25519ScMuladdShippedBlock = true := by
  unfold disciplinedD ed25519ScMuladdShippedBlock
  simp only [List.append_assoc]
  have h8 := disciplinedFromD_append (xs := ed25519ScMuladdShippedPart08)
    (ys := ed25519ScMuladdShippedPart09) scMuladd_D_part08 scMuladd_D_part09
  have h7 := disciplinedFromD_append (xs := ed25519ScMuladdShippedPart07) scMuladd_D_part07 h8
  have h6 := disciplinedFromD_append (xs := ed25519ScMuladdShippedPart06) scMuladd_D_part06 h7
  have h5 := disciplinedFromD_append (xs := ed25519ScMuladdShippedPart05) scMuladd_D_part05 h6
  have h4 := disciplinedFromD_append (xs := ed25519ScMuladdShippedPart04) scMuladd_D_part04 h5
  have h3 := disciplinedFromD_append (xs := ed25519ScMuladdShippedPart03) scMuladd_D_part03 h4
  have h2 := disciplinedFromD_append (xs := ed25519ScMuladdShippedPart02) scMuladd_D_part02 h3
  exact disciplinedFromD_append (xs := ed25519ScMuladdShippedPart01) scMuladd_D_part01 h2

end ScMuladd

/-! ### `ed25519_point_add` -/

section PointAdd
open Ed25519PointAddShipped

theorem pointAdd_D_part01 :
    disciplinedFromD shippedBank {} ed25519PointAddShippedPart01 = true ∧
      runD shippedBank {} ed25519PointAddShippedPart01 = paState 1 := by decide +kernel
theorem pointAdd_D_part02 :
    disciplinedFromD shippedBank (paState 1) ed25519PointAddShippedPart02 = true ∧
      runD shippedBank (paState 1) ed25519PointAddShippedPart02 = paState 2 := by
  decide +kernel
theorem pointAdd_D_part03 :
    disciplinedFromD shippedBank (paState 2) ed25519PointAddShippedPart03 = true ∧
      runD shippedBank (paState 2) ed25519PointAddShippedPart03 = paState 3 := by
  decide +kernel
theorem pointAdd_D_part04 :
    disciplinedFromD shippedBank (paState 3) ed25519PointAddShippedPart04 = true ∧
      runD shippedBank (paState 3) ed25519PointAddShippedPart04 = paState 4 := by
  decide +kernel
theorem pointAdd_D_part05 :
    disciplinedFromD shippedBank (paState 4) ed25519PointAddShippedPart05 = true ∧
      runD shippedBank (paState 4) ed25519PointAddShippedPart05 = paState 5 := by
  decide +kernel
theorem pointAdd_D_part06 :
    disciplinedFromD shippedBank (paState 5) ed25519PointAddShippedPart06 = true ∧
      runD shippedBank (paState 5) ed25519PointAddShippedPart06 = paState 6 := by
  decide +kernel
theorem pointAdd_D_part07 :
    disciplinedFromD shippedBank (paState 6) ed25519PointAddShippedPart07 = true ∧
      runD shippedBank (paState 6) ed25519PointAddShippedPart07 = paState 7 := by
  decide +kernel
theorem pointAdd_D_part08 :
    disciplinedFromD shippedBank (paState 7) ed25519PointAddShippedPart08 = true ∧
      runD shippedBank (paState 7) ed25519PointAddShippedPart08 = paState 8 := by
  decide +kernel
theorem pointAdd_D_part09 :
    disciplinedFromD shippedBank (paState 8) ed25519PointAddShippedPart09 = true ∧
      runD shippedBank (paState 8) ed25519PointAddShippedPart09 = paState 9 := by
  decide +kernel
theorem pointAdd_D_part10 :
    disciplinedFromD shippedBank (paState 9) ed25519PointAddShippedPart10 = true := by
  decide +kernel

theorem ed25519PointAdd_disciplinedD :
    disciplinedD shippedBank ed25519PointAddShippedBlock = true := by
  unfold disciplinedD ed25519PointAddShippedBlock
  simp only [List.append_assoc]
  have h9 := disciplinedFromD_append (xs := ed25519PointAddShippedPart09)
    (ys := ed25519PointAddShippedPart10) pointAdd_D_part09 pointAdd_D_part10
  have h8 := disciplinedFromD_append (xs := ed25519PointAddShippedPart08) pointAdd_D_part08 h9
  have h7 := disciplinedFromD_append (xs := ed25519PointAddShippedPart07) pointAdd_D_part07 h8
  have h6 := disciplinedFromD_append (xs := ed25519PointAddShippedPart06) pointAdd_D_part06 h7
  have h5 := disciplinedFromD_append (xs := ed25519PointAddShippedPart05) pointAdd_D_part05 h6
  have h4 := disciplinedFromD_append (xs := ed25519PointAddShippedPart04) pointAdd_D_part04 h5
  have h3 := disciplinedFromD_append (xs := ed25519PointAddShippedPart03) pointAdd_D_part03 h4
  have h2 := disciplinedFromD_append (xs := ed25519PointAddShippedPart02) pointAdd_D_part02 h3
  exact disciplinedFromD_append (xs := ed25519PointAddShippedPart01) pointAdd_D_part01 h2

end PointAdd

end Shipped

end CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
