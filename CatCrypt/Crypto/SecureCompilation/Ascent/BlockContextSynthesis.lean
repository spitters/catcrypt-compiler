/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.JInstrToArithBlock

/-!
# Synthesising the context of a decoded block

`JInstrToArithBlock.liftBlock_runBlock` takes the typing context `Γ`, the
register map `nm` and the scope map `find` as arguments: the caller states the
calling convention of the block it is lifting. This module derives the three
from the block itself, so the lift takes only the instruction list and the
output register name.

## The construction

* `entryNames` — the block's inputs: the register names an op reads before any
  op has written them, in order of first appearance. `entryNames_nodup` is what
  makes the scope map single-valued.
* `ctxOf` / `nmOf` / `findOf` — a context with one `reg 64` slot per entry name,
  the map reading the name back out of a De Bruijn position, and the lookup
  taking a name to its position. They are defined by structural recursion on the
  name list, so each one's `cons` case reduces to the head slot and the
  recursive call on the tail.
* `findOf_nmOf` — the scope map is a right inverse of the register map on the
  names it resolves, the `hfind` hypothesis of the lift.
* `decompileBlock` — parse and elaborate in one step, returning the recovered
  ops together with the `ArithBlock` over their synthesised context.
* `liftBlock_runBlock_synth` — the lift over the synthesised data.

`FreshFor nm (dstStream ops)` remains a hypothesis, as in `liftBlock_runBlock`.

@ascent-fixture theorems: synthDemo_parse, synthDemo_decompile_ops
`synthDemoBlock` is the witness that the synthesised typing context, register map
and scope map are the ones the block itself determines. It encodes no bytes that
ship.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-! ## 1. The entry names of a block -/

/-- Add a read name to the accumulated entry list, unless it is already an entry
    or has been written by an earlier op. -/
def pushEntry (acc wr : List String) (r : String) : List String :=
  if r ∈ acc ∨ r ∈ wr then acc else r :: acc

/-- `pushEntry` preserves duplicate-freeness: a name is prepended only when it is
    absent from the accumulator. -/
theorem pushEntry_nodup {acc wr : List String} {r : String} (h : acc.Nodup) :
    (pushEntry acc wr r).Nodup := by
  unfold pushEntry
  split
  · exact h
  · rename_i hmem
    exact List.nodup_cons.mpr ⟨fun hr => hmem (Or.inl hr), h⟩

/-- The entry-name scan: `acc` holds the entries found so far in reverse order,
    `wr` the destinations written so far. Each op contributes its two operand
    names and then records its destination as written. -/
def entryScan : List String → List String → List RawArith → List String
  | acc, _, [] => acc.reverse
  | acc, wr, o :: rest =>
      entryScan (pushEntry (pushEntry acc wr o.a) wr o.b) (o.dst :: wr) rest

/-- The scan preserves duplicate-freeness of the accumulator. -/
theorem entryScan_nodup : (ops : List RawArith) → (acc wr : List String) →
    acc.Nodup → (entryScan acc wr ops).Nodup
  | [], acc, _, h => by
      show acc.reverse.Nodup
      exact List.pairwise_reverse.mpr (h.imp Ne.symm)
  | o :: rest, acc, wr, h => by
      exact entryScan_nodup rest _ _ (pushEntry_nodup (pushEntry_nodup h))

/-- **The inputs of a block.** The register names read before being written, in
    order of first appearance. -/
def entryNames (ops : List RawArith) : List String := entryScan [] [] ops

/-- The entry names are pairwise distinct, so the synthesised scope map assigns
    each of them one De Bruijn position. -/
theorem entryNames_nodup (ops : List RawArith) : (entryNames ops).Nodup :=
  entryScan_nodup ops [] [] List.nodup_nil

/-! ## 2. The synthesised context, register map and scope map -/

/-- One `reg 64` slot per name, newest name at the head. -/
def ctxOf : List String → Ctxt jasminDialect
  | [] => []
  | _ :: rest => (.reg 64 : JasminTy) :: ctxOf rest

/-- `ctxOf` is the constant `reg 64` map over the name list. -/
theorem ctxOf_eq_map (names : List String) :
    ctxOf names = names.map (fun _ => (.reg 64 : JasminTy)) := by
  induction names with
  | nil => rfl
  | cons _ rest ih => simp only [ctxOf, List.map_cons, ih]

/-- The register map of a synthesised context: a De Bruijn position maps to the
    name sitting at that position of the name list. -/
def nmOf : (names : List String) → RegMapG (ctxOf names)
  | [] => fun v => nomatch v
  | n :: rest => fun v =>
      match v with
      | .here => n
      | .there w => nmOf rest w

/-- The scope map of a synthesised context: a name maps to the position of its
    first occurrence in the name list, and to `none` when it does not occur. -/
def findOf : (names : List String) → String → Option (Ctxt.Var (ctxOf names) (.reg 64))
  | [], _ => none
  | n :: rest, r =>
      if r = n then some .here else (findOf rest r).map Ctxt.Var.there

/-- The scope map of a non-empty name list is the head-extension of the scope map
    of its tail. -/
theorem findOf_cons (n : String) (rest : List String) :
    findOf (n :: rest) = extendFind (findOf rest) n := by
  funext r
  rfl

/-- The register map of a non-empty name list is the head-extension of the
    register map of its tail. -/
theorem nmOf_cons (n : String) (rest : List String)
    (v : Ctxt.Var (ctxOf (n :: rest)) (.reg 64)) :
    nmOf (n :: rest) v = (nmOf rest).extend n v := by
  match v with
  | .here => rfl
  | .there _ => rfl

/-! ## 3. Coherence of the synthesised maps -/

/-- **The synthesised maps are inverse.** A name the scope map resolves is the
    name the register map reads back out of the resolved position — the `hfind`
    hypothesis of `liftBlock_runBlock`. -/
theorem findOf_nmOf : (names : List String) → (hnd : names.Nodup) →
    (v : Ctxt.Var (ctxOf names) (.reg 64)) → (r : String) →
    findOf names r = some v → nmOf names v = r
  | [], _, v, _, _ => nomatch v
  | n :: rest, hnd, v, r, h => by
      rw [nmOf_cons n rest v]
      exact hfind_extend (nmOf rest) (findOf rest)
        (fun w r' hw => findOf_nmOf rest hnd.of_cons w r' hw) n v r h

/-! ## 4. The one-argument lift -/

/-- **Parse and elaborate a decoded block over its own context.** The recovered
    ops come from `parseBlock`; the context, register map and scope map come from
    `entryNames` of those ops. -/
def decompileBlock (blk : List (JInstr 64)) (out : String) :
    Option ((ops : List RawArith) × ArithBlock (ctxOf (entryNames ops))) :=
  match parseBlock blk with
  | none => none
  | some ops =>
      (elabOps (findOf (entryNames ops)) ops out).map (fun ab => ⟨ops, ab⟩)

/-- **The lift over the synthesised context.** A decoded block that parses and
    elaborates over the context read off its own entry names leaves, in the
    output register, the value the elaborated dialect program denotes. The
    instance of `liftBlock_runBlock` at `nm := nmOf (entryNames ops)`,
    `find := findOf (entryNames ops)`. -/
theorem liftBlock_runBlock_synth (blk : List (JInstr 64)) (ops : List RawArith)
    (out : String) (ab : ArithBlock (ctxOf (entryNames ops)))
    (hparse : parseBlock blk = some ops)
    (helab : elabOps (findOf (entryNames ops)) ops out = some ab)
    (s : JState 64) (V : Ctxt.Valuation (ctxOf (entryNames ops)))
    (hinterp : JStateInterpG (nmOf (entryNames ops)) V s)
    (hfresh : FreshFor (nmOf (entryNames ops)) (dstStream ops))
    (hmem : BlockMemOk ab (nmOf (entryNames ops)) (dstStream ops) V s :=
      by first | trivial | simp [BlockMemOk]) :
    (runBlock s blk).get (outReg ab (nmOf (entryNames ops)) (dstStream ops))
      = ab.toCom.denote V :=
  liftBlock_runBlock blk ops (nmOf (entryNames ops)) (findOf (entryNames ops))
    (findOf_nmOf (entryNames ops) (entryNames_nodup ops)) out ab hparse helab
    s V hinterp hfresh hmem

/-! ## 5. Non-vacuity — a two-op block decompiled from nothing but itself

The block `%rcx := %rax + %rbx ; %rdx := %rcx * %rax` computes `(x + y) * x`.
Its context, register map and scope map are all read off the instruction list.
-/

/-- The two-op machine block. -/
def synthDemoBlock : List (JInstr 64) :=
  lowerArith2 .add "%rax" "%rbx" "%rcx" ++ lowerArith2 .mul "%rcx" "%rax" "%rdx"

/-- The two ops the block parses to. -/
def synthDemoOps : List RawArith :=
  [⟨.add, "%rcx", "%rax", "%rbx"⟩, ⟨.mul, "%rdx", "%rcx", "%rax"⟩]

/-- The block parses to its two ops. -/
theorem synthDemo_parse : parseBlock synthDemoBlock = some synthDemoOps := rfl

/-- The entry names of the parsed ops are the two registers read before being
    written. `%rcx` is written by the first op, so the second op's read of it is
    not an input. -/
theorem synthDemo_entryNames : entryNames synthDemoOps = ["%rax", "%rbx"] := rfl

/-- The first input of the synthesised context. -/
abbrev synthX : Ctxt.Var (ctxOf (entryNames synthDemoOps)) (.reg 64) := .here

/-- The second input of the synthesised context. -/
abbrev synthY : Ctxt.Var (ctxOf (entryNames synthDemoOps)) (.reg 64) := .there .here

/-- The ops elaborate over the synthesised scope map, and the resulting dialect
    program denotes `mul (add x y) x` on a symbolic valuation. -/
theorem synthDemo_elab_denote (V : Ctxt.Valuation (ctxOf (entryNames synthDemoOps))) :
    (elabOps (findOf (entryNames synthDemoOps)) synthDemoOps "%rdx").map
        (fun ab => ab.toCom.denote V)
      = some (JasminBinOp.mul.apply
          (JasminBinOp.add.apply (synthX.lookup V) (synthY.lookup V))
          (synthX.lookup V)) := rfl

/-- The packaged decompilation of the block succeeds and recovers the two ops. -/
theorem synthDemo_decompile_ops :
    (decompileBlock synthDemoBlock "%rdx").map (fun p => p.1) = some synthDemoOps := rfl

end CatCrypt.Crypto.SecureCompilation.Ascent
