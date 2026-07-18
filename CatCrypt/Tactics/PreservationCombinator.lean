/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.BignumExec
import CatCrypt.Crypto.Jasmin.Examples.BignumStep
import CatCrypt.Crypto.Jasmin.Examples.Curve25519CryptoptPort

set_option autoImplicit false

/-!
# Preservation combinator: replace 95 per-chunk preservation lemmas with one

The chunked composition in `ChunkedComposition.lean` proves 95 individual
preservation lemmas (mem, a-reg, b-reg for ~30 chunks). Most are
near-identical boilerplate.

This file extracts the common structure into a single combinator:
`bignumExecPlus_preserves_reg` plus a decidable `writesTo` predicate.
With these, every per-chunk preservation lemma reduces to:

```
chunk_X_preserves_a := bignumExecPlus_preserves_reg chunk_X "a" (by decide)
```

(One line per chunk, vs ~15 LoC of boilerplate today.)

The cost: a single induction-over-instruction-list proof of the
combinator (~30 LoC) plus a per-opcode preservation lemma table
(~200 LoC, but reusable across all chunks AND any future asm).
-/

namespace CatCrypt.Crypto.Jasmin

/-! ## §1. `writesToReg`: which register an LVal targets. -/

def LVal.writesToReg : LVal → String → Bool
  | .Lvar v, r => v.var.vname = r
  | _, _ => false  -- Lnone (no-op flag) and Lmem (memory) don't write to registers

def InstrR.regWrites : InstrR → List String
  | .Cassgn (.Lvar v) _ _ _   => [v.var.vname]
  | .Cassgn _ _ _ _            => []
  | .Copn lvs _ _ _            => lvs.filterMap fun lv => match lv with
      | .Lvar v => some v.var.vname
      | _ => none
  | _ => []  -- Cif, Cfor, Cwhile, Ccall don't appear in straight-line asm

/-- A register name `r` is preserved by an instruction `i` iff `r` is not
    in the list of registers `i` writes to. Decidable for concrete inputs. -/
def InstrR.preservesReg (i : InstrR) (r : String) : Prop :=
  r ∉ i.regWrites

instance (i : InstrR) (r : String) : Decidable (i.preservesReg r) := by
  unfold InstrR.preservesReg
  infer_instance

/-! ## §1c. Recursive register-write predicate over CFG sub-bodies

`InstrR.regWrites` (above) returns `[]` for `Cif`/`Cfor`/`Cwhile`/`Ccall`,
which is **sound for `bignumExecPlus`** (the straight-line interpreter
returns `none` on those constructs, so the preservation claim is vacuous)
but **useless for `bignumExecFuel`** (which actually executes them).

`InstrR.regWritesRec` traverses sub-bodies. `Cfor v _ body` adds the
loop counter `v.var.vname`. `Ccall` contributes the `Lvar` names of its
result LVals: the void-return path (`lvs = []`) copies callee memory back
but leaves caller registers unchanged, while the non-void path binds each
callee result into the corresponding caller LVal via `bindResults`
(writing exactly the `Lvar` targets).

The `where listRegWrites` clause keeps termination structural via the
nested-list pattern (mirrors `PassFramework.fuelBoundInstr`). -/

def InstrR.regWritesRec : InstrR → List String
  | .Cassgn (.Lvar v) _ _ _   => [v.var.vname]
  | .Cassgn _ _ _ _            => []
  | .Copn lvs _ _ _            => lvs.filterMap fun lv => match lv with
      | .Lvar v => some v.var.vname
      | _ => none
  | .Cif _ ct ce               => listRegWrites ct ++ listRegWrites ce
  | .Cfor v _ body             => v.var.vname :: listRegWrites body
  | .Cwhile cb _ ca            => listRegWrites cb ++ listRegWrites ca
  | .Ccall _ lvs _ _           => lvs.filterMap fun lv => match lv with
      | .Lvar v => some v.var.vname
      | _ => none
where
  listRegWrites : List InstrR → List String
    | []      => []
    | i :: is => InstrR.regWritesRec i ++ listRegWrites is

/-- Register `r` is preserved by `i` (recursively, through CFG sub-bodies)
    iff `r` is not in `i.regWritesRec`. Decidable for concrete inputs. -/
def InstrR.preservesRegRec (i : InstrR) (r : String) : Prop :=
  r ∉ i.regWritesRec

instance (i : InstrR) (r : String) : Decidable (i.preservesRegRec r) := by
  unfold InstrR.preservesRegRec
  infer_instance

/-! ## §1b. Memory write predicate -/

def LVal.writesToMem : LVal → Bool
  | .Lmem _ _ _ => true
  | _           => false

def InstrR.hasMemWrite : InstrR → Bool
  | .Cassgn lv _ _ _ => lv.writesToMem
  | _                => false
  -- Copn, in the shapes `execInstr` actually handles, only ever uses
  -- `Lnone` / `Lvar` LVals (via the writeSubBundle / writeMulxBundle /
  -- writeAdxBundle / writeXorBundle / writeTestBundle helpers), so it
  -- never writes memory.  Cif / Cfor / Cwhile / Ccall return `none`
  -- from `execInstrPlus` so they cannot appear in any successful
  -- straight-line execution; the proof handles them as vacuous.

/-- An instruction `i` preserves memory iff it does no `Lmem` Cassgn.
    Decidable for concrete inputs. -/
def InstrR.preservesMem (i : InstrR) : Prop :=
  i.hasMemWrite = false

instance (i : InstrR) : Decidable i.preservesMem := by
  unfold InstrR.preservesMem
  infer_instance

/-! ## §1d. Recursive memory-write predicate over CFG sub-bodies

`InstrR.hasMemWrite` (above) returns `false` for `Cif`/`Cfor`/`Cwhile`/`Ccall`,
which is **sound for `bignumExecPlus`** (those constructs return `none` from
the straight-line interpreter, so the preservation claim is vacuous) but
**unsound for `bignumExecFuel`** which actually executes them. In particular,
the void-return `Ccall` arm of `bignumExecFuel` (lines 467-469 of
`BignumExec.lean`) sets `mem := calleeFinal.mem`, so an unconditional
`bignumExecFuel_preserves_mem` is false.

`InstrR.hasMemWriteRec` traverses CFG sub-bodies AND treats `Ccall` as a
memory-writer (it copies callee memory back). The `where listHasMemWrite`
clause keeps termination structural via the nested-list pattern (mirrors
§1c's `regWritesRec`). -/

def InstrR.hasMemWriteRec : InstrR → Bool
  | .Cassgn lv _ _ _   => lv.writesToMem
  | .Copn _ _ _ _      => false
  | .Cif _ ct ce       => listHasMemWrite ct || listHasMemWrite ce
  | .Cfor _ _ body     => listHasMemWrite body
  | .Cwhile cb _ ca    => listHasMemWrite cb || listHasMemWrite ca
  | .Ccall _ _ _ _     => true
where
  listHasMemWrite : List InstrR → Bool
    | []      => false
    | i :: is => InstrR.hasMemWriteRec i || listHasMemWrite is

/-- Memory is preserved by `i` (recursively, through CFG sub-bodies) iff
    `i.hasMemWriteRec = false`. Decidable for concrete inputs. -/
def InstrR.preservesMemRec (i : InstrR) : Prop :=
  i.hasMemWriteRec = false

instance (i : InstrR) : Decidable i.preservesMemRec := by
  unfold InstrR.preservesMemRec
  infer_instance

end CatCrypt.Crypto.Jasmin

namespace CatCrypt.Tactics.PreservationCombinator

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Curve25519CryptoptOps

/-! ## §2. The per-instruction preservation lemma.

For every instruction shape that `execInstrPlus` handles, if the
instruction doesn't write to register `r`, the post-state's `r` register
equals the pre-state's. Stating-form for now; the proof case-splits on
the instruction shape (matching the BignumStep simp lemmas). -/

/-! ### Per-bundle preservation helpers

Each `writeXBundle` helper writes a fixed list of LVals; if `r` is not among
those LVals' register names, the bundle preserves `s.regs r`. These mirror
the private helpers in `BignumHoare.lean` but are exposed here for use by
the main combinator. -/

theorem writeSubBundle_preserves
    (s s' : BignumState) (lvs : List LVal) (cf rv : BitVec 64) (r : String)
    (h : writeSubBundle s lvs cf rv = some s')
    (h_no : r ∉ lvs.filterMap (fun lv => match lv with
              | .Lvar v => some v.var.vname | _ => none)) :
    s'.regs r = s.regs r := by
  unfold writeSubBundle at h
  split at h
  next info1 ty1 cfV info2 ty2 info3 ty3 info4 ty4 rV =>
    simp at h; subst h
    simp at h_no
    obtain ⟨h_cf, h_r⟩ := h_no
    simp [setReg, h_cf, h_r]
  next => simp at h

theorem writeMulxBundle_preserves
    (s s' : BignumState) (lvs : List LVal) (hi lo : BitVec 64) (r : String)
    (h : writeMulxBundle s lvs hi lo = some s')
    (h_no : r ∉ lvs.filterMap (fun lv => match lv with
              | .Lvar v => some v.var.vname | _ => none)) :
    s'.regs r = s.regs r := by
  unfold writeMulxBundle at h
  split at h
  next hiV loV =>
    simp at h; subst h
    simp at h_no
    obtain ⟨h_hi, h_lo⟩ := h_no
    simp [setReg, h_hi, h_lo]
  next => simp at h

theorem writeAdxBundle_preserves
    (s s' : BignumState) (lvs : List LVal) (flag rv : BitVec 64) (r : String)
    (h : writeAdxBundle s lvs flag rv = some s')
    (h_no : r ∉ lvs.filterMap (fun lv => match lv with
              | .Lvar v => some v.var.vname | _ => none)) :
    s'.regs r = s.regs r := by
  unfold writeAdxBundle at h
  split at h
  next flagV rV =>
    simp at h; subst h
    simp at h_no
    obtain ⟨h_f, h_r⟩ := h_no
    simp [setReg, h_f, h_r]
  next => simp at h

theorem writeXorBundle_preserves
    (s s' : BignumState) (lvs : List LVal) (of cf rv : BitVec 64) (r : String)
    (h : writeXorBundle s lvs of cf rv = some s')
    (h_no : r ∉ lvs.filterMap (fun lv => match lv with
              | .Lvar v => some v.var.vname | _ => none)) :
    s'.regs r = s.regs r := by
  unfold writeXorBundle at h
  split at h
  next ofV cfV info3 ty3 info4 ty4 info5 ty5 rV =>
    simp at h; subst h
    simp at h_no
    obtain ⟨h_of, h_cf, h_r⟩ := h_no
    simp [setReg, h_of, h_cf, h_r]
  next info1 ty1 cfV info2 ty2 info3 ty3 info4 ty4 rV =>
    simp at h; subst h
    simp at h_no
    obtain ⟨h_cf, h_r⟩ := h_no
    simp [setReg, h_cf, h_r]
  next => simp at h

theorem writeDivBundle_preserves
    (s s' : BignumState) (lvs : List LVal) (q rv : BitVec 64) (r : String)
    (h : writeDivBundle s lvs q rv = some s')
    (h_no : r ∉ lvs.filterMap (fun lv => match lv with
              | .Lvar v => some v.var.vname | _ => none)) :
    s'.regs r = s.regs r := by
  unfold writeDivBundle at h
  split at h
  next info1 ty1 info2 ty2 info3 ty3 info4 ty4 info5 ty5 qV rV =>
    simp at h; subst h
    simp at h_no
    obtain ⟨h_q, h_r⟩ := h_no
    simp [setReg, h_q, h_r]
  next => simp at h

theorem writeShiftBundle_preserves
    (s s' : BignumState) (lvs : List LVal) (rv : BitVec 64) (r : String)
    (h : writeShiftBundle s lvs rv = some s')
    (h_no : r ∉ lvs.filterMap (fun lv => match lv with
              | .Lvar v => some v.var.vname | _ => none)) :
    s'.regs r = s.regs r := by
  unfold writeShiftBundle at h
  split at h
  next info1 ty1 info2 ty2 info3 ty3 info4 ty4 info5 ty5 rV =>
    simp at h; subst h
    simp at h_no
    simp [setReg, h_no]
  next info1 ty1 cfV info2 ty2 info3 ty3 info4 ty4 rV =>
    simp at h; subst h
    simp at h_no
    obtain ⟨h_cf, h_r⟩ := h_no
    simp [setReg, h_cf, h_r]
  next rV =>
    simp at h; subst h
    simp at h_no
    simp [setReg, h_no]
  next => simp at h

private theorem writeSingleVar_preserves
    (s s' : BignumState) (lvs : List LVal) (rv : BitVec 64) (r : String)
    (h : writeSingleVar s lvs rv = some s')
    (h_no : r ∉ lvs.filterMap (fun lv => match lv with
              | .Lvar v => some v.var.vname | _ => none)) :
    s'.regs r = s.regs r := by
  unfold writeSingleVar at h
  split at h
  next vV =>
    simp at h; subst h
    simp at h_no
    simp [setReg', setReg, h_no]
  next => simp at h

private theorem writeTestBundle_preserves
    (s s' : BignumState) (lvs : List LVal) (of cf : BitVec 64) (r : String)
    (h : writeTestBundle s lvs of cf = some s')
    (h_no : r ∉ lvs.filterMap (fun lv => match lv with
              | .Lvar v => some v.var.vname | _ => none)) :
    s'.regs r = s.regs r := by
  unfold writeTestBundle at h
  split at h
  next ofV cfV =>
    simp at h; subst h
    simp at h_no
    obtain ⟨h_of, h_cf⟩ := h_no
    simp [setReg', setReg, h_of, h_cf]
  next => simp at h

/-! ### Helper: form lemma for `execInstr` on `Cassgn (Lvar v) _ _ e`

For ALL PExpr shapes, when `execInstr s (.Cassgn (.Lvar v) tag ty e) = some s'`,
we have `s' = setReg s v.var.vname w` for some `w`. -/

private theorem execInstr_Cassgn_Lvar_form
    (s s' : BignumState) (v : VarI) (tag : AssgnTag) (ty : SType) (e : PExpr)
    (h : execInstr s (.Cassgn (.Lvar v) tag ty e) = some s') :
    ∃ w, s' = setReg s v.var.vname w := by
  rw [show execInstr s (.Cassgn (.Lvar v) tag ty e) =
        (evalPExpr s e).bind (fun w => some (setReg s v.var.vname w))
        from rfl] at h
  cases h_w : evalPExpr s e with
  | none => rw [h_w] at h; simp at h
  | some w =>
    rw [h_w] at h; simp at h
    exact ⟨w, h.symm⟩

/-! ### Helper: `execInstr` on `Cassgn (Lmem .U64 base off) _ _ e` preserves regs -/

private theorem execInstr_Cassgn_Lmem_U64_preserves_regs
    (s s' : BignumState) (base : VarI) (off : PExpr)
    (tag : AssgnTag) (ty : SType) (e : PExpr) (r : String)
    (h : execInstr s (.Cassgn (.Lmem .U64 base off) tag ty e) = some s') :
    s'.regs r = s.regs r := by
  rw [show execInstr s (.Cassgn (.Lmem .U64 base off) tag ty e) =
        (evalPExpr s e).bind
          (fun (w : BitVec 64) => (resolveAddr s base off).bind
            (fun addr => some (storeMem s addr (UInt64.ofNat w.toNat))))
        from rfl] at h
  cases h_w : evalPExpr s e with
  | none => rw [h_w] at h; simp at h
  | some w =>
    rw [h_w] at h; simp at h
    cases h_a : resolveAddr s base off with
    | none => rw [h_a] at h; simp at h
    | some addr =>
      rw [h_a] at h; simp at h
      subst h
      rfl

/-! ### Helper: `execInstr` returns none for non-handled InstrR shapes. -/

private theorem execInstr_Cif_eq_none (s : BignumState)
    (cond : PExpr) (cthen celse : List InstrR) :
    execInstr s (.Cif cond cthen celse) = none := rfl

private theorem execInstr_Cfor_eq_none (s : BignumState)
    (vi : VarI) (range : Range) (body : List InstrR) :
    execInstr s (.Cfor vi range body) = none := rfl

private theorem execInstr_Cwhile_eq_none (s : BignumState)
    (cb : List InstrR) (cond : PExpr) (ca : List InstrR) :
    execInstr s (.Cwhile cb cond ca) = none := rfl

private theorem execInstr_Ccall_eq_none (s : BignumState)
    (ii : InlineInfo) (lvs : List LVal) (fn : FunName) (args : List PExpr) :
    execInstr s (.Ccall ii lvs fn args) = none := rfl

private theorem execInstr_Cassgn_Lnone_eq_none (s : BignumState)
    (info : VarInfo) (lty : SType) (tag : AssgnTag) (ty : SType) (e : PExpr) :
    execInstr s (.Cassgn (.Lnone info lty) tag ty e) = none := rfl

private theorem execInstr_Cassgn_Laset_eq_none (s : BignumState)
    (aa : ArrAccess) (ws : WSize) (x : VarI) (idx : PExpr)
    (tag : AssgnTag) (ty : SType) (e : PExpr) :
    execInstr s (.Cassgn (.Laset aa ws x idx) tag ty e) = none := rfl

private theorem execInstr_Cassgn_Lasub_eq_none (s : BignumState)
    (aa : ArrAccess) (ws : WSize) (len : Nat) (x : VarI) (idx : PExpr)
    (tag : AssgnTag) (ty : SType) (e : PExpr) :
    execInstr s (.Cassgn (.Lasub aa ws len x idx) tag ty e) = none := rfl

/-! ### `execInstrPlus` reduces to `execInstr` outside the special arms. -/

private theorem execInstrPlus_Cif_eq (s : BignumState)
    (cond : PExpr) (cthen celse : List InstrR) :
    execInstrPlus s (.Cif cond cthen celse) =
    execInstr s (.Cif cond cthen celse) := rfl

private theorem execInstrPlus_Cfor_eq (s : BignumState)
    (vi : VarI) (range : Range) (body : List InstrR) :
    execInstrPlus s (.Cfor vi range body) =
    execInstr s (.Cfor vi range body) := rfl

private theorem execInstrPlus_Cwhile_eq (s : BignumState)
    (cb : List InstrR) (cond : PExpr) (ca : List InstrR) :
    execInstrPlus s (.Cwhile cb cond ca) =
    execInstr s (.Cwhile cb cond ca) := rfl

private theorem execInstrPlus_Ccall_eq (s : BignumState)
    (ii : InlineInfo) (lvs : List LVal) (fn : FunName) (args : List PExpr) :
    execInstrPlus s (.Ccall ii lvs fn args) =
    execInstr s (.Ccall ii lvs fn args) := rfl

private theorem execInstrPlus_Cassgn_Lnone_eq (s : BignumState)
    (info : VarInfo) (lty : SType) (tag : AssgnTag) (ty : SType) (e : PExpr) :
    execInstrPlus s (.Cassgn (.Lnone info lty) tag ty e) =
    execInstr s (.Cassgn (.Lnone info lty) tag ty e) := rfl

private theorem execInstrPlus_Cassgn_Laset_eq (s : BignumState)
    (aa : ArrAccess) (ws : WSize) (x : VarI) (idx : PExpr)
    (tag : AssgnTag) (ty : SType) (e : PExpr) :
    execInstrPlus s (.Cassgn (.Laset aa ws x idx) tag ty e) =
    execInstr s (.Cassgn (.Laset aa ws x idx) tag ty e) := rfl

private theorem execInstrPlus_Cassgn_Lasub_eq (s : BignumState)
    (aa : ArrAccess) (ws : WSize) (len : Nat) (x : VarI) (idx : PExpr)
    (tag : AssgnTag) (ty : SType) (e : PExpr) :
    execInstrPlus s (.Cassgn (.Lasub aa ws len x idx) tag ty e) =
    execInstr s (.Cassgn (.Lasub aa ws len x idx) tag ty e) := rfl

private theorem execInstrPlus_Cassgn_Lmem_eq (s : BignumState)
    (ws : WSize) (base : VarI) (off : PExpr)
    (tag : AssgnTag) (ty : SType) (e : PExpr) :
    execInstrPlus s (.Cassgn (.Lmem ws base off) tag ty e) =
    execInstr s (.Cassgn (.Lmem ws base off) tag ty e) := rfl

private theorem execInstr_Cassgn_Lmem_nonU64_eq_none (s : BignumState)
    (ws : WSize) (base : VarI) (off : PExpr)
    (tag : AssgnTag) (ty : SType) (e : PExpr)
    (h : ws ≠ .U64) (h32 : ws ≠ .U32) (h8 : ws ≠ .U8) :
    execInstr s (.Cassgn (.Lmem ws base off) tag ty e) = none := by
  cases ws with
  | U64 => exact absurd rfl h
  | U8 => exact absurd rfl h8
  | U16 => rfl
  | U32 => exact absurd rfl h32
  | U128 => rfl
  | U256 => rfl
  | U512 => rfl

/-- **(U32, additive)** A 32-bit memory store (`.Lmem .U32`) preserves all
    registers — it touches only `s.mem` (via `storeMem32`).  Mirror of
    `execInstr_Cassgn_Lmem_U64_preserves_regs` for the new U32 store arm
    of `execInstr` (added to `BignumExec` alongside U32 interpretation). -/
private theorem execInstr_Cassgn_Lmem_U32_preserves_regs
    (s s' : BignumState) (base : VarI) (off : PExpr)
    (tag : AssgnTag) (ty : SType) (e : PExpr) (r : String)
    (h : execInstr s (.Cassgn (.Lmem .U32 base off) tag ty e) = some s') :
    s'.regs r = s.regs r := by
  rw [show execInstr s (.Cassgn (.Lmem .U32 base off) tag ty e) =
        (evalPExpr s e).bind
          (fun (w : BitVec 64) => (resolveAddr s base off).bind
            (fun addr => some (storeMem32 s addr (UInt64.ofNat w.toNat))))
        from rfl] at h
  cases h_w : evalPExpr s e with
  | none => rw [h_w] at h; simp at h
  | some w =>
    rw [h_w] at h; simp at h
    cases h_a : resolveAddr s base off with
    | none => rw [h_a] at h; simp at h
    | some addr =>
      rw [h_a] at h; simp at h
      subst h
      rfl

/-- **(U8, additive)** A 1-byte memory store (`.Lmem .U8`) preserves all
    registers — it touches only `s.mem` (via `storeMem8`).  Mirror of
    `execInstr_Cassgn_Lmem_U32_preserves_regs` for the byte-store arm
    of `execInstr`. -/
private theorem execInstr_Cassgn_Lmem_U8_preserves_regs
    (s s' : BignumState) (base : VarI) (off : PExpr)
    (tag : AssgnTag) (ty : SType) (e : PExpr) (r : String)
    (h : execInstr s (.Cassgn (.Lmem .U8 base off) tag ty e) = some s') :
    s'.regs r = s.regs r := by
  rw [show execInstr s (.Cassgn (.Lmem .U8 base off) tag ty e) =
        (evalPExpr s e).bind
          (fun (w : BitVec 64) => (resolveAddr s base off).bind
            (fun addr => some (storeMem8 s addr (UInt8.ofNat (w.toNat % 256)))))
        from rfl] at h
  cases h_w : evalPExpr s e with
  | none => rw [h_w] at h; simp at h
  | some w =>
    rw [h_w] at h; simp at h
    cases h_a : resolveAddr s base off with
    | none => rw [h_a] at h; simp at h
    | some addr =>
      rw [h_a] at h; simp at h
      subst h
      rfl

/-! ### Reduction lemma: `execInstrPlus` on `Copn _ _ (Oasm o) _` reduces to
    its inner match. -/

private theorem execInstrPlus_Copn_Oasm_reduce (s : BignumState)
    (lvs : List LVal) (tag : AssgnTag) (o : AsmOp) (args : List PExpr) :
    execInstrPlus s (.Copn lvs tag (.Oasm o) args) =
    (match o.name, args with
     | "BZHI_64", [ea, eb] => do
         let a ← evalPExpr s ea
         let c ← evalPExpr s eb
         writeSingleVar s lvs (bzhi a c)
     | "SHRD_64_imm", [ea, eb, .Pconst k] => do
         let dst ← evalPExpr s ea
         let src ← evalPExpr s eb
         writeSingleVar s lvs (shrdImm dst src k.toNat)
     | "IMUL_imm_64", [ea, .Pconst k] => do
         let a ← evalPExpr s ea
         match lvs with
         | [.Lnone _ _, .Lnone _ _, .Lnone _ _, .Lnone _ _,
            .Lnone _ _, .Lvar rV] =>
           some (setReg' s rV.var.vname (imulImm a k))
         | _ => none
     | "SHLX_64", [ea, eb] => do
         let a ← evalPExpr s ea
         let c ← evalPExpr s eb
         writeSingleVar s lvs (shlx a c)
     | "AND_64", [ea, eb] => do
         let a ← evalPExpr s ea
         let b ← evalPExpr s eb
         match lvs with
         | [.Lnone _ _, .Lnone _ _, .Lnone _ _, .Lnone _ _,
            .Lnone _ _, .Lvar rV] =>
           some (setReg' s rV.var.vname (and64 a b))
         | _ => none
     | "TEST_64", [ea, eb] => do
         let a ← evalPExpr s ea
         let b ← evalPExpr s eb
         let (of, cf) := test64 a b
         writeTestBundle s lvs of cf
     | _, _ =>
         execInstr s (.Copn lvs .AT_none (.Oasm o) args)) := rfl

private theorem execInstr_Copn_Oasm_reduce (s : BignumState)
    (lvs : List LVal) (tag : AssgnTag) (o : AsmOp) (args : List PExpr) :
    execInstr s (.Copn lvs tag (.Oasm o) args) =
    (match o.name, args with
     | "SUB_64", [ea, eb] => do
         let a ← evalPExpr s ea
         let b ← evalPExpr s eb
         let (cf, r) := subBorrow a b
         writeSubBundle s lvs cf r
     | "SBB_64", [ea, eb, ec] => do
         let a ← evalPExpr s ea
         let b ← evalPExpr s eb
         let c ← evalPExpr s ec
         let (cf, r) := subBorrowIn a b c
         writeSubBundle s lvs cf r
     | "ADD_64", [ea, eb] => do
         let a ← evalPExpr s ea
         let b ← evalPExpr s eb
         let (cf, r) := addCarry a b
         writeSubBundle s lvs cf r
     | "ADC_64", [ea, eb, ec] => do
         let a ← evalPExpr s ea
         let b ← evalPExpr s eb
         let c ← evalPExpr s ec
         let (cf, r) := addCarryIn a b c
         writeSubBundle s lvs cf r
     | "MULX", [ea, eb] => do
         let a ← evalPExpr s ea
         let b ← evalPExpr s eb
         let (hi, lo) := mulx a b
         writeMulxBundle s lvs hi lo
     | "DIV_64", [eh, el, ed] => do
         let hi ← evalPExpr s eh
         let lo ← evalPExpr s el
         let d ← evalPExpr s ed
         let (q, r) := divrem64 hi lo d
         writeDivBundle s lvs q r
     | "ADCX", [ea, eb, ec] => do
         let a ← evalPExpr s ea
         let b ← evalPExpr s eb
         let c ← evalPExpr s ec
         let (cf, r) := addCarryIn a b c
         writeAdxBundle s lvs cf r
     | "ADOX", [ea, eb, ec] => do
         let a ← evalPExpr s ea
         let b ← evalPExpr s eb
         let c ← evalPExpr s ec
         let (of, r) := addCarryIn a b c
         writeAdxBundle s lvs of r
     | "XOR_64", [ea, eb] => do
         let a ← evalPExpr s ea
         let b ← evalPExpr s eb
         let r : BitVec 64 := a ^^^ b
         writeXorBundle s lvs 0 0 r
     | "SHL_64", [ea, ek] => do
         let a ← evalPExpr s ea
         let k ← evalPExpr s ek
         writeShiftBundle s lvs (shl64 a k)
     | "SHR_64", [ea, ek] => do
         let a ← evalPExpr s ea
         let k ← evalPExpr s ek
         writeShiftBundle s lvs (shr64 a k)
     | "SHLD_64", [edst, esrc, ek] => do
         let dst ← evalPExpr s edst
         let src ← evalPExpr s esrc
         let k ← evalPExpr s ek
         writeShiftBundle s lvs (shld64 dst src k)
     | "SHRD_64", [edst, esrc, ek] => do
         let dst ← evalPExpr s edst
         let src ← evalPExpr s esrc
         let k ← evalPExpr s ek
         writeShiftBundle s lvs (shrd64 dst src k)
     | "SUB_32", [ea, eb] => do
         let a ← evalPExpr s ea
         let b ← evalPExpr s eb
         let (cf, r) := subBorrow32 a b
         writeSubBundle s lvs cf r
     | "ADD_32", [ea, eb] => do
         let a ← evalPExpr s ea
         let b ← evalPExpr s eb
         let (cf, r) := addCarry32 a b
         writeSubBundle s lvs cf r
     | "ADC_32", [ea, eb, ec] => do
         let a ← evalPExpr s ea
         let b ← evalPExpr s eb
         let c ← evalPExpr s ec
         let (cf, r) := addCarryIn32 a b c
         writeSubBundle s lvs cf r
     | "SBB_32", [ea, eb, ec] => do
         let a ← evalPExpr s ea
         let b ← evalPExpr s eb
         let c ← evalPExpr s ec
         let (bf, r) := subBorrowIn32 a b c
         writeSubBundle s lvs bf r
     | "MULX_32", [ea, eb] => do
         let a ← evalPExpr s ea
         let b ← evalPExpr s eb
         let (hi, lo) := mulx32 a b
         writeMulxBundle s lvs hi lo
     | _, _ => none) := rfl

/-! ### Form lemma for `execInstrPlus` on `Cassgn (Lvar v) _ _ e`

For all `e`, when `execInstrPlus` succeeds, the result has the form
`setReg s v.var.vname w` for some `w`. -/

private theorem execInstrPlus_Cassgn_Lvar_form
    (s s' : BignumState) (v : VarI) (tag : AssgnTag) (ty : SType) (e : PExpr)
    (h : execInstrPlus s (.Cassgn (.Lvar v) tag ty e) = some s') :
    ∃ w, s' = setReg s v.var.vname w := by
  cases e with
  | Papp2 op a b =>
    rw [show execInstrPlus s (.Cassgn (.Lvar v) tag ty (.Papp2 op a b)) =
          (match evalCassgnPlus s (.Papp2 op a b) with
           | some w => some (setReg' s v.var.vname w)
           | none => execInstr s
               (.Cassgn (.Lvar v) .AT_none (.sword .U64) (.Papp2 op a b)))
          from rfl] at h
    cases h_p : evalCassgnPlus s (.Papp2 op a b) with
    | some w =>
      rw [h_p] at h
      simp only [Option.some.injEq] at h
      exact ⟨w, by unfold setReg' at h; exact h.symm⟩
    | none =>
      rw [h_p] at h
      exact execInstr_Cassgn_Lvar_form _ _ _ _ _ _ h
  | Pconst k =>
    have heq : execInstrPlus s (.Cassgn (.Lvar v) tag ty (.Pconst k)) =
               execInstr s (.Cassgn (.Lvar v) tag ty (.Pconst k)) := rfl
    rw [heq] at h
    exact execInstr_Cassgn_Lvar_form _ _ _ _ _ _ h
  | Pbool b =>
    have heq : execInstrPlus s (.Cassgn (.Lvar v) tag ty (.Pbool b)) =
               execInstr s (.Cassgn (.Lvar v) tag ty (.Pbool b)) := rfl
    rw [heq] at h
    exact execInstr_Cassgn_Lvar_form _ _ _ _ _ _ h
  | Parr_init n =>
    have heq : execInstrPlus s (.Cassgn (.Lvar v) tag ty (.Parr_init n)) =
               execInstr s (.Cassgn (.Lvar v) tag ty (.Parr_init n)) := rfl
    rw [heq] at h
    exact execInstr_Cassgn_Lvar_form _ _ _ _ _ _ h
  | Pvar gv =>
    have heq : execInstrPlus s (.Cassgn (.Lvar v) tag ty (.Pvar gv)) =
               execInstr s (.Cassgn (.Lvar v) tag ty (.Pvar gv)) := rfl
    rw [heq] at h
    exact execInstr_Cassgn_Lvar_form _ _ _ _ _ _ h
  | Pget aa ws gx idx =>
    have heq : execInstrPlus s (.Cassgn (.Lvar v) tag ty (.Pget aa ws gx idx)) =
               execInstr s (.Cassgn (.Lvar v) tag ty (.Pget aa ws gx idx)) := rfl
    rw [heq] at h
    exact execInstr_Cassgn_Lvar_form _ _ _ _ _ _ h
  | Psub aa ws len gx idx =>
    have heq : execInstrPlus s (.Cassgn (.Lvar v) tag ty (.Psub aa ws len gx idx)) =
               execInstr s (.Cassgn (.Lvar v) tag ty (.Psub aa ws len gx idx)) := rfl
    rw [heq] at h
    exact execInstr_Cassgn_Lvar_form _ _ _ _ _ _ h
  | Pload ws base off =>
    have heq : execInstrPlus s (.Cassgn (.Lvar v) tag ty (.Pload ws base off)) =
               execInstr s (.Cassgn (.Lvar v) tag ty (.Pload ws base off)) := rfl
    rw [heq] at h
    exact execInstr_Cassgn_Lvar_form _ _ _ _ _ _ h
  | Papp1 op a =>
    have heq : execInstrPlus s (.Cassgn (.Lvar v) tag ty (.Papp1 op a)) =
               execInstr s (.Cassgn (.Lvar v) tag ty (.Papp1 op a)) := rfl
    rw [heq] at h
    exact execInstr_Cassgn_Lvar_form _ _ _ _ _ _ h
  | PappN op es =>
    have heq : execInstrPlus s (.Cassgn (.Lvar v) tag ty (.PappN op es)) =
               execInstr s (.Cassgn (.Lvar v) tag ty (.PappN op es)) := rfl
    rw [heq] at h
    exact execInstr_Cassgn_Lvar_form _ _ _ _ _ _ h
  | Pif tyi cond et ef =>
    have heq : execInstrPlus s (.Cassgn (.Lvar v) tag ty (.Pif tyi cond et ef)) =
               execInstr s (.Cassgn (.Lvar v) tag ty (.Pif tyi cond et ef)) := rfl
    rw [heq] at h
    exact execInstr_Cassgn_Lvar_form _ _ _ _ _ _ h

theorem execInstrPlus_preserves_reg (i : InstrR) (s s' : BignumState) (r : String)
    (h_pres : i.preservesReg r)
    (h_exec : execInstrPlus s i = some s') :
    s'.regs r = s.regs r := by
  unfold InstrR.preservesReg at h_pres
  cases i with
  | Cif cond ct ce =>
    rw [execInstrPlus_Cif_eq, execInstr_Cif_eq_none] at h_exec
    cases h_exec
  | Cfor vi range body =>
    rw [execInstrPlus_Cfor_eq, execInstr_Cfor_eq_none] at h_exec
    cases h_exec
  | Cwhile cb cond ca =>
    rw [execInstrPlus_Cwhile_eq, execInstr_Cwhile_eq_none] at h_exec
    cases h_exec
  | Ccall ii lvs fn args =>
    rw [execInstrPlus_Ccall_eq, execInstr_Ccall_eq_none] at h_exec
    cases h_exec
  | Cassgn lv tag ty e =>
    cases lv with
    | Lnone info lty =>
      rw [execInstrPlus_Cassgn_Lnone_eq, execInstr_Cassgn_Lnone_eq_none] at h_exec
      cases h_exec
    | Laset aa ws x idx =>
      rw [execInstrPlus_Cassgn_Laset_eq, execInstr_Cassgn_Laset_eq_none] at h_exec
      cases h_exec
    | Lasub aa ws len x idx =>
      rw [execInstrPlus_Cassgn_Lasub_eq, execInstr_Cassgn_Lasub_eq_none] at h_exec
      cases h_exec
    | Lvar v =>
      simp only [InstrR.regWrites, List.mem_singleton] at h_pres
      obtain ⟨w, rfl⟩ := execInstrPlus_Cassgn_Lvar_form _ _ _ _ _ _ h_exec
      show (if r = v.var.vname then w else s.regs r) = s.regs r
      exact if_neg h_pres
    | Lmem ws base off =>
      cases ws with
      | U64 =>
        rw [execInstrPlus_Cassgn_Lmem_eq] at h_exec
        exact execInstr_Cassgn_Lmem_U64_preserves_regs _ _ _ _ _ _ _ _ h_exec
      | U8 =>
        -- (U8, additive) U8 byte store now succeeds; it preserves regs.
        rw [execInstrPlus_Cassgn_Lmem_eq] at h_exec
        exact execInstr_Cassgn_Lmem_U8_preserves_regs _ _ _ _ _ _ _ _ h_exec
      | U16 =>
        rw [execInstrPlus_Cassgn_Lmem_eq,
            execInstr_Cassgn_Lmem_nonU64_eq_none _ _ _ _ _ _ _
              (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)]
            at h_exec
        cases h_exec
      | U32 =>
        -- (U32, additive) U32 memory store now succeeds; it preserves regs.
        rw [execInstrPlus_Cassgn_Lmem_eq] at h_exec
        exact execInstr_Cassgn_Lmem_U32_preserves_regs _ _ _ _ _ _ _ _ h_exec
      | U128 =>
        rw [execInstrPlus_Cassgn_Lmem_eq,
            execInstr_Cassgn_Lmem_nonU64_eq_none _ _ _ _ _ _ _
              (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)]
            at h_exec
        cases h_exec
      | U256 =>
        rw [execInstrPlus_Cassgn_Lmem_eq,
            execInstr_Cassgn_Lmem_nonU64_eq_none _ _ _ _ _ _ _
              (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)]
            at h_exec
        cases h_exec
      | U512 =>
        rw [execInstrPlus_Cassgn_Lmem_eq,
            execInstr_Cassgn_Lmem_nonU64_eq_none _ _ _ _ _ _ _
              (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)]
            at h_exec
        cases h_exec
  | Copn lvs tag op args =>
    simp only [InstrR.regWrites] at h_pres
    cases op with
    | Oasm o =>
      rw [execInstrPlus_Copn_Oasm_reduce] at h_exec
      split at h_exec
      · -- BZHI_64: o.name = "BZHI_64", args = [ea, eb]
        rename_i ea eb _h
        rcases h_a : evalPExpr s ea with _ | a
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_c : evalPExpr s eb with _ | c
          · rw [h_c] at h_exec; simp at h_exec
          · rw [h_c] at h_exec; simp at h_exec
            exact writeSingleVar_preserves _ _ _ _ _ h_exec h_pres
      · -- SHRD_64_imm
        rename_i ea eb k _h
        rcases h_d : evalPExpr s ea with _ | d
        · rw [h_d] at h_exec; simp at h_exec
        · rw [h_d] at h_exec; simp at h_exec
          rcases h_src : evalPExpr s eb with _ | src
          · rw [h_src] at h_exec; simp at h_exec
          · rw [h_src] at h_exec; simp at h_exec
            exact writeSingleVar_preserves _ _ _ _ _ h_exec h_pres
      · -- IMUL_imm_64
        rename_i ea k _h
        rcases h_a : evalPExpr s ea with _ | a
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          split at h_exec
          next info1 ty1 info2 ty2 info3 ty3 info4 ty4 info5 ty5 rV =>
            simp at h_exec; subst h_exec
            simp at h_pres
            simp [setReg', setReg, h_pres]
          next => simp at h_exec
      · -- SHLX_64
        rename_i ea eb _h
        rcases h_a : evalPExpr s ea with _ | a
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_c : evalPExpr s eb with _ | c
          · rw [h_c] at h_exec; simp at h_exec
          · rw [h_c] at h_exec; simp at h_exec
            exact writeSingleVar_preserves _ _ _ _ _ h_exec h_pres
      · -- AND_64
        rename_i ea eb _h
        rcases h_a : evalPExpr s ea with _ | a
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_b : evalPExpr s eb with _ | b
          · rw [h_b] at h_exec; simp at h_exec
          · rw [h_b] at h_exec; simp at h_exec
            split at h_exec
            next info1 ty1 info2 ty2 info3 ty3 info4 ty4 info5 ty5 rV =>
              simp at h_exec; subst h_exec
              simp at h_pres
              simp [setReg', setReg, h_pres]
            next => simp at h_exec
      · -- TEST_64
        rename_i ea eb _h
        rcases h_a : evalPExpr s ea with _ | a
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_b : evalPExpr s eb with _ | b
          · rw [h_b] at h_exec; simp at h_exec
          · rw [h_b] at h_exec; simp at h_exec
            exact writeTestBundle_preserves _ _ _ _ _ _ h_exec h_pres
      · -- Fall through to base execInstr
        rw [execInstr_Copn_Oasm_reduce] at h_exec
        split at h_exec
        · -- SUB_64
          rename_i ea eb _h _ _ _ _ _ _
          rcases h_a : evalPExpr s ea with _ | a
          · rw [h_a] at h_exec; simp at h_exec
          · rw [h_a] at h_exec; simp at h_exec
            rcases h_b : evalPExpr s eb with _ | b
            · rw [h_b] at h_exec; simp at h_exec
            · rw [h_b] at h_exec; simp at h_exec
              exact writeSubBundle_preserves _ _ _ _ _ _ h_exec h_pres
        · -- SBB_64
          rename_i ea eb ec _h _ _ _ _ _ _
          rcases h_a : evalPExpr s ea with _ | a
          · rw [h_a] at h_exec; simp at h_exec
          · rw [h_a] at h_exec; simp at h_exec
            rcases h_b : evalPExpr s eb with _ | b
            · rw [h_b] at h_exec; simp at h_exec
            · rw [h_b] at h_exec; simp at h_exec
              rcases h_c : evalPExpr s ec with _ | c
              · rw [h_c] at h_exec; simp at h_exec
              · rw [h_c] at h_exec; simp at h_exec
                exact writeSubBundle_preserves _ _ _ _ _ _ h_exec h_pres
        · -- ADD_64
          rename_i ea eb _h _ _ _ _ _ _
          rcases h_a : evalPExpr s ea with _ | a
          · rw [h_a] at h_exec; simp at h_exec
          · rw [h_a] at h_exec; simp at h_exec
            rcases h_b : evalPExpr s eb with _ | b
            · rw [h_b] at h_exec; simp at h_exec
            · rw [h_b] at h_exec; simp at h_exec
              exact writeSubBundle_preserves _ _ _ _ _ _ h_exec h_pres
        · -- ADC_64
          rename_i ea eb ec _h _ _ _ _ _ _
          rcases h_a : evalPExpr s ea with _ | a
          · rw [h_a] at h_exec; simp at h_exec
          · rw [h_a] at h_exec; simp at h_exec
            rcases h_b : evalPExpr s eb with _ | b
            · rw [h_b] at h_exec; simp at h_exec
            · rw [h_b] at h_exec; simp at h_exec
              rcases h_c : evalPExpr s ec with _ | c
              · rw [h_c] at h_exec; simp at h_exec
              · rw [h_c] at h_exec; simp at h_exec
                exact writeSubBundle_preserves _ _ _ _ _ _ h_exec h_pres
        · -- MULX
          rename_i ea eb _h _ _ _ _ _ _
          rcases h_a : evalPExpr s ea with _ | a
          · rw [h_a] at h_exec; simp at h_exec
          · rw [h_a] at h_exec; simp at h_exec
            rcases h_b : evalPExpr s eb with _ | b
            · rw [h_b] at h_exec; simp at h_exec
            · rw [h_b] at h_exec; simp at h_exec
              exact writeMulxBundle_preserves _ _ _ _ _ _ h_exec h_pres
        · -- DIV_64
          rename_i eh el ed _h _ _ _ _ _ _
          rcases h_a : evalPExpr s eh with _ | hi
          · rw [h_a] at h_exec; simp at h_exec
          · rw [h_a] at h_exec; simp at h_exec
            rcases h_b : evalPExpr s el with _ | lo
            · rw [h_b] at h_exec; simp at h_exec
            · rw [h_b] at h_exec; simp at h_exec
              rcases h_c : evalPExpr s ed with _ | d
              · rw [h_c] at h_exec; simp at h_exec
              · rw [h_c] at h_exec; simp at h_exec
                exact writeDivBundle_preserves _ _ _ _ _ _ h_exec h_pres
        · -- ADCX
          rename_i ea eb ec _h _ _ _ _ _ _
          rcases h_a : evalPExpr s ea with _ | a
          · rw [h_a] at h_exec; simp at h_exec
          · rw [h_a] at h_exec; simp at h_exec
            rcases h_b : evalPExpr s eb with _ | b
            · rw [h_b] at h_exec; simp at h_exec
            · rw [h_b] at h_exec; simp at h_exec
              rcases h_c : evalPExpr s ec with _ | c
              · rw [h_c] at h_exec; simp at h_exec
              · rw [h_c] at h_exec; simp at h_exec
                exact writeAdxBundle_preserves _ _ _ _ _ _ h_exec h_pres
        · -- ADOX
          rename_i ea eb ec _h _ _ _ _ _ _
          rcases h_a : evalPExpr s ea with _ | a
          · rw [h_a] at h_exec; simp at h_exec
          · rw [h_a] at h_exec; simp at h_exec
            rcases h_b : evalPExpr s eb with _ | b
            · rw [h_b] at h_exec; simp at h_exec
            · rw [h_b] at h_exec; simp at h_exec
              rcases h_c : evalPExpr s ec with _ | c
              · rw [h_c] at h_exec; simp at h_exec
              · rw [h_c] at h_exec; simp at h_exec
                exact writeAdxBundle_preserves _ _ _ _ _ _ h_exec h_pres
        · -- XOR_64
          rename_i ea eb _h _ _ _ _ _ _
          rcases h_a : evalPExpr s ea with _ | a
          · rw [h_a] at h_exec; simp at h_exec
          · rw [h_a] at h_exec; simp at h_exec
            rcases h_b : evalPExpr s eb with _ | b
            · rw [h_b] at h_exec; simp at h_exec
            · rw [h_b] at h_exec; simp at h_exec
              exact writeXorBundle_preserves _ _ _ _ _ _ _ h_exec h_pres
        · -- (Shift, additive) SHL_64
          rename_i ea ek _h _ _ _ _ _ _
          rcases h_a : evalPExpr s ea with _ | a
          · rw [h_a] at h_exec; simp at h_exec
          · rw [h_a] at h_exec; simp at h_exec
            rcases h_k : evalPExpr s ek with _ | k
            · rw [h_k] at h_exec; simp at h_exec
            · rw [h_k] at h_exec; simp at h_exec
              exact writeShiftBundle_preserves _ _ _ _ _ h_exec h_pres
        · -- (Shift, additive) SHR_64
          rename_i ea ek _h _ _ _ _ _ _
          rcases h_a : evalPExpr s ea with _ | a
          · rw [h_a] at h_exec; simp at h_exec
          · rw [h_a] at h_exec; simp at h_exec
            rcases h_k : evalPExpr s ek with _ | k
            · rw [h_k] at h_exec; simp at h_exec
            · rw [h_k] at h_exec; simp at h_exec
              exact writeShiftBundle_preserves _ _ _ _ _ h_exec h_pres
        · -- (Shift, additive) SHLD_64
          rename_i edst esrc ek _h _ _ _ _ _ _
          rcases h_a : evalPExpr s edst with _ | dst
          · rw [h_a] at h_exec; simp at h_exec
          · rw [h_a] at h_exec; simp at h_exec
            rcases h_b : evalPExpr s esrc with _ | src
            · rw [h_b] at h_exec; simp at h_exec
            · rw [h_b] at h_exec; simp at h_exec
              rcases h_k : evalPExpr s ek with _ | k
              · rw [h_k] at h_exec; simp at h_exec
              · rw [h_k] at h_exec; simp at h_exec
                exact writeShiftBundle_preserves _ _ _ _ _ h_exec h_pres
        · -- (Shift, additive) SHRD_64
          rename_i edst esrc ek _h _ _ _ _ _ _
          rcases h_a : evalPExpr s edst with _ | dst
          · rw [h_a] at h_exec; simp at h_exec
          · rw [h_a] at h_exec; simp at h_exec
            rcases h_b : evalPExpr s esrc with _ | src
            · rw [h_b] at h_exec; simp at h_exec
            · rw [h_b] at h_exec; simp at h_exec
              rcases h_k : evalPExpr s ek with _ | k
              · rw [h_k] at h_exec; simp at h_exec
              · rw [h_k] at h_exec; simp at h_exec
                exact writeShiftBundle_preserves _ _ _ _ _ h_exec h_pres
        · -- (U32, additive) SUB_32
          rename_i ea eb _h _ _ _ _ _ _
          rcases h_a : evalPExpr s ea with _ | a
          · rw [h_a] at h_exec; simp at h_exec
          · rw [h_a] at h_exec; simp at h_exec
            rcases h_b : evalPExpr s eb with _ | b
            · rw [h_b] at h_exec; simp at h_exec
            · rw [h_b] at h_exec; simp at h_exec
              exact writeSubBundle_preserves _ _ _ _ _ _ h_exec h_pres
        · -- (U32, additive) ADD_32
          rename_i ea eb _h _ _ _ _ _ _
          rcases h_a : evalPExpr s ea with _ | a
          · rw [h_a] at h_exec; simp at h_exec
          · rw [h_a] at h_exec; simp at h_exec
            rcases h_b : evalPExpr s eb with _ | b
            · rw [h_b] at h_exec; simp at h_exec
            · rw [h_b] at h_exec; simp at h_exec
              exact writeSubBundle_preserves _ _ _ _ _ _ h_exec h_pres
        · -- (U32, additive) ADC_32
          rename_i ea eb ec _h _ _ _ _ _ _
          rcases h_a : evalPExpr s ea with _ | a
          · rw [h_a] at h_exec; simp at h_exec
          · rw [h_a] at h_exec; simp at h_exec
            rcases h_b : evalPExpr s eb with _ | b
            · rw [h_b] at h_exec; simp at h_exec
            · rw [h_b] at h_exec; simp at h_exec
              rcases h_c : evalPExpr s ec with _ | c
              · rw [h_c] at h_exec; simp at h_exec
              · rw [h_c] at h_exec; simp at h_exec
                exact writeSubBundle_preserves _ _ _ _ _ _ h_exec h_pres
        · -- (U32, additive) SBB_32
          rename_i ea eb ec _h _ _ _ _ _ _
          rcases h_a : evalPExpr s ea with _ | a
          · rw [h_a] at h_exec; simp at h_exec
          · rw [h_a] at h_exec; simp at h_exec
            rcases h_b : evalPExpr s eb with _ | b
            · rw [h_b] at h_exec; simp at h_exec
            · rw [h_b] at h_exec; simp at h_exec
              rcases h_c : evalPExpr s ec with _ | c
              · rw [h_c] at h_exec; simp at h_exec
              · rw [h_c] at h_exec; simp at h_exec
                exact writeSubBundle_preserves _ _ _ _ _ _ h_exec h_pres
        · -- (U32, additive) MULX_32
          rename_i ea eb _h _ _ _ _ _ _
          rcases h_a : evalPExpr s ea with _ | a
          · rw [h_a] at h_exec; simp at h_exec
          · rw [h_a] at h_exec; simp at h_exec
            rcases h_b : evalPExpr s eb with _ | b
            · rw [h_b] at h_exec; simp at h_exec
            · rw [h_b] at h_exec; simp at h_exec
              exact writeMulxBundle_preserves _ _ _ _ _ _ h_exec h_pres
        · simp at h_exec

/-! ## §3. The list combinator. -/

theorem bignumExecPlus_preserves_reg (is : List InstrR) (r : String)
    (h_pres : ∀ i ∈ is, i.preservesReg r)
    (s s' : BignumState) (h_exec : bignumExecPlus is s = some s') :
    s'.regs r = s.regs r := by
  induction is generalizing s with
  | nil =>
    simp only [bignumExecPlus] at h_exec
    rw [Option.some_inj.mp h_exec]
  | cons i rest ih =>
    simp only [bignumExecPlus_cons] at h_exec
    rcases h_step : execInstrPlus s i with _ | s_mid
    · simp [h_step] at h_exec
    · simp [h_step, Option.bind_some] at h_exec
      have h_i_pres : i.preservesReg r := h_pres i (by simp)
      have h_step_pres :=
        execInstrPlus_preserves_reg i s s_mid r h_i_pres h_step
      have h_rest_pres : ∀ j ∈ rest, j.preservesReg r := fun j hj =>
        h_pres j (by simp [hj])
      have h_ih := ih h_rest_pres s_mid h_exec
      rw [h_ih, h_step_pres]

/-! ## §4. Memory preservation chain.

Mirrors §1–§3 but for memory: an instruction that doesn't have an
`Lmem` Cassgn target (decidable via `InstrR.preservesMem`) preserves
`s.mem`. Every `writeXBundle` only calls `setReg` / `setReg'`, both of
which preserve memory by `setReg_mem` (a `@[simp]` lemma in
`BignumStep.lean`). The combinator collapses each per-chunk
`_mem_preserved` lemma in `ChunkedComposition.lean` to one line:

```
chunk_X_mem_preserved s ... s' h :=
  bignumExecPlus_preserves_mem chunk_X (by decide) s s' h
```
-/

/-! ### §4.1 Per-bundle memory-preservation helpers. -/

theorem writeSubBundle_preserves_mem
    (s s' : BignumState) (lvs : List LVal) (cf rv : BitVec 64)
    (h : writeSubBundle s lvs cf rv = some s') :
    s'.mem = s.mem := by
  unfold writeSubBundle at h
  split at h
  next info1 ty1 cfV info2 ty2 info3 ty3 info4 ty4 rV =>
    simp at h; subst h
    simp [setReg]
  next => simp at h

theorem writeMulxBundle_preserves_mem
    (s s' : BignumState) (lvs : List LVal) (hi lo : BitVec 64)
    (h : writeMulxBundle s lvs hi lo = some s') :
    s'.mem = s.mem := by
  unfold writeMulxBundle at h
  split at h
  next hiV loV =>
    simp at h; subst h
    simp [setReg]
  next => simp at h

theorem writeAdxBundle_preserves_mem
    (s s' : BignumState) (lvs : List LVal) (flag rv : BitVec 64)
    (h : writeAdxBundle s lvs flag rv = some s') :
    s'.mem = s.mem := by
  unfold writeAdxBundle at h
  split at h
  next flagV rV =>
    simp at h; subst h
    simp [setReg]
  next => simp at h

theorem writeXorBundle_preserves_mem
    (s s' : BignumState) (lvs : List LVal) (of cf rv : BitVec 64)
    (h : writeXorBundle s lvs of cf rv = some s') :
    s'.mem = s.mem := by
  unfold writeXorBundle at h
  split at h
  next ofV cfV info3 ty3 info4 ty4 info5 ty5 rV =>
    simp at h; subst h
    simp [setReg]
  next info1 ty1 cfV info2 ty2 info3 ty3 info4 ty4 rV =>
    simp at h; subst h
    simp [setReg]
  next => simp at h

theorem writeDivBundle_preserves_mem
    (s s' : BignumState) (lvs : List LVal) (q rv : BitVec 64)
    (h : writeDivBundle s lvs q rv = some s') :
    s'.mem = s.mem := by
  unfold writeDivBundle at h
  split at h
  next info1 ty1 info2 ty2 info3 ty3 info4 ty4 info5 ty5 qV rV =>
    simp at h; subst h
    simp [setReg]
  next => simp at h

theorem writeShiftBundle_preserves_mem
    (s s' : BignumState) (lvs : List LVal) (rv : BitVec 64)
    (h : writeShiftBundle s lvs rv = some s') :
    s'.mem = s.mem := by
  unfold writeShiftBundle at h
  split at h
  next info1 ty1 info2 ty2 info3 ty3 info4 ty4 info5 ty5 rV =>
    simp at h; subst h
    simp [setReg]
  next info1 ty1 cfV info2 ty2 info3 ty3 info4 ty4 rV =>
    simp at h; subst h
    simp [setReg]
  next rV =>
    simp at h; subst h
    simp [setReg]
  next => simp at h

private theorem writeSingleVar_preserves_mem
    (s s' : BignumState) (lvs : List LVal) (rv : BitVec 64)
    (h : writeSingleVar s lvs rv = some s') :
    s'.mem = s.mem := by
  unfold writeSingleVar at h
  split at h
  next vV =>
    simp at h; subst h
    simp [setReg', setReg]
  next => simp at h

private theorem writeTestBundle_preserves_mem
    (s s' : BignumState) (lvs : List LVal) (of cf : BitVec 64)
    (h : writeTestBundle s lvs of cf = some s') :
    s'.mem = s.mem := by
  unfold writeTestBundle at h
  split at h
  next ofV cfV =>
    simp at h; subst h
    simp [setReg', setReg]
  next => simp at h

/-! ### §4.2 The per-instruction memory-preservation lemma. -/

theorem execInstrPlus_preserves_mem (i : InstrR) (s s' : BignumState)
    (h_pres : i.preservesMem)
    (h_exec : execInstrPlus s i = some s') :
    s'.mem = s.mem := by
  unfold InstrR.preservesMem at h_pres
  cases i with
  | Cif cond ct ce =>
    rw [execInstrPlus_Cif_eq, execInstr_Cif_eq_none] at h_exec
    cases h_exec
  | Cfor vi range body =>
    rw [execInstrPlus_Cfor_eq, execInstr_Cfor_eq_none] at h_exec
    cases h_exec
  | Cwhile cb cond ca =>
    rw [execInstrPlus_Cwhile_eq, execInstr_Cwhile_eq_none] at h_exec
    cases h_exec
  | Ccall ii lvs fn args =>
    rw [execInstrPlus_Ccall_eq, execInstr_Ccall_eq_none] at h_exec
    cases h_exec
  | Cassgn lv tag ty e =>
    cases lv with
    | Lnone info lty =>
      rw [execInstrPlus_Cassgn_Lnone_eq, execInstr_Cassgn_Lnone_eq_none] at h_exec
      cases h_exec
    | Laset aa ws x idx =>
      rw [execInstrPlus_Cassgn_Laset_eq, execInstr_Cassgn_Laset_eq_none] at h_exec
      cases h_exec
    | Lasub aa ws len x idx =>
      rw [execInstrPlus_Cassgn_Lasub_eq, execInstr_Cassgn_Lasub_eq_none] at h_exec
      cases h_exec
    | Lvar v =>
      obtain ⟨w, rfl⟩ := execInstrPlus_Cassgn_Lvar_form _ _ _ _ _ _ h_exec
      simp [setReg]
    | Lmem ws base off =>
      simp [InstrR.hasMemWrite, LVal.writesToMem] at h_pres
  | Copn lvs tag op args =>
    cases op with
    | Oasm o =>
      rw [execInstrPlus_Copn_Oasm_reduce] at h_exec
      split at h_exec
      · -- BZHI_64: o.name = "BZHI_64", args = [ea, eb]
        rename_i ea eb _h
        rcases h_a : evalPExpr s ea with _ | a
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_c : evalPExpr s eb with _ | c
          · rw [h_c] at h_exec; simp at h_exec
          · rw [h_c] at h_exec; simp at h_exec
            exact writeSingleVar_preserves_mem _ _ _ _ h_exec
      · -- SHRD_64_imm
        rename_i ea eb k _h
        rcases h_d : evalPExpr s ea with _ | d
        · rw [h_d] at h_exec; simp at h_exec
        · rw [h_d] at h_exec; simp at h_exec
          rcases h_src : evalPExpr s eb with _ | src
          · rw [h_src] at h_exec; simp at h_exec
          · rw [h_src] at h_exec; simp at h_exec
            exact writeSingleVar_preserves_mem _ _ _ _ h_exec
      · -- IMUL_imm_64
        rename_i ea k _h
        rcases h_a : evalPExpr s ea with _ | a
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          split at h_exec
          next info1 ty1 info2 ty2 info3 ty3 info4 ty4 info5 ty5 rV =>
            simp at h_exec; subst h_exec
            simp [setReg', setReg]
          next => simp at h_exec
      · -- SHLX_64
        rename_i ea eb _h
        rcases h_a : evalPExpr s ea with _ | a
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_c : evalPExpr s eb with _ | c
          · rw [h_c] at h_exec; simp at h_exec
          · rw [h_c] at h_exec; simp at h_exec
            exact writeSingleVar_preserves_mem _ _ _ _ h_exec
      · -- AND_64
        rename_i ea eb _h
        rcases h_a : evalPExpr s ea with _ | a
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_b : evalPExpr s eb with _ | b
          · rw [h_b] at h_exec; simp at h_exec
          · rw [h_b] at h_exec; simp at h_exec
            split at h_exec
            next info1 ty1 info2 ty2 info3 ty3 info4 ty4 info5 ty5 rV =>
              simp at h_exec; subst h_exec
              simp [setReg', setReg]
            next => simp at h_exec
      · -- TEST_64
        rename_i ea eb _h
        rcases h_a : evalPExpr s ea with _ | a
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_b : evalPExpr s eb with _ | b
          · rw [h_b] at h_exec; simp at h_exec
          · rw [h_b] at h_exec; simp at h_exec
            exact writeTestBundle_preserves_mem _ _ _ _ _ h_exec
      · -- Fall through to base execInstr
        rw [execInstr_Copn_Oasm_reduce] at h_exec
        split at h_exec
        · -- SUB_64
          rename_i ea eb _h _ _ _ _ _ _
          rcases h_a : evalPExpr s ea with _ | a
          · rw [h_a] at h_exec; simp at h_exec
          · rw [h_a] at h_exec; simp at h_exec
            rcases h_b : evalPExpr s eb with _ | b
            · rw [h_b] at h_exec; simp at h_exec
            · rw [h_b] at h_exec; simp at h_exec
              exact writeSubBundle_preserves_mem _ _ _ _ _ h_exec
        · -- SBB_64
          rename_i ea eb ec _h _ _ _ _ _ _
          rcases h_a : evalPExpr s ea with _ | a
          · rw [h_a] at h_exec; simp at h_exec
          · rw [h_a] at h_exec; simp at h_exec
            rcases h_b : evalPExpr s eb with _ | b
            · rw [h_b] at h_exec; simp at h_exec
            · rw [h_b] at h_exec; simp at h_exec
              rcases h_c : evalPExpr s ec with _ | c
              · rw [h_c] at h_exec; simp at h_exec
              · rw [h_c] at h_exec; simp at h_exec
                exact writeSubBundle_preserves_mem _ _ _ _ _ h_exec
        · -- ADD_64
          rename_i ea eb _h _ _ _ _ _ _
          rcases h_a : evalPExpr s ea with _ | a
          · rw [h_a] at h_exec; simp at h_exec
          · rw [h_a] at h_exec; simp at h_exec
            rcases h_b : evalPExpr s eb with _ | b
            · rw [h_b] at h_exec; simp at h_exec
            · rw [h_b] at h_exec; simp at h_exec
              exact writeSubBundle_preserves_mem _ _ _ _ _ h_exec
        · -- ADC_64
          rename_i ea eb ec _h _ _ _ _ _ _
          rcases h_a : evalPExpr s ea with _ | a
          · rw [h_a] at h_exec; simp at h_exec
          · rw [h_a] at h_exec; simp at h_exec
            rcases h_b : evalPExpr s eb with _ | b
            · rw [h_b] at h_exec; simp at h_exec
            · rw [h_b] at h_exec; simp at h_exec
              rcases h_c : evalPExpr s ec with _ | c
              · rw [h_c] at h_exec; simp at h_exec
              · rw [h_c] at h_exec; simp at h_exec
                exact writeSubBundle_preserves_mem _ _ _ _ _ h_exec
        · -- MULX
          rename_i ea eb _h _ _ _ _ _ _
          rcases h_a : evalPExpr s ea with _ | a
          · rw [h_a] at h_exec; simp at h_exec
          · rw [h_a] at h_exec; simp at h_exec
            rcases h_b : evalPExpr s eb with _ | b
            · rw [h_b] at h_exec; simp at h_exec
            · rw [h_b] at h_exec; simp at h_exec
              exact writeMulxBundle_preserves_mem _ _ _ _ _ h_exec
        · -- DIV_64
          rename_i eh el ed _h _ _ _ _ _ _
          rcases h_a : evalPExpr s eh with _ | hi
          · rw [h_a] at h_exec; simp at h_exec
          · rw [h_a] at h_exec; simp at h_exec
            rcases h_b : evalPExpr s el with _ | lo
            · rw [h_b] at h_exec; simp at h_exec
            · rw [h_b] at h_exec; simp at h_exec
              rcases h_c : evalPExpr s ed with _ | d
              · rw [h_c] at h_exec; simp at h_exec
              · rw [h_c] at h_exec; simp at h_exec
                exact writeDivBundle_preserves_mem _ _ _ _ _ h_exec
        · -- ADCX
          rename_i ea eb ec _h _ _ _ _ _ _
          rcases h_a : evalPExpr s ea with _ | a
          · rw [h_a] at h_exec; simp at h_exec
          · rw [h_a] at h_exec; simp at h_exec
            rcases h_b : evalPExpr s eb with _ | b
            · rw [h_b] at h_exec; simp at h_exec
            · rw [h_b] at h_exec; simp at h_exec
              rcases h_c : evalPExpr s ec with _ | c
              · rw [h_c] at h_exec; simp at h_exec
              · rw [h_c] at h_exec; simp at h_exec
                exact writeAdxBundle_preserves_mem _ _ _ _ _ h_exec
        · -- ADOX
          rename_i ea eb ec _h _ _ _ _ _ _
          rcases h_a : evalPExpr s ea with _ | a
          · rw [h_a] at h_exec; simp at h_exec
          · rw [h_a] at h_exec; simp at h_exec
            rcases h_b : evalPExpr s eb with _ | b
            · rw [h_b] at h_exec; simp at h_exec
            · rw [h_b] at h_exec; simp at h_exec
              rcases h_c : evalPExpr s ec with _ | c
              · rw [h_c] at h_exec; simp at h_exec
              · rw [h_c] at h_exec; simp at h_exec
                exact writeAdxBundle_preserves_mem _ _ _ _ _ h_exec
        · -- XOR_64
          rename_i ea eb _h _ _ _ _ _ _
          rcases h_a : evalPExpr s ea with _ | a
          · rw [h_a] at h_exec; simp at h_exec
          · rw [h_a] at h_exec; simp at h_exec
            rcases h_b : evalPExpr s eb with _ | b
            · rw [h_b] at h_exec; simp at h_exec
            · rw [h_b] at h_exec; simp at h_exec
              exact writeXorBundle_preserves_mem _ _ _ _ _ _ h_exec
        · -- (Shift, additive) SHL_64
          rename_i ea ek _h _ _ _ _ _ _
          rcases h_a : evalPExpr s ea with _ | a
          · rw [h_a] at h_exec; simp at h_exec
          · rw [h_a] at h_exec; simp at h_exec
            rcases h_k : evalPExpr s ek with _ | k
            · rw [h_k] at h_exec; simp at h_exec
            · rw [h_k] at h_exec; simp at h_exec
              exact writeShiftBundle_preserves_mem _ _ _ _ h_exec
        · -- (Shift, additive) SHR_64
          rename_i ea ek _h _ _ _ _ _ _
          rcases h_a : evalPExpr s ea with _ | a
          · rw [h_a] at h_exec; simp at h_exec
          · rw [h_a] at h_exec; simp at h_exec
            rcases h_k : evalPExpr s ek with _ | k
            · rw [h_k] at h_exec; simp at h_exec
            · rw [h_k] at h_exec; simp at h_exec
              exact writeShiftBundle_preserves_mem _ _ _ _ h_exec
        · -- (Shift, additive) SHLD_64
          rename_i edst esrc ek _h _ _ _ _ _ _
          rcases h_a : evalPExpr s edst with _ | dst
          · rw [h_a] at h_exec; simp at h_exec
          · rw [h_a] at h_exec; simp at h_exec
            rcases h_b : evalPExpr s esrc with _ | src
            · rw [h_b] at h_exec; simp at h_exec
            · rw [h_b] at h_exec; simp at h_exec
              rcases h_k : evalPExpr s ek with _ | k
              · rw [h_k] at h_exec; simp at h_exec
              · rw [h_k] at h_exec; simp at h_exec
                exact writeShiftBundle_preserves_mem _ _ _ _ h_exec
        · -- (Shift, additive) SHRD_64
          rename_i edst esrc ek _h _ _ _ _ _ _
          rcases h_a : evalPExpr s edst with _ | dst
          · rw [h_a] at h_exec; simp at h_exec
          · rw [h_a] at h_exec; simp at h_exec
            rcases h_b : evalPExpr s esrc with _ | src
            · rw [h_b] at h_exec; simp at h_exec
            · rw [h_b] at h_exec; simp at h_exec
              rcases h_k : evalPExpr s ek with _ | k
              · rw [h_k] at h_exec; simp at h_exec
              · rw [h_k] at h_exec; simp at h_exec
                exact writeShiftBundle_preserves_mem _ _ _ _ h_exec
        · -- (U32, additive) SUB_32
          rename_i ea eb _h _ _ _ _ _ _
          rcases h_a : evalPExpr s ea with _ | a
          · rw [h_a] at h_exec; simp at h_exec
          · rw [h_a] at h_exec; simp at h_exec
            rcases h_b : evalPExpr s eb with _ | b
            · rw [h_b] at h_exec; simp at h_exec
            · rw [h_b] at h_exec; simp at h_exec
              exact writeSubBundle_preserves_mem _ _ _ _ _ h_exec
        · -- (U32, additive) ADD_32
          rename_i ea eb _h _ _ _ _ _ _
          rcases h_a : evalPExpr s ea with _ | a
          · rw [h_a] at h_exec; simp at h_exec
          · rw [h_a] at h_exec; simp at h_exec
            rcases h_b : evalPExpr s eb with _ | b
            · rw [h_b] at h_exec; simp at h_exec
            · rw [h_b] at h_exec; simp at h_exec
              exact writeSubBundle_preserves_mem _ _ _ _ _ h_exec
        · -- (U32, additive) ADC_32
          rename_i ea eb ec _h _ _ _ _ _ _
          rcases h_a : evalPExpr s ea with _ | a
          · rw [h_a] at h_exec; simp at h_exec
          · rw [h_a] at h_exec; simp at h_exec
            rcases h_b : evalPExpr s eb with _ | b
            · rw [h_b] at h_exec; simp at h_exec
            · rw [h_b] at h_exec; simp at h_exec
              rcases h_c : evalPExpr s ec with _ | c
              · rw [h_c] at h_exec; simp at h_exec
              · rw [h_c] at h_exec; simp at h_exec
                exact writeSubBundle_preserves_mem _ _ _ _ _ h_exec
        · -- (U32, additive) SBB_32
          rename_i ea eb ec _h _ _ _ _ _ _
          rcases h_a : evalPExpr s ea with _ | a
          · rw [h_a] at h_exec; simp at h_exec
          · rw [h_a] at h_exec; simp at h_exec
            rcases h_b : evalPExpr s eb with _ | b
            · rw [h_b] at h_exec; simp at h_exec
            · rw [h_b] at h_exec; simp at h_exec
              rcases h_c : evalPExpr s ec with _ | c
              · rw [h_c] at h_exec; simp at h_exec
              · rw [h_c] at h_exec; simp at h_exec
                exact writeSubBundle_preserves_mem _ _ _ _ _ h_exec
        · -- (U32, additive) MULX_32
          rename_i ea eb _h _ _ _ _ _ _
          rcases h_a : evalPExpr s ea with _ | a
          · rw [h_a] at h_exec; simp at h_exec
          · rw [h_a] at h_exec; simp at h_exec
            rcases h_b : evalPExpr s eb with _ | b
            · rw [h_b] at h_exec; simp at h_exec
            · rw [h_b] at h_exec; simp at h_exec
              exact writeMulxBundle_preserves_mem _ _ _ _ _ h_exec
        · simp at h_exec

/-! ### §4.3 The list combinator. -/

theorem bignumExecPlus_preserves_mem (is : List InstrR)
    (h_pres : ∀ i ∈ is, i.preservesMem)
    (s s' : BignumState) (h_exec : bignumExecPlus is s = some s') :
    s'.mem = s.mem := by
  induction is generalizing s with
  | nil =>
    simp only [bignumExecPlus] at h_exec
    rw [Option.some_inj.mp h_exec]
  | cons i rest ih =>
    simp only [bignumExecPlus_cons] at h_exec
    rcases h_step : execInstrPlus s i with _ | s_mid
    · simp [h_step] at h_exec
    · simp [h_step, Option.bind_some] at h_exec
      have h_i_pres : i.preservesMem := h_pres i (by simp)
      have h_step_pres :=
        execInstrPlus_preserves_mem i s s_mid h_i_pres h_step
      have h_rest_pres : ∀ j ∈ rest, j.preservesMem := fun j hj =>
        h_pres j (by simp [hj])
      have h_ih := ih h_rest_pres s_mid h_exec
      rw [h_ih, h_step_pres]

/-! ## §4c. CFG-aware combinator over `bignumExecFuel`

Parallel to §3 / §4 (which operate over `bignumExecPlus`, the
straight-line interpreter), this section targets `bignumExecFuel`
(`BignumExec.lean:446`), the fuel-aware interpreter that handles
`Cif`/`Cfor`/`Cwhile`/`Ccall`. The predicate is `InstrR.preservesRegRec`
(§1c above) which traverses CFG sub-bodies recursively.

The proof is by well-founded recursion on `(fuel, body.length)`
(matching `bignumExecFuel`'s `termination_by` clause):

| Case | Recipe |
|------|--------|
| `0, _, _` | `bignumExecFuel = none`; contradiction. |
| `_+1, [], s` | `bignumExecFuel = some s`; `s' = s`, trivial. |
| `_+1, .Cassgn _, _ ; rest` | Use `execInstr_preserves_reg` on the head, then IH on rest. |
| `_+1, .Copn _, _ ; rest` | Same as Cassgn. |
| `_+1, .Cif cond ct ce ; rest` | Case-split on `evalPExpr s cond`; recurse on `ct` or `ce` (preservation captured by recursive `regWritesRec`); IH on rest. |
| `_+1, .Cfor v range body ; rest` | Reduce to `bignumExecFuel registry fuel (unrollFor v range body ++ rest) s` (fuel decreases); the loop counter `v.var.vname` is in `regWritesRec`, so `r ≠ v.var.vname`; IH on the unrolled list. |
| `_+1, .Cwhile cb cond ca ; rest` | Reduce to `bignumExecFuel registry fuel (cb ++ [.Cif cond (ca ++ [.Cwhile ..]) []] ++ rest) s` (fuel decreases); `regWritesRec` covers `cb` and `ca`. |
| `_+1, .Ccall _ lvs _ _ ; rest` | Void (`lvs = []`): caller regs unchanged. Non-void: `bindResults` writes only the `Lvar` names of `lvs`, all covered by `regWritesRec`; IH on rest. |

Call site mirrors §3:

  example (s s' : BignumState) (fuel : Nat)
      (h : bignumExecFuel registry fuel myBody s = some s') :
      s'.regs "preserved" = s.regs "preserved" :=
    bignumExecFuel_preserves_reg registry fuel myBody "preserved"
      (by decide) s s' h
-/

/-! ### §4c.1 Helper: `execInstr_preserves_reg`.

The `bignumExecFuel` fall-through case (line 495-498 of `BignumExec.lean`)
calls `execInstr` (not `execInstrPlus`), so we need an analogous
preservation lemma. `execInstr` handles fewer Oasm shapes than
`execInstrPlus` (no BZHI/SHRD/IMUL/SHLX/AND/TEST), so the proof is a
strict subset of `execInstrPlus_preserves_reg`. -/

theorem execInstr_preserves_reg (i : InstrR) (s s' : BignumState) (r : String)
    (h_pres : i.preservesReg r)
    (h_exec : execInstr s i = some s') :
    s'.regs r = s.regs r := by
  unfold InstrR.preservesReg at h_pres
  cases i with
  | Cif cond ct ce => rw [execInstr_Cif_eq_none] at h_exec; cases h_exec
  | Cfor vi range body => rw [execInstr_Cfor_eq_none] at h_exec; cases h_exec
  | Cwhile cb cond ca => rw [execInstr_Cwhile_eq_none] at h_exec; cases h_exec
  | Ccall ii lvs fn args => rw [execInstr_Ccall_eq_none] at h_exec; cases h_exec
  | Cassgn lv tag ty e =>
    cases lv with
    | Lnone info lty =>
      rw [execInstr_Cassgn_Lnone_eq_none] at h_exec; cases h_exec
    | Laset aa ws x idx =>
      rw [execInstr_Cassgn_Laset_eq_none] at h_exec; cases h_exec
    | Lasub aa ws len x idx =>
      rw [execInstr_Cassgn_Lasub_eq_none] at h_exec; cases h_exec
    | Lvar v =>
      simp only [InstrR.regWrites, List.mem_singleton] at h_pres
      obtain ⟨w, rfl⟩ := execInstr_Cassgn_Lvar_form _ _ _ _ _ _ h_exec
      show (if r = v.var.vname then w else s.regs r) = s.regs r
      exact if_neg h_pres
    | Lmem ws base off =>
      cases ws with
      | U64 =>
        exact execInstr_Cassgn_Lmem_U64_preserves_regs _ _ _ _ _ _ _ _ h_exec
      | U8 =>
        -- (U8, additive) U8 byte store now succeeds; it preserves regs.
        exact execInstr_Cassgn_Lmem_U8_preserves_regs _ _ _ _ _ _ _ _ h_exec
      | U16 =>
        rw [execInstr_Cassgn_Lmem_nonU64_eq_none _ _ _ _ _ _ _
              (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)]
          at h_exec
        cases h_exec
      | U32 =>
        -- (U32, additive) U32 memory store now succeeds; it preserves regs.
        exact execInstr_Cassgn_Lmem_U32_preserves_regs _ _ _ _ _ _ _ _ h_exec
      | U128 =>
        rw [execInstr_Cassgn_Lmem_nonU64_eq_none _ _ _ _ _ _ _
              (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)]
          at h_exec
        cases h_exec
      | U256 =>
        rw [execInstr_Cassgn_Lmem_nonU64_eq_none _ _ _ _ _ _ _
              (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)]
          at h_exec
        cases h_exec
      | U512 =>
        rw [execInstr_Cassgn_Lmem_nonU64_eq_none _ _ _ _ _ _ _
              (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)]
          at h_exec
        cases h_exec
  | Copn lvs tag op args =>
    simp only [InstrR.regWrites] at h_pres
    cases op with
    | Oasm o =>
      rw [execInstr_Copn_Oasm_reduce] at h_exec
      split at h_exec
      · -- SUB_64
        rename_i ea eb _h
        rcases h_a : evalPExpr s ea with _ | a
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_b : evalPExpr s eb with _ | b
          · rw [h_b] at h_exec; simp at h_exec
          · rw [h_b] at h_exec; simp at h_exec
            exact writeSubBundle_preserves _ _ _ _ _ _ h_exec h_pres
      · -- SBB_64
        rename_i ea eb ec _h
        rcases h_a : evalPExpr s ea with _ | a
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_b : evalPExpr s eb with _ | b
          · rw [h_b] at h_exec; simp at h_exec
          · rw [h_b] at h_exec; simp at h_exec
            rcases h_c : evalPExpr s ec with _ | c
            · rw [h_c] at h_exec; simp at h_exec
            · rw [h_c] at h_exec; simp at h_exec
              exact writeSubBundle_preserves _ _ _ _ _ _ h_exec h_pres
      · -- ADD_64
        rename_i ea eb _h
        rcases h_a : evalPExpr s ea with _ | a
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_b : evalPExpr s eb with _ | b
          · rw [h_b] at h_exec; simp at h_exec
          · rw [h_b] at h_exec; simp at h_exec
            exact writeSubBundle_preserves _ _ _ _ _ _ h_exec h_pres
      · -- ADC_64
        rename_i ea eb ec _h
        rcases h_a : evalPExpr s ea with _ | a
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_b : evalPExpr s eb with _ | b
          · rw [h_b] at h_exec; simp at h_exec
          · rw [h_b] at h_exec; simp at h_exec
            rcases h_c : evalPExpr s ec with _ | c
            · rw [h_c] at h_exec; simp at h_exec
            · rw [h_c] at h_exec; simp at h_exec
              exact writeSubBundle_preserves _ _ _ _ _ _ h_exec h_pres
      · -- MULX
        rename_i ea eb _h
        rcases h_a : evalPExpr s ea with _ | a
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_b : evalPExpr s eb with _ | b
          · rw [h_b] at h_exec; simp at h_exec
          · rw [h_b] at h_exec; simp at h_exec
            exact writeMulxBundle_preserves _ _ _ _ _ _ h_exec h_pres
      · -- DIV_64
        rename_i eh el ed _h
        rcases h_a : evalPExpr s eh with _ | hi
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_b : evalPExpr s el with _ | lo
          · rw [h_b] at h_exec; simp at h_exec
          · rw [h_b] at h_exec; simp at h_exec
            rcases h_c : evalPExpr s ed with _ | d
            · rw [h_c] at h_exec; simp at h_exec
            · rw [h_c] at h_exec; simp at h_exec
              exact writeDivBundle_preserves _ _ _ _ _ _ h_exec h_pres
      · -- ADCX
        rename_i ea eb ec _h
        rcases h_a : evalPExpr s ea with _ | a
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_b : evalPExpr s eb with _ | b
          · rw [h_b] at h_exec; simp at h_exec
          · rw [h_b] at h_exec; simp at h_exec
            rcases h_c : evalPExpr s ec with _ | c
            · rw [h_c] at h_exec; simp at h_exec
            · rw [h_c] at h_exec; simp at h_exec
              exact writeAdxBundle_preserves _ _ _ _ _ _ h_exec h_pres
      · -- ADOX
        rename_i ea eb ec _h
        rcases h_a : evalPExpr s ea with _ | a
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_b : evalPExpr s eb with _ | b
          · rw [h_b] at h_exec; simp at h_exec
          · rw [h_b] at h_exec; simp at h_exec
            rcases h_c : evalPExpr s ec with _ | c
            · rw [h_c] at h_exec; simp at h_exec
            · rw [h_c] at h_exec; simp at h_exec
              exact writeAdxBundle_preserves _ _ _ _ _ _ h_exec h_pres
      · -- XOR_64
        rename_i ea eb _h
        rcases h_a : evalPExpr s ea with _ | a
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_b : evalPExpr s eb with _ | b
          · rw [h_b] at h_exec; simp at h_exec
          · rw [h_b] at h_exec; simp at h_exec
            exact writeXorBundle_preserves _ _ _ _ _ _ _ h_exec h_pres
      · -- (Shift, additive) SHL_64
        rename_i ea ek _h
        rcases h_a : evalPExpr s ea with _ | a
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_k : evalPExpr s ek with _ | k
          · rw [h_k] at h_exec; simp at h_exec
          · rw [h_k] at h_exec; simp at h_exec
            exact writeShiftBundle_preserves _ _ _ _ _ h_exec h_pres
      · -- (Shift, additive) SHR_64
        rename_i ea ek _h
        rcases h_a : evalPExpr s ea with _ | a
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_k : evalPExpr s ek with _ | k
          · rw [h_k] at h_exec; simp at h_exec
          · rw [h_k] at h_exec; simp at h_exec
            exact writeShiftBundle_preserves _ _ _ _ _ h_exec h_pres
      · -- (Shift, additive) SHLD_64
        rename_i edst esrc ek _h
        rcases h_a : evalPExpr s edst with _ | dst
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_b : evalPExpr s esrc with _ | src
          · rw [h_b] at h_exec; simp at h_exec
          · rw [h_b] at h_exec; simp at h_exec
            rcases h_k : evalPExpr s ek with _ | k
            · rw [h_k] at h_exec; simp at h_exec
            · rw [h_k] at h_exec; simp at h_exec
              exact writeShiftBundle_preserves _ _ _ _ _ h_exec h_pres
      · -- (Shift, additive) SHRD_64
        rename_i edst esrc ek _h
        rcases h_a : evalPExpr s edst with _ | dst
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_b : evalPExpr s esrc with _ | src
          · rw [h_b] at h_exec; simp at h_exec
          · rw [h_b] at h_exec; simp at h_exec
            rcases h_k : evalPExpr s ek with _ | k
            · rw [h_k] at h_exec; simp at h_exec
            · rw [h_k] at h_exec; simp at h_exec
              exact writeShiftBundle_preserves _ _ _ _ _ h_exec h_pres
      · -- (U32, additive) SUB_32
        rename_i ea eb _h
        rcases h_a : evalPExpr s ea with _ | a
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_b : evalPExpr s eb with _ | b
          · rw [h_b] at h_exec; simp at h_exec
          · rw [h_b] at h_exec; simp at h_exec
            exact writeSubBundle_preserves _ _ _ _ _ _ h_exec h_pres
      · -- (U32, additive) ADD_32
        rename_i ea eb _h
        rcases h_a : evalPExpr s ea with _ | a
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_b : evalPExpr s eb with _ | b
          · rw [h_b] at h_exec; simp at h_exec
          · rw [h_b] at h_exec; simp at h_exec
            exact writeSubBundle_preserves _ _ _ _ _ _ h_exec h_pres
      · -- (U32, additive) ADC_32
        rename_i ea eb ec _h
        rcases h_a : evalPExpr s ea with _ | a
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_b : evalPExpr s eb with _ | b
          · rw [h_b] at h_exec; simp at h_exec
          · rw [h_b] at h_exec; simp at h_exec
            rcases h_c : evalPExpr s ec with _ | c
            · rw [h_c] at h_exec; simp at h_exec
            · rw [h_c] at h_exec; simp at h_exec
              exact writeSubBundle_preserves _ _ _ _ _ _ h_exec h_pres
      · -- (U32, additive) SBB_32
        rename_i ea eb ec _h
        rcases h_a : evalPExpr s ea with _ | a
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_b : evalPExpr s eb with _ | b
          · rw [h_b] at h_exec; simp at h_exec
          · rw [h_b] at h_exec; simp at h_exec
            rcases h_c : evalPExpr s ec with _ | c
            · rw [h_c] at h_exec; simp at h_exec
            · rw [h_c] at h_exec; simp at h_exec
              exact writeSubBundle_preserves _ _ _ _ _ _ h_exec h_pres
      · -- (U32, additive) MULX_32
        rename_i ea eb _h
        rcases h_a : evalPExpr s ea with _ | a
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_b : evalPExpr s eb with _ | b
          · rw [h_b] at h_exec; simp at h_exec
          · rw [h_b] at h_exec; simp at h_exec
            exact writeMulxBundle_preserves _ _ _ _ _ _ h_exec h_pres
      · simp at h_exec

/-! ### §4c.2 Bridge: `regWritesRec` ⇒ `regWrites` for non-CFG shapes.

`InstrR.regWrites` is the per-instruction list (no recursion through CFG).
`regWritesRec` matches it on `Cassgn`/`Copn`/`Ccall` and recurses on
`Cif`/`Cfor`/`Cwhile`. So `r ∉ regWritesRec i → r ∉ regWrites i` when
`i` is not a CFG-shape, which is the case at the fall-through arm of
`bignumExecFuel`. -/

private theorem InstrR.preservesReg_of_preservesRegRec (i : InstrR) (r : String)
    (h : i.preservesRegRec r) : i.preservesReg r := by
  unfold InstrR.preservesRegRec at h
  unfold InstrR.preservesReg
  cases i with
  | Cassgn lv tag ty e =>
    cases lv with
    | Lvar v =>
      simp only [InstrR.regWritesRec, InstrR.regWrites] at *
      exact h
    | Lnone _ _ =>
      simp only [InstrR.regWrites]; intro h'; cases h'
    | Laset _ _ _ _ =>
      simp only [InstrR.regWrites]; intro h'; cases h'
    | Lasub _ _ _ _ _ =>
      simp only [InstrR.regWrites]; intro h'; cases h'
    | Lmem _ _ _ =>
      simp only [InstrR.regWrites]; intro h'; cases h'
  | Copn lvs tag op args =>
    simp only [InstrR.regWritesRec, InstrR.regWrites] at *
    exact h
  | Cif _ _ _ =>
    simp only [InstrR.regWrites]; intro h'; cases h'
  | Cfor _ _ _ =>
    simp only [InstrR.regWrites]; intro h'; cases h'
  | Cwhile _ _ _ =>
    simp only [InstrR.regWrites]; intro h'; cases h'
  | Ccall _ _ _ _ =>
    simp only [InstrR.regWrites]; intro h'; cases h'

/-! ### §4c.3 Helper: `unrollFor` preserves `r` recursively.

If `r ∉ v.var.vname :: listRegWrites body` (= `r ∉ regWritesRec (Cfor v r body)`),
then every instruction in `unrollFor v range body` preserves `r`
recursively. The unroll produces only `mkSetVarConst v _` (a Cassgn into
`v`, write list `[v.var.vname]` — distinct from `r`) and instructions
copied from `body`. -/

private theorem unrollFor_preservesRegRec
    (v : VarI) (range : Range) (body : List InstrR) (r : String)
    (h_neq : r ≠ v.var.vname)
    (h_body : ∀ j ∈ body, j.preservesRegRec r) :
    ∀ i ∈ unrollFor v range body, i.preservesRegRec r := by
  intro i hi
  unfold unrollFor at hi
  -- `range.dir` is the LoopDir.UpTo/DownTo discriminator. Capture it in
  -- an equality so we can split.
  cases hdir : range.dir with
  | UpTo =>
    rw [hdir] at hi
    simp only [List.mem_flatMap, List.mem_range] at hi
    obtain ⟨k, _hk, hi_in⟩ := hi
    rw [List.mem_cons] at hi_in
    rcases hi_in with hi_eq | hi_in
    · -- i = mkSetVarConst v (range.lo + k); regWritesRec = [v.var.vname]
      rw [hi_eq, mkSetVarConst_eq]
      show r ∉ InstrR.regWritesRec _
      simp only [InstrR.regWritesRec, List.mem_singleton]
      exact h_neq
    · exact h_body _ hi_in
  | DownTo =>
    rw [hdir] at hi
    simp only [List.mem_flatMap, List.mem_range] at hi
    obtain ⟨k, _hk, hi_in⟩ := hi
    rw [List.mem_cons] at hi_in
    rcases hi_in with hi_eq | hi_in
    · rw [hi_eq, mkSetVarConst_eq]
      show r ∉ InstrR.regWritesRec _
      simp only [InstrR.regWritesRec, List.mem_singleton]
      exact h_neq
    · exact h_body _ hi_in

/-! ### §4c.4 Predicate splitting helpers. -/

private theorem InstrR.regWritesRec_cons_iff (r : String) (i : InstrR)
    (is : List InstrR) :
    r ∉ InstrR.regWritesRec.listRegWrites (i :: is) ↔
      r ∉ i.regWritesRec ∧ r ∉ InstrR.regWritesRec.listRegWrites is := by
  simp only [InstrR.regWritesRec.listRegWrites, List.mem_append, not_or]

private theorem InstrR.listRegWrites_eq_listMem (r : String) (is : List InstrR) :
    r ∉ InstrR.regWritesRec.listRegWrites is ↔
      ∀ i ∈ is, r ∉ i.regWritesRec := by
  induction is with
  | nil =>
    constructor
    · intro _ j hj; cases hj
    · intro _; simp [InstrR.regWritesRec.listRegWrites]
  | cons i is ih =>
    rw [InstrR.regWritesRec_cons_iff]
    constructor
    · rintro ⟨h1, h2⟩ j hj
      rw [List.mem_cons] at hj
      rcases hj with rfl | hj
      · exact h1
      · exact (ih.mp h2) j hj
    · intro h
      refine ⟨h i (by simp), ih.mpr fun j hj => h j ?_⟩
      rw [List.mem_cons]; right; exact hj

/-! ### §4c.4b Helper: `bindResults` preserves untargeted registers.

`bindResult` writes a caller register only through its `Lvar` arm; the
`Lnone` arm is the identity and the `Lmem .U64` arm touches only memory.
So if `r` is not among the `Lvar` names of `lvs`, threading `bindResults`
leaves `r` unchanged. -/

private theorem bindResults_preserves_reg
    (sCallee : BignumState) (lvs : List LVal) (rs : List VarI)
    (sCaller s' : BignumState) (r : String)
    (h : bindResults sCaller sCallee lvs rs = some s')
    (h_no : r ∉ lvs.filterMap (fun lv => match lv with
              | .Lvar v => some v.var.vname | _ => none)) :
    s'.regs r = sCaller.regs r := by
  induction lvs generalizing rs sCaller with
  | nil =>
    cases rs with
    | nil =>
      simp only [bindResults, Option.some_inj] at h
      rw [h]
    | cons res rs => simp [bindResults] at h
  | cons lv lvs ih =>
    cases rs with
    | nil => simp [bindResults] at h
    | cons res rs =>
      cases lv with
      | Lnone info ty =>
        simp at h_no
        simp only [bindResults, bindResult] at h
        simp at h
        exact ih rs sCaller h (by simpa using h_no)
      | Lvar x =>
        simp at h_no
        obtain ⟨h_ne, h_tail⟩ := h_no
        simp only [bindResults, bindResult] at h
        simp at h
        rw [ih rs _ h (by simpa using h_tail)]
        simp [setReg, h_ne]
      | Lmem ws base off =>
        simp at h_no
        cases ws with
        | U64 =>
          simp only [bindResults, bindResult] at h
          rcases h_a : resolveAddr sCaller base off with _ | addr
          · rw [h_a] at h; simp at h
          · rw [h_a] at h; simp at h
            rw [ih rs _ h (by simpa using h_no)]
            rfl
        | U8 => simp [bindResults, bindResult] at h
        | U16 => simp [bindResults, bindResult] at h
        | U32 => simp [bindResults, bindResult] at h
        | U128 => simp [bindResults, bindResult] at h
        | U256 => simp [bindResults, bindResult] at h
        | U512 => simp [bindResults, bindResult] at h
      | Laset aa ws x idx => simp [bindResults, bindResult] at h
      | Lasub aa ws len x idx => simp [bindResults, bindResult] at h

/-! ### §4c.5 Main theorem: `bignumExecFuel_preserves_reg`.

The auxiliary uses `r ∉ listRegWrites is` (single hypothesis),
which is more convenient for the recursive structure than a
`∀ i ∈ is, ...` quantifier. The wrapper at the bottom restores
the public `∀`-form expected by callers. -/

private theorem bignumExecFuel_preserves_reg_aux
    (registry : BignumRegistry) (fuel : Nat) (is : List InstrR) (r : String)
    (h_pres : r ∉ InstrR.regWritesRec.listRegWrites is)
    (s s' : BignumState)
    (h_exec : bignumExecFuel registry fuel is s = some s') :
    s'.regs r = s.regs r := by
  match fuel, is, h_pres, s, s', h_exec with
  | 0, _, _, _, _, h_exec =>
    simp only [bignumExecFuel] at h_exec
    cases h_exec
  | _ + 1, [], _, s, s', h_exec =>
    simp only [bignumExecFuel, Option.some_inj] at h_exec
    rw [h_exec]
  | fuel + 1, .Cassgn lv tag ty e :: rest, h_pres, s, s', h_exec =>
    rw [InstrR.regWritesRec_cons_iff] at h_pres
    obtain ⟨h_head, h_tail⟩ := h_pres
    have h_head' : (InstrR.Cassgn lv tag ty e).preservesReg r :=
      InstrR.preservesReg_of_preservesRegRec _ _ h_head
    -- Reduce bignumExecFuel on Cassgn head via its definitional equation.
    simp only [bignumExecFuel] at h_exec
    rcases h_step : execInstr s (.Cassgn lv tag ty e) with _ | s_mid
    · rw [h_step] at h_exec; cases h_exec
    · rw [h_step] at h_exec
      have h_step_pres :=
        execInstr_preserves_reg _ _ _ _ h_head' h_step
      have h_ih :=
        bignumExecFuel_preserves_reg_aux registry (fuel + 1) rest r h_tail
          s_mid s' h_exec
      rw [h_ih, h_step_pres]
  | fuel + 1, .Copn lvs tag op args :: rest, h_pres, s, s', h_exec =>
    rw [InstrR.regWritesRec_cons_iff] at h_pres
    obtain ⟨h_head, h_tail⟩ := h_pres
    have h_head' : (InstrR.Copn lvs tag op args).preservesReg r :=
      InstrR.preservesReg_of_preservesRegRec _ _ h_head
    simp only [bignumExecFuel] at h_exec
    rcases h_step : execInstr s (.Copn lvs tag op args) with _ | s_mid
    · rw [h_step] at h_exec; cases h_exec
    · rw [h_step] at h_exec
      have h_step_pres :=
        execInstr_preserves_reg _ _ _ _ h_head' h_step
      have h_ih :=
        bignumExecFuel_preserves_reg_aux registry (fuel + 1) rest r h_tail
          s_mid s' h_exec
      rw [h_ih, h_step_pres]
  | fuel + 1, .Cif cond ct ce :: rest, h_pres, s, s', h_exec =>
    rw [InstrR.regWritesRec_cons_iff] at h_pres
    obtain ⟨h_head, h_tail⟩ := h_pres
    -- regWritesRec (Cif cond ct ce) = listRegWrites ct ++ listRegWrites ce
    simp only [InstrR.regWritesRec, List.mem_append, not_or] at h_head
    obtain ⟨h_ct, h_ce⟩ := h_head
    simp only [bignumExecFuel] at h_exec
    rcases h_cond : evalPExpr s cond with _ | condV
    · rw [h_cond] at h_exec; cases h_exec
    · rw [h_cond] at h_exec
      simp only at h_exec
      -- chosen branch
      by_cases hc : condV != 0
      · rw [if_pos hc] at h_exec
        rcases h_inner : bignumExecFuel registry fuel ct s with _ | s_mid
        · rw [h_inner] at h_exec; cases h_exec
        · rw [h_inner] at h_exec
          have h_inner_pres :=
            bignumExecFuel_preserves_reg_aux registry fuel ct r h_ct
              s s_mid h_inner
          have h_tail_pres :=
            bignumExecFuel_preserves_reg_aux registry (fuel + 1) rest r h_tail
              s_mid s' h_exec
          rw [h_tail_pres, h_inner_pres]
      · rw [if_neg hc] at h_exec
        rcases h_inner : bignumExecFuel registry fuel ce s with _ | s_mid
        · rw [h_inner] at h_exec; cases h_exec
        · rw [h_inner] at h_exec
          have h_inner_pres :=
            bignumExecFuel_preserves_reg_aux registry fuel ce r h_ce
              s s_mid h_inner
          have h_tail_pres :=
            bignumExecFuel_preserves_reg_aux registry (fuel + 1) rest r h_tail
              s_mid s' h_exec
          rw [h_tail_pres, h_inner_pres]
  | fuel + 1, .Cfor v range body :: rest, h_pres, s, s', h_exec =>
    rw [InstrR.regWritesRec_cons_iff] at h_pres
    obtain ⟨h_head, h_tail⟩ := h_pres
    -- regWritesRec (Cfor v _ body) = v.var.vname :: listRegWrites body
    simp only [InstrR.regWritesRec, List.mem_cons, not_or] at h_head
    obtain ⟨h_neq, h_body⟩ := h_head
    have h_body' : ∀ j ∈ body, j.preservesRegRec r := by
      rw [InstrR.listRegWrites_eq_listMem] at h_body; exact h_body
    have h_unroll_pres :
        ∀ i ∈ unrollFor v range body, i.preservesRegRec r :=
      unrollFor_preservesRegRec v range body r h_neq h_body'
    -- Combined preservation for `unrollFor v range body ++ rest`
    have h_combined :
        r ∉ InstrR.regWritesRec.listRegWrites
          (unrollFor v range body ++ rest) := by
      rw [InstrR.listRegWrites_eq_listMem]
      intro j hj
      rw [List.mem_append] at hj
      rcases hj with hj | hj
      · exact h_unroll_pres j hj
      · rw [InstrR.listRegWrites_eq_listMem] at h_tail
        exact h_tail j hj
    simp only [bignumExecFuel] at h_exec
    exact bignumExecFuel_preserves_reg_aux registry fuel
      (unrollFor v range body ++ rest) r h_combined s s' h_exec
  | fuel + 1, .Cwhile cb cond ca :: rest, h_pres, s, s', h_exec =>
    rw [InstrR.regWritesRec_cons_iff] at h_pres
    obtain ⟨h_head, h_tail⟩ := h_pres
    -- regWritesRec (Cwhile cb _ ca) = listRegWrites cb ++ listRegWrites ca
    simp only [InstrR.regWritesRec, List.mem_append, not_or] at h_head
    obtain ⟨h_cb, h_ca⟩ := h_head
    simp only [bignumExecFuel] at h_exec
    -- Build preservation for the unfolded body.
    have h_oneIter :
        r ∉ InstrR.regWritesRec.listRegWrites
          ((cb ++ [.Cif cond (ca ++ [.Cwhile cb cond ca]) []]) ++ rest) := by
      rw [InstrR.listRegWrites_eq_listMem]
      intro j hj
      rw [List.mem_append] at hj
      rcases hj with hj | hj
      · -- j ∈ cb ++ [Cif ...]
        rw [List.mem_append, List.mem_singleton] at hj
        rcases hj with hj | rfl
        · -- j ∈ cb
          rw [InstrR.listRegWrites_eq_listMem] at h_cb
          exact h_cb j hj
        · -- j = Cif cond (ca ++ [Cwhile cb cond ca]) []
          show r ∉ InstrR.regWritesRec
            (.Cif cond (ca ++ [.Cwhile cb cond ca]) [])
          simp only [InstrR.regWritesRec, List.mem_append, not_or,
                     InstrR.regWritesRec.listRegWrites]
          refine ⟨?_, by intro h; cases h⟩
          -- Need: r ∉ listRegWrites (ca ++ [Cwhile cb cond ca])
          rw [InstrR.listRegWrites_eq_listMem]
          intro k hk
          rw [List.mem_append, List.mem_singleton] at hk
          rcases hk with hk | rfl
          · rw [InstrR.listRegWrites_eq_listMem] at h_ca
            exact h_ca k hk
          · -- k = Cwhile cb cond ca
            show r ∉ InstrR.regWritesRec (.Cwhile cb cond ca)
            simp only [InstrR.regWritesRec, List.mem_append, not_or]
            exact ⟨h_cb, h_ca⟩
      · -- j ∈ rest
        rw [InstrR.listRegWrites_eq_listMem] at h_tail
        exact h_tail j hj
    exact bignumExecFuel_preserves_reg_aux registry fuel
      ((cb ++ [.Cif cond (ca ++ [.Cwhile cb cond ca]) []]) ++ rest)
      r h_oneIter s s' h_exec
  | fuel + 1, .Ccall ii lvs fn args :: rest, h_pres, s, s', h_exec =>
    rw [InstrR.regWritesRec_cons_iff] at h_pres
    obtain ⟨h_head, h_tail⟩ := h_pres
    simp only [bignumExecFuel] at h_exec
    rcases h_reg : registry fn.name with _ | calleeFd
    · rw [h_reg] at h_exec; cases h_exec
    · rw [h_reg] at h_exec
      simp only at h_exec
      rcases h_args : args.mapM (evalPExpr s) with _ | argValues
      · rw [h_args] at h_exec; cases h_exec
      · rw [h_args] at h_exec
        simp only at h_exec
        -- Cases on the callee execution result directly via `match` in h_exec.
        split at h_exec
        · -- callee returned none
          cases h_exec
        · -- callee returned some calleeFinal — case-split on the void check
          rename_i calleeFinal _h_callee
          split at h_exec
          · -- lvs.isEmpty: caller regs unchanged
            rename_i h_void
            have h_ih :=
              bignumExecFuel_preserves_reg_aux registry (fuel + 1) rest r h_tail
                { s with mem := calleeFinal.mem } s' h_exec
            show s'.regs r = s.regs r
            rw [h_ih]
          · -- non-void: bind callee results into caller LVals, continue.
            -- `regWritesRec` covers exactly the `Lvar` names of `lvs`, so
            -- `bindResults` leaves `r` unchanged.
            simp only [InstrR.regWritesRec] at h_head
            split at h_exec
            · -- bindResults failed
              cases h_exec
            · rename_i sBound h_bind
              have h_bound : sBound.regs r = s.regs r :=
                bindResults_preserves_reg calleeFinal lvs calleeFd.results
                  { regs := s.regs, mem := calleeFinal.mem } sBound r h_bind h_head
              have h_ih :=
                bignumExecFuel_preserves_reg_aux registry (fuel + 1) rest r h_tail
                  sBound s' h_exec
              show s'.regs r = s.regs r
              rw [h_ih, h_bound]
  termination_by (fuel, is.length)
  decreasing_by
    all_goals
      simp_wf
      first
        | (apply Prod.Lex.right; simp)
        | (apply Prod.Lex.left; simp)
        | omega

theorem bignumExecFuel_preserves_reg
    (registry : BignumRegistry) (fuel : Nat) (is : List InstrR) (r : String)
    (h_pres : ∀ i ∈ is, i.preservesRegRec r)
    (s s' : BignumState)
    (h_exec : bignumExecFuel registry fuel is s = some s') :
    s'.regs r = s.regs r := by
  -- Convert per-instruction preservation to listRegWrites form.
  have h_pres_list : r ∉ InstrR.regWritesRec.listRegWrites is := by
    rw [InstrR.listRegWrites_eq_listMem]
    intro j hj; exact h_pres j hj
  exact bignumExecFuel_preserves_reg_aux registry fuel is r h_pres_list s s' h_exec

/-! ## §5. Demo: applying the combinator to `mulBody` chunks. -/

-- Verify decidability works on a concrete chunk via a small example.
example : ∀ i ∈ ([CatCrypt.Crypto.Jasmin.Examples.Curve25519CryptoptPort.mulxReg "rhi" "rlo" "rdx" "rsrc",
                  CatCrypt.Crypto.Jasmin.Examples.Curve25519CryptoptPort.movReg "r8" "rdx"] : List InstrR),
                 i.preservesReg "a" := by decide

-- Once `execInstrPlus_preserves_reg` is fully proven, every per-chunk
-- preservation lemma collapses to:
--
-- example (s s' : BignumState)
--     (h : bignumExecPlus mulBodyRealChunk1 s = some s') :
--     s'.regs "a" = s.regs "a" :=
--   bignumExecPlus_preserves_reg mulBodyRealChunk1 "a"
--     (by decide) s s' h
--
-- The `by decide` checks the `InstrR.preservesReg` predicate against
-- every instruction in the chunk's literal list. Since the predicate is
-- decidable (via the LVal.writesToReg instance) and all chunk
-- instructions are concrete, decide closes immediately.

/-! ## §6. CFG-aware memory-preservation chain (parallel to §4c).

Mirrors §4c but for memory through `bignumExecFuel`. The predicate is
`InstrR.preservesMemRec` (§1d above) which (a) traverses CFG sub-bodies
recursively, and (b) treats `Ccall` as a memory-writer because the
void-return Ccall arm copies callee memory back into the caller (lines
467-469 of `BignumExec.lean`). Hence the `Ccall` case in
`bignumExecFuel_preserves_mem` is a **contradiction** with `h_pres`,
unlike the register version where Ccall is a trivial preservation. -/

/-! ### §6.1 Helper: `execInstr_preserves_mem`.

The `bignumExecFuel` fall-through case calls `execInstr` (not
`execInstrPlus`), so we need an analogous mem-preservation lemma. Strict
subset of `execInstrPlus_preserves_mem` (no BZHI/SHRD/IMUL/SHLX/AND/TEST). -/

theorem execInstr_preserves_mem (i : InstrR) (s s' : BignumState)
    (h_pres : i.preservesMem)
    (h_exec : execInstr s i = some s') :
    s'.mem = s.mem := by
  unfold InstrR.preservesMem at h_pres
  cases i with
  | Cif cond ct ce => rw [execInstr_Cif_eq_none] at h_exec; cases h_exec
  | Cfor vi range body => rw [execInstr_Cfor_eq_none] at h_exec; cases h_exec
  | Cwhile cb cond ca => rw [execInstr_Cwhile_eq_none] at h_exec; cases h_exec
  | Ccall ii lvs fn args => rw [execInstr_Ccall_eq_none] at h_exec; cases h_exec
  | Cassgn lv tag ty e =>
    cases lv with
    | Lnone info lty =>
      rw [execInstr_Cassgn_Lnone_eq_none] at h_exec; cases h_exec
    | Laset aa ws x idx =>
      rw [execInstr_Cassgn_Laset_eq_none] at h_exec; cases h_exec
    | Lasub aa ws len x idx =>
      rw [execInstr_Cassgn_Lasub_eq_none] at h_exec; cases h_exec
    | Lvar v =>
      obtain ⟨w, rfl⟩ := execInstr_Cassgn_Lvar_form _ _ _ _ _ _ h_exec
      simp [setReg]
    | Lmem ws base off =>
      simp [InstrR.hasMemWrite, LVal.writesToMem] at h_pres
  | Copn lvs tag op args =>
    cases op with
    | Oasm o =>
      rw [execInstr_Copn_Oasm_reduce] at h_exec
      split at h_exec
      · -- SUB_64
        rename_i ea eb _h
        rcases h_a : evalPExpr s ea with _ | a
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_b : evalPExpr s eb with _ | b
          · rw [h_b] at h_exec; simp at h_exec
          · rw [h_b] at h_exec; simp at h_exec
            exact writeSubBundle_preserves_mem _ _ _ _ _ h_exec
      · -- SBB_64
        rename_i ea eb ec _h
        rcases h_a : evalPExpr s ea with _ | a
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_b : evalPExpr s eb with _ | b
          · rw [h_b] at h_exec; simp at h_exec
          · rw [h_b] at h_exec; simp at h_exec
            rcases h_c : evalPExpr s ec with _ | c
            · rw [h_c] at h_exec; simp at h_exec
            · rw [h_c] at h_exec; simp at h_exec
              exact writeSubBundle_preserves_mem _ _ _ _ _ h_exec
      · -- ADD_64
        rename_i ea eb _h
        rcases h_a : evalPExpr s ea with _ | a
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_b : evalPExpr s eb with _ | b
          · rw [h_b] at h_exec; simp at h_exec
          · rw [h_b] at h_exec; simp at h_exec
            exact writeSubBundle_preserves_mem _ _ _ _ _ h_exec
      · -- ADC_64
        rename_i ea eb ec _h
        rcases h_a : evalPExpr s ea with _ | a
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_b : evalPExpr s eb with _ | b
          · rw [h_b] at h_exec; simp at h_exec
          · rw [h_b] at h_exec; simp at h_exec
            rcases h_c : evalPExpr s ec with _ | c
            · rw [h_c] at h_exec; simp at h_exec
            · rw [h_c] at h_exec; simp at h_exec
              exact writeSubBundle_preserves_mem _ _ _ _ _ h_exec
      · -- MULX
        rename_i ea eb _h
        rcases h_a : evalPExpr s ea with _ | a
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_b : evalPExpr s eb with _ | b
          · rw [h_b] at h_exec; simp at h_exec
          · rw [h_b] at h_exec; simp at h_exec
            exact writeMulxBundle_preserves_mem _ _ _ _ _ h_exec
      · -- DIV_64
        rename_i eh el ed _h
        rcases h_a : evalPExpr s eh with _ | hi
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_b : evalPExpr s el with _ | lo
          · rw [h_b] at h_exec; simp at h_exec
          · rw [h_b] at h_exec; simp at h_exec
            rcases h_c : evalPExpr s ed with _ | d
            · rw [h_c] at h_exec; simp at h_exec
            · rw [h_c] at h_exec; simp at h_exec
              exact writeDivBundle_preserves_mem _ _ _ _ _ h_exec
      · -- ADCX
        rename_i ea eb ec _h
        rcases h_a : evalPExpr s ea with _ | a
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_b : evalPExpr s eb with _ | b
          · rw [h_b] at h_exec; simp at h_exec
          · rw [h_b] at h_exec; simp at h_exec
            rcases h_c : evalPExpr s ec with _ | c
            · rw [h_c] at h_exec; simp at h_exec
            · rw [h_c] at h_exec; simp at h_exec
              exact writeAdxBundle_preserves_mem _ _ _ _ _ h_exec
      · -- ADOX
        rename_i ea eb ec _h
        rcases h_a : evalPExpr s ea with _ | a
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_b : evalPExpr s eb with _ | b
          · rw [h_b] at h_exec; simp at h_exec
          · rw [h_b] at h_exec; simp at h_exec
            rcases h_c : evalPExpr s ec with _ | c
            · rw [h_c] at h_exec; simp at h_exec
            · rw [h_c] at h_exec; simp at h_exec
              exact writeAdxBundle_preserves_mem _ _ _ _ _ h_exec
      · -- XOR_64
        rename_i ea eb _h
        rcases h_a : evalPExpr s ea with _ | a
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_b : evalPExpr s eb with _ | b
          · rw [h_b] at h_exec; simp at h_exec
          · rw [h_b] at h_exec; simp at h_exec
            exact writeXorBundle_preserves_mem _ _ _ _ _ _ h_exec
      · -- (Shift, additive) SHL_64
        rename_i ea ek _h
        rcases h_a : evalPExpr s ea with _ | a
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_k : evalPExpr s ek with _ | k
          · rw [h_k] at h_exec; simp at h_exec
          · rw [h_k] at h_exec; simp at h_exec
            exact writeShiftBundle_preserves_mem _ _ _ _ h_exec
      · -- (Shift, additive) SHR_64
        rename_i ea ek _h
        rcases h_a : evalPExpr s ea with _ | a
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_k : evalPExpr s ek with _ | k
          · rw [h_k] at h_exec; simp at h_exec
          · rw [h_k] at h_exec; simp at h_exec
            exact writeShiftBundle_preserves_mem _ _ _ _ h_exec
      · -- (Shift, additive) SHLD_64
        rename_i edst esrc ek _h
        rcases h_a : evalPExpr s edst with _ | dst
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_b : evalPExpr s esrc with _ | src
          · rw [h_b] at h_exec; simp at h_exec
          · rw [h_b] at h_exec; simp at h_exec
            rcases h_k : evalPExpr s ek with _ | k
            · rw [h_k] at h_exec; simp at h_exec
            · rw [h_k] at h_exec; simp at h_exec
              exact writeShiftBundle_preserves_mem _ _ _ _ h_exec
      · -- (Shift, additive) SHRD_64
        rename_i edst esrc ek _h
        rcases h_a : evalPExpr s edst with _ | dst
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_b : evalPExpr s esrc with _ | src
          · rw [h_b] at h_exec; simp at h_exec
          · rw [h_b] at h_exec; simp at h_exec
            rcases h_k : evalPExpr s ek with _ | k
            · rw [h_k] at h_exec; simp at h_exec
            · rw [h_k] at h_exec; simp at h_exec
              exact writeShiftBundle_preserves_mem _ _ _ _ h_exec
      · -- (U32, additive) SUB_32
        rename_i ea eb _h
        rcases h_a : evalPExpr s ea with _ | a
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_b : evalPExpr s eb with _ | b
          · rw [h_b] at h_exec; simp at h_exec
          · rw [h_b] at h_exec; simp at h_exec
            exact writeSubBundle_preserves_mem _ _ _ _ _ h_exec
      · -- (U32, additive) ADD_32
        rename_i ea eb _h
        rcases h_a : evalPExpr s ea with _ | a
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_b : evalPExpr s eb with _ | b
          · rw [h_b] at h_exec; simp at h_exec
          · rw [h_b] at h_exec; simp at h_exec
            exact writeSubBundle_preserves_mem _ _ _ _ _ h_exec
      · -- (U32, additive) ADC_32
        rename_i ea eb ec _h
        rcases h_a : evalPExpr s ea with _ | a
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_b : evalPExpr s eb with _ | b
          · rw [h_b] at h_exec; simp at h_exec
          · rw [h_b] at h_exec; simp at h_exec
            rcases h_c : evalPExpr s ec with _ | c
            · rw [h_c] at h_exec; simp at h_exec
            · rw [h_c] at h_exec; simp at h_exec
              exact writeSubBundle_preserves_mem _ _ _ _ _ h_exec
      · -- (U32, additive) SBB_32
        rename_i ea eb ec _h
        rcases h_a : evalPExpr s ea with _ | a
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_b : evalPExpr s eb with _ | b
          · rw [h_b] at h_exec; simp at h_exec
          · rw [h_b] at h_exec; simp at h_exec
            rcases h_c : evalPExpr s ec with _ | c
            · rw [h_c] at h_exec; simp at h_exec
            · rw [h_c] at h_exec; simp at h_exec
              exact writeSubBundle_preserves_mem _ _ _ _ _ h_exec
      · -- (U32, additive) MULX_32
        rename_i ea eb _h
        rcases h_a : evalPExpr s ea with _ | a
        · rw [h_a] at h_exec; simp at h_exec
        · rw [h_a] at h_exec; simp at h_exec
          rcases h_b : evalPExpr s eb with _ | b
          · rw [h_b] at h_exec; simp at h_exec
          · rw [h_b] at h_exec; simp at h_exec
            exact writeMulxBundle_preserves_mem _ _ _ _ _ h_exec
      · simp at h_exec

/-! ### §6.2 Bridge: `preservesMemRec` ⇒ `preservesMem` for non-CFG shapes.

`InstrR.hasMemWrite` is the per-instruction predicate (no recursion through
CFG). `hasMemWriteRec` matches it on `Cassgn`/`Copn` and recurses on
`Cif`/`Cfor`/`Cwhile`/`Ccall`. So `preservesMemRec → preservesMem` when
`i` is not a CFG-shape. -/

private theorem InstrR.preservesMem_of_preservesMemRec (i : InstrR)
    (h : i.preservesMemRec) : i.preservesMem := by
  unfold InstrR.preservesMemRec at h
  unfold InstrR.preservesMem
  cases i with
  | Cassgn lv tag ty e =>
    simp only [InstrR.hasMemWriteRec, InstrR.hasMemWrite] at *
    exact h
  | Copn lvs tag op args => rfl
  | Cif _ _ _ => rfl
  | Cfor _ _ _ => rfl
  | Cwhile _ _ _ => rfl
  | Ccall _ _ _ _ =>
    -- hasMemWriteRec (Ccall ..) = true, contradicts `h : true = false`.
    simp only [InstrR.hasMemWriteRec] at h
    exact Bool.noConfusion h

/-! ### §6.3 Helper: `unrollFor` preserves mem recursively.

If every instruction in `body` preserves mem recursively, then every
instruction in `unrollFor v range body` does as well. The unroll produces
only `mkSetVarConst v _` (a `Cassgn (Lvar v) ...` — `writesToMem = false`,
so `hasMemWriteRec = false`) and instructions copied from `body`. -/

private theorem unrollFor_preservesMemRec
    (v : VarI) (range : Range) (body : List InstrR)
    (h_body : ∀ j ∈ body, j.preservesMemRec) :
    ∀ i ∈ unrollFor v range body, i.preservesMemRec := by
  intro i hi
  unfold unrollFor at hi
  cases hdir : range.dir with
  | UpTo =>
    rw [hdir] at hi
    simp only [List.mem_flatMap, List.mem_range] at hi
    obtain ⟨k, _hk, hi_in⟩ := hi
    rw [List.mem_cons] at hi_in
    rcases hi_in with hi_eq | hi_in
    · -- i = mkSetVarConst v (range.lo + k); writesToMem = false
      rw [hi_eq, mkSetVarConst_eq]
      show InstrR.hasMemWriteRec _ = false
      simp [InstrR.hasMemWriteRec, LVal.writesToMem]
    · exact h_body _ hi_in
  | DownTo =>
    rw [hdir] at hi
    simp only [List.mem_flatMap, List.mem_range] at hi
    obtain ⟨k, _hk, hi_in⟩ := hi
    rw [List.mem_cons] at hi_in
    rcases hi_in with hi_eq | hi_in
    · rw [hi_eq, mkSetVarConst_eq]
      show InstrR.hasMemWriteRec _ = false
      simp [InstrR.hasMemWriteRec, LVal.writesToMem]
    · exact h_body _ hi_in

/-! ### §6.4 Predicate splitting helpers. -/

private theorem InstrR.listHasMemWrite_cons_iff (i : InstrR)
    (is : List InstrR) :
    InstrR.hasMemWriteRec.listHasMemWrite (i :: is) = false ↔
      i.hasMemWriteRec = false ∧
        InstrR.hasMemWriteRec.listHasMemWrite is = false := by
  simp only [InstrR.hasMemWriteRec.listHasMemWrite, Bool.or_eq_false_iff]

private theorem InstrR.listHasMemWrite_eq_listMem (is : List InstrR) :
    InstrR.hasMemWriteRec.listHasMemWrite is = false ↔
      ∀ i ∈ is, i.preservesMemRec := by
  induction is with
  | nil =>
    constructor
    · intro _ j hj; cases hj
    · intro _; simp [InstrR.hasMemWriteRec.listHasMemWrite]
  | cons i is ih =>
    rw [InstrR.listHasMemWrite_cons_iff]
    constructor
    · rintro ⟨h1, h2⟩ j hj
      rw [List.mem_cons] at hj
      rcases hj with rfl | hj
      · exact h1
      · exact (ih.mp h2) j hj
    · intro h
      refine ⟨h i (by simp), ih.mpr fun j hj => h j ?_⟩
      rw [List.mem_cons]; right; exact hj

/-! ### §6.5 Main theorem: `bignumExecFuel_preserves_mem`.

Mirrors `bignumExecFuel_preserves_reg`'s 8-case structure. The `Ccall`
case is the inverse of the register version: there, Ccall trivially
preserves caller regs; here, Ccall is excluded by `h_pres` because
`hasMemWriteRec (Ccall ..) = true`, so it's a contradiction. -/

private theorem bignumExecFuel_preserves_mem_aux
    (registry : BignumRegistry) (fuel : Nat) (is : List InstrR)
    (h_pres : InstrR.hasMemWriteRec.listHasMemWrite is = false)
    (s s' : BignumState)
    (h_exec : bignumExecFuel registry fuel is s = some s') :
    s'.mem = s.mem := by
  match fuel, is, h_pres, s, s', h_exec with
  | 0, _, _, _, _, h_exec =>
    simp only [bignumExecFuel] at h_exec
    cases h_exec
  | _ + 1, [], _, s, s', h_exec =>
    simp only [bignumExecFuel, Option.some_inj] at h_exec
    rw [h_exec]
  | fuel + 1, .Cassgn lv tag ty e :: rest, h_pres, s, s', h_exec =>
    rw [InstrR.listHasMemWrite_cons_iff] at h_pres
    obtain ⟨h_head, h_tail⟩ := h_pres
    have h_head' : (InstrR.Cassgn lv tag ty e).preservesMem :=
      InstrR.preservesMem_of_preservesMemRec _ h_head
    simp only [bignumExecFuel] at h_exec
    rcases h_step : execInstr s (.Cassgn lv tag ty e) with _ | s_mid
    · rw [h_step] at h_exec; cases h_exec
    · rw [h_step] at h_exec
      have h_step_pres :=
        execInstr_preserves_mem _ _ _ h_head' h_step
      have h_ih :=
        bignumExecFuel_preserves_mem_aux registry (fuel + 1) rest h_tail
          s_mid s' h_exec
      rw [h_ih, h_step_pres]
  | fuel + 1, .Copn lvs tag op args :: rest, h_pres, s, s', h_exec =>
    rw [InstrR.listHasMemWrite_cons_iff] at h_pres
    obtain ⟨h_head, h_tail⟩ := h_pres
    have h_head' : (InstrR.Copn lvs tag op args).preservesMem :=
      InstrR.preservesMem_of_preservesMemRec _ h_head
    simp only [bignumExecFuel] at h_exec
    rcases h_step : execInstr s (.Copn lvs tag op args) with _ | s_mid
    · rw [h_step] at h_exec; cases h_exec
    · rw [h_step] at h_exec
      have h_step_pres :=
        execInstr_preserves_mem _ _ _ h_head' h_step
      have h_ih :=
        bignumExecFuel_preserves_mem_aux registry (fuel + 1) rest h_tail
          s_mid s' h_exec
      rw [h_ih, h_step_pres]
  | fuel + 1, .Cif cond ct ce :: rest, h_pres, s, s', h_exec =>
    rw [InstrR.listHasMemWrite_cons_iff] at h_pres
    obtain ⟨h_head, h_tail⟩ := h_pres
    -- hasMemWriteRec (Cif cond ct ce) = listHasMemWrite ct || listHasMemWrite ce
    simp only [InstrR.hasMemWriteRec, Bool.or_eq_false_iff] at h_head
    obtain ⟨h_ct, h_ce⟩ := h_head
    simp only [bignumExecFuel] at h_exec
    rcases h_cond : evalPExpr s cond with _ | condV
    · rw [h_cond] at h_exec; cases h_exec
    · rw [h_cond] at h_exec
      simp only at h_exec
      by_cases hc : condV != 0
      · rw [if_pos hc] at h_exec
        rcases h_inner : bignumExecFuel registry fuel ct s with _ | s_mid
        · rw [h_inner] at h_exec; cases h_exec
        · rw [h_inner] at h_exec
          have h_inner_pres :=
            bignumExecFuel_preserves_mem_aux registry fuel ct h_ct
              s s_mid h_inner
          have h_tail_pres :=
            bignumExecFuel_preserves_mem_aux registry (fuel + 1) rest h_tail
              s_mid s' h_exec
          rw [h_tail_pres, h_inner_pres]
      · rw [if_neg hc] at h_exec
        rcases h_inner : bignumExecFuel registry fuel ce s with _ | s_mid
        · rw [h_inner] at h_exec; cases h_exec
        · rw [h_inner] at h_exec
          have h_inner_pres :=
            bignumExecFuel_preserves_mem_aux registry fuel ce h_ce
              s s_mid h_inner
          have h_tail_pres :=
            bignumExecFuel_preserves_mem_aux registry (fuel + 1) rest h_tail
              s_mid s' h_exec
          rw [h_tail_pres, h_inner_pres]
  | fuel + 1, .Cfor v range body :: rest, h_pres, s, s', h_exec =>
    rw [InstrR.listHasMemWrite_cons_iff] at h_pres
    obtain ⟨h_head, h_tail⟩ := h_pres
    -- hasMemWriteRec (Cfor v _ body) = listHasMemWrite body
    simp only [InstrR.hasMemWriteRec] at h_head
    have h_body' : ∀ j ∈ body, j.preservesMemRec := by
      rw [InstrR.listHasMemWrite_eq_listMem] at h_head; exact h_head
    have h_unroll_pres :
        ∀ i ∈ unrollFor v range body, i.preservesMemRec :=
      unrollFor_preservesMemRec v range body h_body'
    have h_combined :
        InstrR.hasMemWriteRec.listHasMemWrite
          (unrollFor v range body ++ rest) = false := by
      rw [InstrR.listHasMemWrite_eq_listMem]
      intro j hj
      rw [List.mem_append] at hj
      rcases hj with hj | hj
      · exact h_unroll_pres j hj
      · rw [InstrR.listHasMemWrite_eq_listMem] at h_tail
        exact h_tail j hj
    simp only [bignumExecFuel] at h_exec
    exact bignumExecFuel_preserves_mem_aux registry fuel
      (unrollFor v range body ++ rest) h_combined s s' h_exec
  | fuel + 1, .Cwhile cb cond ca :: rest, h_pres, s, s', h_exec =>
    rw [InstrR.listHasMemWrite_cons_iff] at h_pres
    obtain ⟨h_head, h_tail⟩ := h_pres
    -- hasMemWriteRec (Cwhile cb _ ca) = listHasMemWrite cb || listHasMemWrite ca
    simp only [InstrR.hasMemWriteRec, Bool.or_eq_false_iff] at h_head
    obtain ⟨h_cb, h_ca⟩ := h_head
    simp only [bignumExecFuel] at h_exec
    have h_oneIter :
        InstrR.hasMemWriteRec.listHasMemWrite
          ((cb ++ [.Cif cond (ca ++ [.Cwhile cb cond ca]) []]) ++ rest)
            = false := by
      rw [InstrR.listHasMemWrite_eq_listMem]
      intro j hj
      rw [List.mem_append] at hj
      rcases hj with hj | hj
      · -- j ∈ cb ++ [Cif ...]
        rw [List.mem_append, List.mem_singleton] at hj
        rcases hj with hj | rfl
        · -- j ∈ cb
          rw [InstrR.listHasMemWrite_eq_listMem] at h_cb
          exact h_cb j hj
        · -- j = Cif cond (ca ++ [Cwhile cb cond ca]) []
          show InstrR.hasMemWriteRec
            (.Cif cond (ca ++ [.Cwhile cb cond ca]) []) = false
          show (InstrR.hasMemWriteRec.listHasMemWrite
                  (ca ++ [.Cwhile cb cond ca]) ||
                InstrR.hasMemWriteRec.listHasMemWrite []) = false
          rw [show InstrR.hasMemWriteRec.listHasMemWrite ([] : List InstrR)
                = false from rfl, Bool.or_false]
          rw [InstrR.listHasMemWrite_eq_listMem]
          intro k hk
          rw [List.mem_append, List.mem_singleton] at hk
          rcases hk with hk | rfl
          · rw [InstrR.listHasMemWrite_eq_listMem] at h_ca
            exact h_ca k hk
          · -- k = Cwhile cb cond ca
            show InstrR.hasMemWriteRec (.Cwhile cb cond ca) = false
            simp only [InstrR.hasMemWriteRec, Bool.or_eq_false_iff]
            exact ⟨h_cb, h_ca⟩
      · -- j ∈ rest
        rw [InstrR.listHasMemWrite_eq_listMem] at h_tail
        exact h_tail j hj
    exact bignumExecFuel_preserves_mem_aux registry fuel
      ((cb ++ [.Cif cond (ca ++ [.Cwhile cb cond ca]) []]) ++ rest)
      h_oneIter s s' h_exec
  | _ + 1, .Ccall ii lvs fn args :: rest, h_pres, _, _, _ =>
    -- Ccall is excluded by `h_pres`: hasMemWriteRec (Ccall ..) = true.
    rw [InstrR.listHasMemWrite_cons_iff] at h_pres
    obtain ⟨h_head, _⟩ := h_pres
    simp only [InstrR.hasMemWriteRec] at h_head
    exact Bool.noConfusion h_head
  termination_by (fuel, is.length)
  decreasing_by
    all_goals
      simp_wf
      first
        | (apply Prod.Lex.right; simp)
        | (apply Prod.Lex.left; simp)
        | omega

theorem bignumExecFuel_preserves_mem
    (registry : BignumRegistry) (fuel : Nat) (is : List InstrR)
    (h_pres : ∀ i ∈ is, i.preservesMemRec)
    (s s' : BignumState)
    (h_exec : bignumExecFuel registry fuel is s = some s') :
    s'.mem = s.mem := by
  have h_pres_list : InstrR.hasMemWriteRec.listHasMemWrite is = false := by
    rw [InstrR.listHasMemWrite_eq_listMem]
    intro j hj; exact h_pres j hj
  exact bignumExecFuel_preserves_mem_aux registry fuel is h_pres_list s s' h_exec

end CatCrypt.Tactics.PreservationCombinator
