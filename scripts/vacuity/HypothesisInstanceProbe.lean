/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulMulCarrySel
import CatCrypt.Crypto.SecureCompilation.Algebraic.Ed25519PointAddEmit
import CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath

/-!
# Evaluator for the decidable side conditions of the whole-function faithfulness theorem

`scripts/hypothesis-instance-gate.sh` runs this file with `lake lean` and reads the
`RESULT` rows it prints. Each row counts, over one shipped program, how many
bindings satisfy one side condition of
`X86Backend.ToLprogFaithfulMulCarrySel.toLprogPhysAbi_faithful_uniformMCS`.

The theorem is conditional on `hcd : CoverDataMCS body (bodyPhysTable body) nArgs
com d bs`. `CoverDataMCS` is an inductive over the `Com`, one constructor per
binding, and each constructor carries side conditions on the register allocation
that the constructor's binding structure records. Those conditions are equalities
and disequalities between strings produced by `physRename`, so on a fixed program
each is a computation. A `Prop`-level hypothesis that nothing evaluates can hold
for no binding of any shipped program while the theorem stays green, which is the
state this evaluator measures.

## The conditions, and why each is decidable on a fixed program

Write `ρ = physRename body (bodyPhysTable body)` for the logical-to-physical
register renaming of one body.

* `hcol` (the `var` and `var64` arms): `ρ (resolveVarName d nArgs a0) = ρ (regName d)`,
  the two-address collapse — the allocator placed the binding's first source and
  its destination on one physical register. At the head at depth `d` the two names
  are the head's first source operand and its destination, so the condition is a
  string equality between two `ρ` images.
* The `varMov` and `var64Mov` arms carry no collapse condition; their binding
  structure `BinopMovBinding` requires `ρ nDst ≠ ρ nS0`, `nSrc ≠ nDst`, and that
  the leading move does not place two spill slots in one instruction
  (`LOperand.isSpill`). All three are computations on the head.
* `hinj` (every binding structure of the fragment): `∀ m, ρ m = ρ nDst → m = nDst`.
  The quantifier is over all strings and the condition is still decidable, because
  `ρ` factors through `nameSlot body`, whose range is `{0, …, (bodyNames body).length}`
  and whose last value is the image of every name the body does not mention.
  Checking `bodyNames body` together with one name absent from it therefore decides
  the quantifier.
* The cover fixes one width for the whole binding list, and the exporter targets a
  64-bit state, so a head whose mnemonic carries no `:64` tag is outside the
  binding list the cover data ranges over. `hwidth64` counts the tagged heads.

`decide` does not reach any of this: `physLiveData` routes through
`List.mergeSort`, whose well-founded recursion does not reduce in the kernel. The
measurement is an evaluation, printed for a shell gate to read, rather than a
proof obligation.

## Main definitions

* `HeadFacts`: the decidable facts about one emitted head — the mnemonic class,
  the width tag, the collapse condition, the mov-arm conditions, and injectivity
  of the renaming at the destination.
* `headsOf`: the binding-head list of a `Com` at the exporter's own parameters
  (`nArgs = Γ.length`, argument names `argName`, empty immediate map, initial
  depth `nArgs`), which is the `body` the theorem's `hbody` names.
* `measure`: the `RESULT` and `INFO` rows for one registered instance.
* `main`: the three registered instances of
  `scripts/vacuity/hypothesis-instances.tsv`.
-/

set_option maxRecDepth 10000

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulNary
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulSpill

namespace HypothesisInstanceProbe

/-- The theorem whose side conditions the rows below count. -/
def theoremName : String :=
  "CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulMulCarrySel." ++
    "toLprogPhysAbi_faithful_uniformMCS"

/-- The mnemonics `opToLinstrR` emits for the `regArith` binops the collapse
    condition applies to (`binOpName` on the non-shift operators). -/
def binopMnems : List String := ["ADD", "SUB", "MUL", "AND", "OR", "XOR"]

/-- The mnemonics of the ops `CoverDataMCS` has a constructor for: the binops,
    `regConst` (`MOV`), `mulhi` (`MULXHI`), the two carry ops (`ADCX`, `ADCXHI`)
    and `select` (`CMOV`). -/
def fragmentMnems : List String := binopMnems ++ ["MOV", "MULXHI", "ADCX", "ADCXHI", "CMOV"]

/-- The mnemonic of an emitted head. -/
def opnOf : Linstr → Option String
  | ⟨_, .Lopn _ o _⟩ => some o
  | _ => none

/-- The destination register name of an emitted head with one register
    destination. -/
def dstOf : Linstr → Option String
  | ⟨_, .Lopn [.reg d] _ _⟩ => some d
  | _ => none

/-- The register-operand source names of an emitted head, in order. -/
def srcRegs : Linstr → List String
  | ⟨_, .Lopn _ _ srcs⟩ => srcs.filterMap (fun s => match s with | .reg n => some n | _ => none)
  | _ => []

/-- The decidable facts about one emitted head. -/
structure HeadFacts where
  /-- The head's mnemonic, width tag included. -/
  opn : String
  /-- The mnemonic with the `:64` width tag removed. -/
  base : String
  /-- Whether the head is a `regArith` binop, the case the collapse condition
      applies to. -/
  isBinop : Bool
  /-- Whether the head's op has a `CoverDataMCS` constructor. -/
  inFragment : Bool
  /-- Whether the mnemonic carries the `:64` width tag. -/
  tagged : Bool
  /-- The two-address collapse `ρ src0 = ρ dst` (the `hcol` of the `var` arms). -/
  collapse : Bool
  /-- The decidable conditions of the mov arms: the destination is not on the
      first source's register, the second source is not the destination, and the
      leading move carries at most one spill operand. -/
  movArm : Bool
  /-- The destination is the only name the renaming sends to its physical
      register (the `hinj` every binding structure carries). -/
  inj : Bool

/-- The facts of one head, against the body's renaming. `imgs` is the list of
    `ρ`-images of the body's names and `freshImg` the image of a name the body
    does not mention. -/
def factsOf (body : Lcmd) (tbl : Array Nat) (imgs : List String) (freshImg : String)
    (i : Linstr) : Option HeadFacts := do
  let opn ← opnOf i
  let dst ← dstOf i
  let base := stripWidthTag opn
  let srcs := srcRegs i
  let ρ := physRename body tbl
  let pdst := ρ dst
  let collapse := match srcs with
    | s0 :: _ => ρ s0 == pdst
    | [] => false
  let movArm := match srcs with
    | s0 :: s1 :: _ =>
        ρ s0 != pdst && s1 != dst
          && !((LOperand.reg pdst).isSpill && (LOperand.reg (ρ s0)).isSpill)
    | _ => false
  return { opn := opn
           base := base
           isBinop := binopMnems.contains base
           inFragment := fragmentMnems.contains base
           tagged := hasSuffix opn ":64"
           collapse := collapse
           movArm := movArm
           inj := imgs.countP (fun p => p == pdst) == 1 && pdst != freshImg }

/-- The binding-head list of a `Com` at the parameters `comToLfundef` exports it
    with: `nArgs = Γ.length` arguments named by `argName`, no immediate map, and
    the initial depth `nArgs`. This is the `body` of the theorem's `hbody`. -/
def headsOf {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t) : Lcmd :=
  bindingHeads Γ.length argName (fun _ => none) com Γ.length

/-- A `RESULT` row: the theorem, the side condition, the instance, the number of
    bindings satisfying it, and the number of bindings it applies to. -/
def result (inst hyp : String) (sat total : Nat) : IO Unit :=
  IO.println s!"RESULT\t{theoremName}\t{hyp}\t{inst}\t{sat}\t{total}"

/-- An `INFO` row: a measurement that decides nothing, carried so the gate's
    output states what the program is. -/
def info (inst key value : String) : IO Unit :=
  IO.println s!"INFO\t{inst}\t{key}\t{value}"

/-- The rows for one registered instance. -/
def measure {Γ : Ctxt jasminDialect} {t : JasminTy}
    (inst : String) (com : Com jasminDialect Γ t) : IO Unit := do
  let body := headsOf com
  let tbl := bodyPhysTable body
  let names := bodyNames body
  let fresh := if names.contains "?absent" then "?absent'" else "?absent"
  let imgs := names.map (physRename body tbl)
  let freshImg := physRename body tbl fresh
  let facts := body.filterMap (factsOf body tbl imgs freshImg)
  let binops := facts.filter (·.isBinop)
  let heads := facts.length
  -- The arms of `CoverDataMCS` a binding can be built by, as far as the
  -- allocation conditions decide it: the collapse arm, the mov arm, and the
  -- conjunction that any arm needs.
  result inst "hcol" (binops.countP (·.collapse)) binops.length
  result inst "mov_arm" (binops.countP (·.movArm)) binops.length
  result inst "hinj" (facts.countP (·.inj)) heads
  result inst "hwidth64" (facts.countP (·.tagged)) heads
  result inst "cover_arm"
    (facts.countP (fun f => f.inFragment && f.tagged && f.inj
      && (!f.isBinop || f.collapse || f.movArm))) heads
  info inst "names" (toString names.length)
  info inst "heads" (toString heads)
  info inst "outside_fragment" (toString (facts.countP (fun f => !f.inFragment)))
  info inst "mnemonics" (String.intercalate ","
    ((facts.map (·.opn)).eraseDups.take 24))

def main : IO Unit := do
  IO.println "PROBE\thypothesis-instance evaluator"
  measure "CatCrypt.Crypto.SecureCompilation.Algebraic.Ed25519PointAdd.pointAddCom"
    CatCrypt.Crypto.SecureCompilation.Algebraic.Ed25519PointAdd.pointAddCom
  measure "CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath.fieldAddCom"
    CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath.fieldAddCom
  measure "CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath.fieldCondSub251Com"
    CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath.fieldCondSub251Com
  IO.println "PROBE\tend"

end HypothesisInstanceProbe

#eval HypothesisInstanceProbe.main
