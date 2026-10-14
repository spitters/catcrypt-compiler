/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.LprogIsaSubset
public import CatCrypt.Crypto.SecureCompilation.VIR.IsaAsmSim
public import CatCrypt.Crypto.SecureCompilation.X86Backend.X86AsmSim
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGen
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLinkReloc
public import CatCrypt.Crypto.SecureCompilation.CT.Leakage

@[expose] public section

set_option autoImplicit false

/-!
# The back-end record of an instruction set

The back end of an instruction set `I : Isa` beside its data and step: the machine, the
assembly simulation, the instruction forms the lowering emits, the encodability of a body,
and the link check of a call of a linked function. The laws that tie these together and the
laws of the step and of a symbolic companion are `Prop` structures over an instance.

## Main definitions

* `opdIsMem`, `immSigned`, `IsaData.operandsOK`: the memory operands, the signed reading of
  an immediate, and the operand forms of an instruction at an instruction set (memory only
  at `memOperand`, immediates within `immFits`, `fixedOperand` respected).
* `Isa.CoreOn`: on an instruction of a fragment `S`, the step is `coreStep`.
* `Isa.RenameEquiv`: the step commutes with a renaming of register names that fixes a list
  of names, over a renaming of instructions and a relation of renamed states.
* `X86Isa.IsaSym.CopyLaw`: the symbolic step of a copy is the assignment, with no guard.
* `X86Isa.IsaSym.GuardFacts`: the symbolic decisions of the loop guard and of the first
  branch of the zero-trip guard are the non-zero test of the counter.
* `IsaBackend`: the machine, the source semantics and its assembly simulation, the
  instruction forms `legal`, the encodability `encodable`, the callees, the link check
  `link` and the call distance `callDist`.
* `IsaBackend.Laws`: legal bodies are encodable and, under a structural predicate, in the
  gate of the assembly simulation; encodable bodies within `callRange` pass the link check.
* `IsaBackend.CtSim`: the decoded bytes of a gated body that passes a leak check are
  constant time.
* `x86LinkSym`, `x86LinkB`: the symbol map and the checks of the x86 relocating encoder.
* `x86Backend`: the x86 back end.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.CT

/-! ## Operand forms -/

/-- Whether an operand names memory: an array element, a register-indexed element, a spill
    slot `k.N`, a save slot `qsave.*` or a cell `mem.*`. -/
def opdIsMem : LOperand → Bool
  | .reg n => "k.".isPrefixOf n || "qsave.".isPrefixOf n || "mem.".isPrefixOf n
  | .arr _ _ => true
  | .arrIdx _ _ _ => true
  | .imm _ => false

/-- The immediate `v` read as a signed 64-bit integer. -/
def immSigned (v : Nat) : Int :=
  if v < 2 ^ 63 then (v : Int) else (v : Int) - 2 ^ 64

/-- **The operand forms of an instruction at an instruction set**: every operand of an
    `Lopn dsts opn srcs` at position `k` of `dsts ++ srcs`, at the mnemonic base `b` of
    `opn`, is memory only when `I.memOperand b k`, an immediate `v` only when
    `I.immFits b k (immSigned v)`, and a register equal to `r` when `I.fixedOperand b k` is
    `some r`. Every other instruction passes. -/
def IsaData.operandsOK (I : IsaData) : LinstrR → Bool
  | .Lopn dsts opn srcs =>
      let b := stripWidthTag opn
      (dsts ++ srcs).zipIdx.all fun (o, k) =>
        (!opdIsMem o || I.memOperand b k)
          && (match o with
              | .imm v => I.immFits b k (immSigned v)
              | _ => true)
          && (match I.fixedOperand b k, o with
              | some r, .reg n => n == r
              | _, _ => true)
  | _ => true

/-! ## Laws of the step -/

/-- **The step on the ISA-neutral fragment**: on every instruction of the fragment `S`, the
    step of `I` is `coreStep`. -/
structure Isa.CoreOn (I : Isa) (S : LinstrRM → Bool) : Prop where
  /-- On an instruction of `S` the step is `coreStep`. -/
  step_core : ∀ (P : LprogM) (i : LinstrRM) (s : LstateMF), S i = true →
    I.step P i s = coreStep P i s

/-- **The step commutes with a renaming of register names** that fixes the names `fix`.
    The renaming of instructions `ren` and the relation `Ren σ s t` of a state `s` and its
    renaming `t` under `σ` are parameters: for an injective `σ` that fixes `fix`, a step
    from `s` is matched by a step of the renamed instruction from every renaming of `s`, to
    a renaming of the result. -/
structure Isa.RenameEquiv (I : Isa) (fix : List String)
    (ren : (String → String) → LinstrRM → LinstrRM)
    (Ren : (String → String) → LstateMF → LstateMF → Prop) : Prop where
  /-- A step from `s` is matched by a step of the renamed instruction from a renaming of
      `s`, to a renaming of the result. -/
  step_ren : ∀ (σ : String → String), Function.Injective σ → (∀ r ∈ fix, σ r = r) →
    ∀ (P : LprogM) (i : LinstrRM) (s t s' : LstateMF), Ren σ s t → I.step P i s = some s' →
    ∃ t', I.step P (ren σ i) t = some t' ∧ Ren σ s' t'

end CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV

/-! ## Laws of a symbolic companion -/

/-- **The symbolic step of a copy is the assignment.** At a copy mnemonic `m` of the
    instruction set, the symbolic step of `Lopn [d] m [s]` on register names sets `d` to the
    symbolic word of `s`, with no guard. A frame slot is a register name, so a slot load and
    a slot store are such copies. -/
structure IsaSym.CopyLaw {I : Isa} (T : IsaSym I) : Prop where
  /-- The symbolic step of a copy at a copy mnemonic is the assignment, with no guard. -/
  copy : ∀ (opn m : String), I.copyMnemonic opn = some m → ∀ (d s : String) (tag : MemTag)
    (ss : SSt), T.symStep (.Lopn [.reg d] m [.reg s], tag) ss = .ok (ss.setR d (ss.regs s)) []

/-- **The symbolic decisions of the guards are the counter tests.** For a typing `tag` of
    instructions: the loop guard on `ctr` is a list `pre` followed by a branch on `c` to
    `top`, and after the symbolic run of `pre` the decision of `c` has the value of the
    non-zero test of `ctr`; at a branch of the zero-trip guard with no branch before it, the
    decision of a branch to the exit label `endL` has the value of the zero test of `ctr`,
    and that of a branch to the loop label `top` the value of the non-zero test. -/
structure IsaSym.GuardFacts {I : Isa} (T : IsaSym I) : Prop where
  /-- The decision of the back edge is the non-zero test of the counter. -/
  loop : ∀ (ctr : String) (top : LLabel) (pre : List LinstrR) (c : LOperand),
    I.loopGuard ctr top = pre ++ [.Lcond c top] →
    ∀ (tag : LinstrR → MemTag) (ss ss' : SSt) (gs : List SG),
      T.symRun (pre.map fun i => (i, tag i)) ss = .ok ss' gs →
      ∀ (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O Z : Bool), AllG V A C O gs →
        (T.symDec ss' c).ev V A C O Z = (SDec.nz (ss.regs ctr)).ev V A C O Z
  /-- The decision of the first branch of the zero-trip guard, to the exit label, is the
      zero test of the counter. -/
  zeroTrip_exit : ∀ (ctr : String) (top endL : LLabel) (pre post : List LinstrR)
    (c : LOperand), top ≠ endL →
    I.zeroTripGuard ctr top endL = pre ++ .Lcond c endL :: post →
    (∀ i ∈ pre, ∀ c' l', i ≠ .Lcond c' l') →
    ∀ (tag : LinstrR → MemTag) (ss ss' : SSt) (gs : List SG),
      T.symRun (pre.map fun i => (i, tag i)) ss = .ok ss' gs →
      ∀ (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O Z : Bool), AllG V A C O gs →
        (T.symDec ss' c).ev V A C O Z = !(SDec.nz (ss.regs ctr)).ev V A C O Z
  /-- The decision of the first branch of the zero-trip guard, to the loop label, is the
      non-zero test of the counter. -/
  zeroTrip_enter : ∀ (ctr : String) (top endL : LLabel) (pre post : List LinstrR)
    (c : LOperand), top ≠ endL →
    I.zeroTripGuard ctr top endL = pre ++ .Lcond c top :: post →
    (∀ i ∈ pre, ∀ c' l', i ≠ .Lcond c' l') →
    ∀ (tag : LinstrR → MemTag) (ss ss' : SSt) (gs : List SG),
      T.symRun (pre.map fun i => (i, tag i)) ss = .ok ss' gs →
      ∀ (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O Z : Bool), AllG V A C O gs →
        (T.symDec ss' c).ev V A C O Z = (SDec.nz (ss.regs ctr)).ev V A C O Z

end CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa

namespace CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.CT

/-! ## The back-end record -/

/-- **The back end of an instruction set** `I`: the machine `M`; the source semantics `src`
    of its assembly simulation, with the body `toBody` of an `Lcmd`, and the assembly
    simulation `asm`; the instruction forms `legal body i` the lowering emits; the
    encodability `encodable` of a body; the type `Callee` of a linked function, the checks
    `link` of a call of a callee from a body, and the distance in bytes `callDist` from a
    call site of a body to the code of the callee. -/
structure IsaBackend (I : Isa) : Type 1 where
  /-- The machine level. -/
  M : IsaMachine
  /-- The source semantics of the assembly simulation. -/
  src : SrcSem
  /-- The body of the source semantics of an `Lcmd`. -/
  toBody : Lcmd → src.Body
  /-- The assembly simulation. -/
  asm : AsmSim src M
  /-- Whether an instruction of a body has a form the lowering emits. -/
  legal : Lcmd → LinstrR → Bool
  /-- Whether a body has an encoding. -/
  encodable : Lcmd → Bool
  /-- The data of a linked function. -/
  Callee : Type
  /-- The checks of a call of a callee from a body. -/
  link : Callee → Lcmd → Bool
  /-- The distance in bytes from a call site of a body to the code of the callee. -/
  callDist : Callee → Lcmd → Nat

namespace IsaBackend

variable {I : Isa} (B : IsaBackend I)

/-- **The laws of a back end** at the export data `D` and the structural predicate `Shape`
    on bodies (return last, the placement of the guards): a body whose instructions are
    legal is encodable, and when it also satisfies `Shape` it is in the gate of the assembly
    simulation; an encodable body whose call distance to a callee is below `D.callRange`
    passes the link check. -/
structure Laws (D : IsaExportData) (Shape : Lcmd → Prop) : Prop where
  /-- A body whose instructions are legal is encodable. -/
  encodable_of_legal : ∀ body : Lcmd, (∀ i ∈ body, B.legal body i.li_i = true) →
    B.encodable body = true
  /-- A body of the structural shape whose instructions are legal is in the gate. -/
  gate_of_legal : ∀ body : Lcmd, Shape body → (∀ i ∈ body, B.legal body i.li_i = true) →
    B.asm.gate (B.toBody body) = true
  /-- An encodable body within the call range passes the link check. -/
  link_of_encodable : ∀ (c : B.Callee) (body : Lcmd), B.encodable body = true →
    B.callDist c body < D.callRange → B.link c body = true

/-- **Constant time of the decoded bytes** at the side condition `ok` of the machine
    operations: every decoding of the bytes of a gated body that passes the leak check
    `LeakOk` is constant time for the public relation `Pub body`. The leak check is the one
    that reads `I.leaksOperands` on the bases the body runs with secret operands. -/
structure CtSim (ok : B.M.MState → B.M.Op → Prop) (LeakOk : Lcmd → Prop)
    (Pub : Lcmd → B.M.MState → B.M.MState → Prop) : Prop where
  /-- The decoded bytes of a gated body that passes the leak check are constant time. -/
  ct : ∀ body : Lcmd, B.asm.gate (B.toBody body) = true → LeakOk body →
    ∀ prog, B.M.decode (B.asm.encode (B.toBody body)) = some prog →
      ConstantTimeRel (Pub body) (fun s t => ∃ s', B.M.RunL ok prog 0 s t s')

end IsaBackend

/-! ## The x86 back end -/

/-- The symbol map of the x86 relocating encoder for a call of the function `name` from
    the printed body `b`: `name` sits at the byte after the function of `b`, at that length
    less the prologue; every other symbol is unmapped. -/
def x86LinkSym (name : String) (b : Lcmd) : String → Option Int := fun g =>
  if g = name then
    some (Int.ofNat (X86Backend.LprogBytes.encodeLfundefBytesReloc (fun _ => none) b).length
      - Int.ofNat (X86Backend.LprogBytes.prologueLen b))
  else none

/-- **The checks of the x86 relocating encoder** on the printed body `b` of a caller of the
    function `name` with code `code`: the code is nonempty; the instructions of `b` have
    shapes (`DecodeGen.shapesOf`); and the items `LprogBytesLinkReloc.fundefItemsRelocL` of
    `b` at the shapes and the symbol map `x86LinkSym` pass
    `LprogBytesLinkReloc.branchOKReloc` at the byte length of the function and denote a
    program (`LprogBytesLinkReloc.expectedReloc`). -/
def x86LinkB (name : String) (code : List (BitVec 8)) (b : Lcmd) : Bool :=
  !code.isEmpty &&
    match X86Backend.DecodeGen.shapesOf (X86Backend.LprogBytesDecode.Params.ofBody b) b with
    | none => false
    | some ds =>
        let items := X86Backend.LprogBytesLinkReloc.fundefItemsRelocL (x86LinkSym name b)
          (X86Backend.LprogBytesDecode.Params.ofBody b) b ds
        let L := (X86Backend.LprogBytes.encodeLfundefBytesReloc (x86LinkSym name b) b).length
        X86Backend.LprogBytesLinkReloc.branchOKReloc items
            (X86Backend.LprogBytesDecode.decCount items) L 0 items
          && (X86Backend.LprogBytesLinkReloc.expectedReloc items
            (X86Backend.LprogBytesDecode.decCount items) L items).isSome

/-- **The x86 back end**: the machine `x86Mach` and the assembly simulation `x86AsmSim` of
    the class `printedAddrWB` at the regime `doitm`, on the address semantics of printed
    bodies; the operand forms `operandsOK` at the x86 data; the encodability
    `encodableLcmd`; a callee as its symbol and code, the checks `x86LinkB`, and the byte
    length of the function of the caller as call distance. -/
def x86Backend : IsaBackend X86Backend.X86Isa.x86Isa where
  M := X86Backend.X86Isa.x86Mach .doitm
  src := X86Backend.X86AsmSim.x86AddrSem X86Backend.DecodePrintedAddrW.SafeW
  toBody := id
  asm := X86Backend.X86AsmSim.x86AsmSim .doitm
  legal := fun _ i => X86Backend.X86Isa.x86Isa.toIsaData.operandsOK i
  encodable := X86Backend.LprogBytes.encodableLcmd
  Callee := String × List (BitVec 8)
  link := fun c b => x86LinkB c.1 c.2 b
  callDist := fun c b =>
    (X86Backend.LprogBytes.encodeLfundefBytesReloc (x86LinkSym c.1 b) b).length

theorem x86Backend_asm : x86Backend.asm = X86Backend.X86AsmSim.x86AsmSim .doitm := rfl

theorem x86Backend_encodable : x86Backend.encodable = X86Backend.LprogBytes.encodableLcmd :=
  rfl

theorem x86Backend_legal (body : Lcmd) (i : LinstrR) :
    x86Backend.legal body i = X86Backend.X86Isa.x86Isa.toIsaData.operandsOK i := rfl

end CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
