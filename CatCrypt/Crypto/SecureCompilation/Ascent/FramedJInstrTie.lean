/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.ComToArithBlock
public import CatCrypt.Crypto.SecureCompilation.Ascent.BytesToDialectJoin
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ComToFramedJInstr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull6

/-!
# The denotation carried by a framed `JInstr` body

Two compile paths take a `Com jasminDialect` to a framed `JInstr` body. This
module states what each one's body instructions compute.

## The virtual-register path

`Com.toLprog` names a fresh virtual register per operation and surrounds the
arithmetic with no ABI scaffolding, so the block gathered from its body is the
source program's operations and nothing else.

`ComToFramedJInstr.comToFramedJFunc` gathers that body through
`OptimizedComToElf.gatherJBlock`, which covers the two-address `"ADD"` / `"MOV"`
forms of a hand-written `Lcmd` rather than the three-address `"ADD:64"` /
`"MUL:64"` forms the exporter emits, and which also rejects the terminal `Lret`.
`List.mapM` turns either rejection into `none` for the whole block, so that entry
is `none` on every program (`comToFramedJFunc_eq_none`,
`comToFramedJInstr_eq_none`), and the framing results in its own module are about
hand-supplied `JFunc`s.

`comToFramedJFunc6` is the same path over `GatherImmForms.gatherJBlock6`, the
gather the shipped `compileComToElfJInstrFull6` entry uses: it covers the
exporter's forms and filters the `Lret` the framing supplies itself. It lives here
rather than beside `comToFramedJFunc` because `GatherImmForms` reaches that module
through `FramingReconcile`. `framedFunc6_denote` reads the source denotation out
of its body: when the block parses and elaborates to an `ArithBlock` whose
compiled program is the source `Com`, the output register after `runBlock` holds
that program's value.

## The physical-ABI path

`CompileComToElfJInstrFull.physBodyOf` takes the body of `Com.toLprogPhysAbi` —
the register-allocated export — and `GatherImmForms.gatherJBlock6` filters the
`Lret` out before lowering. This is the body generator of the shipped
`compileComToElfJInstrFull6` entry.

`coreSegment_denote` ties a segment of such a body to the source program: when a
block splits as `pre ++ core ++ post`, the middle segment parses and elaborates
to an `ArithBlock` whose compiled program is the source `Com`, the state
correspondence holds after `pre`, and `post` leaves the output register alone,
then reading that register after the whole run gives the `Com`'s denotation.
`serializedCore_denote` is the same statement with the block pinned to the
serializer's output.

## The fragment boundary

The physical-ABI export reuses registers: on `comBlock2` the destination of the
second recovered operation is the register the second input arrives in
(`shipped_stream_collides`), so `FreshFor` — the hypothesis both
`lowerBlock_tie` and `liftBlock_runBlock` carry — does not hold of that body.
`comBlock2_core_denote` therefore states the concrete agreement as a machine
register read at a concrete entry state rather than through the tie.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter (GpAlloc AbiArg usedCalleeSaved)
open CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrFramedEmit (JFunc jinstrFramedEmit)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ComToFramedJInstr
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtended
open CatCrypt.Crypto.SecureCompilation.X86Backend.OptimizedComToElf (gatherJBlock)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull (physBodyOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.GatherImmForms (gatherJBlock6)

/-! ## 1. The virtual-register path -/

/-- The exported body of a program ends with an `Lret`, which the framing supplies
    itself and which only `gatherJBlock6` filters out. -/
theorem comToBody_snoc_lret (nArgs : Nat) (argNames : Nat → String)
    (ims : ImmSlotMap) : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    (c : Com jasminDialect Γ t) → (d : Nat) →
    ∃ pfx : Lcmd, comToBody nArgs argNames ims c d = pfx ++ [⟨0, .Lret⟩]
  | _, _, .ret _, _ => ⟨[], rfl⟩
  | _, _, .var e body, d => by
      obtain ⟨pfx, hp⟩ := comToBody_snoc_lret nArgs argNames ims body (d + 1)
      exact ⟨⟨0, opToLinstrR e.op (regName d) (exprArgs d nArgs argNames ims e)⟩ :: pfx, by
        simp [comToBody, hp]⟩

/-- The body `comBody` extracts is the exported walk of the program. -/
theorem comBody_eq {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String) (ims : ImmSlotMap) :
    comBody com fname ims = some (comToBody Γ.length argName ims com Γ.length) := rfl

/-- The gather of an exported body is `none`: its terminal `Lret` is outside the
    `lowerLinstrExt` fragment, and `List.mapM` propagates that to the whole block. -/
theorem gatherJBlock_comBody {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String) (ims : ImmSlotMap)
    (body : List Linstr) (h : comBody com fname ims = some body) :
    gatherJBlock body = none := by
  rw [comBody_eq] at h
  obtain ⟨pfx, hp⟩ := comToBody_snoc_lret Γ.length argName ims com Γ.length
  cases h
  rw [hp]
  unfold gatherJBlock
  rw [show (pfx ++ [(⟨0, .Lret⟩ : Linstr)]).mapM lowerLinstrExtL = none by
    simp [List.mapM_append, show lowerLinstrExtL ⟨0, .Lret⟩ = none from rfl]]
  rfl

/-- The framed `JFunc` of `ComToFramedJInstr` is `none` on every program. -/
theorem comToFramedJFunc_eq_none {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String) (alloc : GpAlloc)
    (args : List AbiArg) (savedRegs : List String) (ims : ImmSlotMap) :
    comToFramedJFunc com fname alloc args savedRegs ims = none := by
  have h := gatherJBlock_comBody com fname ims _ (comBody_eq com fname ims)
  simp [comToFramedJFunc, comBody_eq, h]

/-- The framed `JInstr` byte image of `ComToFramedJInstr` is `none` on every
    program. -/
theorem comToFramedJInstr_eq_none {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String) (alloc : GpAlloc)
    (args : List AbiArg) (savedRegs : List String) (ims : ImmSlotMap) :
    comToFramedJInstr com fname alloc args savedRegs ims = none := by
  rw [comToFramedJInstr_eq, comToFramedJFunc_eq_none]
  rfl

/-- **The framed `JFunc` over the gather that covers the exporter's forms.** The
    same path as `comToFramedJFunc`, with `gatherJBlock6` in place of
    `gatherJBlock`. -/
def comToFramedJFunc6 {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (alloc : GpAlloc) (args : List AbiArg)
    (savedRegs : List String := usedCalleeSaved alloc)
    (ims : ImmSlotMap := fun _ => none) : Option JFunc :=
  (comBody com fname ims).bind (fun body =>
    (gatherJBlock6 body).map (fun blk =>
      { name := fname, alloc := alloc, args := args, body := blk,
        savedRegs := savedRegs }))

/-- The framed `JInstr` byte image over that gather. -/
def comToFramedJInstr6 {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (alloc : GpAlloc) (args : List AbiArg)
    (savedRegs : List String := usedCalleeSaved alloc)
    (ims : ImmSlotMap := fun _ => none) : Option (List (BitVec 8)) :=
  (comToFramedJFunc6 com fname alloc args savedRegs ims).map jinstrFramedEmit

/-- **The framed body carries the program's denotation.** When the framed `JFunc` of
    the virtual-register path exists and its instructions parse and elaborate to an
    `ArithBlock` whose compiled program is the source `c`, reading the block's output
    register after `runBlock` gives `c.denote V`.

    The virtual-register export binds a fresh name per operation, so no ABI
    scaffolding surrounds the block and the freshness hypothesis is about the
    exporter's own naming. -/
theorem framedFunc6_denote {Γ : Ctxt jasminDialect}
    (c : Com jasminDialect Γ (.reg 64)) (fname : String) (alloc : GpAlloc)
    (args : List AbiArg) (savedRegs : List String) (ims : ImmSlotMap)
    (f : JFunc) (hf : comToFramedJFunc6 c fname alloc args savedRegs ims = some f)
    (ops : List RawArith)
    (nm : RegMapG Γ) (find : String → Option (Ctxt.Var Γ (.reg 64)))
    (hfind : ∀ (v : Ctxt.Var Γ (.reg 64)) (r : String), find r = some v → nm v = r)
    (out : String) (ab : ArithBlock Γ)
    (hparse : parseBlock f.body = some ops) (helab : elabOps find ops out = some ab)
    (htoCom : ab.toCom = c)
    (s : JState 64) (V : Ctxt.Valuation Γ)
    (hinterp : JStateInterpG nm V s) (hfresh : FreshFor nm (dstStream ops))
    (hmem : BlockMemOk ab nm (dstStream ops) V s :=
      by first | trivial | simp [BlockMemOk]) :
    (comToFramedJFunc6 c fname alloc args savedRegs ims).map
        (fun f => (runBlock s f.body).get (outReg ab nm (dstStream ops)))
      = some (c.denote V) := by
  rw [hf, Option.map_some, ← htoCom]
  exact congrArg some
    (liftBlock_runBlock f.body ops nm find hfind out ab hparse helab s V hinterp
      hfresh hmem)

/-- The byte image of the framed path exists exactly when the framed `JFunc` does. -/
theorem comToFramedJInstr6_isSome {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (fname : String) (alloc : GpAlloc)
    (args : List AbiArg) (savedRegs : List String) (ims : ImmSlotMap) :
    (comToFramedJInstr6 c fname alloc args savedRegs ims).isSome
      = (comToFramedJFunc6 c fname alloc args savedRegs ims).isSome := by
  rw [comToFramedJInstr6]
  cases comToFramedJFunc6 c fname alloc args savedRegs ims <;> rfl

/-! ## 2. The segment tie -/

/-- **A machine block whose middle segment carries a program's denotation.** The
    block splits as `pre ++ core ++ post`; `core` parses to a list of recovered
    operations and elaborates to an `ArithBlock` whose compiled program is `c`;
    the state correspondence holds at the state `pre` leaves; the allocation is
    fresh for the recovered destinations; and `post` does not write the output
    register. Reading that register after the whole run gives `c.denote V`. -/
theorem coreSegment_denote {Γ : Ctxt jasminDialect}
    (c : Com jasminDialect Γ (.reg 64))
    (pre core post : List (JInstr 64)) (ops : List RawArith)
    (nm : RegMapG Γ) (find : String → Option (Ctxt.Var Γ (.reg 64)))
    (hfind : ∀ (v : Ctxt.Var Γ (.reg 64)) (r : String), find r = some v → nm v = r)
    (out : String) (ab : ArithBlock Γ)
    (hparse : parseBlock core = some ops) (helab : elabOps find ops out = some ab)
    (htoCom : ab.toCom = c)
    (s : JState 64) (V : Ctxt.Valuation Γ)
    (hinterp : JStateInterpG nm V (runBlock s pre))
    (hfresh : FreshFor nm (dstStream ops))
    (hpost : ∀ s' : JState 64,
      (runBlock s' post).get (outReg ab nm (dstStream ops))
        = s'.get (outReg ab nm (dstStream ops)))
    (hmem : BlockMemOk ab nm (dstStream ops) V (runBlock s pre) :=
      by first | trivial | simp [BlockMemOk]) :
    (runBlock s (pre ++ core ++ post)).get (outReg ab nm (dstStream ops))
      = c.denote V := by
  rw [runBlock_append, runBlock_append, hpost,
    liftBlock_runBlock core ops nm find hfind out ab hparse helab
      (runBlock s pre) V hinterp hfresh hmem, htoCom]

/-- **The serializer's body carries the program's denotation.** The same
    statement as `coreSegment_denote` with the block pinned to the body
    `compileComToElfJInstrFull6` emits for `c`: the physical-ABI export gathered
    by `gatherJBlock6`. -/
theorem serializedCore_denote {Γ : Ctxt jasminDialect}
    (c : Com jasminDialect Γ (.reg 64)) (fname : String)
    (pre core post : List (JInstr 64)) (ops : List RawArith)
    (hgather : gatherJBlock6 (physBodyOf c fname) = some (pre ++ core ++ post))
    (nm : RegMapG Γ) (find : String → Option (Ctxt.Var Γ (.reg 64)))
    (hfind : ∀ (v : Ctxt.Var Γ (.reg 64)) (r : String), find r = some v → nm v = r)
    (out : String) (ab : ArithBlock Γ)
    (hparse : parseBlock core = some ops) (helab : elabOps find ops out = some ab)
    (htoCom : ab.toCom = c)
    (s : JState 64) (V : Ctxt.Valuation Γ)
    (hinterp : JStateInterpG nm V (runBlock s pre))
    (hfresh : FreshFor nm (dstStream ops))
    (hpost : ∀ s' : JState 64,
      (runBlock s' post).get (outReg ab nm (dstStream ops))
        = s'.get (outReg ab nm (dstStream ops)))
    (hmem : BlockMemOk ab nm (dstStream ops) V (runBlock s pre) :=
      by first | trivial | simp [BlockMemOk]) :
    (gatherJBlock6 (physBodyOf c fname)).map
        (fun blk => (runBlock s blk).get (outReg ab nm (dstStream ops)))
      = some (c.denote V) := by
  rw [hgather, Option.map_some,
    coreSegment_denote c pre core post ops nm find hfind out ab hparse helab
      htoCom s V hinterp hfresh hpost hmem]

/-! ## 3. A two-operation program through the virtual-register path

The exported body of `comBlock2` is four instructions over the exporter's own
names: the two inputs arrive in `a1` and `a0`, the two results are bound to `r2`
and `r3`, and nothing surrounds them. So the recogniser reads the source program
back out of the whole body, and the freshness condition is about the exporter's
naming rather than about a register allocation. -/

/-- A name whose first character is not `'%'` is not a padding name. -/
theorem ne_padName_of_head (r : String) (c : Char) (rest : List Char)
    (hr : r.toList = c :: rest) (hc : c ≠ '%') (k : Nat) : r ≠ padName k :=
  ne_padName_of_toList r k (by rw [hr]; simp [hc])

/-- The body the virtual-register path gathers for the two-operation program.
    `regName` and `argName` build their names with `toString`, which does not reduce
    in the kernel, so the results below take the identification with the path's
    output as a hypothesis rather than proving it by `rfl`; the identification is
    settled by evaluating the gather, which is outside the kernel. -/
def framedBody2 : List (JInstr 64) :=
  [ .mov "r2" (.reg "a1"), .add "r2" (.reg "a0")
  , .mov "r3" (.reg "r2"), .imul "r3" (.reg "a1") ]

/-- The two operations the body parses to. -/
def framedOps2 : List RawArith :=
  [⟨.add, "r2", "a1", "a0"⟩, ⟨.mul, "r3", "r2", "a1"⟩]

/-- The exporter's register map on the inputs of the two-operation program. -/
def nmV : RegMapG Δ2 := fun v =>
  match v with
  | .here => "a1"
  | .there .here => "a0"

/-- The name resolution inverse to `nmV`. -/
def findV : String → Option (Ctxt.Var Δ2 (.reg 64)) := fun r =>
  if r = "a1" then some dA else if r = "a0" then some dB else none

/-- `findV` and `nmV` invert on the two inputs. -/
theorem findV_nmV : ∀ (v : Ctxt.Var Δ2 (.reg 64)) (r : String),
    findV r = some v → nmV v = r := by
  intro v r h
  unfold findV at h
  split at h
  · next hr => subst hr; cases h; rfl
  · split at h
    · next hr => subst hr; cases h; rfl
    · exact absurd h (by simp)

/-- The body parses to the two operations. -/
theorem framedBody2_parse : parseBlock framedBody2 = some framedOps2 := rfl

/-- The parsed operations elaborate to the block the source program is
    recognised as. -/
theorem framedOps2_elab : elabOps findV framedOps2 "r3" = some block2 := rfl

/-- `r2` is not a padding name. -/
theorem r2_ne_padName (k : Nat) : ("r2" : String) ≠ padName k :=
  ne_padName_of_head _ 'r' ['2'] (by decide) (by decide) k

/-- `r3` is not a padding name. -/
theorem r3_ne_padName (k : Nat) : ("r3" : String) ≠ padName k :=
  ne_padName_of_head _ 'r' ['3'] (by decide) (by decide) k

/-- `a1` is not a padding name. -/
theorem a1_ne_padName (k : Nat) : ("a1" : String) ≠ padName k :=
  ne_padName_of_head _ 'a' ['1'] (by decide) (by decide) k

/-- `a0` is not a padding name. -/
theorem a0_ne_padName (k : Nat) : ("a0" : String) ≠ padName k :=
  ne_padName_of_head _ 'a' ['0'] (by decide) (by decide) k

/-- The exporter's allocation is fresh for the recovered destinations. -/
theorem framedOps2_fresh : FreshFor nmV (dstStream framedOps2) := by
  constructor
  · intro i j hij
    match i, j with
    | 0, 0 => exact absurd rfl hij
    | 0, 1 => exact by decide
    | 1, 0 => exact by decide
    | 1, 1 => exact absurd rfl hij
    | 0, j + 2 => exact r2_ne_padName j
    | 1, j + 2 => exact r3_ne_padName j
    | i + 2, 0 => exact fun hp => r2_ne_padName i hp.symm
    | i + 2, 1 => exact fun hp => r3_ne_padName i hp.symm
    | i + 2, j + 2 =>
        exact fun hp => hij (by
          rw [show dstStream framedOps2 (i + 2) = padName i from rfl,
            show dstStream framedOps2 (j + 2) = padName j from rfl] at hp
          rw [padName_inj hp])
  · intro i v
    match i, v with
    | 0, .here => exact by decide
    | 0, .there .here => exact by decide
    | 1, .here => exact by decide
    | 1, .there .here => exact by decide
    | i + 2, .here => exact fun hp => a1_ne_padName i hp.symm
    | i + 2, .there .here => exact fun hp => a0_ne_padName i hp.symm

/-- **The framed body of the two-operation program denotes it.** Under the
    identification of the path's body with `framedBody2`, reading the output register
    after running it gives the source program's value, for every machine state that
    carries the valuation in the exporter's argument registers. -/
theorem framedFunc2_denote
    (hbody : (comToFramedJFunc6 comBlock2 "f" [] []).map (·.body) = some framedBody2)
    (s : JState 64) (V : Ctxt.Valuation Δ2)
    (hinterp : JStateInterpG nmV V s) :
    (comToFramedJFunc6 comBlock2 "f" [] []).map
        (fun f => (runBlock s f.body).get "r3")
      = some (comBlock2.denote V) := by
  obtain ⟨f, hf, hfb⟩ := Option.map_eq_some_iff.mp hbody
  have h := framedFunc6_denote comBlock2 "f" [] [] (usedCalleeSaved [])
    (fun _ => none) f hf framedOps2 nmV findV findV_nmV "r3" block2
    (hfb ▸ framedBody2_parse) framedOps2_elab comBlock2_toCom s V hinterp
    framedOps2_fresh
  rwa [show outReg block2 nmV (dstStream framedOps2) = "r3" from rfl] at h

/-! ## 4. Non-vacuity

The body is a real machine block and running it gives a value. -/

/-- An entry state carrying the valuation `⟨7, 35⟩` in the exporter's argument
    registers. -/
def framedEntry2 : JState 64 :=
  { regs := fun r => if r = "a1" then 7 else if r = "a0" then 35 else 0 }

/-- The valuation `⟨7, 35⟩`. -/
def framedV2 : Ctxt.Valuation Δ2 :=
  .cons (7 : BitVec 64) (.cons (35 : BitVec 64) .nil)

/-- The entry state carries the valuation. -/
theorem framedEntry2_interp : JStateInterpG nmV framedV2 framedEntry2 := by
  intro v
  match v with
  | .here => rfl
  | .there .here => rfl

/-- Running the gathered body from that state leaves `(7 + 35) * 7 = 294` in
    `r3`. -/
theorem framedBody2_concrete :
    (runBlock framedEntry2 framedBody2).get "r3" = (294 : BitVec 64) := rfl

/-! ## 5. A two-operation program through the serializer's body

The three segments below are the shape a physical-ABI export takes: the
callee-saved registers spilled to the frame and the arguments reloaded, the
arithmetic, the restores. `comBlock2_serialized_denote` carries the
identification with the serializer's output on `comBlock2` as a hypothesis;
`physBodyOf` runs the register allocator and does not reduce in the kernel, so
that equation is not available as a proof. -/

/-- The segment before the arithmetic: the callee-saved spills, the argument
    marshalling move, and the two argument reloads. -/
def comBlock2Pre : List (JInstr 64) :=
  [ .storeMem "RSP" 56 (.reg "RDI"), .storeMem "RSP" 48 (.reg "RSI")
  , .storeMem "RSP" 40 (.reg "RBX"), .storeMem "RSP" 32 (.reg "RBP")
  , .storeMem "RSP" 24 (.reg "R12"), .storeMem "RSP" 16 (.reg "R13")
  , .storeMem "RSP" 8 (.reg "R14"), .storeMem "RSP" 0 (.reg "R15")
  , .mov "R14" (.reg "RSI")
  , .loadMem "RCX" "RSP" 56, .loadMem "RBX" "RSP" 48 ]

/-- The arithmetic segment: the two-address lowerings of the add and the
    multiply. -/
def comBlock2Core : List (JInstr 64) :=
  [ .mov "RAX" (.reg "RBX"), .add "RAX" (.reg "RCX")
  , .mov "RCX" (.reg "RAX"), .imul "RCX" (.reg "RBX") ]

/-- The segment after the arithmetic: the callee-saved restores. -/
def comBlock2Post : List (JInstr 64) :=
  [ .loadMem "RBX" "RSP" 40, .loadMem "RBP" "RSP" 32
  , .loadMem "R12" "RSP" 24, .loadMem "R13" "RSP" 16
  , .loadMem "R14" "RSP" 8, .loadMem "R15" "RSP" 0 ]

/-- The two operations the arithmetic segment parses to. -/
def comBlock2Ops : List RawArith :=
  [⟨.add, "RAX", "RBX", "RCX"⟩, ⟨.mul, "RCX", "RAX", "RBX"⟩]

/-- The register map of the two inputs in the physical-ABI body: the first input
    arrives in `%rbx`, the second in `%rcx`. -/
def comBlock2Nm : RegMapG Δ2 := fun v =>
  match v with
  | .here => "RBX"
  | .there .here => "RCX"

/-- The name resolution inverse to `comBlock2Nm` on the two inputs. -/
def comBlock2Find : String → Option (Ctxt.Var Δ2 (.reg 64)) := fun r =>
  if r = "RBX" then some dA else if r = "RCX" then some dB else none

/-- The arithmetic segment parses to the two operations. -/
theorem comBlock2Core_parse : parseBlock comBlock2Core = some comBlock2Ops := rfl

/-- The parsed operations elaborate to the block `comBlock2` is recognised
    as. -/
theorem comBlock2Ops_elab :
    elabOps comBlock2Find comBlock2Ops "RCX" = some block2 := rfl

/-- The elaborated block compiles back to the source program. -/
theorem comBlock2Ops_toCom : block2.toCom = comBlock2 := comBlock2_toCom

/-- The output register of the elaborated block under the body's register map
    and destination stream. -/
theorem comBlock2_outReg :
    outReg block2 comBlock2Nm (dstStream comBlock2Ops) = "RCX" := rfl

/-- **The destination stream collides with the register map.** The second
    recovered operation writes `%rcx`, the register the second input arrives in,
    so the allocation of this body is not fresh for the recovered
    destinations. -/
theorem shipped_stream_collides :
    dstStream comBlock2Ops 1 = comBlock2Nm dB := rfl

/-- The freshness hypothesis of `coreSegment_denote` fails for this body. -/
theorem comBlock2_not_freshFor :
    ¬ FreshFor comBlock2Nm (dstStream comBlock2Ops) :=
  fun h => h.2 1 dB shipped_stream_collides

/-- An entry state of the compiled function: the first input in `%rsi`, the
    second in `%rdi`, every other register zero. -/
def comBlock2Entry : JState 64 :=
  { regs := fun r => if r = "RSI" then 7 else if r = "RDI" then 35 else 0 }

/-- **The concrete agreement.** Running the three segments from the entry state
    leaves in `%rcx` the value the source program denotes on the inputs the
    entry state carries. -/
theorem comBlock2_core_denote :
    (runBlock comBlock2Entry (comBlock2Pre ++ comBlock2Core ++ comBlock2Post)).get "RCX"
      = comBlock2.denote (.cons (7 : BitVec 64) (.cons (35 : BitVec 64) .nil)) := rfl

/-- **The concrete agreement on the serializer's output.** Under the hypothesis
    that the serializer's body for `comBlock2` is the three segments, reading
    `%rcx` after running that body from the entry state gives the value the
    source program denotes. -/
theorem comBlock2_serialized_denote
    (hgather : gatherJBlock6 (physBodyOf comBlock2 "f")
      = some (comBlock2Pre ++ comBlock2Core ++ comBlock2Post)) :
    (gatherJBlock6 (physBodyOf comBlock2 "f")).map
        (fun blk => (runBlock comBlock2Entry blk).get "RCX")
      = some (comBlock2.denote (.cons (7 : BitVec 64) (.cons (35 : BitVec 64) .nil))) := by
  rw [hgather, Option.map_some]
  exact congrArg some comBlock2_core_denote

end CatCrypt.Crypto.SecureCompilation.Ascent
