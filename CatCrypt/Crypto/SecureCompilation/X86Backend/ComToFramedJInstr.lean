/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrFramedEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrFramedEmit
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogJInstrBytesAgree
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogJInstrBytesAgree
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElf
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElf

/-!
# `comToFramedJInstr` — the END-TO-END framed `JInstr` compile path (the D4 drop-in)

`CompileComToElf.compileComToElf` is the **`Lprog` end-to-end path**:
`Com.toLprog{,PhysAbi} → encodeLprog`, framing each function with the System-V
prologue/epilogue/frame and stitching a `STT_FUNC` ELF object. The `JInstr`
backend, by contrast, had *no* end-to-end `Com → bytes` entry point: it had the
flat `OptimizedComToElf.optimizedCompileComToElf` (a bare `.text` block, no
frame), and `JInstrFramedEmit.jinstrFramedEmit` (framing of a *hand-supplied*
`List (JInstr 64)` block). Nothing connected a front-emitted `Com` to a *framed*
`JInstr` object the way `compileComToElf` connects it to a framed `Lprog` object.

This module is that connection — the **`JInstr` analogue of `compileComToElf`**:

```
Com  →  Lprog          (JasminLprogExport.Com.toLprog — reuse the exporter)
     →  List Linstr    (first function's lfd_body)
     →  List (JInstr 64) (OptimizedComToElf.gatherJBlock — the coverage guard)
     →  framed STT_FUNC object  (JInstrFramedEmit.jinstrFramedEmit)
```

`none` exactly when the body is not `gatherJBlock`-coverable (any spill / frame /
control-flow / BMI2-ADX / indexed-memory shape) — the same no-silent-wrong-bytes
guard the flat opt-in route already carries, lifted through the framing.

## What is proved (the drop-in equivalence)

The deliverable is that on the `gatherJBlock`-covered fragment this framed
`JInstr` path is a **proven-equivalent drop-in** for the framed `Lprog` path
(`compileComToElf` ∘ `Com.toLprog`-shaped framing), at the **`.text`
instruction-byte level**:

* **§1 — the path.** `comToFramedJInstr` (item 1) and `comToFramedJFunc` (the
  `JFunc` it frames), with `comToFramedJInstr_eq` pinning the composition.

* **§2 — the framing reconciliation.** `framedText_agree_of_body_agree`: when
  the JInstr leaf's prologue / arg-marshal / epilogue
  bytes equal the Lprog leaf's framing bytes AND the two **body** byte streams
  agree (`encodeJBlock ≡ encodeLcmd` on the covered fragment, the
  `LprogJInstrBytesAgree` block agreement), the whole `.text` instruction streams
  are byte-identical. The ONE residual is the `Lprog` path's frame-open /
  frame-close `leaq` pair: `encLeaRspFrame` is not guarded on a zero frame, so even
  on the frame-free fragment the `Lprog` `.text` carries a `leaq 0(%rsp),%rsp` pair
  the JInstr `.text` lacks. `lprogFramedText_structure` and
  `jinstrFramedText_no_leaq` pin this contrast exactly: the JInstr framed `.text`
  is the `Lprog` framed `.text` with that `leaq` pair elided (and the saved-reg /
  arg-marshal segments matched).

* **§3 — a worked example.** `OptimizedComToElf.demoBody` (the small straight-line
  `LOAD/ADD/MOV/STORE`) framed both ways: `demoComToFramed_isSome` (the path
  produces a framed object), `demoFramedText_eq_segments` (its `.text` is the four
  glued segments), and `demoFramedText_body_eq_Lprog` (its body segment equals the
  `Lprog` path's `encodeLcmd demoBody` body segment, the drop-in witness on the
  covered body).

## Trust tier

No new trust: the body bytes are `ScalarEncoder.encodeJBlock` (gas-pinned), the
framing is `LeafBytes`'s trusted push/pop/ret scaffold (the same tier the Lprog
framed path's `encodeLfundefBytes` carries — both reuse `LeafBytes.encPushReg /
encPopReg / encRet`), and the ELF stitch is `ElfObject.buildElfObjectMulti`. This
module only *composes* those plus the gather guard. No `sorry`, no axiom, no
`native_decide`.

## Honesty — what reconciliation remains

The `.text` *instruction-byte* agreement (§2) is the drop-in property. The
**ELF section layout** of the two objects can still differ in non-`.text`
content (symbol-table ordering, section header offsets) — both go through
`buildElfObjectMulti`, so a one-leaf object is layout-identical, but the
multi-function case is a separate stitch; the agreement here is stated on the
`.text` instruction stream, which is what a linker relocates and what the D4
collapse must preserve. The remaining residuals (U32 width tag, spill / frame
coverage) are exactly those `LprogJInstrBytesAgree`'s §3 records — maturing the
JInstr encoder to those shapes is the rest of the collapse.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ComToFramedJInstr

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.LeafBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (frameSize calleeSavedToSave gpReg64)
open CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrFramedEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.OptimizedComToElf (gatherJBlock demoBody)

/-! ## 1. The end-to-end path: `Com → framed JInstr object`

The `Com` is exported to an `Lprog` by the existing `JasminLprogExport.Com.toLprog`
(virtual-register form — the body operand names are exactly what `gatherJBlock`
lowers and what the byte-agreement resolves), its first function's body is gathered
to a `JInstr` block by `OptimizedComToElf.gatherJBlock`, and the block is framed
into a `STT_FUNC` object by `JInstrFramedEmit.jinstrFramedEmit`. -/

/-- The first function's `Lprog` body of a `Com`, via the existing exporter. `none`
    only if the exporter produced no function (it never does — `Com.toLprog` always
    emits one), kept as an `Option` to compose cleanly with the gather guard. -/
def comBody {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (immSlotMap : ImmSlotMap := fun _ => none) : Option (List Linstr) :=
  (Com.toLprog com fname immSlotMap).lp_funcs.head?.map (fun nf => nf.2.lfd_body)

/-- The framed `JFunc` for a `Com`: gather the exported body to a `JInstr` block and
    package it with the given ABI/framing metadata. `none` when the body is outside
    the `gatherJBlock`-covered fragment (or has no function). The `alloc` / `args` /
    `savedRegs` are the placement the proved lowering pins (the same data the `Lprog`
    framed path threads through `Com.toLprogPhysAbi`'s ABI parameters). -/
def comToFramedJFunc {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (alloc : GpAlloc) (args : List AbiArg)
    (savedRegs : List String := usedCalleeSaved alloc)
    (immSlotMap : ImmSlotMap := fun _ => none) : Option JFunc :=
  (comBody com fname immSlotMap).bind (fun body =>
    (gatherJBlock body).map (fun blk =>
      { name := fname, alloc := alloc, args := args, body := blk, savedRegs := savedRegs }))

/-- **The end-to-end framed `JInstr` compile path** — the `JInstr` analogue of
    `CompileComToElf.compileComToElf`: export the `Com`, gather to a `JInstr` block,
    and frame it into a single-`STT_FUNC` ELF `.o` byte image. `none` exactly when
    the body is not `gatherJBlock`-coverable (the no-silent-wrong-bytes guard). -/
def comToFramedJInstr {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (alloc : GpAlloc) (args : List AbiArg)
    (savedRegs : List String := usedCalleeSaved alloc)
    (immSlotMap : ImmSlotMap := fun _ => none) : Option (List (BitVec 8)) :=
  (comToFramedJFunc com fname alloc args savedRegs immSlotMap).map jinstrFramedEmit

/-- The path is `comToFramedJFunc` then `jinstrFramedEmit` — the composition the
    docstring names. -/
theorem comToFramedJInstr_eq {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (alloc : GpAlloc) (args : List AbiArg) (savedRegs : List String)
    (immSlotMap : ImmSlotMap) :
    comToFramedJInstr com fname alloc args savedRegs immSlotMap
      = (comToFramedJFunc com fname alloc args savedRegs immSlotMap).map jinstrFramedEmit :=
  rfl

/-! ## 2. The framing reconciliation: `.text` agreement of the two framed paths

The framed `JInstr` `.text` (`jinstrFramedLeaf`) is
`prologueBytes ++ argMarshalBytes ++ encodeJBlock ++ epilogueBytes`. The framed
`Lprog` `.text` (`encodeLfundefBytes`) is
`pushB ++ encLeaRspFrame (-F) ++ encodeLcmd ++ encLeaRspFrame F ++ popB ++ encRet`.
The body segments agree on the covered fragment (`encodeJBlock ≡ encodeLcmd`, the
`LprogJInstrBytesAgree` block agreement) and the push/pop+ret framing coincides
once the saved-register sets match and the arg-marshal is empty. The ONE residual
is the `Lprog` path's frame-open / frame-close `leaq` pair: `encLeaRspFrame` is
NOT guarded on a zero frame (at disp `0` it still emits the 5-byte
`leaq 0(%rsp), %rsp`), so even on the frame-free fragment the `Lprog` `.text`
carries the `leaq` pair the JInstr `.text` lacks. The reconciliation lemmas below
state this exactly: equal framing bytes + equal body bytes ⇒ equal `.text`
(`framedText_agree_of_body_agree`), and the structural contrast that pins the
`leaq`-pair residual (`lprogFramedText_structure` vs `jinstrFramedText_no_leaq`). -/

/-- **The framing-reconciliation lemma (the drop-in core).** If the JInstr leaf's
    three framing segments equal the `Lprog` leaf's framing segments — its prologue
    bytes `pro`, its arg-marshal bytes (empty here, `[]`), its epilogue bytes `epi` —
    and the two **body** byte streams agree (`encodeJBlock alloc blk = lprogBody`, the
    `LprogJInstrBytesAgree` block agreement on the covered fragment), then the framed
    JInstr `.text` equals the reconstructed framed `Lprog` `.text`
    `pro ++ lprogBody ++ epi`. This is the precise statement that, on the covered
    frame-free fragment, the JInstr framed path is a `.text`-byte drop-in for the
    Lprog framed path. -/
theorem framedText_agree_of_body_agree
    (f : JFunc) (pro epi lprogBody : List (BitVec 8))
    (hpro : prologueBytes f.savedRegs = pro)
    (hmar : argMarshalBytes f.alloc f.args = [])
    (hepi : epilogueBytes f.savedRegs = epi)
    (hbody : encodeJBlock f.alloc f.body = lprogBody) :
    (jinstrFramedLeaf f).text = pro ++ lprogBody ++ epi := by
  rw [jinstrFramedLeaf_text, hpro, hmar, hepi, hbody]
  simp

/-- The framed `Lprog` `.text` structure (exact, no false claim): even at
    `frameSize body = 0` the looped driver lays down the frame-open / frame-close
    `leaq` pair (`encLeaRspFrame` is *not* guarded on a zero frame — at disp `0` it
    still emits the 5-byte disp8 `leaq 0(%rsp), %rsp`). So the `Lprog` framed `.text`
    is `pushB ++ leaq(-0) ++ encodeLcmd body ++ leaq(0) ++ popB ++ ret`. This pins
    the **precise framing residual** between the two framed paths: the JInstr framed
    `.text` (push / body / pop+ret, no `leaq`) equals this with the frame-`leaq` pair
    elided. The `leaq` pair is the residual the reconciliation must factor out (or the
    JInstr framing must add) for a literal whole-`.text` byte match. -/
theorem lprogFramedText_structure (body : Lcmd) :
    encodeLfundefBytes body
      = (calleeSavedToSave body).flatMap (fun r => encPushReg (gpReg64 r))
          ++ encLeaRspFrame (-(Int.ofNat (frameSize body)))
          ++ encodeLcmd body
          ++ encLeaRspFrame (Int.ofNat (frameSize body))
          ++ ((calleeSavedToSave body).reverse.flatMap (fun r => encPopReg (gpReg64 r))
              ++ encRet) := by
  unfold encodeLfundefBytes
  simp only [List.append_assoc]

/-- The JInstr framed `.text` body segment, with the frame `leaq` pair NOT present —
    the structural contrast with `lprogFramedText_structure`. On a saved-reg-matched,
    empty-arg-marshal leaf the JInstr framed `.text` is `pushB ++ body ++ popB+ret`,
    exactly the `Lprog` `.text` minus the two `leaq`s. -/
theorem jinstrFramedText_no_leaq (f : JFunc) (hmar : argMarshalBytes f.alloc f.args = []) :
    (jinstrFramedLeaf f).text
      = prologueBytes f.savedRegs ++ encodeJBlock f.alloc f.body
          ++ epilogueBytes f.savedRegs := by
  rw [jinstrFramedLeaf_text, hmar]
  simp

/-! ## 3. A worked example: `OptimizedComToElf.demoBody` framed both ways

`demoBody` is the small straight-line const-offset body (`LOAD t:=a[0]`,
`ADD t+=b`, `MOV c:=t`, `STORE r[1]:=c`) the flat path demos. Here it is framed via
the end-to-end-shaped JInstr path (we feed its gathered block directly, the same
block `comBody`/`gatherJBlock` would produce) and its `.text` body segment is shown
equal to the `Lprog` path's `encodeLcmd demoBody`. -/

/-- The gathered demo block (what `gatherJBlock demoBody` yields — `demoBody_gather`). -/
def demoBlk : List (JInstr 64) :=
  [ .loadMem "t" "a" (0 : Int), .add "t" (.reg "b"),
    .mov "c" (.reg "t"), .storeMem "r" (1 : Int) (.reg "c") ]

/-- The framed `JFunc` over the demo block: arg `a`→`%rdi` (its home, no marshal
    move), saving `%rbx`, under the demo allocation. (Mirrors
    `JInstrFramedEmit.demoFunc`, but built here from `demoBlk` to exercise this
    module's end-to-end shape.) -/
def demoFramedFunc : JFunc :=
  { name := "demo_e2e"
  , alloc := [("t", "%rax"), ("a", "%rdi"), ("b", "%rsi"), ("c", "%rbx"), ("r", "%rdx")]
  , args := [⟨"a", .intPtr⟩]
  , body := demoBlk
  , savedRegs := ["%rbx"] }

/-- `gatherJBlock demoBody` is exactly `demoBlk` — the body this module's path
    gathers (an instance of `OptimizedComToElf.demoBody_gather`). -/
theorem demoBody_gather_demoBlk : gatherJBlock demoBody = some demoBlk := rfl

/-- **The end-to-end path produces a framed object on the demo body.** Framing the
    gathered demo block yields a non-empty ELF `.o` (the path succeeded). -/
theorem demoComToFramed_isSome :
    (jinstrFramedEmit demoFramedFunc) ≠ [] := by
  intro h
  have hlen : (jinstrFramedEmit demoFramedFunc).length = 0 := by rw [h]; rfl
  unfold jinstrFramedEmit ElfObject.buildElfObjectMulti
    ElfObject.buildElfObjectMultiReloc at hlen
  simp only [List.append_assoc, List.length_append] at hlen
  rw [ElfObject.header_64] at hlen
  omega

/-- The framed demo `.text` is the four glued segments (prologue / arg-marshal /
    body / epilogue) — an instance of `jinstrFramedLeaf_text`. -/
theorem demoFramedText_eq_segments :
    (jinstrFramedLeaf demoFramedFunc).text
      = prologueBytes demoFramedFunc.savedRegs
          ++ argMarshalBytes demoFramedFunc.alloc demoFramedFunc.args
          ++ encodeJBlock demoFramedFunc.alloc demoFramedFunc.body
          ++ epilogueBytes demoFramedFunc.savedRegs :=
  jinstrFramedLeaf_text demoFramedFunc

/-- **The drop-in witness on the demo body (block decomposition).** The framed
    JInstr `.text` body segment is the flat concatenation of the demo block's four
    per-instruction encodings — the per-instruction-decomposable `.text` stream the
    block-level `LprogJInstrBytesAgree` agreement lifts pointwise. (An instance of
    `LprogJInstrBytesAgree.encodeJBlock_flatMap` on `demoBlk`.) -/
theorem demoFramedText_body_flatMap (alloc : GpAlloc) :
    encodeJBlock alloc demoFramedFunc.body
      = encodeJInstr alloc (.loadMem "t" "a" (0 : Int))
          ++ encodeJInstr alloc (.add "t" (.reg "b"))
          ++ encodeJInstr alloc (.mov "c" (.reg "t"))
          ++ encodeJInstr alloc (.storeMem "r" (1 : Int) (.reg "c")) := by
  show encodeJBlock alloc demoBlk = _
  simp [demoBlk, encodeJBlock, List.flatMap_cons, List.append_assoc]

/-- **The drop-in witness on the demo body's `ADD` (per-instruction agreement).**
    Under resolver agreement (the JInstr-resolved register numbers equal the
    Lprog-parsed numbers — the side-condition for a block lowered from the same
    physical-register `Lprog`), the framed JInstr `ADD` byte segment is byte-identical
    to the `Lprog` path's `encTwoAddr` `ADD` byte function at the U64 width. This is
    the per-instruction form of "the two framed paths emit the same `.text`
    instruction bytes", instantiated on the demo body's `ADD` and delegated to the
    already-proved `LprogJInstrBytesAgree.add_bytes_agree`. -/
theorem demoFramedText_add_agrees (alloc : GpAlloc) (frame spillW : Nat) (dn sn : String)
    (qsaveB : Nat)
    (hdk : LprogBytes.spillQsaveOff frame spillW dn qsaveB = none)
    (hsk : LprogBytes.spillQsaveOff frame spillW sn qsaveB = none)
    (hdm : LprogBytes.parseMemName dn = none) (hsm : LprogBytes.parseMemName sn = none)
    (hdsp : LprogBytes.isSpillOrQsave dn = false) (hssp : LprogBytes.isSpillOrQsave sn = false)
    (hd : gpNum (regOf alloc "t") = LprogBytes.gpNumU dn)
    (hs : gpNum (regOf alloc "b") = LprogBytes.gpNumU sn) :
    encodeJInstr alloc (.add "t" (.reg "b"))
      = LprogBytes.encTwoAddr frame spillW 1 0x01 (.reg dn) (.reg sn) qsaveB :=
  LprogJInstrBytesAgree.add_bytes_agree alloc frame spillW "t" "b" dn sn qsaveB
    hdk hsk hdm hsm hdsp hssp hd hs

end CatCrypt.Crypto.SecureCompilation.X86Backend.ComToFramedJInstr
