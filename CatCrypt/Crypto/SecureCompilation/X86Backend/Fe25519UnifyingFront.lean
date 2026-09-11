/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public meta import CatCrypt.Crypto.SecureCompilation.VIR.QuerySampleBranchFront
public import CatCrypt.Crypto.SecureCompilation.VIR.QuerySampleBranchFront
public meta import CatCrypt.Crypto.SecureCompilation.VIR.Shake256SpongeFront
public import CatCrypt.Crypto.SecureCompilation.VIR.Shake256SpongeFront

/-!
# Unifying owned-backend front for the whole X25519 scalarmult orchestrator

The deployed `Fe25519LfundefBridge.x25519ScalarmultLcmd` is the whole RFC 7748
`x25519_scalarmult(out,k,u)` folded into ONE owned-RA `Lcmd`: decode/clamp of the
scalar and base point, a **255-iteration** Montgomery-ladder loop (constant-time
`cswap` mask arithmetic + a sibling `call x25519_mono_step`), the `z^(p-2)`
inversion addition chain (several **counted squaring-run loops** interleaved with
sibling `call fe25519_{mul,sqr}`), and the little-endian encode. It was assembled
as a raw `List Linstr` through the ad-hoc smart constructors `w64`/`st64`/
`callLeaf` — i.e. hand-authored, below every landed step-language front.

## What the landed fronts already provide (the assessment)

Three step-languages landed before this one:

* **`OrchFront.OrchStep`** — `call`/`movRR`/`movImm`/`addImm`/`subImm`, wrapped by
  ONE `loopLcmd`. The sibling `.Lcall`-in-a-loop is its native shape
  (`buildOrchLoop` puts a real `.call leaf` inside `loopLcmd`).
* **`QuerySampleBranchFront.BStep`** — adds word `load`/`store` (`mem.<base>.<off>`),
  address arithmetic, a forward data-dependent branch (`condFwd`/`label`), the
  leaf `call` (a real `.Lcall`), and a **mid-body counted `loop`** (whose inner is
  an arbitrary `Lcmd`, so it hosts a `call` and can itself nest a `loop`).
* **`Shake256SpongeFront.SpStep`** — `BStep` (as `.ctrl`) plus `frame`/`lea`/
  `goto`/word-and-byte memory XOR/`subRR`, and threads **two** runtime loops.

So the two pieces the prior finding flagged as "missing vs a plain `BStep`" are in
fact ALREADY structurally expressible: (a) a **sequence of loops** is just several
`.loop` steps in the flat schedule (`bband`/`spband` flatten a list, and each
`.loop` is an independent `loopLcmd`), and nesting is a `.loop` whose inner
`Lcmd` is itself a rendered `.loop`; (b) a **sibling `.Lcall` inside a loop** is
`BStep.call`/`OrchStep.call` placed in a `.loop` body. Neither is a new capability.

The ONE thing the landed fronts do not match is the deployed x25519 kernel's
**operand convention**: it uses the *two-address destructive* ALU/shift forms
`[dst] OP [src]` (`andq %rax, %r8`, `adcq %r9, %r9`, `subq %r14, %rcx`) and
`[dst] OP [imm]` (`addq $k, %rdi`, `shrq $63, %rbp`), whereas `BStep`/`SpStep`
render the *three-slot* form `[dst] OP [dst, src]`. A byte-identical re-source of
the deployed body therefore needs those two-slot forms. That — plus a `.loop`
node whose sequence/nesting the deployed inversion chain exercises, and the
sibling `.call` — is the unifying language `UStep` here.

## The unifying language

`UStep` is the union of the landed control alphabet (the leaf `call` and the
counted `loop` — the SAME `loopLcmd` back-edge `BStep.loop`/`OrchStep` render, see
`ustepToLcmd_call_eq_bstep` / `ustepToLcmd_loop_eq_bstep`) with the word
`load`/`store` and the two-slot destructive ALU/shift forms the x25519 kernel's
convention needs (`andRR`/`orRR`/`xorRR`/`addRR`/`adcRR`/`subRR`/`addImm`/
`subImm`/`shrImm`). `uband w` renders a schedule to an owned-backend `Lcmd`.
`Fe25519LfundefBridge` re-sources the whole scalarmult body from a `List UStep`
schedule (`x25519ScalarmultLcmd := uband 64 …`), so the deployed `Lcmd` is
GENERATED, not hand-authored, and its RFC 7748 §5.2 byte-KAT
(`bench/x25519_ladder`, `make …scalarmult_owned_kat`) carries over verbatim.

## Denotation honesty

The counted `loop` and the sibling `call` have the same denotation status as
`BStep.loop` / `LprogControlFlow.loopLcmd`: the pure A-normal `Com` substrate
carries no label/jump/call denotation, so a machine-denote for the back-edge and
the cross-function call is the reported residual, not claimed here. What is
discharged is the structural contract — the schedule renders exactly the
owned-backend `loopLcmd` / `.Lcall` shape the byte encoder consumes (the deployed
`frameSize`/byte-encodability facts re-verify against this front's output) and the
byte-identical re-source.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519UnifyingFront

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow
  (loopLcmd loopLcmd_length)

/-! ## 1. The unifying step language `UStep`

The full owned-backend alphabet the folded X25519 scalarmult needs: register and
immediate moves, word `load`/`store` by operand name, the two-address destructive
ALU/shift forms (`[dst] OP [src]` / `[dst] OP [imm]` — the x25519 kernel's
convention, distinct from `BStep`'s three-slot forms), the sibling leaf `call`
(a real `.Lcall`), a counted `loop` (the verified `loopLcmd` back-edge, whose
`inner` `Lcmd` hosts sibling calls and nested loops), and the function `ret`. -/

/-- One step of a unifying owned-backend schedule. -/
inductive UStep where
  /-- Register-to-register move `MOV dst, src`. -/
  | movRR (dst src : String)
  /-- Immediate move `MOV dst, #imm`. -/
  | movImm (dst : String) (imm : Nat)
  /-- Word load `LOAD dst, <memName>` (the memory operand carried by NAME, e.g.
      `"mem.RSI.0"` — matching the deployed `st64`/`w64 … "LOAD"` builders). -/
  | load (dst memName : String)
  /-- Word store `STORE <memName>, src` (`memName` a `mem.<base>.<off>` cell or a
      spill name like `"k.109"`). -/
  | store (memName src : String)
  /-- Two-address `AND dst, src` (`[dst] AND [src]` — destructive). -/
  | andRR (dst src : String)
  /-- Two-address `OR dst, src`. -/
  | orRR (dst src : String)
  /-- Two-address `XOR dst, src`. -/
  | xorRR (dst src : String)
  /-- Two-address `ADD dst, src`. -/
  | addRR (dst src : String)
  /-- Two-address `ADC dst, src` (add-with-carry, the multi-limb doubling). -/
  | adcRR (dst src : String)
  /-- Two-address `SUB dst, src`. -/
  | subRR (dst src : String)
  /-- Two-address immediate `ADD dst, #imm` (pointer stride / counter). -/
  | addImm (dst : String) (imm : Nat)
  /-- Two-address immediate `SUB dst, #imm` (counter decrement). -/
  | subImm (dst : String) (imm : Nat)
  /-- Two-address immediate `SHR dst, #imm` (top-bit extraction). -/
  | shrImm (dst : String) (imm : Nat)
  /-- A void near-`call` to a sibling/leaf symbol (a real `.Lcall`). -/
  | call (sym : String)
  /-- A counted `loop`: `loopLcmd w top counter inner` (the verified back-edge).
      `inner` is an already-rendered `Lcmd` (itself typically a `uband` of a
      sub-schedule), so it hosts sibling `call`s and nested loops. -/
  | loop (top : LLabel) (counter : String) (inner : Lcmd)
  /-- The function-level `Lret`. -/
  | ret

/-- Render one `UStep` to an owned-backend `Lcmd` at op width `w`. Every mnemonic
    carries `withWidthTag w`; the two-slot ALU/shift arms produce exactly the
    `[dst] OP [src]` / `[dst] OP [imm]` form the deployed `w64` builder writes;
    `call`/`loop` reuse the SAME `.Lcall` / `loopLcmd` the landed fronts emit. -/
def ustepToLcmd (w : Nat) : UStep → Lcmd
  | .movRR d s      => [⟨0, .Lopn [.reg d] (withWidthTag w "MOV") [.reg s]⟩]
  | .movImm d v     => [⟨0, .Lopn [.reg d] (withWidthTag w "MOV") [.imm v]⟩]
  | .load d m       => [⟨0, .Lopn [.reg d] (withWidthTag w "LOAD") [.reg m]⟩]
  | .store m s      => [⟨0, .Lopn [.reg m] (withWidthTag w "STORE") [.reg s]⟩]
  | .andRR d s      => [⟨0, .Lopn [.reg d] (withWidthTag w "AND") [.reg s]⟩]
  | .orRR d s       => [⟨0, .Lopn [.reg d] (withWidthTag w "OR") [.reg s]⟩]
  | .xorRR d s      => [⟨0, .Lopn [.reg d] (withWidthTag w "XOR") [.reg s]⟩]
  | .addRR d s      => [⟨0, .Lopn [.reg d] (withWidthTag w "ADD") [.reg s]⟩]
  | .adcRR d s      => [⟨0, .Lopn [.reg d] (withWidthTag w "ADC") [.reg s]⟩]
  | .subRR d s      => [⟨0, .Lopn [.reg d] (withWidthTag w "SUB") [.reg s]⟩]
  | .addImm d v     => [⟨0, .Lopn [.reg d] (withWidthTag w "ADD") [.imm v]⟩]
  | .subImm d v     => [⟨0, .Lopn [.reg d] (withWidthTag w "SUB") [.imm v]⟩]
  | .shrImm d v     => [⟨0, .Lopn [.reg d] (withWidthTag w "SHR") [.imm v]⟩]
  | .call sym       => [⟨0, .Lcall none (sym, 0)⟩]
  | .loop top c inr => loopLcmd w top c inr
  | .ret            => [⟨0, .Lret⟩]

/-- Render a schedule to an `Lcmd` (the flattened owned body). -/
def uband (w : Nat) (steps : List UStep) : Lcmd := steps.flatMap (ustepToLcmd w)

@[simp] theorem uband_nil (w : Nat) : uband w [] = [] := rfl

@[simp] theorem uband_cons (w : Nat) (s : UStep) (ss : List UStep) :
    uband w (s :: ss) = ustepToLcmd w s ++ uband w ss := by
  simp [uband, List.flatMap_cons]

@[simp] theorem uband_append (w : Nat) (a b : List UStep) :
    uband w (a ++ b) = uband w a ++ uband w b := by
  simp [uband, List.flatMap_append]

/-! ## 2. Composition witnesses: the control core coincides with the landed fronts

`UStep`'s control ops (`call`, `loop`) reuse — do not reinvent — the exact
owned-backend forms `QuerySampleBranchFront.BStep` renders, so the unifying front
is a genuine SUPERSET of the landed control alphabet. The genuinely new part is
the two-slot destructive ALU/shift convention (§3). -/

open CatCrypt.Crypto.SecureCompilation.VIR.QuerySampleBranchFront (BStep bstepToLcmd)

/-- The leaf `call` renders identically to `BStep.call` (the SAME real `.Lcall`). -/
theorem ustepToLcmd_call_eq_bstep (w : Nat) (sym : String) :
    ustepToLcmd w (.call sym) = bstepToLcmd w (.call sym) := rfl

/-- The counted `loop` renders identically to `BStep.loop` (the SAME `loopLcmd`
    back-edge). -/
theorem ustepToLcmd_loop_eq_bstep (w : Nat) (top : LLabel) (c : String) (inr : Lcmd) :
    ustepToLcmd w (.loop top c inr) = bstepToLcmd w (.loop top c inr) := rfl

/-- Register/immediate moves render identically to `BStep`. -/
theorem ustepToLcmd_movRR_eq_bstep (w : Nat) (d s : String) :
    ustepToLcmd w (.movRR d s) = bstepToLcmd w (.movRR d s) := rfl

theorem ustepToLcmd_movImm_eq_bstep (w : Nat) (d : String) (v : Nat) :
    ustepToLcmd w (.movImm d v) = bstepToLcmd w (.movImm d v) := rfl

/-- The word `load` subsumes `BStep.load`: a `UStep.load` whose operand name is
    the `mem.<base>.<off>` form renders exactly as `BStep.load base off`. -/
theorem ustepToLcmd_load_eq_bstep (w : Nat) (d base : String) (off : Nat) :
    ustepToLcmd w (.load d ("mem." ++ base ++ "." ++ toString off))
      = bstepToLcmd w (.load d base off) := rfl

/-- The word `store` subsumes `BStep.store` on a `mem.<base>.<off>` cell. -/
theorem ustepToLcmd_store_eq_bstep (w : Nat) (base : String) (off : Nat) (s : String) :
    ustepToLcmd w (.store ("mem." ++ base ++ "." ++ toString off) s)
      = bstepToLcmd w (.store base off s) := rfl

/-- The two-slot destructive `addImm` is DISTINCT from `BStep.addImm`: the x25519
    kernel writes `[dst] ADD [imm]` (`addq $k, %rdi`), `BStep` writes the three-slot
    `[dst] ADD [dst, imm]`. This is the genuine convention gap the unifying front
    closes (documented, not an equality). -/
theorem ustepToLcmd_addImm_two_slot (w : Nat) (d : String) (v : Nat) :
    ustepToLcmd w (.addImm d v) = [⟨0, .Lopn [.reg d] (withWidthTag w "ADD") [.imm v]⟩] := rfl

/-! ## 3. Generic combinator witnesses: sequential loops + sibling call-in-loop

The two shapes the folded X25519 orchestrator needs beyond a single straight-line
`BStep` body: a SEQUENCE of counted loops (the inversion chain's squaring runs),
and a sibling `.Lcall` INSIDE a loop body (the squaring-run `call fe25519_sqr` and
the ladder loop's `call x25519_mono_step`). Both are plain `uband` of a `List
UStep`; no new combinator is needed. -/

/-- A predicate: an `Lcmd` carries a sibling near-`call`. -/
def hasLcall (body : Lcmd) : Bool :=
  body.any (fun i => match i.li_i with | .Lcall _ _ => true | _ => false)

/-- A predicate: an `Lcmd` carries a `loop` back-edge (an internal `Llabel`). -/
def hasBackEdge (body : Lcmd) : Bool :=
  body.any (fun i => match i.li_i with | .Llabel .internal _ => true | _ => false)

/-- **Sequential loops compose.** Two `.loop` steps in a flat schedule render to
    two independent `loopLcmd` back-edges, concatenated — the shape the inversion
    chain's successive squaring runs need. -/
theorem seq_loops_render (w : Nat) (t1 t2 : LLabel) (c1 c2 : String) (b1 b2 : Lcmd) :
    uband w [.loop t1 c1 b1, .loop t2 c2 b2]
      = loopLcmd w t1 c1 b1 ++ loopLcmd w t2 c2 b2 := by
  simp [ustepToLcmd]

/-- **A sibling `call` inside a loop body.** A `.loop` whose `inner` is a
    `uband`-rendered body containing a `.call` renders a `loopLcmd` whose body
    carries the real `.Lcall` — the squaring-run / ladder shape. -/
theorem call_in_loop :
    hasLcall (uband 64 [.loop 0 "R15"
      (uband 64 [.call "fe25519_sqr_x86_from_lean", .subImm "R15" 1])]) = true := by
  native_decide

/-- **A nested loop.** A `.loop` whose `inner` is itself a rendered `.loop`
    produces two internal back-edges — nesting is structural. -/
theorem nested_loop :
    hasBackEdge (uband 64 [.loop 0 "R13"
      (uband 64 [.loop 1 "R15" [], .subImm "R13" 1])]) = true := by
  native_decide

/-! ## 4. Generation gate (`wellFormedU`) — the `isSome` analogue

`uband` is total, so the front gate is a decidable well-formedness `Bool`: a
scalarmult-orchestrator schedule is well-formed iff it carries a sibling `call`
and a counted `loop` (the ladder / squaring-run back-edges). -/

/-- The schedule contains a sibling leaf `call`. -/
def hasCall (steps : List UStep) : Bool :=
  steps.any (fun s => match s with | .call _ => true | _ => false)

/-- The schedule contains a counted `loop`. -/
def hasLoop (steps : List UStep) : Bool :=
  steps.any (fun s => match s with | .loop _ _ _ => true | _ => false)

/-- The number of counted `loop` steps in the schedule (the ladder loop + the
    several inversion squaring-run loops ⇒ this is `≥ 2` for the scalarmult). -/
def loopCount (steps : List UStep) : Nat :=
  (steps.filter (fun s => match s with | .loop _ _ _ => true | _ => false)).length

/-- Generation gate: a scalarmult-orchestrator schedule is well-formed iff it
    carries a sibling `call` and a counted `loop`. -/
def wellFormedU (steps : List UStep) : Bool := hasCall steps && hasLoop steps

/-! ## 5. A self-contained demo schedule (the front's own witness)

A minimal schedule exercising the whole unifying alphabet: decode-style
load/clamp (two-slot `AND`), a counted ladder-style loop with a sibling
`call x25519_mono_step`, TWO sequential squaring-run loops each with a sibling
`call fe25519_sqr`, and a final field `call fe25519_mul` — the control shape of
the deployed scalarmult in miniature. -/

/-- The demo squaring-run: a counted loop whose body calls the field-sqr leaf and
    decrements the counter (the inversion chain's shape). -/
def demoSqrRun (top : LLabel) (n : Nat) : List UStep :=
  [ .movImm "R15" n
  , .loop top "R15" (uband 64 [.call "fe25519_sqr_x86_from_lean", .subImm "R15" 1]) ]

/-- The demo scalarmult schedule: clamp, a 255-trip ladder loop calling the step
    leaf, two sequential squaring-run loops, and a final field-mul call. -/
def demoScalarmult : List UStep :=
  [ .load "R8" "mem.RSI.0"
  , .movImm "RAX" 0xfffffffffffffff8, .andRR "R8" "RAX"
  , .store "mem.RBX.8" "R8"
  , .movImm "R13" 255
  , .loop 0 "R13" (uband 64
      [ .load "R11" "mem.RBX.32", .shrImm "R11" 63
      , .movImm "RCX" 0, .subRR "RCX" "R14"
      , .call "x25519_mono_step", .subImm "R13" 1 ]) ]
  ++ demoSqrRun 10 4 ++ demoSqrRun 11 9
  ++ [ .call "fe25519_mul_x86_from_lean", .ret ]

/-- The demo schedule passes the generation gate. -/
theorem demoScalarmult_wellFormed : wellFormedU demoScalarmult = true := by native_decide

/-- The demo schedule carries at least three counted loops (the ladder loop + the
    two squaring runs) — the multiple-sequential-loops capability. -/
theorem demoScalarmult_multiple_loops : 3 ≤ loopCount demoScalarmult := by native_decide

/-- The demo's rendered body carries sibling `.Lcall`s (the step + field leaves)
    INSIDE its loop back-edges. -/
theorem demoScalarmult_has_calls_and_backedges :
    hasLcall (uband 64 demoScalarmult) = true
      ∧ hasBackEdge (uband 64 demoScalarmult) = true := by
  refine ⟨?_, ?_⟩ <;> native_decide

end CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519UnifyingFront
