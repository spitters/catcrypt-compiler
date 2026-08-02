/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
import CatCrypt.Crypto.SecureCompilation.Dialects.OrchFront

/-!
# Branch / runtime-loop front for the DuplexChallenger query sampler (combinator core)

`OrchFront.buildOrchLoop` (the loop-over-call combinator) produces a **counted**
loop body whose per-iteration schedule is `{ leaf call ; pointer stride ;
counter decrement }` — `OrchStep` has `call/movRR/movImm/addImm/subImm`, wrapped
by ONE `loopLcmd` back-edge. `LprogControlFlow` adds the counted `loopLcmd`, the
data-dependent `whileLcmd` (both *backward* branches), and the `cfor*`/`nest*`
loop splices. What NEITHER layer has is a **forward data-dependent branch** — the
`CMP g,#k ; Lcond cc L ; <then> ; L:` skip that a `DuplexChallenger`'s
`observe`/`sample` trigger needs — nor a body step-language that carries memory
loads/stores, address arithmetic, and a mid-body counted loop alongside the leaf
`call`s.

This module is that missing front piece. It sits at the same owned-backend level
as `OrchFront` (imports only `JasminLprogExport` + `LprogControlFlow` +
`LprogAsmPrinter`, plus `OrchFront` for layering), so it is upstream of the
`Plonky3QuerySampleEmit` deploy with no import cycle.

## What the query sampler needs vs the landed fronts

The deployed `Plonky3QuerySampleEmit` kernel (`p3_fs_observe` /
`p3_fs_sample` / `p3_fs_sample_bits` / the partial-absorb duplex
`p3_fs_duplex_n`) is a `DuplexChallenger<16,8>` sample/observe wrapper. Its
control shape needs three things the landed fronts lack:

* **(a) forward data-dependent branches.** `observe`'s `if (inlen==8)` trigger,
  `sample`'s disjunctive `if (inlen>0 || outlen==0)` trigger, and `duplex_n`'s
  `if (inlen==0)` zero-trip guard are all **forward** `Lcond`-to-skip-label
  branches. `loopLcmd`/`whileLcmd` are backward (loop) branches; `OrchStep` has
  no branch node at all. → the new `.condFwd` / `.label` steps + `condSkip`.
* **(b) a runtime-N loop with surrounding calls and memory.** `duplex_n`'s absorb
  loop is a *counted* loop (`loopLcmd`) whose trip count is **loaded from the
  struct** (`inlen`), sitting between a leaf `call hp_perm16` and word-copy
  loads/stores. `OrchFront`'s `buildOrchLoop` counted loop fits the *shape* but
  its step-language cannot express the struct load, the word-copy body, or the
  guard around it. → the new `.load` / `.store` / `.loop` steps.
* **(c) the "byte-narrow tail".** In this kernel the query-index truncation is
  the `& 31` five-bit mask — an owned `AND:64` (`.andImm`), NOT a sub-word byte
  store. So there is **no** byte-cell dependency for the query sampler:
  the mask is expressible with the owned word ALU. (A real sub-word byte STORE —
  the separate byte-cell agent's work — is not needed here.)

So the residual for the query sampler is exactly **(a)** — a forward branch —
plus **(b)**'s richer body step-language; **(c)** is a non-issue. This module
supplies both and re-sources the deployed bodies from the schedules.

## Denotation honesty

The forward branch (`condSkip`) and the backward loops it composes with have the
**same** denotation status as `LprogControlFlow.whileLcmd`: the pure A-normal
`Com` substrate carries no label/jump denotation, so a machine-denote for the
forward branch is the reported residual, not claimed here. What we *do* discharge
is the structural contract — the schedule renders exactly the owned-backend
`CMP ; Lcond ; … ; label` / `loopLcmd` shape the byte encoder consumes, the
generation gate (`wellFormed`), and the byte-identical re-source (the deployed
kernel IS this front's output, so its rendered `.s` is unchanged and its
gas-assembled bench KAT carries over verbatim).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.QuerySampleBranchFront

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow
  (loopLcmd loopLcmd_length occursIn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLfundef)

/-! ## 1. The branch/loop/memory step language

`OrchStep` (loop-over-call) carries `call/movRR/movImm/addImm/subImm`. `BStep`
extends that with the shapes a `DuplexChallenger` wrapper needs: a flat-struct
memory **load**/**store** (`mem.<base>.<off>` operand), the counter address
arithmetic (`shlImm`/`andImm`/`cmpImm`/`addRR`), a **forward branch**
(`condFwd`) and its **skip label** (`label`), and a mid-body **counted loop**
(`loop`, whose back-edge is the verified `loopLcmd`). Each step renders to an
owned-backend `Lcmd`; `bband` concatenates a schedule. -/

/-- A flat-struct memory operand `mem.<base>.<off>` (the reader materialises it as
    the x86 `off(%base)` effective address). Matches the hand form
    `"mem." ++ base ++ "." ++ toString off`. -/
def memOp (base : String) (off : Nat) : LOperand :=
  .reg ("mem." ++ base ++ "." ++ toString off)

/-- One step of a branch/runtime-loop schedule. Superset of `OrchStep` with
    memory, address arithmetic, a forward branch, and a mid-body counted loop. -/
inductive BStep where
  /-- Register-to-register move `MOV dst, src`. -/
  | movRR (dst src : String)
  /-- Immediate move `MOV dst, #imm`. -/
  | movImm (dst : String) (imm : Nat)
  /-- Word load `LOAD dst, mem.<base>.<off>` (flat-struct field read). -/
  | load (dst base : String) (off : Nat)
  /-- Word store `STORE mem.<base>.<off>, src` (flat-struct field write). -/
  | store (base : String) (off : Nat) (src : String)
  /-- Immediate add `ADD reg, #imm` (pointer stride / counter bump). -/
  | addImm (reg : String) (imm : Nat)
  /-- Immediate subtract `SUB reg, #imm` (counter decrement). -/
  | subImm (reg : String) (imm : Nat)
  /-- Immediate mask `AND reg, #imm` (the `& 31` query-index truncation). -/
  | andImm (reg : String) (imm : Nat)
  /-- Immediate left shift `SHL reg, #imm` (index → byte offset, `<< 3`). -/
  | shlImm (reg : String) (imm : Nat)
  /-- Immediate compare `CMP reg, #imm` (branch predicate materialisation). -/
  | cmpImm (reg : String) (imm : Nat)
  /-- Register add `ADD dst, src` (add base pointer into an address reg). -/
  | addRR (dst src : String)
  /-- A void near-`call` to a sibling/leaf symbol. -/
  | call (sym : String)
  /-- A **forward** conditional branch `Lcond cc → lbl` (skip when `cc` holds). -/
  | condFwd (cc : String) (lbl : LLabel)
  /-- A skip/join label `Llabel internal lbl` (a forward branch target). -/
  | label (lbl : LLabel)
  /-- A mid-body **counted loop**: `loopLcmd w top counter inner` (verified
      back-edge). `inner` is the front-generated body (itself a `bband`). -/
  | loop (top : LLabel) (counter : String) (inner : Lcmd)

/-- Render one `BStep` to an owned-backend `Lcmd` at op width `w`. Every mnemonic
    carries `withWidthTag w`, matching the width tag the hand-authored owned
    bodies write (`"LOAD:64"`, `"ADD:64"`, `"CMP:64"`, …). -/
def bstepToLcmd (w : Nat) : BStep → Lcmd
  | .movRR d s      => [⟨0, .Lopn [.reg d] (withWidthTag w "MOV") [.reg s]⟩]
  | .movImm d v     => [⟨0, .Lopn [.reg d] (withWidthTag w "MOV") [.imm v]⟩]
  | .load d base o  => [⟨0, .Lopn [.reg d] (withWidthTag w "LOAD") [memOp base o]⟩]
  | .store base o s => [⟨0, .Lopn [memOp base o] (withWidthTag w "STORE") [.reg s]⟩]
  | .addImm r v     => [⟨0, .Lopn [.reg r] (withWidthTag w "ADD") [.reg r, .imm v]⟩]
  | .subImm r v     => [⟨0, .Lopn [.reg r] (withWidthTag w "SUB") [.reg r, .imm v]⟩]
  | .andImm r v     => [⟨0, .Lopn [.reg r] (withWidthTag w "AND") [.reg r, .imm v]⟩]
  | .shlImm r v     => [⟨0, .Lopn [.reg r] (withWidthTag w "SHL") [.reg r, .imm v]⟩]
  | .cmpImm r v     => [⟨0, .Lopn [.reg r] (withWidthTag w "CMP") [.reg r, .imm v]⟩]
  | .addRR d s      => [⟨0, .Lopn [.reg d] (withWidthTag w "ADD") [.reg d, .reg s]⟩]
  | .call sym       => [⟨0, .Lcall none (sym, 0)⟩]
  | .condFwd cc lbl => [⟨0, .Lcond (.reg cc) lbl⟩]
  | .label lbl      => [⟨0, .Llabel .internal lbl⟩]
  | .loop top counter inner => loopLcmd w top counter inner

/-- Render a schedule to an `Lcmd` (the flattened owned body). -/
def bband (w : Nat) (steps : List BStep) : Lcmd := steps.flatMap (bstepToLcmd w)

@[simp] theorem bband_nil (w : Nat) : bband w [] = [] := rfl

@[simp] theorem bband_cons (w : Nat) (s : BStep) (ss : List BStep) :
    bband w (s :: ss) = bstepToLcmd w s ++ bband w ss := by
  simp [bband, List.flatMap_cons]

@[simp] theorem bband_append (w : Nat) (a b : List BStep) :
    bband w (a ++ b) = bband w a ++ bband w b := by
  simp [bband, List.flatMap_append]

/-! ## 2. The forward-branch combinator (the new primitive)

`loopLcmd`/`whileLcmd` are *backward* branches; `condSkip` is the *forward* one:
`CMP gReg,#imm ; Lcond cc → lbl ; <then> ; lbl:`. Its `then` band runs iff the
skip condition `cc` does **not** hold. This is exactly the shape the query
sampler's `if (inlen==8)` observe trigger and the `if (inlen==0)` duplex zero
guard render to. It is a plain `Lcmd`; like `loopLcmd`/`whileLcmd` it is CT only
for a **public** predicate (the sponge counters `inlen`/`outlen` are public
buffer occupancy, so these branches are CT-admissible; a secret-dependent guard
would need `CMOVcc`, forbidden here). -/

/-- The owned-backend **forward** conditional skip: `CMP gReg,#imm ; Lcond cc →
    lbl ; <then> ; Llabel lbl`. The `then` band executes iff the skip condition
    `cc` is false at the compare. -/
def condSkip (w : Nat) (gReg : String) (imm : Nat) (cc : String) (lbl : LLabel)
    (thenBand : Lcmd) : Lcmd :=
  (⟨0, .Lopn [.reg gReg] (withWidthTag w "CMP") [.reg gReg, .imm imm]⟩
    :: ⟨0, .Lcond (.reg cc) lbl⟩ :: thenBand) ++ [⟨0, .Llabel .internal lbl⟩]

/-- `condSkip` length is constant in the `then` band: predicate compare + branch
    + label + the band. -/
@[simp] theorem condSkip_length (w : Nat) (gReg : String) (imm : Nat) (cc : String)
    (lbl : LLabel) (thenBand : Lcmd) :
    (condSkip w gReg imm cc lbl thenBand).length = thenBand.length + 3 := by
  simp [condSkip, List.length_append]

/-- `condSkip` **begins with the predicate compare** `CMP gReg,#imm` (what sets
    the flags the forward branch tests). -/
theorem condSkip_head (w : Nat) (gReg : String) (imm : Nat) (cc : String)
    (lbl : LLabel) (thenBand : Lcmd) :
    (condSkip w gReg imm cc lbl thenBand).head?
      = some ⟨0, .Lopn [.reg gReg] (withWidthTag w "CMP") [.reg gReg, .imm imm]⟩ := by
  rfl

/-- `condSkip` **ends with the skip label** `Llabel internal lbl` (the forward
    branch target the byte encoder records). -/
theorem condSkip_last (w : Nat) (gReg : String) (imm : Nat) (cc : String)
    (lbl : LLabel) (thenBand : Lcmd) :
    (condSkip w gReg imm cc lbl thenBand).getLast? = some ⟨0, .Llabel .internal lbl⟩ := by
  rw [condSkip, List.getLast?_append_of_ne_nil _ (by simp)]; rfl

/-- The `condSkip` band is exactly what the flat schedule
    `cmpImm ; condFwd ; <then steps> ; label` produces — so a body written with
    the flat `BStep` language factors through the named forward-branch primitive.
    (The observe trigger and the duplex zero-guard are `condSkip`-shaped.) -/
theorem condSkip_eq_band (w : Nat) (gReg : String) (imm : Nat) (cc : String)
    (lbl : LLabel) (thenSteps : List BStep) :
    condSkip w gReg imm cc lbl (bband w thenSteps)
      = bband w ([.cmpImm gReg imm, .condFwd cc lbl] ++ thenSteps ++ [.label lbl]) := by
  simp only [bband_append, bband_cons, bband_nil, bstepToLcmd, condSkip,
    List.nil_append, List.append_nil, List.cons_append]

/-! ## 3. The query-sampler configuration (the flat-`Chal` ABI)

The step-specs are parametric over the flat-`Chal` byte offsets and the linked
symbols, so the deploy passes its own layout (single source of truth, no
duplicated constants). -/

/-- The flat-`Chal` layout + linked symbols the query-sampler schedules read. -/
structure QSConfig where
  /-- `inbuf` byte offset. -/
  inbufOff : Nat
  /-- `outbuf` byte offset. -/
  outbufOff : Nat
  /-- `inlen` (absorb counter) byte offset. -/
  inlenOff : Nat
  /-- `outlen` (squeeze pop counter) byte offset. -/
  outlenOff : Nat
  /-- Poseidon2 permute leaf symbol. -/
  permSym : String
  /-- Full-absorb duplex symbol (`inlen==8` observe trigger). -/
  duplexFullSym : String
  /-- Partial-absorb duplex symbol (`inlen` words, sample trigger). -/
  duplexNSym : String
  /-- The one-word squeeze the query index masks. -/
  sampleSym : String := "p3_fs_sample"

/-! ## 4. The query-sampler schedules (branch + runtime loop + calls)

Each schedule is a `List BStep`; `bband 64` renders it to the deployed owned
body. These reproduce the deployed `Plonky3QuerySampleEmit` bodies exactly
(the deploy re-sources its `*Body` defs from these), so the emitted `.s` is
byte-identical. -/

/-- One word-copy iteration `dst[i] ← src[i]` (`%rsi` src, `%rdx` dst, `%r8`
    counter): load, store, advance both pointers, decrement the counter. -/
def wordCopySteps : List BStep :=
  [ .load "RAX" "RSI" 0, .store "RDX" 0 "RAX"
  , .addImm "RSI" 8, .addImm "RDX" 8, .subImm "R8" 1 ]

/-- The word-copy loop body (front-generated leaf reused by both duplex loops). -/
def wordCopyBodyFront : Lcmd := bband 64 wordCopySteps

/-- Partial-absorb duplex `p3_fs_duplex_n(Chal *c)`: absorb `inlen` words
    (runtime-N `loopLcmd`, guarded by the `inlen==0` forward-branch zero-trip
    skip), permute (`call permSym`), squeeze 8. The runtime absorb count is
    **loaded from the struct** (`.load "R8" c inlen`) — the shape `OrchFront`
    cannot express. -/
def duplexNSteps (cfg : QSConfig) : List BStep :=
  [ .movRR "RBX" "RDI"
  , .movRR "RSI" "RBX", .addImm "RSI" cfg.inbufOff
  , .movRR "RDX" "RBX"
  , .load "R8" "RBX" cfg.inlenOff
  , .cmpImm "R8" 0, .condFwd "E" 2
  , .loop 0 "R8" wordCopyBodyFront
  , .label 2
  , .movRR "RDI" "RBX", .movRR "RSI" "RBX", .call cfg.permSym
  , .movRR "RSI" "RBX", .movRR "RDX" "RBX", .addImm "RDX" cfg.outbufOff
  , .movImm "R8" 8
  , .loop 1 "R8" wordCopyBodyFront ]

/-- The partial-absorb duplex body. -/
def duplexNBodyFront (cfg : QSConfig) : Lcmd := bband 64 (duplexNSteps cfg)

/-- `p3_fs_observe(Chal *c, uint64_t v)`: `outlen=0 ; inbuf[inlen++]=v ; if
    (inlen==8) { duplex ; inlen=0 ; outlen=8 }`. The `if (inlen==8)` trigger is a
    `condFwd`-skip forward branch; the store address is `c + inbuf + (inlen<<3)`
    (`shlImm`/`addRR`). -/
def observeSteps (cfg : QSConfig) : List BStep :=
  [ .movRR "RBX" "RDI"
  , .movImm "RAX" 0, .store "RBX" cfg.outlenOff "RAX"
  , .load "RCX" "RBX" cfg.inlenOff
  , .movRR "RDX" "RCX", .shlImm "RDX" 3, .addRR "RDX" "RBX", .addImm "RDX" cfg.inbufOff
  , .store "RDX" 0 "RSI"
  , .addImm "RCX" 1, .store "RBX" cfg.inlenOff "RCX"
  , .cmpImm "RCX" 8, .condFwd "NE" 7
  , .movRR "RDI" "RBX", .call cfg.duplexFullSym
  , .movImm "RAX" 0, .store "RBX" cfg.inlenOff "RAX"
  , .movImm "RAX" 8, .store "RBX" cfg.outlenOff "RAX"
  , .label 7 ]

/-- The observe body. -/
def observeBodyFront (cfg : QSConfig) : Lcmd := bband 64 (observeSteps cfg)

/-- `p3_fs_sample(Chal *c) -> uint64_t`: `if (inlen>0 || outlen==0) { duplex_n ;
    inlen=0 ; outlen=8 } ; outlen-- ; return outbuf[outlen]`. The disjunctive
    trigger is TWO forward branches to two labels (`inlen!=0 → do_dup`,
    `outlen!=0 → skip`), the flat step-language's native shape. -/
def sampleSteps (cfg : QSConfig) : List BStep :=
  [ .movRR "RBX" "RDI"
  , .load "RCX" "RBX" cfg.inlenOff, .cmpImm "RCX" 0, .condFwd "NE" 1
  , .load "RCX" "RBX" cfg.outlenOff, .cmpImm "RCX" 0, .condFwd "NE" 2
  , .label 1
  , .movRR "RDI" "RBX", .call cfg.duplexNSym
  , .movImm "RAX" 0, .store "RBX" cfg.inlenOff "RAX"
  , .movImm "RAX" 8, .store "RBX" cfg.outlenOff "RAX"
  , .label 2
  , .load "RCX" "RBX" cfg.outlenOff, .subImm "RCX" 1, .store "RBX" cfg.outlenOff "RCX"
  , .movRR "RDX" "RCX", .shlImm "RDX" 3, .addRR "RDX" "RBX", .addImm "RDX" cfg.outbufOff
  , .load "RAX" "RDX" 0 ]

/-- The sample body. -/
def sampleBodyFront (cfg : QSConfig) : Lcmd := bband 64 (sampleSteps cfg)

/-- `p3_fs_sample_bits(Chal *c) -> uint64_t`: `sample() & 31` — the 5-bit FRI
    query index. `call sampleSym` then the owned `andImm` mask (case (c): a word
    ALU mask, not a sub-word byte store). -/
def sampleBitsSteps (cfg : QSConfig) : List BStep :=
  [ .call cfg.sampleSym, .andImm "RAX" 31 ]

/-- The sample-bits body. -/
def sampleBitsBodyFront (cfg : QSConfig) : Lcmd := bband 64 (sampleBitsSteps cfg)

/-! ## 5. Generation gate (`wellFormed`) — the `isSome` analogue

`bband` is total, so the analogue of an `… |>.isSome = true` front gate is a
decidable well-formedness `Bool` on the schedule. A query-sampler wrapper
schedule is well-formed iff it contains a leaf `call` and a forward branch
(`condFwd`) OR is a straight-line mask tail (`sample_bits`). -/

/-- The schedule contains a leaf `call`. -/
def hasCall (steps : List BStep) : Bool :=
  steps.any (fun s => match s with | .call _ => true | _ => false)

/-- The schedule contains a forward branch. -/
def hasBranch (steps : List BStep) : Bool :=
  steps.any (fun s => match s with | .condFwd _ _ => true | _ => false)

/-- The schedule contains a mid-body counted loop. -/
def hasLoop (steps : List BStep) : Bool :=
  steps.any (fun s => match s with | .loop _ _ _ => true | _ => false)

/-- Generation gate: a branch-wrapper schedule is well-formed iff it calls a leaf
    and carries a forward branch. -/
def wellFormedWrapper (steps : List BStep) : Bool := hasCall steps && hasBranch steps

theorem observe_wellFormed (cfg : QSConfig) : wellFormedWrapper (observeSteps cfg) = true := rfl
theorem sample_wellFormed (cfg : QSConfig) : wellFormedWrapper (sampleSteps cfg) = true := rfl
/-- The partial-absorb duplex carries the runtime loop and the leaf permute call
    (its guard is the `inlen==0` zero-trip skip). -/
theorem duplexN_hasLoop_hasCall (cfg : QSConfig) :
    hasLoop (duplexNSteps cfg) = true ∧ hasCall (duplexNSteps cfg) = true
      ∧ hasBranch (duplexNSteps cfg) = true := ⟨rfl, rfl, rfl⟩

/-! ## 6. Structural shape facts (the schedules render the owned control flow)

The deployed emit's render checks in `Plonky3QuerySampleEmit` apply to these
bodies verbatim once the deploy is re-sourced from them. Here we pin, at the
front, that each body renders its control shape — the forward branch /
back-edge / mask / call — with a fixed config witness. -/

/-- A concrete config witness (the deployed flat-`Chal` layout). -/
def demoCfg : QSConfig :=
  { inbufOff := 128, outbufOff := 192, inlenOff := 256, outlenOff := 264
    permSym := "hp_perm16", duplexFullSym := "p3_fs_duplex", duplexNSym := "p3_fs_duplex_n" }

/- The observe body renders the `inlen==8` forward trigger (`cmpq $8,%rcx ;
    jne .L7 ; … ; .L7:`) and the full-absorb `call`. -/
#guard
  let s := renderLfundef "p3_fs_observe" (observeBodyFront demoCfg)
  occursIn "cmpq $8, %rcx" s && occursIn ".L7:" s
    && occursIn "jne .L7" s && occursIn "call p3_fs_duplex" s

/- The sample body renders the disjunctive `inlen>0 || outlen==0` trigger (two
    `cmpq $0` + two `jne`) and the partial-absorb `call`. -/
#guard
  let s := renderLfundef "p3_fs_sample" (sampleBodyFront demoCfg)
  occursIn "cmpq $0, %rcx" s && occursIn "jne .L1" s
    && occursIn "jne .L2" s && occursIn "call p3_fs_duplex_n" s

/- The partial-absorb duplex renders the runtime counted absorb loop
    (`.L0: … ; jne .L0`) and the `call hp_perm16` permute. -/
#guard
  let s := renderLfundef "p3_fs_duplex_n" (duplexNBodyFront demoCfg)
  occursIn ".L0:" s && occursIn "jne .L0" s && occursIn "call hp_perm16" s

/- The sample-bits body renders the `& 31` mask (`andq $31,%rax`) over the
    `call p3_fs_sample` result (case (c): a word ALU mask). -/
#guard
  let s := renderLfundef "p3_fs_sample_bits" (sampleBitsBodyFront demoCfg)
  occursIn "call p3_fs_sample" s && occursIn "andq $31, %rax" s

end CatCrypt.Crypto.SecureCompilation.VIR.QuerySampleBranchFront
