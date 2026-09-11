/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.Lowering
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Lowering
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage

/-!
# Closing the lowering COVERAGE gap: constant-offset memory load/store (P2)

`Lowering.lean`'s proof-of-concept `lowerLinstrR` (#148) lowers a
`LinstrR.Lopn` into the **register/flag-only** machine `Instr w`
(`Model.lean`), and matches *only* the nine ALU/`MOV` mnemonics
`ADD/SUB/MUL/AND/OR/XOR/SHL/SHR/MOV`. Every other instruction shape — in
particular the **memory** pseudo-ops `LOAD`/`STORE` (and `LOADIDX`/`STOREIDX`,
`CMOV`, `ADCX`, the cast/`CALL` pseudo-ops, the control-flow constructors) —
falls to the `_ => none` arm and is then **silently dropped** by `lowerLcmd`'s
`filterMap`. A generic `Com` that uses those shapes therefore cannot be lowered.

This module (P2) extends coverage to the highest-value uncovered shape we
already have a machine
model **and** byte encoder for: **constant-offset memory load/store**. We target
the memory-capable `JInstr 64` model (`JasminModel.lean`, namespace `Jasmin`) —
whose `loadMem`/`storeMem` constructors `Model.lean`'s `Instr` lacks — and reuse
its `runBlock` denotation and the `ConstantTimeCoverage` `allDirect` result.

## Why `JInstr 64`, not `Instr w`

The POC's `Instr w` (`Model.lean`) is a register/flag machine with **no memory
constructors**; it cannot be a lowering target for `LOAD`/`STORE`. The faithful
Jasmin transcription `JInstr w` (`JasminModel.lean`) *does* carry memory:
constant-offset `loadMem dst base off` / `storeMem base off src`, and the
register-indexed `loadMemIdx`/`storeMemIdx`. `ScalarEncoder.encodeJInstr` encodes
all four (SDM `8B`/`89` `MOV` reg↔mem, with/without SIB), so a lowering into
these constructors stays inside the encodable subset.

## Coverage delta

`lowerLinstrExt` is a **strict superset** of the POC coverage. The POC mnemonic
table `{ADD,SUB,MUL,AND,OR,XOR,SHL,SHR,MOV}` is re-covered (now as one-element
`JInstr 64` blocks), and the following are **newly covered**:

* `LOAD`  with a constant-offset source `[.arr base off]` →
  `[loadMem dst base off]`  (`movq off(%base), %dst`);
* `STORE` with a constant-offset destination `[.arr base off, val]` →
  `[storeMem base off val]` (`movq %val, off(%base)`).

`lowerLinstrExt` returns `none` on everything else: `CMOV`,
`ADCX`/`ADOX`/`ADCXHI`/`ADOXHI`, `MULXHI`, `ZEROEXT`/`TRUNC`, `CALL:`/`CALLN:`,
the native `ROR:`/`SHR:n`/`SHL:n`/`SAR:n` immediate shifts, `ANDN`, the
register-INDEXED `LOADIDX`/`STOREIDX`, the `VPACK8u64:` vector op, and every
non-`Lopn` `LinstrR` constructor (`Lsyscall`/`Lcall`/`Lret`/`Lalign`/`Llabel`/
`Lgoto`/`Ligoto`/`LstoreLabel`/`Lcond`).

**That list scopes to this function.** `lowerLinstrExt` is the last level of the
chain the byte path enters at `gatherJBlock6`: every level above it intercepts
the shapes it adds before delegating the rest down, so much of the list is
accepted upstream and never arrives here, and an arm added here for such a shape
is unreachable. What the GATHER accepts — one row per shape, with the `file:line`
of the arm that accepts it, and the chain's own declined set — is derived from
these sources into `GATHER_COVERAGE.md` by `scripts/gen-gather-coverage.sh`,
which CI re-derives and diffs. Consult that table before reading any entry above
as a pipeline capability gap.

`loadMemIdx`/`storeMemIdx` are **not** `IsDirect` — their CT shape is the
`agreePub`/`CTAddressed` one of `LowCTMemCT.lean`, not the unconditional
`allDirect`. The ADX arms compute no effective address, so an `ADCX`/`ADOX`
block is `IsDirect` by the catch-all and passes `allDirect`.

## What is proved

* `lowerLinstrExt_superset_alu` — on every ALU/`MOV` shape the POC lowered
  (`lowerLinstrR` returned `some`), `lowerLinstrExt` also returns `some`
  (strict-superset witness for the arithmetic arms).
* `lowerLinstrExt_load` / `lowerLinstrExt_store` — the new arms return `some`
  on the constant-offset memory shapes the POC dropped.
* `lowerLinstrExt_load_denote` / `lowerLinstrExt_store_denote` — **denotation
  preservation** for the new arms, against `JInstr`'s `runBlock`: a lowered load
  leaves `dst` holding the memory word `[base + off]`; a lowered store leaves the
  cell `[base + off]` holding the stored value. Proved in general (not demo-only)
  from the `JState.load_store_same` / `JState.get_setReg_same` model lemmas.
* `lowerLinstrExt_load_allDirect` / `lowerLinstrExt_store_allDirect` — the new
  arms produce `allDirect` blocks (constant-offset memory is `IsDirect`), so they
  are constant-time **by construction** via `allDirect_constant_time`.
* A worked **demo** (`demoStore`/`demoLoad`): a `LinstrR` whose `lowerLinstr`
  returned `none` now lowers under `lowerLinstrExt`, with the right `runBlock`
  effect (`decide`/`native_decide`) and `allDirect = true`.

## Deferred merge-time integration

At merge time these arms fold into `Lowering.lean`'s `lowerLinstrR`: replace the
`| _ => none` (and the `Lopn` `opn` fallthrough) for the `LOAD`/`STORE` mnemonics
with the bodies of `lowerLoad`/`lowerStore` here. Because the memory ops live in
`JInstr` (not `Instr w`), that fold also migrates the POC lowering target from
`Instr w` to `JInstr 64` (the union model) — tracked as the next step in the
perf-review P2 item.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtended

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage

/-! ## 1. Operand translation into the `JInstr` operand type

`JOperand` (`JasminModel.lean`) is `reg`/`imm` only — the register/immediate
surface a two-address ALU source needs. An `LOperand.arr`/`.arrIdx` is a memory
operand, not a `JOperand`; it is handled by the dedicated `LOAD`/`STORE` arms
(memory operands never appear as an ALU `JOperand`). For a non-memory operand we
translate `reg`/`imm` directly; a stray memory operand in an ALU position is
out of range and lowered conservatively to `reg 0` (it never occurs for the
covered mnemonics). -/

/-- Translate an `lprog` operand to a `JInstr` register/immediate operand. -/
def lowerJOperand : LOperand → JOperand
  | .reg name => .reg name
  | .imm v => .imm v
  | .arr base idx => .reg (base ++ "[" ++ toString idx ++ "]")
  | .arrIdx base idx scale => .reg (base ++ "[" ++ idx ++ "*" ++ toString scale ++ "]")

/-! ## 2. The ALU/`MOV` arms (the POC coverage, lifted to `JInstr 64`)

Each maps the two-address `Lopn [reg dst] OP [src]` to the matching `JInstr 64`
arm — the same mnemonic table `lowerLinstrR` covers, now into the memory-capable
union model. `MUL` lowers to `imul` (the low-word multiply `JInstr` carries). -/

/-- Lower one ALU/`MOV` mnemonic over a single source to the matching
    `JInstr 64`, or `none` if the mnemonic is outside the POC table. -/
def lowerAluJ (dst : String) (opn : String) (s : JOperand) : Option (JInstr 64) :=
  match opn with
  | "ADD" => some (.add dst s)
  | "SUB" => some (.sub dst s)
  | "MUL" => some (.imul dst s)
  | "AND" => some (.and_ dst s)
  | "OR"  => some (.or_ dst s)
  | "XOR" => some (.xor_ dst s)
  | "SHL" => some (.shl dst s)
  | "SHR" => some (.shr dst s)
  | "MOV" => some (.mov dst s)
  | _     => none

/-! ## 3. The new constant-offset memory arms

A `LOAD` reads a word from `[base + off]` into a destination register; a `STORE`
writes a source value to `[base + off]`. The constant offset `off` is the
compile-time element index carried by `LOperand.arr base off` — the **direct**
addressing mode (no index register), so the lowered op is `IsDirect`. -/

/-- Lower a constant-offset `LOAD`: `dst := [base + off]`. -/
def lowerLoad (dst base : String) (off : Nat) : JInstr 64 :=
  .loadMem dst base (off : Int)

/-- Lower a constant-offset `STORE`: `[base + off] := src`. -/
def lowerStore (base : String) (off : Nat) (src : JOperand) : JInstr 64 :=
  .storeMem base (off : Int) src

/-! ### 3b. The supported-op ALU forms the SSA exporter actually emits (D4)

`opToLinstrR` (`JasminLprogExport.lean`) exports the legal `SupportedOp` set in
shapes the POC single-source ALU arm does **not** match:

* `regArith bop 64` → `Lopn [reg dst] "ADD:64" [s0, s1]` — **two** sources, and
  the mnemonic carries the `:64` width tag;
* `mulhi 64` → `Lopn [reg dst] "MULXHI:64" [s0, s1]` — two sources, a mnemonic
  with no `lowerAluJ` arm;
* `shrImm 64 n` / `shlImm 64 n` → `Lopn [reg dst] "SHR:<n>:64" [src]` /
  `"SHL:<n>:64"` — a single source, the shift count baked into the mnemonic.

The helpers below lower each into the memory-capable `JInstr 64` model, stripping
the width tag first (`stripWidthTag`). They are the bodies the new
`lowerLinstrExt` arms (§4) dispatch to; the existing arms are untouched. -/

/-- Strip the `:64` width tag and lower a **two-source** ALU op
    `dst := s0 OP s1` to two-address form `[mov dst s0; OP dst s1]` — first
    materialise `dst := s0`, then apply the binop against `s1` (the standard
    SSA→two-address split, here made explicit). `none` if the (tag-stripped)
    mnemonic is outside the `lowerAluJ` table. -/
def lowerAluJ2 (dst : String) (opn : String) (s0 s1 : JOperand) :
    Option (List (JInstr 64)) :=
  (lowerAluJ dst (stripWidthTag opn) s1).map (fun i => [JInstr.mov dst s0, i])

/-- Lower the high-word widening multiply `dst := high(s0 · s1)` (`MULXHI`) to a
    single `mulx`, routing the low word to a scratch register `dst ++ "__mulxlo"`
    (the matching low binding is the producer's `regArith .mul` over the same
    sources — see `opToLinstrR`'s `MULXHI` note). -/
def lowerMulHiJ (dst : String) (s0 s1 : JOperand) : List (JInstr 64) :=
  [JInstr.mulx dst (dst ++ "__mulxlo") s0 s1]

/-- The shift count of an immediate-shift mnemonic `SH?:<n>` (`<n>` is the suffix
    after the 4-character `"SHL:"`/`"SHR:"` prefix); `0` if unparseable (never the
    case for an exporter-emitted mnemonic). Defined via `String.toList`/`drop` so it
    reduces in the kernel (the `splitOn`-based form did not). -/
def shiftCountOf (bare : String) : Nat :=
  (natOfDigits? (bare.toList.drop 4)).getD 0

/-- Parse a (tag-stripped) immediate-shift mnemonic `SHL:<n>` / `SHR:<n>` into
    `(isLeft, n)`. `none` for any other mnemonic. Detection is by the 4-character
    `hasPrefix` prefix (kernel-reducible on a closed mnemonic), so the per-op
    bridge's `parseShiftMnem "BOP" = none` / `…"SHR:<n>" = some _` facts are
    provable by reduction; the count is recovered separately by `shiftCountOf`. -/
def parseShiftMnem (opn : String) : Option (Bool × Nat) :=
  let bare := stripWidthTag opn
  if hasPrefix bare "SHL:" then some (true, shiftCountOf bare)
  else if hasPrefix bare "SHR:" then some (false, shiftCountOf bare)
  else none

/-- Lower a native immediate shift `dst := src >> n` (`SHR:<n>`) /
    `dst := src << n` (`SHL:<n>`) to two-address form
    `[mov dst src; SH dst, #n]`. `none` if `opn` is not an immediate-shift
    mnemonic. -/
def lowerShiftImmJ (dst : String) (opn : String) (src : JOperand) :
    Option (List (JInstr 64)) :=
  (parseShiftMnem opn).map (fun p =>
    [JInstr.mov dst src,
     if p.1 then JInstr.shl dst (JOperand.imm p.2) else JInstr.shr dst (JOperand.imm p.2)])

/-! ## 4. The extended lowering

`lowerLinstrExt` strictly extends the POC `lowerLinstrR`: every shape the POC
lowered returns `some` here (as a one-element block), and the constant-offset
`LOAD`/`STORE` shapes the POC dropped now lower too. Everything else stays
`none` — the remainder of THIS function, which the module header separates from
what the gather chain accepts. -/

/-- The extended single-instruction lowering, into `List (JInstr 64)`.
    Strict superset of `lowerLinstrR` on the ALU/`MOV` arms, plus constant-offset
    `LOAD`/`STORE`. -/
def lowerLinstrExt : LinstrR → Option (List (JInstr 64))
  -- constant-offset LOAD: `dst := [base + off]`
  | .Lopn [.reg dst] "LOAD" [.arr base off] =>
      some [lowerLoad dst base off]
  -- constant-offset STORE: `[base + off] := val`
  | .Lopn [.reg _] "STORE" [.arr base off, val] =>
      some [lowerStore base off (lowerJOperand val)]
  -- the POC ALU/`MOV` table
  | .Lopn [.reg dst] opn [src] =>
      (lowerAluJ dst opn (lowerJOperand src)).map (fun i => [i])
  | _ => none

/-- Lower a full `Linstr` (drops the position tag), extended form. -/
def lowerLinstrExtL (i : Linstr) : Option (List (JInstr 64)) :=
  lowerLinstrExt i.li_i

/-! ### 4b. The D4 supported-op superset (`lowerLinstrExt2`)

`lowerLinstrExt2` is a **strict superset** of `lowerLinstrExt`: it lowers
everything `lowerLinstrExt` does (delegating verbatim — `lowerLinstrExt2_of_ext`)
*and* the supported-op ALU forms the SSA exporter emits that the POC single-source
arm misses — the **two-source** `regArith`/`MULXHI` exports and the **width-tagged
immediate shifts** `SHR:<n>:64` / `SHL:<n>:64`. It is defined as a separate
function (not an in-place extension of `lowerLinstrExt`) so the POC lowering's
emit/KAT behaviour and its boolean mirror `linstrRSupported` are byte-identical;
the new file gives `lowerLinstrExt2` its own mirror and gather story. -/

/-- The supported-op superset lowering. New arms (vs `lowerLinstrExt`): the
    high-word multiply `MULXHI:64`, the generic two-source ALU
    `op dst, [s0, s1]`, and the single-source immediate shifts `SHR:<n>` /
    `SHL:<n>` (tag-stripped). Every other shape delegates to `lowerLinstrExt`. -/
def lowerLinstrExt2 : LinstrR → Option (List (JInstr 64))
  -- the POC constant-offset memory shapes first, so the generic two-source ALU
  -- arm below does not intercept the `[.arr base off, val]` STORE form (its
  -- mnemonic is `"STORE"`, not an ALU mnemonic) — `lowerLinstrExt2` stays a strict
  -- superset of `lowerLinstrExt`.
  | .Lopn [.reg dst] "LOAD" [.arr base off] =>
      lowerLinstrExt (.Lopn [.reg dst] "LOAD" [.arr base off])
  | .Lopn [.reg dst] "STORE" [.arr base off, val] =>
      lowerLinstrExt (.Lopn [.reg dst] "STORE" [.arr base off, val])
  -- high-word widening multiply (tagged), two sources
  | .Lopn [.reg dst] "MULXHI:64" [s0, s1] =>
      some (lowerMulHiJ dst (lowerJOperand s0) (lowerJOperand s1))
  -- generic two-source ALU (`regArith bop 64` export), tag-stripped inside
  | .Lopn [.reg dst] opn [s0, s1] =>
      lowerAluJ2 dst opn (lowerJOperand s0) (lowerJOperand s1)
  -- single source: a tagged immediate shift, then the (tag-stripped) ALU/`MOV`
  -- table (covers `regConst`'s `MOV:64`), else delegate to the POC fragment
  -- (the constant-offset `LOAD`, whose `.arr` source / `"LOAD"` mnemonic is not
  -- an ALU mnemonic).
  | .Lopn [.reg dst] opn [src] =>
      match parseShiftMnem opn with
      | some _ => lowerShiftImmJ dst opn (lowerJOperand src)
      | none   =>
        match lowerAluJ dst (stripWidthTag opn) (lowerJOperand src) with
        | some i => some [i]
        | none   => lowerLinstrExt (.Lopn [.reg dst] opn [src])
  -- everything else (LOAD/STORE, control-flow, …): the POC fragment verbatim
  | i => lowerLinstrExt i

/-- Lower a full `Linstr` (drops the position tag), supported-op superset. -/
def lowerLinstrExt2L (i : Linstr) : Option (List (JInstr 64)) :=
  lowerLinstrExt2 i.li_i

/-! ## 5. Strict-superset witnesses (coverage delta) -/

/-- The nine ALU/`MOV` mnemonics the POC `lowerLinstrR` covers. -/
def pocMnemonics : List String :=
  ["ADD", "SUB", "MUL", "AND", "OR", "XOR", "SHL", "SHR", "MOV"]

/-- **Superset on the ALU/`MOV` arms.** For every mnemonic the POC `lowerLinstrR`
    covers (`opn ∈ pocMnemonics`) and every source operand `src`, `lowerLinstrExt`
    returns `some` — so it lowers at least everything the POC ALU table did.
    (The POC's `Instr w` target and this module's `JInstr 64` target differ, so
    the witness is "the extended lowering succeeds", not pointwise instruction
    equality. The `LOAD`/`STORE` head patterns do not fire here: their operand
    lists are `[.arr ..]` / `[.arr .., _]`, never the single `[src]` an ALU op
    carries.) -/
theorem lowerLinstrExt_superset_alu (dst : String) (opn : String)
    (src : LOperand) (hopn : opn ∈ pocMnemonics) :
    ∃ b, lowerLinstrExt (.Lopn [.reg dst] opn [src]) = some b := by
  -- On a single source `[src]` the `LOAD`/`STORE` head patterns (which require a
  -- two-element list for STORE, and a `.arr` source for LOAD) do not match, so
  -- `lowerLinstrExt` reduces to `(lowerAluJ dst opn _).map (·::[])`; on each of
  -- the nine mnemonics `lowerAluJ` returns `some`.
  simp only [pocMnemonics, List.mem_cons, List.not_mem_nil, or_false] at hopn
  rcases hopn with h|h|h|h|h|h|h|h|h <;> subst h <;> exact ⟨_, rfl⟩

/-- **New coverage: constant-offset `LOAD`.** The POC dropped it (`lowerLcmd`
    `filterMap`); the extended lowering returns the single-`loadMem` block. -/
theorem lowerLinstrExt_load (dst base : String) (off : Nat) :
    lowerLinstrExt (.Lopn [.reg dst] "LOAD" [.arr base off])
      = some [lowerLoad dst base off] := rfl

/-- **New coverage: constant-offset `STORE`.** -/
theorem lowerLinstrExt_store (dst base : String) (off : Nat) (val : LOperand) :
    lowerLinstrExt (.Lopn [.reg dst] "STORE" [.arr base off, val])
      = some [lowerStore base off (lowerJOperand val)] := rfl

/-! ## 6. Denotation preservation for the new arms

Against `JInstr`'s `runBlock` (the straight-line fold of `evalInstr`): the
lowered `LOAD` block leaves `dst` holding the loaded word `[base + off]`; the
lowered `STORE` block leaves the cell `[base + off]` holding the stored value.
Proved in general from the `JasminModel` model lemmas, not demo-anchored. -/

/-- **`LOAD` denotation.** `runBlock` of the lowered load leaves `dst` equal to
    the memory word at `[base + off]` in the initial state. -/
theorem lowerLinstrExt_load_denote (dst base : String) (off : Nat) (s : JState 64) :
    (runBlock s [lowerLoad dst base off]).get dst = s.load base (off : Int) := by
  show (runBlock s [lowerLoad dst base off]).get dst = s.load base (off : Int)
  simp only [lowerLoad, runBlock, evalInstr, x86_MOV, JState.load,
    JState.get_setReg_same]

/-- **`STORE` denotation.** `runBlock` of the lowered store leaves the cell
    `[base + off]` holding the stored value `src.eval s`. -/
theorem lowerLinstrExt_store_denote (base : String) (off : Nat) (src : JOperand)
    (s : JState 64) :
    (runBlock s [lowerStore base off src]).load base (off : Int) = x86_MOV (src.eval s) := by
  simp only [lowerStore, runBlock, evalInstr, JState.load_store_same]

/-! ## 7. Constant-time for the new arms (by construction)

Constant-offset memory is direct-addressed: `loadMem`/`storeMem` are `IsDirect`
(only the register-indexed `loadMemIdx`/`storeMemIdx` are excluded). So the
lowered blocks pass the decidable `allDirect` check and are constant-time via
`allDirect_constant_time` — the clean unconditional win, no `agreePub` premise. -/

/-- The lowered `LOAD` block is `allDirect` (constant-offset memory is direct). -/
theorem lowerLinstrExt_load_allDirect (dst base : String) (off : Nat) :
    allDirect [lowerLoad dst base off] = true := rfl

/-- The lowered `STORE` block is `allDirect`. -/
theorem lowerLinstrExt_store_allDirect (base : String) (off : Nat) (src : JOperand) :
    allDirect [lowerStore base off src] = true := rfl

/-- **`LOAD` is constant-time by construction.** Same machine leakage trace from
    any two initial states. -/
theorem lowerLinstrExt_load_constant_time (dst base : String) (off : Nat)
    (s₁ s₂ : JState 64) :
    blockLeak s₁ [lowerLoad dst base off] = blockLeak s₂ [lowerLoad dst base off] :=
  allDirect_constant_time _ (lowerLinstrExt_load_allDirect dst base off) s₁ s₂

/-- **`STORE` is constant-time by construction.** -/
theorem lowerLinstrExt_store_constant_time (base : String) (off : Nat) (src : JOperand)
    (s₁ s₂ : JState 64) :
    blockLeak s₁ [lowerStore base off src] = blockLeak s₂ [lowerStore base off src] :=
  allDirect_constant_time _ (lowerLinstrExt_store_allDirect base off src) s₁ s₂

/-! ## 8. Worked demo: a previously-`none` shape now lowering

`demoStore` is the `lprog` instruction `STORE op[1] := v` (the result-store of a
reg-ptr ABI: write register `v` to `op[1]`, i.e. `[op + 1]`). `lowerLinstr`
(POC) returns `none` for it — the `STORE` mnemonic, and the `arr` memory
operand, are both outside the POC table. `lowerLinstrExt` lowers it to a single
`storeMem`, with the right `runBlock` effect and `allDirect = true`. `demoLoad`
is the dual argument-load `LOAD t := ap[2]`. -/

/-- A previously-`none` `STORE op[1] := v`. -/
def demoStore : LinstrR := .Lopn [.reg "rout"] "STORE" [.arr "op" 1, .reg "v"]

/-- A previously-`none` `LOAD t := ap[2]`. -/
def demoLoad : LinstrR := .Lopn [.reg "t"] "LOAD" [.arr "ap" 2]

/-- The POC drops `demoStore` (returns `none`). -/
theorem demoStore_poc_none : lowerLinstr 64 ⟨0, demoStore⟩ = none := rfl

/-- The POC drops `demoLoad` (returns `none`). -/
theorem demoLoad_poc_none : lowerLinstr 64 ⟨0, demoLoad⟩ = none := rfl

/-- The extended lowering lowers `demoStore` to a single `storeMem`. -/
theorem demoStore_ext :
    lowerLinstrExt demoStore = some [.storeMem "op" (1 : Int) (.reg "v")] := rfl

/-- The extended lowering lowers `demoLoad` to a single `loadMem`. -/
theorem demoLoad_ext :
    lowerLinstrExt demoLoad = some [.loadMem "t" "ap" (2 : Int)] := rfl

/-- The demo store block is `allDirect` (constant-time class). -/
theorem demoStore_allDirect :
    allDirect [(.storeMem "op" (1 : Int) (.reg "v") : JInstr 64)] = true := by decide

/-- The demo load block is `allDirect`. -/
theorem demoLoad_allDirect :
    allDirect [(.loadMem "t" "ap" (2 : Int) : JInstr 64)] = true := by decide

/-- **Demo store effect.** Running the lowered `demoStore` from a state where
    register `v` holds `7` leaves the cell `[op + 1]` holding `7`. -/
theorem demoStore_effect :
    (runBlock ({ regs := fun r => if r = "v" then 7 else 0 } : JState 64)
        [.storeMem "op" (1 : Int) (.reg "v")]).load "op" (1 : Int) = 7 := by
  native_decide

/-- **Demo load effect.** Running the lowered `demoLoad` from a state where the
    cell `[ap + 2]` holds `9` leaves register `t` holding `9`. -/
theorem demoLoad_effect :
    (runBlock ({ regs := fun _ => 0, mem := fun b o => if b = "ap" ∧ o = 2 then 9 else 0 }
        : JState 64) [.loadMem "t" "ap" (2 : Int)]).get "t" = 9 := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtended
