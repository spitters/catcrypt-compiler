/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.Examples.MpnDecimalSpec
import CatCrypt.Crypto.Jasmin.Examples.MpnAddNAdcSpillPrototype
import CatCrypt.Crypto.Jasmin.Examples.MpnPowPrototype

set_option autoImplicit false

/-!
# Verified-pipeline emission of `mpn_to_string` — Nat → decimal char buffer

**EXPERIMENTAL FILE.**  This is the Jasmin-emission layer for Lean's runtime
`lean::mpn_to_string(a, lng, buf, lbuf) → char*` API.  It closes the last
"unverified glue" gap in the bignum-to-decimal pipeline:

* The **pure mathematical reference** is `MpnDecimalSpec.toDecimal` /
  `MpnDecimalSpec.chunkExtract` (algorithm-level base-conversion correctness),
  already proved against `Nat.digits 10` / `Nat.ofDigits 10`.
* This file emits the matching Jasmin kernel and pins the bridge `Prop`
  in the `MpnPowPrototype.MpnPowJasminRefines` style: sorry-free `Prop`
  recording the residual, with the algorithm-level math fully discharged
  upstream.

## NOT constant-time by design

`mpn_to_string` is **inherently data-dependent** at the kernel level:

* the outer loop runs once per decimal digit of the value, so the iteration
  count depends on the secret;
* the inner `#DIV_64` (128÷64-by-10) executes a variable-cycle hardware
  divide whose latency leaks the dividend;
* per-iteration byte writes to `buf` happen at addresses that depend on the
  number of digits emitted so far (a public count, but visibly value-derived).

This is acceptable — mainstream crypto never decimal-prints secret data
(decimal I/O is a UI surface, not a cryptographic primitive).  We do **not**
fake an `isCT_Cmd` proof here; the `decide` would either fail or rely on
data-dependent shapes outside our CT whitelist (see §3).

## Algorithm shape (matches `MpnDecimalSpec.toDecimal` at the limb level)

The kernel is the standard per-digit `divmod 10` print loop, mirroring
`MpnDecimalSpec.toDecimal n = if n = 0 then [] else (n % 10) :: toDecimal (n / 10)`:

```
q = a;                          // running quotient (single-limb here)
while (q != 0) {                // outer: O(log_10 q) iterations
    hi = 0;                     // reset upper for 128÷64
    _, _, _, _, _, q, r = #DIV_64(hi, q, d=10);   // q := q/10, r := q%10
    c64 = r + 48;               // ASCII '0' + digit
    c8  = (8u) c64;             // narrow to u8
    [:u8 buf + 0] = c8;         // emit one byte (LSB-first)
    buf += 1;
}
```

The output buffer is filled **LSB-first**; a caller-side reverse produces the
human-readable MSB-first string.  This matches `MpnDecimalSpec.toDecimal`'s
LSB-first list (equal to `Nat.digits 10 n` by `toDecimal_eq_digits`).

This emission targets the **single-limb** variant: `a` is a `reg u64`, not a
limb array.  The `lng = 1` case of the C ABI; the multi-limb variant
(`lng > 1`) is the chunk-by-`10^19` algorithm whose pure reference is
`MpnDecimalSpec.chunkExtract 19` (already proved value-preserving by
`MpnDecimalSpec.ofDigits_chunkExtract`).  Extending the emitted body to a
multi-limb input is a follow-up — the inner `divmod` becomes a limb-list
`mpnDivRem _ [B]` step (the verified `MpnDecimalSpec.limbDivBase_step`), and
the outer loop becomes "while limb-list nonzero" (the `mpnDivRem` quotient
limb-list shrinks).

## Bridge status: CLOSED as a theorem

The semantic bridge `MpnToStringJasminRefines` is **closed as a theorem**
(`MpnToStringJasminRefines_holds`).  The required `BignumExec` arms are
all wired:

* `#DIV_64`: commit `73773d02` — the `Copn .Oasm "DIV_64"` arm.
* `Papp1 (.Ozeroext _ _)`: commit `6571eecc` — the narrow-to-byte arm.
* `.Lmem .U8`: commit `6571eecc` — the byte-store arm (`storeMem8`).

The bridge proof is:

1. `bignumExec_execPrefix_step_with_d` — the 4-instruction divmod-by-10
   prefix `[hi := 0; DIV_64; c64 := r; c64 += 48]` lands `c64 := (q%10)+48`,
   `q := q/10`.
2. `bignumExec_execSuffix_step` — the 3-instruction emit-and-bump suffix
   `[c8 := (8u) c64; [:u8 buf+0] := c8; buf += 1]` writes one ASCII byte
   to memory and advances `buf`.
3. `bignumExec_loopBody_step` — composes prefix + suffix into one outer
   iteration.
4. `mpnToString_outer_loop` — well-founded induction on `qv.toNat`
   (decreases by factor 10 each iteration) closes the `Cwhile` loop.
5. `MpnToStringJasminRefines_holds` — combines the prelude (`d := 10;
   q := a`) with the outer-loop closure.

Axioms: only the standard kernel trio (`propext`, `Classical.choice`,
`Quot.sound`).  No `sorryAx`, no `native_decide.ax_1_1`.

## What is fully proved here

* The **pure algorithm-level reference** (in `MpnDecimalSpec`):
  `toDecimal n = Nat.digits 10 n`, `ofDigits_chunkExtract`,
  `limbDivBase_step` — all sorry-free, no new axioms.
* The **structural facts** about the emitted `body`: every per-iteration
  instruction is `.isNonControl`, the outer `Cwhile` has the standard
  `(n != 0)` guard shape (so the emitter recognizes it as a runtime loop),
  and the body has bounded size (10 instructions in the loop body).
* The **emission to a string**: `Emit.emitFunDecl mpnToStringFd = some _`.
  Verified by `#eval` and by the `emit_succeeds` example.
* `jasminc` accepts the emitted `.jazz` (verified offline; the byte-store
  syntax `[:u8 buf + 0] = c8;` and the `#DIV_64` 7-lvalue calling convention
  both type-check and pass register allocation in the actual `jasminc`
  release we use).
-/

namespace CatCrypt.Crypto.Jasmin.Examples.MpnToStringPrototype

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Emit
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.Examples.MpnDecimalSpec

/-! ## §1  The Jasmin body for `mpn_to_string` (single-limb input variant)

We reuse the helper `Var`/`PExpr`/`InstrR` constructors from
`MpnAddNAdcSpillPrototype` (re-imported via the chain through
`MpnAddPrototype`).  This keeps the body wire-format identical to the other
verified-pipeline kernels (`mpn_add_n`, `mpn_mul`, `mpn_pow`).
-/

/-- `reg u64` variable (mirror of `MpnAddNAdcSpillPrototype.vr`). -/
def vr (s : String) : Var := { vname := s, vtype := .sword .U64 }

/-- `reg u8` variable — the narrow byte register that holds an ASCII
    digit before it is stored to the output buffer. -/
def vrU8 (s : String) : Var := { vname := s, vtype := .sword .U8 }

/-- A `Pvar` reading register `s`. -/
def pv (s : String) : PExpr := .Pvar { gv := { var := vr s }, gs := false }

/-- A `Pvar` reading a `u8` register `s`. -/
def pvU8 (s : String) : PExpr := .Pvar { gv := { var := vrU8 s }, gs := false }

/-- `r := imm` — write a u64 constant. -/
def assignConst (r : String) (k : Int) : InstrR :=
  .Cassgn (.Lvar { var := vr r }) .AT_none (.sword .U64) (.Pconst k)

/-- `r := src` — u64 register-to-register copy. -/
def assignCopy (r src : String) : InstrR :=
  .Cassgn (.Lvar { var := vr r }) .AT_none (.sword .U64) (pv src)

/-- `r += k` / `r -= k` / `r *= k` scalar update.  Mirrors
    `MpnAddNAdcSpillPrototype.binImm`. -/
def binImm (r : String) (op : SOp2) (k : Int) : InstrR :=
  .Cassgn (.Lvar { var := vr r }) .AT_none (.sword .U64)
    (.Papp2 op (pv r) (.Pconst k))

/-- `#DIV_64` LVal bundle: five flag slots (`Lnone`) plus the two named
    outputs `q` (quotient) and `r` (remainder).  Total of 7 lvalues,
    matching the x86 `div` intrinsic's calling convention in Jasmin. -/
def divBundle (qName rName : String) : List LVal :=
  [.Lnone {} (.sbool),
   .Lnone {} (.sbool),
   .Lnone {} (.sbool),
   .Lnone {} (.sbool),
   .Lnone {} (.sbool),
   .Lvar { var := vr qName },
   .Lvar { var := vr rName }]

/-- `_, _, _, _, _, q, r := #DIV_64(hi, q, d)` — the inner divide step.
    Computes `(q, r) := ((hi · 2^64 + q) / d, (hi · 2^64 + q) % d)` via
    the hardware 128÷64 instruction.

    **NB**: As of commit `73773d02`, `BignumExec.execInstr` HAS a `#DIV_64`
    arm (`Copn .Oasm "DIV_64"` → `writeDivBundle (divrem64 hi lo d)`).  This
    is the inner-divide primitive `MpnDivRemPrototype` established.  The
    `bignumExec_execPrefix_step` lemma below exercises this arm. -/
def divCore : InstrR :=
  .Copn (divBundle "q" "r") .AT_none (.Oasm ⟨"DIV_64"⟩)
        [pv "hi", pv "q", pv "d"]

/-- `c8 := (8u) c64` — zero-extend / narrow the u64 ASCII char value to
    `u8` for the byte store.  This is the `JasminEmit`-supported shape
    `(8u) src;`.

    **NB**: `BignumExec.evalPExpr` does NOT have a `Papp1 (.Ozeroext _ _)`
    arm — see the file header.  The `bignumExec_execPrefix_step` lemma
    below proves the *prefix* of `loopBody` (up to and including
    `c64 += 48`) executes; this `narrowToByte` instruction is the first
    one that does not. -/
def narrowToByte : InstrR :=
  .Cassgn (.Lvar { var := vrU8 "c8" }) .AT_none (.sword .U8)
    (.Papp1 (.Ozeroext .U8 .U64) (pv "c64"))

/-- `[:u8 buf + 0] := c8` — the per-digit byte emission to the output
    buffer.  This is the emitter-supported shape
    `Cassgn (.Lmem .U8 …) _ _ (.Pvar _)`; `JasminEmit`'s `Lmem` arm
    handles arbitrary `WSize` parametrically, so `.U8` emits as
    `[:u8 buf + 0] = c8;`.

    **NB**: `BignumExec.execInstr` does NOT semantically execute the
    `.Lmem .U8` arm — only `.Lmem .U64` and `.Lmem .U32` are wired.
    Adding a per-byte `Mem.store8` is the residual the bridge records. -/
def storeByte : InstrR :=
  .Cassgn (.Lmem .U8 { var := vr "buf" } (.Pconst 0)) .AT_none (.sword .U8)
    (pvU8 "c8")

/-- One outer-loop iteration: reset `hi`, do the 128÷64 divide-by-10,
    convert remainder to ASCII, narrow, store, advance `buf`. -/
def loopBody : List InstrR :=
  [ assignConst "hi" 0
  , divCore
  , assignCopy "c64" "r"
  , binImm "c64" (.Oadd .U64) 48
  , narrowToByte
  , storeByte
  , binImm "buf" (.Oadd .U64) 1 ]

/-- Outer body: set up `d = 10`, copy `a → q`, then loop until `q == 0`.

    The `lng` parameter is currently unused — this is the single-limb
    variant (the `lng = 1` case of the C ABI).  `lbuf` is also unused
    here; bounds-checking against `lbuf` would be added in a fuller
    variant that returns the byte count.  Both unused parameters trigger
    `jasminc` warnings but do not block emission. -/
def body : List InstrR :=
  [ assignConst "d" 10
  , assignCopy "q" "a"
  , .Cwhile [] (.Papp2 (.Oneq .U64) (pv "q") (.Pconst 0)) loopBody ]

/-- `mpn_to_string(a, lng, buf, lbuf)` as a Jasmin `FunDecl`.  Matches
    Lean's runtime ABI

    ```
    char * mpn_to_string(mpn_digit const * a, size_t lng,
                         char * buf, size_t lbuf);
    ```

    declaratively (`mpn_digit = unsigned int = u32` in the C side, treated
    here as the low limb of a u64 register for the single-limb variant). -/
def mpnToStringFd : FunDecl where
  name := { name := "mpn_to_string" }
  params := [⟨{ var := vr "a" }⟩, ⟨{ var := vr "lng" }⟩,
             ⟨{ var := vr "buf" }⟩, ⟨{ var := vr "lbuf" }⟩]
  body := body
  results := []

/-! ## §2  Emission to Jasmin source

The body uses only `JasminEmit`-supported shapes:
* `.Cassgn (.Lvar _) _ _ (.Pconst _)`           — `d = 10;`, `hi = 0;`
* `.Cassgn (.Lvar _) _ _ (.Pvar _)`             — `q = a;`, `c64 = r;`
* `.Cassgn (.Lvar _) _ _ (.Papp2 op (pv) (.Pconst _))` — `c64 += 48;`, `buf += 1;`
* `.Cassgn (.Lvar _) _ _ (.Papp1 (.Ozeroext _ _) (.Pvar _))` — `c8 = (8u) c64;`
* `.Cassgn (.Lmem ws _ (.Pconst _)) _ _ (.Pvar _)`  — `[:u8 buf + 0] = c8;`
* `.Copn lvs _ (.Oasm _) args`                  — `_, …, q, r = #DIV_64(hi, q, d);`
* `.Cwhile [] (.Papp2 (.Oneq _) (.Pvar _) (.Pconst 0)) _`  — `while (q != 0) { … }`

Every shape is in `emitInstr` — emission succeeds. -/

/-- The emitted Jasmin source (option-valued; `none` indicates an
    emitter-unsupported shape, which `body` deliberately avoids). -/
def emitted : Option String := emitFunDecl mpnToStringFd

/-- **Emission succeeds** — the body is built entirely from
    `JasminEmit`-supported instruction shapes (see §2). -/
example : (emitFunDecl mpnToStringFd).isSome := by
  -- `emitFunDecl` is computable; reduce to a concrete `some _`.
  native_decide

-- The real `.jazz` source, for offline `jasminc` testing.
#eval match emitted with | some s => s | none => "EMIT FAILED"

/-! ## §3  CT honesty — `mpn_to_string` is NOT constant-time (despite the
syntactic `isCT_Cmd` returning `true`)

The current `JasminCT.isCT_Cmd` predicate is a **shape-level** check that
returns `true` for a `Cwhile [] (n != 0) _` shape **without descending into
the loop body**.  Our `body` matches that shape — the outer `while (q !=
0) { … }` — so `isCT_Cmd body = true` by `decide`.

This is a **known limitation of the current syntactic predicate**, not a
soundness claim about `mpn_to_string`.  The body in fact contains two
non-CT operations:

1. `.Cassgn (.Lmem .U8 _ _) _ _ (.Pvar _)` — the byte store — is not in
   `JasminCT.isCT_LVal`'s whitelist (only `.Lmem .U64` and `.Lmem .U32`
   are CT-accepted).  A body-descending CT predicate would reject it.
2. `Copn _ _ (.Oasm "DIV_64") _` — the divide intrinsic — is not in
   `JasminCT.ct_intrinsic`'s whitelist.  A body-descending CT predicate
   would reject it too (`#DIV_64` has data-dependent execution time on
   x86).

Both rejections are correct: `mpn_to_string` is a UI surface, not a
cryptographic primitive, and the C/Lean runtime use is unrelated to any
secret-handling path.  The CT obligation downstream code can rely on is
**not** a per-function CT proof for `mpn_to_string`; it is the
whole-program guarantee that `mpn_to_string` is **never called on
secret-dependent inputs** in the verified pipeline, established by the
L1 driver's call-site discipline.

The `isCT_Cmd body = true` example below is recorded for honesty about
*what the current predicate computes* — and the prose above documents
the structural reasons that classification is *uninformative* for this
kernel.
-/

/-- After `fe13561a` (`isCT_Cmd` now body-recursive), the predicate
    **correctly** rejects this body — it contains a `.Lmem .U8` store and
    a `#DIV_64` intrinsic, neither of which is whitelisted (and `#DIV_64`
    is variable-latency on most uarchs).  `mpn_to_string` is not
    constant-time by design (termination depends on the value of `a`).
    Whole-program guarantee: never called on secret data. -/
example : isCT_Cmd body = false := by native_decide

/-! ## §3.5  The per-iteration prefix-step (fully proved)

Even before the two remaining `BignumExec` arms (`Papp1 (.Ozeroext _ _)`
and `.Lmem .U8`) land, the *register* content of one outer-loop iteration
is fully discharged by the present interpreter.

The 4-instruction prefix `execPrefix` covers everything from `hi := 0`
through `c64 += 48` — i.e., the divmod-by-10 and the ASCII-offset add.
After the prefix runs, register `c64` holds the ASCII byte `(q.toNat % 10)
+ 48` and register `q` holds the new dividend `q.toNat / 10`.  The
remaining 3 instructions of `loopBody` (narrow to `c8`, byte-store, `buf
+= 1`) consume the two gap arms; their algorithm-level content is just
"copy the low byte of `c64` to `mem[buf]` and bump `buf`" — no math.

This is the per-iteration *register-frame* lemma the eventual outer-loop
induction will instantiate, with the byte-store frame composed on top.
-/

/-- The 4-instruction prefix of `loopBody` that executes correctly under
    the present interpreter (`#DIV_64` is wired; `assignConst`,
    `assignCopy`, `binImm` are all `Lvar`-writing `Cassgn` with `Pconst` /
    `Pvar` / `Papp2 .Oadd` rhs — all in `evalPExpr`). -/
def execPrefix : List InstrR :=
  [ assignConst "hi" 0
  , divCore
  , assignCopy "c64" "r"
  , binImm "c64" (.Oadd .U64) 48 ]

set_option linter.unusedSimpArgs false in
/-- **Per-iteration prefix-step.**  Starting from a state where `d` holds
    the divisor 10 and `q` holds the current dividend `qv`, executing the
    4-instruction prefix lands a state where:
    * `q` is the new quotient `BitVec.ofNat 64 (qv.toNat / 10)`,
    * `r` is the remainder `BitVec.ofNat 64 (qv.toNat % 10)`,
    * `c64 = r + 48` is the ASCII digit register, and
    * memory and the `buf`/`a` registers are unchanged.

    This is the *register* content of one `mpn_to_string` outer-loop
    iteration; the remaining 3 instructions of `loopBody`
    (`narrowToByte`, `storeByte`, `buf += 1`) consume the two
    `BignumExec` gap arms `Papp1 (.Ozeroext _ _)` and `.Lmem .U8`.

    No hypothesis on `qv.toNat ≠ 0` is needed at the *register* level —
    the prefix executes regardless of whether `q = 0` (the outer
    `Cwhile` guard handles the exit case).  When `qv = 0` we get
    `c64 = 48` (ASCII `'0'`), which is consistent with the trailing-zero
    semantics of `toDecimal`. -/
theorem bignumExec_execPrefix_step (s : BignumState) (qv : BitVec 64)
    (hd : s.regs "d" = 10) (hqval : s.regs "q" = qv) :
    ∃ s', bignumExec execPrefix s = some s' ∧
      s'.regs "q" = BitVec.ofNat 64 (qv.toNat / 10) ∧
      s'.regs "r" = BitVec.ofNat 64 (qv.toNat % 10) ∧
      s'.regs "c64" = BitVec.ofNat 64 (qv.toNat % 10) + 48 ∧
      s'.regs "buf" = s.regs "buf" ∧
      s'.regs "a" = s.regs "a" ∧
      s'.mem = s.mem := by
  -- Unfold the 4-step bignumExec into the four execInstr matches.
  -- The first three are `Cassgn (Lvar _) _ _ rhs`; the fourth is `Copn`.
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [execPrefix, bignumExec, execInstr, assignConst, assignCopy, binImm,
               divCore, divBundle, evalPExpr, pv, vr, writeDivBundle,
               MpnAddPrototype.setReg_regs, MpnAddPrototype.setReg_mem,
               divrem64, hd, hqval,
               Option.bind_some, bind, Option.bind, String.reduceEq,
               ↓reduceIte, if_true, if_false, reduceIte,
               show BitVec.ofInt 64 0 = (0 : BitVec 64) from rfl,
               show BitVec.ofInt 64 48 = (48 : BitVec 64) from rfl,
               show ((10 : BitVec 64).toNat) = 10 from by decide,
               show ((0 : BitVec 64).toNat) = 0 from by decide,
               Nat.zero_mul, Nat.zero_add]

/-- `execPrefix` is straight-line — all four instructions are `Cassgn`
    (Lvar destination) or `Copn` with no nested `Cwhile`/`Cif`/`Ccall`. -/
theorem execPrefix_straightLine : InstrR.bodyIsStraightLine execPrefix := by
  simp only [execPrefix, assignConst, divCore, assignCopy, binImm,
             InstrR.bodyIsStraightLine, InstrR.isStraightLine, and_self]

/-- Every instruction in `execPrefix` is `isNonControl` (so the prefix
    commutes with the forward `bignumExecFuel_append_join`). -/
theorem execPrefix_nonControl : ∀ i ∈ execPrefix, i.isNonControl := by
  intro i hi
  simp only [execPrefix, assignConst, divCore, assignCopy, binImm,
             List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h <;> (subst h; exact True.intro)

/-! ## §3.6  Projection simp lemmas for `storeMem8`

The OO2 commit (`6571eecc`) added `storeMem8` to `BignumExec` but did not
expose `@[simp]` projection lemmas.  We add them locally — both projections
are definitional `rfl`s and mirror the existing `setReg_regs` / `storeMem_regs`
lemmas used throughout `MpnAddPrototype`. -/

@[simp] theorem storeMem8_regs (s : BignumState) (a : UInt64) (v : UInt8) :
    (storeMem8 s a v).regs = s.regs := rfl

@[simp] theorem storeMem8_mem (s : BignumState) (a : UInt64) (v : UInt8) :
    (storeMem8 s a v).mem = s.mem.storeByte a v := rfl

/-! ## §3.7  The per-iteration suffix-step (emit-and-bump)

The 3-instruction suffix that runs *after* `execPrefix`:
* `narrowToByte` — `c8 := (8u) c64`
* `storeByte`   — `[:u8 buf + 0] := c8`
* `binImm "buf" .Oadd 1` — `buf += 1`

Given a state where `c64` holds an ASCII byte (`digit + 48` with
`digit < 10`, hence `< 256`), this suffix writes that byte at the
current `buf` address and advances `buf` by 1.  Other registers and
memory outside `buf` are unchanged.

This consumes the two `BignumExec` arms wired in `6571eecc`:
`Papp1 (.Ozeroext .U8 .U64)` (the narrow) and `.Lmem .U8` (the byte
store). -/

/-- The 3-instruction emit-and-bump suffix of `loopBody`. -/
def execSuffix : List InstrR :=
  [ narrowToByte
  , storeByte
  , binImm "buf" (.Oadd .U64) 1 ]

set_option linter.unusedSimpArgs false in
/-- **Per-iteration suffix-step.**  Starting from a state where the `c64`
    register holds an ASCII byte (i.e., `digit + 48` with `digit < 10` so
    the result fits in `< 256`), the 3-instruction suffix:
    * writes the low byte of `c64` to memory at the current `buf` address,
    * advances `buf` by 1,
    * leaves all other registers and other memory unchanged. -/
theorem bignumExec_execSuffix_step (s : BignumState) (digit : Nat)
    (hdigit : digit < 10)
    (hc64 : s.regs "c64" = BitVec.ofNat 64 (digit + 48)) :
    ∃ s', bignumExec execSuffix s = some s' ∧
      s'.regs "buf" = s.regs "buf" + 1 ∧
      s'.regs "q" = s.regs "q" ∧
      s'.regs "r" = s.regs "r" ∧
      s'.regs "a" = s.regs "a" ∧
      s'.regs "d" = s.regs "d" ∧
      s'.regs "c64" = s.regs "c64" ∧
      s'.mem = s.mem.storeByte
        (UInt64.ofNat (s.regs "buf").toNat) (UInt8.ofNat (digit + 48)) ∧
      (∀ a, a ≠ UInt64.ofNat (s.regs "buf").toNat →
        s'.mem.loadByte a = s.mem.loadByte a) := by
  -- Step through the three instructions manually so we keep tight
  -- control over `simp`'s rewriting.
  -- After step 1 (`narrowToByte`):
  --   c8 register := BitVec.ofNat 64 ((c64.toNat) % 2^8)
  --                = BitVec.ofNat 64 ((digit + 48) % 256)
  --                = BitVec.ofNat 64 (digit + 48)        (since digit+48 < 256)
  -- The other registers and memory are unchanged.
  have hdigit_lt : digit + 48 < 256 := by omega
  have hc64_toNat : (BitVec.ofNat 64 (digit + 48)).toNat = digit + 48 := by
    simp [BitVec.toNat_ofNat]; omega
  have h_narrow_val : (s.regs "c64").toNat % (2 ^ WSize.U8.bits)
      = digit + 48 := by
    rw [hc64, hc64_toNat]
    show (digit + 48) % 256 = digit + 48
    omega
  -- Step 2 result:
  -- After narrowToByte, define s1 := setReg s "c8" (BitVec.ofNat 64 (digit+48)).
  set s1 := setReg s "c8" (BitVec.ofNat 64 (digit + 48)) with hs1
  have hexec1 : execInstr s narrowToByte = some s1 := by
    simp only [narrowToByte, execInstr, evalPExpr, pv, vr, vrU8, bind, Option.bind,
               WSize.bits, hs1]
    congr 1
    rw [show (2 : Nat) ^ 8 = 256 from by decide]
    rw [hc64, hc64_toNat]
    show setReg s "c8" (BitVec.ofNat 64 ((digit + 48) % 256))
       = setReg s "c8" (BitVec.ofNat 64 (digit + 48))
    have : (digit + 48) % 256 = digit + 48 := by omega
    rw [this]
  -- Step 2: storeByte writes to memory at addr := UInt64.ofNat (s1.regs "buf").toNat.
  -- s1.regs "buf" = s.regs "buf" (since we only set "c8").
  have hbuf1 : s1.regs "buf" = s.regs "buf" := by
    simp only [hs1, MpnAddPrototype.setReg_regs]; rfl
  have haddr1 : resolveAddr s1 { var := vr "buf" } (.Pconst 0)
      = some (UInt64.ofNat (s.regs "buf").toNat) := by
    simp only [resolveAddr, vr, hbuf1]
    congr 1
    apply UInt64.toNat.inj
    simp only [UInt64.toNat_ofNat', BitVec.toNat_add,
               show ((BitVec.ofInt 64 0 : BitVec 64).toNat = 0) from by decide,
               Nat.add_zero, Nat.mod_mod]
  -- `evalPExpr s1 (pvU8 "c8") = some (s1.regs "c8") = some (BitVec.ofNat 64 (digit+48))`.
  have hc8val1 : s1.regs "c8" = BitVec.ofNat 64 (digit + 48) := by
    simp only [hs1, MpnAddPrototype.setReg_regs, if_true]
  have hevalC8 : evalPExpr s1 (pvU8 "c8") = some (BitVec.ofNat 64 (digit + 48)) := by
    simp only [pvU8, vrU8, evalPExpr, hc8val1]
  -- After storeByte: s2 := storeMem8 s1 addr (UInt8.ofNat ((BitVec.ofNat 64 (digit+48)).toNat % 256))
  --                  = storeMem8 s1 addr (UInt8.ofNat (digit+48))  (since digit+48 < 256)
  have h_store_byte : ((BitVec.ofNat 64 (digit + 48)).toNat % 256) = digit + 48 := by
    rw [hc64_toNat]; omega
  set s2 := storeMem8 s1 (UInt64.ofNat (s.regs "buf").toNat)
                       (UInt8.ofNat (digit + 48)) with hs2
  have hexec2 : execInstr s1 storeByte = some s2 := by
    simp only [storeByte, execInstr, bind, Option.bind, hevalC8, haddr1, hs2,
               h_store_byte]
  -- s2.regs = s1.regs, so "buf" is still s.regs "buf" in s2.
  have hbuf2 : s2.regs "buf" = s.regs "buf" := by
    simp only [hs2, storeMem8_regs, hbuf1]
  -- Step 3: binImm "buf" .Oadd 1 — buf += 1.
  -- This is Cassgn (Lvar "buf") with rhs Papp2 .Oadd (pv "buf") (.Pconst 1).
  -- evalPExpr s2 (Papp2 .Oadd (pv "buf") (.Pconst 1))
  --   = some ((s2.regs "buf") + BitVec.ofInt 64 1)
  --   = some (s.regs "buf" + 1)
  have hone : (BitVec.ofInt 64 1 : BitVec 64) = 1 := rfl
  have heval_buf_inc : evalPExpr s2 (.Papp2 (.Oadd .U64) (pv "buf") (.Pconst 1))
      = some (s.regs "buf" + 1) := by
    simp only [evalPExpr, pv, vr, bind, Option.bind, hbuf2, hone]
  set s3 := setReg s2 "buf" (s.regs "buf" + 1) with hs3
  have hexec3 : execInstr s2 (binImm "buf" (.Oadd .U64) 1) = some s3 := by
    simp only [binImm, execInstr, bind, Option.bind, heval_buf_inc, hs3, vr]
  -- Now combine: bignumExec execSuffix s = some s3.
  refine ⟨s3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- The execSuffix runs through the three instructions.
    simp only [execSuffix, bignumExec, hexec1, hexec2, hexec3]
  · -- s3.regs "buf" = s.regs "buf" + 1.
    simp only [hs3, MpnAddPrototype.setReg_regs, if_true]
  · -- s3.regs "q" = s.regs "q".  Trace: s3 ← s2 ← s1 ← s; only "c8" and "buf" (in s3) and mem changed.
    simp only [hs3, MpnAddPrototype.setReg_regs, hs2, storeMem8_regs, hs1, MpnAddPrototype.setReg_regs,
               show ("q" = "buf") = False from by decide,
               show ("q" = "c8") = False from by decide, if_false]
  · simp only [hs3, MpnAddPrototype.setReg_regs, hs2, storeMem8_regs, hs1, MpnAddPrototype.setReg_regs,
               show ("r" = "buf") = False from by decide,
               show ("r" = "c8") = False from by decide, if_false]
  · simp only [hs3, MpnAddPrototype.setReg_regs, hs2, storeMem8_regs, hs1, MpnAddPrototype.setReg_regs,
               show ("a" = "buf") = False from by decide,
               show ("a" = "c8") = False from by decide, if_false]
  · simp only [hs3, MpnAddPrototype.setReg_regs, hs2, storeMem8_regs, hs1, MpnAddPrototype.setReg_regs,
               show ("d" = "buf") = False from by decide,
               show ("d" = "c8") = False from by decide, if_false]
  · simp only [hs3, MpnAddPrototype.setReg_regs, hs2, storeMem8_regs, hs1, MpnAddPrototype.setReg_regs,
               show ("c64" = "buf") = False from by decide,
               show ("c64" = "c8") = False from by decide, if_false]
  · -- s3.mem = s2.mem = (storeMem8 s1 addr v).mem = s1.mem.storeByte addr v
    --         = s.mem.storeByte addr v
    simp only [hs3, MpnAddPrototype.setReg_mem, hs2, storeMem8_mem,
               hs1, MpnAddPrototype.setReg_mem]
  · -- Frame: addresses other than buf are unchanged in s3.mem.
    intro a ha
    simp only [hs3, MpnAddPrototype.setReg_mem, hs2, storeMem8_mem,
               hs1, MpnAddPrototype.setReg_mem]
    exact Mem.loadByte_storeByte_other _ _ _ _ ha

/-- `execSuffix` is straight-line. -/
theorem execSuffix_straightLine : InstrR.bodyIsStraightLine execSuffix := by
  simp only [execSuffix, narrowToByte, storeByte, binImm,
             InstrR.bodyIsStraightLine, InstrR.isStraightLine, and_self]

/-- Every instruction in `execSuffix` is `isNonControl`. -/
theorem execSuffix_nonControl : ∀ i ∈ execSuffix, i.isNonControl := by
  intro i hi
  simp only [execSuffix, narrowToByte, storeByte, binImm,
             List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h <;> (subst h; exact True.intro)

/-! ## §4  The pinned bridge `Prop` — `MpnToStringJasminRefines`

In the precise `MpnPowPrototype.MpnPowJasminRefines` /
`MpnAdd32Refines.MpnAdd32JasminRefinesProp` style: a sorry-free `Prop`
identifying the bridge obligation.  `#DIV_64` is now wired (commit
`73773d02`); once `BignumExec` learns `Papp1 (.Ozeroext _ _)` and
`.Lmem .U8` semantics (the two remaining open primitives — see file
header), this residual instantiates to a closed theorem **without
restating the obligation**.  The per-iteration *register* content of the
loop body is already proved (`bignumExec_execPrefix_step` below).

### Why the algorithm-level math is already discharged

The per-iteration step rewrites
`(q_in, buf_in, digits_so_far) ↦ (q_in / 10, buf_in + 1, digits_so_far ++ [q_in % 10])`,
and the closed-form invariant after `k` iterations is `digits_so_far =
toDecimal (a / 10^k)`'s prefix.  Both pieces are the inductive shape of
`MpnDecimalSpec.toDecimal`'s recursion (`toDecimal_of_ne_zero`).  The
buffer-prefix correctness reduces to
`MpnDecimalSpec.toDecimal_eq_digits` — i.e., `Nat.digits 10`.  No
algorithm-level lemma is missing.

### What the bridge says

"Running `body` from a state where `a` holds the input value (as a
`BitVec 64`), under a sufficiently large fuel, produces a final state
whose memory at `buf` holds the LSB-first decimal digits of `a.toNat` as
ASCII bytes."

Stated against the pure reference `MpnDecimalSpec.toDecimal`:
each emitted byte at offset `k` equals `48 + (toDecimal a.toNat).get k`
(ASCII `'0'` plus the `k`-th decimal digit).
-/

/-- The byte at offset `k` in the buffer should equal `48 + d` where `d`
    is the `k`-th decimal digit of `n` (LSB-first).  Returns `0` if `k` is
    out of range (no more digits to emit).  This is the per-byte
    correctness target. -/
def expectedByte (n k : Nat) : Nat :=
  match (toDecimal n)[k]? with
  | some d => 48 + d
  | none   => 0

/-- The number of decimal digits of `n` — equivalently the iteration count
    of the outer loop.  Equals `(Nat.digits 10 n).length` by
    `MpnDecimalSpec.toDecimal_eq_digits`. -/
def numDigits (n : Nat) : Nat := (toDecimal n).length

/-- `numDigits = (Nat.digits 10 _).length` — the buffer length the kernel
    will fill.  Direct corollary of `toDecimal_eq_digits`. -/
theorem numDigits_eq_digits_length (n : Nat) :
    numDigits n = (Nat.digits 10 n).length := by
  unfold numDigits
  rw [toDecimal_eq_digits]

/-- **The `mpn_to_string` Jasmin refinement obligation.**

    Stated as a sorry-free `Prop`.  Pins the bridge in the precise
    `MpnPowPrototype.MpnPowJasminRefines` /
    `MpnAdd32Refines.MpnAdd32JasminRefinesProp` style.

    `#DIV_64` is now wired (commit `73773d02`).  The two remaining open
    primitives are `Papp1 (.Ozeroext _ _)` (the `(8u) c64` narrow) and
    `.Lmem .U8` (the per-byte store) — both mechanical extensions a future
    byte-mem track will provide.  Once both are in `BignumExec`, the
    residual proof is a per-iteration induction mirroring
    `MpnAddPrototype.mpnAddN_loop`, with the per-iteration *register*
    content already discharged by `bignumExec_execPrefix_step` below.
    The algorithm-level math (LSB-first decimal recursion) is fully
    discharged in `MpnDecimalSpec`.

    Hypotheses:
    * `s.regs "a"` holds the value to convert.
    * `s.regs "buf"` is the output buffer base; the region
      `[buf, buf + numDigits a.toNat)` is in writable memory.
    * `fuel` covers the outer-loop iteration count plus the body cost.

    Conclusion:
    * After running `body`, the byte at `buf + k` (for `0 ≤ k <
      numDigits a.toNat`) equals `expectedByte a.toNat k` — i.e.
      ASCII `'0' + k`-th decimal digit of `a.toNat`. -/
def mpnToString_outer_loop_obligation : Prop :=
  ∀ (s : BignumState) (a : BitVec 64) (fuel : Nat),
    s.regs "a" = a →
    fuel > 7 * numDigits a.toNat + 4 →
    ∃ s', bignumExecFuel emptyRegistry fuel body s = some s' ∧
      -- Per-byte correctness: every position in the filled range holds
      -- the expected ASCII digit.
      ∀ k, k < numDigits a.toNat →
        ∃ b : UInt8, s'.mem.loadByte
          (UInt64.ofNat ((s.regs "buf").toNat + k)) = some b ∧
        b.toNat = expectedByte a.toNat k

/-- **`MpnToStringJasminRefines`** — the canonical bridge `Prop` for the
    emitted `mpn_to_string` body, identified with the residual
    `mpnToString_outer_loop_obligation`.

    Same packaging convention as `MpnPowPrototype.MpnPowJasminRefines`:
    an `abbrev` rather than a `def`, so downstream sites can refer to
    the bridge statement by its canonical name without restatement. -/
abbrev MpnToStringJasminRefines : Prop := mpnToString_outer_loop_obligation

/-! ## §4.5  Auxiliary BitVec/numeric facts

A few small numeric lemmas used by the outer-loop induction.  Kept local
to this file so the proof script can rely on a tight, named simp set. -/

/-- `loopBody` decomposes as `execPrefix ++ execSuffix`. -/
theorem loopBody_eq_prefix_append_suffix : loopBody = execPrefix ++ execSuffix := by
  rfl

/-- `loopBody` is straight-line (all 7 instructions are `Cassgn`/`Copn`). -/
theorem loopBody_straightLine : InstrR.bodyIsStraightLine loopBody := by
  simp only [loopBody, assignConst, divCore, assignCopy, binImm,
             narrowToByte, storeByte,
             InstrR.bodyIsStraightLine, InstrR.isStraightLine, and_self]

/-- Every instruction in `loopBody` is `isNonControl`. -/
theorem loopBody_nonControl : ∀ i ∈ loopBody, i.isNonControl := by
  intro i hi
  simp only [loopBody, assignConst, divCore, assignCopy, binImm,
             narrowToByte, storeByte,
             List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h <;> (subst h; exact True.intro)

/-- Loop-guard `q != 0` evaluates to `1` when register `q` is nonzero. -/
theorem evalPExpr_qLoopCond_true (s : BignumState) (hq : s.regs "q" ≠ 0) :
    evalPExpr s (.Papp2 (.Oneq .U64) (pv "q") (.Pconst 0)) = some 1 := by
  rw [pv, evalPExpr]
  simp only [evalPExpr, vr, bind, Option.bind,
    show (BitVec.ofInt 64 0 : BitVec 64) = 0 from rfl]
  rw [if_neg hq]

/-- Loop-guard `q != 0` evaluates to `0` when register `q` is `0`. -/
theorem evalPExpr_qLoopCond_false (s : BignumState) (hq : s.regs "q" = 0) :
    evalPExpr s (.Papp2 (.Oneq .U64) (pv "q") (.Pconst 0)) = some 0 := by
  rw [pv, evalPExpr]
  simp only [evalPExpr, vr, bind, Option.bind,
    show (BitVec.ofInt 64 0 : BitVec 64) = 0 from rfl]
  rw [if_pos hq]

/-- **Forward one-iteration rule for the outer `q != 0` loop.**  Mirrors
    `MpnAddPrototype.bignumExecFuel_loop_step` retargeted at this file's
    `loopBody`.  One iteration costs 2 fuel (Cwhile→Cif→body), and the
    straight-line `loopBody` consumes one more for the empty
    continuation join, giving the `f + 3` total. -/
theorem bignumExecFuel_qLoop_step (reg : BignumRegistry) (f : Nat)
    (cond : PExpr) (s s_mid s' : BignumState)
    (hcond : evalPExpr s cond = some 1)
    (hbody : bignumExec loopBody s = some s_mid)
    (hrec : bignumExecFuel reg (f + 1) [.Cwhile [] cond loopBody] s_mid = some s') :
    bignumExecFuel reg (f + 3) [.Cwhile [] cond loopBody] s = some s' := by
  have hsl : bignumExecFuel reg (f + 1) loopBody s = some s_mid := by
    rw [bignumExecFuel_eq_bignumExec_of_straightLine reg f loopBody s loopBody_straightLine]
    exact hbody
  conv_lhs => rw [show f + 3 = (f + 2) + 1 from rfl, bignumExecFuel]
  simp only [List.nil_append, List.append_nil, bignumExecFuel, hcond, bne_iff_ne, ne_eq,
    show ((1 : BitVec 64) ≠ 0) from by decide, not_false_eq_true, if_true]
  rw [bignumExecFuel_append_join reg (f + 1) loopBody [.Cwhile [] cond loopBody]
        loopBody_nonControl s s_mid s' hsl hrec]

/-- Local copy of `bignumExec_append_some_local` — forward append join
    for `bignumExec`. -/
private theorem bignumExec_append_some_local
    (b1 b2 : List InstrR) (s s_mid s' : BignumState)
    (h1 : bignumExec b1 s = some s_mid)
    (h2 : bignumExec b2 s_mid = some s') :
    bignumExec (b1 ++ b2) s = some s' := by
  induction b1 generalizing s with
  | nil =>
    simp [bignumExec] at h1
    rw [← h1] at h2; simp [bignumExec]; exact h2
  | cons i b1' ih =>
    simp only [bignumExec] at h1
    cases h_step : execInstr s i with
    | none => rw [h_step] at h1; simp at h1
    | some s1 =>
      rw [h_step] at h1
      simp only [List.cons_append, bignumExec, h_step]
      exact ih s1 h1

set_option linter.unusedSimpArgs false in
/-- **Strengthened per-iteration prefix-step.**  Same statement as
    `bignumExec_execPrefix_step` but additionally exposes preservation of
    register `d` (the divisor 10, which the prefix never overwrites).
    This is needed for the outer-loop induction, where successive
    iterations need to know `d` is still 10. -/
theorem bignumExec_execPrefix_step_with_d (s : BignumState) (qv : BitVec 64)
    (hd : s.regs "d" = 10) (hqval : s.regs "q" = qv) :
    ∃ s', bignumExec execPrefix s = some s' ∧
      s'.regs "q" = BitVec.ofNat 64 (qv.toNat / 10) ∧
      s'.regs "r" = BitVec.ofNat 64 (qv.toNat % 10) ∧
      s'.regs "c64" = BitVec.ofNat 64 (qv.toNat % 10) + 48 ∧
      s'.regs "buf" = s.regs "buf" ∧
      s'.regs "a" = s.regs "a" ∧
      s'.regs "d" = s.regs "d" ∧
      s'.mem = s.mem := by
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [execPrefix, bignumExec, execInstr, assignConst, assignCopy, binImm,
               divCore, divBundle, evalPExpr, pv, vr, writeDivBundle,
               MpnAddPrototype.setReg_regs, MpnAddPrototype.setReg_mem,
               divrem64, hd, hqval,
               Option.bind_some, bind, Option.bind, String.reduceEq,
               ↓reduceIte, if_true, if_false, reduceIte,
               show BitVec.ofInt 64 0 = (0 : BitVec 64) from rfl,
               show BitVec.ofInt 64 48 = (48 : BitVec 64) from rfl,
               show ((10 : BitVec 64).toNat) = 10 from by decide,
               show ((0 : BitVec 64).toNat) = 0 from by decide,
               Nat.zero_mul, Nat.zero_add]

/-- **Per-iteration `loopBody` step.**  Composing
    `bignumExec_execPrefix_step_with_d` with `bignumExec_execSuffix_step`,
    this gives the full per-iteration effect: starting from a state with
    `d = 10` and `q = qv`, `bignumExec loopBody s` yields a state where:
    * `q` is the new dividend `qv / 10` (BitVec form),
    * `buf` is advanced by 1,
    * memory has a byte `(qv % 10) + 48` written at the old `buf` address,
    * `d` is preserved (still 10),
    * other registers and memory cells (outside `buf`) are unchanged. -/
theorem bignumExec_loopBody_step (s : BignumState) (qv : BitVec 64)
    (hd : s.regs "d" = 10) (hqval : s.regs "q" = qv) :
    ∃ s', bignumExec loopBody s = some s' ∧
      s'.regs "q" = BitVec.ofNat 64 (qv.toNat / 10) ∧
      s'.regs "buf" = s.regs "buf" + 1 ∧
      s'.regs "a" = s.regs "a" ∧
      s'.regs "d" = s.regs "d" ∧
      s'.mem = s.mem.storeByte
        (UInt64.ofNat (s.regs "buf").toNat)
        (UInt8.ofNat (qv.toNat % 10 + 48)) ∧
      (∀ a, a ≠ UInt64.ofNat (s.regs "buf").toNat →
        s'.mem.loadByte a = s.mem.loadByte a) := by
  -- Step 1: run the prefix (using strengthened version with d preservation).
  obtain ⟨s1, hs1, hs1_q, _hs1_r, hs1_c64, hs1_buf, hs1_a, hs1_d, hs1_mem⟩ :=
    bignumExec_execPrefix_step_with_d s qv hd hqval
  -- Step 2: run the suffix from s1.
  have hdigit_lt : qv.toNat % 10 < 10 := Nat.mod_lt _ (by decide)
  have hsum_eq : BitVec.ofNat 64 (qv.toNat % 10) + (48 : BitVec 64)
      = BitVec.ofNat 64 (qv.toNat % 10 + 48) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
               show ((48 : BitVec 64).toNat) = 48 from by decide]
    have h1 : qv.toNat % 10 % 2 ^ 64 = qv.toNat % 10 := by
      have : qv.toNat % 10 < 2 ^ 64 := by
        have := hdigit_lt; omega
      omega
    have h2 : (qv.toNat % 10 + 48) % 2 ^ 64 = qv.toNat % 10 + 48 := by
      have : qv.toNat % 10 + 48 < 2 ^ 64 := by
        have := hdigit_lt; omega
      omega
    rw [h1, h2]
  have hc64_s1 : s1.regs "c64" = BitVec.ofNat 64 (qv.toNat % 10 + 48) := by
    rw [hs1_c64, hsum_eq]
  obtain ⟨s2, hs2, hs2_buf, hs2_q, _hs2_r, hs2_a, hs2_d, _hs2_c64, hs2_mem, hs2_frame⟩ :=
    bignumExec_execSuffix_step s1 (qv.toNat % 10) hdigit_lt hc64_s1
  -- Combine: bignumExec loopBody s = bignumExec (prefix ++ suffix) s
  --                                = bignumExec suffix s1 = some s2.
  refine ⟨s2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [loopBody_eq_prefix_append_suffix]
    exact bignumExec_append_some_local execPrefix execSuffix s s1 s2 hs1 hs2
  · rw [hs2_q, hs1_q]
  · rw [hs2_buf, hs1_buf]
  · rw [hs2_a, hs1_a]
  · rw [hs2_d, hs1_d]
  · rw [hs2_mem, hs1_buf, hs1_mem]
  · intro a ha
    rw [hs1_buf] at hs2_frame
    rw [hs2_frame a ha, hs1_mem]

/-- `BitVec.ofNat 64 (qv.toNat / 10) = 0` iff `qv.toNat < 10`.  This is
    the BitVec form of the loop-exit condition `q == 0` after one
    divmod-by-10 step.  Used to detect base-case in the loop induction. -/
theorem bv_div10_eq_zero_iff (qv : BitVec 64) :
    BitVec.ofNat 64 (qv.toNat / 10) = (0 : BitVec 64) ↔ qv.toNat < 10 := by
  have hqv : qv.toNat < 2 ^ 64 := qv.isLt
  have hdiv : qv.toNat / 10 < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hqv
  have hzeroToNat : (0 : BitVec 64).toNat = 0 := by decide
  constructor
  · intro h
    have hToNat : (BitVec.ofNat 64 (qv.toNat / 10)).toNat = (0 : BitVec 64).toNat := by
      rw [h]
    rw [hzeroToNat] at hToNat
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdiv] at hToNat
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [hzeroToNat]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdiv]
    omega

/-- `numDigits = 0` iff `n = 0`.  `toDecimal` is empty iff `n = 0` (base
    case of the LSB recurrence). -/
theorem numDigits_eq_zero_iff (n : Nat) : numDigits n = 0 ↔ n = 0 := by
  unfold numDigits
  constructor
  · intro h
    by_contra hne
    rw [toDecimal_of_ne_zero hne] at h
    simp at h
  · intro h; subst h
    rw [toDecimal_zero]; rfl

/-- `numDigits n` for `n < 10` non-zero equals 1.  Used in the base step
    of the loop induction (when `n / 10 = 0`). -/
theorem numDigits_of_lt_ten (n : Nat) (h1 : n ≠ 0) (h2 : n < 10) :
    numDigits n = 1 := by
  unfold numDigits
  rw [toDecimal_of_ne_zero h1]
  have hdiv : n / 10 = 0 := Nat.div_eq_of_lt h2
  rw [hdiv, toDecimal_zero]
  simp

/-- One-step `numDigits` recurrence: `numDigits n = 1 + numDigits (n/10)`
    for nonzero `n`.  Direct consequence of `toDecimal_of_ne_zero`. -/
theorem numDigits_of_ne_zero {n : Nat} (h : n ≠ 0) :
    numDigits n = 1 + numDigits (n / 10) := by
  unfold numDigits
  rw [toDecimal_of_ne_zero h]
  simp [Nat.add_comm]

/-- `expectedByte n k` for `n ≠ 0` and `k > 0` shifts to `expectedByte (n/10)`. -/
theorem expectedByte_succ {n : Nat} (h : n ≠ 0) (k : Nat) :
    expectedByte n (k + 1) = expectedByte (n / 10) k := by
  unfold expectedByte
  rw [toDecimal_of_ne_zero h]
  simp [List.getElem?_cons_succ]

/-- `expectedByte n 0` for `n ≠ 0` equals `48 + n % 10`. -/
theorem expectedByte_zero_of_ne_zero {n : Nat} (h : n ≠ 0) :
    expectedByte n 0 = 48 + n % 10 := by
  unfold expectedByte
  rw [toDecimal_of_ne_zero h]
  simp

/-- **Crude bound**: `numDigits n ≤ n`.  Used to rule out address wraparound
    in the outer-loop induction (`j < numDigits qv'.toNat ≤ qv'.toNat < 2^64`).
    Proof by strong induction on `n`, using the `numDigits n = 1 + numDigits (n/10)`
    recurrence and the fact that `n/10 ≤ n - 1` for `n ≥ 1`. -/
theorem numDigits_le_self (n : Nat) : numDigits n ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hzero : n = 0
    · rw [hzero]
      have : numDigits 0 = 0 := (numDigits_eq_zero_iff _).mpr rfl
      omega
    · rw [numDigits_of_ne_zero hzero]
      have hn_div : n / 10 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hzero) (by decide)
      have hih := ih (n / 10) hn_div
      -- numDigits n = 1 + numDigits (n/10) ≤ 1 + n/10 ≤ n.
      have hn_div_le : n / 10 ≤ n - 1 := by
        have : n ≥ 1 := Nat.pos_of_ne_zero hzero
        omega
      omega

/-! ## §4.6  Outer-loop induction

Prove the outer `while (q != 0) { … }` loop produces the buffer of
ASCII decimal digits.  By well-founded recursion on `qv.toNat`:

* Base (`qv.toNat = 0`): the loop exits with no writes (`numDigits 0 = 0`,
  so the postcondition's universal quantification over `k < 0` is vacuous).
* Step (`qv.toNat ≠ 0`): one iteration writes the LSB digit, advances
  `buf`, and recurses on `qv / 10` (which strictly decreases).

The fuel cost is `8 * numDigits + 3` (each iteration consumes 3 fuel via
`bignumExecFuel_qLoop_step`; the final exit costs 3 more), plus arbitrary
extra fuel.

The invariant we thread through induction tracks both per-byte
correctness for the digits written so far, AND a frame condition for
addresses outside the buffer range.  Both are needed: previous
iterations' writes must survive into the final state, and the frame
across iterations is what proves that. -/

/-- **The outer-loop correctness theorem** (by well-founded induction on
    `qv.toNat`).  Given a state holding `d = 10` and `q = qv`, the
    `Cwhile (q != 0) loopBody` loop runs to a final state whose memory at
    each offset `k < numDigits qv.toNat` of the buffer holds the
    expected ASCII digit `expectedByte qv.toNat k`.

    Memory addresses *outside* the buffer range
    `[buf, buf + numDigits qv.toNat)` are unchanged (the frame component
    threads cross-iteration framing). -/
theorem mpnToString_outer_loop (qv : BitVec 64) (s : BignumState)
    (extra : Nat)
    (hd : s.regs "d" = 10) (hq : s.regs "q" = qv) :
    ∃ s', bignumExecFuel emptyRegistry (3 * numDigits qv.toNat + 3 + extra)
          [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "q") (.Pconst 0)) loopBody] s
            = some s' ∧
      (∀ k, k < numDigits qv.toNat →
        ∃ b : UInt8,
          s'.mem.loadByte (UInt64.ofNat ((s.regs "buf").toNat + k)) = some b ∧
          b.toNat = expectedByte qv.toNat k) ∧
      (∀ a, (∀ k, k < numDigits qv.toNat →
                  a ≠ UInt64.ofNat ((s.regs "buf").toNat + k)) →
            s'.mem.loadByte a = s.mem.loadByte a) := by
  -- Well-founded induction on qv.toNat.
  induction hN : qv.toNat using Nat.strong_induction_on generalizing qv s extra with
  | _ N ih =>
    subst hN
    by_cases hq_zero : qv.toNat = 0
    · -- Base case: qv = 0, loop exits immediately.
      have hqv_eq_zero : qv = 0 := by
        apply BitVec.eq_of_toNat_eq
        simp [hq_zero]
      have hq_zero_reg : s.regs "q" = 0 := by rw [hq, hqv_eq_zero]
      have hcond : evalPExpr s (.Papp2 (.Oneq .U64) (pv "q") (.Pconst 0)) = some 0 :=
        evalPExpr_qLoopCond_false s hq_zero_reg
      have hnd : numDigits qv.toNat = 0 :=
        (numDigits_eq_zero_iff _).mpr hq_zero
      -- Fuel = 3 * 0 + 3 + extra = extra + 3.
      have hfuel_eq : 3 * numDigits qv.toNat + 3 + extra = extra + 3 := by
        rw [hnd]; omega
      refine ⟨s, ?_, ?_, ?_⟩
      · rw [hfuel_eq]
        exact MpnAddPrototype.bignumExecFuel_loop_exit_generic emptyRegistry extra _ loopBody s hcond
      · intro k hk
        rw [hnd] at hk
        omega
      · intro a _; rfl
    · -- Step case: qv.toNat ≠ 0.
      -- One iteration: loop guard true, run loopBody, then recurse.
      have hqv_ne_zero : qv ≠ 0 := by
        intro h; apply hq_zero
        rw [h]; rfl
      have hq_ne_zero : s.regs "q" ≠ 0 := by rw [hq]; exact hqv_ne_zero
      have hcond_true : evalPExpr s (.Papp2 (.Oneq .U64) (pv "q") (.Pconst 0)) = some 1 :=
        evalPExpr_qLoopCond_true s hq_ne_zero
      -- Run one iteration via bignumExec_loopBody_step.
      obtain ⟨s1, hs1_exec, hs1_q, hs1_buf, hs1_a, hs1_d, hs1_mem, hs1_frame⟩ :=
        bignumExec_loopBody_step s qv hd hq
      -- New qv' = BitVec.ofNat 64 (qv.toNat / 10).  Its toNat is qv.toNat / 10
      -- (which is < 2^64 since it ≤ qv.toNat < 2^64).
      set qv' : BitVec 64 := BitVec.ofNat 64 (qv.toNat / 10) with hqv'
      have hqv'_lt : qv'.toNat < qv.toNat := by
        rw [hqv']
        have hqv'_toNat : qv'.toNat = qv.toNat / 10 := by
          rw [hqv']
          simp only [BitVec.toNat_ofNat]
          have hdiv : qv.toNat / 10 < 2 ^ 64 :=
            Nat.lt_of_le_of_lt (Nat.div_le_self _ _) qv.isLt
          omega
        rw [show (BitVec.ofNat 64 (qv.toNat / 10)).toNat = qv.toNat / 10 from by
            simp only [BitVec.toNat_ofNat]
            exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) qv.isLt)]
        exact Nat.div_lt_self (Nat.pos_of_ne_zero hq_zero) (by decide)
      -- Recurse on s1 with qv' = BitVec.ofNat 64 (qv.toNat / 10).
      have hs1_d_10 : s1.regs "d" = 10 := by rw [hs1_d, hd]
      have hs1_q_eq : s1.regs "q" = qv' := by rw [hs1_q]
      have hqv'_toNat_eq : qv'.toNat = qv.toNat / 10 := by
        rw [hqv']
        simp only [BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) qv.isLt)
      obtain ⟨s', hs'_exec, hs'_byte, hs'_frame⟩ :=
        ih qv'.toNat hqv'_lt qv' s1 (extra + 1) hs1_d_10 hs1_q_eq rfl
      -- Now combine: fuel = 3 * numDigits qv.toNat + 3 + extra.
      -- With numDigits qv.toNat = 1 + numDigits qv'.toNat, the total is
      --   3 + 3 * numDigits qv'.toNat + 3 + extra.
      -- bignumExecFuel_qLoop_step turns f+3 into f+1 for the recursive call.
      -- Set f = 3 * numDigits qv'.toNat + 3 + extra; then f+1 = (the IH fuel)
      -- and f+3 = 3 * numDigits qv'.toNat + 6 + extra = 3 * numDigits qv.toNat + 3 + extra. ✓
      have hnd_step : numDigits qv.toNat = 1 + numDigits (qv.toNat / 10) :=
        numDigits_of_ne_zero hq_zero
      have hnd_step' : numDigits qv.toNat = 1 + numDigits qv'.toNat := by
        rw [hqv'_toNat_eq]; exact hnd_step
      have hfuel_decomp : 3 * numDigits qv.toNat + 3 + extra
          = (3 * numDigits qv'.toNat + 3 + extra) + 3 := by
        rw [hnd_step']; ring
      refine ⟨s', ?_, ?_, ?_⟩
      · -- Fuel-step: combine the iteration step with the recursive result.
        rw [hfuel_decomp]
        -- IH gave fuel `3 * numDigits qv'.toNat + 3 + (extra + 1)`
        --             = `3 * numDigits qv'.toNat + 4 + extra` for the recursive call.
        -- bignumExecFuel_qLoop_step at f = 3 * numDigits qv'.toNat + 3 + extra
        -- expects recursive fuel f+1 = 3 * numDigits qv'.toNat + 4 + extra.  ✓
        have hs'_exec' : bignumExecFuel emptyRegistry
            (3 * numDigits qv'.toNat + 3 + extra + 1)
            [InstrR.Cwhile [] (PExpr.Papp2 (SOp2.Oneq WSize.U64) (pv "q") (PExpr.Pconst 0)) loopBody]
            s1 = some s' := by
          have : 3 * numDigits qv'.toNat + 3 + (extra + 1)
              = 3 * numDigits qv'.toNat + 3 + extra + 1 := by ring
          rw [← this]; exact hs'_exec
        exact bignumExecFuel_qLoop_step emptyRegistry (3 * numDigits qv'.toNat + 3 + extra) _
          s s1 s' hcond_true hs1_exec hs'_exec'
      · -- Per-byte correctness.  For k = 0, the byte at buf is the LSB digit (q%10+48).
        -- For k ≥ 1, recurse: the byte at buf+(k+1)-1 = (buf+1) + (k-1) is the (k-1)-th
        -- digit of qv/10, which equals the k-th digit of qv (by expectedByte_succ).
        intro k hk
        rw [hnd_step'] at hk
        -- hk : k < 1 + numDigits qv'.toNat.
        cases k with
        | zero =>
          -- The byte at offset 0 was written by the current iteration.
          -- s1.mem.loadByte (UInt64.ofNat (s.regs "buf").toNat) = some (UInt8.ofNat (qv%10+48)).
          -- We need to show s'.mem.loadByte agrees.  Use hs'_frame:
          -- the recursive call doesn't touch addresses outside [s1.regs "buf", ...).
          -- s1.regs "buf" = s.regs "buf" + 1, so offset-0 of s is not in the recursive range.
          have hbuf_addr : UInt64.ofNat ((s.regs "buf").toNat + 0)
              = UInt64.ofNat (s.regs "buf").toNat := by simp
          rw [hbuf_addr]
          -- Need: s'.mem.loadByte (UInt64.ofNat (s.regs "buf").toNat) = some (...).
          -- From the frame: s'.mem.loadByte addr = s1.mem.loadByte addr if addr is not in
          -- [s1.regs "buf", s1.regs "buf" + numDigits qv'.toNat).
          -- s1.regs "buf" = s.regs "buf" + 1 (BitVec).
          -- For any j, UInt64.ofNat ((s1.regs "buf").toNat + j)
          --         = UInt64.ofNat ((s.regs "buf" + 1).toNat + j).
          -- These are addresses one or more bytes past s.regs "buf", so they
          -- never equal UInt64.ofNat (s.regs "buf").toNat ... as long as the
          -- successive offsets don't wrap around to the original buf.
          have h_buf_addr_notin : ∀ j, j < numDigits qv'.toNat →
              UInt64.ofNat (s.regs "buf").toNat ≠
              UInt64.ofNat ((s1.regs "buf").toNat + j) := by
            intro j hj
            -- s1.regs "buf" = s.regs "buf" + 1 (BitVec).
            -- (s.regs "buf" + 1).toNat = ((s.regs "buf").toNat + 1) % 2^64.
            -- So UInt64.ofNat ((s1.regs "buf").toNat + j)
            --  = UInt64.ofNat ((s.regs "buf").toNat + 1 + j)  (mod 2^64)
            -- For this to equal UInt64.ofNat (s.regs "buf").toNat, we'd need
            -- (s.regs "buf").toNat + 1 + j ≡ (s.regs "buf").toNat (mod 2^64),
            -- i.e., 1 + j ≡ 0 (mod 2^64), i.e., 1 + j ≥ 2^64.
            -- We bound numDigits qv'.toNat ≤ 20 trivially: a UInt64 has ≤ 20
            -- decimal digits.  So j < 20 < 2^64 - 1.
            -- This is the wrap-around argument.  We'll handle it via UInt64
            -- injection: UInt64.ofNat (a) = UInt64.ofNat (b) iff a % 2^64 = b % 2^64.
            intro heq
            -- Suppose for contradiction.  We'll show j + 1 ≥ 2^64 is impossible
            -- because numDigits qv'.toNat < 2^64 (it's a small bound).
            have hj_lt_nd : j < numDigits qv'.toNat := hj
            -- We need: UInt64.ofNat (s.regs "buf").toNat
            --        = UInt64.ofNat ((s1.regs "buf").toNat + j)
            -- ⇒ (s.regs "buf").toNat ≡ (s1.regs "buf").toNat + j (mod 2^64).
            -- Use the explicit value of (s1.regs "buf").toNat in terms of
            -- (s.regs "buf").
            -- s1.regs "buf" = s.regs "buf" + 1 (BitVec arithmetic).
            -- (s.regs "buf" + 1).toNat = ((s.regs "buf").toNat + 1) % 2^64.
            have hs1_buf_toNat : (s1.regs "buf").toNat
                = ((s.regs "buf").toNat + 1) % 2 ^ 64 := by
              rw [hs1_buf]
              simp [BitVec.toNat_add, BitVec.toNat_ofNat]
            have hbuf_lt : (s.regs "buf").toNat < 2 ^ 64 := (s.regs "buf").isLt
            -- Apply UInt64.toNat injection.
            have hUInt64_inj : ∀ (x y : Nat), UInt64.ofNat x = UInt64.ofNat y ↔
                x % 2 ^ 64 = y % 2 ^ 64 := by
              intro x y
              constructor
              · intro h
                have := congrArg UInt64.toNat h
                simp [UInt64.toNat_ofNat'] at this
                exact this
              · intro h
                apply UInt64.toNat.inj
                simp [UInt64.toNat_ofNat']
                exact h
            rw [hUInt64_inj] at heq
            rw [Nat.mod_eq_of_lt hbuf_lt] at heq
            rw [hs1_buf_toNat] at heq
            -- heq : (s.regs "buf").toNat = (((s.regs "buf").toNat + 1) % 2^64 + j) % 2^64
            -- Simplify: the RHS reduces mod 2^64.
            have hmod_assoc : (((s.regs "buf").toNat + 1) % 2 ^ 64 + j) % 2 ^ 64
                = ((s.regs "buf").toNat + 1 + j) % 2 ^ 64 := by
              rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
            rw [hmod_assoc] at heq
            -- heq : (s.regs "buf").toNat = ((s.regs "buf").toNat + 1 + j) % 2^64
            -- Let b := (s.regs "buf").toNat (so b < 2^64).
            -- heq : b = (b + 1 + j) % 2^64.
            -- Case: b + 1 + j < 2^64: then heq says b = b + 1 + j, so 1 + j = 0, impossible.
            -- Case: b + 1 + j ≥ 2^64: then heq says b = b + 1 + j - 2^64 (one wrap).
            --   So 1 + j = 2^64, i.e., j = 2^64 - 1.
            -- We need a bound: j < numDigits qv'.toNat ≤ numDigits qv.toNat ≤ 20.
            -- We don't have this bound directly.  Use a coarser one: j is a
            -- decimal-digit-index, and the loop has at most as many iterations as
            -- (qv').toNat ≤ qv.toNat which is < 2^64.  So j < 2^64 - 1.
            -- Actually, what we really need is that j+1 < 2^64.
            -- Since numDigits n ≤ n (each digit contributes ≥ 1 to the value), and
            -- qv'.toNat < 2^64, we have j < qv'.toNat < 2^64.  Use numDigits_le_self.
            -- We'll prove `j + 1 < 2^64` from `j < numDigits qv'.toNat ≤ qv'.toNat`,
            -- plus `qv'.toNat < 2^64`.
            -- Actually simplest: use a direct bound `numDigits n ≤ n + 1` (with care
            -- for n = 0).  Since qv'.toNat could be 0 → numDigits 0 = 0 → no j to consider.
            have hqv'_pos : qv'.toNat > 0 ∨ numDigits qv'.toNat = 0 := by
              by_cases h : qv'.toNat = 0
              · right; exact (numDigits_eq_zero_iff _).mpr h
              · left; omega
            rcases hqv'_pos with hpos | hzero
            · -- qv'.toNat > 0.  Use numDigits ≤ qv'.toNat.
              have hnd_le_val : numDigits qv'.toNat ≤ qv'.toNat := numDigits_le_self _
              have : j < qv'.toNat := Nat.lt_of_lt_of_le hj_lt_nd hnd_le_val
              have hqv'_lt_pow : qv'.toNat < 2 ^ 64 := qv'.isLt
              have hj_plus_1_lt : 1 + j < 2 ^ 64 := by omega
              have h_sum_lt : (s.regs "buf").toNat + 1 + j < 2 ^ 65 := by omega
              -- heq : b = (b + 1 + j) % 2^64.  Since b < 2^64, b % 2^64 = b.
              -- If b + 1 + j < 2^64, then (b+1+j) % 2^64 = b+1+j ≠ b (since 1+j > 0).
              -- If b + 1 + j ≥ 2^64, then (b+1+j) % 2^64 = b+1+j-2^64.
              -- Setting equal to b: b = b+1+j-2^64 ⇒ 1+j = 2^64.  But 1+j < 2^64. Contradiction.
              by_cases hwrap : (s.regs "buf").toNat + 1 + j < 2 ^ 64
              · rw [Nat.mod_eq_of_lt hwrap] at heq
                omega
              · push Not at hwrap
                -- (b+1+j) % 2^64 = (b+1+j) - 2^64 if b+1+j < 2*2^64.
                -- Use h_sum_lt to derive this.
                have hmod_val : ((s.regs "buf").toNat + 1 + j) % 2 ^ 64
                    = (s.regs "buf").toNat + 1 + j - 2 ^ 64 := by
                  rw [Nat.mod_eq_sub_mod hwrap]
                  exact Nat.mod_eq_of_lt (by omega)
                rw [hmod_val] at heq
                omega
            · -- numDigits qv'.toNat = 0 ⇒ hj_lt_nd impossible.
              rw [hzero] at hj_lt_nd
              omega
          -- Apply frame to s'.
          have hs'_at_buf : s'.mem.loadByte (UInt64.ofNat (s.regs "buf").toNat)
              = s1.mem.loadByte (UInt64.ofNat (s.regs "buf").toNat) := by
            apply hs'_frame
            intro k hk
            -- hk : k < numDigits qv'.toNat.
            -- Need : UInt64.ofNat (s.regs "buf").toNat ≠
            --        UInt64.ofNat ((s1.regs "buf").toNat + k).
            exact h_buf_addr_notin k hk
          rw [hs'_at_buf, hs1_mem]
          refine ⟨UInt8.ofNat (qv.toNat % 10 + 48), ?_, ?_⟩
          · -- s.mem.storeByte addr v: loadByte addr = some v.
            exact Mem.loadByte_storeByte_same _ _ _
          · -- (UInt8.ofNat (qv.toNat % 10 + 48)).toNat = qv.toNat % 10 + 48.
            -- And expectedByte qv.toNat 0 = 48 + qv.toNat % 10 (by expectedByte_zero_of_ne_zero).
            rw [expectedByte_zero_of_ne_zero hq_zero]
            -- LHS: (UInt8.ofNat (qv.toNat % 10 + 48)).toNat.
            -- = (qv.toNat % 10 + 48) % 256.  Since qv.toNat % 10 < 10, sum < 58 < 256.
            have hsum_lt_256 : qv.toNat % 10 + 48 < 256 := by
              have : qv.toNat % 10 < 10 := Nat.mod_lt _ (by decide)
              omega
            -- UInt8.toNat (UInt8.ofNat n) = n % 256 = n (when n < 256).
            have huint8 : (UInt8.ofNat (qv.toNat % 10 + 48)).toNat = qv.toNat % 10 + 48 := by
              show ((qv.toNat % 10 + 48) % 256 : Nat) = qv.toNat % 10 + 48
              omega
            rw [huint8]
            omega
        | succ k =>
          -- For offset (k+1), the byte was written during the recursive call.
          -- Need to relate s.regs "buf" offset (k+1) to s1.regs "buf" offset k.
          obtain ⟨b, hb_load, hb_val⟩ := hs'_byte k (by omega)
          -- hb_load : s'.mem.loadByte (UInt64.ofNat ((s1.regs "buf").toNat + k)) = some b.
          -- hb_val  : b.toNat = expectedByte qv'.toNat k.
          -- We want : s'.mem.loadByte (UInt64.ofNat ((s.regs "buf").toNat + (k+1))) = some b
          --   AND   : b.toNat = expectedByte qv.toNat (k+1).
          -- First the address equality: (s.regs "buf").toNat + (k+1) ≡ (s1.regs "buf").toNat + k (mod 2^64).
          -- s1.regs "buf" = s.regs "buf" + 1 (BitVec), so (s1.regs "buf").toNat = ((s.regs "buf").toNat + 1) % 2^64.
          have haddr_eq : UInt64.ofNat ((s.regs "buf").toNat + (k + 1))
              = UInt64.ofNat ((s1.regs "buf").toNat + k) := by
            apply UInt64.toNat.inj
            simp only [UInt64.toNat_ofNat', hs1_buf]
            -- Both sides reduce mod 2^64.
            have hbuf_add : ((s.regs "buf") + 1 : BitVec 64).toNat
                = ((s.regs "buf").toNat + 1) % 2 ^ 64 := by
              simp [BitVec.toNat_add, BitVec.toNat_ofNat]
            rw [hbuf_add]
            -- Need: ((s.regs "buf").toNat + (k+1)) % 2^64
            --     = ((s.regs "buf").toNat + 1) % 2^64 + k) % 2^64.
            conv_rhs => rw [Nat.add_mod]
            simp only [Nat.mod_mod]
            rw [← Nat.add_mod]
            congr 1
            omega
          refine ⟨b, ?_, ?_⟩
          · rw [haddr_eq]; exact hb_load
          · rw [hb_val]
            -- Goal: expectedByte qv'.toNat k = expectedByte qv.toNat (k+1).
            -- Use expectedByte_succ: expectedByte qv.toNat (k+1) = expectedByte (qv.toNat/10) k.
            rw [expectedByte_succ hq_zero k]
            congr 1
      · -- Frame for the assembled loop: addresses outside [buf, buf + numDigits qv.toNat)
        -- are unchanged from s to s'.
        intro a ha
        -- ha : ∀ k < numDigits qv.toNat, a ≠ UInt64.ofNat ((s.regs "buf").toNat + k).
        -- We split the chain: s.mem → s1.mem (one byte at buf) → s'.mem (frame from recursive).
        -- s1.mem differs from s.mem only at UInt64.ofNat (s.regs "buf").toNat
        -- (offset 0).  hs1_frame: a ≠ that addr ⇒ same byte.
        -- s'.mem differs from s1.mem only at [s1.regs "buf", + numDigits qv'.toNat).
        -- hs'_frame: a ≠ UInt64.ofNat ((s1.regs "buf").toNat + j) for all j ⇒ same byte.
        have ha_ne_buf : a ≠ UInt64.ofNat (s.regs "buf").toNat := by
          have h0 : 0 < numDigits qv.toNat := by
            rw [hnd_step']; omega
          have := ha 0 h0
          simpa using this
        have ha_ne_s1buf : ∀ j, j < numDigits qv'.toNat →
            a ≠ UInt64.ofNat ((s1.regs "buf").toNat + j) := by
          intro j hj
          -- Map back to offset (j+1) of s.regs "buf".
          have hj_succ : j + 1 < numDigits qv.toNat := by
            rw [hnd_step']; omega
          have hne := ha (j + 1) hj_succ
          -- hne : a ≠ UInt64.ofNat ((s.regs "buf").toNat + (j + 1)).
          -- Show UInt64.ofNat ((s.regs "buf").toNat + (j+1))
          --    = UInt64.ofNat ((s1.regs "buf").toNat + j).
          have haddr_eq : UInt64.ofNat ((s.regs "buf").toNat + (j + 1))
              = UInt64.ofNat ((s1.regs "buf").toNat + j) := by
            apply UInt64.toNat.inj
            simp only [UInt64.toNat_ofNat', hs1_buf]
            have hbuf_add : ((s.regs "buf") + 1 : BitVec 64).toNat
                = ((s.regs "buf").toNat + 1) % 2 ^ 64 := by
              simp [BitVec.toNat_add, BitVec.toNat_ofNat]
            rw [hbuf_add]
            conv_rhs => rw [Nat.add_mod]
            simp only [Nat.mod_mod]
            rw [← Nat.add_mod]
            congr 1
            omega
          rw [← haddr_eq]; exact hne
        have ha_s' := hs'_frame a ha_ne_s1buf
        rw [ha_s']
        rw [hs1_mem]
        exact Mem.loadByte_storeByte_other _ _ _ _ ha_ne_buf


/-! ## §5  Concrete sanity checks

These are `native_decide` checks on the **pure** reference (no Jasmin
interpreter involved), validating that `expectedByte` + `numDigits`
agree with the canonical `Nat.digits 10` representation. -/

/-- `numDigits 0 = 0` (the empty digit list; `toDecimal 0 = []`). -/
example : numDigits 0 = 0 := by native_decide

/-- `numDigits 1234 = 4`. -/
example : numDigits 1234 = 4 := by native_decide

/-- `expectedByte 1234 0 = 52` (ASCII `'4'`, LSB digit). -/
example : expectedByte 1234 0 = 52 := by native_decide

/-- `expectedByte 1234 3 = 49` (ASCII `'1'`, MSB digit, LSB-first index). -/
example : expectedByte 1234 3 = 49 := by native_decide

/-- Per-iteration accounting: each step extracts one decimal digit, so
    the outer loop runs exactly `numDigits a.toNat` times.  Direct
    consequence of `toDecimal`'s LSB-first recurrence
    (`toDecimal_of_ne_zero`). -/
theorem outer_loop_count (a : BitVec 64) :
    numDigits a.toNat = (Nat.digits 10 a.toNat).length :=
  numDigits_eq_digits_length _

/-- **Algorithm-level corollary of `bignumExec_execPrefix_step`.**  The
    per-iteration ASCII digit produced by the prefix matches the head of
    the LSB-first decimal expansion (`expectedByte n 0`).

    Combined with the `toDecimal_of_ne_zero` recursion shape, this is the
    per-iteration invariant the outer-loop induction will thread: after
    `k` iterations, the bytes written to `buf` are `(toDecimal a.toNat).take k`
    plus the ASCII offset.  The prefix-step lemma proves the *register*
    side (`c64 = BitVec.ofNat 64 ((qv % 10) + 48)`); this corollary turns
    that register content into `expectedByte qv.toNat 0`. -/
theorem execPrefix_c64_matches_expectedByte
    (qv : BitVec 64) (hqv : qv.toNat ≠ 0) :
    (qv.toNat % 10) + 48 = expectedByte qv.toNat 0 := by
  -- `expectedByte n 0 = 48 + (toDecimal n)[0]?.map id`.  When `n ≠ 0`,
  -- `toDecimal n = (n % 10) :: toDecimal (n / 10)`, so the head is `n % 10`.
  simp only [expectedByte, toDecimal_of_ne_zero hqv, List.getElem?_cons_zero,
             Nat.add_comm]

/-! ## §5.5  Final assembly — closing `MpnToStringJasminRefines`

The full `body` = `[assignConst "d" 10; assignCopy "q" "a"; Cwhile (q != 0) loopBody]`.
The two prelude instructions are straight-line and consume no fuel
decrement under `bignumExecFuel` (they fall in the wildcard `i => execInstr s i`
arm which recurses with `fuel + 1`).  After the prelude:
* `s_after_d.regs "d" = 10` (from `assignConst`),
* `s_pre_loop.regs "q" = s.regs "a"` (from `assignCopy`),
all other registers and memory unchanged.

Then the outer loop closes via `mpnToString_outer_loop`. -/

/-- **`MpnToStringJasminRefines_holds`** — the full Jasmin refinement
    bridge for `mpn_to_string` (single-limb variant), proved as a
    theorem.  Combines the prelude (`d := 10; q := a`) with the
    `mpnToString_outer_loop` closure.  No `sorry`, no new axioms beyond
    the standard kernel trio (`propext`, `Quot.sound`, `Classical.choice`).

    This closes the `MpnToStringJasminRefines` Prop and turns the bridge
    from a pinned residual into a discharged theorem — the single-limb
    `mpn_to_string` Jasmin emission is now end-to-end verified. -/
theorem MpnToStringJasminRefines_holds : MpnToStringJasminRefines := by
  -- Unfold to mpnToString_outer_loop_obligation.
  intro s a fuel ha hfuel
  -- Reduce fuel: 7 * numDigits a.toNat + 4 < fuel.
  -- Run the prelude: assignConst "d" 10, then assignCopy "q" "a".
  -- Define s_after_d and s_pre_loop.
  set s_after_d : BignumState := setReg s "d" (BitVec.ofNat 64 10) with hs_after_d
  have hs_after_d_d : s_after_d.regs "d" = BitVec.ofNat 64 10 := by
    simp [hs_after_d, setReg]
  have hexec_d : execInstr s (assignConst "d" 10) = some s_after_d := by
    simp [assignConst, execInstr, evalPExpr, vr, bind, Option.bind, hs_after_d, setReg,
          show ((BitVec.ofInt 64 10 : BitVec 64)) = BitVec.ofNat 64 10 from by
            apply BitVec.eq_of_toNat_eq; rfl]
  -- assignCopy "q" "a" reads s_after_d.regs "a" = s.regs "a" = a.
  have hs_after_d_a : s_after_d.regs "a" = a := by
    simp [hs_after_d, setReg, ha,
          show ("a" = "d") = False from by decide]
  set s_pre_loop : BignumState := setReg s_after_d "q" a with hs_pre_loop
  have hexec_q : execInstr s_after_d (assignCopy "q" "a") = some s_pre_loop := by
    simp [assignCopy, execInstr, evalPExpr, pv, vr, bind, Option.bind,
          hs_after_d_a, hs_pre_loop]
  -- Properties of s_pre_loop:
  have hbv10 : (BitVec.ofNat 64 10 : BitVec 64) = 10 := by
    apply BitVec.eq_of_toNat_eq; rfl
  have hs_pre_d : s_pre_loop.regs "d" = 10 := by
    rw [hs_pre_loop]
    simp only [MpnAddPrototype.setReg_regs,
               show ("d" = "q") = False from by decide, if_false]
    rw [hs_after_d_d, hbv10]
  have hs_pre_q : s_pre_loop.regs "q" = a := by
    rw [hs_pre_loop]
    simp only [MpnAddPrototype.setReg_regs, if_true]
  have hs_pre_buf : s_pre_loop.regs "buf" = s.regs "buf" := by
    rw [hs_pre_loop, hs_after_d]
    simp only [MpnAddPrototype.setReg_regs,
               show ("buf" = "q") = False from by decide,
               show ("buf" = "d") = False from by decide, if_false]
  have hs_pre_mem : s_pre_loop.mem = s.mem := by
    rw [hs_pre_loop, hs_after_d]
    simp only [MpnAddPrototype.setReg_mem]
  -- Now run the loop from s_pre_loop.
  obtain ⟨F, hF⟩ : ∃ F, fuel = F + 1 := ⟨fuel - 1, by omega⟩
  obtain ⟨extra, hextra⟩ : ∃ extra, fuel = 3 * numDigits a.toNat + 3 + extra :=
    ⟨fuel - (3 * numDigits a.toNat + 3), by
      have : numDigits a.toNat ≥ 0 := Nat.zero_le _
      omega⟩
  -- Now invoke mpnToString_outer_loop with qv = a, s = s_pre_loop, extra.
  obtain ⟨s', hs'_exec, hs'_byte, _hs'_frame⟩ :=
    mpnToString_outer_loop a s_pre_loop extra hs_pre_d hs_pre_q
  -- Need: bignumExecFuel emptyRegistry fuel body s = some s'.
  -- body = [assignConst "d" 10; assignCopy "q" "a"; Cwhile ...].
  -- At fuel F+1 = fuel: cons step on assignConst — execInstr returns s_after_d,
  -- recurse on [assignCopy; Cwhile] at fuel F+1.
  -- Cons step on assignCopy — execInstr returns s_pre_loop, recurse on [Cwhile] at fuel F+1.
  -- Cons step on Cwhile: per the bignumExecFuel def, Cwhile at fuel F+1 reduces to
  --   bignumExecFuel registry F (oneIter ++ []) s_pre_loop.
  -- Hmm — the fuel semantics for Cwhile differ from the simple straight-line steps.
  refine ⟨s', ?_, ?_⟩
  · -- Show: bignumExecFuel emptyRegistry fuel body s = some s'.
    -- body = [assignConst "d" 10; assignCopy "q" "a"; Cwhile (...) loopBody].
    -- Strategy: prove the prelude reduces to the loop call on s_pre_loop, mirroring
    -- the `MpnAddNAdcSpillPrototype.MpnAddNAdcSpillJasminRefines` pattern.
    have hbody_eq : bignumExecFuel emptyRegistry (F + 1) body s
        = bignumExecFuel emptyRegistry (F + 1)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "q") (.Pconst 0)) loopBody] s_pre_loop := by
      conv_lhs => rw [body]
      -- Cons step 1: assignConst falls in wildcard, execInstr s = some s_after_d.
      show bignumExecFuel emptyRegistry (F + 1)
          (assignConst "d" 10 :: assignCopy "q" "a" ::
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "q") (.Pconst 0)) loopBody]) s = _
      rw [show (assignConst "d" 10 : InstrR) = .Cassgn (.Lvar { var := vr "d" }) .AT_none (.sword .U64) (.Pconst 10) from rfl]
      simp only [bignumExecFuel]
      rw [show execInstr s (.Cassgn (.Lvar { var := vr "d" }) .AT_none (.sword .U64) (.Pconst 10)) = some s_after_d from hexec_d]
      -- Cons step 2: assignCopy on s_after_d.
      rw [show (assignCopy "q" "a" : InstrR) = .Cassgn (.Lvar { var := vr "q" }) .AT_none (.sword .U64) (pv "a") from rfl]
      simp only [bignumExecFuel]
      rw [show execInstr s_after_d (.Cassgn (.Lvar { var := vr "q" }) .AT_none (.sword .U64) (pv "a")) = some s_pre_loop from hexec_q]
    rw [hF]
    rw [hbody_eq]
    -- Now: bignumExecFuel emptyRegistry (F+1) [Cwhile ...] s_pre_loop = some s'.
    have hF_eq : F + 1 = 3 * numDigits a.toNat + 3 + extra := by
      omega
    rw [hF_eq]; exact hs'_exec
  · -- Per-byte correctness: from hs'_byte applied with s_pre_loop's buf = s.regs "buf".
    intro k hk
    obtain ⟨b, hb_load, hb_val⟩ := hs'_byte k hk
    refine ⟨b, ?_, hb_val⟩
    rw [← hs_pre_buf]; exact hb_load

/-! ## §6  Axiom audit

All pieces are axiom-clean, depending only on the standard Lean kernel
trio (`propext`, `Classical.choice`, `Quot.sound`) and (transitively) on
`MpnDecimalSpec.toDecimal_eq_digits` (proved in the imported spec).

* `numDigits_eq_digits_length` — buffer length equals `Nat.digits 10 _`.
* `outer_loop_count` — outer iteration count equals digit count.
* `bignumExec_execPrefix_step` — **per-iteration register-frame step**;
  the 4-instruction prefix executes correctly under the present
  interpreter (uses the `#DIV_64` arm wired in `73773d02`).
* `bignumExec_execSuffix_step` — **per-iteration emit-and-bump step**;
  the 3-instruction suffix `[narrowToByte; storeByte; binImm "buf" .Oadd 1]`
  writes one ASCII byte to memory at `buf` and advances `buf`.  Uses the
  `Papp1 (.Ozeroext .U8 .U64)` and `.Lmem .U8` arms wired in `6571eecc`.
* `bignumExec_loopBody_step` — composes prefix and suffix into the full
  per-iteration step.
* `mpnToString_outer_loop` — well-founded induction on `qv.toNat` (via
  `Nat.strong_induction_on`) closing the outer `while (q != 0) { … }` loop.
* **`MpnToStringJasminRefines_holds`** — the full Jasmin refinement
  bridge, proved as a theorem.  Single-limb `mpn_to_string` is now
  end-to-end verified. -/

#print axioms numDigits_eq_digits_length
#print axioms outer_loop_count
#print axioms toDecimal_eq_digits
#print axioms bignumExec_execPrefix_step
#print axioms execPrefix_straightLine
#print axioms execPrefix_nonControl
#print axioms execPrefix_c64_matches_expectedByte
#print axioms bignumExec_execSuffix_step
#print axioms bignumExec_loopBody_step
#print axioms mpnToString_outer_loop
#print axioms MpnToStringJasminRefines_holds

/-! ## §7  Emitted Jasmin source for offline `jasminc` testing -/

#eval match Emit.emitFunDecl mpnToStringFd with
  | some s => IO.println s
  | none => IO.println "// emission failed"

end CatCrypt.Crypto.Jasmin.Examples.MpnToStringPrototype
