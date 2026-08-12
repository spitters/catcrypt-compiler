/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.JasminToSSA
import CatCrypt.Crypto.Jasmin.JasminEmit
import CatCrypt.Crypto.CTAdmClass
import CatCrypt.Crypto.SecureCompilation.Jasmin.JasminToSSADialect
import CatCrypt.Crypto.SecureCompilation.Jasmin.JasminToSSADialectNative

/-!
# Syntactic constant-time predicate for the Jasmin SSA subset + ADC extension

Two things in this module:

## Part A — syntactic CT predicate (`isCT_Cmd`)

A decidable predicate on `InstrR` / `Cmd` that captures the
"CT by construction" property: an instruction is CT iff

* it's `Cassgn (.Lvar _) _ _ e` where `e` uses only
  `Pvar` / `Pconst` / `Papp1 (Oword_of_int|Olnot|Oneg)` /
  `Papp2 op` for `op ∈ {+, -, *, ^, &, |, <<, >>}` with both operands
  `Pvar` (or `Pconst` on the right for shifts) — at width `U64` or
  `U32` — **no variable shifts, no division**;
* it's `Cassgn (.Lmem .U{64,32} _ (.Pconst _)) _ _ (.Pvar _)` — a
  memory store at a literal byte-offset from a public base pointer;
* it's `Copn lvs _ (Oasm op) args` invoking one of a whitelist of
  x86-64 primitives that are constant-time on Intel/AMD (∼2005 onward):
  `BSWAP_64`, `LZCNT`, `TZCNT`, `POPCNT`, `ADD_{64,32}`, `ADC_{64,32}`,
  `SUB_{64,32}`, `SBB_{64,32}`, `MULX[_32]`, `ROR`, `ROL`, `ANDN`,
  `CMOVcc`, `STORE64`, `CLONE_TOWER`;
* it's a `Cfor _ _ body` (compile-time `Nat` bounds, body is CT) or a
  `Cwhile [] guard body` with public-loop-counter guard and body CT.
  Loop bodies are recursively checked (body recursion landed 2026-05-26
  — see `isCT_InstrR` docstring).

The predicate is syntactic, decidable by `Bool.decEq`, and `decide`-able
for any concrete body. Every port in `S2NBignumSSA.lean` is verified
CT via `decide` (see `isCT_*` theorems at the bottom of the module
that imports this file). The list is exhaustive: any instruction not in
the whitelist returns `false`.

### Composition with the semantic CT framework

`CTPass.lean` provides a semantic CT predicate `ct_spComp` on
`SPComp`-valued computations. Our syntactic `isCT_Cmd` composes with
`translateMonoFun_correct`:

```
isCT_Cmd body  →  translateMonoFun_correct …  →  SPComp.pure _ = ct_spComp
```

The second step is immediate: `SPComp.pure v` is deterministic, so its
leakage is the constant `()`, which is trivially independent of secrets.

## Part B — extended evaluator `pureEvalMonoCmdExt`

A conservative extension of `pureEvalMonoCmd` that handles `#ADD_64` /
`#ADC_64` multi-output intrinsics, used by bignum-add ports. On bodies
without `Copn`, `pureEvalMonoCmdExt = pureEvalMonoCmd` (proved as
`pureEvalMonoCmdExt_agrees_on_copnFree`). So existing correctness
results apply unchanged to the `Cassgn`-only subset.

## CT preservation under the optimizer (now fully proved)

Preservation of `isCT_Cmd` under each of the four `JasminEmit.optimize`
passes is proved universally:

* `isCT_peepholeArith`     — `peepholeArith` preserves `isCT_Cmd`
* `isCT_propagateConstants` — `propagateConstants` preserves `isCT_Cmd`
* `isCT_deadCodeElim`       — `deadCodeElim` preserves `isCT_Cmd`
* `isCT_coalesceGo`         — `coalesceGo` preserves `isCT_Cmd`
* `isCT_optimize`           — the full pipeline preserves `isCT_Cmd`

Each per-pass theorem is proved by structural induction on the pass's
own definition (using the auto-generated `.induct` principle for
`peepholeArith` / `coalesceGo`, or direct induction on the input list
for `deadCodeElim` / `propagateConstants`). All five theorems depend
only on the standard trio of axioms (`propext`, `Classical.choice`,
`Quot.sound`).

The per-port `native_decide` checks in `S2NBignumSSA.lean` remain as
empirical evidence; they are now strictly redundant given the universal
preservation theorems, but kept as a regression net.
-/

namespace CatCrypt.Crypto.Jasmin

open CatCrypt.Crypto.Jasmin.ToSSA

set_option autoImplicit false

/-! ## Part A: Syntactic CT predicate -/

/-- Whitelist of CT binary ops at `U64` or `U32`.  All listed operations are
    fixed-latency on Intel/AMD silicon at both widths (logical AND/OR/XOR,
    integer ADD/SUB, IMUL, constant-shift SHL/SHR) — their timing is
    independent of operand values, so the operation is CT iff its operands
    are CT.  The U32 arms are required for the body of the U32 bignum loop
    kernels (`MpnAdd32Emit` / `MpnSub32Emit` / `MpnLogical32Emit` /
    `MpnMul132Emit` / `MpnAddmul132Emit` / `MpnSubmul132Emit`), where the
    inner per-limb carry/borrow and bitwise ops are written at `.U32`. -/
def ct_sop2 : SOp2 → Bool
  | .Oadd .U64 | .Osub .U64 | .Omul .U64
  | .Olxor .U64 | .Oland .U64 | .Olor .U64
  | .Olsl .U64 | .Olsr .U64 => true
  | .Oadd .U32 | .Osub .U32 | .Omul .U32
  | .Olxor .U32 | .Oland .U32 | .Olor .U32
  | .Olsl .U32 | .Olsr .U32 => true
  | _ => false

/-- Whitelist of CT unary ops at `U64` or `U32`. -/
def ct_sop1 : SOp1 → Bool
  | .Oword_of_int .U64 | .Olnot .U64 | .Oneg .U64 => true
  | .Oword_of_int .U32 | .Olnot .U32 | .Oneg .U32 => true
  | _ => false

/-- Whitelist of CT x86 intrinsics (constant-time on modern Intel/AMD).
    Non-CT examples deliberately excluded: `DIV`, `IDIV`, `SHL_*` with
    register-variable count (the intrinsic form leaks timing on older
    uarchs when the count is a secret — only const shifts are safe).

    Track C3.4 additions:
    * `STORE64` — emitted by `LowCTToJasmin` for `RLimbStore loc i v`.
      Lowers to a `mov [base + 8*i], v` x86-64 store at a literal byte
      offset from a caller-supplied base pointer.  The address is a
      function of the public base + a literal index, never of secret
      data, so the store is CT (no address-dependent timing).
    * `CLONE_TOWER` — emitted by `LowCTToJasmin` for the `RCloneCall`
      array-copy prelude.  Lowers to a fixed-length `rep movsq`-equivalent
      sequence whose iteration count is statically known from the
      `TowerType.byteSize`.  Bytes are copied unconditionally, so timing
      is independent of the array contents (which may be secret). -/
def ct_intrinsic : String → Bool
  | "BSWAP_64" | "LZCNT" | "TZCNT" | "POPCNT"
  | "ADD_64" | "ADC_64" | "SUB_64" | "SBB_64"
  | "MULX" | "MULX_lo_hi" | "MULX_hi"
  -- BMI2/ADX dual-carry-chain ops. Same CT story as ADC_64/SBB_64:
  -- 1-cycle fixed-latency x86-64 instructions whose timing is independent
  -- of operand values. ADCX reads/writes CF only; ADOX reads/writes OF
  -- only — the dual-flag isolation enables MpnAddMul1Adx-style schedules
  -- (commit 5d09b3a4) without changing the timing profile per-instruction.
  | "ADCX" | "ADOX"
  | "ROR" | "ROL" | "ANDN"
  -- Conditional move (branchless select).  CMOVcc is on the **Intel DOIT**
  -- list (CT_INSTRUCTION_REFERENCES.md §"CMOV / branchless select") and is
  -- *the* CT selection primitive in ct-verif / FaCT / Jasmin.  Both the
  -- canonical spelling `"CMOVcc"` and the bare `"CMOV"` name that
  -- `LowCTToJasmin.toJasminCmd` emits for `RSelect` are admitted.
  | "CMOVcc" | "CMOV"
  -- Track C3.4: bignum store + tower-clone oracles (RLimbStore / RCloneCall).
  | "STORE64" | "CLONE_TOWER"
  -- U32 width-suffixed bignum intrinsics emitted by the U32 kernels
  -- (`MpnAdd32Emit`, `MpnSub32Emit`, `MpnMul132Emit`, `MpnAddmul132Emit`,
  -- `MpnSubmul132Emit`). Each is the direct U32 sibling of an already
  -- whitelisted U64 intrinsic and shares the same CT story: fixed-latency
  -- x86-64 instructions whose timing is independent of operand values.
  | "ADD_32" | "ADC_32" | "SUB_32" | "SBB_32" | "MULX_32" => true
  | _ => false

/-- A `PExpr` is CT iff its shape is in our supported subset and any
    right-operand of a shift is a `Pconst` (not a `Pvar`). Memory loads
    `Pload .U64 base (Pconst k)` are CT because the address is a
    base-pointer plus a **literal** byte offset — the address does not
    depend on secret values. Variable-offset loads (`Pload _ _ (Pvar _)`)
    remain rejected (conservative). -/
def isCT_PExpr : PExpr → Bool
  | .Pconst _ => true
  | .Pbool _ => true
  | .Pvar _ => true
  | .Papp1 op (.Pvar _) => ct_sop1 op
  | .Papp1 op (.Pconst _) => ct_sop1 op
  | .Papp2 op (.Pvar _) (.Pvar _) => ct_sop2 op
  | .Papp2 op (.Pvar _) (.Pconst _) => ct_sop2 op
  -- Memory load at constant offset: address = base-pointer (typically a
  -- function param) + literal, which is independent of secrets.  Both U64
  -- and U32 widths are emitted by the bignum kernels; the address-CT story
  -- is identical (literal byte offset from a public base pointer).
  | .Pload .U64 _ (.Pconst _) => true
  | .Pload .U32 _ (.Pconst _) => true
  -- Array read at a **literal/constant** index (`arr[k]` with `k` a
  -- `Pconst`).  Emitted by `LowCTToJasmin.toJasminCmd` for `RArrLoadLit`.
  -- The leaked observation of a memory access is its *address*
  -- (CT_INSTRUCTION_REFERENCES.md §"Public/constant-index memory", USENIX'16
  -- ct-verif + Structured-Leakage CCS'21): a literal index is a public,
  -- data-independent address, so the read is CT.  A *variable* index
  -- (`Pget _ _ _ (.Pvar _)`) would leak a secret-dependent address and is
  -- deliberately NOT matched here (falls through to `false`).
  | .Pget _ _ _ (.Pconst _) => true
  -- Track C3.4: a `Parr_init n` expression evaluates to the constant
  -- all-zero array of length `n`, regardless of any input.  The result
  -- is input-independent, so its leakage is the constant `()` and the
  -- expression is trivially CT.  (Emitted by `LowCTToJasmin` for
  -- `RLetZero x t body`.)
  | .Parr_init _ => true
  | _ => false

/-- An `LVal` is a CT write target. `Lmem ws base (Pconst k)` is CT
    because the store address is a literal byte-offset from a caller-
    supplied base pointer — not a function of secret data.  Both U64 and
    U32 widths are emitted by the bignum kernels (U32 by the `Mpn*32Emit`
    families); the address-CT story is identical at either width. -/
def isCT_LVal : LVal → Bool
  | .Lvar _ => true
  | .Lnone _ _ => true  -- unused flag output
  | .Lmem .U64 _ (.Pconst _) => true
  | .Lmem .U32 _ (.Pconst _) => true
  -- Array write at a **literal/constant** index (`arr[k] = …` with `k` a
  -- `Pconst`).  Emitted by `LowCTToJasmin.toJasminCmd` for `RArrStoreLit`.
  -- Same CT-leakage argument as the `Pget` read above: the store address
  -- is a literal (public) index, so the leaked address is data-independent
  -- (CT_INSTRUCTION_REFERENCES.md §"Public/constant-index memory").  A
  -- variable index (`Laset _ _ _ (.Pvar _)`) would leak and is not matched.
  | .Laset _ _ _ (.Pconst _) => true
  | _ => false

/-! ### `isCT_InstrR` / `isCT_Cmd` — body-recursive (2026-05-26)

An instruction is CT under our subset: either a `Cassgn` with a `.Lvar`
LHS and a CT RHS, a `Cassgn` with a memory store whose right-hand-side
is a bare `Pvar` (the emitter's supported form for multi-limb writes
like `[:u64 op + k] = rN;`), a `Copn` with a whitelisted intrinsic and
CT lvals and args, a **counted `Cfor` loop** with statically known
bounds and a CT body, or a **runtime `Cwhile`** with a public
loop-counter guard and a CT body.  All other control-flow constructs
return `false` conservatively.

**Why `Cfor` is CT when bounds are compile-time known:** Jasmin's
`inline int` for-loops are unrolled at compile time. The unrolled body
contains no branching on secret-dependent conditions, and the number
of iterations depends only on the public bound — so the leakage
profile is identical to the concatenated-body case. The AST `Range`
already forces static `Nat` bounds (`Range.lo`, `Range.hi`), so
data-dependent bounds cannot arise in this subset.

**Body recursion (2026-05-26):** `Cwhile` and `Cfor` now *descend*
into their bodies — we check that every instruction in the body is
itself CT, rather than accept any body via a wildcard.  Previously the
wildcard let arbitrary U32 `Papp2`s inside loops pass `isCT_Cmd … =
true` as a quirk of the matcher, even though `ct_sop2` only covered
`.U64`; pairing body recursion with the new `.U32` arms of `ct_sop2` /
`ct_sop1` makes the predicate witness CT for U32-limb kernels
*explicitly* via their actual operators, not implicitly via the
wildcard. -/
mutual
  /-- `isCT_InstrR i` — see the section docstring above. -/
  def isCT_InstrR : InstrR → Bool
    | .Cassgn (.Lvar _) _ _ e => isCT_PExpr e
    -- Memory store: only the concrete emittable shape `(uN)[base + k] = src;`,
    -- for `N ∈ {64, 32}` (the widths the bignum kernels emit).
    | .Cassgn (.Lmem .U64 _ (.Pconst _)) _ _ (.Pvar _) => true
    | .Cassgn (.Lmem .U32 _ (.Pconst _)) _ _ (.Pvar _) => true
    -- Array element store at a **literal** index: `arr[k] = src;` with `k`
    -- a `Pconst` and `src` a `Pvar`.  Emitted by `LowCTToJasmin` for
    -- `RArrStoreLit`.  CT because the store address (literal index) is
    -- public/data-independent (CT_INSTRUCTION_REFERENCES.md
    -- §"Public/constant-index memory"); a variable index is not matched.
    | .Cassgn (.Laset _ _ _ (.Pconst _)) _ _ (.Pvar _) => true
    | .Copn lvs _ (.Oasm op) args =>
        ct_intrinsic op.name && lvs.all isCT_LVal && args.all isCT_PExpr
    -- Extension 3A: counted for-loop with compile-time `Nat` bounds.  The
    -- range is public by construction (`Range.lo`/`Range.hi : Nat`); we
    -- recurse on the body to make the U32 / U64 `Papp2` checks of the
    -- loop interior witness CT explicitly.
    | .Cfor _ _ body => isCT_Cmd body
    -- Extension 3B: runtime while-loop. CT only when the loop condition
    -- is a comparison of a loop-counter variable to zero (no condition on
    -- secret-dependent computed values). The counter is a `reg u64` that
    -- represents a public length/index — never a secret. We also require
    -- `cbefore` to be empty (standard shape) so the condition is evaluated
    -- before each iteration, not after an opaque setup block.  The body
    -- (`cafter`) is now recursively checked.
    | .Cwhile [] (.Papp2 (.Oneq .U64) (.Pvar _) (.Pconst 0)) cafter =>
        isCT_Cmd cafter
    | .Cwhile [] (.Papp2 (.Oneq .U64) (.Pvar _)
                   (.Papp1 (.Oword_of_int .U64) (.Pconst 0))) cafter =>
        isCT_Cmd cafter
    -- Track C3.4: `Cif e ct cf` is CT only when its guard `e` matches
    -- the public-flag shape `LowCTToJasmin` emits for `RIfNz` — a U64
    -- inequality between a `Pvar` (a public flag/loop-counter, never a
    -- secret) and a literal-zero word, mirroring the already-accepted
    -- `Cwhile` shape above.  The branches are not inspected here; the
    -- CT obligation on them is discharged compositionally at the source
    -- level by `LowCTCTBridge.jasminCTSafe`'s recursion on `RIfNz`,
    -- following the same pattern as `Cwhile`/`Cfor`.
    | .Cif (.Papp2 (.Oneq .U64) (.Pvar _)
              (.Papp1 (.Oword_of_int .U64) (.Pconst 0))) _ _ => true
    | .Cif (.Papp2 (.Oneq .U64) (.Pvar _) (.Pconst 0)) _ _ => true
    -- Track C3.4: `Ccall ii lvs fn args` is CT iff every argument
    -- expression is CT (the actual call is to a function whose body has
    -- already been certified CT at the source level — by
    -- `isCT_LowCT' leaves _`'s leaf-whitelist check, which only admits
    -- `RCall f` for `f ∈ leaves`).  We additionally require every output
    -- l-value to be CT (no secret-dependent store address).  As with
    -- `Cwhile`/`Cfor`, the *callee body* is not inspected here — this
    -- clause certifies the call-site shape; the callee is verified at
    -- its own definition-site through the same machinery.
    | .Ccall _ lvs _ args =>
        lvs.all isCT_LVal && args.all isCT_PExpr
    | _ => false

  /-- A body is CT iff every instruction is. -/
  def isCT_Cmd : Cmd → Bool
    | [] => true
    | i :: rest => isCT_InstrR i && isCT_Cmd rest
end

/-- Bridge to `List.all`: `isCT_Cmd` is exactly the list-wide `all`
    of `isCT_InstrR`.  Used by downstream preservation proofs that
    were written against the pre-body-recursion definition (where
    `isCT_Cmd c := c.all isCT_InstrR` was definitionally). -/
theorem isCT_Cmd_eq_all (c : Cmd) : isCT_Cmd c = c.all isCT_InstrR := by
  induction c with
  | nil => rfl
  | cons i rest ih => simp [isCT_Cmd, List.all_cons, ih]

/-- A function declaration is CT iff its body is. -/
def isCT_FunDecl (fd : FunDecl) : Bool := isCT_Cmd fd.body

/-! ## CT preservation (statements + structural arguments)

Each of the four `JasminEmit.optimize` passes preserves `isCT_Cmd`.
The structural arguments are short:

* **`peepholeArith`** rewrites `x := a + c ; y := x - c ;` into `y := a ;`
  — both shapes are CT (LHS is CT-Cassgn pattern, RHS is CT-Cassgn copy).
* **`propagateConstants`** drops `c := Pconst k` definitions and rewrites
  right-operand `Pvar c` references to `Pconst k`. Both shapes
  (`Papp2 op (.Pvar _) (.Pvar _)` and `Papp2 op (.Pvar _) (.Pconst _)`)
  are in `isCT_PExpr`, so the result is CT.
* **`deadCodeElim`** filters the instruction list — a filtered list of
  CT instructions is CT.
* **`coalesceGo`** performs renaming (`renameInstr old new`) — renaming
  preserves the instruction *shape* (op, operand kinds, arity), and
  `isCT_InstrR` depends only on the shape, so renaming preserves it.

Given the per-port decidability below, the preservation properties can
always be checked at the concrete-port level via `decide`. Full proofs
require unfolding `JasminEmit`'s private helpers and are deferred
(the case analysis mechanically follows the bullets above). -/

/-- `isCT_InstrR (Cif cond a b)` is independent of the branches `a`, `b`:
    every CT-accepting `Cif` arm only inspects the guard `cond`. -/
private lemma isCT_Cif_branch_irrel (cond : PExpr) (a b a' b' : Cmd) :
    isCT_InstrR (.Cif cond a b) = isCT_InstrR (.Cif cond a' b') := by
  -- Both sides are a `match` on the same guard `cond`; only `Papp2 (Oneq _)`
  -- arms are accepting, and they ignore the branches.  Splitting `cond` to a
  -- concrete shape lets both `match`es compute to the same literal.
  -- Unfold both occurrences of the predicate to their `match` form, then
  -- split each `match` on the (shared) guard `cond`.  In the reachable arms
  -- both sides reduce to the same literal (the branches `a b` / `a' b'` are
  -- never inspected by a CT-accepting `Cif` arm); in the unreachable arms the
  -- discriminant equality is contradictory.
  unfold isCT_InstrR
  split <;> split <;> first | rfl | (rename_i h1 h2; simp_all)

/-- For a `Cwhile` with empty `cbefore`, `isCT_InstrR` depends only on the
    guard and on `isCT_Cmd` of the `cafter` body — so it transfers from one
    `cafter` to another whenever the second `cafter` is CT. -/
private lemma isCT_Cwhile_nil_transfer (cond : PExpr) (ca ca' : Cmd)
    (hca' : isCT_Cmd ca' = true)
    (h : isCT_InstrR (.Cwhile [] cond ca) = true) :
    isCT_InstrR (.Cwhile [] cond ca') = true := by
  revert h
  unfold isCT_InstrR
  split <;> intro h <;> first | exact hca' | exact h | simp_all

/-- A CT `Cwhile` with empty `cbefore` has a CT `cafter` body. -/
private lemma isCT_Cwhile_nil_body (cond : PExpr) (ca : Cmd)
    (h : isCT_InstrR (.Cwhile [] cond ca) = true) : isCT_Cmd ca = true := by
  revert h
  unfold isCT_InstrR
  split <;> intro h <;> first | exact h | simp_all

/-- `deadCodeElim` preserves `isCT`. The pass either *drops* a leaf
    `Cassgn`-to-`Lvar` (when its target is dead), or *keeps* the
    instruction while recursing into any nested command bodies
    (`Cif` / `Cfor` / `Cwhile`).

    Dropping is sound for CT trivially: a filtered sub-list of CT
    instructions is CT.  Keeping with body-recursion is sound because
    every CT-accepting control-flow shape (per `isCT_InstrR`) is
    preserved by `deadCodeElim`'s reassembly:

    * `Cassgn` / `Copn` / `Ccall` pass through unchanged (`match … | other`),
      so CT is immediate.
    * `Cfor v r body` requires `isCT_Cmd body`; the rebuilt
      `Cfor v r (deadCodeElim … body)` is CT by the induction hypothesis on
      `body` (a strict subterm).
    * `Cwhile cb cond ca` is CT only when `cb = []`; since
      `deadCodeElim _ [] = []` the rebuilt `cbefore` stays `[]`, `cond` is
      untouched, and CT of the rebuilt `cafter` follows from the IH on `ca`.
    * `Cif cond _ _` is CT purely from its guard shape (branches are not
      inspected by `isCT_InstrR`), and `deadCodeElim` keeps the guard, so
      the rebuilt `Cif` is CT regardless of the cleaned branches.

    The recursion follows `deadCodeElim`'s own structure (`termination_by
    sizeOf c`): each nested body is a strict subterm of the head
    instruction, so the measure decreases. -/
theorem isCT_deadCodeElim (liveOut : List Var) (c : Cmd) (h : isCT_Cmd c) :
    isCT_Cmd (deadCodeElim liveOut c) := by
  match c with
  | [] => simp [deadCodeElim, isCT_Cmd]
  | i :: rest =>
    rw [isCT_Cmd, Bool.and_eq_true] at h
    obtain ⟨hi, hrest⟩ := h
    have ihrest' : isCT_Cmd (deadCodeElim liveOut rest) :=
      isCT_deadCodeElim _ rest hrest
    cases i with
    | Cassgn lv tag ty e =>
      -- leaf: `deadCodeElim` either drops it (dead) or keeps it unchanged
      rw [deadCodeElim]
      split
      · -- dropped (dead)
        exact ihrest'
      · -- kept unchanged: `match i with | other => other` reduces to `i`
        rw [isCT_Cmd, Bool.and_eq_true]
        exact ⟨hi, ihrest'⟩
      -- the `match i` of `deadCodeElim` leaves trivially-contradictory
      -- "`Cassgn` is a `Cif`/`Cfor`/…" obligations from the matcher splitter
      all_goals (intro _ _ _ hc; exact absurd hc (by simp))
    | Copn lvs tag op es =>
      -- `isDeadInstr _ (Copn …) = false`, so always kept, unchanged
      simp only [deadCodeElim, isDeadInstr, Bool.false_eq_true, if_false]
      rw [isCT_Cmd, Bool.and_eq_true]
      exact ⟨hi, ihrest'⟩
    | Ccall ii lvs fn args =>
      simp only [deadCodeElim, isDeadInstr, Bool.false_eq_true, if_false]
      rw [isCT_Cmd, Bool.and_eq_true]
      exact ⟨hi, ihrest'⟩
    | Cif cond th el =>
      -- `isDeadInstr _ (Cif …) = false`, so always kept; guard-shape ⇒ CT.
      simp only [deadCodeElim, isDeadInstr, Bool.false_eq_true, if_false]
      rw [isCT_Cmd, Bool.and_eq_true]
      refine ⟨?_, ihrest'⟩
      rw [isCT_Cif_branch_irrel cond _ _ th el]
      exact hi
    | Cfor v range body =>
      simp only [deadCodeElim, isDeadInstr, Bool.false_eq_true, if_false]
      rw [isCT_Cmd, Bool.and_eq_true]
      refine ⟨?_, ihrest'⟩
      simp only [isCT_InstrR] at hi ⊢
      exact isCT_deadCodeElim _ body hi
    | Cwhile cb cond ca =>
      simp only [deadCodeElim, isDeadInstr, Bool.false_eq_true, if_false]
      rw [isCT_Cmd, Bool.and_eq_true]
      refine ⟨?_, ihrest'⟩
      -- CT shape forces `cb = []`; the rebuilt `cbefore` is `dce _ [] = []`
      cases cb with
      | cons hd tl => exact absurd hi (by simp [isCT_InstrR])
      | nil =>
        -- rebuilt cbefore is `deadCodeElim _ [] = []`
        simp only [deadCodeElim]
        have hca : isCT_Cmd ca = true := isCT_Cwhile_nil_body cond ca hi
        exact isCT_Cwhile_nil_transfer cond ca _
          (isCT_deadCodeElim _ ca hca) hi
  termination_by sizeOf c

/-! ### Rename lemmas — structural, used by peephole/coalesce preservation -/

open CatCrypt.Crypto.Jasmin.Emit

/-- `isCT_PExpr (Pvar _) = true` unconditionally. -/
private lemma isCT_PExpr_Pvar (gv : GVar) : isCT_PExpr (.Pvar gv) = true := rfl

/-- Renaming a `Pvar` yields a `Pvar`. -/
private lemma renameExpr_Pvar_eq (old new : String) (gv : GVar) :
    isCT_PExpr (renameExpr old new (.Pvar gv)) = true := by
  unfold renameExpr
  split <;> rfl

/-- Renaming inside a `PExpr` preserves its `isCT_PExpr` status: renames
    change names, not constructor shapes, and `isCT_PExpr` depends only
    on shape + operator. -/
theorem isCT_renameExpr (old new : String) (e : PExpr) :
    isCT_PExpr (renameExpr old new e) = isCT_PExpr e := by
  cases e with
  | Pconst _ => rfl
  | Pbool _ => rfl
  | Pvar gv => rw [renameExpr_Pvar_eq, isCT_PExpr_Pvar]
  | Papp1 op e =>
    cases e with
    | Pvar gv =>
      show isCT_PExpr (.Papp1 op (renameExpr old new (.Pvar gv))) =
           isCT_PExpr (.Papp1 op (.Pvar gv))
      unfold renameExpr
      split <;> rfl
    | Pconst _ => rfl
    | _ => simp [renameExpr, isCT_PExpr]
  | Papp2 op e1 e2 =>
    cases e1 with
    | Pvar g1 =>
      cases e2 with
      | Pvar g2 =>
        show isCT_PExpr
              (.Papp2 op (renameExpr old new (.Pvar g1)) (renameExpr old new (.Pvar g2))) =
             isCT_PExpr (.Papp2 op (.Pvar g1) (.Pvar g2))
        unfold renameExpr
        split <;> split <;> rfl
      | Pconst _ =>
        show isCT_PExpr
              (.Papp2 op (renameExpr old new (.Pvar g1)) (.Pconst _)) =
             isCT_PExpr (.Papp2 op (.Pvar g1) (.Pconst _))
        unfold renameExpr
        split <;> rfl
      | _ => simp [renameExpr, isCT_PExpr]
    | _ => simp [renameExpr, isCT_PExpr]
  | Pload ws x off => simp [renameExpr, isCT_PExpr]
  | _ => simp [renameExpr, isCT_PExpr]

/-- Renaming inside an `LVal` preserves its `isCT_LVal` status. -/
theorem isCT_renameLVal (old new : String) (lv : LVal) :
    isCT_LVal (renameLVal old new lv) = isCT_LVal lv := by
  cases lv with
  | Lvar x =>
    show isCT_LVal (renameLVal old new (.Lvar x)) = isCT_LVal (.Lvar x)
    simp only [renameLVal]
    split_ifs <;> rfl
  | Lnone _ _ => rfl
  | Lmem _ _ _ => rfl  -- renameLVal on Lmem is identity (no traversal into addr)
  | _ => rfl

/-- Renaming inside an instruction preserves its `isCT_InstrR` status. -/
theorem isCT_renameInstr (old new : String) (i : InstrR) :
    isCT_InstrR (renameInstr old new i) = isCT_InstrR i := by
  cases i with
  | Cassgn lv tag ty e =>
    cases lv with
    | Lvar x =>
      show isCT_InstrR (.Cassgn (renameLVal old new (.Lvar x)) tag ty (renameExpr old new e)) =
           isCT_InstrR (.Cassgn (.Lvar x) tag ty e)
      simp only [renameLVal]
      have hE := isCT_renameExpr old new e
      split_ifs <;>
        · show isCT_PExpr (renameExpr old new e) = isCT_PExpr e
          exact hE
    | Lmem ws x off =>
      -- `renameLVal` is identity on `Lmem`. `isCT_InstrR` on `Lmem`-LHS
      -- is non-trivially `true` only for `ws ∈ {U64, U32}` and
      -- `off = Pconst _` with RHS = `Pvar _`. All other combos yield
      -- `false` on both sides.  Renaming a `Pvar` to a `Pvar`
      -- preserves the shape.
      cases ws with
      | U64 =>
        cases off with
        | Pconst k =>
          cases e with
          | Pvar gv =>
            show isCT_InstrR (.Cassgn (.Lmem .U64 x (.Pconst k)) tag ty
                   (renameExpr old new (.Pvar gv))) =
                 isCT_InstrR (.Cassgn (.Lmem .U64 x (.Pconst k)) tag ty (.Pvar gv))
            unfold renameExpr
            split_ifs <;> rfl
          | _ => simp [renameInstr, renameLVal, renameExpr, isCT_InstrR]
        | _ => simp [renameInstr, renameLVal, isCT_InstrR]
      | U32 =>
        cases off with
        | Pconst k =>
          cases e with
          | Pvar gv =>
            show isCT_InstrR (.Cassgn (.Lmem .U32 x (.Pconst k)) tag ty
                   (renameExpr old new (.Pvar gv))) =
                 isCT_InstrR (.Cassgn (.Lmem .U32 x (.Pconst k)) tag ty (.Pvar gv))
            unfold renameExpr
            split_ifs <;> rfl
          | _ => simp [renameInstr, renameLVal, renameExpr, isCT_InstrR]
        | _ => simp [renameInstr, renameLVal, isCT_InstrR]
      | _ => simp [renameInstr, renameLVal, isCT_InstrR]
    | Lnone _ _ =>
      simp [renameInstr, renameLVal, isCT_InstrR]
    | Laset aa ws xv idx =>
      -- The array-store clause `Laset … (Pconst _)` with `Pvar` RHS is now
      -- non-trivial in `isCT_InstrR`; renaming preserves both the literal
      -- index shape and the `Pvar` RHS shape, so CT status is unchanged.
      cases idx with
      | Pconst k =>
        cases e with
        | Pvar gv =>
          show isCT_InstrR (.Cassgn (.Laset aa ws xv (.Pconst k)) tag ty
                 (renameExpr old new (.Pvar gv))) =
               isCT_InstrR (.Cassgn (.Laset aa ws xv (.Pconst k)) tag ty (.Pvar gv))
          unfold renameExpr
          split_ifs <;> rfl
        | _ => simp [renameInstr, renameLVal, renameExpr, isCT_InstrR]
      | _ => simp [renameInstr, renameLVal, isCT_InstrR]
    | Lasub _ _ _ _ _ =>
      simp [renameInstr, renameLVal, isCT_InstrR]
  | Copn lvs tag op es =>
    cases op with
    | Oasm aop =>
      simp only [renameInstr, isCT_InstrR]
      congr 1
      · -- all lvs preserve isCT_LVal under rename
        rw [show ∀ xs : List LVal,
             (xs.map (renameLVal old new)).all isCT_LVal = xs.all isCT_LVal from ?_]
        intro xs
        induction xs with
        | nil => rfl
        | cons x xs ih =>
          simp [List.all_cons, isCT_renameLVal, ih]
      · -- all args preserve isCT_PExpr under rename
        rw [show ∀ xs : List PExpr,
             (xs.map (renameExpr old new)).all isCT_PExpr = xs.all isCT_PExpr from ?_]
        intro xs
        induction xs with
        | nil => rfl
        | cons x xs ih =>
          simp [List.all_cons, isCT_renameExpr, ih]
  | Cif _ _ _ => rfl
  | Cfor _ _ _ => rfl
  | Cwhile _ _ _ => rfl
  | Ccall _ _ _ _ => rfl

/-- Lift to lists: renaming preserves `isCT_Cmd`. -/
theorem isCT_renameBody (old new : String) (c : Cmd) :
    isCT_Cmd (c.map (renameInstr old new)) = isCT_Cmd c := by
  induction c with
  | nil => rfl
  | cons i rest ih =>
    have hi := isCT_renameInstr old new i
    simp only [isCT_Cmd, List.map_cons, hi, ih]

/-! ### substRightOp preserves isCT (used by propagateConstants) -/

/-- `substRightOp` either leaves an instruction unchanged or rewrites
    `Papp2 op (.Pvar _) (.Pvar _)` (CT iff `ct_sop2 op`) into
    `Papp2 op (.Pvar _) (.Pconst _)` (CT under the same condition) —
    so CT status is preserved. -/
theorem isCT_substRightOp (cm : List (String × Int)) (i : InstrR)
    (h : isCT_InstrR i) : isCT_InstrR (substRightOp cm i) := by
  cases i with
  | Cassgn lv tag ty e =>
    cases e with
    | Papp2 op e1 e2 =>
      cases e2 with
      | Pvar gv =>
        simp [substRightOp]
        split
        · -- substituted to Pconst
          cases lv with
          | Lvar _ =>
            cases e1 with
            | Pvar _ =>
              simp [isCT_InstrR, isCT_PExpr] at h ⊢; exact h
            | Pconst _ =>
              simp [isCT_InstrR, isCT_PExpr] at h
            | _ =>
              simp [isCT_InstrR, isCT_PExpr] at h
          | Lmem ws base off =>
            -- `Cassgn (Lmem _ _ _) _ _ (Papp2 _ _ _)` is NOT in `isCT_InstrR`:
            -- the only `Lmem` arms accept a bare `Pvar` RHS (U64 or U32 with
            -- `off = Pconst _`); a `Papp2` RHS falls through to the catch-all
            -- `_ => false`.  So `h` is contradictory in this case.  We do
            -- the case-split on `ws` and `off` explicitly because the
            -- auto-generated match equation lemma for `isCT_InstrR` has
            -- a kernel-checker glitch on the bundled `simp` reduction
            -- after the U32 arms were added (2026-05-26).
            cases ws <;> cases off <;> exact absurd h (by simp [isCT_InstrR])
          -- `Lnone`/`Laset`/`Lasub` with a `Papp2` RHS: none of these are
          -- accepted by `isCT_InstrR` (only the `Laset … (Pconst _)`-index
          -- store with a *bare* `Pvar` RHS is — see the array-store clause),
          -- so a `Papp2` RHS falls through to `_ => false`; `h` is
          -- contradictory.  Split on the index like the `Lmem` case to dodge
          -- the bundled match-equation reduction glitch.
          | Lnone _ _ => exact absurd h (by simp [isCT_InstrR])
          | Laset aa ws x idx => cases idx <;> exact absurd h (by simp [isCT_InstrR])
          | Lasub aa ws len x idx => cases idx <;> exact absurd h (by simp [isCT_InstrR])
        · exact h
      | _ => simp [substRightOp]; exact h
    | _ => simp [substRightOp]; exact h
  | _ => simp [substRightOp]; exact h

/-- `propagateConstants` preserves CT: drops a subset of Cassgn
    instructions (CT-preserving), then maps `substRightOp` (CT-preserving
    per-instruction). -/
theorem isCT_propagateConstants (c : Cmd) (h : isCT_Cmd c) :
    isCT_Cmd (propagateConstants c) := by
  unfold propagateConstants
  rw [isCT_Cmd_eq_all, List.all_eq_true]
  intro i hi
  rw [List.mem_map] at hi
  obtain ⟨j, hj_in, hj_eq⟩ := hi
  have hj_in_c : j ∈ c := by
    unfold dropConstDefs at hj_in
    exact List.mem_of_mem_filter hj_in
  have hj_CT : isCT_InstrR j := by
    have h' := h
    rw [isCT_Cmd_eq_all, List.all_eq_true] at h'
    exact h' j hj_in_c
  subst hj_eq
  exact isCT_substRightOp _ j hj_CT

/-! ### peepholeArith preserves CT

The structural argument: `peepholeArith` outputs instructions that are
either (a) in the original input (directly kept, possibly with the
next-pair instruction carried forward) or (b) a newly synthesised copy
of shape `Cassgn (.Lvar _) _ _ (.Pvar _)`. The latter is CT because
`Pvar` is always in `isCT_PExpr` regardless of operator.

`peepholeArith`'s recursion passes synthesised copies back to itself,
so the generated induction principle has multiple branches mirroring
the `if/else` structure of the definition. Discharging each branch
mechanically is possible but verbose. We check every concrete port
after the full `optimize` pipeline via `decide` in
`S2NBignumSSA.lean::all_ports_are_CT_after_optimize` (below), which
amounts to a per-port proof of the preservation property. -/

/-! **Helpers for isCT-preservation proofs.** Working with
    `isCT_Cmd (i :: rest)` in `Bool` rather than decomposing into `Prop`
    conjunctions keeps the tactic state cleaner when we have to
    reconstruct CT premises across recursive calls. -/

lemma isCT_Cmd_cons_iff (i : InstrR) (rest : Cmd) :
    isCT_Cmd (i :: rest) = true ↔
      isCT_InstrR i = true ∧ isCT_Cmd rest = true := by
  simp [isCT_Cmd]

/-- The synthesised copy produced by peephole's first fire branch is CT. -/
lemma isCT_synth_copy (y : VarI) (ty : SType) (ya : GVar) :
    isCT_InstrR (.Cassgn (.Lvar y) .AT_none ty (.Pvar ya)) = true := by
  simp [isCT_InstrR, isCT_PExpr]

/-- Reduction lemma: when neither `(Cassgn (Lvar _) _ _ (Papp2 _ Pvar Pvar))`
    pattern fires at the head of `i :: rest`, `peepholeArith (i :: rest)`
    unfolds to `i :: peepholeArith rest`. The hypothesis `hNoFire` is the
    contrapositive form `peepholeArith.induct` produces in its catch-all
    case (no pair of `(Cassgn (Lvar _) _ _ (Papp2 _ (Pvar _) (Pvar _)))`
    instructions at the head). Pure case-bash on the AST constructors. -/
private lemma peepholeArith_no_fire_eq (i : InstrR) (rest : List InstrR)
    (hNoFire : ∀ (x : VarI) (tag : AssgnTag) (ty1 : SType) (op1 : SOp2)
        (ya c1 : GVar) (y : VarI) (tag_1 : AssgnTag) (ty : SType)
        (op2 : SOp2) (xr c2 : GVar) (rest_1 : List InstrR),
        i = .Cassgn (.Lvar x) tag ty1 (.Papp2 op1 (.Pvar ya) (.Pvar c1)) →
          rest = .Cassgn (.Lvar y) tag_1 ty
                   (.Papp2 op2 (.Pvar xr) (.Pvar c2)) :: rest_1 → False) :
    peepholeArith (i :: rest) = i :: peepholeArith rest := by
  rw [peepholeArith.eq_def]
  cases i with
  | Cassgn lv tag ty e =>
    cases lv with
    | Lvar x =>
      cases e with
      | Papp2 op1 e1 e2 =>
        cases e1 with
        | Pvar ya =>
          cases e2 with
          | Pvar c1 =>
            cases rest with
            | nil => rfl
            | cons i2 rest1 =>
              cases i2 with
              | Cassgn lv2 tag2 ty2 e2 =>
                cases lv2 with
                | Lvar y =>
                  cases e2 with
                  | Papp2 op2 e1' e2' =>
                    cases e1' with
                    | Pvar xr =>
                      cases e2' with
                      | Pvar c2 =>
                        exfalso
                        exact hNoFire x tag ty op1 ya c1 y tag2 ty2
                          op2 xr c2 rest1 rfl rfl
                      | _ => rfl
                    | _ => rfl
                  | _ => rfl
                | _ => rfl
              | _ => rfl
          | _ => rfl
        | _ => rfl
      | _ => rfl
    | _ => rfl
  | _ => rfl

/-- **Universal `peepholeArith` preservation.** Each output instruction
    is either (a) a member of the input list (CT by hypothesis), or
    (b) a synthesised copy `Cassgn (.Lvar _) _ _ (.Pvar _)` (CT by
    `isCT_synth_copy`).  We use `peepholeArith.induct`, which provides
    five cases mirroring the definition's match arms; the two “fire”
    cases push a synthesised copy back onto the recursion's input, the
    "no-fire pair" case carries the original first instruction forward
    to a recursion on the strictly shorter (re-stitched) tail, and the
    catch-all case is handled by `peepholeArith_no_fire_eq`. -/
theorem isCT_peepholeArith (c : Cmd) (h : isCT_Cmd c) :
    isCT_Cmd (peepholeArith c) := by
  induction c using peepholeArith.induct with
  | case1 => simp [peepholeArith, isCT_Cmd]
  | case2 x tag ty1 op1 ya c1 y tag2 ty op2 xr c2 rest hCond ih =>
    show isCT_Cmd (peepholeArith _) = true
    have hEq : peepholeArith
      (.Cassgn (.Lvar x) tag ty1 (.Papp2 op1 (.Pvar ya) (.Pvar c1)) ::
        .Cassgn (.Lvar y) tag2 ty (.Papp2 op2 (.Pvar xr) (.Pvar c2)) :: rest)
      = peepholeArith (.Cassgn (.Lvar y) .AT_none ty1 (.Pvar ya) :: rest) := by
      conv_lhs => rw [peepholeArith]
      rw [if_pos hCond]
    rw [hEq]
    apply ih
    rw [isCT_Cmd_cons_iff] at h ⊢
    obtain ⟨_, h2⟩ := h
    rw [isCT_Cmd_cons_iff] at h2
    obtain ⟨_, hrest⟩ := h2
    exact ⟨isCT_synth_copy _ _ _, hrest⟩
  | case3 x tag ty1 op1 ya c1 y tag2 ty op2 xr c2 rest hNeg hCond ih =>
    show isCT_Cmd (peepholeArith _) = true
    have hEq : peepholeArith
      (.Cassgn (.Lvar x) tag ty1 (.Papp2 op1 (.Pvar ya) (.Pvar c1)) ::
        .Cassgn (.Lvar y) tag2 ty (.Papp2 op2 (.Pvar xr) (.Pvar c2)) :: rest)
      = peepholeArith (.Cassgn (.Lvar y) .AT_none ty1 (.Pvar c1) :: rest) := by
      conv_lhs => rw [peepholeArith]
      rw [if_neg hNeg, if_pos hCond]
    rw [hEq]
    apply ih
    rw [isCT_Cmd_cons_iff] at h ⊢
    obtain ⟨_, h2⟩ := h
    rw [isCT_Cmd_cons_iff] at h2
    obtain ⟨_, hrest⟩ := h2
    exact ⟨isCT_synth_copy _ _ _, hrest⟩
  | case4 x tag ty1 op1 ya c1 y tag2 ty op2 xr c2 rest hN1 hN2 ih =>
    show isCT_Cmd (peepholeArith _) = true
    have hEq : peepholeArith
      (.Cassgn (.Lvar x) tag ty1 (.Papp2 op1 (.Pvar ya) (.Pvar c1)) ::
        .Cassgn (.Lvar y) tag2 ty (.Papp2 op2 (.Pvar xr) (.Pvar c2)) :: rest)
      = .Cassgn (.Lvar x) tag ty1 (.Papp2 op1 (.Pvar ya) (.Pvar c1)) ::
        peepholeArith
          (.Cassgn (.Lvar y) .AT_none ty1
            (.Papp2 op2 (.Pvar xr) (.Pvar c2)) :: rest) := by
      conv_lhs => rw [peepholeArith]
      rw [if_neg hN1, if_neg hN2]
    rw [hEq, isCT_Cmd_cons_iff]
    rw [isCT_Cmd_cons_iff] at h
    obtain ⟨h1, h2⟩ := h
    refine ⟨h1, ?_⟩
    apply ih
    rw [isCT_Cmd_cons_iff] at h2 ⊢
    obtain ⟨h2a, h2b⟩ := h2
    refine ⟨?_, h2b⟩
    -- `Cassgn (Lvar y) tag2 ty (Papp2 …)` and
    -- `Cassgn (Lvar y) AT_none ty1 (Papp2 …)` have the same
    -- shape that `isCT_InstrR` checks (LHS = `Lvar`, RHS = `Papp2`).
    simp [isCT_InstrR] at h2a ⊢
    exact h2a
  | case5 i rest hNoFire ih =>
    rw [peepholeArith_no_fire_eq i rest hNoFire]
    rw [isCT_Cmd_cons_iff]
    rw [isCT_Cmd_cons_iff] at h
    obtain ⟨h1, h2⟩ := h
    exact ⟨h1, ih h2⟩

/-! ### coalesceGo preserves CT

`coalesceGo` is now a total `def` with `termination_by body.length`,
so Lean generates `coalesceGo.induct`. The proof: at every step
`coalesceGo` either (a) keeps the instruction unchanged, (b) rewrites
`Cassgn (.Lvar x) _ ty (.Papp2 op (.Pvar y) z)` to
`Cassgn (.Lvar y) _ ty (.Papp2 op (.Pvar y) z)` — same op, same
operand kinds — or (c) renames variables in the tail, which preserves
CT by `isCT_renameBody`. -/

/-- The synthesised merge instruction
    `Cassgn (Lvar y') tag ty (Papp2 op (Pvar y) (Pvar/Pconst _))`
    has the same `isCT_InstrR` shape as the original
    `Cassgn (Lvar x) tag ty (Papp2 op (Pvar y) (Pvar/Pconst _))`
    (LHS: `Lvar`, RHS: `Papp2`).  Both reduce to `isCT_PExpr (Papp2 …)`,
    which is independent of the LHS variable. -/
private lemma isCT_merged_instr_pvar (y' : VarI) (tag : AssgnTag) (ty : SType)
    (op : SOp2) (y z : GVar) :
    isCT_InstrR (.Cassgn (.Lvar y') tag ty (.Papp2 op (.Pvar y) (.Pvar z))) =
    isCT_PExpr (.Papp2 op (.Pvar y) (.Pvar z)) := rfl

private lemma isCT_merged_instr_pconst (y' : VarI) (tag : AssgnTag) (ty : SType)
    (op : SOp2) (y : GVar) (k : Int) :
    isCT_InstrR (.Cassgn (.Lvar y') tag ty (.Papp2 op (.Pvar y) (.Pconst k))) =
    isCT_PExpr (.Papp2 op (.Pvar y) (.Pconst k)) := rfl

/-- **Universal `coalesceGo` preservation.**
    Each output instruction is either (a) the same as the input
    instruction (CT preserved trivially), or (b) a synthesised
    `Cassgn (Lvar y) tag ty (Papp2 op (Pvar y) (Pvar/Pconst _))` whose
    shape matches the input's `Cassgn (Lvar x) tag ty (Papp2 op (Pvar y)
    (Pvar/Pconst _))` shape (so `isCT_InstrR` is preserved by
    `isCT_merged_instr_*`). The recursive tail is either renamed
    (CT preserved by `isCT_renameBody`) or unchanged.

    `coalesceGo.induct` has motive `List Var → List InstrR → Prop`, so
    we induct on the pair `(liveOut, c)` simultaneously. -/
theorem isCT_coalesceGo (liveOut : List Var) (c : Cmd) (h : isCT_Cmd c) :
    isCT_Cmd (coalesceGo liveOut c).1 := by
  induction liveOut, c using coalesceGo.induct with
  | case1 lo => simp [coalesceGo, isCT_Cmd]
  | case2 lo rest x tag ty op y z _ _ _ _ hMerge _ tail lo' hCG ih =>
    -- Cassgn (Lvar x) tag ty (Papp2 op (Pvar y) (Pvar z)), canMerge true
    rw [isCT_Cmd_cons_iff] at h
    obtain ⟨hi, hrest⟩ := h
    have hEq : (coalesceGo lo
        (.Cassgn (.Lvar x) tag ty (.Papp2 op (.Pvar y) (.Pvar z)) :: rest)).1
        = .Cassgn (.Lvar { var := y.gv.var }) tag ty
            (.Papp2 op (.Pvar y) (.Pvar z)) ::
          (coalesceGo (renameLiveOut x.var.vname y.gv.var.vname lo)
            (rest.map (renameInstr x.var.vname y.gv.var.vname))).1 := by
      rw [coalesceGo, if_pos hMerge]
    rw [hEq, isCT_Cmd_cons_iff]
    refine ⟨?_, ?_⟩
    · rw [isCT_merged_instr_pvar]
      have hPvar : isCT_InstrR
        (.Cassgn (.Lvar x) tag ty (.Papp2 op (.Pvar y) (.Pvar z))) = true := hi
      simp [isCT_InstrR] at hPvar
      exact hPvar
    · apply ih
      rw [isCT_renameBody]
      exact hrest
  | case3 lo rest x tag ty op y z _ _ _ _ hMerge tail lo' hCG ih =>
    rw [isCT_Cmd_cons_iff] at h
    obtain ⟨hi, hrest⟩ := h
    have hEq : (coalesceGo lo
        (.Cassgn (.Lvar x) tag ty (.Papp2 op (.Pvar y) (.Pvar z)) :: rest)).1
        = .Cassgn (.Lvar x) tag ty (.Papp2 op (.Pvar y) (.Pvar z)) ::
          (coalesceGo lo rest).1 := by
      rw [coalesceGo, if_neg hMerge]
    rw [hEq, isCT_Cmd_cons_iff]
    exact ⟨hi, ih hrest⟩
  | case4 lo rest x tag ty op y k _ _ _ hMerge _ tail lo' hCG ih =>
    -- Cassgn (Lvar x) tag ty (Papp2 op (Pvar y) (Pconst k)), canMerge true
    rw [isCT_Cmd_cons_iff] at h
    obtain ⟨hi, hrest⟩ := h
    have hEq : (coalesceGo lo
        (.Cassgn (.Lvar x) tag ty (.Papp2 op (.Pvar y) (.Pconst k)) :: rest)).1
        = .Cassgn (.Lvar { var := y.gv.var }) tag ty
            (.Papp2 op (.Pvar y) (.Pconst k)) ::
          (coalesceGo (renameLiveOut x.var.vname y.gv.var.vname lo)
            (rest.map (renameInstr x.var.vname y.gv.var.vname))).1 := by
      rw [coalesceGo, if_pos hMerge]
    rw [hEq, isCT_Cmd_cons_iff]
    refine ⟨?_, ?_⟩
    · rw [isCT_merged_instr_pconst]
      have hPc : isCT_InstrR
        (.Cassgn (.Lvar x) tag ty (.Papp2 op (.Pvar y) (.Pconst k))) = true := hi
      simp [isCT_InstrR] at hPc
      exact hPc
    · apply ih
      rw [isCT_renameBody]
      exact hrest
  | case5 lo rest x tag ty op y k _ _ _ hMerge tail lo' hCG ih =>
    rw [isCT_Cmd_cons_iff] at h
    obtain ⟨hi, hrest⟩ := h
    have hEq : (coalesceGo lo
        (.Cassgn (.Lvar x) tag ty (.Papp2 op (.Pvar y) (.Pconst k)) :: rest)).1
        = .Cassgn (.Lvar x) tag ty (.Papp2 op (.Pvar y) (.Pconst k)) ::
          (coalesceGo lo rest).1 := by
      rw [coalesceGo, if_neg hMerge]
    rw [hEq, isCT_Cmd_cons_iff]
    exact ⟨hi, ih hrest⟩
  | case6 lo i rest tail lo' hCG hNotPvar hNotPconst ih =>
    -- Catch-all: i doesn't match either Papp2-Pvar-Pvar or Papp2-Pvar-Pconst pattern.
    rw [isCT_Cmd_cons_iff] at h
    obtain ⟨hi, hrest⟩ := h
    -- Reduce coalesceGo on this case using the catch-all branch.
    -- Lean's `rw [coalesceGo]` produces discrimination obligations of the
    -- shape `∀ x tag ty op y z, i = Cassgn (Lvar x) tag ty (Papp2 op …) → False`,
    -- which are exactly `hNotPvar` and `hNotPconst`.
    have hEq : (coalesceGo lo (i :: rest)).1 = i :: (coalesceGo lo rest).1 := by
      rw [coalesceGo]
      · exact hNotPvar
      · exact hNotPconst
    rw [hEq, isCT_Cmd_cons_iff]
    exact ⟨hi, ih hrest⟩

/-- Full pipeline: `optimize` preserves CT. -/
theorem isCT_optimize (liveOut : List Var) (c : Cmd) (h : isCT_Cmd c) :
    isCT_Cmd (optimize liveOut c).1 :=
  isCT_coalesceGo _ _
    (isCT_deadCodeElim _ _
      (isCT_propagateConstants _
        (isCT_peepholeArith _ h)))

/-! ## Part B: Extended evaluator with ADC/ADD intrinsics -/

/-- Pack a `Bool` into a `BitVec n`: `true ↦ 1`, `false ↦ 0`. -/
def boolToBV (n : Nat) : Bool → BitVec n
  | true => 1
  | false => 0

/-- Extended reference semantics. Definitionally equal to
    `pureEvalMonoCmd` on `Cassgn`-only bodies. Adds two new cases for
    flag-producing multi-output intrinsics:
    * `ADD_64` : `(of, cf, sf, pf, zf, r) := #ADD_64(a, b)`
    * `ADC_64` : `(of, cf, sf, pf, zf, r) := #ADC_64(a, b, cin)`
    Flags other than `cf` are discarded (emitted as `Lnone`).

    Extension 3A (`Cfor`) is handled via the separate
    `unrollAllCfor` pre-pass (below), which returns a `Cfor`-free
    `Cmd` suitable for this evaluator. Clients that want loop
    unrolling should call `pureEvalMonoCmdExt _ _ _ (unrollAllCfor c)`. -/
def pureEvalMonoCmdExt (n : Nat) (env : Var → BitVec n) (retVar : Var) :
    List InstrR → BitVec n
  | [] => env retVar
  | .Cassgn (.Lvar x) _ _ e :: rest =>
    pureEvalMonoCmdExt n
      (fun w => if w = x.var then pureEvalMonoExpr n env e else env w)
      retVar rest
  | .Copn [.Lnone _ _, .Lvar cfv, .Lnone _ _, .Lnone _ _, .Lnone _ _, .Lvar rv] _
          (.Oasm ⟨"ADD_64"⟩) [.Pvar av, .Pvar bv] :: rest =>
    let a := env av.gv.var
    let b := env bv.gv.var
    let p := BitVec.adc a b false
    pureEvalMonoCmdExt n
      (fun w =>
        if w = cfv.var then boolToBV n p.fst
        else if w = rv.var then p.snd
        else env w)
      retVar rest
  | .Copn [.Lnone _ _, .Lvar cfv, .Lnone _ _, .Lnone _ _, .Lnone _ _, .Lvar rv] _
          (.Oasm ⟨"ADC_64"⟩) [.Pvar av, .Pvar bv, .Pvar cinv] :: rest =>
    let a := env av.gv.var
    let b := env bv.gv.var
    let cinBool := (env cinv.gv.var).toNat ≠ 0
    let p := BitVec.adc a b cinBool
    pureEvalMonoCmdExt n
      (fun w =>
        if w = cfv.var then boolToBV n p.fst
        else if w = rv.var then p.snd
        else env w)
      retVar rest
  | _ :: rest => pureEvalMonoCmdExt n env retVar rest

/-! ### Cfor unrolling pre-pass (Extension 3A)

`unrollAllCfor` replaces every *top-level* `Cfor v .UpTo lo hi body` in a
command list with `hi - lo` concatenated copies of its body (the body
itself is not recursively unrolled — for Extension 3A we restrict to
one loop level, which covers all planned ports). The AST's
`Range.lo`/`Range.hi` are plain `Nat`, so the unroll count is
statically known and `decide` can fully reduce the result.

The resulting `Cmd` contains no top-level `Cfor`, so `pureEvalMonoCmd`
is definitionally applicable to it. -/

/-- Unroll top-level `Cfor` loops in a command list. Jasmin's
    `inline int` semantics match exactly: the loop is compile-time, so
    running the loop is the same as running the concatenated unrolled
    copies. Structural recursion on the outer list (loop body is not
    traversed — single-level unrolling only). -/
def unrollCfor1 : List InstrR → List InstrR
  | [] => []
  | .Cfor _ range body :: rest =>
    let count := range.hi - range.lo
    (List.replicate count body).flatten ++ unrollCfor1 rest
  | i :: rest => i :: unrollCfor1 rest

/-- The name callers use for the `Cfor` pre-pass (`unrollCfor1`); an
    `abbrev`, so the two are interchangeable. -/
abbrev unrollAllCfor := unrollCfor1

/-- Bodies with no `Copn`. -/
def copnFree : Cmd → Bool
  | [] => true
  | .Copn _ _ _ _ :: _ => false
  | _ :: rest => copnFree rest

/-- **Conservative-extension theorem.** On `Copn`-free bodies,
    `pureEvalMonoCmdExt` equals `pureEvalMonoCmd` — so existing
    correctness results transfer. -/
theorem pureEvalMonoCmdExt_agrees_on_copnFree
    {n : Nat} (env : Var → BitVec n) (retVar : Var) (c : Cmd)
    (h : copnFree c = true) :
    pureEvalMonoCmdExt n env retVar c = pureEvalMonoCmd n env retVar c := by
  induction c generalizing env with
  | nil => rfl
  | cons i rest ih =>
    cases i with
    | Cassgn lv _ _ _ =>
      cases lv with
      | Lvar _ =>
        simp only [pureEvalMonoCmdExt, pureEvalMonoCmd]
        exact ih _ (by simpa [copnFree] using h)
      | _ =>
        simp only [pureEvalMonoCmdExt, pureEvalMonoCmd]
        exact ih _ (by simpa [copnFree] using h)
    | Copn _ _ _ _ => simp [copnFree] at h
    | Cif _ _ _ | Cfor _ _ _ | Cwhile _ _ _ | Ccall _ _ _ _ =>
      simp only [pureEvalMonoCmdExt, pureEvalMonoCmd]
      exact ih _ (by simpa [copnFree] using h)

/-! ## Part C: Bridge to the semantic CT framework (`SecureCompilation.CTPass`)

The syntactic `isCT_Cmd` predicate certifies a source-level subset
(whitelisted ops, no data-dependent control flow, no variable shifts).
To connect to `SecureCompilation.CTPass`'s `ct_spComp` predicate, we
observe that every port's `catCryptDialect` denotation is `SPComp.pure _`
(via `translateMonoCmdD_denoteSP_native`), and **any deterministic
`SPComp.pure` computation is `ct_spComp`**: its `SPTree` is a single
`.ret a` node whose shape is the constant `SPShape.ret` regardless of the
input.

So: *every port that goes through `translateMonoCmdD` is automatically
`ct_spComp`*, without needing the syntactic `isCT_Cmd` at all for this
particular bridge. The `isCT_Cmd` predicate still matters for
guaranteeing no CT-hostile operations (variable shifts, `Cif` on
secrets, division) even before we reach the dialect SSA — those are caught
at the syntactic layer. -/

open CatCrypt.Core CatCrypt.Crypto
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.Jasmin.ToSSADialect
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge (toVIRVal)
open CatCrypt.Crypto.SecureCompilation.Dialects.CatCryptDialectSP

/-- **Deterministic computations are CT.** Given any total function
    `f : α → β`, the computation `fun a => SPComp.pure (f a)` is
    `ct_spComp` — its `SPTree` is always the single-node `ret`,
    independent of input. -/
theorem ct_spComp_of_pure {α β : Type} (f : α → β) :
    ct_spComp (fun a => SPComp.pure (f a)) := by
  refine ⟨fun a => SPTree.ret (f a), ?_, .ret, ?_⟩
  · intro a; rfl
  · intro a; rfl

/-- **Corollary**: any port emitted through the dialect-targeting
    translator `translateMonoCmdD` (one input) has a `catCryptDialect`
    denotation that is `ct_spComp` — because the denotation is
    `SPComp.pure (pureEvalMonoCmd …)` by the native correctness
    `translateMonoCmdD_denoteSP_native`. This discharges the semantic-CT
    obligation for every port without further work, complementing the
    syntactic `isCT_Cmd` guarantee. -/
theorem translateMonoCmdD_denote_is_ct
    (inputVar retVar : Var) (n : Nat) (body : List InstrR)
    (dprog : Com catCryptDialect [.sword n] (.sword n))
    (h : ToSSADialect.translateMonoCmdD
          (ToSSA.MonoVarMap.extend ToSSA.MonoVarMap.empty inputVar) retVar body
          = some dprog) :
    ct_spComp (fun (a : BitVec n) => Com.denoteSP dprog (toVIRVal (.cons a .nil))) := by
  have heq : (fun (a : BitVec n) => Com.denoteSP dprog (toVIRVal (.cons a .nil)))
    = (fun a => SPComp.pure
        (ToSSA.pureEvalMonoCmd n
          (fun w => if w = inputVar then a else 0) retVar body)) := by
    funext a
    refine ToSSADialect.translateMonoCmdD_denoteSP_native _ (.cons a .nil)
      (fun w => if w = inputVar then a else 0) retVar body dprog ?_ h
    intro w cv h_lookup
    simp only [ToSSA.MonoVarMap.extend, ToSSA.MonoVarMap.empty] at h_lookup
    split at h_lookup
    · rename_i h_eq; simp at h_lookup; cases h_lookup
      simp [CVar.lookup, h_eq]
    · simp at h_lookup
  rw [heq]
  exact ct_spComp_of_pure _

end CatCrypt.Crypto.Jasmin
