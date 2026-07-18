/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.S2NBignumSSA
import CatCrypt.Crypto.Jasmin.BignumExec

set_option autoImplicit false

/-!
# FEASIBILITY PROTOTYPE — verified variable-length `mpn_add_n`

**EXPERIMENTAL FILE.**  This is a feasibility prototype for the
"runtime-length loop" capability that a verified GMP replacement
(`mpn_add_n`: add two equal-length limb arrays with carry) needs.  The
existing high-speed-crypto MLIR/Jasmin pipeline only emits straight-line
/ compile-time-unrolled code; this file demonstrates how far the *Jasmin
`Cwhile`* path already gets us toward a genuine runtime-bounded loop, and
states + proves the functional spec at the `List (BitVec 64)` denotation
level.

## Why the Jasmin `Cwhile` path (not MLIR `scf.for`)

Two candidate loop targets were investigated:

* **(a) MLIR `scf.for` / `scf.while` from `LowCTToMLIR`.**  The MLIR
  emitter (`LowCTToMLIR.emitCmd`) emits `// <RFor: not emitted>` and
  `// <RWhileNz: not emitted>` — there is *no* runtime loop at all.
  Adding `scf.for` would mean writing a new region-carrying emitter from
  scratch with zero existing validation infrastructure.

* **(b) Jasmin `Cwhile` with a runtime bound.**  The Jasmin emitter
  (`JasminEmit.emitInstr`) *already* renders
  `Cwhile [] (n != 0) cafter` to `while (n != 0) { … }` and the comments
  record this shape was validated with `jasminc`.  An existing port
  (`S2NBignumSSA.WordBitsize`, "Port 29") ships a working runtime
  `while (a != 0)` loop, and `BignumExec.bignumExecFuel` gives a
  fuel-bounded executable semantics for `Cwhile` (one iteration unrolled
  into `Cif cond (cafter ++ [Cwhile …]) []`).

**Chosen: (b).**  The Jasmin `Cwhile` path is dramatically lower friction
— the emitter, a validated example, and a loop-aware interpreter all
already exist.  No core-AST edit is required: `mpn_add_n` is expressed
using only existing `InstrR` constructors.

## What this prototype delivers

1. A Jasmin `FunDecl` `mpnAddNFd` for `mpn_add_n(op, ap, bp, n)` built as
   a *pointer-advancing* `while (n != 0)` loop using only emitter-
   supported instruction shapes (constant-offset `Pload`/`Lmem`,
   `#ADC_64`, `+=`/`-=`).  `#eval` produces the real `.jazz` text.

2. A pure functional reference `mpnAddN : List (BitVec 64) →
   List (BitVec 64) → Bool → (List (BitVec 64) × Bool)` (carry-in /
   carry-out) and a little-endian denotation `toNat`.

3. The functional spec
   `toNat (mpnAddN a b cin).1 + 2^(64*a.length) * (carry-out as Nat)
      = toNat a + toNat b + (cin as Nat)`,
   **proved by induction on the limb list** (the inductive invariant the
   loop maintains).  This is the load-bearing obligation: `bv_decide`
   alone cannot close an unbounded loop.

## Honest status

* The carry-chain spec on the *pure reference* `mpnAddN` is fully proved.
* The bridge from the emitted Jasmin loop to `mpnAddN` (i.e. that
  `bignumExecFuel` on `mpnAddNFd.body` computes `mpnAddN` on the
  in-memory limb arrays) is **fully proved** — see `MpnAddNJasminRefines`
  near the end.  It rests on a `Cwhile` loop-invariant rule over the
  byte-memory model with pointer aliasing (§5–§8) and a per-iteration
  induction on the limb list (§10).
-/

namespace CatCrypt.Crypto.Jasmin.Examples.MpnAddPrototype

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Emit

/-! ## §1  The Jasmin `mpn_add_n` body — runtime `Cwhile` loop -/

/-- `reg u64` variable. -/
private def vr (s : String) : Var := { vname := s, vtype := .sword .U64 }

/-- A `Pvar` reading register `s`. -/
private def pv (s : String) : PExpr := .Pvar { gv := { var := vr s }, gs := false }

/-- Memory load `x := [:u64 base + 0]` (offset 0 — the only emitter-
    supported runtime-pointer form; we advance the pointer instead of
    indexing). -/
private def loadAt0 (x base : String) : InstrR :=
  .Cassgn (.Lvar { var := vr x }) .AT_none (.sword .U64)
    (.Pload .U64 { var := vr base } (.Pconst 0))

/-- Memory store `[:u64 base + 0] := src`. -/
private def storeAt0 (base src : String) : InstrR :=
  .Cassgn (.Lmem .U64 { var := vr base } (.Pconst 0)) .AT_none (.sword .U64)
    (.Pvar { gv := { var := vr src }, gs := false })

/-- `r += k` / `r -= k` style scalar update (`Cassgn (Papp2 op (Pvar r) (Pconst k))`). -/
private def binImm (r : String) (op : SOp2) (k : Int) : InstrR :=
  .Cassgn (.Lvar { var := vr r }) .AT_none (.sword .U64)
    (.Papp2 op (pv r) (.Pconst k))

private def adc_flag_pre  : List LVal := [.Lnone {} (.sword .U64)]
private def adc_flag_post : List LVal := List.replicate 3 (.Lnone {} (.sword .U64))

/-- `_, cf, _, _, _, r = #ADC_64(a, b, cin);` — the carry register `cin`
    is also the carry-out register `cf`, threading the carry across loop
    iterations. -/
private def adcCopn (cfName rName aName bName cinName : String) : InstrR :=
  .Copn (adc_flag_pre ++ [.Lvar { var := vr cfName }] ++ adc_flag_post
          ++ [.Lvar { var := vr rName }])
        .AT_none (.Oasm ⟨"ADC_64"⟩)
        [pv aName, pv bName, pv cinName]

/-- One loop iteration body:
    ```
    t = [:u64 ap + 0];
    s = [:u64 bp + 0];
    _, cf, _, _, _, r = #ADC_64(t, s, cf);
    [:u64 op + 0] = r;
    ap += 8; bp += 8; op += 8;
    n  -= 1;
    ```
    The carry register `cf` is initialised to 0 before the loop (so the
    first iteration's `#ADC_64(_, _, cf)` is a plain add) and is
    read-modified-written each iteration. -/
def loopBody : List InstrR :=
  [ loadAt0 "t" "ap"
  , loadAt0 "s" "bp"
  , adcCopn "cf" "r" "t" "s" "cf"
  , storeAt0 "op" "r"
  , binImm "ap" (.Oadd .U64) 8
  , binImm "bp" (.Oadd .U64) 8
  , binImm "op" (.Oadd .U64) 8
  , binImm "n"  (.Osub .U64) 1 ]

/-- Full body of `mpn_add_n`:
    ```
    cf = 0;
    while (n != 0) { <loopBody> }
    ```
    The carry register `cf` survives the loop; a production version would
    return it (the GMP `mpn_add_n` ABI returns the final carry as the
    function result).  Here the function is void (writes to `*op`);
    `cf` is left in a register for a follow-up `return cf;`. -/
def body : List InstrR :=
  [ .Cassgn (.Lvar { var := vr "cf" }) .AT_none (.sword .U64) (.Pconst 0)
  , .Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBody ]

/-- `mpn_add_n(op, ap, bp, n)` as a Jasmin `FunDecl`.  Void return
    (output via the `op` pointer); SysV ABI `rdi=op, rsi=ap, rdx=bp,
    rcx=n`. -/
def mpnAddNFd : FunDecl where
  name := { name := "mpn_add_n" }
  params := [⟨{ var := vr "op" }⟩, ⟨{ var := vr "ap" }⟩,
             ⟨{ var := vr "bp" }⟩, ⟨{ var := vr "n" }⟩]
  body := body
  results := []   -- void: result is via *op; carry left in `cf`

/-- The function is constant-time-*shaped*: the loop condition `n != 0`
    depends only on the public length `n`, never on a secret limb. -/
example : CatCrypt.Crypto.Jasmin.isCT_Cmd body = true := by decide

/-- Emit the real `.jazz` source.  `#eval` this to read the emitted loop. -/
def emitted : Option String := emitFunDecl mpnAddNFd

#eval match emitted with | some s => s | none => "EMIT FAILED"

/-! ## §2  Pure functional reference + little-endian denotation -/

/-- Little-endian denotation: `toNat [w0, w1, …] = w0 + 2^64·w1 + …`. -/
def toNat : List (BitVec 64) → Nat
  | []      => 0
  | w :: ws => w.toNat + 2 ^ 64 * toNat ws

/-- One ADC step on `BitVec 64`: returns `(sum, carry-out)`.
    `sum = (a + b + cin) mod 2^64`, `carry-out = (a + b + cin) / 2^64 ∈ {0,1}`. -/
def adcStep (a b : BitVec 64) (cin : Bool) : BitVec 64 × Bool :=
  let s : Nat := a.toNat + b.toNat + (if cin then 1 else 0)
  (BitVec.ofNat 64 s, decide (s ≥ 2 ^ 64))

/-- Pure reference for `mpn_add_n`: add two limb lists with a carry chain,
    recursing in lockstep.  Returns `(result limbs, final carry-out)`.
    The recursion stops when *either* list is exhausted (GMP requires
    equal length; the spec below is stated for equal-length inputs, where
    the two `nil` branches never disagree).  This is exactly the carry
    chain the emitted `while (n != 0)` loop walks, limb by limb. -/
def mpnAddN : List (BitVec 64) → List (BitVec 64) → Bool →
    (List (BitVec 64) × Bool)
  | a :: as, b :: bs, cin =>
      let (r, cout) := adcStep a b cin
      let (rs, fcout) := mpnAddN as bs cout
      (r :: rs, fcout)
  | _, _, cin => ([], cin)

/-- Boolean carry as a Nat (0 or 1). -/
def carryNat (c : Bool) : Nat := if c then 1 else 0

/-! ## §3  Functional spec: the carry-chain invariant

The load-bearing theorem.  `bv_decide` cannot close this — it is a
statement about a list of unbounded length, so it needs an inductive
invariant.  The invariant is exactly the per-limb carry-chain identity:
after processing the first `k` limbs, the partial output denotes
`(low k bits of a) + (low k bits of b) + cin`, with the running carry
sitting in bit position `64·k`.  We prove it by induction on the limb
list. -/

/-- The single-step ADC identity, on `Nat`:
    `adcStep a b cin` produces `(sum, cout)` with
    `sum.toNat + 2^64 · cout = a.toNat + b.toNat + cin`.
    This is the leaf of the carry chain; `bv_decide`-friendly facts about
    one limb feed the inductive step. -/
theorem adcStep_spec (a b : BitVec 64) (cin : Bool) :
    (adcStep a b cin).1.toNat + 2 ^ 64 * carryNat (adcStep a b cin).2
      = a.toNat + b.toNat + carryNat cin := by
  unfold adcStep carryNat
  -- `a.toNat, b.toNat < 2^64` ⇒ `s < 2·2^64`, so `s / 2^64 ∈ {0,1}`
  -- and `(s % 2^64) + 2^64·(s ≥ 2^64 ? 1 : 0) = s`.
  have ha : a.toNat < 2 ^ 64 := a.isLt
  have hb : b.toNat < 2 ^ 64 := b.isLt
  simp only [BitVec.toNat_ofNat, decide_eq_true_eq]
  -- Abbreviate the pre-reduction sum as `s`, keeping its definition in `hs`
  -- so omega retains the `s < 2·2^64` bound from the limb bounds.
  set s : Nat := a.toNat + b.toNat + (if cin then 1 else 0) with hs
  have hc1 : (if cin then 1 else 0) ≤ 1 := by cases cin <;> simp
  have hub : s < 2 ^ 64 * 2 := by rw [hs]; omega
  by_cases hge : s ≥ 2 ^ 64
  · -- carry-out is 1; the wrapped sum is `s - 2^64`.
    have hmod : s % 2 ^ 64 = s - 2 ^ 64 := by omega
    simp only [hge, if_true, hmod]
    omega
  · -- carry-out is 0; `s < 2^64` so `s % 2^64 = s`.
    have hlt : s < 2 ^ 64 := by omega
    simp only [hge, if_false]
    rw [Nat.mod_eq_of_lt hlt]
    omega

/-- **Main functional spec — proved by induction on the limb list.**

    For equal-length limb lists `a, b` and any carry-in `cin`, the pure
    reference `mpnAddN` satisfies the multi-precision addition identity:
    the denotation of the output limbs, plus the final carry-out shifted
    to bit `64·|a|`, equals `toNat a + toNat b + cin`.

    This is the inductive invariant the emitted `while (n != 0)` loop
    maintains: each iteration peels one limb (`adcStep_spec`), and the IH
    carries the identity over the `2^64`-scaled tail. -/
theorem mpnAddN_spec :
    ∀ (a b : List (BitVec 64)), a.length = b.length → ∀ (cin : Bool),
      toNat (mpnAddN a b cin).1
        + (2 ^ 64) ^ a.length * carryNat (mpnAddN a b cin).2
      = toNat a + toNat b + carryNat cin := by
  intro a
  induction a with
  | nil =>
    intro b hlen cin
    -- b is also empty; both sides reduce to `carryNat cin`.
    cases b with
    | nil => simp [mpnAddN, toNat, carryNat]
    | cons _ _ => simp at hlen
  | cons a as ih =>
    intro b hlen cin
    cases b with
    | nil => simp at hlen
    | cons b bs =>
      have hlen' : as.length = bs.length := by simpa using hlen
      -- Name the one-limb ADC result `p` and the recursive tail result `q`,
      -- keeping the defining equations so the head/tail specs apply.
      set p := adcStep a b cin with hp
      have hstep := adcStep_spec a b cin
      rw [← hp] at hstep
      set q := mpnAddN as bs p.2 with hq
      have htail := ih bs hlen' p.2
      rw [← hq] at htail
      -- Unfold one step of `mpnAddN` and `toNat`; the let-bindings resolve
      -- to `p` and `q`.
      have hunfold : mpnAddN (a :: as) (b :: bs) cin = (p.1 :: q.1, q.2) := by
        simp only [mpnAddN, hp, hq]
      rw [hunfold]
      simp only [toNat, List.length_cons]
      -- `(2^64)^(n+1) = 2^64 * (2^64)^n`.  Abstract `M := 2^64` and
      -- `P := (2^64)^as.length` so the goal becomes purely linear, then
      -- close it with the head spec (`hstep`) + the IH (`htail`).
      have hpow : (2 ^ 64) ^ (as.length + 1) = 2 ^ 64 * (2 ^ 64) ^ as.length := by
        rw [pow_succ]; ring
      rw [hpow]
      -- `2^64 * toNat q.1 + 2^64 * ((2^64)^as.length * carryNat q.2)`
      --   = 2^64 * (toNat q.1 + (2^64)^as.length * carryNat q.2)  [factor]
      --   = 2^64 * (toNat as + toNat bs + carryNat p.2)           [htail]
      have hkey : 2 ^ 64 * toNat q.1 + 2 ^ 64 * (2 ^ 64) ^ as.length * carryNat q.2
          = 2 ^ 64 * (toNat as + toNat bs + carryNat p.2) := by
        rw [← htail]; ring
      -- Goal: p.1.toNat + 2^64*toNat q.1 + 2^64*(2^64)^as.length*carryNat q.2
      --        = a.toNat + 2^64*toNat as + (b.toNat + 2^64*toNat bs) + carryNat cin
      omega

/-- The usual entry point: carry-in 0.  `mpn_add_n` with no incoming
    carry adds two equal-length bignums; the result plus the carry-out at
    bit `64·|a|` equals `toNat a + toNat b`.  This is the GMP `mpn_add_n`
    contract (the return value is the carry-out). -/
theorem mpnAddN_spec_carryIn_false (a b : List (BitVec 64))
    (hlen : a.length = b.length) :
    toNat (mpnAddN a b false).1
      + (2 ^ 64) ^ a.length * carryNat (mpnAddN a b false).2
    = toNat a + toNat b := by
  have h := mpnAddN_spec a b hlen false
  simpa [carryNat] using h

/-! ### Concrete sanity checks (decidable `#eval`) -/

/-- `[0xFFFF…FFFF] + [1]` overflows: result `0`, carry-out `true`. -/
example : mpnAddN [(-1 : BitVec 64)] [1] false = ([0], true) := by native_decide

/-- `[5,0] + [7,0]` (two-limb) = `[12,0]`, no carry. -/
example : mpnAddN [5, 0] [7, 0] false = ([12, 0], false) := by native_decide

/-- Carry propagation across two limbs: `[0xFFFF…, 0] + [1, 0] = [0, 1]`. -/
example : mpnAddN [(-1 : BitVec 64), 0] [1, 0] false = ([0, 1], false) := by
  native_decide

#eval toNat (mpnAddN [(-1 : BitVec 64), 0] [1, 0] false).1   -- 2^64

/-! ## §4  Bridge to the emitted Jasmin loop — STATED, OPEN

The pure reference `mpnAddN` is what the emitted `while (n != 0)` loop
computes, limb by limb, over byte memory.  The bridge `MpnAddNJasminRefines`
below says exactly that, against the `BignumExec.bignumExecFuel`
semantics: starting from a state whose memory holds limb lists `as`, `bs`
at the `ap`, `bp` pointers and `n = |as|`, after running `mpnAddNFd.body`
the memory at `op` holds `(mpnAddN as bs false).1` and register `cf` holds
the carry-out.

## Status: the bridge is now PROVED

Phase 1 (this file's §5–§8) discharges what the original prototype called
the "load-bearing obligation": a **`Cwhile` loop-invariant rule over the
byte-memory model with pointer aliasing**.  Concretely, all of the
following are fully proved (no `sorry`):

* **Memory algebra** (§5): `load64Mem`/`store64` read-back
  (`load64Mem_store64_same`) and the disjoint-block frame rule
  (`load64Mem_store64_disjoint`), via per-byte `bv_decide` reasoning
  about `UInt64` addresses.
* **ADC bridge** (§6): the executable `addCarryIn` matches the pure
  `adcStep` (`addCarryIn_sum`, `addCarryIn_carry`).
* **One straight-line iteration** (§7): `bignumExec_loopBody_step`
  computes the exact effect of one `loopBody` pass (load `a`,`b`; ADC;
  store sum at `op`; advance `ap`,`bp`,`op` by 8; `n -= 1`).
* **The `Cwhile` fuel rule** (§8): one loop iteration when the condition
  holds (`bignumExecFuel_loop_step`) and the loop exit when it fails
  (`bignumExecFuel_loop_exit`).  This *is* the invariant rule the original
  docstring said `BignumExec` "does not yet provide".

The emitted loop condition `Papp2 (Oneq U64) (Pvar n) (Pconst 0)` is now
evaluated by `BignumExec.evalPExpr` (its `Oneq` arm returns `1` when the
operands differ, `0` otherwise — nonzero iff `!=` holds, matching how
`bignumExecFuel`'s `Cif`/`Cwhile` test the guard).  With the guard
evaluable, the §8 rules instantiate directly: each iteration is
`bignumExecFuel_loop_step` (condition true since `n ≠ 0`,
`evalPExpr_loopCond_true`), the final step is `bignumExecFuel_loop_exit`
(condition false at `n = 0`, `evalPExpr_loopCond_false`), and
per-iteration correctness is `bignumExec_loopBody_step` + the
disjointness frame (`load64Mem_store64_disjoint`).  `MpnAddNJasminRefines`
below assembles these into the full bridge, proved by induction on the
limb list.

The disjointness hypotheses below (`op` vs `ap`, `op` vs `bp`) are the
separation preconditions that prevent the per-iteration `op[i]` store from
corrupting unread `ap`/`bp` limbs; they are required for the bridge to be
*true* (GMP's in-place `rp == up` aliasing case is a deliberate
follow-up).  This `Examples/` prototype is never imported by `Crypto`. -/

/-- Predicate: memory `m` holds the limb list `ws` little-endian starting
    at byte address `base` (one `u64` = 8 bytes per limb). -/
def memHoldsLimbs (m : MemoryModel.Mem) (base : UInt64) :
    List (BitVec 64) → Prop
  | []      => True
  | w :: ws =>
      load64Mem m base = some (UInt64.ofNat w.toNat) ∧
      memHoldsLimbs m (base + 8) ws

/-- **The bridge statement, as an abbreviation.**  This is the shape of
    the theorem connecting the emitted Jasmin loop to `mpnAddN`: starting
    from a state whose memory holds `as` at `ap`, `bs` at `bp`, with
    `n = |as|`, running `mpnAddNFd.body` lands in a state whose memory at
    `op` holds `(mpnAddN as bs false).1` and whose `cf` register holds the
    carry-out.  It is *proved* as `MpnAddNJasminRefines` in §10 below
    (the proof needs the §5–§9 lemmas, hence the split).

    The two `Disjoint` hypotheses separate the `op` output region from the
    `ap`/`bp` input regions (each `8·|as|` bytes), so the per-iteration
    store cannot corrupt unread source limbs.  The aliased in-place case
    (GMP allows `rp == up`) is left as a follow-up. -/
def MpnAddNRefinesStmt : Prop :=
  ∀ (s : BignumState) (as bs : List (BitVec 64)) (fuel : Nat),
    as.length = bs.length →
    s.regs "n" = BitVec.ofNat 64 as.length →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) as →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "bp").toNat) bs →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * as.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * as.length)) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * as.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat) (8 * as.length)) →
    fuel > 2 * as.length + 2 →
    ∃ s', bignumExecFuel emptyRegistry fuel body s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "op").toNat) (mpnAddN as bs false).1 ∧
      s'.regs "cf" = BitVec.ofNat 64 (carryNat (mpnAddN as bs false).2)

/-! ## §5  Memory algebra: `load64Mem` / `store64` (Phase 1 foundation)

The Phase-1 loop-invariant rule needs two facts about how an 8-byte
`store64` interacts with an 8-byte `load64Mem`:

* **read-back**: loading the just-stored word returns it;
* **frame**: a store into a disjoint 8-byte block leaves a load unchanged.

The recurring obstacle (flagged in `MemoryModel.lean`) is UInt64 address
arithmetic — `omega` cannot see `UInt64`.  **`bv_decide` can**, and is the
tool of choice for every pointer (in)equality below. -/

open CatCrypt.Crypto.Jasmin.MemoryModel

/-- UInt64 left-cancellation, via `bv_decide` (not `omega`). -/
theorem uint64_add_left_cancel (a x y : UInt64) (h : a + x = a + y) : x = y := by
  bv_decide

/-! ### Next step: the `load64Mem`/`store64` read-back + frame lemmas

The two facts the loop rule needs are:

* `load64Mem (m.store64 a v) a = some v`  (read-back)
* `Disjoint (range a 8) (range a' 8) → load64Mem (m.store64 a' v) a = load64Mem m a`
  (frame)

Both reduce, after `simp only [load64Mem, Mem.store64]`, to an 8-byte
`Option`-bind chain over the nested `storeByte`s.  The byte (in)equalities
(`a+i ≠ a+j`, and cross-block `a+i ≠ a'+j` from `range_disjoint_byte_ne`)
are all `bv_decide`-provable — **`bv_decide` is the tool for the UInt64
address layer** (`omega` cannot see `UInt64`; see `uint64_add_left_cancel`).

Obstacle observed: `simp`'s *conditional-rewrite discharger* does not fire
`Mem.loadByte_storeByte_other` for the inner bytes even when the `a+i ≠ a+j`
facts are in the simp set (only the same-address outermost byte resolves).
The robust route is a per-byte `loadByte_store64` lemma proved by
`interval_cases` over the 8 offsets with explicit `bv_decide`-discharged
inequalities, then assembled.  This is the immediate Phase-1 work item. -/

/-- Reading byte `k` (`k < 8`) of a freshly `store64`-d word returns
    `byteAt v k`.  Proved by `interval_cases` over the 8 offsets; each
    case peels the nested `storeByte`s, discharging the `a+i ≠ a+j`
    side conditions with `bv_decide` (`omega` cannot see `UInt64`). -/
theorem loadByte_store64 (m : Mem) (a v : UInt64) (k : Nat) (hk : k < 8) :
    (m.store64 a v).loadByte (a + UInt64.ofNat k) = some (byteAt v k) := by
  simp only [Mem.store64, Mem.loadByte, Mem.storeByte]
  -- The store chain writes bytes at `a + 7, a + 6, …, a + 0` (innermost
  -- last).  The load is at `a + ofNat k`; for fixed `k`, the matching
  -- condition is the one with offset `k`.  After normalizing
  -- `UInt64.ofNat <lit>` to a numeral (so `bv_decide` sees a BitVec
  -- constant), `repeat rw [if_neg …]` skips the `> k` offsets (each `≠`
  -- discharged by `bv_decide`); when the matching offset is reached the
  -- `≠` proof fails, `repeat` stops, and the trailing `if_pos` fires.
  interval_cases k <;>
    simp only [show (UInt64.ofNat 0) = (0 : UInt64) from rfl,
               show (UInt64.ofNat 1) = (1 : UInt64) from rfl,
               show (UInt64.ofNat 2) = (2 : UInt64) from rfl,
               show (UInt64.ofNat 3) = (3 : UInt64) from rfl,
               show (UInt64.ofNat 4) = (4 : UInt64) from rfl,
               show (UInt64.ofNat 5) = (5 : UInt64) from rfl,
               show (UInt64.ofNat 6) = (6 : UInt64) from rfl,
               show (UInt64.ofNat 7) = (7 : UInt64) from rfl] <;>
    (repeat rw [if_neg (by bv_decide)]) <;>
    rw [if_pos (by bv_decide)]

/-- **Read-back.**  `load64Mem (m.store64 a v) a = some v`: loading the
    word just written returns it.  Each of the 8 byte loads resolves via
    `loadByte_store64` to `byteAt v k`; the little-endian recomposition
    back to `v` is a pure `BitVec` identity closed by `bv_decide`. -/
theorem load64Mem_store64_same (m : Mem) (a v : UInt64) :
    load64Mem (m.store64 a v) a = some v := by
  -- Resolve the 8 byte loads.  `loadByte_store64` is stated at
  -- `a + UInt64.ofNat k`; rewrite the `a, a+1, …, a+7` shapes to that
  -- normal form (the address equalities are `bv_decide` facts).
  have h0 := loadByte_store64 m a v 0 (by omega)
  have h1 := loadByte_store64 m a v 1 (by omega)
  have h2 := loadByte_store64 m a v 2 (by omega)
  have h3 := loadByte_store64 m a v 3 (by omega)
  have h4 := loadByte_store64 m a v 4 (by omega)
  have h5 := loadByte_store64 m a v 5 (by omega)
  have h6 := loadByte_store64 m a v 6 (by omega)
  have h7 := loadByte_store64 m a v 7 (by omega)
  simp only [show (UInt64.ofNat 0) = (0 : UInt64) from rfl,
             show (UInt64.ofNat 1) = (1 : UInt64) from rfl,
             show (UInt64.ofNat 2) = (2 : UInt64) from rfl,
             show (UInt64.ofNat 3) = (3 : UInt64) from rfl,
             show (UInt64.ofNat 4) = (4 : UInt64) from rfl,
             show (UInt64.ofNat 5) = (5 : UInt64) from rfl,
             show (UInt64.ofNat 6) = (6 : UInt64) from rfl,
             show (UInt64.ofNat 7) = (7 : UInt64) from rfl,
             show a + (0 : UInt64) = a from by bv_decide, Mem.loadByte]
    at h0 h1 h2 h3 h4 h5 h6 h7
  simp only [load64Mem, Mem.loadByte, h0, h1, h2, h3, h4, h5, h6, h7,
             Option.bind_some, bind, Option.bind]
  -- Goal now: recompose `byteAt v 0 … byteAt v 7` little-endian = `v`.
  -- `byteAt v k = (v >>> ofNat (8·k)).toUInt8`; normalize the shift
  -- amounts to numerals so `bv_decide` sees BitVec constants, then
  -- inject through `some` and close the pure recomposition identity.
  simp only [byteAt, Option.some.injEq,
             show (8 * 0 : Nat) = 0 from rfl, show (8 * 1 : Nat) = 8 from rfl,
             show (8 * 2 : Nat) = 16 from rfl, show (8 * 3 : Nat) = 24 from rfl,
             show (8 * 4 : Nat) = 32 from rfl, show (8 * 5 : Nat) = 40 from rfl,
             show (8 * 6 : Nat) = 48 from rfl, show (8 * 7 : Nat) = 56 from rfl,
             show (UInt64.ofNat 0) = (0 : UInt64) from rfl,
             show (UInt64.ofNat 8) = (8 : UInt64) from rfl,
             show (UInt64.ofNat 16) = (16 : UInt64) from rfl,
             show (UInt64.ofNat 24) = (24 : UInt64) from rfl,
             show (UInt64.ofNat 32) = (32 : UInt64) from rfl,
             show (UInt64.ofNat 40) = (40 : UInt64) from rfl,
             show (UInt64.ofNat 48) = (48 : UInt64) from rfl,
             show (UInt64.ofNat 56) = (56 : UInt64) from rfl]
  bv_decide

/-- **Per-byte frame.**  A `store64` at `a'` does not disturb the load of
    byte `a + ofNat k` (`k < 8`) when that address lies outside the
    8-byte block `[a', a' + 8)`.  The 8 `≠` side conditions come from the
    block-disjointness witness via `range_disjoint_byte_ne`. -/
theorem loadByte_store64_frame (m : Mem) (a a' v : UInt64) (k : Nat)
    (hk : k < 8)
    (hne : ∀ j : Nat, j < 8 → a + UInt64.ofNat k ≠ a' + UInt64.ofNat j) :
    (m.store64 a' v).loadByte (a + UInt64.ofNat k) = m.loadByte (a + UInt64.ofNat k) := by
  have hn0 := hne 0 (by omega)
  have hn1 := hne 1 (by omega)
  have hn2 := hne 2 (by omega)
  have hn3 := hne 3 (by omega)
  have hn4 := hne 4 (by omega)
  have hn5 := hne 5 (by omega)
  have hn6 := hne 6 (by omega)
  have hn7 := hne 7 (by omega)
  simp only [show (UInt64.ofNat 0) = (0 : UInt64) from rfl,
             show (UInt64.ofNat 1) = (1 : UInt64) from rfl,
             show (UInt64.ofNat 2) = (2 : UInt64) from rfl,
             show (UInt64.ofNat 3) = (3 : UInt64) from rfl,
             show (UInt64.ofNat 4) = (4 : UInt64) from rfl,
             show (UInt64.ofNat 5) = (5 : UInt64) from rfl,
             show (UInt64.ofNat 6) = (6 : UInt64) from rfl,
             show (UInt64.ofNat 7) = (7 : UInt64) from rfl,
             show a' + (0 : UInt64) = a' from by bv_decide] at hn0 hn1 hn2 hn3 hn4 hn5 hn6 hn7
  simp only [Mem.store64, Mem.loadByte, Mem.storeByte,
             if_neg hn7, if_neg hn6, if_neg hn5, if_neg hn4,
             if_neg hn3, if_neg hn2, if_neg hn1, if_neg hn0]

/-- **Frame.**  A `store64` into a block `[a', a' + 8)` disjoint from
    `[a, a + 8)` leaves `load64Mem … a` unchanged.  Each of the 8 byte
    loads is preserved by `loadByte_store64_frame`; the cross-block byte
    inequalities are supplied by `range_disjoint_byte_ne`. -/
theorem load64Mem_store64_disjoint (m : Mem) (a a' v : UInt64)
    (hdisj : MemoryModel.Disjoint (range a 8) (range a' 8)) :
    load64Mem (m.store64 a' v) a = load64Mem m a := by
  -- Each byte `a + ofNat k` (k < 8) avoids the whole `[a', a' + 8)`
  -- block, so its load is framed.
  have frame : ∀ k : Nat, k < 8 →
      (m.store64 a' v).loadByte (a + UInt64.ofNat k)
        = m.loadByte (a + UInt64.ofNat k) := by
    intro k hk
    refine loadByte_store64_frame m a a' v k hk (fun j hj => ?_)
    exact range_disjoint_byte_ne a a' 8 hdisj k j hk hj
  have f0 := frame 0 (by omega)
  have f1 := frame 1 (by omega)
  have f2 := frame 2 (by omega)
  have f3 := frame 3 (by omega)
  have f4 := frame 4 (by omega)
  have f5 := frame 5 (by omega)
  have f6 := frame 6 (by omega)
  have f7 := frame 7 (by omega)
  simp only [show (UInt64.ofNat 0) = (0 : UInt64) from rfl,
             show (UInt64.ofNat 1) = (1 : UInt64) from rfl,
             show (UInt64.ofNat 2) = (2 : UInt64) from rfl,
             show (UInt64.ofNat 3) = (3 : UInt64) from rfl,
             show (UInt64.ofNat 4) = (4 : UInt64) from rfl,
             show (UInt64.ofNat 5) = (5 : UInt64) from rfl,
             show (UInt64.ofNat 6) = (6 : UInt64) from rfl,
             show (UInt64.ofNat 7) = (7 : UInt64) from rfl,
             show a + (0 : UInt64) = a from by bv_decide] at f0 f1 f2 f3 f4 f5 f6 f7
  simp only [load64Mem, f0, f1, f2, f3, f4, f5, f6, f7]

/-! ## §6  ADC bridge: executable `addCarryIn` matches pure `adcStep`

The emitted `#ADC_64` runs `BignumExec.addCarryIn` (BitVec carry logic);
the pure reference uses `adcStep` (Nat carry logic).  These two lemmas
show they agree once the carry-in register encodes `carryNat cin` as a
`BitVec 64`. -/

/-- ADC sum bridge: the result word of `addCarryIn` (carry-in encoded as
    a `BitVec`) is the wrapped Nat sum that `adcStep` produces. -/
theorem addCarryIn_sum (a b : BitVec 64) (c : Bool) :
    (addCarryIn a b (BitVec.ofNat 64 (if c then 1 else 0))).2
      = (adcStep a b c).1 := by
  have ha := a.isLt; have hb := b.isLt
  apply BitVec.eq_of_toNat_eq
  unfold addCarryIn adcStep
  cases c <;> simp [BitVec.toNat_add, BitVec.toNat_ofNat]

/-- The carry-out of `addCarryIn` is a single bit (`0` or `1`).  Needed
    so that the `BitVec`-encoded carry round-trips through `toNat`. -/
theorem addCarryIn_carry_toNat_le (a b : BitVec 64) (c01 : Nat) :
    (addCarryIn a b (BitVec.ofNat 64 c01)).1.toNat ≤ 1 := by
  unfold addCarryIn
  simp only [BitVec.toNat_or, BitVec.ult, decide_eq_true_eq]
  split_ifs <;> simp_all <;> decide

/-- ADC `toNat` identity for `addCarryIn`: the result word plus the
    carry-out shifted to bit 64 equals the unwrapped sum (carry-in given
    as a one-bit Nat).  The multi-precision analogue of `adcStep_spec`
    for the executable carry path. -/
theorem addCarryIn_spec (a b : BitVec 64) (c01 : Nat) (hc : c01 ≤ 1) :
    (addCarryIn a b (BitVec.ofNat 64 c01)).2.toNat
      + 2 ^ 64 * (addCarryIn a b (BitVec.ofNat 64 c01)).1.toNat
      = a.toNat + b.toNat + c01 := by
  have ha := a.isLt; have hb := b.isLt
  have hc' : c01 < 2 ^ 64 := by omega
  unfold addCarryIn
  simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_add,
             BitVec.ult, decide_eq_true_eq, Nat.mod_eq_of_lt hc',
             show ((1 : BitVec 64).toNat) = 1 from rfl]
  have hand : c01 &&& 1 = c01 := by
    rcases (by omega : c01 = 0 ∨ c01 = 1) with h | h <;> simp [h]
  rw [hand]
  split_ifs <;> simp_all <;> omega

/-- ADC carry bridge: the carry-out flag of `addCarryIn` equals the
    `BitVec`-encoded `carryNat` of `adcStep`'s carry-out.  Derived by
    cancelling the matching sums (`addCarryIn_sum`) in the two `toNat`
    identities (`addCarryIn_spec`, `adcStep_spec`). -/
theorem addCarryIn_carry (a b : BitVec 64) (c : Bool) :
    (addCarryIn a b (BitVec.ofNat 64 (if c then 1 else 0))).1
      = BitVec.ofNat 64 (carryNat (adcStep a b c).2) := by
  set c01 : Nat := if c then 1 else 0 with hc01
  have hc : c01 ≤ 1 := by rw [hc01]; cases c <;> simp
  apply BitVec.eq_of_toNat_eq
  -- Two `toNat` carry-chain identities with the SAME word (addCarryIn_sum)
  -- ⇒ the carries' `toNat`s agree; both sides are < 2^64.
  have hspec := addCarryIn_spec a b c01 hc
  have hstep := adcStep_spec a b c
  have hsum : (addCarryIn a b (BitVec.ofNat 64 c01)).2.toNat = (adcStep a b c).1.toNat := by
    rw [addCarryIn_sum]
  have hcle := addCarryIn_carry_toNat_le a b c01
  have hcarryNat_le : carryNat (adcStep a b c).2 ≤ 1 := by
    unfold carryNat; cases (adcStep a b c).2 <;> simp
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold carryNat at hstep ⊢
  omega

/-! ## §7  One loop iteration as an explicit state update

`loopBody` is straight-line, so it runs via `bignumExec`.  Given a state
whose memory holds limb `a` at `ap` and `b` at `bp`, one iteration:
loads `a`, `b`; ADCs them with the carry register; stores the sum at
`op`; advances `ap`, `bp`, `op` by 8 and decrements `n`.  This lemma
computes the resulting state explicitly. -/

/-- Address named by register `x` (offset 0), as the executable
    `resolveAddr` resolves it. -/
def regAddr (s : BignumState) (x : String) : UInt64 :=
  UInt64.ofNat (s.regs x).toNat

theorem resolveAddr_reg (s : BignumState) (x : String) :
    resolveAddr s { var := vr x } (.Pconst 0) = some (regAddr s x) := by
  simp only [resolveAddr, regAddr, vr]
  norm_num

/-- Advancing a pointer register by 8 (`BitVec` add, with wraparound)
    advances its resolved `UInt64` address by 8 (also with wraparound):
    the two `mod 2^64` reductions agree. -/
theorem regAddr_advance (bv : BitVec 64) :
    UInt64.ofNat (bv + 8).toNat = UInt64.ofNat bv.toNat + 8 := by
  apply UInt64.toNat.inj
  simp only [UInt64.toNat_ofNat', UInt64.toNat_add, BitVec.toNat_add,
             show ((8 : UInt64).toNat) = 8 from rfl,
             show ((8 : BitVec 64).toNat) = 8 from rfl]
  omega

/-- A `BitVec 64` round-trips through `UInt64.ofNat _.toNat` then
    `BitVec.ofNat 64 _.toNat`: the load decode is the identity on words. -/
theorem bv_uint_roundtrip (w : BitVec 64) :
    BitVec.ofNat 64 (UInt64.ofNat w.toNat).toNat = w := by
  have hw := w.isLt
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt hw]

@[simp] theorem setReg_mem (s : BignumState) (x : String) (v : BitVec 64) :
    (setReg s x v).mem = s.mem := rfl

@[simp] theorem setReg_regs (s : BignumState) (x : String) (v : BitVec 64) :
    (setReg s x v).regs = fun y => if y = x then v else s.regs y := rfl

@[simp] theorem storeMem_mem (s : BignumState) (addr v : UInt64) :
    (storeMem s addr v).mem = s.mem.store64 addr v := rfl

@[simp] theorem storeMem_regs (s : BignumState) (addr v : UInt64) :
    (storeMem s addr v).regs = s.regs := rfl

/-- One iteration of `loopBody` (run via the straight-line interpreter
    `bignumExec`), assuming memory holds limb `a` at `ap` and `b` at `bp`
    and the carry register encodes the incoming carry bit `cin`.
    The result state is described entirely by its `cf` register, its
    `ap`/`bp`/`op`/`n` registers, and a single `store64` at `op`. -/
theorem bignumExec_loopBody_step (s : BignumState) (a b : BitVec 64) (cin : Bool)
    (hcf : s.regs "cf" = BitVec.ofNat 64 (if cin then 1 else 0))
    (ha : load64Mem s.mem (regAddr s "ap") = some (UInt64.ofNat a.toNat))
    (hb : load64Mem s.mem (regAddr s "bp") = some (UInt64.ofNat b.toNat)) :
    ∃ s', bignumExec loopBody s = some s' ∧
      s'.mem = s.mem.store64 (regAddr s "op")
        (UInt64.ofNat (adcStep a b cin).1.toNat) ∧
      s'.regs "cf" = BitVec.ofNat 64 (carryNat (adcStep a b cin).2) ∧
      s'.regs "ap" = s.regs "ap" + 8 ∧
      s'.regs "bp" = s.regs "bp" + 8 ∧
      s'.regs "op" = s.regs "op" + 8 ∧
      s'.regs "n" = s.regs "n" - 1 := by
  -- Unfold the body into the nested `execInstr` matches, resolving the
  -- two loads (round-trip via `ha`/`hb`), the ADC bundle, the store, and
  -- the four register advances.  `setReg`/`storeMem` projection simp
  -- lemmas push `regAddr`/`.mem` through the intermediate states.  `vr`
  -- is left folded so `resolveAddr_reg` matches the base pointers.
  simp only [loopBody, loadAt0, adcCopn, storeAt0, binImm, adc_flag_pre, adc_flag_post,
             bignumExec, execInstr, evalPExpr, pv, resolveAddr_reg, vr,
             setReg_mem, setReg_regs, storeMem_mem, storeMem_regs,
             Option.bind_some, bind, Option.bind,
             List.replicate, List.cons_append, List.nil_append, writeSubBundle]
  -- Resolve the three base+offset addresses directly (offset 0 ⇒ the
  -- base register value), decide the string-literal register lookups in
  -- the intermediate `setReg`/`storeMem` states, reduce `+ 0`, then fire
  -- the two loads (`ha`/`hb`) and decode them (`bv_uint_roundtrip`).
  simp only [regAddr, resolveAddr, reduceIte, String.reduceEq, if_true, if_false,
             ↓reduceIte, setReg_regs, storeMem_regs, storeMem_mem,
             show BitVec.ofInt 64 0 = 0 from rfl, BitVec.add_zero,
             ha, hb, bv_uint_roundtrip, Option.bind_some, bind, Option.bind] at *
  -- Eliminate the residual `+ 0` in the two load addresses; `ha`/`hb`
  -- then fire and the loaded words decode to `a`/`b`.
  rw [show s.regs "ap" + 0 = s.regs "ap" from by bv_decide]
  rw [ha]
  simp only [bv_uint_roundtrip, Option.bind_some, bind, Option.bind]
  rw [show (setReg s "t" a).regs "bp" + 0 = s.regs "bp" from by
        simp only [setReg_regs]; bv_decide, setReg_mem, hb]
  simp only [bv_uint_roundtrip, Option.bind_some, bind, Option.bind]
  -- The witness state is now fully concrete.  Read off the carry register
  -- (ADC bridges, `hcf`), the store, and the four register advances.
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [setReg_regs, setReg_mem, storeMem_mem, storeMem_regs, regAddr,
               String.reduceEq, ↓reduceIte, reduceIte,
               hcf, addCarryIn_sum, addCarryIn_carry,
               show s.regs "op" + 0 = s.regs "op" from by bv_decide,
               show BitVec.ofInt 64 8 = (8 : BitVec 64) from rfl,
               show BitVec.ofInt 64 1 = (1 : BitVec 64) from rfl]

/-- `loopBody` consists only of `Cassgn`/`Copn` — it is straight-line. -/
theorem loopBody_straightLine : InstrR.bodyIsStraightLine loopBody := by
  simp only [loopBody, loadAt0, adcCopn, storeAt0, binImm, InstrR.bodyIsStraightLine,
             InstrR.isStraightLine, and_self]

/-- Every instruction of `loopBody` is non-control (so it commutes with
    the forward `bignumExecFuel_append_join`). -/
theorem loopBody_nonControl : ∀ i ∈ loopBody, i.isNonControl := by
  intro i hi
  simp only [loopBody, loadAt0, adcCopn, storeAt0, binImm, List.mem_cons,
             List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h <;> (subst h; exact True.intro)

/-! ## §8  One `Cwhile` iteration over `bignumExecFuel`

Unfold one loop iteration of the runtime `while (n != 0) { loopBody }`
when the condition is true: it consumes 2 fuel (`Cwhile → Cif → body`),
runs `loopBody` once (`bignumExec_loopBody_step`, lifted to `bignumExecFuel`
via the straight-line agreement and the forward append join), and
re-enters the loop on the resulting state. -/

/-- **Forward one-iteration rule.**  If the loop condition `n != 0`
    holds, `loopBody` runs to `s_mid`, and re-entering the loop on `s_mid`
    at fuel `f + 1` succeeds with `s'`, then the whole iteration at fuel
    `f + 3` also succeeds with `s'` — each iteration costs 2 fuel.  Stated
    forward (success ⇒ success) so only the `bignumExecFuel_append_join`
    direction is needed. -/
theorem bignumExecFuel_loop_step (reg : BignumRegistry) (f : Nat)
    (cond : PExpr) (s s_mid s' : BignumState)
    (hcond : evalPExpr s cond = some 1)
    (hbody : bignumExec loopBody s = some s_mid)
    (hrec : bignumExecFuel reg (f + 1) [.Cwhile [] cond loopBody] s_mid = some s') :
    bignumExecFuel reg (f + 3) [.Cwhile [] cond loopBody] s = some s' := by
  -- Cwhile (f+3) → Cif (f+2); cond true → body (loopBody ++ [Cwhile]) at f+1.
  have hsl : bignumExecFuel reg (f + 1) loopBody s = some s_mid := by
    rw [bignumExecFuel_eq_bignumExec_of_straightLine reg f loopBody s loopBody_straightLine]
    exact hbody
  conv_lhs => rw [show f + 3 = (f + 2) + 1 from rfl, bignumExecFuel]
  simp only [List.nil_append, List.append_nil, bignumExecFuel, hcond, bne_iff_ne, ne_eq,
             show ((1 : BitVec 64) ≠ 0) from by decide, not_false_eq_true, if_true]
  -- body = loopBody ++ [Cwhile] at fuel f+1: run loopBody (straight-line)
  -- to `s_mid`, then re-enter the loop (`hrec`).  The Cif continuation
  -- `[] @ f+2` returns the body result verbatim.
  rw [bignumExecFuel_append_join reg (f + 1) loopBody [.Cwhile [] cond loopBody]
        loopBody_nonControl s s_mid s' hsl hrec]

/-- **Loop exit.**  If the loop condition `n != 0` is false, the `Cwhile`
    returns the state unchanged (fuel `f + 3` ≥ 3 suffices: one for the
    `Cwhile`→`Cif` unfold, one for the `Cif`→empty-branch, one for the
    empty body). -/
theorem bignumExecFuel_loop_exit (reg : BignumRegistry) (f : Nat)
    (cond : PExpr) (ca : List InstrR) (s : BignumState)
    (hcond : evalPExpr s cond = some 0) :
    bignumExecFuel reg (f + 3) [.Cwhile [] cond ca] s = some s := by
  conv_lhs => rw [show f + 3 = (f + 2) + 1 from rfl, bignumExecFuel]
  simp only [List.nil_append, List.append_nil, bignumExecFuel, hcond, bne_self_eq_false,
             Bool.false_eq_true, if_false]

/-! ## §9  Loop-guard evaluation, machine-checked

With `BignumExec.evalPExpr` now modeling `Oneq` (`!=`), the emitted
`while (n != 0)` guard evaluates: it is `1` exactly when `n ≠ 0` and `0`
when `n = 0`.  The two lemmas below record this as a checked fact; they
are the per-iteration guard facts the §10 assembly consumes (loop step vs.
loop exit). -/

/-- The emitted loop guard `n != 0` evaluates to `1` when register `n`
    holds a nonzero value (`evalPExpr`'s `Oneq` arm returns
    `if va = vb then 0 else 1`). -/
theorem evalPExpr_loopCond_true (s : BignumState) (hn : s.regs "n" ≠ 0) :
    evalPExpr s (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) = some 1 := by
  rw [pv, evalPExpr]
  simp only [evalPExpr, vr, bind, Option.bind,
    show (BitVec.ofInt 64 0 : BitVec 64) = 0 from rfl]
  rw [if_neg hn]

/-- The emitted loop guard `n != 0` evaluates to `0` when register `n`
    holds `0` — the loop exit condition. -/
theorem evalPExpr_loopCond_false (s : BignumState) (hn : s.regs "n" = 0) :
    evalPExpr s (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) = some 0 := by
  rw [pv, evalPExpr]
  simp only [evalPExpr, vr, bind, Option.bind,
    show (BitVec.ofInt 64 0 : BitVec 64) = 0 from rfl]
  rw [if_pos hn]

/-! ## §10  Assembly: `MpnAddNJasminRefines`

The full bridge.  `body = [cf := 0; Cwhile (n != 0) loopBody]`: the first
instruction zeroes the carry register, then the loop walks the limb arrays.
We prove a loop lemma by induction on `as` (lockstep with `bs`), each step
peeling one limb via `bignumExec_loopBody_step` and `bignumExecFuel_loop_step`,
preserving the unread `ap`/`bp` suffixes across the `op[i]` store with
`load64Mem_store64_disjoint`, and threading the carry via `adcStep`. -/

open CatCrypt.Crypto.Jasmin.MemoryModel

/-- `range (base + 8) (8 * k)` is contained in `range base (8 * (k + 1))`:
    shifting the start by one limb (8 bytes) and dropping a limb of length
    keeps every address inside the larger block. -/
theorem range_shift_subset (base : UInt64) (k : Nat) (a : UInt64)
    (h : range (base + 8) (8 * k) a) : range base (8 * (k + 1)) a := by
  obtain ⟨j, hj, rfl⟩ := h
  refine ⟨8 + j, by omega, ?_⟩
  rw [UInt64.ofNat_add, show (UInt64.ofNat 8 : UInt64) = 8 from rfl]
  ac_rfl

/-- `range base 8` (one limb) is contained in `range base (8 * (k + 1))`. -/
theorem range_head_subset (base : UInt64) (k : Nat) (a : UInt64)
    (h : range base 8 a) : range base (8 * (k + 1)) a := by
  obtain ⟨j, hj, rfl⟩ := h
  exact ⟨j, by omega, rfl⟩

/-- Disjointness is monotone: shrinking either side preserves it. -/
theorem disjoint_mono {A A' B B' : AddrSet}
    (hA : ∀ a, A' a → A a) (hB : ∀ a, B' a → B a)
    (h : MemoryModel.Disjoint A B) : MemoryModel.Disjoint A' B' :=
  fun a ⟨ha, hb⟩ => h a ⟨hA a ha, hB a hb⟩

/-- A `store64` into an 8-byte block disjoint from the whole `8·|ws|`-byte
    limb region preserves `memHoldsLimbs`.  Proved by induction on `ws`:
    the head limb load is framed by `load64Mem_store64_disjoint` (the store
    block vs. the head limb's 8-byte block), and the tail by the IH (the
    store block vs. the tail region, both shrunk from the input
    disjointness). -/
theorem memHoldsLimbs_store64_frame (m : Mem) (base st : UInt64) (v : UInt64)
    (ws : List (BitVec 64))
    (hdisj : MemoryModel.Disjoint (range st 8) (range base (8 * ws.length)))
    (hmem : memHoldsLimbs m base ws) :
    memHoldsLimbs (m.store64 st v) base ws := by
  induction ws generalizing base with
  | nil => exact True.intro
  | cons w ws ih =>
    obtain ⟨hhead, htail⟩ := hmem
    -- Head: the store block `[st, st+8)` is disjoint from `[base, base+8)`.
    have hdisj_head : MemoryModel.Disjoint (range base 8) (range st 8) :=
      MemoryModel.Disjoint.symm (disjoint_mono (fun a h => h)
        (fun a h => range_head_subset base ws.length a h) hdisj)
    refine ⟨?_, ?_⟩
    · rw [load64Mem_store64_disjoint m base st v hdisj_head]
      exact hhead
    · -- Tail: shrink the input disjointness to the tail region `[base+8, …)`.
      have hdisj_tail : MemoryModel.Disjoint (range st 8) (range (base + 8) (8 * ws.length)) :=
        disjoint_mono (fun a h => h)
          (fun a h => range_shift_subset base ws.length a h) hdisj
      exact ih (base + 8) hdisj_tail htail

/-- **Op-buffer self-separation.**  The first limb block `[op, op+8)` is
    disjoint from the remaining limb blocks `[op+8, op+8+8·k)`, provided
    the whole buffer fits in the address space (`8·(k+1) ≤ 2^64`, so no
    wraparound aliases the head onto a later limb).  This is the
    well-formedness condition for the output buffer; it is implied by the
    three regions (`op`, `ap`, `bp`) being disjoint and each `8·(k+1)`
    bytes (so `3·8·(k+1) ≤ 2^64`). -/
theorem range_op_head_tail_disjoint (op : UInt64) (k : Nat)
    (hbound : 8 * (k + 1) ≤ 2 ^ 64) :
    MemoryModel.Disjoint (range op 8) (range (op + 8) (8 * k)) := by
  intro a ⟨⟨i, hi, hai⟩, ⟨j, hj, haj⟩⟩
  -- `a = op + ofNat i` (i < 8) and `a = op + 8 + ofNat j` (j < 8·k).
  -- Rewrite the tail address as `op + ofNat (8 + j)`, then cancel `op`.
  rw [show op + 8 + UInt64.ofNat j = op + UInt64.ofNat (8 + j) from by
        rw [UInt64.ofNat_add, show (UInt64.ofNat 8 : UInt64) = 8 from rfl]; ac_rfl] at haj
  rw [hai] at haj
  have hcancel := uint64_add_left_cancel op _ _ haj
  have h2 := congrArg UInt64.toNat hcancel
  simp only [UInt64.toNat_ofNat'] at h2
  -- `i < 8 ≤ 8 + j`, and both `< 2^64`, so the two `ofNat`s can't be equal.
  omega

/-- **Disjointness bounds the region length.**  Two *nonempty* equal-length
    ranges can only be disjoint if the length fits the address space: a
    length `≥ 2^64` would make each `range` cover all of `UInt64` (every
    address is `base + ofNat k` for some `k < 2^64 ≤ m`), so they could not
    be disjoint.  Hence the op-vs-ap separation hypothesis already implies
    the op buffer does not wrap. -/
theorem disjoint_range_lt (op ap : UInt64) (m : Nat) (hm : 0 < m)
    (h : MemoryModel.Disjoint (range op m) (range ap m)) : m < 2 ^ 64 := by
  by_contra hge
  rw [Nat.not_lt] at hge
  refine h ap ⟨⟨(ap - op).toNat, by have := (ap - op).toNat_lt; omega, ?_⟩,
    ⟨0, by omega, by simp⟩⟩
  rw [UInt64.ofNat_toNat]; bv_decide

/-- `BitVec.ofNat 64 m` round-trips to `m` when `m < 2^64`. -/
theorem ofNat64_toNat (m : Nat) (h : m < 2 ^ 64) :
    (BitVec.ofNat 64 m).toNat = m := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- `BitVec.ofNat 64 (L+1) ≠ 0` when `L + 1 < 2^64` (the loop guard is true
    while limbs remain). -/
theorem ofNat64_succ_ne_zero (L : Nat) (h : L + 1 < 2 ^ 64) :
    (BitVec.ofNat 64 (L + 1) : BitVec 64) ≠ 0 := by
  intro hz
  have ht := ofNat64_toNat (L + 1) h
  rw [hz] at ht
  simp at ht

/-- Decrementing `BitVec.ofNat 64 (L+1)` gives `BitVec.ofNat 64 L`
    (`n -= 1` on the loop counter, no wrap since `L+1 < 2^64`). -/
theorem ofNat64_succ_sub_one (L : Nat) (h : L + 1 < 2 ^ 64) :
    (BitVec.ofNat 64 (L + 1) : BitVec 64) - 1 = BitVec.ofNat 64 L := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat,
    show ((1 : BitVec 64).toNat) = 1 from rfl, Nat.mod_eq_of_lt h]
  omega

/-- **The loop, by induction on the limb list.**  Running the runtime
    `while (n != 0) { loopBody }` from a state whose memory holds `as` at
    `ap`, `bs` at `bp`, carry register encoding `cin`, and `n = |as|`,
    lands (with `2·|as| + 3` fuel) in a state whose memory at the original
    `op` holds `(mpnAddN as bs cin).1`, whose `cf` register holds the
    carry-out, and which agrees with the input memory on every 8-byte
    block disjoint from the `8·|as|`-byte output region.  The op-vs-ap /
    op-vs-bp separations prevent the per-iteration store from corrupting
    unread source limbs (`load64Mem_store64_disjoint`) and pin the output
    buffer inside the address space (`disjoint_range_lt`). -/
theorem mpnAddN_loop :
    ∀ (as bs : List (BitVec 64)) (s : BignumState) (cin : Bool) (extra : Nat),
      as.length = bs.length →
      s.regs "cf" = BitVec.ofNat 64 (if cin then 1 else 0) →
      s.regs "n" = BitVec.ofNat 64 as.length →
      memHoldsLimbs s.mem (regAddr s "ap") as →
      memHoldsLimbs s.mem (regAddr s "bp") bs →
      MemoryModel.Disjoint (range (regAddr s "op") (8 * as.length))
        (range (regAddr s "ap") (8 * as.length)) →
      MemoryModel.Disjoint (range (regAddr s "op") (8 * as.length))
        (range (regAddr s "bp") (8 * as.length)) →
      ∃ s', bignumExecFuel emptyRegistry (2 * as.length + 3 + extra)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBody] s
              = some s' ∧
        memHoldsLimbs s'.mem (regAddr s "op") (mpnAddN as bs cin).1 ∧
        s'.regs "cf" = BitVec.ofNat 64 (carryNat (mpnAddN as bs cin).2) ∧
        (∀ b, MemoryModel.Disjoint (range b 8)
              (range (regAddr s "op") (8 * as.length)) →
            load64Mem s'.mem b = load64Mem s.mem b) := by
  intro as
  induction as with
  | nil =>
    intro bs s cin extra _ hcf hn _ _ _ _
    -- `as = []`: guard false (`n = 0`), loop exits unchanged.
    have hn0 : s.regs "n" = 0 := by simpa using hn
    refine ⟨s, ?_, ?_, ?_, ?_⟩
    · -- fuel `2·0+3+extra = extra+3`; the exit rule needs `_ + 3`.
      have : 2 * ([] : List (BitVec 64)).length + 3 + extra = extra + 3 := by
        simp only [List.length_nil]; omega
      rw [this]
      exact bignumExecFuel_loop_exit emptyRegistry extra _ loopBody s
        (evalPExpr_loopCond_false s hn0)
    · simp [mpnAddN, memHoldsLimbs]
    · simpa [mpnAddN, carryNat] using hcf
    · intro b _; rfl
  | cons a as ih =>
    intro bs s cin extra hlen hcf hn hap hbp hdoa hdob
    -- `bs = b :: bs'` (equal length).
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have hlen' : as.length = bs.length := by simpa using hlen
      -- Length bound from op-vs-ap disjointness: the buffer doesn't wrap.
      have hpos : 0 < 8 * (as.length + 1) := by omega
      have hsize : 8 * (as.length + 1) < 2 ^ 64 := by
        simpa [List.length_cons] using
          disjoint_range_lt (regAddr s "op") (regAddr s "ap")
            (8 * (a :: as).length) (by simp only [List.length_cons]; omega)
            (by simpa using hdoa)
      have hLsucc : as.length + 1 < 2 ^ 64 := by omega
      -- The guard is true: `n = ofNat (L+1) ≠ 0`.
      have hn_ne : s.regs "n" ≠ 0 := by
        rw [hn]; simpa [List.length_cons] using ofNat64_succ_ne_zero as.length hLsucc
      -- Head limb loads from `ap`, `bp`.
      obtain ⟨hap_head, hap_tail⟩ := hap
      obtain ⟨hbp_head, hbp_tail⟩ := hbp
      -- Run one iteration of `loopBody`.
      obtain ⟨s1, hs1, hs1_mem, hs1_cf, hs1_ap, hs1_bp, hs1_op, hs1_n⟩ :=
        bignumExec_loopBody_step s a b cin hcf hap_head hbp_head
      -- Set up the IH hypotheses on the post-iteration state `s1`.
      set op0 : UInt64 := regAddr s "op" with hop0
      -- `regAddr s1 "ap" = regAddr s "ap" + 8`, etc.
      have hra_ap : regAddr s1 "ap" = regAddr s "ap" + 8 := by
        simp only [regAddr, hs1_ap]; exact regAddr_advance _
      have hra_bp : regAddr s1 "bp" = regAddr s "bp" + 8 := by
        simp only [regAddr, hs1_bp]; exact regAddr_advance _
      have hra_op : regAddr s1 "op" = op0 + 8 := by
        simp only [regAddr, hs1_op, hop0]; exact regAddr_advance _
      -- The single op store at `op0`; abbreviate the stored value.
      have hmem1 : s1.mem = s.mem.store64 op0 (UInt64.ofNat (adcStep a b cin).1.toNat) := by
        simpa [hop0, regAddr] using hs1_mem
      -- Frame the tail of `ap`/`bp` across the head store (disjoint blocks).
      -- The store block is `range op0 8`; the tail regions are
      -- `range (regAddr s "ap" + 8) (8·L)` etc., both ⊆ the op-vs-ap region.
      have hdoa_store_aptail :
          MemoryModel.Disjoint (range op0 8) (range (regAddr s "ap" + 8) (8 * as.length)) := by
        refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdoa
        · exact range_head_subset op0 as.length x (by simpa [List.length_cons] using h)
        · exact range_shift_subset (regAddr s "ap") as.length x
            (by simpa [List.length_cons] using h)
      have hdob_store_bptail :
          MemoryModel.Disjoint (range op0 8) (range (regAddr s "bp" + 8) (8 * as.length)) := by
        refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdob
        · exact range_head_subset op0 as.length x (by simpa [List.length_cons] using h)
        · exact range_shift_subset (regAddr s "bp") as.length x
            (by simpa [List.length_cons] using h)
      have hap1 : memHoldsLimbs s1.mem (regAddr s1 "ap") as := by
        rw [hra_ap, hmem1]
        exact memHoldsLimbs_store64_frame s.mem (regAddr s "ap" + 8) op0 _ as
          hdoa_store_aptail hap_tail
      have hbp1 : memHoldsLimbs s1.mem (regAddr s1 "bp") bs := by
        rw [hra_bp, hmem1]
        exact memHoldsLimbs_store64_frame s.mem (regAddr s "bp" + 8) op0 _ bs
          (by rw [hlen'] at hdob_store_bptail; exact hdob_store_bptail) hbp_tail
      -- Disjointness for the IH (tail op-region vs. tail ap/bp-regions).
      have hdoa1 : MemoryModel.Disjoint (range (regAddr s1 "op") (8 * as.length))
          (range (regAddr s1 "ap") (8 * as.length)) := by
        rw [hra_op, hra_ap]
        refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdoa
        · exact range_shift_subset op0 as.length x (by simpa [List.length_cons] using h)
        · exact range_shift_subset (regAddr s "ap") as.length x
            (by simpa [List.length_cons] using h)
      have hdob1 : MemoryModel.Disjoint (range (regAddr s1 "op") (8 * as.length))
          (range (regAddr s1 "bp") (8 * as.length)) := by
        rw [hra_op, hra_bp]
        refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdob
        · exact range_shift_subset op0 as.length x (by simpa [List.length_cons] using h)
        · exact range_shift_subset (regAddr s "bp") as.length x
            (by simpa [List.length_cons] using h)
      -- `cf` register after iteration encodes the head carry-out.
      have hcf1 : s1.regs "cf" = BitVec.ofNat 64 (if (adcStep a b cin).2 then 1 else 0) := by
        rw [hs1_cf]; simp [carryNat]
      -- `n` register after iteration is `ofNat L`.
      have hn1 : s1.regs "n" = BitVec.ofNat 64 as.length := by
        rw [hs1_n, hn]
        simpa [List.length_cons] using ofNat64_succ_sub_one as.length hLsucc
      -- Apply the IH on the tail with carry `(adcStep a b cin).2`.
      obtain ⟨s', hs', hs'_mem, hs'_cf, hs'_frame⟩ :=
        ih bs s1 (adcStep a b cin).2 extra hlen' hcf1 hn1 hap1 hbp1 hdoa1 hdob1
      -- Assemble: one loop step (`bignumExecFuel_loop_step`) + the IH run.
      refine ⟨s', ?_, ?_, ?_, ?_⟩
      · -- Fuel: `2·(L+1)+3+extra = (2·L+2+extra)+3`; step recurses at
        -- `(2·L+2+extra)+1 = 2·L+3+extra`, matching the IH fuel.
        have hfuel : 2 * (a :: as).length + 3 + extra
            = (2 * as.length + 2 + extra) + 3 := by
          simp only [List.length_cons]; ring
        rw [hfuel]
        refine bignumExecFuel_loop_step emptyRegistry (2 * as.length + 2 + extra) _ s s1 s'
          (evalPExpr_loopCond_true s hn_ne) hs1 ?_
        simpa [show 2 * as.length + 2 + extra + 1 = 2 * as.length + 3 + extra
                from by omega] using hs'
      · -- Memory at op: head limb at `op0` (preserved by IH frame), tail by IH.
        rw [hmem1] at hs'_frame
        -- Op-internal separation: `range op0 8` disjoint from `range (op0+8) (8·L)`.
        have hsep : MemoryModel.Disjoint (range op0 8) (range (op0 + 8) (8 * as.length)) :=
          range_op_head_tail_disjoint op0 as.length (by omega)
        refine ⟨?_, ?_⟩
        · -- `load64Mem s'.mem op0 = head_result`, via IH frame + read-back.
          rw [hs'_frame op0 (by rw [hra_op]; exact hsep)]
          -- Now: `load64Mem (s.mem.store64 op0 v) op0 = some (head result)`.
          have hread := load64Mem_store64_same s.mem op0 (UInt64.ofNat (adcStep a b cin).1.toNat)
          rw [hread]
          -- The head of `(mpnAddN (a::as) (b::bs) cin).1` is `(adcStep a b cin).1`.
          rfl
        · -- Tail: `(mpnAddN as bs (adcStep a b cin).2).1`, from IH (op base `op0+8`).
          have hthis := hs'_mem
          rw [hra_op] at hthis
          exact hthis
      · -- Carry-out: the IH's final carry equals the chain carry-out.
        rw [hs'_cf]; simp only [mpnAddN]
      · -- Frame: `b`-block disjoint from `range op0 (8·(L+1))` ⇒ unchanged.
        intro bb hbb
        rw [hmem1] at hs'_frame
        -- `bb` disjoint from the tail op-region (IH frame applies).
        have hbb_tail : MemoryModel.Disjoint (range bb 8)
            (range (regAddr s1 "op") (8 * as.length)) := by
          rw [hra_op]
          refine disjoint_mono (fun x h => h) (fun x h => ?_) hbb
          exact range_shift_subset (regAddr s "op") as.length x
            (by simpa [List.length_cons] using h)
        rw [hs'_frame bb hbb_tail]
        -- `bb` disjoint from the head store block ⇒ store64 frame.
        have hbb_head : MemoryModel.Disjoint (range bb 8) (range (regAddr s "op") 8) := by
          refine disjoint_mono (fun x h => h) (fun x h => ?_) hbb
          exact range_head_subset (regAddr s "op") as.length x
            (by simpa [List.length_cons] using h)
        rw [load64Mem_store64_disjoint s.mem bb (regAddr s "op") _ hbb_head]

/-- **The bridge, fully proved.**  `mpnAddNFd.body` (the emitted
    `cf := 0; while (n != 0) { loopBody }`) refines the pure reference
    `mpnAddN` over byte memory: starting from a state holding `as` at `ap`,
    `bs` at `bp`, with `n = |as|`, it lands in a state whose memory at `op`
    holds `(mpnAddN as bs false).1` and whose `cf` register holds the
    carry-out.  The `cf := 0` prelude makes the first iteration's
    `#ADC_64(_, _, cf)` a plain add (carry-in `false`); the loop is then
    `mpnAddN_loop`.  The op-vs-ap / op-vs-bp separations keep the
    per-iteration store from clobbering unread source limbs. -/
theorem MpnAddNJasminRefines : MpnAddNRefinesStmt := by
  intro s as bs fuel hlen hn hap hbp hdoa hdob hfuel
  -- Step 1: the `cf := 0` prelude.  `evalPExpr s (Pconst 0) = 0`, so
  -- `execInstr s (Cassgn cf 0) = some (setReg s "cf" 0)`; this leaves
  -- memory and the `ap`/`bp`/`op`/`n` registers untouched.
  set s0 : BignumState := setReg s "cf" 0 with hs0
  have hexec0 : execInstr s
      (.Cassgn (.Lvar { var := vr "cf" }) .AT_none (.sword .U64) (.Pconst 0))
      = some s0 := by
    simp only [execInstr, evalPExpr, vr, bind, Option.bind, hs0,
      show (BitVec.ofInt 64 0 : BitVec 64) = 0 from rfl]
  -- The prelude does not decrement fuel (straight-line catch-all arm),
  -- so `body` at `fuel` runs to the loop at `fuel` on `s0`.
  -- Registers/memory carried over to `s0`:
  have hmem0 : s0.mem = s.mem := by rw [hs0]; rfl
  have hcf0 : s0.regs "cf" = BitVec.ofNat 64 (if false then 1 else 0) := by
    rw [hs0]; simp [setReg]
  have hreg0 : ∀ x, x ≠ "cf" → s0.regs x = s.regs x := by
    intro x hx; rw [hs0]; simp [setReg, hx]
  have hra0 : ∀ x, x ≠ "cf" → regAddr s0 x = regAddr s x := by
    intro x hx; simp only [regAddr, hreg0 x hx]
  -- Transfer the loop preconditions from `s` to `s0`.
  have hn0' : s0.regs "n" = BitVec.ofNat 64 as.length := by
    rw [hreg0 "n" (by decide), hn]
  have hap0 : memHoldsLimbs s0.mem (regAddr s0 "ap") as := by
    rw [hmem0, hra0 "ap" (by decide)]; exact hap
  have hbp0 : memHoldsLimbs s0.mem (regAddr s0 "bp") bs := by
    rw [hmem0, hra0 "bp" (by decide)]; exact hbp
  have hdoa0 : MemoryModel.Disjoint (range (regAddr s0 "op") (8 * as.length))
      (range (regAddr s0 "ap") (8 * as.length)) := by
    rw [hra0 "op" (by decide), hra0 "ap" (by decide)]; exact hdoa
  have hdob0 : MemoryModel.Disjoint (range (regAddr s0 "op") (8 * as.length))
      (range (regAddr s0 "bp") (8 * as.length)) := by
    rw [hra0 "op" (by decide), hra0 "bp" (by decide)]; exact hdob
  -- Extra fuel beyond the loop's `2·|as| + 3` requirement.
  obtain ⟨extra, hextra⟩ : ∃ extra, fuel = 2 * as.length + 3 + extra :=
    ⟨fuel - (2 * as.length + 3), by omega⟩
  -- Step 2: run the loop on `s0`.
  obtain ⟨s', hs', hs'_mem, hs'_cf, _⟩ :=
    mpnAddN_loop as bs s0 false extra hlen hcf0 hn0' hap0 hbp0 hdoa0 hdob0
  refine ⟨s', ?_, ?_, ?_⟩
  · -- Connect `body` at `fuel` to the loop run on `s0`.  The prelude
    -- `cf := 0` runs via the straight-line catch-all arm (no fuel drop),
    -- so `body` at `fuel` equals the loop `[Cwhile…]` at `fuel` on `s0`.
    obtain ⟨F, hF⟩ : ∃ F, fuel = F + 1 := ⟨fuel - 1, by omega⟩
    have hbody : bignumExecFuel emptyRegistry (F + 1) body s
        = bignumExecFuel emptyRegistry (F + 1)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBody] s0 := by
      -- Both sides unfold the `Cwhile` one iteration into a `Cif`; after the
      -- prelude `Cassgn cf 0` runs to `s0` (`hexec0`), the two coincide.
      conv_lhs => rw [body]
      simp only [bignumExecFuel, hexec0]
    rw [hF, hbody, show F + 1 = 2 * as.length + 3 + extra from by omega]
    exact hs'
  · -- Memory at op holds the result; `regAddr s0 "op" = regAddr s "op"`.
    rw [hra0 "op" (by decide)] at hs'_mem
    exact hs'_mem
  · -- Carry-out register.
    exact hs'_cf

/-! ## §11  Stride-parametric generic helpers (additive)

The U64 plumbing above is hard-coded to byte stride `8`.  The lemmas below
**parameterize** the load-bearing pieces by `stride : Nat`, so the U32
mirror at stride `4` (and any future wider/narrower limb) can reuse them
without duplicating the proofs.  Each U64 lemma above is recoverable as a
trivial corollary at `stride = 8`.

These additions are deliberately *additive*: every existing name keeps
its original signature and proof, so all downstream consumers
(`MpnAddOpenCarryPrototype`, `MpnSubPrototype`, the `*_1` family, …)
remain build-clean.  -/

/-- **Stride-parametric pointer advance.**  Generic version of
    `regAddr_advance`: adding `stride : Nat` (as a numeral, lifted into
    both `BitVec 64` and `UInt64`) commutes with the
    `UInt64.ofNat _.toNat` decode.  Both reductions are `mod 2^64`. -/
theorem regAddr_advance_at (bv : BitVec 64) (stride : Nat) :
    UInt64.ofNat (bv + BitVec.ofNat 64 stride).toNat
      = UInt64.ofNat bv.toNat + UInt64.ofNat stride := by
  apply UInt64.toNat.inj
  simp only [UInt64.toNat_ofNat', UInt64.toNat_add, BitVec.toNat_add,
             BitVec.toNat_ofNat]
  omega

/-- **Op-buffer self-separation, stride-parametric.**  Mirror of
    `range_op_head_tail_disjoint` at arbitrary byte stride `s`: the
    first limb block `[op, op + s)` is disjoint from the remaining
    `[op + s, op + s + s·k)` blocks, provided `s · (k + 1) ≤ 2^64`
    (no wraparound). -/
theorem range_op_head_tail_disjoint_at (op : UInt64) (k : Nat) (s : Nat)
    (hbound : s * (k + 1) ≤ 2 ^ 64) :
    MemoryModel.Disjoint (range op s) (range (op + UInt64.ofNat s) (s * k)) := by
  intro a ⟨⟨i, hi, hai⟩, ⟨j, hj, haj⟩⟩
  -- `a = op + ofNat i` (i < s) and `a = op + ofNat s + ofNat j` (j < s·k).
  -- Rewrite the tail address as `op + ofNat (s + j)`, then cancel `op`.
  rw [show op + UInt64.ofNat s + UInt64.ofNat j = op + UInt64.ofNat (s + j) from by
        rw [UInt64.ofNat_add]; ac_rfl] at haj
  rw [hai] at haj
  have hcancel := uint64_add_left_cancel op _ _ haj
  have h2 := congrArg UInt64.toNat hcancel
  simp only [UInt64.toNat_ofNat'] at h2
  -- `i < s · (k + 1) = s + s · k ≤ 2^64`, and `s + j < s + s · k ≤ 2^64`.
  -- So both `ofNat _` round-trips drop the `mod`, giving `i = s + j` which
  -- contradicts `i < s ≤ s + j`.
  have hi' : i < 2 ^ 64 := by
    have : s ≤ s * (k + 1) := Nat.le_mul_of_pos_right s (by omega)
    omega
  have hsj : s + j < 2 ^ 64 := by
    have : s + j < s * (k + 1) := by
      rw [Nat.mul_succ]; omega
    omega
  rw [Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hsj] at h2
  omega

/-- **Stride-4 specialization.**  Op-buffer self-separation at the U32
    stride; consumed by the U32 add_n loop induction. -/
theorem range_op_head_tail_disjoint_4 (op : UInt64) (k : Nat)
    (hbound : 4 * (k + 1) ≤ 2 ^ 64) :
    MemoryModel.Disjoint (range op 4) (range (op + 4) (4 * k)) := by
  have h := range_op_head_tail_disjoint_at op k 4 hbound
  simpa [show (UInt64.ofNat 4 : UInt64) = 4 from rfl] using h

/-- **Generic `Cwhile` step rule (additive).**  Forward one-iteration
    rule paramertized by the loop body: needs only the body's
    straight-line + non-control witnesses, which both
    `MpnAddPrototype.loopBody` and `MpnAddOpenCarryPrototype.loopBody`
    (and any other straight-line body) supply.  The U64 file's
    `bignumExecFuel_loop_step` is a 1-line corollary; the U32 body in
    `MpnAdd32Refines` reuses this verbatim with its own
    `loopBody32_straightLine` / `loopBody32_nonControl`. -/
theorem bignumExecFuel_loop_step_generic (reg : BignumRegistry) (f : Nat)
    (cond : PExpr) (body : List InstrR)
    (hsl : InstrR.bodyIsStraightLine body)
    (hnc : ∀ i ∈ body, i.isNonControl)
    (s s_mid s' : BignumState)
    (hcond : evalPExpr s cond = some 1)
    (hbody : bignumExec body s = some s_mid)
    (hrec : bignumExecFuel reg (f + 1) [.Cwhile [] cond body] s_mid = some s') :
    bignumExecFuel reg (f + 3) [.Cwhile [] cond body] s = some s' := by
  have hsl' : bignumExecFuel reg (f + 1) body s = some s_mid := by
    rw [bignumExecFuel_eq_bignumExec_of_straightLine reg f body s hsl]
    exact hbody
  conv_lhs => rw [show f + 3 = (f + 2) + 1 from rfl, bignumExecFuel]
  simp only [List.nil_append, List.append_nil, bignumExecFuel, hcond, bne_iff_ne, ne_eq,
    show ((1 : BitVec 64) ≠ 0) from by decide, not_false_eq_true, if_true]
  rw [bignumExecFuel_append_join reg (f + 1) body [.Cwhile [] cond body]
        hnc s s_mid s' hsl' hrec]

/-- **Generic `Cwhile` exit rule (additive).**  Loop-exit rule
    parameterized by the body — same as `bignumExecFuel_loop_exit` but
    works for any `body : List InstrR`.  Trivial generalization (the
    proof never inspects the body shape). -/
theorem bignumExecFuel_loop_exit_generic (reg : BignumRegistry) (f : Nat)
    (cond : PExpr) (ca : List InstrR) (s : BignumState)
    (hcond : evalPExpr s cond = some 0) :
    bignumExecFuel reg (f + 3) [.Cwhile [] cond ca] s = some s := by
  conv_lhs => rw [show f + 3 = (f + 2) + 1 from rfl, bignumExecFuel]
  simp only [List.nil_append, List.append_nil, bignumExecFuel, hcond, bne_self_eq_false,
    Bool.false_eq_true, if_false]

/-- The `loopCond_true` guard at register `n` — works for any U64
    register name (the `Oneq U64` arm is width-independent).  Used by
    the U32 bridge with its own (still-U64) `n` register. -/
theorem evalPExpr_neq_zero_true (s : BignumState) (e : PExpr) (v : BitVec 64)
    (hv : evalPExpr s e = some v) (hne : v ≠ 0) :
    evalPExpr s (.Papp2 (.Oneq .U64) e (.Pconst 0)) = some 1 := by
  simp only [evalPExpr, hv, bind, Option.bind,
    show (BitVec.ofInt 64 0 : BitVec 64) = 0 from rfl]
  rw [if_neg hne]

/-- Companion to `evalPExpr_neq_zero_true`: the loop exits when the
    register reads `0`. -/
theorem evalPExpr_neq_zero_false (s : BignumState) (e : PExpr)
    (hv : evalPExpr s e = some 0) :
    evalPExpr s (.Papp2 (.Oneq .U64) e (.Pconst 0)) = some 0 := by
  simp only [evalPExpr, hv, bind, Option.bind,
    show (BitVec.ofInt 64 0 : BitVec 64) = 0 from rfl, if_true]

/-- **U32 store-memory projection lemmas (additive).**  Mirror of
    `storeMem_mem` / `storeMem_regs` for the U32 store; allows the U32
    per-iteration simp script to push `regAddr` through intermediate
    `storeMem32`-bearing states the same way the U64 script does.  -/
@[simp] theorem storeMem32_mem_proj (s : BignumState) (addr v : UInt64) :
    (storeMem32 s addr v).mem = Mem.store32 s.mem addr v := rfl

@[simp] theorem storeMem32_regs_proj (s : BignumState) (addr v : UInt64) :
    (storeMem32 s addr v).regs = s.regs := rfl

end CatCrypt.Crypto.Jasmin.Examples.MpnAddPrototype
