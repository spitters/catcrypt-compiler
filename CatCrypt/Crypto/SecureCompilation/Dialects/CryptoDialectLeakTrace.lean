/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect

/-!
# Dialect-level leakage / constant-time trace for `catCryptDialect`

This file carries the leakage / constant-time *security view* directly on the
crypto dialect. It defines the observable `LeakEvent`/`LeakTrace` model and the
per-op and per-program leak functions on `catCryptDialect`.

## What is defined

* `LeakEvent` / `LeakTrace` — the observable leakage model: an event is either a
  pure op (carrying the op name) or a sampling op, and a trace is the ordered
  list of events. In the constant-time model an adversary observes WHICH
  operations execute (and in what order), but not the VALUES processed.
* `CatCryptOp.leakEvent` — the observable `LeakEvent` of a single dialect op:
  every pure bv/bit/pair op leaks its op name, the sample ops leak `sampleOp`,
  `extCall name` leaks `pureOp ("extCall:" ++ name)`. The branch op `.ite` leaks
  `pureOp "ite"` — in the dialect semantics `ite` is a *value-select* (both arms
  evaluated unconditionally), so it leaks only its op identity, never the
  condition's value. Memref ops carry a **static** `Fin n` index, so the memory
  address is a compile-time constant and leaks no data-dependent observation —
  the memory axis is trivially constant-time in this dialect.
* `Expr.leakEvent` — the leak event of a dialect `Expr` (just its op's event).
* `Com.leakTrace` — the dialect-level leak trace, recursing over the ANF
  `Com.ret`/`Com.var` structure: `.ret` leaks `[]`, `.var e body` leaks
  `e.leakEvent :: body.leakTrace`. The trace is a plain `List LeakEvent` that
  depends only on the program structure (there is no data-dependent branching),
  so it is the same list for every input.

The native constant-time input-independence statements built on this leak trace
are `CryptoDialectCTLeak.catCT` and `catLevelCheck_sound`.

**0 axioms**; all goals closed.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakTrace

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect

/-! ## 0. Leakage events and traces -/

/-- Observable leakage events during program execution.

    In the constant-time model, an adversary can observe WHICH operations
    execute (and in what order), but not the VALUES processed. -/
inductive LeakEvent where
  /-- A pure operation was executed. -/
  | pureOp (name : String)
  /-- A sampling operation was executed. -/
  | sampleOp
  deriving DecidableEq, Repr

/-- Leakage trace: sequence of observable events during execution. -/
abbrev LeakTrace := List LeakEvent

/-! ## 1. Op-level leak event -/

/-- The observable leakage event of a single `catCryptDialect` op.

    Pure bv/bit/pair ops leak their op name, samples leak `sampleOp`, and
    `extCall name` leaks `pureOp ("extCall:" ++ name)`. The branch op `.ite`
    leaks only `pureOp "ite"` (value-select: it never observes the condition's
    value); static-index memref ops leak only their op identity (the address is a
    compile-time constant). -/
def CatCryptOp.leakEvent : CatCryptOp → LeakEvent
  | .constBit _ => .pureOp "constBit"
  | .constUnit => .pureOp "constUnit"
  | .xor => .pureOp "xor"
  | .and => .pureOp "and"
  | .or => .pureOp "or"
  | .not => .pureOp "not"
  | .eqBit => .pureOp "eqBit"
  | .mkPair _ _ => .pureOp "mkPair"
  | .fst _ _ => .pureOp "fst"
  | .snd _ _ => .pureOp "snd"
  | .inl _ _ => .pureOp "inl"
  | .inr _ _ => .pureOp "inr"
  | .bvConst _ _ => .pureOp "bvConst"
  | .bvXor _ => .pureOp "bvXor"
  | .bvAnd _ => .pureOp "bvAnd"
  | .bvOr _ => .pureOp "bvOr"
  | .bvNot _ => .pureOp "bvNot"
  | .bvAdd _ => .pureOp "bvAdd"
  | .bvSub _ => .pureOp "bvSub"
  | .bvMul _ => .pureOp "bvMul"
  | .bvEq _ => .pureOp "bvEq"
  | .bvShiftL _ _ => .pureOp "bvShiftL"
  | .bvShiftR _ _ => .pureOp "bvShiftR"
  | .bvRor _ _ => .pureOp "bvRor"
  | .bvRol _ _ => .pureOp "bvRol"
  | .bvShiftRA _ _ => .pureOp "bvShiftRA"
  | .andn _ => .pureOp "andn"
  | .bvShiftLV _ => .pureOp "bvShiftLV"
  | .bvShiftRV _ => .pureOp "bvShiftRV"
  | .bvAdd64 _ => .pureOp "bvAdd64"
  | .bvAdc _ => .pureOp "bvAdc"
  | .bvMulHi _ => .pureOp "bvMulHi"
  | .bvAddCarryLo _ => .pureOp "bvAddCarryLo"
  | .bvAddCarryHi _ => .pureOp "bvAddCarryHi"
  | .ite _ => .pureOp "ite"
  | .bitToSword _ => .pureOp "bitToSword"
  | .memrefZero _ => .pureOp "memrefZero"
  | .memrefSet _ _ => .pureOp "memrefSet"
  | .memrefGet _ _ => .pureOp "memrefGet"
  -- Dynamic-index memref ops: this trace is input-INDEPENDENT, so they emit only
  -- a structural op-identity event. Their data-dependent address leak (the runtime
  -- index is observable) is captured by `CTPredicate.ctSafe = false` for these ops,
  -- NOT by this static trace.
  | .memrefSetDyn _ => .pureOp "memrefSetDyn"
  | .memrefGetDyn _ => .pureOp "memrefGetDyn"
  | .memrefGetDyn128 _ => .pureOp "memrefGetDyn128"
  | .memrefWSetDyn _ _ => .pureOp "memrefWSetDyn"
  | .memrefWGetDyn _ _ => .pureOp "memrefWGetDyn"
  | .extCall name _ _ => .pureOp ("extCall:" ++ name)
  | .sampleBit => .sampleOp
  | .sampleBv _ => .sampleOp
  -- 128-bit SIMD ops: data-oblivious (fixed lane pattern, no data-dependent
  -- address or branch), so — like every other pure op — the input-independent
  -- trace emits only a structural op-identity event.
  | .vsimd _ => .pureOp "vsimd"
  | .vconst128 _ => .pureOp "vconst128"
  | .vpshufdC _ => .pureOp "vpshufdC"
  | .vaeskeygenC _ => .pureOp "vaeskeygenC"
  | .vpsrldqC _ => .pureOp "vpsrldqC"
  | .vpslldqC _ => .pureOp "vpslldqC"
  | .vsha256rnds2 => .pureOp "vsha256rnds2"
  | .vsha256msg1 => .pureOp "vsha256msg1"
  | .vsha256msg2 => .pureOp "vsha256msg2"

/-- The leakage event of a dialect `Expr` is the event of its op. -/
def Expr.leakEvent {Γ : Ctx} {t : CryptoTy} (e : Expr catCryptDialect Γ t) :
    LeakEvent :=
  CatCryptOp.leakEvent e.op

/-! ## 2. Program-level leak trace -/

/-- Dialect-level static leakage trace of a `Com catCryptDialect`: the ordered
    sequence of observable events emitted by the ANF body.

    A `Com.ret` leaks nothing (`[]`), and a `Com.var e body` leaks `e`'s event
    followed by `body`'s trace. This depends only on the program structure (there
    is no data-dependent branching), so it is the same list for every input. -/
def Com.leakTrace {Γ : Ctx} {t : CryptoTy} :
    Com catCryptDialect Γ t → LeakTrace
  | .ret _ => []
  | .var e body => Expr.leakEvent e :: Com.leakTrace body

end CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakTrace
