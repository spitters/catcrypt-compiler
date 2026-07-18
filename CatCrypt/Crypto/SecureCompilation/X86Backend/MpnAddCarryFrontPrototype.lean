/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-!
# Width-`N` `mpn_add_n` with-carry FRONT feasibility prototype (task #20)

Feasibility prototype: a runtime-`N` GMP-ABI `mpn_add_n` (`res[i] = a[i] + b[i]
+ carry`, carry threaded across iterations) FRONT-COMPILED via
`TranslateDialectRuntimeLoop.rolledForLoopNRt`, using **only** the existing
`SExpr` alphabet — **no new reg-1 carry dialect op**.

The point of the prototype is to show that the loop-carried carry bit needs no
`CF`-native / `addCarryLo`/`addCarryHi` dialect op: it rides the loop-carried
`.sword 64` accumulator, and the per-limb carry-out is recovered by the
HW-faithful half-add split

```
  carry(x + y) = ((x >> 1) + (y >> 1) + ((x & y) & 1)) >> 63
```

which uses only `SShr` / `SAdd` / `SAnd` — the same word-split carry idiom the
deployed `Secp256k1FeMulFront` (FieldWidenMulCurve) and `Poly1305OwnedCom`
(`carryStmts`) fronts already use. All shifts stay within word width, so the
expression lowers faithfully (unlike `>> 64`, which the unbounded-`Nat` `SExpr`
model would permit but a 64-bit register cannot realise). A three-input
`a + b + cin` is two half-add stages; the two stage carries are mutually
exclusive, so their OR is an `SAdd` (dodging the absent `SOr`/`SNot` — the
`SExpr` alphabet has only `SAnd`/`SXor`).

`mpn_sub_n` is structurally identical (the FieldWidenMulCurve sub-borrow: `SSub`
with a `+2^64` bias to avoid `SSub`'s saturation, borrow read off the high split
or via `SLt`).

## Scope / honest status

* This is a **feasibility prototype**: it establishes that the covered
  carry-threading body front-compiles (`rolledForLoopNRt` returns `some`,
  `addRtProg_isSome`), wrapping into a genuine `ComL.forLoopNRt` (one body copy,
  `jne` back-edge, counter seeded from the runtime `n` register). It does NOT yet
  wire the owned `.s` emission or the external `libgmp` byte-KAT — that flip
  (re-sourcing `MpnLoopOwnedEmit`'s hand-authored `addLoopBody`/`subLoopBody`
  through this front) is the follow-up.
* **Carry-in seed ABI wrinkle** (plumbing, not a front gap): `rolledForLoopNRt`
  needs `init` to be an in-scope `Ctxt.Var` of `mapTy accCTy = .reg 64`. GMP's
  `mpn_add_n(rp, ap, bp, n)` has no carry-in argument, so this prototype adds a
  trailing `cy0` register (the C KAT harness would pass `0`). A production flip
  can instead seed the accumulator from a `MOV acc, #0` prologue variant.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddCarryFrontPrototype

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)

/-- Local sequencing helper: fold a `List LowCT` into a right-nested `RSeq`. -/
def seqAll : List LowCT → LowCT
  | [] => .RSkip
  | [c] => c
  | c :: cs => .RSeq c (seqAll cs)

abbrev r64 : JasminTy := .reg 64

/-- The limb count `N` for this prototype instance (any concrete width works; the
    rendered SIB loads are byte-offset so the front is size-agnostic). -/
abbrev N : Nat := 4

/-- The `N`-limb GMP operand array type. -/
abbrev AN : JasminTy := .stackArr 64 N

/-- `2^64 - 1` low-word mask. -/
def mask64 : Nat := 18446744073709551615

/-- Half-add carry-out of `x + y` (both `< 2^64`) as a HW-faithful 64-bit
    expression `((x>>1)+(y>>1)+((x&y)&1))>>63`. Uses only `SShr`/`SAdd`/`SAnd`;
    the largest intermediate is `2^64 - 1`, so no in-register overflow occurs. -/
def halfCarry (x y : String) : SExpr :=
  .SShr
    (.SAdd (.SAdd (.SShr (.SVar x) (.SLit 1)) (.SShr (.SVar y) (.SLit 1)))
           (.SAnd (.SAnd (.SVar x) (.SVar y)) (.SLit 1)))
    (.SLit 63)

/-- The per-limb `mpn_add_n` body over the runtime loop index `idx`, threading the
    carry `cy`. Loads `a[idx]`, `b[idx]`; adds in two half-add stages (`a+b`, then
    `+cy`), each recovering its carry-out via `halfCarry`; stores the low word to
    `out[idx]`; the new carry is `c1 + c2` (mutually exclusive, so `+` = OR).
    The accumulator name returned by the front epilogue is `cy`. -/
def addBodyLowCT : LowCT := seqAll (
  [ .RScalarSetExpr "ix" (.SVar "idx")
  , .RArrLoad ⟨"ai", .TU64⟩ ⟨"a", .TBytes (8 * N)⟩ "ix"
  , .RArrLoad ⟨"bi", .TU64⟩ ⟨"b", .TBytes (8 * N)⟩ "ix"
  -- stage 1: t1 = ai + bi ; c1 = carry(ai, bi) ; s1 = low word of t1
  , .RScalarSetExpr "c1" (halfCarry "ai" "bi")
  , .RScalarSetExpr "s1" (.SAnd (.SAdd (.SVar "ai") (.SVar "bi")) (.SLit mask64))
  -- stage 2: sum = s1 + cy ; c2 = carry(s1, cy) ; store low word
  , .RScalarSetExpr "c2" (halfCarry "s1" "cy")
  , .RScalarSetExpr "sum" (.SAnd (.SAdd (.SVar "s1") (.SVar "cy")) (.SLit mask64))
  , .RArrStore ⟨"out", .TBytes (8 * N)⟩ "ix" ⟨"sum", .TU64⟩
  -- new carry = c1 + c2 (the two stage carries never both fire)
  , .RScalarSetExpr "cy" (.SAdd (.SVar "c1") (.SVar "c2")) ])

/-- Body context: carry accumulator (`.sword 64`), loop index (`.sword 64`), then
    the three memref invariants `a` / `b` / `out`. -/
def Γbody : Ctx := [.sword 64, .sword 64, .memref N, .memref N, .memref N]

/-- The body `VarMap`, bound deepest-first: `out`, `b`, `a`, `idx`, `cy`. -/
def vmBody : VarMap Γbody :=
  (((((VarMap.empty.bind (t := .memref N) "out").bind
      (t := .memref N) "b").bind
      (t := .memref N) "a").bind
      (t := .sword 64) "idx").bind
      (t := .sword 64) "cy")

/-- Outer argument context (newest-first): `n` (runtime trip count), `a`, `b`,
    `out`, `cy0` (the carry-in seed register — see the ABI note in the module
    docstring). -/
def Γouter : Ctxt jasminDialect := [r64, AN, AN, AN, r64]

/-- The front-compiled runtime-trip `mpn_add_n` loop, or `none` if the front
    declines. `count = n` (`.here`), `init = cy0` (deepest), `invs = [a, b, out]`. -/
def addRtProgOpt : Option (ComL Γouter (mapTy (.sword 64))) :=
  rolledForLoopNRt (Γouter := Γouter) (accCTy := .sword 64)
    (invCTys := [.memref N, .memref N, .memref N])
    vmBody "cy" addBodyLowCT
    (count := .here)
    (init := .there (.there (.there (.there .here))))
    (invs := .cons (.there .here) (.cons (.there (.there .here))
              (.cons (.there (.there (.there .here))) .nil)))

/-- **Feasibility keystone:** the runtime-loop front ACCEPTS the covered
    carry-threading `mpn_add_n` body — `rolledForLoopNRt` returns `some`, wrapping
    it in a genuine `ComL.forLoopNRt` (one body copy + `jne` back-edge, counter
    seeded from the runtime `n` register). The loop-carried carry rides the
    `.sword 64` accumulator; no reg-1 carry dialect op is used. -/
theorem addRtProg_isSome : addRtProgOpt.isSome := by native_decide

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddCarryFrontPrototype
