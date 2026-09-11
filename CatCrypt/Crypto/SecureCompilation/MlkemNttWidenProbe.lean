/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-!
# ML-KEM forward-NTT slot widening: the spilling-RA probe (N = 8 → wider)

`MlkemNttFieldEmit.lean` authors the byte-correct word blocks for the ML-KEM
forward NTT (`q = 3329`) and names one residual: *"N = 256 (the slot/RA
widening), the register-allocation layer, not the arithmetic."* The
`Poseidon2WholePermCom` `BState` builder it shares is a **`Fin 25`-slot** machine
(16 Baby Bear lanes + 9 scratch). 256 ML-KEM coefficients do not fit 25 slots,
so a larger-N word Com must spill.

This file establishes the precise mechanism by which the widening works, with a
small concrete probe — **without** touching the N = 8 result.

## The mechanism (the answer to "where does spilling live")

The `Fin 25` cap is an artifact of the **`BState` authoring builder**
(`Poseidon2WholePermCom.BState.cur : Fin 25 → Ctxt.Var Γ r64`), not of the
lowering. The lowering `JasminLprogExport.Com.toLprogPhysAbi` runs its **own**
Poletto–Sarkar linear scan over a **`Nat`-indexed** slot universe
(`physUniverse`, `physScanStep`, `physMap`) and **already spills**: any logical
slot whose linear-scan physical index lands `≥ numGPRegs` (13) is rendered by
`physRegName` as a stack cell `k.{phys-13}` (a red-zone spill the reader
materialises as an `RSP`-relative reference). Spilling is therefore **built into
`toLprogPhysAbi`**, decoupled from how many slots the *authoring* builder used.

So the widening gap is **authoring-ergonomics**, not missing RA integration:
* the lowering accepts and spills a Com with an arbitrarily large live set;
* the only thing tied to `Fin 25` is the Poseidon2-specific `BState` builder.

## The probe

`probeWideCom` is a straight-line `Com jasminDialect` over **16** `r64` inputs
that keeps all 16 inputs live to the very end (each output reads input `i` and
its mirror `15 - i`), so the SSA slot universe far exceeds the 13 GP registers.
Built directly from the generic `Com` constructors with the ML-KEM word ops
(`add`/`sub`/`mul`), it bypasses the `Fin 25` `BState` entirely. We then read off
the lowering's allocation and show:

* `probeWide_universe_gt_pool` — the slot universe exceeds the 13-register pool
  (so a non-spilling allocator would overflow);
* `probeWide_spills` — `toLprogPhysAbi`'s linear scan assigns at least one slot a
  **spill cell** `k.N` (the lowering genuinely spills here), the capability a
  `Fin 25`-bounded author never exercised but ML-KEM N = 256 needs.

This is a register-allocation probe: it does **not** claim a byte-correct
NTT-16; it demonstrates that the existing lowering RA accepts and spills a
>13-live word Com, which is the residual `MlkemNttFieldEmit.lean` named. The
byte-correct widening would author the butterfly chain over the same constructors
with the proven `mkMulW`/`mkAddW`/`mkSubW` word blocks (see "Next steps").
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.MlkemNttWidenProbe

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-- The jasmin word type. -/
abbrev r64 : JasminTy := JasminTy.reg 64

/-- The input context: 16 `r64` words (the ML-KEM "wide" lane set the `Fin 25`
    `BState` cannot hold alongside its scratch). -/
abbrev wideCtxt : Ctxt jasminDialect := List.replicate 16 r64

/-- De Bruijn variable for input word `i` of a `replicate (m+1) r64` context
    (mirrors `Poseidon2WholePermCom.inputVar`). -/
def inputVar : (m : Nat) → Nat →
    @Ctxt.Var jasminDialect (List.replicate (m + 1) r64) r64
  | _, 0 => .here
  | 0, _ => .here
  | (m + 1), (j + 1) => (inputVar m j).there

/-- Input word `i` of `wideCtxt`. -/
def inVar (i : Nat) : Ctxt.Var wideCtxt r64 := inputVar 15 i

/-! ### A `Fin 16`-slot CPS builder (the `BState` pattern at a free slot count)

This mirrors `Poseidon2WholePermCom.BState`/`emitBin` exactly, except the slot
map is `Fin 16 → Var Γ r64` rather than `Fin 25`. This is the load-bearing
observation: the slot count of the *authoring* builder is a free parameter — the
`Fin 25` in `Poseidon2WholePermCom` is a Poseidon2 sizing choice, not a lowering
constraint. A 16-slot machine (or any `Fin n`) threads through the same way. -/

/-- The builder state (the wide-NTT analogue of `Poseidon2WholePermCom.BState`)
    at **32 slots**: lanes `0 … 15` are the inputs, `16 … 31` are result lanes.
    The 32 here, like Poseidon2's `Fin 25`, is a free *authoring* parameter. -/
structure WState (Γ : Ctxt jasminDialect) where
  /-- Current SSA variable for each of the 32 slots. -/
  cur : Fin 32 → Ctxt.Var Γ r64

/-- A continuation over an arbitrary extended context (the CPS body). -/
abbrev WCont (t : JasminTy) :=
  {Γ' : Ctxt jasminDialect} → WState Γ' → Com jasminDialect Γ' t

/-- One `regArith op 64` binding writing slot `dst` from slots `a`, `b`, then
    continue with `k` over the extended context (slot `dst` rebound to the fresh
    head var, every other slot shifted by `.there`). Identical shape to
    `Poseidon2WholePermCom.emitBin`, at `Fin 32`. -/
def emitBin32 {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : WState Γ) (op : JasminBinOp) (dst a b : Fin 32) (k : WCont t) :
    Com jasminDialect Γ t :=
  let e : Expr jasminDialect Γ r64 :=
    { op := .regArith op 64, retTy_eq := rfl, args := .cons (st.cur a) (.cons (st.cur b) .nil) }
  let st' : WState (r64 :: Γ) :=
    { cur := fun i => if i = dst then (.here) else (st.cur i).there }
  .var e (k st')

/-- The initial state: slots `0 … 15` ↦ input words `0 … 15`; the result slots
    `16 … 31` are seeded at input 0 (overwritten before any read). -/
def initWState : WState wideCtxt where
  cur := fun i => if i.val < 16 then inVar i.val else inVar 0

/-- **The wide probe Com.** Sixteen `r64` inputs in slots `0 … 15`; the body
    writes 16 result slots `16 … 31`, **each reading two of the original inputs**
    and writing a fresh slot, so all 16 inputs stay live until result slot `31`'s
    binding (it reads input `15`). At the binding of slot `31` the live set is the
    16 inputs plus the 16 partial results — far past the 13-register pool, forcing
    the lowering's linear scan to spill. Returns slot `16`.

    Built from the `Fin 32` builder (no `Fin 25` `BState`), so it is a legal
    `Com jasminDialect wideCtxt r64` the lowering consumes — and a direct witness
    that the `Fin 25` cap is the *authoring* builder's, not the lowering's. -/
def probeWideCom : Com jasminDialect wideCtxt r64 :=
  -- result slot 16+i := input i  op  input (15-i)   (i = 0 … 15)
  emitBin32 initWState .mul 16 0 15 fun s1 =>
  emitBin32 s1 .add 17 1 14 fun s2 =>
  emitBin32 s2 .sub 18 2 13 fun s3 =>
  emitBin32 s3 .mul 19 3 12 fun s4 =>
  emitBin32 s4 .add 20 4 11 fun s5 =>
  emitBin32 s5 .sub 21 5 10 fun s6 =>
  emitBin32 s6 .mul 22 6 9 fun s7 =>
  emitBin32 s7 .add 23 7 8 fun s8 =>
  emitBin32 s8 .mul 24 8 7 fun s9 =>
  emitBin32 s9 .add 25 9 6 fun s10 =>
  emitBin32 s10 .sub 26 10 5 fun s11 =>
  emitBin32 s11 .mul 27 11 4 fun s12 =>
  emitBin32 s12 .add 28 12 3 fun s13 =>
  emitBin32 s13 .sub 29 13 2 fun s14 =>
  emitBin32 s14 .mul 30 14 1 fun s15 =>
  emitBin32 s15 .add 31 15 0 fun s16 =>
    .ret (s16.cur 16)

/-! ## The lowering allocates and spills the wide Com

We read the lowering's slot model off the **virtual** body of the probe (the
same body `toLprogPhysAbi` walks), then check the two facts: the slot universe
exceeds the 13-register pool, and the linear scan emits at least one spill cell
`k.N`. Both are decidable finite checks on the concrete body. -/

/-- The per-binding logical-slot read/write trace of the probe body, exactly as
    the physical export walks it. -/
def probeTrace : List PhysEvent :=
  bodyTrace (comToLfundef probeWideCom).lfd_body

/-- **The probe's SSA slot universe exceeds the 13-register GP pool.** A
    non-spilling allocator (`AsmPrinter.allocGp` first-fit / the renaming
    `RandomizedRegAlloc`) cannot place a body whose live universe is wider than
    the pool; this is the pressure point ML-KEM N = 256 hits and the `Fin 25`
    `BState` author never reached. -/
theorem probeWide_universe_gt_pool : numGPRegs < physUniverse probeTrace := by
  native_decide

/-- **The lowering linear scan SPILLS the wide probe.** `toLprogPhysAbi`'s
    Poletto–Sarkar scan assigns at least one logical slot a physical index
    `≥ numGPRegs` (13), which `physRegName` renders as a stack spill cell `k.N`.
    The spilling is therefore performed by `toLprogPhysAbi` itself, on a Com
    whose live set the `Fin 25` `BState` builder could never have authored — the
    register-allocation residual named in `MlkemNttFieldEmit.lean`, exercised. -/
theorem probeWide_spills :
    ((physAssign probeTrace).any (fun p => numGPRegs ≤ p.2)) = true := by
  native_decide

/-- At least one rendered physical operand of the spilled probe is a `k.N` stack
    cell (the `physRegName` image of a `≥ numGPRegs` allocation), confirming the
    spill reaches the rendered operand names, not just the abstract assignment. -/
theorem probeWide_renders_spill_cell :
    ((physAssign probeTrace).any
      (fun p => "k.".isPrefixOf (physRegName p.2))) = true := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.MlkemNttWidenProbe
