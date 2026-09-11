/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiEmit
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.ScalarSExprWidth32Prototype
public import CatCrypt.Crypto.SecureCompilation.Dialects.ScalarSExprWidth32Prototype

/-!
# FrodoKEM core arithmetic emitted from a `Com jasminDialect`

FrodoKEM is the conservative / high-assurance lattice KEM (BSI / ISO-recommended)
whose security rests on plain LWE with **no ring structure** — so its core
operation is a dense integer matrix–vector product over `Z/2^16`, not an NTT.
That is precisely the operation jasmin / libjade does **not** ship.

This module emits FrodoKEM's core arithmetic — a `16×16 · 16` matrix–vector tile
over `Z/2^16` (the modulus `q = 2^16` of Frodo-976 / Frodo-1344) — as a
straight-line jasmin computation, built directly as a `Com jasminDialect` and
rendered through the register-arith EMIT-computation path (`emitAbiOrchReg`).

It is the **simplest** emit-computation target: dense `u16` schoolbook multiply +
add, with modular reduction completely **free** via `u16` two's-complement
wraparound (`mul`/`add` on `BitVec 16` already reduce mod `2^16` — no Barrett, no
ring fold). Width `w = 16` throughout.

## Construction (CPS builder over a `stack u16` state array)

The kernel computes `out[r] = Σ_{c=0..15} A[r][c] · s[c]` (mod `2^16`) for the
16 output rows of a row-major `16×16` matrix `A` times a length-16 vector `s`.

The builder threads a `BState` (the 16 output-slot variables, plus the two
scratch variables) over a growing context, emitting one `regArith`-`mul` /
`regArith`-`add` binding at a time via the CPS `emitOp`. To satisfy
`emitAbiOrchReg`'s output convention — output word `j` is the `(cnt-nOut+j)`-th
binding — the program is laid out in three phases:

1. **main** (per row `r`): `out[r] = A[r][0]·s[0]` (one `mul`), then for
   `c = 1..14`: `acc = A[r][c]·s[c]` (`mul`) and `out[r] += acc` (`add`)
   — 29 bindings/row, 464 total;
2. **term-15 precompute** (per row `r`): `t15[r] = A[r][15]·s[15]` (one `mul`)
   — 16 bindings, into 16 private scratch slots;
3. **tail** (the last 16 bindings, in row order): `out[r] += t15[r]` (`add`).

So the final write to `out[r]` is binding `cnt-16+r`, exactly the last-`nOut`
convention. Total: `464 + 16 + 16 = 496` bindings, checked below.

## ABI / state layout

`export fn frodo_matmul(reg ptr u16[16] out, reg const ptr u16[272] inp)`.
The input buffer holds `A[0..255]` (row-major, `A[r][c] = inp[r*16+c]`) followed
by `s[0..15]` (`inp[256..271]`); all `272` are copied into the state array. The
state file is a single `stack u16[305]` array `k`:

* `k[0..255]`   — the matrix `A` (row-major);
* `k[256..271]` — the vector `s`;
* `k[272..287]` — the 16 outputs `out[r]`;
* `k[288]`      — the reused accumulate scratch;
* `k[289..304]` — the 16 term-15 products.

`u16` wraparound IS the modular reduction (`q = 2^16`), so no reduction op is
emitted. The KAT in `bench/frodo_compare/` cross-checks the jasminc-compiled
output byte-identical against an independent C schoolbook reference.

## Scope

This is the dense `Z/2^16` matrix–vector arithmetic that **is** Frodo's core
(`A·s + e`). The full Frodo-640 / 976 / 1344 matrices (`640×640` and larger) tile
this `16×16` kernel via the for-loop layer — out of scope for this straight-line
kernel.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.FrodoMatmulEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiEmit
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)

set_option autoImplicit false

/-- The `reg 16` dialect type, abbreviated. -/
abbrev r16 : JasminTy := .reg 16

/-! ## 1. Dimensions and state-slot layout

State array `stack u16[stateSize]`, slots:

* `A[r][c]` → `k[r*16 + c]`            (`0..255`)
* `s[c]`    → `k[256 + c]`             (`256..271`)
* `out[r]`  → `k[272 + r]`             (`272..287`)
* `acc`     → `k[accSlot]`             (`288`)
* `t15[r]`  → `k[t15Base + r]`         (`289..304`)
-/

/-- Tile dimension (16×16 · 16). -/
abbrev N : Nat := 16

/-- Slot of `A[r][c]` (row-major). -/
def aSlot (r c : Nat) : Nat := r * 16 + c
/-- Slot of `s[c]`. -/
def sSlot (c : Nat) : Nat := 16 * 16 + c
/-- Slot of `out[r]`. -/
def outSlot (r : Nat) : Nat := 16 * 16 + 16 + r
/-- The single reused accumulate-scratch slot. -/
def accSlot : Nat := 16 * 16 + 2 * 16
/-- Base slot of the 16 term-15 products. -/
def t15Base : Nat := 16 * 16 + 2 * 16 + 1
/-- Slot of `t15[r]`. -/
def t15Slot (r : Nat) : Nat := t15Base + r
/-- Number of state slots: `A` (256) + `s` (16) + `out` (16) + `acc` (1) +
    `t15` (16) = 305. -/
def stateSize : Nat := 16 * 16 + 2 * 16 + 1 + 16

/-! ## 2. Builder state and `emitOp`

The state slots are addressed by `Nat`, so `BState` only needs to track *one*
fresh-variable witness per logical slot. We use `Fin stateSize → Ctxt.Var Γ r16`
exactly as ChaCha's `BState.cur`. -/

/-- The current variable for each of the `stateSize` state slots. -/
structure BState (Γ : Ctxt jasminDialect) where
  cur : Fin stateSize → Ctxt.Var Γ r16

/-- The fresh head variable of an extended context. -/
def headVar (Γ : Ctxt jasminDialect) : Ctxt.Var (r16 :: Γ) r16 := .here

/-- Emit one `regArith op 16` binding writing slot `dst`, reading slots `a`/`b`,
    then continue with `k` over the extended context (slot `dst` ← fresh head). -/
def emitOp {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) (op : JasminBinOp) (dst a b : Fin stateSize)
    (k : {Γ' : Ctxt jasminDialect} → BState Γ' → Com jasminDialect Γ' t) :
    Com jasminDialect Γ t :=
  let e : Expr jasminDialect Γ r16 :=
    { op := .regArith op 16
      retTy_eq := rfl
      args := .cons (st.cur a) (.cons (st.cur b) .nil) }
  let st' : BState (r16 :: Γ) :=
    { cur := fun i => if i = dst then headVar Γ else (st.cur i).there }
  .var e (k st')

/-! ## 3. Matrix–vector builders -/

/-- Continuation type: a `Com` builder polymorphic in the (extended) context. -/
abbrev Cont (t : JasminTy) := {Γ' : Ctxt jasminDialect} → BState Γ' → Com jasminDialect Γ' t

/-- Slot witnesses as `Fin stateSize` (all indices are `< stateSize` by `omega`). -/
def aFin (r c : Nat) (h : r < N) (hc : c < N) : Fin stateSize :=
  ⟨aSlot r c, by
    have hr : r < 16 := h; have hc' : c < 16 := hc; unfold aSlot stateSize; omega⟩
def sFin (c : Nat) (hc : c < N) : Fin stateSize :=
  ⟨sSlot c, by have hc' : c < 16 := hc; unfold sSlot stateSize; omega⟩
def outFin (r : Nat) (h : r < N) : Fin stateSize :=
  ⟨outSlot r, by have hr : r < 16 := h; unfold outSlot stateSize; omega⟩
def accFin : Fin stateSize :=
  ⟨accSlot, by unfold accSlot stateSize; omega⟩
def t15Fin (r : Nat) (h : r < N) : Fin stateSize :=
  ⟨t15Slot r, by have hr : r < 16 := h; unfold t15Slot t15Base stateSize; omega⟩

/-- Accumulate terms `c = startC .. 14` for row `r`: each `c` emits
    `acc = A[r][c]·s[c]` (`mul`) and `out[r] += acc` (`add`). Recurses on the
    fuel `fuel = (N-1) - startC` (a `Nat`, so termination is structural). -/
def emitRowAcc {t : JasminTy} (r : Nat) (hr : r < N) :
    Nat → Nat → {Γ : Ctxt jasminDialect} → BState Γ → Cont t →
    Com jasminDialect Γ t
  | 0, _, _, st, k => k st
  | (fuel + 1), c, _, st, k =>
      if hc : c < N - 1 then
        -- acc = A[r][c] * s[c]
        emitOp st .mul accFin (aFin r c hr (by omega)) (sFin c (by omega))
          fun s1 =>
        -- out[r] += acc
        emitOp s1 .add (outFin r hr) (outFin r hr) accFin fun s2 =>
        emitRowAcc r hr fuel (c + 1) s2 k
      else k st

/-- Main phase for one row `r`: `out[r] = A[r][0]·s[0]`, then for `c = 1..14`,
    `acc = A[r][c]·s[c]` (`mul`) and `out[r] += acc` (`add`). 29 bindings. -/
def emitRowMain {t : JasminTy} {Γ : Ctxt jasminDialect}
    (st : BState Γ) (r : Nat) (hr : r < N) (k : Cont t) : Com jasminDialect Γ t :=
  -- out[r] = A[r][0] * s[0]
  emitOp st .mul (outFin r hr) (aFin r 0 hr (by decide)) (sFin 0 (by decide))
    fun s0 =>
  -- accumulate terms c = 1..14
  emitRowAcc r hr (N - 1) 1 s0 k

/-- Term-15 precompute for one row `r`: `t15[r] = A[r][15]·s[15]` (`mul`). -/
def emitRowTerm15 {t : JasminTy} {Γ : Ctxt jasminDialect}
    (st : BState Γ) (r : Nat) (hr : r < N) (k : Cont t) : Com jasminDialect Γ t :=
  emitOp st .mul (t15Fin r hr) (aFin r 15 hr (by decide)) (sFin 15 (by decide)) k

/-- Tail step for one row `r`: `out[r] += t15[r]` (`add`). -/
def emitRowTail {t : JasminTy} {Γ : Ctxt jasminDialect}
    (st : BState Γ) (r : Nat) (hr : r < N) (k : Cont t) : Com jasminDialect Γ t :=
  emitOp st .add (outFin r hr) (outFin r hr) (t15Fin r hr) k

/-- Iterate a per-row builder over rows `0..N-1` in order. -/
def emitRows {t : JasminTy}
    (step : {Γ : Ctxt jasminDialect} → BState Γ → (r : Nat) → r < N → Cont t →
            Com jasminDialect Γ t) :
    Nat → {Γ : Ctxt jasminDialect} → BState Γ → Cont t → Com jasminDialect Γ t
  | 0, _, st, k => k st
  | (m + 1), _, st, k =>
      if h : m < N then
        -- emit rows 0..m-1 first, then row m, so rows come out in order 0,1,…,N-1
        emitRows step m st fun st' => step st' m h k
      else k st

/-! ## 4. Initial context and the top-level `Com` -/

/-- The input context: `stateSize` `r16` words (the whole state array). -/
abbrev inCtxt : Ctxt jasminDialect := List.replicate stateSize r16

/-- The De Bruijn variable for input word `i` of a *replicate* `r16`-context of
    depth `m+1`. Mirrors ChaCha's `inputVar`. -/
def inputVar : (m : Nat) → Nat →
    @Ctxt.Var jasminDialect (List.replicate (m + 1) r16) r16
  | _, 0 => .here
  | 0, _ => .here
  | (m + 1), (k + 1) => (inputVar m k).there

/-- Input word `i` of `inCtxt`. -/
def inVar (i : Nat) : Ctxt.Var inCtxt r16 := inputVar (stateSize - 1) i

/-- The initial builder state: slot `i` points at input word `i`. The matrix and
    vector live in `k[0..271]` (copied in); the output / scratch / term-15 slots
    are written before any read, so their initial value is irrelevant (seeded to
    the slot's own input word). -/
def initBState : BState inCtxt where
  cur := fun i => inVar i.val

/-- The full matrix–vector kernel as a `Com jasminDialect`: the main phase
    (rows 0..15), the term-15 precompute (rows 0..15), then the tail (rows 0..15,
    the last 16 bindings — output words `out[0..15]`). -/
def frodoMatmulCom : Com jasminDialect inCtxt r16 :=
  emitRows (fun st r hr k => emitRowMain st r hr k) N initBState fun s1 =>
  emitRows (fun st r hr k => emitRowTerm15 st r hr k) N s1 fun s2 =>
  emitRows (fun st r hr k => emitRowTail st r hr k) N s2 fun sf =>
  .ret (sf.cur ⟨outSlot 15, by unfold outSlot stateSize; omega⟩)

/-! ## 5. Destination-slot sequence (flat mirror of the typed builder)

`frodoMatmulCom` gives every binding a fresh result; a faithful jasmin emission
must reuse the `stateSize` state-array slots. `frodoSlots` is the per-binding
destination-slot list, a flat mirror of the typed builder's `dst` choices (same
op sequence, same slots), kept in lock-step (checked below). -/

/-- Main-phase slot sequence for one row `r`:
    `[out r] ++ (for c=1..14: [acc, out r])`. 1 + 14·2 = 29 slots. -/
def rowMainSlots (r : Nat) : List Nat :=
  outSlot r :: ((List.range (N - 1)).drop 1).flatMap (fun _ => [accSlot, outSlot r])

/-- Term-15 slot for one row `r`: `[t15 r]`. -/
def rowTerm15Slots (r : Nat) : List Nat := [t15Slot r]

/-- Tail slot for one row `r`: `[out r]`. -/
def rowTailSlots (r : Nat) : List Nat := [outSlot r]

/-- The full destination-slot list: main (rows 0..15), term-15 (rows 0..15),
    tail (rows 0..15). -/
def frodoSlots : List Nat :=
  ((List.range N).flatMap rowMainSlots)
    ++ ((List.range N).flatMap rowTerm15Slots)
    ++ ((List.range N).flatMap rowTailSlots)

/-- Slot `s` → element `k[s]` of the `stack u16[stateSize]` state array. -/
def slotReg (s : Nat) : String := "k[" ++ toString s ++ "]"

/-- The per-binding destination name: binding `k` writes `k[slot]`. -/
def frodoDstName (k : Nat) : String := slotReg (frodoSlots.getD k 0)

/-- Operand string for input word `i`: every state slot is the state-array
    element `k[i]` (the matrix and vector are copied into the array at entry; the
    output / scratch / term-15 slots are written before being read). -/
def frodoInName (i : Nat) : String := slotReg i

/-- The state file declared by the export: a single `stack u16[stateSize]`
    array `k`. The two working registers `w0`,`w1` are declared by the
    orchestration. -/
def frodoRegDecls : List String := ["stack u16[" ++ toString stateSize ++ "] k"]

/-! ## 6. Emit the `.jazz` (register-arith mode) -/

/-- The emitted `.jazz` for the FrodoKEM matrix–vector tile: a `reg ptr u16[16]
    out` output buffer and a `reg const ptr u16[272] inp` input (256 matrix + 16
    vector words), rendered through the `emitAbiOrchReg` EMIT-computation path.
    No leaves: every line is a real `regArith` jasmin scalar `mul`/`add`. -/
def frodoMatmulJazz : String :=
  emitAbiOrchReg "frodo_matmul" (w := 16) (nIn := 272) (nOut := 16) (nCopy := 272)
    frodoRegDecls frodoInName frodoDstName frodoMatmulCom

/-! ### Structural sanity checks on the emitted text -/

/- The export has the expected Frodo-tile ABI (16-word out, 272-word in:
    256 matrix + 16 vector). -/
#guard (strContains frodoMatmulJazz "export fn frodo_matmul(reg ptr u16[16] out, reg const ptr u16[272] inp)")

/- The emitted body renders real `u16` multiply (the schoolbook products). -/
#guard (strContains frodoMatmulJazz " * ")

/- …and real `u16` add (the accumulation). -/
#guard (strContains frodoMatmulJazz " + ")

/- The first emitted op is row 0's first product `out[0] = A[0][0]·s[0]`,
    rendered as the load/compute/store sequence over `w0`,`w1`:
    `w0 = k[0]; w1 = k[256]; w0 = w0 * w1; k[272] = w0;`. -/
#guard (strContains frodoMatmulJazz "w0 = k[0];")
    && (strContains frodoMatmulJazz "w1 = k[256];")
    && (strContains frodoMatmulJazz "w0 = w0 * w1;")

/- The output is copied back from the state array via `w0`: output word 0 stores
    the out-slot element `k[272]` (`out[0]`). -/
#guard (strContains frodoMatmulJazz "w0 = k[272];") && (strContains frodoMatmulJazz "out[0] = w0;")

/- The state lives in the reused `stack u16[305]` array `k`; the only registers
    are the two working scratch `w0`,`w1` (no fresh `t{N}` per binding). -/
#guard (strContains frodoMatmulJazz "stack u16[305] k;")
    && (strContains frodoMatmulJazz "reg u16 w0;")
    && !(strContains frodoMatmulJazz "reg u16 t100;")

/- It emits **no** leaf call (pure computation): no `// non-regArith op skipped`
    marker appears. The body is straight-line `regArith`. -/
#guard !(strContains frodoMatmulJazz "non-regArith op skipped")

/-- Binding count of a `Com` (one per `.var`). -/
def comBindings : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → Nat
  | _, _, .ret _ => 0
  | _, _, .var _ body => 1 + comBindings body

/-- The flat destination-slot list and the typed `Com` are in lock-step: they
    have the same number of bindings (16 rows × 29 main + 16 term-15 + 16 tail =
    496). So `frodoDstName` assigns exactly one destination register per
    `Com.var`. -/
theorem frodoSlots_length_eq_bindings :
    frodoSlots.length = comBindings frodoMatmulCom := by native_decide

/-- The slot list has exactly 496 bindings. -/
theorem frodoSlots_length : frodoSlots.length = 496 := by native_decide

/-! ## 7. Front-sourced MAC core (covered SExpr front, rfl-provenance)

The straight-line `frodoMatmulCom` above is the LEGACY register-arith variant
(rendered to the optional `gen/frodo_matmul.jazz`); it is superseded on the
deploy path by the FRONT-sourced rolled loop — the deployed
`bench/frodo_compare/gen/frodo_matmul_vec.s` is generated by
`FrodoMatmulEmit` from `matmulComL = rolledForLoopN (matmulBody …)`, a
covered-fragment `RFor` over `RScalarSetExpr`/`RArrLoad`/`RArrStore`.

This section pins the arithmetic leaf of that fragment: the FrodoKEM inner MAC
`c += a·b (mod 2^16)` expressed as width-16 `SExpr`s over the covered front
alphabet (`SMul`/`SAdd`, with the `q = 2^16` reduction FREE via `u16`
wraparound) and routed through the verified scalar front leaf `lowerSExprW 16`
→ `Com catCryptDialect` → `cryptoDialectToJasminCom` (the FRONT marker) → owned
x86. Provenance is `isSome := by rfl` (no `native_decide`); value correctness is
the byte-KAT in `bench/frodo_compare`. -/
namespace FrontSourced

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)

/-- The width-parametric scalar-`SExpr` front leaf. -/
abbrev lowerW := @CatCrypt.Crypto.SecureCompilation.Dialects.ScalarSExprWidth32Prototype.lowerSExprW

/-- FrodoKEM lane product `p = a · b` (`u16` wraparound = mod `2^16` reduction). -/
def frodoMul : SExpr := .SMul (.SVar "a") (.SVar "b")

/-- FrodoKEM inner multiply-accumulate `c' = c + a · b` (the loop-body MAC step). -/
def frodoMac : SExpr := .SAdd (.SVar "c") (.SMul (.SVar "a") (.SVar "b"))

/-- The three-slot MAC context (`a b c`, all `.sword 16`). -/
def macΓ : Ctx := [.sword 16, .sword 16, .sword 16]

/-- `VarMap` binding `a b c` (`a` = `.here`). -/
def macVM : VarMap macΓ :=
  (((VarMap.empty.bind "c").bind "b").bind "a")

/-- Lower a width-`w` `SExpr` to `Com catCryptDialect` via the covered front leaf. -/
def progOfW (w : Nat) {Γ : Ctx} (vm : VarMap Γ) (e : SExpr) :
    Option (Com catCryptDialect Γ (.sword w)) :=
  match lowerW w vm 0 e with
  | some r =>
      match r.1.vm.lookup r.2.1 with
      | some ⟨.sword w', v⟩ => if h : w' = w then r.1.cont (Com.ret (toVIRVar (h ▸ v))) else none
      | _ => none
  | none => none

/-- Lower on to the owned x86 backend (`Com jasminDialect`). -/
def jasminOfW (w : Nat) {Γ : Ctx} (vm : VarMap Γ) (e : SExpr) :=
  (progOfW w vm e).bind DialectToJasminCom.cryptoDialectToJasminCom

theorem frodo_mul_isSome : (progOfW 16 macVM frodoMul).isSome := by rfl
theorem frodo_mul_lowers : (jasminOfW 16 macVM frodoMul).isSome := by rfl
theorem frodo_mac_isSome : (progOfW 16 macVM frodoMac).isSome := by rfl
theorem frodo_mac_lowers : (jasminOfW 16 macVM frodoMac).isSome := by rfl

end FrontSourced

end CatCrypt.Crypto.SecureCompilation.VIR.FrodoMatmulEmit
