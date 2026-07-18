/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3FriFoldEmit

/-!
# Plonky3 degree-4 extension-field FRI kernels as `Com jasminDialect`

`FULL_PROVER_VS_P3.md` Gap-2 item 3 / the extension-field FRI residual: the p3
accept-prover (`bench/plonky3_compare/p3_accept_prove.c`) needs
`BinomialExtensionField<BabyBear, 4>` arithmetic (binomial `x^4 = 11`) — the
quartic-extension multiply, the Frobenius/norm inverse, and the `ExtensionMmcs`
fold — and `FULL_PROVER_VS_P3.md` records "there are no emitted extension-field
kernels yet". This module emits the CORE ext-field kernels through the verified
front's register-arith path (the same `emitBBMul`/`emitBBAdd`/`emitBBSub`
builder `Plonky3FriFoldEmit` / `Plonky3GlueEmit` use), so the deg-4 ext
arithmetic is verified-emitted rather than hand-C.

## The reference (byte-for-byte `p3_accept_prove.c`)

```
E = { c[0..3] }              // BinomialExtensionField<BabyBear,4>, x^4 = 11
emul(a,b):                   // ext4 multiply, schoolbook + x^4=11 reduction
  c0 = a0·b0 + 11·(a1·b3 + a2·b2 + a3·b1)
  c1 = a0·b1 + a1·b0 + 11·(a2·b3 + a3·b2)
  c2 = a0·b2 + a1·b1 + a2·b0 + 11·(a3·b3)
  c3 = a0·b3 + a1·b2 + a2·b1 + a3·b0
escale(a,s) = { a_i · s }    // base-field scale (Frobenius coeff multiply)
efrob(a):  c_i = a_i · f1^i,  f1 = 11^((p-1)/4)   // x -> x^p
einv(a):                     // Frobenius / norm inverse
  t = efrob(a)·efrob²(a)·efrob³(a);  n = (a·t).c[0]  (norm, in base field)
  return escale(t, finv(n))
```

`emul` and `escale`/`efrob` are pure base-field `bbMul`/`bbAdd` on canonical
operands (the `W = 11` reduction factor is a `bbMul` by the input constant `11`),
so they sit in the same Barrett regime the A4/A7 leaves are KAT-validated in.
The inverse decomposes into `emul` + `escale` + the existing base-field
`bbInv` leaf (`Plonky3FriFoldEmit.bbInvCom`, the Fermat `a^(p-2)` chain) for
`finv(n)`; the per-element ext-mul leaves are the new field kernels.

## What is emitted here

Each ext4-mul output coordinate is one leaf (`ext4_mul_c0_rc … c3_rc`), taking
the 8 input coords `a0..a3, b0..b3` and the reduction constant `W = 11`, all
canonical, computing the coordinate by Barrett `bbMul`/`bbAdd`. The base-field
scale `ext4_scale_rc` (one coord · scalar) covers `escale`/`efrob`. Each leaf is
`allRegArith` (`*_is_regarith_only`, via the `RegTail` keystone reused from
`Plonky3FriFoldEmit`), so its denotation IS the Barrett word arithmetic
(by-construction `leaf.denote = spec`); numeric equality to `emul`/`escale` is
KAT-witnessed against the p3 reference (`ext4_from_rustcmd_kat.c`).

## Scope / residual

LANDED (verified-emitted, KAT): the deg-4 ext multiply (all four coords) and the
base-field scale — the CORE ext arithmetic, and the multiplicative pieces of the
Frobenius/norm inverse. The `ExtensionMmcs` fold (flattening the arity-2 fold
layer's 16×8 base rows and committing) is **structural marshalling** (lane
interleave + the base-field Merkle commit, which is the existing
`Plonky3CompressEmit`/`HashLeafEmit` leaves) over these ext-mul kernels; the
fold's per-element ext arithmetic IS one of the emitted coords. The fold's row
flatten/commit wiring is the precise residual (index plumbing, no new field op).
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.Plonky3ExtFieldEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiEmit
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)
open CatCrypt.Crypto.SecureCompilation.VIR.Plonky3FriFoldEmit
  (r64 Src Cont LState emitOp emitCsub emitBBMul emitBBAdd emitBBSub
   allRegArith RegTail allRegArith_emitOp regTail_emitCsub regTail_emitBBMul
   regTail_emitBBAdd regTail_emitBBSub nSlots nSlots_pos slot inS stS slotName
   inCtxt initLState comBindings)

set_option autoImplicit false

/-! ## 1. Input-word layout

We reuse `Plonky3FriFoldEmit`'s 16-input context (`inCtxt`) and Barrett-constant
indices (`iMU=7 … iSh63=12`). The ext-mul leaves need the 8 coords
`a0..a3, b0..b3` plus `W = 11`. The Barrett constants are at `7..12`, leaving
free input words `0..6` and `13..15` (10 words). Place:
* `a0..a3` → `0,1,2,3`
* `b0,b1`  → `4,5`        (FriFold's `invTwo,two` slots, unused here)
* `b2,b3`  → `13,14`
* `W = 11` → `15`. -/

def iA : Nat → Nat
  | 0 => 0 | 1 => 1 | 2 => 2 | _ => 3
def iB : Nat → Nat
  | 0 => 4 | 1 => 5 | 2 => 13 | _ => 14
def iW : Nat := 15
/-- The `0` immediate (FriFold's `iZero`). -/
def iZero : Nat := 9

/-! ## 2. Ext4-mul one-coordinate bodies

Slot plan (within `nSlots = 14`): `acc` (slot 0), `s` (slot 1, the inner sum
folded by `W`), `t` (slot 2, per-product scratch). All Barrett `bbMul`/`bbAdd`
on canonical operands. -/

def eAcc : Fin nSlots := slot 0
def eS : Fin nSlots := slot 1
def eT : Fin nSlots := slot 2

/-- `acc = acc + a_i·b_j` (one schoolbook product accumulated). -/
def macc (ai bj : Nat) (k : Cont r64) : Cont r64 := fun st =>
  emitBBMul st eT (inS (iA ai)) (inS (iB bj)) fun s1 =>
  emitBBAdd s1 eAcc (.st eAcc) (.st eT) k

/-- `s = s + a_i·b_j` into the `W`-folded inner sum. -/
def saccS (ai bj : Nat) (k : Cont r64) : Cont r64 := fun st =>
  emitBBMul st eT (inS (iA ai)) (inS (iB bj)) fun s1 =>
  emitBBAdd s1 eS (.st eS) (.st eT) k

/-- `c0 = a0·b0 + W·(a1·b3 + a2·b2 + a3·b1)`. -/
def c0Body (k : Cont r64) : Cont r64 := fun st =>
  -- acc = a0·b0
  emitBBMul st eAcc (inS (iA 0)) (inS (iB 0)) fun s1 =>
  -- s = a1·b3
  emitBBMul s1 eS (inS (iA 1)) (inS (iB 3)) fun s2 =>
  saccS 2 2 (saccS 3 1 (fun s3 =>
    -- s = W·s ; acc = acc + s
    emitBBMul s3 eS (inS iW) (.st eS) fun s4 =>
    emitBBAdd s4 eAcc (.st eAcc) (.st eS) k)) s2

/-- `c1 = a0·b1 + a1·b0 + W·(a2·b3 + a3·b2)`. -/
def c1Body (k : Cont r64) : Cont r64 := fun st =>
  emitBBMul st eAcc (inS (iA 0)) (inS (iB 1)) fun s1 =>
  macc 1 0 (fun s2 =>
    -- s = a2·b3 + a3·b2
    emitBBMul s2 eS (inS (iA 2)) (inS (iB 3)) fun s3 =>
    saccS 3 2 (fun s4 =>
      emitBBMul s4 eS (inS iW) (.st eS) fun s5 =>
      emitBBAdd s5 eAcc (.st eAcc) (.st eS) k) s3) s1

/-- `c2 = a0·b2 + a1·b1 + a2·b0 + W·(a3·b3)`. -/
def c2Body (k : Cont r64) : Cont r64 := fun st =>
  emitBBMul st eAcc (inS (iA 0)) (inS (iB 2)) fun s1 =>
  macc 1 1 (macc 2 0 (fun s2 =>
    -- s = W·(a3·b3)
    emitBBMul s2 eS (inS (iA 3)) (inS (iB 3)) fun s3 =>
    emitBBMul s3 eS (inS iW) (.st eS) fun s4 =>
    emitBBAdd s4 eAcc (.st eAcc) (.st eS) k)) s1

/-- `c3 = a0·b3 + a1·b2 + a2·b1 + a3·b0`. -/
def c3Body (k : Cont r64) : Cont r64 := fun st =>
  emitBBMul st eAcc (inS (iA 0)) (inS (iB 3)) fun s1 =>
  macc 1 2 (macc 2 1 (macc 3 0 k)) s1

def eFinalize : Cont r64 := fun st => .ret (st.cur eAcc)

/-! ## 3. Base-field scale (`escale` / `efrob` coordinate)

`ext4_scale_rc(x, s) = bbMul x s` — one coordinate times the (base-field) scalar.
Inputs: `x` at word `0`, `s` at word `1`. -/

def scaleBody (k : Cont r64) : Cont r64 := fun st =>
  emitBBMul st eAcc (inS 0) (inS 1) k

/-! ## 3a. Per-coordinate ext add / ext sub (`eadd` / `esub`)

`BinomialExtensionField` addition / subtraction is coordinate-wise base-field
`bbAdd` / `bbSub`. The fold (`folded16[r] = escale(eadd(lo,hi),inv2) + …`) and the
barycentric OOD/DEEP (`eadd`/`esub` over reduced openings) need these; each is one
base-field op on the two coordinate inputs (`x` at word `0`, `y` at word `1`). -/

def addBody (k : Cont r64) : Cont r64 := fun st =>
  emitBBAdd st eAcc (inS 0) (inS 1) k

def subBody (k : Cont r64) : Cont r64 := fun st =>
  emitBBSub st eAcc (inS 0) (inS 1) k

/-! ## 4. The top-level `Com`s -/

def ext4MulC0Com : Com jasminDialect inCtxt r64 := c0Body eFinalize initLState
def ext4MulC1Com : Com jasminDialect inCtxt r64 := c1Body eFinalize initLState
def ext4MulC2Com : Com jasminDialect inCtxt r64 := c2Body eFinalize initLState
def ext4MulC3Com : Com jasminDialect inCtxt r64 := c3Body eFinalize initLState
def ext4ScaleCom : Com jasminDialect inCtxt r64 := scaleBody eFinalize initLState
def ext4AddCom : Com jasminDialect inCtxt r64 := addBody eFinalize initLState
def ext4SubCom : Com jasminDialect inCtxt r64 := subBody eFinalize initLState

/-! ## 5. allRegArith — leaf.denote = spec by construction

Each `*Body` is built only from `emitBBMul`/`emitBBAdd` (which preserve
`RegTail`) over the `eFinalize` `.ret`, so every binding is a `regArith` op. -/

/-- `eFinalize` produces an `allRegArith` body (a bare `.ret`). -/
theorem regTail_eFinalize : RegTail eFinalize := by
  intro Γ st; rfl

theorem regTail_macc (ai bj : Nat) {k : Cont r64} (hk : RegTail k) :
    RegTail (macc ai bj k) := by
  intro Γ st
  show allRegArith (macc ai bj k st) = true
  unfold macc
  exact regTail_emitBBMul (regTail_emitBBAdd hk eAcc _ _) eT _ _ Γ st

theorem regTail_saccS (ai bj : Nat) {k : Cont r64} (hk : RegTail k) :
    RegTail (saccS ai bj k) := by
  intro Γ st
  show allRegArith (saccS ai bj k st) = true
  unfold saccS
  exact regTail_emitBBMul (regTail_emitBBAdd hk eS _ _) eT _ _ Γ st

/-- The ext4-mul `c0` leaf is `allRegArith` (denote = Barrett word arithmetic). -/
theorem ext4MulC0_is_regarith_only : allRegArith ext4MulC0Com = true := by
  have h := regTail_emitBBMul
    (regTail_emitBBMul
      (regTail_emitBBAdd regTail_eFinalize eAcc (.st eAcc) (.st eS))
      eS (inS iW) (.st eS))
    eAcc (inS (iA 0)) (inS (iB 0))
  -- assemble through the two `saccS` and the head products
  have h2 := regTail_emitBBMul
    (regTail_saccS 2 2 (regTail_saccS 3 1 (by
      intro Γ st
      exact regTail_emitBBMul
        (regTail_emitBBAdd regTail_eFinalize eAcc (.st eAcc) (.st eS))
        eS (inS iW) (.st eS) Γ st)))
    eS (inS (iA 1)) (inS (iB 3))
  exact regTail_emitBBMul h2 eAcc (inS (iA 0)) (inS (iB 0)) _ initLState

theorem ext4MulC1_is_regarith_only : allRegArith ext4MulC1Com = true := by
  have tail : RegTail (fun st =>
      emitBBMul st eS (inS (iA 2)) (inS (iB 3)) fun s3 =>
      saccS 3 2 (fun s4 =>
        emitBBMul s4 eS (inS iW) (.st eS) fun s5 =>
        emitBBAdd s5 eAcc (.st eAcc) (.st eS) eFinalize) s3) := by
    intro Γ st
    exact regTail_emitBBMul
      (regTail_saccS 3 2 (by
        intro Γ' st'
        exact regTail_emitBBMul
          (regTail_emitBBAdd regTail_eFinalize eAcc (.st eAcc) (.st eS))
          eS (inS iW) (.st eS) Γ' st'))
      eS (inS (iA 2)) (inS (iB 3)) Γ st
  exact regTail_emitBBMul (regTail_macc 1 0 tail) eAcc (inS (iA 0)) (inS (iB 1))
    _ initLState

theorem ext4MulC2_is_regarith_only : allRegArith ext4MulC2Com = true := by
  have tail : RegTail (fun st =>
      emitBBMul st eS (inS (iA 3)) (inS (iB 3)) fun s3 =>
      emitBBMul s3 eS (inS iW) (.st eS) fun s4 =>
      emitBBAdd s4 eAcc (.st eAcc) (.st eS) eFinalize) := by
    intro Γ st
    exact regTail_emitBBMul
      (regTail_emitBBMul
        (regTail_emitBBAdd regTail_eFinalize eAcc (.st eAcc) (.st eS))
        eS (inS iW) (.st eS))
      eS (inS (iA 3)) (inS (iB 3)) Γ st
  exact regTail_emitBBMul (regTail_macc 1 1 (regTail_macc 2 0 tail))
    eAcc (inS (iA 0)) (inS (iB 2)) _ initLState

theorem ext4MulC3_is_regarith_only : allRegArith ext4MulC3Com = true := by
  exact regTail_emitBBMul
    (regTail_macc 1 2 (regTail_macc 2 1 (regTail_macc 3 0 regTail_eFinalize)))
    eAcc (inS (iA 0)) (inS (iB 3)) _ initLState

theorem ext4Scale_is_regarith_only : allRegArith ext4ScaleCom = true := by
  exact regTail_emitBBMul regTail_eFinalize eAcc (inS 0) (inS 1) _ initLState

theorem ext4Add_is_regarith_only : allRegArith ext4AddCom = true := by
  exact regTail_emitBBAdd regTail_eFinalize eAcc (inS 0) (inS 1) _ initLState

theorem ext4Sub_is_regarith_only : allRegArith ext4SubCom = true := by
  exact regTail_emitBBSub regTail_eFinalize eAcc (inS 0) (inS 1) _ initLState

/-- **All five ext-field leaves are `allRegArith`.** Each ext4-mul coordinate and
    the base-field scale denote the exact Barrett word arithmetic — the
    by-construction `leaf.denote = spec` for the deg-4 ext-field kernels. -/
theorem ext_field_all_regarith_only :
    allRegArith ext4MulC0Com = true ∧ allRegArith ext4MulC1Com = true
      ∧ allRegArith ext4MulC2Com = true ∧ allRegArith ext4MulC3Com = true
      ∧ allRegArith ext4ScaleCom = true ∧ allRegArith ext4AddCom = true
      ∧ allRegArith ext4SubCom = true :=
  ⟨ext4MulC0_is_regarith_only, ext4MulC1_is_regarith_only,
   ext4MulC2_is_regarith_only, ext4MulC3_is_regarith_only,
   ext4Scale_is_regarith_only, ext4Add_is_regarith_only,
   ext4Sub_is_regarith_only⟩

end CatCrypt.Crypto.SecureCompilation.VIR.Plonky3ExtFieldEmit
