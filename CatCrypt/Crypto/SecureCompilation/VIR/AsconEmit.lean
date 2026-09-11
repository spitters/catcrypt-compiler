/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom

/-!
# Ascon permutation (`ascon_pa` / `ascon_pb`), FRONT-COMPILED

The Ascon permutation (NIST SP 800-232 / Ascon v1.2) — the core of Ascon-128
AEAD — sourced through the verified `CProg`-free front, with NO hand-built `Com`
anywhere in the emit path:

```
  asconBody (LowCT: RScalarSetExpr u64 word math over the 5 state words)
    --(translateDialectControl)-->   Com catCryptDialect srcCtx (.sword 64)
    --(cryptoDialectToJasminCom)-->  asconP{a,b}Com : Com jasminDialect inCtxt r64
```

The round is pure bit-ops over five 64-bit words `x₀ … x₄`:

* **round-constant add** — one `SXor` of a literal round constant into `x₂`;
* **substitution layer** — the bit-sliced Keccak-χ S-box: `SXor` / `SAnd` and
  NOT(`x`) = `SXor x 0xFFFF…FF`;
* **linear diffusion** — per-word `x ← x ⊕ (x ⋙ a) ⊕ (x ⋙ b)`, where the
  rotate-right `x ⋙ n = (x >> n) | (x << (64-n))` is `SXor (SShr x n) (SShl x
  (64-n))` (the two shifted halves occupy disjoint bit positions for `0 < n <
  64`, so `|` = `⊕`).

Every constant (round constants, all-ones NOT mask, shift amounts) is a literal
(`SLit`) — the front materialises round constants / mask as `regConst` and the
shift counts as immediate `shrImm`/`shlImm` (both render-proven by the Sntrup
Barrett path). So the only SExpr operators used are `SXor`, `SAnd`, `SShl`,
`SShr` — all already lowered by the scalar front to 64-bit `catCryptDialect`
word ops.

## ABI (unchanged)

The deployed `Com jasminDialect inCtxt r64` keeps the 45-word input context the
owned render maps (`inp[0..4]` = the 5 state words `x₀ … x₄`, loaded from `RSI`;
the remaining slots are the permutation's immediates, which this front bakes as
literals so they stay unreferenced). The **last five bindings** are the front's
identity copies of `x₀ … x₄` in order, matching `toLprogPhysAbi`'s last-`nOut`
output convention. `bench/ascon_compare/ascon_owned_emit.lean` renders the SAME
`asconPaCom` / `asconPbCom` to owned AT&T `.s` (`Com.toLprogPhysAbi →
renderLprogAtt`) under the export symbols `ascon_pa` / `ascon_pb`.

## Gates

* In-model: the front translates + lowers (`asconP{a,b}Lowered_isSome`); every
  binding is a pure scalar-arith op — no `extCall`/`stackLoad`/`stackStore`
  (`ascon_pb_is_purearith_only`); the last five bindings are the output copies
  (`ascon_pb_last_five_bindings_are_copies`).
* External: `bench/ascon_compare` `ascon-kat` byte-checks the owned `.s`
  against the Ascon v1.2 / NIST SP 800-232 reference permutation.

The math source of truth is `CatCrypt/Crypto/Ascon/Permutation.lean`
(`ascon_add_const` / `ascon_sub_layer` / `ascon_linear_layer` / `ascon_round`).
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.AsconEmit

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)

set_option autoImplicit false

/-- The `reg 64` dialect type, abbreviated. -/
abbrev r64 : JasminTy := .reg 64

/-! ## 1. Ascon constants (kept for the owned-render ABI + downstream mentions) -/

/-- The number of state slots the ABI reserves: 5 words + 5 S-box temporaries +
    2 rotate scratch. (The front uses SSA temporaries, not a fixed slot file;
    this only fixes the input-context depth the owned render maps.) -/
abbrev numSlots : Nat := 12

/-- The base input index from which immediates are addressed (state words occupy
    `0 … 4`, then the ABI's scratch/immediate slots). -/
abbrev firstImm : Nat := numSlots

/-- The all-ones NOT mask immediate. -/
abbrev maskImm : Nat := 0xFFFFFFFFFFFFFFFF

/-- The round constant `0xf0 - i*0x0f`, `i ∈ [0,11]` (mirrors
    `Ascon.ascon_round_const`). -/
def roundConst (i : Nat) : Nat := 0xf0 - i * 0x0f

/-- The distinct immediates the permutation uses, in a fixed order: the all-ones
    NOT mask, the 12 round constants, and the 10 distinct rotate shift amounts
    with their complements. Kept so the owned render's `deriveImmSlots`/input
    context depth is unchanged; the front bakes these as literals directly, so
    the immediate input words are unreferenced. -/
def immList : List Nat :=
  [0xFFFFFFFFFFFFFFFF]
  ++ [0xf0, 0xe1, 0xd2, 0xc3, 0xb4, 0xa5, 0x96, 0x87, 0x78, 0x69, 0x5a, 0x4b]
  ++ [19, 28, 45, 36, 61, 39, 3, 25, 1, 6, 63, 58, 10, 17, 54, 47, 7, 41, 57, 23]

/-! ## 2. The straight-line `LowCT` permutation body -/

/-- Sequence a list of `LowCT` into an `RSeq` chain. -/
def seqAll : List LowCT → LowCT
  | [] => .RSkip
  | [c] => c
  | c :: cs => .RSeq c (seqAll cs)

/-- State-word slot name `x{i}`. -/
def xN (i : Nat) : String := "x" ++ toString i
/-- S-box temporary slot name `t{i}`. -/
def tN (i : Nat) : String := "t" ++ toString i
/-- Output-copy slot name `o{i}` (the last-five-bindings convention). -/
def oN (i : Nat) : String := "o" ++ toString i

/-- NOT of slot `v`: `v ⊕ 0xFFFF…FF`. -/
def notE (v : String) : SExpr := .SXor (.SVar v) (.SLit maskImm)

/-- Rotate-right of slot `v` by `n` (`0 < n < 64`): `(v >> n) | (v << (64-n))`,
    the two halves disjoint so `|` = `⊕`. Shift amounts are literals, so each
    shift lowers to the immediate `shrImm`/`shlImm`. -/
def rotRE (v : String) (n : Nat) : SExpr :=
  .SXor (.SShr (.SVar v) (.SLit n)) (.SShl (.SVar v) (.SLit (64 - n)))

/-- Round-constant add (`Ascon.ascon_add_const`): XOR round constant for round
    `r` into `x₂`. -/
def addConstStmt (r : Nat) : LowCT :=
  .RScalarSetExpr (xN 2) (.SXor (.SVar (xN 2)) (.SLit (roundConst r)))

/-- The bit-sliced Keccak-χ S-box (Ascon v1.2 / NIST SP 800-232 reference
    `ROUND`), in place on `x₀ … x₄` using temporaries `t₀ … t₄`:

    ```
    x0 ^= x4;  x4 ^= x3;  x2 ^= x1;
    t0 = x0 ^ (~x1 & x2);  t1 = x1 ^ (~x2 & x3);  t2 = x2 ^ (~x3 & x4);
    t3 = x3 ^ (~x4 & x0);  t4 = x4 ^ (~x0 & x1);      -- cyclic reads
    x0 = t0 ^ t4;  x1 = t1 ^ t0;  x2 = ~t2;  x3 = t3 ^ t2;  x4 = t4
    ```

    Each `RScalarSetExpr` rebinds its slot, so the cyclic `t3`/`t4` read the
    already-updated `x0`/`x1` snapshot — the standard χ form the official
    `round.h` / the verified `Ascon.ascon_sub_layer` and the `ascon-hax`
    extraction all match, and the KAT checks against. -/
def subLayerStmts : List LowCT :=
  [ .RScalarSetExpr (xN 0) (.SXor (.SVar (xN 0)) (.SVar (xN 4)))
  , .RScalarSetExpr (xN 4) (.SXor (.SVar (xN 4)) (.SVar (xN 3)))
  , .RScalarSetExpr (xN 2) (.SXor (.SVar (xN 2)) (.SVar (xN 1)))
  , .RScalarSetExpr (tN 0) (.SXor (.SVar (xN 0)) (.SAnd (notE (xN 1)) (.SVar (xN 2))))
  , .RScalarSetExpr (tN 1) (.SXor (.SVar (xN 1)) (.SAnd (notE (xN 2)) (.SVar (xN 3))))
  , .RScalarSetExpr (tN 2) (.SXor (.SVar (xN 2)) (.SAnd (notE (xN 3)) (.SVar (xN 4))))
  , .RScalarSetExpr (tN 3) (.SXor (.SVar (xN 3)) (.SAnd (notE (xN 4)) (.SVar (xN 0))))
  , .RScalarSetExpr (tN 4) (.SXor (.SVar (xN 4)) (.SAnd (notE (xN 0)) (.SVar (xN 1))))
  , .RScalarSetExpr (xN 0) (.SXor (.SVar (tN 0)) (.SVar (tN 4)))
  , .RScalarSetExpr (xN 1) (.SXor (.SVar (tN 1)) (.SVar (tN 0)))
  , .RScalarSetExpr (xN 2) (notE (tN 2))
  , .RScalarSetExpr (xN 3) (.SXor (.SVar (tN 3)) (.SVar (tN 2)))
  , .RScalarSetExpr (xN 4) (.SVar (tN 4)) ]

/-- Per-word linear diffusion `x ← x ⊕ (x ⋙ a) ⊕ (x ⋙ b)` (one
    `RScalarSetExpr`, so all three reads see the pre-update word). -/
def linWordStmt (v : String) (a b : Nat) : LowCT :=
  .RScalarSetExpr v (.SXor (.SXor (.SVar v) (rotRE v a)) (rotRE v b))

/-- Linear diffusion layer (`Ascon.ascon_linear_layer`) with the standard Ascon
    rotation constants. -/
def linLayerStmts : List LowCT :=
  [ linWordStmt (xN 0) 19 28
  , linWordStmt (xN 1) 61 39
  , linWordStmt (xN 2)  1  6
  , linWordStmt (xN 3) 10 17
  , linWordStmt (xN 4)  7 41 ]

/-- One full Ascon round for round index `r` (`Ascon.ascon_round`):
    constant-add, S-box, linear diffusion. -/
def roundStmts (r : Nat) : List LowCT :=
  addConstStmt r :: subLayerStmts ++ linLayerStmts

/-- Output staging: five identity copies `o[i] := x[i]`, each lowering to exactly
    ONE binding, so the **last five bindings** of the emitted `Com` carry
    `x₀ … x₄` in order (the `toLprogPhysAbi` last-`nOut` convention). -/
def outStageStmts : List LowCT :=
  (List.range 5).map (fun i => .RScalarSetExpr (oN i) (.SVar (xN i)))

/-- The full permutation body: `count` rounds starting at `startRound`, then the
    five output copies. -/
def asconBody (count startRound : Nat) : LowCT :=
  seqAll (((List.range count).flatMap (fun i => roundStmts (startRound + i)))
    ++ outStageStmts)

/-! ## 3. Source context + `VarMap` (head-first, depth `nInputs`)

Word `i` sits at De Bruijn index `i`: words `0 … 4` are the state `x₀ … x₄`
(read by the front), words `5 … nInputs-1` are the ABI's scratch/immediate slots
(unreferenced — the front bakes constants as literals). This is the exact layout
the owned render's `deriveInLoad nInputs 5 8` / `deriveImmSlots nInputs firstImm
immList` maps. -/

/-- Input context length: `numSlots` state/scratch slots + the immediates. -/
abbrev nInputs : Nat := numSlots + immList.length

/-- The 45 input word names, head-first: `x0 … x4` then unreferenced ABI slots. -/
def wordNames : List String :=
  [xN 0, xN 1, xN 2, xN 3, xN 4]
    ++ (List.range (nInputs - 5)).map (fun i => "d" ++ toString i)

/-- Bind a name list onto a `replicate`-`sword 64` context, first name = head. -/
def bindAll : (names : List String) → VarMap (List.replicate names.length (.sword 64))
  | [] => VarMap.empty
  | n :: ns => (bindAll ns).bind n

/-- The source context: `nInputs` `u64` scalar slots. -/
def srcCtx : Ctx := List.replicate nInputs (.sword 64)

/-- The source `VarMap` (word 0 = `x0` at the head). -/
def srcVM : VarMap srcCtx := bindAll wordNames

/-- The input context of the deployed `Com`: `nInputs` `r64` words. -/
abbrev inCtxt : Ctxt jasminDialect := List.replicate nInputs r64

/-! ## 4. The front-emitted permutations -/

/-- Push a permutation body through the `CProg`-free control front and cap with
    `ret o4` (the last output copy, the `Com`'s last binding). `none` if the
    front declines. -/
def frontComAt (count startRound : Nat) (name : String) :
    Option (Com catCryptDialect srcCtx (.sword 64)) :=
  match translateDialectControl srcVM (asconBody count startRound) with
  | some r =>
      match r.vm.lookup name with
      | some ⟨.sword 64, v⟩ => r.cont (Com.ret (toVIRVar v))
      | _ => none
  | none => none

/-- The front-emitted `p^b` (6 rounds, `6 … 11`), lowered to the jasmin dialect. -/
def asconPbLoweredOpt :=
  (frontComAt 6 6 (oN 4)).bind DialectToJasminCom.cryptoDialectToJasminCom

/-- The front-emitted `p^a` (12 rounds, `0 … 11`), lowered to the jasmin dialect. -/
def asconPaLoweredOpt :=
  (frontComAt 12 0 (oN 4)).bind DialectToJasminCom.cryptoDialectToJasminCom

/-- The `p^b` front translates and lowers end-to-end. -/
theorem asconPbLowered_isSome : asconPbLoweredOpt.isSome := by native_decide

/-- The `p^a` front translates and lowers end-to-end. -/
theorem asconPaLowered_isSome : asconPaLoweredOpt.isSome := by native_decide

/-- The deployed Ascon `p^b` permutation `Com jasminDialect` — FRONT-GENERATED
    (`translateDialectControl` + `cryptoDialectToJasminCom`), not hand-built.
    Rendered to owned `.s` by `bench/ascon_compare/ascon_owned_emit.lean` under
    the `ascon_pb` symbol. -/
def asconPbCom : Com jasminDialect inCtxt r64 :=
  asconPbLoweredOpt.get asconPbLowered_isSome

/-- The deployed Ascon `p^a` permutation `Com jasminDialect` — FRONT-GENERATED,
    rendered to owned `.s` under `ascon_pa`. -/
def asconPaCom : Com jasminDialect inCtxt r64 :=
  asconPaLoweredOpt.get asconPaLowered_isSome

/-! ## 5. Structural gates on the lowered `Com` (REV-12: cheap in-model only —
correctness is the external C KAT, not a `denote = spec` native_decide) -/

/-- Every binding is a pure scalar-arith op (`regArith`/`regConst`/immediate
    shift) — no `extCall`, no `stackLoad`/`stackStore` — so the denotation is
    exact BitVec word arithmetic. -/
def allPureArith : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → Bool
  | _, _, .ret _ => true
  | _, _, .var e body =>
    (match e.op with
     | .regArith _ _ => true
     | .regConst _ _ => true
     | .shlImm _ _ => true
     | .shrImm _ _ => true
     | _ => false) && allPureArith body

theorem ascon_pb_is_purearith_only : allPureArith asconPbCom = true := by
  native_decide

theorem ascon_pa_is_purearith_only : allPureArith asconPaCom = true := by
  native_decide

/-- Per-binding flag: is the binding the identity copy `shlImm 64 0` (the
    front's `RScalarSetExpr (o i) (SVar (x i))` output copy)? -/
def copyFlags : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → List Bool
  | _, _, .ret _ => []
  | _, _, .var e body =>
    (match e.op with | .shlImm 64 0 => true | _ => false) :: copyFlags body

/-- The **last five bindings** are identity copies — the `o[0..4]` output copies
    the owned render's last-`nOut` epilogue stores to `out[0..4]`. -/
theorem ascon_pb_last_five_bindings_are_copies :
    ((copyFlags asconPbCom).drop ((copyFlags asconPbCom).length - 5))
      = List.replicate 5 true := by native_decide

theorem ascon_pa_last_five_bindings_are_copies :
    ((copyFlags asconPaCom).drop ((copyFlags asconPaCom).length - 5))
      = List.replicate 5 true := by native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.AsconEmit
