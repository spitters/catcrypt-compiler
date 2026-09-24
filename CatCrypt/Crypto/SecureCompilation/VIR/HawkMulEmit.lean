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
# HAWK-256 negacyclic ring multiply: front-compiled emit + proof-model `Com`

**SUPERSEDED (for HAWK-512) by `HawkNttEmit.lean`.** This module carries the
schoolbook **negacyclic** ring multiply over `Z/1024[x]/(x^16 + 1)` — HAWK-256's
ring *shape* (power-of-two modulus, `x^N = -1` fold) at a small straight-line
degree `N = 16`. HAWK-512's byte-identical hot phase (mod-18433 NTT + pointwise
Montgomery) is emitted owned in `HawkNttEmit.lean` / the rolled
`HAWK/PointwiseMontymulRolledEmit.lean`. This file is kept for the HAWK-256
ring-shape kernel: the negacyclic sibling of `Ntruhrss701MulEmit`.

## Two `Com`s, one spec (read this)

* **`hawkMulFrontCom` (deployed)** — FRONT-GENERATED, no hand-built `Com`:

  ```
    mulBody (LowCT: RScalarSetExpr negacyclic schoolbook + `& 1023` mask)
      --(translateDialectControl)-->   Com catCryptDialect srcCtx (.sword 64)
      --(cryptoDialectToJasminCom)-->  hawkMulFrontCom : Com jasminDialect inCtxtF r64
  ```

  `HAWK/HawkMulEmit.lean` renders it to owned AT&T `.s` (symbol
  `hawk_mul`, no jasminc); `bench/hawk_compare/hawk_mul_kat.c` byte-KATs it
  against the independent negacyclic-convolution-mod-1024 reference.

* **`hawkMulCom` (proof model)** — the CPS-built straight-line `Com` whose
  **universal** denotation tie lives in `HawkMulComDenoteTie.lean`:
  `hawkMulCom.denote (encode a b) = embZ (hawkNegacyclicMul a b ⟨N-1⟩)` for
  **every** lane pair, per-coefficient for every `k < N`. It is verification
  content only — it renders no deployed artifact. Both `Com`s
  compute the same mathematical spec: the model ties to `hawkNegacyclicMul`
  universally; the front emit's `hawk_denote_spec` gates it against the same
  independent negacyclic `% 1024` reference on edge + random vectors, and the
  byte-KAT gates the rendered `.s`.

## The negacyclic multiply (the `x^N = -1` sign)

In `Z/q[x]/(x^N + 1)` the fold is `x^N ≡ -1`, so the wrapped half of the
convolution is **subtracted**:

  `out[k] = Σ_{i+j=k} a[i]·b[j]  −  Σ_{i+j=k+N} a[i]·b[j]   (mod q)`

Writing `j = (k − i) mod N`: the term `a[i]·b[(k−i+N) mod N]` is **positive**
when `i ≤ k` (no wrap, `i+j = k`) and **negative** when `i > k` (wrapped,
`i+j = k+N`, picking up the `x^N = -1` sign). The only difference from the
cyclic `Ntruhrss701MulEmit` kernel is the **sign on the wrapped terms**
(`sub` instead of `add`).

## Why the single end mask is exact

Each `out[k]` is a signed sum `P − M` with `P, M ≥ 0`, each
`≤ N·(q−1)² = 16·1023² ≈ 1.67e7`. The emitted words accumulate `P − M` with
wrapping word subtraction; because `q = 2^10` **divides** the word modulus,
masking with `& 1023` is a ring homomorphism onto `Z/q`, so the wrapped
accumulator masks to the correct negacyclic coefficient regardless of any
intermediate wrap.

## ABI of the deployed front emit

`inCtxtF` = 33 `r64` words: `0..15` = `a`, `16..31` = `b`, `32` = unused pad
(the mask `1023` is a front-materialised body constant). The 16 output words
are the **last 16 bindings** (identity copies of `o[0..15]` in order —
`toLprogPhysAbi`'s last-`nOut` convention). C side:
`uint64_t *hawk_mul(uint64_t *out, const uint64_t *inp)`, 8-byte stride.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.HawkMulEmit

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

/-- The `reg 32` dialect type, abbreviated (the proof-model word type). -/
abbrev r32 : JasminTy := .reg 32

/-- The `reg 64` dialect type, abbreviated (the front emit's word type). -/
abbrev r64 : JasminTy := .reg 64

/-- Ring degree of this straight-line kernel (`x^N + 1`). The true HAWK degree is
    `n ∈ {256, 512, 1024}`; this is the same code at `N = 16`. -/
abbrev N : Nat := 16

/-- The HAWK-256 coefficient modulus `q = 1024 = 2^10`; reduction is the single
    mask `& (q - 1) = & 1023`. -/
abbrev qMask : Nat := 1023

/-- Number of `u32` state slots of the proof model: `a` (16) + `b` (16) +
    `out` (16) + `scratch` (1) + mask-constant operand (1) = 50. -/
abbrev M : Nat := 50

/-! ## 1. Proof-model builder state

The model's input buffer holds `2*N = 32` `u32` words: `inp[0..15]` are the
coefficients of `a`, `inp[16..31]` the coefficients of `b` (each `< q`).
`BState Γ` carries one variable per state slot of `Γ`. These CPS builders are
the induction subjects of the universal denotation tie
(`HawkMulComDenoteTie.lean`); they render no deployed artifact. -/

/-- The `M` state slots as variables of `Γ` (slots `0..15` = `a`, `16..31` = `b`,
    `32..47` = `out`, `48` = scratch). -/
structure BState (Γ : Ctxt jasminDialect) where
  st : Fin M → Ctxt.Var Γ r32

/-- The fresh head variable of an extended context. -/
def headVar (Γ : Ctxt jasminDialect) : Ctxt.Var (r32 :: Γ) r32 := .here

/-! ## 2. Emit one `regArith` binding (CPS)

`emitOp` prepends one `regArith op 32` binding writing state slot `dst`, reading
source slots `a`/`b`, then continues building over the extended context with
slot `dst` rebound to the fresh head variable. -/

/-- Emit one `regArith op 32` binding writing state slot `dst`, reading source
    slots `a`/`b`, then continue with `k` over the extended context
    (slot `dst` ← fresh head). -/
def emitOp {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) (op : JasminBinOp) (dst a b : Fin M)
    (k : {Γ' : Ctxt jasminDialect} → BState Γ' → Com jasminDialect Γ' t) :
    Com jasminDialect Γ t :=
  let e : Expr jasminDialect Γ r32 :=
    { op := .regArith op 32
      retTy_eq := rfl
      args := .cons (st.st a) (.cons (st.st b) .nil) }
  let st' : BState (r32 :: Γ) :=
    { st := fun i => if i = dst then headVar Γ else (st.st i).there }
  .var e (k st')

/-! ## 3. The negacyclic convolution builder (proof model)

`(k - i) mod N` is the partner index of `a[i]` in `out[k]`. The term carries the
negacyclic **sign**: `+` when `i ≤ k` (no wrap), `−` when `i > k` (wrapped,
`x^N = -1`). We build the straight line via CPS recursion over the coefficient
and term indices. -/

/-- Continuation type: a `Com` builder polymorphic in the (extended) context. -/
abbrev Cont (t : JasminTy) := {Γ' : Ctxt jasminDialect} → BState Γ' → Com jasminDialect Γ' t

/-- Slot index of `a`'s coefficient `i` (`0..15`). -/
def aSlot (i : Nat) : Fin M :=
  ⟨i % N, by have h : i % N < N := Nat.mod_lt _ (by decide); show i % 16 < 50; omega⟩

/-- Slot index of `b`'s coefficient `j` (`16..31`). -/
def bSlot (j : Nat) : Fin M :=
  ⟨16 + j % N, by have h : j % N < N := Nat.mod_lt _ (by decide); show 16 + j % 16 < 50; omega⟩

/-- Slot index of `out`'s coefficient `k` (`32..47`). -/
def outSlot (k : Nat) : Fin M :=
  ⟨32 + k % N, by have h : k % N < N := Nat.mod_lt _ (by decide); show 32 + k % 16 < 50; omega⟩

/-- The scratch slot (`48`). -/
def scrSlot : Fin M := ⟨48, by decide⟩

/-- Partner index `(k - i) mod N` of `a[i]` in `out[k]`, computed on `Nat`
    (`k + N - i` avoids underflow since `i < N`). -/
def partner (k i : Nat) : Nat := (k + N - i) % N

/-- The accumulating tail for `out[k]`: emit the products with term index
    `i .. N-1` as `scratch = a[i]*b[partner k i]`, then either
    `out[k] += scratch` (positive, `i ≤ k`) or `out[k] -= scratch` (the
    negacyclic sign, `i > k`, since `x^N = -1`). -/
def emitCoeffTail {t : JasminTy} (k : Nat) :
    (i : Nat) → {Γ : Ctxt jasminDialect} → BState Γ → Cont t → Com jasminDialect Γ t
  | i, _, st, kont =>
    if i < N then
      emitOp st .mul scrSlot (aSlot i) (bSlot (partner k i)) fun st1 =>
      emitOp st1 (if i ≤ k then .add else .sub) (outSlot k) (outSlot k) scrSlot fun st2 =>
      emitCoeffTail k (i + 1) st2 kont
    else kont st
termination_by i => N - i

/-- Accumulate all `N` products into `out[k]`: the first (`i = 0`) is a `mul`
    written directly to `out[k]`'s slot (`a[0] * b[k mod N]`, always positive
    since `0 ≤ k`), then the tail (`i = 1 .. N-1`) accumulates through `scratch`
    with the negacyclic sign. -/
def emitCoeff {t : JasminTy} (k : Nat) {Γ : Ctxt jasminDialect}
    (st : BState Γ) (kont : Cont t) : Com jasminDialect Γ t :=
  emitOp st .mul (outSlot k) (aSlot 0) (bSlot (partner k 0)) fun st1 =>
  emitCoeffTail k 1 st1 kont

/-- Accumulate output coefficients `k .. N-1` in order. -/
def emitCoeffs {t : JasminTy} :
    (k : Nat) → {Γ : Ctxt jasminDialect} → BState Γ → Cont t → Com jasminDialect Γ t
  | k, _, st, kont =>
    if k < N then emitCoeff k st fun st1 => emitCoeffs (k + 1) st1 kont
    else kont st
termination_by k => N - k

/-- The mask-constant operand slot (`49`). Never written as a binding
    destination, so it stays bound to its initial input variable `inp[32]` (the
    model encodes the constant `1023` there). Keeping it separate from the
    scratch slot (`48`, which *is* written) keeps the mask a distinct operand. -/
def maskConstSlot : Fin M := ⟨49, by decide⟩

/-- Emit the `N` final mask bindings `out[k] = out[k] & 1023` for `k = 0 .. N-1`,
    in order (the last `N` bindings of the program). -/
def emitMasks {t : JasminTy} :
    (k : Nat) → {Γ : Ctxt jasminDialect} → BState Γ → Cont t → Com jasminDialect Γ t
  | k, _, st, kont =>
    if k < N then emitOp st .and (outSlot k) (outSlot k) maskConstSlot fun st1 =>
      emitMasks (k + 1) st1 kont
    else kont st
termination_by k => N - k

/-! ## 4. Model input context and the proof-model `Com` -/

/-- The model input context: `33` `r32` words (16 `a` + 16 `b` + 1 mask
    constant). -/
abbrev inCtxt : Ctxt jasminDialect := List.replicate 33 r32

/-- De Bruijn variable for input word `i` of a *replicate* `r32`-context of depth
    `m+1`. Out-of-range saturates at `.here` (never triggered). -/
def inputVar : (m : Nat) → Nat →
    @Ctxt.Var jasminDialect (List.replicate (m+1) r32) r32
  | _, 0 => .here
  | 0, _ => .here
  | (m+1), (k+1) => (inputVar m k).there

/-- Input word `i` of `inCtxt = List.replicate 33 r32`. -/
def inVar (i : Nat) : Ctxt.Var inCtxt r32 := inputVar 32 i

/-- The initial builder state over `inCtxt`. The `M = 50` state slots map onto the
    33 inputs: `a` slots `0..15 → inp[0..15]`, `b` slots `16..31 → inp[16..31]`,
    `out` slots `32..47` and `scratch` slot `48` are seeded to input `0` (their
    value is irrelevant — every `out[k]` is written by its first `mul` before any
    read, and `scratch` likewise). The mask-constant operand position
    (`maskConstSlot = 49`) is seeded to input `32` (the encoded `1023`). -/
def initBState : BState inCtxt where
  st := fun i =>
    if i.val < 32 then inVar i.val
    else if i.val = 49 then inVar 32   -- mask-constant operand ↦ inp 32 (= 1023)
    else inVar 0

/-- The **proof-model** degree-`N` negacyclic ring multiply as a
    `Com jasminDialect`: accumulate all `N` output coefficients (positive terms
    `i ≤ k`, negative terms `i > k`), then the `N` final mask bindings. Subject
    of the universal denotation tie `HawkMulComDenoteTie.hawkMulCom_denote_spec`
    (`∀` lane pairs, per-coefficient for every `k < N`). NOT the deployed emit —
    the deployed artifact is the front-generated `hawkMulFrontCom` below. -/
def hawkMulCom : Com jasminDialect inCtxt r32 :=
  emitCoeffs 0 initBState fun st =>
  emitMasks 0 st fun stf =>
  .ret (stf.st (outSlot (N - 1)))

/-! ## 5. The deployed emit, FRONT-COMPILED

The straight-line `LowCT` body of the same negacyclic schoolbook, pushed
through the dialect front (`translateDialectControl` →
`cryptoDialectToJasminCom`) — NO hand-built `Com` in the deployed path. -/

/-- Sequence a list of `LowCT` into an `RSeq` chain. -/
def seqAll : List LowCT → LowCT
  | [] => .RSkip
  | [c] => c
  | c :: cs => .RSeq c (seqAll cs)

/-- `a`-coefficient slot name. -/
def aN (i : Nat) : String := "a" ++ toString i
/-- `b`-coefficient slot name. -/
def bN (i : Nat) : String := "b" ++ toString i

/-- The negacyclic schoolbook accumulator expression for coefficient `k`: the
    first term `a[0]·b[k]` is always positive; each later term
    `a[i]·b[(k−i+N) mod N]` is added when `i ≤ k` and subtracted when `i > k`
    (the `x^N = -1` fold; the word subtraction wraps, and the final `& 1023`
    mask is exact because `1024` divides the word modulus). -/
def coeffSum (k : Nat) : SExpr :=
  (List.range (N - 1)).foldl
    (fun acc j =>
      let i := j + 1
      let term := SExpr.SMul (.SVar (aN i)) (.SVar (bN ((k + N - i) % N)))
      if i ≤ k then .SAdd acc term else .SSub acc term)
    (SExpr.SMul (.SVar (aN 0)) (.SVar (bN (k % N))))

/-- The statements for coefficient `k`: accumulate, then the single `& 1023`
    field mask (the mask constant is a literal — no input word is read for it). -/
def coeffStmts (k : Nat) : List LowCT :=
  let x := "x" ++ toString k
  let o := "o" ++ toString k
  [ .RScalarSetExpr x (coeffSum k),
    .RScalarSetExpr o (.SAnd (.SVar x) (.SLit qMask)) ]

/-- The full tile body: all `N` coefficient blocks, then the `N` output copies
    `f[k] := o[k]` — each lowering to exactly ONE binding, so the **last `N`
    bindings** carry `o[0..N−1]` in order. -/
def mulBody : LowCT := seqAll (
  ((List.range N).flatMap coeffStmts)
  ++ (List.range N).map (fun k =>
      .RScalarSetExpr ("f" ++ toString k) (.SVar ("o" ++ toString k))))

/-- The input words of the front emit, in word order (`0..32`). -/
def wordNames : List String :=
  (List.range N).map aN ++ (List.range N).map bN ++ ["pad32"]

/-- Bind a name list onto a `replicate`-`sword 64` context, first name = head. -/
def bindAll : (names : List String) → VarMap (List.replicate names.length (.sword 64))
  | [] => VarMap.empty
  | n :: ns => (bindAll ns).bind n

/-- The front source context: 33 `u64` scalar slots. -/
def srcCtx : Ctx := List.replicate 33 (.sword 64)

/-- The source `VarMap` (word 0 = `a[0]` at the head). -/
def srcVM : VarMap srcCtx := bindAll wordNames

/-- Push `mulBody` through the dialect control front and cap with
    `ret <name>`. `none` if the front declines. -/
def frontComAt (name : String) : Option (Com catCryptDialect srcCtx (.sword 64)) :=
  match translateDialectControl srcVM mulBody with
  | some r =>
      match r.vm.lookup name with
      | some ⟨.sword 64, v⟩ => r.cont (Com.ret (toVIRVar v))
      | _ => none
  | none => none

/-- The front-emitted tile, lowered to the jasmin dialect (capped at the final
    output copy `f15`, whose binding is the `Com`'s last). -/
def hawkLoweredOpt :=
  (frontComAt ("f" ++ toString (N - 1))).bind
    DialectToJasminCom.cryptoDialectToJasminCom

/-- The front translates and lowers end-to-end. -/
theorem hawkLowered_isSome : hawkLoweredOpt.isSome := by native_decide

/-- The front emit's input context: 33 `r64` words (16 `a` + 16 `b` + 1 unused
    pad word). -/
abbrev inCtxtF : Ctxt jasminDialect := List.replicate 33 r64

/-- The **deployed** HAWK-256 negacyclic ring-multiply tile — FRONT-GENERATED
    (`translateDialectControl` + `cryptoDialectToJasminCom`), not hand-built.
    Rendered to owned `.s` by `HAWK/HawkMulEmit.lean` under the `hawk_mul`
    symbol. -/
def hawkMulFrontCom : Com jasminDialect inCtxtF r64 :=
  hawkLoweredOpt.get hawkLowered_isSome

/-! ## 6. `denote = spec` vs the independent negacyclic-`% q` reference

`refCoeff` is the direct `Nat` transcription of `ref_hawk_mul` in
`hawk_mul_kat.c` — independent of the emitted accumulation shape. It is the
same mathematical spec (`hawkNegacyclicMul`) the proof model ties to
universally in `HawkMulComDenoteTie`. -/

/-- The independent reference coefficient: positive half minus wrapped half,
    mod `1024` (the pad `2^30` is a multiple of `1024` dominating the wrapped
    half `≤ 16·1023² < 2^24`, so the `Nat` subtraction is exact). -/
def refCoeff (a b : List Nat) (k : Nat) : Nat :=
  let pos := (List.range N).foldl (fun acc i =>
    if i ≤ k then acc + a.getD i 0 * b.getD ((k + N - i) % N) 0 else acc) 0
  let neg := (List.range N).foldl (fun acc i =>
    if k < i then acc + a.getD i 0 * b.getD ((k + N - i) % N) 0 else acc) 0
  (pos + 1073741824 - neg) % 1024

/-- Sample coefficient-vector pairs (each 16 coeffs `< q = 1024`): edges +
    pseudo-random. -/
def samples : List (List Nat × List Nat) :=
  [ ((List.range N).map (fun _ => 0), (List.range N).map (fun _ => 0)),
    ((List.range N).map (fun _ => 1023), (List.range N).map (fun _ => 1023)),
    ((List.range N).map (fun i => (i * 123 + 45) % 1024),
     (List.range N).map (fun i => (i * 321 + 7) % 1024)),
    ((List.range N).map (fun i => (i * i * 91 + 17) % 1024),
     (List.range N).map (fun i => (1023 - i * 37 % 1024) % 1024)) ]

/-- Build a head-first valuation from a positional word function (entry `j` of
    the `replicate`-context gets `g j`). -/
def mkVal (g : Nat → BitVec 64) :
    (n : Nat) → @Ctxt.Valuation catCryptDialect _ (List.replicate n (.sword 64))
  | 0 => .nil
  | n + 1 => .cons (g 0) (mkVal (fun j => g (j + 1)) n)

/-- The head-first source valuation of a sample: `a`, `b`, then the unused pad
    word (`0`, matching the KAT harness's `inp[32] = 0`). -/
def valOf (a b : List Nat) : @Ctxt.Valuation catCryptDialect _ srcCtx :=
  mkVal (fun i =>
    if i < 16 then BitVec.ofNat 64 (a.getD i 0)
    else if i < 32 then BitVec.ofNat 64 (b.getD (i - 16) 0)
    else 0) 33

/-- Denote the front program capped at slot `name` on a sample (result word). -/
def frontDenoteAt (name : String) (a b : List Nat) : Option (BitVec 64) :=
  (frontComAt name).map (fun c => c.denote (valOf a b))

/-- **denote = independent spec, all 16 output coefficients.** The front
    program capped at output copy `f[k]` denotes the independent negacyclic
    convolution `% 1024` reference on every sample — the 16 values the owned
    render's last-16-bindings epilogue stores to `out[0..15]`. -/
theorem hawk_denote_spec :
    samples.all (fun (a, b) =>
      (List.range N).all (fun k =>
        frontDenoteAt ("f" ++ toString k) a b
          == some (BitVec.ofNat 64 (refCoeff a b k)))) = true := by
  native_decide

/-! ## 7. Structural gates on the lowered `Com` -/

/-- Every binding is a pure scalar-arith op (`regArith`/`regConst`/immediate
    shift) — no `extCall`, no `stackLoad`/`stackStore`. -/
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

theorem hawk_is_purearith_only : allPureArith hawkMulFrontCom = true := by
  native_decide

/-- Per-binding flag: is the binding the identity copy `shlImm 64 0`? -/
def copyFlags : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → List Bool
  | _, _, .ret _ => []
  | _, _, .var e body =>
    (match e.op with | .shlImm 64 0 => true | _ => false) :: copyFlags body

/-- The **last 16 bindings** are identity copies — the `f[0..15]` output
    copies the owned render's last-`nOut` epilogue stores to `out[0..15]`. -/
theorem hawk_last_bindings_are_copies :
    ((copyFlags hawkMulFrontCom).drop ((copyFlags hawkMulFrontCom).length - N))
      = List.replicate N true := by native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.HawkMulEmit
