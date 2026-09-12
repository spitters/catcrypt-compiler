/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3CompressEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3HashLeafEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3NttLayerEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3FriFoldEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.ComInlineCall

/-!
# `Com jasminDialect` leaf-fusion for the Plonky3 orchestration

The Plonky3 whole-prover orchestration loops (`Plonky3OrchLoopsEmit`) build each
per-iteration leaf invocation as a lowered `LinstrR.Lcall` inside a `loopLcmd`
back-edge — below the `Com jasminDialect` level. The proven leaf-fusion pass
`ComInlineCall.inlineCalls` / `inlineCallCom` consumes `extCall` nodes at the
`Com` level, so it cannot fire on the lowered form.

This module supplies the `Com`-level layer the fusion consumes for the five owned
Plonky3 phase leaves. Each leaf is emitted by its own module as a
`Com jasminDialect (List.replicate n (.reg 64)) (.reg 64)`:

| leaf `FunBodyN` | leaf `Com`                            | `argTys`               | `retTy`   |
|-----------------|---------------------------------------|------------------------|-----------|
| `compressFb`    | `Plonky3CompressEmit.compressComFinal`| `replicate 15 (.reg 64)` | `.reg 64` |
| `hashLeafFb`    | `Plonky3HashLeafEmit.hashLeafCom`     | `replicate 8 (.reg 64)`  | `.reg 64` |
| `nttLayerFb`    | `Plonky3NttLayerEmit.layerCom`        | `replicate 18 (.reg 64)` | `.reg 64` |
| `friFoldFb`     | `Plonky3FriFoldEmit.friFoldCom`       | `replicate 16 (.reg 64)` | `.reg 64` |
| `bbInvFb`       | `Plonky3FriFoldEmit.bbInvCom`         | `replicate 16 (.reg 64)` | `.reg 64` |

## Main results

* `compressFb … bbInvFb` — each phase leaf packaged as a `ComInlineCall.FunBodyN`.
* `<leaf>_inlineCallCom_denote` — the per-call-site fusion denotation law: inlining
  the leaf at a call site (`inlineCallCom <leaf>.body args body`) yields a call-free
  `Com` whose denotation binds the leaf's real value `<leaf>.body.denote args` at the
  head and continues with `body`. A direct instance of
  `ComInlineCall.inlineCallCom_denote`; leaf-agnostic, no registry-consistency side
  condition.
* `compressCallBody` — a `Com jasminDialect` orchestration loop-body carrying a
  single `extCall plonky3_merkle_compress_rc` node (the `Com`-level image of the
  linked `Lcall` the loop body issues), generic in the surrounding context and args.
* `compressCallBodyFused` / `compressCallBodyFused_denote` — the same loop-body with
  the leaf spliced in (the ABI `(out, in)` copy eliminated), and its denotation:
  exactly the leaf value on the call args.
* `plonky3LeafRegistry` — the `ComInlineCall.FuncRegistryN` mapping the five leaf
  names to their `FunBodyN`.
* `compressCallBodyInlined` — the whole-`Com` pass `inlineCalls plonky3LeafRegistry`
  applied to the with-call loop-body, producing a call-free `Com`.
* `plonky3_inlineCalls_denote` — the whole-prover fusion preservation law: for any
  orchestration `Com`, the five-leaf inliner denotes to the substituted interpreter
  binding each registered leaf call to the leaf `Com`'s real value. An instance of the
  leaf-agnostic `ComInlineCall.inlineCalls_denote_eq_denoteSubst`; no consistency side
  condition.
* `compressCallBodyInlined_denote` — the concrete consequence: the whole-`Com`-inlined
  compress loop-body denotes exactly the compress leaf value, agreeing with the per-site
  `compressCallBodyFused_denote`.

## The `jasminExtSem` boundary

`jasminExtSem` returns `JasminTy.default` for a `.reg 64` return (only width-16
`stackArr` lattice leaves carry a real arm). So `ComInlineCall.CalleeConsistent name
fb` — which requires `fb.body.denote = jasminExtSem name …` — is refutable for these
width-64 leaves, and the consistency-gated route
`ComInlineCall.inlineCalls_preserves_denote` (via `RegistryConsistentN`) does not
apply to the Plonky3 leaves. The whole-`Com` fusion for them is the leaf-agnostic
`ComInlineCall.inlineCalls_denote_eq_denoteSubst`: it carries no consistency
hypothesis and characterizes the inlined program's denotation by the substituted
interpreter `denoteSubst`, which binds each registered leaf call to the leaf `Com`'s
real value rather than the opaque `jasminExtSem` default. `compressCallBody_denote_opaque`
records the opaque dialect-level value of the with-call node for contrast.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Plonky3OrchComFuse

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ComInlineCall

/-! ## 1. Each Plonky3 phase leaf as a `FunBodyN` -/

/-- The Merkle compress leaf packaged as a `FunBodyN` (15 words in, 1 word out). -/
def compressFb : FunBodyN where
  argTys := Plonky3CompressEmit.inCtxt
  retTy  := Plonky3CompressEmit.r64
  body   := Plonky3CompressEmit.compressComFinal

/-- The Merkle leaf-hash leaf packaged as a `FunBodyN` (8 words in, 1 word out). -/
def hashLeafFb : FunBodyN where
  argTys := Plonky3HashLeafEmit.inCtxt
  retTy  := Plonky3HashLeafEmit.r64
  body   := Plonky3HashLeafEmit.hashLeafCom

/-- The NTT layer leaf packaged as a `FunBodyN` (18 words in, 1 word out). -/
def nttLayerFb : FunBodyN where
  argTys := Plonky3NttLayerEmit.inCtxt
  retTy  := Plonky3NttLayerEmit.r64
  body   := Plonky3NttLayerEmit.layerCom

/-- The FRI fold leaf packaged as a `FunBodyN` (16 words in, 1 word out). -/
def friFoldFb : FunBodyN where
  argTys := Plonky3FriFoldEmit.inCtxt
  retTy  := Plonky3FriFoldEmit.r64
  body   := Plonky3FriFoldEmit.friFoldCom

/-- The BabyBear inverse leaf packaged as a `FunBodyN` (16 words in, 1 word out). -/
def bbInvFb : FunBodyN where
  argTys := Plonky3FriFoldEmit.inCtxt
  retTy  := Plonky3FriFoldEmit.r64
  body   := Plonky3FriFoldEmit.bbInvCom

/-! ## 2. The per-call-site fusion denotation law for each leaf

`inlineCallCom <leaf>.body args body` splices the leaf `Com` at the call site,
binding the leaf's result at the head and continuing with `body`. The denotation
binds the leaf's real value on the call args — the ABI `(out, in)` copy eliminated,
with the leaf value unchanged. Leaf-agnostic (a direct instance of
`ComInlineCall.inlineCallCom_denote`); no registry-consistency side condition. -/

theorem compress_inlineCallCom_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (args : HVector (fun ty => Ctxt.Var Γ ty) compressFb.argTys)
    (body : Com jasminDialect (compressFb.retTy :: Γ) t)
    (V : Ctxt.Valuation Γ) :
    (inlineCallCom compressFb.body args body).denote V
      = body.denote (Ctxt.Valuation.extend V
          (compressFb.body.denote (Expr.lookupArgs args V))) :=
  inlineCallCom_denote compressFb.body args body V

theorem hashLeaf_inlineCallCom_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (args : HVector (fun ty => Ctxt.Var Γ ty) hashLeafFb.argTys)
    (body : Com jasminDialect (hashLeafFb.retTy :: Γ) t)
    (V : Ctxt.Valuation Γ) :
    (inlineCallCom hashLeafFb.body args body).denote V
      = body.denote (Ctxt.Valuation.extend V
          (hashLeafFb.body.denote (Expr.lookupArgs args V))) :=
  inlineCallCom_denote hashLeafFb.body args body V

theorem nttLayer_inlineCallCom_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (args : HVector (fun ty => Ctxt.Var Γ ty) nttLayerFb.argTys)
    (body : Com jasminDialect (nttLayerFb.retTy :: Γ) t)
    (V : Ctxt.Valuation Γ) :
    (inlineCallCom nttLayerFb.body args body).denote V
      = body.denote (Ctxt.Valuation.extend V
          (nttLayerFb.body.denote (Expr.lookupArgs args V))) :=
  inlineCallCom_denote nttLayerFb.body args body V

theorem friFold_inlineCallCom_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (args : HVector (fun ty => Ctxt.Var Γ ty) friFoldFb.argTys)
    (body : Com jasminDialect (friFoldFb.retTy :: Γ) t)
    (V : Ctxt.Valuation Γ) :
    (inlineCallCom friFoldFb.body args body).denote V
      = body.denote (Ctxt.Valuation.extend V
          (friFoldFb.body.denote (Expr.lookupArgs args V))) :=
  inlineCallCom_denote friFoldFb.body args body V

theorem bbInv_inlineCallCom_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (args : HVector (fun ty => Ctxt.Var Γ ty) bbInvFb.argTys)
    (body : Com jasminDialect (bbInvFb.retTy :: Γ) t)
    (V : Ctxt.Valuation Γ) :
    (inlineCallCom bbInvFb.body args body).denote V
      = body.denote (Ctxt.Valuation.extend V
          (bbInvFb.body.denote (Expr.lookupArgs args V))) :=
  inlineCallCom_denote bbInvFb.body args body V

/-! ## 3. A `Com`-level orchestration loop-body carrying an `extCall` node -/

/-- The Merkle compress leaf's export symbol. -/
def compressName : String := "plonky3_merkle_compress_rc"

/-- A `Com jasminDialect` orchestration loop-body: one iteration issues
    `extCall plonky3_merkle_compress_rc(args)` and returns the digest word. This is
    the `Com`-level node the ABI lowers to the linked `Lcall` the deployed loop body
    issues — the with-call form the fusion eliminates. Generic in the surrounding
    context `Γ` and the call args. -/
def compressCallBody {Γ : Ctxt jasminDialect}
    (args : HVector (fun ty => Ctxt.Var Γ ty) compressFb.argTys) :
    Com jasminDialect Γ (.reg 64) :=
  Com.var (callExpr compressName args) (Com.ret .here)

/-- **The with-call node is opaque at the dialect level** — `jasminExtSem` returns
    the default for a `.reg 64` return, so the loop-body denotes `JasminTy.default`.
    The real leaf value is supplied only by the inlining (`compressCallBodyFused`),
    not by `jasminExtSem`. -/
theorem compressCallBody_denote_opaque {Γ : Ctxt jasminDialect}
    (args : HVector (fun ty => Ctxt.Var Γ ty) compressFb.argTys)
    (V : Ctxt.Valuation Γ) :
    (compressCallBody args).denote V = JasminTy.default (.reg 64) := rfl

/-- The compress loop-body with the leaf spliced in: the ABI `(out, in)` copy
    eliminated, the leaf `Com` inlined ahead of the return. Call-free. -/
def compressCallBodyFused {Γ : Ctxt jasminDialect}
    (args : HVector (fun ty => Ctxt.Var Γ ty) compressFb.argTys) :
    Com jasminDialect Γ (.reg 64) :=
  inlineCallCom compressFb.body args (Com.ret .here)

/-- **The fused loop-body denotes exactly the leaf value on the call args.** The
    ABI copy is gone and the digest word is unchanged. -/
theorem compressCallBodyFused_denote {Γ : Ctxt jasminDialect}
    (args : HVector (fun ty => Ctxt.Var Γ ty) compressFb.argTys)
    (V : Ctxt.Valuation Γ) :
    (compressCallBodyFused args).denote V
      = compressFb.body.denote (Expr.lookupArgs args V) := by
  unfold compressCallBodyFused
  rw [inlineCallCom_denote]
  rfl

/-! ## 4. The Plonky3 phase-leaf registry and the whole-`Com` pass -/

/-- The `FuncRegistryN` mapping the five Plonky3 phase-leaf export symbols to their
    `FunBodyN`. Feeds the whole-`Com` single-pass inliner `ComInlineCall.inlineCalls`. -/
def plonky3LeafRegistry : FuncRegistryN := fun name =>
  if name = "plonky3_merkle_compress_rc" then some compressFb
  else if name = "plonky3_merkle_hash_leaf_rc" then some hashLeafFb
  else if name = "plonky3_ntt_layer8_rc" then some nttLayerFb
  else if name = "fri_fold_rc" then some friFoldFb
  else if name = "bb_inv_rc" then some bbInvFb
  else none

/-- The whole-`Com` single-pass inliner applied to the compress loop-body: every
    registered head `extCall` is replaced by the callee's spliced-in body, yielding
    a call-free `Com`. -/
def compressCallBodyInlined {Γ : Ctxt jasminDialect}
    (args : HVector (fun ty => Ctxt.Var Γ ty) compressFb.argTys) :
    Com jasminDialect Γ (.reg 64) :=
  inlineCalls plonky3LeafRegistry (compressCallBody args)

/-! ## 5. Whole-`Com` fusion preservation for the five-leaf registry

The width-64 Plonky3 leaves have no real `jasminExtSem` arm, so `RegistryConsistentN
plonky3LeafRegistry` is refutable and `ComInlineCall.inlineCalls_preserves_denote`
does not apply. The leaf-agnostic `ComInlineCall.inlineCalls_denote_eq_denoteSubst`
does: the whole-`Com` inliner `inlineCalls plonky3LeafRegistry` denotes to
`ComInlineCall.denoteSubst plonky3LeafRegistry`, which binds each registered head
`extCall` node to its callee `Com`'s own value rather than to the opaque
`jasminExtSem` default. -/

/-- **Whole-prover fusion preservation.** For any orchestration `Com`, the whole-`Com`
    inliner over the five-leaf registry denotes to the substituted interpreter that
    binds each registered leaf call to the leaf `Com`'s real value. No
    registry-consistency side condition, so it holds for these `.reg 64` leaves. -/
theorem plonky3_inlineCalls_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (V : Ctxt.Valuation Γ) :
    (inlineCalls plonky3LeafRegistry c).denote V
      = denoteSubst plonky3LeafRegistry c V :=
  inlineCalls_denote_eq_denoteSubst plonky3LeafRegistry c V

/-- **The whole-`Com`-inlined compress loop-body denotes exactly the leaf value.** The
    single-pass inliner turns the with-call loop-body into a call-free `Com` whose
    denotation is the real compress leaf value on the call args — agreeing with the
    per-site `compressCallBodyFused_denote`, established via the leaf-agnostic
    whole-`Com` law with no consistency hypothesis. -/
theorem compressCallBodyInlined_denote {Γ : Ctxt jasminDialect}
    (args : HVector (fun ty => Ctxt.Var Γ ty) compressFb.argTys)
    (V : Ctxt.Valuation Γ) :
    (compressCallBodyInlined args).denote V
      = compressFb.body.denote (Expr.lookupArgs args V) := by
  unfold compressCallBodyInlined
  rw [plonky3_inlineCalls_denote]
  unfold compressCallBody
  exact denoteSubst_matchedCall plonky3LeafRegistry compressName compressFb args rfl V

end CatCrypt.Crypto.SecureCompilation.VIR.Plonky3OrchComFuse
