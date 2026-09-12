/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminBufferReuse
public import CatCrypt.Crypto.SecureCompilation.VIR.ComInlineCall

/-!
# Soundness of the in-place buffer reuse in the jasmin ABI emitter

`JasminAbiEmit` emits jasminc-valid `.jazz` for a `Com jasminDialect` under the
standard in-place pointer ABI: a stack-array binding is realised by writing the
result into the buffer that already holds the binding's first argument, rather
than into a fresh buffer. Reusing that storage is sound exactly when the first
argument is not read again, and this file supplies the predicate and the
agreement theorem. Of the emitter's arms, `emitBodyRegPtr` performs the reuse
(gated on `JasminAbiEmit.comUsesIdx`) while `emitBody` allocates a fresh buffer
per binding.

The scope is faithfulness of the emitted jasmin **source text** against the `Com`
it was produced from; jasminc is trusted downstream of that text. The owned byte
path (`Com.toLprogPhysAbi → renderLprogAtt`, and
`Com.toLprogPhysAbi → gatherJBlock6 → composeValidated → encodeJBlock6`) is a
separate route and does not go through jasminc.

## The model

The emitted text is a chain of buffer assignments, so the in-place realisation is
modelled at the valuation level: at a binding whose result reuses the buffer of
its first argument `a`, the continuation runs on a valuation in which **both** the
new SSA slot and `a`'s slot hold the result (`JasminBufferReuse.valUpdate` performs
the one-slot overwrite). `Com.denote` instead leaves `a` at its old value. The two
agree precisely when nothing downstream reads `a`.

## Main results

* `hvHeadAt` — the head argument of an argument vector, when its type is the
  binding's result type.
* `reuseSlot` — the buffer a binding reuses: the head argument, when the result
  is a stack array of the head argument's own type; `none` otherwise.
* `stepVal` / `denoteInPlace` — the in-place realisation's valuation step and
  denotation.
* `SlotDeadAfter` / `InPlaceLinear` — the side condition: at every reusing
  binding the reused buffer is `JasminBufferReuse.BodyAvoidsBuffer` in the
  continuation (no later argument and no later `ret` reads it).
* `inPlaceLinearB` — the `Bool` form of `InPlaceLinear`, phrased with the
  emitter's own de Bruijn occurrence check `JasminAbiEmit.comUsesIdx`.
* `inPlaceLinear_of_inPlaceLinearB` / `inPlaceLinearB_of_inPlaceLinear` — the two
  directions relating the `Bool` check and the semantic predicate.
* `denoteInPlace_eq_denote` — under `InPlaceLinear`, the in-place realisation
  denotes to the `Com`'s denotation.
* `denoteInPlace_eq_denote_of_linearB` — the same conclusion from the `Bool` check.
* `denoteInPlace_eq_inlined` — the leaf-parametric form: under
  `ComInlineCall.RegistryConsistentN`, the in-place realisation of a call-carrying
  `Com` denotes to the call-free inlined program.
* `slotDeadAfter_of_headIdx_unused` — the gate `emitBodyRegPtr` computes
  (`hvHeadIdx e.args = some i` and `comUsesIdx (i + 1) body = false`) discharges
  `SlotDeadAfter`.

`denoteInPlace_eq_denote` treats every op, `extCall` included, as a black box: it
never unfolds a leaf's denotation. The per-leaf obligation enters only through
`denoteInPlace_eq_inlined`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiInPlaceSound

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminBufferReuse
open CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiEmit
  (varIdx hvHeadIdx hvUsesIdx comUsesIdx)

/-! ## 1. Which buffer a binding reuses -/

/-- The head variable of an argument vector, when its type is `tRes`. `none` for
    an empty vector or a head of a different type. -/
def hvHeadAt {Γ : Ctxt jasminDialect} (tRes : JasminTy) :
    {tys : List JasminTy} → HVector (fun ty => Ctxt.Var Γ ty) tys →
    Option (Ctxt.Var Γ tRes)
  | [], _ => none
  | ty :: _, .cons v _ => if h : ty = tRes then some (h ▸ v) else none

/-- The buffer a binding's result reuses under the in-place ABI: its first
    argument, when the result is a stack array and the first argument has that
    same array type. A non-array result, an argument-free op, and a heterogeneous
    leaf whose first argument has a different type all reuse nothing. -/
def reuseSlot {Γ : Ctxt jasminDialect} : (tRes : JasminTy) →
    Expr jasminDialect Γ tRes → Option (Ctxt.Var Γ tRes)
  | .stackArr w n, e => hvHeadAt (.stackArr w n) e.args
  | .reg _, _ => none
  | .inlineInt, _ => none
  | .bool, _ => none

/-! ## 2. The in-place realisation -/

/-- The valuation the in-place realisation hands to the continuation of a
    binding. At a reusing binding the result is written both to the new SSA slot
    and to the reused buffer's slot; otherwise only the new slot is added. -/
def stepVal {Γ : Ctxt jasminDialect} (tEx : JasminTy) (e : Expr jasminDialect Γ tEx)
    (V : Ctxt.Valuation Γ) : Ctxt.Valuation (tEx :: Γ) :=
  (match reuseSlot tEx e with
    | some a => valUpdate V a (e.denote V)
    | none => V).extend (e.denote V)

/-- Denotation of the in-place realisation of a `Com`: the same walk as
    `Com.denote`, stepping the valuation with `stepVal` so that a reusing
    binding's result overwrites the reused buffer. -/
def denoteInPlace : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → Ctxt.Valuation Γ → ⟦t⟧
  | _, _, .ret v, V => v.lookup V
  | _, _, .var (t := tEx) e body, V => denoteInPlace body (stepVal tEx e V)

/-! ## 3. The side condition -/

/-- The deadness obligation carried by one binding's reused slot: for a stack
    array, the reused buffer (shifted under the binder) is avoided by the whole
    continuation — no later expression argument and no later `ret` reads it. The
    non-array types carry no obligation, since `reuseSlot` reuses nothing there. -/
def SlotDeadAfter {Γ : Ctxt jasminDialect} : (tEx : JasminTy) →
    Ctxt.Var Γ tEx → {t : JasminTy} → Com jasminDialect (tEx :: Γ) t → Prop
  | .stackArr w n, a, _, body =>
      BodyAvoidsBuffer (Ctxt.Var.there (s := JasminTy.stackArr w n) a) body
  | .reg _, _, _, _ => True
  | .inlineInt, _, _, _ => True
  | .bool, _, _, _ => True

/-- **Single-use linearity of the SSA let-chain for in-place reuse.** Every
    binding that reuses a buffer reuses one that is dead in the rest of the
    chain. This is the property the in-place ABI needs: an argument whose buffer
    is overwritten must have no later reader. -/
def InPlaceLinear : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → Prop
  | _, _, .ret _ => True
  | _, _, .var (t := tEx) e body =>
      (∀ a, reuseSlot tEx e = some a → SlotDeadAfter tEx a body) ∧ InPlaceLinear body

/-! ## 4. Agreement -/

/-- Overwriting the buffer `a` and extending with the result gives a valuation
    that agrees, off the shifted `a`, with the plain extension. -/
theorem agreeOff_valUpdate_extend {Γ : Ctxt jasminDialect} {w n : Nat}
    (a : Ctxt.Var Γ (.stackArr w n)) (V : Ctxt.Valuation Γ)
    (x res : ⟦JasminTy.stackArr w n⟧) :
    AgreeOff (Ctxt.Var.there (s := JasminTy.stackArr w n) a)
      ((valUpdate V a x).extend res) (V.extend res) := by
  intro t v hv
  cases v with
  | here => rfl
  | there v' =>
      show Ctxt.Var.lookup v' (valUpdate V a x) = v'.lookup V
      exact valUpdate_lookup_other V a v' (NotBuffer.of_there hv) x

/-- Overwriting a buffer that the continuation avoids does not change what the
    continuation denotes. -/
theorem denote_reuse_eq {Γ : Ctxt jasminDialect} {w n : Nat}
    (a : Ctxt.Var Γ (.stackArr w n)) {t : JasminTy}
    (body : Com jasminDialect (JasminTy.stackArr w n :: Γ) t)
    (hDead : BodyAvoidsBuffer (Ctxt.Var.there (s := JasminTy.stackArr w n) a) body)
    (V : Ctxt.Valuation Γ) (x res : ⟦JasminTy.stackArr w n⟧) :
    body.denote ((valUpdate V a x).extend res) = body.denote (V.extend res) :=
  denote_agreeOff_all _ body hDead (agreeOff_valUpdate_extend a V x res)

/-- One step of the in-place realisation agrees with one step of `Com.denote`,
    given the binding's deadness obligation. -/
theorem denote_stepVal {Γ : Ctxt jasminDialect} (tEx : JasminTy)
    (e : Expr jasminDialect Γ tEx) {t : JasminTy}
    (body : Com jasminDialect (tEx :: Γ) t)
    (hDead : ∀ a, reuseSlot tEx e = some a → SlotDeadAfter tEx a body)
    (V : Ctxt.Valuation Γ) :
    body.denote (stepVal tEx e V) = body.denote (V.extend (e.denote V)) := by
  cases tEx with
  | reg w => simp only [stepVal, reuseSlot]
  | inlineInt => simp only [stepVal, reuseSlot]
  | bool => simp only [stepVal, reuseSlot]
  | stackArr w n =>
      cases hr : reuseSlot (JasminTy.stackArr w n) e with
      | none => simp only [stepVal, hr]
      | some a =>
          simp only [stepVal, hr]
          exact denote_reuse_eq a body (hDead a hr) V _ _

/-- **The in-place realisation denotes the `Com`.** When every reusing binding
    reuses a buffer that is dead in the rest of the chain, running the chain with
    each result written into its first argument's buffer produces the `Com`'s
    denotation. -/
theorem denoteInPlace_eq_denote :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → (c : Com jasminDialect Γ t) →
    InPlaceLinear c → (V : Ctxt.Valuation Γ) → denoteInPlace c V = c.denote V
  | _, _, .ret _, _, _ => rfl
  | _, _, .var (t := tEx) e body, hLin, V => by
      obtain ⟨hDead, hBody⟩ := hLin
      show denoteInPlace body (stepVal tEx e V) = body.denote (V.extend (e.denote V))
      rw [denoteInPlace_eq_denote body hBody, denote_stepVal tEx e body hDead V]

/-! ## 5. The `Bool` form, phrased with the emitter's occurrence check -/

/-- Equal de Bruijn indices force equal types and equal variables. -/
theorem eq_of_varIdx_eq :
    {Γ : Ctxt jasminDialect} → {t tB : JasminTy} →
    (v : Ctxt.Var Γ t) → (B : Ctxt.Var Γ tB) →
    varIdx v = varIdx B → ∃ h : t = tB, h ▸ v = B
  | _, _, _, .here, .here, _ => ⟨rfl, rfl⟩
  | _, _, _, .here, .there _, h => by simp [varIdx] at h
  | _, _, _, .there _, .here, h => by simp [varIdx] at h
  | _, _, _, .there v', .there B', h => by
      obtain ⟨hty, hv⟩ := eq_of_varIdx_eq v' B' (by simpa [varIdx] using h)
      subst hty
      exact ⟨rfl, by simpa using congrArg Ctxt.Var.there hv⟩

/-- A variable whose de Bruijn index differs from the buffer's is not the
    buffer. -/
theorem notBuffer_of_varIdx_ne {Γ : Ctxt jasminDialect} {wB nB : Nat}
    (B : Ctxt.Var Γ (.stackArr wB nB)) {t : JasminTy} (v : Ctxt.Var Γ t)
    (h : varIdx v ≠ varIdx B) : NotBuffer B v := by
  intro hty
  subst hty
  intro he
  exact h (congrArg varIdx he)

/-- A variable that is not the buffer has a different de Bruijn index. -/
theorem varIdx_ne_of_notBuffer {Γ : Ctxt jasminDialect} {wB nB : Nat}
    (B : Ctxt.Var Γ (.stackArr wB nB)) {t : JasminTy} (v : Ctxt.Var Γ t)
    (h : NotBuffer B v) : varIdx v ≠ varIdx B := by
  intro hidx
  obtain ⟨hty, hv⟩ := eq_of_varIdx_eq v B hidx
  exact h hty hv

/-- An argument vector whose entries all miss the buffer's index is
    `ArgsNotBuffer`. -/
theorem argsNotBuffer_of_hvUsesIdx {Γ : Ctxt jasminDialect} {wB nB : Nat}
    (B : Ctxt.Var Γ (.stackArr wB nB)) :
    {tys : List JasminTy} → (args : HVector (fun ty => Ctxt.Var Γ ty) tys) →
    hvUsesIdx (varIdx B) args = false → ArgsNotBuffer B args
  | [], .nil, _ => trivial
  | _ :: _, .cons v rest, h => by
      have h' : ((varIdx v == varIdx B) || hvUsesIdx (varIdx B) rest) = false := h
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h'
      exact ⟨notBuffer_of_varIdx_ne B v h'.1, argsNotBuffer_of_hvUsesIdx B rest h'.2⟩

/-- Conversely, an `ArgsNotBuffer` vector misses the buffer's index. -/
theorem hvUsesIdx_of_argsNotBuffer {Γ : Ctxt jasminDialect} {wB nB : Nat}
    (B : Ctxt.Var Γ (.stackArr wB nB)) :
    {tys : List JasminTy} → (args : HVector (fun ty => Ctxt.Var Γ ty) tys) →
    ArgsNotBuffer B args → hvUsesIdx (varIdx B) args = false
  | [], .nil, _ => rfl
  | _ :: _, .cons v rest, h => by
      show ((varIdx v == varIdx B) || hvUsesIdx (varIdx B) rest) = false
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]
      exact ⟨varIdx_ne_of_notBuffer B v h.1, hvUsesIdx_of_argsNotBuffer B rest h.2⟩

/-- **The emitter's occurrence check is the deadness predicate.** A buffer whose
    de Bruijn index `comUsesIdx` does not find in the continuation is avoided by
    it in the sense of `BodyAvoidsBuffer`. -/
theorem bodyAvoidsBuffer_of_comUsesIdx {wB nB : Nat} :
    {Γ : Ctxt jasminDialect} → (B : Ctxt.Var Γ (.stackArr wB nB)) → {t : JasminTy} →
    (c : Com jasminDialect Γ t) →
    comUsesIdx (varIdx B) c = false → BodyAvoidsBuffer B c
  | _, B, _, .ret v, h => by
      simp only [comUsesIdx, beq_eq_false_iff_ne] at h
      exact notBuffer_of_varIdx_ne B v h
  | _, B, _, .var (t := tEx) e body, h => by
      simp only [comUsesIdx, Bool.or_eq_false_iff] at h
      refine ⟨argsNotBuffer_of_hvUsesIdx B e.args h.1, ?_⟩
      exact bodyAvoidsBuffer_of_comUsesIdx (Ctxt.Var.there (s := tEx) B) body
        (by simpa [varIdx] using h.2)

/-- Conversely, a buffer the continuation avoids is not found by `comUsesIdx`. -/
theorem comUsesIdx_of_bodyAvoidsBuffer {wB nB : Nat} :
    {Γ : Ctxt jasminDialect} → (B : Ctxt.Var Γ (.stackArr wB nB)) → {t : JasminTy} →
    (c : Com jasminDialect Γ t) →
    BodyAvoidsBuffer B c → comUsesIdx (varIdx B) c = false
  | _, B, _, .ret v, h => by
      simp only [comUsesIdx, beq_eq_false_iff_ne]
      exact varIdx_ne_of_notBuffer B v h
  | _, B, _, .var (t := tEx) e body, h => by
      obtain ⟨hArgs, hBody⟩ := h
      simp only [comUsesIdx, Bool.or_eq_false_iff]
      refine ⟨hvUsesIdx_of_argsNotBuffer B e.args hArgs, ?_⟩
      simpa [varIdx] using
        comUsesIdx_of_bodyAvoidsBuffer (Ctxt.Var.there (s := tEx) B) body hBody

/-- The `Bool` form of `InPlaceLinear`, built from the emitter's own dead-argument
    gate: at every reusing binding, the reused buffer's de Bruijn index (shifted
    under the binder) does not occur in the continuation. -/
def inPlaceLinearB : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → Bool
  | _, _, .ret _ => true
  | _, _, .var (t := tEx) e body =>
      (match reuseSlot tEx e with
        | some a => !comUsesIdx (varIdx a + 1) body
        | none => true) && inPlaceLinearB body

/-- The `Bool` check implies the semantic predicate. -/
theorem inPlaceLinear_of_inPlaceLinearB :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → (c : Com jasminDialect Γ t) →
    inPlaceLinearB c = true → InPlaceLinear c
  | _, _, .ret _, _ => trivial
  | _, _, .var (t := tEx) e body, h => by
      simp only [inPlaceLinearB, Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      refine ⟨?_, inPlaceLinear_of_inPlaceLinearB body h2⟩
      cases tEx with
      | reg w => intro a ha; exact absurd ha (by simp [reuseSlot])
      | inlineInt => intro a ha; exact absurd ha (by simp [reuseSlot])
      | bool => intro a ha; exact absurd ha (by simp [reuseSlot])
      | stackArr w n =>
          intro a ha
          rw [ha] at h1
          simp only [Bool.not_eq_true'] at h1
          exact bodyAvoidsBuffer_of_comUsesIdx
            (Ctxt.Var.there (s := JasminTy.stackArr w n) a) body
            (by simpa [varIdx] using h1)

/-- The semantic predicate implies the `Bool` check. -/
theorem inPlaceLinearB_of_inPlaceLinear :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → (c : Com jasminDialect Γ t) →
    InPlaceLinear c → inPlaceLinearB c = true
  | _, _, .ret _, _ => rfl
  | _, _, .var (t := tEx) e body, h => by
      obtain ⟨h1, h2⟩ := h
      simp only [inPlaceLinearB, Bool.and_eq_true]
      refine ⟨?_, inPlaceLinearB_of_inPlaceLinear body h2⟩
      cases tEx with
      | reg w => simp [reuseSlot]
      | inlineInt => simp [reuseSlot]
      | bool => simp [reuseSlot]
      | stackArr w n =>
          cases hr : reuseSlot (JasminTy.stackArr w n) e with
          | none => rfl
          | some a =>
              have hd : BodyAvoidsBuffer
                  (Ctxt.Var.there (s := JasminTy.stackArr w n) a) body := h1 a hr
              simp only [Bool.not_eq_true']
              simpa [varIdx] using
                comUsesIdx_of_bodyAvoidsBuffer
                  (Ctxt.Var.there (s := JasminTy.stackArr w n) a) body hd

/-- Faithfulness of the in-place realisation from the `Bool` gate. -/
theorem denoteInPlace_eq_denote_of_linearB {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (h : inPlaceLinearB c = true)
    (V : Ctxt.Valuation Γ) : denoteInPlace c V = c.denote V :=
  denoteInPlace_eq_denote c (inPlaceLinear_of_inPlaceLinearB c h) V

/-! ## 6. The emitter's gate, and the leaf obligation -/

/-- A head argument found at the result type is the head argument `hvHeadIdx`
    reports. -/
theorem hvHeadIdx_of_hvHeadAt {Γ : Ctxt jasminDialect} (tRes : JasminTy) :
    {tys : List JasminTy} → (args : HVector (fun ty => Ctxt.Var Γ ty) tys) →
    (a : Ctxt.Var Γ tRes) → hvHeadAt tRes args = some a →
    hvHeadIdx args = some (varIdx a)
  | [], _, _, h => by simp [hvHeadAt] at h
  | ty :: _, .cons v _, a, h => by
      simp only [hvHeadAt] at h
      split at h
      · rename_i hty
        subst hty
        simp only [Option.some.injEq] at h
        subst h
        rfl
      · exact absurd h (by simp)

/-- **The gate `emitBodyRegPtr` computes discharges the deadness obligation.**
    The emitter reuses a buffer only when the head argument's de Bruijn index,
    shifted under the binder, is absent from the continuation; that is exactly
    `SlotDeadAfter`. -/
theorem slotDeadAfter_of_headIdx_unused {Γ : Ctxt jasminDialect} {w n : Nat}
    {e : Expr jasminDialect Γ (.stackArr w n)}
    {a : Ctxt.Var Γ (.stackArr w n)} (ha : reuseSlot (.stackArr w n) e = some a)
    {t : JasminTy} (body : Com jasminDialect (JasminTy.stackArr w n :: Γ) t)
    {i : Nat} (hi : hvHeadIdx e.args = some i)
    (hdead : comUsesIdx (i + 1) body = false) :
    SlotDeadAfter (.stackArr w n) a body := by
  have hia : hvHeadIdx e.args = some (varIdx a) :=
    hvHeadIdx_of_hvHeadAt (JasminTy.stackArr w n) e.args a ha
  have : i = varIdx a := by
    rw [hi] at hia
    exact Option.some.inj hia
  subst this
  exact bodyAvoidsBuffer_of_comUsesIdx
    (Ctxt.Var.there (s := JasminTy.stackArr w n) a) body (by simpa [varIdx] using hdead)

/-- **Leaf-parametric faithfulness.** For a callee registry whose entries compute
    their external leaves (`ComInlineCall.RegistryConsistentN`), the in-place
    realisation of a call-carrying `Com` denotes to the call-free program obtained
    by inlining those callees. The per-leaf obligation is
    `ComInlineCall.CalleeConsistent`; the in-place argument itself is independent
    of it. -/
theorem denoteInPlace_eq_inlined (R : ComInlineCall.FuncRegistryN)
    (hR : ComInlineCall.RegistryConsistentN R)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t)
    (hLin : InPlaceLinear c) (V : Ctxt.Valuation Γ) :
    denoteInPlace c V = (ComInlineCall.inlineCalls R c).denote V := by
  rw [denoteInPlace_eq_denote c hLin, ComInlineCall.inlineCalls_preserves_denote R hR c V]

/-! ## 7. Chains carrying no side condition -/

/-- A `ret` reuses nothing. -/
theorem inPlaceLinear_ret {Γ : Ctxt jasminDialect} {t : JasminTy}
    (v : Ctxt.Var Γ t) : InPlaceLinear (Com.ret v) := trivial

/-- A binding whose result is not a stack array reuses no buffer, so it carries no
    obligation. -/
theorem inPlaceLinear_var_reg {Γ : Ctxt jasminDialect} {w : Nat} {t : JasminTy}
    (e : Expr jasminDialect Γ (.reg w))
    (body : Com jasminDialect (JasminTy.reg w :: Γ) t)
    (hBody : InPlaceLinear body) : InPlaceLinear (Com.var e body) := by
  refine ⟨?_, hBody⟩
  intro a ha
  exact absurd ha (by simp [reuseSlot])

end CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiInPlaceSound
