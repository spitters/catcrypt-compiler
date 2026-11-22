/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
public import CatCrypt.Crypto.SecureCompilation.Haxc.AccessBytes
public import CatCrypt.Crypto.SecureCompilation.Haxc.DeriveBounds

/-!
# Boolean parameters and results of an entry

The front has bits in its domain except as parameter or result of the entry, where a layout
reads words. This module rewrites the extraction of an entry so that its interface has words at
the encoding of a Boolean as 0 or 1, and composes the rewrite with the compiler theorem.

The parameters of an extraction are its leading bindings `let x = x` (`texprPrelude`). A
Boolean parameter gets the type `u8` in these bindings, and `let x = x != 0` follows the last
of them. A Boolean result, read off the statement spine (`DeriveBounds.spineTy`), becomes
`if b {1} else {0}` at the end of the spine, and the nodes of the spine get the type `u8`.
System V leaves the bits of a register above a Boolean unspecified, and a parameter of type
`u8` is read at its width (`AbiLayout.widths`).

The rewrite of the result keeps the statement spine, on which the source semantics reads local
closures (`denoteSpine`). The tests by which the semantics accepts a closure binding have the
same value on the rewritten continuation (`TailWrap`), so the equation `run_boolTail` holds of
every extraction.

The rebinding calls `Ne`, so a module with a Boolean parameter at the entry and a function or
linked function of this name is left as it is (`boolOk`).

## Main definitions

* `boolEntry`, `boolModule`: the rewrite of an extraction and of the entry of a module.
* `encVal`, `encEnv`, `encRes`: the encoding of a Boolean, of the arguments and of the result.
* `decVal`, `decEnv`: the Boolean of a word and the arguments of the source entry.
* `boolRuns`: the runs of the source entry from the Booleans that an entry state encodes.

## Main results

* `boolEntry_of_noBool`, `boolModule_of_noBool`: the rewrite is the identity without Booleans at
  the interface.
* `texprPrelude_boolEntry`, `spineTy_boolEntry`: the parameters and the result type of the
  rewritten extraction.
* `run_boolEntry_encEnv`, `run_boolEntry_reflect`: a run from Boolean arguments gives a run
  from the encoded arguments with the encoded result, and conversely.
* `haxRuns_boolModule`, `exists_boolRuns_of_haxRuns`: the same two statements on modules and
  layouts.
* `haxc_correct_auto_boolEntry`, `haxc_correct_auto_boolResult`: the compiler theorem on the
  rewritten module, with the encoded result and with a Boolean result read in its register.
* `notEntry_boolRuns`, `notEntry_correct`: the negation of one Boolean parameter.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.BoolEntry

open _root_.Hax (ImpExpr ImpLit ImpType TExpr TExprKind Value Env Builtins Outcome denote')
open _root_.Hax.InlineLocalClosures (denoteSpine inlineSpine inlineCalls inlineBlocks callsOk
  noBind frameOk contOk closureOk blockOk closureTable run_bind)
open CatCrypt.Crypto.Hax (HaxModule hax64WExit denoteSpine_letBind spineLetStep isLamE)
open CatCrypt.Crypto.SecureCompilation.Haxc.DeriveBounds (spineTy knownOr)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)

/-! ## The rewrite -/

/-- The type is `bool`. -/
def isBoolTy : ImpType → Bool
  | .bool => true
  | _ => false

/-- The type of an encoded Boolean, `u8`. -/
def wordTy : ImpType := .uint .w8

/-- The names of a parameter list whose first type is `bool`, each once. -/
def boolNames : List (String × ImpType) → List String
  | [] => []
  | (x, τ) :: ps =>
      if isBoolTy τ then x :: (boolNames ps).filter (· != x)
      else (boolNames ps).filter (· != x)

/-- The Boolean parameters of an extraction. -/
def boolParams (te : TExpr) : List String := boolNames (texprPrelude 64 te)

/-- The result of an extraction, read off its statement spine, is a Boolean. -/
def boolResult (te : TExpr) : Bool := isBoolTy (spineTy te)

/-- The name of the disequality that reads a word as a Boolean. -/
def neCall : String := "Ne"

/-- The bindings `let x = x != 0` of the names `B` before `te`. -/
def rebinds : List String → TExpr → TExpr
  | [], te => te
  | x :: B, te =>
      .mk (.letBind x
        (.mk (.app neCall [.mk (.var x) wordTy, .mk (.lit (.int 0)) wordTy]) .bool)
        (rebinds B te)) te.ty

/-- A parameter at the type of the rewritten extraction: `u8` for a name of `B`. -/
def retype (B : List String) (p : String × ImpType) : String × ImpType :=
  (p.1, if B.contains p.1 then wordTy else p.2)

/-- The leading bindings `let x = x` with the names of `B` at the type `u8`, followed by the
    bindings `let x = x != 0` of these names. -/
def wrapParams (B : List String) : TExpr → TExpr
  | .mk (.letBind x (.mk (.var y) τ) b) t =>
      if x == y then
        .mk (.letBind x (.mk (.var y) (retype B (x, τ)).2) (wrapParams B b)) t
      else rebinds B (.mk (.letBind x (.mk (.var y) τ) b) t)
  | te => rebinds B te

/-- The Boolean at the end of the statement spine as the word `if b {1} else {0}`, with the
    nodes of the spine at the type `u8`. -/
def boolTail : TExpr → TExpr
  | .mk (.letBind x v c) _ => .mk (.letBind x v (boolTail c)) wordTy
  | .mk (.seq a b) _ => .mk (.seq a (boolTail b)) wordTy
  | .mk (.ann e) _ => .mk (.ann (boolTail e)) wordTy
  | e => .mk (.ifThenElse e (.mk (.lit (.int 1)) wordTy) (.mk (.lit (.int 0)) wordTy)) wordTy

/-- The extraction with words at its interface: each Boolean parameter is a `u8` rebound to
    `x != 0` after the parameters, and a Boolean result is the word 0 or 1. -/
def boolEntry (te : TExpr) : TExpr :=
  if boolResult te then boolTail (wrapParams (boolParams te) te)
  else wrapParams (boolParams te) te

/-- The call `Ne` of the rebinding has its meaning in the module: the entry has no Boolean
    parameter, or no function or linked function has this name. -/
def boolOk (m : HaxModule) : Bool :=
  (boolParams m.entry).isEmpty
    || (m.fns.all (·.name != neCall) && m.linked.all (·.name != neCall))

/-- The module with words at the interface of its entry, where `boolOk` holds. -/
def boolModule (m : HaxModule) : HaxModule :=
  if boolOk m then { m with entry := boolEntry m.entry } else m

/-! ## The encoding -/

/-- A Boolean as the word 0 or 1, and every other value as it is. -/
def encVal : Value → Value
  | .bool b => .int b.toNat
  | v => v

/-- A word as the Boolean of its disequality from 0, and every other value as it is. -/
def decVal : Value → Value
  | .int n => .bool (n != 0)
  | v => v

/-- The environment with the Booleans of the names `B` encoded. -/
def encEnv (B : List String) (env : Env) : Env :=
  fun x => if B.contains x then (env x).map encVal else env x

/-- The environment with the words of the names `B` read as Booleans. -/
def decEnv (B : List String) (env : Env) : Env :=
  fun x => if B.contains x then (env x).map decVal else env x

/-- Each name of `B` is bound to a word. -/
def WordArgs (B : List String) (env : Env) : Prop :=
  ∀ x ∈ B, ∃ n : Nat, n < 2 ^ 64 ∧ env x = some (.int n)

/-- Each name of `B` is bound to a Boolean. -/
def BoolArgs (B : List String) (env : Env) : Prop :=
  ∀ x ∈ B, ∃ b, env x = some (.bool b)

/-- The table answers `Ne` of a word and 0 by the disequality. -/
def NeWord (bi : Builtins) : Prop :=
  ∀ n : Nat, n < 2 ^ 64 → bi neCall [.int n, .int 0] = some (.bool ((n : Int) != 0))

/-- The value is a Boolean where the result of the extraction is one. -/
def BoolTyped (te : TExpr) (v : Value) : Prop := boolResult te = true → ∃ b, v = .bool b

/-- The result of the rewritten extraction at the result `v` of the extraction. -/
def encRes (te : TExpr) (v : Value) : Value := if boolResult te then encVal v else v

/-- The environment of encoded Boolean arguments decodes to the Boolean arguments. -/
theorem decEnv_encEnv {B : List String} {env : Env} (h : BoolArgs B env) :
    decEnv B (encEnv B env) = env := by
  funext x
  by_cases hx : x ∈ B
  · obtain ⟨b, hb⟩ := h x hx
    cases b <;> simp [decEnv, encEnv, hx, hb, encVal, decVal]
  · simp [decEnv, encEnv, hx]

/-- Encoded Boolean arguments are words. -/
theorem wordArgs_encEnv {B : List String} {env : Env} (h : BoolArgs B env) :
    WordArgs B (encEnv B env) := by
  intro x hx
  obtain ⟨b, hb⟩ := h x hx
  exact ⟨b.toNat, by cases b <;> decide, by simp [encEnv, hx, hb, encVal]⟩

/-- Words decode to Boolean arguments. -/
theorem boolArgs_decEnv {B : List String} {env : Env} (h : WordArgs B env) :
    BoolArgs B (decEnv B env) := by
  intro x hx
  obtain ⟨n, -, hn⟩ := h x hx
  exact ⟨(n : Int) != 0, by simp [decEnv, hx, hn, decVal]⟩

/-! ## What a layout reads of the rewritten extraction -/

/-- The Boolean parameters have distinct names. -/
theorem boolNames_nodup (ps : List (String × ImpType)) : (boolNames ps).Nodup := by
  induction ps with
  | nil => simp [boolNames]
  | cons p ps ih =>
    obtain ⟨x, τ⟩ := p
    simp only [boolNames]
    split
    · exact List.nodup_cons.mpr ⟨by simp, ih.filter _⟩
    · exact ih.filter _

/-- Without a name to rebind the parameters are unchanged. -/
theorem wrapParams_nil (te : TExpr) : wrapParams [] te = te := by
  fun_induction wrapParams [] te <;> simp_all [retype, rebinds]

/-- The rewrite is the identity on an extraction without Booleans at the interface. -/
theorem boolEntry_of_noBool {te : TExpr} (hp : boolParams te = [])
    (hr : boolResult te = false) : boolEntry te = te := by
  simp [boolEntry, hp, hr, wrapParams_nil]

/-- The rewrite is the identity on a module without Booleans at the interface of its entry. -/
theorem boolModule_of_noBool {m : HaxModule} (hp : boolParams m.entry = [])
    (hr : boolResult m.entry = false) : boolModule m = m := by
  simp [boolModule, boolEntry_of_noBool hp hr]

/-- The rebindings before an extraction without parameters add no parameter. -/
theorem texprPrelude_rebinds (B : List String) {te : TExpr}
    (h : ∀ n, texprPrelude n te = []) (n : Nat) : texprPrelude n (rebinds B te) = [] := by
  cases B with
  | nil => exact h n
  | cons x B => cases n <;> simp [rebinds, texprPrelude]

/-- The parameters after the rebinding are the parameters at their rewritten types. -/
theorem texprPrelude_wrapParams (B : List String) (te : TExpr) :
    ∀ n, texprPrelude n (wrapParams B te) = (texprPrelude n te).map (retype B) := by
  fun_induction wrapParams B te with
  | case1 x y τ b t h ih =>
    intro n
    cases n <;> simp_all [texprPrelude, retype]
  | case2 x y τ b t h =>
    intro n
    have h0 : ∀ k, texprPrelude k (.mk (.letBind x (.mk (.var y) τ) b) t) = [] := by
      intro k; cases k <;> simp_all [texprPrelude]
    rw [texprPrelude_rebinds B h0, h0, List.map_nil]
  | case3 te h =>
    intro n
    have h0 : ∀ k, texprPrelude k te = [] := by
      intro k; cases k <;> grind [texprPrelude]
    rw [texprPrelude_rebinds B h0, h0, List.map_nil]

/-- The rewrite of the result keeps the parameters. -/
theorem texprPrelude_boolTail (te : TExpr) :
    ∀ n, texprPrelude n (boolTail te) = texprPrelude n te := by
  fun_induction boolTail te with
  | case1 x v c t ih =>
    intro n
    obtain ⟨k, τ⟩ := v
    cases n <;> cases k <;> simp [texprPrelude, ih]
  | case2 => intro n; cases n <;> simp [texprPrelude]
  | case3 => intro n; cases n <;> simp [texprPrelude]
  | case4 e h =>
    intro n
    obtain ⟨k, τ⟩ := e
    cases n with
    | zero => simp [texprPrelude]
    | succ n =>
      cases k with
      | letBind x v c => exact (h x v c τ rfl).elim
      | _ => simp [texprPrelude]

/-- The parameters of the rewritten extraction are those of the extraction, the Boolean ones
    at the type `u8`. -/
theorem texprPrelude_boolEntry (te : TExpr) (n : Nat) :
    texprPrelude n (boolEntry te) = (texprPrelude n te).map (retype (boolParams te)) := by
  unfold boolEntry
  split <;> simp [texprPrelude_boolTail, texprPrelude_wrapParams]

/-- The spine type is the node type where that is known. -/
theorem knownOr_spineTy (te : TExpr) : knownOr te.ty (fun _ => spineTy te) = spineTy te := by
  obtain ⟨k, t⟩ := te
  cases t <;> cases k <;> rfl

/-- The rebindings keep the spine type. -/
theorem spineTy_rebinds (B : List String) (te : TExpr) :
    spineTy (rebinds B te) = spineTy te := by
  induction B with
  | nil => rw [rebinds]
  | cons x B ih => rw [rebinds, spineTy, ih, knownOr_spineTy]

/-- The rebinding keeps the result type. -/
theorem spineTy_wrapParams (B : List String) (te : TExpr) :
    spineTy (wrapParams B te) = spineTy te := by
  fun_induction wrapParams B te <;> simp_all [spineTy, spineTy_rebinds]

/-- The result type of the rewritten Boolean result is `u8`. -/
theorem spineTy_boolTail (te : TExpr) : spineTy (boolTail te) = wordTy := by
  fun_cases boolTail te <;> simp [spineTy, knownOr, wordTy]

/-- The result type of the rewritten extraction is `u8` for a Boolean result and that of the
    extraction otherwise. -/
theorem spineTy_boolEntry (te : TExpr) :
    spineTy (boolEntry te) = if boolResult te then wordTy else spineTy te := by
  unfold boolEntry
  split <;> simp [spineTy_boolTail, spineTy_wrapParams]

/-- The rebindings keep the variable at the end of the spine. -/
theorem tailVar_rebinds (B : List String) (te : TExpr) :
    tailVar (rebinds B te).erase = tailVar te.erase := by
  induction B <;> simp_all [rebinds, TExpr.erase, tailVar]

/-- The rebindings keep the pair at the end of the spine. -/
theorem spineArrTail_rebinds (B : List String) (te : TExpr) :
    spineArrTail (rebinds B te).erase = spineArrTail te.erase := by
  induction B <;> simp_all [rebinds, TExpr.erase, spineArrTail, arrTailE, neCall]

/-- Without a Boolean result the rewrite keeps the variable at the end of the spine, off
    which a layout reads the result of the in-place form. -/
theorem tailVar_boolEntry {te : TExpr} (hr : boolResult te = false) :
    tailVar (boolEntry te).erase = tailVar te.erase := by
  simp only [boolEntry, hr, Bool.false_eq_true, ite_false]
  generalize boolParams te = B
  clear hr
  fun_induction wrapParams B te <;> simp_all [tailVar_rebinds, TExpr.erase, tailVar]

/-- Without a Boolean result the rewrite keeps the pair at the end of the spine, off which a
    layout reads a pair result. -/
theorem spineArrTail_boolEntry {te : TExpr} (hr : boolResult te = false) :
    spineArrTail (boolEntry te).erase = spineArrTail te.erase := by
  simp only [boolEntry, hr, Bool.false_eq_true, ite_false]
  generalize boolParams te = B
  clear hr
  fun_induction wrapParams B te <;>
    simp_all [spineArrTail_rebinds, TExpr.erase, spineArrTail, arrTailE]

/-! ## The run of the rewritten parameters -/

/-- The outcome of a binding `let x = x` is that of its continuation when `x` is bound to a
    value that is not a control-flow value. -/
theorem run_letSelf (bi : Builtins) (fuel : Nat) (x : String) (c : ImpExpr) (env : Env) :
    ((denoteSpine bi fuel (.letBind x (.var x) c)).run env).1 =
      match env x with
      | none => .err s!"undefined variable: {x}"
      | some w => if w.isControlFlow then .val w else ((denoteSpine bi fuel c).run env).1 := by
  rw [denoteSpine_letBind bi fuel x _ _ rfl, run_bind]
  cases hx : env x with
  | none => simp [denote', StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure, hx, spineLetStep]
  | some w =>
    have he : env.extend x w = env := Env.extend_self env x w hx
    cases w <;> simp [denote', StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure, hx, spineLetStep, modify, modifyGet,
      MonadStateOf.modifyGet, StateT.modifyGet, he]

/-- The rebindings run from words as the extraction from the Booleans of these words. -/
theorem run_rebinds (bi : Builtins) (fuel : Nat) (te : TExpr) :
    ∀ (B : List String) (env : Env), B.Nodup → (∀ x ∈ B, NeWord bi) → WordArgs B env →
      (denoteSpine bi fuel (rebinds B te).erase).run env =
        (denoteSpine bi fuel te.erase).run (decEnv B env)
  | [], env, _, _, _ => by
    have h : decEnv [] env = env := by funext x; simp [decEnv]
    rw [h, rebinds]
  | x :: B, env, hnd, hne, hw => by
    obtain ⟨hx, hB⟩ := List.nodup_cons.mp hnd
    obtain ⟨n, hn, he⟩ := hw x List.mem_cons_self
    have hcall := hne x List.mem_cons_self n hn
    have hw' : WordArgs B (env.extend x (.bool ((n : Int) != 0))) := by
      grind [WordArgs, Env.extend]
    have hdec : decEnv B (env.extend x (.bool ((n : Int) != 0))) = decEnv (x :: B) env := by
      funext y
      by_cases hy : y = x
      · subst hy; simp [decEnv, hx, he, decVal]
      · simp [decEnv, hy]
    have ih := run_rebinds bi fuel te B _ hB (fun y hy => hne y (List.mem_cons_of_mem _ hy)) hw'
    rw [← hdec, ← ih]
    simp only [rebinds, TExpr.erase, TExpr.erase.eraseList]
    have happ : (denote' bi fuel (.app neCall [.var x, .lit (.int 0)])).run env =
        (.val (.bool ((n : Int) != 0)), env) := by
      simp [denote', _root_.Hax.denoteApp', _root_.Hax.denoteArgs', StateT.run, bind,
        StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, he, hcall,
        Value.ofLit]
    rw [denoteSpine_letBind bi fuel x _ _ rfl, run_bind, happ]
    rfl

/-- The outcome of the extraction with rebound parameters from words is that of the extraction
    from the Booleans of these words. -/
theorem run_wrapParams (bi : Builtins) (fuel : Nat) (B : List String) (te : TExpr)
    (hnd : B.Nodup) (hne : ∀ x ∈ B, NeWord bi) :
    ∀ env, WordArgs B env →
      ((denoteSpine bi fuel (wrapParams B te).erase).run env).1 =
        ((denoteSpine bi fuel te.erase).run (decEnv B env)).1 := by
  fun_induction wrapParams B te with
  | case1 x y τ b t h ih =>
    intro env hw
    obtain rfl : x = y := by simpa using h
    simp only [TExpr.erase]
    rw [run_letSelf, run_letSelf]
    by_cases hx : x ∈ B
    · obtain ⟨n, -, he⟩ := hw x hx
      simp [decEnv, hx, he, decVal, ih env hw]
    · simp [decEnv, hx, ih env hw]
  | case2 x y τ b t h =>
    intro env hw
    rw [run_rebinds bi fuel _ B env hnd hne hw]
  | case3 te h =>
    intro env hw
    rw [run_rebinds bi fuel _ B env hnd hne hw]

/-! ## The run of the rewritten result -/

/-- The erasure of `boolTail`. -/
def boolTailE : ImpExpr → ImpExpr
  | .letBind x v c => .letBind x v (boolTailE c)
  | .seq a b => .seq a (boolTailE b)
  | e => .ifThenElse e (.lit (.int 1)) (.lit (.int 0))

/-- `e'` is `e` with one expression `c` in the continuation position of bindings and sequences
    replaced by `if c {1} else {0}`. -/
inductive TailWrap : ImpExpr → ImpExpr → Prop
  /-- The replaced expression. -/
  | tail (e : ImpExpr) : TailWrap e (.ifThenElse e (.lit (.int 1)) (.lit (.int 0)))
  /-- Under a binding. -/
  | letBind (x : String) (v : ImpExpr) {c c' : ImpExpr} :
      TailWrap c c' → TailWrap (.letBind x v c) (.letBind x v c')
  /-- Under a sequence. -/
  | seq (a : ImpExpr) {b b' : ImpExpr} : TailWrap b b' → TailWrap (.seq a b) (.seq a b')

/-- Inlining a pure closure preserves `TailWrap`. -/
theorem TailWrap.inlineCalls {e e' : ImpExpr} (h : TailWrap e e') (f : String)
    (ps : List String) (body : ImpExpr) :
    TailWrap (inlineCalls f ps body e) (inlineCalls f ps body e') := by
  induction h <;> simp only [_root_.Hax.InlineLocalClosures.inlineCalls] <;>
    constructor <;> assumption

/-- Inlining a statement closure preserves `TailWrap`. -/
theorem TailWrap.inlineBlocks {e e' : ImpExpr} (h : TailWrap e e') (f : String)
    (ps : List String) (body : ImpExpr) :
    TailWrap (inlineBlocks f ps body e) (inlineBlocks f ps body e') := by
  induction h <;> simp only [_root_.Hax.InlineLocalClosures.inlineBlocks] <;>
    constructor <;> assumption

/-- `callsOk` has the same value on both sides of `TailWrap`. -/
theorem TailWrap.callsOk_eq {e e' : ImpExpr} (h : TailWrap e e') (f : String) :
    callsOk f e' = callsOk f e := by
  induction h <;> simp_all [callsOk]

/-- `noBind` has the same value on both sides of `TailWrap`. -/
theorem TailWrap.noBind_eq {e e' : ImpExpr} (h : TailWrap e e') (K : List String) :
    noBind K e' = noBind K e := by
  induction h <;> simp_all [noBind]

/-- `frameOk` has the same value on both sides of `TailWrap`. -/
theorem TailWrap.frameOk_eq {e e' : ImpExpr} (h : TailWrap e e') (rd bd ok : String → Bool) :
    frameOk rd bd ok e' = frameOk rd bd ok e := by
  induction h <;> simp_all [frameOk]

/-- An expression in the frame fragment without a call of `f` passes `contOk`. -/
theorem contOk_of_frameOk {f : String} {rd bd : String → Bool} {e : ImpExpr}
    (h : frameOk rd bd (fun g => g != f) e = true) : contOk f rd bd e = true := by
  cases e with
  | break_ o => cases o <;> simp [contOk, h]
  | _ => simp [contOk, h]

/-- `contOk` has the same value on both sides of `TailWrap`. -/
theorem TailWrap.contOk_eq {e e' : ImpExpr} (h : TailWrap e e') (f : String)
    (rd bd : String → Bool) : contOk f rd bd e' = contOk f rd bd e := by
  induction h with
  | tail e =>
    have := @contOk_of_frameOk f rd bd e
    simp only [contOk, frameOk]
    grind
  | letBind x v h ih => simp [contOk, frameOk, h.frameOk_eq, ih]
  | seq a h ih => simp [contOk, frameOk, h.frameOk_eq, ih]

/-- `closureOk` has the same value on both sides of `TailWrap`. -/
theorem TailWrap.closureOk_eq {e e' : ImpExpr} (h : TailWrap e e') (f : String)
    (ps : List String) (body : ImpExpr) : closureOk f ps body e' = closureOk f ps body e := by
  simp [closureOk, h.callsOk_eq, h.noBind_eq]

/-- `blockOk` has the same value on both sides of `TailWrap`. -/
theorem TailWrap.blockOk_eq {e e' : ImpExpr} (h : TailWrap e e') (f : String)
    (ps : List String) (body : ImpExpr) : blockOk f ps body e' = blockOk f ps body e := by
  simp [blockOk, h.contOk_eq]

/-- The inlined spines of an expression and of its `boolTailE` are related by `TailWrap`. -/
theorem tailWrap_inlineSpine (e : ImpExpr) :
    TailWrap (inlineSpine e) (inlineSpine (boolTailE e)) := by
  induction e using ImpExpr.ind with
  | letBind x v c ihv ihc =>
    cases v with
    | lam ps body =>
      simp only [boolTailE, inlineSpine, ihc.closureOk_eq, ihc.blockOk_eq]
      split
      · exact ihc.inlineCalls x ps body
      · split
        · exact ihc.inlineBlocks x ps body
        · exact ihc.letBind x _
    | _ => exact ihc.letBind x _
  | seq a b iha ihb => exact ihb.seq a
  | _ => exact .tail _

/-- The outcome of `if b {1} else {0}` after the outcome of `b`. -/
def boolStep : Outcome → Outcome
  | .val (.controlFlow k w) => .val (.controlFlow k w)
  | .val (.bool b) => .val (.int b.toNat)
  | .val _ => .err "if condition not a bool"
  | o => o

/-- The run of `if e {1} else {0}` is the run of `e` followed by `boolStep`. -/
theorem run_iteWord (bi : Builtins) (fuel : Nat) (e : ImpExpr) (env : Env) :
    (denote' bi fuel (.ifThenElse e (.lit (.int 1)) (.lit (.int 0)))).run env =
      Prod.map boolStep id ((denote' bi fuel e).run env) := by
  simp only [denote']
  rw [run_bind]
  generalize (denote' bi fuel e).run env = q
  obtain ⟨o, env'⟩ := q
  cases o with
  | val v => cases v with
    | bool b => cases b <;> rfl
    | _ => rfl
  | _ => rfl

/-- The run of an expression with the Boolean at the end of its spine as a word is the run of
    the expression followed by the conditional. -/
theorem run_boolTailE (fuel : Nat) (e : ImpExpr) : ∀ (bi : Builtins) (env : Env),
    (denoteSpine bi fuel (boolTailE e)).run env =
      Prod.map boolStep id ((denoteSpine bi fuel e).run env) := by
  induction e using ImpExpr.ind with
  | letBind x v c ihv ihc =>
    intro bi env
    cases hv : isLamE v with
    | false =>
      rw [boolTailE, denoteSpine_letBind bi fuel x v _ hv, denoteSpine_letBind bi fuel x v _ hv,
        run_bind, run_bind]
      generalize (denote' bi fuel v).run env = q
      obtain ⟨o, env'⟩ := q
      cases o with
      | val w => cases w <;> first | rfl | exact ihc bi _
      | _ => rfl
    | true =>
      cases v with
      | lam ps body =>
        simp only [boolTailE, denoteSpine, (tailWrap_inlineSpine c).closureOk_eq,
          (tailWrap_inlineSpine c).blockOk_eq]
        split
        · exact ihc (closureTable bi fuel x ps body env) env
        · rw [_root_.Hax.ContinueFlag.letBind_run, _root_.Hax.ContinueFlag.letBind_run]
          simp only [denote']
          rfl
      | _ => simp [isLamE] at hv
  | seq a b iha ihb =>
    intro bi env
    rw [boolTailE, CatCrypt.Crypto.Hax.denoteSpine_seq, CatCrypt.Crypto.Hax.denoteSpine_seq,
      run_bind, run_bind]
    generalize (denote' bi fuel a).run env = q
    obtain ⟨o, env'⟩ := q
    cases o with
    | val w => cases w <;> first | rfl | exact ihb bi _
    | _ => rfl
  | _ =>
    intro bi env
    exact run_iteWord bi fuel _ env

/-- The erasure commutes with the rewrite of the result. -/
theorem erase_boolTail (te : TExpr) : (boolTail te).erase = boolTailE te.erase := by
  induction te using TExpr.ind with
  | break_none => simp [boolTail, TExpr.erase, boolTailE]
  | _ => simp_all [boolTail, TExpr.erase, boolTailE]

/-- The run of the extraction with a word result is the run of the extraction followed by
    `if b {1} else {0}`, whether or not its spine binds closures. -/
theorem run_boolTail (bi : Builtins) (fuel : Nat) (te : TExpr) (env : Env) :
    (denoteSpine bi fuel (boolTail te).erase).run env =
      Prod.map boolStep id ((denoteSpine bi fuel te.erase).run env) := by
  rw [erase_boolTail, run_boolTailE]

/-! ## The source theorem at the encoding -/

/-- The outcome of the rewritten extraction from words, by that of the extraction from the
    Booleans of these words. -/
theorem run_boolEntry (bi : Builtins) (fuel : Nat) (te : TExpr) {env : Env}
    (hne : ∀ x ∈ boolParams te, NeWord bi) (hw : WordArgs (boolParams te) env) :
    ((denoteSpine bi fuel (boolEntry te).erase).run env).1 =
      if boolResult te
      then boolStep ((denoteSpine bi fuel te.erase).run (decEnv (boolParams te) env)).1
      else ((denoteSpine bi fuel te.erase).run (decEnv (boolParams te) env)).1 := by
  have h := run_wrapParams bi fuel (boolParams te) te (boolNames_nodup _) hne env hw
  unfold boolEntry
  split
  · rw [run_boolTail, Prod.map_fst, h]
  · exact h

/-- A run of the extraction from the Booleans of words gives a run of the rewritten extraction
    from the words, to the encoded result. -/
theorem run_boolEntry_val (bi : Builtins) (fuel : Nat) (te : TExpr) {env : Env}
    (hne : ∀ x ∈ boolParams te, NeWord bi) (hw : WordArgs (boolParams te) env) {v : Value}
    {env' : Env}
    (hrun : (denoteSpine bi fuel te.erase).run (decEnv (boolParams te) env) = (.val v, env'))
    (hv : BoolTyped te v) (hcf : v.isControlFlow = false) :
    (∃ env'', (denoteSpine bi fuel (boolEntry te).erase).run env = (.val (encRes te v), env''))
      ∧ (encRes te v).isControlFlow = false := by
  have h := run_boolEntry bi fuel te hne hw
  rw [hrun] at h
  cases hr : boolResult te with
  | false =>
    simp only [hr, Bool.false_eq_true, ite_false, encRes] at h ⊢
    exact ⟨⟨_, Prod.ext h rfl⟩, hcf⟩
  | true =>
    obtain ⟨b, rfl⟩ := hv hr
    simp only [hr, ite_true, encRes, encVal, boolStep] at h ⊢
    exact ⟨⟨_, Prod.ext h rfl⟩, rfl⟩

/-- A run of the extraction from Boolean arguments gives a run of the rewritten extraction
    from the encoded arguments, to the encoded result. -/
theorem run_boolEntry_encEnv (bi : Builtins) (fuel : Nat) (te : TExpr) {env : Env}
    (hne : ∀ x ∈ boolParams te, NeWord bi) (hb : BoolArgs (boolParams te) env) {v : Value}
    {env' : Env} (hrun : (denoteSpine bi fuel te.erase).run env = (.val v, env'))
    (hv : BoolTyped te v) (hcf : v.isControlFlow = false) :
    ∃ env'', (denoteSpine bi fuel (boolEntry te).erase).run (encEnv (boolParams te) env) =
      (.val (encRes te v), env'') :=
  (run_boolEntry_val bi fuel te hne (wordArgs_encEnv hb)
    (by rwa [decEnv_encEnv hb]) hv hcf).1

/-- A result of the rewritten extraction from words is the encoding of a result of the
    extraction from the Booleans of these words. -/
theorem run_boolEntry_reflect (bi : Builtins) (fuel : Nat) (te : TExpr) {env : Env}
    (hne : ∀ x ∈ boolParams te, NeWord bi) (hw : WordArgs (boolParams te) env) {w : Value}
    {env' : Env} (hrun : (denoteSpine bi fuel (boolEntry te).erase).run env = (.val w, env'))
    (hcf : w.isControlFlow = false) :
    ∃ v env'', (denoteSpine bi fuel te.erase).run (decEnv (boolParams te) env) = (.val v, env'')
      ∧ BoolTyped te v ∧ v.isControlFlow = false ∧ w = encRes te v := by
  have h := run_boolEntry bi fuel te hne hw
  rw [hrun] at h
  generalize hq : (denoteSpine bi fuel te.erase).run (decEnv (boolParams te) env) = q at h
  obtain ⟨o, env''⟩ := q
  cases hr : boolResult te with
  | false =>
    simp only [hr, Bool.false_eq_true, ite_false] at h
    subst h
    exact ⟨w, env'', rfl, by simp [BoolTyped, hr], hcf, by simp [encRes, hr]⟩
  | true =>
    simp only [hr, ite_true] at h
    unfold boolStep at h
    split at h
    · cases h; cases hcf
    · rename_i b
      cases h
      exact ⟨.bool b, env'', rfl, fun _ => ⟨b, rfl⟩, rfl, by simp [encRes, hr, encVal]⟩
    · cases h
    · grind

/-! ## Modules and layouts -/

/-- The table of `u64` code answers `Ne` of a word and 0 by the disequality. -/
theorem neWord_hax64WExit : NeWord hax64WExit := by
  intro n hn
  unfold neCall
  rw [CatCrypt.Crypto.Hax.hax64WExit_of_ne (by decide) (by decide) (by decide) (by decide)]
  have hb : _root_.Hax.hax64Builtins "Ne" [.int n, .int 0] = some (.bool ((n : Int) != 0)) :=
    rfl
  refine CatCrypt.Crypto.Hax.hax64Exit_of_scalarAdmit hb rfl ?_
  simp only [CatCrypt.Crypto.Hax.hax64ScalarAdmit, CatCrypt.Crypto.Hax.hax64ArgsShape]
  simp +decide [CatCrypt.Crypto.Hax.exitMarshalOk_of_arrCtorLen (f := "Ne") rfl,
    CatCrypt.Crypto.Hax.scalarValNB]
  omega

/-- Where `boolOk` holds, each Boolean parameter is rebound by the disequality of the table of
    the module. -/
theorem neWord_table {m : HaxModule} (hok : boolOk m = true) (fuelC : Nat) :
    ∀ x ∈ boolParams m.entry, NeWord (m.table hax64WExit fuelC) := by
  intro x hx n hn
  simp only [boolOk, Bool.or_eq_true, List.isEmpty_iff, Bool.and_eq_true, List.all_eq_true,
    bne_iff_ne] at hok
  rcases hok with h | ⟨hf, hl⟩
  · simp [h] at hx
  · rw [HaxModule.table, CatCrypt.Crypto.Hax.refBi_of_find_none _ _ _ _ (by simpa using hf),
      HaxModule.linkTable, CatCrypt.Crypto.Hax.linkBi_of_find_none _ _ (by simpa using hl)]
    exact neWord_hax64WExit n hn

/-- The rewrite keeps the linked functions. -/
theorem boolModule_linked (m : HaxModule) : (boolModule m).linked = m.linked := by
  unfold boolModule
  split <;> rfl

/-- The rewrite keeps the entry state the source reads at a layout. -/
theorem narrowEntry_boolModule (m : HaxModule) (σ : AbiLayout) (sa : AState) :
    narrowEntry (boolModule m) σ sa = narrowEntry m σ sa := by
  unfold boolModule
  split <;> rfl

/-- The source semantics of an entry with Booleans at its interface: an environment that `σ`
    reads off the entry state, at the widths of `σ`, binds the Boolean parameters to words, and
    the extraction runs from the Booleans of these words to `v`, a Boolean where the result
    type is one. -/
def boolRuns (σ : AbiLayout) (m : HaxModule) (sa : AState) (v : Value) : Prop :=
  ∃ env fuel fuelC env', σ.EnvOf (narrowEntry m σ sa) env
    ∧ WordArgs (boolParams m.entry) env
    ∧ (denoteSpine (m.table hax64WExit fuelC) fuel m.entry.erase).run
        (decEnv (boolParams m.entry) env) = (.val v, env')
    ∧ v.isControlFlow = false ∧ BoolTyped m.entry v

/-- A run from Boolean arguments whose encoding the layout reads off the entry state is a run
    of `boolRuns`. -/
theorem boolRuns_of_boolArgs {σ : AbiLayout} {m : HaxModule} {sa : AState} {env env' : Env}
    {fuel fuelC : Nat} {v : Value} (hb : BoolArgs (boolParams m.entry) env)
    (hσ : σ.EnvOf (narrowEntry m σ sa) (encEnv (boolParams m.entry) env))
    (hrun : (denoteSpine (m.table hax64WExit fuelC) fuel m.entry.erase).run env = (.val v, env'))
    (hcf : v.isControlFlow = false) (hv : BoolTyped m.entry v) : boolRuns σ m sa v :=
  ⟨_, fuel, fuelC, env', hσ, wordArgs_encEnv hb, by rwa [decEnv_encEnv hb], hcf, hv⟩

/-- A run of the source entry is a run of the rewritten module to the encoded result. -/
theorem haxRuns_boolModule {σ : AbiLayout} {m : HaxModule} {sa : AState} {v : Value}
    (hok : boolOk m = true) (h : boolRuns σ m sa v) :
    haxRuns σ (boolModule m) sa (encRes m.entry v) := by
  obtain ⟨env, fuel, fuelC, env', hσ, hw, hrun, hcf, hv⟩ := h
  obtain ⟨⟨env'', h'⟩, hcf'⟩ :=
    run_boolEntry_val _ fuel m.entry (neWord_table hok fuelC) hw hrun hv hcf
  rw [haxRuns, narrowEntry_boolModule]
  simp only [boolModule, hok, ite_true]
  exact ⟨env, fuel, fuelC, env'', hσ, h', hcf'⟩

/-- On a layout that carries every Boolean parameter as a scalar, a run of the rewritten
    module is a run of the source entry, its result read back by the encoding. -/
theorem exists_boolRuns_of_haxRuns {σ : AbiLayout} {m : HaxModule} {sa : AState} {w : Value}
    (hok : boolOk m = true)
    (hargs : ∀ x ∈ boolParams m.entry, ∃ a ∈ σ.args, a.name = x ∧ a.kind = .scalar)
    (h : haxRuns σ (boolModule m) sa w) :
    ∃ v, boolRuns σ m sa v ∧ w = encRes m.entry v := by
  rw [haxRuns, narrowEntry_boolModule] at h
  simp only [boolModule, hok, ite_true] at h
  obtain ⟨env, fuel, fuelC, env', hσ, hrun, hcf⟩ := h
  have hw : WordArgs (boolParams m.entry) env := by
    intro x hx
    obtain ⟨a, ha, rfl, hk⟩ := hargs x hx
    exact ⟨_, ((narrowEntry m σ sa).regs a.reg).isLt, by rw [hσ.1 a ha, AbiArg.read, hk]⟩
  obtain ⟨v, env'', h', hv, hcf', he⟩ :=
    run_boolEntry_reflect _ fuel m.entry (neWord_table hok fuelC) hw hrun hcf
  exact ⟨v, ⟨env, fuel, fuelC, env'', hσ, hw, h', hcf', hv⟩, he⟩

/-! ## The compiler theorem -/

section Compose

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts HaltsC)
open CatCrypt.Crypto.Hax (LinkedFn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (HaltsO)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLink (shiftProg)
open CatCrypt.Crypto.SecureCompilation.Haxc.AccessBytes (HaltsIn)
open CatCrypt.Crypto.SecureCompilation.SepLogic.X86 (wordsLocs frameWords regionWords)

/-- The compiler theorem on an entry with Booleans at its interface. When `compileA` returns
    bytes on the rewritten module, every run of the source entry from the Booleans that the
    entry state encodes is read back at the encoding of its result (`encRes`), with the
    conclusion of `haxc_correct_auto_access`. -/
theorem haxc_correct_auto_boolEntry (m : HaxModule) (σ : AbiLayout) (fname : String) (P : Lprog)
    (bytes : List (BitVec 8)) (hok : boolOk m = true)
    (hc : compileA (boolModule m) σ fname = some (P, bytes))
    (sa : AState) (hsep : σ.Regions sa) (v : Value) (hrun : boolRuns σ m sa v)
    (hnd : (m.linked.map (·.name)).Nodup := by exact List.nodup_nil)
    (hk : ∀ l ∈ m.linked, LinkedKernel l := by exact fun _ h => nomatch h) :
    ∃ prog, decodeLprog bytes = some prog ∧
      ((∃ sa', Halts aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' (encRes m.entry v)
        ∧ sa'.regs "%rsp" = sa.regs "%rsp"
        ∧ (∀ x, SepLogic.X86.Loc.mem x
            ∉ wordsLocs (frameWords (sa.regs "%rsp") σ.frameLo σ.frameHi) →
          (∀ p ∈ σ.regions,
            SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
          sa'.mem x = sa.mem x)
        ∧ HaltsIn (layoutMem σ sa) prog 0 sa sa')
      ∨ ∃ cs : List CalleeData, cs.Sublist (m.linked.filterMap LinkedFn.calleeData)
          ∧ cs ≠ [] ∧ (cs.map (·.name)).Nodup
          ∧ ∃ (pc Q : List RInstr) (k : String → Nat) (q : String → List RInstr),
            (∀ c ∈ cs, decodeLprog c.bytes = some (q c.name))
            ∧ decodeLprog (cs.flatMap (·.bytes)) = some Q
            ∧ (∀ c ∈ cs, ∃ A B,
              Q = A ++ shiftProg A.length (q c.name) ++ B ∧ A.length = k c.name)
            ∧ prog = pc ++ shiftProg pc.length Q
            ∧ (∃ sa', HaltsC aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' (encRes m.entry v))
            ∧ ∃ sa', HaltsO aMachine (tabOracle cs pc.length k q) pc 0 sa sa'
              ∧ σ.ResultOf sa sa' (encRes m.entry v)) := by
  have hl := boolModule_linked m
  have h := haxc_correct_auto_access (boolModule m) σ fname P bytes hc sa hsep _
    (haxRuns_boolModule hok hrun) (by rwa [hl]) (by rwa [hl])
  rwa [hl] at h

/-- The register of a Boolean result holds 0 or 1. -/
theorem regs_of_resultOf_bool {σ : AbiLayout} {te : TExpr} {sa sa' : AState} {r : String}
    {b : Bool} (hr : boolResult te = true) (hσ : σ.result = .reg r)
    (h : σ.ResultOf sa sa' (encRes te (.bool b))) : (sa'.regs r).toNat = b.toNat := by
  simp only [AbiLayout.ResultOf, hσ, ResultKind.read, encRes, hr, ite_true, encVal,
    Value.int.injEq] at h
  omega

/-- The compiler theorem at a Boolean result. When `compileA` returns bytes on the rewritten
    module, every run of the source entry to a Boolean `b` is read back in the result register
    as `b.toNat`, which is 0 or 1, with the conclusion of `haxc_correct_auto_access`. -/
theorem haxc_correct_auto_boolResult (m : HaxModule) (σ : AbiLayout) (fname : String) (P : Lprog)
    (bytes : List (BitVec 8)) (hok : boolOk m = true) (hres : boolResult m.entry = true)
    (r : String) (hσ : σ.result = .reg r)
    (hc : compileA (boolModule m) σ fname = some (P, bytes))
    (sa : AState) (hsep : σ.Regions sa) (b : Bool) (hrun : boolRuns σ m sa (.bool b))
    (hnd : (m.linked.map (·.name)).Nodup := by exact List.nodup_nil)
    (hk : ∀ l ∈ m.linked, LinkedKernel l := by exact fun _ h => nomatch h) :
    ∃ prog, decodeLprog bytes = some prog ∧
      ((∃ sa', Halts aMachine prog 0 sa sa' ∧ (sa'.regs r).toNat = b.toNat
        ∧ sa'.regs "%rsp" = sa.regs "%rsp"
        ∧ (∀ x, SepLogic.X86.Loc.mem x
            ∉ wordsLocs (frameWords (sa.regs "%rsp") σ.frameLo σ.frameHi) →
          (∀ p ∈ σ.regions,
            SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
          sa'.mem x = sa.mem x)
        ∧ HaltsIn (layoutMem σ sa) prog 0 sa sa')
      ∨ ∃ cs : List CalleeData, cs.Sublist (m.linked.filterMap LinkedFn.calleeData)
          ∧ cs ≠ [] ∧ (cs.map (·.name)).Nodup
          ∧ ∃ (pc Q : List RInstr) (k : String → Nat) (q : String → List RInstr),
            (∀ c ∈ cs, decodeLprog c.bytes = some (q c.name))
            ∧ decodeLprog (cs.flatMap (·.bytes)) = some Q
            ∧ (∀ c ∈ cs, ∃ A B,
              Q = A ++ shiftProg A.length (q c.name) ++ B ∧ A.length = k c.name)
            ∧ prog = pc ++ shiftProg pc.length Q
            ∧ (∃ sa', HaltsC aMachine prog 0 sa sa' ∧ (sa'.regs r).toNat = b.toNat)
            ∧ ∃ sa', HaltsO aMachine (tabOracle cs pc.length k q) pc 0 sa sa'
              ∧ (sa'.regs r).toNat = b.toNat) := by
  obtain ⟨prog, hd, h⟩ :=
    haxc_correct_auto_boolEntry m σ fname P bytes hok hc sa hsep _ hrun hnd hk
  refine ⟨prog, hd, ?_⟩
  rcases h with ⟨sa', hh, hR, hrest⟩
    | ⟨cs, hsub, hne, hndc, pc, Q, k, q, hq, hQ, hB, hp, ⟨sa', hC, hR⟩, sa'', hO, hR'⟩
  · exact .inl ⟨sa', hh, regs_of_resultOf_bool hres hσ hR, hrest⟩
  · exact .inr ⟨cs, hsub, hne, hndc, pc, Q, k, q, hq, hQ, hB, hp,
      ⟨sa', hC, regs_of_resultOf_bool hres hσ hR⟩, sa'', hO,
      regs_of_resultOf_bool hres hσ hR'⟩

/-! ## The negation of one Boolean parameter -/

/-- The extraction of `fn(x: bool) -> bool { !x }`. -/
def notEntry : TExpr :=
  .mk (.letBind "x" (.mk (.var "x") .bool) (.mk (.app "Not" [.mk (.var "x") .bool]) .bool)) .bool

/-- The System V layout of the rewritten negation: the parameter in `%rdi` at width 8, the
    result in `%rax`. -/
def notLayout : AbiLayout where
  args := [⟨"x", "%rdi", .scalar⟩]
  consts := []
  result := .reg "%rax"
  bounds := []
  frameLo := -256
  frameHi := -8
  widths := [("%rdi", 8)]

/-- The negation has the parameter `x` as its one Boolean parameter. -/
theorem notEntry_boolParams : boolParams notEntry = ["x"] := by
  simp [boolParams, notEntry, texprPrelude, boolNames, isBoolTy]

/-- The negation has a Boolean result. -/
theorem notEntry_boolResult : boolResult notEntry = true := by
  simp [boolResult, notEntry, spineTy, knownOr, isBoolTy]

/-- The module of the negation satisfies `boolOk`. -/
theorem notEntry_boolOk : boolOk (HaxModule.single notEntry) = true := by
  simp [boolOk, HaxModule.single]

/-- Every entry state satisfies the entry conditions of the layout of the negation. -/
theorem notLayout_regions (sa : AState) : notLayout.Regions sa := by
  have h : notLayout.regions = [] := by decide
  refine ⟨?_, ?_, ?_, AbiLayout.stackIn_of_regCarriedB (by decide) sa⟩
  · simp [notLayout]
  · simp [h]
  · simp [h]

/-- The table of `u64` code answers `Not` of a Boolean by the negation. -/
theorem hax64WExit_notBool (b : Bool) : hax64WExit "Not" [.bool b] = some (.bool !b) := by
  rw [CatCrypt.Crypto.Hax.hax64WExit_of_ne (by decide) (by decide) (by decide) (by decide)]
  have hb : _root_.Hax.hax64Builtins "Not" [.bool b] = some (.bool !b) := rfl
  refine CatCrypt.Crypto.Hax.hax64Exit_of_scalarAdmit hb rfl ?_
  simp only [CatCrypt.Crypto.Hax.hax64ScalarAdmit, CatCrypt.Crypto.Hax.hax64ArgsShape]
  simp +decide [CatCrypt.Crypto.Hax.exitMarshalOk_of_arrCtorLen (f := "Not") rfl,
    CatCrypt.Crypto.Hax.scalarValNB]

/-- From every entry state the negation runs to the negation of the Boolean in the low byte
    of `%rdi`. -/
theorem notEntry_boolRuns (sa : AState) :
    boolRuns notLayout (HaxModule.single notEntry) sa
      (.bool ((sa.regs "%rdi").toNat % 2 ^ 8 == 0)) := by
  let m := HaxModule.single notEntry
  let env := notLayout.canonEnv (narrowEntry m notLayout sa)
  have hn : narrowEntry m notLayout sa = notLayout.clean sa := by
    simp [m, narrowEntry, narrowOk, notLayout, HaxModule.single]
  have hx : env "x" = some (.int (((sa.regs "%rdi").toNat % 2 ^ 8 : Nat) : Int)) := by
    simp only [env, hn]
    rw [← AbiLayout.read_clean_of_width (σ := notLayout) (a := ⟨"x", "%rdi", .scalar⟩) rfl
      (w := 8) (by decide) sa]
    simp [AbiLayout.canonEnv, notLayout]
  refine ⟨env, 0, 0, decEnv ["x"] env, AbiLayout.envOf_canonEnv _ (by decide) _, ?_, ?_, rfl,
    fun _ => ⟨_, rfl⟩⟩
  · intro y hy
    obtain rfl : y = "x" := by simpa [HaxModule.single, notEntry_boolParams] using hy
    exact ⟨_, by omega, hx⟩
  · have hd : decEnv ["x"] env "x"
        = some (.bool ((((sa.regs "%rdi").toNat % 2 ^ 8 : Nat) : Int) != 0)) := by
      simp [decEnv, hx, decVal]
    rw [HaxModule.table_single]
    simp only [HaxModule.single, notEntry_boolParams]
    simp only [notEntry, TExpr.erase, TExpr.erase.eraseList]
    generalize decEnv ["x"] env = e at hd ⊢
    have hnot : ((sa.regs "%rdi").toNat % 2 ^ 8 == 0)
        = !((((sa.regs "%rdi").toNat % 2 ^ 8 : Nat) : Int) != 0) := by grind
    rw [hnot]
    generalize ((((sa.regs "%rdi").toNat % 2 ^ 8 : Nat) : Int) != 0) = b at hd ⊢
    rw [denoteSpine_letBind _ _ _ _ _ rfl, run_bind]
    simp [denote', denoteSpine, _root_.Hax.denoteApp', _root_.Hax.denoteArgs', StateT.run,
      bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, hd,
      hax64WExit_notBool, spineLetStep, modify, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet, Env.extend_self _ _ _ hd]

/-- The bytes `compileA` returns on the rewritten negation halt from every entry state with
    `%rax` at 1 when the low byte of `%rdi` is 0 and at 0 otherwise. -/
theorem notEntry_correct (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA (boolModule (HaxModule.single notEntry)) notLayout fname = some (P, bytes))
    (sa : AState) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ (sa'.regs "%rax").toNat = ((sa.regs "%rdi").toNat % 2 ^ 8 == 0).toNat := by
  obtain ⟨prog, hd, h⟩ := haxc_correct_auto_boolResult (HaxModule.single notEntry) notLayout
    fname P bytes notEntry_boolOk notEntry_boolResult "%rax" rfl hc sa (notLayout_regions sa) _
    (notEntry_boolRuns sa)
  rcases h with ⟨sa', hh, hR, -⟩ | ⟨cs, hsub, hne, -⟩
  · exact ⟨prog, sa', hd, hh, hR⟩
  · exact absurd (List.sublist_nil.mp hsub) hne

end Compose

end CatCrypt.Crypto.SecureCompilation.Haxc.BoolEntry
