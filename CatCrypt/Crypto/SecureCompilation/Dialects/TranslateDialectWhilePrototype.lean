/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow

@[expose] public section

set_option autoImplicit false

/-!
# Prototype: the `RWhileNz` front arm for `translateDialectControl` (data-dependent while)

`translateDialectControl` (`TranslateDialectDirectControl.lean`) fuses the scalar
front's control-flow arms `RIfNz` (φ-merge) and `RFor` (static unroll via
`loopRForD`), but **declines** `RWhileNz` (`.RWhileNz _ _ => none`). A
data-dependent `while (name != 0)` — the plonky3 query-sample / PoW-grind /
reject-sampling shape — has a trip fixed only at run time by the values the body
produces, so its back-edge lives at the `Lprog`/`Lcmd` level (a real
`Llabel`/`Lcond` jump), **not** as a straight-line `catCryptDialect` region: the
pure A-normal `Com` substrate has no label/branch node.

This file prototypes the missing arm **additively and standalone** — it does NOT
modify `translateDialectControl`. It shows the two halves the real integration
needs, and validates them at single-body size:

1. **Front context-plumbing** (`translateWhileArm`): the piece that belongs
   inside `translateDialectControl`. It gates on the guard being a bound scalar
   (mirroring `RIfNz`'s `some ⟨.sword w, _⟩` lookup) and on the body
   front-compiling (recursively via the **existing** `translateDialectControl`),
   and emits the **context-invariant** `DTransOut` (`Γ' = Γ`, `cont = ComCont.id`,
   `vm` unchanged) — the loop-region invariant (see §4).

2. **Back-edge emission** (`translateWhileLcmd`): the real loop, reusing the
   owned backend's `X86Backend.LprogControlFlow.whileLcmd` combinator verbatim —
   `Llabel top ; body ; CMP gReg,#0 ; Lcond NZ → top` (renders `jne .L<top>`).
   `whileLcmd` **composes directly**; no bespoke `Lcmd` was hand-built.

The actual owned lowering already exists at the `Lprog` level
(`TranslateDialectDataWhile.rolledWhileNz`, wrapping `whileLinstrRM`); this
prototype isolates the *front arm* that `translateDialectControl` is missing so
the orchestrator can wire it in (recipe in §4).
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectWhilePrototype

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow
open CatCrypt.Crypto.Jasmin.LowCT (LowCT)

/-! ## 1. The front context-plumbing arm (`translateWhileArm`)

The `DTransOut` half of an `RWhileNz` arm for `translateDialectControl`. Unlike
`RFor`'s `loopRForD` — which threads the growing `VarMap` through `N` unrolled
copies and hands back the extended `Γ'` — a data-dependent `while` cannot unroll
(the trip is unknown at entry) and its body's bindings are **loop-scoped**: they
must not escape into the outer straight-line context. So the arm returns the
*entry* context unchanged (`Γ' = Γ`), gated on the body front-compiling. The
actual per-iteration instructions are emitted at the `Lcmd` level by §2. -/

/-- **The missing `RWhileNz` arm (front half).** Mirrors `RIfNz`'s guard lookup
    (`some ⟨.sword w, _⟩`) and recurses into the **existing**
    `translateDialectControl` on the loop `body`; succeeds iff the guard is a
    bound scalar and the body front-compiles, returning the context-invariant
    `DTransOut` (`Γ' = Γ`, `cont = ComCont.id`, `vm` unchanged — the loop-region
    invariant, §4). Declines (`none`) exactly when the current arm declines: an
    unbound / non-scalar guard, or an uncovered body. -/
def translateWhileArm {Γ : Ctx} (vm : VarMap Γ) (name : String) (body : LowCT) :
    Option (DTransOut Γ) :=
  match vm.lookup name with
  | some ⟨.sword _, _⟩ =>
      -- body must front-compile (recursively, via the EXISTING control front);
      -- its own `Γ'`/`vm` are loop-local, so we discard them and keep `Γ`/`vm`.
      (translateDialectControl vm body).map
        (fun _bodyOut => { Γ' := Γ, cont := ComCont.id, vm := vm })
  | _ => none

/-- On a bound-scalar guard, `translateWhileArm` succeeds precisely when the body
    front-compiles — and then is context-invariant (`Γ' = Γ`, `vm` unchanged).
    The plumbing fact the core-integration proof (§4) reduces to. -/
theorem translateWhileArm_isSome_of_body {Γ : Ctx} (vm : VarMap Γ)
    (name : String) (body : LowCT) (w : Nat) (v : CVar Γ (.sword w))
    (hlk : vm.lookup name = some ⟨.sword w, v⟩)
    (hbody : (translateDialectControl vm body).isSome) :
    (translateWhileArm vm name body).isSome := by
  unfold translateWhileArm
  rw [hlk]
  cases h : translateDialectControl vm body with
  | none => rw [h] at hbody; simp at hbody
  | some o => simp

/-- The success shape is context-invariant: whenever `translateWhileArm`
    succeeds, it returns the entry context and `VarMap` (`Γ' = Γ`, `vm` = `vm`),
    with the identity `Com`-prefix. This is the loop-region invariant the core
    arm must preserve. -/
theorem translateWhileArm_ctx_invariant {Γ : Ctx} (vm : VarMap Γ)
    (name : String) (body : LowCT) (o : DTransOut Γ)
    (h : translateWhileArm vm name body = some o) :
    o.Γ' = Γ := by
  unfold translateWhileArm at h
  split at h
  · cases hb : translateDialectControl vm body with
    | none => rw [hb] at h; simp at h
    | some o' =>
        rw [hb] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        rfl
  · simp at h

/-! ## 2. The back-edge emission (`translateWhileLcmd`) — `whileLcmd` composes

The real loop the front arm stands in for is emitted at the `Lcmd` level. The
owned backend already gives the exact combinator: `whileLcmd` — a do-while whose
back-edge tests a **runtime** predicate register (the guard variable `gReg`),
constant-size in the (data-dependent) trip count. For the countdown idiom
(`while (name != 0)` with the body leaving the counter in `name`) the
guard-compute prefix is empty, so we pass `guard = []` and `gReg = name`. This
reuses `whileLcmd` verbatim — no `Lcmd` is hand-authored. -/

/-- **The back-edge half.** Wrap a rendered body `Lcmd` in the owned backend's
    data-dependent `whileLcmd`: `Llabel top ; body ; CMP name,#0 ; Lcond NZ → top`
    (renders `.L: … ; cmpq $0,%name ; jne .L`). `w` is the guard width, `gReg`
    the `RWhileNz` guard variable `name`, and `guard = []` for the countdown
    idiom (body leaves the counter in `gReg`). Reuses `whileLcmd` directly. -/
def translateWhileLcmd (w : Nat) (top : LLabel) (gReg : String) (bodyLcmd : Lcmd) :
    Lcmd :=
  whileLcmd w top gReg [] bodyLcmd

/-- The emission begins with the loop label (the back-edge target) — inherited
    from `whileLcmd_head`, confirming `whileLcmd` composed cleanly. -/
theorem translateWhileLcmd_head (w : Nat) (top : LLabel) (gReg : String)
    (bodyLcmd : Lcmd) :
    (translateWhileLcmd w top gReg bodyLcmd).head?
      = some ⟨0, .Llabel .internal top⟩ :=
  whileLcmd_head w top gReg [] bodyLcmd

/-- The emission ends with the conditional back-edge `Lcond NZ → top`
    (`jne .L<top>`, taken iff the runtime guard `gReg` is nonzero) — inherited
    from `whileLcmd_last`. A **real** data-dependent loop, not a static unroll. -/
theorem translateWhileLcmd_last (w : Nat) (top : LLabel) (gReg : String)
    (bodyLcmd : Lcmd) :
    (translateWhileLcmd w top gReg bodyLcmd).getLast?
      = some ⟨0, .Lcond (.reg "NZ") top⟩ :=
  whileLcmd_last w top gReg [] bodyLcmd

/-- Constant-size in the (data-dependent) trip count: body + 3 control instrs
    (label, compare, back-edge). Inherited from `whileLcmd_length` at empty
    guard-compute. -/
theorem translateWhileLcmd_length (w : Nat) (top : LLabel) (gReg : String)
    (bodyLcmd : Lcmd) :
    (translateWhileLcmd w top gReg bodyLcmd).length = bodyLcmd.length + 3 := by
  simp [translateWhileLcmd, whileLcmd_length]

/-! ## 3. Validation: a tiny concrete `while (n != 0) { … }`

Single-body validation (KeccakRoundFrontEmit-sized): a bound `sword 64` guard
`n` and a **covered** loop body pushed through both halves. The countdown body a
real grind uses (`n := n - 1`, the `RScalarSetExpr "n" (SExpr.subOne "n")` idiom)
lowers through the separate `RScalarSetExpr` front (a leaf op the covered
fragment declines); here we validate the *loop plumbing* with a covered body
(`n := 0`, `RScalarSet` — trivially terminating), which is exactly what the
`RWhileNz` arm gates on. -/

/-- A `VarMap` binding the guard `n` as a 64-bit scalar. -/
def demoVM : VarMap [CryptoTy.sword 64] :=
  (VarMap.empty).bind (t := .sword 64) "n"

/-- The tiny data-dependent while: `while (n != 0) { n := 0 }`. -/
def demoWhile : LowCT := .RWhileNz "n" (.RScalarSet "n" 0)

/-- **(a) The front arm accepts the loop.** The guard is a bound scalar and the
    body front-compiles, so `translateWhileArm` returns `some`. -/
theorem demoWhile_frontArm_isSome :
    (translateWhileArm demoVM "n" (.RScalarSet "n" 0)).isSome := by
  rfl

/-- **(b) The accepted loop is context-invariant** (`Γ' = Γ`): the loop body's
    bindings are loop-scoped and do not escape into the outer context. -/
theorem demoWhile_frontArm_ctx_invariant
    (o : DTransOut [CryptoTy.sword 64])
    (h : translateWhileArm demoVM "n" (.RScalarSet "n" 0) = some o) :
    o.Γ' = [CryptoTy.sword 64] :=
  translateWhileArm_ctx_invariant demoVM "n" (.RScalarSet "n" 0) o h

/-- **(c) The emitted loop carries a real back-edge.** Wrapping a one-instruction
    countdown body (`SUB n,1` stand-in) in `translateWhileLcmd` ends with the
    conditional back-edge `Lcond NZ → top` — a genuine `jne .L`, not an unroll. -/
theorem demoWhile_backEdge_last :
    (translateWhileLcmd 64 0 "n" [⟨0, .Lopn [.reg "n"] "SUB" [.reg "n", .imm 1]⟩]).getLast?
      = some ⟨0, .Lcond (.reg "NZ") 0⟩ :=
  translateWhileLcmd_last 64 0 "n" _

/-! ## 4. Core-integration recipe (for the orchestrator)

Wiring this into `translateDialectControl` proper is a **one-arm replacement** in
`TranslateDialectDirectControl.lean`. Replace the current declining arm

```
  | .RWhileNz _ _ => … none
```

with

```
  | .RWhileNz name body =>
      match vm.lookup name with
      | some ⟨.sword _, _⟩ =>
          (translateDialectControl vm body).map
            (fun _ => { Γ' := Γ, cont := ComCont.id, vm := vm })
      | _ => none
```

i.e. `translateWhileArm`'s body inlined (it must be *inline* so the recursive
`translateDialectControl vm body` sits inside the same `def`, not a forward
reference).

**Invariant the arm must preserve** (matching the `RIfNz` case-(A)/(B) shape,
where a non-extending branch passes `⟨Γ, vm⟩` through): the `RWhileNz` arm is
**context-invariant** — it always emits `Γ' = Γ` and the entry `vm`, regardless
of what the body does internally, because the body's bindings are loop-scoped.
`translateWhileArm_ctx_invariant` is exactly this obligation; the coverage /
context-agreement extension (`IsCoveredCtl.rWhileNz : IsCoveredCtl body →
IsCoveredCtl (.RWhileNz name body)` plus the matching
`translateDialectControl_*_ctx_agree` case) then reduces to
`translateWhileArm_isSome_of_body` on the body — the arm succeeds iff the body
does, at the unchanged context.

**What the `DTransOut` does NOT carry**: the actual back-edge. `cont = ComCont.id`
is a placeholder — the `catCryptDialect` `Com` substrate has no label/branch
node, so the real loop is emitted downstream at the `Lprog`/`Lcmd` level by
`translateWhileLcmd` / `TranslateDialectDataWhile.rolledWhileNz` (guard-driven
`whileLcmd` / `whileLinstrRM`). The front arm's sole job is the context plumbing
(gate + invariant) that lets `translateDialectControl` *accept* an `RWhileNz`
node and hand the body to the loop emitter; the emitter supplies the trip
(read off the run) and the consumer a fuel/variant termination bound. Closing
the front↔`Lprog` handoff into one `DTransOut` would require adding a
`while`-region node to `catCryptDialect` (so `ComCont` could host the back-edge);
until then the two-level split (this arm + `rolledWhileNz`) is the design. -/

end CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectWhilePrototype
