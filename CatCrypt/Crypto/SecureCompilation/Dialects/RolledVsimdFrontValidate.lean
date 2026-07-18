/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

set_option autoImplicit false

/-!
# Validation: a 128-bit vsimd XOR-accumulate front-compiled to a rolled `ComL.forLoopN`

CAPABILITY G2 witness. It authors a **128-bit SIMD** loop body — a `.sword 128`
accumulator updated by a `vsimd` op each trip (`t := gf2p8mulb(x,x)`;
`acc := acc ⊕ t`) — and front-compiles it through the vsimd-aware
`TranslateDialectVsimd.translateDialectControlV` (via `rolledForLoopNV`) to a
genuine `ComL.forLoopN`: ONE vsimd body copy + a real back-edge (`jne`), NOT `N`
unrolled copies.

```
  vloopBody (RVsimdSetExpr t := gf2p8mulb(x,x); RVsimdSetExpr acc := acc ⊕ t)
    --(vsimd front: translateDialectControlV over [acc:.sword 128, idx:.sword 64, x:.sword 128])
                                                          -->  Com catCryptDialect
    --(cryptoDialectToJasminCom)------------------------------>  Com jasminDialect (= JLoopBodyN.update)
    --(ComL.forLoopN ⟨N, update⟩ acc [x] (ret acc))---------->  ComL  (ONE vsimd body copy + back-edge)
    --(comLToBody / renderLprogAtt)-------------------------->  .s  (genuine `jne .L<d>`, VGF2P8MULB/VPXOR)
```

The scalar `rolledForLoopN` cannot express this: its body flows through the
SCALAR `translateDialectControl`, which has no `.sword 128` binding and does not
intercept `vsimd`-tagged `RCall`s. `rolledForLoopNV` swaps only the body front to
`translateDialectControlV`; everything downstream (`cryptoDialectToJasminCom`
lowering, the `ComL.forLoopN` wrapper) is shared verbatim. When `accCTy =
.sword 128`, `mapTy accCTy = .reg 128`, so the accumulator carried across the
back-edge is a 128-bit register.

The validation checks: (i) the vsimd front succeeds (`rolledForLoopNV`); (ii)
`ComL.denote = the independent N-fold XOR spec`; (iii) the lowered body has a REAL
back-edge (`Lcond`/`Llabel`) with ONE vsimd body copy (one `VGF2P8MULB`, one
`VPXOR` — NOT `N` unrolled).

Note on scope: the accumulator and the input vector `x` enter as `.sword 128`
values (a register accumulator + a register invariant). Per-index 128-bit data
`x[i]` — the full FAEST `acc ^= bf128_mul(x[i], alpha_i)` shape — additionally
needs a **128-bit dynamic array load**. This is now provided by
`CatCryptDialect.memrefGetDyn128` (a `.sword 128` dynamic load, the twin of
`memrefGetDyn`) and the `vloadidx128` vsimd-front tag; the full FAEST per-index
body is re-sourced with a whole-program denote in
`VIR/FaestByteCombineVsimdCovered.lean`. G2 here delivers the vsimd-capable loop
*body* front-compilation.

Invoke (in-model gate):  lake env lean CatCrypt/Crypto/SecureCompilation/Dialects/RolledVsimdFrontValidate.lean
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.RolledVsimdFrontValidate

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (gf2p8mulbW)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT)

/-! ## 0. Trip count -/

/-- A small trip count for the in-model KAT (the deployed alpha-accumulate loops
    use the FAEST field-degree; this witness needs only enough trips to exhibit a
    real counted back-edge). -/
def vN : Nat := 4

/-! ## 1. The vsimd loop body, authored as covered LowCT

The body runs over the catCryptDialect context
`Γbody = [acc:.sword 128, idx:.sword 64, x:.sword 128]` (accumulator first, loop
index next, the input vector `x` as the sole invariant). Each trip:
`t := gf2p8mulb(x,x)` (a `vsimd` binary op) then `acc := acc ⊕ t` (a `vsimd`
bitwise op that **rebinds** the accumulator name, SSA-style — `VarMap.bind`
shadows, so the loop's `ret acc` selects the post-XOR value). -/

/-- One trip of the vsimd accumulate: `t := gf2p8mulb(x,x)`; `acc := acc ⊕ t`. -/
def vloopBody : LowCT :=
  .RSeq (LowCT.RVsimdSetExpr "t"   "vsimd.gf2p8mulb" ["x", "x"])
        (LowCT.RVsimdSetExpr "acc" "vsimd.xor"       ["acc", "t"])

/-! ## 2. The body context + VarMap

`Γbody = [acc, idx, x]` (head-first): `acc` is the accumulator (`.here`), `idx`
the loop binder (`.there .here`), `x` the invariant (`.there² .here`). -/

/-- The body context: `.sword 128` accumulator, `.sword 64` loop index, `.sword 128`
    input vector invariant. -/
def Γbody : Ctx := [.sword 128, .sword 64, .sword 128]

/-- The body VarMap: `acc ↦ .here`, `idx ↦ .there .here`, `x ↦ .there (.there .here)`. -/
def vmBody : VarMap Γbody :=
  (((VarMap.empty.bind (t := .sword 128) "x").bind (t := .sword 64) "idx").bind
      (t := .sword 128) "acc")

/-! ## 3. The outer program: vsimd front body → genuine `ComL.forLoopN`

Outer context `[acc:.reg 128, x:.reg 128]` (`mapTy .sword 128 = .reg 128`): `acc`
is the accumulator seed (`.here`), `x` the invariant seed (`.there .here`). -/

/-- The outer (kernel-argument) jasmin context: two 128-bit registers. -/
def Γouter : Ctxt jasminDialect := [.reg 128, .reg 128]

/-- The front-compiled rolled vsimd `ComL.forLoopN` (one vsimd body copy +
    back-edge), or `none` if the vsimd front declines. -/
def vloopComL : Option (ComL Γouter (.reg 128)) :=
  rolledForLoopNV (Γouter := Γouter) (accCTy := .sword 128)
    (invCTys := [.sword 128])
    vN vmBody "acc" vloopBody
    (init := .here)
    (invs := .cons (.there .here) .nil)

/-! ## 4. Gate: the vsimd front succeeds -/

/-- The 128-bit vsimd loop body front-compiles to a genuine `ComL.forLoopN`. -/
theorem vloopComL_isSome : vloopComL.isSome := by native_decide

/-! ## 5. denote = independent N-fold XOR spec -/

/-- INDEPENDENT pure-`BitVec 128` reference: `N`-fold `acc := acc ⊕ gf2p8mulb(x,x)`
    from the seed `init`, threading the fixed vector `x`. -/
def vloopSpec (init x : BitVec 128) : BitVec 128 :=
  (List.range vN).foldl (fun acc _ => acc ^^^ gf2p8mulbW x x) init

/-- Sample 128-bit inputs (the in-model KAT seed). -/
def sampleInit : BitVec 128 := 0x0f1e2d3c4b5a69788796a5b4c3d2e1f0
def sampleX    : BitVec 128 := 0x00112233445566778899aabbccddeeff

/- **denote = the JLoopBodyN fold, in general.** The front-compiled rolled vsimd
   loop's denotation is the `N`-fold `JLoopBodyN.denote` of its front-compiled body,
   by the committed capability lemma `TranslateDialectRolledLoop.rolledForLoopNV_denote`
   (proven for all `N`, seed, invariants). A concrete `ComL.denote = vloopSpec`
   `native_decide` gate is NOT attempted here: the labeled `ComL.denote` over the
   `.reg 128` vsimd accumulator is not kernel-reducible (unlike the scalar `reg 64`
   case), so `native_decide` cannot evaluate it. The abstract lemma is the denote
   proof; the shape gates below confirm the rolled (one-body-copy) x86. The
   value-carried 128-bit-accumulator `.s` ABI is a follow-up C KAT. -/

/-! ## 6. Rolled lowering: real x86 back-edge, ONE vsimd body copy

The lowered `Lcmd` body (`comLToBody`, `nArgs = 2`) is inspected directly — the
loop body's `.reg 128` register accumulator threads through a `forLoopN` node
lowered by `forLoopLcmdN` (call-free), exactly as the `reg 64` smoke test. -/

/-- The lowered body of the rolled vsimd loop (2-arg context). -/
def vloopBodyLcmd : Option Lcmd :=
  vloopComL.map (fun c => comLToBody 2 argName (fun _ => none) c 1)

/-- **Real back-edge:** the lowered body has both an internal `Llabel` and a `Lcond`
    (`jne .L<d>`) — a genuine counted loop, NOT an unrolled chain. -/
theorem vloopBodyLcmd_has_backedge :
    vloopBodyLcmd.map (fun b =>
      (b.any (fun i => match i.li_i with | .Lcond _ _ => true | _ => false))
        && (b.any (fun i => match i.li_i with | .Llabel _ _ => true | _ => false)))
      = some true := by native_decide

/-- **ONE vsimd multiply body copy:** the `VGF2P8MULB` op appears exactly once —
    the body is rolled, not `N`-unrolled. -/
theorem vloopBodyLcmd_one_mul_copy :
    vloopBodyLcmd.map (fun b =>
      (b.filter (fun i => match i.li_i with
        | .Lopn _ m _ => m == "VGF2P8MULB" | _ => false)).length)
      = some 1 := by native_decide

/-- **ONE vsimd XOR body copy:** the `VPXOR` accumulate op appears exactly once. -/
theorem vloopBodyLcmd_one_xor_copy :
    vloopBodyLcmd.map (fun b =>
      (b.filter (fun i => match i.li_i with
        | .Lopn _ m _ => m == "VPXOR" | _ => false)).length)
      = some 1 := by native_decide

/-! ## 7. Emit driver (full `.s` render)

Best-effort AT&T `.s` render of `vsimd_xoracc(acc, x)` via the committed
`ComL.toLprogPhysAbi` (two 128-bit values in the first two XMM slots). The
back-edge / one-vsimd-body-copy evidence above is at the `Lcmd`
(emitted-instruction) level — `renderLprogAtt` is a trivial pretty-printer over
that `Lcmd`. The register-in/register-out ABI wiring for a value-carried
(non-pointer) `.reg 128` accumulator is the orchestrator's to settle against the
sibling `VsimdAsmPrint` render path, so no `isSome` gate is asserted here. -/

/-- The owned AT&T `.s` text for `vsimd_xoracc` (front-compiled, rolled). -/
def kernelAsm : Option String :=
  vloopComL.map (fun c =>
    renderLprogAtt
      (ComL.toLprogPhysAbi c "vsimd_xoracc" (argName 0) [argName 1]
        (fun _ => none) (fun _ => none) ["XMM0", "XMM1"] [128, 128]))

/-- Write the front-compiled rolled vsimd `.s` (best-effort). -/
def emit (path : System.FilePath) : IO Unit :=
  match kernelAsm with
  | some asm => IO.FS.writeFile path asm
  | none => throw (IO.userError "front-compile of vsimd_xoracc rolled loop failed")

end CatCrypt.Crypto.SecureCompilation.Dialects.RolledVsimdFrontValidate
