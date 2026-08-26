/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-!
# Keccak θ column-parity / diffusion and π rename on the UNIFIED `Com jasminDialect`

This is the SIMD-dialect-unification migration of the cross-lane Keccak θ/π SIMD
block off the bespoke `Avx512Model` (`ZInstr`) machine. The pre-existing
realization (`KeccakThetaPiRealization.lean`) expresses the cross-lane θ/π
data flow as straight-line `ZInstr` blocks over the bespoke AVX-512 register
machine (`ZState`, `runZBlock`) in the 8-way batched Keccak packing (8 ZMM
sub-lanes carry 8 independent Keccak states):

* **θ column parity** — a four-`vpxorq` left fold over five column registers,
  `C[x] = a[x,0] ⊕ a[x,1] ⊕ a[x,2] ⊕ a[x,3] ⊕ a[x,4]`;
* **θ diffusion** — `vpsllvq` / `vpsrlvq` / `vporq` rotate-by-1 of `C[x+1]` then a
  `vpxorq` with `C[x-1]`, `D[x] = C[x-1] ⊕ rotl(C[x+1], 1)`;
* **π lane permutation** — a `vmov` register rename, `a[x,y] ↦ a[(x+3y) mod 5, x]`,
  pure data movement.

The verified Jasmin VIR dialect (`JasminDialect.lean`) already carries
`JasminOp.vpackZMM (bop)` — the carry-free 8×u64 packed-lane register op (denote
`zmmPackQ bop`). Each `ZInstr` op of the θ block maps EXACTLY onto a `vpackZMM`:

* `.vpxorq`   ↦  `JasminOp.vpackZMM .xor`   (denote `zmmPackQ .xor`)
* `.vporq`    ↦  `JasminOp.vpackZMM .or`    (denote `zmmPackQ .or`)
* `.vpsllvq`  ↦  `JasminOp.vpackZMM .shl`   (denote `zmmPackQ .shl`)
* `.vpsrlvq`  ↦  `JasminOp.vpackZMM .shr`   (denote `zmmPackQ .shr`)

The bespoke `vpsllvq` / `vpsrlvq` are the *variable* per-lane shifts
(`laneSllvQ a sh = a <<< sh.toNat`, each lane shifting by its own amount register),
which is exactly `JasminBinOp.shl` / `.shr` (`a <<< b.toNat`) applied lane-wise by
`zmmPackQ`. So the whole θ block is covered by the carry-free `vpackZMM` alphabet
— NO new `SimdOp` op is needed.

The **π rename** uses `.vmov` (a register copy, no arithmetic). In a single-output
`Com`, a pure rename is the trivial program that returns the source register
variable directly (`.ret` of the source `Var`); no op is consumed. So π also needs
no new op.

## Coverage classification

| `ZInstr` op (θ/π block) | cross-lane? | `vpackZMM` arm | new op? |
|--------------------------|-------------|----------------|---------|
| `vpxorq`  | no | `zmmPackQ .xor` | no |
| `vporq`   | no | `zmmPackQ .or`  | no |
| `vpsllvq` | no (variable lane shift) | `zmmPackQ .shl` | no |
| `vpsrlvq` | no (variable lane shift) | `zmmPackQ .shr` | no |
| `vmov` (π) | rename | trivial `.ret` of source `Var` | no |

No `vpermq` / `vpermxvarq` cross-lane permute and no `vploadc` appears in the θ/π
block (the cross-lane structure lives at the multi-register *scheduling* level, not
inside any single SIMD op), so the migration is total — every owned op of the block
is `vpackZMM`-expressible.

## What is proved here

The θ block is built from straight-line `Com jasminDialect` programs over `reg 512`
ZMM registers, off the bespoke `Avx512Model` machine:

* `parityCom` — the four-xor column fold `C = (((c0⊕c1)⊕c2)⊕c3)⊕c4`;
* `dCom` — the diffusion `D = cm ⊕ ((cp ≪ 1) ||| (cp ≫ 63))`, the explicit
  shift-decomposition of `cm ⊕ rotl(cp,1)`, over `vpackZMM .shl/.shr/.or/.xor`;
* `piCom` — the π rename as the trivial `.ret` of the source register variable.

The `*_denote` lemmas characterize each denotation by `rfl`: `Com.denote` of the
straight-line programs unfolds definitionally through the `vpackZMM` denote arm to
nested `zmmPackQ` calls, the carry-free packed semantics shared with the bespoke
`ZState` lane math (no re-proof of the lane arithmetic). This mirrors
`ButterflyBlockCom.lean`'s `vpackZMM` rfl-denote authoring.

Invoke: `lake build CatCrypt.Crypto.SecureCompilation.X86Backend.KeccakThetaPiCom`
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.KeccakThetaPiCom

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. Register type and contexts

A single `reg 512` (one ZMM 8×u64 lane-vector) is the working type. -/

/-- The `reg 512` dialect type (one ZMM 8×u64 lane-vector), abbreviated. -/
abbrev r512 : JasminTy := .reg 512

/-- The θ column-parity input context: five column registers `[c0, c1, c2, c3, c4]`,
    each `reg 512` (the five lanes `a[x,0] … a[x,4]` of one column). De Bruijn order
    `c0 = .here`, …, `c4 = .there (.there (.there (.there .here)))`. -/
abbrev parityCtx : Ctxt jasminDialect := [r512, r512, r512, r512, r512]

/-- The θ diffusion input context `[cm, cp, one, c63]`, each `reg 512`: the two
    parity registers `cm = C[x-1]` / `cp = C[x+1]` and the broadcast shift-amount
    registers `one` (= `1` in every lane) / `c63` (= `63` in every lane). -/
abbrev dCtx : Ctxt jasminDialect := [r512, r512, r512, r512]

/-! ### A single-binding `vpackZMM` denote step

The straight-line θ programs are several `vpackZMM` bindings deep. A whole-program
`rfl` forces `Com.denote` to whnf the entire nest at once (each `Expr.denote`
carries a `retTy_eq ▸` cast over `BitVec 512`), which is expensive. Instead we peel
one binding at a time with this single-layer step lemma — itself a cheap `rfl` — so
each layer's cast resolves once and the proof is a linear `rw` chain. -/

/-- **One `vpackZMM` binding peels to a `zmmPackQ` and an extended valuation.** For
    any continuation `body`, the denotation of a `vpackZMM bop` binding (over the two
    source variables `va`, `vb`) equals the continuation's denotation on the
    valuation extended by `zmmPackQ bop (va.lookup V) (vb.lookup V)`. A single-layer
    `rfl`: `Com.denote`'s `.var` arm composed with the `vpackZMM` denote arm. -/
theorem denote_var_vpackZMM {Γ : Ctxt jasminDialect} {s : JasminTy}
    (bop : JasminBinOp) (va vb : Ctxt.Var Γ r512)
    (body : Com jasminDialect (r512 :: Γ) s) (V : Ctxt.Valuation Γ) :
    (Com.var (Expr.mk (JasminOp.vpackZMM bop) rfl (.cons va (.cons vb .nil))) body).denote V
      = body.denote (V.extend (zmmPackQ bop (va.lookup V) (vb.lookup V))) :=
  rfl

/-- `Ctxt.Var.here.lookup` on an extended valuation reads the freshly bound head.
    (`Valuation.extend V v` is definitionally `.cons v V`.) -/
@[simp] theorem lookup_here_extend {Γ : Ctxt jasminDialect} {t : JasminTy}
    (V : Ctxt.Valuation Γ) (v : ⟦t⟧) :
    (Ctxt.Var.here (Γ := Γ) (t := t)).lookup (V.extend v) = v := rfl

/-- `(Ctxt.Var.there w).lookup` on an extended valuation skips the head and reads
    `w` in the tail. -/
@[simp] theorem lookup_there_extend {Γ : Ctxt jasminDialect} {t t' : JasminTy}
    (V : Ctxt.Valuation Γ) (v : ⟦t'⟧) (w : Ctxt.Var Γ t) :
    (Ctxt.Var.there (s := t') w).lookup (V.extend v) = w.lookup V := rfl

/-- `Ctxt.Var.here.lookup` on a cons valuation reads the head (the input-valuation
    form, since the de Bruijn source variables are resolved against the raw input
    `HVector`). -/
@[simp] theorem lookup_here_cons {Γ : Ctxt jasminDialect} {t : JasminTy}
    (V : Ctxt.Valuation Γ) (v : ⟦t⟧) :
    (Ctxt.Var.here (Γ := Γ) (t := t)).lookup (.cons v V) = v := rfl

/-- `(Ctxt.Var.there w).lookup` on a cons valuation skips the head and reads `w` in
    the tail. -/
@[simp] theorem lookup_there_cons {Γ : Ctxt jasminDialect} {t t' : JasminTy}
    (V : Ctxt.Valuation Γ) (v : ⟦t'⟧) (w : Ctxt.Var Γ t) :
    (Ctxt.Var.there (s := t') w).lookup (.cons v V) = w.lookup V := rfl

/-! ## 2. θ column parity `C = (((c0 ⊕ c1) ⊕ c2) ⊕ c3) ⊕ c4`

A four-`vpackZMM .xor` left fold over the five column registers, mirroring the
bespoke `parityBlock`'s four `vpxorq`. The accumulator is threaded through three
fresh intermediate bindings; each `vpackZMM .xor` consumes the running accumulator
(`.here` after the previous binding) and the next column register (shifted right by
the bindings already pushed). -/

/-- The migrated θ column-parity fold as a `Com jasminDialect` over `reg 512`
    registers — the dialect-native equivalent of the bespoke `parityBlock`'s four
    `vpxorq`: `C = (((c0 ⊕ c1) ⊕ c2) ⊕ c3) ⊕ c4`. -/
def parityCom : Com jasminDialect parityCtx r512 :=
  -- ct1 := c0 ⊕ c1   (c0 = .here, c1 = .there .here)
  .var (.mk (.vpackZMM .xor) rfl
          (.cons .here (.cons (.there .here) .nil)))
    -- ct2 := ct1 ⊕ c2   (ct1 = .here; c2 = .there (.there (.there .here)))
    (.var (.mk (.vpackZMM .xor) rfl
            (.cons .here (.cons (.there (.there (.there .here))) .nil)))
      -- ct3 := ct2 ⊕ c3   (ct2 = .here; c3 = .there (.there (.there (.there (.there .here)))))
      (.var (.mk (.vpackZMM .xor) rfl
              (.cons .here
                (.cons (.there (.there (.there (.there (.there .here))))) .nil)))
        -- cpar := ct3 ⊕ c4   (ct3 = .here; c4 = 7 `.there`s deep)
        (.var (.mk (.vpackZMM .xor) rfl
                (.cons .here
                  (.cons (.there (.there (.there (.there (.there (.there (.there .here)))))))
                    .nil)))
          (.ret .here))))

/-- **θ column-parity denotation pin.** On any column valuation
    `⟨c0, c1, c2, c3, c4⟩`, `parityCom` denotes to the verified-dialect packed xor
    fold `zmmPackQ .xor (zmmPackQ .xor (zmmPackQ .xor (zmmPackQ .xor c0 c1) c2) c3) c4`
    — exactly `C[x] = a[x,0] ⊕ … ⊕ a[x,4]`, the value the bespoke `parityBlock`
    writes into `"cpar"` lane-by-lane. -/
theorem parityCom_denote (c0 c1 c2 c3 c4 : BitVec 512) :
    parityCom.denote (.cons c0 (.cons c1 (.cons c2 (.cons c3 (.cons c4 .nil)))))
      = zmmPackQ .xor (zmmPackQ .xor (zmmPackQ .xor (zmmPackQ .xor c0 c1) c2) c3) c4 := by
  rw [parityCom, denote_var_vpackZMM, denote_var_vpackZMM, denote_var_vpackZMM,
    denote_var_vpackZMM]
  rfl

/-! ## 3. θ diffusion `D = cm ⊕ ((cp ≪ 1) ||| (cp ≫ 63))`

The rotate-by-1 of `cp = C[x+1]` via the explicit shift decomposition: one
`vpackZMM .shl` (`cp ≪ one`), one `vpackZMM .shr` (`cp ≫ c63`), one `vpackZMM .or`,
then a `vpackZMM .xor` against `cm = C[x-1]`. Mirrors the bespoke `dBlock`'s
`vpsllvq`/`vpsrlvq`/`vporq`/`vpxorq`. The shift amounts are supplied as the
broadcast registers `one` / `c63` (each holding `1` / `63` in every lane). -/

/-- The migrated θ diffusion as a `Com jasminDialect` over `reg 512` registers — the
    dialect-native equivalent of the bespoke `dBlock`: with `cm = C[x-1]`,
    `cp = C[x+1]`, `one`/`c63` the broadcast amounts, compute
    `D = cm ⊕ ((cp ≪ 1) ||| (cp ≫ 63))`. The bespoke `vpsllvq`/`vpsrlvq` variable
    per-lane shifts are `vpackZMM .shl`/`.shr` (`a <<< b.toNat` lane-wise). -/
def dCom : Com jasminDialect dCtx r512 :=
  -- dsl := cp ≪ one   (cp = .there .here, one = .there (.there .here))
  .var (.mk (.vpackZMM .shl) rfl
          (.cons (.there .here) (.cons (.there (.there .here)) .nil)))
    -- dsr := cp ≫ c63   (under [dsl,cm,cp,one,c63]: cp = .there (.there .here),
    --                    c63 = .there (.there (.there (.there .here))))
    (.var (.mk (.vpackZMM .shr) rfl
            (.cons (.there (.there .here))
              (.cons (.there (.there (.there (.there .here)))) .nil)))
      -- drot := dsl ||| dsr   (under [dsr,dsl,…]: dsl = .there .here, dsr = .here)
      (.var (.mk (.vpackZMM .or) rfl
              (.cons (.there .here) (.cons .here .nil)))
        -- dout := cm ⊕ drot   (under [drot,dsr,dsl,cm,cp,one,c63]: cm = index 3
        --                      = 3 `.there`s deep, drot = .here)
        (.var (.mk (.vpackZMM .xor) rfl
                (.cons (.there (.there (.there .here))) (.cons .here .nil)))
          (.ret .here))))

/-- **θ diffusion denotation pin.** On any valuation `⟨cm, cp, one, c63⟩`, `dCom`
    denotes to `zmmPackQ .xor cm (zmmPackQ .or (zmmPackQ .shl cp one) (zmmPackQ .shr cp c63))`
    — the verified-dialect packed `cm ⊕ ((cp ≪ one) ||| (cp ≫ c63))`, the explicit
    shift-decomposition of `cm ⊕ rotl(cp,1)` (when `one`/`c63` broadcast `1`/`63`),
    exactly the value the bespoke `dBlock` writes into `"dout"` lane-by-lane. -/
theorem dCom_denote (cm cp one c63 : BitVec 512) :
    dCom.denote (.cons cm (.cons cp (.cons one (.cons c63 .nil))))
      = zmmPackQ .xor cm
          (zmmPackQ .or (zmmPackQ .shl cp one) (zmmPackQ .shr cp c63)) := by
  rw [dCom, denote_var_vpackZMM, denote_var_vpackZMM, denote_var_vpackZMM,
    denote_var_vpackZMM]
  simp only [Com.denote, lookup_here_extend, lookup_there_extend]
  rfl

/-! ## 4. π lane permutation — the `vmov` rename as a trivial `Com`

π performs no arithmetic; it renames a lane position `a[x,y] ↦ a[(x+3y) mod 5, x]`.
In a single-output `Com`, the bespoke `vmov dst src` rename is the trivial program
that returns the source register variable directly — no `vpackZMM` (and no op at
all) is consumed. We give it over the single-register context `[src]`. -/

/-- The π source-register context: one `reg 512`, the source lane register
    `lreg ((x+3y) mod 5) x` of the bespoke `piBlock`. -/
abbrev piCtx : Ctxt jasminDialect := [r512]

/-- The migrated π rename as a `Com jasminDialect`: the trivial program returning the
    source register variable (`.here`). This is the dialect-native equivalent of the
    bespoke `piBlock`'s single `vmov "pdst" (lreg …)`: pure data movement, no op. -/
def piCom : Com jasminDialect piCtx r512 :=
  .ret .here

/-- **π rename denotation pin.** On any valuation `⟨src⟩`, `piCom` denotes to `src`
    — the source register unchanged, exactly the `vmov` data movement the bespoke
    `piBlock` writes into `"pdst"`. π is pure movement: an identity on the source. -/
theorem piCom_denote (src : BitVec 512) :
    piCom.denote (.cons src .nil) = src :=
  rfl

/-! ## 5. The θ block packaged

The two arithmetic θ pieces — parity fold and diffusion mix — packaged together,
the dialect-native realization of the bespoke `parityBlock`/`dBlock` pair off the
`ZInstr` machine, both characterized by the verified-dialect `zmmPackQ` packed
semantics. -/

/-- `parityCom`/`dCom` compute the θ column parity and diffusion in the verified
    `Com jasminDialect`: `C = (((c0⊕c1)⊕c2)⊕c3)⊕c4` and
    `D = cm ⊕ ((cp ≪ one) ||| (cp ≫ c63))`, mirroring the bespoke θ blocks. -/
theorem thetaCom_realizes
    (c0 c1 c2 c3 c4 cm cp one c63 : BitVec 512) :
    parityCom.denote (.cons c0 (.cons c1 (.cons c2 (.cons c3 (.cons c4 .nil)))))
        = zmmPackQ .xor (zmmPackQ .xor (zmmPackQ .xor (zmmPackQ .xor c0 c1) c2) c3) c4
      ∧ dCom.denote (.cons cm (.cons cp (.cons one (.cons c63 .nil))))
        = zmmPackQ .xor cm
            (zmmPackQ .or (zmmPackQ .shl cp one) (zmmPackQ .shr cp c63)) :=
  ⟨parityCom_denote c0 c1 c2 c3 c4, dCom_denote cm cp one c63⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.KeccakThetaPiCom
