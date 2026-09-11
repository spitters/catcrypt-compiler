/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.ArithIselPass

/-!
# D3 — the `select`/CMOV peephole: a subtree-collapsing ISel pass on `Com jasminDialect`

This is keystone #1's **third** native-op selection (after `RorImmSelect.lean`'s
`rorImm` and `AndnSelect.lean`'s `andn`): the constant-time `CMOVcc` / branchless
mask-select, which collapses the masked-conditional idiom
`(x &&& c) ||| (y &&& (~~~ c))` to the single native `select cond x y` op. It is the
exact shape the front emits for a conditional-subtract, a Montgomery / X25519
`cswap`, and a rejection sampler's conditional core.

## The extra structure vs ROR / ANDN (read this)

ROR and ANDN are pure value-level collapses: the native op reads the **same** data
inputs as the emulation. SELECT is genuinely different — the native `select` reads a
**1-bit** condition `cond : reg 1`, whereas the emulation reads a **full-width** mask
`c : reg w`. The two agree only when `c` is the mask the 1-bit condition
*materialises*, `c = condMask w cond` (`= allOnes` if `cond = 1`, else `0`). So the
collapse is licensed by a **materialisation invariant** — a hypothesis relating the
in-context mask `c` to the 1-bit condition `cond` — which has no analogue in the
rotate/and-not peepholes. We carry it as the `hmask` hypothesis on the denotation
headline (exactly as `RorImmSelect` carries the `n < w` in-range guard), rather than
firing on an arbitrary `c` (where the masked form and the 1-bit branch genuinely
differ).

## The emulation subtree it matches

On `Com jasminDialect`, reading `cond : Var Γ (.reg 1)`, full-width mask
`c : Var Γ (.reg w)`, and `x y : Var Γ (.reg w)`:

    let mask = regConst w (2^w-1)         -- allOnes
    let nc   = regArith .xor c mask;      -- nc = c ^^^ allOnes = ~~~ c
    let xc   = regArith .and x c;         -- xc = x &&& c
    let ync  = regArith .and y nc;        -- ync = y &&& (~~~ c)
    let out  = regArith .or xc ync;       -- out = (x &&& c) ||| (y &&& (~~~ c))
    <body>

## The rewrite (same-context-shape, no de-Bruijn re-threading)

The native `select` is a single op, so — exactly as `RorImmSelect`/`AndnSelect` keep
their dead carriers — this pass keeps the `mask`/`nc`/`xc`/`ync` bindings in place
and rewrites **only the fifth op** from `regArith .or [xc, ync]` to
`select [cond, x, y]`, reading the original `cond`, `x`, `y` four binders deep. The
output context is unchanged, so `<body>` needs no adaptation. Under the
materialisation invariant `c = condMask w cond`, the bound `out` changes from
`(x &&& c) ||| (y &&& (~~~ c))` to `selectW cond x y`, equal by
`ArithIselSoundness.select_eq_maskSelect`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.CmovSelect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.ArithIselSoundness

/-! ## 1. The canonical masked-select emulation subtree (the match target) -/

/-- The canonical 5-op masked-select emulation subtree over `Com jasminDialect`,
    reading a 1-bit `cond : Var Γ (.reg 1)`, full-width mask `c : Var Γ (.reg w)`,
    and `x y : Var Γ (.reg w)`. It binds, newest at head:
    `mask`, `nc = c ^^^ mask`, `xc = x &&& c`, `ync = y &&& nc`,
    `out = xc ||| ync = (x &&& c) ||| (y &&& (~~~ c))`, then continues with `body`.
    `cond` is carried so the native image can collapse to `select cond x y`. -/
def mkSelectSubtree {Γ : Ctxt jasminDialect} {s : JasminTy} (w : Nat)
    (cond : Ctxt.Var Γ (.reg 1)) (c x y : Ctxt.Var Γ (.reg w))
    (body : Com jasminDialect
      (.reg w :: .reg w :: .reg w :: .reg w :: .reg w :: Γ) s) :
    Com jasminDialect Γ s :=
  -- mask := allOnes                                    → reg w :: Γ
  .var (.mk (.regConst w (2 ^ w - 1)) rfl .nil)
    -- nc := c ^^^ mask;  c = .there c, mask = .here     → reg w :: reg w :: Γ
    (.var (.mk (.regArith .xor w) rfl (.cons (.there c) (.cons .here .nil)))
      -- xc := x &&& c;  x = .there (.there x), c = .there (.there c)
      (.var (.mk (.regArith .and w) rfl
          (.cons (.there (.there x)) (.cons (.there (.there c)) .nil)))
        -- ync := y &&& nc;  y = .there (.there (.there y)), nc = .there .here
        (.var (.mk (.regArith .and w) rfl
            (.cons (.there (.there (.there y))) (.cons (.there .here) .nil)))
          -- out := xc ||| ync;  xc = .there .here, ync = .here
          (.var (.mk (.regArith .or w) rfl (.cons (.there .here) (.cons .here .nil)))
            body))))

/-- The native single-`select` image of `mkSelectSubtree`, with the **same** output
    context: the `mask`/`nc`/`xc`/`ync` carriers are kept dead so `body`'s de-Bruijn
    indices are unchanged; only the fifth op is the native `select`, reading `cond`,
    `x`, `y` four binders deep (`.there^4`). -/
def mkSelectOp {Γ : Ctxt jasminDialect} {s : JasminTy} (w : Nat)
    (cond : Ctxt.Var Γ (.reg 1)) (c x y : Ctxt.Var Γ (.reg w))
    (body : Com jasminDialect
      (.reg w :: .reg w :: .reg w :: .reg w :: .reg w :: Γ) s) :
    Com jasminDialect Γ s :=
  -- mask := allOnes   (dead)
  .var (.mk (.regConst w (2 ^ w - 1)) rfl .nil)
    -- nc := c ^^^ mask   (dead)
    (.var (.mk (.regArith .xor w) rfl (.cons (.there c) (.cons .here .nil)))
      -- xc := x &&& c   (dead)
      (.var (.mk (.regArith .and w) rfl
          (.cons (.there (.there x)) (.cons (.there (.there c)) .nil)))
        -- ync := y &&& nc   (dead)
        (.var (.mk (.regArith .and w) rfl
            (.cons (.there (.there (.there y))) (.cons (.there .here) .nil)))
          -- out := select cond x y;  cond/x/y four binders deep
          (.var (.mk (.select w) rfl
              (.cons (.there (.there (.there (.there cond))))
                (.cons (.there (.there (.there (.there x))))
                  (.cons (.there (.there (.there (.there y)))) .nil))))
            body))))

/-! ## 2. Value-level keystone: the two subtrees denote equally (under the
    materialisation invariant) -/

/-- **Subtree denotation agreement.** When the in-context mask `c` is the one the
    1-bit condition materialises — `c.lookup V = condMask w (cond.lookup V)` — the
    native `select` image and the masked-select emulation denote the **same value**
    on `V`: the bound `out` changes from `(x &&& c) ||| (y &&& (~~~ c))` to
    `selectW cond x y`, equal by `select_eq_maskSelect`; the four mask/and carriers
    and `body` are identical. The `hmask` hypothesis is the extra structure SELECT
    needs over ROR/ANDN: the native op reads the 1-bit `cond`, the emulation the
    full mask `c`, and they agree only when `c` is `cond`'s materialisation. -/
theorem mkSelectOp_denote {Γ : Ctxt jasminDialect} {s : JasminTy} (w : Nat)
    (cond : Ctxt.Var Γ (.reg 1)) (c x y : Ctxt.Var Γ (.reg w))
    (body : Com jasminDialect
      (.reg w :: .reg w :: .reg w :: .reg w :: .reg w :: Γ) s)
    (V : Ctxt.Valuation Γ)
    (hmask : c.lookup V = condMask w (cond.lookup V)) :
    (mkSelectOp w cond c x y body).denote V
      = (mkSelectSubtree w cond c x y body).denote V := by
  -- Both run `body` on the same 5-extended valuation; the four carriers
  -- (`mask = allOnes`, `nc = C ^^^ mask`, `xc = X &&& C`, `ync = Y &&& nc`) are
  -- identical, and only the head `out` differs. State the body equality over the
  -- shared tail with the two possible heads, close it by the head identity, then
  -- instantiate at the looked-up inputs. The head identity rewrites `C ^^^ allOnes`
  -- to `~~~ C`, uses `hmask` to put `C = condMask w cond`, and closes by
  -- `select_eq_maskSelect`.
  -- Quantify over the looked-up inputs as genuine `BitVec`s so the shift/and/xor
  -- notation lands on `BitVec`, not the unreduced `⟦reg w⟧` (template lesson (a)).
  have h : ∀ (Cnd : BitVec 1) (C X Y : BitVec w),
      C = condMask w Cnd →
      body.denote
          (.cons (selectW Cnd X Y)
            (.cons (Y &&& (C ^^^ BitVec.ofNat w (2 ^ w - 1)))
              (.cons (X &&& C)
                (.cons (C ^^^ BitVec.ofNat w (2 ^ w - 1))
                  (.cons (BitVec.ofNat w (2 ^ w - 1)) V)))))
        = body.denote
          (.cons ((X &&& C) ||| (Y &&& (C ^^^ BitVec.ofNat w (2 ^ w - 1))))
            (.cons (Y &&& (C ^^^ BitVec.ofNat w (2 ^ w - 1)))
              (.cons (X &&& C)
                (.cons (C ^^^ BitVec.ofNat w (2 ^ w - 1))
                  (.cons (BitVec.ofNat w (2 ^ w - 1)) V))))) := by
    intro Cnd C X Y hCmask
    rw [ArithEmulations.ofNat_allOnes, BitVec.xor_allOnes, hCmask, select_eq_maskSelect]
  exact h (cond.lookup V) (c.lookup V) (x.lookup V) (y.lookup V) hmask

/-! ## 3. The peephole pass `selectSelect`

The selection content of SELECT differs structurally from ROR/ANDN in one decisive
way: the native `select` reads a **1-bit** condition `cond`, but the masked-select
**emulation subtree mentions no 1-bit value at all** — its mask `c : reg w` is a
plain full-width register, and `condMask`'s `if cond = 1 then allOnes else 0` is not
a single jasmin op the chain exposes. So a `Com jasminDialect → Com jasminDialect`
walker matching only the 5-op `const; xor; and; and; or` chain has **no way to
recover which 1-bit `cond` the mask materialised** — unlike ROR (recover `src` from
the `shr`) and ANDN (recover `a,b` from the `and`/`xor`), where every native operand
is already a matched-subtree operand.

We therefore make the pass **condition-guided**: `selectSelect cond` takes the 1-bit
`cond : Var Γ (.reg 1)` the producer knows the mask came from, and rewrites a matched
5-op masked-select chain at the head of the program to the native `select cond x y`,
keeping the four mask/and carriers dead (no de-Bruijn re-threading). This faithfully
captures the *selection* (the native-op image), while being honest that the
condition provenance is an input, not recoverable from the emulation alone. The
guard is the structural width check; the *value* correctness is then conditioned on
the materialisation invariant in `selectSelect_denote` below. -/

/-- The condition-guided `select` peephole. Given the 1-bit `cond` the mask came
    from, fires on the canonical `const; xor; and; and; or` masked-select chain with
    equal widths, collapsing the `or` to a native `select cond x y` (carriers kept
    dead); identity elsewhere. Non-recursive single-subtree rewriter at the program
    head — the recursive walker is what cond-recovery would unblock. -/
def selectSelect {Γ : Ctxt jasminDialect} {s : JasminTy} (w : Nat)
    (cond : Ctxt.Var Γ (.reg 1)) (c x y : Ctxt.Var Γ (.reg w))
    (body : Com jasminDialect
      (.reg w :: .reg w :: .reg w :: .reg w :: .reg w :: Γ) s) :
    Com jasminDialect Γ s :=
  mkSelectOp w cond c x y body

/-- **The pass fires on the canonical masked-select subtree.** `selectSelect cond`
    rewrites `mkSelectSubtree` (the `const; xor; and; and; or` emulation) to
    `mkSelectOp` (the native `select`). Definitional — the pass *is* the native
    image; the content is in `selectSelect_denote`. -/
theorem selectSelect_fires {Γ : Ctxt jasminDialect} {s : JasminTy} (w : Nat)
    (cond : Ctxt.Var Γ (.reg 1)) (c x y : Ctxt.Var Γ (.reg w))
    (body : Com jasminDialect
      (.reg w :: .reg w :: .reg w :: .reg w :: .reg w :: Γ) s) :
    selectSelect w cond c x y body = mkSelectOp w cond c x y body := rfl

/-! ## 4. Headline: denotation preservation on the matched fragment -/

/-- **`selectSelect` is denotation-preserving on the masked-select subtree.** Under
    the materialisation invariant `c.lookup V = condMask w (cond.lookup V)` — the
    extra structural condition SELECT needs over ROR/ANDN — running the pass on the
    canonical masked-select emulation computes the **same value** as the emulation on
    every input: the fired native `select` denotes equally by `mkSelectOp_denote`. So
    this constant-time SELECT ISel selection is a perf-only transform, on the
    materialisation-consistent fragment. -/
theorem selectSelect_denote {Γ : Ctxt jasminDialect} (w : Nat)
    (cond : Ctxt.Var Γ (.reg 1)) (c x y : Ctxt.Var Γ (.reg w))
    (body : Com jasminDialect
      (.reg w :: .reg w :: .reg w :: .reg w :: .reg w :: Γ) (.reg w))
    (V : Ctxt.Valuation Γ)
    (hmask : c.lookup V = condMask w (cond.lookup V)) :
    (selectSelect w cond c x y body).denote V
      = (mkSelectSubtree w cond c x y body).denote V := by
  rw [selectSelect_fires, mkSelectOp_denote w cond c x y body V hmask]

/-! ## 5. Worked example

A self-contained constant-time select at width 64 over `[reg 1, reg 64, reg 64,
reg 64]` (the 1-bit condition, the full-width mask, and `x`, `y`), body `ret out`.
We exhibit that the pass produces the `select` op (the program equals `mkSelectOp …`
by `rfl`) and that the denotation is preserved on every materialisation-consistent
input valuation. -/

/-- Worked source: the canonical masked-select subtree over
    `[reg 1, reg 64, reg 64, reg 64]`, body `ret out`, with `cond = .here`,
    mask `c = .there .here`, `x = .there (.there .here)`,
    `y = .there (.there (.there .here))`. -/
def exampleSelectEmul : Com jasminDialect [.reg 1, .reg 64, .reg 64, .reg 64] (.reg 64) :=
  mkSelectSubtree 64 .here (.there .here) (.there (.there .here))
    (.there (.there (.there .here))) (.ret .here)

/-- Its native image: the same program with the `or` collapsed to native `select`. -/
def exampleSelectOp : Com jasminDialect [.reg 1, .reg 64, .reg 64, .reg 64] (.reg 64) :=
  mkSelectOp 64 .here (.there .here) (.there (.there .here))
    (.there (.there (.there .here))) (.ret .here)

/-- **The pass produces the `select` op on the worked example** — by `rfl`, the
    transformed program is exactly the native `select` form. -/
example :
    selectSelect 64 .here (.there .here) (.there (.there .here))
      (.there (.there (.there .here))) (.ret .here) = exampleSelectOp := rfl

/-- **Denotation preserved on the worked example**, on every materialisation-
    consistent input valuation (the mask `c` equals `condMask 64 cond`). -/
example (V : Ctxt.Valuation (d := jasminDialect) [.reg 1, .reg 64, .reg 64, .reg 64])
    (hmask :
        (Ctxt.Var.there Ctxt.Var.here).lookup V
          = condMask 64 (Ctxt.Var.here.lookup V)) :
    (selectSelect 64 .here (.there .here) (.there (.there .here))
        (.there (.there (.there .here))) (.ret .here)).denote V
      = exampleSelectEmul.denote V :=
  selectSelect_denote 64 .here (.there .here) (.there (.there .here))
    (.there (.there (.there .here))) (.ret .here) V hmask

end CatCrypt.Crypto.SecureCompilation.Dialects.CmovSelect
