/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent

/-!
# Pair-elimination pass: `bvAdd64`/`bvAdc` → single-output carry twins

The SExpr-natural full-word carry ops `bvAdd64 w`/`bvAdc w` return a **pair**
`.pair (.sword w) (.sword w)` (the carry-out word and the sum word). The
dialect→jasmin lowering maps `.pair` to `.reg 0`, so a pair node is
**unlowerable** — the carry class is stuck at the pair.

The single-output twins `bvAddCarryLo w`/`bvAddCarryHi w` (carry as a `.sword 1`)
DO lower, 1:1, to the jasmin `addCarryLo`/`addCarryHi` ops (the `ADCX`/`ADOX`
backend, `DialectToJasminComCorrect`). This module supplies the missing compiler
piece: a `Com catCryptDialect → Com catCryptDialect` **pair-elimination pass**
that rewrites each pair node into a block over the twins, reconstructing the pair
interface from the two single-output words so every downstream `fst`/`snd`
consumer is unchanged and denotation is preserved.

## The twin block (only lowering ops)

For `bvAdd64 w a b` (carry-in `false`) the block is

```
  z1 := bvConst 1 0                      -- sword 1 zero carry-in
  lo := bvAddCarryLo w a b z1            -- sword w   = a + b           (= sum)
  hi := bvAddCarryHi w a b z1            -- sword 1   = carry-out bit
  zW := bvConst w 0                      -- sword w zero
  cw := bvAddCarryLo w zW zW hi          -- sword w   = ofNat w hi      (widen 0/1)
  p  := mkPair cw lo                     -- pair (sword w) (sword w)
  ret p
```

The widen `sword 1 → sword w` is `bvAddCarryLo w 0 0 hi = 0+0+ofNat w hi.toNat`
— **itself a lowering op**, so no `ite`/`bvEq` is introduced. For `bvAdc w a b cin`
the carry-in `cin : sword w` is first narrowed to a `sword 1` "nonzero" bit by
`cinBit := bvAddCarryHi w cin (allOnes) 0`
(`carryOutBitC cin (2^w-1) 0 = if cin.toNat ≥ 1 then 1 else 0`), matching
`bvAdc`'s own `cin.toNat ≠ 0` reading; again only lowering ops.

## What is proved (all goals closed)

* `adc64Block` / `adcBlock` + their `_denote` reconciliation lemmas — the two
  twin blocks denote exactly to the pair `bvAdd64`/`bvAdc` compute.
* `pairElimLowering : BlockLoweringData catCryptDialect catCryptDialect` — the
  identity-typed block-expanding lowering whose `lowerExprBlock` is the twin
  block on the two pair ops and the identity rebind on every other op.
* `pairElim_denote` — **whole-program** denotation preservation of the pass, from
  the single per-op block square via `blockFundamental` (no per-program
  induction).

## Residual

The pass rebuilds the pair via `mkPair` to keep every `fst`/`snd` consumer
untouched, so the `.pair` type still sits in the context and still hits
`mapTy .pair = .reg 0` at lowering. The twin *words* (`bvAddCarryLo`/
`bvAddCarryHi`) lower; what survives is the `mkPair` wrapper. Reaching bytes for
the carry class from here needs one more, much simpler, `fst/snd`-of-`mkPair`
beta/copy-forward peephole to strip the rebuilt pair (or direct consumer surgery
splicing the two words directly into the `fst`/`snd` consumers — a 1→2 type map
the single-return `BlockLoweringData` cannot express).

Note this is a *different* pipeline from `MpnLoopEmit`: that module's carry
loops are hand-authored `JInstr 64` / `Com (x86Dialect 64)` at the machine level
(open-coded GPR carry, block-unrolled `adc`), never routed through
`catCryptDialect`, so this pass does not re-source them. This
pass makes the pair ops of the `SExpr → catCryptDialect` FRONT carry class
lowerable.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.PairElimPass

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent

/-! ## 1. The two twin blocks -/

/-- The `bvAdd64 w a b` twin block: `lo = a+b`, `hi = carry`, `cw = widen hi`,
    `p = (cw, lo)`. Uses only `bvConst`/`bvAddCarryLo`/`bvAddCarryHi`/`mkPair` —
    every one a lowering op. -/
def adc64Block {Γ : Ctxt catCryptDialect} (w : Nat)
    (a b : Var Γ (.sword w)) :
    Com catCryptDialect Γ (.pair (.sword w) (.sword w)) :=
  -- z1 : sword 1 (carry-in 0)
  .var ⟨.bvConst 1 0, rfl, .nil⟩ <|
  -- lo : sword w = a + b
  .var ⟨.bvAddCarryLo w, rfl,
        .cons (.there a) (.cons (.there b) (.cons .here .nil))⟩ <|
  -- hi : sword 1 = carry-out
  .var ⟨.bvAddCarryHi w, rfl,
        .cons (.there (.there a)) (.cons (.there (.there b))
          (.cons (.there .here) .nil))⟩ <|
  -- zW : sword w (zero)
  .var ⟨.bvConst w 0, rfl, .nil⟩ <|
  -- cw : sword w = ofNat w hi  (widen the 0/1 carry bit)
  .var ⟨.bvAddCarryLo w, rfl,
        .cons .here (.cons .here (.cons (.there .here) .nil))⟩ <|
  -- p : pair = (cw, lo)
  .var ⟨.mkPair (.sword w) (.sword w), rfl,
        .cons .here (.cons (.there (.there (.there .here))) .nil)⟩ <|
  .ret .here

/-- The `bvAdc w a b cin` twin block: narrow `cin : sword w` to a `sword 1`
    nonzero bit, then the same shape as `adc64Block`. -/
def adcBlock {Γ : Ctxt catCryptDialect} (w : Nat)
    (a b cin : Var Γ (.sword w)) :
    Com catCryptDialect Γ (.pair (.sword w) (.sword w)) :=
  -- ones : sword w = allOnes (= 2^w - 1)
  .var ⟨.bvConst w (BitVec.allOnes w), rfl, .nil⟩ <|
  -- z1 : sword 1 (0)
  .var ⟨.bvConst 1 0, rfl, .nil⟩ <|
  -- cinBit : sword 1 = (cin ≠ 0) ? 1 : 0  via  carryOutBitC cin ones 0
  .var ⟨.bvAddCarryHi w, rfl,
        .cons (.there (.there cin)) (.cons (.there .here) (.cons .here .nil))⟩ <|
  -- lo : sword w = a + b + cinBit
  .var ⟨.bvAddCarryLo w, rfl,
        .cons (.there (.there (.there a)))
          (.cons (.there (.there (.there b))) (.cons .here .nil))⟩ <|
  -- hi : sword 1 = carry-out of a + b + cinBit
  .var ⟨.bvAddCarryHi w, rfl,
        .cons (.there (.there (.there (.there a))))
          (.cons (.there (.there (.there (.there b))))
            (.cons (.there .here) .nil))⟩ <|
  -- zW : sword w (0)
  .var ⟨.bvConst w 0, rfl, .nil⟩ <|
  -- cw : sword w = ofNat w hi
  .var ⟨.bvAddCarryLo w, rfl,
        .cons .here (.cons .here (.cons (.there .here) .nil))⟩ <|
  -- p : pair = (cw, lo)
  .var ⟨.mkPair (.sword w) (.sword w), rfl,
        .cons .here (.cons (.there (.there (.there .here))) .nil)⟩ <|
  .ret .here

/-! ## 2. Per-op denote reducers (`rfl`, cheap — avoid unfolding the whole instance) -/

@[local simp] theorem denote_bvConst {w : Nat} (v : BitVec w)
    (args : HVector (fun t => ⟦t⟧) (DialectSignature.sig (d := catCryptDialect) (.bvConst w v))) :
    DialectDenote.denote (d := catCryptDialect) (.bvConst w v) args = v := rfl

@[local simp] theorem denote_bvAddCarryLo {w : Nat}
    (args : HVector (fun t => ⟦t⟧)
      (DialectSignature.sig (d := catCryptDialect) (.bvAddCarryLo w))) :
    DialectDenote.denote (d := catCryptDialect) (.bvAddCarryLo w) args
      = CatCryptDialect.addCarryWordC args.head args.tail.head args.tail.tail.head := rfl

@[local simp] theorem denote_bvAddCarryHi {w : Nat}
    (args : HVector (fun t => ⟦t⟧)
      (DialectSignature.sig (d := catCryptDialect) (.bvAddCarryHi w))) :
    DialectDenote.denote (d := catCryptDialect) (.bvAddCarryHi w) args
      = CatCryptDialect.carryOutBitC args.head args.tail.head args.tail.tail.head := rfl

@[local simp] theorem denote_mkPair {α β : CryptoSSA.CryptoTy}
    (args : HVector (fun t => ⟦t⟧)
      (DialectSignature.sig (d := catCryptDialect) (.mkPair α β))) :
    DialectDenote.denote (d := catCryptDialect) (.mkPair α β) args
      = (args.head, args.tail.head) := rfl

/-! ### Constructor-form framework reducers (fire in `simp`, unlike the def equations) -/

@[local simp] theorem lookup_here {Γ : Ctxt catCryptDialect} {t : CryptoSSA.CryptoTy}
    (x : ⟦t⟧) (V : Ctxt.Valuation Γ) :
    (Ctxt.Var.here : Var (t :: Γ) t).lookup (HVector.cons x V) = x := rfl

@[local simp] theorem lookup_there {Γ : Ctxt catCryptDialect} {t s : CryptoSSA.CryptoTy}
    (v : Var Γ t) (x : ⟦s⟧) (V : Ctxt.Valuation Γ) :
    (Ctxt.Var.there v : Var (s :: Γ) t).lookup (HVector.cons x V) = v.lookup V := rfl

@[local simp] theorem lookupArgs_nil {Γ : Ctxt catCryptDialect} (V : Ctxt.Valuation Γ) :
    Expr.lookupArgs (d := catCryptDialect) (Γ := Γ) (tys := []) HVector.nil V = HVector.nil :=
  rfl

@[local simp] theorem lookupArgs_cons {Γ : Ctxt catCryptDialect}
    {ty : CryptoSSA.CryptoTy} {tys : List CryptoSSA.CryptoTy}
    (v : Var Γ ty) (rest : HVector (fun ty => Var Γ ty) tys) (V : Ctxt.Valuation Γ) :
    Expr.lookupArgs (.cons v rest) V
      = HVector.cons (v.lookup V) (Expr.lookupArgs rest V) := rfl

@[local simp] theorem hv_head {t : CryptoSSA.CryptoTy} {tys : List CryptoSSA.CryptoTy}
    (x : ⟦t⟧) (xs : HVector (fun t => ⟦t⟧) tys) : (HVector.cons x xs).head = x := rfl

@[local simp] theorem hv_tail {t : CryptoSSA.CryptoTy} {tys : List CryptoSSA.CryptoTy}
    (x : ⟦t⟧) (xs : HVector (fun t => ⟦t⟧) tys) : (HVector.cons x xs).tail = xs := rfl

/-- Widening the 1-bit `1` to width `w` is the width-`w` `1` (the carry-word widen). -/
theorem setWidth_one_word (w : Nat) : BitVec.setWidth w (1#1) = 1#w := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-! ## 3. Reconciliation: the twin blocks compute the pair ops -/

theorem adc64Block_denote {Γ : Ctxt catCryptDialect} {w : Nat}
    (a b : Var Γ (.sword w)) (V : Ctxt.Valuation Γ) :
    (adc64Block w a b).denote V
      = (let av : BitVec w := a.lookup V; let bv : BitVec w := b.lookup V;
         ((if av.toNat + bv.toNat ≥ 2 ^ w then (1 : BitVec w) else 0), av + bv)) := by
  have hred : (adc64Block w a b).denote V
      = (CatCryptDialect.addCarryWordC (0 : BitVec w) (0 : BitVec w)
           (CatCryptDialect.carryOutBitC (a.lookup V : BitVec w) (b.lookup V : BitVec w)
             (0 : BitVec 1)),
         CatCryptDialect.addCarryWordC (a.lookup V : BitVec w) (b.lookup V : BitVec w)
           (0 : BitVec 1)) := rfl
  rw [hred]
  simp [CatCryptDialect.addCarryWordC, CatCryptDialect.carryOutBitC,
    apply_ite (BitVec.setWidth w), setWidth_one_word]

theorem adcBlock_denote {Γ : Ctxt catCryptDialect} {w : Nat}
    (a b cin : Var Γ (.sword w)) (V : Ctxt.Valuation Γ) :
    (adcBlock w a b cin).denote V
      = (let av : BitVec w := a.lookup V; let bv : BitVec w := b.lookup V;
         let c : Nat := if (cin.lookup V : BitVec w).toNat = 0 then 0 else 1;
         ((if av.toNat + bv.toNat + c ≥ 2 ^ w then (1 : BitVec w) else 0),
          av + bv + BitVec.ofNat w c)) := by
  have hred : (adcBlock w a b cin).denote V
      = (CatCryptDialect.addCarryWordC (0 : BitVec w) (0 : BitVec w)
           (CatCryptDialect.carryOutBitC (a.lookup V : BitVec w) (b.lookup V : BitVec w)
             (CatCryptDialect.carryOutBitC (cin.lookup V : BitVec w) (BitVec.allOnes w)
               (0 : BitVec 1))),
         CatCryptDialect.addCarryWordC (a.lookup V : BitVec w) (b.lookup V : BitVec w)
           (CatCryptDialect.carryOutBitC (cin.lookup V : BitVec w) (BitVec.allOnes w)
             (0 : BitVec 1))) := rfl
  rw [hred]
  have hlt : (cin.lookup V : BitVec w).toNat < 2 ^ w := (cin.lookup V).isLt
  have hpos : 0 < 2 ^ w := Nat.two_pow_pos w
  have h0 : (0 : BitVec 1).toNat = 0 := rfl
  have hcin : CatCryptDialect.carryOutBitC (cin.lookup V : BitVec w) (BitVec.allOnes w)
        (0 : BitVec 1) = if (cin.lookup V : BitVec w).toNat = 0 then 0#1 else 1#1 := by
    unfold CatCryptDialect.carryOutBitC
    rw [BitVec.toNat_allOnes, h0]
    split <;> split <;> first | rfl | omega
  rw [hcin]
  simp [CatCryptDialect.addCarryWordC, CatCryptDialect.carryOutBitC,
    apply_ite (BitVec.setWidth w), setWidth_one_word]
  split <;> simp_all [BitVec.toNat_ofNat]

/-! ## 4. Source-op denote bridges (`bvAdd64`/`bvAdc` compute the same explicit forms) -/

theorem bvAdd64_expr_denote {Γ : Ctxt catCryptDialect} {w : Nat}
    (a b : Var Γ (.sword w)) (V : Ctxt.Valuation Γ) :
    (Expr.denote (⟨.bvAdd64 w, rfl, .cons a (.cons b .nil)⟩ :
        Expr catCryptDialect Γ (.pair (.sword w) (.sword w))) V)
      = (let av : BitVec w := a.lookup V; let bv : BitVec w := b.lookup V;
         ((if av.toNat + bv.toNat ≥ 2 ^ w then (1 : BitVec w) else 0), av + bv)) := by
  have hred : (Expr.denote (⟨.bvAdd64 w, rfl, .cons a (.cons b .nil)⟩ :
        Expr catCryptDialect Γ (.pair (.sword w) (.sword w))) V)
      = (let p := BitVec.adc (a.lookup V : BitVec w) (b.lookup V : BitVec w) false;
         ((if p.fst then (1 : BitVec w) else 0), p.snd)) := rfl
  rw [hred, BitVec.adc_spec]
  simp [BitVec.carry_width]

theorem bvAdc_expr_denote {Γ : Ctxt catCryptDialect} {w : Nat}
    (a b cin : Var Γ (.sword w)) (V : Ctxt.Valuation Γ) :
    (Expr.denote (⟨.bvAdc w, rfl, .cons a (.cons b (.cons cin .nil))⟩ :
        Expr catCryptDialect Γ (.pair (.sword w) (.sword w))) V)
      = (let av : BitVec w := a.lookup V; let bv : BitVec w := b.lookup V;
         let c : Nat := if (cin.lookup V : BitVec w).toNat = 0 then 0 else 1;
         ((if av.toNat + bv.toNat + c ≥ 2 ^ w then (1 : BitVec w) else 0),
          av + bv + BitVec.ofNat w c)) := by
  have hred : (Expr.denote (⟨.bvAdc w, rfl, .cons a (.cons b (.cons cin .nil))⟩ :
        Expr catCryptDialect Γ (.pair (.sword w) (.sword w))) V)
      = (let p := BitVec.adc (a.lookup V : BitVec w) (b.lookup V : BitVec w)
            ((cin.lookup V : BitVec w).toNat ≠ 0);
         ((if p.fst then (1 : BitVec w) else 0), p.snd)) := rfl
  rw [hred, BitVec.adc_spec]
  simp only [BitVec.carry_width]
  by_cases h : (cin.lookup V : BitVec w).toNat = 0 <;>
    simp [h, BitVec.ofBool, setWidth_one_word]

/-! ## 5. The pair-elimination lowering + whole-program preservation -/

/-- The per-op block lowering: `bvAdd64`/`bvAdc` expand to their twin blocks; every
    other op is rebound identically (`.var e (.ret .here)`, a no-op block). -/
def lowerExprBlock {Γ : Ctxt catCryptDialect} {t : CryptoSSA.CryptoTy}
    (e : Expr catCryptDialect Γ t) : Com catCryptDialect Γ t :=
  match e with
  | ⟨.bvAdd64 w, hop, .cons a (.cons b .nil)⟩ => hop ▸ adc64Block w a b
  | ⟨.bvAdc w, hop, .cons a (.cons b (.cons cin .nil))⟩ => hop ▸ adcBlock w a b cin
  | e => .var e (.ret .here)

/-- The pair-elimination pass as an identity-typed block-expanding lowering. -/
def pairElimLowering : BlockLoweringData catCryptDialect catCryptDialect where
  mapTy := id
  mapCtx := id
  mapCtx_cons := fun _ _ => rfl
  mapVar := fun v => v
  lowerExprBlock := fun e => lowerExprBlock e

/-- Identity value transport. -/
def idTransTy : TransTy pairElimLowering := fun x => x
/-- Identity valuation transport. -/
def idMapVal : MapVal pairElimLowering := fun V => V

/-- Variable leaf: identity. -/
theorem pairElim_varTransports : VarTransports pairElimLowering idTransTy idMapVal :=
  fun _ _ => rfl

/-- Binding-threading leaf: identity. -/
theorem pairElim_mapValExtends : MapValExtends pairElimLowering idTransTy idMapVal :=
  fun _ _ => rfl

/-- **The per-op block square.** Each op's block denotes to the op's own denotation:
    the two carry-pair ops via `adc64Block_denote`/`adcBlock_denote` reconciled with
    the source-op denotes; every other op via the no-op rebind (`rfl`). -/
theorem pairElim_blockOp : BlockOpTransports pairElimLowering idTransTy idMapVal := by
  intro Γ t e V
  obtain ⟨op, hop, args⟩ := e
  show (lowerExprBlock ⟨op, hop, args⟩).denote V
      = (⟨op, hop, args⟩ : Expr catCryptDialect Γ t).denote V
  cases op
  case bvAdd64 w =>
    match args with
    | .cons a (.cons b .nil) =>
      cases hop
      show (adc64Block w a b).denote V = _
      rw [adc64Block_denote, bvAdd64_expr_denote]
  case bvAdc w =>
    match args with
    | .cons a (.cons b (.cons cin .nil)) =>
      cases hop
      show (adcBlock w a b cin).denote V = _
      rw [adcBlock_denote, bvAdc_expr_denote]
  all_goals rfl

/-- **Whole-program pair-elimination preservation.** For *every* `Com catCryptDialect`,
    running the pair-eliminated program equals running the original — obtained from the
    three leaves by `blockFundamental`, with no per-program induction. Each `bvAdd64`/
    `bvAdc` pair node is replaced by its `bvAddCarryLo`/`bvAddCarryHi` twin block (all
    lowering ops), so the carry class flows through the proven single-output
    twins to the jasmin `addCarryLo`/`addCarryHi` backend. -/
theorem pairElim_denote {Γ : Ctxt catCryptDialect} {t : CryptoSSA.CryptoTy}
    (c : Com catCryptDialect Γ t) (V : Ctxt.Valuation Γ) :
    (pairElimLowering.blockLowerCom c).denote (idMapVal V) = idTransTy (c.denote V) :=
  blockFundamental pairElimLowering idTransTy idMapVal
    pairElim_varTransports pairElim_blockOp pairElim_mapValExtends c V

/-! ## 6. Validation — the pass on a concrete carry program -/

/-- A one-op program with a `bvAdd64` pair node over two 8-bit inputs. -/
def sampleCarryProg :
    Com catCryptDialect [.sword 8, .sword 8] (.pair (.sword 8) (.sword 8)) :=
  .var ⟨.bvAdd64 8, rfl, .cons .here (.cons (.there .here) .nil)⟩ (.ret .here)

/-- The pass rewrites the sample's `bvAdd64` pair node into the `bvAddCarryLo`/
    `bvAddCarryHi` twin block and preserves denotation — the concrete witness that the
    generic `pairElim_denote` fires (pair node in, twin block out, same value). -/
theorem sampleCarryProg_pairElim
    (V : Ctxt.Valuation ([.sword 8, .sword 8] : Ctxt catCryptDialect)) :
    (pairElimLowering.blockLowerCom sampleCarryProg).denote (idMapVal V)
      = idTransTy (sampleCarryProg.denote V) :=
  pairElim_denote sampleCarryProg V

/-! ## 7. The `mkPair`-strip peephole (removing the reconstructed pair residue)

`pairElimLowering` rebuilds the pair via `mkPair cw lo` so every downstream
`fst`/`snd` consumer stays untouched; the residue is the `.pair`-typed binding
(and the two projections reading it), and `CryptoToJasminCom.mapTy (.pair _ _) =
.reg 0` — the lowering refuses any expression touching a `.pair`. This section
supplies the peephole that clears that residue: forward each `fst`/`snd` of a
freshly-built `mkPair` to the component word it selects, and drop the resulting dead
`mkPair` binding, leaving a `.pair`-free `Com` over the twin words alone
(`bvAddCarryLo`/`bvAddCarryHi`), which lower 1:1 through `DialectToJasminCom`.

The three rewrites (`fst_of_mkPair_strip`, `snd_of_mkPair_strip`,
`dropDeadBinding`) are each denotation-neutral, and §7.2 witnesses the full strip
on the canonical `mkPair`-then-project-both consumer shape: a program carrying the
pair residue denotes exactly to a hand-written `.pair`-free program. -/

/-- The `mkPair a b` expression. -/
def mkPairE {Γ : Ctxt catCryptDialect} {α β : CryptoSSA.CryptoTy}
    (a : Var Γ α) (b : Var Γ β) : Expr catCryptDialect Γ (.pair α β) :=
  ⟨.mkPair α β, rfl, .cons a (.cons b .nil)⟩

/-- The `fst p` expression. -/
def fstE {Γ : Ctxt catCryptDialect} {α β : CryptoSSA.CryptoTy}
    (p : Var Γ (.pair α β)) : Expr catCryptDialect Γ α :=
  ⟨.fst α β, rfl, .cons p .nil⟩

/-- The `snd p` expression. -/
def sndE {Γ : Ctxt catCryptDialect} {α β : CryptoSSA.CryptoTy}
    (p : Var Γ (.pair α β)) : Expr catCryptDialect Γ β :=
  ⟨.snd α β, rfl, .cons p .nil⟩

/-- **fst-of-mkPair strip (denotation-neutral).** A `fst` reading the just-built
    pair `mkPair a b` is forwarded to the first component word `a`: the projection
    binding is replaced by a copy-forward of `a` (via `substHeadHom (.there a)`),
    keeping the `mkPair` binding (dead afterwards) in place. Denotation is preserved —
    both sides bind `a.lookup V` at the projection slot. -/
theorem fst_of_mkPair_strip {Γ : Ctxt catCryptDialect} {α β s : CryptoSSA.CryptoTy}
    (a : Var Γ α) (b : Var Γ β)
    (k : Com catCryptDialect (α :: .pair α β :: Γ) s) (V : Ctxt.Valuation Γ) :
    (Com.var (mkPairE a b) (Com.var (fstE Ctxt.Var.here) k)).denote V
      = (Com.var (mkPairE a b)
          (Com.rename (substHeadHom (Ctxt.Var.there a)) k)).denote V := by
  simp only [Com.denote]
  rw [Com.denote_rename, pullV_substHeadHom]
  rfl

/-- **snd-of-mkPair strip (denotation-neutral).** Symmetric to `fst_of_mkPair_strip`:
    a `snd` of the just-built pair is forwarded to the second component `b`. -/
theorem snd_of_mkPair_strip {Γ : Ctxt catCryptDialect} {α β s : CryptoSSA.CryptoTy}
    (a : Var Γ α) (b : Var Γ β)
    (k : Com catCryptDialect (β :: .pair α β :: Γ) s) (V : Ctxt.Valuation Γ) :
    (Com.var (mkPairE a b) (Com.var (sndE Ctxt.Var.here) k)).denote V
      = (Com.var (mkPairE a b)
          (Com.rename (substHeadHom (Ctxt.Var.there b)) k)).denote V := by
  simp only [Com.denote]
  rw [Com.denote_rename, pullV_substHeadHom]
  rfl

/-- **Dead-head-binding elimination (denotation-neutral).** A head binding whose
    continuation is a `weakenOne`-renamed body (i.e. the binding is unused) is
    dropped: `let _ = e; body₀[weaken]` denotes exactly `body₀`. This removes the
    `mkPair` residue once both projections have been forwarded off it. -/
theorem dropDeadBinding {Γ : Ctxt catCryptDialect} {t s : CryptoSSA.CryptoTy}
    (e : Expr catCryptDialect Γ t) (body0 : Com catCryptDialect Γ s)
    (V : Ctxt.Valuation Γ) :
    (Com.var e (Com.rename (Ctxt.Hom.weakenOne Γ t) body0)).denote V
      = body0.denote V := by
  simp only [Com.denote]
  rw [Com.denote_rename]
  have h : pullV (Ctxt.Hom.weakenOne Γ t)
        (Ctxt.Valuation.extend V (e.denote V)) = V := by
    show pullV (fun v => Ctxt.Var.there v)
        (HVector.cons (e.denote V) V) = V
    rw [pullV_there (fun v => v) (e.denote V) V, pullV_id]
  rw [h]

/-! ### 7.2. Full strip on the canonical carry consumer -/

/-- The canonical pair-residue shape a `fst`/`snd`-consuming carry client leaves
    after `pairElim`: build the pair `mkPair a b`, project **both** components
    (`x = fst p = a`, `y = snd p = b`), then combine them (`bvXor` stands in for
    an arbitrary two-word consumer). `a = .here`, `b = .there .here`. -/
def carryConsumerProg (w : Nat) :
    Com catCryptDialect [.sword w, .sword w] (.sword w) :=
  .var (mkPairE Ctxt.Var.here (Ctxt.Var.there Ctxt.Var.here)) <|
  .var (fstE Ctxt.Var.here) <|
  .var (sndE (Ctxt.Var.there Ctxt.Var.here)) <|
  .var ⟨.bvXor w, rfl, .cons (Ctxt.Var.there Ctxt.Var.here) (.cons Ctxt.Var.here .nil)⟩ <|
  .ret Ctxt.Var.here

/-- The fully stripped, `.pair`-free result: the two-word consumer reads the
    component words `a`/`b` directly — no `mkPair`, no `fst`, no `snd`. Every op
    here (`bvXor`) lowers 1:1 through `DialectToJasminCom` (`.reg w`), so this is a
    deployable carry-block `Com`. -/
def carryConsumerStripped (w : Nat) :
    Com catCryptDialect [.sword w, .sword w] (.sword w) :=
  .var ⟨.bvXor w, rfl, .cons Ctxt.Var.here (.cons (Ctxt.Var.there Ctxt.Var.here) .nil)⟩ <|
  .ret Ctxt.Var.here

/-- **The strip is semantics-neutral, end to end.** The pair-residue consumer
    (`mkPair`, `fst`, `snd`, combine) denotes to exactly the hand-written
    `.pair`-free consumer over the two component words — the concrete witness that
    forwarding the projections off the `mkPair` and dropping the dead pair binding
    reaches a deployable, `.pair`-free carry-block `Com`. -/
theorem carryConsumer_strip_denote (w : Nat)
    (V : Ctxt.Valuation ([.sword w, .sword w] : Ctxt catCryptDialect)) :
    (carryConsumerProg w).denote V = (carryConsumerStripped w).denote V := rfl

end CatCrypt.Crypto.SecureCompilation.VIR.PairElimPass
