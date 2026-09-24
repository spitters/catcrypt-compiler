/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
public meta import CatCrypt.Crypto.SecureCompilation.FieldReduceIdioms
public import CatCrypt.Crypto.SecureCompilation.FieldReduceIdioms


@[expose] public section
set_option autoImplicit false

/-!
# Carry-chain instruction selection at the `LowCT → catCryptDialect` front

The LowCT front has no carry-flag surface, so multi-limb field kernels
(`MultiLimbKernel.add2Prog` and its descendants, e.g. `Bn254TowerFrontEmit`)
synthesise every per-limb carry/borrow **branch-free** with the proven `bSltu`
shape

```
x <u y  =  ((~(x ^ y) & (x − y)) | (~x & y)) >> 63     (| as (a^b)^(a&b))
```

emitted as the three-command `ltuCmds` window.  Per limb of a ripple chain this
costs ~25 dialect ops (≈8 ALU instructions per hardware `adc`) — the measured
BN254 `Fp2` add gap (front-emitted 1023 cyc vs 22 cyc for the hand-ADX twin).

The dialect **already** carries the efficient ops — `bvAddCarryLo`/`bvAddCarryHi`
(`[sword 64, sword 64, sword 1] → sword 64 / sword 1`), lowered 1:1 by
`cryptoDialectToJasminCom` to jasmin `addCarryLo`/`addCarryHi` and rendered by
the owned backend as `ADCX`/`ADCXHI` (`bt $0,cin; adcx` / `setc; movzbq`) —
exactly the target `CarryEqLitIdiom` names.  The remaining piece is the
**selection**: rewriting the front's `bSltu` windows into carry-op chains.

This module is that selection pass, at the dialect-lowering level (option (A)
of the design space; see the design note below):

```
LowCT (RSeq spine) ──flattenSeq──▶ List LowCT
  ──selectGo──▶ List Sel                 (window matching, named vars — no de Bruijn)
  ──emitAll──▶ DTransOut                 (bvAddCarryLo/bvAddCarryHi bindings;
                                          unmatched commands fall through to
                                          translateDialectControl unchanged)
```

## The recognised windows (the exact `add2Prog` shapes)

With `ltu c x y` abbreviating the three-command `ltuCmds` window:

| window     | LowCT shape                                                      | fused emission |
|------------|------------------------------------------------------------------|----------------|
| `addStart` | `s := x + y; ltu c s x`                                          | `s := lo x y 0₁; c♭ := hi x y 0₁` |
| `addMid`   | `t := x + y; ltu ca t x; s := t + cₚ; ltu cb s t; c := ca + cb`  | `s := lo x y cₚ♭; c♭ := hi x y cₚ♭` |
| `addFin`   | `t := x + y; s := t + cₚ`                                        | `s := lo x y cₚ♭` |
| `subStart` | `e := x − y; ltu w x y`                                          | `e := lo x ¬y 1₁; w♭ := hi x ¬y 1₁` |
| `subMid`   | `g := x − y; ltu wa x y; e := g − wₚ; ltu wb g wₚ; w := wa + wb` | `e := lo x ¬y wₚ♭; w♭ := hi x ¬y wₚ♭` |

where `lo`/`hi` are `bvAddCarryLo`/`bvAddCarryHi`, `c♭` is the `sword 1` carry
bit bound under `c ++ "#b"`, and borrow chains run in the **complement-add**
convention (x86 `SBB` = `ADC` of the complement): `x − y − borrow = x + ~y +
(1 − borrow)`, so a borrow name's `#b` bit holds the **not-borrow** and threads
directly as the next limb's carry-in.  When a carry/borrow name is also read as
a *word* downstream (e.g. the final borrow driving the masked select `m := 0 −
w₃`), the pass materialises the word: `zext` via `lo 0 0 c♭` for carries, and
`(lo 0 0 w♭) ^^^ 1` for borrows.

## Per-rewrite denotation preservation (the BitVec lemmas)

Each fused emission's ops denote `addCarryWordC` / `carryOutBitC`
(`catCryptDenote`, definitional), and each replaced window's plain lowering
denotes the corresponding `ltuIdiom` composition.  The §2 key theorems
prove, for **all** inputs (`bv_decide`), that the two agree:

* `select_addStart_data` / `select_addStart_carry` — the 2-op start step;
* `select_addMid_data` / `select_addMid_carry` — the 3-input mid step
  (`carryOut = ltu(t,x) + ltu(t+cin,t)`, the two-test carry recombination);
* `select_subStart_data` / `select_subStart_borrow` — borrow start via
  complement-add (`x + ~y + 1 = x − y`, `¬carryOut = x <u y`);
* `select_subMid_data` / `select_subMid_borrow` — borrow mid step;
* `select_zext` / `select_borrow_word` — the word materialisations.

These are the per-rewrite value-preservation obligations (the
`ModReduceSelect` discipline).  The end-to-end program-level check stays the
kernel gates: the selected front still `native_decide`s `denote = the
independent Nat spec` on the anchor vectors (`Bn254TowerFrontEmit` §6), and the
deployed `.s` keeps its external byte KAT.

## Design note: why the dialect-lowering level (option A), not the alternatives

* **`Com → Com`** (the other option-(A) venue): recognising a ~25-binding
  window in intrinsically-typed de-Bruijn SSA and replacing it with 2 bindings
  needs context-shrinking + reference remapping; the existing `Peephole` /
  `ArithIselPass` frameworks are deliberately *binding-preserving* (documented
  v1 limitation), so this would mean building a substitution-based rewrite
  framework first.  At the LowCT spine the same windows are adjacent commands
  over **named** slots — matching and re-emission reuse the front's own
  `VarMap`/`pushVarBind` machinery, which threads weakening automatically.
* **Front alphabet extension** (option B, `SExpr` carry constructors): widens
  the audited front surface (`SExpr` is matched across the leak-factoring /
  coincidence / RustSim companions) and requires editing every kernel body;
  the selection instead benefits every `add2Prog`-shaped kernel with zero
  source changes and leaves `SExpr` untouched.

## Safety of the rewrite

The matcher is conservative: a window is selected only when its scratch slots
(the `ltuCmds` `q`/`r` pair, the mid-step `t`/`ca`/`cb`/`g`/`wa`/`wb`) are not
mentioned anywhere in the remaining command list (`tailMentions`, computed with
an over-approximating `mentionsCmd` that treats unknown constructors as
mentioning everything), all names bound inside the window are pairwise distinct
and disjoint from the operand atoms (no shadowing divergence), and a mid/fin
step's carry-in name was produced by an earlier selected window of the same
kind (so its `#b` bit is bound, with the right carry vs not-borrow reading).
Anything else falls through to `translateDialectControl` unchanged.  A failed
lookup during emission declines the whole translation (`none`) — the same
visible failure mode as the front's other declines, never silent corruption.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelect

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)

/-! ## 1. The recognised idiom, as a BitVec function -/

/-- The all-ones 64-bit literal the kernels' `notE` uses (`2^64 − 1`). -/
def onesLit : Nat := 18446744073709551615

/-- The value of the front-lowered `ltuCmds` window: `q = ~x & y`,
    `r = ~(x^y) & (x−y)`, result `((q^r)^(q&r)) >>> 63` (OR expanded as
    `(a^b)^(a&b)` — the exact `SExpr` shape the kernels emit). -/
def ltuIdiom (x y : BitVec 64) : BitVec 64 :=
  let q := (x ^^^ BitVec.ofNat 64 onesLit) &&& y
  let r := ((x ^^^ y) ^^^ BitVec.ofNat 64 onesLit) &&& (x - y)
  ((q ^^^ r) ^^^ (q &&& r)) >>> 63

/-- The window value is the proven `bSltu` comparison (same idiom, OR
    expanded). -/
theorem ltuIdiom_eq_bSltu (x y : BitVec 64) :
    ltuIdiom x y = CatCrypt.Crypto.SecureCompilation.FieldReduceIdioms.bSltu x y := by
  unfold ltuIdiom CatCrypt.Crypto.SecureCompilation.FieldReduceIdioms.bSltu onesLit
  bv_decide

/-- The window value realises `x <ᵤ y` as a `0/1` word. -/
theorem ltuIdiom_eq (x y : BitVec 64) :
    ltuIdiom x y = (if x.ult y then (1 : BitVec 64) else 0) := by
  unfold ltuIdiom onesLit
  bv_decide

/-! ## 2. The BitVec lemmas (per-rewrite denotation preservation)

`carryOutBitC` is defined via a `Nat` comparison on `toNat`; `carryOutW` is
its pure-BitVec twin (the top bit of the 65-bit sum), bridged once by
`carryOutBitC_eq_carryOutW` so every such lemma discharges by `bv_decide`. -/

/-- Pure-BitVec twin of `carryOutBitC`: bit 64 of the 65-bit sum
    `zext a + zext b + zext cin`. -/
def carryOutW (a b : BitVec 64) (cin : BitVec 1) : BitVec 1 :=
  BitVec.extractLsb' 64 1
    (BitVec.setWidth 65 a + BitVec.setWidth 65 b + BitVec.setWidth 65 cin)

/-- Bridge: the dialect's `carryOutBitC` (a `toNat` comparison) equals the
    pure-BitVec `carryOutW`. -/
theorem carryOutBitC_eq_carryOutW (a b : BitVec 64) (cin : BitVec 1) :
    carryOutBitC a b cin = carryOutW a b cin := by
  unfold carryOutBitC carryOutW
  have ha := a.isLt; have hb := b.isLt; have hc := cin.isLt
  have hsum : (BitVec.setWidth 65 a + BitVec.setWidth 65 b + BitVec.setWidth 65 cin).toNat
      = a.toNat + b.toNat + cin.toNat := by
    simp only [BitVec.toNat_add, BitVec.toNat_setWidth]
    omega
  apply BitVec.eq_of_toNat_eq
  have hex : (BitVec.extractLsb' 64 1
        (BitVec.setWidth 65 a + BitVec.setWidth 65 b + BitVec.setWidth 65 cin)).toNat
      = (a.toNat + b.toNat + cin.toNat) / 2 ^ 64 % 2 ^ 1 := by
    simp only [BitVec.extractLsb', BitVec.toNat_ofNat, hsum, Nat.shiftRight_eq_div_pow]
  rw [hex]
  split <;>
    simp only [show (1 : BitVec 1).toNat = 1 from rfl,
      show (0 : BitVec 1).toNat = 0 from rfl] <;>
    omega

/-- The dialect's carry-add data word, in `bv_decide`-friendly form:
    `a + b + zext cin`. -/
theorem addCarryWordC_eq_setWidth (a b : BitVec 64) (cin : BitVec 1) :
    addCarryWordC a b cin = a + b + BitVec.setWidth 64 cin := by
  unfold addCarryWordC
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth]

/-- **K1 data (addStart).** The selected `lo x y 0` computes the plain sum. -/
theorem select_addStart_data (x y : BitVec 64) :
    addCarryWordC x y 0#1 = x + y := by
  rw [addCarryWordC_eq_setWidth]; bv_decide

/-- **K1 carry (addStart).** The selected carry-out bit (widened) is exactly
    the `bSltu` window value `ltu (x+y) x` the plain lowering computes. -/
theorem select_addStart_carry (x y : BitVec 64) :
    BitVec.setWidth 64 (carryOutBitC x y 0#1) = ltuIdiom (x + y) x := by
  rw [carryOutBitC_eq_carryOutW]
  unfold carryOutW ltuIdiom onesLit
  bv_decide

/-- **K2 data (addMid).** The selected `lo x y cin` computes the two-step
    plain sum `(x + y) + zext cin`. -/
theorem select_addMid_data (x y : BitVec 64) (cin : BitVec 1) :
    addCarryWordC x y cin = (x + y) + BitVec.setWidth 64 cin := by
  rw [addCarryWordC_eq_setWidth]

/-- **K2 carry (addMid).** The selected carry-out bit (widened) is exactly the
    plain lowering's carry recombination `ltu(t,x) + ltu(t + zext cin, t)`
    (`t = x + y`) — the `ca + cb` sum of the two `bSltu` windows. -/
theorem select_addMid_carry (x y : BitVec 64) (cin : BitVec 1) :
    BitVec.setWidth 64 (carryOutBitC x y cin)
      = ltuIdiom (x + y) x + ltuIdiom ((x + y) + BitVec.setWidth 64 cin) (x + y) := by
  rw [carryOutBitC_eq_carryOutW]
  unfold carryOutW ltuIdiom onesLit
  bv_decide

/-- **K3 data (subStart).** Complement-add realises the subtract:
    `lo x (y ^ ones) 1 = x − y`. -/
theorem select_subStart_data (x y : BitVec 64) :
    addCarryWordC x (y ^^^ BitVec.ofNat 64 onesLit) 1#1 = x - y := by
  rw [addCarryWordC_eq_setWidth]; unfold onesLit; bv_decide

/-- **K3 borrow (subStart).** The complement-add carry-out is the
    **not-borrow**: widened and flipped it is exactly the plain `bSltu`
    borrow `ltu x y`. -/
theorem select_subStart_borrow (x y : BitVec 64) :
    BitVec.setWidth 64 (carryOutBitC x (y ^^^ BitVec.ofNat 64 onesLit) 1#1) ^^^ 1#64
      = ltuIdiom x y := by
  rw [carryOutBitC_eq_carryOutW]
  unfold carryOutW ltuIdiom onesLit
  bv_decide

/-- **K4 data (subMid).** With `nb` the not-borrow-in bit (borrow word
    `zext nb ^^^ 1`), the complement-add computes the two-step plain
    difference `(x − y) − (zext nb ^^^ 1)`. -/
theorem select_subMid_data (x y : BitVec 64) (nb : BitVec 1) :
    addCarryWordC x (y ^^^ BitVec.ofNat 64 onesLit) nb
      = (x - y) - (BitVec.setWidth 64 nb ^^^ 1#64) := by
  rw [addCarryWordC_eq_setWidth]; unfold onesLit; bv_decide

/-- **K4 borrow (subMid).** The complement-add carry-out, widened and flipped,
    is the plain lowering's borrow recombination
    `ltu x y + ltu (x−y) (zext nb ^^^ 1)` — the `wa + wb` sum. -/
theorem select_subMid_borrow (x y : BitVec 64) (nb : BitVec 1) :
    BitVec.setWidth 64 (carryOutBitC x (y ^^^ BitVec.ofNat 64 onesLit) nb) ^^^ 1#64
      = ltuIdiom x y + ltuIdiom (x - y) (BitVec.setWidth 64 nb ^^^ 1#64) := by
  rw [carryOutBitC_eq_carryOutW]
  unfold carryOutW ltuIdiom onesLit
  bv_decide

/-- **K5 (word materialisation).** `lo 0 0 c` zero-extends the carry bit —
    the word binding for downstream word reads of a selected carry. -/
theorem select_zext (c : BitVec 1) :
    addCarryWordC 0#64 0#64 c = BitVec.setWidth 64 c := by
  rw [addCarryWordC_eq_setWidth]; bv_decide

/-- **K5′ (borrow word).** For a borrow name the materialised word is
    `zext nb ^^^ 1` — the borrow value (`0/1` flip of the not-borrow bit). -/
theorem select_borrow_word (nb : BitVec 1) :
    addCarryWordC 0#64 0#64 nb ^^^ 1#64 = BitVec.setWidth 64 nb ^^^ 1#64 := by
  rw [select_zext]

/-! ## 3. Window matching over the flattened LowCT spine -/

/-- An operand atom of a matched window: a named `u64` slot or a literal. -/
inductive Atom where
  | avar (s : String)
  | alit (n : Nat)
  deriving DecidableEq, Repr

/-- View an `SExpr` as an atom. -/
def matchAtom : SExpr → Option Atom
  | .SVar s => some (.avar s)
  | .SLit n => some (.alit n)
  | _ => none

/-- The slot names an atom reads. -/
def Atom.vars : Atom → List String
  | .avar s => [s]
  | .alit _ => []

/-- All slot names an `SExpr` reads. -/
def sexprVars : SExpr → List String
  | .SVar s => [s]
  | .SLit _ => []
  | .SAdd a b | .SSub a b | .SMul a b | .SShr a b | .SShl a b
  | .SAnd a b | .SXor a b | .SLt a b | .SAsr a b | .SMulS a b
  | .SMulHiU a b | .SMulHiS a b => sexprVars a ++ sexprVars b
  | .SLimb s _ => [s]

/-- Over-approximating name-mention collector for one command.  `none` means
    "unknown constructor — treat as mentioning everything" (conservative). -/
def mentionsCmd : LowCT → Option (List String)
  | .RSkip => some []
  | .RSeq a b =>
      match mentionsCmd a, mentionsCmd b with
      | some la, some lb => some (la ++ lb)
      | _, _ => none
  | .RBlock b => mentionsCmd b
  | .RLetU64Zero n b => (mentionsCmd b).map (n :: ·)
  | .RScalarSet n _ => some [n]
  | .RScalarSetExpr x e => some (x :: sexprVars e)
  | .RLimbStoreExpr loc _ e => some (loc.locVar :: sexprVars e)
  | .RArrLoad dst src idxVar => some [dst.locVar, src.locVar, idxVar]
  | .RArrStore arr idxVar src => some [arr.locVar, idxVar, src.locVar]
  | .RArrLoadLit dst src _ => some [dst.locVar, src.locVar]
  | .RArrStoreLit arr _ src => some [arr.locVar, src.locVar]
  | _ => none

/-- Is `n` (possibly) mentioned in the remaining command list? -/
def tailMentions (n : String) : List LowCT → Bool
  | [] => false
  | c :: rest =>
      (match mentionsCmd c with
       | some ns => ns.contains n
       | none => true) || tailMentions n rest

/-- All strings pairwise distinct. -/
def pairwiseDistinct : List String → Bool
  | [] => true
  | x :: xs => (!xs.contains x) && pairwiseDistinct xs

/-- No bind-name occurs among the read names. -/
def disjointFrom (binds reads : List String) : Bool :=
  binds.all (fun b => !reads.contains b)

/-- Match the three-command `ltuCmds` window
    `q := ~x & y; r := ~(x^y) & (x−y); dst := ((q^r)^(q&r)) >> 63`.
    Returns `(dst, q, r, x, y, rest)`; requires `x`/`y` to be atoms, the two
    scratch slots distinct and not shadowing the atoms, and full internal
    consistency of the shape. -/
def matchLtu : List LowCT → Option (String × String × String × Atom × Atom × List LowCT)
  | .RScalarSetExpr qn (.SAnd (.SXor ex1 (.SLit o1)) ey1)
      :: .RScalarSetExpr rn (.SAnd (.SXor (.SXor ex2 ey2) (.SLit o2)) (.SSub ex3 ey3))
      :: .RScalarSetExpr dn (.SShr (.SXor (.SXor (.SVar q1) (.SVar r1))
            (.SAnd (.SVar q2) (.SVar r2))) (.SLit sh))
      :: rest =>
      match matchAtom ex1, matchAtom ey1, matchAtom ex2, matchAtom ey2,
            matchAtom ex3, matchAtom ey3 with
      | some x, some y, some x2, some y2, some x3, some y3 =>
          if o1 == onesLit && o2 == onesLit && sh == 63
              && x2 == x && x3 == x && y2 == y && y3 == y
              && q1 == qn && q2 == qn && r1 == rn && r2 == rn
              && qn != rn
              && disjointFrom [qn, rn] (x.vars ++ y.vars) then
            some (dn, qn, rn, x, y, rest)
          else none
      | _, _, _, _, _, _ => none
  | _ => none

/-- One selected step: a plain (fall-through) command or a fused carry/borrow
    window. -/
inductive Sel where
  /-- Fall through to `translateDialectControl`. -/
  | plain (c : LowCT)
  /-- `s := x + y; ltu c s x` — chain-start add. -/
  | addStart (s c : String) (x y : Atom)
  /-- `t := x+y; ltu ca t x; s := t + cp; ltu cb s t; c := ca + cb` — mid add. -/
  | addMid (s c : String) (x y : Atom) (cp : String)
  /-- `t := x + y; s := t + cp` — final add (carry-out dropped). -/
  | addFin (s : String) (x y : Atom) (cp : String)
  /-- `e := x − y; ltu w x y` — chain-start subtract (borrow out). -/
  | subStart (e w : String) (x y : Atom)
  /-- `g := x−y; ltu wa x y; e := g − wp; ltu wb g wp; w := wa + wb` — mid sub. -/
  | subMid (e w : String) (x y : Atom) (wp : String)
  deriving Repr

/-- Names a fused step reads as *words* (its operand atoms; the carry-in is
    consumed as a bit). -/
def Sel.wordReads : Sel → Option (List String)
  | .plain c => mentionsCmd c
  | .addStart _ _ x y => some (x.vars ++ y.vars)
  | .addMid _ _ x y _ => some (x.vars ++ y.vars)
  | .addFin _ x y _ => some (x.vars ++ y.vars)
  | .subStart _ _ x y => some (x.vars ++ y.vars)
  | .subMid _ _ x y _ => some (x.vars ++ y.vars)

/-- Try to match the 9-command `addMid` window at the head; `carries` is the
    set of carry names produced by earlier selected add windows (the carry-in
    must be one, so its `#b` bit is bound). -/
def matchAddMid (carries : List String) (cs : List LowCT) :
    Option (Sel × String × List LowCT) :=
  match cs with
  | .RScalarSetExpr tn (.SAdd ex ey) :: rest1 =>
      match matchAtom ex, matchAtom ey, matchLtu rest1 with
      | some x, some y, some (can, qa, ra, lx1, ly1, rest2) =>
          match rest2 with
          | .RScalarSetExpr sn (.SAdd (.SVar tn') (.SVar cp)) :: rest3 =>
              match matchLtu rest3 with
              | some (cbn, qb, rb, lx2, ly2, rest4) =>
                  match rest4 with
                  | .RScalarSetExpr cn (.SAdd (.SVar can') (.SVar cbn')) :: rest5 =>
                      let binds := [tn, qa, ra, can, sn, qb, rb, cbn, cn]
                      let reads := x.vars ++ y.vars ++ [cp]
                      if lx1 == .avar tn && ly1 == x
                          && tn' == tn && carries.contains cp
                          && lx2 == .avar sn && ly2 == .avar tn
                          && can' == can && cbn' == cbn
                          && pairwiseDistinct binds && disjointFrom binds reads
                          && !tailMentions tn rest5 && !tailMentions can rest5
                          && !tailMentions cbn rest5 && !tailMentions qa rest5
                          && !tailMentions ra rest5 && !tailMentions qb rest5
                          && !tailMentions rb rest5 then
                        some (.addMid sn cn x y cp, cn, rest5)
                      else none
                  | _ => none
              | none => none
          | _ => none
      | _, _, _ => none
  | _ => none

/-- Try to match the 9-command `subMid` window at the head; `borrows` is the
    set of borrow names produced by earlier selected sub windows. -/
def matchSubMid (borrows : List String) (cs : List LowCT) :
    Option (Sel × String × List LowCT) :=
  match cs with
  | .RScalarSetExpr gn (.SSub ex ey) :: rest1 =>
      match matchAtom ex, matchAtom ey, matchLtu rest1 with
      | some x, some y, some (wan, qa, ra, lx1, ly1, rest2) =>
          match rest2 with
          | .RScalarSetExpr en (.SSub (.SVar gn') (.SVar wp)) :: rest3 =>
              match matchLtu rest3 with
              | some (wbn, qb, rb, lx2, ly2, rest4) =>
                  match rest4 with
                  | .RScalarSetExpr wn (.SAdd (.SVar wan') (.SVar wbn')) :: rest5 =>
                      let binds := [gn, qa, ra, wan, en, qb, rb, wbn, wn]
                      let reads := x.vars ++ y.vars ++ [wp]
                      if lx1 == x && ly1 == y
                          && gn' == gn && borrows.contains wp
                          && lx2 == .avar gn && ly2 == .avar wp
                          && wan' == wan && wbn' == wbn
                          && pairwiseDistinct binds && disjointFrom binds reads
                          && !tailMentions gn rest5 && !tailMentions wan rest5
                          && !tailMentions wbn rest5 && !tailMentions qa rest5
                          && !tailMentions ra rest5 && !tailMentions qb rest5
                          && !tailMentions rb rest5 then
                        some (.subMid en wn x y wp, wn, rest5)
                      else none
                  | _ => none
              | none => none
          | _ => none
      | _, _, _ => none
  | _ => none

/-- Try to match the 4-command `addStart` window at the head. -/
def matchAddStart (cs : List LowCT) : Option (Sel × String × List LowCT) :=
  match cs with
  | .RScalarSetExpr sn (.SAdd ex ey) :: rest1 =>
      match matchAtom ex, matchAtom ey, matchLtu rest1 with
      | some x, some y, some (cn, qn, rn, lx, ly, rest2) =>
          let binds := [sn, qn, rn, cn]
          let reads := x.vars ++ y.vars
          if lx == .avar sn && ly == x
              && pairwiseDistinct binds && disjointFrom binds reads
              && !tailMentions qn rest2 && !tailMentions rn rest2 then
            some (.addStart sn cn x y, cn, rest2)
          else none
      | _, _, _ => none
  | _ => none

/-- Try to match the 4-command `subStart` window at the head. -/
def matchSubStart (cs : List LowCT) : Option (Sel × String × List LowCT) :=
  match cs with
  | .RScalarSetExpr en (.SSub ex ey) :: rest1 =>
      match matchAtom ex, matchAtom ey, matchLtu rest1 with
      | some x, some y, some (wn, qn, rn, lx, ly, rest2) =>
          let binds := [en, qn, rn, wn]
          let reads := x.vars ++ y.vars
          if lx == x && ly == y
              && pairwiseDistinct binds && disjointFrom binds reads
              && !tailMentions qn rest2 && !tailMentions rn rest2 then
            some (.subStart en wn x y, wn, rest2)
          else none
      | _, _, _ => none
  | _ => none

/-- Try to match the 2-command `addFin` window at the head (final limb: the
    carry-out is architecturally dropped). -/
def matchAddFin (carries : List String) (cs : List LowCT) :
    Option (Sel × List LowCT) :=
  match cs with
  | .RScalarSetExpr tn (.SAdd ex ey)
      :: .RScalarSetExpr sn (.SAdd (.SVar tn') (.SVar cp)) :: rest =>
      match matchAtom ex, matchAtom ey with
      | some x, some y =>
          let binds := [tn, sn]
          let reads := x.vars ++ y.vars ++ [cp]
          if tn' == tn && carries.contains cp
              && pairwiseDistinct binds && disjointFrom binds reads
              && !tailMentions tn rest then
            some (.addFin sn x y cp, rest)
          else none
      | _, _ => none
  | _ => none

/-- Constant-index environment: the names currently bound to an `SLit` by a
    plain `RScalarSetExpr` (for index re-materialisation). -/
abbrev ConstEnv := List (String × Nat)

/-- Kill a rebound name from the constant environment. -/
def ConstEnv.kill (env : ConstEnv) (n : String) : ConstEnv :=
  env.filter (fun p => p.1 != n)

/-- Names a `Sel` step (re)binds — used to invalidate `ConstEnv` entries. -/
def Sel.binds : Sel → List String
  | .plain c =>
      match c with
      | .RScalarSet n _ => [n]
      | .RScalarSetExpr n _ => [n]
      | .RLetU64Zero n _ => [n]
      | .RArrLoad dst _ _ => [dst.locVar]
      | .RArrStore arr _ _ => [arr.locVar]
      | _ => []
  | .addStart s c _ _ => [s, c]
  | .addMid s c _ _ _ => [s, c]
  | .addFin s _ _ _ => [s]
  | .subStart e w _ _ => [e, w]
  | .subMid e w _ _ _ => [e, w]

/-- The greedy selection walk: longest window first (`addMid`/`subMid`, then
    the starts, then `addFin`), else fall through one command.  `carries` /
    `borrows` accumulate the names whose `#b` bit a later window may consume.

    The walk also performs **index re-materialisation** (live-range splitting):
    an `RArrLoad`/`RArrStore` whose index variable is currently bound to an
    `SLit k` (tracked in `env`) is rewritten to use a FRESH one-shot constant
    binding (`<ix>#r<fuel>`, the `#` char disjoint from kernel slot names), so
    the shared index constants (`idxInit`'s `ix0..ix7`, otherwise live across
    the whole body) die early instead of pinning 8 registers. -/
def selectGo : Nat → ConstEnv → List String → List String → List LowCT → List Sel
  | 0, _, _, _, cs => cs.map .plain
  | _, _, _, _, [] => []
  | fuel + 1, env, carries, borrows, cs =>
      let push (sel : Sel) (env' : ConstEnv) (carries' borrows' : List String)
          (rest : List LowCT) : List Sel :=
        sel :: selectGo fuel (sel.binds.foldl ConstEnv.kill env') carries' borrows' rest
      match matchAddMid carries cs with
      | some (sel, cn, rest) => push sel env (cn :: carries) borrows rest
      | none =>
      match matchSubMid borrows cs with
      | some (sel, wn, rest) => push sel env carries (wn :: borrows) rest
      | none =>
      match matchAddStart cs with
      | some (sel, cn, rest) => push sel env (cn :: carries) borrows rest
      | none =>
      match matchSubStart cs with
      | some (sel, wn, rest) => push sel env carries (wn :: borrows) rest
      | none =>
      match matchAddFin carries cs with
      | some (sel, rest) => push sel env carries borrows rest
      | none =>
      match cs with
      | .RScalarSetExpr n (.SLit k) :: rest =>
          .plain (.RScalarSetExpr n (.SLit k))
            :: selectGo fuel ((n, k) :: ConstEnv.kill env n) carries borrows rest
      | .RArrLoad dst src ix :: rest =>
          match env.find? (fun p => p.1 == ix) with
          | some (_, k) =>
              let fresh := ix ++ "#r" ++ toString fuel
              .plain (.RScalarSetExpr fresh (.SLit k))
                :: push (.plain (.RArrLoad dst src fresh)) env carries borrows rest
          | none => push (.plain (.RArrLoad dst src ix)) env carries borrows rest
      | .RArrStore arr ix srcv :: rest =>
          match env.find? (fun p => p.1 == ix) with
          | some (_, k) =>
              let fresh := ix ++ "#r" ++ toString fuel
              .plain (.RScalarSetExpr fresh (.SLit k))
                :: push (.plain (.RArrStore arr fresh srcv)) env carries borrows rest
          | none => push (.plain (.RArrStore arr ix srcv)) env carries borrows rest
      | c :: rest => push (.plain c) env carries borrows rest
      | [] => []

/-- Flatten the `RSeq` spine to a command list (dropping `RSkip`s). -/
def flattenSeq : LowCT → List LowCT
  | .RSeq a b => flattenSeq a ++ flattenSeq b
  | .RSkip => []
  | c => [c]

/-- Which names need a *word* binding: everything any step reads as a word
    (over-approximated to "everything" if any plain command is of unknown
    shape). -/
def needFun (sels : List Sel) : String → Bool :=
  let collected : Option (List String) :=
    sels.foldl (fun acc s =>
      match acc, s.wordReads with
      | some l, some l' => some (l ++ l')
      | _, _ => none) (some [])
  match collected with
  | some l => fun n => l.contains n
  | none => fun _ => true

/-! ## 4. Fused emission -/

/-- Look up a `sword 1` (carry-bit) slot. -/
def lookupBit {Γ : Ctx} (vm : VarMap Γ) (name : String) :
    Option (CVar Γ (.sword 1)) :=
  match vm.lookup name with
  | some ⟨.sword 1, v⟩ => some v
  | _ => none

/-- Append one `varBind` of arbitrary result type (the `.sword 1` /
    `.sword 64` generalisation of `pushVarBind`). -/
def pushBindT {Γ : Ctx} (o : DTransOut Γ) {t : CryptoTy}
    (e : Expr catCryptDialect o.Γ' t) (nm : String) : DTransOut Γ :=
  { Γ' := t :: o.Γ',
    cont := ComCont.comp o.cont (ComCont.varBind e),
    vm := o.vm.bind nm }

/-- A `bvConst` expression. -/
def constE {Γ : Ctx} (w : Nat) (v : BitVec w) : Expr catCryptDialect Γ (.sword w) :=
  { op := .bvConst w v, retTy_eq := rfl, args := .nil }

/-- A `bvAddCarryLo 64` expression. -/
def carryLoE {Γ : Ctx} (a b : CVar Γ (.sword 64)) (c : CVar Γ (.sword 1)) :
    Expr catCryptDialect Γ (.sword 64) :=
  { op := .bvAddCarryLo 64, retTy_eq := rfl,
    args := .cons (toVIRVar a) (.cons (toVIRVar b) (.cons (toVIRVar c) .nil)) }

/-- A `bvAddCarryHi 64` expression. -/
def carryHiE {Γ : Ctx} (a b : CVar Γ (.sword 64)) (c : CVar Γ (.sword 1)) :
    Expr catCryptDialect Γ (.sword 1) :=
  { op := .bvAddCarryHi 64, retTy_eq := rfl,
    args := .cons (toVIRVar a) (.cons (toVIRVar b) (.cons (toVIRVar c) .nil)) }

/-- A `bvXor 64` expression. -/
def xorE {Γ : Ctx} (a b : CVar Γ (.sword 64)) :
    Expr catCryptDialect Γ (.sword 64) :=
  { op := .bvXor 64, retTy_eq := rfl,
    args := .cons (toVIRVar a) (.cons (toVIRVar b) .nil) }

/-- Resolve an atom to a bound `u64` slot name (materialising a literal as a
    fresh `bvConst` binding under `tmp`). -/
def bindAtom {Γ : Ctx} (o : DTransOut Γ) (a : Atom) (tmp : String) :
    Option (DTransOut Γ × String) :=
  match a with
  | .avar s =>
      match lookupU64 o.vm s with
      | some _ => some (o, s)
      | none => none
  | .alit n => some (pushBindT o (constE 64 (BitVec.ofNat 64 n)) tmp, tmp)

/-- Resolve an atom to the *complement* `~y` (literal complements fold at
    compile time; variables emit `y ^ ones`). -/
def bindAtomNeg {Γ : Ctx} (o : DTransOut Γ) (a : Atom) (tmp : String) :
    Option (DTransOut Γ × String) :=
  match a with
  | .alit n => some (pushBindT o (constE 64 (~~~(BitVec.ofNat 64 n))) tmp, tmp)
  | .avar s =>
      match lookupU64 o.vm s with
      | none => none
      | some _ =>
          let o1 := pushBindT o (constE 64 (BitVec.ofNat 64 onesLit)) (tmp ++ "o")
          match lookupU64 o1.vm s, lookupU64 o1.vm (tmp ++ "o") with
          | some vs, some vo => some (pushBindT o1 (xorE vs vo) tmp, tmp)
          | _, _ => none

/-- Emit `sN := lo xn yn cin; (cN#b) := hi xn yn cin` and, when `needW`, the
    zext word binding `cN := lo 0 0 (cN#b)`. -/
def emitCarryStep {Γ : Ctx} (o0 : DTransOut Γ) (xn yn cinN : String)
    (sN cN : String) (needW : Bool) : Option (DTransOut Γ) :=
  match lookupU64 o0.vm xn, lookupU64 o0.vm yn, lookupBit o0.vm cinN with
  | some va, some vb, some vc =>
      let o1 := pushBindT o0 (carryLoE va vb vc) sN
      match lookupU64 o1.vm xn, lookupU64 o1.vm yn, lookupBit o1.vm cinN with
      | some va', some vb', some vc' =>
          let o2 := pushBindT o1 (carryHiE va' vb' vc') (cN ++ "#b")
          if needW then
            let o3 := pushBindT o2 (constE 64 0) (cN ++ "#z")
            match lookupU64 o3.vm (cN ++ "#z"), lookupBit o3.vm (cN ++ "#b") with
            | some vz, some vcb => some (pushBindT o3 (carryLoE vz vz vcb) cN)
            | _, _ => none
          else some o2
      | _, _, _ => none
  | _, _, _ => none

/-- After `wN#b` (a not-borrow bit) is bound, materialise the borrow *word*
    `wN := (lo 0 0 wN#b) ^^^ 1`. -/
def emitBorrowWord {Γ : Ctx} (o : DTransOut Γ) (wN : String) :
    Option (DTransOut Γ) :=
  let o1 := pushBindT o (constE 64 0) (wN ++ "#z")
  match lookupU64 o1.vm (wN ++ "#z"), lookupBit o1.vm (wN ++ "#b") with
  | some vz, some vcb =>
      let o2 := pushBindT o1 (carryLoE vz vz vcb) (wN ++ "#zw")
      let o3 := pushBindT o2 (constE 64 1) (wN ++ "#one")
      match lookupU64 o3.vm (wN ++ "#zw"), lookupU64 o3.vm (wN ++ "#one") with
      | some va, some vb => some (pushBindT o3 (xorE va vb) wN)
      | _, _ => none
  | _, _ => none

/-- Emit a fused add step: resolve the atoms, resolve the carry-in (`none` =
    chain start, a fresh `bvConst 1 0`; `some cp` = the bit `cp#b`), then the
    lo/hi pair. -/
def emitAdd {Γ : Ctx} (vm : VarMap Γ) (sN cN : String) (x y : Atom)
    (cp : Option String) (needW : Bool) : Option (DTransOut Γ) :=
  let o0 : DTransOut Γ := { Γ' := Γ, cont := ComCont.id, vm := vm }
  match bindAtom o0 x (sN ++ "#x") with
  | none => none
  | some (o1, xn) =>
      match bindAtom o1 y (sN ++ "#y") with
      | none => none
      | some (o2, yn) =>
          match cp with
          | none =>
              let o3 := pushBindT o2 (constE 1 0) (cN ++ "#c0")
              emitCarryStep o3 xn yn (cN ++ "#c0") sN cN needW
          | some cpn => emitCarryStep o2 xn yn (cpn ++ "#b") sN cN needW

/-- Emit the fused final add (`s := lo x y cp#b`, carry-out dropped). -/
def emitAddFin {Γ : Ctx} (vm : VarMap Γ) (sN : String) (x y : Atom)
    (cp : String) : Option (DTransOut Γ) :=
  let o0 : DTransOut Γ := { Γ' := Γ, cont := ComCont.id, vm := vm }
  match bindAtom o0 x (sN ++ "#x") with
  | none => none
  | some (o1, xn) =>
      match bindAtom o1 y (sN ++ "#y") with
      | none => none
      | some (o2, yn) =>
          match lookupU64 o2.vm xn, lookupU64 o2.vm yn, lookupBit o2.vm (cp ++ "#b") with
          | some va, some vb, some vc => some (pushBindT o2 (carryLoE va vb vc) sN)
          | _, _, _ => none

/-- Emit a fused sub (borrow) step in the complement-add convention:
    `e := lo x ~y cin; w#b := hi x ~y cin` with `cin` = `1` at chain start /
    the previous not-borrow bit mid-chain, plus the borrow word when needed. -/
def emitSub {Γ : Ctx} (vm : VarMap Γ) (eN wN : String) (x y : Atom)
    (wp : Option String) (needW : Bool) : Option (DTransOut Γ) :=
  let o0 : DTransOut Γ := { Γ' := Γ, cont := ComCont.id, vm := vm }
  match bindAtom o0 x (eN ++ "#x") with
  | none => none
  | some (o1, xn) =>
      match bindAtomNeg o1 y (eN ++ "#ny") with
      | none => none
      | some (o2, nyn) =>
          let step : Option (DTransOut Γ) :=
            match wp with
            | none =>
                let o3 := pushBindT o2 (constE 1 1) (wN ++ "#c1")
                emitCarryStep o3 xn nyn (wN ++ "#c1") eN wN false
            | some wpn => emitCarryStep o2 xn nyn (wpn ++ "#b") eN wN false
          match step with
          | none => none
          | some o4 => if needW then emitBorrowWord o4 wN else some o4

/-- Emit one selected step. -/
def emitSel (need : String → Bool) {Γ : Ctx} (vm : VarMap Γ) :
    Sel → Option (DTransOut Γ)
  | .plain c => translateDialectControl vm c
  | .addStart sN cN x y => emitAdd vm sN cN x y none (need cN)
  | .addMid sN cN x y cp => emitAdd vm sN cN x y (some cp) (need cN)
  | .addFin sN x y cp => emitAddFin vm sN x y cp
  | .subStart eN wN x y => emitSub vm eN wN x y none (need wN)
  | .subMid eN wN x y wp => emitSub vm eN wN x y (some wp) (need wN)

/-- Thread the selected steps left to right. -/
def emitAll (need : String → Bool) : {Γ : Ctx} → VarMap Γ → List Sel →
    Option (DTransOut Γ)
  | Γ, vm, [] => some { Γ' := Γ, cont := ComCont.id, vm := vm }
  | _, vm, s :: rest =>
      match emitSel need vm s with
      | none => none
      | some o =>
          match emitAll need o.vm rest with
          | none => none
          | some oR => some (seqOut o oR)

/-! ## 5. The selecting front -/

/-- The carry-chain-selecting `LowCT → catCryptDialect` front: flatten the
    `RSeq` spine, select the `add2Prog` carry/borrow windows, emit
    `bvAddCarryLo`/`bvAddCarryHi` chains for the selected windows and fall
    through to `translateDialectControl` for everything else. -/
def translateDialectCarrySelect {Γ : Ctx} (vm : VarMap Γ) (c : LowCT) :
    Option (DTransOut Γ) :=
  let cmds := flattenSeq c
  let sels := selectGo cmds.length [] [] [] cmds
  emitAll (needFun sels) vm sels

/-! ## 6. Smoke test: a one-limb add-with-carry-readback body

`s0 := a0 + b0; ltu c0 s0 a0; m := 0 − c0` — the start window plus a *word*
read of the carry (forcing the zext materialisation).  The selected front and
the plain front must denote identically on the bound inputs. -/

section SmokeTest

open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)

/-- `ltuCmds`-shaped window (mirrors `Bn254TowerFrontEmit.ltuCmds`). -/
def ltuCmdsT (dst : String) (x y : SExpr) : List LowCT :=
  [ .RScalarSetExpr (dst ++ "q") (.SAnd (.SXor x (.SLit onesLit)) y),
    .RScalarSetExpr (dst ++ "r")
      (.SAnd (.SXor (.SXor x y) (.SLit onesLit)) (.SSub x y)),
    .RScalarSetExpr dst
      (.SShr (.SXor (.SXor (.SVar (dst ++ "q")) (.SVar (dst ++ "r")))
        (.SAnd (.SVar (dst ++ "q")) (.SVar (dst ++ "r")))) (.SLit 63)) ]

def seqAllT : List LowCT → LowCT
  | [] => .RSkip
  | [c] => c
  | c :: cs => .RSeq c (seqAllT cs)

/-- The smoke body. -/
def smokeBody : LowCT :=
  seqAllT ([ .RScalarSetExpr "s0" (.SAdd (.SVar "a0") (.SVar "b0")) ]
    ++ ltuCmdsT "c0" (.SVar "s0") (.SVar "a0")
    ++ [ .RScalarSetExpr "m" (.SSub (.SLit 0) (.SVar "c0")) ])

def smokeΓ : Ctx := [.sword 64, .sword 64]

def smokeVM : VarMap smokeΓ :=
  (VarMap.empty.bind (t := .sword 64) "a0").bind (t := .sword 64) "b0"

/-- Run a front on the smoke body and read back `m` (cap with `ret m`). -/
def smokeRun
    (front : VarMap smokeΓ → LowCT → Option (DTransOut smokeΓ))
    (a0 b0 : BitVec 64) : Option (BitVec 64) :=
  match front smokeVM smokeBody with
  | some r =>
      match r.vm.lookup "m" with
      | some ⟨.sword 64, v⟩ =>
          match r.cont (Com.ret (toVIRVar v)) with
          | some com =>
              some (com.denote (.cons b0 (.cons a0 .nil)))
          | none => none
      | _ => none
  | none => none

/-- The selection fires and agrees with the plain front on carry (`≥ 2^63`
    summands) and no-carry inputs. -/
example :
    [((2 : BitVec 64) ^ 63 + 5, (2 : BitVec 64) ^ 63 + 11),
     (7, 9), (BitVec.allOnes 64, 1), (0, 0)].all (fun (a, b) =>
      smokeRun (fun vm c => translateDialectCarrySelect vm c) a b
          == smokeRun (fun vm c => translateDialectControl vm c) a b
        && (smokeRun (fun vm c => translateDialectCarrySelect vm c) a b).isSome) := by
  native_decide

end SmokeTest

end CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelect
