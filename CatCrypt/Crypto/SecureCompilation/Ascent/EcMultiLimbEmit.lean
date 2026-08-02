/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Ascent.EcMultiLimbCapstone
import CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgree
import Mathlib.Tactic.Ring

/-!
# Welding the multi-limb EC subtract capstone to emitted machine-wire bytes

_Part of the AutoCorres-in-Lean ascent begun by Sebastian Graf (`sgraf812/ascent`);
see `Corres.lean` / `RunBlockCorres.lean`._

`EcMultiLimbCapstone.lean` supplies the **abstraction leg**: `corresJ_sbbChain`
lifts an arbitrary-length `sbb`-instruction chain `sbbBlock pairs` up to the clean
abstract borrow fold `sbbAbs pairs` through the flag-carrying relation `SRcarry`,
and `sbbLimbs_spec` states the base-`2^64` borrow-chain value identity (the
recomposed difference minus the top borrow weight equals `⟦X⟧ − ⟦Y⟧ − b_in`).
`X86Backend/RunBlockLsemAgree.lean` supplies the **machine-wire leg**: it bridges
the total fold `runBlock` down to the machine wire `lsemStraightMem` over `LstateM`
through the correspondence `JLstateCorr`.

This module **composes the two legs** so that the machine-wire denotation of an
emitted `sbb` chain computes the abstract borrow fold, and — through the value
identity — realizes the clean multi-limb field-subtract spec `⟦X⟧ − ⟦Y⟧ − b_in`
over the recomposed limbs. This is the `CorresJ` analogue of `feSub_endToEnd`.

## The opcode gap the composition exposes (the honest deliverable)

`RunBlockLsemAgree`'s machine-wire agreement covers the flag-free ALU core
(`add`/`sub`/`imul`/`and`/`or`/`xor`), the compile-time-offset word memory ops
(`loadMem`/`storeMem`), the two-write `mulx`, and — on the **flag/carry** axis
(§9, `adcx_case`/`adox_case`, `JLstateCorrF`) — the **ADX add-with-carry** opcodes
`adcx` / `adox` only. It does **not** cover `sbb` (subtract-with-borrow):

* `sbb ∉ InFieldArithSubset` and `sbb ∉ InSubsetM` (`sbb_not_in_bridge_subset`);
* the concrete lowering sends it to a `Lret` no-op (`sbb_lowers_to_lret`), i.e. the
  bridge emits **no wire** for an `sbb` limb;
* the flag/carry designated-register scheme is built for the `CF`/`OF` carry-**out**
  of the ADX add pair (`addCarryWord` / `carryOutBit`), not the borrow-**out** of
  `sbb`.

So the machine-wire leg for the `sbb` chain is a gap. We name it as the
honest interface `SbbChainWire` — the exact conclusion shape `RunBlockLsemAgree`
delivers for its in-subset opcodes (`runBlock_lsem_agree`), for an `sbb`-supporting
lowering. Closing it means extending the bridge's flag axis with an `sbb` leaf that
threads the borrow-out (the mirror of `adcx_case` on the underflow predicate) — the
same shape `corresJ_sbb` already proved on the abstraction side.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgree
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-! ## The opcode gap: the machine-wire bridge does not cover `sbb` -/

/-- The concrete bridge lowering `jToRM` emits **no wire** for a subtract-with-borrow
    limb: `sbb` falls through to the `Lret` no-op arm. Concrete evidence that the
    machine-wire leg (`runBlock_lsem_agree`, built on `jToRM`) says nothing about an
    `sbb` chain. -/
theorem sbb_lowers_to_lret (dst src : String) :
    jToRM (.sbb dst (.reg src)) = (.Lret, .reg none) := rfl

/-- `sbb` is outside the machine-wire agreement subset `InFieldArithSubset` (the
    flag-free ALU core + word memory). Together with `sbb_not_in_subsetM` this pins
    the opcode gap: `RunBlockLsemAgree` covers `adcx`/`adox` on the flag axis, never
    `sbb`. -/
theorem sbb_not_in_field_subset (dst src : String) :
    ¬ InFieldArithSubset (.sbb dst (.reg src)) := by
  intro h; exact h

/-- `sbb` is outside `InSubsetM` (the ALU core + memory + `mulx`), too. The
    machine-wire block lemmas `runBlock_lsem_agree` / `runBlock_lsem_agreeM` therefore
    do not apply to any block containing an `sbb` limb. -/
theorem sbb_not_in_subsetM (dst src : String) :
    ¬ InSubsetM (.sbb dst (.reg src)) := by
  intro h; exact h

/-! ## The machine-wire leg for the `sbb` chain (the honest interface)

Because the bridge's concrete `jToRM` does not lower `sbb`, the machine-wire leg is
stated over an **arbitrary** lowering `lowered : List LinstrRM` of the `sbb`
chain — precisely the conclusion `RunBlockLsemAgree.runBlock_lsem_agree` proves for
its in-subset opcodes, generalized to the `sbb` chain that lies outside that subset.
Discharging this hypothesis is exactly the residual bridge work (an `sbb` borrow
leaf on the flag axis). -/

/-- `SbbChainWire lowered block`: some machine-wire program `lowered` agrees with the
    total fold `runBlock` on `block` — from any `JLstateCorr`-related start state it
    runs to completion under `lsemStraightMem` (no failure / TOTALITY) and its result
    corresponds, via `JLstateCorr`, to the `runBlock` result. This is the shape of
    `runBlock_lsem_agree`'s conclusion; for the `sbb` chain it is the open leg. -/
def SbbChainWire (lowered : List LinstrRM) (block : List (JInstr 64)) : Prop :=
  ∀ (s : JState 64) (ls : LstateM), JLstateCorr s ls →
    ∃ ls', lsemStraightMem lowered ls = some ls' ∧ JLstateCorr (runBlock s block) ls'

/-! ## The welded capstone: abstraction leg ∘ machine-wire leg -/

/-- **The `sbb`-chain emit ∘ abstraction composition.** Given the machine-wire leg
    for the chain (`hwire`) and a start state related on both sides (`hSR` on the
    abstraction side, `hcorr` on the machine-wire side), the emitted bytes `lowered`
    run to completion under `lsemStraightMem` and their final register file reads
    back — at every register, at width 64 — exactly the abstract borrow-fold result
    `sbbAbs pairs a`. The abstraction leg is `corresJ_sbbChain` (proved); the
    machine-wire leg is `hwire`; the composition is register-agreement transitivity
    (`JLstateCorr.regAgree` ∘ `SRcarry`). This is the `CorresJ` analogue of
    `feSub_endToEnd` at the register level. -/
theorem sbbChain_emit_realizes_abstract
    (pairs : List (String × String)) (lowered : List LinstrRM)
    (hwire : SbbChainWire lowered (sbbBlock pairs))
    (st : JState 64) (ls : LstateM) (a : ACarry)
    (hSR : SRcarry st a) (hcorr : JLstateCorr st ls) :
    ∃ ls', lsemStraightMem lowered ls = some ls' ∧
      ∀ r, ls'.reg.getW r 64 = some ((sbbAbs pairs a).regs r) := by
  obtain ⟨ls', hls', hcorr'⟩ := hwire st ls hcorr
  refine ⟨ls', hls', ?_⟩
  have habs := corresJ_sbbChain pairs st a hSR trivial
  intro r
  rw [hcorr'.regAgree r, habs.1 r]

/-! ## The value-level readout bridge and the field-subtract capstone

The register-level composition above hands the abstract borrow-fold words to the
machine wire. To read those words as the recomposed multi-precision **value** and
tie it to the clean `⟦X⟧ − ⟦Y⟧ − b_in` spec, we need the destination-window readout
of the abstract fold to coincide with the limbwise `sbbLimbs` output. That
coincidence is a register-aliasing bookkeeping fact (the destination limbs are
distinct and disjoint from the later sources) — the one hard leg, left as
the named hypothesis `SbbChainReadout`. -/

/-- `SbbChainReadout pairs a`: the abstract borrow-fold `sbbAbs pairs a`, read out at
    the destination-register window `pairs.map Prod.fst`, equals the limbwise
    subtract-with-borrow `sbbLimbs` on the abstract minuend / subtrahend limb windows;
    and its final carry equals the borrow-out. Holds when the destination registers
    are distinct and disjoint from the sources read at later limbs (no aliasing) — the
    bookkeeping content of a concrete field-sub kernel's register allocation. -/
def SbbChainReadout (pairs : List (String × String)) (a : ACarry) : Prop :=
  (pairs.map Prod.fst).map (fun d => (sbbAbs pairs a).regs d)
      = (sbbLimbs ((pairs.map Prod.fst).map a.regs)
          ((pairs.map Prod.snd).map a.regs) a.cf).1
    ∧ (sbbAbs pairs a).cf
      = (sbbLimbs ((pairs.map Prod.fst).map a.regs)
          ((pairs.map Prod.snd).map a.regs) a.cf).2

/-- **The multi-limb field-subtract capstone at the machine wire.** Composing the
    register-level result (`sbbChain_emit_realizes_abstract`), the value readout
    bridge (`hreadout`), and the borrow-chain identity (`sbbLimbs_spec`): the emitted
    `sbb`-chain bytes `lowered` run to completion, their final register file reads
    back the abstract borrow-fold at every register, and the destination limb window
    — recomposed via `limbVal`, corrected by the top borrow-out at weight
    `2^(64·n)` — equals the true multi-precision difference `⟦X⟧ − ⟦Y⟧ − b_in` over
    `ℤ`. The `CorresJ` analogue of `feSub_endToEnd` for the whole multi-limb chain. -/
theorem sbbChain_emit_realizes_fieldSub
    (pairs : List (String × String)) (lowered : List LinstrRM)
    (hwire : SbbChainWire lowered (sbbBlock pairs))
    (st : JState 64) (ls : LstateM) (a : ACarry)
    (hSR : SRcarry st a) (hcorr : JLstateCorr st ls)
    (hreadout : SbbChainReadout pairs a) :
    ∃ ls', lsemStraightMem lowered ls = some ls' ∧
      (∀ r, ls'.reg.getW r 64 = some ((sbbAbs pairs a).regs r)) ∧
      ((limbVal ((pairs.map Prod.fst).map (fun d => (sbbAbs pairs a).regs d)) : Int)
          - (2 : Int) ^ (64 * (pairs.map Prod.fst).length)
            * (if (sbbAbs pairs a).cf then (1 : Int) else 0)
        = (limbVal ((pairs.map Prod.fst).map a.regs) : Int)
          - limbVal ((pairs.map Prod.snd).map a.regs) - (if a.cf then 1 else 0)) := by
  obtain ⟨ls', hls', hwire_reg⟩ :=
    sbbChain_emit_realizes_abstract pairs lowered hwire st ls a hSR hcorr
  refine ⟨ls', hls', hwire_reg, ?_⟩
  obtain ⟨hr1, hr2⟩ := hreadout
  set xs := (pairs.map Prod.fst).map a.regs with hxs
  set ys := (pairs.map Prod.snd).map a.regs with hys
  have hlen : xs.length = ys.length := by simp only [hxs, hys, List.length_map]
  have hlen2 : (pairs.map Prod.fst).length = xs.length := by simp only [hxs, List.length_map]
  rw [hr1, hr2, hlen2]
  exact sbbLimbs_spec xs ys a.cf hlen

/-! ## The machine-wire leg, discharged: the CF-slot `sbb`-chain block lift

`sbb_case` (`RunBlockLsemAgree`, §11) is the per-instruction leaf: one `.sbb` limb's
`runBlock` step agrees with its two-wire lsem image `[SBBHI cfNew; SBB dst]` under
the `CF`-only correspondence `JLstateCorrCF`, migrating the designated borrow slot
`cfN` to a fresh `cfNew`. This section lifts that leaf over a whole `sbbBlock pairs`
chain — the `runBlock_lsem_agree` analogue for `sbb`, at the `JLstateCorrCF`
correspondence the borrow chain lives on.

The correspondence is `JLstateCorrCF`, not the flag-free `JLstateCorr` of
`SbbChainWire`, for the same reason the ADX chain lift lands in `JLstateCorrF`: each
limb's lsem image writes its borrow-out to a fresh width-1 slot register, so the
final lsem register file disagrees with `runBlock` at those synthetic slots (which
`runBlock` never writes). `JLstateCorrCF` tracks register agreement OFF the flag
namespace `flg` plus the one designated borrow slot — the axis through which the
destination limb window (all off-flag) is read. So the `sbb` chain is bridged under
`JLstateCorrCF`; the plain-`JLstateCorr` `SbbChainWire` is the wrong correspondence
for a borrow-threading lowering. -/

/-- The two-wire lsem lowering of one `.sbb dst (.reg src)` limb reading the current
    borrow slot `cfN` and writing the borrow-out to a fresh slot `cfNew`: the
    structured `SBBHI` (borrow-out) then `SBB` (data). The exact pair `sbb_case`
    bridges. -/
def sbbColumnL (dst src cfN cfNew : String) : List LinstrRM :=
  [ (.Lopn [.reg cfNew] (withWidthTag 64 "SBBHI") [.reg dst, .reg src, .reg cfN], .reg none),
    (.Lopn [.reg dst]   (withWidthTag 64 "SBB")   [.reg dst, .reg src, .reg cfN], .reg none) ]

/-- `sbb_case` repackaged in the `∀ s ls, JLstateCorrCF → …` shape the chain lift
    consumes: one `.sbb` limb bridges `runBlock ↔ lsem`, migrating the borrow slot
    `cfN` to the fresh `cfNew`. -/
theorem sbbColumn_agree (flg : String → Prop) (dst src cfN cfNew : String)
    (hdst : ¬ flg dst) (hsrc : ¬ flg src) (hNew : flg cfNew)
    (hNe_dst : cfNew ≠ dst) (hNe_src : cfNew ≠ src) (hNe_cf : cfNew ≠ cfN) :
    ∀ (s : JState 64) (ls : LstateM), JLstateCorrCF s ls flg cfN →
      ∃ ls', lsemStraightMem (sbbColumnL dst src cfN cfNew) ls = some ls' ∧
        JLstateCorrCF (runBlock s [.sbb dst (.reg src)]) ls' flg cfNew := by
  intro s ls hcorr
  exact sbb_case s ls flg cfN hcorr dst src cfNew hdst hsrc hNew hNe_dst hNe_src hNe_cf

/-- **Borrow-slot-migrating sequential composition.** The `CF`-only analogue of
    `runBlock_lsem_agreeF_seq_migrate`: `b1` migrates the borrow slot `cfN` to `cf1`,
    `b2` migrates `cf1` to `cf2`, and their concatenation migrates `cfN` to `cf2`.
    Block concatenation, dropping the `OF` axis the `sbb` chain does not use. -/
theorem runBlock_lsem_agreeCF_seq_migrate
    (b1 b2 : List (JInstr 64)) (lb1 lb2 : List LinstrRM)
    (flg : String → Prop) (cfN cf1 cf2 : String)
    (h1 : ∀ (s : JState 64) (ls : LstateM), JLstateCorrCF s ls flg cfN →
      ∃ ls', lsemStraightMem lb1 ls = some ls' ∧ JLstateCorrCF (runBlock s b1) ls' flg cf1)
    (h2 : ∀ (s : JState 64) (ls : LstateM), JLstateCorrCF s ls flg cf1 →
      ∃ ls', lsemStraightMem lb2 ls = some ls' ∧ JLstateCorrCF (runBlock s b2) ls' flg cf2)
    (s : JState 64) (ls : LstateM) (h : JLstateCorrCF s ls flg cfN) :
    ∃ ls', lsemStraightMem (lb1 ++ lb2) ls = some ls' ∧
      JLstateCorrCF (runBlock s (b1 ++ b2)) ls' flg cf2 := by
  obtain ⟨ls1, hstep1, hcorr1⟩ := h1 s ls h
  obtain ⟨ls2, hstep2, hcorr2⟩ := h2 (runBlock s b1) ls1 hcorr1
  refine ⟨ls2, ?_, ?_⟩
  · rw [lsemStraightMem_append, hstep1, Option.bind]; exact hstep2
  · rw [runBlock_append]; exact hcorr2

/-- The last borrow slot reached by a chain starting at `cf0` and consuming the fresh
    output slots `cfs`, one per limb: `cf0` if the chain is empty, else the last
    element of `cfs`. -/
def finalSlot : String → List String → String
  | cf0, []          => cf0
  | _,   cfn :: rest => finalSlot cfn rest

/-- The lsem lowering of a whole `sbb` chain `pairs`, threading the fresh borrow
    slots `cfs` (one output slot per limb, in order) from the initial slot `cf0`. -/
def sbbChainL : String → List (String × String) → List String → List LinstrRM
  | cf0, (d, src) :: ps, cfn :: rest => sbbColumnL d src cf0 cfn ++ sbbChainL cfn ps rest
  | _,   _,              _           => []

/-- The freshness / non-aliasing side-conditions the `sbb` chain lift needs: at each
    limb `(d, src)` with fresh output slot `cfn`, the data registers `d`, `src` are
    off the flag namespace, `cfn` is a flag name distinct from `d`, `src`, and the
    current input slot; and `cfs` has exactly one slot per limb. -/
def SbbChainFresh (flg : String → Prop) : String → List (String × String) → List String → Prop
  | _,   [],             []          => True
  | cf0, (d, src) :: ps, cfn :: rest =>
      ¬ flg d ∧ ¬ flg src ∧ flg cfn ∧ cfn ≠ d ∧ cfn ≠ src ∧ cfn ≠ cf0 ∧
        SbbChainFresh flg cfn ps rest
  | _,   _,              _           => False

/-- **The `sbb`-chain block lift (the `runBlock_lsem_agree` analogue for `sbb`).**
    Under the freshness side-conditions, the whole `sbbBlock pairs` chain runs to
    completion under `lsemStraightMem` on the threaded lowering `sbbChainL cf0 pairs
    cfs` (TOTALITY) and its result corresponds — on the register (off flag), memory,
    and borrow-slot axes — to the total fold `runBlock`, migrating the borrow slot
    `cf0` to `finalSlot cf0 cfs`. Straight-line induction on the chain, each limb via
    `sbbColumn_agree`, composed with `runBlock_lsem_agreeCF_seq_migrate`. -/
theorem runBlock_lsem_agreeCF (flg : String → Prop) :
    ∀ (pairs : List (String × String)) (cf0 : String) (cfs : List String),
      SbbChainFresh flg cf0 pairs cfs →
      ∀ (s : JState 64) (ls : LstateM), JLstateCorrCF s ls flg cf0 →
        ∃ ls', lsemStraightMem (sbbChainL cf0 pairs cfs) ls = some ls' ∧
          JLstateCorrCF (runBlock s (sbbBlock pairs)) ls' flg (finalSlot cf0 cfs) := by
  intro pairs
  induction pairs with
  | nil =>
    intro cf0 cfs hfresh s ls h
    match cfs, hfresh with
    | [], _ => exact ⟨ls, rfl, h⟩
  | cons pr ps ih =>
    intro cf0 cfs hfresh s ls h
    obtain ⟨d, src⟩ := pr
    match cfs, hfresh with
    | cfn :: rest, hfresh =>
      obtain ⟨hd, hsrc, hcfn, hne_d, hne_src, hne_cf, htail⟩ := hfresh
      have hcol := sbbColumn_agree flg d src cf0 cfn hd hsrc hcfn hne_d hne_src hne_cf
      have htl := ih cfn rest htail
      have hcomp := runBlock_lsem_agreeCF_seq_migrate
        [.sbb d (.reg src)] (sbbBlock ps)
        (sbbColumnL d src cf0 cfn) (sbbChainL cfn ps rest)
        flg cf0 cfn (finalSlot cfn rest)
        hcol htl s ls h
      simpa only [sbbChainL, sbbBlock, finalSlot, List.singleton_append] using hcomp

/-- `SbbChainWireCF flg cf0 cfEnd lowered block`: the `JLstateCorrCF` analogue of
    `SbbChainWire` — some machine-wire program `lowered` agrees with the total fold
    `runBlock` on `block`, from any start state corresponding under `JLstateCorrCF`
    at borrow slot `cf0`, migrating the borrow slot to `cfEnd`. This is the
    correspondence a borrow-threading lowering delivers; `runBlock_lsem_agreeCF`
    discharges it for the `sbb` chain. -/
def SbbChainWireCF (flg : String → Prop) (cf0 cfEnd : String)
    (lowered : List LinstrRM) (block : List (JInstr 64)) : Prop :=
  ∀ (s : JState 64) (ls : LstateM), JLstateCorrCF s ls flg cf0 →
    ∃ ls', lsemStraightMem lowered ls = some ls' ∧ JLstateCorrCF (runBlock s block) ls' flg cfEnd

/-- **The `sbb`-chain machine-wire leg.** The threaded lowering `sbbChainL cf0 pairs
    cfs` realizes the `JLstateCorrCF` wire interface `SbbChainWireCF` for
    `sbbBlock pairs`, migrating `cf0` to `finalSlot cf0 cfs`. `SbbChainWireCF` states
    the correspondence a borrow-threading lowering satisfies; `runBlock_lsem_agreeCF`
    supplies it. -/
theorem sbbChainWireCF_discharged (flg : String → Prop)
    (pairs : List (String × String)) (cf0 : String) (cfs : List String)
    (hfresh : SbbChainFresh flg cf0 pairs cfs) :
    SbbChainWireCF flg cf0 (finalSlot cf0 cfs) (sbbChainL cf0 pairs cfs) (sbbBlock pairs) :=
  fun s ls h => runBlock_lsem_agreeCF flg pairs cf0 cfs hfresh s ls h

/-- **The welded `sbb`-chain capstone with the machine-wire leg discharged.** The
    `JLstateCorrCF` counterpart of `sbbChain_emit_realizes_abstract`, but with the
    machine-wire leg PROVED (via `runBlock_lsem_agreeCF`) rather than assumed: from a
    start state related on both sides (`hSR` abstraction, `hcorr` machine-wire at
    borrow slot `cf0`) and the freshness side-conditions, the threaded emitted bytes
    `sbbChainL cf0 pairs cfs` run to completion under `lsemStraightMem` and their
    final register file reads back — at every OFF-FLAG register, at width 64 — exactly
    the abstract borrow-fold result `sbbAbs pairs a`. The abstraction leg is
    `corresJ_sbbChain`; the machine-wire leg is `runBlock_lsem_agreeCF`; the
    composition is register-agreement transitivity (`JLstateCorrCF.regAgree` ∘
    `SRcarry`). Off-flag is exactly the destination-limb window a field-sub kernel
    reads. -/
theorem sbbChain_emit_realizes_abstract_CF (flg : String → Prop)
    (pairs : List (String × String)) (cf0 : String) (cfs : List String)
    (hfresh : SbbChainFresh flg cf0 pairs cfs)
    (st : JState 64) (ls : LstateM) (a : ACarry)
    (hSR : SRcarry st a) (hcorr : JLstateCorrCF st ls flg cf0) :
    ∃ ls', lsemStraightMem (sbbChainL cf0 pairs cfs) ls = some ls' ∧
      ∀ r, ¬ flg r → ls'.reg.getW r 64 = some ((sbbAbs pairs a).regs r) := by
  obtain ⟨ls', hls', hcorr'⟩ := runBlock_lsem_agreeCF flg pairs cf0 cfs hfresh st ls hcorr
  refine ⟨ls', hls', ?_⟩
  have habs := corresJ_sbbChain pairs st a hSR trivial
  intro r hr
  rw [hcorr'.regAgree r hr, habs.1 r]

end CatCrypt.Crypto.SecureCompilation.Ascent
