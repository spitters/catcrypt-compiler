/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.JInstrToArithBlock
public import CatCrypt.Crypto.SecureCompilation.Ascent.EgraphBlockEquality
public import CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86BlockRoundtrip

/-!
# Shipped bytes against a source program

The byte ladder decodes a stream into `List (JInstr 64)`; `JInstrToArithBlock`
lifts a decoded block into `Com jasminDialect`; `EgraphBlockEquality` decides
equality of two dialect programs by comparing their bounded saturations. This
module composes the three, so a byte string can be related to a source program
rather than only to a specification written for it.

## What is proved

* `block_denote_source` — the composition. Under the lift's hypotheses and a
  saturation certificate against a source program `src`, the machine register
  the decoded block leaves its result in holds `src.denote V`.
* `joinBytes_decodes` — a concrete byte string decodes to the block it encodes.
* `joinBytes_denote_source` — the end-to-end instance. The bytes compute
  `x ||| x`; the source program computes `x + z`; the two saturate to the same
  term under a known-constant environment claiming `z = 0`, and the machine
  register holds the source program's value on every valuation with `z = 0`.

The instance is where the saturation earns its place: the two programs carry
different ops on different operands and agree only under the constant
hypothesis, which the canonicaliser discharges on both sides.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.Optimizer.Rewrite.Egraph

/-! ## 1. The composition -/

/-- **A decoded block against a source program.** Under the lift's hypotheses
    (the block parses, the parse elaborates, the machine state corresponds to the
    valuation, the allocation is fresh) and a certificate that the lifted program
    and `src` saturate to the same term, the output register after `runBlock`
    holds `src.denote V`. -/
theorem block_denote_source {Γ : Ctxt jasminDialect}
    (blk : List (JInstr 64)) (ops : List RawArith)
    (nm : RegMapG Γ) (find : String → Option (Ctxt.Var Γ (.reg 64)))
    (hfind : ∀ (v : Ctxt.Var Γ (.reg 64)) (r : String), find r = some v → nm v = r)
    (out : String) (ab : ArithBlock Γ) (src : Com jasminDialect Γ (.reg 64))
    (fuel : Nat) (k : KEnv Γ)
    (hparse : parseBlock blk = some ops) (helab : elabOps find ops out = some ab)
    (s : JState 64) (V : Ctxt.Valuation Γ)
    (hk : KEnv.Consistent k V)
    (hcert : saturateCom fuel ab.toCom k = saturateCom fuel src k)
    (hinterp : JStateInterpG nm V s) (hfresh : FreshFor nm (dstStream ops)) :
    (runBlock s blk).get (outReg ab nm (dstStream ops)) = src.denote V := by
  rw [liftBlock_runBlock blk ops nm find hfind out ab hparse helab s V hinterp hfresh]
  exact denote_eq_of_saturateCom_eq fuel ab.toCom src k V hk hcert

/-! ## 2. Separating a physical register name from the padding names -/

/-- A name whose character list is not `'%'` followed by a run of `'p'` is not a
    padding name. -/
theorem ne_padName_of_toList (r : String) (k : Nat)
    (h : r.toList ≠ '%' :: List.replicate k 'p') : r ≠ padName k := by
  intro he
  exact h (by rw [he, padName, String.toList_ofList])

/-- `%rcx` is not a padding name: matching lengths forces `k = 3`, and the run of
    three `'p'` is not `rcx`. -/
theorem rcx_ne_padName (k : Nat) : ("%rcx" : String) ≠ padName k := by
  refine ne_padName_of_toList _ k ?_
  rw [show ("%rcx" : String).toList = ['%', 'r', 'c', 'x'] from by decide]
  intro h
  have hl := congrArg List.length h
  simp only [List.length_cons, List.length_replicate, List.length_nil] at hl
  have hk : k = 3 := by omega
  subst hk
  simp [List.replicate] at h

/-! ## 3. The source program and the machine block

The context holds the input `x` (de Bruijn 0) and a second input `z`
(de Bruijn 1). The source program adds them; the machine block ORs `x` with
itself. They agree exactly when `z` is zero. -/

/-- The two-input context. -/
abbrev Γj : Ctxt jasminDialect := [.reg 64, .reg 64]

/-- The input `x`. -/
abbrev vx : Ctxt.Var Γj (.reg 64) := .here

/-- The second input `z`. -/
abbrev vz : Ctxt.Var Γj (.reg 64) := .there .here

/-- The source program `let s = x + z in ret s`. -/
def srcAddZ : Com jasminDialect Γj (.reg 64) :=
  .var (.mk (.regArith .add 64) rfl (.cons vx (.cons vz .nil))) (.ret .here)

/-- The machine block `mov %rcx, %rax ; or %rcx, %rax`, which leaves
    `x ||| x` in `%rcx`. -/
def joinBlock : List (JInstr 64) := lowerArith2 .or "%rax" "%rax" "%rcx"

/-- The register map: `x` lives in `%rax`, `z` in `%rbx`. -/
def nmJ : RegMapG Γj := fun v =>
  match v with
  | .here => "%rax"
  | .there .here => "%rbx"

/-- The scope map inverting `nmJ`. -/
def findJ : String → Option (Ctxt.Var Γj (.reg 64)) := fun r =>
  if r = "%rax" then some vx else if r = "%rbx" then some vz else none

/-- `findJ` is a right inverse of `nmJ` on the names it resolves. -/
theorem hfindJ (v : Ctxt.Var Γj (.reg 64)) (r : String) (h : findJ r = some v) :
    nmJ v = r := by
  unfold findJ at h
  split at h
  · rename_i hr; subst hr; injection h with h; subst h; rfl
  · split at h
    · rename_i hr; subst hr; injection h with h; subst h; rfl
    · exact absurd h (by simp)

/-- The known-constant environment claiming `z = 0` and nothing about `x`. -/
def kJ : KEnv Γj := .cons none (.cons (some 0) .nil)

/-- `kJ` is consistent with any valuation sending `z` to zero. -/
theorem kJ_consistent (V : Ctxt.Valuation Γj) (hz : vz.lookup V = 0) :
    KEnv.Consistent kJ V := by
  intro w v n hv
  match v with
  | .here => exact absurd hv (by simp [kJ, KEnv.lookup])
  | .there .here =>
      have : n = 0 := by simpa [kJ, KEnv.lookup] using hv
      subst this
      simpa using hz

/-! ## 4. The lift of the machine block -/

/-- The parse of `joinBlock`: one op, `%rcx := %rax ||| %rax`. -/
def joinOps : List RawArith := [⟨.or, "%rcx", "%rax", "%rax"⟩]

/-- `joinBlock` parses to `joinOps`. -/
theorem joinBlock_parse : parseBlock joinBlock = some joinOps := rfl

/-- The lifted program `let s = x ||| x in ret s`. -/
def joinAb : ArithBlock Γj :=
  .op .or trivial vx vx (.ret .here)

/-- The parse elaborates to `joinAb`, returning the freshly bound slot. -/
theorem joinOps_elab : elabOps findJ joinOps "%rcx" = some joinAb := rfl

/-- The output register of the lifted block is `%rcx`. -/
theorem joinAb_outReg : outReg joinAb nmJ (dstStream joinOps) = "%rcx" := rfl

/-! ## 5. The allocation is fresh -/

/-- The single destination `%rcx` is distinct from every padding name and from
    both input registers, so the allocation the lift reads off the block is
    fresh. -/
theorem joinOps_fresh : FreshFor nmJ (dstStream joinOps) := by
  constructor
  · intro i j hij
    match i, j with
    | 0, 0 => exact absurd rfl hij
    | 0, j + 1 =>
        show ("%rcx" : String) ≠ padName j
        exact rcx_ne_padName j
    | i + 1, 0 =>
        show padName i ≠ ("%rcx" : String)
        exact fun h => rcx_ne_padName i h.symm
    | i + 1, j + 1 =>
        show padName i ≠ padName j
        exact fun h => hij (by rw [padName_inj h])
  · intro i v
    match i, v with
    | 0, .here => exact by decide
    | 0, .there .here => exact by decide
    | i + 1, .here => exact fun h => ne_padName_of_toList "%rax" i (by decide) h.symm
    | i + 1, .there .here =>
        exact fun h => ne_padName_of_toList "%rbx" i (by decide) h.symm

/-! ## 6. The certificate and the end-to-end statement -/

/-- The lifted program and the source program saturate to the same term: the
    identity collapse rewrites `x + z` to `x ||| x` once the environment knows
    `z = 0`, and the lifted program is already in that form. -/
theorem joinAb_src_saturate_eq :
    saturateCom 1 joinAb.toCom kJ = saturateCom 1 srcAddZ kJ := rfl

/-- **The end-to-end instance.** The machine block leaves in `%rcx` exactly the
    value the source program `x + z` denotes, on every valuation sending `z` to
    zero and every machine state whose registers hold that valuation. -/
theorem joinBlock_denote_source (s : JState 64) (V : Ctxt.Valuation Γj)
    (hz : vz.lookup V = 0) (hinterp : JStateInterpG nmJ V s) :
    (runBlock s joinBlock).get "%rcx" = srcAddZ.denote V := by
  have h := block_denote_source joinBlock joinOps nmJ findJ hfindJ "%rcx" joinAb
    srcAddZ 1 kJ joinBlock_parse joinOps_elab s V (kJ_consistent V hz)
    joinAb_src_saturate_eq hinterp joinOps_fresh
  rwa [joinAb_outReg] at h

/-! ## 7. The byte entry

The identity allocation on the canonical register names, under which the encoder
emits the block's own names and the decoder recovers them. -/

/-- The identity allocation on the sixteen canonical general-purpose names. -/
def idAlloc : GpAlloc := gpNames.map fun r => (r, r)

/-- The encoding of `joinBlock`. -/
def joinBytes : List (BitVec 8) := encodeJBlock idAlloc joinBlock

/-- `joinBytes` decodes back to `joinBlock`. -/
theorem joinBytes_decodes :
    decodeJStream joinBlock.length joinBytes = some joinBlock := by
  rw [joinBytes, roundtrip_block idAlloc joinBlock (by decide) (by decide)]
  rfl

/-- **The chain from bytes.** The bytes decode to a block whose result register
    holds the source program's value. -/
theorem joinBytes_denote_source (s : JState 64) (V : Ctxt.Valuation Γj)
    (hz : vz.lookup V = 0) (hinterp : JStateInterpG nmJ V s) :
    ∃ blk, decodeJStream joinBlock.length joinBytes = some blk ∧
      (runBlock s blk).get "%rcx" = srcAddZ.denote V :=
  ⟨joinBlock, joinBytes_decodes, joinBlock_denote_source s V hz hinterp⟩

end CatCrypt.Crypto.SecureCompilation.Ascent
