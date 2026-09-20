/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.FramedJInstrTie

/-!
# The straight-line block tie under a liveness condition

`JasminComRunBlockSeq.lowerBlock_tie` ties a straight-line `ArithBlock`'s
`Com jasminDialect` denotation to `runBlock` of its lowering under `FreshFor`:
the destination stream is injective and disjoint from the whole range of the
register map. A register allocator writes a result into a register whose previous
occupant is dead, so a body it emits need not satisfy the second conjunct.

This module states the same conclusion under a per-step liveness condition.

## The three pieces

* `LiveVar block w` — the variables of the block's entry context whose registers
  the lowered instructions still read: the returned variable, the operands of
  the leading operation, and whatever the continuation reads through its own
  shifted variable. The index of a memory arm is a compile-time displacement in
  the lowering, so it reads no register and is not live.
* `JStateInterpLive ρ block V s` — the state correspondence restricted to
  `LiveVar block`: the machine register of every live variable carries that
  variable's value.
* `LiveDisj block ρ g` — the per-step destination condition: at each binder the
  destination `g 0` differs from the register of every variable the continuation
  still reads, and, at a two-operand arm, from the register of the second
  operand, which the two-address lowering's priming `mov` would otherwise
  clobber.

## What is proved

* `lowerBlock_tie_live` — the block tie under `JStateInterpLive` and `LiveDisj`.
* `LiveDisj_of_FreshFor` and `JStateInterpLive_of_JStateInterpG` — `FreshFor`
  and the unrestricted correspondence imply the two liveness hypotheses, so
  `lowerBlock_tie` is the instance `lowerBlock_tie_of_FreshFor`.
* `liftBlock_runBlock_live` and `coreSegment_denote_live` — the liveness forms
  of the packaged lift and the segment tie.
* `comBlock2_liveDisj` — the physical-ABI body of `comBlock2`, whose destination
  stream collides with its register map (`shipped_stream_collides`), satisfies
  `LiveDisj`; `comBlock2_core_live_denote` ties that body's arithmetic segment to
  the source program's denotation at an arbitrary entry state carrying the
  valuation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.GatherImmForms (gatherJBlock6)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull (physBodyOf)

/-! ## 1. Liveness of a block's entry variables -/

/-- **The variables a block still reads.** A variable of the block's entry
    context is live when the block returns it, when the leading binder's lowering
    reads its register, or when the continuation reads it through the shifted
    variable. The scalar arms read their operands; an element store reads the
    source register; an element load reads no register, since the lowering takes
    the index as a compile-time displacement. -/
def LiveVar : {Γ : Ctxt jasminDialect} → ArithBlock Γ → Ctxt.Var Γ (.reg 64) → Prop
  | _, .ret v, w => w = v
  | _, .op _ _ a b rest, w => w = a ∨ w = b ∨ LiveVar rest (.there w)
  | _, .un _ _ a rest, w => w = a ∨ LiveVar rest (.there w)
  | _, .cnst _ rest, w => LiveVar rest (.there w)
  | _, .load _ _ _ _ _ _ rest, w => LiveVar rest (.there w)
  | _, .store _ _ _ _ _ _ src rest, w => w = src ∨ LiveVar rest (.there w)

/-- **The state correspondence on the live variables.** The machine register
    `ρ v` holds `v.lookup V` for every variable the block still reads. The
    restriction of `JStateInterpG` to `LiveVar block`. -/
def JStateInterpLive {Γ : Ctxt jasminDialect} (ρ : RegMapG Γ)
    (block : ArithBlock Γ) (V : Ctxt.Valuation Γ) (s : JState 64) : Prop :=
  ∀ v : Ctxt.Var Γ (.reg 64), LiveVar block v → s.get (ρ v) = v.lookup V

/-- The unrestricted correspondence restricts to the live variables. -/
theorem JStateInterpLive_of_JStateInterpG {Γ : Ctxt jasminDialect} {ρ : RegMapG Γ}
    {block : ArithBlock Γ} {V : Ctxt.Valuation Γ} {s : JState 64}
    (h : JStateInterpG ρ V s) : JStateInterpLive ρ block V s :=
  fun v _ => h v

/-! ## 2. The per-step destination condition -/

/-- **The destination condition at every binder.** At each binder the freshly
    allocated destination `g 0` differs from the register of every variable the
    continuation still reads, and at a two-operand arm from the register of the
    second operand, which the priming `mov` of the two-address lowering writes
    before the operation reads it. A destination may coincide with the register
    of a variable that is dead from that binder on. -/
def LiveDisj : {Γ : Ctxt jasminDialect} → ArithBlock Γ → RegMapG Γ →
    (Nat → String) → Prop
  | _, .ret _, _, _ => True
  | _, .op _ _ _ b rest, ρ, g =>
      g 0 ≠ ρ b ∧ (∀ w, LiveVar rest (.there w) → g 0 ≠ ρ w) ∧
        LiveDisj rest (ρ.extend (g 0)) (fun k => g (k + 1))
  | _, .un _ _ _ rest, ρ, g =>
      (∀ w, LiveVar rest (.there w) → g 0 ≠ ρ w) ∧
        LiveDisj rest (ρ.extend (g 0)) (fun k => g (k + 1))
  | _, .cnst _ rest, ρ, g =>
      (∀ w, LiveVar rest (.there w) → g 0 ≠ ρ w) ∧
        LiveDisj rest (ρ.extend (g 0)) (fun k => g (k + 1))
  | _, .load _ _ _ _ _ _ rest, ρ, g =>
      (∀ w, LiveVar rest (.there w) → g 0 ≠ ρ w) ∧
        LiveDisj rest (ρ.extend (g 0)) (fun k => g (k + 1))
  | _, .store _ _ _ _ _ _ _ rest, ρ, g =>
      LiveDisj rest (RegMapG.shiftArr ρ) g

/-- A fresh allocation satisfies the per-step destination condition: a
    destination disjoint from the whole range of the register map is in
    particular disjoint from the registers of the live variables. -/
theorem LiveDisj_of_FreshFor : {Γ : Ctxt jasminDialect} → (block : ArithBlock Γ) →
    (ρ : RegMapG Γ) → (g : Nat → String) → FreshFor ρ g → LiveDisj block ρ g
  | _, .ret _, _, _, _ => trivial
  | _, .op _ _ _ b rest, ρ, g, hfresh =>
      ⟨hfresh.2 0 b, fun w _ => hfresh.2 0 w,
        LiveDisj_of_FreshFor rest (ρ.extend (g 0)) (fun k => g (k + 1))
          (FreshFor_extend ρ g hfresh)⟩
  | _, .un _ _ _ rest, ρ, g, hfresh =>
      ⟨fun w _ => hfresh.2 0 w,
        LiveDisj_of_FreshFor rest (ρ.extend (g 0)) (fun k => g (k + 1))
          (FreshFor_extend ρ g hfresh)⟩
  | _, .cnst _ rest, ρ, g, hfresh =>
      ⟨fun w _ => hfresh.2 0 w,
        LiveDisj_of_FreshFor rest (ρ.extend (g 0)) (fun k => g (k + 1))
          (FreshFor_extend ρ g hfresh)⟩
  | _, .load _ _ _ _ _ _ rest, ρ, g, hfresh =>
      ⟨fun w _ => hfresh.2 0 w,
        LiveDisj_of_FreshFor rest (ρ.extend (g 0)) (fun k => g (k + 1))
          (FreshFor_extend ρ g hfresh)⟩
  | _, .store _ _ _ _ _ _ _ rest, ρ, g, hfresh =>
      LiveDisj_of_FreshFor rest (RegMapG.shiftArr ρ) g (FreshFor_shiftArr ρ g hfresh)

/-! ## 3. The tie -/

/-- **The block tie under liveness.** For every straight-line `ArithBlock`, under
    the correspondence on the live variables and the per-step destination
    condition, reading the block's output register after `runBlock` of the whole
    lowered block equals the multi-op `Com jasminDialect` program's denotation
    on `V`.

    Structural induction on the block, as in `lowerBlock_tie`: each binder
    extends the restricted correspondence to the continuation — the new slot
    holds the binder's value, and an old register survives by the per-op frame
    together with the step's destination condition — and `LiveDisj` carries the
    condition for the continuation in its own recursive component. -/
theorem lowerBlock_tie_live : {Γ : Ctxt jasminDialect} → (block : ArithBlock Γ) →
    (ρ : RegMapG Γ) → (g : Nat → String) → (s : JState 64) →
    (V : Ctxt.Valuation Γ) → JStateInterpLive ρ block V s → LiveDisj block ρ g →
    (hmem : BlockMemOk block ρ g V s := by first | trivial | simp [BlockMemOk]) →
    (runBlock s (lowerBlock block ρ g)).get (outReg block ρ g)
      = block.toCom.denote V
  | _, .ret v, ρ, g, s, V, hinterp, _, _ => by
      simp only [lowerBlock, outReg, runBlock_nil, ArithBlock.toCom, Com.denote]
      exact hinterp v rfl
  | _, .op bop hbop a b rest, ρ, g, s, V, hinterp, hlive, hmem => by
      obtain ⟨hb, hrest, hlive'⟩ := hlive
      have hinterp' : JStateInterpLive (ρ.extend (g 0)) rest
          (V.extend ((arithExpr bop a b).denote V))
          (runBlock s (lowerArith2 bop (ρ a) (ρ b) (g 0))) := by
        intro w hw
        match w with
        | .here =>
            show (runBlock s (lowerArith2 bop (ρ a) (ρ b) (g 0))).get (g 0)
                = bop.apply (a.lookup V) (b.lookup V)
            rw [lowerArith2_get_dst bop hbop (ρ a) (ρ b) (g 0) hb s,
              hinterp a (Or.inl rfl), hinterp b (Or.inr (Or.inl rfl))]
        | .there w0 =>
            show (runBlock s (lowerArith2 bop (ρ a) (ρ b) (g 0))).get (ρ w0)
                = w0.lookup V
            rw [lowerArith2_get_other bop hbop (ρ a) (ρ b) (g 0) (ρ w0)
              (fun h => (hrest w0 hw) h.symm) s]
            exact hinterp w0 (Or.inr (Or.inr hw))
      have key := lowerBlock_tie_live rest (ρ.extend (g 0)) (fun k => g (k + 1))
        (runBlock s (lowerArith2 bop (ρ a) (ρ b) (g 0)))
        (V.extend ((arithExpr bop a b).denote V)) hinterp' hlive' hmem
      simpa only [lowerBlock, outReg, ArithBlock.toCom, Com.denote, runBlock_append]
        using key
  | _, .un uop huop a rest, ρ, g, s, V, hinterp, hlive, hmem => by
      obtain ⟨hrest, hlive'⟩ := hlive
      have hinterp' : JStateInterpLive (ρ.extend (g 0)) rest
          (V.extend ((unExpr uop a).denote V))
          (runBlock s (uop.toJInstr (g 0) (ρ a))) := by
        intro w hw
        match w with
        | .here =>
            show (runBlock s (uop.toJInstr (g 0) (ρ a))).get (g 0)
                = (unExpr uop a).denote V
            rw [lowerUn_get_dst uop huop (ρ a) (g 0) s, hinterp a (Or.inl rfl),
              unExpr_denote]
        | .there w0 =>
            show (runBlock s (uop.toJInstr (g 0) (ρ a))).get (ρ w0) = w0.lookup V
            rw [lowerUn_get_other uop (ρ a) (g 0) (ρ w0)
              (fun h => (hrest w0 hw) h.symm) s]
            exact hinterp w0 (Or.inr hw)
      have key := lowerBlock_tie_live rest (ρ.extend (g 0)) (fun k => g (k + 1))
        (runBlock s (uop.toJInstr (g 0) (ρ a)))
        (V.extend ((unExpr uop a).denote V)) hinterp' hlive' hmem
      simpa only [lowerBlock, outReg, ArithBlock.toCom, Com.denote, runBlock_append]
        using key
  | _, .cnst n rest, ρ, g, s, V, hinterp, hlive, hmem => by
      obtain ⟨hrest, hlive'⟩ := hlive
      have hinterp' : JStateInterpLive (ρ.extend (g 0)) rest
          (V.extend ((constExpr n).denote V))
          (runBlock s (lowerConst n (g 0))) := by
        intro w hw
        match w with
        | .here =>
            show (runBlock s (lowerConst n (g 0))).get (g 0) = (constExpr n).denote V
            rw [lowerConst_get_dst n (g 0) s, constExpr_denote]
        | .there w0 =>
            show (runBlock s (lowerConst n (g 0))).get (ρ w0) = w0.lookup V
            rw [lowerConst_get_other n (g 0) (ρ w0)
              (fun h => (hrest w0 hw) h.symm) s]
            exact hinterp w0 hw
      have key := lowerBlock_tie_live rest (ρ.extend (g 0)) (fun k => g (k + 1))
        (runBlock s (lowerConst n (g 0)))
        (V.extend ((constExpr n).denote V)) hinterp' hlive' hmem
      simpa only [lowerBlock, outReg, ArithBlock.toCom, Com.denote, runBlock_append]
        using key
  | _, .load _ k _ base arr i rest, ρ, g, s, V, hinterp, hlive, hmem => by
      obtain ⟨hrest, hlive'⟩ := hlive
      have hinterp' : JStateInterpLive (ρ.extend (g 0)) rest
          (V.extend ((loadExpr arr i).denote V))
          (runBlock s (lowerLoad (g 0) base k)) := by
        intro w hw
        match w with
        | .here =>
            show (runBlock s (lowerLoad (g 0) base k)).get (g 0)
                = stackGet (arr.lookup V) (i.lookup V).toNat
            rw [lowerLoad_get_dst (g 0) base k, hmem.2.1, hmem.1]
        | .there w0 =>
            show (runBlock s (lowerLoad (g 0) base k)).get (ρ w0) = w0.lookup V
            rw [lowerLoad_get_other (g 0) base k (ρ w0)
              (fun h => (hrest w0 hw) h.symm)]
            exact hinterp w0 hw
      have key := lowerBlock_tie_live rest (ρ.extend (g 0)) (fun m => g (m + 1))
        (runBlock s (lowerLoad (g 0) base k))
        (V.extend ((loadExpr arr i).denote V)) hinterp' hlive' hmem.2.2
      simpa only [lowerBlock, outReg, ArithBlock.toCom, Com.denote, runBlock_append]
        using key
  | _, .store _ k _ base arr i src rest, ρ, g, s, V, hinterp, hlive, hmem => by
      have hinterp' : JStateInterpLive (RegMapG.shiftArr ρ) rest
          (V.extend ((storeExpr arr i src).denote V))
          (runBlock s (lowerStore base (ρ src) k)) := by
        intro w hw
        match w with
        | .there w0 =>
            show (runBlock s (lowerStore base (ρ src) k)).get (ρ w0) = w0.lookup V
            rw [lowerStore_get base (ρ src) k (ρ w0)]
            exact hinterp w0 (Or.inr hw)
      have key := lowerBlock_tie_live rest (RegMapG.shiftArr ρ) g
        (runBlock s (lowerStore base (ρ src) k))
        (V.extend ((storeExpr arr i src).denote V)) hinterp' hlive hmem.2
      simpa only [lowerBlock, outReg, ArithBlock.toCom, Com.denote, runBlock_append]
        using key

/-- The fresh-allocation block tie is the instance of the liveness tie at a
    `FreshFor` allocation and the unrestricted state correspondence. -/
theorem lowerBlock_tie_of_FreshFor {Γ : Ctxt jasminDialect} (block : ArithBlock Γ)
    (ρ : RegMapG Γ) (g : Nat → String) (s : JState 64) (V : Ctxt.Valuation Γ)
    (hinterp : JStateInterpG ρ V s) (hfresh : FreshFor ρ g)
    (hmem : BlockMemOk block ρ g V s := by first | trivial | simp [BlockMemOk]) :
    (runBlock s (lowerBlock block ρ g)).get (outReg block ρ g)
      = block.toCom.denote V :=
  lowerBlock_tie_live block ρ g s V (JStateInterpLive_of_JStateInterpG hinterp)
    (LiveDisj_of_FreshFor block ρ g hfresh) hmem

/-! ## 4. The lift and the segment tie under liveness -/

/-- **The lift under liveness.** A decoded machine block that parses and
    elaborates carries the elaborated program's denotation in its output
    register, under the correspondence on the live variables and the per-step
    destination condition. The liveness form of
    `JInstrToArithBlock.liftBlock_runBlock`. -/
theorem liftBlock_runBlock_live {Γ : Ctxt jasminDialect}
    (blk : List (JInstr 64)) (ops : List RawArith)
    (nm : RegMapG Γ) (find : String → Option (Ctxt.Var Γ (.reg 64)))
    (hfind : ∀ (v : Ctxt.Var Γ (.reg 64)) (r : String), find r = some v → nm v = r)
    (out : String) (ab : ArithBlock Γ)
    (hparse : parseBlock blk = some ops) (helab : elabOps find ops out = some ab)
    (s : JState 64) (V : Ctxt.Valuation Γ)
    (hinterp : JStateInterpLive nm ab V s)
    (hlive : LiveDisj ab nm (dstStream ops))
    (hmem : BlockMemOk ab nm (dstStream ops) V s :=
      by first | trivial | simp [BlockMemOk]) :
    (runBlock s blk).get (outReg ab nm (dstStream ops)) = ab.toCom.denote V := by
  have hblk : blk = lowerBlock ab nm (dstStream ops) := by
    rw [elabOps_lowerBlock nm find hfind ops out ab helab]
    exact parseBlock_lowerRaw blk ops hparse
  rw [hblk]
  exact lowerBlock_tie_live ab nm (dstStream ops) s V hinterp hlive hmem

/-- **The segment tie under liveness.** A machine block splitting as
    `pre ++ core ++ post` whose middle segment parses and elaborates to an
    `ArithBlock` compiling to `c`: under the correspondence on the live variables
    at the state `pre` leaves, the per-step destination condition, and a `post`
    that does not write the output register, reading that register after the
    whole run gives `c.denote V`. The liveness form of
    `FramedJInstrTie.coreSegment_denote`. -/
theorem coreSegment_denote_live {Γ : Ctxt jasminDialect}
    (c : Com jasminDialect Γ (.reg 64))
    (pre core post : List (JInstr 64)) (ops : List RawArith)
    (nm : RegMapG Γ) (find : String → Option (Ctxt.Var Γ (.reg 64)))
    (hfind : ∀ (v : Ctxt.Var Γ (.reg 64)) (r : String), find r = some v → nm v = r)
    (out : String) (ab : ArithBlock Γ)
    (hparse : parseBlock core = some ops) (helab : elabOps find ops out = some ab)
    (htoCom : ab.toCom = c)
    (s : JState 64) (V : Ctxt.Valuation Γ)
    (hinterp : JStateInterpLive nm ab V (runBlock s pre))
    (hlive : LiveDisj ab nm (dstStream ops))
    (hpost : ∀ s' : JState 64,
      (runBlock s' post).get (outReg ab nm (dstStream ops))
        = s'.get (outReg ab nm (dstStream ops)))
    (hmem : BlockMemOk ab nm (dstStream ops) V (runBlock s pre) :=
      by first | trivial | simp [BlockMemOk]) :
    (runBlock s (pre ++ core ++ post)).get (outReg ab nm (dstStream ops))
      = c.denote V := by
  rw [runBlock_append, runBlock_append, hpost,
    liftBlock_runBlock_live core ops nm find hfind out ab hparse helab
      (runBlock s pre) V hinterp hlive hmem, htoCom]

/-! ## 5. The physical-ABI body of the two-operation program

`FramedJInstrTie.comBlock2_not_freshFor` records that the register map and the
destination stream of this body collide: the second recovered operation writes
`%rcx`, the register the second input arrives in. The second input is read by the
first operation and by nothing after it, so it is dead at the second operation
and the collision satisfies `LiveDisj`. -/

/-- The name resolution of the physical-ABI body and its register map invert on
    the two inputs. -/
theorem comBlock2Find_nm : ∀ (v : Ctxt.Var Δ2 (.reg 64)) (r : String),
    comBlock2Find r = some v → comBlock2Nm v = r := by
  intro v r h
  unfold comBlock2Find at h
  split at h
  · next hr => subst hr; cases h; rfl
  · split at h
    · next hr => subst hr; cases h; rfl
    · exact absurd h (by simp)

/-- The restores after the arithmetic leave `%rcx` alone. -/
theorem comBlock2Post_get_rcx (s : JState 64) :
    (runBlock s comBlock2Post).get "RCX" = s.get "RCX" := by
  simp [comBlock2Post, runBlock_cons, runBlock_nil, evalInstr, x86_MOV,
    JState.setReg, JState.get, JState.load]

/-- **The physical-ABI body satisfies the liveness condition.** Its destination
    stream collides with the register map at the second operation
    (`shipped_stream_collides`), and the variable that collision overwrites is
    read only by the first operation, so it is dead where the collision
    happens. -/
theorem comBlock2_liveDisj :
    LiveDisj block2 comBlock2Nm (dstStream comBlock2Ops) := by
  refine ⟨by decide, ?_, by decide, ?_, trivial⟩
  · intro w _
    match w with
    | .here => exact by decide
    | .there .here => exact by decide
  · intro w hw
    simp only [LiveVar] at hw
    exact absurd hw (by simp)

/-- **The liveness condition is weaker than freshness.** One body satisfies
    `LiveDisj` and not `FreshFor`. -/
theorem liveDisj_not_freshFor :
    LiveDisj block2 comBlock2Nm (dstStream comBlock2Ops)
      ∧ ¬ FreshFor comBlock2Nm (dstStream comBlock2Ops) :=
  ⟨comBlock2_liveDisj, comBlock2_not_freshFor⟩

/-- **The arithmetic segment of the physical-ABI body denotes the source
    program.** For every entry state whose registers carry the valuation on the
    live variables, running the three segments leaves `comBlock2.denote V` in
    `%rcx`. The register-reuse strengthening of
    `FramedJInstrTie.comBlock2_core_denote`, which fixes one concrete entry
    state. -/
theorem comBlock2_core_live_denote (s : JState 64) (V : Ctxt.Valuation Δ2)
    (hinterp : JStateInterpLive comBlock2Nm block2 V (runBlock s comBlock2Pre)) :
    (runBlock s (comBlock2Pre ++ comBlock2Core ++ comBlock2Post)).get "RCX"
      = comBlock2.denote V := by
  have h := coreSegment_denote_live comBlock2 comBlock2Pre comBlock2Core
    comBlock2Post comBlock2Ops comBlock2Nm comBlock2Find comBlock2Find_nm "RCX"
    block2 comBlock2Core_parse comBlock2Ops_elab comBlock2Ops_toCom s V hinterp
    comBlock2_liveDisj (fun s' => by rw [comBlock2_outReg]; exact comBlock2Post_get_rcx s')
  rwa [comBlock2_outReg] at h

end CatCrypt.Crypto.SecureCompilation.Ascent
