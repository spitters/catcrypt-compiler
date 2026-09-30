/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer
public import CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem
public import CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgree

@[expose] public section

set_option autoImplicit false

/-!
# Decoded instructions against the flag machine, one instruction at a time

`LprogBytesDecode.decodeLprog` returns a `List RInstr`, run by `RInstrSemantics.run` on a
`Machine`. This module runs it on `RInstrAddrMem.aMachine`, whose state is the
address-memory state `Ascent.AddrMem.AState` and whose step is `evalInstrA`: a memory
operand `[b + o]` or `(%b, %i, s)` addresses the bytes from the value of `b`.

The other side is the flag machine `lsemFuelMemF` over `LstateMF`: a register file keyed
by name at a width, an array carrier keyed by name, and the zero flag `zf`.

## The relation

`DecLsemCorr π L Lay frame K zfLive sa b zf` relates a machine state `sa` to the flag
machine's base state `b` and flag `zf`:

* each name `r` of the live set `L` reads at width `64` the value of the machine register
  `π r`;
* when `zfLive` holds, the machine zero flag is `zf`;
* each cell `(A, j)` of `K` is in bounds, and the eight bytes at `Lay.addr A j` hold element
  `j` of the array `A` little-endian (the cell component of `JasminLsemAddrMem.Rel`);
* the frame slot of each array holds its base address.

The layout `Lay` and its separation condition `Layout.Sep` are those of
`JasminLsemAddrMem`. The live set changes along a run: a write to a name `d` keeps the
live names whose machine register is not `π d` (`Survives`).

## Step lemmas

`DecSim I J ls js` states that from states related by `I` the flag machine's straight fold
`runStraightF ls` succeeds, with a result related by `J` to `aMachine.runBlock sa js`. It
composes (`DecSim.append`, `DecSim.weaken`), and the instances are:

* `decSim_movReg`, `decSim_movReg_elided`, `decSim_movImm`: `MOV:64` against `mov`;
* `decSim_add`, `decSim_sub`, `decSim_and`, `decSim_xor`, `decSim_or`, `decSim_imul`, the
  generic `decSim_binReg`, `decSim_addImm`, `decSim_subImm`: a three-address operation
  against the two-address machine instruction whose destination register is that of the
  first source;
* `decSim_shrImm`, `decSim_shl0`, `decSim_shl0_elided`: the count-in-mnemonic shifts
  `SHR:k:64` and `SHL:0:64`;
* `decSim_mulx`: the pair `MUL:64`, `MULXHI:64` against one `mulx`;
* `decSim_cmpImm`, `decSim_cmpReg`: the flag compare, after which the zero flag is tracked;
* `decSim_load`, `decSim_store`: `LOADIDX`/`STOREIDX` against the indexed `mov` through a
  register holding the array base, and `decSim_loadR`, `decSim_storeR` with the pointer
  reload from the frame slot in front;
* `decSim_machMov`, `decSim_machLoad`: machine instructions into a register holding no live
  name;
* `label_step`, `aMachine_step_jne`, `aMachine_step_je`, `DecLsemCorr.evalJumpMem`: labels
  and the branches on the zero flag.

`decSim_segment` turns a `DecSim` for an all-`Lopn` segment into the flag machine's run
(`lsemFuelMemF_segF`) and the machine's `Reaches` (`reaches_ops`).
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemStep

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem

/-! ## 1. The machine -/

/-- One `op` of a decoded program on the address machine `RInstrAddrMem.aMachine`. -/
theorem aMachine_step_op (prog : List RInstr) (pc : Nat) (sa : AState) (j : JInstr 64)
    (h : prog[pc]? = some (.op j)) :
    RInstrSemantics.step aMachine prog pc sa
      = some (RInstrSemantics.Next.go (pc + 1) (evalInstrA sa j)) := by
  simp [RInstrSemantics.step, h, aMachine]

/-! ## 2. The relation -/

/-- The correspondence between an address-memory machine state `sa` and the flag machine's
    base state `b` with flag `zf`. `π` sends a name of the flag machine to the machine
    register holding it, and `L` is the set of names whose value the machine register
    holds at width `64`. When `zfLive` holds the machine zero flag is `zf`. Each cell
    `(A, j)` of `K` is in bounds and the word at `Lay.addr A j` is element `j` of the array
    `A` at shape `(64, Lay.len A)`, stored little-endian. Each frame slot of an array holds
    the base address of the array. -/
structure DecLsemCorr (π : String → String) (L : String → Prop) (Lay : Layout)
    (frame : String → Option (BitVec 64)) (K : String → Nat → Prop) (zfLive : Prop)
    (sa : AState) (b : LstateM) (zf : Bool) : Prop where
  /-- A live name reads at width `64` the value of its machine register. -/
  regs : ∀ r, L r → b.reg.getW r 64 = some (sa.regs (π r))
  /-- The machine zero flag is `zf` when it is live. -/
  zfEq : zfLive → sa.flags.zf.getD false = zf
  /-- The array cells of `K` sit at their layout addresses. -/
  cells : ∀ A j, K A j → j < Lay.len A ∧ ∃ arr : Fin (Lay.len A) → BitVec 64,
    b.getArr A 64 (Lay.len A) = some arr ∧ read64 sa.mem (Lay.addr A j) = stackGet arr j
  /-- The frame slot of an array holds its base address. -/
  slots : ∀ A q, Lay.slot A = some q → ∃ a, frame q = some a ∧ read64 sa.mem a = Lay.base A

/-- The live set `L'` after a write to the name `d`: `d` itself, and names live before whose
    machine register is not the one `d` is written to. -/
def Survives (π : String → String) (L L' : String → Prop) (d : String) : Prop :=
  ∀ r, L' r → r = d ∨ (L r ∧ π r ≠ π d)

variable {π : String → String} {L L' : String → Prop} {Lay : Layout}
  {frame : String → Option (BitVec 64)} {K : String → Nat → Prop} {zl zl' : Prop}

/-- A write of `v` to the name `d` on the flag machine and to the register `π d` on the
    machine, memory unchanged, preserves the correspondence on a surviving live set. -/
theorem DecLsemCorr.write {sa : AState} {b : LstateM} {zf : Bool}
    (h : DecLsemCorr π L Lay frame K zl sa b zf) (d : String) (v : BitVec 64) (sa' : AState)
    (hregs : ∀ r, sa'.regs r = if r = π d then v else sa.regs r) (hmem : sa'.mem = sa.mem)
    (hL : Survives π L L' d) (hzf : zl' → sa'.flags.zf.getD false = zf) :
    DecLsemCorr π L' Lay frame K zl' sa' ((b.setReg d v).nextPc) zf where
  regs r hr := by
    rw [LstateM.reg_nextPc, LstateM.reg_setReg, LstateN.getW_nextPc]
    rcases hL r hr with rfl | ⟨hrL, hne⟩
    · rw [LstateN.getW_setReg_same, hregs, if_pos rfl]
    · have hrd : r ≠ d := fun h' => hne (by rw [h'])
      rw [LstateN.getW_setReg_other _ _ _ _ _ hrd, h.regs r hrL, hregs, if_neg hne]
  zfEq := hzf
  cells A j hk := by
    obtain ⟨hj, arr, ha, hr⟩ := h.cells A j hk
    exact ⟨hj, arr, by simpa using ha, by rw [hmem]; exact hr⟩
  slots A q hq := by rw [hmem]; exact h.slots A q hq

/-- A machine write of `v` to a register `D` that holds no live name, memory unchanged,
    preserves the correspondence with the flag machine state unchanged. -/
theorem DecLsemCorr.machWrite {sa : AState} {b : LstateM} {zf : Bool}
    (h : DecLsemCorr π L Lay frame K zl sa b zf) (D : String) (v : BitVec 64) (sa' : AState)
    (hregs : ∀ r, sa'.regs r = if r = D then v else sa.regs r) (hmem : sa'.mem = sa.mem)
    (hL : ∀ r, L' r → L r ∧ π r ≠ D) (hzf : zl' → sa'.flags.zf.getD false = zf) :
    DecLsemCorr π L' Lay frame K zl' sa' b zf where
  regs r hr := by
    obtain ⟨hrL, hne⟩ := hL r hr
    rw [h.regs r hrL, hregs, if_neg hne]
  zfEq := hzf
  cells A j hk := by
    obtain ⟨hj, arr, ha, hr⟩ := h.cells A j hk
    exact ⟨hj, arr, ha, by rw [hmem]; exact hr⟩
  slots A q hq := by rw [hmem]; exact h.slots A q hq

/-- The correspondence does not read the carry and overflow flags of the flag machine. -/
theorem DecLsemCorr.withALUFlags {sa : AState} {b : LstateM} {zf : Bool}
    (h : DecLsemCorr π L Lay frame K zl sa b zf) (i : LinstrRM) (s0 : LstateM) :
    DecLsemCorr π L Lay frame K zl sa (withALUFlags i s0 b) zf where
  regs r hr := by rw [withALUFlags_reg]; exact h.regs r hr
  zfEq := h.zfEq
  cells A j hk := by
    obtain ⟨hj, arr, ha, hr⟩ := h.cells A j hk
    refine ⟨hj, arr, ?_, hr⟩
    unfold LstateM.getArr
    rw [withALUFlags_larr]
    exact ha
  slots := h.slots

/-- The correspondence does not read the program counter. -/
theorem DecLsemCorr.setLpc {sa : AState} {b : LstateM} {zf : Bool}
    (h : DecLsemCorr π L Lay frame K zl sa b zf) (pc : Nat) :
    DecLsemCorr π L Lay frame K zl sa (b.setLpc pc) zf where
  regs r hr := h.regs r hr
  zfEq := h.zfEq
  cells A j hk := h.cells A j hk
  slots := h.slots

/-- The correspondence does not read the program counter. -/
theorem DecLsemCorr.nextPc {sa : AState} {b : LstateM} {zf : Bool}
    (h : DecLsemCorr π L Lay frame K zl sa b zf) :
    DecLsemCorr π L Lay frame K zl sa b.nextPc zf where
  regs r hr := by rw [LstateM.reg_nextPc, LstateN.getW_nextPc]; exact h.regs r hr
  zfEq := h.zfEq
  cells A j hk := by
    obtain ⟨hj, arr, ha, hr⟩ := h.cells A j hk
    exact ⟨hj, arr, by rw [LstateM.getArr_nextPc]; exact ha, hr⟩
  slots := h.slots

/-- A change of register map: names live after, held by `π'` in a register with the value
    of the `π` register. -/
theorem DecLsemCorr.remap {π' : String → String} {sa : AState} {b : LstateM} {zf : Bool}
    (h : DecLsemCorr π L Lay frame K zl sa b zf)
    (hL : ∀ r, L' r → L r ∧ sa.regs (π' r) = sa.regs (π r)) :
    DecLsemCorr π' L' Lay frame K zl sa b zf where
  regs r hr := by rw [(hL r hr).2]; exact h.regs r (hL r hr).1
  zfEq := h.zfEq
  cells := h.cells
  slots := h.slots

/-! ## 3. Segment simulations -/

/-- `DecSim I J ls js`: from states related by `I`, the flag machine's straight fold of
    `ls` succeeds, and its result is related by `J` to the machine's run of the block `js`. -/
def DecSim (I J : AState → LstateM → Bool → Prop) (ls : List LinstrRM)
    (js : List (JInstr 64)) : Prop :=
  ∀ sa b zf, I sa b zf → ∃ b' zf', runStraightF ls b zf = some (b', zf')
    ∧ J (aMachine.runBlock sa js) b' zf'

theorem DecSim.nil (I : AState → LstateM → Bool → Prop) : DecSim I I [] [] :=
  fun _ b zf h => ⟨b, zf, rfl, h⟩

theorem DecSim.append {I J M : AState → LstateM → Bool → Prop}
    {l₁ l₂ : List LinstrRM} {j₁ j₂ : List (JInstr 64)}
    (h₁ : DecSim I J l₁ j₁) (h₂ : DecSim J M l₂ j₂) : DecSim I M (l₁ ++ l₂) (j₁ ++ j₂) := by
  intro sa b zf h
  obtain ⟨b₁, z₁, hr₁, hJ⟩ := h₁ sa b zf h
  obtain ⟨b₂, z₂, hr₂, hM⟩ := h₂ _ b₁ z₁ hJ
  refine ⟨b₂, z₂, ?_, ?_⟩
  · rw [runStraightF_append, hr₁, Option.bind_some]; exact hr₂
  · rw [Machine.runBlock_append]; exact hM

theorem DecSim.weaken {I I' J J' : AState → LstateM → Bool → Prop}
    {ls : List LinstrRM} {js : List (JInstr 64)} (h : DecSim I J ls js)
    (hI : ∀ sa b zf, I' sa b zf → I sa b zf) (hJ : ∀ sa b zf, J sa b zf → J' sa b zf) :
    DecSim I' J' ls js := by
  intro sa b zf hi
  obtain ⟨b', z', hr, hj⟩ := h sa b zf (hI sa b zf hi)
  exact ⟨b', z', hr, hJ _ _ _ hj⟩

/-- One flag-machine instruction against one machine instruction. -/
theorem DecSim.single {I J : AState → LstateM → Bool → Prop} {i : LinstrRM} {j : JInstr 64}
    (h : ∀ sa b zf, I sa b zf →
      ∃ b' zf', fstepF i b zf = some (b', zf') ∧ J (evalInstrA sa j) b' zf') :
    DecSim I J [i] [j] := by
  intro sa b zf hi
  obtain ⟨b', z', hr, hj⟩ := h sa b zf hi
  exact ⟨b', z', by rw [runStraightF_singleton]; exact hr, hj⟩

/-- One flag-machine instruction with no machine instruction. -/
theorem DecSim.lsemOnly {I J : AState → LstateM → Bool → Prop} {i : LinstrRM}
    (h : ∀ sa b zf, I sa b zf → ∃ b' zf', fstepF i b zf = some (b', zf') ∧ J sa b' zf') :
    DecSim I J [i] [] := by
  intro sa b zf hi
  obtain ⟨b', z', hr, hj⟩ := h sa b zf hi
  exact ⟨b', z', by rw [runStraightF_singleton]; exact hr, hj⟩

/-- One machine instruction with no flag-machine instruction. -/
theorem DecSim.machOnly {I J : AState → LstateM → Bool → Prop} {j : JInstr 64}
    (h : ∀ sa b zf, I sa b zf → J (evalInstrA sa j) b zf) : DecSim I J [] [j] :=
  fun sa b zf hi => ⟨b, zf, rfl, h sa b zf hi⟩

/-! ## 4. Register moves -/

/-- The register copy `MOV:64 d, s`. -/
def movRI (d s : String) : LinstrRM :=
  (.Lopn [.reg d] (withWidthTag 64 "MOV") [.reg s], .reg none)

/-- The immediate move `MOV:64 d, #n`. -/
def movII (d : String) (n : Nat) : LinstrRM :=
  (.Lopn [.reg d] (withWidthTag 64 "MOV") [.imm n], .reg none)

theorem fstepF_movRI (d s : String) (b : LstateM) (zf : Bool) (v : BitVec 64)
    (hv : b.reg.getW s 64 = some v) :
    fstepF (movRI d s) b zf = some ((b.setReg d v).nextPc, zf) := by
  simp [fstepF, movRI, cmpArgs?, movRegArgs?,
    JasminLsemScalar.stripWidthTag_withWidthTag_MOV, readReg_of_getW hv]

theorem fstepF_movII (d : String) (n : Nat) (b : LstateM) (zf : Bool) :
    fstepF (movII d n) b zf = some ((b.setReg d (BitVec.ofNat 64 n)).nextPc, zf) := by
  simp [fstepF, movII, cmpArgs?, movRegArgs?]
  rfl

/-- **Register copy.** `MOV:64 d, s` against `mov %s, %d` on the registers of `d` and `s`. -/
theorem decSim_movReg (d s : String) (hs : L s) (hL : Survives π L L' d) :
    DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π L' Lay frame K zl)
      [movRI d s] [.mov (π d) (.reg (π s))] :=
  DecSim.single fun _ b zf h =>
    ⟨_, zf, fstepF_movRI d s b zf _ (h.regs s hs),
      h.write d _ _ (fun _ => rfl) rfl hL (fun hz => h.zfEq hz)⟩

/-- **Elided register copy.** `MOV:64 d, s` with `d` and `s` in one machine register
    needs no machine instruction. -/
theorem decSim_movReg_elided (d s : String) (hs : L s) (hds : π d = π s)
    (hL : Survives π L L' d) :
    DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π L' Lay frame K zl) [movRI d s] [] :=
  DecSim.lsemOnly fun sa b zf h =>
    ⟨_, zf, fstepF_movRI d s b zf _ (h.regs s hs),
      h.write d _ sa (fun r => by split <;> simp_all) rfl hL (fun hz => h.zfEq hz)⟩

/-- **Immediate move.** `MOV:64 d, #n` against `mov $n, %d`. -/
theorem decSim_movImm (d : String) (n : Nat) (hL : Survives π L L' d) :
    DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π L' Lay frame K zl)
      [movII d n] [.mov (π d) (.imm n)] :=
  DecSim.single fun _ b zf h =>
    ⟨_, zf, fstepF_movII d n b zf,
      h.write d _ _ (fun _ => rfl) rfl hL (fun hz => h.zfEq hz)⟩

/-! ## 5. Arithmetic and logic -/

/-- **Two-source operation.** A three-address `opn d, a, c` whose stripped mnemonic `base`
    computes `f`, against the two-address machine instruction `mk` on the register of `d`,
    which is the register of `a`, and the register of `c`. The machine zero flag is not
    tracked afterwards. -/
theorem decSim_binReg (opn base : String) (hstrip : stripWidthTag opn = base)
    (hcmp : opn ≠ withWidthTag 64 "CMP") (hmul : base ≠ "MULXHI")
    (hcarry : base ≠ "ADC" ∧ base ≠ "SBB" ∧ base ≠ "ADCX" ∧ base ≠ "ADOX")
    (f : BitVec 64 → BitVec 64 → BitVec 64)
    (hf : ∀ x y, applyOpnN 64 base [x, y] = some (f x y))
    (mk : String → JOperand → JInstr 64)
    (hmk : ∀ (sa : AState) (D S r : String),
      (evalInstrA sa (mk D (.reg S))).regs r
        = if r = D then f (sa.regs D) (sa.regs S) else sa.regs r)
    (hmkm : ∀ (sa : AState) (D S : String), (evalInstrA sa (mk D (.reg S))).mem = sa.mem)
    (d a c : String) (ha : L a) (hc : L c) (hda : π d = π a) (hL : Survives π L L' d) :
    DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π L' Lay frame K False)
      [binRegI opn d a c] [mk (π d) (.reg (π c))] := by
  refine DecSim.single fun sa b zf h => ⟨_, zf, ?_,
    (h.write d (f (sa.regs (π a)) (sa.regs (π c))) _ (fun r => by rw [hmk, hda]) (hmkm _ _ _) hL
      (fun hz => hz.elim)).withALUFlags (binRegI opn d a c) b⟩
  rw [fstepF_binRegI opn base d a c hstrip hcmp hmul hcarry b zf _ (h.regs a ha), h.regs c hc,
    Option.bind_some, hf, Option.map_some]

theorem stripWidthTag_MUL64 : stripWidthTag "MUL:64" = "MUL" := by decide +kernel

/-- `ADD:64 d, a, c` against `add %c, %d` with `d` and `a` in one register. -/
theorem decSim_add (d a c : String) (ha : L a) (hc : L c) (hda : π d = π a)
    (hL : Survives π L L' d) :
    DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π L' Lay frame K False)
      [addI d a c] [.add (π d) (.reg (π c))] :=
  decSim_binReg _ "ADD" JasminLsemMemSourceTieUncond.stripWidthTag_ADD64 (by decide +kernel)
    (by decide) (by decide) (· + ·) (fun _ _ => rfl) JInstr.add (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    d a c ha hc hda hL

/-- `SUB:64 d, a, c` against `sub %c, %d` with `d` and `a` in one register. -/
theorem decSim_sub (d a c : String) (ha : L a) (hc : L c) (hda : π d = π a)
    (hL : Survives π L L' d) :
    DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π L' Lay frame K False)
      [subI d a c] [.sub (π d) (.reg (π c))] :=
  decSim_binReg _ "SUB" JasminLsemMemSourceTieUncond.stripWidthTag_SUB64 (by decide +kernel)
    (by decide) (by decide) (· - ·) (fun _ _ => rfl) JInstr.sub (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    d a c ha hc hda hL

/-- `AND:64 d, a, c` against `and %c, %d` with `d` and `a` in one register. -/
theorem decSim_and (d a c : String) (ha : L a) (hc : L c) (hda : π d = π a)
    (hL : Survives π L L' d) :
    DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π L' Lay frame K False)
      [andI d a c] [.and_ (π d) (.reg (π c))] :=
  decSim_binReg _ "AND" stripWidthTag_AND64 (by decide +kernel)
    (by decide) (by decide) (· &&& ·) (fun _ _ => rfl) JInstr.and_ (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    d a c ha hc hda hL

/-- `XOR:64 d, a, c` against `xor %c, %d` with `d` and `a` in one register. -/
theorem decSim_xor (d a c : String) (ha : L a) (hc : L c) (hda : π d = π a)
    (hL : Survives π L L' d) :
    DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π L' Lay frame K False)
      [xorI d a c] [.xor_ (π d) (.reg (π c))] :=
  decSim_binReg _ "XOR" stripWidthTag_XOR64 (by decide +kernel)
    (by decide) (by decide) (· ^^^ ·) (fun _ _ => rfl) JInstr.xor_ (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    d a c ha hc hda hL

/-- `OR:64 d, a, c` against `or %c, %d` with `d` and `a` in one register. -/
theorem decSim_or (d a c : String) (ha : L a) (hc : L c) (hda : π d = π a)
    (hL : Survives π L L' d) :
    DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π L' Lay frame K False)
      [orI d a c] [.or_ (π d) (.reg (π c))] :=
  decSim_binReg _ "OR" stripWidthTag_OR64 (by decide +kernel)
    (by decide) (by decide) (· ||| ·) (fun _ _ => rfl) JInstr.or_ (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    d a c ha hc hda hL

/-- `MUL:64 d, a, c` against `imul %c, %d` with `d` and `a` in one register. -/
theorem decSim_imul (d a c : String) (ha : L a) (hc : L c) (hda : π d = π a)
    (hL : Survives π L L' d) :
    DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π L' Lay frame K False)
      [binRegI "MUL:64" d a c] [.imul (π d) (.reg (π c))] :=
  decSim_binReg _ "MUL" stripWidthTag_MUL64 (by decide +kernel)
    (by decide) (by decide) (· * ·) (fun _ _ => rfl) JInstr.imul (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    d a c ha hc hda hL

/-- `ADD:64 d, a, #k` against `add $k, %d` with `d` and `a` in one register. -/
theorem decSim_addImm (d a : String) (k : Nat) (ha : L a) (hda : π d = π a)
    (hL : Survives π L L' d) :
    DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π L' Lay frame K False)
      [addImmI d a k] [.add (π d) (.imm k)] :=
  DecSim.single fun sa b zf h =>
    ⟨_, zf, fstepF_addImmI d a k b zf _ (h.regs a ha),
      DecLsemCorr.withALUFlags (h.write d (sa.regs (π a) + BitVec.ofNat 64 k)
        (aMachine.runBlock sa [.add (π d) (.imm k)]) (fun r => by
          show (if r = π d then sa.regs (π d) + BitVec.ofNat 64 k else sa.regs r) = _
          rw [hda]) rfl hL (fun hz : False => hz.elim)) _ _⟩

/-- `SUB:64 d, a, #k` against `sub $k, %d` with `d` and `a` in one register. -/
theorem decSim_subImm (d a : String) (k : Nat) (ha : L a) (hda : π d = π a)
    (hL : Survives π L L' d) :
    DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π L' Lay frame K False)
      [subImmI d a k] [.sub (π d) (.imm k)] :=
  DecSim.single fun sa b zf h =>
    ⟨_, zf, fstepF_subImmI d a k b zf _ (h.regs a ha),
      DecLsemCorr.withALUFlags (h.write d (sa.regs (π a) - BitVec.ofNat 64 k)
        (aMachine.runBlock sa [.sub (π d) (.imm k)]) (fun r => by
          show (if r = π d then sa.regs (π d) - BitVec.ofNat 64 k else sa.regs r) = _
          rw [hda]) rfl hL (fun hz : False => hz.elim)) _ _⟩

/-! ## 6. Immediate shifts -/

/-- The count-in-mnemonic immediate shift `m:k:64 d, a` for `m ∈ {SHR, SHL}`. -/
def immShiftI (m d a : String) (k : Nat) : LinstrRM :=
  (.Lopn [.reg d] (withWidthTag 64 (m ++ ":" ++ toString k)) [.reg a], .reg none)

open JasminLsemShift in
theorem fstepF_shrImmI (d a : String) (k : Nat) (hk : k < 64) (b : LstateM) (zf : Bool)
    (va : BitVec 64) (hva : b.reg.getW a 64 = some va) :
    fstepF (immShiftI "SHR" d a k) b zf = some ((b.setReg d (va >>> k)).nextPc, zf) := by
  have hkn : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rw [immShiftI, JasminLsemExportTransfer.fstepF_immShiftWire "SHR" (Or.inl rfl) 64 k d a b zf,
    JasminLsemExportTransfer.lsemStepN_immShiftCount (Or.inl rfl) 64 k d a (Or.inl rfl) b.reg,
    lsemStepSh_of_not_sar _ _ (sarStruct?_of_ne (by rw [stripWidthTag_withWidthTag_SHR]; decide))]
  simp only [lsemStepN, readReg_of_getW hva, evalOperandN, stripWidthTag_withWidthTag_SHR,
    applyOpnN, Option.map_some, hkn]
  rfl

open JasminLsemShift in
theorem fstepF_shl0I (d a : String) (b : LstateM) (zf : Bool)
    (va : BitVec 64) (hva : b.reg.getW a 64 = some va) :
    fstepF (immShiftI "SHL" d a 0) b zf = some ((b.setReg d va).nextPc, zf) := by
  rw [immShiftI, JasminLsemExportTransfer.fstepF_immShiftWire "SHL" (Or.inr (Or.inl rfl)) 64 0
      d a b zf,
    JasminLsemExportTransfer.lsemStepN_immShiftCount (Or.inr (Or.inl rfl)) 64 0 d a (Or.inl rfl)
      b.reg,
    lsemStepSh_of_not_sar _ _ (sarStruct?_of_ne (by rw [stripWidthTag_withWidthTag_SHL]; decide))]
  simp only [lsemStepN, readReg_of_getW hva, evalOperandN, stripWidthTag_withWidthTag_SHL,
    applyOpnN, Option.map_some, BitVec.toNat_ofNat, Nat.zero_mod, BitVec.shiftLeft_zero]
  rfl

/-- The data word of `shr $k` for a count `0 < k < 64`. -/
theorem x86_SHR_word_imm (v : BitVec 64) (k : Nat) (hk0 : k ≠ 0) (hk : k < 64) :
    (x86_SHR v (BitVec.ofNat 64 k)).word = v >>> k := by
  have hkn : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  simp only [x86_SHR, shiftCount, hkn, Nat.mod_eq_of_lt hk, if_neg hk0, rflags_OF, wshr,
    Nat.min_eq_right hk.le]

/-- `SHR:k:64 d, a` against `shr $k, %d` with `d` and `a` in one register, `0 < k < 64`. -/
theorem decSim_shrImm (d a : String) (k : Nat) (hk0 : k ≠ 0) (hk : k < 64) (ha : L a)
    (hda : π d = π a) (hL : Survives π L L' d) :
    DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π L' Lay frame K False)
      [immShiftI "SHR" d a k] [.shr (π d) (.imm k)] :=
  DecSim.single fun sa b zf h =>
    ⟨_, zf, fstepF_shrImmI d a k hk b zf _ (h.regs a ha),
      h.write d _ _ (fun r => by
        show (if r = π d then (x86_SHR (sa.regs (π d)) (BitVec.ofNat 64 k)).word
          else sa.regs r) = _
        rw [x86_SHR_word_imm _ k hk0 hk, hda]) rfl hL (fun hz => hz.elim)⟩

/-- The count-`0` shift `SHL:0:64 d, a` against the copy `mov %a, %d`. -/
theorem decSim_shl0 (d a : String) (ha : L a) (hL : Survives π L L' d) :
    DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π L' Lay frame K zl)
      [immShiftI "SHL" d a 0] [.mov (π d) (.reg (π a))] :=
  DecSim.single fun _ b zf h =>
    ⟨_, zf, fstepF_shl0I d a b zf _ (h.regs a ha),
      h.write d _ _ (fun _ => rfl) rfl hL (fun hz => h.zfEq hz)⟩

/-- The count-`0` shift `SHL:0:64 d, a` with `d` and `a` in one register needs no machine
    instruction. -/
theorem decSim_shl0_elided (d a : String) (ha : L a) (hda : π d = π a)
    (hL : Survives π L L' d) :
    DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π L' Lay frame K zl)
      [immShiftI "SHL" d a 0] [] :=
  DecSim.lsemOnly fun sa b zf h =>
    ⟨_, zf, fstepF_shl0I d a b zf _ (h.regs a ha),
      h.write d _ sa (fun r => by split <;> simp_all) rfl hL (fun hz => h.zfEq hz)⟩

/-! ## 7. The widening multiply -/

/-- The high half `MULXHI:64 d, a, c` of the widening multiply. -/
def mulhiI (d a c : String) : LinstrRM :=
  (.Lopn [.reg d] (withWidthTag 64 "MULXHI") [.reg a, .reg c], .reg none)

theorem fstepF_mulhiI (d a c : String) (b : LstateM) (zf : Bool) (va vc : BitVec 64)
    (ha : b.reg.getW a 64 = some va) (hc : b.reg.getW c 64 = some vc) :
    fstepF (mulhiI d a c) b zf = some ((b.setReg d (mulHiW va vc)).nextPc, zf) := by
  have h1 : withWidthTag 64 "MULXHI" ≠ withWidthTag 64 "CMP" := by decide +kernel
  have hL := RunBlockLsemAgree.lsemStepMem_mulhi3 d a c b va vc ha hc
  have ha' : aluFlagOp? (mulhiI d a c) = none := by simp [aluFlagOp?, mulhiI, withWidthTag]
  have hc' : cmpArgs? (mulhiI d a c) = none := by simp [cmpArgs?, mulhiI, h1]
  have hm' : movRegArgs? (mulhiI d a c) = none := by
    simp [movRegArgs?, mulhiI, withWidthTag]
  unfold fstepF
  rw [hc', hm']
  simp only []
  rw [stepMemF_of_lsemStepMem (i := mulhiI d a c) hL, withALUFlags_of_none ha']
  rfl

/-- **Widening multiply.** The low half `MUL:64 lo, a, c` followed by the high half
    `MULXHI:64 hi, a, c` against one `mulx %c, %lo, %hi` whose implicit source is the
    register of `a`. The two machine destinations are distinct, and the low half does not
    overwrite a source of the high half. -/
theorem decSim_mulx (lo hi a c : String) (ha : L a) (hc : L c) (hloa : lo ≠ a)
    (hloc : lo ≠ c) (hHL : π hi ≠ π lo)
    (hL : ∀ r, L' r → r = hi ∨ r = lo ∨ (L r ∧ π r ≠ π lo ∧ π r ≠ π hi)) :
    DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π L' Lay frame K zl)
      [binRegI "MUL:64" lo a c, mulhiI hi a c]
      [.mulx (π hi) (π lo) (.reg (π a)) (.reg (π c))] := by
  intro sa b zf h
  have hva := h.regs a ha
  have hvc := h.regs c hc
  set va := sa.regs (π a)
  set vc := sa.regs (π c)
  have h1 : fstepF (binRegI "MUL:64" lo a c) b zf = some ((b.setReg lo (va * vc)).nextPc, zf) := by
    rw [fstepF_binRegI _ "MUL" lo a c stripWidthTag_MUL64 (by decide +kernel) (by decide)
      (by decide) b zf _ hva, hvc, Option.bind_some]
    simp only [withALUFlags_of_none (show aluFlagOp? (binRegI "MUL:64" lo a c) = none by
      simp [aluFlagOp?, binRegI, withWidthTag])]
    rfl
  set b1 := (b.setReg lo (va * vc)).nextPc
  have hva1 : b1.reg.getW a 64 = some va := by
    simp only [b1, LstateM.reg_nextPc, LstateM.reg_setReg, LstateN.getW_nextPc,
      LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hloa), hva]
  have hvc1 : b1.reg.getW c 64 = some vc := by
    simp only [b1, LstateM.reg_nextPc, LstateM.reg_setReg, LstateN.getW_nextPc,
      LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hloc), hvc]
  let sa1 : AState := { sa with regs := fun r => if r = π lo then va * vc else sa.regs r }
  have hc1 : DecLsemCorr π (fun r => r = lo ∨ (L r ∧ π r ≠ π lo)) Lay frame K zl sa1 b1 zf :=
    h.write lo (va * vc) sa1 (fun _ => rfl) rfl (fun r hr => hr) (fun hz => h.zfEq hz)
  refine ⟨(b1.setReg hi (mulHiW va vc)).nextPc, zf, ?_, ?_⟩
  · simp only [runStraightF_cons, h1, Option.bind_some,
      fstepF_mulhiI hi a c b1 zf va vc hva1 hvc1, runStraightF_nil]
  · refine hc1.write hi (mulHiW va vc) _ (fun r => ?_) rfl (fun r hr => ?_)
      (fun hz => h.zfEq hz)
    · show (if r = π hi then (x86_MULX_lo_hi va vc).2
        else if r = π lo then (x86_MULX_lo_hi va vc).1 else sa.regs r) = _
      rw [← RunBlockLsemAgree.mulLo_eq, ← RunBlockLsemAgree.mulHi_eq]
    · rcases hL r hr with rfl | rfl | ⟨hrL, hne1, hne2⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨Or.inl rfl, Ne.symm hHL⟩
      · exact Or.inr ⟨Or.inr ⟨hrL, hne1⟩, hne2⟩

/-! ## 8. The flag compare -/

/-- The flag compare `CMP:64 c, o`. -/
def cmpRI (c : String) (o : LOperand) : LinstrRM :=
  (.Lopn [.reg c] (withWidthTag 64 "CMP") [.reg c, o], .reg none)

theorem fstepF_cmpRI (c : String) (o : LOperand) (b : LstateM) (zf : Bool) (vc vo : BitVec 64)
    (hc : b.reg.getW c 64 = some vc) (ho : evalOperandN b.reg 64 o = some vo) :
    fstepF (cmpRI c o) b zf = some (b.nextPc, vc == vo) := by
  have hc' : evalOperandN b.reg 64 (.reg c) = some vc := hc
  simp [fstepF, cmpRI, cmpArgs?, hc', ho]

/-- The zero flag of a difference is the equality of the operands. -/
theorem ZF_of_word_sub (x y : BitVec 64) : ZF_of_word (x - y) = (x == y) := by
  unfold ZF_of_word
  by_cases h : x = y
  · subst h; simp
  · have h' : (x - y).toNat ≠ 0 := by
      intro h0
      apply h
      have : x - y = 0 := BitVec.eq_of_toNat_eq (by simpa using h0)
      exact sub_eq_zero.mp this
    rw [decide_eq_false h']
    exact (beq_eq_false_iff_ne.mpr h).symm

/-- A machine instruction that writes only the zero flag, against a flag-machine step that
    moves only the program counter and sets the flag. -/
theorem DecLsemCorr.flagOnly {sa : AState} {b : LstateM} {zf : Bool}
    (h : DecLsemCorr π L Lay frame K zl sa b zf) (sa' : AState) (zf' : Bool)
    (hregs : sa'.regs = sa.regs) (hmem : sa'.mem = sa.mem)
    (hzf : zl' → sa'.flags.zf.getD false = zf') :
    DecLsemCorr π L Lay frame K zl' sa' b.nextPc zf' where
  regs r hr := by rw [hregs]; exact h.nextPc.regs r hr
  zfEq := hzf
  cells A j hk := by rw [hmem]; exact h.nextPc.cells A j hk
  slots A q hq := by rw [hmem]; exact h.slots A q hq

/-- **Compare with an immediate.** `CMP:64 c, #k` against `cmp $k, %c`; the zero flag is
    tracked afterwards. -/
theorem decSim_cmpImm (c : String) (k : Nat) (hc : L c) :
    DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π L Lay frame K True)
      [cmpRI c (.imm k)] [.cmp (π c) (.imm k)] :=
  DecSim.single fun sa b zf h =>
    ⟨_, _, fstepF_cmpRI c (.imm k) b zf _ _ (h.regs c hc) rfl,
      h.flagOnly _ _ rfl rfl (fun _ => by
        show (some (ZF_of_word (sa.regs (π c) - BitVec.ofNat 64 k))).getD false = _
        rw [ZF_of_word_sub]; rfl)⟩

/-- **Compare two registers.** `CMP:64 c, r` against `cmp %r, %c`; the zero flag is
    tracked afterwards. -/
theorem decSim_cmpReg (c r : String) (hc : L c) (hr : L r) :
    DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π L Lay frame K True)
      [cmpRI c (.reg r)] [.cmp (π c) (.reg (π r))] :=
  DecSim.single fun sa b zf h =>
    ⟨_, _, fstepF_cmpRI c (.reg r) b zf _ _ (h.regs c hc) (h.regs r hr),
      h.flagOnly _ _ rfl rfl (fun _ => by
        show (some (ZF_of_word (sa.regs (π c) - sa.regs (π r)))).getD false = _
        rw [ZF_of_word_sub]; rfl)⟩

/-! ## 9. Machine-only instructions -/

/-- A machine register copy into a register that holds no live name. -/
theorem decSim_machMov (D S : String) (hL : ∀ r, L' r → L r ∧ π r ≠ D) :
    DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π L' Lay frame K zl)
      [] [.mov D (.reg S)] :=
  DecSim.machOnly fun _ _ _ h => h.machWrite D _ _ (fun _ => rfl) rfl hL (fun hz => h.zfEq hz)

/-- A machine load `mov off(%B), %D` into a register that holds no live name. -/
theorem decSim_machLoad (D B : String) (off : Int) (hL : ∀ r, L' r → L r ∧ π r ≠ D) :
    DecSim (DecLsemCorr π L Lay frame K zl) (DecLsemCorr π L' Lay frame K zl)
      [] [.loadMem D B off] :=
  DecSim.machOnly fun _ _ _ h => h.machWrite D _ _ (fun _ => rfl) rfl hL (fun hz => h.zfEq hz)

/-- The register a machine load writes holds the word at the address. -/
theorem evalInstrA_loadMem_regs (sa : AState) (D B : String) (off : Int) :
    (evalInstrA sa (.loadMem D B off)).regs D = read64 sa.mem (sa.regs B + BitVec.ofInt 64 off) := by
  show (if D = D then _ else _) = _
  rw [if_pos rfl]; rfl

/-- A machine instruction leaves a register outside its destinations unchanged. -/
theorem evalInstrA_regs_of_not_mem_dsts (sa : AState) (j : JInstr 64) (r : String)
    (h : r ∉ dsts j) : (evalInstrA sa j).regs r = sa.regs r :=
  evalInstr_regs_of_not_mem_dsts sa.view j r h

/-! ## 10. Register-indexed memory -/

/-- The address the machine's indexed access `(%B, %I, 8)` forms is the layout address of
    the element the index selects, when `B` holds the base of the array. -/
theorem addr_idx8 (Lay : Layout) (A : String) (p vi : BitVec 64) (hp : p = Lay.base A) :
    p + BitVec.ofInt 64 ((8 * vi.toNat : Nat) : Int) = Lay.addr A vi.toNat := by
  rw [hp, Layout.addr, BitVec.ofInt_natCast]

/-- **Indexed load.** `LOADIDX d, (A, idx, 8)` against `mov (%B, %idx, 8), %d`, where `B`
    holds the base address of `A` and the index selects a cell of `K`. -/
theorem decSim_load (d A idx B : String) (hidx : L idx) (hL : Survives π L L' d) :
    DecSim (fun sa b zf => DecLsemCorr π L Lay frame K zl sa b zf ∧ sa.regs B = Lay.base A
        ∧ K A (sa.regs (π idx)).toNat)
      (DecLsemCorr π L' Lay frame K zl) [loadN Lay d A idx] [.loadMemIdx (π d) B (π idx) 8] := by
  refine DecSim.single fun sa b zf ⟨h, hB, hK⟩ => ?_
  obtain ⟨_, arr, harr, hcell⟩ := h.cells A _ hK
  refine ⟨(b.setReg d (stackGet arr (sa.regs (π idx)).toNat)).nextPc, zf, ?_, ?_⟩
  · rw [fstepF_loadN]
    simp only [lsemStepMem, loadN, loadStruct?, if_true, harr, h.regs idx hidx, Option.map_some]
  · refine h.write d _ _ (fun r => ?_) rfl hL (fun hz => h.zfEq hz)
    show (if r = π d then read64 sa.mem (sa.regs B
        + BitVec.ofInt 64 ((8 * (sa.regs (π idx)).toNat : Nat) : Int)) else sa.regs r) = _
    rw [addr_idx8 Lay A _ _ hB, hcell]

/-- **Indexed store.** `STOREIDX dst, (A, idx, 8), val` against
    `mov %val, (%B, %idx, 8)`, where `B` holds the base address of `A`, `dst` and `A` name
    one region, and the index selects the cell `j` of `K`. The cells become
    `afterStore Lay K dst A j`. -/
theorem decSim_store (hsep : Lay.Sep frame) (dst A idx val B : String)
    (hbase : Lay.base dst = Lay.base A) (hlen : Lay.len dst = Lay.len A)
    (hidx : L idx) (hval : L val) (j : Nat) :
    DecSim (fun sa b zf => DecLsemCorr π L Lay frame K zl sa b zf ∧ sa.regs B = Lay.base A
        ∧ (sa.regs (π idx)).toNat = j ∧ K A j)
      (DecLsemCorr π L Lay frame (afterStore Lay K dst A j) zl)
      [storeN Lay dst A idx val] [.storeMemIdx B (π idx) 8 (.reg (π val))] := by
  have haddr : ∀ j', Lay.addr dst j' = Lay.addr A j' := fun j' => by
    unfold Layout.addr; rw [hbase]
  refine DecSim.single fun sa b zf ⟨h, hB, hj, hK⟩ => ?_
  obtain ⟨hjl, arr, harr, _⟩ := h.cells A j hK
  refine ⟨(b.setArr dst (stackSet arr j (sa.regs (π val)))).nextPc, zf, ?_, ?_⟩
  · rw [fstepF_storeN]
    simp only [lsemStepMem, storeN, storeStruct?, if_true, harr, h.regs idx hidx,
      h.regs val hval, hj, Option.map_some]
  · have hmem : (evalInstrA sa (.storeMemIdx B (π idx) 8 (.reg (π val)))).mem
        = write64 sa.mem (Lay.addr A j) (sa.regs (π val)) := by
      show write64 sa.mem (sa.regs B
        + BitVec.ofInt 64 ((8 * (sa.regs (π idx)).toNat : Nat) : Int)) (sa.regs (π val)) = _
      rw [addr_idx8 Lay A _ _ hB, hj]
    have hdisj : ∀ C k, K C k → Lay.addr C k ≠ Lay.addr A j →
        Disjoint8 (Lay.addr A j) (Lay.addr C k) := fun C k hCk hne => by
      rcases hsep.cells A j C k hjl (h.cells C k hCk).1 with h' | h'
      · exact absurd h'.symm hne
      · exact h'
    refine ⟨fun r hr => ?_, fun hz => h.zfEq hz, fun A' j' hk => ?_, fun C q hq => ?_⟩
    · rw [LstateM.reg_nextPc, LstateM.reg_setArr, LstateN.getW_nextPc]
      exact h.regs r hr
    · rw [hmem]
      show j' < Lay.len A' ∧ ∃ arr' : Fin (Lay.len A') → BitVec 64,
        ((b.setArr dst (stackSet arr j (sa.regs (π val)))).nextPc).getArr A' 64 (Lay.len A')
          = some arr'
        ∧ read64 (write64 sa.mem (Lay.addr A j) (sa.regs (π val))) (Lay.addr A' j')
          = stackGet arr' j'
      rcases hk with ⟨rfl, hk⟩ | ⟨hA, hk, hne⟩
      · rw [haddr, hlen]
        rcases hk with rfl | ⟨hk, hne⟩
        · refine ⟨hjl, stackSet arr j' (sa.regs (π val)), by simp, ?_⟩
          rw [read64_write64_same, stackGet_stackSet_same _ _ _ hjl]
        · obtain ⟨hj', arr', ha', hr'⟩ := h.cells A j' hk
          rw [harr] at ha'
          obtain rfl := Option.some.inj ha'
          refine ⟨hj', stackSet arr j (sa.regs (π val)), by simp, ?_⟩
          rw [read64_write64_of_disjoint _ _ _ _ (hdisj A j' hk hne), hr',
            stackGet_stackSet_ne _ _ _ _ hjl hj']
          rintro rfl
          exact hne rfl
      · obtain ⟨hj', arr', ha', hr'⟩ := h.cells A' j' hk
        rw [read64_write64_of_disjoint _ _ _ _ (hdisj A' j' hk hne)]
        exact ⟨hj', arr', by simpa [hA] using ha', hr'⟩
    · rw [hmem]
      obtain ⟨aC, hqC, hpC⟩ := h.slots C q hq
      refine ⟨aC, hqC, ?_⟩
      rw [read64_write64_of_disjoint _ _ _ _ (hsep.slots A j C q aC hjl hq hqC)]
      exact hpC

/-- The pointer reload `mov off(%SP), %S` from the frame slot `q` of the array `A` leaves the
    base address of `A` in `S`, and changes no register other than `S`. -/
theorem reload_regs {sa : AState} {b : LstateM} {zf : Bool}
    (h : DecLsemCorr π L Lay frame K zl sa b zf) (A S SP q : String) (off : Int)
    (hq : Lay.slot A = some q) (hf : frame q = some (sa.regs SP + BitVec.ofInt 64 off)) :
    (evalInstrA sa (.loadMem S SP off)).regs S = Lay.base A
      ∧ ∀ r, r ≠ S → (evalInstrA sa (.loadMem S SP off)).regs r = sa.regs r := by
  obtain ⟨a, hfa, hpa⟩ := h.slots A q hq
  rw [hf] at hfa
  obtain rfl := Option.some.inj hfa
  refine ⟨by rw [evalInstrA_loadMem_regs]; exact hpa, fun r hr => ?_⟩
  show (if r = S then _ else _) = _
  rw [if_neg hr]
  rfl

/-- **Indexed load through a reloaded pointer.** `LOADIDX d, (A, idx, 8)` against the reload
    of the pointer of `A` from its frame slot into a scratch register `S` that holds no live
    name, followed by `mov (%S, %idx, 8), %d`. -/
theorem decSim_loadR (d A idx S SP q : String) (off : Int) (hq : Lay.slot A = some q)
    (hidx : L idx) (hS : ∀ r, L r → π r ≠ S) (hL : Survives π L L' d) :
    DecSim (fun sa b zf => DecLsemCorr π L Lay frame K zl sa b zf
        ∧ frame q = some (sa.regs SP + BitVec.ofInt 64 off) ∧ K A (sa.regs (π idx)).toNat)
      (DecLsemCorr π L' Lay frame K zl) [loadN Lay d A idx]
      [.loadMem S SP off, .loadMemIdx (π d) S (π idx) 8] := by
  intro sa b zf ⟨h, hf, hK⟩
  obtain ⟨hS1, hfr⟩ := reload_regs h A S SP q off hq hf
  have hc1 := h.machWrite (L' := L) (zl' := zl) S _ (evalInstrA sa (.loadMem S SP off))
    (fun _ => rfl) rfl (fun r hr => ⟨hr, hS r hr⟩) (fun hz => h.zfEq hz)
  have hK1 : K A ((evalInstrA sa (.loadMem S SP off)).regs (π idx)).toNat := by
    rw [hfr _ (hS idx hidx)]; exact hK
  exact decSim_load d A idx S hidx hL _ b zf ⟨hc1, hS1, hK1⟩

/-- **Indexed store through a reloaded pointer.** `STOREIDX dst, (A, idx, 8), val` against
    the reload of the pointer of `A` from its frame slot into a scratch register `S` that
    holds no live name, followed by `mov %val, (%S, %idx, 8)`. -/
theorem decSim_storeR (hsep : Lay.Sep frame) (dst A idx val S SP q : String) (off : Int)
    (hq : Lay.slot A = some q) (hbase : Lay.base dst = Lay.base A)
    (hlen : Lay.len dst = Lay.len A) (hidx : L idx) (hval : L val) (hS : ∀ r, L r → π r ≠ S)
    (j : Nat) :
    DecSim (fun sa b zf => DecLsemCorr π L Lay frame K zl sa b zf
        ∧ frame q = some (sa.regs SP + BitVec.ofInt 64 off) ∧ (sa.regs (π idx)).toNat = j
        ∧ K A j)
      (DecLsemCorr π L Lay frame (afterStore Lay K dst A j) zl) [storeN Lay dst A idx val]
      [.loadMem S SP off, .storeMemIdx S (π idx) 8 (.reg (π val))] := by
  intro sa b zf ⟨h, hf, hj, hK⟩
  obtain ⟨hS1, hfr⟩ := reload_regs h A S SP q off hq hf
  have hc1 := h.machWrite (L' := L) (zl' := zl) S _ (evalInstrA sa (.loadMem S SP off))
    (fun _ => rfl) rfl (fun r hr => ⟨hr, hS r hr⟩) (fun hz => h.zfEq hz)
  have hj1 : ((evalInstrA sa (.loadMem S SP off)).regs (π idx)).toNat = j := by
    rw [hfr _ (hS idx hidx)]; exact hj
  exact decSim_store hsep dst A idx val S hbase hlen hidx hval j _ b zf ⟨hc1, hS1, hj1, hK⟩

/-! ## 11. Labels and branches -/

/-- A resolved jump moves only the program counter, so the correspondence holds after it. -/
theorem DecLsemCorr.evalJumpMem {sa : AState} {zf : Bool} {P : LprogM} {lbl : LLabel}
    {p p' : LstatePM} (h : DecLsemCorr π L Lay frame K zl sa p.base zf)
    (hj : JasminLsemMemLoop.evalJumpMem P lbl p = some p') :
    DecLsemCorr π L Lay frame K zl sa p'.base zf := by
  unfold JasminLsemMemLoop.evalJumpMem at hj
  split at hj
  · obtain rfl := Option.some.inj hj
    exact h.setLpc _
  · exact absurd hj (by simp)

/-- A label moves the flag machine's program counter and has no machine instruction; the
    correspondence holds after it. -/
theorem label_step (P : LprogM) (lk : LabelKind) (lbl : LLabel) (tag : MemTag) (t : LstateMF)
    (sa : AState) (h : DecLsemCorr π L Lay frame K zl sa t.prog.base t.zf) :
    ∃ t', evalInstrPMemF P (.Llabel lk lbl, tag) t = some t'
      ∧ DecLsemCorr π L Lay frame K zl sa t'.prog.base t'.zf :=
  ⟨_, evalInstrPMemF_label P lk lbl tag t, h.nextPc⟩

/-- **`jne`.** Under a tracked zero flag, the machine's `jcc` with nibble `5` falls through
    when `zf` holds and goes to its target otherwise, as the flag machine's `Lcond NZ`
    (`evalInstrPMemF_jne`) does. -/
theorem aMachine_step_jne (prog : List RInstr) (pc tgt : Nat) (sa : AState) (b : LstateM)
    (zf : Bool) (h : DecLsemCorr π L Lay frame K zl sa b zf) (hz : zl)
    (hj : prog[pc]? = some (.jcc 5 tgt)) :
    RInstrSemantics.step aMachine prog pc sa
      = some (RInstrSemantics.Next.go (if zf then pc + 1 else tgt) sa) := by
  have hf : (aMachine.view sa).flagB (·.zf) = zf := h.zfEq hz
  simp only [RInstrSemantics.step, hj, condtOfNibble_five, Option.map_some, condB_ne, hf]
  cases zf <;> rfl

/-- **`je`.** Under a tracked zero flag, the machine's `jcc` with nibble `4` goes to its
    target when `zf` holds and falls through otherwise, as the flag machine's `Lcond Z`
    (`evalInstrPMemF_je`) does. -/
theorem aMachine_step_je (prog : List RInstr) (pc tgt : Nat) (sa : AState) (b : LstateM)
    (zf : Bool) (h : DecLsemCorr π L Lay frame K zl sa b zf) (hz : zl)
    (hj : prog[pc]? = some (.jcc 4 tgt)) :
    RInstrSemantics.step aMachine prog pc sa
      = some (RInstrSemantics.Next.go (if zf then tgt else pc + 1) sa) := by
  have hf : (aMachine.view sa).flagB (·.zf) = zf := h.zfEq hz
  simp only [RInstrSemantics.step, hj, condtOfNibble_four, Option.map_some, condB_e, hf]
  cases zf <;> rfl

/-! ## 12. Straight segments -/

/-- **Straight segment.** Let `ls` be an all-`Lopn` segment at the program counter of `b`
    in `P`, and `js` a machine block at index `pre.length` of a decoded program, with
    `DecSim I J ls js`. From states related by `I`, the flag machine runs `ls` in
    `ls.length` steps, the machine reaches the index after `js` in `aMachine.runBlock sa js`,
    and the two results are related by `J`. -/
theorem decSim_segment {I J : AState → LstateM → Bool → Prop} {ls : List LinstrRM}
    {js : List (JInstr 64)} (hs : DecSim I J ls js) (hlopn : ∀ i ∈ ls, IsLopn i)
    (P : LprogM) (fn : String) (hfn : fn = P.lfn) (b : LstateM) (zf : Bool)
    (hpos : ∀ k, k < ls.length → P.body[b.lpc + k]? = ls[k]?)
    (pre rest : List RInstr) (sa : AState) (h : I sa b zf) :
    ∃ b' zf', (∀ f, lsemFuelMemF P (ls.length + f) { prog := { base := b, lfn := fn }, zf := zf }
        = lsemFuelMemF P f { prog := { base := b', lfn := fn }, zf := zf' })
      ∧ Reaches aMachine (pre ++ js.map .op ++ rest) pre.length sa (pre.length + js.length)
          (aMachine.runBlock sa js)
      ∧ J (aMachine.runBlock sa js) b' zf' := by
  obtain ⟨b', zf', hr, hJ⟩ := hs sa b zf h
  refine ⟨b', zf', fun f => ?_, reaches_ops aMachine pre js rest sa, hJ⟩
  rw [lsemFuelMemF_segF P fn hfn ls b zf f hlopn hpos, hr, Option.bind_some]

end CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemStep
