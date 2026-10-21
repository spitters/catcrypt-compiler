/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeak

@[expose] public section

set_option autoImplicit false

/-!
# The leakage of the address machine and of the image simulation

The address machine `JasminLsemAddrRun.runA` runs a printed body over a register file and a
byte memory. Its leakage, in the events `CTLeak`, is the byte address of each memory access
and the decision of each branch:

* `instrLeakA frame i sa`: for each memory operand that `fstepA frame` reads or writes, the
  event `evA a` of its resolved byte address `a` (an indexed access at `base + sc · idx`, a
  frame word at its frame address, a cell `[B + off]` at the address in `B` plus `off`);
* `stepLeakA frame c sa zf`: `instrLeakA` at an `Lopn`, the branch event `zf == pol` at a
  conditional on a zero-flag condition code of polarity `pol`, nothing otherwise;
* `runALeak frame c fuel sa zf`: the run `runA` with the events of each step in execution
  order.

The event `evA a` is `addr "" a`, the form in which `DecodedCT.resolveEv` records a resolved
memory access of the decoded bytes.

## The map of the image simulation

`ImageAddrSim.image_addr_sim` matches a run of the name-keyed image `virtImg slotArr body`
from a state `s` by a run of the address machine on `body` from a state `sa` related by
`ImgRel frame slotArr base body`. The events of the two runs correspond position by
position. At instruction `x` of the body with image instruction `i`, `posT frame base x i`
maps the events `e` of the image instruction:

* an indexed load or store: each `addr A o` of `e` to `evA (base A + o)` (`phiEv base`);
* a branch: `e`;
* a move from or to a frame word `q`, or a compare against it: the frame address of `q`,
  independent of `e` and of the state;
* an array zeroing of `n` words and a constant-index store at index `j`, whose image
  instruction names the array `A`: the words `base A + 8 i`, `i < n`, and the word
  `base A + 8 j`, independent of `e` and of the state;
* any other instruction: nothing.

`physT frame base slotArr body xs k ℓ` applies `posT` along the instructions `xs` from
position `k`, consuming from the virtual trace `ℓ` the number of events `evCountF` of each
image instruction, a function of the instruction alone. It depends only on the frame, the
array bases `base`, the slot map and the body.

## Main results

* `runALeak_fst`, `runALeak_det`: the traced run projects to `runA` and is deterministic.
* `instrLeakA_ldm`, `instrLeakA_stm`, `instrLeakA_ldx`, `instrLeakA_stx`,
  `instrLeakA_slotLoad`, `instrLeakA_slotStore`, `instrLeakA_slotCmp`, `instrLeakA_regOk`:
  the events of each kind of instruction on the address machine.
* `instrLeakF_length`: the virtual events of an instruction are `evCountF` many.
* `step_leak`: from related states, the events of a step of the address machine are `posT`
  of the events of the image instruction.
* `image_addr_leak`: for a body without a conditional branch, every halting checked run of
  the image from a related state is matched by a halting run of the address machine whose
  trace is `physT` of the trace of the image.
* `image_addr_ct`: constant time of the image (`MemFCT`) gives constant time of the address
  machine on the body, between address states related to public-equal image states at one
  program counter, at one frame and at one map `base` of array bases.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeakPhys

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeak
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV (findInstrMem_single)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (fstepA_lpc)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG (evalInstrPMemF_next
  NextPc)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak ConstantTimeRel)

/-! ## 1. The leakage of the address machine -/

/-- The event of a memory access at the byte address `a`. -/
def evA (a : BitVec 64) : CTLeak := .addr "" (a.toNat : Int)

/-- The events of the zeroing of `n` words from the address `p`: the words at `p + 8 i`,
    `i < n`, in order. -/
def zeroEvs (p : BitVec 64) (n : Nat) : List CTLeak :=
  (List.range n).map fun i => evA (p + BitVec.ofNat 64 (8 * i))

/-- **The events of an instruction on the address machine** at `sa`: the event of the byte
    address of each memory word `fstepA frame` reads or writes, sources before the
    destination. An indexed access reads or writes `base + sc · idx`, with the index the
    value `idxVal` of the index register (its 64-bit word when the access steps); a move
    from or to a frame slot, a compare against one and an immediate move into one access
    the slot's address; a cell access `[B + off]` (`cellA?`, a 64-bit move into or out of a
    cell among them) accesses the address in `B` plus `off`, and
    the address `LEA:64 d, mem.B.off` of a cell accesses no memory; a
    carry-chain instruction accesses its frame-slot carry-in, its frame-slot word sources and
    its frame-slot destination; a select accesses its frame-slot values and its frame-slot
    destination, whatever the condition. An array zeroing `ZEROARR [], [B, #n', #w']` at the
    tag `.zero w n` writes the `n` words from the address in `B` (`zeroEvs`); a
    constant-index store `STOREIMM d, [B, V, #k]` at the tag `.storeImm w n` writes the word
    `storeImmAddr?` gives from the address in `B`. Every other instruction emits nothing. -/
def instrLeakA (frame : String → Option (BitVec 64)) (i : LinstrRM) (sa : LstateA) :
    List CTLeak :=
  match i.snd with
  | .load _ _ =>
      match loadIdxA? i.fst with
      | some (_, base, idx, sc) =>
          match sa.reg.getW base 64 with
          | some p => [evA (p + BitVec.ofNat 64 (sc * idxVal sa.reg idx))]
          | none => []
      | none => []
  | .store _ _ =>
      match storeIdxA? i.fst with
      | some (base, idx, sc, _) =>
          match sa.reg.getW base 64 with
          | some p => [evA (p + BitVec.ofNat 64 (sc * idxVal sa.reg idx))]
          | none => []
      | none => []
  | .reg _ =>
      match slotMov? i.fst with
      | some (dst, src) =>
          match frame src, frame dst with
          | some a, _ => [evA a]
          | none, some a => [evA a]
          | none, none => []
      | none =>
          match slotCmp? i.fst with
          | some (_, _, q) =>
              match frame q with
              | some a => [evA a]
              | none => []
          | none =>
              match cellA? i.fst with
              | some (.ld _ b off) =>
                  match sa.reg.getW b 64 with
                  | some p => [evA (p + BitVec.ofNat 64 off)]
                  | none => []
              | some (.st b off _) =>
                  match sa.reg.getW b 64 with
                  | some p => [evA (p + BitVec.ofNat 64 off)]
                  | none => []
              | some (.lea _ _ _) => []
              | none =>
                  match slotCarry? frame i.fst with
                  | some (_, d, a, s, c) =>
                      (frame c).toList.map evA ++ (frame a).toList.map evA
                        ++ (frame s).toList.map evA ++ (frame d).toList.map evA
                  | none =>
                      match slotImm? frame i.fst with
                      | some (a, _) => [evA a]
                      | none =>
                          match slotCmov? frame i.fst with
                          | some (d, _, a, b) =>
                              (frame a).toList.map evA ++ (frame b).toList.map evA
                                ++ (frame d).toList.map evA
                          | none => []
  | .zero _ n =>
      match zeroArrA? i.fst with
      | some b =>
          match sa.reg.getW b 64 with
          | some p => zeroEvs p n
          | none => []
      | none => []
  | .storeImm _ n =>
      match storeImmStruct? i.fst with
      | some (_, b, _, k) =>
          match sa.reg.getW b 64 with
          | some p => (storeImmAddr? p n k).toList.map evA
          | none => []
      | none => []
  | _ => []

/-- **The events of a step of the address machine** on the body `c`: `instrLeakA` at an
    `Lopn`, the decision `zf == pol` at a conditional on a condition code of polarity `pol`,
    nothing otherwise. -/
def stepLeakA (frame : String → Option (BitVec 64)) (c : Lcmd) (s : LstateA) (zf : Bool) :
    List CTLeak :=
  match c[s.reg.lpc]? with
  | some ⟨_, .Lopn ds o ss⟩ => instrLeakA frame (normA (.Lopn ds o ss), tagA (.Lopn ds o ss)) s
  | some ⟨_, .Lcond (.reg cc) _⟩ =>
      match condPol cc with
      | some pol => [.branch (zf == pol)]
      | none => []
  | _ => []

/-- **The address machine with its leakage trace**: the recursion of `runA`, each step
    prepending the events `stepLeakA` of the state it runs from. -/
def runALeak (frame : String → Option (BitVec 64)) (c : Lcmd) :
    Nat → LstateA → Bool → Option ((LstateA × Bool) × List CTLeak)
  | 0, s, zf => if haltedA c s then some ((s, zf), []) else none
  | fuel + 1, s, zf =>
      if haltedA c s then some ((s, zf), [])
      else (stepA frame c s zf).bind fun bz =>
        (runALeak frame c fuel bz.1 bz.2).map fun r => (r.1, stepLeakA frame c s zf ++ r.2)

theorem runALeak_halt (frame : String → Option (BitVec 64)) (c : Lcmd) (fuel : Nat)
    (s : LstateA) (zf : Bool) (h : haltedA c s = true) :
    runALeak frame c fuel s zf = some ((s, zf), []) := by
  cases fuel <;> simp [runALeak, h]

theorem runALeak_step (frame : String → Option (BitVec 64)) (c : Lcmd) (fuel : Nat)
    (s : LstateA) (zf : Bool) (h : haltedA c s = false) :
    runALeak frame c (fuel + 1) s zf
      = (stepA frame c s zf).bind fun bz =>
          (runALeak frame c fuel bz.1 bz.2).map fun r => (r.1, stepLeakA frame c s zf ++ r.2) := by
  simp [runALeak, h]

/-- The state component of the traced run is `runA`. -/
theorem runALeak_fst (frame : String → Option (BitVec 64)) (c : Lcmd) :
    ∀ (fuel : Nat) (s : LstateA) (zf : Bool),
      (runALeak frame c fuel s zf).map Prod.fst = runA frame c fuel s zf := by
  intro fuel
  induction fuel with
  | zero =>
      intro s zf
      cases hh : haltedA c s <;> simp [runALeak, runA, hh]
  | succ n ih =>
      intro s zf
      cases hh : haltedA c s
      · rw [runALeak_step frame c n s zf hh, runA_step frame c n s zf hh]
        cases stepA frame c s zf with
        | none => rfl
        | some bz =>
            simp only [Option.bind_some]
            rw [← ih bz.1 bz.2, Option.map_map]
            rfl
      · rw [runALeak_halt frame c _ s zf hh, runA_halt frame c _ s zf hh]
        rfl

/-- **Determinism of the traced run**: two terminating traced runs from one state, at any
    fuels, end in one state with one trace. -/
theorem runALeak_det (frame : String → Option (BitVec 64)) (c : Lcmd) :
    ∀ (k k' : Nat) (s : LstateA) (zf : Bool) (r r' : (LstateA × Bool) × List CTLeak),
      runALeak frame c k s zf = some r → runALeak frame c k' s zf = some r' → r = r' := by
  intro k
  induction k with
  | zero =>
      intro k' s zf r r' h h'
      cases hh : haltedA c s
      · simp [runALeak, hh] at h
      · rw [runALeak_halt _ _ _ _ _ hh] at h h'
        exact (Option.some.inj h).symm.trans (Option.some.inj h')
  | succ k ih =>
      intro k' s zf r r' h h'
      cases hh : haltedA c s
      · cases k' with
        | zero => simp [runALeak, hh] at h'
        | succ k' =>
            rw [runALeak_step _ _ _ _ _ hh] at h h'
            cases hs : stepA frame c s zf with
            | none => rw [hs] at h; cases h
            | some bz =>
                rw [hs, Option.bind_some] at h h'
                obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
                obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp h'
                rw [ih k' _ _ q q' hq hq']
      · rw [runALeak_halt _ _ _ _ _ hh] at h h'
        exact (Option.some.inj h).symm.trans (Option.some.inj h')

/-- A terminating run of the address machine on `c` from the state and zero flag `a`, with
    trace `ℓ`. -/
def ARun (frame : String → Option (BitVec 64)) (c : Lcmd) (a : LstateA × Bool)
    (ℓ : List CTLeak) : Prop :=
  ∃ fuel r, runALeak frame c fuel a.1 a.2 = some (r, ℓ)

/-! ## 2. The events of each kind of instruction -/

/-- The cell load `LOAD:64 D, n`, `n` the cell `[B + off]`, accesses the address in `B` plus
    `off`. -/
theorem instrLeakA_ldm (frame : String → Option (BitVec 64)) {D n B : String} {off : Nat}
    (hn : cellParts? n = some (B, off)) {sa : LstateA} {p : BitVec 64}
    (hB : sa.reg.getW B 64 = some p) :
    instrLeakA frame (.Lopn [.reg D] "LOAD:64" [.reg n], .reg none) sa
      = [evA (p + BitVec.ofNat 64 off)] := by
  simp [instrLeakA, slotMov?, slotCmp?, cellA?, hn, hB]

/-- The cell store `STORE:64 n, S`, `n` the cell `[B + off]`, accesses the address in `B`
    plus `off`. -/
theorem instrLeakA_stm (frame : String → Option (BitVec 64)) {n S B : String} {off : Nat}
    (hn : cellParts? n = some (B, off)) {sa : LstateA} {p : BitVec 64}
    (hB : sa.reg.getW B 64 = some p) :
    instrLeakA frame (.Lopn [.reg n] "STORE:64" [.reg S], .reg none) sa
      = [evA (p + BitVec.ofNat 64 off)] := by
  simp [instrLeakA, slotMov?, slotCmp?, cellA?, hn, hB]

/-- The move `MOV:64 n, S` into the cell `n = [B + off]` accesses the address in `B` plus
    `off`. -/
theorem instrLeakA_stv (frame : String → Option (BitVec 64)) {n S B : String} {off : Nat}
    (hn : cellParts? n = some (B, off)) {sa : LstateA} {p : BitVec 64}
    (hB : sa.reg.getW B 64 = some p) :
    instrLeakA frame (.Lopn [.reg n] "MOV:64" [.reg S], .reg none) sa
      = [evA (p + BitVec.ofNat 64 off)] := by
  simp [instrLeakA, slotMov?, slotCmp?, cellA?, hn, hB]

/-- The address `LEA:64 D, n` of a cell `n` accesses no memory. -/
theorem instrLeakA_lea (frame : String → Option (BitVec 64)) {D n B : String} {off : Nat}
    (hn : cellParts? n = some (B, off)) (sa : LstateA) :
    instrLeakA frame (.Lopn [.reg D] "LEA:64" [.reg n], .reg none) sa = [] := by
  simp [instrLeakA, slotMov?, slotCmp?, cellA?, hn]

/-- The indexed load `LOADIDX d, (b, idx, sc)` accesses `b + sc · idx`. -/
theorem instrLeakA_ldx (frame : String → Option (BitVec 64)) (d b idx : String) (sc : Nat)
    (w n : Nat) {sa : LstateA} {p vi : BitVec 64} (hb : sa.reg.getW b 64 = some p)
    (hi : sa.reg.getW idx 64 = some vi) :
    instrLeakA frame (.Lopn [.reg d] "LOADIDX" [.arrIdx b idx sc], .load w n) sa
      = [evA (p + BitVec.ofNat 64 (sc * vi.toNat))] := by
  simp [instrLeakA, loadIdxA?, hb, idxVal_of_getW hi]

/-- The indexed store `STOREIDX _, (b, idx, sc), v` accesses `b + sc · idx`. -/
theorem instrLeakA_stx (frame : String → Option (BitVec 64)) (d b idx v : String) (sc : Nat)
    (w n : Nat) {sa : LstateA} {p vi : BitVec 64} (hb : sa.reg.getW b 64 = some p)
    (hi : sa.reg.getW idx 64 = some vi) :
    instrLeakA frame (.Lopn [.reg d] "STOREIDX" [.arrIdx b idx sc, .reg v], .store w n) sa
      = [evA (p + BitVec.ofNat 64 (sc * vi.toNat))] := by
  simp [instrLeakA, storeIdxA?, hb, idxVal_of_getW hi]

/-- A move from the frame word `q` accesses the frame address of `q`. -/
theorem instrLeakA_slotLoad (frame : String → Option (BitVec 64)) {x : LinstrR} {d q : String}
    (h : slotMov? x = some (d, q)) {a : BitVec 64} (ha : frame q = some a) (sa : LstateA) :
    instrLeakA frame (x, .reg none) sa = [evA a] := by
  simp [instrLeakA, h, ha]

/-- A move of a register into the frame word `q` accesses the frame address of `q`. -/
theorem instrLeakA_slotStore (frame : String → Option (BitVec 64)) {x : LinstrR}
    {q S : String} (h : slotMov? x = some (q, S)) (hS : frame S = none) {a : BitVec 64}
    (ha : frame q = some a) (sa : LstateA) :
    instrLeakA frame (x, .reg none) sa = [evA a] := by
  simp [instrLeakA, h, ha, hS]

/-- A compare against the frame word `q` accesses the frame address of `q`. -/
theorem instrLeakA_slotCmp (frame : String → Option (BitVec 64)) {x : LinstrR}
    {d y q : String} (h : slotCmp? x = some (d, y, q)) {a : BitVec 64} (ha : frame q = some a)
    (sa : LstateA) :
    instrLeakA frame (x, .reg none) sa = [evA a] := by
  have hm : slotMov? x = none := by rw [slotCmp?_eq h]; rfl
  simp [instrLeakA, hm, h, ha]

/-- A register instruction passing `regOkB` accesses no memory. -/
theorem instrLeakA_regOk {frame : String → Option (BitVec 64)} {x : LinstrR}
    (h : regOkB frame x = true) (tag : Option Nat) (sa : LstateA) :
    instrLeakA frame (x, .reg tag) sa = [] := by
  have hsi := slotImm?_none_of_regOkB h
  have hsv := slotCmov?_none_of_regOkB h
  simp only [regOkB, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
  obtain ⟨⟨⟨⟨hcell, hcar⟩, hmov⟩, hcmp⟩, -⟩ := h
  cases hm : slotMov? x with
  | some p =>
      obtain ⟨d, q⟩ := p
      rw [hm] at hmov
      simp only [Option.all_some, Bool.and_eq_true, Option.isNone_iff_eq_none] at hmov
      simp [instrLeakA, hm, hmov.1, hmov.2]
  | none =>
      cases hc : slotCmp? x with
      | some p =>
          obtain ⟨d, y, q⟩ := p
          rw [hc] at hcmp
          simp only [Option.all_some, Option.isNone_iff_eq_none] at hcmp
          simp [instrLeakA, hm, hc, hcmp]
      | none => simp [instrLeakA, hm, hc, hcell, hcar, hsi, hsv]

/-! ## 3. The map of the image simulation -/

/-- The physical event of a virtual event at the array bases `base`: the address event
    `addr A o` of the array `A` at offset `o` is the byte address `base A + o`; every other
    event is kept. -/
def phiEv (base : String → BitVec 64) : CTLeak → CTLeak
  | .addr A o => evA (base A + BitVec.ofNat 64 o.toNat)
  | e => e

/-- **The physical events at an instruction** `x` of the body, with image instruction `i`,
    from the events `e` of the image: `phiEv base` of `e` at an indexed access, `e` at a
    branch, the frame address of the frame word at a frame-word move or compare, the `n`
    words from `base A` at an array zeroing of `n` words and the word `j` from `base A` at a
    constant-index store at index `j`, `A` the array the image instruction names, nothing
    otherwise. -/
def posT (frame : String → Option (BitVec 64)) (base : String → BitVec 64) (x : LinstrR)
    (i : LinstrRM) (e : List CTLeak) : List CTLeak :=
  match icase frame x with
  | .ldx _ _ _ => e.map (phiEv base)
  | .stx _ _ _ _ => e.map (phiEv base)
  | .cond _ _ => e
  | .sload _ q => (frame q).toList.map evA
  | .sstore q _ => (frame q).toList.map evA
  | .scmp _ _ q => (frame q).toList.map evA
  | .zarr _ n _ =>
      match i.fst with
      | .Lopn [.reg A] _ _ => zeroEvs (base A) n
      | _ => []
  | .simm _ _ _ j =>
      match i.fst with
      | .Lopn [.reg A] _ _ => [evA (base A + BitVec.ofNat 64 (8 * j))]
      | _ => []
  | _ => []

/-- The operand is an array operand. -/
def isArrOp : LOperand → Bool
  | .arr _ _ => true
  | .arrIdx _ _ _ => true
  | _ => false

/-- The number of events `instrLeakF` emits at an instruction: one at a conditional, the
    number of array operands at an `Lopn` other than a load-effective-address, none
    otherwise. -/
def evCountF (i : LinstrRM) : Nat :=
  match flagCondCC? i with
  | some _ => 1
  | none =>
      match i.fst with
      | .Lopn ds o ss => if stripWidthTag o = "LEA" then 0 else (ds ++ ss).countP isArrOp
      | .Lcond _ _ => 1
      | _ => 0

theorem opLeakF_length (r : LstateN) (o : LOperand) :
    (opLeakF r o).length = if isArrOp o then 1 else 0 := by
  cases o <;> rfl

theorem flatMap_opLeakF_length (r : LstateN) :
    ∀ l : List LOperand, (l.flatMap (opLeakF r)).length = l.countP isArrOp
  | [] => rfl
  | o :: l => by
      rw [List.flatMap_cons, List.length_append, flatMap_opLeakF_length r l, List.countP_cons,
        opLeakF_length]
      omega

/-- The virtual events of an instruction are `evCountF` many, at every state. -/
theorem instrLeakF_length (i : LinstrRM) (s : LstateMF) :
    (instrLeakF i s).length = evCountF i := by
  unfold instrLeakF evCountF
  cases flagCondCC? i with
  | some _ => rfl
  | none =>
      obtain ⟨w, tag⟩ := i
      cases w with
      | Lopn ds o ss =>
          simp only [instrLeakB]
          split_ifs
          · rfl
          · exact flatMap_opLeakF_length _ _
      | _ => rfl

/-- **The physical trace of the image simulation** along the instructions `xs` of `body`
    from position `k`: at each instruction `x`, `posT` of the next `evCountF` events of the
    virtual trace `ℓ`, the count of the image of `x`. -/
def physT (frame : String → Option (BitVec 64)) (base : String → BitVec 64)
    (slotArr : String → Option (String × Nat)) (body : Lcmd) :
    List Linstr → Nat → List CTLeak → List CTLeak
  | [], _, _ => []
  | x :: xs, k, ℓ =>
      posT frame base x.li_i (imgInstr slotArr body k x.li_i)
          (ℓ.take (evCountF (imgInstr slotArr body k x.li_i)))
        ++ physT frame base slotArr body xs (k + 1)
          (ℓ.drop (evCountF (imgInstr slotArr body k x.li_i)))

/-! ## 4. One step -/

/-- **The events of one step.** From related states, at an instruction `bi` of a body that
    passes the gate, a step of the address machine emits `posT` of the events of the image
    instruction. -/
theorem step_leak {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp)
    (hgate : imgGateB frame slotArr body = true) {s : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRel frame slotArr base body s sa zf) (hlt : sa.reg.lpc < body.length - 1)
    {bi : Linstr} (hb : body[sa.reg.lpc]? = some bi) :
    stepLeakA frame body sa zf
      = posT frame base bi.li_i (imgInstr slotArr body sa.reg.lpc bi.li_i)
          (instrLeakF (imgInstr slotArr body sa.reg.lpc bi.li_i) s) := by
  have hg : instrGateB frame slotArr body sa.reg.lpc bi.li_i = true := by
    simp only [imgGateB, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hgate
    have := hgate.1.1 sa.reg.lpc hlt
    rw [hb] at this
    simpa using this
  unfold instrGateB at hg
  obtain ⟨ii0, x⟩ := bi
  simp only at hg ⊢
  cases hc : icase frame x with
  | other => rw [hc] at hg; cases hg
  | label =>
      obtain ⟨ii, l, rfl⟩ := icase_label hc
      simp [stepLeakA, hb, posT, hc]
  | cond cc l =>
      rw [hc] at hg
      simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hg
      obtain ⟨⟨pol, hpol⟩, -⟩ := hg
      have hz := hrel.zf
      obtain rfl := icase_cond hc
      obtain ⟨t, ht⟩ : ∃ t, imgInstr slotArr body sa.reg.lpc (.Lcond (.reg cc) l)
          = (.Lcond (.reg cc) l, t) := ⟨_, rfl⟩
      rw [ht]
      simp only [posT, hc, stepLeakA, hb, hpol]
      unfold condPol at hpol
      split at hpol <;> cases hpol <;> simp [instrLeakF, flagCondCC?, hz]
  | ldx d b idx =>
      rw [hc] at hg
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Option.isSome_iff_exists] at hg
      obtain ⟨⟨⟨⟨⟨An, hacc⟩, -⟩, -⟩, hidx⟩, hbf⟩ := hg
      obtain ⟨A, n⟩ := An
      obtain ⟨q, -, hp⟩ := ptr_of_reload hsep (.of_imgGateB hgate) hrel hacc hbf
      have hidxv : idxVal s.prog.base.reg idx = idxVal sa.reg idx := by
        unfold idxVal
        rw [hrel.regs idx hidx]
      obtain rfl := icase_ldx hc
      rw [imgInstr_ldx slotArr body _ hacc]
      simp [stepLeakA, hb, posT, hc, instrLeakA, normA, tagA, loadIdxA?, hp, instrLeakF,
        flagCondCC?, instrLeakB, opLeakF, hidxv, phiEv]
      norm_cast
  | stx d b idx v =>
      rw [hc] at hg
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Option.isSome_iff_exists] at hg
      obtain ⟨⟨⟨⟨An, hacc⟩, hidx⟩, hbf⟩, -⟩ := hg
      obtain ⟨A, n⟩ := An
      obtain ⟨q, -, hp⟩ := ptr_of_reload hsep (.of_imgGateB hgate) hrel hacc hbf
      have hidxv : idxVal s.prog.base.reg idx = idxVal sa.reg idx := by
        unfold idxVal
        rw [hrel.regs idx hidx]
      obtain rfl := icase_stx hc
      rw [imgInstr_stx slotArr body _ hacc]
      simp [stepLeakA, hb, posT, hc, instrLeakA, normA, tagA, storeIdxA?, hp, instrLeakF,
        flagCondCC?, instrLeakB, opLeakF, hidxv, phiEv]
      norm_cast
  | sload d q =>
      obtain ⟨hm, -, hq⟩ := icase_sload hc
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hq
      rcases slotMov?_cases hm with rfl | rfl <;>
        simp [stepLeakA, hb, posT, hc, instrLeakA, normA, tagA, hm, ha]
  | sstore q S =>
      obtain ⟨hm, hS, hq⟩ := icase_sstore hc
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hq
      rcases slotMov?_cases hm with rfl | rfl <;>
        simp [stepLeakA, hb, posT, hc, instrLeakA, normA, tagA, hm, ha, hS]
  | scmp d y q =>
      obtain ⟨hm, hq⟩ := icase_scmp hc
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hq
      obtain rfl := slotCmp?_eq hm
      simp [stepLeakA, hb, posT, hc, instrLeakA, normA, tagA, slotMov?, slotCmp?, ha]
  | zarr b n w =>
      rw [hc] at hg
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hg
      obtain ⟨⟨hacc, -⟩, hbf⟩ := hg
      cases hA : accArr slotArr body sa.reg.lpc b with
      | none => rw [hA] at hacc; cases hacc
      | some An =>
      obtain ⟨A, m⟩ := An
      obtain ⟨q, -, hp⟩ := ptr_of_reload hsep (.of_imgGateB hgate) hrel hA hbf
      obtain rfl := icase_zarr hc
      rw [imgInstr_zeroArr slotArr body _ hA]
      simp [stepLeakA, hb, posT, hc, instrLeakA, normA, tagA, zeroTagA, zeroArrA?, hp]
  | simm d b v j =>
      rw [hc] at hg
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hg
      obtain ⟨⟨hacc, hbf⟩, -⟩ := hg
      cases hA : accArr slotArr body sa.reg.lpc b with
      | none => rw [hA] at hacc; cases hacc
      | some An =>
      obtain ⟨A, m⟩ := An
      obtain ⟨q, -, hp⟩ := ptr_of_reload hsep (.of_imgGateB hgate) hrel hA hbf
      obtain rfl := icase_simm hc
      rw [imgInstr_storeImm slotArr body _ hA]
      simp [stepLeakA, hb, posT, hc, instrLeakA, normA, tagA, storeImmTagA, storeImmStruct?, hp,
        storeImmAddr?_of_lt _ (Nat.lt_succ_self j)]
  | reg =>
      rw [hc] at hg
      obtain ⟨ds, o, ss, rfl, ho1, ho2, hk⟩ := icase_reg hc
      have hok : regOkB frame (normA (.Lopn ds o ss)) = true := by
        simp only [regGateB, Bool.and_eq_true] at hg
        first
          | exact hg.1
          | exact hg.1.1
          | exact hg.1.1.1
      obtain ⟨hz1, hz2⟩ := icase_reg_arr hc ds o ss rfl
      have ht : tagA (.Lopn ds o ss) = .reg none := tagA_reg ho1 ho2 hk hz1 hz2
      simp only [stepLeakA, hb, posT, hc, ht]
      exact instrLeakA_regOk hok none sa

/-! ## 5. Straight runs -/

/-- A body without a conditional branch. -/
def NoCond (body : Lcmd) : Prop := ∀ bi ∈ body, ∀ c l, bi.li_i ≠ .Lcond c l

/-- On a body without a conditional branch, a step of the address machine advances the
    program counter by one. -/
theorem stepA_lpc_noCond {frame : String → Option (BitVec 64)} {body : Lcmd}
    (hnc : NoCond body) {sa sa1 : LstateA} {zf z1 : Bool}
    (h : stepA frame body sa zf = some (sa1, z1)) : sa1.reg.lpc = sa.reg.lpc + 1 := by
  unfold stepA at h
  split at h
  · exact fstepA_lpc frame _ sa sa1 zf z1 h
  · cases h
    rfl
  · rename_i ii cc l hbi
    exact absurd rfl (hnc _ (List.mem_of_getElem? hbi) (.reg cc) l)
  · cases h

/-- The image of a gated instruction other than a conditional is an `Lopn` or a label, which
    advances the program counter by one. -/
theorem imgInstr_nextPc {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat} {x : LinstrR}
    (hg : instrGateB frame slotArr body k x = true) (hnc : ∀ c l, x ≠ .Lcond c l)
    (wl : List LinstrR) (p p' : Nat) (h : NextPc wl (imgInstr slotArr body k x).1 p p') :
    p' = p + 1 := by
  unfold instrGateB at hg
  have key : (∃ ds o ss, x = .Lopn ds o ss) ∨ (∃ ii l, x = .Llabel ii l) := by
    cases hc : icase frame x with
    | other => rw [hc] at hg; cases hg
    | label => exact Or.inr (icase_label hc)
    | cond cc l => exact absurd (icase_cond hc) (hnc _ _)
    | ldx d b idx => exact Or.inl ⟨_, _, _, icase_ldx hc⟩
    | stx d b idx v => exact Or.inl ⟨_, _, _, icase_stx hc⟩
    | sload d q =>
        rcases slotMov?_cases (icase_sload hc).1 with h | h <;> exact Or.inl ⟨_, _, _, h⟩
    | sstore q S =>
        rcases slotMov?_cases (icase_sstore hc).1 with h | h <;> exact Or.inl ⟨_, _, _, h⟩
    | scmp d y q => exact Or.inl ⟨_, _, _, slotCmp?_eq (icase_scmp hc).1⟩
    | zarr b n w => exact Or.inl ⟨_, _, _, icase_zarr hc⟩
    | simm d b v j => exact Or.inl ⟨_, _, _, icase_simm hc⟩
    | reg =>
        obtain ⟨ds, o, ss, h, -, -⟩ := icase_reg hc
        exact Or.inl ⟨_, _, _, h⟩
  rcases key with ⟨ds, o, ss, rfl⟩ | ⟨ii, l, rfl⟩
  · obtain ⟨ds', o', ss', he⟩ : ∃ ds' o' ss',
        (imgInstr slotArr body k (.Lopn ds o ss)).1 = .Lopn ds' o' ss' := by
      unfold imgInstr
      repeat' split
      all_goals first
        | exact ⟨_, _, _, rfl⟩
        | (apply arrImmImg_lopn; assumption)
    rw [he] at h
    exact h
  · exact h

/-- **The traced image simulation on a body without a conditional branch.** For a printed
    body that passes the gate `imgGateB` and the class `physImgB`, at a separation `ImgSep`,
    every halting checked run of the image from a state related to an address state has a
    traced run with trace `ℓ`, and is matched by a halting traced run of the address machine
    on the body with trace `physT` of `ℓ` from the program counter of the start, with the
    relation at the end. -/
theorem image_addr_leak {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateB frame slotArr body = true) (hnc : NoCond body) (fn : String) :
    ∀ (fuel : Nat) (s t : LstateMF) (sa : LstateA) (zf : Bool), s.prog.lfn = fn →
      ImgRel frame slotArr base body s sa zf →
      lsemFuelMemFk true (singletonProgM fn (virtImg slotArr body)) fuel s = some t →
      ∃ ℓ fuel' sa' zf',
        lsemFuelMemFLeak (singletonProgM fn (virtImg slotArr body)) fuel s = some (t, ℓ)
        ∧ runALeak frame body fuel' sa zf
            = some ((sa', zf'),
                physT frame base slotArr body (body.dropLast.drop sa.reg.lpc) sa.reg.lpc ℓ)
        ∧ ImgRel frame slotArr base body t sa' zf' := by
  set P := singletonProgM fn (virtImg slotArr body)
  have halt : ∀ (s : LstateMF) (sa : LstateA) (zf : Bool), s.prog.lfn = fn →
      ImgRel frame slotArr base body s sa zf → findInstrMem P s.prog = none →
      ∀ fuel, ∃ ℓ fuel' sa' zf',
        lsemFuelMemFLeak P fuel s = some (s, ℓ)
        ∧ runALeak frame body fuel' sa zf
            = some ((sa', zf'),
                physT frame base slotArr body (body.dropLast.drop sa.reg.lpc) sa.reg.lpc ℓ)
        ∧ ImgRel frame slotArr base body s sa' zf' := by
    intro s sa zf hfn hrel hf fuel
    have hnil : body.dropLast.drop sa.reg.lpc = [] := by
      have h := hf
      rw [findInstrMem_single hfn, List.getElem?_eq_none_iff, virtImg_length, ← hrel.pc] at h
      exact List.drop_eq_nil_of_le (by rw [List.length_dropLast]; exact h)
    refine ⟨[], 0, sa, zf, lsemFuelMemFLeak_halt P fuel s hf, ?_, hrel⟩
    rw [hnil, runALeak_halt frame body 0 sa zf (haltedA_of_img (.of_imgGateB hgate) fn hfn hrel.pc hf)]
    rfl
  intro fuel
  induction fuel with
  | zero =>
      intro s t sa zf hfn hrel hrun
      cases hf : findInstrMem P s.prog with
      | some _ => simp [lsemFuelMemFk, hf] at hrun
      | none =>
          simp only [lsemFuelMemFk, hf, Option.some.injEq] at hrun
          subst hrun
          exact halt s sa zf hfn hrel hf 0
  | succ f ih =>
      intro s t sa zf hfn hrel hrun
      cases hf : findInstrMem P s.prog with
      | none =>
          simp only [lsemFuelMemFk, hf, Option.some.injEq] at hrun
          subst hrun
          exact halt s sa zf hfn hrel hf (f + 1)
      | some i =>
          simp only [lsemFuelMemFk, hf] at hrun
          cases he : evalInstrPMemFk true P i s with
          | none => rw [he] at hrun; cases hrun
          | some s1 =>
              rw [he] at hrun
              obtain ⟨hh, -, hfn1, sa1, z1, hst1, hcase⟩ :=
                img_step hsep hphys hgate fn hfn hrel hf he
              have hfetch := hf
              rw [findInstrMem_single hfn, virtImg_getElem?, ← hrel.pc,
                List.getElem?_dropLast] at hfetch
              split at hfetch
              case isFalse => cases hfetch
              rename_i hlt
              obtain ⟨bi, hb, rfl⟩ := Option.map_eq_some_iff.mp hfetch
              have hpc1 := stepA_lpc_noCond hnc hst1
              have hev := evalInstrPMemF_of_k he
              have hg : instrGateB frame slotArr body sa.reg.lpc bi.li_i = true := by
                simp only [imgGateB, Bool.and_eq_true, List.all_eq_true, List.mem_range]
                  at hgate
                have := hgate.1.1 sa.reg.lpc hlt
                rw [hb] at this
                simpa using this
              have hncb : ∀ c l, bi.li_i ≠ .Lcond c l :=
                hnc bi (List.mem_of_getElem? hb)
              have hvpc : s1.prog.base.reg.lpc = s.prog.base.reg.lpc + 1 :=
                imgInstr_nextPc hg hncb _ _ _ (evalInstrPMemF_next P _ s s1 hev).2
              rcases hcase with hrel1 | ⟨-, -, sa2, z2, hst2, hrel2⟩
              · obtain ⟨ℓ', f', sa', zf', hl', hr', hrel'⟩ := ih s1 t sa1 z1 hfn1 hrel1 hrun
                refine ⟨instrLeakF (imgInstr slotArr body sa.reg.lpc bi.li_i) s ++ ℓ',
                  f' + 1, sa', zf', ?_, ?_, hrel'⟩
                · rw [lsemFuelMemFLeak_step P f _ s s1 hf hev, hl']
                  rfl
                · have hdl : sa.reg.lpc < body.dropLast.length := by
                    rw [List.length_dropLast]; exact hlt
                  have hbi : body.dropLast[sa.reg.lpc] = bi := by
                    rw [List.getElem_dropLast]
                    exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans hb)
                  rw [runALeak_step frame body f' sa zf hh, hst1, Option.bind_some, hr',
                    List.drop_eq_getElem_cons hdl, hbi, hpc1,
                    step_leak hsep hgate hrel hlt hb]
                  simp only [Option.map_some, physT,
                    ← instrLeakF_length (imgInstr slotArr body sa.reg.lpc bi.li_i) s,
                    List.take_left', List.drop_left']
              · have hpc2 := stepA_lpc_noCond hnc hst2
                have h1 := hrel.pc
                have h2 := hrel2.pc
                omega

/-! ## 6. Constant time -/

/-- **Public-equal address states** of the image simulation: they are related, at one frame,
    one slot map and one map `base` of array bases, to two image states that are public-equal,
    at one program counter, and that have halting checked runs. -/
def AddrPub (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (base : String → BitVec 64) (body : Lcmd) (fn : String)
    (pubEq : LstateMF → LstateMF → Prop) (a₁ a₂ : LstateA × Bool) : Prop :=
  ∃ s₁ s₂ : LstateMF, pubEq s₁ s₂ ∧ s₁.prog.base.reg.lpc = s₂.prog.base.reg.lpc
    ∧ s₁.prog.lfn = fn ∧ s₂.prog.lfn = fn
    ∧ ImgRel frame slotArr base body s₁ a₁.1 a₁.2 ∧ ImgRel frame slotArr base body s₂ a₂.1 a₂.2
    ∧ (∃ f t, lsemFuelMemFk true (singletonProgM fn (virtImg slotArr body)) f s₁ = some t)
    ∧ (∃ f t, lsemFuelMemFk true (singletonProgM fn (virtImg slotArr body)) f s₂ = some t)

/-- **Constant time of the address machine from constant time of the image.** For a printed
    body without a conditional branch that passes the gate and the class, at a separation,
    constant time of the image on the flag machine gives constant time of the address machine
    on the body between public-equal address states (`AddrPub`). The array bases are one map
    `base` for both runs. -/
theorem image_addr_ct {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateB frame slotArr body = true) (hnc : NoCond body) (fn : String)
    {pubEq : LstateMF → LstateMF → Prop}
    (hct : MemFCT (singletonProgM fn (virtImg slotArr body)) pubEq) :
    ConstantTimeRel (AddrPub frame slotArr base body fn pubEq) (ARun frame body) := by
  rintro ⟨sa₁, zf₁⟩ ⟨sa₂, zf₂⟩ ℓ₁ ℓ₂
    ⟨s₁, s₂, hpub, hpc, hfn₁, hfn₂, hr₁, hr₂, ⟨f₁, t₁, hk₁⟩, ⟨f₂, t₂, hk₂⟩⟩
    ⟨g₁, r₁, hA₁⟩ ⟨g₂, r₂, hA₂⟩
  obtain ⟨v₁, F₁, sa₁', zf₁', hv₁, hL₁, -⟩ :=
    image_addr_leak hsep hphys hgate hnc fn f₁ s₁ t₁ sa₁ zf₁ hfn₁ hr₁ hk₁
  obtain ⟨v₂, F₂, sa₂', zf₂', hv₂, hL₂, -⟩ :=
    image_addr_leak hsep hphys hgate hnc fn f₂ s₂ t₂ sa₂ zf₂ hfn₂ hr₂ hk₂
  have hv : v₁ = v₂ := hct s₁ s₂ v₁ v₂ hpub ⟨f₁, t₁, hv₁⟩ ⟨f₂, t₂, hv₂⟩
  have e₁ := congrArg Prod.snd (runALeak_det frame body g₁ F₁ sa₁ zf₁ _ _ hA₁ hL₁)
  have e₂ := congrArg Prod.snd (runALeak_det frame body g₂ F₂ sa₂ zf₂ _ _ hA₂ hL₂)
  have hsp : sa₁.reg.lpc = sa₂.reg.lpc := by rw [hr₁.pc, hr₂.pc, hpc]
  simp only at e₁ e₂
  rw [e₁, e₂, hv, hsp]

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeakPhys
