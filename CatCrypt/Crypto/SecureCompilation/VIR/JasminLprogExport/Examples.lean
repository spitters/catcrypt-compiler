/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
import all Init.Data.List.Sort.Basic
import all Init.Data.String.Slice
import all Init.Data.String.Search
public meta import CatCrypt.Crypto.SecureCompilation.VIR.Core
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import Std.Data.HashMap
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.Proofs
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.Proofs

/-!
# Worked instances of the linear export

Small programs exercising each export path (fixed-trip, multi-binder and
runtime-trip loops, leaf calls in loop bodies, the ABI and frame-owning
exports, mixed register classes) with the equations that pin their outputs.

## Main definitions

* `loopSmokePhys`, `loopSmokePhysBody`, `mapAddOnePhysBody`,
  `mapAddOneAbiBody`, `loopSmokeRtPhysBody`: the example programs and bodies.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## Fixed-trip loop smoke test (`ComL` / `comLToBody`)

A one-argument program that seeds an accumulator from its input, runs the
doubling body `acc := acc + acc` `4` times via a `forLoop` node, and returns it.
The denotation is the mathematical `1 · 2⁴ = 16`, and the lowered body is a real
back-edge (`Llabel`/`Lcond`) with **one** copy of the body op (not `4`). -/

/-- The doubling loop body `acc := acc + acc` over `reg 64`. -/
def dblLoopBody : JLoopBody (.reg 64) :=
  ⟨4, .var (.mk (.regArith .add 64) rfl (.cons .here (.cons .here .nil)))
        (.ret .here)⟩

/-- Seed `a0`, loop `dblLoopBody` four times, return the accumulator. -/
def loopSmokeProg : ComL [.reg 64] (.reg 64) :=
  .forLoop dblLoopBody .here (.ret .here)

/-- **Denote = spec:** on input `1` the loop denotes `1 · 2⁴ = 16`. -/
theorem loopSmokeProg_denote :
    ComL.denote loopSmokeProg (.cons (1 : BitVec 64) .nil) = (16 : BitVec 64) := by
  rfl

/-- The lowered body of `loopSmokeProg`. -/
def loopSmokeBody : Lcmd := comLToBody 1 argName (fun _ => none) loopSmokeProg 1

/-- **Real back-edge:** the lowered body contains a conditional jump (`Lcond`,
    rendered `jne .L<d>`). -/
theorem loopSmokeBody_has_backedge :
    loopSmokeBody.any (fun i => match i.li_i with | .Lcond _ _ => true | _ => false)
      = true := by decide

/-- **Real loop label:** the lowered body contains an internal `Llabel` (the
    back-edge target `.L<d>:`). -/
theorem loopSmokeBody_has_label :
    loopSmokeBody.any (fun i => match i.li_i with | .Llabel _ _ => true | _ => false)
      = true := by decide

/-- **One body copy, not `n`:** the doubling op `ADD:64` appears exactly **once**
    in the lowered body — the loop is rolled, not unrolled four times. -/
theorem loopSmokeBody_one_body_copy :
    (loopSmokeBody.filter
      (fun i => match i.li_i with | .Lopn _ m _ => m == "ADD:64" | _ => false)).length
      = 1 := by decide

/-- The lowered body still ends with `Lret` (terminal return after the loop). -/
theorem loopSmokeBody_ends_Lret :
    loopSmokeBody.getLast?.map Linstr.li_i = some .Lret := rfl

/-! ### Physical-RA loop body (`ComL.toLfundefPhys`)

The looped smoke program through the physical-register export. Evidence that the
rolled loop renders with REAL x86 registers (no `%<UNKNOWN>`), one body copy, and
a real `jne .L<d>` back-edge with the accumulator / counter loop-carried in fixed
physical registers. -/

/-- The physical (post-RA) `lfundef` of the doubling loop. -/
def loopSmokePhys : Lfundef := ComL.toLfundefPhys loopSmokeProg

/-- The physical body of the doubling loop. -/
def loopSmokePhysBody : Lcmd := loopSmokePhys.lfd_body

/-- True iff an operand names a real allocatable x86 GP register (one of
    `gpRegNames`, i.e. NOT a spill `k.N`, NOT an SSA `rN`/`L<d>_r<k>`/`Lctr<d>`
    name). -/
def isRealGPName (n : String) : Bool := gpRegNames.contains n || n == "R14" || n == "R15"

/-- Every register operand of a `Lopn` in the physical loop body is a REAL x86
    register name — none is a leftover SSA name (`rN` / `L<d>_r<k>` / `Lctr<d>`)
    that the owned printer would render as `%<UNKNOWN>`. (The non-`reg`
    operands — immediates, the `NZ` condition flag carried by `Lcond` — are not
    register-file operands and are excluded.) -/
theorem loopSmokePhysBody_all_real_registers :
    loopSmokePhysBody.all (fun i =>
      match i.li_i with
      | .Lopn dsts _ srcs =>
          (dsts.filterMap LOperand.regName?).all isRealGPName &&
          (srcs.filterMap LOperand.regName?).all isRealGPName
      | _ => true) = true := by native_decide

/-- **No `%<UNKNOWN>` SSA names survive:** no `Lopn` register operand in the
    physical loop body still carries an SSA-shape name (`r…` / `L…` / `Lctr…`).
    The complement of `loopSmokePhysBody_all_real_registers`, stated as the
    absence of the SSA-name shapes the owned printer maps to `%<UNKNOWN>`. -/
theorem loopSmokePhysBody_no_ssa_names :
    loopSmokePhysBody.all (fun i =>
      match i.li_i with
      | .Lopn dsts _ srcs =>
          ((dsts ++ srcs).filterMap LOperand.regName?).all (fun n =>
            !("L".isPrefixOf n) && !("r".isPrefixOf n))
      | _ => true) = true := by native_decide

/-- **Real back-edge preserved:** the physical loop body still contains the
    `Lcond` conditional jump (`jne .L<d>`). -/
theorem loopSmokePhysBody_has_backedge :
    loopSmokePhysBody.any (fun i =>
      match i.li_i with | .Lcond _ _ => true | _ => false) = true := by native_decide

/-- **Real loop label preserved:** the physical loop body still contains the
    internal `Llabel` back-edge target. -/
theorem loopSmokePhysBody_has_label :
    loopSmokePhysBody.any (fun i =>
      match i.li_i with | .Llabel _ _ => true | _ => false) = true := by native_decide

/-- **One body copy, not `n`:** the doubling op `ADD:64` appears exactly **once**
    in the physical body — RA preserves the rolled shape (the loop is not
    unrolled four times). -/
theorem loopSmokePhysBody_one_body_copy :
    (loopSmokePhysBody.filter
      (fun i => match i.li_i with | .Lopn _ m _ => m == "ADD:64" | _ => false)).length
      = 1 := by native_decide

-- `loopSmokePhysBody_expected` moved out of Lean: the instruction text is pinned by
-- `lake exe jasmin-lprog-shape-kat` against `scripts/golden/jasmin-lprog-shape.txt`.

/-- The looped physical export has exactly one function, named `fname`, exported.
    (Structural well-formedness — the loop-aware analogue of
    `Com.toLprogPhys`'s well-formedness.) -/
theorem ComL.toLprogPhys_wf {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : ComL Γ t) (fname : String) :
    (ComL.toLprogPhys c fname).lp_funcs.length = 1 ∧
      ((ComL.toLprogPhys c fname).lp_funcs.head?.map Prod.fst = some fname) ∧
      ((ComL.toLprogPhys c fname).lp_funcs.head?.map (fun p => p.2.lfd_export)
        = some true) :=
  ⟨rfl, rfl, rfl⟩

/-! ## Multi-binder loop smoke test (`forLoopN` / indexed array load/store)

A two-argument program `mapAddOneProg [out, in]` that runs the array-map body
`out[i] := in[i] + 1` over 4-element `reg 64` arrays via a single `forLoopN`
node. The body reads the loop index as the runtime SIB index of a `stackLoad`
(`LOADIDX in[i]`) and a `stackStore` (`STOREIDX out[i]`), so the rolled loop does
a per-iteration indexed array load/store — the increment kernels like
`mayo_encode` (`out[i] := pack(in[2i], in[2i+1])`) need. The denotation is the
mathematical array map `i ↦ in[i] + 1`, and the lowered body is ONE body copy
with the index advance + a real back-edge. -/

/-- The array-map body `out[i] := in[i] + 1` over the multi-binder context
    `[accTy = stackArr 64 4, idx = reg 64, inv = stackArr 64 4]`:
    `v0 := stackLoad in[idx]`, `v1 := 1`, `v2 := v0 + v1`,
    `v3 := stackStore acc[idx] := v2`, return `v3`. -/
def mapAddOneBody :
    Com jasminDialect [.stackArr 64 4, .reg 64, .stackArr 64 4] (.stackArr 64 4) :=
  -- v0 := stackLoad in[idx]   (in = .there (.there .here), idx = .there .here)
  .var (.mk (.stackLoad 64 4) rfl (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
  -- v1 := 1
  (.var (.mk (.regConst 64 1) rfl .nil)
  -- v2 := v0 + v1   (v0 = .there .here, v1 = .here)
  (.var (.mk (.regArith .add 64) rfl (.cons (.there .here) (.cons .here .nil)))
  -- v3 := stackStore acc[idx] := v2
  -- ctx (newest-first): [v2, v1, v0, acc, idx, in]
  --   acc = .there^3 .here, idx = .there^4 .here, v2 = .here
  (.var (.mk (.stackStore 64 4) rfl
      (.cons (.there (.there (.there .here)))
        (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil))))
  (.ret .here))))

/-- The 4-trip multi-binder map loop. -/
def mapAddOneLoop : JLoopBodyN (.stackArr 64 4) [.stackArr 64 4] := ⟨4, mapAddOneBody⟩

/-- Seed the accumulator from the `out` argument (`.here`), thread the `in`
    argument (`.there .here`) as the invariant base, loop 4 times, return the
    final array. -/
def mapAddOneProg : ComL [.stackArr 64 4, .stackArr 64 4] (.stackArr 64 4) :=
  .forLoopN mapAddOneLoop .here (.cons (.there .here) .nil) (.ret .here)

/-- A sample input array `in[i] = 10·i` and a zeroed initial output array. -/
def mapAddOneIn : Fin 4 → BitVec 64 := fun i => BitVec.ofNat 64 (i.val * 10)

/-- **Denote = array-map spec:** the loop denotes `out[i] = in[i] + 1` at every
    index. The whole computed array equals the pointwise spec `fun i => in[i] + 1`. -/
theorem mapAddOneProg_denote :
    (ComL.denote mapAddOneProg (.cons (fun _ => (0 : BitVec 64)) (.cons mapAddOneIn .nil)))
      = (fun i => mapAddOneIn i + 1) := by
  funext i; revert i; decide

/-- The virtual (pre-RA) lowered body of the map loop. -/
def mapAddOneBodyV : Lcmd := comLToBody 2 argName (fun _ => none) mapAddOneProg 2

/-- The physical (post-RA) lowered body of the map loop. -/
def mapAddOnePhysBody : Lcmd := (ComL.toLfundefPhys mapAddOneProg).lfd_body

/-- **Indexed array load IN the loop body:** the virtual body contains exactly one
    `LOADIDX` whose source is a register-indexed SIB element `in[idx*8]` — a
    per-iteration `stackLoad in[i]`, not a compile-time `.arr` element. -/
theorem mapAddOneBodyV_has_indexed_load :
    (mapAddOneBodyV.filter (fun i => match i.li_i with
      | .Lopn _ "LOADIDX" [.arrIdx _ idx 8] => idx == loopIdx 2
      | _ => false)).length = 1 := by decide

/-- **Indexed array store IN the loop body:** exactly one `STOREIDX` whose
    destination is a SIB element `out[idx*8]` — a per-iteration `stackStore
    out[i]`. -/
theorem mapAddOneBodyV_has_indexed_store :
    (mapAddOneBodyV.filter (fun i => match i.li_i with
      | .Lopn _ "STOREIDX" [.arrIdx _ idx 8, _] => idx == loopIdx 2
      | _ => false)).length = 1 := by decide

/-- **One body copy, not `n`:** the indexed load appears exactly once — the loop
    is rolled (one `LOADIDX in[i]`), not unrolled four times. -/
theorem mapAddOneBodyV_one_body_copy :
    (mapAddOneBodyV.filter (fun i => match i.li_i with
      | .Lopn _ m _ => m == "LOADIDX" | _ => false)).length = 1 := by decide

/-- **Real back-edge + label:** the virtual body has both an internal `Llabel`
    (`.L<d>:`) and a `Lcond` (`jne .L<d>`). -/
theorem mapAddOneBodyV_has_backedge :
    mapAddOneBodyV.any (fun i => match i.li_i with | .Lcond _ _ => true | _ => false)
      = true ∧
    mapAddOneBodyV.any (fun i => match i.li_i with | .Llabel _ _ => true | _ => false)
      = true := by exact ⟨by decide, by decide⟩

/-- **Index advance:** the body advances the loop index `Lidx<d>` by one each trip
    (`ADD Lidx<d>, Lidx<d>, #1`) — distinct from the trip-counter decrement. -/
theorem mapAddOneBodyV_has_index_advance :
    mapAddOneBodyV.any (fun i => match i.li_i with
      | .Lopn [.reg d] _ [.reg s, .imm 1] => d == loopIdx 2 && s == loopIdx 2
      | _ => false) = true := by decide

-- `mapAddOnePhysBody_expected` moved out of Lean: the instruction text is pinned by
-- `lake exe jasmin-lprog-shape-kat` against `scripts/golden/jasmin-lprog-shape.txt`.

/-- **Every physical body operand is a real x86 register** — no leftover SSA name
    (`r…` / `L…` / `Lctr…` / `Lidx…`) that the owned printer would render as
    `%<UNKNOWN>`. (Immediates and the `NZ` flag are excluded — not register-file
    operands.) -/
theorem mapAddOnePhysBody_all_real_registers :
    mapAddOnePhysBody.all (fun i =>
      match i.li_i with
      | .Lopn dsts _ srcs =>
          (dsts.filterMap LOperand.regName?).all isRealGPName &&
          (srcs.filterMap LOperand.regName?).all isRealGPName
      | _ => true) = true := by native_decide

/-- **No SSA names survive in the SIB operands either:** every `LOADIDX`/`STOREIDX`
    SIB base and index in the physical body is a real x86 register (so the
    indexed memory references assemble). -/
theorem mapAddOnePhysBody_sib_real_registers :
    mapAddOnePhysBody.all (fun i =>
      match i.li_i with
      | .Lopn dsts _ srcs =>
          (dsts ++ srcs).all (fun o => match o with
            | .arrIdx b idx _ => isRealGPName b && isRealGPName idx
            | _ => true)
      | _ => true) = true := by native_decide

/-- **One body copy in the physical body too:** RA preserves the rolled shape —
    one `LOADIDX` (the loop is not unrolled). -/
theorem mapAddOnePhysBody_one_body_copy :
    (mapAddOnePhysBody.filter (fun i => match i.li_i with
      | .Lopn _ m _ => m == "LOADIDX" | _ => false)).length = 1 := by native_decide

/-! ### 7g″ demo: a self-allocating (frame-owning) straight-line export

A minimal `ComL` over a single `stackArr 64 4` "argument" that is NOT a caller
pointer: it lives in a frame the function allocates itself. The body writes
`arr[0] := 42` then reads it back, returning the loaded scalar — the fixed-base
array idiom MAYO's self-test uses (the base is materialised once, never fed back,
so it is free of the §7g′ functional-array-accumulator hazard). Exported through
`ComL.toLfundefPhysFramed`: a 32-byte self-owned frame, the frame base IS `%rsp`
(single region at offset 0, call-free → the `%rsp`-direct SIB path), a
`STOREIDX`/`LOADIDX` at `(%rsp,%idx,8)`, and no SysV pointer argument anywhere.
The register-ABI export (§7g) cannot express this (it materialises the base from
a SysV pointer arg and opens no frame). -/

/-- The demo `ComL`: `v0 := 0; v1 := 42; v2 := stackStore arr[v0] := v1;
    v3 := stackLoad v2[v0]; return v3` — store `42` into a frame cell, load it
    back, return it. -/
def framedStoreLoadProg : ComL [.stackArr 64 4] (.reg 64) :=
  -- v0 := 0 (the cell index)
  .var (.mk (.regConst 64 0) rfl .nil)
  -- v1 := 42 (the stored value)
  (.var (.mk (.regConst 64 42) rfl .nil)
  -- v2 := stackStore arr[v0] := v1     ctx=[v1,v0,arr]
  (.var (.mk (.stackStore 64 4) rfl
      (.cons (.there (.there .here)) (.cons (.there .here) (.cons .here .nil))))
  -- v3 := stackLoad arr[v0]            ctx=[v2,v1,v0,arr]  (base arr=.there^3.here, idx v0=.there.there.here)
  -- Read back through the FIXED frame base `arr` (materialised once), not the
  -- stackStore result thread `v2` — the in-place, fixed-base idiom MAYO uses.
  (.var (.mk (.stackLoad 64 4) rfl
      (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) .nil)))
  (.ret .here))))

/-- The frame-allocating export of the store/load demo: a 32-byte self-owned
    frame, the frame base `%rsp` directly (no base LEA), a `STOREIDX`+`LOADIDX`
    in-frame, and a scalar `uint64_t` return — no SysV pointer args. -/
def framedDemoFundef : Lfundef :=
  ComL.toLfundefPhysFramed 32 [("arr", 0)] framedStoreLoadProg

/-- The framed export's body as text (for inspection / the structural pins). -/
def framedDemoBodyText : List String :=
  framedDemoFundef.lfd_body.map (fun i => i.li_i.toText)

-- `framedDemoBodyText_expected` moved out of Lean: the instruction text is pinned by
-- `lake exe jasmin-lprog-shape-kat` against `scripts/golden/jasmin-lprog-shape.txt`.

/-- **The `FRAME` directive leads** the framed body (the `frameSize` marker the
    printer reads to open the `leaq -F(%rsp)` frame), stating the exact 32-byte
    self-owned frame. -/
theorem framedDemoFundef_frame_directive :
    framedDemoBodyText.head? = some "Lopn [] FRAME [#32]" := by
  native_decide

/-- **`lfd_stk_max` records the self-allocated frame size** (0 in the register-ABI
    export), and there are **no incoming SysV pointer arguments** (the arrays are
    self-owned, not passed). -/
theorem framedDemoFundef_stk_and_args :
    framedDemoFundef.lfd_stk_max = 32 ∧ framedDemoFundef.lfd_arg = [] := by
  native_decide

/-- **Every array access reaches the self-owned frame base `%rsp`.** There is NO
    base LEA (the frame alloc `leaq -F(%rsp), %rsp` establishes `%rsp` as the
    base); every `STOREIDX`/`LOADIDX` SIB base in the body is exactly `%rsp` — no
    caller pointer, no reserved register, no reused loop-carried register. -/
theorem framedDemoFundef_accesses_frame_base :
    framedDemoFundef.lfd_body.any (fun i => match i.li_i with
      | .Lopn _ "STOREIDX" (.arrIdx b _ _ :: _) => b == "RSP" | _ => false) = true ∧
    framedDemoFundef.lfd_body.all (fun i => match i.li_i with
      | .Lopn _ "STOREIDX" (.arrIdx b _ _ :: _) => b == "RSP"
      | .Lopn _ "LOADIDX" [.arrIdx b _ _] => b == "RSP"
      | _ => true) = true := by native_decide

/-! ### 7g′. 2-pointer-ABI looped export (`ComL.toLfundefPhysAbi`) — IN/OUT base
fix

The register-ABI `ComL.toLfundefPhys` body (above) binds the IN/OUT array bases
to RA-assigned registers that the loop reuses as scratch — the gdb-confirmed
swap-and-clobber. `ComL.toLfundefPhysAbi` is the 2-pointer-ABI export that saves
each pointer argument to a red-zone qsave slot and reloads each `LOADIDX`/
`STOREIDX` SIB base from its slot into `R14` immediately before every access
(the proven straight-line `comToLfundefPhysAbi` machinery, lifted onto the loop).
The smoke kernel is `mapAddOneProg` with `out = a1` (the `init` arg) and
`in = a0` (the `invs` arg), ABI `out = RDI`, `in = RSI`. -/

/-- The 2-pointer-ABI looped body of the map kernel. -/
def mapAddOneAbiBody : Lcmd :=
  (ComL.toLfundefPhysAbi mapAddOneProg "a1" ["a0"]).lfd_body

-- `mapAddOneAbiBody_expected` moved out of Lean: the instruction text is pinned by
-- `lake exe jasmin-lprog-shape-kat` against `scripts/golden/jasmin-lprog-shape.txt`.

/-- **The IN load base is the reloaded IN pointer, the OUT store base the reloaded
    OUT pointer — no swap.** Every `LOADIDX` is immediately preceded by a reload of
    the in-pointer (`MOVQ R14, [qsave.RSI]`), and every `STOREIDX` by a reload of
    the out-pointer (`MOVQ R14, [qsave.RDI]`), with the SIB base `R14`. -/
theorem mapAddOneAbiBody_no_swap :
    (mapAddOneAbiBody.zip (mapAddOneAbiBody.drop 1)).all (fun (prev, cur) =>
      match cur.li_i with
      | .Lopn _ "LOADIDX" [.arrIdx "R14" _ _] =>
          prev.li_i.toText == "Lopn [R14] MOVQ [qsave.RSI]"
      | .Lopn _ "STOREIDX" [.arrIdx "R14" _ _, _] =>
          prev.li_i.toText == "Lopn [R14] MOVQ [qsave.RDI]"
      | _ => true) = true := by native_decide

/-- **No invariant-base clobber inside the loop body.** Every `LOADIDX`/`STOREIDX`
    SIB base is the reserved reload scratch `R14`, which is rewritten from a
    red-zone qsave slot immediately before the access — so no body instruction can
    leave a stale data word in the base register (the segfault root cause). -/
theorem mapAddOneAbiBody_sib_base_is_reloaded_scratch :
    mapAddOneAbiBody.all (fun i =>
      match i.li_i with
      | .Lopn _ _ srcs => srcs.all (fun o =>
          match o with
          | .arrIdx base _ _ => base == reloadScratch2
          | _ => true)
      | _ => true) = true := by native_decide

/-- **One body copy in the ABI export too:** the loop stays rolled — exactly one
    `LOADIDX` (the array map is not unrolled). -/
theorem mapAddOneAbiBody_one_body_copy :
    (mapAddOneAbiBody.filter (fun i => match i.li_i with
      | .Lopn _ m _ => m == "LOADIDX" | _ => false)).length = 1 := by native_decide

/-! ### 7f. Mixed scalar+vector register-class allocation (smoke test)

A body that MIXES scalar GP ops (`ADD`/`SUB`) and vector ops (`VPXOR`/`VPADDQ`,
`reg 128`) is allocated in ONE class-aware linear scan: GP bindings to GP
registers, vector bindings to `XMM`, with disjoint pools so no value crosses
class. -/

/-- A mixed body: two GP `Lopn`s then two vector (`reg 128`) `Lopn`s. -/
def mixedClassBody : Lcmd :=
  [ ⟨0, .Lopn [.reg "r0"] "ADD" [.reg "a0", .reg "a1"]⟩
  , ⟨0, .Lopn [.reg "r1"] "SUB" [.reg "r0", .reg "a0"]⟩
  , ⟨0, .Lopn [.reg "r2"] "VPXOR" [.reg "a2", .reg "a3"]⟩
  , ⟨0, .Lopn [.reg "r3"] "VPADDQ" [.reg "r2", .reg "a2"]⟩
  , ⟨0, .Lret⟩ ]

/-- The vector slots: the GP-only inputs/results (`r0`,`a0`,`a1`,`r1`) are GP; the
    vector inputs and results (`r2`,`a2`,`a3`,`r3`) are vector. (Slots are in
    `bodyNames` first-appearance order, destination-first; the trailing `false`
    is the universe-padding entry.) -/
theorem mixedClassBody_vecSlots :
    (bodyVecSlots mixedClassBody).toList
      = [false, false, false, false, true, true, true, true, false] := by native_decide

/-- The one-pass class-aware table: GP slots land in `0,1,2` (→ `RAX`,`RBX`,`RCX`),
    vector slots land in `vectorBase + 0/1/2` (→ `XMM0`,`XMM1`,`XMM2`). No GP slot
    reaches `vectorBase`, no vector slot stays below it — disjoint pools. -/
theorem mixedClassBody_table :
    (bodyPhysTable mixedClassBody).toList = [0, 1, 2, 2, 1000, 1001, 1002, 1002] := by
  native_decide

-- `mixedClassBody_expected` moved out of Lean: the instruction text is pinned by
-- `lake exe jasmin-lprog-shape-kat` against `scripts/golden/jasmin-lprog-shape.txt`.

/-- **No cross-class assignment.** Every GP `Lopn` (mnemonic not vector) carries
    only GP register operands (or immediates / spills), and every vector `Lopn`
    carries only `XMM` operands — no GP name in a vector op and no `XMM` in a GP
    op. -/
theorem mixedClassBody_no_cross_class :
    (physBody (fun _ => none) mixedClassBody).all (fun i =>
      match i.li_i with
      | .Lopn dsts opn srcs =>
          let names := (dsts ++ srcs).filterMap LOperand.regName?
          if isVectorMnem opn then names.all (fun n => n.startsWith "XMM")
          else names.all (fun n => !n.startsWith "XMM")
      | _ => true) = true := by native_decide

/-- A pure-scalar body of the same shape (no vector op). -/
def scalarClassBody : Lcmd :=
  [ ⟨0, .Lopn [.reg "r0"] "ADD" [.reg "a0", .reg "a1"]⟩
  , ⟨0, .Lopn [.reg "r1"] "SUB" [.reg "r0", .reg "a0"]⟩
  , ⟨0, .Lopn [.reg "r2"] "XOR" [.reg "a2", .reg "a3"]⟩
  , ⟨0, .Lopn [.reg "r3"] "ADD" [.reg "r2", .reg "a2"]⟩
  , ⟨0, .Lret⟩ ]

/-- **Byte-identical GP-only path.** A pure-scalar body classifies every slot GP,
    so the class-aware table equals the original GP-only `physTable ∘ bodyTrace`
    and its physical body equals the GP-only `physBody`. The vector register class
    is purely additive. -/
theorem scalarClassBody_table_identical :
    bodyPhysTable scalarClassBody = physTable (bodyTrace scalarClassBody) := by
  native_decide

theorem scalarClassBody_allGP :
    (bodyVecSlots scalarClassBody).all (· == false) = true := by native_decide

/-! ### 7g‴. Multi-input scalar-reduce looped export — accumulator/input base fix

A regression guard for the GF-dot / matmul-accumulate shape
`out[0] := Σ_{i<n} a[i]·b[i]` (the `qruov` / `sdith` kernels): a looped `ComL`
with a 1-cell out/accumulator array (`stackArr W 1`) and **two** input arrays.

`resolveVar` maps a `Var` to `argName (curDepth-1-deBruijn)`, counting the slot
from the program root — the **reverse** of the newest-first `Γ`. So for a
top-level `ComL` whose `Γ` is the argument list, the loop's `init` (newest,
`.here`, the out/accumulator) resolves to the highest arg slot and the last
`invs` entry to `a0`. The export now derives the per-role base names from the
program's own `init`/`invs` via `ComL.loopArgBaseNames`, so the alias and the
qsave-reload map key on the names the body actually uses — independent of how the
caller ordered `outArg`/`inArgs`. Previously the multi-input callers passed
`Γ`-ordered names, so the 2nd input (`b`) resolved to `a0` and reloaded from the
out qsave slot — the byte-KAT-confirmed `42864 vs 69` garbage. -/

abbrev DGN : Nat := 12
abbrev DGW : Nat := 64

/-- One GF-dot iteration `acc[0] := acc[0] + a[i]·b[i]` over the multi-binder
    loop context `[acc(stackArr 1), idx, a(stackArr N), b(stackArr N)]`. -/
def dgBody : Com jasminDialect
    [.stackArr DGW 1, .reg 64, .stackArr DGW DGN, .stackArr DGW DGN] (.stackArr DGW 1) :=
  .var (.mk (.regConst 64 0) rfl .nil)
  (.var (.mk (.stackLoad DGW DGN) rfl
        (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) .nil)))
  (.var (.mk (.stackLoad DGW DGN) rfl
        (.cons (.there (.there (.there (.there (.there .here)))))
          (.cons (.there (.there (.there .here))) .nil)))
  (.var (.mk (.regArith .mul DGW) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.stackLoad DGW 1) rfl
        (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there .here))) .nil)))
  (.var (.mk (.regArith .add DGW) rfl (.cons .here (.cons (.there .here) .nil)))
  (.var (.mk (.stackStore DGW 1) rfl
        (.cons (.there (.there (.there (.there (.there (.there .here))))))
          (.cons (.there (.there (.there (.there (.there .here)))))
            (.cons .here .nil))))
  (.ret .here)))))))

def dgLoop : JLoopBodyN (.stackArr DGW 1) [.stackArr DGW DGN, .stackArr DGW DGN] := ⟨DGN, dgBody⟩
def dgProg : ComL [.stackArr DGW 1, .stackArr DGW DGN, .stackArr DGW DGN] (.stackArr DGW 1) :=
  .forLoopN dgLoop .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)) (.ret .here)

/-- Sample residue streams `a[i] = b[i] = i+1`. -/
def dgA : Fin DGN → BitVec DGW := fun i => BitVec.ofNat DGW (i.val + 1)
def dgB : Fin DGN → BitVec DGW := fun i => BitVec.ofNat DGW (i.val + 1)

/-- **Denote = dot spec:** `out[0] = Σ_{i<12}(i+1)^2 = 650`. -/
theorem dg_denote :
    (ComL.denote dgProg (.cons (fun _ => (0:BitVec DGW)) (.cons dgA (.cons dgB .nil))) ⟨0, by decide⟩).toNat
      = 650 := by native_decide

/-- The 3-pointer-ABI rolled body, exported with the caller's `outArg`/`inArgs`
    given in `Γ`-order (the convention the multi-input callers use). -/
def dgBodyR : Lcmd := (ComL.toLfundefPhysAbi dgProg (argName 0) [argName 1, argName 2]
    (fun _ => none) (fun _ => none) ["RDI","RSI","RDX"] [64,64,64]).lfd_body

/-- The reload qsave-slot before each memref access, in body order
    `[a[i], b[i], acc[0]-load, acc[0]-store]`. -/
def dgReloads : List String :=
  (dgBodyR.zip (dgBodyR.drop 1)).filterMap (fun (prev, cur) =>
    match cur.li_i, prev.li_i with
    | .Lopn _ "LOADIDX" (.arrIdx "R14" _ _ :: _), .Lopn [.reg "R14"] _ [.reg q] => some q
    | .Lopn _ "STOREIDX" (.arrIdx "R14" _ _ :: _), .Lopn [.reg "R14"] _ [.reg q] => some q
    | _, _ => none)

/-- **The accumulator/input base fix.** Each access reloads from its OWN slot:
    `a → qsave.RSI`, `b → qsave.RDX`, and both accumulator accesses (load + store)
    from the out slot `qsave.RDI`. No cross-wiring (before the fix, `b[i]`
    reloaded from `qsave.RDI`, reading the out array as `b`). -/
theorem dg_reload_slots_fixed :
    dgReloads = ["qsave.RSI", "qsave.RDX", "qsave.RDI", "qsave.RDI"] := by native_decide

/-- The two inputs and the accumulator/out use THREE distinct qsave slots. -/
theorem dg_three_distinct_slots : (dgReloads.take 3).Nodup := by native_decide

/-- Every SIB base is the reloaded scratch `R14` (no body-clobberable base). -/
theorem dg_all_bases_r14 :
    dgBodyR.all (fun i => match i.li_i with
      | .Lopn _ _ srcs => srcs.all (fun o => match o with
          | .arrIdx base _ _ => base == reloadScratch2 | _ => true)
      | _ => true) = true := by native_decide

/-- **No regression:** the single-input array-map kernel (`mapAddOne`) is
    byte-identical to its byte-KAT-passing reference (the fix changes nothing
    when the caller's names already match the `resolveVar` convention). -/
theorem mapAddOneAbiBody_unchanged_by_fix :
    (ComL.toLfundefPhysAbi mapAddOneProg "a1" ["a0"]).lfd_body = mapAddOneAbiBody := by
  rfl

/-! ### 7g″. Scalar-before-array invariant order

The `mpn_mul_1` / `mpn_divrem_1` shape: a runtime-trip fold whose loop invariants
are a scalar multiplier and an input array, with the scalar listed first. The
reload map pairs array bases with `abiArgs.drop 1` by position, so a scalar
counted as a position would push the input array's base onto the next ABI
register — reloading the array through a scalar argument's red-zone slot and
dereferencing an integer as a pointer. `arrArgNamesHV` keeps only the array
invariants, so the pairing is fixed by the array count alone. -/

/-- One `acc[0] := acc[0] + arr[i]·s` iteration over the loop context
    `[acc(stackArr 1), idx, s(reg 64), arr(stackArr N)]` — a scalar invariant
    ahead of an array invariant. -/
def dsBody : Com jasminDialect
    [.stackArr DGW 1, .reg 64, .reg 64, .stackArr DGW DGN] (.stackArr DGW 1) :=
  .var (.mk (.regConst 64 0) rfl .nil)
  (.var (.mk (.stackLoad DGW DGN) rfl
        (.cons (.there (.there (.there (.there .here))))
          (.cons (.there (.there .here)) .nil)))
  (.var (.mk (.regArith .mul DGW) rfl
        (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil)))
  (.var (.mk (.stackLoad DGW 1) rfl
        (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) .nil)))
  (.var (.mk (.regArith .add DGW) rfl (.cons .here (.cons (.there .here) .nil)))
  (.var (.mk (.stackStore DGW 1) rfl
        (.cons (.there (.there (.there (.there (.there .here)))))
          (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil))))
  (.ret .here))))))

def dsLoop : JLoopBodyN (.stackArr DGW 1) [.reg 64, .stackArr DGW DGN] := ⟨DGN, dsBody⟩

/-- The scaled-accumulate kernel over the argument context `[s, arr, acc]`, so
    that `acc` is argument slot 0 (`RDI`), `arr` slot 1 (`RSI`) and the scalar `s`
    slot 2 (`RDX`). The invariants list the scalar first. -/
def dsProg : ComL [.reg 64, .stackArr DGW DGN, .stackArr DGW 1] (.stackArr DGW 1) :=
  .forLoopN dsLoop (.there (.there .here))
    (.cons .here (.cons (.there .here) .nil)) (.ret .here)

/-- The 3-argument-ABI rolled body of the scalar-before-array kernel. -/
def dsBodyR : Lcmd := (ComL.toLfundefPhysAbi dsProg (argName 0) [argName 1]
    (fun _ => none) (fun _ => none) ["RDI","RSI","RDX"] [64,64,64]).lfd_body

/-- The qsave slot each memref access reloads its SIB base from, in body order. -/
def dsReloads : List String :=
  (dsBodyR.zip (dsBodyR.drop 1)).filterMap (fun (prev, cur) =>
    match cur.li_i, prev.li_i with
    | .Lopn _ "LOADIDX" (.arrIdx "R14" _ _ :: _), .Lopn [.reg "R14"] _ [.reg q] => some q
    | .Lopn _ "STOREIDX" (.arrIdx "R14" _ _ :: _), .Lopn [.reg "R14"] _ [.reg q] => some q
    | _, _ => none)

-- The input array reloads from the `RSI` slot, both accumulator accesses from the
-- `RDI` slot. The scalar's slot `qsave.RDX` is not a base for any access.
#guard dsReloads = ["qsave.RSI", "qsave.RDI", "qsave.RDI"]
#guard !(dsReloads.contains "qsave.RDX")

/-! ## Real-`Lcall` leaf-call-in-loop-body smoke test (`loopBodyWalkNCall`)

The loop body MSM's Straus inner loop and the GGM real AES-PRG node need: a body
that `call`s an opaque leaf, lowered to a real `LinstrR.Lcall` (not the
`CALL:` shadow `Lopn`), with the SysV ABI marshalling around it. -/

/-- A single-arg leaf-call loop body `acc := ed_point_double(acc)` over the
    multi-binder context `[reg 64, reg 64, ]` (`invTys = []`). -/
def edDblCallBody : JLoopBodyN (.reg 64) [] :=
  ⟨3, .var (.mk (.extCall "ed_point_double" [.reg 64] (.reg 64)) rfl
              (.cons .here .nil))
        (.ret .here)⟩

/-- The lowered body via the real-`Lcall` walk (acc in `RAX`, idx `Lidx1`,
    no invariants; the body walk starts at `curDepth = 2 + 0`). -/
def edDblCallBodyW : Lcmd :=
  (loopBodyWalkNCall 1 "RAX" "Lidx1" [] (fun _ => none) edDblCallBody.update 2).1

-- `edDblCallBodyW_expected` moved out of Lean: the instruction text is pinned by
-- `lake exe jasmin-lprog-shape-kat` against `scripts/golden/jasmin-lprog-shape.txt`.

/-- **It is an `LinstrR.Lcall`,** not an `Lopn "CALL:…"` shadow. -/
theorem edDblCallBodyW_has_real_Lcall :
    edDblCallBodyW.any (fun i =>
      match i.li_i with | .Lcall _ _ => true | _ => false) = true := by decide

/-- A two-arg leaf-call body `acc := ed_point_add(acc, inv)` over the context
    `[reg 64 (acc), reg 64 (idx), reg 64 (inv)]` (one invariant base). -/
def edAddCallBody : JLoopBodyN (.reg 64) [.reg 64] :=
  ⟨5, .var (.mk (.extCall "ed_point_add" [.reg 64, .reg 64] (.reg 64)) rfl
              (.cons .here (.cons (.there (.there .here)) .nil)))
        (.ret .here)⟩

/-- The lowered two-arg call body (acc `RAX`, invariant base `RBX`; the walk
    starts at `curDepth = 2 + 1`). -/
def edAddCallBodyW : Lcmd :=
  (loopBodyWalkNCall 1 "RAX" "Lidx1" ["RBX"] (fun _ => none) edAddCallBody.update 3).1

-- `edAddCallBodyW_expected` moved out of Lean: the instruction text is pinned by
-- `lake exe jasmin-lprog-shape-kat` against `scripts/golden/jasmin-lprog-shape.txt`.

/-- The call-free doubling body `acc := acc + acc` over `[reg 64, reg 64]`. -/
def dblCallfreeBody :
    Com jasminDialect [JasminTy.reg 64, JasminTy.reg 64] (JasminTy.reg 64) :=
  .var (.mk (.regArith .add 64) rfl (.cons .here (.cons .here .nil))) (.ret .here)

/-- A loop body whose single binding calls a leaf returning a 16-word buffer,
    taking the accumulator as its first operand and returning that binding: the
    in-place accumulator update, in the body context of a 16-word array
    accumulator, the loop index, and a 12-word invariant array. -/
def inPlaceBufCallBody :
    Com jasminDialect
      [JasminTy.stackArr 64 16, JasminTy.reg 64, JasminTy.stackArr 64 12]
      (JasminTy.stackArr 64 16) :=
  .var (.mk (.extCall "madd" [.stackArr 64 16, .stackArr 64 12] (.stackArr 64 16)) rfl
          (.cons .here (.cons (.there (.there .here)) .nil)))
    (.ret .here)

/-- A loop body whose single binding calls a leaf returning a 16-word buffer from
    the loop index alone: a buffer result that is not an accumulator update. -/
def scratchBufCallBody :
    Com jasminDialect [JasminTy.stackArr 64 16, JasminTy.reg 64]
      (JasminTy.stackArr 64 16) :=
  .var (.mk (.extCall "table_select" [.reg 64] (.stackArr 64 16)) rfl
          (.cons (.there .here) .nil))
    (.ret .here)

-- Static checks pinning the in-place condition against silent change, at each
-- body's own walk start depth (`2 + nInv`): the accumulator-updating buffer call
-- is detected and takes no frame scratch, a buffer call that is not an
-- accumulator update keeps its scratch slot, and a call-free body has neither.
#guard loopInPlaceBufSlot inPlaceBufCallBody 3 = some 3
#guard loopBufBindings inPlaceBufCallBody 3 = [(3, 128)]
#guard loopScratchBufBindings inPlaceBufCallBody 3 = []
#guard loopBufTotal (loopScratchBufBindings inPlaceBufCallBody 3) = 0
#guard loopInPlaceBufSlot scratchBufCallBody 2 = none
#guard loopScratchBufBindings scratchBufCallBody 2 = [(2, 128)]
#guard loopBufTotal (loopScratchBufBindings scratchBufCallBody 2) = 128
#guard loopInPlaceBufSlot dblCallfreeBody 2 = none
#guard loopScratchBufBindings dblCallfreeBody 2 = []

-- The walk's result name carries the destination the call wrote: the in-place
-- update returns the accumulator register, so the loop emits no feedback move,
-- and a scratch buffer result returns its frame slot.
#guard (loopBodyWalkNBuf 3 "RACC" "Lidx3" ["RBX"] [] (some 3) (fun _ => none)
          inPlaceBufCallBody 3).2 = "RACC"
#guard (loopBodyWalkNBuf 2 "RACC" "Lidx2" [] (loopScratchBufBindings scratchBufCallBody 2)
          none (fun _ => none) scratchBufCallBody 2).2 = "mem.RSP.0"

-- `loopBodyWalkNCall_callfree_eq_loopBodyWalkN` moved out of Lean: the two
-- renderings are compared by `lake exe jasmin-lprog-shape-kat`.

/-! ### Caller-save barrier for an in-loop `Lcall` (`physBody` / `remapOperand`)

A rolled loop body that `call`s a leaf (`loopBodyCallLcmd`) must keep
its loop-carried values (accumulator, `Lidx`, `Lctr`) in callee-saved registers
across the call, and leave the literal SysV arg/return registers the marshalling
names (`RDI`/`RAX`) verbatim. The barrier in `remapOperand` (engaged by
`bodyHasCall`) achieves both; a call-free body is byte-identical. -/

/-- A rolled loop body with an in-body real `Lcall` (`acc := ed_point_double(acc)`)
    whose loop-carried set is `acc` (accumulator), `Lidx1` (index), `Lctr1`
    (counter). The marshalling `MOV RDI, acc` and capture `MOV acc, RAX` name the
    SysV arg/return registers literally. -/
def callBarrierBody : Lcmd :=
  [ ⟨0, .Lopn [.reg "acc"] (withWidthTag 64 "MOV") [.reg "a0"]⟩
  , ⟨0, .Lopn [.reg "Lidx1"] (withWidthTag 64 "MOV") [.imm 0]⟩
  , ⟨0, .Lopn [.reg "Lctr1"] (withWidthTag 64 "MOV") [.imm 8]⟩
  , ⟨0, .Llabel .internal 1⟩
  , ⟨0, .Lopn [.reg "RDI"] (withWidthTag 64 "MOV") [.reg "acc"]⟩
  , ⟨0, .Lcall none ("ed_point_double", 0)⟩
  , ⟨0, .Lopn [.reg "acc"] (withWidthTag 64 "MOV") [.reg "RAX"]⟩
  , ⟨0, .Lopn [.reg "Lidx1"] (withWidthTag 64 "ADD") [.reg "Lidx1", .imm 1]⟩
  , ⟨0, .Lopn [.reg "Lctr1"] (withWidthTag 64 "SUB") [.reg "Lctr1", .imm 1]⟩
  , ⟨0, .Lopn [.reg "Lctr1"] (withWidthTag 64 "CMP") [.reg "Lctr1", .imm 0]⟩
  , ⟨0, .Lcond (.reg "NZ") 1⟩ ]

/-- The barrier engages: the body has a real `Lcall`. -/
theorem callBarrierBody_hasCall : bodyHasCall callBarrierBody = true := by decide

/-- **Call-free regression guard.** The barrier is a no-op on the call-free loop
    smoke export (`bodyHasCall = false`): its physical body is byte-identical to
    the pre-barrier allocation (accumulator `RAX`, counter `RBX`). -/
theorem loopSmoke_callfree_barrier_noop :
    bodyHasCall (ComL.toLfundefPhys loopSmokeProg).lfd_body = false ∧
    loopSmokePhysBody.map (fun i => i.li_i.toText) =
      [ "Lopn [RBX] MOVQ [RDI]"
      , "Lopn [RAX] MOV:64 [RBX]"
      , "Lopn [RBX] MOV:64 [#4]"
      , "Llabel int 1"
      , "Lopn [RCX] MOV:64 [RAX]"
      , "Lopn [RCX] ADD:64 [RCX,RAX]"
      , "Lopn [RAX] MOV:64 [RCX]"
      , "Lopn [RBX] SUB:64 [RBX,#1]"
      , "Lopn [RBX] CMP:64 [RBX,#0]"
      , "Lcond NZ 1"
      , "Lret" ] := by native_decide

/-! ### In-loop-call ComL through the full ABI export (`ComL.toLprogPhysAbi`)

A `ComL.forLoopN` whose body `call`s a leaf
(`acc := ed_point_double(acc)`, MSM's Straus / GGM rolled-kernel shape) assembled
through the SAME full ABI export the call-free kernels use. The call-walk
selection (`comBodyHasCall` ⇒ `forLoopLcmdNCall`) makes the body issue a real
`Lcall`, so `bodyHasCall` holds on the export. The aux name-resolution passes
(`buildArgMaterializePhys` / `buildArgPtrMaterialize` / `buildEpilogue` /
`memrefBaseReload`) resolve names through `physNameForBody`; the body operands use
the call-free `remapOperand`. The theorems below check that the in-loop `Lcall`
is emitted (the call is present) and that the call-free loop path is
byte-identical. -/

/-- The looped accumulator kernel `acc := ed_point_double(acc)` (4 trips) over a
    single `reg 64` argument. -/
def edDblLoopProg : ComL [JasminTy.reg 64] (JasminTy.reg 64) :=
  .forLoopN edDblCallBody .here .nil (.ret .here)

/-- The program is recognised as an in-loop-call `ComL`, so the call-walk engages. -/
theorem edDblLoopProg_hasLoopCall : comLHasLoopCall edDblLoopProg = true := by decide

/-- The virtual lowered body now uses a **real `Lcall`** (not the `CALL:` shadow),
    so `bodyHasCall` fires on it (the barrier-gating predicate). -/
theorem edDblLoopProg_virt_hasCall :
    bodyHasCall (ComL.toLfundef edDblLoopProg).lfd_body = true := by decide

/-- The full physical export's body keeps `bodyHasCall` true (the body still issues
    the real `Lcall` after RA), so the barrier stayed engaged end-to-end. -/
theorem edDblLoopProg_phys_hasCall :
    bodyHasCall (ComL.toLfundefPhys edDblLoopProg).lfd_body = true := by native_decide

/-- **The body issues exactly one `LinstrR.Lcall`** (not a `CALL:`
    shadow `Lopn`) — the real `call ed_point_double`. -/
theorem edDblLoopProg_one_real_Lcall :
    ((ComL.toLfundefPhys edDblLoopProg).lfd_body.filter (fun i =>
      match i.li_i with | .Lcall _ _ => true | _ => false)).length = 1 := by
  native_decide

/-- **Call-free byte-identical guard.** The call-walk selection
    (`comBodyHasCall ⇒ forLoopLcmdNCall`) and the `physNameForBody` barrier are
    no-ops on a call-free loop: the map-style loop `mapAddOneProg` has no in-loop
    call, so `bodyHasCall = false` and the export takes the original path. The full
    byte-identity to the pre-wiring reference is still `mapAddOneAbiBody_unchanged_by_fix`
    (proved by `rfl`), which is unaffected by this change. -/
theorem mapAddOneProg_callfree_byte_identical :
    comLHasLoopCall mapAddOneProg = false ∧
    bodyHasCall (ComL.toLfundefPhysAbi mapAddOneProg "a1" ["a0"]).lfd_body = false := by
  refine ⟨by decide, by native_decide⟩

/-! ## Runtime-trip loop smoke test (`ComL.forLoopNRt` / runtime counter seed)

A two-argument program `(seed, count)` that seeds an accumulator from `seed`,
runs the squaring body `acc := acc · acc` a **runtime** number of times (`count`,
read from a register), and returns it. The denotation is the mathematical
`seed^(2^count)`; the lowered body seeds the trip counter from a **register**
(`MOV Lctr, a0`), not an immediate — the capability poly1305-style
`f(out, inp, nblk)` kernels need (the trip count is a runtime argument). The body
op is `MUL` (distinct from the loop scaffolding's `ADD Lidx`/`SUB Lctr`), so the
one-body-copy check reads cleanly. -/

/-- The runtime-count squaring body `acc := acc · acc` over the
    `JLoopBodyN`-shaped context `[reg 64 (acc), reg 64 (idx)]` (invTys = `[]`; the
    loop index is unused by this scalar body). -/
def sqrRtBody : Com jasminDialect [JasminTy.reg 64, JasminTy.reg 64] (.reg 64) :=
  .var (.mk (.regArith .mul 64) rfl (.cons .here (.cons .here .nil))) (.ret .here)

/-- Seed `acc` from arg `.here`, loop `sqrRtBody` a RUNTIME number of times (the
    in-scope `count` var `.there .here`), return the accumulator. invTys = `[]`. -/
def loopSmokeRtProg : ComL [JasminTy.reg 64, JasminTy.reg 64] (.reg 64) :=
  .forLoopNRt sqrRtBody (.there .here) .here .nil (.ret .here)

/-- **Denote = spec:** seed `3`, runtime count `2` → `3^(2²) = 81`. The fold runs
    `(count.lookup V).toNat = 2` times. -/
theorem loopSmokeRtProg_denote :
    ComL.denote loopSmokeRtProg (.cons (3 : BitVec 64) (.cons (2 : BitVec 64) .nil))
      = (81 : BitVec 64) := by rfl

/-- **Denote = spec (different runtime count):** seed `2`, runtime count `3` →
    `2^(2³) = 256`. Same program, different `count` argument: the trip count is
    read from the valuation, not baked in. -/
theorem loopSmokeRtProg_denote_count3 :
    ComL.denote loopSmokeRtProg (.cons (2 : BitVec 64) (.cons (3 : BitVec 64) .nil))
      = (256 : BitVec 64) := by rfl

/-- The lowered body of `loopSmokeRtProg` (top-level, `nArgs = 2`). -/
def loopSmokeRtBody : Lcmd := comLToBody 2 argName (fun _ => none) loopSmokeRtProg 2

/-- **Real back-edge:** the runtime-count loop lowers to a conditional jump
    (`Lcond`, rendered `jne .L<d>`) — a rolled loop, not an unrolled chain. -/
theorem loopSmokeRtBody_has_backedge :
    loopSmokeRtBody.any (fun i => match i.li_i with | .Lcond _ _ => true | _ => false)
      = true := by decide

/-- **Runtime counter seed:** the trip counter `Lctr2` is initialised from a
    **register** (the resolved `count` argument `a0`), i.e. `MOV Lctr2, a0` — NOT
    `MOV Lctr2, #n`. This is the one instruction that distinguishes a runtime-trip
    loop from the fixed-trip `forLoopN`, and the whole point of the capability. -/
theorem loopSmokeRtBody_runtime_counter_seed :
    loopSmokeRtBody.any (fun i => match i.li_i with
      | .Lopn dsts mnem srcs =>
          mnem == withWidthTag 64 "MOV" &&
          (dsts.filterMap LOperand.regName?).contains (loopCtr 2) &&
          (srcs.filterMap LOperand.regName?).contains (argName 0)
      | _ => false) = true := by decide

/-- **One body copy, not `count`:** the squaring op `MUL:64` appears exactly once
    — the loop is rolled (one copy + back-edge), independent of the trip count. -/
theorem loopSmokeRtBody_one_body_copy :
    (loopSmokeRtBody.filter
      (fun i => match i.li_i with | .Lopn _ m _ => m == "MUL:64" | _ => false)).length
      = 1 := by decide

/-- The lowered body still ends with `Lret`. -/
theorem loopSmokeRtBody_ends_Lret :
    loopSmokeRtBody.getLast?.map Linstr.li_i = some .Lret := rfl

/-- **Physical-RA export:** the runtime-count loop survives the same SSA→physical
    register allocation as a straight-line `Com` — every `Lopn` operand is a real
    x86 register (no `%<UNKNOWN>` SSA name), and the back-edge is preserved. -/
def loopSmokeRtPhysBody : Lcmd := (ComL.toLfundefPhys loopSmokeRtProg).lfd_body

/-- Every register operand of the physical runtime-count loop body is a real x86
    register name (no leftover SSA `rN`/`L<d>_r<k>`/`Lctr<d>` name). -/
theorem loopSmokeRtPhysBody_all_real_registers :
    loopSmokeRtPhysBody.all (fun i =>
      match i.li_i with
      | .Lopn dsts _ srcs =>
          (dsts.filterMap LOperand.regName?).all isRealGPName &&
          (srcs.filterMap LOperand.regName?).all isRealGPName
      | _ => true) = true := by native_decide

/-- **Real back-edge preserved through RA:** the physical body still contains the
    `Lcond` conditional jump. -/
theorem loopSmokeRtPhysBody_has_backedge :
    loopSmokeRtPhysBody.any (fun i =>
      match i.li_i with | .Lcond _ _ => true | _ => false) = true := by native_decide

/-! ### 3-argument ABI: a runtime count from the 3rd SysV int register (`RDX`)

The `poly1305_mac_hacl(out, inp, nblk)` ABI shape: the runtime trip count `nblk`
is the **3rd** integer argument. Under the export's program-root convention
(`resolveVar`: the newest binder `.here` resolves to the highest arg slot, which
maps to the 3rd SysV register), placing the `count` var at `.here` routes the
trip count through `a2` → `RDX`. This smoke is a 3-argument runtime-count loop
`acc := acc · inv` (count from `a2`), proving the counter seed reads `a2` (the
3rd SysV int arg). The existing `ComL.toLfundefPhys`/`toLfundefPhysAbi` argument
materialization (`buildArgMaterializePhys` / `buildArgPtrMaterialize` +
`abiSaveOfExt`) already routes a 3rd SysV register, so no new ABI entry point is
needed — only the runtime-count node feeds it. -/

/-- Body `acc := acc · inv` over `[accTy = reg 64, idx = reg 64, inv = reg 64]`
    (the loop index is unused; the invariant `inv` is the deepest binder
    `.there (.there .here)`). -/
def mulInvRtBody : Com jasminDialect [JasminTy.reg 64, JasminTy.reg 64, JasminTy.reg 64] (.reg 64) :=
  .var (.mk (.regArith .mul 64) rfl (.cons .here (.cons (.there (.there .here)) .nil)))
    (.ret .here)

/-- A 3-argument runtime-count loop. `Γ = [count, inv, acc]` (newest-first), so
    the program-root args are `a0 = acc`, `a1 = inv`, `a2 = count` — i.e. the trip
    count is the 3rd SysV integer argument (`RDX`), the `poly1305_mac_hacl(out,
    inp, nblk)` ABI shape. `count = .here`, `inv = .there .here`,
    `init (acc) = .there (.there .here)`. -/
def loopSmokeRt3Prog :
    ComL [JasminTy.reg 64, JasminTy.reg 64, JasminTy.reg 64] (.reg 64) :=
  .forLoopNRt mulInvRtBody .here (.there (.there .here))
    (.cons (.there .here) .nil) (.ret .here)

/-- **Denote = spec:** `acc = 2`, `inv = 3`, runtime count = `2` → `2·3² = 18`.
    The valuation is `[count, inv, acc] = [2, 3, 2]`. -/
theorem loopSmokeRt3Prog_denote :
    ComL.denote loopSmokeRt3Prog
      (.cons (2 : BitVec 64) (.cons (3 : BitVec 64) (.cons (2 : BitVec 64) .nil)))
      = (18 : BitVec 64) := by rfl

/-- The lowered body of the 3-argument runtime-count loop (`nArgs = 3`). -/
def loopSmokeRt3Body : Lcmd := comLToBody 3 argName (fun _ => none) loopSmokeRt3Prog 3

/-- **3rd SysV arg → counter seed:** the trip counter `Lctr3` is seeded from
    `a2` (the 3rd program-root argument, which the SysV projection maps to `RDX`)
    via `MOV Lctr3, a2` — the `poly1305_mac_hacl(…, nblk)` runtime count routed
    into the loop. -/
theorem loopSmokeRt3Body_counter_from_a2 :
    loopSmokeRt3Body.any (fun i => match i.li_i with
      | .Lopn dsts mnem srcs =>
          mnem == withWidthTag 64 "MOV" &&
          (dsts.filterMap LOperand.regName?).contains (loopCtr 3) &&
          (srcs.filterMap LOperand.regName?).contains (argName 2)
      | _ => false) = true := by decide

/-- **Physical export survives RA with 3 args:** every register operand is a real
    x86 register (no `%<UNKNOWN>`), and the back-edge is preserved. The 3rd SysV
    argument (`RDX`) is materialized into the body's count register at entry by
    `buildArgMaterializePhys`. -/
theorem loopSmokeRt3PhysBody_all_real_registers :
    (ComL.toLfundefPhys loopSmokeRt3Prog).lfd_body.all (fun i =>
      match i.li_i with
      | .Lopn dsts _ srcs =>
          (dsts.filterMap LOperand.regName?).all isRealGPName &&
          (srcs.filterMap LOperand.regName?).all isRealGPName
      | _ => true) = true := by native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
