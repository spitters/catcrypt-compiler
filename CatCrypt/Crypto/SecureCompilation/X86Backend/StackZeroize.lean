/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

/-!
# `zeroizeLprog`: clearing the stack frame before an export function returns

An opt-in `Lprog → Lprog` pass in the family of `LprogStoreToLoad.elimReloadsLprog`
and `LprogScheduler.scheduleLprog`: it appends, immediately before each function
body's `Lret`, one zero store per frame cell the body writes.

## The frame, and where the stores go

`LprogAsmPrinter.renderLfundef` brackets the rendered body with
`leaq -F(%rsp), %rsp` and `leaq F(%rsp), %rsp` (`F = frameSize body`), followed by
`ret`. The body itself carries the ABI prologue (`buildPrologue`: eight `MOVQ`
saves into `qsave.*`), the register allocator's spill traffic (`k.N`), the output
stores, and the callee-saved restores (`calleeSaveRestoreEpilogue`), and ends with
`Lret`, which renders to no line. So the position "last instruction of `lfd_body`,
before `Lret`" is after every callee-saved restore and before the frame is
released — the two ordering constraints a clearing pass has. No store is issued
below the released `%rsp`.

## The cells that are cleared

`resolveName` maps three name classes to an `%rsp`-relative address: the spill
slots `k.N`, the ABI save slots `qsave.X`, and the frame scratch buffers
`mem.RSP.<off>`. A `mem.<base>.<off>` name with any other base is caller memory —
the output buffer is `mem.R14.<off>` — and is not a frame cell.

`writtenFrameCells` collects the frame-cell names that occur as an `Lopn`
destination anywhere in the body, deduplicated in first-write order, and
`zeroizeBody` appends one `MOVQ <cell>, $0` per name. Cells the body never writes
as a destination are not cleared; a cell a called leaf writes through a pointer
(the array-ABI `extCall` orchestration passes `mem.RSP.<off>` buffer addresses to
an opaque leaf) carries no `Lopn` destination and is outside the census.

## The store width

The zero stores use the mnemonic `MOVQ`, which `LprogAsmPrinter.mnemWidth` sizes
at 64 bits and which does not end in `:64`, so `bodyIsU64` — and with it the
spill-cell stride — is unchanged (`bodyIsU64_zeroizeBody`). The pass adds no
`FRAME` directive, no `Lcall`, and no spill name the body does not already carry,
so `frameSize`'s other inputs read the same as well.
A quadword store covers a `qsave` slot exactly
(`qsaveFrameOff` strides 8) and covers a `u64` spill cell exactly; on a `u32` body
the 4-byte spill cells are covered together with the cell above, which stays
inside the frame because the spill region sits below the 64-byte `qsave` block and
is itself zeroed.

## Main results

* `zeroizeBody_eq_prefix_ret` / `zeroizeBody_ends_Lret` — the pass rewrites a body
  ending in `Lret` to `body.dropLast ++ zeroStores body ++ [Lret]` and leaves any
  other body alone.
* `zeroizeBody_isPrefix` — the original instructions are a prefix of the output:
  nothing is dropped, reordered, or modified.
* `mem_writtenFrameCells_isFrameCell` — every cleared name is a frame cell, so no
  bare register and no caller memory name is written.
* `zeroizePrefix_lsemStraight` — value preservation against
  `JasminLsem.lsemStraight`: the transformed prefix completes whenever the original
  prefix does, reaching a state that agrees with the original on every name outside
  the census and has the same `lmem`.
* `zeroizePrefix_erases` — every censused cell holds `0` in that state.
* `zeroizeLfundef_sig` — every non-`lfd_body` field is unchanged.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.StackZeroize

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

/-! ## 1. Frame-cell names

The name classes `LprogAsmPrinter.resolveName` resolves to an `%rsp`-relative
address: the register allocator's spill slots `k.N`, the ABI save slots
`qsave.X`, and the frame scratch buffers `mem.RSP.<off>`. Every other name is
either a bare physical register or a caller-memory reference
(`mem.RDI.<off>`, `mem.R14.<off>`, …). The name `qsave.RSP+off` of a stack argument
resolves to the caller's stack word above the frame and is no frame cell. -/

/-- True iff the operand name denotes a cell of this function's own stack frame:
    a spill slot `k.N`, an ABI save slot `qsave.X` other than a caller stack word
    `qsave.RSP+off`, or a frame scratch buffer `mem.RSP.<off>`. A `mem.<base>.<off>`
    name with a base other than `RSP` is caller memory and is excluded. -/
def isFrameCell (n : String) : Bool :=
  "k.".isPrefixOf n || ("qsave.".isPrefixOf n && !"qsave.RSP+".isPrefixOf n)
    || "mem.RSP.".isPrefixOf n

/-- A caller stack word `qsave.RSP+off` is no frame cell, so the pass writes no zero
    store to it. -/
theorem isFrameCell_rsp (off : Nat) : isFrameCell ("qsave.RSP+" ++ toString off) = false := by
  simp only [isFrameCell, isPrefixOf_eq_hasPrefix, hasPrefix, String.toList_append]
  simp [List.isPrefixOf]

/-- The frame-cell names an instruction writes as a destination. Non-`Lopn`
    instructions write nothing. -/
def frameCellDsts : LinstrR → List String
  | .Lopn dsts _ _ =>
      dsts.filterMap (fun o =>
        match o with
        | .reg n => if isFrameCell n then some n else none
        | _ => none)
  | _ => []

/-- Every name a `frameCellDsts` census returns is a frame cell. -/
theorem isFrameCell_of_mem_frameCellDsts {i : LinstrR} {n : String}
    (h : n ∈ frameCellDsts i) : isFrameCell n = true := by
  cases i with
  | Lopn dsts opn srcs =>
    rw [frameCellDsts, List.mem_filterMap] at h
    obtain ⟨o, _, ho⟩ := h
    cases o with
    | reg m =>
      by_cases hm : isFrameCell m = true
      · simp only [hm, ite_true, Option.some.injEq] at ho
        exact ho ▸ hm
      · simp only [Bool.not_eq_true] at hm
        simp only [hm, Bool.false_eq_true, ite_false] at ho
        exact absurd ho (by simp)
    | arr b i => simp at ho
    | imm v => simp at ho
    | arrIdx b i s => simp at ho
  | _ => simp [frameCellDsts] at h

/-! ## 2. The written-cell census

`writtenFrameCells` is the deduplicated list of frame-cell names the body writes,
in first-write order. `addUnique` appends a name that is not already recorded. -/

/-- Append `n` to `acc` unless it is already there. -/
def addUnique (acc : List String) (n : String) : List String :=
  if acc.contains n then acc else acc ++ [n]

/-- A member of `addUnique acc n` is a member of `acc` or is `n`. -/
theorem mem_addUnique {acc : List String} {n m : String} (h : m ∈ addUnique acc n) :
    m ∈ acc ∨ m = n := by
  unfold addUnique at h
  split at h
  · exact Or.inl h
  · rcases List.mem_append.1 h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (by simpa using h')

/-- A member of a left fold of `addUnique` came from the accumulator or the
    list. -/
theorem mem_foldl_addUnique : ∀ (l acc : List String) {m : String},
    m ∈ l.foldl addUnique acc → m ∈ acc ∨ m ∈ l := by
  intro l
  induction l with
  | nil => intro acc m h; exact Or.inl h
  | cons a rest ih =>
    intro acc m h
    rw [List.foldl_cons] at h
    rcases ih _ h with h' | h'
    · rcases mem_addUnique h' with h'' | h''
      · exact Or.inl h''
      · exact Or.inr (h'' ▸ List.mem_cons_self)
    · exact Or.inr (List.mem_cons_of_mem _ h')

/-- The frame-cell names a body writes as `Lopn` destinations, deduplicated and
    in first-write order. -/
def writtenFrameCells (body : Lcmd) : List String :=
  (body.flatMap (fun i => frameCellDsts i.li_i)).foldl addUnique []

/-- **Every cleared name is a frame cell.** No bare physical register and no
    caller-memory name (`mem.R14.<off>` and the other non-`RSP` bases) is in the
    census, so the pass writes only this function's own frame. -/
theorem mem_writtenFrameCells_isFrameCell {body : Lcmd} {n : String}
    (h : n ∈ writtenFrameCells body) : isFrameCell n = true := by
  rcases mem_foldl_addUnique _ [] h with h' | h'
  · simp at h'
  · rw [List.mem_flatMap] at h'
    obtain ⟨i, _, hi⟩ := h'
    exact isFrameCell_of_mem_frameCellDsts hi

/-- A name that is not a frame cell is outside the census. -/
theorem not_mem_writtenFrameCells {body : Lcmd} {n : String}
    (h : isFrameCell n = false) : n ∉ writtenFrameCells body := by
  intro hm
  rw [mem_writtenFrameCells_isFrameCell hm] at h
  exact absurd h (by decide)

/-! ## 3. The zeroing stores and the pass

One `MOVQ <cell>, $0` per censused cell, appended between the body's last
instruction and its `Lret`. -/

/-- The zero store for one frame cell: `Lopn [cell] MOVQ [$0]`, which
    `LprogAsmPrinter` renders as `movq $0, <off>(%rsp)`. -/
def zeroStore (n : String) : Linstr := ⟨0, .Lopn [.reg n] "MOVQ" [.imm 0]⟩

/-- The zero stores for a body: one per censused frame cell, in census order. -/
def zeroStores (body : Lcmd) : Lcmd := (writtenFrameCells body).map zeroStore

/-- True iff the body's last instruction is the function-return terminator. -/
def endsWithLret (body : Lcmd) : Bool :=
  match body.getLast? with
  | some i => match i.li_i with
              | .Lret => true
              | _ => false
  | none => false

/-- The `Lret`-free instruction list the transformed body runs before returning:
    the original body without its terminator, followed by the zero stores. -/
def zeroizePrefix (body : Lcmd) : Lcmd := body.dropLast ++ zeroStores body

/-- **The stack-clearing pass on one body.** For a body ending in `Lret`, the
    zero stores are inserted between the body's last instruction and the
    terminator; any other body is returned unchanged. -/
def zeroizeBody (body : Lcmd) : Lcmd :=
  if endsWithLret body then zeroizePrefix body ++ [⟨0, .Lret⟩] else body

/-- On a body ending in `Lret` the pass produces the zeroing prefix followed by
    the terminator. -/
theorem zeroizeBody_eq_prefix_ret {body : Lcmd} (h : endsWithLret body = true) :
    zeroizeBody body = zeroizePrefix body ++ [⟨0, .Lret⟩] := by
  simp only [zeroizeBody, h, ite_true]

/-- A body that does not end in `Lret` is returned unchanged. -/
theorem zeroizeBody_of_not_ends {body : Lcmd} (h : endsWithLret body = false) :
    zeroizeBody body = body := by
  simp only [zeroizeBody, h, Bool.false_eq_true, ite_false]

/-- The transformed body still ends in `Lret`. -/
theorem zeroizeBody_ends_Lret {body : Lcmd} (h : endsWithLret body = true) :
    (zeroizeBody body).getLast?.map Linstr.li_i = some LinstrR.Lret := by
  rw [zeroizeBody_eq_prefix_ret h]
  simp

/-! ## 4. Structural results

The pass adds instructions and modifies none: the input is a prefix of the
output, and every added instruction is a zero store to a frame cell. -/

/-- Dropping the terminator and re-appending it recovers the body. -/
theorem dropLast_append_Lret {body : Lcmd} (h : endsWithLret body = true) :
    ∃ k : Nat, body.dropLast ++ [⟨k, LinstrR.Lret⟩] = body := by
  unfold endsWithLret at h
  cases hl : body.getLast? with
  | none => rw [hl] at h; exact absurd h (by decide)
  | some i =>
    rw [hl] at h
    obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.1 hl
    obtain ⟨ii, ir⟩ := i
    cases ir <;> simp at h
    exact ⟨ii, by rw [hys, List.dropLast_concat]⟩

/-- **The input is a prefix of the output.** The pass appends the zero stores and
    the terminator; it drops, reorders, and modifies nothing. -/
theorem zeroizeBody_isPrefix {body : Lcmd} (h : endsWithLret body = true) :
    ∃ suffix : Lcmd, zeroizeBody body = body.dropLast ++ suffix := by
  refine ⟨zeroStores body ++ [⟨0, LinstrR.Lret⟩], ?_⟩
  rw [zeroizeBody_eq_prefix_ret h, zeroizePrefix, List.append_assoc]

/-- The pass adds one instruction per censused cell plus the terminator. -/
theorem zeroizeBody_length {body : Lcmd} (h : endsWithLret body = true) :
    (zeroizeBody body).length
      = body.dropLast.length + (writtenFrameCells body).length + 1 := by
  rw [zeroizeBody_eq_prefix_ret h, zeroizePrefix, zeroStores]
  simp
  omega

/-- Every added instruction is a zero store whose destination is a frame cell. -/
theorem mem_zeroStores {body : Lcmd} {i : Linstr} (h : i ∈ zeroStores body) :
    ∃ n, isFrameCell n = true ∧ i = ⟨0, .Lopn [.reg n] "MOVQ" [.imm 0]⟩ := by
  rw [zeroStores, List.mem_map] at h
  obtain ⟨n, hn, hi⟩ := h
  exact ⟨n, mem_writtenFrameCells_isFrameCell hn, hi ▸ rfl⟩

/-! ### The frame layout is unchanged

`LprogAsmPrinter.bodyIsU64` decides the spill-cell stride, and through it every
rendered `k.N` offset. The zero stores carry the mnemonic `MOVQ`, which does not
end in `:64`, so the predicate reads the same on the transformed body. -/

/-- `bodyIsU64` of a concatenation is the disjunction of the two halves. -/
theorem bodyIsU64_append (a b : Lcmd) :
    bodyIsU64 (a ++ b) = (bodyIsU64 a || bodyIsU64 b) := List.any_append

/-- A lone function-return terminator carries no width tag. -/
theorem bodyIsU64_Lret (k : Nat) : bodyIsU64 [⟨k, LinstrR.Lret⟩] = false := rfl

/-- No zero store carries a `:64` width tag. -/
theorem bodyIsU64_zeroStores (body : Lcmd) : bodyIsU64 (zeroStores body) = false := by
  simp only [bodyIsU64, zeroStores]
  induction writtenFrameCells body with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.map_cons, List.any_cons, ih, zeroStore, Bool.or_false]
    decide +kernel

/-- **The spill stride is unchanged.** `bodyIsU64` reads the same on the
    transformed body, so the spill-cell stride `frameSize` computes from it, and
    with it every rendered `k.N` offset, is the same. -/
theorem bodyIsU64_zeroizeBody {body : Lcmd} (h : endsWithLret body = true) :
    bodyIsU64 (zeroizeBody body) = bodyIsU64 body := by
  obtain ⟨k, hk⟩ := dropLast_append_Lret h
  have hb : bodyIsU64 body = bodyIsU64 (body.dropLast ++ [(⟨k, LinstrR.Lret⟩ : Linstr)]) :=
    congrArg bodyIsU64 hk.symm
  rw [zeroizeBody_eq_prefix_ret h, zeroizePrefix, hb, bodyIsU64_append, bodyIsU64_append,
    bodyIsU64_append, bodyIsU64_zeroStores, bodyIsU64_Lret, bodyIsU64_Lret]
  simp

/-! ## 5. Applying the pass to an `Lprog`

`zeroizeLfundef` runs the pass on one function's body; `zeroizeLprog` maps it over
every function, leaving every other field of the program and of each `Lfundef`
untouched. -/

/-- Run the stack-clearing pass on one function's body. -/
def zeroizeLfundef (f : Lfundef) : Lfundef :=
  { f with lfd_body := zeroizeBody f.lfd_body }

/-- **The stack-clearing pass on a program.** Every function body gains its
    frame-clearing stores; every other field is preserved. -/
def zeroizeLprog (p : Lprog) : Lprog :=
  { p with lp_funcs := p.lp_funcs.map (fun (n, f) => (n, zeroizeLfundef f)) }

/-- The pass preserves the function signature: arguments, argument and result
    widths, results, the callee-saved list, and the frame fields are unchanged;
    only `lfd_body` differs. -/
theorem zeroizeLfundef_sig (f : Lfundef) :
    (zeroizeLfundef f).lfd_arg = f.lfd_arg ∧
    (zeroizeLfundef f).lfd_tyin = f.lfd_tyin ∧
    (zeroizeLfundef f).lfd_res = f.lfd_res ∧
    (zeroizeLfundef f).lfd_tyout = f.lfd_tyout ∧
    (zeroizeLfundef f).lfd_export = f.lfd_export ∧
    (zeroizeLfundef f).lfd_callee_saved = f.lfd_callee_saved ∧
    (zeroizeLfundef f).lfd_stk_max = f.lfd_stk_max ∧
    (zeroizeLfundef f).lfd_frame_size = f.lfd_frame_size ∧
    (zeroizeLfundef f).lfd_align = f.lfd_align ∧
    (zeroizeLfundef f).lfd_align_args = f.lfd_align_args :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Every function of the transformed program is the transformed function of the
    source program under the same name; `lp_rip`, `lp_rsp`, `lp_globs`, and
    `lp_glob_names` are unchanged. -/
theorem zeroizeLprog_funcs (p : Lprog) :
    (zeroizeLprog p).lp_funcs = p.lp_funcs.map (fun nf => (nf.1, zeroizeLfundef nf.2)) := rfl

/-- The program's register and global fields are unchanged. -/
theorem zeroizeLprog_fields (p : Lprog) :
    (zeroizeLprog p).lp_rip = p.lp_rip ∧
    (zeroizeLprog p).lp_rsp = p.lp_rsp ∧
    (zeroizeLprog p).lp_globs = p.lp_globs ∧
    (zeroizeLprog p).lp_glob_names = p.lp_glob_names :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## 6. Semantics

`JasminLsem.lsemStraight` runs the terminator-free instruction list; a frame cell
is an `lvm` entry keyed by its name (`memName`-shaped names and `k.N` / `qsave.X`
are `lvm` entries at this model's granularity), so "the cell holds zero at the
return" is a statement about the state `lsemStraight` reaches.

The whole body is `zeroizePrefix body ++ [Lret]`, and `JasminLsem.lsemRun_body_ret`
identifies running that under `lsemRun` with running `zeroizePrefix body` under
`lsemStraight`, so the results below are results about the state at the return. -/

/-- One zero store writes `0` to its cell and advances the pc. -/
theorem lsemStep_zeroStore {w : Nat} (n : String) (s : Lstate w) :
    lsemStep (zeroStore n).li_i s = some ((s.setReg n 0).nextPc) := by
  simp only [zeroStore, lsemStep, stripWidthTag_MOVQ, List.map_cons, List.map_nil,
    evalOperand, applyOpn_MOVQ]
  rfl

/-- **The zero stores run and clear their cells.** From any state, the list of
    zero stores for `cells` completes, leaves every name outside `cells` and the
    memory untouched, and puts `0` in every name in `cells`. -/
theorem lsemStraight_zeroStoresOf {w : Nat} :
    ∀ (cells : List String) (s : Lstate w),
    ∃ t : Lstate w, lsemStraight ((cells.map zeroStore).map Linstr.li_i) s = some t
      ∧ (∀ n ∈ cells, t.lvm n = 0)
      ∧ (∀ n, n ∉ cells → t.lvm n = s.lvm n)
      ∧ t.lmem = s.lmem := by
  intro cells
  induction cells with
  | nil => intro s; exact ⟨s, rfl, by simp, fun _ _ => rfl, rfl⟩
  | cons a rest ih =>
    intro s
    obtain ⟨t, hrun, hzero, hframe, hmem⟩ := ih ((s.setReg a 0).nextPc)
    refine ⟨t, ?_, ?_, ?_, ?_⟩
    · simp only [List.map_cons, lsemStraight_cons, lsemStep_zeroStore, hrun]
    · intro n hn
      rcases List.mem_cons.1 hn with rfl | hn'
      · by_cases hr : n ∈ rest
        · exact hzero n hr
        · rw [hframe n hr]
          simp [Lstate.setReg]
      · exact hzero n hn'
    · intro n hn
      have hna : n ≠ a := fun he => hn (he ▸ List.mem_cons_self)
      have hnr : n ∉ rest := fun hm => hn (List.mem_cons_of_mem _ hm)
      rw [hframe n hnr]
      simp [Lstate.setReg, Lstate.nextPc, hna]
    · rw [hmem]; rfl

/-- **Value preservation.** Whenever the original terminator-free body completes,
    the transformed one completes from the same start state and reaches a state
    that agrees with the original's on every name outside the census and has the
    same memory. The names in the census are the erased frame cells, and the
    theorem states exactly that they are what changed. -/
theorem zeroizePrefix_lsemStraight {w : Nat} (body : Lcmd) (s t : Lstate w)
    (h : lsemStraight (body.dropLast.map Linstr.li_i) s = some t) :
    ∃ t' : Lstate w, lsemStraight ((zeroizePrefix body).map Linstr.li_i) s = some t'
      ∧ (∀ n, n ∉ writtenFrameCells body → t'.lvm n = t.lvm n)
      ∧ (∀ n ∈ writtenFrameCells body, t'.lvm n = 0)
      ∧ t'.lmem = t.lmem := by
  obtain ⟨t', hrun, hzero, hframe, hmem⟩ :=
    lsemStraight_zeroStoresOf (w := w) (writtenFrameCells body) t
  refine ⟨t', ?_, hframe, hzero, hmem⟩
  rw [zeroizePrefix, zeroStores, List.map_append, lsemStraight_append, h]
  exact hrun

/-- **Erasure.** In the state the transformed body reaches at its return, every
    frame cell the body wrote holds `0`. -/
theorem zeroizePrefix_erases {w : Nat} (body : Lcmd) (s t' : Lstate w)
    (hs : ∃ t : Lstate w, lsemStraight (body.dropLast.map Linstr.li_i) s = some t)
    (h : lsemStraight ((zeroizePrefix body).map Linstr.li_i) s = some t') :
    ∀ n ∈ writtenFrameCells body, t'.lvm n = 0 := by
  obtain ⟨t, ht⟩ := hs
  obtain ⟨t'', hrun, _, hzero, _⟩ := zeroizePrefix_lsemStraight body s t ht
  rw [h] at hrun
  rw [← Option.some.inj hrun] at hzero
  exact hzero

/-- **Erasure at the whole-function return.** `lsemRun` on the transformed body
    ends at its `Lret`; the state it returns has `0` in every frame cell the body
    wrote. -/
theorem zeroizeBody_lsemRun_erases {w : Nat} (body : Lcmd)
    (hret : endsWithLret body = true) (hfree : LinstrR.Lret ∉ (zeroizePrefix body).map Linstr.li_i)
    (s t' : Lstate w)
    (hs : ∃ t : Lstate w, lsemStraight (body.dropLast.map Linstr.li_i) s = some t)
    (h : lsemRun ((zeroizeBody body).map Linstr.li_i) s = some t') :
    ∀ n ∈ writtenFrameCells body, t'.lvm n = 0 := by
  rw [zeroizeBody_eq_prefix_ret hret, List.map_append, List.map_cons, List.map_nil] at h
  rw [lsemRun_body_ret _ [] s hfree] at h
  exact zeroizePrefix_erases body s t' hs h

/-- A name that is not a frame cell reads the same after the pass as before: no
    caller-visible register and no caller-memory cell is touched. -/
theorem zeroizePrefix_preserves_nonFrame {w : Nat} (body : Lcmd) (s t t' : Lstate w)
    (h : lsemStraight (body.dropLast.map Linstr.li_i) s = some t)
    (h' : lsemStraight ((zeroizePrefix body).map Linstr.li_i) s = some t')
    {n : String} (hn : isFrameCell n = false) : t'.lvm n = t.lvm n := by
  obtain ⟨t'', hrun, hframe, _, _⟩ := zeroizePrefix_lsemStraight body s t h
  rw [h'] at hrun
  rw [Option.some.inj hrun]
  exact hframe n (not_mem_writtenFrameCells hn)

/-! ## 7. Pins

A two-instruction demonstration body: a spill write, an output store through the
restored out-pointer, and the terminator. The census picks up the spill slot and
not the caller-memory store, and the zero store renders as a quadword write to
the slot's frame offset. -/

/-- A body writing one spill slot and one caller-memory output cell, ending in
    the function-return terminator. -/
def demoBody : Lcmd :=
  [⟨0, .Lopn [.reg "k.0"] "MOV:64" [.reg "RAX"]⟩,
   ⟨0, .Lopn [.reg "mem.R14.0"] "MOV:64" [.reg "k.0"]⟩,
   ⟨0, .Lret⟩]

-- The census holds the spill slot and not the caller-memory output cell.
#guard writtenFrameCells demoBody == ["k.0"]

-- The pass appends one zero store and keeps the terminator last.
#guard (zeroizeBody demoBody).length == 4

#guard endsWithLret (zeroizeBody demoBody)

-- The added instruction is a quadword zero store to the censused cell.
#guard (zeroStores demoBody).map (fun i => reprStr i.li_i)
  == [reprStr (LinstrR.Lopn [.reg "k.0"] "MOVQ" [.imm 0])]

-- In a 128-byte frame with 8-byte spill cells, `k.0` sits at offset 56 and the
-- zero store renders as a quadword write there.
#guard renderLinstrR 128 64 (zeroStore "k.0").li_i == ["\tmovq $0, 56(%rsp)"]

-- The ABI save slot `qsave.RBX` sits at the top of the same frame.
#guard renderLinstrR 128 64 (zeroStore "qsave.RBX").li_i == ["\tmovq $0, 104(%rsp)"]

end CatCrypt.Crypto.SecureCompilation.X86Backend.StackZeroize
