/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionBackend
public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapComplete

@[expose] public section

/-!
# Definite assignment and forward reachability of the region export

The register allocator of the region back end assigns registers by live ranges taken in the
order of the text, and the gate `regCoB` checks its renaming against the dataflow liveness
table `liveRegTab`. The completeness of the gate needs that the text-order ranges cover the
dataflow liveness. This module proves two facts about the code of the region export `exportR`
on which that comparison rests.

## Paths

The control flow is the successor relation `webSuccs` of `ArrWebs`, under which
`liveRegTab` computes liveness: the next position for every instruction other than an
unconditional jump, and the position after the label for a jump. A path (`Path`) is a walk
along it from the entry position `0`.

## Definite assignment

`DefInit E code`: on every path, every name an instruction reads (`useNames`) is in `E` or is
written (`defNames`) at an earlier position of the path. A certificate (`Cert`) is a table of
names per position, empty at the entry, containing the names read at each position outside
`E`, and closed backwards along the edges up to the names an instruction writes. A
certificate gives definite assignment (`Cert.defInit`), and definite assignment has the
certificate of the names written on every path (`DefInit.cert`). Under a certificate, every
name of `liveRegTab` at a position is in the certificate there, in `E`, or the array
destination of a store or an array zeroing that does not read it (`liveRegTab_bound`); at the
entry the certificate is empty (`liveRegTab_entry`).

The certificate of the export is assembled by a block judgement (`Blk`) over a label table:
each label carries the names guaranteed after it, a jump requires them, and blocks compose by
concatenation (`Blk.append`). The judgement of an export (`exportR_blk`) is proved by
induction on the program, following `ExportRegions.exportR_alphabet`: every set `X`
containing the bindings in scope at the entry depth gives a judgement from `X` to the names of
`X` and the bindings in scope at the returned depth. The frames of the counted loop, the
exit-flag loop and the branch are proved from the blocks of their moves, guards and labels.

The names that may be read without a prior write (`ExportE`) are the argument names and the
symbol operands of the symbol-base loads `LOADSYM`, which carry a link-time symbol as a
register operand.

## Forward reachability and loop headers

The export contains no unconditional jump (`exportR_noGoto`), so every position is reached
by the walk along the next positions (`FwdPath`). The jumps are nested (`Nest`,
`exportR_nest`): for a back edge from `k` to a label at `p` and a jump to a label strictly
between `p` and `k`, the jump lies after `p` and up to `k`. Hence every back edge targets a
loop header (`LoopHeader`, `loopHeader_of_nest`): the positions after the one after the label
up to the back edge are entered only from inside the loop.

## The steps to the input of the allocation

Without a callee the allocation of `regionLprog` takes
`regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) []`, where `r` is the
webs `regionWebsAt ex none r0` of the export `r0`, and
`regionAllocCode C outs = backEdgePins (pinSelfMoves (C.map (renArr σ)))` at the coalescing
renaming `σ = canonMemrefName (aliasTab outs C)`. The certificates and the nesting are carried
through each step:

* the result copy: `Cert.append_blk`, `Cert.regionLprogCopy`, when the source and the buffer
  of the copy are definitely assigned or in `E`;
* the renaming of the array positions: `Cert.map`, `Cert.renRM`, and the certificate through
  the sorted namespace `RegionExportDefInitSort.Cert.renArrS`;
* the liveness instructions at the self-moves, at the same positions: `Cert.selfMovesPinned`
  (through `Cert.of_pointwise`: same successors, fewer reads, and every write of the
  replaced instruction kept or read by it) gives the certificate outside `E`,
  `pinSelfMoves_nest_noGoto` the nesting and `regDsts_pinSelfMoves` the register
  destinations;
* the liveness pins: `backEdgePins_eq` presents them as inserted operations
  (`insertBefore`, `insSpec`, `Cert.insertBefore`, `insertBefore_nest_noGoto`), and
  the pin of a jump from `k` to a label at `p < k` reads the names `backEdgePinNames`: the
  names exposed in the loop text, which `exposed_mustW` proves written on every path to `k`
  from definite assignment, nesting, the absence of unconditional jumps and register
  destinations (`RegDsts`, `exportR_regDsts`), and the names of `liveRegTab C []` at `p`.
  A name of the table is live after the label (`PLiveR`, `pLiveR_of_liveRegTab`), hence in
  the certificate after the label, in `E`, or of `ArrOnly` (`Cert.pLiveR`), and a name of
  the certificate after the label is written on every path to `k` (`MustW.loop`). An
  `ArrOnly` name need not be written on a path to `k`: it is live across a loop when the
  code after the loop zeroes or stores into that array before reading it, since
  `liveRegTab` does not count the array destination as a write. `backEdgePins_cert` gives
  the certificate at the names of `E` and of `ArrOnly`;
* the liveness instruction at entry `arrBasePins` (`entryPinRM`): it reads array bases of
  the argument slots and argument names live at entry, which the certificate bounds
  (`entryPin_defInit`).

`RegionExportDefInitSort.allocChain` and `RegionExportDefInitSort.regionAllocCode_chain`
compose the last three steps, and `RegionAllocMapLive.exportR_allocInput` the whole path from
`exportR`.

## Main results

* `exportR_defInit`: definite assignment of the export of a program from the depth and the
  argument count `Γ.length` and the label `0`, of its returned names at the end, and the bound
  of `liveRegTab` at the entry by the argument names, the symbol operands and the array
  destinations of `ArrOnly`.
* `exportR_fwdReach`: every position of an export is forward reachable, and every back edge
  targets a loop header.
* `DefInit.liveRegTab_entry`: the bound of `liveRegTab` at the entry under definite
  assignment.
* `webB_path`, `DefInit.webRen`, `DefInitOut.webRen`, `Cert.webRen`: along a path, a live
  name keeps its own name back to the entry or its web name is written on the path; hence
  definite assignment transfers to the webs `ArrWebs.webRen w ao` of a code accepted by
  `webB` whose register reads are written as registers on every path (`RegReads`).
* `RegionExp.noGoto`, `RegionExp.nest`, `RegionExp.fwdReach`, `RegionExp.labelsOK`,
  `RegionExp.cert`, `RegionExp.defInit`: the facts of the export at every code of
  `RegionExp`, the last two under `RegReads` of the export.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RegionExportDefInit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (findLabelMem IsLopn)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc (useNames defNames regDefs
  jumpLabel?)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ArrWebs (webSuccs)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize (x86Data x86Data_loopGuard
  x86Data_zeroTripGuard)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (IsaData callShadow)

/-! ## 1. Paths and definite assignment -/

/-- **A path of a code.** `Path code k ks` holds when the positions `ks`, the most recent
    first, followed by `k`, are a walk from the entry position `0` along the successor
    relation `webSuccs` of `code`: the next position for every instruction other than an
    unconditional jump, and the position after the label for a jump. This is the control
    flow under which `liveRegTab` computes liveness. -/
inductive Path (code : List LinstrRM) : Nat → List Nat → Prop
  /-- The empty walk at the entry. -/
  | nil : Path code 0 []
  /-- A walk extended by one edge. -/
  | cons {k s : Nat} {ks : List Nat} {i : LinstrRM} :
      Path code k ks → code[k]? = some i → s ∈ webSuccs code k i → Path code s (k :: ks)

/-- The name `r` is written at one of the positions `ks`: it is a destination name
    (`defNames`) of the instruction there. -/
def WrittenOn (code : List LinstrRM) (ks : List Nat) (r : String) : Prop :=
  ∃ j ∈ ks, ∃ i, code[j]? = some i ∧ r ∈ defNames i.1

/-- **Definite assignment.** On every path of `code`, every name an instruction reads
    (`useNames`) satisfies `E` or is written at an earlier position of the path. -/
def DefInit (E : String → Prop) (code : List LinstrRM) : Prop :=
  ∀ k ks i, Path code k ks → code[k]? = some i → ∀ r ∈ useNames i.1, E r ∨ WrittenOn code ks r

/-- **Definite assignment of the names read after the code.** On every path of `code` to its
    end, every name of `outs` satisfies `E` or is written on the path. -/
def DefInitOut (E : String → Prop) (code : List LinstrRM) (outs : List String) : Prop :=
  ∀ ks, Path code code.length ks → ∀ r ∈ outs, E r ∨ WrittenOn code ks r

/-- The names written on every path of `code` to the position `k`. -/
def MustW (code : List LinstrRM) (k : Nat) (r : String) : Prop :=
  ∀ ks, Path code k ks → WrittenOn code ks r

/-- **A certificate of definite assignment**: a table `D` of names for each position, empty at
    the entry, containing every name read at a position that is not in `E`, and such that a
    name at a successor of a position is at that position or written by its instruction. -/
structure Cert (E : String → Prop) (code : List LinstrRM) (D : Nat → String → Prop) :
    Prop where
  /-- The table is empty at the entry. -/
  entry : ∀ r, ¬ D 0 r
  /-- The names read at a position are in the table there or in `E`. -/
  use : ∀ k i, code[k]? = some i → ∀ r ∈ useNames i.1, D k r ∨ E r
  /-- A name at a successor is at the position or written there. -/
  step : ∀ k i, code[k]? = some i → ∀ s ∈ webSuccs code k i, ∀ r, D s r →
    D k r ∨ r ∈ defNames i.1

/-- The names of a certificate at a position are written on every path to it. -/
theorem Cert.written {E : String → Prop} {code : List LinstrRM} {D : Nat → String → Prop}
    (h : Cert E code D) {k : Nat} {ks : List Nat} (hp : Path code k ks) :
    ∀ r, D k r → WrittenOn code ks r := by
  induction hp with
  | nil => exact fun r hr => (h.entry r hr).elim
  | cons hp hi hs ih =>
      intro r hr
      rcases h.step _ _ hi _ hs r hr with h1 | h1
      · obtain ⟨j, hj, i', h2, h3⟩ := ih r h1
        exact ⟨j, List.mem_cons_of_mem _ hj, i', h2, h3⟩
      · exact ⟨_, List.mem_cons_self, _, hi, h1⟩

/-- A certificate gives definite assignment. -/
theorem Cert.defInit {E : String → Prop} {code : List LinstrRM} {D : Nat → String → Prop}
    (h : Cert E code D) : DefInit E code := by
  intro k ks i hp hi r hr
  rcases h.use k i hi r hr with h1 | h1
  · exact Or.inr (h.written hp r h1)
  · exact Or.inl h1

/-- A certificate gives definite assignment of the names it holds at the end. -/
theorem Cert.defInitOut {E : String → Prop} {code : List LinstrRM} {D : Nat → String → Prop}
    (h : Cert E code D) {outs : List String} (ho : ∀ r ∈ outs, D code.length r ∨ E r) :
    DefInitOut E code outs := by
  intro ks hp r hr
  rcases ho r hr with h1 | h1
  · exact Or.inr (h.written hp r h1)
  · exact Or.inl h1

/-- **Definite assignment has a certificate**: the names written on every path (`MustW`). -/
theorem DefInit.cert {E : String → Prop} {code : List LinstrRM} (h : DefInit E code) :
    Cert E code (MustW code) where
  entry r hr := by
    obtain ⟨j, hj, -⟩ := hr [] Path.nil
    simp at hj
  use k i hi r hr := by
    by_cases hE : E r
    · exact Or.inr hE
    · exact Or.inl fun ks hp => (h k ks i hp hi r hr).resolve_left hE
  step k i hi s hs r hr := by
    by_cases hd : r ∈ defNames i.1
    · exact Or.inr hd
    · refine Or.inl fun ks hp => ?_
      obtain ⟨j, hj, i', h1, h2⟩ := hr _ (Path.cons hp hi hs)
      rcases List.mem_cons.mp hj with rfl | hj
      · rw [hi] at h1
        cases h1
        exact absurd h2 hd
      · exact ⟨j, hj, i', h1, h2⟩

/-! ## 2. The register liveness table under a certificate -/

/-- The name `r` is written by an instruction of `code` that writes it as a name other than a
    register of the flag machine (`regDefs`) and does not read it: the array destination of a
    store or of an array zeroing. -/
def ArrOnly (code : List LinstrRM) (r : String) : Prop :=
  ∃ i ∈ code, r ∈ defNames i.1 ∧ r ∉ regDefs i ∧ r ∉ useNames i.1

/-- The bound of a liveness table under a certificate: the name is in the certificate, in
    `E`, or of `ArrOnly`. -/
def LiveBound (E : String → Prop) (code : List LinstrRM) (D : Nat → String → Prop)
    (k : Nat) (r : String) : Prop :=
  D k r ∨ E r ∨ ArrOnly code r

/-- The invariant of the passes: every name of the table at a position is in the bound. -/
def TabInv (E : String → Prop) (code : List LinstrRM) (D : Nat → String → Prop)
    (A : Array (List String)) : Prop :=
  ∀ k, ∀ r ∈ A.getD k [], LiveBound E code D k r

theorem defNames_nonLopn {w : LinstrR} (h : ∀ ds o ss, w ≠ .Lopn ds o ss) : defNames w = [] := by
  cases w <;> first | rfl | exact absurd rfl (h _ _ _)

/-- A name at a successor carried back over an instruction that does not write it. -/
theorem liveBound_back {E : String → Prop} {code : List LinstrRM} {D : Nat → String → Prop}
    (hC : Cert E code D) {k : Nat} {i : LinstrRM} (hi : code[k]? = some i) {s : Nat}
    (hs : s ∈ webSuccs code k i) {r : String} (hr : LiveBound E code D s r)
    (hd : r ∉ defNames i.1) : LiveBound E code D k r := by
  rcases hr with h | h | h
  · rcases hC.step k i hi s hs r h with h' | h'
    · exact Or.inl h'
    · exact absurd h' hd
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem mem_webSuccs_label {code : List LinstrRM} {k : Nat} {i : LinstrRM} {l : LLabel}
    {p : Nat} (hl : jumpLabel? i.1 = some l) (hp : findLabelMem l code = some p) :
    p + 1 ∈ webSuccs code k i := by
  rcases i with ⟨w, tag⟩
  cases w <;> simp_all [jumpLabel?, webSuccs]

/-- The names `liveRegNeed` adds at a position are in the bound. -/
theorem liveRegNeed_bound {E : String → Prop} {code : List LinstrRM} {D : Nat → String → Prop}
    (hC : Cert E code D) {A : Array (List String)} (hA : TabInv E code D A) {k : Nat}
    {i : LinstrRM} (hi : code[k]? = some i) :
    ∀ r ∈ liveRegNeed code A k i, LiveBound E code D k r := by
  have htgt : ∀ l r, jumpLabel? i.1 = some l →
      r ∈ (match findLabelMem l code with
        | some p => A.getD (p + 1) []
        | none => []) → defNames i.1 = [] → LiveBound E code D k r := by
    intro l r hl hr hd
    cases hf : findLabelMem l code with
    | none => simp [hf] at hr
    | some p =>
        simp only [hf] at hr
        exact liveBound_back hC hi (mem_webSuccs_label hl hf) (hA _ r hr) (by simp [hd])
  have hnext : ∀ r, r ∈ A.getD (k + 1) [] → defNames i.1 = [] →
      (∀ f l, i.1 ≠ .Lgoto (f, l)) → LiveBound E code D k r := by
    intro r hr hd hng
    refine liveBound_back hC hi ?_ (hA _ r hr) (by simp [hd])
    rcases i with ⟨w, tag⟩
    cases w with
    | Lgoto t =>
        obtain ⟨f, l⟩ := t
        exact absurd rfl (hng f l)
    | _ => simp [webSuccs]
  intro r hr
  rcases i with ⟨w, tag⟩
  cases w with
  | Lgoto t =>
      obtain ⟨f, l⟩ := t
      exact htgt l r rfl hr rfl
  | Lcond c l =>
      simp only [liveRegNeed, List.mem_append] at hr
      rcases hr with hr | hr
      · exact hnext r hr rfl (by simp)
      · exact htgt l r rfl hr rfl
  | Lopn ds o ss =>
      simp only [liveRegNeed, List.mem_append, List.mem_filter, Bool.not_eq_true',
        List.contains_eq_mem, decide_eq_false_iff_not] at hr
      rcases hr with hr | ⟨hr, hnd⟩
      · rcases hC.use k _ hi r hr with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · rcases hA _ r hr with h | h | h
        · rcases hC.step k _ hi (k + 1) (by simp [webSuccs]) r h with h' | h'
          · exact Or.inl h'
          · by_cases hu : r ∈ useNames (LinstrR.Lopn ds o ss)
            · rcases hC.use k _ hi r hu with h'' | h''
              · exact Or.inl h''
              · exact Or.inr (Or.inl h'')
            · exact Or.inr (Or.inr ⟨_, List.mem_of_getElem? hi, h', hnd, hu⟩)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
  | Lsyscall _ => exact hnext r hr rfl (by simp)
  | Lcall _ _ => exact hnext r hr rfl (by simp)
  | Lret => exact hnext r hr rfl (by simp)
  | Lalign => exact hnext r hr rfl (by simp)
  | Llabel _ _ => exact hnext r hr rfl (by simp)
  | Ligoto _ => exact hnext r hr rfl (by simp)
  | LstoreLabel _ _ => exact hnext r hr rfl (by simp)

theorem tabInv_setIfInBounds {E : String → Prop} {code : List LinstrRM}
    {D : Nat → String → Prop} {A : Array (List String)} (hA : TabInv E code D A) {k : Nat}
    {L : List String} (hL : ∀ r ∈ L, LiveBound E code D k r) :
    TabInv E code D (A.setIfInBounds k L) := by
  intro j r hr
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds] at hr
  split at hr
  · next h =>
      subst h
      split at hr
      · exact hL r (by simpa using hr)
      · exact hA _ r (by rw [Array.getD_eq_getD_getElem?]; simp at hr)
  · exact hA j r (by rw [Array.getD_eq_getD_getElem?]; exact hr)

theorem tabInv_liveRegPass {E : String → Prop} {code : List LinstrRM}
    {D : Nat → String → Prop} (hC : Cert E code D) {A : Array (List String)}
    (hA : TabInv E code D A) : TabInv E code D (liveRegPass code A) := by
  unfold liveRegPass
  induction List.range code.length with
  | nil => exact hA
  | cons k ks ih =>
      rw [List.foldr_cons]
      split
      · next i hi =>
          refine tabInv_setIfInBounds ih fun r hr => ?_
          rw [List.mem_eraseDups, List.mem_append] at hr
          rcases hr with hr | hr
          · exact ih k r hr
          · exact liveRegNeed_bound hC ih hi r hr
      · exact ih

theorem tabInv_liveRegIter {E : String → Prop} {code : List LinstrRM}
    {D : Nat → String → Prop} (hC : Cert E code D) :
    ∀ (fuel : Nat) {A : Array (List String)}, TabInv E code D A →
      TabInv E code D (liveRegIter code fuel A)
  | 0, _, hA => hA
  | fuel + 1, A, hA => by
      unfold liveRegIter
      dsimp only
      split
      · exact hA
      · exact tabInv_liveRegIter hC fuel (tabInv_liveRegPass hC hA)

/-- **The register liveness table under a certificate.** For a certificate `D` of definite
    assignment of `code` and names `outs` read after the code that are in `D` at the end or in
    `E`, every name of `liveRegTab code outs` at a position `k` is in `D k`, in `E`, or written
    by some instruction of `code` as an array destination it does not read (`ArrOnly`). -/
theorem liveRegTab_bound {E : String → Prop} {code : List LinstrRM}
    {D : Nat → String → Prop} (hC : Cert E code D) {outs : List String}
    (ho : ∀ r ∈ outs, D code.length r ∨ E r) :
    ∀ k, ∀ r ∈ tabAt (liveRegTab code outs) k, LiveBound E code D k r := by
  unfold tabAt liveRegTab
  refine tabInv_liveRegIter hC _ ?_
  intro j r hr
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds] at hr
  split at hr
  · next h =>
      subst h
      simp only [Array.size_replicate, Nat.lt_add_one, ↓reduceIte, Option.getD_some] at hr
      rcases ho r hr with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  · simp only [Array.getElem?_replicate] at hr
    split at hr <;> simp at hr

/-- **The names live at the entry.** Under a certificate of definite assignment of `code`
    with the names `outs` read after it in the certificate at the end or in `E`, every name
    of `liveRegTab code outs` at the entry is in `E` or written by some instruction of `code`
    as an array destination it does not read. -/
theorem liveRegTab_entry {E : String → Prop} {code : List LinstrRM}
    {D : Nat → String → Prop} (hC : Cert E code D) {outs : List String}
    (ho : ∀ r ∈ outs, D code.length r ∨ E r) :
    ∀ r ∈ tabAt (liveRegTab code outs) 0, E r ∨ ArrOnly code r := by
  intro r hr
  rcases liveRegTab_bound hC ho 0 r hr with h | h
  · exact absurd h (hC.entry r)
  · exact h

/-- **The names live at the entry under definite assignment.** For a code with definite
    assignment at `E` and names `outs` read after it that are in `E` or written on every path
    to its end, every name of `liveRegTab code outs` at the entry is in `E` or the array
    destination of a store or an array zeroing of the code that does not read it. -/
theorem DefInit.liveRegTab_entry {E : String → Prop} {code : List LinstrRM}
    (h : DefInit E code) {outs : List String}
    (ho : ∀ r ∈ outs, E r ∨ MustW code code.length r) :
    ∀ x ∈ tabAt (liveRegTab code outs) 0, E x ∨ ArrOnly code x :=
  RegionExportDefInit.liveRegTab_entry h.cert fun r hr => (ho r hr).elim Or.inr Or.inl

/-! ## 3. Certificates of blocks -/

/-- An unconditional jump. -/
def isGoto : LinstrR → Bool
  | .Lgoto _ => true
  | _ => false

/-- **A certificate of a block** `c` at the label table `Λ`: the table `D` of names at each
    position of the block contains the names read there that are not in `E`; a name at the
    next position is at the position or written there, unless the instruction is an
    unconditional jump; a name after a label `l` is in `Λ l`; and the names `Λ l` of the
    label a jump names are at the jump. -/
structure LCert (E : String → Prop) (Λ : LLabel → String → Prop) (c : List LinstrRM)
    (D : Nat → String → Prop) : Prop where
  /-- The names read are in the table or in `E`. -/
  use : ∀ j i, c[j]? = some i → ∀ r ∈ useNames i.1, D j r ∨ E r
  /-- The names at the next position are at the position or written there. -/
  fall : ∀ j i, c[j]? = some i → isGoto i.1 = false → ∀ r, D (j + 1) r →
    D j r ∨ r ∈ defNames i.1
  /-- The names after a label are in its table. -/
  lab : ∀ j i, c[j]? = some i → ∀ l, labelOf? i.1 = some l → ∀ r, D (j + 1) r → Λ l r
  /-- The table of the label of a jump is at the jump. -/
  jmp : ∀ j i, c[j]? = some i → ∀ l, jumpLabel? i.1 = some l → ∀ r, Λ l r → D j r

/-- **The block judgement.** The block `c` has a certificate at the label table `Λ` whose
    names at the entry are in `X` and which contains the names `Y` at the end. -/
def Blk (E : String → Prop) (Λ : LLabel → String → Prop) (X : String → Prop)
    (c : List LinstrRM) (Y : String → Prop) : Prop :=
  ∃ D, LCert E Λ c D ∧ (∀ r, D 0 r → X r) ∧ ∀ r, Y r → D c.length r

variable {E : String → Prop} {Λ : LLabel → String → Prop}

theorem Blk.mono {X X' Y Y' : String → Prop} {c : List LinstrRM} (h : Blk E Λ X c Y)
    (hX : ∀ r, X r → X' r) (hY : ∀ r, Y' r → Y r) : Blk E Λ X' c Y' := by
  obtain ⟨D, hD, h0, h1⟩ := h
  exact ⟨D, hD, fun r hr => hX r (h0 r hr), fun r hr => h1 r (hY r hr)⟩

theorem Blk.monoE {E' : String → Prop} {X Y : String → Prop} {c : List LinstrRM}
    (h : Blk E Λ X c Y) (hE : ∀ r, E r → E' r) : Blk E' Λ X c Y := by
  obtain ⟨D, hD, h0, h1⟩ := h
  refine ⟨D, ⟨fun j i hi r hr => ?_, hD.fall, hD.lab, hD.jmp⟩, h0, h1⟩
  rcases hD.use j i hi r hr with h | h
  · exact Or.inl h
  · exact Or.inr (hE r h)

theorem blk_nil {X Y : String → Prop} (h : ∀ r, Y r → X r) : Blk E Λ X [] Y :=
  ⟨fun _ => X, ⟨fun _ _ hi => by simp at hi, fun _ _ hi => by simp at hi,
    fun _ _ hi => by simp at hi, fun _ _ hi => by simp at hi⟩, fun _ h => h, h⟩

theorem blk_single {X Y : String → Prop} (i : LinstrRM)
    (hu : ∀ r ∈ useNames i.1, X r ∨ E r)
    (hf : isGoto i.1 = false → ∀ r, Y r → X r ∨ r ∈ defNames i.1)
    (hl : ∀ l, labelOf? i.1 = some l → ∀ r, Y r → Λ l r)
    (hj : ∀ l, jumpLabel? i.1 = some l → ∀ r, Λ l r → X r) : Blk E Λ X [i] Y := by
  refine ⟨fun j => if j = 0 then X else Y, ⟨?_, ?_, ?_, ?_⟩, fun r h => by simpa using h,
    fun r h => by simpa using h⟩
  · intro j i' hi r hr
    obtain ⟨rfl, rfl⟩ : j = 0 ∧ i' = i := by
      cases j <;> simp_all
    simpa using hu r hr
  · intro j i' hi hg r hr
    obtain ⟨rfl, rfl⟩ : j = 0 ∧ i' = i := by
      cases j <;> simp_all
    simpa using hf hg r (by simpa using hr)
  · intro j i' hi l hl' r hr
    obtain ⟨rfl, rfl⟩ : j = 0 ∧ i' = i := by
      cases j <;> simp_all
    exact hl l hl' r (by simpa using hr)
  · intro j i' hi l hl' r hr
    obtain ⟨rfl, rfl⟩ : j = 0 ∧ i' = i := by
      cases j <;> simp_all
    simpa using hj l hl' r hr

theorem Blk.append {X Y Z : String → Prop} {c₁ c₂ : List LinstrRM} (h₁ : Blk E Λ X c₁ Y)
    (h₂ : Blk E Λ Y c₂ Z) : Blk E Λ X (c₁ ++ c₂) Z := by
  obtain ⟨D₁, hD₁, h10, h11⟩ := h₁
  obtain ⟨D₂, hD₂, h20, h21⟩ := h₂
  let D : Nat → String → Prop := fun j => if j < c₁.length then D₁ j else D₂ (j - c₁.length)
  -- the table at the next position is contained in that of the first block
  have hnext : ∀ j, j < c₁.length → ∀ r, D (j + 1) r → D₁ (j + 1) r := by
    intro j hj r hr
    simp only [D] at hr
    split at hr
    · exact hr
    · have : j + 1 = c₁.length := by omega
      rw [this]
      exact h11 r (h20 r (by rw [show j + 1 - c₁.length = 0 by omega] at hr; exact hr))
  refine ⟨D, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro j i hi r hr
    by_cases hj : j < c₁.length
    · rw [List.getElem?_append_left hj] at hi
      simpa [D, hj] using hD₁.use j i hi r hr
    · rw [List.getElem?_append_right (by omega)] at hi
      simpa [D, hj] using hD₂.use _ i hi r hr
  · intro j i hi hg r hr
    by_cases hj : j < c₁.length
    · rw [List.getElem?_append_left hj] at hi
      simpa [D, hj] using hD₁.fall j i hi hg r (hnext j hj r hr)
    · rw [List.getElem?_append_right (by omega)] at hi
      have hr' : D₂ (j - c₁.length + 1) r := by
        simp only [D, show ¬ j + 1 < c₁.length by omega, ↓reduceIte] at hr
        rwa [show j + 1 - c₁.length = j - c₁.length + 1 by omega] at hr
      simpa [D, hj] using hD₂.fall _ i hi hg r hr'
  · intro j i hi l hl r hr
    by_cases hj : j < c₁.length
    · rw [List.getElem?_append_left hj] at hi
      exact hD₁.lab j i hi l hl r (hnext j hj r hr)
    · rw [List.getElem?_append_right (by omega)] at hi
      have hr' : D₂ (j - c₁.length + 1) r := by
        simp only [D, show ¬ j + 1 < c₁.length by omega, ↓reduceIte] at hr
        rwa [show j + 1 - c₁.length = j - c₁.length + 1 by omega] at hr
      exact hD₂.lab _ i hi l hl r hr'
  · intro j i hi l hl r hr
    by_cases hj : j < c₁.length
    · rw [List.getElem?_append_left hj] at hi
      simpa [D, hj] using hD₁.jmp j i hi l hl r hr
    · rw [List.getElem?_append_right (by omega)] at hi
      simpa [D, hj] using hD₂.jmp _ i hi l hl r hr
  · intro r hr
    simp only [D] at hr
    split at hr
    · exact h10 r hr
    · have h0 : c₁.length = 0 := by omega
      rw [h0, Nat.sub_zero] at hr
      have := h11 r (h20 r hr)
      rw [h0] at this
      exact h10 r this
  · intro r hr
    simp only [D, List.length_append, show ¬ c₁.length + c₂.length < c₁.length by omega,
      ↓reduceIte, Nat.add_sub_cancel_left]
    exact h21 r hr

theorem Blk.cons {X Y Z : String → Prop} {i : LinstrRM} {c : List LinstrRM}
    (h₁ : Blk E Λ X [i] Y) (h₂ : Blk E Λ Y c Z) : Blk E Λ X (i :: c) Z :=
  Blk.append h₁ h₂

theorem jumpLabel?_eq_jumpTarget? (w : LinstrR) : jumpLabel? w = jumpTarget? w := by
  cases w <;> rfl

/-- The block judgement reads the label table only at the labels the block declares and the
    labels its jumps name. -/
theorem Blk.congrΛ {Λ' : LLabel → String → Prop} {X Y : String → Prop} {c : List LinstrRM}
    (h : Blk E Λ X c Y) (hl : ∀ l ∈ labelsOf c, Λ' l = Λ l)
    (ht : ∀ l ∈ targetsOf c, Λ' l = Λ l) : Blk E Λ' X c Y := by
  obtain ⟨D, hD, h0, h1⟩ := h
  refine ⟨D, ⟨hD.use, hD.fall, fun j i hi l hl' r hr => ?_, fun j i hi l hl' r hr => ?_⟩,
    h0, h1⟩
  · have hm : l ∈ labelsOf c :=
      List.mem_filterMap.mpr ⟨i, List.mem_of_getElem? hi, hl'⟩
    rw [hl l hm]
    exact hD.lab j i hi l hl' r hr
  · have hm : l ∈ targetsOf c :=
      List.mem_filterMap.mpr ⟨i, List.mem_of_getElem? hi, by
        rw [← jumpLabel?_eq_jumpTarget?]; exact hl'⟩
    rw [ht l hm] at hr
    exact hD.jmp j i hi l hl' r hr

/-- The label a label position of `findLabelMem` declares. -/
theorem findLabelMem_label {code : List LinstrRM} {l : LLabel} {p : Nat}
    (h : findLabelMem l code = some p) :
    ∃ i, code[p]? = some i ∧ labelOf? i.1 = some l := by
  obtain ⟨w, hw, hl⟩ := JasminLsemLabeled.findLabel_sound l _ p h
  rw [List.getElem?_map] at hw
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hw
  refine ⟨i, hi, ?_⟩
  rcases i with ⟨w, tag⟩
  cases w <;> simp_all [JasminLsemLabeled.isLabel, labelOf?]

/-- **A certificate of the whole code from a block judgement** with no names at the entry. -/
theorem cert_of_blk {code : List LinstrRM} {Y : String → Prop}
    (h : Blk E Λ (fun _ => False) code Y) :
    ∃ D, Cert E code D ∧ ∀ r, Y r → D code.length r := by
  obtain ⟨D, hD, h0, h1⟩ := h
  refine ⟨D, ⟨fun r hr => h0 r hr, hD.use, ?_⟩, h1⟩
  intro k i hi s hs r hr
  have hjump : ∀ l p, jumpLabel? i.1 = some l → findLabelMem l code = some p → s = p + 1 →
      D k r ∨ r ∈ defNames i.1 := by
    intro l p hl hp hs'
    subst hs'
    obtain ⟨i', hi', hl'⟩ := findLabelMem_label hp
    exact Or.inl (hD.jmp k i hi l hl r (hD.lab p i' hi' l hl' r hr))
  rcases i with ⟨w, tag⟩
  cases w with
  | Lgoto t =>
      obtain ⟨f, l⟩ := t
      simp only [webSuccs, List.mem_map, Option.mem_toList] at hs
      obtain ⟨p, hp, rfl⟩ := hs
      exact hjump l p rfl hp rfl
  | Lcond c l =>
      simp only [webSuccs, List.mem_cons, List.mem_map, Option.mem_toList] at hs
      rcases hs with rfl | ⟨p, hp, rfl⟩
      · exact hD.fall k _ hi rfl r hr
      · exact hjump l p rfl hp rfl
  | _ =>
      simp only [webSuccs, List.mem_singleton] at hs
      subst hs
      exact hD.fall k _ hi rfl r hr

/-! ## 4. Blocks of the frame instructions -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (opNames)

@[simp] theorem useNames_Lopn (ds : List LOperand) (o : String) (ss : List LOperand) :
    useNames (.Lopn ds o ss) = ss.flatMap opNames := rfl

@[simp] theorem defNames_Lopn (ds : List LOperand) (o : String) (ss : List LOperand) :
    defNames (.Lopn ds o ss) = ds.flatMap opNames := rfl

/-- The block of one operation that reads names of `X` or `E` and is followed by the names
    of `X` and the names it writes. -/
theorem blk_opn {X : String → Prop} (ds : List LOperand) (o : String) (ss : List LOperand)
    (tag : MemTag) (hs : ∀ x ∈ ss.flatMap opNames, X x ∨ E x) :
    Blk E Λ X [(.Lopn ds o ss, tag)] (fun r => X r ∨ r ∈ ds.flatMap opNames) :=
  blk_single _ (by simpa using hs) (fun _ r hr => by simpa using hr)
    (by simp [labelOf?]) (by simp [jumpLabel?])

/-- The block of a move. -/
theorem blk_movI {X : String → Prop} (dst : String) (src : LOperand)
    (hs : ∀ x ∈ opNames src, X x ∨ E x) :
    Blk E Λ X [movI dst src] (fun r => X r ∨ r = dst) :=
  (blk_opn (Λ := Λ) _ _ [src] _ (by simpa using hs)).mono (fun _ h => h)
    (fun r hr => by rcases hr with h | h <;> simp_all [opNames])

/-- The block of a list of moves whose sources read names of `X` or `E`. -/
theorem blk_movs {α : Type} (f : α → String) (g : α → LOperand) :
    ∀ (l : List α) {X : String → Prop}, (∀ a ∈ l, ∀ x ∈ opNames (g a), X x ∨ E x) →
      Blk E Λ X (l.map fun a => movI (f a) (g a)) (fun r => X r ∨ ∃ a ∈ l, r = f a)
  | [], X, _ => blk_nil fun r hr => by simpa using hr
  | a :: l, X, hs => by
      refine Blk.cons (blk_movI (f a) (g a) (hs a List.mem_cons_self)) ?_
      refine (blk_movs f g l (X := fun r => X r ∨ r = f a) fun b hb x hx => ?_).mono
        (fun _ h => h) fun r hr => ?_
      · rcases hs b (List.mem_cons_of_mem _ hb) x hx with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rcases hr with h | ⟨b, hb, rfl⟩
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.mp hb with rfl | hb
          · exact Or.inl (Or.inr rfl)
          · exact Or.inr ⟨b, hb, rfl⟩

/-- The block of an array move with the index register in `X` and the source in `X` or
    `E`: it is followed by the names of `X` and the target. -/
theorem blk_arrMove {X : String → Prop} (z t : String) (a : ArrMove) (hz : X z)
    (hs : X a.src ∨ E a.src) : Blk E Λ X (arrMove z t a) (fun r => X r ∨ r = a.dst) := by
  refine Blk.cons (blk_opn (Λ := Λ) _ _ _ _ (fun x hx => ?_))
    ((blk_opn (Λ := Λ) _ _ _ _ (fun x hx => ?_)).mono (fun _ h => h) fun r hr => ?_)
  · simp only [List.flatMap_cons, List.flatMap_nil, opNames, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hs
    · exact Or.inl hz
  · simp only [List.flatMap_cons, List.flatMap_nil, opNames, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false, List.cons_append, List.nil_append] at hx
    rcases hx with rfl | rfl | rfl
    · rcases hs with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · exact Or.inl (Or.inl hz)
    · exact Or.inl (Or.inr (by simp [opNames]))
  · rcases hr with h | rfl
    · exact Or.inl (Or.inl h)
    · exact Or.inr (by simp [opNames])

/-- The block of a list of array moves. -/
theorem blk_arrMoves (z t : String) :
    ∀ (mv : List ArrMove) {X : String → Prop}, X z → (∀ a ∈ mv, X a.src ∨ E a.src) →
      Blk E Λ X (arrMoves z t mv) (fun r => X r ∨ ∃ a ∈ mv, r = a.dst)
  | [], X, _, _ => blk_nil fun r hr => by simpa using hr
  | a :: mv, X, hz, hs => by
      refine Blk.append (blk_arrMove z t a hz (hs a List.mem_cons_self)) ?_
      refine (blk_arrMoves z t mv (X := fun r => X r ∨ r = a.dst) (Or.inl hz)
        fun b hb => ?_).mono (fun _ h => h) fun r hr => ?_
      · rcases hs b (List.mem_cons_of_mem _ hb) with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rcases hr with h | ⟨b, hb, rfl⟩
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.mp hb with rfl | hb
          · exact Or.inl (Or.inr rfl)
          · exact Or.inr ⟨b, hb, rfl⟩

theorem mem_arrStage_dst {D : Nat} :
    ∀ {mv : List ArrMove} {a : ArrMove}, a ∈ arrStage D mv → ∃ j, a.dst = regName (D + j)
  | [], _, h => by simp [arrStage] at h
  | b :: mv, a, h => by
      simp only [arrStage, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨0, rfl⟩
      · obtain ⟨j, hj⟩ := mem_arrStage_dst h
        exact ⟨j + 1, by rw [hj]; congr 1; omega⟩

theorem mem_arrStage_src {D : Nat} :
    ∀ {mv : List ArrMove} {a : ArrMove}, a ∈ arrStage D mv → ∃ b ∈ mv, a.src = b.src
  | [], _, h => by simp [arrStage] at h
  | b :: mv, a, h => by
      simp only [arrStage, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨b, List.mem_cons_self, rfl⟩
      · obtain ⟨c, hc, hj⟩ := mem_arrStage_src h
        exact ⟨c, List.mem_cons_of_mem _ hc, hj⟩

theorem mem_arrCommit_src {D : Nat} :
    ∀ {mv : List ArrMove} {a : ArrMove}, a ∈ arrCommit D mv →
      ∃ b ∈ arrStage D mv, a.src = b.dst
  | [], _, h => by simp [arrCommit] at h
  | b :: mv, a, h => by
      simp only [arrCommit, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨⟨regName D, b.src, b.w, b.n⟩, by simp [arrStage], rfl⟩
      · obtain ⟨c, hc, hj⟩ := mem_arrCommit_src h
        exact ⟨c, by simp [arrStage, hc], hj⟩

theorem mem_arrCommit_dst {D : Nat} :
    ∀ {mv : List ArrMove} {b : ArrMove}, b ∈ mv → ∃ a ∈ arrCommit D mv, a.dst = b.dst
  | [], _, h => by simp at h
  | c :: mv, b, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨⟨b.dst, regName D, b.w, b.n⟩, by simp [arrCommit], rfl⟩
      · obtain ⟨a, ha, hj⟩ := mem_arrCommit_dst (D := D + 1) h
        exact ⟨a, by simp [arrCommit, ha], hj⟩

/-- The block of a parallel assignment of arrays: it is followed by the names of `X` and the
    targets. -/
theorem blk_arrParMoves (z t : String) (D : Nat) (mv : List ArrMove) {X : String → Prop}
    (hz : X z) (hs : ∀ a ∈ mv, X a.src ∨ E a.src) :
    Blk E Λ X (arrParMoves z t D mv) (fun r => X r ∨ ∃ a ∈ mv, r = a.dst) := by
  unfold arrParMoves
  split
  · exact blk_arrMoves z t mv hz hs
  · refine Blk.append (blk_arrMoves z t (arrStage D mv) hz fun a ha => ?_) ?_
    · obtain ⟨b, hb, he⟩ := mem_arrStage_src ha
      rw [he]
      exact hs b hb
    · refine (blk_arrMoves z t (arrCommit D mv) (Or.inl hz) fun a ha => ?_).mono
        (fun _ h => h) fun r hr => ?_
      · obtain ⟨b, hb, he⟩ := mem_arrCommit_src ha
        exact Or.inl (Or.inr ⟨b, hb, he⟩)
      · rcases hr with h | ⟨b, hb, rfl⟩
        · exact Or.inl (Or.inl h)
        · obtain ⟨a, ha, he⟩ := mem_arrCommit_dst (D := D) hb
          exact Or.inr ⟨a, ha, he.symm⟩

/-- The block of a parallel assignment of registers with at least as many operands as
    targets: it is followed by the names of `X` and the targets. -/
theorem blk_parMoves (D : Nat) (tgts : List String) (ops : List LOperand) {X : String → Prop}
    (hreg : ∀ o ∈ ops, o = .reg (JasminLsemWidthN.operandName o))
    (hs : ∀ o ∈ ops, X (JasminLsemWidthN.operandName o) ∨ E (JasminLsemWidthN.operandName o))
    (hlen : tgts.length ≤ ops.length) :
    Blk E Λ X (ExportRegions.parMoves D tgts ops) (fun r => X r ∨ r ∈ tgts) := by
  unfold ExportRegions.parMoves
  rw [stageMoves_eq_range D ops hreg, commitMoves_eq_range D tgts]
  refine Blk.append (blk_movs (fun j => regName (D + j))
    (fun j => .reg (JasminLsemWidthN.operandName (ops.getD j (.imm 0)))) _ fun j hj x hx => ?_)
    ((blk_movs (fun j => tgts.getD j "") (fun j => .reg (regName (D + j))) _
      fun j hj x hx => ?_).mono (fun _ h => h) fun r hr => ?_)
  · simp only [opNames, List.mem_singleton] at hx
    subst hx
    have hj' : j < ops.length := List.mem_range.mp hj
    have hm : ops.getD j (.imm 0) ∈ ops := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some]
      exact List.getElem_mem hj'
    exact hs _ hm
  · simp only [opNames, List.mem_singleton] at hx
    subst hx
    exact Or.inl (Or.inr ⟨j, List.mem_range.mpr (by have := List.mem_range.mp hj; omega), rfl⟩)
  · rcases hr with h | hr
    · exact Or.inl (Or.inl h)
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hr
      exact Or.inr ⟨j, List.mem_range.mpr hj, by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]⟩

theorem mem_arrPairs {tp : List (JasminTy × String × String)} {a : ArrMove}
    (h : a ∈ arrPairs tp) : ∃ p ∈ tp, a.dst = p.2.1 ∧ a.src = p.2.2 := by
  obtain ⟨p, hp, hq⟩ := List.mem_filterMap.mp h
  rcases p with ⟨ty, x, y⟩
  cases ty <;> simp at hq
  subst hq
  exact ⟨_, hp, rfl, rfl⟩

theorem mem_regPairs {tp : List (JasminTy × String × String)} {q : String × String}
    (h : q ∈ regPairs tp) : ∃ p ∈ tp, q = p.2 := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
  exact ⟨p, (List.mem_filter.mp hp).1, rfl⟩

/-- Every typed pair is an array pair or a register pair. -/
theorem pair_cover {tp : List (JasminTy × String × String)} {p : JasminTy × String × String}
    (hp : p ∈ tp) : (∃ a ∈ arrPairs tp, a.dst = p.2.1) ∨ (∃ q ∈ regPairs tp, q.1 = p.2.1) := by
  rcases p with ⟨ty, x, y⟩
  cases ty with
  | stackArr w n =>
      exact Or.inl ⟨⟨x, y, w, n⟩, List.mem_filterMap.mpr ⟨_, hp, rfl⟩, rfl⟩
  | _ => exact Or.inr ⟨(x, y), List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨hp, rfl⟩, rfl⟩, rfl⟩

/-- The block of typed moves: it is followed by the names of `X` and the targets. -/
theorem blk_typedMoves (z t : String) (tp : List (JasminTy × String × String))
    {X : String → Prop} (hz : X z) (hs : ∀ p ∈ tp, X p.2.2 ∨ E p.2.2) :
    Blk E Λ X (typedMoves z t tp) (fun r => X r ∨ ∃ p ∈ tp, r = p.2.1) := by
  unfold typedMoves regMoves
  refine Blk.append (blk_arrMoves z t (arrPairs tp) hz fun a ha => ?_)
    ((blk_movs (fun q => q.1) (fun q => .reg q.2) (regPairs tp) fun q hq x hx => ?_).mono
      (fun _ h => h) fun r hr => ?_)
  · obtain ⟨p, hp, -, he⟩ := mem_arrPairs ha
    rw [he]
    exact hs p hp
  · obtain ⟨p, hp, rfl⟩ := mem_regPairs hq
    simp only [opNames, List.mem_singleton] at hx
    subst hx
    rcases hs p hp with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
  · rcases hr with h | ⟨p, hp, rfl⟩
    · exact Or.inl (Or.inl h)
    · rcases pair_cover hp with ⟨a, ha, he⟩ | ⟨q, hq, he⟩
      · exact Or.inl (Or.inr ⟨a, ha, he.symm⟩)
      · exact Or.inr ⟨q, hq, he.symm⟩

/-- The targets of the typed pairs of a carried tuple are the carried names. -/
theorem carriedPairs_targets {cs : List JasminTy} {car : List String} {ops : List LOperand}
    (h1 : car.length = cs.length) (h2 : cs.length ≤ ops.length) :
    ∀ x ∈ car, ∃ p ∈ carriedPairs cs car ops, x = p.2.1 := by
  intro x hx
  have hm : ((carriedPairs cs car ops).map Prod.snd).map Prod.fst = car := by
    unfold carriedPairs
    rw [List.map_snd_zip (by simp; omega), List.map_fst_zip (by simp; omega)]
  rw [← hm] at hx
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
  exact ⟨p, hp, rfl⟩

/-- The sources of the typed pairs of a carried tuple are names of its operands. -/
theorem carriedPairs_sources {cs : List JasminTy} {car : List String} {ops : List LOperand}
    {p : JasminTy × String × String} (hp : p ∈ carriedPairs cs car ops) :
    ∃ o ∈ ops, p.2.2 = JasminLsemWidthN.operandName o := by
  have h1 := List.of_mem_zip hp
  have h2 := List.of_mem_zip h1.2
  obtain ⟨o, ho, he⟩ := List.mem_map.mp h2.2
  exact ⟨o, ho, he.symm⟩

theorem x86Data_selectMnemonic : x86Data.selectMnemonic = some "CMOV" := rfl

/-- The block of the widening of a bit into `r` on x86: it is followed by the names of `X`
    and `r`. -/
theorem blk_flagWord (r z : String) (op : LOperand) {X : String → Prop}
    (hs : ∀ x ∈ opNames op, X x ∨ E x) :
    Blk E Λ X (flagWord x86Data r z op) (fun x => X x ∨ x = r) := by
  unfold flagWord
  split
  · next f =>
      rw [x86Data_selectMnemonic]
      refine Blk.cons (blk_movI r (.imm 1) (by simp [opNames]))
        (Blk.cons (blk_movI z (.imm 0) (by simp [opNames])) ?_)
      refine (blk_opn _ _ _ _ fun x hx => ?_).mono (fun _ h => h) fun x hx => ?_
      · simp only [List.flatMap_cons, List.flatMap_nil, opNames, List.cons_append,
          List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · rcases hs x (by simp [opNames]) with h | h
          · exact Or.inl (Or.inl (Or.inl h))
          · exact Or.inr h
        · exact Or.inl (Or.inl (Or.inr rfl))
        · exact Or.inl (Or.inr rfl)
      · rcases hx with h | rfl
        · exact Or.inl (Or.inl (Or.inl h))
        · exact Or.inr (by simp [opNames])
  · exact blk_movI r op hs

theorem x86_zeroTrip (c : String) (t e : LLabel) :
    (x86Data.zeroTripGuard c t e).map guardI =
      [guardI (.Lopn [.reg c] (withWidthTag 64 "CMP") [.reg c, .imm 0]),
        guardI (.Lcond (.reg "Z") e)] := by
  rw [x86Data_zeroTripGuard]; rfl

theorem x86_loopGuard (c : String) (t : LLabel) :
    (x86Data.loopGuard c t).map guardI =
      [guardI (.Lopn [.reg c] (withWidthTag 64 "CMP") [.reg c, .imm 0]),
        guardI (.Lcond (.reg "NZ") t)] := by
  rw [x86Data_loopGuard]; rfl

/-- The block of a guard on `c` with a jump to `l`: `c` is in `X` and the table of `l` is in
    `X`. -/
theorem blk_guard (c : String) (cc : String) (l : LLabel) {X : String → Prop} (hc : X c)
    (hl : ∀ x, Λ l x → X x) :
    Blk E Λ X [guardI (.Lopn [.reg c] (withWidthTag 64 "CMP") [.reg c, .imm 0]),
      guardI (.Lcond (.reg cc) l)] X := by
  refine Blk.cons ((blk_opn _ _ _ _ fun x hx => ?_).mono (fun _ h => h) fun x hx => Or.inl hx)
    (blk_single _ (by simp [guardI, useNames]) (fun _ x hx => Or.inl hx) (by simp [guardI, labelOf?])
      (fun l' hl' x hx => ?_))
  · simp only [List.flatMap_cons, List.flatMap_nil, opNames,
      List.mem_singleton, List.append_nil] at hx
    subst hx
    exact Or.inl hc
  · simp only [guardI, jumpLabel?, Option.some.injEq] at hl'
    subst hl'
    exact hl x hx

/-- The block of a label `l`, followed by names `Y` of `X` and of the table of `l`. -/
theorem blk_label (l : LLabel) {X Y : String → Prop} (hX : ∀ x, Y x → X x)
    (hl : ∀ x, Y x → Λ l x) : Blk E Λ X [labelI l] Y :=
  blk_single _ (by simp [labelI, useNames]) (fun _ x hx => Or.inl (hX x hx))
    (fun l' hl' x hx => by
      simp only [labelI, labelOf?, Option.some.injEq] at hl'
      subst hl'
      exact hl x hx)
    (by simp [labelI, jumpLabel?])

/-- The block of the assignment of the results of a branch to the block
    `carriedRegs d rs.length`: it is followed by the names of `X` and that block. -/
theorem blk_ifResMoves (rs : List JasminTy) (d D : Nat) (ops : List LOperand)
    {X : String → Prop} (_hreg : ∀ o ∈ ops, o = .reg (JasminLsemWidthN.operandName o))
    (hs : ∀ o ∈ ops, X (JasminLsemWidthN.operandName o) ∨ E (JasminLsemWidthN.operandName o))
    (hlen : rs.length ≤ ops.length) :
    Blk E Λ X (ifResMoves rs d D ops) (fun r => X r ∨ r ∈ carriedRegs d rs.length) := by
  have hsrc : ∀ p ∈ ifResPairs rs d ops, X p.2.2 ∨ E p.2.2 := by
    intro p hp
    obtain ⟨o, ho, he⟩ := carriedPairs_sources hp
    rw [he]
    exact hs o ho
  have hpar : ∀ {X' : String → Prop}, (∀ x, X x → X' x) →
      Blk E Λ X' (ExportRegions.parMoves D ((regPairs (ifResPairs rs d ops)).map Prod.fst)
        ((regPairs (ifResPairs rs d ops)).map fun p => .reg p.2))
        (fun r => X' r ∨ r ∈ (regPairs (ifResPairs rs d ops)).map Prod.fst) := by
    intro X' hX'
    refine blk_parMoves D _ _ (fun o ho => ?_) (fun o ho => ?_) (by simp)
    · obtain ⟨q, -, rfl⟩ := List.mem_map.mp ho
      rfl
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ho
      obtain ⟨p, hp, rfl⟩ := mem_regPairs hq
      rcases hsrc p hp with h | h
      · exact Or.inl (hX' _ h)
      · exact Or.inr h
  have htgt : ∀ x ∈ carriedRegs d rs.length, ∃ p ∈ ifResPairs rs d ops, x = p.2.1 :=
    carriedPairs_targets (carriedRegs_length d rs.length) hlen
  unfold ifResMoves
  split
  · next he =>
      refine (hpar (fun _ h => h)).mono (fun _ h => h) fun r hr => ?_
      rcases hr with h | hr
      · exact Or.inl h
      · obtain ⟨p, hp, rfl⟩ := htgt r hr
        rcases pair_cover hp with ⟨a, ha, -⟩ | ⟨q, hq, he'⟩
        · rw [List.isEmpty_iff.mp he] at ha
          simp at ha
        · exact Or.inr (List.mem_map.mpr ⟨q, hq, he'⟩)
  · refine Blk.append (Blk.cons (blk_movI (regName (D + 1)) (.imm 0) (by simp [opNames]))
      (blk_arrParMoves _ _ D _ (Or.inr rfl) fun a ha => ?_)) ?_
    · obtain ⟨p, hp, -, he⟩ := mem_arrPairs ha
      rw [he]
      rcases hsrc p hp with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · refine (hpar fun _ h => Or.inl (Or.inl h)).mono (fun _ h => h) fun r hr => ?_
      rcases hr with h | hr
      · exact Or.inl (Or.inl (Or.inl h))
      · obtain ⟨p, hp, rfl⟩ := htgt r hr
        rcases pair_cover hp with ⟨a, ha, he'⟩ | ⟨q, hq, he'⟩
        · exact Or.inl (Or.inr ⟨a, ha, he'.symm⟩)
        · exact Or.inr (List.mem_map.mpr ⟨q, hq, he'⟩)

/-! ## 5. The names of the export -/

/-- An argument name of a function of `nArgs` arguments. -/
def ArgName (nArgs : Nat) (r : String) : Prop := ∃ j, j < nArgs ∧ r = argName j

/-- A name of a binding in scope at depth `d`: `regName j` with `nArgs ≤ j < d`. -/
def InScope (nArgs d : Nat) (r : String) : Prop := ∃ j, nArgs ≤ j ∧ j < d ∧ r = regName j

/-- The names a symbol-base load `LOADSYM` reads: its operand, a link-time symbol carried as a
    register operand. No other instruction has such names. -/
def symReads (i : LinstrRM) : List String :=
  match i.1 with
  | .Lopn _ o ss => if o = "LOADSYM" then ss.flatMap opNames else []
  | _ => []

/-- The names of `E` include the symbol operands of the code. -/
def SymOK (E : String → Prop) (code : List LinstrRM) : Prop :=
  ∀ i ∈ code, ∀ r ∈ symReads i, E r

/-- Operands that are registers naming an argument or a binding in scope at depth `d`. -/
def ResOK (nArgs d : Nat) (os : List LOperand) : Prop :=
  ∀ o ∈ os, ∃ x, o = .reg x ∧ (ArgName nArgs x ∨ InScope nArgs d x)

theorem InScope.mono {nArgs d d' : Nat} (h : d ≤ d') {r : String} (hr : InScope nArgs d r) :
    InScope nArgs d' r := by
  obtain ⟨j, h1, h2, rfl⟩ := hr
  exact ⟨j, h1, by omega, rfl⟩

theorem resolveVar_ok {nArgs d : Nat} {Γ : Ctxt jasminDialect} {τ : JasminTy}
    (v : Ctxt.Var Γ τ) (hΓ : Γ.length ≤ d) :
    ∃ x, resolveVar d nArgs argName (fun _ => none) v = .reg x
      ∧ (ArgName nArgs x ∨ InScope nArgs d x) := by
  have hv := JasminLsemSimulation.varIndex_lt v
  unfold resolveVar
  dsimp only
  split
  · exact ⟨_, rfl, Or.inl ⟨_, by assumption, rfl⟩⟩
  · exact ⟨_, rfl, Or.inr ⟨_, by omega, by omega, rfl⟩⟩

theorem exprArgsHV_ok {nArgs d : Nat} {Γ : Ctxt jasminDialect} (hΓ : Γ.length ≤ d) :
    ∀ {ts : List JasminTy} (vs : HVector (fun t => Ctxt.Var Γ t) ts),
      ResOK nArgs d (exprArgsHV d nArgs argName (fun _ => none) vs)
  | [], .nil => by simp [ResOK, exprArgsHV]
  | _ :: _, .cons v rest => by
      intro o ho
      rw [show exprArgsHV d nArgs argName (fun _ => none) (.cons v rest)
        = resolveVar d nArgs argName (fun _ => none) v
          :: exprArgsHV d nArgs argName (fun _ => none) rest from rfl, List.mem_cons] at ho
      rcases ho with rfl | ho
      · exact resolveVar_ok v hΓ
      · exact exprArgsHV_ok hΓ rest o ho

theorem exprArgs_go_ok {nArgs d : Nat} {Γ : Ctxt jasminDialect} (hΓ : Γ.length ≤ d) :
    ∀ {ts : List JasminTy} (vs : HVector (fun t => Ctxt.Var Γ t) ts),
      ResOK nArgs d (exprArgs.go d nArgs argName (fun _ => none) vs)
  | [], .nil => by simp [ResOK, exprArgs.go]
  | _ :: _, .cons v rest => by
      intro o ho
      rw [show exprArgs.go d nArgs argName (fun _ => none) (.cons v rest)
        = resolveVar d nArgs argName (fun _ => none) v
          :: exprArgs.go d nArgs argName (fun _ => none) rest from rfl, List.mem_cons] at ho
      rcases ho with rfl | ho
      · exact resolveVar_ok v hΓ
      · exact exprArgs_go_ok hΓ rest o ho

theorem ResOK.names {nArgs d : Nat} {os : List LOperand} (h : ResOK nArgs d os) :
    ∀ x ∈ os.flatMap opNames, ArgName nArgs x ∨ InScope nArgs d x := by
  intro x hx
  obtain ⟨o, ho, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨y, rfl, hy⟩ := h o ho
  simp only [opNames, List.mem_singleton] at hx
  subst hx
  exact hy

theorem ResOK.reg {nArgs d : Nat} {os : List LOperand} (h : ResOK nArgs d os) :
    ∀ o ∈ os, o = .reg (JasminLsemWidthN.operandName o) := by
  intro o ho
  obtain ⟨y, rfl, -⟩ := h o ho
  rfl

theorem ResOK.name {nArgs d : Nat} {os : List LOperand} (h : ResOK nArgs d os) :
    ∀ o ∈ os, ArgName nArgs (JasminLsemWidthN.operandName o)
      ∨ InScope nArgs d (JasminLsemWidthN.operandName o) := by
  intro o ho
  obtain ⟨y, rfl, hy⟩ := h o ho
  exact hy

theorem ResOK.mono {nArgs d d' : Nat} (hd : d ≤ d') {os : List LOperand}
    (h : ResOK nArgs d os) : ResOK nArgs d' os := by
  intro o ho
  obtain ⟨y, rfl, hy⟩ := h o ho
  exact ⟨y, rfl, hy.imp id (InScope.mono hd)⟩

/-- The instruction of an operation with the destination `dst`: an operation writing `dst`
    whose read names are names of its operands or, for a symbol-base load, its symbol. -/
theorem opToLinstrR_shape (op : JasminOp) (dst : String) (srcs : List LOperand) :
    ∃ o ss, opToLinstrR op dst srcs = .Lopn [.reg dst] o ss
      ∧ ∀ x ∈ ss.flatMap opNames, x ∈ srcs.flatMap opNames ∨ o = "LOADSYM" := by
  cases op <;> dsimp only [opToLinstrR] <;> (repeat' split) <;>
    first
    | exact ⟨_, _, rfl, fun x hx => Or.inl hx⟩
    | exact ⟨_, _, rfl, fun x hx => Or.inr rfl⟩
    | exact ⟨_, _, rfl, fun x hx => Or.inl (by simp_all [opNames])⟩

/-- The instruction of a binding at depth `d`: an operation writing `regName d` whose read
    names are names of its resolved operands or, for a symbol-base load, its symbol. -/
theorem bindOps_shape (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (d : Nat) :
    ∃ o ss tag, bindOps nArgs e d = [(.Lopn [.reg (regName d)] o ss, tag)]
      ∧ ∀ x ∈ ss.flatMap opNames,
        x ∈ (exprArgs d nArgs argName (fun _ => none) e).flatMap opNames ∨ o = "LOADSYM" := by
  simp only [bindOps, straightOpsMem]
  generalize exprArgs d nArgs argName (fun _ => none) e = src
  generalize e.op = op
  have hop := opToLinstrR_shape op (regName d) src
  obtain ⟨o, ss, he, hss⟩ := hop
  split
  all_goals first
    | exact ⟨o, ss, _, by rw [he], hss⟩
    | (split
       all_goals first
         | exact ⟨o, ss, _, by rw [he], hss⟩
         | exact ⟨_, _, _, rfl, fun x hx => Or.inl (by
              simp_all [opNames])⟩)

/-! ## 6. The block judgement of the export -/

theorem SymOK.append {E : String → Prop} {a b : List LinstrRM} (h : SymOK E (a ++ b)) :
    SymOK E a ∧ SymOK E b :=
  ⟨fun i hi => h i (List.mem_append_left _ hi), fun i hi => h i (List.mem_append_right _ hi)⟩

theorem blk_advance (idx ctr : String) {X : String → Prop} (h1 : X idx) (h2 : X ctr) :
    Blk E Λ X (advanceOps idx ctr) X := by
  unfold advanceOps
  refine Blk.cons ((blk_opn _ _ _ _ fun x hx => ?_).mono (fun _ h => h) fun x hx => Or.inl hx)
    ((blk_opn _ _ _ _ fun x hx => ?_).mono (fun _ h => h) fun x hx => Or.inl hx)
  · simp only [List.flatMap_cons, List.flatMap_nil, opNames,
      List.mem_singleton, List.append_nil] at hx
    subst hx
    exact Or.inl h1
  · simp only [List.flatMap_cons, List.flatMap_nil, opNames,
      List.mem_singleton, List.append_nil] at hx
    subst hx
    exact Or.inl h2

theorem mem_carriedRegs_of {d nCar m : Nat} (hm : m < nCar) :
    regName (d + m) ∈ carriedRegs d nCar :=
  mem_carriedRegs.mpr ⟨nCar - 1 - m, by omega, by congr 1; omega⟩

theorem regName_of_mem_carriedRegs {d nCar : Nat} {r : String} (h : r ∈ carriedRegs d nCar) :
    ∃ m, m < nCar ∧ r = regName (d + m) := by
  obtain ⟨j, hj, rfl⟩ := mem_carriedRegs.mp h
  exact ⟨nCar - 1 - j, by omega, rfl⟩

/-- The block judgement of a label table that agrees with `Λ'` on an interval containing the
    labels of an export. -/
theorem Blk.congr_range {Λ' : LLabel → String → Prop} {X Y : String → Prop} {c : List LinstrRM}
    {lo hi : Nat} (h : Blk E Λ' X c Y)
    (hr : ∀ l ∈ labelsOf c, lo ≤ l ∧ l < hi) (hcl : ∀ l ∈ targetsOf c, l ∈ labelsOf c)
    (hΛ : ∀ l, lo ≤ l → l < hi → Λ l = Λ' l) : Blk E Λ X c Y :=
  h.congrΛ (fun l hl => hΛ l (hr l hl).1 (hr l hl).2)
    (fun l hl => hΛ l (hr l (hcl l hl)).1 (hr l (hcl l hl)).2)

theorem exprArgs_ok {nArgs d : Nat} {Γ : Ctxt jasminDialect} {t : JasminTy} (hΓ : Γ.length ≤ d)
    (e : Expr jasminDialect Γ t) : ResOK nArgs d (exprArgs d nArgs argName (fun _ => none) e) :=
  exprArgs_go_ok hΓ e.args

theorem blk_seed1 {X : String → Prop} (c : String) (o : LOperand)
    (h : ∀ x ∈ opNames o, X x ∨ E x) : Blk E Λ X (seedMoves [c] [o]) (fun x => X x ∨ x = c) :=
  blk_movI c o h

/-- A good name of a resolved operand list is in `X` or `E`. -/
theorem good_of_resOK {nArgs d : Nat} {X : String → Prop} (hE : ∀ x, ArgName nArgs x → E x)
    (hX : ∀ x, InScope nArgs d x → X x) {os : List LOperand} (h : ResOK nArgs d os) :
    ∀ o ∈ os, X (JasminLsemWidthN.operandName o) ∨ E (JasminLsemWidthN.operandName o) := by
  intro o ho
  rcases h.name o ho with h' | h'
  · exact Or.inr (hE _ h')
  · exact Or.inl (hX _ h')

theorem shiftPairs_sources {d : Nat} {cs : List JasminTy} {p : JasminTy × String × String}
    (hp : p ∈ shiftPairs d cs) : p.2.2 ∈ carriedRegs (d + 1) cs.length := by
  unfold shiftPairs at hp
  have h1 := List.of_mem_zip (List.mem_reverse.mp hp)
  exact (List.of_mem_zip h1.2).2

/-- **The block judgement of the export.** For an export `r` of a program over a context of
    length at most `d`, the returned operands are argument names or bindings in scope at the
    returned depth; and for every set `E` containing the argument names and the symbol
    operands of the code, and every set `X` containing the bindings in scope at `d`, the code
    has a block certificate from `X` to the names of `X` and the bindings in scope at the
    returned depth, at some label table. -/
theorem exportR_blk (nArgs : Nat) (fn : String) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) :
    ∀ (d n : Nat) (r : Exported), exportR nArgs fn p d n x86Data = some r → Γ.length ≤ d →
      ResOK nArgs r.depth r.res ∧
      ∀ (E : String → Prop), (∀ x, ArgName nArgs x → E x) → SymOK E r.code →
        ∀ (X : String → Prop), (∀ x, InScope nArgs d x → X x) →
          ∃ Λ : LLabel → String → Prop,
            Blk E Λ X r.code (fun x => X x ∨ InScope nArgs r.depth x) := by
  induction p with
  | ret vs =>
      intro d n r h hΓ
      simp only [exportR, Option.some.injEq] at h
      subst h
      refine ⟨exprArgsHV_ok hΓ vs, fun E hE hS X hX => ⟨fun _ _ => False, blk_nil fun x hx => ?_⟩⟩
      rcases hx with hx | hx
      · exact hx
      · exact hX x hx
  | var e k ih =>
      intro d n r h hΓ
      simp only [exportR, Option.map_eq_some_iff] at h
      obtain ⟨rk, hk, rfl⟩ := h
      obtain ⟨hres, hK⟩ := ih (d + 1) n rk hk (by simp only [List.length_cons]; omega)
      refine ⟨hres, fun E hE hS X hX => ?_⟩
      obtain ⟨o, ss, tag, hb, hss⟩ := bindOps_shape nArgs e d
      simp only [Exported.prepend] at hS ⊢
      rw [hb] at hS ⊢
      have hS' := SymOK.append (a := [_]) hS
      have hX1 : ∀ x, InScope nArgs (d + 1) x → X x ∨ x = regName d := by
        rintro x ⟨j, h1, h2, rfl⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h2 | rfl
        · exact Or.inl (hX _ ⟨j, h1, h2, rfl⟩)
        · exact Or.inr rfl
      obtain ⟨Λ, hB⟩ := hK E hE hS'.2 _ hX1
      refine ⟨Λ, Blk.cons ((blk_opn _ _ _ _ fun x hx => ?_).mono (fun _ h => h) fun x hx => ?_)
        (hB.mono (fun _ h => h) fun x hx => ?_)⟩
      · rcases hss x hx with hx' | ho
        · rcases (exprArgs_ok hΓ e).names x hx' with h' | h'
          · exact Or.inr (hE _ h')
          · exact Or.inl (hX _ h')
        · exact Or.inr (hS'.1 _ List.mem_cons_self x (by simp [symReads, ho, hx]))
      · rcases hx with h' | rfl
        · exact Or.inl h'
        · exact Or.inr (by simp [opNames])
      · rcases hx with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
  | @call Γ as rs ts f args k ih =>
      intro d n r h hΓ
      obtain ⟨hw, rk, hk, rfl⟩ := exportR_call_eq_some.mp h
      have hrs : rs.length = 1 := by
        rcases ((wordSig_iff).mp hw).2 with rfl | ⟨m, rfl⟩ <;> rfl
      obtain ⟨hres, hK⟩ := ih (d + rs.length) n rk hk (by simp only [List.length_append]; omega)
      refine ⟨hres, fun E hE hS X hX => ?_⟩
      simp only [Exported.prepend] at hS ⊢
      have hS' := SymOK.append (a := [_]) hS
      have hX1 : ∀ x, InScope nArgs (d + rs.length) x → X x ∨ x = regName d := by
        rintro x ⟨j, h1, h2, rfl⟩
        rw [hrs] at h2
        rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h2 | rfl
        · exact Or.inl (hX _ ⟨j, h1, h2, rfl⟩)
        · exact Or.inr rfl
      obtain ⟨Λ, hB⟩ := hK E hE hS'.2 _ hX1
      refine ⟨Λ, Blk.cons ((blk_opn (Λ := Λ) [.reg (regName d)] ("CALL:" ++ f) _ (.reg none)
        fun x hx => ?_).mono (fun _ h => h) fun x hx => ?_) (hB.mono (fun _ h => h)
          fun x hx => ?_)⟩
      · rcases (exprArgsHV_ok hΓ args).names x hx with h' | h'
        · exact Or.inr (hE _ h')
        · exact Or.inl (hX _ h')
      · rcases hx with h' | rfl
        · exact Or.inl h'
        · exact Or.inr (by simp [opNames])
      · rcases hx with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
  | @forLoop Γ cs ts count inits body k ihb ihk =>
      intro d n r h hΓ
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hk, rfl⟩ := h
      obtain ⟨hresB, hB⟩ := ihb _ _ b hb
        (by simp only [List.length_append, List.length_cons]; omega)
      obtain ⟨hresK, hK⟩ := ihk _ _ rk hk (by simp only [List.length_append]; omega)
      refine ⟨hresK, fun E hE hS X hX => ?_⟩
      simp only [Exported.prepend] at hS ⊢
      have hSF := SymOK.append hS
      have hLb := exportR_labelsOK nArgs fn x86Data_guardsPlain body _ _ b hb
      have hLk := exportR_labelsOK nArgs fn x86Data_guardsPlain k _ _ rk hk
      have hdep := exportR_depth_le nArgs fn body _ _ b hb
      have hlenB := exportR_res_length nArgs fn body _ _ b hb
      have hlenI := exprArgsHV_length d nArgs inits
      have hresI := exprArgsHV_ok (nArgs := nArgs) hΓ inits
      obtain ⟨cx, hcx, hcxok⟩ := resolveVar_ok (nArgs := nArgs) count hΓ
      let car := carriedRegs (d + 1) cs.length
      let LN : String → Prop := fun x => X x ∨ x = regName d ∨ x = loopCtr n ∨ x ∈ car
      have hLNin : ∀ m, nArgs ≤ m → m < d + 1 + cs.length → LN (regName m) := by
        intro m h1 h2
        by_cases hm : m < d
        · exact Or.inl (hX _ ⟨m, h1, hm, rfl⟩)
        · by_cases hm' : m = d
          · subst hm'; exact Or.inr (Or.inl rfl)
          · refine Or.inr (Or.inr (Or.inr ?_))
            have := mem_carriedRegs_of (d := d + 1) (nCar := cs.length) (m := m - (d + 1))
              (by omega)
            rwa [show d + 1 + (m - (d + 1)) = m by omega] at this
      have hSb : SymOK E b.code := fun i hi => hSF.1 i (by unfold forArrFrame; simp [hi])
      obtain ⟨Λb, hBb⟩ := hB E hE hSb LN fun x ⟨j, h1, h2, he⟩ => he ▸ hLNin j h1 h2
      obtain ⟨Λk, hKk⟩ := hK E hE hSF.2 LN fun x ⟨j, h1, h2, he⟩ => he ▸ hLNin j h1 (by omega)
      let Λ : LLabel → String → Prop := fun l =>
        if l = n ∨ l = n + 1 then LN else if l < b.next then Λb l else Λk l
      have hΛn : ∀ x, Λ n x = LN x := fun x => by simp [Λ]
      have hΛn1 : ∀ x, Λ (n + 1) x = LN x := fun x => by simp [Λ]
      have hBb' : Blk E Λ LN b.code (fun x => LN x ∨ InScope nArgs b.depth x) :=
        hBb.congr_range hLb.range hLb.closed fun l h1 h2 => by
          simp only [Λ, ite_eq_right (show ¬(l = n ∨ l = n + 1) by omega), ite_eq_left h2]
      have hKk' : Blk E Λ LN rk.code (fun x => LN x ∨ InScope nArgs rk.depth x) :=
        hKk.congr_range hLk.range hLk.closed fun l h1 h2 => by
          have := hLb.le
          simp only [Λ, ite_eq_right (show ¬(l = n ∨ l = n + 1) by omega),
            ite_eq_right (show ¬(l < b.next) by omega)]
      have hgoodB := good_of_resOK (E := E) (X := fun x => LN x ∨ InScope nArgs b.depth x) hE
        (fun x hx => Or.inr hx) hresB
      have hF : Blk E Λ X (forArrFrame d n cs (exprArgsHV d nArgs argName (fun _ => none) inits)
          (resolveVar d nArgs argName (fun _ => none) count) b.code b.res b.depth x86Data) LN := by
        unfold forArrFrame
        dsimp only
        rw [x86_zeroTrip (loopCtr n) n (n + 1), x86_loopGuard (loopCtr n) n, hcx]
        -- the seeds
        refine Blk.cons (blk_movI _ _ (by simp [opNames])) ?_
        refine Blk.append (blk_typedMoves (regName d) _ _ (Or.inr rfl) fun p hp => ?_) ?_
        · obtain ⟨o, ho, he⟩ := carriedPairs_sources hp
          rw [he]
          rcases good_of_resOK hE hX hresI o ho with h' | h'
          · exact Or.inl (Or.inl h')
          · exact Or.inr h'
        refine Blk.append (blk_seed1 (loopCtr n) (.reg cx) fun x hx => ?_) ?_
        · simp only [opNames, List.mem_singleton] at hx
          subst hx
          rcases hcxok with h' | h'
          · exact Or.inr (hE _ h')
          · exact Or.inl (Or.inl (Or.inl (hX _ h')))
        have hLN0 : ∀ x, LN x → (((X x ∨ x = regName d) ∨ ∃ p ∈ carriedPairs cs car
            (exprArgsHV d nArgs argName (fun _ => none) inits), x = p.2.1) ∨ x = loopCtr n) := by
          rintro x (h' | rfl | rfl | h')
          · exact Or.inl (Or.inl (Or.inl h'))
          · exact Or.inl (Or.inl (Or.inr rfl))
          · exact Or.inr rfl
          · exact Or.inl (Or.inr (carriedPairs_targets (carriedRegs_length _ _) (by omega) x h'))
        refine Blk.append (blk_guard _ _ _ (Or.inr rfl) fun x hx => hLN0 x (by
          rw [hΛn1] at hx; exact hx)) ?_
        refine Blk.cons (blk_label n hLN0 fun x hx => by rw [hΛn]; exact hx) ?_
        -- the body
        refine Blk.append hBb' ?_
        -- the assignment at the back edge
        refine Blk.cons (blk_movI _ _ (by simp [opNames])) ?_
        refine Blk.append (blk_arrParMoves _ _ _ _ (Or.inr rfl) fun a ha => ?_) ?_
        · obtain ⟨p, hp, -, he⟩ := mem_arrPairs ha
          obtain ⟨o, ho, he'⟩ := carriedPairs_sources hp
          rw [he, he']
          rcases hgoodB o ho with h' | h'
          · exact Or.inl (Or.inl h')
          · exact Or.inr h'
        refine Blk.append ((blk_parMoves _ _ _ (fun o ho => ?_) (fun o ho => ?_)
          (by simp)).mono (fun _ h => h) (fun x (hx : LN x) => ?_)) ?_
        · obtain ⟨q, -, rfl⟩ := List.mem_map.mp ho
          rfl
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ho
          obtain ⟨p, hp, rfl⟩ := mem_regPairs hq
          obtain ⟨o, ho', he'⟩ := carriedPairs_sources hp
          show _ ∨ E p.2.2
          rw [he']
          rcases hgoodB o ho' with h' | h'
          · exact Or.inl (Or.inl (Or.inl h'))
          · exact Or.inr h'
        · exact Or.inl (Or.inl (Or.inl (Or.inl hx)))
        -- the advance, the back edge and the shift
        refine Blk.append (blk_advance _ _ (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl)))) ?_
        refine Blk.append (blk_guard _ _ _ (Or.inr (Or.inr (Or.inl rfl))) fun x hx => by
          rw [hΛn] at hx; exact hx) ?_
        refine Blk.cons (blk_label (n + 1) (fun x hx => hx) fun x hx => by rw [hΛn1]; exact hx) ?_
        refine Blk.cons (blk_movI _ _ (by simp [opNames])) ?_
        refine (blk_typedMoves (regName d) _ _ (Or.inr rfl) fun p hp => ?_).mono (fun _ h => h)
          fun x hx => Or.inl (Or.inl hx)
        exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (shiftPairs_sources hp)))))
      refine ⟨Λ, Blk.append hF (hKk'.mono (fun _ h => h) fun x hx => ?_)⟩
      rcases hx with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
  | @whileLoop Γ cs ts inits body k ihb ihk =>
      intro d n r h hΓ
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hk, rfl⟩ := h
      obtain ⟨hresB, hB⟩ := ihb _ _ b hb (by simp only [List.length_append]; omega)
      obtain ⟨hresK, hK⟩ := ihk _ _ rk hk (by simp only [List.length_append]; omega)
      refine ⟨hresK, fun E hE hS X hX => ?_⟩
      simp only [Exported.prepend] at hS ⊢
      have hSF := SymOK.append hS
      have hLb := exportR_labelsOK nArgs fn x86Data_guardsPlain body _ _ b hb
      have hLk := exportR_labelsOK nArgs fn x86Data_guardsPlain k _ _ rk hk
      have hlenB := exportR_res_length nArgs fn body _ _ b hb
      have hlenI := exprArgsHV_length d nArgs inits
      have hresI := exprArgsHV_ok (nArgs := nArgs) hΓ inits
      let car := carriedRegs d cs.length
      let LN : String → Prop := fun x => X x ∨ x ∈ car
      have hLNin : ∀ m, nArgs ≤ m → m < d + cs.length → LN (regName m) := by
        intro m h1 h2
        by_cases hm : m < d
        · exact Or.inl (hX _ ⟨m, h1, hm, rfl⟩)
        · refine Or.inr ?_
          have := mem_carriedRegs_of (d := d) (nCar := cs.length) (m := m - d) (by omega)
          rwa [show d + (m - d) = m by omega] at this
      have hSb : SymOK E b.code := fun i hi => hSF.1 i (by unfold whileFrame; simp [hi])
      obtain ⟨Λb, hBb⟩ := hB E hE hSb LN fun x ⟨j, h1, h2, he⟩ => he ▸ hLNin j h1 h2
      obtain ⟨Λk, hKk⟩ := hK E hE hSF.2 LN fun x ⟨j, h1, h2, he⟩ => he ▸ hLNin j h1 h2
      let Λ : LLabel → String → Prop := fun l =>
        if l = n then LN else if l < b.next then Λb l else Λk l
      have hΛn : ∀ x, Λ n x = LN x := fun x => by simp [Λ]
      have hBb' : Blk E Λ LN b.code (fun x => LN x ∨ InScope nArgs b.depth x) :=
        hBb.congr_range hLb.range hLb.closed fun l h1 h2 => by
          simp only [Λ, ite_eq_right (show ¬(l = n) by omega), ite_eq_left h2]
      have hKk' : Blk E Λ LN rk.code (fun x => LN x ∨ InScope nArgs rk.depth x) :=
        hKk.congr_range hLk.range hLk.closed fun l h1 h2 => by
          have := hLb.le
          simp only [Λ, ite_eq_right (show ¬(l = n) by omega), ite_eq_right (show ¬(l < b.next) by omega)]
      have hgoodB := good_of_resOK (E := E) (X := fun x => LN x ∨ InScope nArgs b.depth x) hE
        (fun x hx => Or.inr hx) hresB
      have hF : Blk E Λ X (whileFrame d n cs.length
          (exprArgsHV d nArgs argName (fun _ => none) inits) b.code (b.res.headD (.imm 0))
          b.res.tail b.depth x86Data) LN := by
        unfold whileFrame seedMoves
        dsimp only
        rw [x86_loopGuard (regName (b.depth + cs.length)) n]
        refine Blk.append ((blk_movs (fun p : String × LOperand => p.1)
          (fun p : String × LOperand => p.2) _ fun p hp x hx => ?_).mono
          (fun _ h => h) (fun x (hx : LN x) => ?_)) ?_
        · have ho := (List.of_mem_zip hp).2
          obtain ⟨y, hy, hyok⟩ := hresI p.2 ho
          rw [hy] at hx
          simp only [opNames, List.mem_singleton] at hx
          subst hx
          rcases hyok with h' | h'
          · exact Or.inr (hE _ h')
          · exact Or.inl (hX _ h')
        · rcases hx with h' | h'
          · exact Or.inl h'
          · have hm : (car.zip (exprArgsHV d nArgs argName (fun _ => none) inits)).map Prod.fst
                = car := List.map_fst_zip (by simp [car, carriedRegs_length]; omega)
            rw [← hm] at h'
            obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h'
            exact Or.inr ⟨q, hq, rfl⟩
        refine Blk.cons (blk_label n (fun x hx => hx) fun x hx => by rw [hΛn]; exact hx) ?_
        refine Blk.append hBb' ?_
        refine Blk.append (blk_flagWord _ _ _ fun x hx => ?_) ?_
        · cases hr : b.res with
          | nil => rw [hr] at hx; simp [opNames] at hx
          | cons o os =>
              rw [hr] at hx
              obtain ⟨y, hy, -⟩ := hresB o (by rw [hr]; exact List.mem_cons_self)
              simp only [List.headD_cons, hy, opNames, List.mem_singleton] at hx
              subst hx
              have := hgoodB o (by rw [hr]; exact List.mem_cons_self)
              rwa [hy] at this
        refine Blk.append ((blk_parMoves _ _ _ (fun o ho => hresB.reg o (List.mem_of_mem_tail ho))
          (fun o ho => ?_) ?_).mono (fun _ h => h)
          (fun x (hx : LN x ∨ x = regName (b.depth + cs.length)) => ?_)) ?_
        · rcases hgoodB o (List.mem_of_mem_tail ho) with h' | h'
          · exact Or.inl (Or.inl h')
          · exact Or.inr h'
        · simp [carriedRegs_length, List.length_tail, hlenB]
        · rcases hx with h' | h'
          · exact Or.inl (Or.inl (Or.inl h'))
          · exact Or.inl (Or.inr h')
        exact (blk_guard _ _ _ (Or.inr rfl) fun x hx => Or.inl (by rw [hΛn] at hx; exact hx)).mono
          (fun _ h => h) fun x hx => Or.inl hx
      refine ⟨Λ, Blk.append hF (hKk'.mono (fun _ h => h) fun x hx => ?_)⟩
      rcases hx with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
  | @ifThenElse Γ rs ts cond thn els k iht ihe ihk =>
      intro d n r h hΓ
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨t, ht, e, he, rk, hk, rfl⟩ := h
      obtain ⟨hresT, hT⟩ := iht _ _ t ht hΓ
      obtain ⟨hresE, hE'⟩ := ihe _ _ e he hΓ
      obtain ⟨hresK, hK⟩ := ihk _ _ rk hk (by simp only [List.length_append]; omega)
      refine ⟨hresK, fun E hE hS X hX => ?_⟩
      simp only [Exported.prepend] at hS ⊢
      have hSF := SymOK.append hS
      have hLt := exportR_labelsOK nArgs fn x86Data_guardsPlain thn _ _ t ht
      have hLe := exportR_labelsOK nArgs fn x86Data_guardsPlain els _ _ e he
      have hLk := exportR_labelsOK nArgs fn x86Data_guardsPlain k _ _ rk hk
      have hlenT := exportR_res_length nArgs fn thn _ _ t ht
      have hlenE := exportR_res_length nArgs fn els _ _ e he
      obtain ⟨cx, hcx, hcxok⟩ := resolveVar_ok (nArgs := nArgs) cond hΓ
      let JN : String → Prop := fun x => X x ∨ x ∈ carriedRegs d rs.length
      have hJNin : ∀ m, nArgs ≤ m → m < d + rs.length → JN (regName m) := by
        intro m h1 h2
        by_cases hm : m < d
        · exact Or.inl (hX _ ⟨m, h1, hm, rfl⟩)
        · refine Or.inr ?_
          have := mem_carriedRegs_of (d := d) (nCar := rs.length) (m := m - d) (by omega)
          rwa [show d + (m - d) = m by omega] at this
      have hSt : SymOK E t.code := fun i hi => hSF.1 i (by unfold ifFrame; simp [hi])
      have hSe : SymOK E e.code := fun i hi => hSF.1 i (by unfold ifFrame; simp [hi])
      obtain ⟨Λt, hTt⟩ := hT E hE hSt X hX
      obtain ⟨Λe, hEe⟩ := hE' E hE hSe X hX
      obtain ⟨Λk, hKk⟩ := hK E hE hSF.2 JN fun x ⟨j, h1, h2, he⟩ => he ▸ hJNin j h1 h2
      have hle1 := hLt.le
      have hle2 := hLe.le
      let Λ : LLabel → String → Prop := fun l =>
        if l = n ∨ l = n + 1 then X else if l = n + 2 then JN
        else if l < t.next then Λt l else if l < e.next then Λe l else Λk l
      have hΛn : ∀ x, Λ n x = X x := fun x => by simp [Λ]
      have hΛn1 : ∀ x, Λ (n + 1) x = X x := fun x => by simp [Λ]
      have hΛn2 : ∀ x, Λ (n + 2) x = JN x := fun x => by simp [Λ]
      have hTt' : Blk E Λ X t.code (fun x => X x ∨ InScope nArgs t.depth x) :=
        hTt.congr_range hLt.range hLt.closed fun l h1 h2 => by
          simp only [Λ, ite_eq_right (show ¬(l = n ∨ l = n + 1) by omega),
            ite_eq_right (show ¬(l = n + 2) by omega), ite_eq_left h2]
      have hEe' : Blk E Λ X e.code (fun x => X x ∨ InScope nArgs e.depth x) :=
        hEe.congr_range hLe.range hLe.closed fun l h1 h2 => by
          simp only [Λ, ite_eq_right (show ¬(l = n ∨ l = n + 1) by omega),
            ite_eq_right (show ¬(l = n + 2) by omega), ite_eq_right (show ¬(l < t.next) by omega), ite_eq_left h2]
      have hKk' : Blk E Λ JN rk.code (fun x => JN x ∨ InScope nArgs rk.depth x) :=
        hKk.congr_range hLk.range hLk.closed fun l h1 h2 => by
          simp only [Λ, ite_eq_right (show ¬(l = n ∨ l = n + 1) by omega),
            ite_eq_right (show ¬(l = n + 2) by omega), ite_eq_right (show ¬(l < t.next) by omega),
            ite_eq_right (show ¬(l < e.next) by omega)]
      have hgoodT := good_of_resOK (E := E) (X := fun x => X x ∨ InScope nArgs t.depth x) hE
        (fun x hx => Or.inr hx) hresT
      have hgoodE := good_of_resOK (E := E) (X := fun x => X x ∨ InScope nArgs e.depth x) hE
        (fun x hx => Or.inr hx) hresE
      have hF : Blk E Λ X (ifFrame fn d n rs (resolveVar d nArgs argName (fun _ => none) cond)
          t.code t.res t.depth e.code e.res e.depth x86Data) JN := by
        unfold ifFrame
        rw [x86_zeroTrip (regName d) n (n + 1), x86_loopGuard (regName (d + rs.length)) (n + 2),
          hcx]
        refine Blk.append (blk_flagWord _ _ _ fun x hx => ?_) ?_
        · simp only [opNames, List.mem_singleton] at hx
          subst hx
          rcases hcxok with h' | h'
          · exact Or.inr (hE _ h')
          · exact Or.inl (hX _ h')
        refine Blk.append (blk_guard _ _ _ (Or.inr rfl) fun x hx => Or.inl (by
          rw [hΛn1] at hx; exact hx)) ?_
        refine Blk.cons (blk_label n (fun x hx => Or.inl hx) fun x hx => by
          rw [hΛn]; exact hx) ?_
        refine Blk.append hTt' ?_
        refine Blk.append (blk_ifResMoves _ _ _ _ hresT.reg hgoodT (by omega)) ?_
        refine Blk.cons (blk_movI _ _ (by simp [opNames])) ?_
        refine Blk.append (blk_guard _ _ _ (Or.inr rfl) fun x hx => ?_) ?_
        · rw [hΛn2] at hx
          rcases hx with h' | h'
          · exact Or.inl (Or.inl (Or.inl h'))
          · exact Or.inl (Or.inr h')
        refine Blk.cons (blk_label (n + 1) (fun x hx => Or.inl (Or.inl (Or.inl hx)))
          fun x hx => by rw [hΛn1]; exact hx) ?_
        refine Blk.append hEe' ?_
        refine Blk.append (blk_ifResMoves _ _ _ _ hresE.reg hgoodE (by omega)) ?_
        refine blk_label (n + 2) (fun x hx => ?_) fun x hx => by rw [hΛn2]; exact hx
        rcases hx with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      refine ⟨Λ, Blk.append hF (hKk'.mono (fun _ h => h) fun x hx => ?_)⟩
      rcases hx with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'

/-! ## 7. Forward reachability and the headers of back edges -/

/-- `omega` after unfolding the label type `LLabel` to `Nat`. -/
macro "lomega" : tactic => `(tactic| first | omega | ((try dsimp only [LLabel] at *); omega))

/-- No instruction of the code is an unconditional jump. -/
def NoGoto (code : List LinstrRM) : Prop := ∀ i ∈ code, isGoto i.1 = false

/-- **Forward reachability.** `FwdPath code k`: the position `k` is reached from the entry by a
    walk along `webSuccs` each of whose edges goes to a larger position. -/
inductive FwdPath (code : List LinstrRM) : Nat → Prop
  /-- The entry. -/
  | zero : FwdPath code 0
  /-- A forward edge. -/
  | step {k s : Nat} {i : LinstrRM} : FwdPath code k → code[k]? = some i →
      s ∈ webSuccs code k i → k < s → FwdPath code s

/-- A forward walk is a path. -/
theorem FwdPath.path {code : List LinstrRM} {k : Nat} (h : FwdPath code k) :
    ∃ ks, Path code k ks := by
  induction h with
  | zero => exact ⟨[], Path.nil⟩
  | step _ hi hs _ ih =>
      obtain ⟨ks, hks⟩ := ih
      exact ⟨_, Path.cons hks hi hs⟩

theorem mem_webSuccs_next {code : List LinstrRM} {k : Nat} {i : LinstrRM}
    (h : isGoto i.1 = false) : k + 1 ∈ webSuccs code k i := by
  rcases i with ⟨w, tag⟩
  cases w <;> simp_all [webSuccs, isGoto]

/-- **Without unconditional jumps every position is forward reachable**: the walk along the
    next positions reaches every position up to the end of the code. -/
theorem fwdPath_of_noGoto {code : List LinstrRM} (h : NoGoto code) :
    ∀ k, k ≤ code.length → FwdPath code k
  | 0, _ => FwdPath.zero
  | k + 1, hk => by
      have hlt : k < code.length := by omega
      exact FwdPath.step (fwdPath_of_noGoto h k (by omega)) (List.getElem?_eq_getElem hlt)
        (mem_webSuccs_next (h _ (List.getElem_mem hlt))) (by omega)

/-- A back edge: the jump at `k` names a label whose position `p` is before `k`. -/
def BackEdge (code : List LinstrRM) (k p : Nat) : Prop :=
  ∃ i l, code[k]? = some i ∧ jumpLabel? i.1 = some l ∧ findLabelMem l code = some p ∧ p < k

/-- **A loop header.** The label at `p` heads the loop that ends at the back edge at `k`: every
    edge of the code into a position after the one after the label, up to `k`, leaves a
    position after `p` and up to `k`. The positions after `p + 1` up to `k` are entered only
    through `p + 1`. -/
def LoopHeader (code : List LinstrRM) (p k : Nat) : Prop :=
  ∀ j i s, code[j]? = some i → s ∈ webSuccs code j i → p + 1 < s → s ≤ k → p < j ∧ j ≤ k

/-- A label `l` lies strictly inside the loop of a back edge of the code `c`, by positions of
    occurrence. -/
def InnerL (c : List LinstrRM) (l : LLabel) : Prop :=
  ∃ (k p q : Nat) (ik ip iq : LinstrRM) (lk : LLabel), c[k]? = some ik ∧ jumpLabel? ik.1 = some lk ∧ c[p]? = some ip ∧
    labelOf? ip.1 = some lk ∧ c[q]? = some iq ∧ labelOf? iq.1 = some l ∧ p < q ∧ q < k

/-- **Nesting of the jumps.** For every back edge from `k` to a label at `p` and every jump to
    a label at a position strictly between `p` and `k`, the jump lies after `p` and up to
    `k`. -/
def Nest (c : List LinstrRM) : Prop :=
  ∀ (k p q j : Nat) (ik ip iq ij : LinstrRM) (lk lj : LLabel), c[k]? = some ik → jumpLabel? ik.1 = some lk → c[p]? = some ip →
    labelOf? ip.1 = some lk → p < k → c[j]? = some ij → jumpLabel? ij.1 = some lj →
    c[q]? = some iq → labelOf? iq.1 = some lj → p < q → q < k → p < j ∧ j ≤ k

theorem mem_labelsOf_iff {c : List LinstrRM} {l : LLabel} :
    l ∈ labelsOf c ↔ ∃ (q : Nat) (iq : LinstrRM), c[q]? = some iq ∧ labelOf? iq.1 = some l := by
  unfold labelsOf
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨i, hi, hl⟩
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.mp hi
    exact ⟨q, i, hq, hl⟩
  · rintro ⟨q, i, hq, hl⟩
    exact ⟨i, List.mem_of_getElem? hq, hl⟩

theorem mem_targetsOf_iff {c : List LinstrRM} {l : LLabel} :
    l ∈ targetsOf c ↔ ∃ (j : Nat) (ij : LinstrRM), c[j]? = some ij ∧ jumpLabel? ij.1 = some l := by
  unfold targetsOf
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨i, hi, hl⟩
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.mp hi
    exact ⟨q, i, hq, by rw [jumpLabel?_eq_jumpTarget?]; exact hl⟩
  · rintro ⟨q, i, hq, hl⟩
    exact ⟨i, List.mem_of_getElem? hq, by rw [← jumpLabel?_eq_jumpTarget?]; exact hl⟩

/-- A code with no label is nested. -/
theorem nest_of_noLabel {c : List LinstrRM} (h : labelsOf c = []) : Nest c := by
  intro k p q j ik ip iq ij lk lj _ _ hp hl
  have : lk ∈ labelsOf c := mem_labelsOf_iff.mpr ⟨p, ip, hp, hl⟩
  simp [h] at this

theorem InnerL.mem {c : List LinstrRM} {l : LLabel} (h : InnerL c l) : l ∈ labelsOf c := by
  obtain ⟨k, p, q, ik, ip, iq, lk, -, -, -, -, hq, hl, -⟩ := h
  exact mem_labelsOf_iff.mpr ⟨q, iq, hq, hl⟩

theorem not_innerL_of_noJump {c : List LinstrRM} (h : targetsOf c = []) (l : LLabel) :
    ¬ InnerL c l := by
  rintro ⟨k, p, q, ik, ip, iq, lk, hk, hj, -⟩
  have : lk ∈ targetsOf c := mem_targetsOf_iff.mpr ⟨k, ik, hk, hj⟩
  simp [h] at this

theorem InnerL.cons_label {m : LLabel} {c : List LinstrRM} {l : LLabel}
    (h : InnerL (labelI m :: c) l) : l ∈ labelsOf c := by
  obtain ⟨k, p, q, ik, ip, iq, lk, -, -, -, -, hq, hl, hpq, -⟩ := h
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  exact mem_labelsOf_iff.mpr ⟨q', iq, by simpa using hq, hl⟩

theorem InnerL.append {A B : List LinstrRM} {l : LLabel}
    (h1 : ∀ l ∈ targetsOf B, l ∉ labelsOf A) (h : InnerL (A ++ B) l) :
    InnerL A l ∨ InnerL B l := by
  obtain ⟨k, p, q, ik, ip, iq, lk, hk, hj, hp, hl, hq, hl', hpq, hqk⟩ := h
  by_cases hkA : k < A.length
  · rw [List.getElem?_append_left hkA] at hk
    rw [List.getElem?_append_left (by omega)] at hp hq
    exact Or.inl ⟨k, p, q, ik, ip, iq, lk, hk, hj, hp, hl, hq, hl', hpq, hqk⟩
  · rw [List.getElem?_append_right (by omega)] at hk
    by_cases hpA : p < A.length
    · rw [List.getElem?_append_left hpA] at hp
      exact absurd (mem_labelsOf_iff.mpr ⟨p, ip, hp, hl⟩)
        (h1 lk (mem_targetsOf_iff.mpr ⟨_, ik, hk, hj⟩))
    · rw [List.getElem?_append_right (by omega)] at hp hq
      exact Or.inr ⟨k - A.length, p - A.length, q - A.length, ik, ip, iq, lk, hk, hj, hp, hl,
        hq, hl', by omega, by omega⟩

/-- **The nesting of an appended code** whose second part jumps to no label of the first, and
    whose first part jumps to no label strictly inside a loop of the second. -/
theorem Nest.append {A B : List LinstrRM} (hA : Nest A) (hB : Nest B)
    (h1 : ∀ l ∈ targetsOf B, l ∉ labelsOf A) (h2 : ∀ l ∈ targetsOf A, ¬ InnerL B l) :
    Nest (A ++ B) := by
  intro k p q j ik ip iq ij lk lj hk hjk hp hlp hpk hj hjj hq hlq hpq hqk
  by_cases hkA : k < A.length
  · rw [List.getElem?_append_left hkA] at hk
    rw [List.getElem?_append_left (by omega)] at hp hq
    by_cases hjA : j < A.length
    · rw [List.getElem?_append_left hjA] at hj
      exact hA k p q j ik ip iq ij lk lj hk hjk hp hlp hpk hj hjj hq hlq hpq hqk
    · rw [List.getElem?_append_right (by omega)] at hj
      exact absurd (mem_labelsOf_iff.mpr ⟨q, iq, hq, hlq⟩)
        (h1 lj (mem_targetsOf_iff.mpr ⟨_, ij, hj, hjj⟩))
  · rw [List.getElem?_append_right (by omega)] at hk
    by_cases hpA : p < A.length
    · rw [List.getElem?_append_left hpA] at hp
      exact absurd (mem_labelsOf_iff.mpr ⟨p, ip, hp, hlp⟩)
        (h1 lk (mem_targetsOf_iff.mpr ⟨_, ik, hk, hjk⟩))
    · rw [List.getElem?_append_right (by omega)] at hp hq
      by_cases hjA : j < A.length
      · rw [List.getElem?_append_left hjA] at hj
        exact absurd ⟨k - A.length, p - A.length, q - A.length, ik, ip, iq, lk, hk, hjk, hp, hlp,
          hq, hlq, by omega, by omega⟩ (h2 lj (mem_targetsOf_iff.mpr ⟨j, ij, hj, hjj⟩))
      · rw [List.getElem?_append_right (by omega)] at hj
        have := hB _ _ _ _ ik ip iq ij lk lj hk hjk hp hlp (by omega) hj hjj hq hlq (by omega)
          (by omega)
        omega

/-- **The nesting of a loop** `labelI n :: (C ++ G)`: `C` is nested, jumps only to its own
    labels and declares no label `n`, and `G` declares no label and jumps only to `n`. -/
theorem nest_loop {n : LLabel} {C G : List LinstrRM} (hC : Nest C)
    (hCt : ∀ l ∈ targetsOf C, l ∈ labelsOf C) (hCn : n ∉ labelsOf C) (hG : labelsOf G = [])
    (hGt : ∀ l ∈ targetsOf G, l = n) : Nest (labelI n :: (C ++ G)) := by
  have hGl : ∀ (q : Nat) (iq : LinstrRM) (l : LLabel), G[q]? = some iq → labelOf? iq.1 = some l → False := by
    intro q iq l hq hl
    have : l ∈ labelsOf G := mem_labelsOf_iff.mpr ⟨q, iq, hq, hl⟩
    simp [hG] at this
  -- a position of the loop is the label, a position of `C` or a position of `G`
  have hpos : ∀ (x : Nat) (ix : LinstrRM), (labelI n :: (C ++ G))[x]? = some ix →
      (x = 0 ∧ ix = labelI n) ∨ (1 ≤ x ∧ x ≤ C.length ∧ C[x - 1]? = some ix)
        ∨ (C.length + 1 ≤ x ∧ G[x - 1 - C.length]? = some ix) := by
    intro x ix hx
    cases x with
    | zero => simp at hx; exact Or.inl ⟨rfl, hx.symm⟩
    | succ x =>
        simp only [List.getElem?_cons_succ] at hx
        by_cases hxC : x < C.length
        · rw [List.getElem?_append_left hxC] at hx
          exact Or.inr (Or.inl ⟨by omega, by omega, by simpa using hx⟩)
        · rw [List.getElem?_append_right (by omega)] at hx
          exact Or.inr (Or.inr ⟨by omega, by rwa [show x + 1 - 1 - C.length = x - C.length by
            omega]⟩)
  intro k p q j ik ip iq ij lk lj hk hjk hp hlp hpk hj hjj hq hlq hpq hqk
  rcases hpos q iq hq with ⟨rfl, rfl⟩ | ⟨hq1, hq2, hqC⟩ | ⟨_, hqG⟩
  · omega
  · -- the label at `q` is a label of `C`, so the jump at `j` is in `C`
    have hlC : lj ∈ labelsOf C := mem_labelsOf_iff.mpr ⟨_, iq, hqC, hlq⟩
    rcases hpos j ij hj with ⟨rfl, rfl⟩ | ⟨hj1, hj2, hjC⟩ | ⟨_, hjG⟩
    · simp [labelI, jumpLabel?] at hjj
    · rcases hpos k ik hk with ⟨rfl, rfl⟩ | ⟨hk1, hk2, hkC⟩ | ⟨hk1, hkG⟩
      · simp [labelI, jumpLabel?] at hjk
      · -- a back edge of `C`
        have hlk : lk ∈ labelsOf C := hCt lk (mem_targetsOf_iff.mpr ⟨_, ik, hkC, hjk⟩)
        rcases hpos p ip hp with ⟨rfl, rfl⟩ | ⟨hp1, -, hpC⟩ | ⟨_, hpG⟩
        · simp only [labelI, labelOf?, Option.some.injEq] at hlp
          subst hlp
          exact absurd hlk hCn
        · have := hC (k - 1) (p - 1) (q - 1) (j - 1) ik ip iq ij lk lj hkC hjk hpC hlp
            (by omega) hjC hjj hqC hlq (by omega) (by omega)
          omega
        · exact (hGl _ _ _ hpG hlp).elim
      · -- a back edge of the loop: its label `n` is at the first position
        have hlk : lk = n := hGt lk (mem_targetsOf_iff.mpr ⟨_, ik, hkG, hjk⟩)
        subst hlk
        rcases hpos p ip hp with ⟨rfl, rfl⟩ | ⟨_, _, hpC⟩ | ⟨_, hpG⟩
        · omega
        · exact absurd (mem_labelsOf_iff.mpr ⟨_, ip, hpC, hlp⟩) hCn
        · exact (hGl _ _ _ hpG hlp).elim
    · have := hGt lj (mem_targetsOf_iff.mpr ⟨_, ij, hjG, hjj⟩)
      subst this
      exact absurd hlC hCn
  · exact (hGl _ _ _ hqG hlq).elim

/-- **Nesting gives loop headers.** In a nested code every back edge targets a loop header. -/
theorem loopHeader_of_nest {code : List LinstrRM} (h : Nest code) {k p : Nat}
    (hb : BackEdge code k p) : LoopHeader code p k := by
  obtain ⟨ik, lk, hk, hjk, hf, hpk⟩ := hb
  obtain ⟨ip, hp, hlp⟩ := findLabelMem_label hf
  intro j ij s hj hs h1 h2
  rcases ij with ⟨w, tag⟩
  have hjump : ∀ lj q, jumpLabel? w = some lj → findLabelMem lj code = some q → s = q + 1 →
      p < j ∧ j ≤ k := by
    intro lj q hl hq hsq
    subst hsq
    obtain ⟨iq, hq', hlq⟩ := findLabelMem_label hq
    exact h k p q j ik ip iq (w, tag) lk lj hk hjk hp hlp hpk hj hl hq' hlq (by omega) (by omega)
  cases w with
  | Lgoto t =>
      obtain ⟨f, l⟩ := t
      simp only [webSuccs, List.mem_map, Option.mem_toList] at hs
      obtain ⟨q, hq, rfl⟩ := hs
      exact hjump l q rfl hq rfl
  | Lcond c l =>
      simp only [webSuccs, List.mem_cons, List.mem_map, Option.mem_toList] at hs
      rcases hs with rfl | ⟨q, hq, rfl⟩
      · omega
      · exact hjump l q rfl hq rfl
  | _ =>
      simp only [webSuccs, List.mem_singleton] at hs
      omega

/-- A code with no jump is nested. -/
theorem nest_of_noJump {c : List LinstrRM} (h : targetsOf c = []) : Nest c := by
  intro k p q j ik ip iq ij lk lj hk hj
  have : lk ∈ targetsOf c := mem_targetsOf_iff.mpr ⟨k, ik, hk, hj⟩
  simp [h] at this

/-! ### The labels and the jumps of the pieces of the frames -/

section Pieces

theorem isGoto_of_isLopn {i : LinstrRM} (h : IsLopn i) : isGoto i.1 = false := by
  obtain ⟨d, o, s, h⟩ := h
  rw [h]; rfl

theorem noGoto_of_isLopn {xs : List LinstrRM} (h : ∀ i ∈ xs, IsLopn i) :
    ∀ i ∈ xs, isGoto i.1 = false := fun i hi => isGoto_of_isLopn (h i hi)

@[simp] theorem labelsOf_labelI_cons (l : LLabel) (c : List LinstrRM) :
    labelsOf (labelI l :: c) = l :: labelsOf c := by
  rw [labelsOf_cons]; rfl

@[simp] theorem targetsOf_labelI_cons (l : LLabel) (c : List LinstrRM) :
    targetsOf (labelI l :: c) = targetsOf c := by
  rw [targetsOf_cons]; rfl

@[simp] theorem labelsOf_movI_cons (x : String) (o : LOperand) (c : List LinstrRM) :
    labelsOf (movI x o :: c) = labelsOf c := by
  rw [labelsOf_cons]; rfl

@[simp] theorem targetsOf_movI_cons (x : String) (o : LOperand) (c : List LinstrRM) :
    targetsOf (movI x o :: c) = targetsOf c := by
  rw [targetsOf_cons]; rfl

@[simp] theorem labelsOf_guard2 (c cc : String) (l : LLabel) :
    labelsOf [guardI (.Lopn [.reg c] (withWidthTag 64 "CMP") [.reg c, .imm 0]),
      guardI (.Lcond (.reg cc) l)] = [] := rfl

@[simp] theorem targetsOf_guard2 (c cc : String) (l : LLabel) :
    targetsOf [guardI (.Lopn [.reg c] (withWidthTag 64 "CMP") [.reg c, .imm 0]),
      guardI (.Lcond (.reg cc) l)] = [l] := rfl

@[simp] theorem labelsOf_typedMoves (z t : String) (tp : List (JasminTy × String × String)) :
    labelsOf (typedMoves z t tp) = [] := labelsOf_of_isLopn (isLopn_typedMoves z t tp)
@[simp] theorem targetsOf_typedMoves (z t : String) (tp : List (JasminTy × String × String)) :
    targetsOf (typedMoves z t tp) = [] := targetsOf_of_isLopn (isLopn_typedMoves z t tp)
@[simp] theorem labelsOf_seedMoves (car : List String) (ops : List LOperand) :
    labelsOf (seedMoves car ops) = [] := labelsOf_of_isLopn (isLopn_seedMoves car ops)
@[simp] theorem targetsOf_seedMoves (car : List String) (ops : List LOperand) :
    targetsOf (seedMoves car ops) = [] := targetsOf_of_isLopn (isLopn_seedMoves car ops)
@[simp] theorem labelsOf_arrParMoves (z t : String) (D : Nat) (mv : List ArrMove) :
    labelsOf (arrParMoves z t D mv) = [] := labelsOf_of_isLopn (isLopn_arrParMoves z t D mv)
@[simp] theorem targetsOf_arrParMoves (z t : String) (D : Nat) (mv : List ArrMove) :
    targetsOf (arrParMoves z t D mv) = [] := targetsOf_of_isLopn (isLopn_arrParMoves z t D mv)
@[simp] theorem labelsOf_parMoves (D : Nat) (tgts : List String) (ops : List LOperand) :
    labelsOf (ExportRegions.parMoves D tgts ops) = [] := labelsOf_of_isLopn (isLopn_parMoves D tgts ops)
@[simp] theorem targetsOf_parMoves (D : Nat) (tgts : List String) (ops : List LOperand) :
    targetsOf (ExportRegions.parMoves D tgts ops) = [] := targetsOf_of_isLopn (isLopn_parMoves D tgts ops)
@[simp] theorem labelsOf_advanceOps (idx ctr : String) :
    labelsOf (advanceOps idx ctr) = [] := labelsOf_of_isLopn (isLopn_advanceOps idx ctr)
@[simp] theorem targetsOf_advanceOps (idx ctr : String) :
    targetsOf (advanceOps idx ctr) = [] := targetsOf_of_isLopn (isLopn_advanceOps idx ctr)
@[simp] theorem labelsOf_ifResMoves (rs : List JasminTy) (d D : Nat) (ops : List LOperand) :
    labelsOf (ifResMoves rs d D ops) = [] := labelsOf_of_isLopn (isLopn_ifResMoves rs d D ops)
@[simp] theorem targetsOf_ifResMoves (rs : List JasminTy) (d D : Nat) (ops : List LOperand) :
    targetsOf (ifResMoves rs d D ops) = [] := targetsOf_of_isLopn (isLopn_ifResMoves rs d D ops)
@[simp] theorem labelsOf_flagWord (I : IsaData) (r z : String) (op : LOperand) :
    labelsOf (flagWord I r z op) = [] := labelsOf_of_isLopn (isLopn_flagWord I r z op)
@[simp] theorem targetsOf_flagWord (I : IsaData) (r z : String) (op : LOperand) :
    targetsOf (flagWord I r z op) = [] := targetsOf_of_isLopn (isLopn_flagWord I r z op)

end Pieces

/-- **The export has no unconditional jump.** -/
theorem exportR_noGoto (nArgs : Nat) (fn : String) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) :
    ∀ (d n : Nat) (r : Exported), exportR nArgs fn p d n x86Data = some r → NoGoto r.code := by
  have hT : ∀ z t tp, ∀ i ∈ typedMoves z t tp, isGoto i.1 = false :=
    fun z t tp => noGoto_of_isLopn (isLopn_typedMoves z t tp)
  have hS : ∀ car ops, ∀ i ∈ seedMoves car ops, isGoto i.1 = false :=
    fun car ops => noGoto_of_isLopn (isLopn_seedMoves car ops)
  have hA : ∀ z t D mv, ∀ i ∈ arrParMoves z t D mv, isGoto i.1 = false :=
    fun z t D mv => noGoto_of_isLopn (isLopn_arrParMoves z t D mv)
  have hP : ∀ D tgts ops, ∀ i ∈ ExportRegions.parMoves D tgts ops, isGoto i.1 = false :=
    fun D tgts ops => noGoto_of_isLopn (isLopn_parMoves D tgts ops)
  have hV : ∀ idx ctr, ∀ i ∈ advanceOps idx ctr, isGoto i.1 = false :=
    fun idx ctr => noGoto_of_isLopn (isLopn_advanceOps idx ctr)
  have hR : ∀ rs d D ops, ∀ i ∈ ifResMoves rs d D ops, isGoto i.1 = false :=
    fun rs d D ops => noGoto_of_isLopn (isLopn_ifResMoves rs d D ops)
  have hW : ∀ I r z op, ∀ i ∈ flagWord I r z op, isGoto i.1 = false :=
    fun I r z op => noGoto_of_isLopn (isLopn_flagWord I r z op)
  induction p with
  | ret vs =>
      intro d n r h
      simp only [exportR, Option.some.injEq] at h
      subst h
      intro i hi; simp at hi
  | var e k ih =>
      intro d n r h
      simp only [exportR, Option.map_eq_some_iff] at h
      obtain ⟨rk, hk, rfl⟩ := h
      intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · exact noGoto_of_isLopn (isLopn_bindOps nArgs e d) i hi
      · exact ih _ _ _ hk i hi
  | call f args k ih =>
      intro d n r h
      obtain ⟨-, rk, hk, rfl⟩ := exportR_call_eq_some.mp h
      intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · rfl
      · exact ih _ _ _ hk i hi
  | forLoop count inits body k ihb ihk =>
      intro d n r h
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hk, rfl⟩ := h
      have hB := ihb _ _ _ hb
      have hK := ihk _ _ _ hk
      simp only [NoGoto, Exported.prepend, forArrFrame, List.forall_mem_append,
        List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true,
        List.map_cons, List.map_nil]
      repeat' constructor
      all_goals first
        | exact hB
        | exact hK
        | exact hT _ _ _
        | exact hS _ _
        | exact hA _ _ _ _
        | exact hP _ _ _
        | exact hV _ _
  | ifThenElse cond thn els k iht ihe ihk =>
      intro d n r h
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨t, ht, e, he, rk, hk, rfl⟩ := h
      have hT' := iht _ _ _ ht
      have hE := ihe _ _ _ he
      have hK := ihk _ _ _ hk
      simp only [NoGoto, Exported.prepend, ifFrame, List.forall_mem_append,
        List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true,
        List.map_cons, List.map_nil]
      repeat' constructor
      all_goals first
        | exact hT'
        | exact hE
        | exact hK
        | exact hR _ _ _ _
        | exact hW _ _ _ _
  | whileLoop inits body k ihb ihk =>
      intro d n r h
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hk, rfl⟩ := h
      have hB := ihb _ _ _ hb
      have hK := ihk _ _ _ hk
      simp only [NoGoto, Exported.prepend, whileFrame, List.forall_mem_append,
        List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true,
        List.map_cons, List.map_nil]
      repeat' constructor
      all_goals first
        | exact hB
        | exact hK
        | exact hS _ _
        | exact hW _ _ _ _
        | exact hP _ _ _

/-- The nesting of the shape of a counted loop: a head `P` without labels jumping to the exit
    label, the loop `labelI n :: (C ++ G)`, the exit label with a part `S` without labels and
    jumps, and the continuation `K`, whose labels lie at or above `m` while those of `C` lie
    in `[n + 2, m)`. -/
theorem nest_forShape {n m : LLabel} {P C G S K : List LinstrRM} (hP : labelsOf P = [])
    (hPt : ∀ l ∈ targetsOf P, l = n + 1) (hC : Nest C)
    (hCt : ∀ l ∈ targetsOf C, l ∈ labelsOf C) (hCr : ∀ l ∈ labelsOf C, n + 2 ≤ l ∧ l < m)
    (hG : labelsOf G = []) (hGt : ∀ l ∈ targetsOf G, l = n) (hS : labelsOf S = [])
    (hSt : targetsOf S = []) (hK : Nest K) (hKt : ∀ l ∈ targetsOf K, l ∈ labelsOf K)
    (hKr : ∀ l ∈ labelsOf K, m ≤ l) (hnm : n + 2 ≤ m) :
    Nest (P ++ ((labelI n :: (C ++ G)) ++ ((labelI (n + 1) :: S) ++ K))) := by
  have hCn : ∀ l ∈ labelsOf C, l ≠ n ∧ l ≠ n + 1 := fun l hl => by
    have := hCr l hl; lomega
  have hKn : ∀ l ∈ labelsOf K, ∀ l' ∈ labelsOf C, l ≠ l' := fun l hl l' hl' => by
    have := hKr l hl; have := hCr l' hl'; lomega
  have hKn2 : ∀ l ∈ labelsOf K, l ≠ n ∧ l ≠ n + 1 := fun l hl => by
    have := hKr l hl; lomega
  have hXK : Nest ((labelI (n + 1) :: S) ++ K) :=
    Nest.append (nest_of_noJump (by simp [hSt])) hK
      (fun l hl => by
        simp only [labelsOf_labelI_cons, hS, List.mem_singleton]
        exact (hKn2 l (hKt l hl)).2)
      (fun l hl => by simp [hSt] at hl)
  have hL : Nest (labelI n :: (C ++ G)) :=
    nest_loop hC hCt (fun h => (hCn n h).1 rfl) hG hGt
  have hTXK : ∀ l ∈ targetsOf ((labelI (n + 1) :: S) ++ K), l ∈ labelsOf K := by
    intro l hl
    simp only [targetsOf_append, targetsOf_labelI_cons, hSt, List.nil_append] at hl
    exact hKt l hl
  have hcross1 : ∀ l ∈ targetsOf ((labelI (n + 1) :: S) ++ K),
      l ∉ labelsOf (labelI n :: (C ++ G)) := by
    intro l hl hm
    have hk := hTXK l hl
    simp only [labelsOf_labelI_cons, labelsOf_append, hG, List.append_nil,
      List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact (hKn2 _ hk).1 rfl
    · exact hKn l hk l hm rfl
  have hcross2 : ∀ l ∈ targetsOf K, l ∉ labelsOf (labelI (n + 1) :: S) := by
    intro l hl hm
    simp only [labelsOf_labelI_cons, hS, List.mem_singleton] at hm
    subst hm
    exact (hKn2 _ (hKt _ hl)).2 rfl
  have hRest : Nest ((labelI n :: (C ++ G)) ++ ((labelI (n + 1) :: S) ++ K)) := by
    refine Nest.append hL hXK hcross1 (fun l hl hI => ?_)
    have hm := hI.mem
    simp only [labelsOf_append, labelsOf_labelI_cons, hS, List.mem_append,
      List.mem_singleton] at hm
    simp only [targetsOf_labelI_cons, targetsOf_append, List.mem_append] at hl
    have hl' : l = n ∨ l ∈ labelsOf C := by
      rcases hl with hl | hl
      · exact Or.inr (hCt l hl)
      · exact Or.inl (hGt l hl)
    rcases hl' with rfl | hl' <;> rcases hm with hm | hm
    · lomega
    · exact (hKn2 _ hm).1 rfl
    · exact (hCn _ hl').2 hm
    · exact hKn l hm l hl' rfl
  refine Nest.append (nest_of_noLabel hP) hRest (fun l _ hm => by simp [hP] at hm)
    (fun l hl hI => ?_)
  obtain rfl := hPt l hl
  rcases InnerL.append hcross1 hI with hI | hI
  · have hm := hI.mem
    simp only [labelsOf_labelI_cons, labelsOf_append, hG, List.append_nil, List.mem_cons] at hm
    rcases hm with hm | hm
    · lomega
    · exact (hCn _ hm).2 rfl
  · rcases InnerL.append hcross2 hI with hI | hI
    · have hm := hI.cons_label
      simp [hS] at hm
    · exact (hKn2 _ hI.mem).2 rfl

/-- The nesting of the shape of an exit-flag loop: a head `P` without labels and jumps, the
    loop `labelI n :: (C ++ G)` and the continuation `K`, whose labels lie at or above `m`
    while those of `C` lie in `[n + 1, m)`. -/
theorem nest_whileShape {n m : LLabel} {P C G K : List LinstrRM} (hP : labelsOf P = [])
    (hPt : targetsOf P = []) (hC : Nest C)
    (hCt : ∀ l ∈ targetsOf C, l ∈ labelsOf C) (hCr : ∀ l ∈ labelsOf C, n + 1 ≤ l ∧ l < m)
    (hG : labelsOf G = []) (hGt : ∀ l ∈ targetsOf G, l = n) (hK : Nest K)
    (hKt : ∀ l ∈ targetsOf K, l ∈ labelsOf K) (hKr : ∀ l ∈ labelsOf K, m ≤ l)
    (hnm : n < m) : Nest (P ++ ((labelI n :: (C ++ G)) ++ K)) := by
  have hL : Nest (labelI n :: (C ++ G)) :=
    nest_loop hC hCt (fun h => by have := hCr n h; lomega) hG hGt
  refine Nest.append (nest_of_noLabel hP) (Nest.append hL hK (fun l hl hm => ?_)
    (fun l hl hI => ?_)) (fun l _ hm => by simp [hP] at hm) (fun l hl => by simp [hPt] at hl)
  · have hk := hKr l (hKt l hl)
    simp only [labelsOf_labelI_cons, labelsOf_append, hG, List.append_nil, List.mem_cons] at hm
    rcases hm with rfl | hm
    · lomega
    · have := hCr l hm; lomega
  · have hk := hKr l hI.mem
    simp only [targetsOf_labelI_cons, targetsOf_append, List.mem_append] at hl
    rcases hl with hl | hl
    · have := hCr l (hCt l hl); lomega
    · have := hGt l hl; lomega

/-- The nesting of the shape of a branch: a head `P` without labels jumping to the label
    `n + 1`, the then part `labelI n :: (T ++ GT)` with `GT` jumping to `n + 2`, the else part
    `labelI (n + 1) :: (F ++ GF)`, the join label `n + 2` and the continuation `K`, with the
    labels of `T`, `F` and `K` in `[n + 3, a)`, `[a, b)` and `[b, ∞)`. -/
theorem nest_ifShape {n a b : LLabel} {P T GT F GF K : List LinstrRM} (hP : labelsOf P = [])
    (hPt : ∀ l ∈ targetsOf P, l = n + 1) (hT : Nest T)
    (hTt : ∀ l ∈ targetsOf T, l ∈ labelsOf T) (hTr : ∀ l ∈ labelsOf T, n + 3 ≤ l ∧ l < a)
    (hGT : labelsOf GT = []) (hGTt : ∀ l ∈ targetsOf GT, l = n + 2) (hF : Nest F)
    (hFt : ∀ l ∈ targetsOf F, l ∈ labelsOf F) (hFr : ∀ l ∈ labelsOf F, a ≤ l ∧ l < b)
    (hGF : labelsOf GF = []) (hGFt : targetsOf GF = []) (hK : Nest K)
    (hKt : ∀ l ∈ targetsOf K, l ∈ labelsOf K) (hKr : ∀ l ∈ labelsOf K, b ≤ l)
    (hab : n + 3 ≤ a ∧ a ≤ b) :
    Nest (P ++ ((labelI n :: (T ++ GT)) ++ ((labelI (n + 1) :: (F ++ GF)) ++
      (labelI (n + 2) :: K)))) := by
  -- the labels of the four parts after the head
  have hLT : ∀ l, l ∈ labelsOf (labelI n :: (T ++ GT)) → l = n ∨ (n + 3 ≤ l ∧ l < a) := by
    intro l hl
    simp only [labelsOf_labelI_cons, labelsOf_append, hGT, List.append_nil, List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact Or.inl rfl
    · exact Or.inr (hTr l hl)
  have hLF : ∀ l, l ∈ labelsOf (labelI (n + 1) :: (F ++ GF)) → l = n + 1 ∨ (a ≤ l ∧ l < b) := by
    intro l hl
    simp only [labelsOf_labelI_cons, labelsOf_append, hGF, List.append_nil, List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact Or.inl rfl
    · exact Or.inr (hFr l hl)
  have hLJ : ∀ l, l ∈ labelsOf (labelI (n + 2) :: K) → l = n + 2 ∨ b ≤ l := by
    intro l hl
    simp only [labelsOf_labelI_cons, List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact Or.inl rfl
    · exact Or.inr (hKr l hl)
  have hTJ : ∀ l ∈ targetsOf (labelI (n + 2) :: K), b ≤ l := by
    intro l hl
    simp only [targetsOf_labelI_cons] at hl
    exact hKr l (hKt l hl)
  have hTF : ∀ l ∈ targetsOf ((labelI (n + 1) :: (F ++ GF)) ++ (labelI (n + 2) :: K)),
      a ≤ l := by
    intro l hl
    simp only [targetsOf_append, targetsOf_labelI_cons, hGFt, List.append_nil,
      List.mem_append] at hl
    rcases hl with hl | hl
    · exact (hFr l (hFt l hl)).1
    · have := hTJ l hl; lomega
  have hNJ : Nest (labelI (n + 2) :: K) :=
    Nest.append (A := [labelI (n + 2)]) (B := K) (nest_of_noJump rfl) hK
      (fun l hl hm => by
        have := hKr l (hKt l hl)
        simp [labelsOf, labelI, labelOf?] at hm; lomega)
      (fun l hl => by simp [targetsOf, labelI, jumpTarget?] at hl)
  have hNF : Nest (labelI (n + 1) :: (F ++ GF)) :=
    Nest.append (A := [labelI (n + 1)]) (B := F ++ GF) (nest_of_noJump rfl)
      (Nest.append hF (nest_of_noLabel hGF) (fun l hl => by simp [hGFt] at hl)
        (fun l _ hI => by have := hI.mem; simp [hGF] at this))
      (fun l hl hm => by
        simp only [targetsOf_append, hGFt, List.append_nil] at hl
        have := hFr l (hFt l hl)
        simp [labelsOf, labelI, labelOf?] at hm; lomega)
      (fun l hl => by simp [targetsOf, labelI, jumpTarget?] at hl)
  have hNT : Nest (labelI n :: (T ++ GT)) :=
    Nest.append (A := [labelI n]) (B := T ++ GT) (nest_of_noJump rfl)
      (Nest.append hT (nest_of_noLabel hGT) (fun l hl hm => by
          have := hGTt l hl; have := hTr l hm; lomega)
        (fun l _ hI => by have := hI.mem; simp [hGT] at this))
      (fun l hl hm => by
        simp only [targetsOf_append, List.mem_append] at hl
        simp [labelsOf, labelI, labelOf?] at hm
        rcases hl with hl | hl
        · have := hTr l (hTt l hl); lomega
        · have := hGTt l hl; lomega)
      (fun l hl => by simp [targetsOf, labelI, jumpTarget?] at hl)
  have hR2 : Nest ((labelI (n + 1) :: (F ++ GF)) ++ (labelI (n + 2) :: K)) :=
    Nest.append hNF hNJ (fun l hl hm => by
        have := hTJ l hl
        rcases hLF l hm with rfl | hm <;> lomega)
      (fun l hl hI => by
        have hm := hLJ l hI.mem
        simp only [targetsOf_labelI_cons, targetsOf_append, hGFt, List.append_nil] at hl
        have := hFr l (hFt l hl)
        lomega)
  -- a label of the head's jumps or of the then part is not inside a loop of a later part
  have hInner2 : ∀ l, (l = n + 1 ∨ l = n + 2) →
      ¬ InnerL ((labelI (n + 1) :: (F ++ GF)) ++ (labelI (n + 2) :: K)) l := by
    intro l hl hI
    rcases InnerL.append (fun l' hl' hm => by
        have := hTJ l' hl'; rcases hLF l' hm with rfl | hm <;> lomega) hI with hI | hI
    · have hm := hI.cons_label
      simp only [labelsOf_append, hGF, List.append_nil] at hm
      have := hFr l hm
      lomega
    · change InnerL ([labelI (n + 2)] ++ K) l at hI
      rcases InnerL.append (fun l' hl' hm => by
          have := hKr l' (hKt l' hl')
          simp [labelsOf, labelI, labelOf?] at hm; lomega) hI with hI | hI
      · exact not_innerL_of_noJump rfl l hI
      · have := hKr l hI.mem; lomega
  have hR1 : Nest ((labelI n :: (T ++ GT)) ++
      ((labelI (n + 1) :: (F ++ GF)) ++ (labelI (n + 2) :: K))) :=
    Nest.append hNT hR2 (fun l hl hm => by
        have := hTF l hl
        rcases hLT l hm with rfl | hm <;> lomega)
      (fun l hl hI => by
        simp only [targetsOf_labelI_cons, targetsOf_append, List.mem_append] at hl
        rcases hl with hl | hl
        · have h1 := hTr l (hTt l hl)
          have hm := hI.mem
          simp only [labelsOf_append, labelsOf_labelI_cons, hGF, List.append_nil,
            List.cons_append, List.mem_cons, List.mem_append] at hm
          rcases hm with rfl | hm | rfl | hm
          · lomega
          · have := hFr l hm; lomega
          · lomega
          · have := hKr l hm; lomega
        · exact hInner2 l (Or.inr (hGTt l hl)) hI)
  refine Nest.append (nest_of_noLabel hP) hR1 (fun l _ hm => by simp [hP] at hm)
    (fun l hl hI => ?_)
  obtain rfl := hPt l hl
  rcases InnerL.append (fun l' hl' hm => by
      have := hTF l' hl'; rcases hLT l' hm with rfl | hm <;> lomega) hI with hI | hI
  · rcases hLT _ hI.mem with h | h <;> lomega
  · exact hInner2 _ (Or.inl rfl) hI

/-- **The jumps of the export are nested.** -/
theorem exportR_nest (nArgs : Nat) (fn : String) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) :
    ∀ (d n : Nat) (r : Exported), exportR nArgs fn p d n x86Data = some r → Nest r.code := by
  induction p with
  | ret vs =>
      intro d n r h
      simp only [exportR, Option.some.injEq] at h
      subst h
      exact nest_of_noLabel rfl
  | var e k ih =>
      intro d n r h
      simp only [exportR, Option.map_eq_some_iff] at h
      obtain ⟨rk, hk, rfl⟩ := h
      exact Nest.append (nest_of_noLabel (labelsOf_of_isLopn (isLopn_bindOps nArgs e d)))
        (ih _ _ _ hk) (by simp [labelsOf_of_isLopn (isLopn_bindOps nArgs e d)])
        (by simp [targetsOf_of_isLopn (isLopn_bindOps nArgs e d)])
  | call f args k ih =>
      intro d n r h
      obtain ⟨-, rk, hk, rfl⟩ := exportR_call_eq_some.mp h
      exact Nest.append (A := [_]) (nest_of_noLabel rfl) (ih _ _ _ hk)
        (fun l _ hm => by simp [labelsOf, callI, callShadow, labelOf?] at hm)
        (fun l hl => by simp [targetsOf, callI, callShadow, jumpTarget?] at hl)
  | @forLoop Γ cs ts count inits body k ihb ihk =>
      intro d n r h
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hk, rfl⟩ := h
      have hLb := exportR_labelsOK nArgs fn x86Data_guardsPlain body _ _ b hb
      have hLk := exportR_labelsOK nArgs fn x86Data_guardsPlain k _ _ rk hk
      simp only [Exported.prepend]
      rw [show forArrFrame d n cs (exprArgsHV d nArgs argName (fun _ => none) inits)
          (resolveVar d nArgs argName (fun _ => none) count) b.code b.res b.depth x86Data
          ++ rk.code =
        (movImmI (regName d) 0 :: (typedMoves (regName d) (regName (d + 1 + cs.length))
          (carriedPairs cs (carriedRegs (d + 1) cs.length)
            (exprArgsHV d nArgs argName (fun _ => none) inits))
          ++ (seedMoves [loopCtr n] [resolveVar d nArgs argName (fun _ => none) count]
          ++ [guardI (.Lopn [.reg (loopCtr n)] (withWidthTag 64 "CMP")
                [.reg (loopCtr n), .imm 0]), guardI (.Lcond (.reg "Z") (n + 1))])))
        ++ ((labelI n :: (b.code ++ (movImmI (regName (b.depth + 1)) 0
          :: (arrParMoves (regName (b.depth + 1)) (regName b.depth) b.depth
              (arrPairs (carriedPairs cs (carriedRegs (d + 1) cs.length) b.res))
          ++ (ExportRegions.parMoves b.depth
              ((regPairs (carriedPairs cs (carriedRegs (d + 1) cs.length) b.res)).map Prod.fst)
              ((regPairs (carriedPairs cs (carriedRegs (d + 1) cs.length) b.res)).map
                fun p => .reg p.2)
          ++ (advanceOps (regName d) (loopCtr n)
          ++ [guardI (.Lopn [.reg (loopCtr n)] (withWidthTag 64 "CMP")
                [.reg (loopCtr n), .imm 0]), guardI (.Lcond (.reg "NZ") n)]))))))
        ++ ((labelI (n + 1) :: (movImmI (regName d) 0 :: typedMoves (regName d)
              (regName (d + 1 + cs.length)) (shiftPairs d cs))) ++ rk.code))
        from by simp [forArrFrame]]
      exact nest_forShape (m := b.next) (by simp [movImmI]) (by simp [movImmI])
        (ihb _ _ _ hb) hLb.closed (fun l hl => hLb.range l hl) (by simp [movImmI])
        (by simp [movImmI]) (by simp [movImmI]) (by simp [movImmI]) (ihk _ _ _ hk) hLk.closed
        (fun l hl => (hLk.range l hl).1) hLb.le
  | @whileLoop Γ cs ts inits body k ihb ihk =>
      intro d n r h
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hk, rfl⟩ := h
      have hLb := exportR_labelsOK nArgs fn x86Data_guardsPlain body _ _ b hb
      have hLk := exportR_labelsOK nArgs fn x86Data_guardsPlain k _ _ rk hk
      simp only [Exported.prepend]
      rw [show whileFrame d n cs.length (exprArgsHV d nArgs argName (fun _ => none) inits)
          b.code (b.res.headD (.imm 0)) b.res.tail b.depth x86Data ++ rk.code =
        seedMoves (carriedRegs d cs.length) (exprArgsHV d nArgs argName (fun _ => none) inits)
        ++ ((labelI n :: (b.code ++ (flagWord x86Data (regName (b.depth + cs.length))
              (regName (b.depth + cs.length + 1)) (b.res.headD (.imm 0))
          ++ (ExportRegions.parMoves b.depth (carriedRegs d cs.length) b.res.tail
          ++ [guardI (.Lopn [.reg (regName (b.depth + cs.length))] (withWidthTag 64 "CMP")
                [.reg (regName (b.depth + cs.length)), .imm 0]),
              guardI (.Lcond (.reg "NZ") n)]))))
        ++ rk.code)
        from by simp [whileFrame]]
      exact nest_whileShape (m := b.next) (by simp) (by simp) (ihb _ _ _ hb) hLb.closed
        (fun l hl => hLb.range l hl) (by simp) (by simp) (ihk _ _ _ hk) hLk.closed
        (fun l hl => (hLk.range l hl).1) (by have := hLb.le; lomega)
  | @ifThenElse Γ rs ts cond thn els k iht ihe ihk =>
      intro d n r h
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨t, ht, e, he, rk, hk, rfl⟩ := h
      have hLt := exportR_labelsOK nArgs fn x86Data_guardsPlain thn _ _ t ht
      have hLe := exportR_labelsOK nArgs fn x86Data_guardsPlain els _ _ e he
      have hLk := exportR_labelsOK nArgs fn x86Data_guardsPlain k _ _ rk hk
      simp only [Exported.prepend]
      rw [show ifFrame fn d n rs (resolveVar d nArgs argName (fun _ => none) cond)
          t.code t.res t.depth e.code e.res e.depth x86Data ++ rk.code =
        (flagWord x86Data (regName d) (regName (d + 1))
            (resolveVar d nArgs argName (fun _ => none) cond)
          ++ [guardI (.Lopn [.reg (regName d)] (withWidthTag 64 "CMP")
                [.reg (regName d), .imm 0]), guardI (.Lcond (.reg "Z") (n + 1))])
        ++ ((labelI n :: (t.code ++ (ifResMoves rs d (t.depth + rs.length) t.res
            ++ (movImmI (regName (d + rs.length)) 1
              :: [guardI (.Lopn [.reg (regName (d + rs.length))] (withWidthTag 64 "CMP")
                    [.reg (regName (d + rs.length)), .imm 0]),
                  guardI (.Lcond (.reg "NZ") (n + 2))]))))
        ++ ((labelI (n + 1) :: (e.code ++ ifResMoves rs d (e.depth + rs.length) e.res))
        ++ (labelI (n + 2) :: rk.code)))
        from by simp [ifFrame]]
      exact nest_ifShape (a := t.next) (b := e.next) (by simp) (by simp) (iht _ _ _ ht)
        hLt.closed (fun l hl => hLt.range l hl) (by simp [movImmI]) (by simp [movImmI])
        (ihe _ _ _ he) hLe.closed (fun l hl => hLe.range l hl) (by simp) (by simp)
        (ihk _ _ _ hk) hLk.closed (fun l hl => (hLk.range l hl).1) ⟨hLt.le, hLe.le⟩

/-! ## 8. The two headline statements -/

/-- The names a code may read without a prior write: the argument names of a function of
    `nArgs` arguments and the symbol operands of its symbol-base loads. -/
def ExportE (nArgs : Nat) (code : List LinstrRM) (r : String) : Prop :=
  ArgName nArgs r ∨ ∃ i ∈ code, r ∈ symReads i

/-- The certificate of definite assignment of the export of a whole program, from the depth
    and the argument count `Γ.length` and the label `0`, which also holds the names of the
    returned operands at the end. -/
theorem exportR_cert (fn : String) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) {r : Exported}
    (h : exportR Γ.length fn p Γ.length 0 x86Data = some r) :
    ∃ D, Cert (ExportE Γ.length r.code) r.code D ∧
      ∀ x ∈ r.res.flatMap opNames, D r.code.length x ∨ ExportE Γ.length r.code x := by
  obtain ⟨hres, hB⟩ := exportR_blk Γ.length fn p _ 0 r h le_rfl
  obtain ⟨Λ, hb⟩ := hB (ExportE Γ.length r.code) (fun x hx => Or.inl hx)
    (fun i hi x hx => Or.inr ⟨i, hi, hx⟩) (fun _ => False)
    (fun x ⟨j, h1, h2, _⟩ => by omega)
  obtain ⟨D, hC, hY⟩ := cert_of_blk hb
  refine ⟨D, hC, fun x hx => ?_⟩
  rcases hres.names x hx with h' | h'
  · exact Or.inr (Or.inl h')
  · exact Or.inl (hY x (Or.inr h'))

/-- **Definite assignment of the region export** (`exportR_defInit`). Let `r` be the export of
    a program over the argument context `Γ`, from the depth and the argument count `Γ.length`
    and the label `0`, on x86, and let `E` be the argument names `argName j`, `j < Γ.length`,
    together with the symbol operands of the symbol-base loads of `r.code` (`ExportE`). Then:

    1. on every path of `r.code` along `webSuccs` from the entry, every name an instruction
       reads (`useNames`) is in `E` or is written (`defNames`) at an earlier position of the
       path (`DefInit`);
    2. on every path to the end of `r.code`, every name of a returned operand is in `E` or
       written on the path (`DefInitOut`);
    3. for names `outs` read after the code that are returned names or in `E`, every name of
       the register liveness table `liveRegTab r.code outs` at the entry is in `E` or is the
       array destination of a store or array zeroing of `r.code` that does not read it
       (`ArrOnly`): the register names live at the entry are argument names. -/
theorem exportR_defInit (fn : String) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) {r : Exported}
    (h : exportR Γ.length fn p Γ.length 0 x86Data = some r) :
    DefInit (ExportE Γ.length r.code) r.code
      ∧ DefInitOut (ExportE Γ.length r.code) r.code (r.res.flatMap opNames)
      ∧ ∀ outs : List String,
          (∀ x ∈ outs, x ∈ r.res.flatMap opNames ∨ ExportE Γ.length r.code x) →
          ∀ x ∈ tabAt (liveRegTab r.code outs) 0,
            ExportE Γ.length r.code x ∨ ArrOnly r.code x := by
  obtain ⟨D, hC, hres⟩ := exportR_cert fn p h
  refine ⟨hC.defInit, hC.defInitOut hres, fun outs ho => liveRegTab_entry hC fun x hx => ?_⟩
  rcases ho x hx with h' | h'
  · exact hres x h'
  · exact Or.inr h'

/-- **Forward reachability of the region export** (`exportR_fwdReach`). For every export `r` on
    x86: every position of `r.code`, every label among them, is reached from the entry by a
    walk along `webSuccs` whose every edge goes forward (`FwdPath`); and every back edge, a
    jump at `k` to a label at `p < k`, targets a loop header (`LoopHeader`): every edge into a
    position after `p + 1` up to `k` leaves a position after `p` up to `k`. -/
theorem exportR_fwdReach (nArgs : Nat) (fn : String) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) {d n : Nat} {r : Exported}
    (h : exportR nArgs fn p d n x86Data = some r) :
    (∀ k, k ≤ r.code.length → FwdPath r.code k)
      ∧ ∀ k q, BackEdge r.code k q → LoopHeader r.code q k :=
  ⟨fwdPath_of_noGoto (exportR_noGoto nArgs fn p d n r h),
    fun _ _ hb => loopHeader_of_nest (exportR_nest nArgs fn p d n r h) hb⟩

/-! ## 9. The steps between the export and the input of the allocation -/

section Transfer

theorem isLabel_eq (l : LLabel) (w : LinstrR) :
    JasminLsemLabeled.isLabel l w = decide (labelOf? w = some l) := by
  cases w with
  | Llabel k l' =>
      simp only [JasminLsemLabeled.isLabel, labelOf?, Option.some.injEq]
      by_cases h : l = l'
      · subst h; simp
      · simp [h, Ne.symm h]
  | _ => rfl

/-- `findLabelMem` of a mapped code whose instructions declare the labels of the original. -/
theorem findLabelMem_map {code : List LinstrRM} (f : LinstrRM → LinstrRM)
    (hlab : ∀ i ∈ code, labelOf? (f i).1 = labelOf? i.1) (l : LLabel) :
    findLabelMem l (code.map f) = findLabelMem l code := by
  unfold findLabelMem JasminLsemLabeled.findLabel
  rw [List.map_map, List.findIdx?_map, List.findIdx?_map]
  induction code with
  | nil => rfl
  | cons i c ih =>
      rw [List.findIdx?_cons, List.findIdx?_cons]
      simp only [Function.comp_apply, isLabel_eq, hlab i List.mem_cons_self]
      rw [ih fun j hj => hlab j (List.mem_cons_of_mem _ hj)]

/-- The successors of an instruction whose jump label and kind of jump are those of another,
    in codes whose labels are found at the same positions. -/
theorem webSuccs_congr {code code' : List LinstrRM} {k : Nat} {i i' : LinstrRM}
    (hj : jumpLabel? i'.1 = jumpLabel? i.1) (hg : isGoto i'.1 = isGoto i.1)
    (hf : ∀ l, findLabelMem l code' = findLabelMem l code) :
    webSuccs code' k i' = webSuccs code k i := by
  rcases i with ⟨w, t⟩
  rcases i' with ⟨w', t'⟩
  cases w <;> cases w' <;> simp_all [webSuccs, jumpLabel?, isGoto]

/-- **The certificate of a mapped code with a renaming of names.** For a map `f` of
    instructions that keeps the labels, the jump labels and the kind of jump of every
    instruction of `code`, whose read names are images under `σ` of the read names of the
    original and whose written names include the images of the written names, a certificate
    `D` of `code` gives the certificate `σ '' D` of `code.map f` at the names `σ '' E`. -/
theorem Cert.map {E : String → Prop} {code : List LinstrRM} {D : Nat → String → Prop}
    (hC : Cert E code D) (f : LinstrRM → LinstrRM) (σ : String → String)
    (hlab : ∀ i ∈ code, labelOf? (f i).1 = labelOf? i.1)
    (hjmp : ∀ i ∈ code, jumpLabel? (f i).1 = jumpLabel? i.1)
    (hgoto : ∀ i ∈ code, isGoto (f i).1 = isGoto i.1)
    (hU : ∀ i ∈ code, ∀ x ∈ useNames (f i).1, ∃ y ∈ useNames i.1, x = σ y)
    (hW : ∀ i ∈ code, ∀ y ∈ defNames i.1, σ y ∈ defNames (f i).1) :
    Cert (fun x => ∃ y, E y ∧ x = σ y) (code.map f) (fun k x => ∃ y, D k y ∧ x = σ y) where
  entry x := fun ⟨y, hy, _⟩ => hC.entry y hy
  use k i' hi' x hx := by
    rw [List.getElem?_map] at hi'
    obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hi'
    have hm := List.mem_of_getElem? hi
    obtain ⟨y, hy, rfl⟩ := hU i hm x hx
    rcases hC.use k i hi y hy with h | h
    · exact Or.inl ⟨y, h, rfl⟩
    · exact Or.inr ⟨y, h, rfl⟩
  step k i' hi' s hs x hx := by
    rw [List.getElem?_map] at hi'
    obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hi'
    have hm := List.mem_of_getElem? hi
    rw [webSuccs_congr (hjmp i hm) (hgoto i hm) (findLabelMem_map f hlab)] at hs
    obtain ⟨y, hy, rfl⟩ := hx
    rcases hC.step k i hi s hs y hy with h | h
    · exact Or.inl ⟨y, h, rfl⟩
    · exact Or.inr (hW i hm y h)

theorem useNames_renLinstrR (σ : String → String) (w : LinstrR) :
    useNames (JasminLsemExportTransfer.renLinstrR σ w) = (useNames w).map σ := by
  cases w with
  | Lopn ds o ss =>
      simp only [JasminLsemExportTransfer.renLinstrR, useNames_Lopn, List.flatMap_map,
        List.map_flatMap]
      congr 1
      funext a
      cases a <;> rfl
  | _ => rfl

theorem defNames_renLinstrR (σ : String → String) (w : LinstrR) :
    defNames (JasminLsemExportTransfer.renLinstrR σ w) = (defNames w).map σ := by
  cases w with
  | Lopn ds o ss =>
      simp only [JasminLsemExportTransfer.renLinstrR, defNames_Lopn, List.flatMap_map,
        List.map_flatMap]
      congr 1
      funext a
      cases a <;> rfl
  | _ => rfl

theorem renLinstrR_ctl (σ : String → String) (w : LinstrR) :
    labelOf? (JasminLsemExportTransfer.renLinstrR σ w) = labelOf? w
      ∧ jumpLabel? (JasminLsemExportTransfer.renLinstrR σ w) = jumpLabel? w
      ∧ isGoto (JasminLsemExportTransfer.renLinstrR σ w) = isGoto w := by
  cases w <;> exact ⟨rfl, rfl, rfl⟩

/-- **The certificate of a renamed code.** A certificate `D` of `code` gives the certificate
    `σ '' D` of `code.map (renRM σ)` at the names `σ '' E`. -/
theorem Cert.renRM {E : String → Prop} {code : List LinstrRM} {D : Nat → String → Prop}
    (hC : Cert E code D) (σ : String → String) :
    Cert (fun x => ∃ y, E y ∧ x = σ y) (code.map (JasminLsemExportTransfer.renRM σ))
      (fun k x => ∃ y, D k y ∧ x = σ y) :=
  hC.map _ σ (fun i _ => (renLinstrR_ctl σ i.1).1) (fun i _ => (renLinstrR_ctl σ i.1).2.1)
    (fun i _ => (renLinstrR_ctl σ i.1).2.2)
    (fun i _ x hx => by
      simp only [JasminLsemExportTransfer.renRM, useNames_renLinstrR, List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨y, hy, rfl⟩)
    (fun i _ y hy => by
      simp only [JasminLsemExportTransfer.renRM, defNames_renLinstrR]
      exact List.mem_map_of_mem hy)

/-- A control instruction: a label or a jump. -/
def IsCtl (i : LinstrRM) : Prop := labelOf? i.1 ≠ none ∨ jumpLabel? i.1 ≠ none

/-- **Nesting along an order-preserving map of positions.** If the positions of `code'` map
    monotonically to positions of `code`, injectively on control instructions, and each control
    instruction of `code'` declares the label and names the jump label of its image, then the
    nesting of `code` gives that of `code'`. -/
theorem Nest.of_embed {code code' : List LinstrRM} (h : Nest code) (e : Nat → Nat)
    (hmono : ∀ a b, a < b → b < code'.length → e a ≤ e b)
    (hctl : ∀ x ix, code'[x]? = some ix → IsCtl ix →
      ∃ i, code[e x]? = some i ∧ labelOf? i.1 = labelOf? ix.1 ∧ jumpLabel? i.1 = jumpLabel? ix.1)
    (hinj : ∀ a b ia ib, code'[a]? = some ia → code'[b]? = some ib → IsCtl ia → IsCtl ib →
      e a = e b → a = b) : Nest code' := by
  intro k p q j ik ip iq ij lk lj hk hjk hp hlp hpk hj hjj hq hlq hpq hqk
  have hck : IsCtl ik := Or.inr (by rw [hjk]; simp)
  have hcp : IsCtl ip := Or.inl (by rw [hlp]; simp)
  have hcq : IsCtl iq := Or.inl (by rw [hlq]; simp)
  have hcj : IsCtl ij := Or.inr (by rw [hjj]; simp)
  have hlen : ∀ x ix, code'[x]? = some ix → x < code'.length := fun x ix hx =>
    (List.getElem?_eq_some_iff.mp hx).1
  obtain ⟨ik', hk', -, hjk'⟩ := hctl k ik hk hck
  obtain ⟨ip', hp', hlp', -⟩ := hctl p ip hp hcp
  obtain ⟨iq', hq', hlq', -⟩ := hctl q iq hq hcq
  obtain ⟨ij', hj', -, hjj'⟩ := hctl j ij hj hcj
  have hlt : ∀ a b ia ib, code'[a]? = some ia → code'[b]? = some ib → IsCtl ia → IsCtl ib →
      a < b → e a < e b := by
    intro a b ia ib ha hb hca hcb hab
    rcases Nat.lt_or_eq_of_le (hmono a b hab (hlen b ib hb)) with h' | h'
    · exact h'
    · exact absurd (hinj a b ia ib ha hb hca hcb h') (by omega)
  have := h (e k) (e p) (e q) (e j) ik' ip' iq' ij' lk lj hk' (hjk'.trans hjk) hp'
    (hlp'.trans hlp) (hlt p k ip ik hp hk hcp hck hpk) hj' (hjj'.trans hjj) hq' (hlq'.trans hlq)
    (hlt p q ip iq hp hq hcp hcq hpq) (hlt q k iq ik hq hk hcq hck hqk)
  constructor
  · by_contra hc
    rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hc) with hc | rfl
    · have := hmono j p hc (hlen p ip hp); omega
    · omega
  · by_contra hc
    have h1 := hmono k j (Nat.lt_of_not_le hc) (hlen j ij hj)
    have h2 := hinj j k ij ik hj hk hcj hck (by omega)
    omega

/-- `findLabelMem` of a code followed by a code without labels. -/
theorem findLabelMem_append_noLabel (l : LLabel) (xs ys : List LinstrRM)
    (hy : ∀ i ∈ ys, labelOf? i.1 = none) : findLabelMem l (xs ++ ys) = findLabelMem l xs := by
  unfold findLabelMem JasminLsemLabeled.findLabel
  rw [List.map_append, List.findIdx?_append]
  have hnone : (ys.map Prod.fst).findIdx? (JasminLsemLabeled.isLabel l) = none := by
    rw [List.findIdx?_eq_none_iff]
    intro w hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    rw [isLabel_eq, hy i hi]
    simp
  rw [hnone]
  cases (xs.map Prod.fst).findIdx? (JasminLsemLabeled.isLabel l) <;> rfl

theorem labelOf?_of_isLopn {i : LinstrRM} (h : IsLopn i) : labelOf? i.1 = none := by
  obtain ⟨d, o, s, h⟩ := h; rw [h]; rfl

theorem jumpLabel?_of_isLopn {i : LinstrRM} (h : IsLopn i) : jumpLabel? i.1 = none := by
  obtain ⟨d, o, s, h⟩ := h; rw [h]; rfl

theorem webSuccs_of_isLopn {code : List LinstrRM} {k : Nat} {i : LinstrRM} (h : IsLopn i) :
    webSuccs code k i = [k + 1] := by
  obtain ⟨d, o, s, h⟩ := h
  rcases i with ⟨w, t⟩
  simp only at h
  subst h
  rfl

theorem findLabelMem_lt {code : List LinstrRM} {l : LLabel} {p : Nat}
    (h : findLabelMem l code = some p) : p < code.length := by
  obtain ⟨i, hi, -⟩ := findLabelMem_label h
  exact (List.getElem?_eq_some_iff.mp hi).1

theorem webSuccs_le {code : List LinstrRM} {k : Nat} {i : LinstrRM} (hk : k < code.length)
    {s : Nat} (hs : s ∈ webSuccs code k i) : s ≤ code.length := by
  rcases i with ⟨w, t⟩
  cases w with
  | Lgoto t' =>
      obtain ⟨f, l⟩ := t'
      simp only [webSuccs, List.mem_map, Option.mem_toList] at hs
      obtain ⟨p, hp, rfl⟩ := hs
      have := findLabelMem_lt hp; omega
  | Lcond c l =>
      simp only [webSuccs, List.mem_cons, List.mem_map, Option.mem_toList] at hs
      rcases hs with rfl | ⟨p, hp, rfl⟩
      · omega
      · have := findLabelMem_lt hp; omega
  | _ =>
      simp only [webSuccs, List.mem_singleton] at hs
      omega

/-- **The certificate of a code followed by straight operations.** A certificate `D` of `c`
    and a block judgement of operations `ys` from the names of `D` at the end of `c` to `Z`
    give a certificate of `c ++ ys` that holds `Z` at the end. -/
theorem Cert.append_blk {E : String → Prop} {Λ : LLabel → String → Prop} {c : List LinstrRM}
    {D : Nat → String → Prop} (hC : Cert E c D) {ys : List LinstrRM} {Z : String → Prop}
    (h : Blk E Λ (D c.length) ys Z) (hy : ∀ i ∈ ys, IsLopn i) :
    ∃ D', Cert E (c ++ ys) D' ∧ ∀ r, Z r → D' (c ++ ys).length r := by
  obtain ⟨Dy, hDy, h0, h1⟩ := h
  let D' : Nat → String → Prop := fun k => if k < c.length then D k else Dy (k - c.length)
  have hlab : ∀ l, findLabelMem l (c ++ ys) = findLabelMem l c := fun l =>
    findLabelMem_append_noLabel l c ys fun i hi => labelOf?_of_isLopn (hy i hi)
  have hD' : ∀ s, s ≤ c.length → ∀ r, D' s r → D s r := by
    intro s hs r hr
    simp only [D'] at hr
    split at hr
    · exact hr
    · have : s = c.length := by omega
      subst this
      exact h0 r (by simpa using hr)
  refine ⟨D', ⟨fun r hr => ?_, fun k i hi r hr => ?_, fun k i hi s hs r hr => ?_⟩, ?_⟩
  · exact hC.entry r (hD' 0 (Nat.zero_le _) r hr)
  · by_cases hk : k < c.length
    · rw [List.getElem?_append_left hk] at hi
      simp only [D', hk, ↓reduceIte]
      exact hC.use k i hi r hr
    · rw [List.getElem?_append_right (by omega)] at hi
      simp only [D', hk, ↓reduceIte]
      exact hDy.use _ i hi r hr
  · by_cases hk : k < c.length
    · rw [List.getElem?_append_left hk] at hi
      have hs' : s ∈ webSuccs c k i := by
        rwa [webSuccs_congr rfl rfl (fun l => hlab l)] at hs
      simp only [D', hk, ↓reduceIte]
      exact hC.step k i hi s hs' r (hD' s (webSuccs_le hk hs') r hr)
    · rw [List.getElem?_append_right (by omega)] at hi
      have hiy := hy _ (List.mem_of_getElem? hi)
      rw [webSuccs_of_isLopn hiy, List.mem_singleton] at hs
      subst hs
      simp only [D', hk, show ¬ k + 1 < c.length by omega, ↓reduceIte] at hr ⊢
      rw [show k + 1 - c.length = (k - c.length) + 1 by omega] at hr
      obtain ⟨d, o, s', he⟩ := hiy
      exact hDy.fall _ i hi (by rw [he]; rfl) r hr
  · intro r hr
    simp only [D', List.length_append, show ¬ c.length + ys.length < c.length by omega,
      ↓reduceIte, Nat.add_sub_cancel_left]
    exact h1 r hr

/-- The block of the first `k` words of the result copy of `src` into `Dn`: from names `X`
    in which, with `E`, the source and the buffer are, to the names of `X` and the version
    `copyName Dn k`. -/
theorem blk_resCopy {Λ : LLabel → String → Prop} (src Dn : String) (M : Nat) {X : String → Prop}
    (hs : X src ∨ E src) (hD : X Dn ∨ E Dn) :
    ∀ k, Blk E Λ X ((List.range k).flatMap (resCopyStep src Dn M))
      (fun r => X r ∨ (0 < k ∧ r = copyName Dn k))
  | 0 => blk_nil fun r hr => by simpa using hr
  | k + 1 => by
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      refine Blk.append (blk_resCopy src Dn M hs hD k) ?_
      unfold resCopyStep
      refine Blk.cons (blk_movI _ _ (by simp [opNames])) ?_
      refine Blk.cons (blk_opn _ _ _ _ fun x hx => ?_) ?_
      · simp only [List.flatMap_cons, List.flatMap_nil, opNames, List.append_nil,
          List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · rcases hs with h | h
          · exact Or.inl (Or.inl (Or.inl h))
          · exact Or.inr h
        · exact Or.inl (Or.inr rfl)
      refine (blk_opn _ _ _ _ fun x hx => ?_).mono (fun _ h => h) fun x hx => ?_
      · simp only [List.flatMap_cons, List.flatMap_nil, opNames, List.append_nil,
          List.mem_cons, List.not_mem_nil, or_false, List.cons_append, List.nil_append] at hx
        rcases hx with rfl | rfl | rfl
        · cases k with
          | zero =>
              simp only [copyName, ↓reduceIte]
              rcases hD with h | h
              · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
              · exact Or.inr h
          | succ k => exact Or.inl (Or.inl (Or.inl (Or.inr ⟨by omega, rfl⟩)))
        · exact Or.inl (Or.inl (Or.inr rfl))
        · exact Or.inl (Or.inr (by simp [opNames]))
      · rcases hx with h | ⟨-, rfl⟩
        · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
        · exact Or.inr (by simp [opNames])

theorem isLopn_resCopyCode (src Dn : String) (M : Nat) :
    ∀ i ∈ resCopyCode src Dn M, IsLopn i := by
  intro i hi
  obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp hi
  simp only [resCopyStep, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl <;> exact ⟨_, _, _, rfl⟩

/-- **The certificate of the code with the array result copy** (`regionLprogCopy`). A
    certificate `D` of `code` gives a certificate of `code ++ regionLprogCopy a callee ts code
    res` that holds the names of `D` at the end of `code` at its end, when the source and the
    buffer of the copy decided by `resCopyOf` are in `D` at the end of `code` or in `E`. -/
theorem Cert.regionLprogCopy {E : String → Prop} {code : List LinstrRM}
    {D : Nat → String → Prop} (hC : Cert E code D) (a : AbiNames)
    (callee : Option CalleeTab) (ts : List JasminTy) (res : List LOperand)
    (hcp : ∀ t src Dn m, callee = none → ts = [t] → resCopyOf a.outArg t code res = some (src, Dn, m) →
      (D code.length src ∨ E src) ∧ (D code.length Dn ∨ E Dn)) :
    ∃ D', Cert E (code ++ regionLprogCopy a callee ts code res) D' ∧
      ∀ r, D code.length r → D' (code ++ regionLprogCopy a callee ts code res).length r := by
  have hnil : ∃ D', Cert E (code ++ []) D' ∧ ∀ r, D code.length r → D' (code ++ []).length r :=
    ⟨D, by simpa using hC, fun r hr => by simpa using hr⟩
  unfold Haxc.regionLprogCopy
  split
  · next t =>
      split
      · next src Dn m hcopy =>
          obtain ⟨hs, hD⟩ := hcp t src Dn m rfl rfl hcopy
          obtain ⟨D', hC', hY⟩ := hC.append_blk (Λ := fun _ _ => False)
            (blk_resCopy (E := E) src Dn m hs hD m) (isLopn_resCopyCode src Dn m)
          exact ⟨D', hC', fun r hr => hY r (Or.inl hr)⟩
      · exact hnil
  · exact hnil

/-! ### The liveness instructions at the array self-moves -/

theorem findLabelMem_cons (l : LLabel) (i : LinstrRM) (c : List LinstrRM) :
    findLabelMem l (i :: c) =
      if labelOf? i.1 = some l then some 0 else (findLabelMem l c).map (· + 1) := by
  unfold findLabelMem JasminLsemLabeled.findLabel
  rw [List.map_cons, List.findIdx?_cons, isLabel_eq]
  by_cases h : labelOf? i.1 = some l <;> simp [h]

/-- **A certificate of a code with the control flow of another and fewer reads and
    writes.** Let each position of `c'` hold an instruction with the successors, in `c'`, of
    the instruction of `c` there, whose read names are read names of that instruction and
    which writes every name that instruction writes and does not read. A certificate `D` of
    `c` gives the certificate of `c'` that holds at each position the names of `D` there
    outside `E`. -/
theorem Cert.of_pointwise {E : String → Prop} {c c' : List LinstrRM} {D : Nat → String → Prop}
    (hC : Cert E c D)
    (hpt : ∀ k i', c'[k]? = some i' → ∃ i, c[k]? = some i ∧ webSuccs c' k i' = webSuccs c k i
      ∧ (∀ r ∈ useNames i'.1, r ∈ useNames i.1)
      ∧ ∀ r ∈ defNames i.1, r ∈ defNames i'.1 ∨ r ∈ useNames i.1) :
    Cert E c' (fun k r => D k r ∧ ¬ E r) := by
  refine ⟨fun r hr => hC.entry r hr.1, fun k i' hk r hr => ?_, fun k i' hk s hs r hr => ?_⟩
  · obtain ⟨i, hi, -, hu, -⟩ := hpt k i' hk
    by_cases hE : E r
    · exact Or.inr hE
    · rcases hC.use k i hi r (hu r hr) with h | h
      · exact Or.inl ⟨h, hE⟩
      · exact absurd h hE
  · obtain ⟨i, hi, hw, -, hd⟩ := hpt k i' hk
    rw [hw] at hs
    rcases hC.step k i hi s hs r hr.1 with h | h
    · exact Or.inl ⟨h, hr.2⟩
    · rcases hd r h with h | h
      · exact Or.inr h
      · rcases hC.use k i hi r h with h | h
        · exact Or.inl ⟨h, hr.2⟩
        · exact absurd h hr.2

/-- The liveness instructions at the self-moves keep the positions of the labels. -/
theorem findLabelMem_pinSelfMoves (l : LLabel) : ∀ c : List LinstrRM,
    findLabelMem l (Haxc.pinSelfMoves c) = findLabelMem l c
  | [] => rfl
  | [_] => rfl
  | i :: j :: rest => by
      by_cases hs : selfMoveB i j = true
      · obtain ⟨t, a, z, sc, w, n, rfl, rfl⟩ := selfMoveB_shape hs
        rw [pinSelfMoves_pair]
        simp only [findLabelMem_cons, findLabelMem_pinSelfMoves l rest]
        simp [labelOf?, selfPinLoad, selfPinStore]
      · rw [pinSelfMoves_cons (Bool.eq_false_iff.mpr hs)]
        simp only [findLabelMem_cons, findLabelMem_pinSelfMoves l (j :: rest)]

/-- **The certificate of the code with liveness instructions at its self-moves**
    (`pinSelfMoves`). A certificate `D` of `c` gives the certificate of `pinSelfMoves c` that
    holds at each position the names of `D` there outside `E`: the liveness instruction of
    a load reads its array base and index register and writes its scratch register, and that
    of a store reads the array base, the index and the scratch register; the array name the
    store writes is one it reads. -/
theorem Cert.selfMovesPinned {E : String → Prop} {c : List LinstrRM} {D : Nat → String → Prop}
    (hC : Cert E c D) : Cert E (Haxc.pinSelfMoves c) (fun k r => D k r ∧ ¬ E r) := by
  refine hC.of_pointwise fun k i' hk => ?_
  obtain ⟨i, hi, h⟩ := getElem?_pinSelfMoves c k i' hk
  refine ⟨i, hi, ?_⟩
  rcases h with rfl | ⟨t, a, z, sc, w, n, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · refine ⟨?_, fun r hr => hr, fun r hr => Or.inl hr⟩
    rcases i' with ⟨w, tg⟩
    cases w <;> simp only [webSuccs, findLabelMem_pinSelfMoves]
  · refine ⟨rfl, ?_, ?_⟩ <;> simp [selfPinLoad, useNames, defNames, opNames]
  · refine ⟨rfl, ?_, ?_⟩ <;> simp [selfPinStore, useNames, defNames, opNames]

/-- **The liveness instructions at the self-moves keep the nesting and the absence of
    unconditional jumps.** -/
theorem pinSelfMoves_nest_noGoto {c : List LinstrRM} (hN : Nest c) (hG : NoGoto c) :
    Nest (Haxc.pinSelfMoves c) ∧ NoGoto (Haxc.pinSelfMoves c) := by
  refine ⟨hN.of_embed id (fun a b hab _ => hab.le) (fun x ix hx hc => ?_)
    (fun a b _ _ _ _ _ _ h => h), fun i hi => ?_⟩
  · obtain ⟨i, hi, h⟩ := getElem?_pinSelfMoves c x ix hx
    rcases h with rfl | ⟨t, a, z, sc, w, n, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩
    · exact ⟨ix, hi, rfl, rfl⟩
    · exact absurd hc (by simp [IsCtl, selfPinLoad, labelOf?, jumpLabel?])
    · exact absurd hc (by simp [IsCtl, selfPinStore, labelOf?, jumpLabel?])
  · rcases mem_pinSelfMoves hi with h | ⟨t, a, z, sc, w, n, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩
    · exact hG i h
    · rfl
    · rfl

/-! ### The insertion of operations before instructions -/

/-- The code `C` with the operations `ins k i` inserted before its instruction `i` at the
    index `k` (from `n`). -/
def insertBefore (C : List LinstrRM) (ins : Nat → LinstrRM → List LinstrRM) (n : Nat) :
    List LinstrRM :=
  (C.zipIdx n).flatMap fun p => ins p.2 p.1 ++ [p.1]

/-- **The positions of a code with inserted operations.** The map `e` sends each position of
    the new code to the position of the instruction of `C` it is, or before which it is
    inserted, and the end to the end. -/
structure InsSpec (C : List LinstrRM) (ins : Nat → LinstrRM → List LinstrRM) (n : Nat)
    (e : Nat → Nat) : Prop where
  /-- Every position holds an instruction of `C`, followed by the next one, or an inserted
      operation, followed by a position of the same image. -/
  get : ∀ x y, (insertBefore C ins n)[x]? = some y →
    ∃ i, C[e x]? = some i ∧ ((y = i ∧ e (x + 1) = e x + 1)
      ∨ (y ∈ ins (n + e x) i ∧ e (x + 1) = e x))
  /-- The first position. -/
  first : e 0 = 0
  /-- The end. -/
  last : e (insertBefore C ins n).length = C.length
  /-- The labels. -/
  label : ∀ l, findLabelMem l C = (findLabelMem l (insertBefore C ins n)).map e

/-- The position map of a code with operations inserted before its first instruction: the
    `L` inserted positions and the first instruction to `0`, the rest by `e'` shifted. -/
def insMap (L : Nat) (e' : Nat → Nat) (x : Nat) : Nat := if x ≤ L then 0 else e' (x - L - 1) + 1

theorem insMap_le {L : Nat} {e' : Nat → Nat} {x : Nat} (h : x ≤ L) : insMap L e' x = 0 := by
  simp [insMap, h]

theorem insMap_gt {L : Nat} {e' : Nat → Nat} (x : Nat) : insMap L e' (L + 1 + x) = e' x + 1 := by
  simp [insMap, show ¬ L + 1 + x ≤ L by omega, show L + 1 + x - L - 1 = x by omega]

theorem insertBefore_cons (i : LinstrRM) (C : List LinstrRM)
    (ins : Nat → LinstrRM → List LinstrRM) (n : Nat) :
    insertBefore (i :: C) ins n = ins n i ++ (i :: insertBefore C ins (n + 1)) := by
  simp [insertBefore, List.zipIdx_cons]

theorem insSpec (ins : Nat → LinstrRM → List LinstrRM)
    (hins : ∀ k i, ∀ y ∈ ins k i, IsLopn y) :
    ∀ (C : List LinstrRM) (n : Nat), ∃ e, InsSpec C ins n e
  | [], n => ⟨fun _ => 0, fun x y hx => by simp [insertBefore] at hx, rfl, rfl,
      fun l => by simp [insertBefore, findLabelMem, JasminLsemLabeled.findLabel]⟩
  | i :: C, n => by
      obtain ⟨e', he'⟩ := insSpec ins hins C (n + 1)
      refine ⟨insMap (ins n i).length e', ⟨fun x y hx => ?_, insMap_le (Nat.zero_le _), ?_,
        fun l => ?_⟩⟩
      · rw [insertBefore_cons] at hx
        by_cases hxL : x < (ins n i).length
        · rw [List.getElem?_append_left hxL] at hx
          refine ⟨i, by rw [insMap_le (by omega)]; rfl, Or.inr ⟨?_, ?_⟩⟩
          · rw [insMap_le (by omega), Nat.add_zero]
            exact List.mem_of_getElem? hx
          · rw [insMap_le (by omega), insMap_le (by omega)]
        · rw [List.getElem?_append_right (by omega)] at hx
          by_cases hxe : x = (ins n i).length
          · subst hxe
            simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hx
            subst hx
            refine ⟨i, by rw [insMap_le le_rfl]; rfl, Or.inl ⟨rfl, ?_⟩⟩
            rw [insMap_le le_rfl, show (ins n i).length + 1 = (ins n i).length + 1 + 0 from rfl,
              insMap_gt, he'.first]
          · obtain ⟨x', rfl⟩ : ∃ x', x = (ins n i).length + 1 + x' :=
              ⟨x - (ins n i).length - 1, by omega⟩
            rw [show (ins n i).length + 1 + x' - (ins n i).length = x' + 1 by omega,
              List.getElem?_cons_succ] at hx
            obtain ⟨i', hi', h'⟩ := he'.get x' y hx
            have he2 : insMap (ins n i).length e' ((ins n i).length + 1 + x' + 1)
                = e' (x' + 1) + 1 := by
              rw [show (ins n i).length + 1 + x' + 1 = (ins n i).length + 1 + (x' + 1) by omega,
                insMap_gt]
            refine ⟨i', by rw [insMap_gt, List.getElem?_cons_succ]; exact hi', ?_⟩
            rw [insMap_gt, he2]
            rcases h' with ⟨rfl, h2⟩ | ⟨h1, h2⟩
            · exact Or.inl ⟨rfl, by rw [h2]⟩
            · exact Or.inr ⟨by rwa [show n + (e' x' + 1) = n + 1 + e' x' by omega], by rw [h2]⟩
      · rw [insertBefore_cons]
        simp only [List.length_append, List.length_cons]
        rw [show (ins n i).length + ((insertBefore C ins (n + 1)).length + 1)
          = (ins n i).length + 1 + (insertBefore C ins (n + 1)).length by omega, insMap_gt,
          he'.last]
      · rw [insertBefore_cons, JasminLsemMemFlagPrefix.findLabelMem_prefix l _ _ (hins n i),
          findLabelMem_cons l i C, findLabelMem_cons l i (insertBefore C ins (n + 1)),
          he'.label l]
        split
        · simp [insMap_le]
        · simp only [Option.map_map]
          congr 1
          funext q
          simp only [Function.comp_apply]
          rw [show q + 1 + (ins n i).length = (ins n i).length + 1 + q by omega, insMap_gt]

theorem InsSpec.mono {C : List LinstrRM} {ins : Nat → LinstrRM → List LinstrRM} {n : Nat}
    {e : Nat → Nat} (he : InsSpec C ins n e) :
    ∀ a b, a ≤ b → b ≤ (insertBefore C ins n).length → e a ≤ e b := by
  intro a b hab hb
  induction b with
  | zero => rw [Nat.le_zero.mp hab]
  | succ b ih =>
      rcases Nat.lt_or_eq_of_le hab with h | rfl
      · have h1 := ih (by omega) (by omega)
        obtain ⟨y, hy⟩ : ∃ y, (insertBefore C ins n)[b]? = some y :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        obtain ⟨i, -, h'⟩ := he.get b y hy
        rcases h' with ⟨-, h2⟩ | ⟨-, h2⟩ <;> omega
      · exact le_rfl

/-- **The certificate of a code with inserted operations.** A certificate `D` of `C` and
    inserted operations whose read names are in `D` at the position of the instruction they
    precede, or in `E`, give a certificate of the new code that holds the names of `D` at the
    end of `C` at its end. -/
theorem Cert.insertBefore {E : String → Prop} {C : List LinstrRM} {D : Nat → String → Prop}
    (hC : Cert E C D) (ins : Nat → LinstrRM → List LinstrRM)
    (hins : ∀ k i, ∀ y ∈ ins k i, IsLopn y)
    (hread : ∀ k i, C[k]? = some i → ∀ y ∈ ins k i, ∀ r ∈ useNames y.1, D k r ∨ E r) :
    ∃ D', Cert E (insertBefore C ins 0) D' ∧
      ∀ r, D C.length r → D' (insertBefore C ins 0).length r := by
  obtain ⟨e, he⟩ := insSpec ins hins C 0
  refine ⟨fun x => D (e x), ⟨fun r hr => ?_, fun k y hk r hr => ?_,
    fun k y hk s hs r hr => ?_⟩, fun r hr => by show D (e _) r; rw [he.last]; exact hr⟩
  · rw [he.first] at hr; exact hC.entry r hr
  · obtain ⟨i, hi, h'⟩ := he.get k y hk
    rcases h' with ⟨rfl, -⟩ | ⟨hy, -⟩
    · exact hC.use _ y hi r hr
    · exact hread _ i hi y (by simpa using hy) r hr
  · obtain ⟨i, hi, h'⟩ := he.get k y hk
    rcases h' with ⟨rfl, h2⟩ | ⟨hy, h2⟩
    · -- an instruction of `C`
      have hlt := (List.getElem?_eq_some_iff.mp hk).1
      have hjump : ∀ (l : LLabel) (pc : Nat), findLabelMem l (RegionExportDefInit.insertBefore C ins 0) = some pc →
          findLabelMem l C = some (e pc) ∧ e (pc + 1) = e pc + 1 := by
        intro l pc hpc
        refine ⟨by rw [he.label l, hpc]; rfl, ?_⟩
        obtain ⟨iq, hq, hl⟩ := findLabelMem_label hpc
        obtain ⟨i', -, h''⟩ := he.get pc iq hq
        rcases h'' with ⟨-, h3⟩ | ⟨h1, -⟩
        · exact h3
        · have := labelOf?_of_isLopn (hins _ _ iq h1); rw [this] at hl; cases hl
      have hs' : ∃ t, s = t + 1 ∧ e (t + 1) = e t + 1 ∧ e t + 1 ∈ webSuccs C (e k) y := by
        rcases y with ⟨w, tg⟩
        cases w with
        | Lgoto t' =>
            obtain ⟨f, l⟩ := t'
            simp only [webSuccs, List.mem_map, Option.mem_toList] at hs ⊢
            obtain ⟨pc, hpc, rfl⟩ := hs
            exact ⟨pc, rfl, (hjump l pc hpc).2, e pc, (hjump l pc hpc).1, rfl⟩
        | Lcond cd l =>
            simp only [webSuccs, List.mem_cons, List.mem_map, Option.mem_toList] at hs ⊢
            rcases hs with rfl | ⟨pc, hpc, rfl⟩
            · exact ⟨k, rfl, h2, Or.inl rfl⟩
            · exact ⟨pc, rfl, (hjump l pc hpc).2, Or.inr ⟨e pc, (hjump l pc hpc).1, rfl⟩⟩
        | _ =>
            simp only [webSuccs, List.mem_singleton] at hs ⊢
            exact ⟨k, hs, h2, rfl⟩
      obtain ⟨t, rfl, ht, hs''⟩ := hs'
      rw [ht] at hr
      exact hC.step _ _ hi _ hs'' r hr
    · -- an inserted operation
      rw [webSuccs_of_isLopn (hins _ _ _ hy), List.mem_singleton] at hs
      subst hs
      rw [h2] at hr
      exact Or.inl hr

/-- **The insertion of operations keeps the nesting and the absence of unconditional
    jumps.** -/
theorem insertBefore_nest_noGoto {C : List LinstrRM} (ins : Nat → LinstrRM → List LinstrRM)
    (hins : ∀ k i, ∀ y ∈ ins k i, IsLopn y) (hN : Nest C) (hG : NoGoto C) :
    Nest (insertBefore C ins 0) ∧ NoGoto (insertBefore C ins 0) := by
  obtain ⟨e, he⟩ := insSpec ins hins C 0
  have horig : ∀ x y, (insertBefore C ins 0)[x]? = some y → IsCtl y →
      C[e x]? = some y ∧ e (x + 1) = e x + 1 := by
    intro x y hx hc
    obtain ⟨i, hi, h'⟩ := he.get x y hx
    rcases h' with ⟨rfl, h2⟩ | ⟨hy, -⟩
    · exact ⟨hi, h2⟩
    · have h1 := labelOf?_of_isLopn (hins _ _ _ hy)
      have h2 := jumpLabel?_of_isLopn (hins _ _ _ hy)
      exact absurd hc (by simp [IsCtl, h1, h2])
  refine ⟨hN.of_embed e (fun a b hab hb => he.mono a b hab.le hb.le)
    (fun x ix hx hc => ⟨ix, (horig x ix hx hc).1, rfl, rfl⟩)
    (fun a b ia ib ha hb hca hcb hab => ?_), fun y hy => ?_⟩
  · have hla := (List.getElem?_eq_some_iff.mp ha).1
    have hlb := (List.getElem?_eq_some_iff.mp hb).1
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have h1 := (horig a ia ha hca).2
      have := he.mono (a + 1) b (by omega) (by omega); omega
    · have h1 := (horig b ib hb hcb).2
      have := he.mono (b + 1) a (by omega) (by omega); omega
  · obtain ⟨x, hx⟩ := List.mem_iff_getElem?.mp hy
    obtain ⟨i, hi, h'⟩ := he.get x y hx
    rcases h' with ⟨rfl, -⟩ | ⟨h1, -⟩
    · exact hG y (List.mem_of_getElem? hi)
    · exact isGoto_of_isLopn (hins _ _ _ h1)

/-! ### The liveness instructions at the back edges -/

/-- The liveness instructions before the instruction `i` at the index `k` of `C`: the
    instruction `backEdgePin` at the register liveness table `liveRegTab C []` before a jump,
    and none before any other instruction. -/
def pinsOf (C : List LinstrRM) (k : Nat) (i : LinstrRM) : List LinstrRM :=
  match i.1 with
  | .Lcond _ l => backEdgePin (liveRegTab C []) C k l
  | .Lgoto (_, l) => backEdgePin (liveRegTab C []) C k l
  | _ => []

theorem backEdgePins_eq (C : List LinstrRM) : backEdgePins C = insertBefore C (pinsOf C) 0 := by
  unfold backEdgePins insertBefore
  dsimp only
  congr 1
  funext p
  rcases p with ⟨⟨w, t⟩, k⟩
  cases w <;> rfl

theorem isLopn_backEdgePin (T : Array (List String)) (C : List LinstrRM) (k : Nat)
    (l : LLabel) : ∀ y ∈ backEdgePin T C k l, IsLopn y := by
  intro y hy
  unfold backEdgePin at hy
  dsimp only at hy
  split at hy
  · split at hy
    · simp only [List.mem_singleton] at hy; subst hy; exact ⟨_, _, _, rfl⟩
    · simp at hy
  · simp at hy

theorem isLopn_pinsOf (C : List LinstrRM) (k : Nat) (i : LinstrRM) :
    ∀ y ∈ pinsOf C k i, IsLopn y := by
  intro y hy
  rcases i with ⟨w, t⟩
  cases w with
  | Lcond c l => exact isLopn_backEdgePin _ C k l y hy
  | Lgoto tg =>
      obtain ⟨f, l⟩ := tg
      exact isLopn_backEdgePin _ C k l y hy
  | _ => exact (List.not_mem_nil (show y ∈ ([] : List LinstrRM) from hy)).elim

/-- The destinations of every operation of the code are register operands. -/
def RegDsts (C : List LinstrRM) : Prop :=
  ∀ i ∈ C, ∀ ds o ss, i.1 = .Lopn ds o ss → ∀ d ∈ ds, ∃ x, d = LOperand.reg x

/-- The liveness instructions at the self-moves keep the register destinations. -/
theorem regDsts_pinSelfMoves {c : List LinstrRM} (hR : RegDsts c) :
    RegDsts (Haxc.pinSelfMoves c) := by
  intro i hi
  rcases mem_pinSelfMoves hi with h | ⟨t, a, z, sc, w, n, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩
  · exact hR i h
  · intro ds o ss he d hd
    simp only [selfPinLoad, LinstrR.Lopn.injEq] at he
    obtain ⟨rfl, -, -⟩ := he
    exact ⟨t, List.mem_singleton.mp hd⟩
  · intro ds o ss he d hd
    simp only [selfPinStore, LinstrR.Lopn.injEq] at he
    obtain ⟨rfl, -, -⟩ := he
    exact ⟨_, List.mem_singleton.mp hd⟩

theorem regReads_sub {w : LinstrR} (h : ∀ ds o ss, w = .Lopn ds o ss → ∀ d ∈ ds, ∃ x, d = .reg x) :
    ∀ x ∈ regReads w, x ∈ useNames w := by
  intro x hx
  cases w with
  | Lopn ds o ss =>
      simp only [regReads, List.mem_append, List.mem_flatMap] at hx
      rcases hx with ⟨a, ha, hx⟩ | ⟨a, ha, hx⟩
      · simp only [useNames_Lopn, List.mem_flatMap]
        refine ⟨a, ha, ?_⟩
        cases a <;> simp_all [opNames]
      · obtain ⟨y, rfl⟩ := h ds o ss rfl a ha
        simp at hx
  | _ => exact (List.not_mem_nil (show x ∈ ([] : List String) from hx)).elim

theorem defNames_sub_regWrites {w : LinstrR}
    (h : ∀ ds o ss, w = .Lopn ds o ss → ∀ d ∈ ds, ∃ x, d = .reg x) :
    ∀ x ∈ defNames w, x ∈ regWrites w := by
  intro x hx
  cases w with
  | Lopn ds o ss =>
      simp only [defNames_Lopn, List.mem_flatMap] at hx
      obtain ⟨a, ha, hx⟩ := hx
      obtain ⟨y, rfl⟩ := h ds o ss rfl a ha
      simp only [opNames, List.mem_singleton] at hx
      subst hx
      simp only [regWrites, List.mem_flatMap]
      exact ⟨_, ha, by simp⟩
  | _ => exact (List.not_mem_nil (show x ∈ ([] : List String) from hx)).elim

/-- The fold of `regExposed`: a name it returns was returned before, or is read by an
    instruction before which no instruction writes it and which the names written before do
    not contain. -/
theorem regExposed_fold (is : List LinstrR) :
    ∀ (A W : List String) (x : String),
      x ∈ (is.foldl (fun (acc : List String × List String) i =>
        (acc.1 ++ ((regReads i).filter fun x => !acc.2.contains x && !acc.1.contains x).eraseDups,
          acc.2 ++ regWrites i)) (A, W)).1 →
      x ∈ A ∨ (x ∉ W ∧ ∃ m, m < is.length ∧ (∃ i, is[m]? = some i ∧ x ∈ regReads i)
        ∧ ∀ m', m' < m → ∀ i', is[m']? = some i' → x ∉ regWrites i') := by
  induction is with
  | nil => intro A W x hx; exact Or.inl hx
  | cons i is ih =>
      intro A W x hx
      rw [List.foldl_cons] at hx
      rcases ih _ _ x hx with h | ⟨hW, m, hm, hr, hw⟩
      · rcases List.mem_append.mp h with h | h
        · exact Or.inl h
        · rw [List.mem_eraseDups, List.mem_filter] at h
          simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
            decide_eq_false_iff_not] at h
          exact Or.inr ⟨h.2.1, 0, by simp, ⟨i, rfl, h.1⟩, fun m' hm' => absurd hm' (by omega)⟩
      · rw [List.mem_append, not_or] at hW
        refine Or.inr ⟨hW.1, m + 1, by simpa using hm, by simpa using hr, fun m' hm' i' hi' => ?_⟩
        cases m' with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hi'
            subst hi'
            exact hW.2
        | succ m' => exact hw m' (by omega) i' (by simpa using hi')

/-- A name of `regExposed is` is read by an instruction of `is` before which no instruction
    writes it. -/
private theorem exists_first_read_of_mem_regExposed {is : List LinstrR} {x : String}
    (h : x ∈ regExposed is) :
    ∃ m, m < is.length ∧ (∃ i, is[m]? = some i ∧ x ∈ regReads i)
      ∧ ∀ m', m' < m → ∀ i', is[m']? = some i' → x ∉ regWrites i' := by
  rcases regExposed_fold is [] [] x h with h | ⟨-, h⟩
  · simp at h
  · exact h

/-- **A walk into a loop passes the position after its header.** If the label at `p` heads
    the loop ending at `k`, every path to a position from `p + 1` to `k` has a prefix that is
    a path to `p + 1`. -/
theorem LoopHeader.entry {code : List LinstrRM} {p k : Nat} (hL : LoopHeader code p k)
    {y : Nat} {ks : List Nat} (hp : Path code y ks) (h1 : p + 1 ≤ y) (h2 : y ≤ k) :
    ∃ ks', Path code (p + 1) ks' ∧ ∀ z ∈ ks', z ∈ ks := by
  induction hp with
  | nil => omega
  | @cons z s zs i hz hi hs ih =>
      by_cases hs1 : s = p + 1
      · subst hs1
        exact ⟨_, Path.cons hz hi hs, fun _ h => h⟩
      · obtain ⟨hz1, hz2⟩ := hL z i s hi hs (by omega) h2
        obtain ⟨ks', hk', hsub⟩ := ih (by omega) (by omega)
        exact ⟨ks', hk', fun w hw => List.mem_cons_of_mem _ (hsub w hw)⟩

/-- **The walk along the next positions.** In a code without unconditional jumps, a path to
    `a` extends by the next positions to every `b` from `a` up to the end. -/
theorem Path.fall {code : List LinstrRM} (hG : NoGoto code) {a : Nat} {ks : List Nat}
    (hp : Path code a ks) :
    ∀ d, a + d ≤ code.length → Path code (a + d) ((List.range d).reverse.map (a + ·) ++ ks)
  | 0, _ => by simpa using hp
  | d + 1, h => by
      have hp' := Path.fall hG hp d (by omega)
      have hlt : a + d < code.length := by omega
      have hi := List.getElem?_eq_getElem hlt
      have := Path.cons hp' hi (mem_webSuccs_next (hG _ (List.getElem_mem hlt)))
      rw [show a + d + 1 = a + (d + 1) by omega] at this
      simpa [List.range_succ] using this

/-- **The names a liveness instruction reads are definitely assigned at its back edge.** In a
    code with definite assignment, without unconditional jumps, with nested jumps and with
    register destinations, every name exposed in the slice from the label at `p` to a jump at
    `k > p` to that label is in `E` or written on every path to `k`. -/
theorem exposed_mustW {E : String → Prop} {code : List LinstrRM} (hD : DefInit E code)
    (hG : NoGoto code) (hN : Nest code) (hR : RegDsts code) {k p : Nat} {i : LinstrRM}
    {l : LLabel} (hk : code[k]? = some i) (hl : jumpLabel? i.1 = some l)
    (hp : findLabelMem l code = some p) (hpk : p < k) {x : String}
    (hx : x ∈ regExposed (((code.drop p).take (k - p)).map Prod.fst)) :
    E x ∨ MustW code k x := by
  obtain ⟨m, hm, ⟨w, hw, hxr⟩, hnw⟩ := exists_first_read_of_mem_regExposed hx
  simp only [List.length_map, List.length_take, List.length_drop] at hm
  have hlen : k < code.length := (List.getElem?_eq_some_iff.mp hk).1
  rw [List.getElem?_map, List.getElem?_take_of_lt (by omega), List.getElem?_drop] at hw
  obtain ⟨im, him, rfl⟩ := Option.map_eq_some_iff.mp hw
  have hmem := List.mem_of_getElem? him
  have hregs : ∀ ds o ss, im.1 = .Lopn ds o ss → ∀ d ∈ ds, ∃ x, d = .reg x := hR im hmem
  have hxu := regReads_sub hregs x hxr
  -- the read is after the label
  have hm0 : 1 ≤ m := by
    by_contra h0
    have : m = 0 := by omega
    subst this
    obtain ⟨ip, hip, hlp⟩ := findLabelMem_label hp
    rw [Nat.add_zero] at him
    have heq : ip = im := Option.some.inj (hip.symm.trans him)
    subst heq
    rcases ip with ⟨wi, ti⟩
    cases wi with
    | Llabel _ _ => exact (List.not_mem_nil (show x ∈ ([] : List String) from hxr)).elim
    | _ => simp [labelOf?] at hlp
  by_cases hE : E x
  · exact Or.inl hE
  refine Or.inr fun ks hks => ?_
  have hL := loopHeader_of_nest hN ⟨i, l, hk, hl, hp, hpk⟩
  obtain ⟨ks', hks', hsub⟩ := hL.entry hks (by omega) le_rfl
  have hpath := Path.fall hG hks' (m - 1) (by omega)
  rw [show p + 1 + (m - 1) = p + m by omega] at hpath
  rcases hD _ _ im hpath him x hxu with h | ⟨j, hj, ij, hij, hxj⟩
  · exact absurd h hE
  · rcases List.mem_append.mp hj with hj | hj
    · -- a write inside the slice before the read is excluded
      simp only [List.mem_map, List.mem_reverse, List.mem_range] at hj
      obtain ⟨d, hd, rfl⟩ := hj
      exfalso
      have hij' : ((((code.drop p).take (k - p)).map Prod.fst))[1 + d]? = some ij.1 := by
        rw [List.getElem?_map, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
          show p + (1 + d) = p + 1 + d by omega, hij]
        rfl
      exact hnw (1 + d) (by omega) ij.1 hij'
        (defNames_sub_regWrites (hR ij (List.mem_of_getElem? hij)) x hxj)
    · exact ⟨j, hsub j hj, ij, hij, hxj⟩

/-- A certificate at the names `E` is a certificate at every larger set of names. -/
theorem Cert.monoE {E E' : String → Prop} {code : List LinstrRM} {D : Nat → String → Prop}
    (h : Cert E code D) (hE : ∀ r, E r → E' r) : Cert E' code D where
  entry := h.entry
  use k i hi r hr := (h.use k i hi r hr).imp_right (hE r)
  step := h.step

/-- **The live names under a certificate.** For a certificate `D` of `code` and names `outs`
    read after the code that are in `D` at the end or in `E`, a name live at a position
    (`PLiveR`) is in `D` there, in `E`, or of `ArrOnly`. -/
theorem Cert.pLiveR {E : String → Prop} {code : List LinstrRM} {D : Nat → String → Prop}
    (hC : Cert E code D) {outs : List String} (ho : ∀ r ∈ outs, D code.length r ∨ E r)
    {k : Nat} {r : String} (h : RegionAllocMapComplete.PLiveR code outs k r) :
    LiveBound E code D k r := by
  induction h with
  | read hi hy =>
      rcases hC.use _ _ hi _ hy with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  | @next k i y hi hg hd _ ih =>
      have hs : k + 1 ∈ webSuccs code k i := by
        rcases i with ⟨w, t⟩
        cases w with
        | Lgoto x => exact absurd rfl (hg x)
        | _ => simp [webSuccs]
      by_cases hdn : y ∈ defNames i.1
      · rcases i with ⟨w, t⟩
        cases w with
        | Lopn ds o ss =>
            by_cases hu : y ∈ useNames (LinstrR.Lopn ds o ss)
            · rcases hC.use _ _ hi _ hu with h | h
              · exact Or.inl h
              · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr ⟨_, List.mem_of_getElem? hi, hdn, hd ds o ss rfl, hu⟩)
        | _ => simp [defNames] at hdn
      · exact liveBound_back hC hi hs ih hdn
  | jump hi hl hp _ ih =>
      refine liveBound_back hC hi (mem_webSuccs_label hl hp) ih ?_
      rw [defNames_nonLopn fun ds o ss h => by rw [h] at hl; simp [jumpLabel?] at hl]
      simp
  | out hy =>
      rcases ho _ hy with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)

/-- A name live at the position of a label is live at the next position. -/
private theorem pLiveR_succ_of_labelOf {code : List LinstrRM} {outs : List String} {p : Nat}
    {ip : LinstrRM}
    {l : LLabel} (hp : code[p]? = some ip) (hl : labelOf? ip.1 = some l) {r : String}
    (h : RegionAllocMapComplete.PLiveR code outs p r) :
    RegionAllocMapComplete.PLiveR code outs (p + 1) r := by
  rcases ip with ⟨w, t⟩
  cases w <;> simp only [labelOf?, reduceCtorEq] at hl
  cases h with
  | read hi hy =>
      rw [hp] at hi
      cases hi
      simp [useNames] at hy
  | next _ _ _ h' => exact h'
  | jump hi hj _ _ =>
      rw [hp] at hi
      cases hi
      simp [jumpLabel?] at hj
  | out _ => simp at hp

/-- The names written on every path to the position after the label of a loop header are
    written on every path to its back edge. -/
theorem MustW.loop {code : List LinstrRM} {p k : Nat} (hL : LoopHeader code p k)
    (hpk : p < k) {r : String} (h : MustW code (p + 1) r) : MustW code k r := by
  intro ks hks
  obtain ⟨ks', hks', hsub⟩ := hL.entry hks (by omega) le_rfl
  obtain ⟨j, hj, i, h1, h2⟩ := h ks' hks'
  exact ⟨j, hsub j hj, i, h1, h2⟩

/-- **The names of the liveness table at the label of a back edge.** In a code with definite
    assignment and nested jumps, every name of `liveRegTab code []` at the position `p` of
    the label of a jump at `k > p` is written on every path to `k`, is in `E`, or is the
    array destination of a store or an array zeroing that does not read it (`ArrOnly`). -/
theorem tab_mustW {E : String → Prop} {code : List LinstrRM} (hD : DefInit E code)
    (hN : Nest code) {k p : Nat} {i : LinstrRM} {l : LLabel} (hk : code[k]? = some i)
    (hl : jumpLabel? i.1 = some l) (hp : findLabelMem l code = some p) (hpk : p < k)
    {x : String} (hx : x ∈ tabAt (liveRegTab code []) p) :
    MustW code k x ∨ E x ∨ ArrOnly code x := by
  obtain ⟨ip, hip, hlp⟩ := findLabelMem_label hp
  have h1 := pLiveR_succ_of_labelOf hip hlp (RegionAllocMapComplete.pLiveR_of_liveRegTab hx)
  rcases hD.cert.pLiveR (outs := []) (by simp) h1 with h | h
  · exact Or.inl (MustW.loop (loopHeader_of_nest hN ⟨i, l, hk, hl, hp, hpk⟩) hpk h)
  · exact Or.inr h

/-- **The liveness pins keep definite assignment up to the array destinations.** In a code
    with definite assignment at `E`, without unconditional jumps, with nested jumps and with
    register destinations, the code with the liveness instructions `backEdgePins` has a
    certificate of definite assignment at the names of `E` and the names of `ArrOnly C`, that
    holds at its end the names written on every path to the end of the code. A name a pin
    reads is exposed in the loop text (`exposed_mustW`) or in the table at the label
    (`tab_mustW`); the second kind can be an `ArrOnly` name not written on a path to the
    jump. -/
theorem backEdgePins_cert {E : String → Prop} {C : List LinstrRM} (hD : DefInit E C)
    (hG : NoGoto C) (hN : Nest C) (hR : RegDsts C) :
    ∃ D', Cert (fun r => E r ∨ ArrOnly C r) (backEdgePins C) D'
      ∧ ∀ r, MustW C C.length r → D' (backEdgePins C).length r := by
  rw [backEdgePins_eq]
  refine Cert.insertBefore (hD.cert.monoE fun r h => Or.inl h) (pinsOf C) (isLopn_pinsOf C)
    fun k i hk y hy r hr => ?_
  have hpin : ∀ l, jumpLabel? i.1 = some l → y ∈ backEdgePin (liveRegTab C []) C k l →
      MustW C k r ∨ (E r ∨ ArrOnly C r) := by
    intro l hl hy'
    unfold backEdgePin at hy'
    dsimp only at hy'
    split at hy'
    · next p hp =>
        split at hy'
        · next hc =>
            simp only [List.mem_singleton] at hy'
            subst hy'
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
            simp only [useNames_Lopn, List.flatMap_map, List.mem_flatMap, opNames,
              List.mem_singleton] at hr
            obtain ⟨x, hx, rfl⟩ := hr
            unfold backEdgePinNames at hx
            rcases List.mem_append.mp hx with hx | hx
            · rcases exposed_mustW hD hG hN hR hk hl hp hc.1 hx with h | h
              · exact Or.inr (Or.inl h)
              · exact Or.inl h
            · exact tab_mustW hD hN hk hl hp hc.1 (List.mem_filter.mp hx).1
        · simp at hy'
    · simp at hy'
  rcases i with ⟨w, t⟩
  cases w with
  | Lcond c l => exact hpin l rfl hy
  | Lgoto tg =>
      obtain ⟨f, l⟩ := tg
      exact hpin l rfl hy
  | _ => exact (List.not_mem_nil (show y ∈ ([] : List LinstrRM) from hy)).elim

theorem backEdgePins_nest_noGoto {C : List LinstrRM} (hN : Nest C) (hG : NoGoto C) :
    Nest (backEdgePins C) ∧ NoGoto (backEdgePins C) := by
  rw [backEdgePins_eq]
  exact insertBefore_nest_noGoto _ (isLopn_pinsOf C) hN hG

/-! ### Register destinations -/

/-- The destinations of an operation are register operands. -/
def RegShape (i : LinstrRM) : Prop :=
  ∀ ds o ss, i.1 = .Lopn ds o ss → ∀ d ∈ ds, ∃ x, d = .reg x

theorem regShape_reg {i : LinstrRM} {x o : String} {ss : List LOperand}
    (h : i.1 = .Lopn [.reg x] o ss) : RegShape i := by
  intro ds o' ss' h' d hd
  rw [h] at h'
  cases h'
  simp only [List.mem_singleton] at hd
  exact ⟨x, hd⟩

theorem regShape_nonLopn {i : LinstrRM} (h : ∀ ds o ss, i.1 ≠ .Lopn ds o ss) : RegShape i :=
  fun ds o ss h' => absurd h' (h ds o ss)

theorem regShape_movI (dst : String) (src : LOperand) : RegShape (movI dst src) :=
  regShape_reg rfl

theorem regShape_movs {α : Type} (l : List α) (f : α → String) (g : α → LOperand) :
    ∀ i ∈ l.map (fun a => movI (f a) (g a)), RegShape i := by
  intro i hi
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp hi
  exact regShape_movI _ _

theorem regShape_arrMoves (z t : String) (mv : List ArrMove) :
    ∀ i ∈ arrMoves z t mv, RegShape i := by
  intro i hi
  obtain ⟨a, -, hi⟩ := List.mem_flatMap.mp hi
  simp only [arrMove, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> exact regShape_reg rfl

theorem regShape_typedMoves (z t : String) (tp : List (JasminTy × String × String)) :
    ∀ i ∈ typedMoves z t tp, RegShape i := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact regShape_arrMoves _ _ _ i hi
  · exact regShape_movs _ (fun p : String × String => p.1) (fun p => .reg p.2) i hi

theorem regShape_seedMoves (car : List String) (ops : List LOperand) :
    ∀ i ∈ seedMoves car ops, RegShape i :=
  regShape_movs _ (fun p : String × LOperand => p.1) (fun p => p.2)

theorem regShape_arrParMoves (z t : String) (D : Nat) (mv : List ArrMove) :
    ∀ i ∈ arrParMoves z t D mv, RegShape i := by
  intro i hi
  unfold arrParMoves at hi
  split at hi
  · exact regShape_arrMoves _ _ _ i hi
  · rcases List.mem_append.mp hi with hi | hi <;> exact regShape_arrMoves _ _ _ i hi

theorem regShape_parMoves (D : Nat) (tgts : List String) (ops : List LOperand) :
    ∀ i ∈ ExportRegions.parMoves D tgts ops, RegShape i := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact regShape_movs _ (fun p : LOperand × Nat => regName (D + p.2)) (fun p => p.1) i hi
  · exact regShape_movs _ (fun p : String × Nat => p.1) (fun p => .reg (regName (D + p.2))) i hi

theorem regShape_advanceOps (idx ctr : String) : ∀ i ∈ advanceOps idx ctr, RegShape i := by
  intro i hi
  simp only [advanceOps, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> exact regShape_reg rfl

theorem regShape_ifResMoves (rs : List JasminTy) (d D : Nat) (ops : List LOperand) :
    ∀ i ∈ ifResMoves rs d D ops, RegShape i := by
  intro i hi
  unfold ifResMoves at hi
  rcases List.mem_append.mp hi with hi | hi
  · split at hi
    · simp at hi
    · rcases List.mem_cons.mp hi with rfl | hi
      · exact regShape_movI _ _
      · exact regShape_arrParMoves _ _ _ _ i hi
  · exact regShape_parMoves _ _ _ i hi

theorem regShape_flagWord (I : IsaData) (r z : String) (op : LOperand) :
    ∀ i ∈ flagWord I r z op, RegShape i := by
  intro i hi
  unfold flagWord at hi
  split at hi
  · split at hi
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> exact regShape_reg rfl
    · simp at hi
  · simp only [List.mem_singleton] at hi
    subst hi
    exact regShape_movI _ _

theorem regShape_guard2 (c cc : String) (l : LLabel) :
    ∀ i ∈ [guardI (.Lopn [.reg c] (withWidthTag 64 "CMP") [.reg c, .imm 0]),
      guardI (.Lcond (.reg cc) l)], RegShape i := by
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact regShape_reg rfl
  · exact regShape_nonLopn fun _ _ _ h => by cases h

/-- **The export has register destinations.** -/
theorem exportR_regDsts (nArgs : Nat) (fn : String) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) :
    ∀ (d n : Nat) (r : Exported), exportR nArgs fn p d n x86Data = some r → RegDsts r.code := by
  have hlab : ∀ l, RegShape (labelI l) := fun l => regShape_nonLopn fun _ _ _ h => by cases h
  induction p with
  | ret vs =>
      intro d n r h
      simp only [exportR, Option.some.injEq] at h
      subst h
      intro i hi; simp at hi
  | var e k ih =>
      intro d n r h
      simp only [exportR, Option.map_eq_some_iff] at h
      obtain ⟨rk, hk, rfl⟩ := h
      intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · obtain ⟨o, ss, tag, hb, -⟩ := bindOps_shape nArgs e d
        rw [hb, List.mem_singleton] at hi
        subst hi
        exact regShape_reg rfl
      · exact ih _ _ _ hk i hi
  | call f args k ih =>
      intro d n r h
      obtain ⟨-, rk, hk, rfl⟩ := exportR_call_eq_some.mp h
      intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact regShape_reg rfl
      · exact ih _ _ _ hk i hi
  | forLoop count inits body k ihb ihk =>
      intro d n r h
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hk, rfl⟩ := h
      have hB := ihb _ _ _ hb
      have hK := ihk _ _ _ hk
      show ∀ i ∈ _, RegShape i
      simp only [Exported.prepend, forArrFrame,
        List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
        implies_true, and_true, List.map_cons, List.map_nil]
      repeat' constructor
      all_goals first
        | exact hB
        | exact hK
        | exact hT'
        | exact hE
        | exact hlab _
        | exact regShape_movI _ _
        | exact regShape_typedMoves _ _ _
        | exact regShape_seedMoves _ _
        | exact regShape_arrParMoves _ _ _ _
        | exact regShape_parMoves _ _ _
        | exact regShape_advanceOps _ _
        | exact regShape_ifResMoves _ _ _ _
        | exact regShape_flagWord _ _ _ _
        | exact regShape_reg rfl
        | exact regShape_nonLopn fun _ _ _ h => by cases h
  | ifThenElse cond thn els k iht ihe ihk =>
      intro d n r h
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨t, ht, e, he, rk, hk, rfl⟩ := h
      have hT' := iht _ _ _ ht
      have hE := ihe _ _ _ he
      have hK := ihk _ _ _ hk
      show ∀ i ∈ _, RegShape i
      simp only [Exported.prepend, ifFrame,
        List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
        implies_true, and_true, List.map_cons, List.map_nil]
      repeat' constructor
      all_goals first
        | exact hB
        | exact hK
        | exact hT'
        | exact hE
        | exact hlab _
        | exact regShape_movI _ _
        | exact regShape_typedMoves _ _ _
        | exact regShape_seedMoves _ _
        | exact regShape_arrParMoves _ _ _ _
        | exact regShape_parMoves _ _ _
        | exact regShape_advanceOps _ _
        | exact regShape_ifResMoves _ _ _ _
        | exact regShape_flagWord _ _ _ _
        | exact regShape_reg rfl
        | exact regShape_nonLopn fun _ _ _ h => by cases h
  | whileLoop inits body k ihb ihk =>
      intro d n r h
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hk, rfl⟩ := h
      have hB := ihb _ _ _ hb
      have hK := ihk _ _ _ hk
      show ∀ i ∈ _, RegShape i
      simp only [Exported.prepend, whileFrame,
        List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
        implies_true, and_true, List.map_cons, List.map_nil]
      repeat' constructor
      all_goals first
        | exact hB
        | exact hK
        | exact hT'
        | exact hE
        | exact hlab _
        | exact regShape_movI _ _
        | exact regShape_typedMoves _ _ _
        | exact regShape_seedMoves _ _
        | exact regShape_arrParMoves _ _ _ _
        | exact regShape_parMoves _ _ _
        | exact regShape_advanceOps _ _
        | exact regShape_ifResMoves _ _ _ _
        | exact regShape_flagWord _ _ _ _
        | exact regShape_reg rfl
        | exact regShape_nonLopn fun _ _ _ h => by cases h

/-! ### The chain of the input of the allocation -/

theorem regShape_renRM (σ : String → String) {i : LinstrRM} (h : RegShape i) :
    RegShape (JasminLsemExportTransfer.renRM σ i) := by
  intro ds o ss hi d hd
  rcases i with ⟨w, t⟩
  cases w with
  | Lopn ds' o' ss' =>
      simp only [JasminLsemExportTransfer.renRM, JasminLsemExportTransfer.renLinstrR,
        LinstrR.Lopn.injEq] at hi
      obtain ⟨rfl, rfl, rfl⟩ := hi
      obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hd
      obtain ⟨x, rfl⟩ := h ds' o' ss' rfl d' hd'
      exact ⟨σ x, rfl⟩
  | _ => cases hi

/-- The renaming keeps the nesting, the absence of unconditional jumps and the register
    destinations. -/
theorem renRM_nest_noGoto_regDsts {C : List LinstrRM} (σ : String → String) (hN : Nest C)
    (hG : NoGoto C) (hR : RegDsts C) :
    Nest (C.map (JasminLsemExportTransfer.renRM σ))
      ∧ NoGoto (C.map (JasminLsemExportTransfer.renRM σ))
      ∧ RegDsts (C.map (JasminLsemExportTransfer.renRM σ)) := by
  refine ⟨hN.of_embed id (fun a b hab _ => hab.le) (fun x ix hx _ => ?_)
    (fun a b _ _ _ _ _ _ h => h), fun i hi => ?_, fun i hi => ?_⟩
  · rw [List.getElem?_map] at hx
    obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hx
    exact ⟨i, hi, (renLinstrR_ctl σ i.1).1.symm, (renLinstrR_ctl σ i.1).2.1.symm⟩
  · obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hi
    rw [show (JasminLsemExportTransfer.renRM σ i').1 = JasminLsemExportTransfer.renLinstrR σ i'.1
      from rfl, (renLinstrR_ctl σ i'.1).2.2]
    exact hG i' hi'
  · obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hi
    exact regShape_renRM σ (hR i' hi')

/-- The names of a renamed set. -/
def img (σ : String → String) (P : String → Prop) (x : String) : Prop := ∃ y, P y ∧ x = σ y

theorem isLopn_regionLprogCopy (a : AbiNames) (callee : Option CalleeTab) (ts : List JasminTy)
    (code : List LinstrRM) (res : List LOperand) :
    ∀ i ∈ Haxc.regionLprogCopy a callee ts code res, IsLopn i := by
  intro i hi
  unfold Haxc.regionLprogCopy at hi
  split at hi
  · split at hi
    · exact isLopn_resCopyCode _ _ _ i hi
    · simp at hi
  · simp at hi

theorem regShape_regionLprogCopy (a : AbiNames) (callee : Option CalleeTab)
    (ts : List JasminTy) (code : List LinstrRM) (res : List LOperand) :
    ∀ i ∈ Haxc.regionLprogCopy a callee ts code res, RegShape i := by
  intro i hi
  unfold Haxc.regionLprogCopy at hi
  split at hi
  · split at hi
    · obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp hi
      simp only [resCopyStep, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl <;> exact regShape_reg rfl
    · simp at hi
  · simp at hi

/-! ### The liveness instruction at entry -/

/-- **A certificate of a code preceded by operations.** A certificate `D` of `C` and
    operations `P` whose read names are in `E` give a certificate of `P ++ C` that holds the
    names of `D` at the end of `C` at its end. -/
theorem Cert.prefix {E : String → Prop} {C : List LinstrRM} {D : Nat → String → Prop}
    (hC : Cert E C D) (P : List LinstrRM) (hP : ∀ y ∈ P, IsLopn y)
    (hr : ∀ y ∈ P, ∀ r ∈ useNames y.1, E r) :
    ∃ D', Cert E (P ++ C) D' ∧ ∀ r, D C.length r → D' (P ++ C).length r := by
  have hsucc : ∀ x y, P.length ≤ x → C[x - P.length]? = some y → ∀ s ∈ webSuccs (P ++ C) x y,
      P.length ≤ s ∧ s - P.length ∈ webSuccs C (x - P.length) y := by
    intro x y hx _ s hs
    have hf := fun l => JasminLsemMemFlagPrefix.findLabelMem_prefix l P C hP
    rcases y with ⟨w, t⟩
    cases w with
    | Lgoto tg =>
        obtain ⟨f, l⟩ := tg
        simp only [webSuccs, hf, List.mem_map, Option.mem_toList, Option.map_eq_some_iff] at hs ⊢
        obtain ⟨q, ⟨q', hq', rfl⟩, rfl⟩ := hs
        exact ⟨by omega, q', hq', by omega⟩
    | Lcond c l =>
        simp only [webSuccs, hf, List.mem_cons, List.mem_map, Option.mem_toList,
          Option.map_eq_some_iff] at hs ⊢
        rcases hs with rfl | ⟨q, ⟨q', hq', rfl⟩, rfl⟩
        · exact ⟨by omega, Or.inl (by omega)⟩
        · exact ⟨by omega, Or.inr ⟨q', hq', by omega⟩⟩
    | _ =>
        simp only [webSuccs, List.mem_singleton] at hs ⊢
        omega
  refine ⟨fun x r => P.length ≤ x ∧ D (x - P.length) r,
    ⟨fun r h => hC.entry r (by simpa using h.2), fun x y hx r hr' => ?_,
      fun x y hx s hs r hr' => ?_⟩, fun r h => ⟨by simp, by simpa using h⟩⟩
  · by_cases hxL : x < P.length
    · rw [List.getElem?_append_left hxL] at hx
      exact Or.inr (hr y (List.mem_of_getElem? hx) r hr')
    · rw [List.getElem?_append_right (by omega)] at hx
      rcases hC.use _ y hx r hr' with h | h
      · exact Or.inl ⟨by omega, h⟩
      · exact Or.inr h
  · by_cases hxL : x < P.length
    · rw [List.getElem?_append_left hxL] at hx
      rw [webSuccs_of_isLopn (hP y (List.mem_of_getElem? hx)), List.mem_singleton] at hs
      subst hs
      obtain ⟨h1, h2⟩ := hr'
      rw [show x + 1 - P.length = 0 by omega] at h2
      exact absurd h2 (hC.entry r)
    · rw [List.getElem?_append_right (by omega)] at hx
      obtain ⟨hsL, hs'⟩ := hsucc x y (by omega) hx s hs
      rcases hC.step _ y hx _ hs' r hr'.2 with h | h
      · exact Or.inl ⟨by omega, h⟩
      · exact Or.inr h

/-- The liveness instruction at entry `arrBasePins a C` as instructions of the code given to
    the allocation. -/
def entryPinRM (a : AbiNames) (C : List LinstrRM) : List LinstrRM :=
  (arrBasePins a C).map fun i => (i.li_i, .reg none)

/-- `entryPinRM` is `arrBasePins` with the instruction index `0`. -/
theorem entryPinRM_map (a : AbiNames) (C : List LinstrRM) :
    (entryPinRM a C).map (fun i => (⟨0, i.1⟩ : Linstr)) = arrBasePins a C := by
  unfold entryPinRM arrBasePins
  dsimp only
  split <;> rfl

theorem isLopn_entryPinRM (a : AbiNames) (C : List LinstrRM) :
    ∀ y ∈ entryPinRM a C, IsLopn y := by
  intro y hy
  unfold entryPinRM arrBasePins at hy
  dsimp only at hy
  split at hy
  · simp at hy
  · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hy
    subst hy
    exact ⟨_, _, _, rfl⟩

/-- A name of the entry pin is an array base of `a` paired with an argument register, or a
    name of the register liveness table at entry. -/
theorem mem_entryPinNames {a : AbiNames} {C : List LinstrRM} {x : String}
    (h : x ∈ entryPinNames a C) :
    x ∈ (argBasePairsPos (a.outArg :: a.inArgs) a.abiArgs).map Prod.fst
      ∨ x ∈ tabAt (liveRegTab C []) 0 := by
  unfold entryPinNames at h
  dsimp only at h
  rcases List.mem_append.mp h with h | h
  · left
    split at h
    · exact h
    · simp at h
  · right
    simp only [List.mem_filter, Bool.and_eq_true, List.contains_eq_mem,
      decide_eq_true_eq] at h
    exact h.2.1

/-- The names the entry pin reads are those of `entryPinNames`. -/
theorem entryPinRM_reads {a : AbiNames} {C : List LinstrRM} {y : LinstrRM}
    (hy : y ∈ entryPinRM a C) {x : String} (hx : x ∈ useNames y.1) :
    x ∈ entryPinNames a C := by
  unfold entryPinRM arrBasePins at hy
  dsimp only at hy
  split at hy
  · simp at hy
  · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hy
    subst hy
    simp only [useNames_Lopn, List.flatMap_map, List.mem_flatMap, opNames,
      List.mem_singleton] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    exact hz

/-- **The entry pin keeps definite assignment.** For a code `C` with a certificate of
    definite assignment at `E` whose end needs no name, the code `entryPinRM a C ++ C` has
    definite assignment at the names of `E`, of `ArrOnly C` and the array bases of `a` paired
    with an argument register: the argument names the pin reads are live at entry, hence in
    `E` or of `ArrOnly C` (`liveRegTab_entry`). -/
theorem entryPin_defInit {E : String → Prop} {C : List LinstrRM} {D : Nat → String → Prop}
    (hC : Cert E C D) (a : AbiNames) :
    DefInit (fun x => E x ∨ ArrOnly C x
        ∨ x ∈ (argBasePairsPos (a.outArg :: a.inArgs) a.abiArgs).map Prod.fst)
      (entryPinRM a C ++ C) := by
  obtain ⟨D', hC', -⟩ := (hC.monoE (E' := fun x => E x ∨ ArrOnly C x
      ∨ x ∈ (argBasePairsPos (a.outArg :: a.inArgs) a.abiArgs).map Prod.fst)
      fun x h => Or.inl h).prefix (entryPinRM a C) (isLopn_entryPinRM a C)
    fun y hy x hx => by
      rcases mem_entryPinNames (entryPinRM_reads hy hx) with h | h
      · exact Or.inr (Or.inr h)
      · rcases liveRegTab_entry hC (outs := []) (by simp) x h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
  exact hC'.defInit

end Transfer

/-! ## 10. The webs of the export -/

section Webs

open CatCrypt.Crypto.SecureCompilation.X86Backend.ArrWebs (webRen webB webInstrB stepRen
  webB_instr webB_entry webB_exit webB_obs webB_live_pred webSuccs_webRen)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg (renArr coInstrB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete (wrArr rdArr armOf Succ
  ClassA coInstrB_iff)

/-- The renaming of array positions keeps the label, the jump label and the kind of jump of
    an instruction. -/
theorem ctl_renArr (σ : String → String) (i : LinstrRM) :
    labelOf? (renArr σ i).1 = labelOf? i.1 ∧ jumpLabel? (renArr σ i).1 = jumpLabel? i.1
      ∧ isGoto (renArr σ i).1 = isGoto i.1 := by
  obtain ⟨w, tag⟩ := i
  cases w with
  | Lopn d o s =>
      have : ∃ d' o' s', (renArr σ (.Lopn d o s, tag)).1 = .Lopn d' o' s' := by
        cases tag <;>
          simp only [renArr, X86Backend.ImageCoalesceCfg.renLoad,
            X86Backend.ImageCoalesceCfg.renStore, X86Backend.ImageCoalesceCfg.renZero,
            X86Backend.ImageCoalesceCfg.renStoreImm] <;>
          (try split) <;> (try split) <;>
          first
            | exact ⟨_, _, _, rfl⟩
            | exact X86Backend.ImageCoalesceCfg.renCallW_lopn ⟨_, _, _, rfl⟩
      obtain ⟨d', o', s', h⟩ := this
      rw [h]
      exact ⟨rfl, rfl, rfl⟩
  | _ => cases tag <;> exact ⟨rfl, rfl, rfl⟩

theorem getElem?_webRen (w : Nat → String → String) (ao : String → Option Nat)
    (code : List LinstrRM) (k : Nat) :
    (webRen w ao code)[k]? = code[k]?.map fun i => renArr (stepRen w ao k i) i := by
  simp [webRen, List.getElem?_mapIdx]

theorem length_webRen (w : Nat → String → String) (ao : String → Option Nat)
    (code : List LinstrRM) : (webRen w ao code).length = code.length := by
  simp [webRen]

/-- The renamed code has the paths of the code. -/
theorem path_webRen (w : Nat → String → String) (ao : String → Option Nat)
    {code : List LinstrRM} {k : Nat} {ks : List Nat} :
    Path (webRen w ao code) k ks ↔ Path code k ks := by
  constructor
  · intro h
    induction h with
    | nil => exact Path.nil
    | cons _ hi hs ih =>
        rw [getElem?_webRen] at hi
        obtain ⟨i, hi', rfl⟩ := Option.map_eq_some_iff.mp hi
        rw [webSuccs_webRen] at hs
        exact Path.cons ih hi' hs
  · intro h
    induction h with
    | nil => exact Path.nil
    | @cons k s ks i _ hi hs ih =>
        refine Path.cons ih (i := renArr (stepRen w ao k i) i) ?_ ?_
        · rw [getElem?_webRen, hi]; rfl
        · rw [webSuccs_webRen]; exact hs

theorem shadowCall_of_armOf {i : LinstrRM} {dst f : String} {srcs : List LOperand}
    (h : armOf i = .call dst f srcs) : LprogIsa.shadowCall? i.1 = some (dst, f, srcs) := by
  unfold armOf at h
  repeat' (first | split at h | split_ifs at h)
  all_goals simp_all

theorem armOf_of_shadowCall {i : LinstrRM} {dst f : String} {srcs : List LOperand}
    (h : LprogIsa.shadowCall? i.1 = some (dst, f, srcs)) : armOf i = .call dst f srcs := by
  unfold armOf
  rw [h]

theorem armOf_of_arrShapeB {i : LinstrRM} (h : LprogIsa.shadowCall? i.1 = none)
    (hs : X86Backend.ImageCoalesceCfg.arrShapeB i = true) : armOf i = .arr := by
  unfold armOf
  rw [h]
  simp [hs]

/-- Outside a shadow instruction of a call, the array an instruction writes is that of a
    store or of an array zeroing. -/
theorem wrArr_eq_arrWrite {ao : String → Option Nat} {i : LinstrRM}
    (h : LprogIsa.shadowCall? i.1 = none) :
    wrArr ao i = X86Backend.ImageStraightRoute.arrWrite i := by
  by_cases hs : X86Backend.ImageCoalesceCfg.arrShapeB i = true
  · unfold wrArr
    rw [armOf_of_arrShapeB h hs]
    rfl
  · rw [X86Backend.ImageCoalesceCfg.arrWrite_of_arrShapeB (by simpa using hs)]
    unfold wrArr
    rcases ha : armOf i with ⟨dst, f, srcs⟩ | _ | _ | lbl | lbl | _ | _
    · rw [shadowCall_of_armOf ha] at h
      cases h
    all_goals first | rfl |
      exact X86Backend.ImageCoalesceCfg.arrWrite_of_arrShapeB (by simpa using hs)

/-- Outside a shadow instruction of a call, the renaming of array positions keeps every
    written name other than the array written by a store or an array zeroing. -/
theorem defNames_renArr_noCall (σ : String → String) {i : LinstrRM}
    (h : LprogIsa.shadowCall? i.1 = none) {y : String} (hy : y ∈ defNames i.1)
    (hw : X86Backend.ImageStraightRoute.arrWrite i ≠ some y) :
    y ∈ defNames (renArr σ i).1 := by
  obtain ⟨w, tag⟩ := i
  cases tag <;> simp only [renArr] <;>
    (try simp only [X86Backend.ImageCoalesceCfg.renCallW_of_none h]) <;>
    (try simp only [X86Backend.ImageCoalesceCfg.renLoad, X86Backend.ImageCoalesceCfg.renStore,
      X86Backend.ImageCoalesceCfg.renZero, X86Backend.ImageCoalesceCfg.renStoreImm]) <;>
    (repeat' split) <;>
    simp_all [X86Backend.ImageStraightRoute.arrWrite, storeStruct?, zeroStruct?,
      storeImmStruct?, defNames, JasminLsemExportRewrites.opNames]

/-- **The names the renaming of array positions writes**: outside a shadow instruction of a
    call, a name written by `renArr σ i` is written by `i` or is the image under `σ` of a name
    written by `i`. -/
theorem mem_defNames_renArr (σ : String → String) {i : LinstrRM}
    (h : LprogIsa.shadowCall? i.1 = none) {x : String} (hx : x ∈ defNames (renArr σ i).1) :
    x ∈ defNames i.1 ∨ ∃ y ∈ defNames i.1, x = σ y := by
  obtain ⟨w, tag⟩ := i
  cases tag <;> simp only [renArr] at hx <;>
    (try simp only [X86Backend.ImageCoalesceCfg.renCallW_of_none h] at hx) <;>
    (try simp only [X86Backend.ImageCoalesceCfg.renLoad, X86Backend.ImageCoalesceCfg.renStore,
      X86Backend.ImageCoalesceCfg.renZero, X86Backend.ImageCoalesceCfg.renStoreImm] at hx) <;>
    (repeat' split at hx) <;>
    simp_all [defNames, JasminLsemExportRewrites.opNames]

/-- The renaming of array positions writes the image of the array of a store or an array
    zeroing. -/
theorem defNames_renArr_arrWrite (σ : String → String) {i : LinstrRM} {d : String}
    (h : X86Backend.ImageStraightRoute.arrWrite i = some d) :
    σ d ∈ defNames (renArr σ i).1 := by
  obtain ⟨w, tag⟩ := i
  cases tag <;> simp only [renArr] <;> simp only [X86Backend.ImageStraightRoute.arrWrite] at h <;>
    (try cases h) <;>
    (try simp only [X86Backend.ImageCoalesceCfg.renStore, X86Backend.ImageCoalesceCfg.renZero,
      X86Backend.ImageCoalesceCfg.renStoreImm]) <;>
    (repeat' split) <;>
    simp_all [storeStruct?, zeroStruct?, storeImmStruct?, defNames,
      JasminLsemExportRewrites.opNames]

/-- A position of `webSuccs` other than the fall-through of a constant-taken guard is a
    successor of the arm of an instruction that passes the coalescing check. -/
theorem succ_of_mem_webSuccs {σ : String → String} {code : List LinstrRM}
    {L : Nat → List String} {k k' : Nat} {i : LinstrRM} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} (hc : coInstrB σ code L k i aa ao = true)
    (hs : k' ∈ webSuccs code k i)
    (hg : ¬ (X86Backend.ConstGuard.constTakenB code k = true ∧ k' = k + 1)) :
    Succ code k i k' := by
  obtain ⟨w, tag⟩ := i
  have hA := ((coInstrB_iff _ _ _ _ _ _ _).mp hc).1
  unfold Succ
  by_cases hg : ∃ x l, w = .Lgoto (x, l)
  · obtain ⟨x, l, rfl⟩ := hg
    have ha : armOf (.Lgoto (x, l), tag) = .goto l := by
      cases tag <;> rfl
    rw [ha]
    simp only [webSuccs, List.mem_map, Option.mem_toList] at hs
    obtain ⟨p, hp, rfl⟩ := hs
    exact ⟨p, hp, rfl⟩
  by_cases hcnd : ∃ c l, w = .Lcond c l
  · obtain ⟨c, l, rfl⟩ := hcnd
    have ha : armOf (.Lcond c l, tag) = .cc l := by
      unfold armOf
      cases tag <;>
        simp [LprogIsa.shadowCall?, X86Backend.ImageCoalesceCfg.arrShapeB,
          JasminLsemMemFlagGuard.cmpArgs?, JasminLsemMemFlagGuard.movRegArgs?, loadStruct?,
          storeStruct?, zeroStruct?, storeImmStruct?] <;>
        unfold JasminLsemMemFlagGuard.flagCondCC? <;> split <;> (try rfl) <;> rename_i heq <;>
        split at heq <;> simp_all
    rw [ha]
    simp only [webSuccs, List.mem_cons, List.mem_map, Option.mem_toList] at hs
    rcases hs with rfl | ⟨p, hp, rfl⟩
    · exact Or.inl ⟨rfl, Bool.eq_false_iff.mpr fun h => hg ⟨h, rfl⟩⟩
    · exact Or.inr ⟨p, hp, rfl⟩
  have hk : k' = k + 1 := by
    cases w <;> simp [webSuccs] at hs <;>
      first | exact hs | exact absurd ⟨_, _, rfl⟩ hg | exact absurd ⟨_, _, rfl⟩ hcnd
  subst hk
  rcases ha : armOf (w, tag) with ⟨dst, f, srcs⟩ | _ | _ | lbl | lbl | _ | _
  all_goals first | rfl | exact Or.inl ⟨rfl, Bool.eq_false_iff.mpr fun h => hg ⟨h, rfl⟩⟩ | skip
  · exfalso
    unfold armOf at ha
    repeat' (first | split at ha | split_ifs at ha)
    all_goals simp_all
  · rw [ha] at hA
    exact hA.elim

/-- **The liveness certificate of an accepted map is closed backwards** along the edges at
    every name the instruction does not write as an array. -/
theorem mem_L_of_webSuccs {w : Nat → String → String} {code : List LinstrRM}
    {L : Nat → List String} {obs : List String} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} (hc : webB w code L obs aa ao = true) {k k' : Nat}
    {i : LinstrRM} (hi : code[k]? = some i) (hs : k' ∈ webSuccs code k i) {r : String}
    (hr : r ∈ L k') (hw : wrArr ao i ≠ some r) : r ∈ L k := by
  have h := webB_instr hc hi
  unfold webInstrB at h
  simp only [Bool.and_eq_true] at h
  by_cases hg : X86Backend.ConstGuard.constTakenB code k = true ∧ k' = k + 1
  · obtain ⟨hg, rfl⟩ := hg
    have h2 := h.2
    simp only [hg, Bool.not_true, Bool.false_or] at h2
    exact X86Backend.ImageCoalesceCfg.subB_spec h2 r hr
  · exact ((coInstrB_iff _ _ _ _ _ _ _).mp h.1.1.1).2.1.2 k' r
      (succ_of_mem_webSuccs h.1.1.1 hs hg) (fun e => hw e.symm) hr

/-- The array an instruction writes is written under its renaming. -/
theorem defNames_renArr_wr {σ : String → String} {code : List LinstrRM}
    {L : Nat → List String} {k : Nat} {i : LinstrRM} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} (hc : coInstrB σ code L k i aa ao = true) {d : String}
    (hd : wrArr ao i = some d) : σ d ∈ defNames (renArr σ i).1 := by
  rcases hsc : LprogIsa.shadowCall? i.1 with _ | ⟨dst, f, srcs⟩
  · rw [wrArr_eq_arrWrite hsc] at hd
    exact defNames_renArr_arrWrite σ hd
  · have hA := ((coInstrB_iff _ _ _ _ _ _ _).mp hc).1
    rw [armOf_of_shadowCall hsc] at hA
    unfold wrArr at hd
    rw [armOf_of_shadowCall hsc] at hd
    obtain ⟨-, -, rfl⟩ := Option.map_eq_some_iff.mp hd
    obtain ⟨w, tag⟩ := i
    dsimp only at hsc
    rw [LprogIsa.eq_callShadow_of_shadowCall? hsc,
      X86Backend.ImageCoalesceCfg.renArr_callShadow _ _ _ hA.1]
    simp [LprogIsa.callShadow, defNames, JasminLsemExportRewrites.opNames]

/-- A name an instruction writes other than as its array is written by the renamed
    instruction under its own name. -/
theorem defNames_renArr_keep {σ : String → String} {code : List LinstrRM}
    {L : Nat → List String} {k : Nat} {i : LinstrRM} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} (hc : coInstrB σ code L k i aa ao = true) {y : String}
    (hy : y ∈ defNames i.1) (hw : wrArr ao i ≠ some y) : y ∈ defNames (renArr σ i).1 := by
  rcases hsc : LprogIsa.shadowCall? i.1 with _ | ⟨dst, f, srcs⟩
  · rw [wrArr_eq_arrWrite hsc] at hw
    exact defNames_renArr_noCall σ hsc hy hw
  · have hA := ((coInstrB_iff _ _ _ _ _ _ _).mp hc).1
    rw [armOf_of_shadowCall hsc] at hA
    unfold wrArr at hw
    rw [armOf_of_shadowCall hsc] at hw
    obtain ⟨w, tag⟩ := i
    dsimp only at hsc hy
    rw [LprogIsa.eq_callShadow_of_shadowCall? hsc] at hy ⊢
    rw [X86Backend.ImageCoalesceCfg.renArr_callShadow _ _ _ hA.1]
    simp only [LprogIsa.callShadow, defNames, JasminLsemExportRewrites.opNames,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_singleton] at hy ⊢
    subst hy
    cases hao : ao f with
    | none => exact (hA.2.2 hao).symm
    | some _ => simp [X86Backend.CoalesceComplete.wrArrA, hao] at hw

/-- **The web of a live name along a path.** For a map `w` accepted by `webB` and a path of
    the code to `k` along which the name `y` is live at `k`: either `w k y = y` and no
    instruction of the path writes `y` as an array, or the renamed code writes `w k y` on
    the path. -/
theorem webB_path {w : Nat → String → String} {code : List LinstrRM}
    {L : Nat → List String} {obs : List String} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} (hc : webB w code L obs aa ao = true) {k : Nat}
    {ks : List Nat} (hp : Path code k ks) {y : String} (hy : y ∈ L k) :
    (w k y = y ∧ ∀ j ∈ ks, ∀ i, code[j]? = some i → wrArr ao i ≠ some y)
      ∨ WrittenOn (webRen w ao code) ks (w k y) := by
  induction hp with
  | nil => exact Or.inl ⟨webB_entry hc y hy, fun j hj => by simp at hj⟩
  | @cons k s ks i hp hi hs ih =>
      have hlp := webB_live_pred hc hi hs hy
      by_cases hw : wrArr ao i = some y
      · right
        refine ⟨k, List.mem_cons_self, renArr (stepRen w ao k i) i,
          by rw [getElem?_webRen, hi]; rfl, ?_⟩
        have hc' := webB_instr hc hi
        unfold webInstrB at hc'
        simp only [Bool.and_eq_true] at hc'
        have h1 := defNames_renArr_wr hc'.1.1.1 hw
        rw [← hlp.2 hw]
        simpa [stepRen, hw] using h1
      · have hyk := mem_L_of_webSuccs hc hi hs hy hw
        rw [← hlp.1 hw]
        rcases ih hyk with ⟨h1, h2⟩ | ⟨j, hj, i', h1, h2⟩
        · refine Or.inl ⟨h1, fun j hj i' hi' => ?_⟩
          rcases List.mem_cons.mp hj with rfl | hj
          · rw [hi] at hi'
            cases hi'
            exact hw
          · exact h2 j hj i' hi'
        · exact Or.inr ⟨j, List.mem_cons_of_mem _ hj, i', h1, h2⟩

/-- A name written on a path of the code at positions that do not write it as an array is
    written on the path of the renamed code. -/
theorem writtenOn_webRen {w : Nat → String → String} {code : List LinstrRM}
    {L : Nat → List String} {obs : List String} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} (hc : webB w code L obs aa ao = true) {ks : List Nat}
    {y : String} (hn : ∀ j ∈ ks, ∀ i, code[j]? = some i → wrArr ao i ≠ some y)
    (h : WrittenOn code ks y) : WrittenOn (webRen w ao code) ks y := by
  obtain ⟨j, hj, ij, hij, hy⟩ := h
  have hwj := webB_instr hc hij
  unfold webInstrB at hwj
  simp only [Bool.and_eq_true] at hwj
  exact ⟨j, hj, _, by rw [getElem?_webRen, hij]; rfl,
    defNames_renArr_keep hwj.1.1.1 hy (hn j hj ij hij)⟩

/-- The name `r` is written at one of the positions `ks` other than as the array the
    instruction there writes (`wrArr`). -/
def RegWrittenOn (ao : String → Option Nat) (code : List LinstrRM) (ks : List Nat)
    (r : String) : Prop :=
  ∃ j ∈ ks, ∃ i, code[j]? = some i ∧ r ∈ defNames i.1 ∧ wrArr ao i ≠ some r

/-- A name written on a path of the code other than as an array is written on the path of
    the renamed code. -/
theorem regWrittenOn_webRen {w : Nat → String → String} {code : List LinstrRM}
    {L : Nat → List String} {obs : List String} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} (hc : webB w code L obs aa ao = true) {ks : List Nat}
    {y : String} (h : RegWrittenOn ao code ks y) : WrittenOn (webRen w ao code) ks y := by
  obtain ⟨j, hj, ij, hij, hy, hn⟩ := h
  have hwj := webB_instr hc hij
  unfold webInstrB at hwj
  simp only [Bool.and_eq_true] at hwj
  exact ⟨j, hj, _, by rw [getElem?_webRen, hij]; rfl, defNames_renArr_keep hwj.1.1.1 hy hn⟩

/-- **The register reads of a code are written as registers on every path**: under every
    renaming `σ` of the shape conditions `ClassA`, a name read by the renamed instruction at
    the position `k` is in `E`, or is written other than as an array on every path to `k`
    (`RegWrittenOn`), or is the image under `σ` of an array name the instruction reads
    (`rdArr`). -/
def RegReads (E : String → Prop) (aa : String → Nat → Option Nat) (ao : String → Option Nat)
    (code : List LinstrRM) : Prop :=
  ∀ k i, code[k]? = some i → ∀ σ : String → String, ClassA σ code aa ao i (armOf i) →
    ∀ x ∈ useNames (renArr σ i).1,
      E x ∨ (∀ ks, Path code k ks → RegWrittenOn ao code ks x)
        ∨ ∃ y ∈ rdArr aa i, y ∈ useNames i.1 ∧ x = σ y

/-- **Definite assignment of the webs.** A map `w` accepted by `webB` renames a code with
    definite assignment at `E` whose register reads are written as registers on every path
    (`RegReads`) into a code with definite assignment at `E`. -/
theorem DefInit.webRen {E : String → Prop} {w : Nat → String → String}
    {code : List LinstrRM} {L : Nat → List String} {obs : List String}
    {aa : String → Nat → Option Nat} {ao : String → Option Nat}
    (hc : webB w code L obs aa ao = true) (hR : RegReads E aa ao code) (h : DefInit E code) :
    DefInit E (webRen w ao code) := by
  intro k ks i' hp hi' x hx
  have hp0 := (path_webRen w ao).mp hp
  rw [getElem?_webRen] at hi'
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hi'
  have hwi := webB_instr hc hi
  unfold webInstrB at hwi
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hwi
  have hcls := (coInstrB_iff _ _ _ _ _ _ _).mp hwi.1.1.1
  rcases hR k i hi _ hcls.1 x hx with hE | hW | ⟨y, hy, hyu, rfl⟩
  · exact Or.inl hE
  · exact Or.inr (regWrittenOn_webRen hc (hW ks hp0))
  · have hyL : y ∈ L k := hcls.2.1.1 y hy
    rw [hwi.1.1.2 y hyL]
    rcases webB_path hc hp0 hyL with ⟨h1, h2⟩ | h1
    · rw [h1]
      rcases h k ks i hp0 hi y hyu with h3 | h3
      · exact Or.inl h3
      · exact Or.inr (writtenOn_webRen hc h2 h3)
    · exact Or.inr h1

/-- **Definite assignment of the names read after the webs**, for names read after the body
    (`obs`) or never written as an array. -/
theorem DefInitOut.webRen {E : String → Prop} {w : Nat → String → String}
    {code : List LinstrRM} {L : Nat → List String} {obs : List String}
    {aa : String → Nat → Option Nat} {ao : String → Option Nat}
    (hc : webB w code L obs aa ao = true) {outs : List String} (h : DefInitOut E code outs)
    (ho : ∀ r ∈ outs, r ∈ obs ∨ ∀ i ∈ code, wrArr ao i ≠ some r) :
    DefInitOut E (webRen w ao code) outs := by
  intro ks hp r hr
  rw [length_webRen] at hp
  have hp0 := (path_webRen w ao).mp hp
  rcases ho r hr with hobs | hn
  · rcases webB_path hc hp0 (webB_obs hc r hobs) with ⟨-, h2⟩ | h1
    · rcases h ks hp0 r hr with h3 | h3
      · exact Or.inl h3
      · exact Or.inr (writtenOn_webRen hc h2 h3)
    · rw [webB_exit hc r hobs] at h1
      exact Or.inr h1
  · rcases h ks hp0 r hr with h3 | h3
    · exact Or.inl h3
    · exact Or.inr (writtenOn_webRen hc (fun j _ i hi => hn i (List.mem_of_getElem? hi)) h3)

/-- **The certificate of the webs**: the names written on every path of the renamed code
    (`MustW`). -/
theorem Cert.webRen {E : String → Prop} {w : Nat → String → String}
    {code : List LinstrRM} {L : Nat → List String} {obs : List String}
    {aa : String → Nat → Option Nat} {ao : String → Option Nat} {D : Nat → String → Prop}
    (hc : webB w code L obs aa ao = true) (hR : RegReads E aa ao code) (h : Cert E code D) :
    Cert E (webRen w ao code) (MustW (webRen w ao code)) :=
  (DefInit.webRen hc hR h.defInit).cert

/-- A fact on the instructions read through a filter that the renaming of array positions
    keeps holds of the renamed code. -/
theorem filterMap_webRen {α : Type} (f : LinstrR → Option α)
    (hf : ∀ σ i, f (renArr σ i).1 = f i.1) (w : Nat → String → String)
    (ao : String → Option Nat) (code : List LinstrRM) :
    (webRen w ao code).filterMap (fun i => f i.1) = code.filterMap (fun i => f i.1) := by
  unfold webRen
  induction code using List.reverseRecOn with
  | nil => rfl
  | append_singleton c a ih =>
      rw [List.mapIdx_append, List.filterMap_append, List.filterMap_append, ih]
      simp only [List.mapIdx_cons, List.mapIdx_nil, List.filterMap_cons, List.filterMap_nil, hf]

/-- The renaming of array positions keeps the symbol operands of an instruction. -/
theorem symReads_renArr_eq (σ : String → String) (i : LinstrRM) :
    symReads (renArr σ i) = symReads i := by
  obtain ⟨w, tag⟩ := i
  rcases hsc : LprogIsa.shadowCall? w with _ | ⟨dst, f, srcs⟩
  · cases tag <;> simp only [renArr] <;>
      (try simp only [X86Backend.ImageCoalesceCfg.renCallW_of_none hsc]) <;>
      (try simp only [X86Backend.ImageCoalesceCfg.renLoad, X86Backend.ImageCoalesceCfg.renStore,
        X86Backend.ImageCoalesceCfg.renZero, X86Backend.ImageCoalesceCfg.renStoreImm]) <;>
      (repeat' split) <;> simp_all [symReads]
  · have hne : "CALL:" ++ f ≠ "LOADSYM" := LprogIsa.callMnem_ne (by decide)
    rw [LprogIsa.eq_callShadow_of_shadowCall? hsc]
    cases tag <;> simp only [renArr] <;>
      (try simp only [X86Backend.ImageCoalesceCfg.renCallW_callShadow]) <;>
      (try simp only [X86Backend.ImageCoalesceCfg.renLoad, X86Backend.ImageCoalesceCfg.renStore,
        X86Backend.ImageCoalesceCfg.renZero, X86Backend.ImageCoalesceCfg.renStoreImm]) <;>
      (repeat' split) <;> simp_all [symReads, LprogIsa.callShadow]

/-- **The two shapes of the webs, with their check**: `regionWebs ex r` is `r`, or `r` with
    its code renamed by a position map that `webB` accepts against the liveness table of the
    code and the names `regionWebsObs ex r`. -/
theorem regionWebs_webB (ex : List String) (r : Exported) :
    regionWebs ex r = r ∨ ∃ w, webB w r.code
        (tabAt (liveArrTab r.code (regionWebsObs ex r) (fun _ _ => none) (fun _ => none) false))
        (regionWebsObs ex r) (fun _ _ => none) (fun _ => none) = true
      ∧ regionWebs ex r = { r with code := webRen w (fun _ => none) r.code } := by
  unfold regionWebs
  split
  · next hc => exact Or.inr ⟨_, ((Bool.and_eq_true _ _).mp hc).1, rfl⟩
  · exact Or.inl rfl

/-- **A renaming into web names**: every name is sent to itself or to a web name of it, the
    name followed by `#w` and a number (`ArrWebs.webLook_cases`). -/
def WebNameRen (σ : String → String) : Prop :=
  ∀ x, σ x = x ∨ ∃ n : Nat, σ x = x ++ "#w" ++ toString n

/-- **Facts kept by renamings into web names hold on the webs.** A predicate on instructions
    that every renaming `renArr σ` into web names keeps and that holds on every instruction of
    the code of `r` holds on every instruction of the code of `regionWebs ex r aa ao`. -/
theorem forall_mem_regionWebs_web {P : LinstrRM → Prop}
    (hP : ∀ σ i, WebNameRen σ → P i → P (renArr σ i)) (ex : List String) (r : Exported)
    (aa : String → Nat → Option Nat) (ao : String → Option Nat)
    (h : ∀ i ∈ r.code, P i) : ∀ j ∈ (regionWebs ex r aa ao).code, P j := by
  intro j hj
  unfold regionWebs at hj
  split at hj
  · dsimp only [webRen] at hj
    obtain ⟨k, hk, rfl⟩ := List.mem_mapIdx.mp hj
    refine hP _ _ (fun x => ?_) (h _ (List.getElem_mem hk))
    unfold stepRen
    split <;> exact X86Backend.ArrWebs.webLook_cases _ _ _
  · exact h j hj

/-- **An exported code has no unconditional jump.** -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.Haxc.RegionExp.noGoto
    {fn : String} {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} {ex : List String} {r : Exported}
    (h : RegionExp fn p ex r) : NoGoto r.code := by
  obtain ⟨r0, h0, hr | hr⟩ := h <;> subst r
  · exact exportR_noGoto _ _ p _ _ r0 h0
  · exact forall_mem_regionWebs (P := fun i => isGoto i.1 = false)
      (fun σ i hi => (ctl_renArr σ i).2.2.trans hi) ex r0 _ _ (exportR_noGoto _ _ p _ _ r0 h0)

/-- **The jumps of an exported code are nested.** -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.Haxc.RegionExp.nest
    {fn : String} {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} {ex : List String} {r : Exported}
    (h : RegionExp fn p ex r) : Nest r.code := by
  obtain ⟨r0, h0, hr | hr⟩ := h <;> subst r
  · exact exportR_nest _ _ p _ _ r0 h0
  · rcases regionWebs_cases ex r0 (fun _ _ => none) (fun _ => none) with he | ⟨w, he⟩
    · rw [he]
      exact exportR_nest _ _ p _ _ r0 h0
    · rw [he]
      refine (exportR_nest _ _ p _ _ r0 h0).of_embed id (fun a b hab _ => hab.le)
        (fun x ix hx _ => ?_) (fun a b _ _ _ _ _ _ h => h)
      rw [getElem?_webRen] at hx
      obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hx
      exact ⟨i, hi, (ctl_renArr _ i).1.symm, (ctl_renArr _ i).2.1.symm⟩

/-- **Forward reachability of an exported code**: every position is forward reachable, and
    every back edge targets a loop header. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.Haxc.RegionExp.fwdReach
    {fn : String} {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} {ex : List String} {r : Exported}
    (h : RegionExp fn p ex r) :
    (∀ k, k ≤ r.code.length → FwdPath r.code k)
      ∧ ∀ k q, BackEdge r.code k q → LoopHeader r.code q k :=
  ⟨fwdPath_of_noGoto h.noGoto, fun _ _ hb => loopHeader_of_nest h.nest hb⟩

/-- **The label facts of an exported code** from the label `0`. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.Haxc.RegionExp.labelsOK
    {fn : String} {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} {ex : List String} {r : Exported}
    (h : RegionExp fn p ex r) : LabelsOK 0 r := by
  obtain ⟨r0, h0, hr | hr⟩ := h <;> subst r
  · exact exportR_labelsOK _ _ x86Data_guardsPlain p _ _ r0 h0
  · have hL := exportR_labelsOK _ _ x86Data_guardsPlain p _ _ r0 h0
    rcases regionWebs_cases ex r0 (fun _ _ => none) (fun _ => none) with he | ⟨w, he⟩
    · rw [he]
      exact hL
    · rw [he]
      have hl : labelsOf (webRen w (fun _ => none) r0.code) = labelsOf r0.code :=
        filterMap_webRen labelOf? (fun σ i => (ctl_renArr σ i).1) w _ r0.code
      have ht : targetsOf (webRen w (fun _ => none) r0.code) = targetsOf r0.code :=
        filterMap_webRen jumpTarget?
          (fun σ i => by simp only [← jumpLabel?_eq_jumpTarget?, (ctl_renArr σ i).2.1]) w _
          r0.code
      exact ⟨hL.le, by rw [hl]; exact hL.range, by rw [hl]; exact hL.nodup,
        by rw [ht, hl]; exact hL.closed⟩

/-- **The certificate of definite assignment of an exported code**, at the argument names
    and the symbol operands, which also holds the names of the returned operands at the end.
    For the webs, the register reads of the export are written as registers on every path
    (`RegReads`). -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.Haxc.RegionExp.cert
    {fn : String} {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} {ex : List String} {r : Exported}
    (h : RegionExp fn p ex r)
    (hR : ∀ r0, exportR Γ.length fn p Γ.length 0 x86Data = some r0 →
      RegReads (ExportE Γ.length r0.code) (fun _ _ => none) (fun _ => none) r0.code) :
    ∃ D, Cert (ExportE Γ.length r.code) r.code D ∧
      ∀ x ∈ r.res.flatMap opNames, D r.code.length x ∨ ExportE Γ.length r.code x := by
  obtain ⟨r0, h0, hr | hr⟩ := h <;> subst r
  · exact exportR_cert fn p h0
  obtain ⟨D, hC, hres⟩ := exportR_cert fn p h0
  rcases regionWebs_webB ex r0 with he | ⟨w, hc, he⟩
  · rw [he]
    exact ⟨D, hC, hres⟩
  rw [he]
  dsimp only
  have hE : ∀ x, ExportE Γ.length r0.code x →
      ExportE Γ.length (webRen w (fun _ => none) r0.code) x := by
    rintro x (hx | ⟨i, hi, hx⟩)
    · exact Or.inl hx
    · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hi
      exact Or.inr ⟨_, by unfold webRen; exact List.mem_mapIdx.mpr ⟨k, hk, rfl⟩,
        by rwa [symReads_renArr_eq]⟩
  have hD := DefInit.webRen hc (hR r0 h0) hC.defInit
  have hO := DefInitOut.webRen hc (hC.defInitOut hres) (outs := r0.res.flatMap opNames)
    (fun x hx => by
      left
      obtain ⟨o, ho, hxo⟩ := List.mem_flatMap.mp hx
      rw [exportR_res_isReg _ _ p _ _ r0 h0 o ho] at hxo
      simp only [opNames, List.mem_singleton] at hxo
      subst hxo
      exact List.mem_append_left _ (List.mem_map_of_mem ho))
  refine ⟨MustW (webRen w (fun _ => none) r0.code), ?_, fun x hx => ?_⟩
  · have hD' : DefInit (ExportE Γ.length (webRen w (fun _ => none) r0.code))
        (webRen w (fun _ => none) r0.code) :=
      fun k ks i hp hi x hx => (hD k ks i hp hi x hx).imp_left (hE x)
    exact hD'.cert
  · by_cases hx' : ExportE Γ.length (webRen w (fun _ => none) r0.code) x
    · exact Or.inr hx'
    · refine Or.inl fun ks hp => ?_
      rw [length_webRen] at hp
      exact (hO ks (by rwa [length_webRen]) x hx).resolve_left fun h' => hx' (hE x h')

/-- **Definite assignment of an exported code** (the statement of `exportR_defInit` at every
    code of `RegionExp`), under `RegReads` of the export. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.Haxc.RegionExp.defInit
    {fn : String} {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} {ex : List String} {r : Exported}
    (h : RegionExp fn p ex r)
    (hR : ∀ r0, exportR Γ.length fn p Γ.length 0 x86Data = some r0 →
      RegReads (ExportE Γ.length r0.code) (fun _ _ => none) (fun _ => none) r0.code) :
    DefInit (ExportE Γ.length r.code) r.code
      ∧ DefInitOut (ExportE Γ.length r.code) r.code (r.res.flatMap opNames)
      ∧ ∀ outs : List String,
          (∀ x ∈ outs, x ∈ r.res.flatMap opNames ∨ ExportE Γ.length r.code x) →
          ∀ x ∈ tabAt (liveRegTab r.code outs) 0,
            ExportE Γ.length r.code x ∨ ArrOnly r.code x := by
  obtain ⟨D, hC, hres⟩ := h.cert hR
  refine ⟨hC.defInit, hC.defInitOut hres, fun outs ho => liveRegTab_entry hC fun x hx => ?_⟩
  rcases ho x hx with h' | h'
  · exact hres x h'
  · exact Or.inr h'

end Webs

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionExportDefInit
