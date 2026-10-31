/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapDom

@[expose] public section

set_option autoImplicit false

/-!
# The positions of the coalesced code in the input of the allocation

The input `regionAllocCode code outs` of the allocation of a region export is the coalesced code
`code.map (renArr ρ)` with the liveness instructions of `pinSelfMoves` in place of the array
self-moves, one for one, and the liveness instructions of `backEdgePins` inserted before the
jumps to earlier labels. This module states the map from the positions of the coalesced code to
the positions of the allocation input and the transfer of the register liveness `PLiveR` along
it.

## Main definitions

* `insBefore`: a code with a list of instructions inserted before each instruction.
* `insPos`: the position in `insBefore` of an instruction of the code.
* `bePre`: the instructions `backEdgePins` inserts before an instruction.
* `allocPos`: the position in `regionAllocCode code outs rr` of a position of the coalesced
  code.

## Main results

* `pLiveR_map`: the liveness of a code transfers along a position map that preserves the
  instructions up to their reads, writes and jumps, the labels and the end.
* `pLiveR_pinSelfMoves`: a name live in a code is live at the same position of the code with its
  self-moves pinned, unless it is the pin name.
* `pLiveR_backEdgePins`: a name live in a code other than the pin name is live at the image of
  its position under `insPos` in the code with its back-edge pins.
* `allocPos_lt`, `getElem?_allocPos`, `allocPos_length`: the map `allocPos` is strictly
  monotone, it sends each instruction of the pinned code to itself, and it sends the end to the
  end.
* `pLiveR_regionAllocCode`: the liveness of the coalesced code is contained in the liveness of
  the allocation input at the image of each position.
* `pLiveR_segment`, `pLiveR_renRM`: the liveness of a code with a label-free prefix and suffix
  restricted to the middle part, and the liveness of a renamed code as the image of the
  liveness of the code.
* `renArr_regionCoCode_eq`: the coalescing renamings of the parts and of the allocation agree
  on an instruction of the exported code that mentions no version of a result buffer.
* `pLiveR_regionCoParts_code`, `pLiveR_regionCoParts_alloc`, `bd_regionCoParts`: a name in the
  liveness table of the parts at a position of the exported code is the image under the
  pairs of the renaming of a name live there in the code given to the allocation, with the
  boundary condition at one result type.
* `eq_of_renOf_certArgs_keep`, `arrUse_ne_of_keep`, `pLiveR_regionCoParts_allocCode`: a name
  the merge keeps is its own preimage, no array of the code given to the allocation, and
  live in the input of the allocation at the image of its position.
* `liveAt_hull`, `regionAllocBody_code`: a name live after an instruction of the pinned
  coalesced code and a name that instruction touches are live at one trace position of the
  certified body, behind a touch of the live name at or before the instruction.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapPins

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (findLabelMem)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc (useNames defNames regDefs
  arrUse? jumpLabel?)
open RegionAllocMapComplete

/-! ## 1. Transfer of liveness along a position map -/

/-- The instruction `i'` simulates the instruction `i` for the liveness of the name `y`: it
    reads `y` when `i` does, it is no unconditional jump when `i` is none, it writes `y` as an
    operation only when `i` does, and it names the label `i` names. -/
structure LiveSim (y : String) (i i' : LinstrRM) : Prop where
  read : y ∈ useNames i.1 → y ∈ useNames i'.1
  noGoto : (∀ x, i.1 ≠ .Lgoto x) → ∀ x, i'.1 ≠ .Lgoto x
  noDef : (∀ ds o ss, i.1 = .Lopn ds o ss → y ∉ regDefs i) →
    ∀ ds o ss, i'.1 = .Lopn ds o ss → y ∉ regDefs i'
  label : jumpLabel? i'.1 = jumpLabel? i.1

theorem LiveSim.refl (y : String) (i : LinstrRM) : LiveSim y i i :=
  ⟨id, id, id, rfl⟩

/-- **Liveness along a position map.** Let `f` send each instruction of `X` to an instruction of
    `Y` that simulates it for `y`, let `y` stay live across the positions of `Y` between the
    images `f k + 1` and `f (k + 1)`, let `f` send the position of each label of `X` to the
    position of that label in `Y`, and let `y` be live at the image of the end when it is read
    after `X`. Then `y` live at a position of `X` is live at its image. -/
theorem pLiveR_map {X Y : List LinstrRM} {outs outs' : List String} {y : String}
    {f : Nat → Nat}
    (hins : ∀ k i, X[k]? = some i → ∃ i', Y[f k]? = some i' ∧ LiveSim y i i')
    (hgap : ∀ k, k < X.length → PLiveR Y outs' (f (k + 1)) y → PLiveR Y outs' (f k + 1) y)
    (hlab : ∀ l p, findLabelMem l X = some p → findLabelMem l Y = some (f p))
    (hend : y ∈ outs → PLiveR Y outs' (f X.length) y) {k : Nat}
    (h : PLiveR X outs k y) : PLiveR Y outs' (f k) y := by
  induction h with
  | read hi hy =>
    obtain ⟨i', hi', hs⟩ := hins _ _ hi
    exact .read hi' (hs.read hy)
  | @next k i y hi hg hd _ ih =>
    obtain ⟨i', hi', hs⟩ := hins _ _ hi
    have hk : k < X.length := (List.getElem?_eq_some_iff.mp hi).1
    exact .next hi' (hs.noGoto hg) (hs.noDef hd) (hgap k hk (ih hins hgap hend))
  | @jump k i l p y hi hl hp _ ih =>
    obtain ⟨i', hi', hs⟩ := hins _ _ hi
    have hpl : p < X.length := by
      simpa [findLabelMem] using
        JasminLsemLabeled.findLabel_lt_length l (X.map Prod.fst) p hp
    exact .jump hi' (hs.label.trans hl) (hlab l p hp) (hgap p hpl (ih hins hgap hend))
  | out hy => exact hend hy

/-- A name stays live backwards across positions of `Y` holding the instructions of `G` when no
    instruction of `G` is an unconditional jump or writes it as an operation. -/
theorem pLiveR_gap {Y : List LinstrRM} {outs : List String} {y : String} :
    ∀ (G : List LinstrRM) (m : Nat), (∀ j, j < G.length → Y[m + j]? = G[j]?) →
      (∀ g ∈ G, (∀ x, g.1 ≠ .Lgoto x) ∧ ∀ ds o ss, g.1 = .Lopn ds o ss → y ∉ regDefs g) →
      PLiveR Y outs (m + G.length) y → PLiveR Y outs m y := by
  intro G
  induction G with
  | nil => intro m _ _ h; simpa using h
  | cons g G ih =>
    intro m hY hG h
    have h1 : PLiveR Y outs (m + 1) y :=
      ih (m + 1) (fun j hj => by
          have := hY (j + 1) (by simp; omega)
          simpa [Nat.add_assoc, Nat.add_comm 1 j] using this)
        (fun g' hg' => hG g' (List.mem_cons_of_mem _ hg'))
        (by simpa [Nat.add_assoc, Nat.add_comm 1] using h)
    have h0 : Y[m]? = some g := by simpa using hY 0 (by simp)
    obtain ⟨hg1, hg2⟩ := hG g List.mem_cons_self
    exact .next h0 hg1 hg2 h1

/-! ## 2. Instructions inserted before the instructions of a code -/

/-- The code `C` with the instructions `ins n i` inserted before its instruction `i` at the
    index `n`, counted from `n`. -/
def insBefore (ins : Nat → LinstrRM → List LinstrRM) : List LinstrRM → Nat → List LinstrRM
  | [], _ => []
  | i :: C, n => ins n i ++ i :: insBefore ins C (n + 1)

/-- The position in `insBefore ins C n` of the instruction of `C` at position `k`; the length
    of `insBefore ins C n` at `k = C.length`. -/
def insPos (ins : Nat → LinstrRM → List LinstrRM) : List LinstrRM → Nat → Nat → Nat
  | [], _, _ => 0
  | i :: _, n, 0 => (ins n i).length
  | i :: C, n, k + 1 => (ins n i).length + 1 + insPos ins C (n + 1) k

variable {ins : Nat → LinstrRM → List LinstrRM}

theorem getElem?_insPos : ∀ (C : List LinstrRM) (n k : Nat), k < C.length →
    (insBefore ins C n)[insPos ins C n k]? = C[k]?
  | [], _, _, h => by simp at h
  | i :: C, n, 0, _ => by simp [insBefore, insPos]
  | i :: C, n, k + 1, h => by
    have ih := getElem?_insPos C (n + 1) k (by simpa using h)
    simp only [insBefore, insPos, List.getElem?_cons_succ]
    rw [List.getElem?_append_right (by omega)]
    simpa [Nat.add_assoc, Nat.add_comm 1] using ih

theorem insPos_length : ∀ (C : List LinstrRM) (n : Nat),
    insPos ins C n C.length = (insBefore ins C n).length
  | [], _ => rfl
  | i :: C, n => by
    simp only [List.length_cons, insPos, insBefore, List.length_append, insPos_length C (n + 1)]
    omega

/-- The instructions `insBefore` inserts before the first instruction of a code. -/
def insHead (ins : Nat → LinstrRM → List LinstrRM) : List LinstrRM → Nat → List LinstrRM
  | [], _ => []
  | i :: _, n => ins n i

theorem insPos_zero (C : List LinstrRM) (n : Nat) :
    insPos ins C n 0 = (insHead ins C n).length := by
  cases C <;> rfl

theorem getElem?_insHead (C : List LinstrRM) (n : Nat) {j : Nat}
    (hj : j < (insHead ins C n).length) :
    (insBefore ins C n)[j]? = (insHead ins C n)[j]? := by
  cases C with
  | nil => simp [insHead] at hj
  | cons i C =>
    simp only [insHead] at hj ⊢
    simp only [insBefore]
    rw [List.getElem?_append_left hj]

/-- Between the images of the positions `k` and `k + 1` the code holds instructions inserted
    by `ins`. -/
theorem insPos_succ (P : LinstrRM → Prop) (hP : ∀ m i, ∀ g ∈ ins m i, P g) :
    ∀ (C : List LinstrRM) (n k : Nat), k < C.length →
      ∃ G : List LinstrRM, insPos ins C n (k + 1) = insPos ins C n k + 1 + G.length
        ∧ (∀ j, j < G.length → (insBefore ins C n)[insPos ins C n k + 1 + j]? = G[j]?)
        ∧ ∀ g ∈ G, P g
  | [], _, _, h => by simp at h
  | i :: C, n, 0, _ => by
    refine ⟨insHead ins C (n + 1), ?_, fun j hj => ?_, fun g hg => ?_⟩
    · simp only [insPos, insPos_zero]
    · simp only [insBefore, insPos]
      rw [List.getElem?_append_right (by omega)]
      rw [show (ins n i).length + 1 + j - (ins n i).length = j + 1 by omega,
        List.getElem?_cons_succ]
      exact getElem?_insHead C (n + 1) hj
    · cases C with
      | nil => simp [insHead] at hg
      | cons j C => exact hP _ _ g hg
  | i :: C, n, k + 1, h => by
    obtain ⟨G, h1, h2, h3⟩ := insPos_succ P hP C (n + 1) k (by simpa using h)
    refine ⟨G, ?_, fun j hj => ?_, h3⟩
    · simp only [insPos, h1]
      omega
    · simp only [insBefore, insPos]
      rw [List.getElem?_append_right (by omega)]
      have := h2 j hj
      rw [show (ins n i).length + 1 + insPos ins C (n + 1) k + 1 + j - (ins n i).length
        = (insPos ins C (n + 1) k + 1 + j) + 1 by omega, List.getElem?_cons_succ]
      exact this

/-- The map `insPos` is strictly monotone on the positions of the code and its end. -/
theorem insPos_lt (C : List LinstrRM) (n : Nat) {k k' : Nat} (hk : k < k')
    (hk' : k' ≤ C.length) : insPos ins C n k < insPos ins C n k' := by
  induction k' with
  | zero => omega
  | succ k' ih =>
    obtain ⟨G, h1, -, -⟩ := insPos_succ (ins := ins) (fun _ => True) (fun _ _ _ _ => trivial)
      C n k' (by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · have := ih hk (by omega)
      omega
    · omega

/-- When no inserted instruction is a label, the labels of `insBefore ins C n` are at the images
    of the labels of `C`. -/
theorem findLabelMem_insBefore
    (hL : ∀ m i, ∀ g ∈ ins m i, ∀ l, JasminLsemLabeled.isLabel l g.1 = false)
    (l : LLabel) : ∀ (C : List LinstrRM) (n : Nat),
      findLabelMem l (insBefore ins C n) = (findLabelMem l C).map (insPos ins C n)
  | [], _ => rfl
  | i :: C, n => by
    have ih := findLabelMem_insBefore hL l C (n + 1)
    unfold findLabelMem JasminLsemLabeled.findLabel at ih ⊢
    have hnone : List.findIdx? (JasminLsemLabeled.isLabel l) ((ins n i).map Prod.fst) = none := by
      rw [List.findIdx?_eq_none_iff]
      intro x hx
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
      simp [hL n i g hg l]
    simp only [insBefore, List.map_append, List.map_cons, List.findIdx?_append, hnone,
      List.findIdx?_cons, Option.none_or]
    cases h : JasminLsemLabeled.isLabel l i.1
    · simp only [Bool.false_eq_true, ite_false, ih, Option.map_map]
      cases List.findIdx? (JasminLsemLabeled.isLabel l) (C.map Prod.fst)
      · rfl
      · simp only [Option.map_some, Function.comp_apply, insPos, List.length_map,
          Option.some.injEq]
        omega
    · simp [insPos]

/-- **Liveness under inserted instructions.** A name live at a position of `C` is live at its
    image in `insBefore ins C n` when no inserted instruction is a label, an unconditional jump
    or an operation writing the name. -/
theorem pLiveR_insBefore {C : List LinstrRM} {n : Nat} {outs : List String} {y : String}
    (hI : ∀ m i, ∀ g ∈ ins m i, (∀ l, JasminLsemLabeled.isLabel l g.1 = false)
      ∧ (∀ x, g.1 ≠ .Lgoto x) ∧ ∀ ds o ss, g.1 = .Lopn ds o ss → y ∉ regDefs g)
    {k : Nat} (h : PLiveR C outs k y) : PLiveR (insBefore ins C n) outs (insPos ins C n k) y := by
  refine pLiveR_map (fun k i hi => ⟨i, ?_, LiveSim.refl y i⟩) (fun k hk hlive => ?_)
    (fun l p hp => ?_) (fun hy => ?_) h
  · rw [getElem?_insPos C n k (List.getElem?_eq_some_iff.mp hi).1, hi]
  · obtain ⟨G, h1, h2, h3⟩ := insPos_succ (ins := ins)
      (fun g => (∀ x, g.1 ≠ .Lgoto x) ∧ ∀ ds o ss, g.1 = .Lopn ds o ss → y ∉ regDefs g)
      (fun m i g hg => (hI m i g hg).2) C n k hk
    rw [h1] at hlive
    exact pLiveR_gap G _ h2 h3 hlive
  · rw [findLabelMem_insBefore (fun m i g hg => (hI m i g hg).1) l C n, hp]
    rfl
  · rw [insPos_length]
    exact .out hy

/-! ## 3. The back-edge pins -/

/-- The instructions `backEdgePins` inserts before the instruction `i` at position `k` of `C`,
    at the table `T`. -/
def bePre (T : Array (List String)) (C : List LinstrRM) (k : Nat) (i : LinstrRM) :
    List LinstrRM :=
  match i.1 with
  | .Lcond _ l => backEdgePin T C k l
  | .Lgoto (_, l) => backEdgePin T C k l
  | _ => []

theorem backEdgePins_eq_insBefore (C : List LinstrRM) :
    backEdgePins C = insBefore (bePre (liveRegTab C []) C) C 0 := by
  unfold backEdgePins
  suffices h : ∀ (L : List LinstrRM) (n : Nat), (L.zipIdx n).flatMap
      (fun (p : LinstrRM × Nat) => match p.1.1 with
        | .Lcond _ l => backEdgePin (liveRegTab C []) C p.2 l ++ [p.1]
        | .Lgoto (_, l) => backEdgePin (liveRegTab C []) C p.2 l ++ [p.1]
        | _ => [p.1]) = insBefore (bePre (liveRegTab C []) C) L n from h C 0
  intro L
  induction L with
  | nil => intro n; rfl
  | cons i L ih =>
    intro n
    rw [List.zipIdx_cons, List.flatMap_cons, ih (n + 1)]
    obtain ⟨w, t⟩ := i
    cases w with
    | Lgoto x => obtain ⟨f, l⟩ := x; simp [insBefore, bePre]
    | _ => simp [insBefore, bePre]

/-- An instruction of `backEdgePin` is a `LIVEPIN` writing the pin name. -/
theorem mem_bePre {T : Array (List String)} {C : List LinstrRM} {k : Nat} {i g : LinstrRM}
    (h : g ∈ bePre T C k i) : ∃ ns : List String,
      g = (.Lopn [.reg "%livepin"] "LIVEPIN" (ns.map LOperand.reg), .reg none) := by
  have key : ∀ l, g ∈ backEdgePin T C k l → ∃ ns : List String,
      g = (.Lopn [.reg "%livepin"] "LIVEPIN" (ns.map LOperand.reg), .reg none) := by
    intro l hl
    unfold backEdgePin at hl
    split at hl
    · dsimp only at hl
      split_ifs at hl
      · exact ⟨_, List.mem_singleton.mp hl⟩
      · simp at hl
    · simp at hl
  unfold bePre at h
  split at h
  · exact key _ h
  · exact key _ h
  · simp at h

theorem regDefs_livepin (ns : List String) :
    regDefs (.Lopn [.reg "%livepin"] "LIVEPIN" (ns.map LOperand.reg), .reg none)
      = ["%livepin"] := by
  have hc : ¬ ("LIVEPIN" = withWidthTag 64 "CMP") := by decide
  simp only [regDefs, JasminLsemMemFlagGuard.cmpArgs?, JasminLsemMemFlagGuard.movRegArgs?,
    JasminLsemExportRegAlloc.memRegDefs, JasminLsemExportRegAlloc.storeHit?, defNames]
  rcases ns with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
    simp [hc, JasminLsemExportRewrites.opNames]

/-- **Liveness in the code with its back-edge pins**: a name other than the pin name live at a
    position of `C` is live at its image under `insPos`. -/
theorem pLiveR_backEdgePins {C : List LinstrRM} {outs : List String} {y : String}
    (hy : y ≠ "%livepin") {k : Nat} (h : PLiveR C outs k y) :
    PLiveR (backEdgePins C) outs (insPos (bePre (liveRegTab C []) C) C 0 k) y := by
  rw [backEdgePins_eq_insBefore]
  refine pLiveR_insBefore (fun m i g hg => ?_) h
  obtain ⟨ns, rfl⟩ := mem_bePre hg
  refine ⟨fun l => rfl, fun x => by simp, fun ds o ss _ => ?_⟩
  rw [regDefs_livepin]
  simpa using hy

/-! ## 4. The pinned self-moves -/

/-- **Liveness in the code with its self-moves pinned**: a name live at a position of `X` is
    live at the same position of `pinSelfMoves X` when it is not the pin name: each liveness
    instruction reads the names the instruction in its place reads. -/
theorem pLiveR_pinSelfMoves {X : List LinstrRM} {outs : List String} {y : String}
    (hy : y ≠ "%livepin") {k : Nat}
    (h : PLiveR X outs k y) : PLiveR (pinSelfMoves X) outs k y := by
  have hcl : ¬ ("LIVEPIN" = withWidthTag 64 "CMP") := by decide
  refine pLiveR_map (f := id) (fun k i hi => ?_) (fun k _ hl => hl) (fun l p hp => ?_)
    (fun hy' => ?_) h
  · have hk : k < (pinSelfMoves X).length := by
      rw [length_pinSelfMoves]; exact (List.getElem?_eq_some_iff.mp hi).1
    obtain ⟨i', hi'⟩ : ∃ i', (pinSelfMoves X)[k]? = some i' :=
      ⟨_, List.getElem?_eq_getElem hk⟩
    obtain ⟨i0, hi0, hc⟩ := getElem?_pinSelfMoves X k i' hi'
    rw [hi] at hi0
    obtain rfl := Option.some.inj hi0
    refine ⟨i', hi', ?_⟩
    rcases hc with rfl | ⟨t, a, z, sc, w, n, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact LiveSim.refl y _
    · refine ⟨fun hr => ?_, fun _ x => by simp [selfPinLoad], fun hd ds o ss _ => ?_, rfl⟩
      · simp [useNames, selfPinLoad, JasminLsemExportRewrites.opNames] at hr ⊢
        exact hr
      · have := hd _ _ _ rfl
        simpa [selfPinLoad, regDefs, JasminLsemMemFlagGuard.cmpArgs?, hcl,
          JasminLsemMemFlagGuard.movRegArgs?, JasminLsemExportRegAlloc.memRegDefs,
          JasminLsemExportRegAlloc.storeHit?, defNames, JasminLsemExportRewrites.opNames]
          using this
    · refine ⟨fun hr => ?_, fun _ x => by simp [selfPinStore], fun _ ds o ss _ => ?_, rfl⟩
      · simp [useNames, selfPinStore, JasminLsemExportRewrites.opNames] at hr ⊢
        exact hr
      · simp [selfPinStore, regDefs, JasminLsemMemFlagGuard.cmpArgs?,
          JasminLsemMemFlagGuard.movRegArgs?, JasminLsemExportRegAlloc.memRegDefs,
          JasminLsemExportRegAlloc.storeHit?, defNames, JasminLsemExportRewrites.opNames]
        exact hy
  · exact (RegionExportDefInit.findLabelMem_pinSelfMoves l X).trans hp
  · simpa [length_pinSelfMoves] using (PLiveR.out hy' : PLiveR (pinSelfMoves X) outs _ y)

/-! ## 5. The positions of the allocation input -/

/-- **The position in the allocation input** `regionAllocCode code outs rr` of the position `k`
    of the coalesced code `code.map (renArr ρ)`, `ρ` the coalescing renaming of `code` at `outs`
    and the result alias `rr`. -/
def allocPos (code : List LinstrRM) (outs : List (String × Nat)) (rr : Option (String × String))
    (k : Nat) : Nat :=
  let P := pinSelfMoves (code.map (X86Backend.ImageCoalesceCfg.renArr
    (canonMemrefName (resAliasTab outs rr code))))
  insPos (bePre (liveRegTab P []) P) P 0 k

/-- The map `allocPos` is strictly monotone on the positions of the code and its end. -/
theorem allocPos_lt (code : List LinstrRM) (outs : List (String × Nat))
    (rr : Option (String × String)) {k k' : Nat} (hk : k < k') (hk' : k' ≤ code.length) :
    allocPos code outs rr k < allocPos code outs rr k' :=
  insPos_lt _ 0 hk (by rw [length_pinSelfMoves, List.length_map]; exact hk')

/-- The map `allocPos` is injective on the positions of the code and its end. -/
theorem allocPos_inj (code : List LinstrRM) (outs : List (String × Nat))
    (rr : Option (String × String)) {k k' : Nat}
    (hk : k ≤ code.length) (hk' : k' ≤ code.length)
    (h : allocPos code outs rr k = allocPos code outs rr k') : k = k' := by
  rcases Nat.lt_trichotomy k k' with hlt | heq | hgt
  · exact absurd h (allocPos_lt code outs rr hlt hk').ne
  · exact heq
  · exact absurd h (allocPos_lt code outs rr hgt hk).ne'

/-- The allocation input holds at `allocPos code outs rr k` the instruction of the pinned
    coalesced code at `k`. -/
theorem getElem?_allocPos (code : List LinstrRM) (outs : List (String × Nat))
    (rr : Option (String × String)) {k : Nat} (hk : k < code.length) :
    (regionAllocCode code outs rr)[allocPos code outs rr k]?
      = (pinSelfMoves (code.map (X86Backend.ImageCoalesceCfg.renArr
          (canonMemrefName (resAliasTab outs rr code)))))[k]? := by
  unfold regionAllocCode allocPos
  rw [backEdgePins_eq_insBefore]
  exact getElem?_insPos _ 0 k (by rw [length_pinSelfMoves, List.length_map]; exact hk)

/-- The map `allocPos` sends the end of the code to the end of the allocation input. -/
theorem allocPos_length (code : List LinstrRM) (outs : List (String × Nat))
    (rr : Option (String × String)) :
    allocPos code outs rr code.length = (regionAllocCode code outs rr).length := by
  unfold regionAllocCode allocPos
  rw [backEdgePins_eq_insBefore, ← insPos_length]
  simp only [length_pinSelfMoves, List.length_map]

/-- **The liveness of the coalesced code in the allocation input** (ALIGN-LIVE): a name live at
    a position `k` of the coalesced code `code.map (renArr ρ)`, read after it as `O`, is live at
    `allocPos code outs rr k` in the allocation input `regionAllocCode code outs rr` read after
    as `O`, when it is not the pin name. -/
theorem pLiveR_regionAllocCode (code : List LinstrRM) (outs : List (String × Nat))
    (rr : Option (String × String)) {O : List String} {y : String} (hy : y ≠ "%livepin")
    {k : Nat}
    (h : PLiveR (code.map (X86Backend.ImageCoalesceCfg.renArr
      (canonMemrefName (resAliasTab outs rr code)))) O k y) :
    PLiveR (regionAllocCode code outs rr) O (allocPos code outs rr k) y :=
  pLiveR_backEdgePins hy (pLiveR_pinSelfMoves hy h)

/-! ## 6. The liveness of the reference restricted to its renamed code -/

/-- The labels of a code behind a label-free prefix are shifted by the length of the prefix. -/
theorem findLabelMem_append_noLabel_left (l : LLabel) {xs : List LinstrRM} (ys : List LinstrRM)
    (hx : ∀ i ∈ xs, ∀ l, JasminLsemLabeled.isLabel l i.1 = false) :
    findLabelMem l (xs ++ ys) = (findLabelMem l ys).map (· + xs.length) := by
  unfold findLabelMem JasminLsemLabeled.findLabel
  have hnone : List.findIdx? (JasminLsemLabeled.isLabel l) (xs.map Prod.fst) = none := by
    rw [List.findIdx?_eq_none_iff]
    intro x hx'
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx'
    simp [hx g hg l]
  rw [List.map_append, List.findIdx?_append, hnone, Option.none_or, List.length_map]

/-- The labels of a code followed by a label-free suffix are those of the code. -/
theorem findLabelMem_append_noLabel_right (l : LLabel) (xs : List LinstrRM) {ys : List LinstrRM}
    (hy : ∀ i ∈ ys, ∀ l, JasminLsemLabeled.isLabel l i.1 = false) :
    findLabelMem l (xs ++ ys) = findLabelMem l xs := by
  unfold findLabelMem JasminLsemLabeled.findLabel
  have hnone : List.findIdx? (JasminLsemLabeled.isLabel l) (ys.map Prod.fst) = none := by
    rw [List.findIdx?_eq_none_iff]
    intro x hx'
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx'
    simp [hy g hg l]
  rw [List.map_append, List.findIdx?_append, hnone]
  cases List.findIdx? (JasminLsemLabeled.isLabel l) (xs.map Prod.fst) <;> rfl

/-- **The liveness of a middle part.** In the code `pre ++ L1 ++ L2` with a label-free prefix
    and suffix, a name live at a position of `L1` is live there in `L1` read after it as the
    list of the liveness table of the whole code at the end of `L1`. -/
theorem pLiveR_segment {pre L1 L2 : List LinstrRM} {outs : List String} {y : String}
    (hpre : ∀ i ∈ pre, ∀ l, JasminLsemLabeled.isLabel l i.1 = false)
    (hL2 : ∀ i ∈ L2, ∀ l, JasminLsemLabeled.isLabel l i.1 = false) {k : Nat}
    (hk : k ≤ L1.length) (h : PLiveR (pre ++ L1 ++ L2) outs (pre.length + k) y) :
    PLiveR L1 (tabAt (liveRegTab (pre ++ L1 ++ L2) outs) (pre.length + L1.length)) k y := by
  suffices key : ∀ n, PLiveR (pre ++ L1 ++ L2) outs n y → pre.length ≤ n →
      n ≤ pre.length + L1.length →
      PLiveR L1 (tabAt (liveRegTab (pre ++ L1 ++ L2) outs) (pre.length + L1.length))
        (n - pre.length) y by
    simpa using key _ h (by omega) (by omega)
  clear h hk
  intro n hn
  have hget : ∀ m i, pre.length ≤ m → m < pre.length + L1.length →
      (pre ++ L1 ++ L2)[m]? = some i → L1[m - pre.length]? = some i := by
    intro m i h1 h2 hm
    rw [List.append_assoc, List.getElem?_append_right h1,
      List.getElem?_append_left (by omega)] at hm
    exact hm
  induction hn with
  | @read m i y hi hy =>
    intro h1 h2
    by_cases he : m = pre.length + L1.length
    · subst he
      rw [Nat.add_sub_cancel_left]
      exact .out (mem_liveRegTab_iff.mpr (.read hi hy))
    · exact .read (hget m i h1 (by omega) hi) hy
  | @next m i y hi hg hd hn ih =>
    intro h1 h2
    by_cases he : m = pre.length + L1.length
    · subst he
      rw [Nat.add_sub_cancel_left]
      exact .out (mem_liveRegTab_iff.mpr (.next hi hg hd hn))
    · have := ih (by omega) (by omega)
      rw [show m + 1 - pre.length = m - pre.length + 1 by omega] at this
      exact .next (hget m i h1 (by omega) hi) hg hd this
  | @jump m i l p y hi hl hp hn ih =>
    intro h1 h2
    by_cases he : m = pre.length + L1.length
    · subst he
      rw [Nat.add_sub_cancel_left]
      exact .out (mem_liveRegTab_iff.mpr (.jump hi hl hp hn))
    · rw [List.append_assoc, findLabelMem_append_noLabel_left l _ hpre,
        findLabelMem_append_noLabel_right l _ hL2] at hp
      obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp hp
      have hql : q < L1.length := by
        simpa [findLabelMem] using
          JasminLsemLabeled.findLabel_lt_length l (L1.map Prod.fst) q hq
      have := ih (by omega) (by omega)
      rw [show q + pre.length + 1 - pre.length = q + 1 by omega] at this
      exact .jump (hget m i h1 (by omega) hi) hl hq this
  | @out y hy =>
    intro h1 h2
    have hlen : (pre ++ L1 ++ L2).length = pre.length + L1.length := by
      simp only [List.length_append] at h2 ⊢; omega
    rw [hlen]
    simp only [Nat.add_sub_cancel_left]
    exact .out (mem_liveRegTab_iff.mpr (hlen ▸ .out hy))

/-- **The liveness of a renamed code**: a name live at a position of `L.map (renRM τ)` read
    after it as `O` is the image under `τ` of a name live there in `L` read after it as `O0`,
    when every name of `O` is the image of a name of `O0`. -/
theorem pLiveR_renRM {L : List LinstrRM} {τ : String → String} {O O0 : List String}
    (hO : ∀ z ∈ O, ∃ z0 ∈ O0, τ z0 = z) {k : Nat} {y : String}
    (h : PLiveR (L.map (JasminLsemExportTransfer.renRM τ)) O k y) :
    ∃ y0, τ y0 = y ∧ PLiveR L O0 k y0 := by
  have hjl : ∀ w : LinstrR,
      jumpLabel? (JasminLsemExportTransfer.renLinstrR τ w) = jumpLabel? w := by
    intro w; cases w <;> rfl
  induction h with
  | @read m i' y hi hy =>
    obtain ⟨i, hi0, rfl⟩ := Option.map_eq_some_iff.mp (List.getElem?_map ▸ hi)
    rw [JasminLsemExportTransfer.renRM, RegionExportDefInit.useNames_renLinstrR] at hy
    obtain ⟨y0, hy0, rfl⟩ := List.mem_map.mp hy
    exact ⟨y0, rfl, .read hi0 hy0⟩
  | @next m i' y hi hg hd _ ih =>
    obtain ⟨i, hi0, rfl⟩ := Option.map_eq_some_iff.mp (List.getElem?_map ▸ hi)
    obtain ⟨y0, rfl, h0⟩ := ih
    refine ⟨y0, rfl, .next hi0 (fun x hx => hg x ?_) (fun ds o ss hx hm => ?_) h0⟩
    · simp [JasminLsemExportTransfer.renRM, hx, JasminLsemExportTransfer.renLinstrR]
    · refine hd (ds.map (JasminLsemExportTransfer.renOperand τ)) o
        (ss.map (JasminLsemExportTransfer.renOperand τ)) (by simp only
          [JasminLsemExportTransfer.renRM, hx, JasminLsemExportTransfer.renLinstrR]) ?_
      rw [RegionAllocMapLive.regDefs_renRM]
      exact List.mem_map_of_mem hm
  | @jump m i' l p y hi hl hp _ ih =>
    obtain ⟨i, hi0, rfl⟩ := Option.map_eq_some_iff.mp (List.getElem?_map ▸ hi)
    obtain ⟨y0, rfl, h0⟩ := ih
    rw [JasminLsemExportRewrites.findLabelMem_map_renRM] at hp
    exact ⟨y0, rfl, .jump hi0 ((hjl i.1).symm.trans hl) hp h0⟩
  | @out y hy =>
    obtain ⟨y0, hy0, rfl⟩ := hO y hy
    exact ⟨y0, rfl, by simpa using (PLiveR.out hy0 : PLiveR L O0 L.length y0)⟩

/-! ## 7. The coalesced code of the parts against the input of the allocation -/

open JasminDialect (JasminTy)

/-- The alias steps of register copies leave the alias table unchanged. -/
theorem foldl_aliasStepO_movesOf (outs : List (String × Nat)) (ps : List (String × String))
    (M : Std.HashMap String String) :
    (JasminLsemRenameLoop.movesOf ps).foldl (X86Backend.ImageStraightRoute.aliasStepO outs) M
      = M := by
  unfold JasminLsemRenameLoop.movesOf
  induction ps generalizing M with
  | nil => rfl
  | cons p ps ih =>
    rw [List.map_cons, List.foldl_cons]
    have hs : X86Backend.ImageStraightRoute.aliasStepO outs M
        (JasminLsemExportLower.movWire p.2 p.1 "MOV:64", .reg none) = M := by
      simp [X86Backend.ImageStraightRoute.aliasStepO, JasminLsemExportLower.movWire,
        LprogIsa.shadowCall?]
    rw [hs]
    exact ih M

/-- The alias steps of the result copy into `D` keep the image of every name other than the
    versions `copyName D (k + 1)`, `k < m`. -/
theorem getD_foldl_aliasStepO_resCopyCode (outs : List (String × Nat)) (src D : String)
    (m : Nat) (M : Std.HashMap String String) {n : String}
    (hn : ∀ k, k < m → n ≠ copyName D (k + 1)) :
    ((resCopyCode src D m).foldl (X86Backend.ImageStraightRoute.aliasStepO outs) M).getD n n
      = M.getD n n := by
  refine RegionCoComplete.getD_foldl_aliasStepO_of _ M fun j hj M' => ?_
  obtain ⟨k, hk, hj⟩ := List.mem_flatMap.mp hj
  have hk' := List.mem_range.mp hk
  simp only [resCopyStep, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl
  · simp [X86Backend.ImageStraightRoute.aliasStepO, ExportRegions.movImmI, ExportRegions.movI,
      LprogIsa.shadowCall?, withWidthTag]
  · rfl
  · have hne : (copyName D (k + 1) == n) = false :=
      beq_eq_false_iff_ne.mpr (Ne.symm (hn k hk'))
    rw [X86Backend.FreshenArr.aliasStepO_store, Std.HashMap.getD_insert, hne]
    rfl

/-- The renaming of the array positions of an instruction depends only on the images of the
    names the instruction mentions. -/
theorem renArr_congr {σ σ' : String → String} {i : LinstrRM}
    (h : ∀ n ∈ LprogCallCut.instrNames i.1, σ n = σ' n) :
    X86Backend.ImageCoalesceCfg.renArr σ i = X86Backend.ImageCoalesceCfg.renArr σ' i := by
  obtain ⟨w, tag⟩ := i
  have hn : ∀ n ∈ LprogCallCut.instrNames w, σ n = σ' n := h
  have hnm : ∀ (ds : List LOperand) (o : String) (ss : List LOperand), w = .Lopn ds o ss →
      ∀ op ∈ ds ++ ss, ∀ n ∈ LprogCallCut.opNames op, σ n = σ' n := by
    intro ds o ss hw op hop n hnop
    subst hw
    exact hn n (List.mem_flatMap.mpr ⟨op, hop, hnop⟩)
  have hcall : X86Backend.ImageCoalesceCfg.renCallW σ w
      = X86Backend.ImageCoalesceCfg.renCallW σ' w := by
    unfold X86Backend.ImageCoalesceCfg.renCallW
    split
    · next dst f srcs hs =>
      have hw := LprogIsa.eq_callShadow_of_shadowCall? hs
      have h1 := hnm _ _ _ hw (.reg dst) (by simp) dst (by simp [LprogCallCut.opNames])
      rw [h1]
      congr 1
      refine List.map_congr_left fun o ho => ?_
      cases o with
      | reg x =>
        show LOperand.reg (σ x) = LOperand.reg (σ' x)
        rw [hnm _ _ _ hw (.reg x) (by simp [ho]) x (by simp [LprogCallCut.opNames])]
      | arr _ _ => rfl
      | imm _ => rfl
      | arrIdx _ _ _ => rfl
    · rfl
  cases tag <;> simp only [X86Backend.ImageCoalesceCfg.renArr]
  all_goals first
    | rw [hcall]
    | (congr 1
       first
       | (unfold X86Backend.ImageCoalesceCfg.renLoad
          split
          · rename_i d opn b x sc
            have hb : σ b = σ' b := hn b (by simp [LprogCallCut.instrNames, LprogCallCut.opNames])
            simp only [hb]
          · rfl)
       | (unfold X86Backend.ImageCoalesceCfg.renStore
          split
          · rename_i d opn b x sc v
            have hb : σ b = σ' b := hn b (by simp [LprogCallCut.instrNames, LprogCallCut.opNames])
            have hd : σ d = σ' d := hn d (by simp [LprogCallCut.instrNames, LprogCallCut.opNames])
            simp only [hb, hd]
          · rfl)
       | (unfold X86Backend.ImageCoalesceCfg.renStoreImm
          split
          · rename_i d opn b v k
            have hb : σ b = σ' b := hn b (by simp [LprogCallCut.instrNames, LprogCallCut.opNames])
            have hd : σ d = σ' d := hn d (by simp [LprogCallCut.instrNames, LprogCallCut.opNames])
            simp only [hb, hd]
          · rfl)
       | (unfold X86Backend.ImageCoalesceCfg.renZero
          split
          · rename_i d opn ss
            have hd : σ d = σ' d := hn d (by simp [LprogCallCut.instrNames, LprogCallCut.opNames])
            have hs : ss.map (X86Backend.ImageCoalesceCfg.renOpA σ)
                = ss.map (X86Backend.ImageCoalesceCfg.renOpA σ') := by
              refine List.map_congr_left fun o ho => ?_
              cases o with
              | arr b k =>
                show LOperand.arr (σ b) k = LOperand.arr (σ' b) k
                rw [hn b (by simp [LprogCallCut.instrNames]; exact Or.inr ⟨_, ho, by
                  simp [LprogCallCut.opNames]⟩)]
              | arrIdx b x sc =>
                show LOperand.arrIdx (σ b) x sc = LOperand.arrIdx (σ' b) x sc
                rw [hn b (by simp [LprogCallCut.instrNames]; exact Or.inr ⟨_, ho, by
                  simp [LprogCallCut.opNames]⟩)]
              | reg _ => rfl
              | imm _ => rfl
            simp only [hd, hs]
          · rfl))

/-- The instruction `i` mentions no version `copyName D (k + 1)` of the result buffer `D`. -/
def CopyFree (D : String) (i : LinstrRM) : Prop :=
  ∀ n ∈ LprogCallCut.instrNames i.1, ∀ k, n ≠ copyName D (k + 1)

theorem resCopyOf_buf {D : String} {t : JasminTy} {code : List LinstrRM} {res : List LOperand}
    {src D' : String} {m : Nat} (h : resCopyOf D t code res = some (src, D', m)) : D' = D := by
  unfold resCopyOf at h
  split at h
  · split_ifs at h
    cases h
    rfl
  · cases h

/-- **The coalescing renaming of the parts and of the allocation agree on the exported code**
    (`renArr_regionCoCode_eq`): an instruction of `code` that mentions no version of the
    result buffer of either result copy has the same array positions under the alias table
    of `regionCoCode` and under the alias table of `code` followed by `regionLprogCopy`. The
    suffixes add the register copies of the result, which leave the alias table unchanged,
    and the stores of the result copy, which add the versions of the result buffer. -/
theorem renArr_regionCoCode_eq (σ : AbiLayout) (nm : String → String) (t : JasminTy)
    (code : List LinstrRM) (res : List LOperand) (cp : Option (String × String × Nat))
    (a : AbiNames) (ts : List JasminTy) {i : LinstrRM}
    (hM : ∀ src D m, cp = some (src, D, m) → CopyFree D i) (hB : CopyFree a.outArg i) :
    X86Backend.ImageCoalesceCfg.renArr
        (canonMemrefName (X86Backend.ImageStraightRoute.aliasTab []
          (regionCoCode σ nm t code res cp))) i
      = X86Backend.ImageCoalesceCfg.renArr
        (canonMemrefName (X86Backend.ImageStraightRoute.aliasTab []
          (code ++ regionLprogCopy a none ts code res))) i := by
  refine renArr_congr fun n hn => ?_
  unfold canonMemrefName X86Backend.ImageStraightRoute.aliasTab
  have hL : ((regionCoCode σ nm t code res cp).foldl
        (X86Backend.ImageStraightRoute.aliasStepO []) {}).getD n n
      = (code.foldl (X86Backend.ImageStraightRoute.aliasStepO []) {}).getD n n := by
    unfold regionCoCode
    cases cp with
    | none => rw [List.foldl_append, foldl_aliasStepO_movesOf]
    | some c =>
      obtain ⟨src, D, m⟩ := c
      rw [List.foldl_append, List.foldl_append, foldl_aliasStepO_movesOf,
        getD_foldl_aliasStepO_resCopyCode _ _ _ _ _ (fun k _ => hM src D m rfl n hn k)]
  have hR : ((code ++ regionLprogCopy a none ts code res).foldl
        (X86Backend.ImageStraightRoute.aliasStepO []) {}).getD n n
      = (code.foldl (X86Backend.ImageStraightRoute.aliasStepO []) {}).getD n n := by
    rw [List.foldl_append]
    unfold regionLprogCopy
    split
    · split
      · rename_i src D m hc
        rw [resCopyOf_buf hc]
        exact getD_foldl_aliasStepO_resCopyCode _ _ _ _ _ (fun k _ => hB n hn k)
      · rfl
    · rfl
  rw [hL, hR]

/-- A name live at the end of a code is read after it. -/
theorem pLiveR_end {C : List LinstrRM} {O : List String} {y : String} {n : Nat}
    (h : PLiveR C O n y) (hn : C.length = n) : y ∈ O := by
  cases h with
  | read hi _ => simp [← hn] at hi
  | next hi _ _ _ => simp [← hn] at hi
  | jump hi _ _ _ => simp [← hn] at hi
  | out hy => exact hy

/-- The liveness grows with the names read after the code. -/
theorem pLiveR_mono_outs {C : List LinstrRM} {O O' : List String} (hO : ∀ z ∈ O, z ∈ O')
    {k : Nat} {y : String} (h : PLiveR C O k y) : PLiveR C O' k y := by
  induction h with
  | read hi hy => exact .read hi hy
  | next hi hg hd _ ih => exact .next hi hg hd ih
  | jump hi hl hp _ ih => exact .jump hi hl hp ih
  | out hy => exact .out (hO _ hy)

/-- **The liveness of a prefix in the whole code**: a name live at a position of `X`, read
    after `X` as names live at the end of `X` in `X ++ Y`, is live there in `X ++ Y`. -/
theorem pLiveR_append_left {X Y : List LinstrRM} {O O0 : List String}
    (hO0 : ∀ z ∈ O0, PLiveR (X ++ Y) O X.length z) {k : Nat} {y : String}
    (h : PLiveR X O0 k y) : PLiveR (X ++ Y) O k y := by
  refine pLiveR_map (f := id) (fun k i hi => ⟨i, ?_, LiveSim.refl y i⟩) (fun _ _ hl => hl)
    (fun l p hp => ?_) (fun hy => hO0 _ hy) h
  · rw [id, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hi).1]
    exact hi
  · unfold findLabelMem JasminLsemLabeled.findLabel at hp ⊢
    rw [List.map_append, List.findIdx?_append, hp]
    rfl

/-- The pairs of the renaming of the parts fix a hardware register name. -/
theorem renOf_certArgs_of_hw {σ : AbiLayout} {cert : List (String × String)} {z : String}
    (hz : isHwRegName z = true) : JasminLsemRenameLoop.renOf (certArgs σ cert) z = z := by
  apply JasminLsemRenameLoop.renOf_of_not_mem
  intro hm
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
  obtain ⟨j, -, hj⟩ := RegionAllocMapLive.exists_of_isArgNameB (List.mem_filter.mp hp).2
  exact (RegionAllocMapLive.hw_ne hz).2 j hj

theorem isLabel_movesOf (ps : List (String × String)) :
    ∀ i ∈ JasminLsemRenameLoop.movesOf ps, ∀ l, JasminLsemLabeled.isLabel l i.1 = false := by
  intro i hi l
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hi
  rfl

theorem isLabel_resCopyCode (src D : String) (m : Nat) :
    ∀ i ∈ resCopyCode src D m, ∀ l, JasminLsemLabeled.isLabel l i.1 = false := by
  intro i hi l
  obtain ⟨k, -, hk⟩ := List.mem_flatMap.mp hi
  simp only [resCopyStep, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl <;> rfl

/-- The code of the parts is the exported code followed by label-free result copies. -/
theorem regionCoCode_split (σ : AbiLayout) (nm : String → String) (t : JasminTy)
    (code : List LinstrRM) (res : List LOperand) (cp : Option (String × String × Nat)) :
    ∃ S, regionCoCode σ nm t code res cp = code ++ S
      ∧ ∀ i ∈ S, ∀ l, JasminLsemLabeled.isLabel l i.1 = false := by
  unfold regionCoCode
  cases cp with
  | none => exact ⟨_, rfl, isLabel_movesOf _⟩
  | some c =>
    obtain ⟨src, D, m⟩ := c
    refine ⟨_ ++ _, List.append_assoc _ _ _, fun i hi l => ?_⟩
    rcases List.mem_append.mp hi with hi | hi
    · exact isLabel_movesOf _ i hi l
    · exact isLabel_resCopyCode src D m i hi l

/-- **The liveness of the parts restricted to the coalesced exported code**
    (`pLiveR_regionCoParts_code`): a name in the liveness table of the parts `d` at the
    position `d.pre.length + k` of the exported code, `k ≤ code.length`, is the image under
    the pairs `d.ps` of a name live at `k` in the coalesced exported code, read after it as
    the names live at the end of the exported code in the coalesced code `regionCoBody`
    read after as `d.outs`. The pairs fix the targets of the result copy, the hardware
    register names read after the code. -/
theorem pLiveR_regionCoParts_code (σ : AbiLayout) (nm : String → String) (body : Lcmd)
    (t : JasminTy) (code : List LinstrRM) (res : List LOperand) (cert : List (String × String))
    (hRA : ∀ RA, σ.result = .reg RA → isHwRegName (nm RA) = true) {k : Nat} {y : String}
    (hk : k ≤ code.length)
    (hy : y ∈ tabAt (regionCoParts σ nm body t code res cert none).live
      ((regionCoParts σ nm body t code res cert none).pre.length + k)) :
    ∃ y0, JasminLsemRenameLoop.renOf (regionCoParts σ nm body t code res cert none).ps y0 = y
      ∧ PLiveR (code.map (X86Backend.ImageCoalesceCfg.renArr (canonMemrefName
          (regionAliasTab σ nm t none res
            (regionCoCode σ nm t code res (regionCopy σ nm t none code res))))))
        (tabAt (liveRegTab (regionCoBody σ nm t code res none)
          (regionCoParts σ nm body t code res cert none).outs) code.length) k y0 := by
  obtain ⟨S, hS, hSl⟩ := regionCoCode_split σ nm t code res (regionCopy σ nm t none code res)
  have hB : regionCoBody σ nm t code res none
      = [] ++ code.map (X86Backend.ImageCoalesceCfg.renArr (canonMemrefName
          (regionAliasTab σ nm t none res
            (regionCoCode σ nm t code res (regionCopy σ nm t none code res)))))
        ++ S.map (X86Backend.ImageCoalesceCfg.renArr (canonMemrefName
          (regionAliasTab σ nm t none res
            (regionCoCode σ nm t code res (regionCopy σ nm t none code res))))) := by
    show (regionCoCode σ nm t code res (regionCopy σ nm t none code res)).map
      (X86Backend.ImageCoalesceCfg.renArr (canonMemrefName
        (regionAliasTab σ nm t none res
          (regionCoCode σ nm t code res (regionCopy σ nm t none code res))))) = _
    generalize canonMemrefName (regionAliasTab σ nm t none res
      (regionCoCode σ nm t code res (regionCopy σ nm t none code res))) = ρ
    rw [hS, List.map_append, List.nil_append]
  have hpre : ∀ i ∈ (regionCoParts σ nm body t code res cert none).pre, ∀ l,
      JasminLsemLabeled.isLabel l i.1 = false := by
    intro i hi l
    rcases List.mem_append.mp hi with hi | hi
    · exact isLabel_movesOf _ i hi l
    · exact isLabel_movesOf _ i hi l
  have hlen : code.length ≤ (regionCoParts σ nm body t code res cert none).ren.length := by
    show code.length ≤ ((regionCoBody σ nm t code res none).map _).length
    rw [List.length_map, hB]
    simp
  have h1 : PLiveR ((regionCoParts σ nm body t code res cert none).pre
      ++ (regionCoParts σ nm body t code res cert none).ren ++ [])
      (regionCoParts σ nm body t code res cert none).outs
      ((regionCoParts σ nm body t code res cert none).pre.length + k) y := by
    rw [List.append_nil]
    exact mem_liveRegTab_iff.mp hy
  have h2 := pLiveR_segment hpre (by simp) (by omega) h1
  rw [List.append_nil, ← List.length_append, liveRegTab_end] at h2
  obtain ⟨y0, hy0, h3⟩ := pLiveR_renRM (L := regionCoBody σ nm t code res none)
    (O0 := (regionCoParts σ nm body t code res cert none).outs)
    (fun z hz => ⟨z, hz, renOf_certArgs_of_hw
      (RegionAllocMapAlign.outs_hw_regionCoParts body t code res cert none hRA z hz)⟩) h2
  refine ⟨y0, hy0, ?_⟩
  rw [hB] at h3
  have h4 := pLiveR_segment (pre := []) (by simp) (fun i hi l => ?_) ?hk
    (by simpa using h3)
  · rw [← hB] at h4
    simpa using h4
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    rw [X86Backend.ImageCoalesceCfg.isLabel_renArr]
    exact hSl j hj l
  · rw [List.length_map]
    exact hk

/-- **The liveness of the parts in the code given to the allocation**
    (`pLiveR_regionCoParts_alloc`): under the agreement `hcode` of the two coalescing
    renamings on the exported code (`renArr_regionCoCode_eq`) and the boundary condition
    `hbd` (the names live at the end of the exported code in the coalesced code of the parts
    are live there in the coalesced code of the allocation, read after as `O`), a name in
    the liveness table of the parts at the position `d.pre.length + k`, `k ≤ code.length`,
    is the image under the pairs `d.ps` of a name live at `k` in the code `code` followed by
    `regionLprogCopy`, renamed by its alias table and read after as `O`. -/
theorem pLiveR_regionCoParts_alloc (σ : AbiLayout) (nm : String → String) (body : Lcmd)
    (t : JasminTy) (code : List LinstrRM) (res : List LOperand) (cert : List (String × String))
    (a : AbiNames) (ts : List JasminTy) (O : List String)
    (hRA : ∀ RA, σ.result = .reg RA → isHwRegName (nm RA) = true)
    (hcode : ∀ i ∈ code,
      X86Backend.ImageCoalesceCfg.renArr (canonMemrefName (regionAliasTab σ nm t none res
          (regionCoCode σ nm t code res (regionCopy σ nm t none code res)))) i
        = X86Backend.ImageCoalesceCfg.renArr (canonMemrefName
          (resAliasTab [] (resAliasOf none (some a.outArg) ts res)
            (code ++ regionLprogCopy a none ts code res))) i)
    (hbd : ∀ z, PLiveR (regionCoBody σ nm t code res none)
        (regionCoParts σ nm body t code res cert none).outs code.length z →
      PLiveR ((code ++ regionLprogCopy a none ts code res).map
        (X86Backend.ImageCoalesceCfg.renArr (canonMemrefName
          (resAliasTab [] (resAliasOf none (some a.outArg) ts res)
            (code ++ regionLprogCopy a none ts code res)))))
        O code.length z)
    {k : Nat} {y : String} (hk : k ≤ code.length)
    (hy : y ∈ tabAt (regionCoParts σ nm body t code res cert none).live
      ((regionCoParts σ nm body t code res cert none).pre.length + k)) :
    ∃ y0, JasminLsemRenameLoop.renOf (regionCoParts σ nm body t code res cert none).ps y0 = y
      ∧ PLiveR ((code ++ regionLprogCopy a none ts code res).map
        (X86Backend.ImageCoalesceCfg.renArr (canonMemrefName
          (resAliasTab [] (resAliasOf none (some a.outArg) ts res)
            (code ++ regionLprogCopy a none ts code res)))))
        O k y0 := by
  obtain ⟨y0, hy0, h⟩ := pLiveR_regionCoParts_code σ nm body t code res cert hRA hk hy
  refine ⟨y0, hy0, ?_⟩
  rw [List.map_congr_left hcode] at h
  rw [List.map_append]
  refine pLiveR_append_left (fun z hz => ?_) h
  rw [List.length_map, ← List.map_append]
  exact hbd z (mem_liveRegTab_iff.mp hz)

/-- After a register copy of `s` into `R` read after as `[R]`, the names live before the copy
    are `s`. -/
theorem pLiveR_append_mov {X : List LinstrRM} {R s z : String} {n : Nat}
    (h : PLiveR (X ++ [(JasminLsemExportLower.movWire R s "MOV:64", .reg none)]) [R] n z)
    (hn : n = X.length) : z = s := by
  subst hn
  have hget : ∀ i, (X ++ [(JasminLsemExportLower.movWire R s "MOV:64", .reg none)])[X.length]?
      = some i → i = (JasminLsemExportLower.movWire R s "MOV:64", .reg none) := by
    intro i hi
    rw [List.getElem?_append_right le_rfl, Nat.sub_self] at hi
    simpa [eq_comm] using hi
  generalize hn : X.length = n at h
  cases h with
  | read hi hy =>
    subst hn
    obtain rfl := hget _ hi
    simpa [useNames, JasminLsemExportLower.movWire, JasminLsemExportRewrites.opNames] using hy
  | next hi hg hd hl =>
    subst hn
    obtain rfl := hget _ hi
    have hz := pLiveR_end hl (by simp)
    rw [List.mem_singleton] at hz
    subst hz
    exact absurd (by simp [regDefs, JasminLsemMemFlagGuard.cmpArgs?,
      JasminLsemMemFlagGuard.movRegArgs?, JasminLsemExportRegAlloc.memRegDefs,
      JasminLsemExportRegAlloc.storeHit?, JasminLsemExportRegAlloc.defNames,
      JasminLsemExportLower.movWire, JasminLsemExportRewrites.opNames])
      (hd _ _ _ rfl)
  | jump hi hl _ _ =>
    subst hn
    obtain rfl := hget _ hi
    simp [jumpLabel?, JasminLsemExportLower.movWire] at hl
  | out _ => simp at hn

theorem pLiveR_out_of {C : List LinstrRM} {O : List String} {y : String} {n : Nat}
    (hy : y ∈ O) (hn : C.length = n) : PLiveR C O n y :=
  hn ▸ .out hy

/-- The result copy `regionRet` of a register result. -/
theorem regionRet_some {σ : AbiLayout} {nm : String → String} {t : JasminTy}
    {res : List LOperand} {s R : String} (h : regionRet σ nm t res = some (s, R)) :
    ∃ w RA op, t = .reg w ∧ σ.result = .reg RA ∧ res = [op]
      ∧ s = JasminLsemWidthN.operandName op ∧ R = nm RA := by
  unfold regionRet at h
  split at h
  · split at h
    · rename_i RA op hσ
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨_, RA, op, rfl, hσ, rfl, h.1.symm, h.2.symm⟩
    · cases h
  · cases h

/-- **The boundary condition of the parts at the allocation** (`bd_regionCoParts`): at one
    result type `t`, when the output array `a.outArg` is the result buffer of the layout and
    the operand of a single returned operand is read after the code given to the allocation,
    the names live at the end of the exported code in the coalesced code of the parts are
    live there in the coalesced code of the allocation. With an array result copy the two
    codes are equal and nothing is read after them; with a register result the copy into
    the result register reads the returned operand; otherwise nothing is live there. -/
theorem bd_regionCoParts (σ : AbiLayout) (nm : String → String) (body : Lcmd)
    (t : JasminTy) (code : List LinstrRM) (res : List LOperand) (cert : List (String × String))
    (a : AbiNames) (ts : List JasminTy) (O : List String) (hts : ts = [t])
    (hout : ∀ D n, regionResBuf σ nm = some (D, n) → a.outArg = D)
    (hO : ∀ op, res = [op] → JasminLsemWidthN.operandName op ∈ O) :
    ∀ z, PLiveR (regionCoBody σ nm t code res none)
        (regionCoParts σ nm body t code res cert none).outs code.length z →
      PLiveR ((code ++ regionLprogCopy a none ts code res).map
        (X86Backend.ImageCoalesceCfg.renArr (canonMemrefName
          (resAliasTab [] (resAliasOf none (some a.outArg) ts res)
            (code ++ regionLprogCopy a none ts code res)))))
        O code.length z := by
  intro z hz
  subst hts
  have houts : (regionCoParts σ nm body t code res cert none).outs
      = (regionRet σ nm t res).toList.map Prod.snd := rfl
  rcases hc : regionCopy σ nm t none code res with _ | ⟨src, D, m⟩
  · have hB : regionCoBody σ nm t code res none
        = (code ++ JasminLsemRenameLoop.movesOf (regionRet σ nm t res).toList).map
          (X86Backend.ImageCoalesceCfg.renArr (canonMemrefName
            (regionAliasTab σ nm t none res
              (code ++ JasminLsemRenameLoop.movesOf (regionRet σ nm t res).toList)))) := by
      unfold regionCoBody
      rw [hc]
      rfl
    rw [houts, hB] at hz
    rcases hr : regionRet σ nm t res with _ | ⟨s, R⟩
    · rw [hr] at hz
      have := pLiveR_end hz (by simp [JasminLsemRenameLoop.movesOf])
      simp at this
    · obtain ⟨w, RA, op, rfl, -, hres, rfl, rfl⟩ := regionRet_some hr
      rw [hr, Option.toList_some, List.map_append, List.map_cons, List.map_nil] at hz
      have hmv : JasminLsemRenameLoop.movesOf [(JasminLsemWidthN.operandName op, nm RA)]
          = [(JasminLsemExportLower.movWire (nm RA) (JasminLsemWidthN.operandName op)
            "MOV:64", .reg none)] := rfl
      rw [RegionExportDefInitSort.map_renArr_of_regTag (fun i hi =>
        ⟨by obtain ⟨p, -, rfl⟩ := List.mem_map.mp hi; exact ⟨none, rfl⟩,
          RegionCoComplete.noShadow_movesOf _ i hi⟩), hmv] at hz
      obtain rfl := pLiveR_append_mov hz (by simp)
      have hcp : regionLprogCopy a none [.reg w] code res = [] := rfl
      rw [hcp]
      exact pLiveR_out_of (hO op hres) (by simp)
  · obtain ⟨-, ht, -, -, -, -⟩ := regionCopy_some hc
    have hc' := hc
    unfold regionCopy at hc'
    split at hc'
    · rename_i D' n hbuf
      obtain ⟨hc1, -⟩ := Option.filter_eq_some_iff.mp hc'
      have hD := resCopyOf_buf hc1
      subst hD
      have haD := hout _ _ hbuf
      have hcopy : regionLprogCopy a none [t] code res = resCopyCode src D m := by
        simp [regionLprogCopy, haD, hc1]
      have hret : regionRet σ nm t res = none := by
        subst ht
        rfl
      have hcode : regionCoCode σ nm t code res (some (src, D, m))
          = code ++ regionLprogCopy a none [t] code res := by
        unfold regionCoCode
        rw [hret, hcopy]
        simp [JasminLsemRenameLoop.movesOf]
      have hB : regionCoBody σ nm t code res none
          = (code ++ regionLprogCopy a none [t] code res).map
            (X86Backend.ImageCoalesceCfg.renArr (canonMemrefName
              (resAliasTab [] (resAliasOf none (some a.outArg) [t] res)
                (code ++ regionLprogCopy a none [t] code res)))) := by
        unfold regionCoBody regionAliasTab
        rw [hc, hcode, hbuf, haD]
        rfl
      rw [houts, hret, hB] at hz
      exact pLiveR_mono_outs (by simp) hz
    · cases hc'

/-- The pairs of the renaming fix a name the merge keeps that is no vector register name:
    the image of an argument name under the allocation is a hardware register name, a
    frame-slot name, a vector register name or the argument name, and the merge keeps none
    of them. -/
theorem eq_of_renOf_certArgs_keep {σ : AbiLayout} {B : Lcmd} {tbl : Array Nat}
    {arrs X : List String} {y0 y : String}
    (h : JasminLsemRenameLoop.renOf (certArgs σ (allocCertOf B tbl)) y0 = y)
    (hK : certMergeKeep σ arrs X y = true) (hv : y ∉ vectorRegNames) : y0 = y := by
  unfold certArgs at h
  rw [renOf_filter_allocCertOf B tbl _ (isArgNameB σ) y0] at h
  split_ifs at h with hc
  · exfalso
    subst h
    rcases allocName_cases B tbl y0 with h1 | h1 | h1 | h1
    · simp [certMergeKeep, h1] at hK
    · simp [certMergeKeep, h1] at hK
    · exact hv h1
    · rw [h1] at hK
      simp [certMergeKeep, hc.2] at hK
  · exact h

/-- The array an instruction accesses, under a renaming of every name, is the image of the
    array the instruction accesses. -/
theorem arrUse?_renRM (τ : String → String) {i : LinstrRM} {x : String}
    (h : arrUse? i = some x) : arrUse? (JasminLsemExportTransfer.renRM τ i) = some (τ x) := by
  obtain ⟨w, tag⟩ := i
  cases tag <;> simp only [arrUse?] at h ⊢ <;> try cases h
  all_goals
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
    first
    | (unfold loadStruct? at hp
       split at hp
       · split_ifs at hp with hop
         subst hop
         cases hp
         simp [JasminLsemExportTransfer.renRM, JasminLsemExportTransfer.renLinstrR,
           JasminLsemExportTransfer.renOperand, loadStruct?]
       · cases hp)
    | (unfold storeStruct? at hp
       split at hp
       · split_ifs at hp with hop
         subst hop
         cases hp
         simp [JasminLsemExportTransfer.renRM, JasminLsemExportTransfer.renLinstrR,
           JasminLsemExportTransfer.renOperand, storeStruct?]
       · cases hp)
    | (unfold storeImmStruct? at hp
       split at hp
       · split_ifs at hp with hop
         subst hop
         cases hp
         simp [JasminLsemExportTransfer.renRM, JasminLsemExportTransfer.renLinstrR,
           JasminLsemExportTransfer.renOperand, storeImmStruct?]
       · cases hp)

/-- **No instruction of the code given to the allocation accesses a kept name as an array**
    (`arrUse_ne_of_keep`), when every instruction of that code accessing an array is an
    instruction of the coalesced code of the parts: the merge keeps no array name of the
    parts, and the pairs fix a kept name. -/
theorem arrUse_ne_of_keep (σ : AbiLayout) (nm : String → String) (body : Lcmd)
    (t : JasminTy) (code : List LinstrRM) (res : List LOperand) (cert : List (String × String))
    {X : List String} {y : String} {Z : List LinstrRM}
    (hsub : ∀ i ∈ Z, arrUse? i ≠ none → i ∈ regionCoBody σ nm t code res none)
    (hK : certMergeKeep σ (regionCoParts σ nm body t code res cert none).arrs X y = true) :
    ∀ i ∈ Z, arrUse? i ≠ some y := by
  intro i hi hu
  have hm := hsub i hi (by rw [hu]; exact Option.some_ne_none _)
  have hren : JasminLsemExportTransfer.renRM
      (JasminLsemRenameLoop.renOf (regionCoParts σ nm body t code res cert none).ps) i
        ∈ (regionCoParts σ nm body t code res cert none).ren := List.mem_map_of_mem hm
  have hy : JasminLsemRenameLoop.renOf (regionCoParts σ nm body t code res cert none).ps y = y := by
    apply JasminLsemRenameLoop.renOf_of_not_mem
    intro hmem
    obtain ⟨p, hp, hpy⟩ := List.mem_map.mp hmem
    have harg := (List.mem_filter.mp hp).2
    rw [hpy] at harg
    simp [certMergeKeep, harg] at hK
  have hA := RegionAllocMapClose.mem_arrNames_use hren
    (by rw [arrUse?_renRM _ hu, hy]; exact List.mem_singleton_self y)
  have hmem : y ∈ (regionCoParts σ nm body t code res cert none).arrs :=
    List.mem_append_left _ (List.mem_append_left _ hA)
  simp [certMergeKeep] at hK
  exact hK.2 hmem

/-- **A kept live name of the parts is live in the input of the allocation**
    (`pLiveR_regionCoParts_allocCode`): at the certificate `allocCertOf B tbl`, a name `y` in
    the liveness table of the parts at the position `d.pre.length + k`, `k ≤ code.length`,
    that the merge keeps and that is no vector register name, is live at `allocPos … k` in
    the input `regionAllocCode` of the allocation, read after as `O`, under the agreement of
    the renamings on the exported code and the boundary condition. -/
theorem pLiveR_regionCoParts_allocCode (σ : AbiLayout) (nm : String → String) (body : Lcmd)
    (t : JasminTy) (code : List LinstrRM) (res : List LOperand) (B : Lcmd) (tbl : Array Nat)
    (a : AbiNames) (ts : List JasminTy) (O : List String) {X : List String}
    (hRA : ∀ RA, σ.result = .reg RA → isHwRegName (nm RA) = true)
    (hcode : ∀ i ∈ code,
      X86Backend.ImageCoalesceCfg.renArr (canonMemrefName (regionAliasTab σ nm t none res
          (regionCoCode σ nm t code res (regionCopy σ nm t none code res)))) i
        = X86Backend.ImageCoalesceCfg.renArr (canonMemrefName
          (resAliasTab [] (resAliasOf none (some a.outArg) ts res)
            (code ++ regionLprogCopy a none ts code res))) i)
    (hbd : ∀ z, PLiveR (regionCoBody σ nm t code res none)
        (regionCoParts σ nm body t code res (allocCertOf B tbl) none).outs code.length z →
      PLiveR ((code ++ regionLprogCopy a none ts code res).map
        (X86Backend.ImageCoalesceCfg.renArr (canonMemrefName
          (resAliasTab [] (resAliasOf none (some a.outArg) ts res)
            (code ++ regionLprogCopy a none ts code res)))))
        O code.length z)
    {k : Nat} {y : String} (hk : k ≤ code.length)
    (hy : y ∈ tabAt (regionCoParts σ nm body t code res (allocCertOf B tbl) none).live
      ((regionCoParts σ nm body t code res (allocCertOf B tbl) none).pre.length + k))
    (hK : certMergeKeep σ (regionCoParts σ nm body t code res (allocCertOf B tbl) none).arrs X y
      = true)
    (hv : y ∉ vectorRegNames) :
    PLiveR (regionAllocCode (code ++ regionLprogCopy a none ts code res) []
        (resAliasOf none (some a.outArg) ts res)) O
      (allocPos (code ++ regionLprogCopy a none ts code res) []
        (resAliasOf none (some a.outArg) ts res) k) y := by
  obtain ⟨y0, hy0, h⟩ := pLiveR_regionCoParts_alloc σ nm body t code res (allocCertOf B tbl) a ts
    O hRA hcode hbd hk hy
  obtain rfl := eq_of_renOf_certArgs_keep hy0 hK hv
  exact pLiveR_regionAllocCode _ [] _ (by rintro rfl; simp [certMergeKeep] at hK) h

/-! ## 8. The live ranges of the certified body -/

open X86Backend.ToLprogFaithfulRAInterference (LiveAt)

/-- The trace position of the instruction at position `q` of a body: the number of operations
    before it, each of which is one event of `bodyTrace`. -/
def tracePos (B : Lcmd) (q : Nat) : Nat := (bodyOpNames (B.take q)).length

/-- The instruction `w` touches the name `n` in the trace: it is an operation whose first
    destination register or whose source register names hold `n`. -/
def TouchW (n : String) (w : LinstrR) : Prop :=
  ∃ ds o ss, w = .Lopn ds o ss
    ∧ (n ∈ (ds.head?.bind LOperand.regName?).toList ∨ n ∈ ss.flatMap LOperand.srcRegNames)

theorem bodyTraceOut_nil (B : Lcmd) : bodyTraceOut B [] = bodyTrace B := by
  simp [bodyTraceOut, outStoreSlots]

/-- The event of an operation that touches `n` touches the slot of `n`. -/
theorem tracePos_touch {B : Lcmd} {q : Nat} {li : Linstr} {n : String} (hq : B[q]? = some li)
    (hn : TouchW n li.li_i) :
    ∃ h : tracePos B q < (bodyTrace B).length,
      nameSlot B n ∈ ((bodyTrace B)[tracePos B q]'h).touched := by
  have hlt := (List.getElem?_eq_some_iff.mp hq).1
  have hget : B[q] = li := by
    rw [List.getElem?_eq_getElem hlt] at hq
    exact Option.some.inj hq
  obtain ⟨ds, o, ss, hw, hn⟩ := hn
  have hsplit : B = B.take q ++ li :: B.drop (q + 1) := by
    conv_lhs => rw [← List.take_append_drop q B]
    rw [List.drop_eq_getElem_cons hlt, hget]
  have hops : bodyOpNames B = bodyOpNames (B.take q)
      ++ (ds.head?.bind LOperand.regName?, ss.flatMap LOperand.srcRegNames)
        :: bodyOpNames (B.drop (q + 1)) := by
    conv_lhs => rw [hsplit]
    simp [bodyOpNames, List.filterMap_append, linstrRegNames, hw]
  have hev : (bodyTrace B)[tracePos B q]? = some
      { wr := ((ds.head?.bind LOperand.regName?).map (nameSlot B)).getD 0,
        rds := (ss.flatMap LOperand.srcRegNames).map (nameSlot B) } := by
    unfold bodyTrace tracePos
    rw [hops, List.getElem?_map, List.getElem?_append_right le_rfl, Nat.sub_self]
    rfl
  obtain ⟨hl, he⟩ := List.getElem?_eq_some_iff.mp hev
  refine ⟨hl, ?_⟩
  rw [he]
  simp only [PhysEvent.touched, List.mem_cons, List.mem_map]
  rcases hn with hn | hn
  · left
    cases hd : ds.head?.bind LOperand.regName? with
    | none => rw [hd] at hn; cases hn
    | some d =>
      rw [hd] at hn
      have hnd : n = d := by simpa using hn
      subst hnd
      rfl
  · exact Or.inr ⟨n, hn, rfl⟩

theorem tracePos_le (B : Lcmd) {q q' : Nat} (h : q ≤ q') : tracePos B q ≤ tracePos B q' := by
  unfold tracePos
  have hs : B.take q' = B.take q ++ (B.take q').drop q := by
    conv_lhs => rw [← List.take_append_drop q (B.take q')]
    rw [List.take_take, Nat.min_eq_left h]
  rw [hs]
  simp [bodyOpNames, List.filterMap_append]

/-- **Two names touched around an operation are live at its trace position**: when `y` is
    touched by operations at the positions `qy ≤ qx ≤ qy'` and `x` by the operation at `qx`,
    the slots of `y` and `x` are live at the trace position of `qx`. -/
theorem liveAt_of_touchW {B : Lcmd} {qy qx qy' : Nat} {ly lx ly' : Linstr} {x y : String}
    (hy1 : B[qy]? = some ly) (hy1t : TouchW y ly.li_i) (hx : B[qx]? = some lx)
    (hxt : TouchW x lx.li_i) (hy2 : B[qy']? = some ly') (hy2t : TouchW y ly'.li_i)
    (h1 : qy ≤ qx) (h2 : qx ≤ qy') :
    ∃ pos, LiveAt (bodyTraceOut B []) pos (nameSlot B y)
      ∧ LiveAt (bodyTraceOut B []) pos (nameSlot B x) := by
  rw [bodyTraceOut_nil]
  obtain ⟨hl1, ht1⟩ := tracePos_touch hy1 hy1t
  obtain ⟨hlx, htx⟩ := tracePos_touch hx hxt
  obtain ⟨hl2, ht2⟩ := tracePos_touch hy2 hy2t
  exact ⟨tracePos B qx,
    liveAt_of_touch_le_ge hl1 ht1 hl2 ht2 (tracePos_le B h1) (tracePos_le B h2),
    liveAt_of_touch_le_ge hlx htx hlx htx le_rfl le_rfl⟩

/-- The instructions inserted before the instruction at position `k` sit directly before its
    image, behind the images of the earlier positions. -/
theorem insBefore_pre : ∀ (C : List LinstrRM) (n k : Nat) (i : LinstrRM), C[k]? = some i →
    ∃ b, b + (ins (n + k) i).length = insPos ins C n k
      ∧ (∀ t, t < (ins (n + k) i).length → (insBefore ins C n)[b + t]? = (ins (n + k) i)[t]?)
      ∧ ∀ k', k' < k → insPos ins C n k' < b
  | [], _, _, _, h => by simp at h
  | j :: C, n, 0, i, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    refine ⟨0, by simp [insPos], fun t ht => ?_, fun k' hk' => absurd hk' (Nat.not_lt_zero _)⟩
    simp only [Nat.add_zero] at ht
    simp only [insBefore, Nat.add_zero, Nat.zero_add]
    rw [List.getElem?_append_left ht]
  | j :: C, n, k + 1, i, h => by
    obtain ⟨b, hb1, hb2, hb3⟩ := insBefore_pre C (n + 1) k i (by simpa using h)
    have he : n + (k + 1) = n + 1 + k := by omega
    rw [he]
    refine ⟨(ins n j).length + 1 + b, ?_, fun t ht => ?_, fun k' hk' => ?_⟩
    · simp only [insPos]
      omega
    · simp only [insBefore]
      rw [List.getElem?_append_right (by omega),
        show (ins n j).length + 1 + b + t - (ins n j).length = (b + t) + 1 by omega,
        List.getElem?_cons_succ]
      exact hb2 t ht
    · cases k' with
      | zero => simp only [insPos]; omega
      | succ k' =>
        have := hb3 k' (by omega)
        simp only [insPos]
        omega

/-- A name live at a position read after the code as `O` is live there read after as nothing,
    or a name of `O`. -/
theorem pLiveR_or_outs {C : List LinstrRM} {O : List String} {k : Nat} {y : String}
    (h : PLiveR C O k y) : PLiveR C [] k y ∨ y ∈ O := by
  induction h with
  | read hi hy => exact Or.inl (.read hi hy)
  | next hi hg hd _ ih => exact ih.imp (fun h => .next hi hg hd h) id
  | jump hi hl hp _ ih => exact ih.imp (fun h => .jump hi hl hp h) id
  | out hy => exact Or.inr hy

theorem touchW_of_useNames {w : LinstrR} {y : String} (h : y ∈ useNames w) : TouchW y w := by
  cases w with
  | Lopn ds o ss =>
    refine ⟨ds, o, ss, rfl, Or.inr ?_⟩
    obtain ⟨op, hop, hy⟩ := List.mem_flatMap.mp h
    have he : JasminLsemExportRewrites.opNames op = LOperand.srcRegNames op := by
      cases op <;> rfl
    exact List.mem_flatMap.mpr ⟨op, hop, he ▸ hy⟩
  | _ => simp [useNames] at h

/-- **The hull of a live name and a written name in the certified body** (ALIGN-HULL,
    `liveAt_hull`). Let the body `B` hold the code `backEdgePins P` behind the instructions
    `Pre`, let `x` be touched by the instruction `P[k]`, let `y` be live after it, at `k + 1`
    of `P` read after as `O`, where every name of `O` is touched by an instruction of `B`
    behind the code, and let `y` be touched by an instruction of `B` at or before the image
    of `k`. Then the slots of `y` and `x` are live at one trace position of
    `bodyTraceOut B []`, the trace position of the image of `k`. Forward, `y` is read at or
    after `k + 1` in `P` or by the `LIVEPIN` of `backEdgePins` before a back edge at or
    after `k + 1` (`liveRegTab_fwd`), or it is a name of `O`. -/
theorem liveAt_hull {B Pre : Lcmd} {P : List LinstrRM} {O : List String} {k : Nat}
    {i : LinstrRM} {x y : String}
    (hB : ∀ q, q < (backEdgePins P).length →
      B[Pre.length + q]? = ((backEdgePins P)[q]?).map fun j => (⟨0, j.1⟩ : Linstr))
    (hi : P[k]? = some i) (hx : TouchW x i.1) (hy : PLiveR P O (k + 1) y)
    (hO : ∀ z ∈ O, ∃ q li, Pre.length + (backEdgePins P).length ≤ q ∧ B[q]? = some li
      ∧ TouchW z li.li_i)
    (hyb : ∃ q li, q ≤ Pre.length + insPos (bePre (liveRegTab P []) P) P 0 k
      ∧ B[q]? = some li ∧ TouchW y li.li_i) :
    ∃ pos, LiveAt (bodyTraceOut B []) pos (nameSlot B y)
      ∧ LiveAt (bodyTraceOut B []) pos (nameSlot B x) := by
  have hk : k < P.length := (List.getElem?_eq_some_iff.mp hi).1
  have hac : backEdgePins P = insBefore (bePre (liveRegTab P []) P) P 0 := backEdgePins_eq_insBefore P
  have hlen : (backEdgePins P).length = insPos (bePre (liveRegTab P []) P) P 0 P.length := by
    rw [hac, insPos_length]
  -- the image of a position of `P` in `B`
  have himg : ∀ j i', P[j]? = some i' →
      insPos (bePre (liveRegTab P []) P) P 0 j < (backEdgePins P).length
        ∧ B[Pre.length + insPos (bePre (liveRegTab P []) P) P 0 j]?
          = some (⟨0, i'.1⟩ : Linstr) := by
    intro j i' hj
    have hjl : j < P.length := (List.getElem?_eq_some_iff.mp hj).1
    have hlt : insPos (bePre (liveRegTab P []) P) P 0 j < (backEdgePins P).length := by
      rw [hlen]
      exact insPos_lt P 0 hjl le_rfl
    refine ⟨hlt, ?_⟩
    rw [hB _ hlt, hac, getElem?_insPos P 0 j hjl, hj]
    rfl
  obtain ⟨hxl, hxB⟩ := himg k i hi
  obtain ⟨qy, ly, hqy, hly, hty⟩ := hyb
  -- a touch of `y` at or after the image of `k`
  have hfwd : ∃ q li, Pre.length + insPos (bePre (liveRegTab P []) P) P 0 k ≤ q
      ∧ B[q]? = some li ∧ TouchW y li.li_i := by
    rcases pLiveR_or_outs hy with h | h
    · rcases liveRegTab_fwd (liveRegTab_stable P []) (mem_liveRegTab_iff.mpr h) with
        ⟨j, i', hj, hi', hu⟩ | ⟨j, i', l, p, hj, hi', hl, -, -, ns, hpin, hns⟩
      · obtain ⟨-, hjB⟩ := himg j i' hi'
        have hjl : j < P.length := (List.getElem?_eq_some_iff.mp hi').1
        exact ⟨_, _, by
          have := insPos_lt (ins := bePre (liveRegTab P []) P) P 0 (show k < j by omega)
            hjl.le
          omega, hjB, touchW_of_useNames hu⟩
      · have hjl : j < P.length := (List.getElem?_eq_some_iff.mp hi').1
        have hbe : bePre (liveRegTab P []) P j i'
            = [(.Lopn [.reg "%livepin"] "LIVEPIN" (ns.map LOperand.reg), .reg none)] := by
          rw [← hpin]
          obtain ⟨w, tg⟩ := i'
          cases w <;> simp_all [bePre, jumpLabel?]
        obtain ⟨b, hb1, hb2, hb3⟩ := insBefore_pre (ins := bePre (liveRegTab P []) P) P 0 j i' hi'
        rw [Nat.zero_add, hbe] at hb1 hb2
        have hb0 := hb2 0 (by simp)
        have hkb := hb3 k (by omega)
        have hbl : b < (backEdgePins P).length := by
          rw [hlen]
          have := insPos_lt (ins := bePre (liveRegTab P []) P) P 0 (show j < P.length from hjl)
            le_rfl
          simp only [List.length_singleton] at hb1
          omega
        refine ⟨Pre.length + b, ⟨0, .Lopn [.reg "%livepin"] "LIVEPIN" (ns.map LOperand.reg)⟩,
          by omega, ?_, ⟨_, _, _, rfl, Or.inr ?_⟩⟩
        · rw [Nat.add_zero] at hb0
          rw [hB _ hbl, hac, hb0]
          rfl
        · simpa [List.flatMap_map, LOperand.srcRegNames] using hns
    · obtain ⟨q, li, hq, hqB, ht⟩ := hO y h
      exact ⟨q, li, by omega, hqB, ht⟩
  obtain ⟨qy', ly', hqy', hly', hty'⟩ := hfwd
  exact liveAt_of_touchW hly hty hxB hx hly' hty' hqy hqy'

/-- **The input of the allocation in the certified body** (`regionAllocBody_code`): when the
    export has the shape `ShapeB` and `canonicalizeMemrefThread` leaves the virtual body,
    alone or behind the entry pin `arrBasePins`, unchanged, the certified body holds the
    code `regionAllocCode` given to the allocation behind a prefix, one instruction per
    instruction. This is the hypothesis `hB` of `liveAt_hull` at `P` the pinned coalesced
    code, whose back-edge pins are that code. -/
theorem regionAllocBody_code (a : AbiNames) (nArgs : Nat) (ts : List JasminTy)
    (r : ExportRegions.Exported)
    (hr : ∀ i ∈ r.code, RegionAllocMapDom.ShapeB i.1)
    (hcanon : ∀ Pre : Lcmd,
      (Pre = [] ∨ Pre = arrBasePins a
        (regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) [] (resAliasOf none (some a.outArg) ts r.res))) →
      canonicalizeMemrefThread (Pre
        ++ ((regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) [] (resAliasOf none (some a.outArg) ts r.res)).map
          (fun i => (⟨0, i.1⟩ : Linstr)) ++ [⟨0, .Lret⟩]))
      = Pre ++ ((regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) [] (resAliasOf none (some a.outArg) ts r.res)).map
          (fun i => (⟨0, i.1⟩ : Linstr)) ++ [⟨0, .Lret⟩])) :
    ∃ Pre : Lcmd, ∀ q,
      q < (regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) [] (resAliasOf none (some a.outArg) ts r.res)).length →
      (RegionAllocMapAlign.regionAllocBody a nArgs ts r)[Pre.length + q]?
        = ((regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) [] (resAliasOf none (some a.outArg) ts r.res))[q]?).map
          fun j => (⟨0, j.1⟩ : Linstr) := by
  have hacS : ∀ i ∈ regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) [] (resAliasOf none (some a.outArg) ts r.res),
      RegionAllocMapDom.ShapeB i.1 := by
    refine RegionAllocMapDom.shapeB_regionAllocCode fun i hi => ?_
    rcases List.mem_append.mp hi with hi | hi
    · exact hr i hi
    · exact RegionAllocMapDom.shapeB_regionLprogCopy a ts r.code r.res i hi
  have hbody : ∀ i ∈ (regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res)
      [] (resAliasOf none (some a.outArg) ts r.res)).map (fun i => (⟨0, i.1⟩ : Linstr))
        ++ [⟨0, .Lret⟩],
      RegionAllocMapDom.ShapeB i.li_i := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      exact hacS j hj
    · rw [List.mem_singleton.mp hi]
      exact RegionAllocMapDom.shapeB_nonLopn (fun _ _ _ e => by cases e) (fun _ _ e => by cases e)
  have hget : ∀ (Pre Suf : Lcmd) (q : Nat),
      q < (regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) [] (resAliasOf none (some a.outArg) ts r.res)).length →
      (Pre ++ ((regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) [] (resAliasOf none (some a.outArg) ts r.res)).map
          (fun i => (⟨0, i.1⟩ : Linstr)) ++ [⟨0, .Lret⟩]) ++ Suf)[Pre.length + q]?
        = ((regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) [] (resAliasOf none (some a.outArg) ts r.res))[q]?).map
          fun j => (⟨0, j.1⟩ : Linstr) := by
    intro Pre Suf q hq
    rw [List.append_assoc, List.getElem?_append_right (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left, List.append_assoc,
      List.getElem?_append_left (by rw [List.length_map]; exact hq), List.getElem?_map]
  unfold RegionAllocMapAlign.regionAllocBody
  dsimp only
  split
  · refine ⟨[⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
      ((List.range nArgs).map fun j => (.reg (argName j) : LOperand))⟩], fun q hq => ?_⟩
    have hc0 := hcanon [] (Or.inl rfl)
    simp only [List.nil_append] at hc0
    rw [RegionAllocMapDom.expandCallShadows_of_shapeB hbody, hc0]
    exact hget _ _ q hq
  · refine ⟨(if a.abiArgs.length ≥ 4 then
        [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
          ((List.range a.abiArgs.length).map fun j => (.reg (argName j) : LOperand))⟩]
       else []) ++ arrBasePins a
        (regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) [] (resAliasOf none (some a.outArg) ts r.res)), fun q hq => ?_⟩
    rw [hcanon _ (Or.inr rfl)]
    have := hget ((if a.abiArgs.length ≥ 4 then
        [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
          ((List.range a.abiArgs.length).map fun j => (.reg (argName j) : LOperand))⟩]
       else []) ++ arrBasePins a
        (regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) [] (resAliasOf none (some a.outArg) ts r.res))) [] q hq
    simpa only [List.append_assoc, List.append_nil] using this

/-- A name the merge keeps is not the pin name. -/
theorem ne_livepin_of_keep {σ : AbiLayout} {arrs X : List String} {y : String}
    (hK : certMergeKeep σ arrs X y = true) : y ≠ "%livepin" := by
  rintro rfl
  simp [certMergeKeep] at hK

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapPins
