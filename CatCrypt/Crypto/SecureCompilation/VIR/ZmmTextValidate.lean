/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmLinearRender
public import CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmLinearRender
public import CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextModel
public meta import CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextModel

/-!
# Translation validation of the owned `%zmm` / `%ymm` text

`VpackZmmLinearRender.renderZmmLinearBinds` prints a straight-line binding list as AT&T
text through an unverified register allocation, operand selection (broadcast memory
operands, immediate shift counts, resident and scratch constants), the range-dependent
selections (`vpmuludq` for a 64-bit multiply, `vpminu` for the conditional add), the
high-multiply sequence and the `%ymm` form. `validate` checks one printed text against
the binding list it was printed from, so that none of these steps is trusted.

`validate` parses the text (`parse`, which accepts the renderer's own format only), runs
it on the machine model of `ZmmTextModel` symbolically, and after each instruction
replaces the written term by the name of the binding it computes (`norm`). The candidate
binding comes from a hash table keyed by the term's shape and is then checked by
`verify`, one recogniser per instruction form: `vBin` (a lane-wise operation, operands
exchanged for a commuting one), `vMulU` (`vpmuludq` as a 64-bit multiply, when range
facts or constant lanes put both operands below `2^32`), `vShi` (a shift by a constant
as an immediate shift), `vMulhi` and `vMullo` (the two halves of the `vpmuludq` /
`vmovshdup` / merge sequence) and `vMinu` (the conditional add as an unsigned minimum,
under the range fact `RangeDomain.condAdd_eq_umin` needs). A rotate `vprolq` and a
`vpternlogq` of a supported truth table need no recogniser of their own: the symbolic
step reads them as their composites of shifts and bitwise operations
(`ZmmTextModel.rolTerm`, `ZmmTextModel.ternTerms`), each node normalised, so that each
node is matched as the binding that computes it. The text is accepted when
store `j` writes a register holding output `j`. Names are compared up to value numbering
(`repTable`): the binding list may compute one value in several bindings, and the
bindings are checked in the form `renameB` gives them, reading representatives.

The reference is a lane valuation `E` (the value `E k n` of name `n` on lane `k`)
satisfying every binding on every active lane (`SatB`); the range facts are intervals
per name (`RangeDomain.Iv.Mem`), the form `ComRange.rangeAnalysis_sound` concludes.

## Main definitions

* `SatB`, `Facts`: the reference and the facts the checks rest on.
* `vBin`, `vMulU`, `vShi`, `vMulhi`, `vMullo`, `vMinu`, `vMontSub`, `verify`: the
  recognisers; `vMontSub` checks the Montgomery step kept in the even/odd products, under
  `montSub_extract`.
* `keyMap`, `norm`: the candidate table and the normaliser.
* `parse`: the parser of the renderer's text.
* `frameOK`: the discipline of the stack frame that holds spilled registers.
* `buildRep`, `repCheck`, `repTable`, `renameB`: value numbering of the bindings.
* `validate`: the validator.

## Main results

* `verify_sound`, `norm_sound`: a recognised term has the value of its binding.
* `repCheck_sound`: a name has the value of its representative.
* `validate_sound`: when `validate` accepts the text, running the parsed program on any
  input region holding the inputs succeeds and leaves at offset `stride·j` a value whose
  active lanes are the values of output `j` of the bindings on those lanes.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextValidate

open CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextModel
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp mulHiW)
open CatCrypt.Crypto.SecureCompilation.RangeDomain (Iv umin condAdd)
open CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmLinearRender (ZBind LaneW bopCommutes)

/-! ## 5. The reference: a lane valuation satisfying the bindings -/

/-- Lane `k` of the reference satisfies binding `b` at lane width `w`: `E k n` is the
    value of name `n` on lane `k`. -/
def SatB (w : LaneW) (E : Nat → String → BitVec w.bits) (k : Nat) : ZBind → Prop
  | .pack w' bop d a b => w' = w → E k d = bop.apply (E k a) (E k b)
  | .mulhi d a b => E k d = mulHiW (E k a) (E k b)
  | .const d v => E k d = lane w.bits (BitVec.ofNat 512 v) k
  | .shi w' l d a n => w' = w → E k d = if l then E k a <<< n else E k a >>> n
  | _ => True

/-- The packed reference: lane `k` of `pack E n` is `E k n`. -/
def pack (w : LaneW) (E : Nat → String → BitVec w.bits) (n : String) : BitVec 512 :=
  ofLanes w.bits (fun k => E k n)

/-- Lane `k` is active in mode `m` at width `w`. -/
def Active (m : Mode) (w : LaneW) (k : Nat) : Prop := w.bits * k + w.bits ≤ m.act

theorem laneBits_cases (w : LaneW) : w.bits = 32 ∨ w.bits = 64 := by
  cases w <;> simp [LaneW.bits]

theorem laneBits_pos (w : LaneW) : 0 < w.bits := by
  cases w <;> simp [LaneW.bits]

theorem active_iff (m : Mode) (w : LaneW) (k : Nat) : Active m w k ↔ k < m.act / w.bits := by
  unfold Active
  rcases laneBits_cases w with h | h <;> rw [h] <;> rcases m.act_cases with h' | h' <;>
    rw [h'] <;> omega

theorem Active.le512 {m : Mode} {w : LaneW} {k : Nat} (h : Active m w k) :
    w.bits * k + w.bits ≤ 512 := by
  unfold Active at h
  rcases m.act_cases with h' | h' <;> omega

theorem lane_pack {m : Mode} {w : LaneW} (E : Nat → String → BitVec w.bits) (n : String)
    {k : Nat} (hk : Active m w k) : lane w.bits (pack w E n) k = E k n :=
  lane_ofLanes _ (laneBits_pos w) hk.le512

/-- The name to binding table of a binding list. -/
def mkDefs (bs : Array ZBind) : Std.HashMap String ZBind :=
  bs.foldl (fun m b => m.insert b.dst b) {}

theorem mkDefs_mem (bs : Array ZBind) (n : String) (b : ZBind)
    (h : (mkDefs bs)[n]? = some b) : b ∈ bs.toList := by
  unfold mkDefs at h
  rw [← Array.foldl_toList] at h
  have key : ∀ (l : List ZBind) (m0 : Std.HashMap String ZBind),
      (∀ (n : String) (b : ZBind), m0[n]? = some b → b ∈ bs.toList) →
      (∀ b ∈ l, b ∈ bs.toList) →
      ∀ (n : String) (b : ZBind),
        (l.foldl (fun m b => m.insert b.dst b) m0)[n]? = some b → b ∈ bs.toList := by
    intro l
    induction l with
    | nil => intro m0 h0 _ n b h; exact h0 n b h
    | cons x l ih =>
      intro m0 h0 hl n b h
      refine ih _ ?_ (fun b hb => hl b (List.mem_cons_of_mem _ hb)) n b h
      intro n' b' h'
      rw [Std.HashMap.getElem?_insert] at h'
      split at h'
      · cases h'; exact hl x List.mem_cons_self
      · exact h0 n' b' h'
  exact key bs.toList {} (by simp) (fun b hb => hb) n b h

/-- The facts the validator's checks rest on: every binding holds on every active lane,
    and every range fact holds on every active lane. -/
structure Facts (m : Mode) (w : LaneW) (D : Std.HashMap String ZBind)
    (rf : Std.HashMap String Iv) (E : Nat → String → BitVec w.bits) : Prop where
  sat : ∀ (n : String) (b : ZBind), D[n]? = some b → ∀ k, Active m w k → SatB w E k b
  rng : ∀ (n : String) (i : Iv), rf[n]? = some i → ∀ k, Active m w k → i.Mem w.bits (E k n)

/-! ## 6. Operand matching and the recognisers -/

/-- The term `t` denotes the name `a`: it is `var a`, or `a` is a constant binding and `t`
    its value. -/
def opMatch (D : Std.HashMap String ZBind) (t : Term) (a : String) : Bool :=
  match t with
  | .var x => x == a
  | .cst c =>
    match D[a]? with
    | some (.const a' v) => a' == a && c == BitVec.ofNat 512 v
    | _ => false
  | _ => false

section Sound

variable {m : Mode} {w : LaneW} {D : Std.HashMap String ZBind} {rf : Std.HashMap String Iv}
  {E : Nat → String → BitVec w.bits} {σ0 : Fin 32 → BitVec 512}

theorem opMatch_lane (hf : Facts m w D rf E) {t : Term} {a : String}
    (h : opMatch D t a = true) {k : Nat} (hk : Active m w k) :
    lane w.bits (t.eval m σ0 (pack w E)) k = E k a := by
  cases t with
  | var x =>
    simp only [opMatch, beq_iff_eq] at h
    subst h
    simp only [Term.eval]
    rw [lane_wr _ hk, lane_pack E x hk]
  | cst c =>
    simp only [opMatch] at h
    split at h
    · rename_i a' v hd
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Term.eval]
      rw [lane_wr _ hk]
      exact (hf.sat _ _ hd k hk).symm
    · cases h
  | _ => simp [opMatch] at h

/-- Two terms whose evaluations are writes agree when their active lanes agree. -/
theorem eval_eq_var {X : BitVec 512} {n : String}
    (h : ∀ k, Active m w k → lane w.bits X k = E k n) :
    wr m X = (Term.var n).eval m σ0 (pack w E) := by
  simp only [Term.eval]
  apply wr_eq_of_lanes (laneBits_cases w)
  intro k hk
  rw [h k hk, lane_pack E n hk]

theorem JasminBinOp.apply_comm {L : Nat} (bop : JasminBinOp) (h : bopCommutes bop = true)
    (x y : BitVec L) : bop.apply x y = bop.apply y x := by
  cases bop <;> simp [bopCommutes] at h <;>
    simp [JasminBinOp.apply, BitVec.add_comm, BitVec.mul_comm, BitVec.and_comm, BitVec.or_comm,
      BitVec.xor_comm]

end Sound

/-- `lw L (bin bop) ta tb` computes binding `n = a bop b` (operands exchanged when `bop`
    commutes). -/
def vBin (w : LaneW) (D : Std.HashMap String ZBind) (n : String) (L : Nat)
    (bop : JasminBinOp) (ta tb : Term) : Bool :=
  match D[n]? with
  | some (.pack w' bop' d a b) =>
    decide (w' = w) && decide (d = n) && decide (L = w.bits) && decide (bop' = bop) &&
      ((opMatch D ta a && opMatch D tb b) ||
        (bopCommutes bop && opMatch D ta b && opMatch D tb a))
  | _ => false

/-- The lanes of `x` lie below `2^32`: by a range fact, or by the constant's lanes. -/
def narrow (m : Mode) (D : Std.HashMap String ZBind) (rf : Std.HashMap String Iv)
    (x : String) : Bool :=
  (match rf[x]? with
   | some i => decide (0 ≤ i.1 ∧ i.2 < 2 ^ 32)
   | none => false) ||
  (match D[x]? with
   | some (.const x' v) => decide (x' = x) &&
       (List.range (m.act / 64)).all (fun k => decide ((lane 64 (BitVec.ofNat 512 v) k).toNat < 2 ^ 32))
   | _ => false)

/-- `lw 64 muludq ta tb` (`vpmuludq`) computes the 64-bit product `n = a * b`, whose
    operands `narrow` shows below `2^32`. -/
def vMulU (w : LaneW) (m : Mode) (D : Std.HashMap String ZBind) (rf : Std.HashMap String Iv)
    (n : String) (ta tb : Term) : Bool :=
  match D[n]? with
  | some (.pack w' bop d a b) =>
    decide (w = .q) && decide (w' = .q) && decide (bop = .mul) && decide (d = n) &&
      narrow m D rf a && narrow m D rf b &&
      ((opMatch D ta a && opMatch D tb b) || (opMatch D ta b && opMatch D tb a))
  | _ => false

/-- `shi L left imm ta` computes the shift `n = a << kc` or `n = a >> kc` by the constant
    `kc`, every active lane of which is `imm`, a count below the lane width, or `n` is the
    immediate shift of `a` by `imm` in the same direction. -/
def vShi (w : LaneW) (m : Mode) (D : Std.HashMap String ZBind) (n : String) (L : Nat)
    (left : Bool) (imm : Nat) (ta : Term) : Bool :=
  match D[n]? with
  | some (.pack w' bop d a kc) =>
    decide (w' = w) && decide (d = n) && decide (L = w.bits) &&
      decide (bop = if left then .shl else .shr) && opMatch D ta a &&
      decide (imm < w.bits) &&
      (match D[kc]? with
       | some (.const kc' v) => decide (kc' = kc) &&
           (List.range (m.act / w.bits)).all
             (fun k => decide ((lane w.bits (BitVec.ofNat 512 v) k).toNat = imm))
       | _ => false)
  | some (.shi w' l d a i) =>
    decide (w' = w) && decide (d = n) && decide (L = w.bits) && decide (l = left) &&
      decide (i = imm) && opMatch D ta a
  | _ => false

/-- The odd factor `Bo` of the odd products holds the odd dwords of `B` in its even
    dwords: `Bo = vmovshdup B`, or `B` is a constant whose dword pairs are equal. -/
def oddOK (Bo B : Term) : Bool :=
  decide (Bo = .dup true B) ||
    (decide (Bo = B) && match B with
      | .cst c => decide (semDup true c = c)
      | _ => false)

/-- The high-multiply sequence: the even high words (`vmovshdup` of the even products)
    merged under `0x5555` into the odd products, `n = mulhi(a, b)`. -/
def vMulhi (w : LaneW) (D : Std.HashMap String ZBind) (n : String) (t : Term) : Bool :=
  match t with
  | .mdup true k0 (.lw 64 .muludq A B) (.lw 64 .muludq (.dup true A') Bo) =>
    decide (w = .d) && decide (k0 = 0x5555#16) && decide (A' = A) && oddOK Bo B &&
      (match D[n]? with
       | some (.mulhi d a b) => decide (d = n) &&
           ((opMatch D A a && opMatch D B b) || (opMatch D A b && opMatch D B a))
       | _ => false)
  | _ => false

/-- The low half of the same products: the odd low words (`vmovsldup` of the odd
    products) merged under `0xAAAA` into the even products, `n = a * b` on dwords. -/
def vMullo (w : LaneW) (D : Std.HashMap String ZBind) (n : String) (t : Term) : Bool :=
  match t with
  | .mdup false k0 (.lw 64 .muludq (.dup true A') Bo) (.lw 64 .muludq A B) =>
    decide (w = .d) && decide (k0 = 0xAAAA#16) && decide (A' = A) && oddOK Bo B &&
      (match D[n]? with
       | some (.pack w' bop d a b) => decide (w' = .d) && decide (bop = .mul) && decide (d = n) &&
           ((opMatch D A a && opMatch D B b) || (opMatch D A b && opMatch D B a))
       | _ => false)
  | _ => false

section Sound

variable {m : Mode} {w : LaneW} {D : Std.HashMap String ZBind} {rf : Std.HashMap String Iv}
  {E : Nat → String → BitVec w.bits} {σ0 : Fin 32 → BitVec 512}

theorem vBin_sound (hf : Facts m w D rf E) {n : String} {L : Nat} {bop : JasminBinOp}
    {ta tb : Term} (h : vBin w D n L bop ta tb = true) :
    (Term.lw L (.bin bop) ta tb).eval m σ0 (pack w E) = (Term.var n).eval m σ0 (pack w E) := by
  unfold vBin at h
  split at h
  · rename_i w' bop' d a b hd
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, hm⟩ := h
    subst h1 h2 h3 h4
    apply eval_eq_var
    intro k hk
    rw [lane_semLW _ _ _ (laneBits_pos _) hk.le512]
    have hs := hf.sat _ _ hd k hk rfl
    simp only [LOp.apply]
    rcases hm with ⟨ha, hb⟩ | ⟨⟨hc, ha⟩, hb⟩
    · rw [opMatch_lane hf ha hk, opMatch_lane hf hb hk, hs]
    · rw [opMatch_lane hf ha hk, opMatch_lane hf hb hk, hs, JasminBinOp.apply_comm bop' hc]
  · cases h

theorem narrow_lt {D : Std.HashMap String ZBind} {E : Nat → String → BitVec LaneW.q.bits}
    (hf : Facts m .q D rf E) {x : String} (h : narrow m D rf x = true) {k : Nat}
    (hk : Active m .q k) : (E k x).toNat < 2 ^ 32 := by
  unfold narrow at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    · rename_i i hi
      simp only [decide_eq_true_eq] at h
      obtain ⟨v, h1, h2, h3⟩ := hf.rng x i hi k hk
      have hv : v % 2 ^ LaneW.q.bits = v := Int.emod_eq_of_lt (by omega)
        (by simp only [LaneW.bits]; omega)
      rw [hv] at h3
      omega
    · cases h
  · split at h
    · rename_i x' v hd
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
      obtain ⟨rfl, hl⟩ := h
      have hs : E k x' = lane 64 (BitVec.ofNat 512 v) k := hf.sat _ _ hd k hk
      rw [hs]
      exact hl k (by have := (active_iff m .q k).1 hk; simpa [LaneW.bits] using this)
    · cases h

theorem vMulU_sound (hf : Facts m w D rf E) {n : String} {ta tb : Term}
    (h : vMulU w m D rf n ta tb = true) :
    (Term.lw 64 .muludq ta tb).eval m σ0 (pack w E) = (Term.var n).eval m σ0 (pack w E) := by
  unfold vMulU at h
  split at h
  · rename_i w' bop d a b hd
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, hna⟩, hnb⟩, hm⟩ := h
    subst h1 h2 h3 h4
    apply eval_eq_var
    intro k hk
    have hk' : 64 * k + 64 ≤ 512 := hk.le512
    show lane 64 _ k = _
    rw [lane_semLW _ _ _ (by norm_num) hk']
    have hs : E k d = E k a * E k b := hf.sat _ _ hd k hk rfl
    have ha := narrow_lt hf hna hk
    have hb := narrow_lt hf hnb hk
    simp only [LOp.apply]
    rcases hm with ⟨ma, mb⟩ | ⟨ma, mb⟩
    · rw [show lane 64 (ta.eval m σ0 (pack .q E)) k = E k a from opMatch_lane hf ma hk,
        show lane 64 (tb.eval m σ0 (pack .q E)) k = E k b from opMatch_lane hf mb hk, hs,
        ← RangeDomain.mul_eq_mul_setWidth32 _ _ ha hb]
      rfl
    · rw [show lane 64 (ta.eval m σ0 (pack .q E)) k = E k b from opMatch_lane hf ma hk,
        show lane 64 (tb.eval m σ0 (pack .q E)) k = E k a from opMatch_lane hf mb hk, hs,
        ← RangeDomain.mul_eq_mul_setWidth32 _ _ hb ha, BitVec.mul_comm]
      rfl
  · cases h

theorem vShi_sound (hf : Facts m w D rf E) {n : String} {L : Nat} {left : Bool} {imm : Nat}
    {ta : Term} (h : vShi w m D n L left imm ta = true) :
    (Term.shi L left imm ta).eval m σ0 (pack w E) = (Term.var n).eval m σ0 (pack w E) := by
  unfold vShi at h
  split at h
  · rename_i w' bop d a kc hd
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, ha⟩, hlt⟩, hc⟩ := h
    subst h1 h2 h3 h4
    split at hc
    · rename_i kc' v hkc
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hc
      obtain ⟨rfl, hl⟩ := hc
      apply eval_eq_var
      intro k hk
      rw [lane_semShImm _ _ _ (laneBits_pos _) hk.le512, opMatch_lane hf ha hk]
      have hs := hf.sat _ _ hd k hk rfl
      have hkv : E k kc' = lane _ (BitVec.ofNat 512 v) k := hf.sat _ _ hkc k hk
      have himm : (E k kc').toNat = imm := by rw [hkv]; exact hl k ((active_iff m _ k).1 hk)
      rw [hs]
      cases left <;>
        simp [JasminBinOp.apply, himm,
          CatCrypt.Crypto.SecureCompilation.VIR.shiftMask_of_lt hlt]
    · cases hc
  · rename_i w' l d a i hd
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, ha⟩ := h
    subst h1 h2 h3 h4 h5
    apply eval_eq_var
    intro k hk
    rw [lane_semShImm _ _ _ (laneBits_pos _) hk.le512, opMatch_lane hf ha hk]
    exact (hf.sat _ _ hd k hk rfl).symm
  · cases h

/-- The dwords of the even products `vpmuludq x, y` and of the odd products
    `vpmuludq (vmovshdup x), bo`, where `bo` holds the odd dwords of `y` in its even
    dwords. -/
theorem prod_lanes (x y bo : BitVec 512)
    (hbo : ∀ i, 64 * i + 64 ≤ m.act → lane 32 bo (2 * i) = lane 32 y (2 * i + 1))
    (i : Nat) (hi : 64 * i + 64 ≤ m.act) :
    lane 32 (wr m (semLW 64 .muludq x y)) (2 * i) = lane 32 x (2 * i) * lane 32 y (2 * i) ∧
    lane 32 (wr m (semLW 64 .muludq x y)) (2 * i + 1) =
      mulHiW (lane 32 x (2 * i)) (lane 32 y (2 * i)) ∧
    lane 32 (wr m (semLW 64 .muludq (wr m (semDup true x)) bo)) (2 * i) =
      lane 32 x (2 * i + 1) * lane 32 y (2 * i + 1) ∧
    lane 32 (wr m (semLW 64 .muludq (wr m (semDup true x)) bo)) (2 * i + 1) =
      mulHiW (lane 32 x (2 * i + 1)) (lane 32 y (2 * i + 1)) := by
  have h512 : 64 * i + 64 ≤ 512 := by rcases m.act_cases with h | h <;> omega
  have e0 : ∀ u v : BitVec 512, lane 64 (wr m (semLW 64 .muludq u v)) i =
      (lane 32 u (2 * i)).setWidth 64 * (lane 32 v (2 * i)).setWidth 64 := by
    intro u v
    rw [lane_wr _ hi, lane_semLW _ _ _ (by norm_num) h512]
    simp only [LOp.apply, lane32_even]
  have hdx : lane 32 (wr m (semDup true x)) (2 * i) = lane 32 x (2 * i + 1) := by
    rw [lane_wr _ (by omega), lane_semDup _ _ (by omega)]
    simp only [if_true]
    congr 1
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [lane32_even, e0, lo_mul_setWidth]
  · rw [lane32_odd, e0, hi_mul_setWidth]
  · rw [lane32_even, e0, lo_mul_setWidth, hdx, hbo i hi]
  · rw [lane32_odd, e0, hi_mul_setWidth, hdx, hbo i hi]

theorem mask5555 (i : Nat) (hi : i < 8) :
    (0x5555#16).getLsbD (2 * i) = true ∧ (0x5555#16).getLsbD (2 * i + 1) = false := by
  interval_cases i <;> decide

theorem maskAAAA (i : Nat) (hi : i < 8) :
    (0xAAAA#16).getLsbD (2 * i) = false ∧ (0xAAAA#16).getLsbD (2 * i + 1) = true := by
  interval_cases i <;> decide

theorem oddOK_lane {Bo B : Term} (h : oddOK Bo B = true) (i : Nat) (hi : 64 * i + 64 ≤ m.act) :
    lane 32 (Bo.eval m σ0 (pack w E)) (2 * i) = lane 32 (B.eval m σ0 (pack w E)) (2 * i + 1) := by
  unfold oddOK at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with rfl | ⟨rfl, hc⟩
  · simp only [Term.eval]
    rw [lane_wr _ (by omega), lane_semDup _ _ (by rcases m.act_cases with h | h <;> omega)]
    simp only [if_true]
    congr 1
    omega
  · split at hc
    · rename_i c
      simp only [decide_eq_true_eq] at hc
      simp only [Term.eval]
      rw [lane_wr _ (by omega), lane_wr _ (by omega)]
      conv_lhs => rw [← hc]
      rw [lane_semDup _ _ (by rcases m.act_cases with h | h <;> omega)]
      rw [if_pos rfl, show 2 * (2 * i / 2) + 1 = 2 * i + 1 by omega]
    · cases hc

theorem mulHiW_comm {L : Nat} (a b : BitVec L) : mulHiW a b = mulHiW b a := by
  simp [mulHiW, Nat.mul_comm]

theorem vMulhi_sound (hf : Facts m w D rf E) {n : String} {t : Term}
    (h : vMulhi w D n t = true) :
    t.eval m σ0 (pack w E) = (Term.var n).eval m σ0 (pack w E) := by
  unfold vMulhi at h
  split at h
  · rename_i k0 A B A' Bo
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, hodd⟩, hm⟩ := h
    subst h1 h2 A'
    split at hm
    · rename_i d a b hd
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hm
      obtain ⟨rfl, hm⟩ := hm
      apply eval_eq_var
      intro j hj
      have hj' : 32 * j + 32 ≤ m.act := hj
      have hj16 : j < 16 := by rcases m.act_cases with h | h <;> omega
      show lane 32 _ j = _
      simp only [Term.eval]
      have hs : E j d = mulHiW (E j a) (E j b) := hf.sat _ _ hd j hj
      rw [lane_semMerge _ _ _ hj16, hs]
      have hval : mulHiW (lane 32 (A.eval m σ0 (pack .d E)) j) (lane 32 (B.eval m σ0 (pack .d E)) j)
          = mulHiW (E j a) (E j b) := by
        rcases hm with ⟨ma, mb⟩ | ⟨ma, mb⟩
        · rw [show lane 32 (A.eval m σ0 (pack .d E)) j = E j a from opMatch_lane hf ma hj,
            show lane 32 (B.eval m σ0 (pack .d E)) j = E j b from opMatch_lane hf mb hj]
          rfl
        · rw [show lane 32 (A.eval m σ0 (pack .d E)) j = E j b from opMatch_lane hf ma hj,
            show lane 32 (B.eval m σ0 (pack .d E)) j = E j a from opMatch_lane hf mb hj,
            mulHiW_comm]
          rfl
      rw [← hval]
      obtain ⟨i, rfl | rfl⟩ : ∃ i, j = 2 * i ∨ j = 2 * i + 1 := ⟨j / 2, by omega⟩
      · have hi : 64 * i + 64 ≤ m.act := by rcases m.act_cases with h | h <;> omega
        have hp := prod_lanes (A.eval m σ0 (pack .d E)) (B.eval m σ0 (pack .d E))
          (Bo.eval m σ0 (pack .d E)) (fun i hi => oddOK_lane hodd i hi) i hi
        rw [(mask5555 i (by omega)).1, if_pos rfl, lane_semDup _ _ (by omega)]
        simp only [if_true, show 2 * (2 * i / 2) + 1 = 2 * i + 1 by omega]
        exact hp.2.1
      · have hi : 64 * i + 64 ≤ m.act := by rcases m.act_cases with h | h <;> omega
        have hp := prod_lanes (A.eval m σ0 (pack .d E)) (B.eval m σ0 (pack .d E))
          (Bo.eval m σ0 (pack .d E)) (fun i hi => oddOK_lane hodd i hi) i hi
        rw [(mask5555 i (by omega)).2]
        simp only [Bool.false_eq_true, if_false]
        exact hp.2.2.2
    · cases hm
  · cases h

theorem vMullo_sound (hf : Facts m w D rf E) {n : String} {t : Term}
    (h : vMullo w D n t = true) :
    t.eval m σ0 (pack w E) = (Term.var n).eval m σ0 (pack w E) := by
  unfold vMullo at h
  split at h
  · rename_i k0 A' Bo A B
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, hodd⟩, hm⟩ := h
    subst h1 h2 h3
    split at hm
    · rename_i w' bop d a b hd
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hm
      obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, hm⟩ := hm
      apply eval_eq_var
      intro j hj
      have hj' : 32 * j + 32 ≤ m.act := hj
      have hj16 : j < 16 := by rcases m.act_cases with h | h <;> omega
      show lane 32 _ j = _
      simp only [Term.eval]
      have hs : E j d = E j a * E j b := hf.sat _ _ hd j hj rfl
      rw [lane_semMerge _ _ _ hj16, hs]
      have hval : lane 32 (A'.eval m σ0 (pack .d E)) j * lane 32 (B.eval m σ0 (pack .d E)) j
          = E j a * E j b := by
        rcases hm with ⟨ma, mb⟩ | ⟨ma, mb⟩
        · rw [show lane 32 (A'.eval m σ0 (pack .d E)) j = E j a from opMatch_lane hf ma hj,
            show lane 32 (B.eval m σ0 (pack .d E)) j = E j b from opMatch_lane hf mb hj]
          rfl
        · rw [show lane 32 (A'.eval m σ0 (pack .d E)) j = E j b from opMatch_lane hf ma hj,
            show lane 32 (B.eval m σ0 (pack .d E)) j = E j a from opMatch_lane hf mb hj,
            BitVec.mul_comm]
          rfl
      rw [← hval]
      obtain ⟨i, rfl | rfl⟩ : ∃ i, j = 2 * i ∨ j = 2 * i + 1 := ⟨j / 2, by omega⟩
      · have hi : 64 * i + 64 ≤ m.act := by rcases m.act_cases with h | h <;> omega
        have hp := prod_lanes (A'.eval m σ0 (pack .d E)) (B.eval m σ0 (pack .d E))
          (Bo.eval m σ0 (pack .d E)) (fun i hi => oddOK_lane hodd i hi) i hi
        rw [(maskAAAA i (by omega)).1]
        simp only [Bool.false_eq_true, if_false]
        exact hp.1
      · have hi : 64 * i + 64 ≤ m.act := by rcases m.act_cases with h | h <;> omega
        have hp := prod_lanes (A'.eval m σ0 (pack .d E)) (B.eval m σ0 (pack .d E))
          (Bo.eval m σ0 (pack .d E)) (fun i hi => oddOK_lane hodd i hi) i hi
        rw [(maskAAAA i (by omega)).2, if_pos rfl, lane_semDup _ _ (by omega)]
        simp only [Bool.false_eq_true, if_false, show 2 * ((2 * i + 1) / 2) + 0 = 2 * i by omega]
        exact hp.2.2.1
    · cases hm
  · cases h

end Sound

/-! ### The Montgomery step in the even/odd products -/

/-- Binding `l` is the dword product of `A` and `B`, in either order. -/
def montLo (D : Std.HashMap String ZBind) (l : String) (A B : Term) : Bool :=
  match D[l]? with
  | some (.pack w' bop d x y) => decide (w' = .d) && decide (bop = .mul) && decide (d = l) &&
      ((opMatch D A x && opMatch D B y) || (opMatch D A y && opMatch D B x))
  | _ => false

/-- Binding `h` is the high multiply of `A` and `B`, in either order. -/
def montHi (D : Std.HashMap String ZBind) (h : String) (A B : Term) : Bool :=
  match D[h]? with
  | some (.mulhi d x y) => decide (d = h) &&
      ((opMatch D A x && opMatch D B y) || (opMatch D A y && opMatch D B x))
  | _ => false

/-- Binding `q` is `lo·Mu` for a binding `lo` that `montLo` recognises, in either order. -/
def montQ (D : Std.HashMap String ZBind) (q : String) (A B Mu : Term) : Bool :=
  match D[q]? with
  | some (.pack w' bop d x y) => decide (w' = .d) && decide (bop = .mul) && decide (d = q) &&
      ((montLo D x A B && opMatch D Mu y) || (montLo D y A B && opMatch D Mu x))
  | _ => false

/-- Binding `u` is `mulhi(q, P)` for a binding `q` that `montQ` recognises, in either
    order. -/
def montU (D : Std.HashMap String ZBind) (u : String) (A B Mu P : Term) : Bool :=
  match D[u]? with
  | some (.mulhi d x y) => decide (d = u) &&
      ((montQ D x A B Mu && opMatch D P y) || (montQ D y A B Mu && opMatch D P x))
  | _ => false

/-- The Montgomery step `VpackZmmLinearRender.montSubLines`: the even products `x` of `A`,
    `B` and the odd products (of `vmovshdup A` and the odd factor `Bo`), each reduced to
    `x - (x·c1)·c2` by `vpmuludq` and `vpsubq`, the even high words merged under `0x5555`
    into the odd ones, compute `n = h - u` for `h = mulhi(a, b)` and
    `u = mulhi((a·b)·mu, p)`, where the constants `c1`, `c2` (the values of `mu`, `p`) have
    equal dword pairs and multiply to one on every dword. -/
def vMontSub (w : LaneW) (D : Std.HashMap String ZBind) (n : String) (t : Term) : Bool :=
  match t with
  | .mdup true k0
      (.lw 64 (.bin .sub) (.lw 64 .muludq A B)
        (.lw 64 .muludq (.lw 64 .muludq PE (.cst c1)) (.cst c2)))
      (.lw 64 (.bin .sub) (.lw 64 .muludq (.dup true A') Bo)
        (.lw 64 .muludq (.lw 64 .muludq PO (.cst c1')) (.cst c2'))) =>
    decide (w = .d) && decide (k0 = 0x5555#16) && decide (A' = A) &&
      decide (PE = .lw 64 .muludq A B) && decide (PO = .lw 64 .muludq (.dup true A) Bo) &&
      decide (c1' = c1) && decide (c2' = c2) && oddOK Bo B &&
      oddOK (.cst c1) (.cst c1) && oddOK (.cst c2) (.cst c2) &&
      (List.range 16).all (fun j => lane 32 c1 j * lane 32 c2 j == 1) &&
      (match D[n]? with
       | some (.pack w' bop d h u) =>
         decide (w' = .d) && decide (bop = .sub) && decide (d = n) &&
           montHi D h A B && montU D u A B (.cst c1) (.cst c2)
       | _ => false)
  | _ => false

/-- The Montgomery difference as the high word of a 64-bit difference: for
    `mu·p = 1` the products `a·b` and `((a·b)·mu)·p` have equal low words, so the high
    word of their 64-bit difference is `mulhi(a, b) - mulhi((a·b)·mu, p)`. -/
theorem montSub_extract (a b μ p : BitVec 32) (h : μ * p = 1) :
    (a.setWidth 64 * b.setWidth 64 - (a * b * μ).setWidth 64 * p.setWidth 64).extractLsb' 32 32
      = mulHiW a b - mulHiW (a * b * μ) p := by
  rw [RangeDomain.extractLsb'_sub_of_setWidth_eq _ _ (by
      rw [lo_mul_setWidth, lo_mul_setWidth, BitVec.mul_assoc (a * b), h]; simp),
    hi_mul_setWidth, hi_mul_setWidth]

section Sound

variable {m : Mode} {D : Std.HashMap String ZBind} {rf : Std.HashMap String Iv}
  {σ0 : Fin 32 → BitVec 512}

/-- Qword `i` of a `vpmuludq` is the product of the zero-extended even dwords. -/
theorem muludq_lane64 (x y : BitVec 512) {i : Nat} (hi : 64 * i + 64 ≤ m.act) :
    lane 64 (wr m (semLW 64 .muludq x y)) i =
      (lane 32 x (2 * i)).setWidth 64 * (lane 32 y (2 * i)).setWidth 64 := by
  have h512 : 64 * i + 64 ≤ 512 := by rcases m.act_cases with h | h <;> omega
  rw [lane_wr _ hi, lane_semLW _ _ _ (by norm_num) h512]
  simp only [LOp.apply, lane32_even]

/-- Dword `2i` of a `vpmuludq` is the product of the even dwords. -/
theorem muludq_lo (x y : BitVec 512) {i : Nat} (hi : 64 * i + 64 ≤ m.act) :
    lane 32 (wr m (semLW 64 .muludq x y)) (2 * i) = lane 32 x (2 * i) * lane 32 y (2 * i) := by
  rw [lane32_even, muludq_lane64 _ _ hi, lo_mul_setWidth]

/-- Dword `2i+1` of the reduced product `x - (x·c1)·c2` of the products `x` of `a`, `b`:
    the Montgomery difference of the dwords `2i`, when `c1·c2 = 1` there. -/
theorem montSub_lane (a b c1 c2 : BitVec 512) {i : Nat} (hi : 64 * i + 64 ≤ m.act)
    (hinv : lane 32 c1 (2 * i) * lane 32 c2 (2 * i) = 1) :
    lane 32 (wr m (semLW 64 (.bin .sub) (wr m (semLW 64 .muludq a b))
      (wr m (semLW 64 .muludq (wr m (semLW 64 .muludq (wr m (semLW 64 .muludq a b)) c1))
        c2)))) (2 * i + 1) =
      mulHiW (lane 32 a (2 * i)) (lane 32 b (2 * i)) -
        mulHiW (lane 32 a (2 * i) * lane 32 b (2 * i) * lane 32 c1 (2 * i))
          (lane 32 c2 (2 * i)) := by
  have h512 : 64 * i + 64 ≤ 512 := by rcases m.act_cases with h | h <;> omega
  rw [lane32_odd, lane_wr _ hi, lane_semLW _ _ _ (by norm_num) h512]
  simp only [LOp.apply, JasminBinOp.apply]
  rw [muludq_lane64 _ _ hi, muludq_lane64 _ _ hi, muludq_lo _ _ hi, muludq_lo _ _ hi]
  exact montSub_extract _ _ _ _ hinv

variable {E : Nat → String → BitVec LaneW.d.bits}

theorem montLo_sound (hf : Facts m .d D rf E) {l : String} {A B : Term}
    (h : montLo D l A B = true) {j : Nat} (hj : Active m .d j) :
    E j l = lane 32 (A.eval m σ0 (pack .d E)) j * lane 32 (B.eval m σ0 (pack .d E)) j := by
  unfold montLo at h
  split at h
  · rename_i w' bop d x y hd
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, hm⟩ := h
    have hs : E j d = E j x * E j y := hf.sat _ _ hd j hj rfl
    rw [hs]
    rcases hm with ⟨ma, mb⟩ | ⟨ma, mb⟩
    · rw [show lane 32 (A.eval m σ0 (pack .d E)) j = E j x from opMatch_lane hf ma hj,
        show lane 32 (B.eval m σ0 (pack .d E)) j = E j y from opMatch_lane hf mb hj]
      rfl
    · rw [show lane 32 (A.eval m σ0 (pack .d E)) j = E j y from opMatch_lane hf ma hj,
        show lane 32 (B.eval m σ0 (pack .d E)) j = E j x from opMatch_lane hf mb hj]
      exact BitVec.mul_comm _ _
  · cases h

theorem montHi_sound (hf : Facts m .d D rf E) {h : String} {A B : Term}
    (hm : montHi D h A B = true) {j : Nat} (hj : Active m .d j) :
    E j h = mulHiW (lane 32 (A.eval m σ0 (pack .d E)) j)
      (lane 32 (B.eval m σ0 (pack .d E)) j) := by
  unfold montHi at hm
  split at hm
  · rename_i d x y hd
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hm
    obtain ⟨rfl, hm⟩ := hm
    have hs : E j d = mulHiW (E j x) (E j y) := hf.sat _ _ hd j hj
    rw [hs]
    rcases hm with ⟨ma, mb⟩ | ⟨ma, mb⟩
    · rw [show lane 32 (A.eval m σ0 (pack .d E)) j = E j x from opMatch_lane hf ma hj,
        show lane 32 (B.eval m σ0 (pack .d E)) j = E j y from opMatch_lane hf mb hj]
      rfl
    · rw [show lane 32 (A.eval m σ0 (pack .d E)) j = E j y from opMatch_lane hf ma hj,
        show lane 32 (B.eval m σ0 (pack .d E)) j = E j x from opMatch_lane hf mb hj]
      exact mulHiW_comm _ _
  · cases hm

theorem montQ_sound (hf : Facts m .d D rf E) {q : String} {A B Mu : Term}
    (h : montQ D q A B Mu = true) {j : Nat} (hj : Active m .d j) :
    E j q = lane 32 (A.eval m σ0 (pack .d E)) j * lane 32 (B.eval m σ0 (pack .d E)) j *
      lane 32 (Mu.eval m σ0 (pack .d E)) j := by
  unfold montQ at h
  split at h
  · rename_i w' bop d x y hd
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, hm⟩ := h
    have hs : E j d = E j x * E j y := hf.sat _ _ hd j hj rfl
    rw [hs]
    rcases hm with ⟨ml, mu⟩ | ⟨ml, mu⟩
    · rw [montLo_sound (σ0 := σ0) hf ml hj,
        show lane 32 (Mu.eval m σ0 (pack .d E)) j = E j y from opMatch_lane hf mu hj]
      rfl
    · rw [montLo_sound (σ0 := σ0) hf ml hj,
        show lane 32 (Mu.eval m σ0 (pack .d E)) j = E j x from opMatch_lane hf mu hj]
      exact BitVec.mul_comm _ _
  · cases h

theorem montU_sound (hf : Facts m .d D rf E) {u : String} {A B Mu P : Term}
    (h : montU D u A B Mu P = true) {j : Nat} (hj : Active m .d j) :
    E j u = mulHiW (lane 32 (A.eval m σ0 (pack .d E)) j * lane 32 (B.eval m σ0 (pack .d E)) j *
      lane 32 (Mu.eval m σ0 (pack .d E)) j) (lane 32 (P.eval m σ0 (pack .d E)) j) := by
  unfold montU at h
  split at h
  · rename_i d x y hd
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, hm⟩ := h
    have hs : E j d = mulHiW (E j x) (E j y) := hf.sat _ _ hd j hj
    rw [hs]
    rcases hm with ⟨mq, mp⟩ | ⟨mq, mp⟩
    · rw [montQ_sound (σ0 := σ0) hf mq hj,
        show lane 32 (P.eval m σ0 (pack .d E)) j = E j y from opMatch_lane hf mp hj]
      rfl
    · rw [montQ_sound (σ0 := σ0) hf mq hj,
        show lane 32 (P.eval m σ0 (pack .d E)) j = E j x from opMatch_lane hf mp hj]
      exact mulHiW_comm _ _
  · cases h

end Sound

section Sound

variable {m : Mode} {w : LaneW} {D : Std.HashMap String ZBind} {rf : Std.HashMap String Iv}
  {E : Nat → String → BitVec w.bits} {σ0 : Fin 32 → BitVec 512}

theorem vMontSub_sound (hf : Facts m w D rf E) {n : String} {t : Term}
    (h : vMontSub w D n t = true) :
    t.eval m σ0 (pack w E) = (Term.var n).eval m σ0 (pack w E) := by
  unfold vMontSub at h
  split at h
  · rename_i k0 A' B PE c1' c2' A Bo PO c1 c2
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
      beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hw, hk⟩, hA⟩, hPE⟩, hPO⟩, hc1⟩, hc2⟩, hodd⟩, hmu⟩, hp⟩, hinv⟩, hD⟩ := h
    subst hw hk hA hPE hPO hc1 hc2
    split at hD
    · rename_i w' bop d hh u hd
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hD
      obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, hhi⟩, hu⟩ := hD
      apply eval_eq_var
      intro j hj
      have hj' : 32 * j + 32 ≤ m.act := hj
      have hj16 : j < 16 := by rcases m.act_cases with h | h <;> omega
      have hs : E j d = E j hh - E j u := hf.sat _ _ hd j hj rfl
      have hwc : ∀ (c : BitVec 512) (k : Nat), 32 * k + 32 ≤ m.act →
          lane 32 (wr m c) k = lane 32 c k := fun c k hk => lane_wr c hk
      have hinv' : ∀ i, 64 * i + 64 ≤ m.act →
          lane 32 (wr m c1) (2 * i) * lane 32 (wr m c2) (2 * i) = 1 := fun i hi => by
        rw [hwc _ _ (by omega), hwc _ _ (by omega)]
        exact hinv _ (by rcases m.act_cases with h | h <;> omega)
      show lane 32 _ j = _
      rw [hs, montHi_sound (σ0 := σ0) hf hhi hj, montU_sound (σ0 := σ0) hf hu hj]
      simp only [Term.eval]
      rw [lane_semMerge _ _ _ hj16]
      obtain ⟨i, rfl | rfl⟩ : ∃ i, j = 2 * i ∨ j = 2 * i + 1 := ⟨j / 2, by omega⟩
      · have hi : 64 * i + 64 ≤ m.act := by rcases m.act_cases with h | h <;> omega
        rw [(mask5555 i (by omega)).1, if_pos rfl, lane_semDup _ _ (by omega)]
        simp only [if_true, show 2 * (2 * i / 2) + 1 = 2 * i + 1 by omega]
        exact montSub_lane _ _ _ _ hi (hinv' i hi)
      · have hi : 64 * i + 64 ≤ m.act := by rcases m.act_cases with h | h <;> omega
        rw [(mask5555 i (by omega)).2]
        simp only [Bool.false_eq_true, if_false]
        have hdx : lane 32 (wr m (semDup true (A.eval m σ0 (pack .d E)))) (2 * i) =
            lane 32 (A.eval m σ0 (pack .d E)) (2 * i + 1) := by
          rw [lane_wr _ (by omega), lane_semDup _ _ (by omega)]
          simp only [if_true]
          congr 1
          omega
        have hbo := oddOK_lane (σ0 := σ0) (E := E) hodd i hi
        have hc1p := oddOK_lane (σ0 := σ0) (E := E) hmu i hi
        have hc2p := oddOK_lane (σ0 := σ0) (E := E) hp i hi
        simp only [Term.eval] at hc1p hc2p
        rw [montSub_lane _ _ _ _ hi (hinv' i hi), hdx, hbo, hc1p, hc2p]
        rfl
    · cases hD
  · cases h

end Sound

/-- Binding `n` is `a bop b` at width `w`. -/
def isPack (D : Std.HashMap String ZBind) (n : String) (w : LaneW) (bop : JasminBinOp)
    (a b : String) : Bool :=
  match D[n]? with
  | some (.pack w' bop' d a' b') => decide (w' = w ∧ bop' = bop ∧ d = n ∧ a' = a ∧ b' = b)
  | _ => false

/-- The value of the constant binding `x`. -/
def constVal (D : Std.HashMap String ZBind) (x : String) : Option Nat :=
  match D[x]? with
  | some (.const x' v) => if x' = x then some v else none
  | _ => none

/-- Every active lane of width `w` of the constant `v` satisfies `p`. -/
def lanesAll (m : Mode) (w : LaneW) (v : Nat) (p : BitVec w.bits → Bool) : Bool :=
  (List.range (m.act / w.bits)).all (fun k => p (lane w.bits (BitVec.ofNat 512 v) k))

/-- `T` is `vpadd dn, cC` in either operand order. -/
def isAddDC (w : LaneW) (D : Std.HashMap String ZBind) (dn cC : String) (T : Term) : Bool :=
  match T with
  | .lw L (.bin .add) U V => decide (L = w.bits) &&
      ((opMatch D U dn && opMatch D V cC) || (opMatch D U cC && opMatch D V dn))
  | _ => false

/-- The unsigned minimum `lw L minu X Y` computes the conditional add
    `n = dn + ((0 - (dn >> (L-1))) & C)` named by the witness
    `[dn, tn, mm, cC, z, s, kk]` (`tn = mm & cC`, `mm = z - s`, `z = 0`,
    `s = dn >> kk`, `kk = L-1`), under the range fact on `dn` that
    `RangeDomain.condAdd_eq_umin` needs: either as `minu(x, dn)` for `dn = x - cC2` with
    `cC2 = cC` (witness tail `[x, cC2]`), or as `minu(dn, dn + cC)` (empty tail). -/
def vMinu (w : LaneW) (m : Mode) (D : Std.HashMap String ZBind) (rf : Std.HashMap String Iv)
    (n : String) (wit : List String) (t : Term) : Bool :=
  match t, wit with
  | .lw L .minu X Y, dn :: tn :: mm :: cC :: z :: s :: kk :: rest =>
    decide (L = w.bits) &&
    (isPack D n w .add dn tn || isPack D n w .add tn dn) &&
    (isPack D tn w .and mm cC || isPack D tn w .and cC mm) &&
    isPack D mm w .sub z s && isPack D s w .shr dn kk &&
    (match constVal D z, constVal D kk, constVal D cC, rf[dn]? with
     | some zv, some kv, some cv, some id =>
       decide (zv = 0) &&
       lanesAll m w kv (fun x => decide (x.toNat = w.bits - 1)) &&
       lanesAll m w cv (fun x => decide (x.toNat < 2 ^ (w.bits - 1) ∧ -(x.toNat : Int) ≤ id.1)) &&
       decide (id.2 < 2 ^ (w.bits - 1)) &&
       (match rest with
        | [x, cC2] => isPack D dn w .sub x cC2 && decide (constVal D cC2 = some cv) &&
            ((opMatch D X x && opMatch D Y dn) || (opMatch D X dn && opMatch D Y x))
        | [] => (opMatch D X dn && isAddDC w D dn cC Y) || (isAddDC w D dn cC X && opMatch D Y dn)
        | _ => false)
     | _, _, _, _ => false)
  | _, _ => false

section Sound

variable {m : Mode} {w : LaneW} {D : Std.HashMap String ZBind} {rf : Std.HashMap String Iv}
  {E : Nat → String → BitVec w.bits} {σ0 : Fin 32 → BitVec 512}

theorem isPack_sat (hf : Facts m w D rf E) {n a b : String} {bop : JasminBinOp}
    (h : isPack D n w bop a b = true) {k : Nat} (hk : Active m w k) :
    E k n = bop.apply (E k a) (E k b) := by
  unfold isPack at h
  split at h
  · rename_i w' bop' d a' b' hd
    simp only [decide_eq_true_eq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    exact hf.sat _ _ hd k hk rfl
  · cases h

theorem constVal_lane (hf : Facts m w D rf E) {x : String} {v : Nat}
    (h : constVal D x = some v) {k : Nat} (hk : Active m w k) :
    E k x = lane w.bits (BitVec.ofNat 512 v) k := by
  unfold constVal at h
  split at h
  · rename_i x' v' hd
    split at h
    · rename_i hx
      cases h
      subst hx
      exact hf.sat _ _ hd k hk
    · cases h
  · cases h

theorem lanesAll_spec {v : Nat} {p : BitVec w.bits → Bool} (h : lanesAll m w v p = true)
    {k : Nat} (hk : Active m w k) : p (lane w.bits (BitVec.ofNat 512 v) k) = true := by
  unfold lanesAll at h
  simp only [List.all_eq_true, List.mem_range] at h
  exact h k ((active_iff m w k).1 hk)

theorem isAddDC_lane (hf : Facts m w D rf E) {dn cC : String} {T : Term}
    (h : isAddDC w D dn cC T = true) {k : Nat} (hk : Active m w k) :
    lane w.bits (T.eval m σ0 (pack w E)) k = E k dn + E k cC := by
  unfold isAddDC at h
  split at h
  · rename_i L U V
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, hm⟩ := h
    simp only [Term.eval]
    rw [lane_wr _ hk, lane_semLW _ _ _ (laneBits_pos w) hk.le512]
    simp only [LOp.apply, JasminBinOp.apply]
    rcases hm with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · rw [opMatch_lane hf hu hk, opMatch_lane hf hv hk]
    · rw [opMatch_lane hf hu hk, opMatch_lane hf hv hk, BitVec.add_comm]
  · cases h

theorem lane_zero (L k : Nat) : lane L (BitVec.ofNat 512 0) k = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp [getLsbD_lane]

theorem vMinu_sound (hf : Facts m w D rf E) {n : String} {wit : List String} {t : Term}
    (h : vMinu w m D rf n wit t = true) :
    t.eval m σ0 (pack w E) = (Term.var n).eval m σ0 (pack w E) := by
  unfold vMinu at h
  split at h
  · rename_i L X Y dn tn mm cC z s kk rest
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨hL, hn⟩, htn⟩, hmm⟩, hs⟩, hc⟩ := h
    subst hL
    split at hc
    · rename_i zv kv cv id hz hkk hcC hid
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨hz0, hkl⟩, hcl⟩, hhi⟩, hform⟩ := hc
      subst hz0
      apply eval_eq_var
      intro k hk
      have hw : 0 < w.bits := laneBits_pos w
      have hcond : E k n = condAdd (E k dn) (E k cC) := by
        have hzv : E k z = 0 := by rw [constVal_lane hf hz hk, lane_zero]
        have hkv : (E k kk).toNat = w.bits - 1 := by
          have := lanesAll_spec hkl hk
          simp only [decide_eq_true_eq] at this
          rw [constVal_lane hf hkk hk]; exact this
        have hsv : E k s = E k dn >>> (w.bits - 1) := by
          rw [isPack_sat hf hs hk]
          simp [JasminBinOp.apply, hkv,
            CatCrypt.Crypto.SecureCompilation.VIR.shiftMask_of_lt
              (show w.bits - 1 < w.bits by omega)]
        have hmv : E k mm = 0 - (E k dn >>> (w.bits - 1)) := by
          rw [isPack_sat hf hmm hk, hzv, hsv]; rfl
        have htv : E k tn = (0 - (E k dn >>> (w.bits - 1))) &&& E k cC := by
          rcases htn with h' | h'
          · rw [isPack_sat hf h' hk, hmv]; rfl
          · rw [isPack_sat hf h' hk, hmv]; simp [JasminBinOp.apply, BitVec.and_comm]
        unfold condAdd
        rcases hn with h' | h'
        · rw [isPack_sat hf h' hk, htv]; rfl
        · rw [isPack_sat hf h' hk, htv]; simp [JasminBinOp.apply, BitVec.add_comm]
      have hC := lanesAll_spec hcl hk
      simp only [decide_eq_true_eq] at hC
      rw [← constVal_lane hf hcC hk] at hC
      obtain ⟨hC1, hC2⟩ := hC
      have hd : id.Mem w.bits (E k dn) := hf.rng _ _ hid k hk
      rw [hcond, lane_semLW _ _ _ hw hk.le512]
      simp only [LOp.apply]
      split at hform
      · rename_i x cC2
        simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hform
        obtain ⟨⟨hdn, hc2⟩, hm⟩ := hform
        have hdv : E k dn = E k x - E k cC := by
          rw [isPack_sat hf hdn hk, constVal_lane hf hc2 hk, constVal_lane hf hcC hk]; rfl
        rw [hdv] at hd ⊢
        rw [RangeDomain.condAdd_sub_eq_umin hw hd hC1 hC2 hhi]
        rcases hm with ⟨hx, hy⟩ | ⟨hx, hy⟩
        · rw [opMatch_lane hf hx hk, opMatch_lane hf hy hk, hdv]
        · rw [opMatch_lane hf hx hk, opMatch_lane hf hy hk, hdv, RangeDomain.umin_comm]
      · simp only [Bool.or_eq_true, Bool.and_eq_true] at hform
        rw [RangeDomain.condAdd_eq_umin hw hd hC1 hC2 hhi]
        rcases hform with ⟨hx, hy⟩ | ⟨hx, hy⟩
        · rw [opMatch_lane hf hx hk, isAddDC_lane hf hy hk]
        · rw [isAddDC_lane hf hx hk, opMatch_lane hf hy hk, RangeDomain.umin_comm]
      · cases hform
    · cases hc
  · cases h

end Sound

/-! ## 7. Recognition: candidates and the normaliser -/

/-- The checked recogniser: binding `n` (with witness `wit` for the conditional add)
    has the value of `t`. -/
def verify (w : LaneW) (m : Mode) (D : Std.HashMap String ZBind) (rf : Std.HashMap String Iv)
    (n : String) (wit : List String) (t : Term) : Bool :=
  match t with
  | .lw L (.bin bop) a b => vBin w D n L bop a b
  | .lw 64 .muludq a b => vMulU w m D rf n a b
  | .shi L l i a => vShi w m D n L l i a
  | _ => vMinu w m D rf n wit t || vMulhi w D n t || vMullo w D n t || vMontSub w D n t

theorem verify_sound {m : Mode} {w : LaneW} {D : Std.HashMap String ZBind}
    {rf : Std.HashMap String Iv} {E : Nat → String → BitVec w.bits}
    {σ0 : Fin 32 → BitVec 512} (hf : Facts m w D rf E) {n : String} {wit : List String}
    {t : Term} (h : verify w m D rf n wit t = true) :
    t.eval m σ0 (pack w E) = (Term.var n).eval m σ0 (pack w E) := by
  unfold verify at h
  split at h
  · exact vBin_sound hf h
  · exact vMulU_sound hf h
  · exact vShi_sound hf h
  · simp only [Bool.or_eq_true] at h
    rcases h with ((h | h) | h) | h
    · exact vMinu_sound hf h
    · exact vMulhi_sound hf h
    · exact vMullo_sound hf h
    · exact vMontSub_sound hf h

/-- A tag per operation, for the candidate keys. -/
def bopTag : JasminBinOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .and => "and" | .or => "or"
  | .xor => "xor" | .shl => "shl" | .shr => "shr" | .andn => "andn"

/-- The key of a name as an operand: its value when it is a constant binding. -/
def leafKey (D : Std.HashMap String ZBind) (a : String) : String :=
  match constVal D a with
  | some v => "c" ++ toString (BitVec.ofNat 512 v).toNat
  | none => "v" ++ a

/-- The key of an operand term: a name, a constant, or the sum of two of them. -/
def termKey : Term → Option String
  | .var x => some ("v" ++ x)
  | .cst c => some ("c" ++ toString c.toNat)
  | .lw _ (.bin .add) a b => do
    let ka ← termKey a
    let kb ← termKey b
    some ("(+" ++ ka ++ "," ++ kb ++ ")")
  | _ => none

/-- The candidate keys of a term. -/
def candKeys (t : Term) : List String :=
  let k2 (tag : String) (a b : Term) : List String :=
    match termKey a, termKey b with
    | some ka, some kb => [tag ++ "|" ++ ka ++ "|" ++ kb]
    | _, _ => []
  match t with
  | .lw _ (.bin bop) a b => k2 ("b" ++ bopTag bop) a b
  | .lw _ .muludq a b => k2 "u" a b
  | .lw _ .minu a b => k2 "m" a b
  | .shi _ l i a =>
    match termKey a with
    | some ka => ["s|" ++ toString l ++ "|" ++ toString i ++ "|" ++ ka]
    | none => []
  | .mdup true _ (.lw _ (.bin .sub) (.lw _ .muludq a b)
      (.lw _ .muludq (.lw _ .muludq _ mu) p)) _ =>
    match termKey a, termKey b, termKey mu, termKey p with
    | some ka, some kb, some km, some kp => ["M|" ++ ka ++ "|" ++ kb ++ "|" ++ km ++ "|" ++ kp]
    | _, _, _, _ => []
  | .mdup true _ (.lw _ .muludq a b) _ => k2 "h" a b
  | .mdup false _ _ (.lw _ .muludq a b) => k2 "l" a b
  | _ => []

/-- The candidate keys of the conditional add `n = a + b` and its witnesses, when it has
    the shape `vMinu` checks. -/
def minuKeys (w : LaneW) (D : Std.HashMap String ZBind) (n a b : String) :
    List (String × (String × List String)) :=
  [(a, b), (b, a)].flatMap fun (dn, tn) =>
    match D[tn]? with
    | some (.pack w1 .and _ t1 t2) =>
      let (mm, cC) := if (constVal D t2).isSome then (t1, t2) else (t2, t1)
      match D[mm]? with
      | some (.pack _ .sub _ z s) =>
        match D[s]? with
        | some (.pack _ .shr _ _ kk) =>
          if w1 = w then
            let base := [dn, tn, mm, cC, z, s, kk]
            let kd := leafKey D dn
            let kc := leafKey D cC
            let u1 := "(+" ++ kd ++ "," ++ kc ++ ")"
            let u2 := "(+" ++ kc ++ "," ++ kd ++ ")"
            let uForm := [u1, u2].flatMap fun u =>
              [("m|" ++ kd ++ "|" ++ u, (n, base)), ("m|" ++ u ++ "|" ++ kd, (n, base))]
            let direct := match D[dn]? with
              | some (.pack _ .sub _ x cC2) =>
                let kx := leafKey D x
                [("m|" ++ kx ++ "|" ++ kd, (n, base ++ [x, cC2])),
                  ("m|" ++ kd ++ "|" ++ kx, (n, base ++ [x, cC2]))]
              | _ => []
            uForm ++ direct
          else []
        | _ => []
      | _ => []
    | _ => []

/-- The candidate keys of the difference `n = h - u` when `u` has the shape `vMontSub`
    checks, `u = mulhi((x·y)·mu, p)`: one key per order of `x`, `y`. -/
def montKeys (D : Std.HashMap String ZBind) (n u : String) :
    List (String × (String × List String)) :=
  match D[u]? with
  | some (.mulhi _ u1 u2) =>
    [(u1, u2), (u2, u1)].flatMap fun (q, p) =>
      match D[q]? with
      | some (.pack _ .mul _ q1 q2) =>
        [(q1, q2), (q2, q1)].flatMap fun (l, mu) =>
          match D[l]? with
          | some (.pack _ .mul _ x y) =>
            let kx := leafKey D x
            let ky := leafKey D y
            let tail := "|" ++ leafKey D mu ++ "|" ++ leafKey D p
            [("M|" ++ kx ++ "|" ++ ky ++ tail, (n, [])), ("M|" ++ ky ++ "|" ++ kx ++ tail, (n, []))]
          | _ => []
      | _ => []
  | _ => []

/-- The candidate keys of one binding at lane width `w`. -/
def bindKeys (w : LaneW) (m : Mode) (D : Std.HashMap String ZBind) (b : ZBind) :
    List (String × (String × List String)) :=
  match b with
  | .pack w' bop d a b2 =>
    if w' = w then
      let ka := leafKey D a
      let kb := leafKey D b2
      let one (k : String) := (k, (d, ([] : List String)))
      let binK := one ("b" ++ bopTag bop ++ "|" ++ ka ++ "|" ++ kb) ::
        (if bopCommutes bop then [one ("b" ++ bopTag bop ++ "|" ++ kb ++ "|" ++ ka)] else [])
      let mulK := if bop = .mul then
          (if w = .q then [one ("u|" ++ ka ++ "|" ++ kb), one ("u|" ++ kb ++ "|" ++ ka)]
           else [one ("l|" ++ ka ++ "|" ++ kb), one ("l|" ++ kb ++ "|" ++ ka)])
        else []
      let shK := match bop, constVal D b2 with
        | .shl, some v =>
          [one ("s|true|" ++ toString (lane w.bits (BitVec.ofNat 512 v) 0).toNat ++ "|" ++ ka)]
        | .shr, some v =>
          [one ("s|false|" ++ toString (lane w.bits (BitVec.ofNat 512 v) 0).toNat ++ "|" ++ ka)]
        | _, _ => []
      let minK := if bop = .add then minuKeys w D d a b2 else []
      let montK := if bop = .sub ∧ w = .d then montKeys D d b2 else []
      let _ := m
      binK ++ mulK ++ shK ++ minK ++ montK
    else []
  | .mulhi d a b2 =>
    let ka := leafKey D a
    let kb := leafKey D b2
    [("h|" ++ ka ++ "|" ++ kb, (d, [])), ("h|" ++ kb ++ "|" ++ ka, (d, []))]
  | .shi w' l d a i =>
    if w' = w then [("s|" ++ toString l ++ "|" ++ toString i ++ "|" ++ leafKey D a, (d, []))]
    else []
  | _ => []

/-- The candidate table of a binding list: each key names the first binding that has it. -/
def keyMap (w : LaneW) (m : Mode) (D : Std.HashMap String ZBind) (bs : Array ZBind) :
    Std.HashMap String (String × List String) :=
  bs.foldl (fun km b => (bindKeys w m D b).foldl (fun km (k, v) => km.insertIfNew k v) km) {}

/-- Replace a term by the name of a binding it is checked to compute. -/
def norm (w : LaneW) (m : Mode) (D : Std.HashMap String ZBind) (rf : Std.HashMap String Iv)
    (km : Std.HashMap String (String × List String)) (t : Term) : Term :=
  match (candKeys t).findSome? (fun k =>
      match km[k]? with
      | some (n, wit) => if verify w m D rf n wit t then some n else none
      | none => none) with
  | some n => .var n
  | none => t

theorem norm_sound {m : Mode} {w : LaneW} {D : Std.HashMap String ZBind}
    {rf : Std.HashMap String Iv} {E : Nat → String → BitVec w.bits}
    {σ0 : Fin 32 → BitVec 512} (hf : Facts m w D rf E)
    (km : Std.HashMap String (String × List String)) (t : Term) :
    (norm w m D rf km t).eval m σ0 (pack w E) = t.eval m σ0 (pack w E) := by
  unfold norm
  split
  · rename_i n hn
    obtain ⟨k, -, hk⟩ := List.exists_of_findSome?_eq_some hn
    split at hk
    · rename_i n' wit _
      split at hk
      · rename_i hv
        cases hk
        exact (verify_sound hf hv).symm
      · cases hk
    · cases hk
  · rfl

/-! ## 8. The parser of the renderer's text -/

/-- `s` without the prefix `p`. -/
def stripPre (p s : String) : Option String :=
  if p.toList.isPrefixOf s.toList then some (String.ofList (s.toList.drop p.length))
  else none

/-- `s` without the suffix `x`. -/
def stripSuf (x s : String) : Option String :=
  if x.toList.reverse.isPrefixOf s.toList.reverse then
    some (String.ofList (s.toList.take (s.length - x.length)))
  else none

/-- A decimal numeral in its canonical spelling. -/
def parseNat (s : String) : Option Nat :=
  match s.toNat? with
  | some n => if toString n = s then some n else none
  | none => none

/-- A vector register of mode `m`: `%zmmN` or `%ymmN`, `N < 32`. -/
def parseReg (m : Mode) (s : String) : Option (Fin 32) := do
  let r ← stripPre (match m with | .zmm => "%zmm" | .ymm => "%ymm") s
  let n ← parseNat r
  if h : n < 32 then some ⟨n, h⟩ else none

/-- A destination register with an optional merge mask `{%kN}`, `1 ≤ N ≤ 7`. -/
def parseRegMask (m : Mode) (s : String) : Option (Fin 32 × Option (Fin 8)) :=
  match s.splitOn "{" with
  | [r] => (parseReg m r).map (·, none)
  | [r, k] => do
    let d ← parseReg m r
    let kn ← (stripPre "%k" k).bind (stripSuf "}") |>.bind parseNat
    if h : 1 ≤ kn ∧ kn < 8 then some (d, some ⟨kn, h.2⟩) else none
  | _ => none

/-- A data label operand `lbl(%rip)`. -/
def parseLbl (s : String) : Option String :=
  match stripSuf "(%rip)" s with
  | some l => if l.isEmpty || l.contains '(' || l.contains '{' then none else some l
  | none => none

/-- The embedded-broadcast count of a width-`L` operation in mode `m`. -/
def bcastCount (m : Mode) (L : Nat) : Nat := m.act / L

/-- The second source of a lane-wise instruction: a register, `lbl(%rip)`, or the
    broadcast `lbl(%rip){1toK}`. -/
def parseSrc2 (m : Mode) (L : Nat) (s : String) : Option Opnd :=
  match parseReg m s with
  | some r => some (.reg r)
  | none =>
    match parseLbl s with
    | some l => some (.mem (.full l))
    | none => do
      let body ← stripSuf ("{1to" ++ toString (bcastCount m L) ++ "}") s
      let l ← parseLbl body
      if L = 64 then some (.mem (.bq l)) else if L = 32 then some (.mem (.bd l)) else none

/-- The lane-wise mnemonics: lane width and operation. -/
def opTable : String → Option (Nat × LOp)
  | "vpaddq" => some (64, .bin .add) | "vpsubq" => some (64, .bin .sub)
  | "vpmullq" => some (64, .bin .mul) | "vpmuludq" => some (64, .muludq)
  | "vpandq" => some (64, .bin .and) | "vporq" => some (64, .bin .or)
  | "vpxorq" => some (64, .bin .xor) | "vpandnq" => some (64, .bin .andn)
  | "vpsllvq" => some (64, .bin .shl) | "vpsrlvq" => some (64, .bin .shr)
  | "vpminuq" => some (64, .minu)
  | "vpaddd" => some (32, .bin .add) | "vpsubd" => some (32, .bin .sub)
  | "vpmulld" => some (32, .bin .mul)
  | "vpandd" => some (32, .bin .and) | "vpord" => some (32, .bin .or)
  | "vpxord" => some (32, .bin .xor) | "vpandnd" => some (32, .bin .andn)
  | "vpsllvd" => some (32, .bin .shl) | "vpsrlvd" => some (32, .bin .shr)
  | "vpminud" => some (32, .minu)
  | _ => none

/-- The immediate-count shift mnemonics: lane width and direction (left). -/
def shiftTable : String → Option (Nat × Bool)
  | "vpsllq" => some (64, true) | "vpsrlq" => some (64, false)
  | "vpslld" => some (32, true) | "vpsrld" => some (32, false)
  | _ => none

/-- The instruction of mnemonic `mn` with operands `ops`. -/
def parseOps (m : Mode) (mn : String) (ops : List String) : Option Instr :=
  match mn, ops with
  | "vmovdqu64", [a, b] =>
    match (stripSuf "(%rsi)" a).bind parseNat, parseReg m b with
    | some off, some d => some (.ldIn off d)
    | _, _ =>
      match parseLbl a, parseReg m b with
      | some l, some d => some (.ldC (.full l) d)
      | _, _ =>
        match parseReg m a, (stripSuf "(%rdi)" b).bind parseNat with
        | some r, some off => some (.st r off)
        | _, _ =>
          match (stripSuf "(%rsp)" a).bind parseNat, parseReg m b with
          | some off, some d => some (.ldS off d)
          | _, _ =>
            match parseReg m a, (stripSuf "(%rsp)" b).bind parseNat with
            | some r, some off => some (.stS r off)
            | _, _ => none
  | "subq", [a, "%rsp"] => do some (.spSub (← (stripPre "$" a).bind parseNat))
  | "addq", [a, "%rsp"] => do some (.spAdd (← (stripPre "$" a).bind parseNat))
  | "vpbroadcastq", [a, b] => do some (.ldC (.bq (← parseLbl a)) (← parseReg m b))
  | "vpbroadcastd", [a, b] => do some (.ldC (.bd (← parseLbl a)) (← parseReg m b))
  | "vmovdqa64", [a, b] => do some (.mova (← parseReg m a) (← parseReg m b))
  | "vmovshdup", [a, b] => do
    let (d, k) ← parseRegMask m b
    some (.dup true (← parseReg m a) d k)
  | "vmovsldup", [a, b] => do
    let (d, k) ← parseRegMask m b
    some (.dup false (← parseReg m a) d k)
  | "movl", [a, "%eax"] => do
    let imm ← (stripPre "$" a).bind parseNat
    if imm < 2 ^ 32 then some (.movEax (BitVec.ofNat 32 imm)) else none
  | "kmovw", ["%eax", k] => do
    let kn ← (stripPre "%k" k).bind parseNat
    if h : 1 ≤ kn ∧ kn < 8 then some (.kmov ⟨kn, h.2⟩) else none
  | "vpermd", [a, b, c] => do
    some (.perm (← parseReg m a) (← parseReg m b) (← parseReg m c))
  | "vpblendmd", [a, b, c] => do
    let (d, k) ← parseRegMask m c
    some (.blend (← k) (← parseReg m a) (← parseReg m b) d)
  | "vprolq", [a, b, c] => do
    some (.rol 64 (← (stripPre "$" a).bind parseNat) (← parseReg m b) (← parseReg m c))
  | "vprold", [a, b, c] => do
    some (.rol 32 (← (stripPre "$" a).bind parseNat) (← parseReg m b) (← parseReg m c))
  | "vpternlogq", [i, a, b, c] => do
    let imm ← (stripPre "$" i).bind parseNat
    if imm < 256 then
      some (.tern 64 (BitVec.ofNat 8 imm) (← parseReg m a) (← parseReg m b) (← parseReg m c))
    else none
  | "vpternlogd", [i, a, b, c] => do
    let imm ← (stripPre "$" i).bind parseNat
    if imm < 256 then
      some (.tern 32 (BitVec.ofNat 8 imm) (← parseReg m a) (← parseReg m b) (← parseReg m c))
    else none
  | mn, [a, b, c] =>
    match shiftTable mn with
    | some (L, left) => do
      let imm ← (stripPre "$" a).bind parseNat
      if imm < L then some (.shi L left imm (← parseReg m b) (← parseReg m c)) else none
    | none => do
      let (L, o) ← opTable mn
      some (.op L o (← parseSrc2 m L a) (← parseReg m b) (← parseReg m c))
  | _, _ => none

/-- One instruction line `\tmnemonic op, op, …`. -/
def parseInstr (m : Mode) (line : String) : Option Instr := do
  let body ← stripPre "\t" line
  let cs := body.toList
  let mn := cs.takeWhile (· ≠ ' ')
  let rest := cs.drop (mn.length + 1)
  if cs.length ≤ mn.length then none else
  parseOps m (String.ofList mn) ((String.ofList rest).splitOn ", ")

/-- The instruction lines up to the epilogue `vzeroupper; ret`. -/
def parseBody (m : Mode) : List String → List Instr →
    Except String (List Instr × List String)
  | "\tvzeroupper" :: "\tret" :: rest, acc => .ok (acc.reverse, rest)
  | l :: rest, acc =>
    match parseInstr m l with
    | some i => parseBody m rest (i :: acc)
    | none => .error ("unrecognised line: " ++ l)
  | [], _ => .error "missing epilogue"

/-- The data table being read: the finished entries, the open entry, and whether a
    label is expected next. -/
structure DataSt where
  ro : Std.HashMap String (Array (BitVec 64)) := {}
  cur : Option (String × Array (BitVec 64)) := none
  expectLabel : Bool := false

/-- Close the open entry, which must hold a quadword. -/
def DataSt.flush (st : DataSt) : Except String DataSt :=
  match st.cur with
  | none => .ok st
  | some (l, q) =>
    if q.isEmpty then .error ("empty data entry " ++ l)
    else .ok { st with ro := st.ro.insert l q, cur := none }

/-- The `.rodata` lines: entries `.p2align 3|6`, `lbl:`, `.quad n`…, then the
    `.note.GNU-stack` section line and the final empty line. Labels are `.L…` and
    distinct. -/
def parseData : List String → DataSt → Except String (Std.HashMap String (Array (BitVec 64)))
  | ["\t.section .note.GNU-stack,\"\",@progbits", ""], st =>
    if st.expectLabel then .error "dangling alignment" else (st.flush).map (·.ro)
  | l :: rest, st =>
    if l = "\t.p2align 3" ∨ l = "\t.p2align 6" then
      if st.expectLabel then .error "two alignments" else
      match st.flush with
      | .ok st' => parseData rest { st' with expectLabel := true }
      | .error e => .error e
    else if st.expectLabel then
      match stripSuf ":" l with
      | some lbl =>
        if (stripPre ".L" lbl).isSome && !st.ro.contains lbl then
          parseData rest { st with cur := some (lbl, #[]), expectLabel := false }
        else .error ("bad label " ++ l)
      | none => .error ("expected a label: " ++ l)
    else
      match st.cur, (stripPre "\t.quad " l).bind parseNat with
      | some (lbl, q), some n =>
        if n < 2 ^ 64 then parseData rest { st with cur := some (lbl, q.push (BitVec.ofNat 64 n)) }
        else .error ("quad out of range: " ++ l)
      | _, _ => .error ("unrecognised data line: " ++ l)
  | [], _ => .error "missing section trailer"

/-- The renderer's text: the header of `sym`, the instructions, the epilogue, the
    `.size` and `.rodata` lines and the data. Anything else is rejected. -/
def parse (m : Mode) (text : String) :
    Except String (List Instr × Std.HashMap String (Array (BitVec 64))) :=
  match text.splitOn "\n" with
  | l0 :: l1 :: l2 :: l3 :: rest =>
    match stripPre "\t.globl " l1 with
    | none => .error "missing .globl"
    | some sym =>
      if l0 = "\t.text" ∧ l2 = "\t.type " ++ sym ++ ", @function" ∧ l3 = sym ++ ":" then
        match parseBody m rest [] with
        | .ok (prog, l4 :: l5 :: data) =>
          if l4 = "\t.size " ++ sym ++ ", .-" ++ sym ∧ l5 = "\t.section .rodata" then
            (parseData data {}).map (prog, ·)
          else .error "missing .size or .rodata"
        | .ok _ => .error "missing trailer"
        | .error e => .error e
      else .error "bad header"
  | _ => .error "short text"

/-! ## 9. Value numbering

The binding list has no common-subexpression elimination, so several bindings may
compute one value. The candidate table names each register by one binding, so the
validator compares names up to value numbering: `buildRep` maps every binding to the
first binding with the same operation on the same representatives (a constant to the
first constant of its value), `repCheck` checks the table against the bindings, and
`renameB` makes every binding read representatives. `repCheck_sound`: on a lane
satisfying every binding, a name and its representative have one value. -/

/-- The representative table: name `n` ↦ `(r, i)`, the representative `r` of `n` and the
    position `i` of `n` in the binding list. -/
abbrev RepMap := Std.HashMap String (String × Nat)

/-- The representative of `n`: its table entry, or `n` itself. -/
def repOf (R : RepMap) (n : String) : String :=
  match R[n]? with
  | some (r, _) => r
  | none => n

/-- The value-numbering key of a binding at lane width `w` over the representatives `R`:
    the operation and the representatives of its operands (ordered for a commuting
    operation), or the value of a constant. -/
def valKey (w : LaneW) (R : RepMap) : ZBind → Option String
  | .const _ v => some ("c" ++ toString v)
  | .pack w' bop _ a b =>
    if w' = w then
      let x := repOf R a
      let y := repOf R b
      let (x, y) := if bopCommutes bop && decide (y < x) then (y, x) else (x, y)
      some ("p" ++ bopTag bop ++ "|" ++ x ++ "|" ++ y)
    else none
  | .mulhi _ a b =>
    let x := repOf R a
    let y := repOf R b
    let (x, y) := if decide (y < x) then (y, x) else (x, y)
    some ("h|" ++ x ++ "|" ++ y)
  | _ => none

/-- Value numbering of `bs` at lane width `w`: binding `i` is mapped to the first binding
    with its key, or to itself when it is the first. -/
def buildRep (w : LaneW) (bs : Array ZBind) : RepMap :=
  (bs.foldl (fun (acc : RepMap × Std.HashMap String String × Nat) b =>
    let (R, T, i) := acc
    match valKey w R b with
    | some k =>
      match T[k]? with
      | some r => (R.insert b.dst (r, i), T, i + 1)
      | none => (R.insert b.dst (b.dst, i), T.insert k b.dst, i + 1)
    | none => (R.insert b.dst (b.dst, i), T, i + 1)) ({}, {}, 0)).1

/-- Name `x` has no table entry, or one of position below `i`. -/
def below (R : RepMap) (i : Nat) (x : String) : Bool :=
  match R[x]? with
  | some (_, j) => decide (j < i)
  | none => true

/-- The operand pairs `(a, b)` and `(c, e)` have equal representatives, exchanged when
    `comm` allows. -/
def sameOps (R : RepMap) (comm : Bool) (a b c e : String) : Bool :=
  (repOf R a == repOf R c && repOf R b == repOf R e) ||
    (comm && repOf R a == repOf R e && repOf R b == repOf R c)

/-- Binding `b` of `n` and binding `b'` of `r` compute one value: they are constants of
    one value, or the same operation at width `w` on operands with equal representatives
    and positions below `i`. -/
def sameVal (w : LaneW) (R : RepMap) (i : Nat) (n r : String) : ZBind → ZBind → Bool
  | .const d v, .const d' v' => d == n && d' == r && v == v'
  | .pack w1 bop d a b, .pack w2 bop' d' c e =>
    d == n && d' == r && decide (w1 = w) && decide (w2 = w) && decide (bop' = bop) &&
      below R i a && below R i b && below R i c && below R i e &&
      sameOps R (bopCommutes bop) a b c e
  | .mulhi d a b, .mulhi d' c e =>
    d == n && d' == r && below R i a && below R i b && below R i c && below R i e &&
      sameOps R true a b c e
  | _, _ => false

/-- The table entry `n ↦ (r, i)` is justified by the bindings `D`. -/
def repEntryOK (w : LaneW) (D : Std.HashMap String ZBind) (R : RepMap)
    (e : String × (String × Nat)) : Bool :=
  e.1 == e.2.1 ||
    match D[e.1]?, D[e.2.1]? with
    | some b, some b' => sameVal w R e.2.2 e.1 e.2.1 b b'
    | _, _ => false

/-- Every entry of the representative table is justified by the bindings `D`. -/
def repCheck (w : LaneW) (D : Std.HashMap String ZBind) (R : RepMap) : Bool :=
  R.toList.all (repEntryOK w D R)

/-- The representative table `validate` uses: the value numbering of `bs` when `repCheck`
    justifies it, and the empty table otherwise. -/
def repTable (w : LaneW) (bs : Array ZBind) : RepMap :=
  let R := buildRep w bs
  if repCheck w (mkDefs bs) R then R else {}

/-- The binding `b` with its operands replaced by their representatives. -/
def renameB (R : RepMap) : ZBind → ZBind
  | .pack w bop d a b => .pack w bop d (repOf R a) (repOf R b)
  | .mulhi d a b => .mulhi d (repOf R a) (repOf R b)
  | b => b

section Rep

variable {w : LaneW} {D : Std.HashMap String ZBind} {R : RepMap}
  {E : Nat → String → BitVec w.bits} {k : Nat}

theorem sameOps_val {comm : Bool} {a b c e : String}
    (ha : E k a = E k (repOf R a)) (hb : E k b = E k (repOf R b))
    (hc : E k c = E k (repOf R c)) (he : E k e = E k (repOf R e))
    (h : sameOps R comm a b c e = true) :
    (E k a = E k c ∧ E k b = E k e) ∨ (comm = true ∧ E k a = E k e ∧ E k b = E k c) := by
  unfold sameOps at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨h1, h2⟩ | ⟨⟨h0, h1⟩, h2⟩
  · exact Or.inl ⟨by rw [ha, hc, h1], by rw [hb, he, h2]⟩
  · exact Or.inr ⟨h0, by rw [ha, he, h1], by rw [hb, hc, h2]⟩

theorem sameVal_sound (hsat : ∀ (n : String) (b : ZBind), D[n]? = some b → SatB w E k b)
    {i : Nat} {n r : String} {b b' : ZBind} (hn : D[n]? = some b) (hr : D[r]? = some b')
    (ih : ∀ x, below R i x = true → E k x = E k (repOf R x))
    (h : sameVal w R i n r b b' = true) : E k n = E k r := by
  have sb := hsat _ _ hn
  have sb' := hsat _ _ hr
  cases b <;> cases b' <;> simp only [sameVal, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq, Bool.false_eq_true] at h
  · rename_i w1 bop d a b w2 bop' d' c e
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, ha⟩, hb⟩, hc⟩, he⟩, hs⟩ := h
    simp only [SatB] at sb sb'
    rw [sb trivial, sb' trivial]
    rcases sameOps_val (ih _ ha) (ih _ hb) (ih _ hc) (ih _ he) hs with ⟨h1, h2⟩ | ⟨h0, h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, JasminBinOp.apply_comm _ h0]
  · rename_i d a b d' c e
    obtain ⟨⟨⟨⟨⟨⟨rfl, rfl⟩, ha⟩, hb⟩, hc⟩, he⟩, hs⟩ := h
    simp only [SatB] at sb sb'
    rw [sb, sb']
    rcases sameOps_val (ih _ ha) (ih _ hb) (ih _ hc) (ih _ he) hs with ⟨h1, h2⟩ | ⟨-, h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, mulHiW_comm]
  · rename_i d v d' v'
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    simp only [SatB] at sb sb'
    rw [sb, sb']

/-- **Soundness of the representative table.** On a lane satisfying every binding of `D`,
    every name has the value of its representative. -/
theorem repCheck_sound (hsat : ∀ (n : String) (b : ZBind), D[n]? = some b → SatB w E k b)
    (hc : repCheck w D R = true) (x : String) : E k x = E k (repOf R x) := by
  have key : ∀ i x, below R i x = true → E k x = E k (repOf R x) := by
    intro i
    induction i with
    | zero =>
      intro x hx
      unfold below at hx
      split at hx
      · simp at hx
      · rename_i hR
        simp [repOf, hR]
    | succ i ih =>
      intro x hx
      unfold below at hx
      split at hx
      · rename_i r j hR
        simp only [decide_eq_true_eq] at hx
        rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hj | rfl
        · exact ih x (by simp [below, hR, hj])
        · have hrep : repOf R x = r := by simp [repOf, hR]
          rw [hrep]
          have he := List.all_eq_true.1 hc (x, (r, j))
            (Std.HashMap.mem_toList_iff_getElem?_eq_some.2 hR)
          unfold repEntryOK at he
          simp only [Bool.or_eq_true, beq_iff_eq] at he
          rcases he with he | he
          · rw [he]
          · split at he
            · rename_i b b' hn hr
              exact sameVal_sound hsat hn hr ih he
            · cases he
      · rename_i hR
        simp [repOf, hR]
  exact key ((R[x]?.map (·.2)).getD 0 + 1) x (by
    unfold below
    split
    · rename_i r j hR
      simp [hR]
    · rfl)

theorem satB_renameB (hr : ∀ x, E k x = E k (repOf R x)) {b : ZBind} (h : SatB w E k b) :
    SatB w E k (renameB R b) := by
  cases b with
  | pack w' bop d a b =>
    intro hw
    simp only [SatB] at h
    rw [h hw, ← hr, ← hr]
  | mulhi d a b =>
    simp only [SatB] at h
    simp only [renameB, SatB]
    rw [h, ← hr, ← hr]
  | _ => exact h

theorem repTable_sound {bs : Array ZBind}
    (hsat : ∀ (n : String) (b : ZBind), (mkDefs bs)[n]? = some b → SatB w E k b)
    (x : String) : E k x = E k (repOf (repTable w bs) x) := by
  unfold repTable
  dsimp only
  split
  · rename_i hc
    exact repCheck_sound hsat hc x
  · simp [repOf]

end Rep

/-! ## 10. The validator -/

/-- The name of the input at byte offset `off`: parameter `s` is at `offs[s]`. -/
def paramAt (params : List String) (offs : List Nat) (off : Nat) : Option String :=
  ((params.zip offs).find? (fun p => p.2 == off)).map (·.1)

theorem paramAt_mem {params : List String} {offs : List Nat} {off : Nat} {p : String}
    (h : paramAt params offs off = some p) : (p, off) ∈ params.zip offs := by
  unfold paramAt at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨⟨p', off'⟩, hf, rfl⟩ := h
  have hmem := List.mem_of_find?_eq_some hf
  have hoff := List.find?_some hf
  simp only [beq_iff_eq] at hoff
  subst hoff
  exact hmem

/-- The stores leave output `j` at offset `stride·j`, a value `opMatch` identifies
    with `outs[j]`, and every store offset is a multiple of the stride. -/
def outsOK (m : Mode) (D : Std.HashMap String ZBind) (s : SState) (outs : List String) : Bool :=
  (List.range outs.length).all (fun j =>
    match s.outAt (m.stride * j), outs[j]? with
    | some t, some o => opMatch D t o
    | _, _ => false) &&
  s.log.all (fun e => e.1 % m.stride == 0)

/-- The last `nOut` names bound by a binding list: the outputs in the renderer's
    convention. -/
def lastOuts (bs : Array ZBind) (nOut : Nat) : List String :=
  (bs.toList.drop (bs.size - nOut)).map ZBind.dst

/-- The frame discipline of a program run with `depth` bytes of stack frame allocated:
    an `addq` of `%rsp` releases at most what is allocated, every stack access at offset
    `off` is at a multiple of the store width and lies inside the frame
    (`off + stride ≤ depth`), and nothing is allocated at the end. -/
def frameOK (m : Mode) : Nat → List Instr → Bool
  | depth, [] => depth == 0
  | depth, .spSub n :: is => frameOK m (depth + n) is
  | depth, .spAdd n :: is => decide (n ≤ depth) && frameOK m (depth - n) is
  | depth, .ldS off _ :: is =>
    off % m.stride == 0 && decide (off + m.stride ≤ depth) && frameOK m depth is
  | depth, .stS _ off :: is =>
    off % m.stride == 0 && decide (off + m.stride ≤ depth) && frameOK m depth is
  | depth, _ :: is => frameOK m depth is

/-- The translation validator: parse `text`, check the frame discipline (`frameOK`), run
    it symbolically from the inputs `params` at offsets `offs`, recognise each written
    value as a binding of `bs` (lane width `w`) with the range facts `rf`, and check that
    output `j` is `outs[j]`. -/
def validate (m : Mode) (w : LaneW) (params : List String) (offs : List Nat)
    (bs : Array ZBind) (outs : List String) (rf : Std.HashMap String Iv) (text : String) :
    Bool :=
  match parse m text with
  | .ok (prog, ro) =>
    let R := repTable w bs
    let bs' := bs.map (renameB R)
    let D := mkDefs bs'
    let km := keyMap w m D bs'
    match srun m ro (paramAt params offs) (norm w m D rf km) SState.init prog with
    | some s => frameOK m 0 prog && outsOK m D s (outs.map (repOf R))
    | none => false
  | .error _ => false

/-- **Soundness of the validator.** When `validate` accepts `text`, the text parses to a
    program `prog` with data table `ro`, and for every lane valuation `E` satisfying the
    bindings `bs` and the range facts `rf` on the active lanes, every input region whose
    lanes at offset `offs[s]` hold parameter `s`, and every initial machine state with no
    stores, running `prog` succeeds and leaves at offset `stride·j` of the output region a
    value whose active lane `k` is `E k outs[j]`, the value of output `j` of the scalar
    bindings on lane `k`. -/
theorem validate_sound {m : Mode} {w : LaneW} {params : List String} {offs : List Nat}
    {bs : Array ZBind} {outs : List String} {rf : Std.HashMap String Iv} {text : String}
    (h : validate m w params offs bs outs rf text = true) :
    ∃ prog ro, parse m text = .ok (prog, ro) ∧
      ∀ (E : Nat → String → BitVec w.bits),
        (∀ b ∈ bs.toList, ∀ k < m.act / w.bits, SatB w E k b) →
        (∀ (n : String) (i : Iv), rf[n]? = some i → ∀ k < m.act / w.bits,
          i.Mem w.bits (E k n)) →
        ∀ (inp : Nat → BitVec 512),
        (∀ p off, (p, off) ∈ params.zip offs → ∀ k < m.act / w.bits,
          lane w.bits (inp off) k = E k p) →
        ∀ σ : MState, σ.log = [] →
        ∃ σ', run m inp ro σ prog = some σ' ∧
          ∀ j (hj : j < outs.length), ∃ v, σ'.outAt (m.stride * j) = some v ∧
            ∀ k < m.act / w.bits, lane w.bits v k = E k outs[j] := by
  unfold validate at h
  split at h
  · rename_i prog ro hp
    refine ⟨prog, ro, hp, ?_⟩
    intro E hsat hrf inp hinp σ hσ
    have hrep : ∀ k, Active m w k → ∀ x, E k x = E k (repOf (repTable w bs) x) :=
      fun k hk => repTable_sound
        (fun n b hb => hsat b (mkDefs_mem bs n b hb) k ((active_iff m w k).1 hk))
    have hf : Facts m w (mkDefs (bs.map (renameB (repTable w bs)))) rf E :=
      { sat := fun n b hb k hk => by
          have hm := mkDefs_mem _ n b hb
          rw [Array.toList_map, List.mem_map] at hm
          obtain ⟨b0, hb0, rfl⟩ := hm
          exact satB_renameB (hrep k hk) (hsat b0 hb0 k ((active_iff m w k).1 hk))
        rng := fun n i hi k hk => hrf n i hi k ((active_iff m w k).1 hk) }
    dsimp only at h
    split at h
    · rename_i s hs
      have hin : ∀ off p, paramAt params offs off = some p →
          wr m (inp off) = wr m (pack w E p) := by
        intro off p hpa
        apply wr_eq_of_lanes (laneBits_cases w)
        intro k hk
        rw [hinp p off (paramAt_mem hpa) k ((active_iff m w k).1 hk), lane_pack E p hk]
      obtain ⟨σ', hrun, hrel⟩ := srun_sound (inp := inp) (norm_sound hf _) hin prog
        (rel_init m σ (pack w E) hσ) hs
      refine ⟨σ', hrun, ?_⟩
      intro j hj
      unfold outsOK at h
      simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
      have hj' := h.2.1 j (by rw [List.length_map]; exact hj)
      rw [List.getElem?_map, List.getElem?_eq_getElem hj] at hj'
      split at hj'
      · rename_i t o hto ho
        cases ho
        refine ⟨_, outAt_rel hrel _ t hto, ?_⟩
        intro k hk
        have hk' : Active m w k := (active_iff m w k).2 hk
        rw [lane_wr _ hk', opMatch_lane hf hj' hk', ← hrep k hk']
      · cases hj'
    · cases h
  · cases h

/-- A short description of a term for diagnostics. -/
def termDesc : Term → String
  | .var x => x
  | .cst _ => "const"
  | .init r => s!"init{r}"
  | .lw L o a b =>
    let os := match o with
      | .bin .add => "add" | .bin .sub => "sub" | .bin .mul => "mul" | .bin .and => "and"
      | .bin .or => "or" | .bin .xor => "xor" | .bin .shl => "shl" | .bin .shr => "shr"
      | .bin .andn => "andn" | .minu => "minu" | .muludq => "muludq"
    let d (t : Term) : String := match t with
      | .var x => x | .cst _ => "const" | _ => "term"
    s!"lw{L} {os}({d a}, {d b})"
  | .shi L l k _ => s!"shi{L} {if l then "left" else "right"} {k}"
  | .dup _ _ => "dup"
  | .mdup _ _ _ _ => "mdup"

/-- The first register written by the step from `s` to `s'` whose term is an unnamed
    lane-wise operation other than the addition of a constant, which the unsigned-minimum
    form of the conditional add leaves unnamed (diagnostics only). -/
def unnamedWrite (s s' : SState) : Option String :=
  ((List.range 32).find? (fun r =>
    (s'.regs.toArray.getD r (.init 0)) != (s.regs.toArray.getD r (.init 0)) &&
      match (s'.regs.toArray.getD r (.init 0)) with
      | .lw _ (.bin .add) _ (.cst _) => false
      | .lw _ (.bin .add) (.cst _) _ => false
      | .lw .. => true
      | _ => false)).map
    (fun r => s!"%zmm{r} := {termDesc (s'.regs.toArray.getD r (.init 0))}")

/-- The symbolic run of `validate` from `s`, reporting the index of the first instruction
    it rejects (diagnostics only; not used by `validate_sound`). -/
def diagRun (m : Mode) (w : LaneW) (ro : Std.HashMap String (Array (BitVec 64)))
    (params : List String) (offs : List Nat) (D : Std.HashMap String ZBind)
    (rf : Std.HashMap String Iv) (km : Std.HashMap String (String × List String)) (outs : List String) :
    SState → Nat → List Instr → String
  | s, _, [] =>
    if outsOK m D s outs then "accepted" else
    match (List.range outs.length).find? (fun j =>
        match s.outAt (m.stride * j), outs[j]? with
        | some t, some o => !opMatch D t o
        | _, _ => true) with
    | some j =>
      let got := match s.outAt (m.stride * j) with
        | some (.var x) => "var " ++ x
        | some (.cst _) => "a constant"
        | some _ => "a non-variable term"
        | none => "no store"
      s!"output {j}: expected {outs[j]?.getD "?"}, stored {got}"
    | none => "a store offset is not a multiple of the stride"
  | s, i, x :: xs =>
    match sstep m ro (paramAt params offs) (norm w m D rf km) s x with
    | some s' =>
      match unnamedWrite s s' with
      | some msg => s!"instruction {i} leaves an unnamed value: {msg}"
      | none => diagRun m w ro params offs D rf km outs s' (i + 1) xs
    | none => s!"instruction {i} rejected"

/-- Why `validate` rejects `text`: the parse error, a violation of the frame discipline,
    or the index of the first instruction the symbolic run rejects (diagnostics only). -/
def validateDiag (m : Mode) (w : LaneW) (params : List String) (offs : List Nat)
    (bs : Array ZBind) (outs : List String) (rf : Std.HashMap String Iv) (text : String) :
    String :=
  match parse m text with
  | .ok (prog, ro) =>
    if !frameOK m 0 prog then "the stack frame discipline (frameOK) is violated" else
    let R := repTable w bs
    let bs' := bs.map (renameB R)
    let D := mkDefs bs'
    diagRun m w ro params offs D rf (keyMap w m D bs') (outs.map (repOf R)) SState.init 0 prog
  | .error e => "parse: " ++ e

/-! ## 11. Static checks -/

open CatCrypt.Crypto.SecureCompilation.VIR in
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect in
/-- The validator on the renderer's text of a packed program `c` with `nOut` outputs,
    parameter `s` at byte offset `64·s`, in the `%zmm` form at 64-bit lanes, with no range
    facts; `edit` is applied to the text first. -/
def validatePackedQ {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty} (nOut : Nat)
    (c : Com jasminDialect Γ t) (edit : String → String := id) : Bool :=
  let (params, vm) := JasminPrint.paramsAndMap Γ
  let names := params.map (fun p => p.var.var.vname)
  let bs := (VpackZmmLinearRender.collectZBinds vm 0 #[] c).1
  match VpackZmmLinearRender.renderZmmLinearFunction "f" (fun s => 64 * s) nOut c with
  | .ok text =>
    validate .zmm .q names (names.zipIdx.map (fun (_, s) => 64 * s)) bs (lastOuts bs nOut) {}
      (edit text)
  | .error _ => false

/- The butterfly `hi` slice of the renderer's §4 (`prod := w ⊙ b`, `hi := a + prod`)
    validates against its own binding list. The render and the validator (with value numbering) run in the interpreter here; the
    check measured 232 ms under a two-thread build, so its budget is 400 ms. -/
open CatCrypt.Crypto.SecureCompilation.X86Backend.ButterflyBlockCom (butterflyHiCom) in
set_option kat.ms 400 in
#kat validatePackedQ 1 butterflyHiCom

/- The same text with its add turned into a subtract is rejected. -/
open CatCrypt.Crypto.SecureCompilation.X86Backend.ButterflyBlockCom (butterflyHiCom) in
set_option kat.ms 400 in
#kat !validatePackedQ 1 butterflyHiCom (fun s => s.replace "vpaddq" "vpsubq")

/-- The validator on the renderer's text of the binding list `bs` over parameters
    `names` (parameter `s` at offset `stride·s`), with the renderer's range input `ranges`
    and the validator's range facts `rf`; `edit` is applied to the text first. -/
def validateBinds (m : Mode) (w : LaneW) (names : List String) (bs : Array ZBind)
    (nOut : Nat) (ranges : Option (Nat × Array Iv)) (rf : List (String × Iv))
    (edit : String → String := id) : Bool :=
  match VpackZmmLinearRender.renderZmmLinearBinds "f" (fun s => m.stride * s) nOut names bs
      ranges (m == .ymm) with
  | .ok text =>
    validate m w names (names.zipIdx.map (fun (_, s) => m.stride * s)) bs (lastOuts bs nOut)
      (Std.HashMap.ofList rf) (edit text)
  | .error _ => false

/-- The 32-bit Montgomery multiply of `FieldDescentBBMont32` as a binding list:
    `hi - mulhi(lo·μ, p)` and its conditional add of `p`. -/
def montBinds : Array ZBind := #[
  .const "v0" (VpackZmmLinearRender.bcast512d 2013265921),
  .const "v1" (VpackZmmLinearRender.bcast512d 2281701377),
  .const "v2" (VpackZmmLinearRender.bcast512d 31), .const "v3" 0,
  .pack .d .mul "v4" "a" "b", .mulhi "v5" "a" "b", .pack .d .mul "v6" "v4" "v1",
  .mulhi "v7" "v6" "v0", .pack .d .sub "v8" "v5" "v7", .pack .d .shr "v9" "v8" "v2",
  .pack .d .sub "v10" "v3" "v9", .pack .d .and "v11" "v10" "v0",
  .pack .d .add "v12" "v8" "v11"]

/-- The range input of `montBinds`: `v8 = hi - u` lies in `[-(p-1), p-1]`. -/
def montRanges : Array Iv :=
  (Array.replicate 13 ((0 : Int), (2 ^ 32 - 1 : Int))).set! 8 (-2013265920, 2013265920)

/- The Montgomery multiply renders to the fused high/low multiply (`vpmuludq`,
    `vmovshdup`, `vmovsldup` under `%k1`, `%k2`), a resident broadcast constant, a
    `{1to16}` operand and the unsigned-minimum form of the conditional add, and
    validates with the range fact on `v8`. -/
#kat validateBinds .zmm .d ["a", "b"] montBinds 1 (some (2013265920, montRanges))
  [("v8", (-2013265920, 2013265920))]

/- Without the range fact the unsigned minimum is rejected. -/
#kat !validateBinds .zmm .d ["a", "b"] montBinds 1 (some (2013265920, montRanges)) []

/- A merge under the wrong mask is rejected. -/
#kat !validateBinds .zmm .d ["a", "b"] montBinds 1 (some (2013265920, montRanges))
  [("v8", (-2013265920, 2013265920))] (fun s => s.replace "{%k2}" "{%k1}")

/- The Montgomery step of `montBinds` renders in the even/odd products (`fuseMontSub`): no
   `vpmulld` and no `vmovsldup`, two `vpsubq`; with the 64-bit differences turned into sums
   the text is rejected. -/
#kat (VpackZmmLinearRender.renderZmmLinearBinds "f" (fun s => 64 * s) 1 ["a", "b"] montBinds
    (some (2013265920, montRanges))).toOption.any (fun s =>
      (s.splitOn "vpmulld").length == 1 && (s.splitOn "vmovsldup").length == 1 &&
        (s.splitOn "vpsubq").length == 3) &&
  !validateBinds .zmm .d ["a", "b"] montBinds 1 (some (2013265920, montRanges))
    [("v8", (-2013265920, 2013265920))] (fun s => s.replace "vpsubq" "vpaddq")

/-- The BabyBear Barrett quotient of `FieldDescentBB` as a binding list:
    `x - (((x >> 30)·m >> 32)·p)` for `x = a·b`. -/
def barrettBinds : Array ZBind := #[
  .const "v0" (VpackZmmLinearRender.bcast512 30),
  .const "v1" (VpackZmmLinearRender.bcast512 2290649223),
  .const "v2" (VpackZmmLinearRender.bcast512 32),
  .const "v3" (VpackZmmLinearRender.bcast512 2013265921),
  .pack .q .mul "v4" "a" "b", .pack .q .shr "v5" "v4" "v0", .pack .q .mul "v6" "v5" "v1",
  .pack .q .shr "v7" "v6" "v2", .pack .q .mul "v8" "v7" "v3", .pack .q .sub "v9" "v4" "v8"]

/-- The range input of `barrettBinds`: `v5` and `v7` lie below `2^32`. -/
def barrettRanges : Array Iv := Array.replicate 10 ((0 : Int), (2 ^ 32 - 1 : Int))

/-- The validator's range facts of `barrettBinds`. -/
def barrettFacts : List (String × Iv) :=
  [("a", (0, 2013265920)), ("b", (0, 2013265920)), ("v5", (0, 2 ^ 32 - 1)),
    ("v7", (0, 2 ^ 32 - 1))]

/- The Barrett quotient renders with `vpmuludq` for its three multiplies and immediate
    shifts, and validates in the `%zmm` and in the `%ymm` form. -/
#kat validateBinds .zmm .q ["a", "b"] barrettBinds 1 (some (2013265920, barrettRanges))
  barrettFacts

#kat validateBinds .ymm .q ["a", "b"] barrettBinds 1 (some (2013265920, barrettRanges))
  barrettFacts

/- The two shifts of the Barrett quotient by broadcast constants render in the
    immediate-count form, `vpsrlq $30` and `vpsrlq $32`, with no variable-count
    `vpsrlvq`; with the count `30` printed as `31` the text is rejected. -/
#kat (VpackZmmLinearRender.renderZmmLinearBinds "f" (fun s => 64 * s) 1 ["a", "b"]
    barrettBinds (some (2013265920, barrettRanges))).toOption.any (fun s =>
      (s.splitOn "\tvpsrlq $30, ").length == 2 && (s.splitOn "\tvpsrlq $32, ").length == 2 &&
        (s.splitOn "vpsrlvq").length == 1) &&
  !validateBinds .zmm .q ["a", "b"] barrettBinds 1 (some (2013265920, barrettRanges))
    barrettFacts (fun s => s.replace "\tvpsrlq $30, " "\tvpsrlq $31, ")

/-- Sixteen-lane shifts by broadcast constants: `v2 = ((a << 7) >> 3) ⊕ b`. -/
def shiftDBinds : Array ZBind := #[
  .const "k7" (VpackZmmLinearRender.bcast512d 7), .const "k3" (VpackZmmLinearRender.bcast512d 3),
  .pack .d .shl "v0" "a" "k7", .pack .d .shr "v1" "v0" "k3", .pack .d .xor "v2" "v1" "b"]

/- The dword shifts render as `vpslld $7` and `vpsrld $3`, with no variable-count
    `vpsllvd` or `vpsrlvd`, and validate; with the count `3` printed as `4` the text is
    rejected. -/
#kat (VpackZmmLinearRender.renderZmmLinearBinds "f" (fun s => 64 * s) 1 ["a", "b"]
    shiftDBinds).toOption.any (fun s =>
      (s.splitOn "\tvpslld $7, ").length == 2 && (s.splitOn "\tvpsrld $3, ").length == 2 &&
        (s.splitOn "vpsllvd").length == 1 && (s.splitOn "vpsrlvd").length == 1) &&
  validateBinds .zmm .d ["a", "b"] shiftDBinds 1 none [] &&
  !validateBinds .zmm .d ["a", "b"] shiftDBinds 1 none []
    (fun s => s.replace "\tvpsrld $3, " "\tvpsrld $4, ")

/- Without the range fact on `v7` the `vpmuludq` of `v8` is rejected. -/
#kat !validateBinds .zmm .q ["a", "b"] barrettBinds 1 (some (2013265920, barrettRanges))
  (barrettFacts.take 3)

/-- A binding list with duplicated bindings: `v1` computes `v0` and `v3` computes `v2`,
    each read after its duplicate; the outputs are `v3` and `v4`. -/
def dupBinds : Array ZBind := #[
  .pack .q .add "v0" "a" "b", .pack .q .add "v1" "b" "a", .pack .q .xor "v2" "v0" "b",
  .pack .q .xor "v3" "v1" "b", .pack .q .add "v4" "v2" "v3"]

/- Duplicated bindings validate: registers and operands are compared up to value
    numbering. -/
#kat validateBinds .zmm .q ["a", "b"] dupBinds 2 none []

/-- The doubling `x = a + a` of a BabyBear element, computed twice (`v3`, `v4`), and its
    conditional subtract of `p` through the duplicate, `v5 = v4 - p` and
    `v9 = v5 + ((0 - (v5 >> 63)) & p)`, added to the first copy. -/
def doubleDupBinds : Array ZBind := #[
  .const "v0" (VpackZmmLinearRender.bcast512 2013265921),
  .const "v1" (VpackZmmLinearRender.bcast512 63), .const "v2" 0,
  .pack .q .add "v3" "a" "a", .pack .q .add "v4" "a" "a", .pack .q .sub "v5" "v4" "v0",
  .pack .q .shr "v6" "v5" "v1", .pack .q .sub "v7" "v2" "v6", .pack .q .and "v8" "v7" "v0",
  .pack .q .add "v9" "v5" "v8", .pack .q .add "v10" "v3" "v9"]

/-- The range input of `doubleDupBinds`: `v5 = 2a - p` lies in `[-p, p-2]`. -/
def doubleDupRanges : Array Iv :=
  (Array.replicate 11 ((0 : Int), (2 ^ 32 - 1 : Int))).set! 5 (-2013265921, 2013265919)

/- The conditional subtract renders as `vpminuq` of the two copies' registers and
    validates with the range fact on `v5`. -/
#kat validateBinds .zmm .q ["a"] doubleDupBinds 1 (some (2013265920, doubleDupRanges))
  [("v5", (-2013265921, 2013265919))]

/-- `montBinds` with a second high half `v8 = mulhi(a, b)` after the fused pair; the
    subtraction `v9` reads the first. -/
def montDupBinds : Array ZBind := #[
  .const "v0" (VpackZmmLinearRender.bcast512d 2013265921),
  .const "v1" (VpackZmmLinearRender.bcast512d 2281701377),
  .const "v2" (VpackZmmLinearRender.bcast512d 31), .const "v3" 0,
  .pack .d .mul "v4" "a" "b", .mulhi "v5" "a" "b", .pack .d .mul "v6" "v4" "v1",
  .mulhi "v7" "v6" "v0", .mulhi "v8" "b" "a", .pack .d .sub "v9" "v5" "v7",
  .pack .d .shr "v10" "v9" "v2", .pack .d .sub "v11" "v3" "v10",
  .pack .d .and "v12" "v11" "v0", .pack .d .add "v13" "v9" "v12"]

/-- The range input of `montDupBinds`: `v9 = hi - u` lies in `[-(p-1), p-1]`. -/
def montDupRanges : Array Iv :=
  (Array.replicate 14 ((0 : Int), (2 ^ 32 - 1 : Int))).set! 9 (-2013265920, 2013265920)

/- The fused high/low multiply, the duplicate high half and the unsigned-minimum form of
    the conditional add validate. -/
#kat validateBinds .zmm .d ["a", "b"] montDupBinds 1 (some (2013265920, montDupRanges))
  [("v9", (-2013265920, 2013265920))]

/-- The forty parameters `p0..p39` of `spillBinds`. -/
def spillNames : List String := (List.range 40).map (fun i => "p" ++ toString i)

/-- Forty pairwise sums `t_i = p_i + p_(i+1 mod 40)` followed by the running sum
    `s_k = s_(k-1) + t_(k+1)` of them: the forty `t_i` are live together, more values
    than the 31 allocatable registers hold. -/
def spillBinds : Array ZBind :=
  ((List.range 40).map (fun i => ZBind.pack .q .add ("t" ++ toString i) ("p" ++ toString i)
      ("p" ++ toString ((i + 1) % 40))) ++
    (List.range 39).map (fun k => ZBind.pack .q .add ("s" ++ toString k)
      (if k = 0 then "t0" else "s" ++ toString (k - 1)) ("t" ++ toString (k + 1)))).toArray

/- A program whose parameters and live values exceed the registers renders with a stack
    frame (its text addresses `%rsp`) and validates in both register forms; with the frame
    release turned into a second allocation it is rejected. The check measured 83 ms in
    the language server, so its budget is 400 ms. -/
set_option kat.ms 400 in
#kat validateBinds .zmm .q spillNames spillBinds 1 none [] &&
  validateBinds .ymm .q spillNames spillBinds 1 none [] &&
  !validateBinds .zmm .q spillNames spillBinds 1 none [] (fun s => s.replace "\taddq" "\tsubq") &&
  (VpackZmmLinearRender.renderZmmLinearBinds "f" (fun s => 64 * s) 1 spillNames
    spillBinds).toOption.any (fun s => (s.splitOn "(%rsp)").length > 1)

/-- A rotate `v2 = (a << 1) | (a >> 63)`, a three-input exclusive or `v4 = (b ⊕ c) ⊕ d`
    and a Keccak χ step `v7 = a ⊕ ((b ⊕ 1…1) ∧ c)`, the outputs `v2`, `v4`, `v7`. -/
def rolTernBinds : Array ZBind := #[
  .const "k1" (VpackZmmLinearRender.bcast512 1), .const "k63" (VpackZmmLinearRender.bcast512 63),
  .const "K" (VpackZmmLinearRender.bcast512 (2 ^ 64 - 1)),
  .pack .q .shl "v0" "a" "k1", .pack .q .shr "v1" "a" "k63", .pack .q .xor "v3" "b" "c",
  .pack .q .xor "v5" "b" "K", .pack .q .and "v6" "v5" "c",
  .pack .q .or "v2" "v0" "v1", .pack .q .xor "v4" "v3" "d", .pack .q .xor "v7" "a" "v6"]

/-- The text the renderer prints for `rolTernBinds` on `%zmm`. -/
def rolTernText : Option String :=
  (VpackZmmLinearRender.renderZmmLinearBinds "f" (fun s => 64 * s) 3 ["a", "b", "c", "d"]
    rolTernBinds).toOption

/- The rotate renders as `vprolq $1`, the exclusive or and χ as `vpternlogq` with the
    truth tables of `xor3B` (150) and `chiB` (210), and the text validates on `%zmm` and
    `%ymm`. -/
#kat rolTernText.any (fun s => (s.splitOn "\tvprolq $1, ").length == 2 &&
    (s.splitOn "\tvpternlogq $150, ").length == 2 && (s.splitOn "\tvpternlogq $210, ").length == 2
    && (s.splitOn "\tvpsllq").length == 1 && (s.splitOn "\tvpandq").length == 1)
#kat validateBinds .zmm .q ["a", "b", "c", "d"] rolTernBinds 3 none [] &&
  validateBinds .ymm .q ["a", "b", "c", "d"] rolTernBinds 3 none []

/- Each `vpternlogq` of `rolTernBinds` writes the register of an operand read for the last
    time there, with no `vmovdqa64`: the exclusive or writes `d` (`%zmm3`, its table
    permuted, which for `xor3B` is itself) and χ writes `a` (`%zmm0`). A wrong rotate count
    and a wrong truth table are rejected; the χ step with its operands in another order,
    the truth table permuted to match and the result moved to the register of `a`, is
    accepted. -/
#kat rolTernText.any (fun s => (s.splitOn "vmovdqa64").length == 1 &&
    (s.splitOn "\tvpternlogq $150, %zmm2, %zmm1, %zmm3\n").length == 2 &&
    (s.splitOn "\tvpternlogq $210, %zmm2, %zmm1, %zmm0\n").length == 2) &&
  !validateBinds .zmm .q ["a", "b", "c", "d"] rolTernBinds 3 none []
    (fun s => s.replace "\tvprolq $1, " "\tvprolq $2, ") &&
  !validateBinds .zmm .q ["a", "b", "c", "d"] rolTernBinds 3 none []
    (fun s => s.replace "\tvpternlogq $210, " "\tvpternlogq $150, ") &&
  validateBinds .zmm .q ["a", "b", "c", "d"] rolTernBinds 3 none []
    (fun s => s.replace "\tvpternlogq $210, %zmm2, %zmm1, %zmm0\n"
      ("\tvpternlogq $" ++
        toString (ZmmTextModel.ternTable fun p q r => ZmmTextModel.chiB q p r).toNat ++
        ", %zmm2, %zmm0, %zmm1\n\tvmovdqa64 %zmm1, %zmm0\n"))

/-- A Keccak χ step `v2 = a ⊕ ((b ⊕ 1…1) ∧ c)` followed by the bindings `tail`. -/
def chiThen (tail : List ZBind) : Array ZBind :=
  #[.const "K" (VpackZmmLinearRender.bcast512 (2 ^ 64 - 1)), .pack .q .xor "v0" "b" "K",
    .pack .q .and "v1" "v0" "c", .pack .q .xor "v2" "a" "v1"] ++ tail.toArray

/-- The `%zmm` text of `chiThen tail` over the parameters `a`, `b`, `c`. -/
def chiThenText (tail : List ZBind) (nOut : Nat) : Option String :=
  (VpackZmmLinearRender.renderZmmLinearBinds "f" (fun s => 64 * s) nOut ["a", "b", "c"]
    (chiThen tail)).toOption

/- When only `b` (the second operand of χ) is read for the last time at χ, the
    `vpternlogq` writes `%zmm1` with the table of `chiB y x z`; when only `c` is, it
    writes `%zmm2` with the table of `chiB y z x`; neither needs a `vmovdqa64`, and both
    validate on `%zmm` and `%ymm`. When every operand is read later, one `vmovdqa64`
    copies `a` first, and the text validates. -/
#kat (chiThenText [.pack .q .add "v3" "a" "c"] 2).any (fun s =>
    (s.splitOn "vmovdqa64").length == 1 && (s.splitOn ("\tvpternlogq $" ++
      toString (ZmmTextModel.ternTable fun p q r => ZmmTextModel.chiB q p r).toNat ++
      ", %zmm2, %zmm0, %zmm1\n")).length == 2) &&
  (chiThenText [.pack .q .add "v3" "a" "b"] 2).any (fun s =>
    (s.splitOn "vmovdqa64").length == 1 && (s.splitOn ("\tvpternlogq $" ++
      toString (ZmmTextModel.ternTable fun p q r => ZmmTextModel.chiB q r p).toNat ++
      ", %zmm1, %zmm0, %zmm2\n")).length == 2)
#kat validateBinds .zmm .q ["a", "b", "c"] (chiThen [.pack .q .add "v3" "a" "c"]) 2 none [] &&
  validateBinds .ymm .q ["a", "b", "c"] (chiThen [.pack .q .add "v3" "a" "c"]) 2 none [] &&
  validateBinds .zmm .q ["a", "b", "c"] (chiThen [.pack .q .add "v3" "a" "b"]) 2 none [] &&
  validateBinds .ymm .q ["a", "b", "c"] (chiThen [.pack .q .add "v3" "a" "b"]) 2 none []
#kat (chiThenText [.pack .q .add "v3" "a" "b", .pack .q .add "v4" "v3" "c",
    .pack .q .xor "v5" "v4" "v2"] 1).any (fun s => (s.splitOn "vmovdqa64").length == 2) &&
  validateBinds .zmm .q ["a", "b", "c"] (chiThen [.pack .q .add "v3" "a" "b",
    .pack .q .add "v4" "v3" "c", .pack .q .xor "v5" "v4" "v2"]) 1 none []

end CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextValidate
