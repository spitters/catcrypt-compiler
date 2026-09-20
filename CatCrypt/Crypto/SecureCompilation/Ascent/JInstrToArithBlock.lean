/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.JasminComRunBlockSeq

/-!
# Lifting a decoded machine block to a typed dialect program

The byte ladder ends at `List (JInstr 64)` and the source ladder ends at
`Com jasminDialect`. Without an arrow between them a decoded byte string can be
related only to a specification written for it, never to a source program. This
module supplies the arrow in the upward direction: a decoded straight-line block
that parses is a typed dialect program `ArithBlock Γ` / `Com jasminDialect Γ (.reg 64)`,
and the block's `runBlock` output register holds that program's denotation.

## The two stages

* **Parse** — `bopOfJInstr` inverts `bopToJInstr` on the scalar arms, `recogOp`
  recognises the two-instruction window `mov dst ra; op dst rb` that `lowerArith2`
  emits, and `parseBlock` iterates it into a list of untyped `RawArith` records.
  `parseBlock_lowerRaw` is the syntactic round trip: a block that parses is the
  concatenation of the per-op lowerings of the records it parsed to.
* **Elaborate** — `elabOps` turns the untyped records into an `ArithBlock Γ`,
  resolving register names to De Bruijn variables through a partial map `find`
  extended slot by slot (`extendFind`). `elabOps_lowerBlock` is the semantic
  round trip: the elaborated block lowers, under the register map `nm` and the
  destination stream `dstStream`, back to the instructions it was parsed from.

`liftBlock_runBlock` composes the two with the imported `lowerBlock_tie`.

## Hypotheses that stay explicit

`FreshFor nm (dstStream ops)` — that the parsed destinations are injective and
disjoint from the live register map — is a hypothesis of `liftBlock_runBlock`,
not something the parser checks. `hfind`, that `find` and `nm` are inverse on
the names `find` resolves, is the invariant carried through the elaboration
proof (`hfind_extend`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-! ## 1. The untyped recovered op -/

/-- One scalar arithmetic op recovered from a decoded machine block: the operator
    together with the three register names it was emitted over. Untyped — the
    register names are not yet resolved to De Bruijn variables. -/
structure RawArith where
  /-- The recovered operator. -/
  bop : JasminBinOp
  /-- The destination register name. -/
  dst : String
  /-- The first operand's register name. -/
  a : String
  /-- The second operand's register name. -/
  b : String
  deriving DecidableEq, Repr

/-! ## 2. The recogniser -/

/-- The decidable form of `IsScalarBop`: `true` exactly on `add/sub/and/or/xor/mul`. -/
def isScalarBopB : JasminBinOp → Bool
  | .add | .sub | .and | .or | .xor | .mul => true
  | _ => false

/-- `isScalarBopB` implies the `Prop`-valued `IsScalarBop` that `ArithBlock.op`
    carries. -/
theorem IsScalarBop_of_isScalarBopB {bop : JasminBinOp} (h : isScalarBopB bop = true) :
    IsScalarBop bop := by
  cases bop <;> simp_all [isScalarBopB, IsScalarBop]

/-- Invert `bopToJInstr` on the scalar arms: a two-address ALU instruction with a
    register source yields its operator, destination and source name. Every other
    instruction is rejected. -/
def bopOfJInstr : JInstr 64 → Option (JasminBinOp × String × String)
  | .add d (.reg r) => some (.add, d, r)
  | .sub d (.reg r) => some (.sub, d, r)
  | .and_ d (.reg r) => some (.and, d, r)
  | .or_ d (.reg r) => some (.or, d, r)
  | .xor_ d (.reg r) => some (.xor, d, r)
  | .imul d (.reg r) => some (.mul, d, r)
  | _ => none

/-- Recognise the two-instruction window `mov dst ra; op dst rb` that `lowerArith2`
    emits, returning the recovered op and the instructions after the window. The
    ALU instruction's destination must be the register the `mov` primed. -/
def recogOp : List (JInstr 64) → Option (RawArith × List (JInstr 64))
  | .mov dst (.reg ra) :: i :: rest =>
      match bopOfJInstr i with
      | some (bop, d, rb) =>
          if d = dst then some (⟨bop, dst, ra, rb⟩, rest) else none
      | none => none
  | _ => none

/-- Parse a decoded machine block into the list of ops it was lowered from. The
    empty block parses to the empty list; any instruction sequence that is not a
    concatenation of recognised two-input windows is rejected — the one-input and
    constant lowerings of `ArithBlock.un` and `ArithBlock.cnst` are outside the
    parsed subset. -/
def parseBlock : List (JInstr 64) → Option (List RawArith)
  | [] => some []
  | i₀ :: i₁ :: rest =>
      match recogOp (i₀ :: i₁ :: rest) with
      | some (o, _) => (parseBlock rest).map (fun ops => o :: ops)
      | none => none
  | _ => none

/-! ## 3. Parse soundness — the syntactic round trip -/

/-- The lowering of a list of untyped ops: the concatenation of the per-op
    lowerings `lowerArith2`. -/
def lowerRaw (ops : List RawArith) : List (JInstr 64) :=
  ops.flatMap (fun o => lowerArith2 o.bop o.a o.b o.dst)

/-- The lowering of a non-empty list splits off its head op's block. -/
theorem lowerRaw_cons (o : RawArith) (ops : List RawArith) :
    lowerRaw (o :: ops) = lowerArith2 o.bop o.a o.b o.dst ++ lowerRaw ops := rfl

/-- `bopOfJInstr` inverts `bopToJInstr`: an instruction it recognises is the one
    `bopToJInstr` emits for the recovered operator, destination and source. -/
theorem bopOfJInstr_eq {i : JInstr 64} {bop : JasminBinOp} {d r : String}
    (h : bopOfJInstr i = some (bop, d, r)) : i = bopToJInstr bop d (.reg r) := by
  unfold bopOfJInstr at h
  split at h <;> simp_all [bopToJInstr] <;> (obtain ⟨rfl, -, -⟩ := h; rfl)

/-- **Parse soundness.** A block that parses is exactly the lowering of the ops
    it parsed to. -/
theorem parseBlock_lowerRaw : (blk : List (JInstr 64)) → (ops : List RawArith) →
    parseBlock blk = some ops → blk = lowerRaw ops
  | [], ops, h => by
      simp only [parseBlock, Option.some.injEq] at h
      subst h; rfl
  | i₀ :: i₁ :: rest, ops, h => by
      simp only [parseBlock] at h
      split at h
      · rename_i o tl hrec
        rcases hpr : parseBlock rest with _ | ops'
        · rw [hpr] at h; simp at h
        · rw [hpr] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          have ih := parseBlock_lowerRaw rest ops' hpr
          unfold recogOp at hrec
          split at hrec
          · rename_i dst ra i rest' heq
            split at hrec
            · rename_i bop d rb hb
              split at hrec
              · rename_i hd
                subst hd
                simp only [Option.some.injEq, Prod.mk.injEq] at hrec
                obtain ⟨ho, htl⟩ := hrec
                cases List.cons.inj heq |>.1
                have hrest : rest = rest' := (List.cons.inj (List.cons.inj heq).2).2
                subst hrest
                subst ho
                have hi : i = bopToJInstr bop d (.reg rb) := bopOfJInstr_eq hb
                have hi₁ : i₁ = i := (List.cons.inj (List.cons.inj heq).2).1
                rw [lowerRaw_cons, ← ih, hi₁, hi, lowerArith2]
                rfl
              · simp at hrec
            · simp at hrec
          · simp at hrec
      · simp at h
  | [_], ops, h => by simp [parseBlock] at h

/-! ## 4. Elaboration into the dependent context -/

/-- Extend a name-resolution map with a fresh binding `d` for the new slot: `d`
    resolves to `.here`, every other name goes through `find` shifted by `.there`.
    The register-side `RegMapG.extend` read backwards. -/
def extendFind {Γ : Ctxt jasminDialect} (find : String → Option (Ctxt.Var Γ (.reg 64)))
    (d : String) : String → Option (Ctxt.Var ((.reg 64 :: Γ : Ctxt jasminDialect)) (.reg 64)) :=
  fun r => if r = d then some .here else (find r).map Ctxt.Var.there

/-- **Elaborate untyped ops into an `ArithBlock`.** Each op's operand names are
    resolved through `find`, its operator is checked to be scalar, and the
    remainder is elaborated under the extended map. The final `out` name resolves
    to the returned variable. -/
def elabOps : {Γ : Ctxt jasminDialect} → (String → Option (Ctxt.Var Γ (.reg 64))) →
    List RawArith → String → Option (ArithBlock Γ)
  | _, find, [], out => (find out).map ArithBlock.ret
  | _, find, o :: rest, out =>
      match h : isScalarBopB o.bop, find o.a, find o.b with
      | true, some va, some vb =>
          (elabOps (extendFind find o.dst) rest out).map
            (fun rest' => .op o.bop (IsScalarBop_of_isScalarBopB h) va vb rest')
      | _, _, _ => none

/-! ## 5. The destination stream -/

/-- The padding name at index `k`: a `'%'` followed by `k` copies of `'p'`. The
    length of the character list carries the index, which is what makes the
    family injective (`padName_inj`). -/
def padName (k : Nat) : String := String.ofList ('%' :: List.replicate k 'p')

/-- Distinct indices give distinct padding names, read off the length of the
    character list. -/
theorem padName_inj {i j : Nat} (h : padName i = padName j) : i = j := by
  have hl : ('%' :: List.replicate i 'p') = ('%' :: List.replicate j 'p') :=
    String.ofList_inj.mp h
  simpa using congrArg List.length hl

/-- The destination-name stream of a list of parsed ops: the `i`-th op's
    destination, padded past the end of the list by `padName` indexed from the
    end, so that a stream can remain injective beyond the ops it describes. -/
def dstStream (ops : List RawArith) (i : Nat) : String :=
  match ops[i]? with
  | some o => o.dst
  | none => padName (i - ops.length)

/-- Shifting the stream past the head op is the stream of the tail. -/
theorem dstStream_cons_succ (o : RawArith) (ops : List RawArith) (k : Nat) :
    dstStream (o :: ops) (k + 1) = dstStream ops k := by
  simp only [dstStream, List.getElem?_cons_succ, List.length_cons]
  cases ops[k]? <;> simp [Nat.succ_sub_succ]

/-- The head of the stream is the head op's destination. -/
theorem dstStream_zero (o : RawArith) (ops : List RawArith) :
    dstStream (o :: ops) 0 = o.dst := rfl

/-! ## 6. Elaboration soundness — the semantic round trip -/

/-- The `find`/`nm` inverse invariant is preserved by extending both sides with
    the same fresh destination name. -/
theorem hfind_extend {Γ : Ctxt jasminDialect} (nm : RegMapG Γ)
    (find : String → Option (Ctxt.Var Γ (.reg 64)))
    (hfind : ∀ (v : Ctxt.Var Γ (.reg 64)) (r : String), find r = some v → nm v = r)
    (d : String) :
    ∀ (v : Ctxt.Var ((.reg 64 :: Γ : Ctxt jasminDialect)) (.reg 64)) (r : String),
      extendFind find d r = some v → (nm.extend d) v = r := by
  intro v r h
  unfold extendFind at h
  split at h
  · rename_i hr
    subst hr
    simp only [Option.some.injEq] at h
    subst h
    rfl
  · rcases hf : find r with _ | w
    · rw [hf] at h; simp at h
    · rw [hf] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      exact hfind w r hf

/-- **Elaboration soundness.** An `ArithBlock` elaborated from a list of parsed
    ops lowers, under a register map inverse to the name resolution and the
    destination stream of those ops, back to exactly the instructions they
    describe. -/
theorem elabOps_lowerBlock : {Γ : Ctxt jasminDialect} →
    (nm : RegMapG Γ) → (find : String → Option (Ctxt.Var Γ (.reg 64))) →
    (hfind : ∀ (v : Ctxt.Var Γ (.reg 64)) (r : String), find r = some v → nm v = r) →
    (ops : List RawArith) → (out : String) → (ab : ArithBlock Γ) →
    elabOps find ops out = some ab →
    lowerBlock ab nm (dstStream ops) = lowerRaw ops
  | _, nm, find, _, [], out, ab, h => by
      simp only [elabOps] at h
      rcases hf : find out with _ | v
      · rw [hf] at h; simp at h
      · rw [hf] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        rfl
  | _, nm, find, hfind, o :: rest, out, ab, h => by
      simp only [elabOps] at h
      split at h
      · rename_i va vb _hs hva hvb
        rcases he : elabOps (extendFind find o.dst) rest out with _ | rest'
        · rw [he] at h; simp at h
        · rw [he] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          have ih := elabOps_lowerBlock (nm.extend o.dst) (extendFind find o.dst)
            (hfind_extend nm find hfind o.dst) rest out rest' he
          have hstream : (fun k => dstStream (o :: rest) (k + 1)) = dstStream rest := by
            funext k; exact dstStream_cons_succ o rest k
          simp only [lowerBlock, dstStream_zero, hstream, hfind va o.a hva,
            hfind vb o.b hvb, ih, lowerRaw, List.flatMap_cons]
      · simp at h

/-! ## 7. The packaged lift -/

/-- **The lift.** A decoded machine block that parses and elaborates is a typed
    dialect program, and the block's `runBlock` output register holds that
    program's `Com jasminDialect` denotation. Composes the syntactic round trip
    (`parseBlock_lowerRaw`), the semantic round trip (`elabOps_lowerBlock`) and
    the downward tie (`lowerBlock_tie`). -/
theorem liftBlock_runBlock {Γ : Ctxt jasminDialect}
    (blk : List (JInstr 64)) (ops : List RawArith)
    (nm : RegMapG Γ) (find : String → Option (Ctxt.Var Γ (.reg 64)))
    (hfind : ∀ (v : Ctxt.Var Γ (.reg 64)) (r : String), find r = some v → nm v = r)
    (out : String) (ab : ArithBlock Γ)
    (hparse : parseBlock blk = some ops) (helab : elabOps find ops out = some ab)
    (s : JState 64) (V : Ctxt.Valuation Γ)
    (hinterp : JStateInterpG nm V s) (hfresh : FreshFor nm (dstStream ops)) :
    (runBlock s blk).get (outReg ab nm (dstStream ops)) = ab.toCom.denote V := by
  have hblk : blk = lowerBlock ab nm (dstStream ops) := by
    rw [elabOps_lowerBlock nm find hfind ops out ab helab]
    exact parseBlock_lowerRaw blk ops hparse
  rw [hblk]
  exact lowerBlock_tie ab nm (dstStream ops) s V hinterp hfresh

/-! ## 8. Non-vacuity — a concrete decoded block lifted back

The two-op block of `JasminComRunBlockSeq` §8, lowered over concrete registers,
parses to two `RawArith` records and elaborates to a dialect program denoting
`mul (add a b) a`. -/

/-- The concrete register map for `Δ2`: `a ↦ "a"`, `b ↦ "b"`. -/
def demoρ : RegMapG Δ2 := fun v =>
  match v with
  | .here => "a"
  | .there .here => "b"

/-- The concrete fresh-name stream. `block2` allocates two destinations, so only
    indices `0` and `1` are queried; one name stands for the whole tail. -/
def demoG : Nat → String
  | 0 => "t0"
  | 1 => "t1"
  | _ + 2 => "t"

/-- The name resolution inverse to `demoρ` on the two inputs. -/
def demoFind : String → Option (Ctxt.Var Δ2 (.reg 64)) := fun r =>
  if r = "a" then some dA else if r = "b" then some dB else none

/-- The two ops the concrete lowered block decodes to. -/
def demoOps : List RawArith :=
  [⟨.add, "t0", "a", "b"⟩, ⟨.mul, "t1", "t0", "a"⟩]

/-- The concrete lowered machine block parses back to its two ops. -/
theorem demo_parse : parseBlock (lowerBlock block2 demoρ demoG) = some demoOps := by
  rfl

/-- The parsed ops elaborate to a dialect program denoting `mul (add a b) a` on a
    symbolic valuation — the same composed `JasminBinOp.apply` fold as
    `block2_denote`. -/
theorem demo_elab_denote (V : Ctxt.Valuation Δ2) :
    (elabOps demoFind demoOps "t1").map (fun ab => ab.toCom.denote V)
      = some (JasminBinOp.mul.apply
          (JasminBinOp.add.apply (dA.lookup V) (dB.lookup V)) (dA.lookup V)) := by
  rfl

end CatCrypt.Crypto.SecureCompilation.Ascent
