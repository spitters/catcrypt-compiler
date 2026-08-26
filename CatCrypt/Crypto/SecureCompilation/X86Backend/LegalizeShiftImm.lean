/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-!
# Shift- and rotate-immediate legalisation for the owned x86 backend

`Com.toLprogPhysAbi` emits a shift or rotate as a unary `Lopn [d] "SHR:<n>[:64]" [s]`
whose count rides in the mnemonic. The AT&T printer recognises the two-source
operand form `[d] SHR[:64] [d, #n]`, and recognises no rotate mnemonic. This
module holds the mnemonic parsers, the rotate expansion, and the body/program
traversal shared by the per-primitive emit modules.

The per-instruction rewrite is not shared. Each emit module supplies its own
`legalizeShiftImmInstr` and instantiates `legalizeBody` / `legalizeLprog` at it,
which is what lets the rewrite differ per primitive: shift-only, shift with a
rotate arm through `expandRotInPlace`, or shift with a rotate-by-zero copy.

## Main results

`parseShiftImm` returns one of four mnemonics, so the width tag of the parsed
base mnemonic is the width tag of the input; `movForShiftMnem` carries that width
tag onto the `MOV` prefixing a `d ≠ s` rewrite. `expandRotInPlace` emits four
mnemonics, each at the width it is given. The traversal results are the `flatMap`
structure of `legalizeBody` and the preserved shape of `legalizeLprog`.

## Obligations not discharged here

Preservation of the `lsemStraight` value of the program is open, and is owed per
variant rather than once, because the per-instruction rewrite is a parameter:

* a shift-only rewrite owes the store equality across the inserted `MOV`;
* a rewrite whose rotate arm calls `expandRotInPlace` additionally owes that
  `reloadScratch` (`R15`) is dead at the rewritten instruction, since the
  expansion writes it;
* a rewrite that drops a rotate by zero owes that the dropped instruction is a
  register copy.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LegalizeShiftImm

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-! ## 1. Mnemonic parsers -/

/-- Parse a unary shift-immediate mnemonic `"SHR:<n>"` / `"SHL:<n>"` (optionally
    width-tagged `":64"`) into `(baseMnem, count)`. Returns `none` for any other
    mnemonic, so every non-shift-immediate `Lopn` is left untouched. -/
def parseShiftImm (opn : String) : Option (String × Nat) :=
  let isU64 := opn.endsWith ":64"
  let core := if isU64 then String.ofList (opn.toList.dropLast.dropLast.dropLast) else opn
  match core.splitOn ":" with
  | [base, cnt] =>
      if base = "SHR" || base = "SHL" then
        match cnt.toNat? with
        | some n => some ((if isU64 then base ++ ":64" else base), n)
        | none => none
      else none
  | _ => none

/-- Parse a rotate-immediate mnemonic `"ROR:<n>"` / `"ROL:<n>"` (optionally
    width-tagged `":64"`) into `(baseDir, count, width)`, where `baseDir` is
    `"ROR"` or `"ROL"` and `width` is `64` for a `:64`-tagged op else `32`.
    Returns `none` for any other mnemonic. -/
def parseRotImm (opn : String) : Option (String × Nat × Nat) :=
  let isU64 := opn.endsWith ":64"
  let core := if isU64 then String.ofList (opn.toList.dropLast.dropLast.dropLast) else opn
  match core.splitOn ":" with
  | [base, cnt] =>
      if base = "ROR" || base = "ROL" then
        match cnt.toNat? with
        | some n => some (base, n, if isU64 then 64 else 32)
        | none => none
      else none
  | _ => none

/-- Width-tag suffix (`":64"` for 64-bit, empty for 32-bit) for a legalised
    two-source mnemonic at width `w`. -/
def wTag (w : Nat) : String := if w = 64 then ":64" else ""

/-- The `MOV` mnemonic prefixing a rewrite whose destination differs from its
    source, at the width carried by the legalised shift mnemonic `baseMnem`. -/
def movForShiftMnem (baseMnem : String) : String :=
  if baseMnem.endsWith ":64" then "MOV:64" else "MOV"

/-! ## 2. Rotate expansion -/

/-- Expand an in-place rotate of register `d` by `n` at width `w` into the
    shift-or idiom over scratch `R15`. `ror(d,n) = (d>>n)|(d<<(w-n))`;
    `rol(d,n) = ror(d, w-n)`. All four lines are printer-recognised two-source
    forms. `ii` is the carried instruction info. -/
def expandRotInPlace (ii : Nat) (d : LOperand) (dir : String)
    (n w : Nat) : List Linstr :=
  let rn := if dir = "ROL" then (w - n) % w else n % w
  let ln := (w - rn) % w
  let sh := wTag w
  let mv := if w = 64 then "MOV:64" else "MOV"
  [⟨ii, .Lopn [.reg reloadScratch] mv [d]⟩,
   ⟨ii, .Lopn [.reg reloadScratch] ("SHR" ++ sh) [.reg reloadScratch, .imm rn]⟩,
   ⟨ii, .Lopn [d] ("SHL" ++ sh) [d, .imm ln]⟩,
   ⟨ii, .Lopn [d] ("OR" ++ sh) [d, .reg reloadScratch]⟩]

/-! ## 3. Traversal -/

/-- Apply a per-instruction rewrite across a whole body. -/
def legalizeBody (step : Linstr → List Linstr) (body : Lcmd) : Lcmd :=
  body.flatMap step

/-- Apply a per-instruction rewrite to every function body of an `Lprog`. -/
def legalizeLprog (step : Linstr → List Linstr) (p : Lprog) : Lprog :=
  { p with
    lp_funcs := p.lp_funcs.map (fun (n, f) =>
      (n, { f with lfd_body := legalizeBody step f.lfd_body })) }

/-- The `Lopn` mnemonics of an instruction list, with the empty string standing
    for a non-`Lopn` instruction. -/
def opnMnemonics (c : Lcmd) : List String :=
  c.map (fun i => match i.li_i with | .Lopn _ m _ => m | _ => "")

/-! ## 4. Width results

The mnemonic a legalised shift carries determines the width of the `MOV` that
prefixes it. Emitting a bare 32-bit `MOV` where a `MOV:64` is required renders
`movl` and truncates a 64-bit value, so the width agreement is stated rather
than left to the shape of the `if`. -/

/-- `parseShiftImm` returns exactly one of the four legal shift mnemonics. -/
theorem parseShiftImm_base {opn b : String} {n : Nat}
    (h : parseShiftImm opn = some (b, n)) :
    b = "SHR" ∨ b = "SHL" ∨ b = "SHR:64" ∨ b = "SHL:64" := by
  simp only [parseShiftImm] at h
  split at h
  · split at h
    · split at h
      · rename_i hbase _ _ _
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hb, -⟩ := h
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hbase
        rcases hbase with hbase | hbase <;> subst hbase <;> subst hb <;>
          split <;> simp
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The base mnemonic `parseShiftImm` returns carries the width tag of the
    mnemonic it parsed. -/
theorem parseShiftImm_widthTag {opn b : String} {n : Nat}
    (h : parseShiftImm opn = some (b, n)) :
    b.endsWith ":64" = opn.endsWith ":64" := by
  simp only [parseShiftImm] at h
  split at h
  · split at h
    · split at h
      · rename_i hbase _ _ _
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hb, -⟩ := h
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hbase
        rcases hbase with hbase | hbase <;> subst hbase <;> subst hb <;>
          cases opn.endsWith ":64" <;> simp [String.endsWith] <;> decide
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The `MOV` prefixing a legalised shift carries the shift mnemonic's width
    tag. -/
theorem movForShiftMnem_widthTag (b : String) :
    (movForShiftMnem b).endsWith ":64" = b.endsWith ":64" := by
  unfold movForShiftMnem
  cases b.endsWith ":64" <;> simp [String.endsWith] <;> decide

/-- The `MOV` prefixing a legalised shift carries the width tag of the mnemonic
    that `parseShiftImm` accepted. -/
theorem movForShiftMnem_widthTag_of_parse {opn b : String} {n : Nat}
    (h : parseShiftImm opn = some (b, n)) :
    (movForShiftMnem b).endsWith ":64" = opn.endsWith ":64" := by
  rw [movForShiftMnem_widthTag, parseShiftImm_widthTag h]

/-- The mnemonics `expandRotInPlace` emits, in order. -/
theorem expandRotInPlace_mnemonics (ii : Nat) (d : LOperand) (dir : String)
    (n w : Nat) :
    opnMnemonics (expandRotInPlace ii d dir n w) =
      [if w = 64 then "MOV:64" else "MOV",
       "SHR" ++ wTag w, "SHL" ++ wTag w, "OR" ++ wTag w] := rfl

/-- Every mnemonic `expandRotInPlace` emits, the leading `MOV` included, carries
    the width tag of the rotate width it was given. -/
theorem expandRotInPlace_widthTag (ii : Nat) (d : LOperand) (dir : String)
    (n w : Nat) {m : String} (hm : m ∈ opnMnemonics (expandRotInPlace ii d dir n w)) :
    m.endsWith ":64" = decide (w = 64) := by
  rw [expandRotInPlace_mnemonics] at hm
  by_cases hw : w = 64
  · subst hw
    simp [wTag] at hm
    rcases hm with hm | hm | hm | hm <;> subst hm <;> simp [String.endsWith] <;> decide
  · simp [wTag, hw] at hm
    rcases hm with hm | hm | hm | hm <;> subst hm <;> simp [hw, String.endsWith] <;> decide

/-! ## 5. Traversal results -/

@[simp] theorem legalizeBody_nil (step : Linstr → List Linstr) :
    legalizeBody step [] = [] := rfl

@[simp] theorem legalizeBody_cons (step : Linstr → List Linstr)
    (i : Linstr) (c : Lcmd) :
    legalizeBody step (i :: c) = step i ++ legalizeBody step c := rfl

/-- The traversal distributes over concatenation of bodies. -/
theorem legalizeBody_append (step : Linstr → List Linstr) (c₁ c₂ : Lcmd) :
    legalizeBody step (c₁ ++ c₂) = legalizeBody step c₁ ++ legalizeBody step c₂ := by
  simp [legalizeBody, List.flatMap_append]

/-- The traversal emits exactly the instructions the rewrite emits. -/
theorem mem_legalizeBody {step : Linstr → List Linstr} {c : Lcmd} {j : Linstr} :
    j ∈ legalizeBody step c ↔ ∃ i ∈ c, j ∈ step i := by
  simp [legalizeBody]

/-- A rewrite that fires nowhere leaves the body unchanged. -/
theorem legalizeBody_id {step : Linstr → List Linstr} (h : ∀ i, step i = [i])
    (c : Lcmd) : legalizeBody step c = c := by
  induction c with
  | nil => rfl
  | cons i c ih => simp [legalizeBody_cons, h i, ih]

/-- The traversal's length is the total length of the rewrite's outputs. -/
theorem legalizeBody_length (step : Linstr → List Linstr) (c : Lcmd) :
    (legalizeBody step c).length = (c.map (fun i => (step i).length)).sum := by
  induction c with
  | nil => rfl
  | cons i c ih => simp [legalizeBody_cons, ih]

/-- A rewrite that never grows an instruction cannot grow the body. -/
theorem legalizeBody_length_le {step : Linstr → List Linstr}
    (h : ∀ i, (step i).length ≤ 1) (c : Lcmd) :
    (legalizeBody step c).length ≤ c.length := by
  induction c with
  | nil => simp
  | cons i c ih =>
      simp only [legalizeBody_cons, List.length_append, List.length_cons]
      have := h i
      omega

@[simp] theorem legalizeLprog_lp_funcs (step : Linstr → List Linstr) (p : Lprog) :
    (legalizeLprog step p).lp_funcs =
      p.lp_funcs.map (fun (n, f) => (n, { f with lfd_body := legalizeBody step f.lfd_body })) :=
  rfl

/-- The pass preserves the function table's names and their order. -/
theorem legalizeLprog_names (step : Linstr → List Linstr) (p : Lprog) :
    (legalizeLprog step p).lp_funcs.map Prod.fst = p.lp_funcs.map Prod.fst := by
  simp [legalizeLprog, List.map_map, Function.comp_def]

/-- The pass preserves the number of exported functions. -/
theorem legalizeLprog_lp_funcs_length (step : Linstr → List Linstr) (p : Lprog) :
    (legalizeLprog step p).lp_funcs.length = p.lp_funcs.length := by
  simp [legalizeLprog]

/-- The pass touches only function bodies: the program's register conventions
    and global data are carried through. -/
theorem legalizeLprog_globals (step : Linstr → List Linstr) (p : Lprog) :
    (legalizeLprog step p).lp_rip = p.lp_rip
      ∧ (legalizeLprog step p).lp_rsp = p.lp_rsp
      ∧ (legalizeLprog step p).lp_globs = p.lp_globs
      ∧ (legalizeLprog step p).lp_glob_names = p.lp_glob_names :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## 6. Recogniser pins

A shift-immediate mnemonic parses to its base mnemonic and count, keeping the
width tag; a rotate is not a shift and a shift is not a rotate; the `MOV` width
tracks the shift width; and the rotate expansion is four two-source instructions
at a single width. -/

#guard parseShiftImm "SHR:32:64" == some ("SHR:64", 32)
#guard parseShiftImm "SHL:7" == some ("SHL", 7)
#guard parseShiftImm "ROR:16:64" == none
#guard parseShiftImm "ADD:64" == none

#guard parseRotImm "ROR:16:64" == some ("ROR", 16, 64)
#guard parseRotImm "ROL:7" == some ("ROL", 7, 32)
#guard parseRotImm "SHR:32:64" == none

#guard movForShiftMnem "SHR:64" == "MOV:64"
#guard movForShiftMnem "SHR" == "MOV"

#guard opnMnemonics (expandRotInPlace 0 (.reg "RAX") "ROR" 16 64)
    == ["MOV:64", "SHR:64", "SHL:64", "OR:64"]
#guard opnMnemonics (expandRotInPlace 0 (.reg "RAX") "ROL" 7 32)
    == ["MOV", "SHR", "SHL", "OR"]

end CatCrypt.Crypto.SecureCompilation.X86Backend.LegalizeShiftImm
