/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddSegments

/-!
# Cut every part check of the shipped point addition in two

For each of the ten parts this tool finds a segment boundary at which the part check splits
into two, and writes `Ed25519PointAddCutNN.lean`: the boundary certificate, the two half
checks, and `pa_partNN_of_halves`, which derives from the halves the conclusion
`partCheck2_sound` draws from the whole-part check.

A boundary is accepted when the certificate reads back to a bounded size and both halves
evaluate `true`; the middle boundary is tried first, then its neighbours. The symbolic state
holds node indices into a hash-consed table, so the certificate needs the inverse of
interning: a node that is a statement slot's reads back as that slot, where `internS`
conses so that slot `j` sits at index `n - 1 - j` of `σ`. A second half starts at the slot
one past the last its entry map mentions, since `enterF` interns an entry map with no
statements in scope.

    lake env lean scripts/cutgen/Ed25519PointAddCutAll.lean
-/

set_option autoImplicit false
set_option maxRecDepth 100000

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519PointAddShipped
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddShippedProof

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddCutAll

/-- The slot a node stands for, inverting `sget`. -/
def slotOf (σ : List Nat) (n : Nat) (j : Nat) : Option Nat :=
  match σ.idxOf? j with
  | some k => if k < n then some (n - 1 - k) else none
  | none => none

/-- The word expression a node denotes, or none at a register or cell leaf. -/
partial def weOf (T : Tb) (σ : List Nat) (n : Nat) (j : Nat) : Option WE :=
  match slotOf σ n j with
  | some s => some (.v s)
  | none =>
    match nodeAt T.nodes j with
    | some (.inp i) => some (.v i)
    | some (.lit v) => some (.lit v)
    | some (.add p q) => (weOf T σ n p).bind fun x => (weOf T σ n q).map fun y => .add x y
    | some (.sub p q) => (weOf T σ n p).bind fun x => (weOf T σ n q).map fun y => .sub x y
    | some (.and p q) => (weOf T σ n p).bind fun x => (weOf T σ n q).map fun y => .and x y
    | some (.xor p q) => (weOf T σ n p).bind fun x => (weOf T σ n q).map fun y => .xor x y
    | some (.mul p q) => (weOf T σ n p).bind fun x => (weOf T σ n q).map fun y => .mul x y
    | some (.mulhi p q) =>
        (weOf T σ n p).bind fun x => (weOf T σ n q).map fun y => .mulhi x y
    | some (.shr p k) => (weOf T σ n p).map fun x => .shr x k
    | _ => none

/-- The locations of a symbolic state that read back. -/
def mapOf (T : Tb) (σ : List Nat) (n : Nat) (S : SSt) : List (Loc × WE) :=
  (S.regs.filterMap fun p => (weOf T σ n p.2).map fun e => (Loc.reg p.1, e)) ++
    (S.mem.filterMap fun p => (weOf T σ n p.2).map fun e => (Loc.cell p.1.1 p.1.2, e))

/-- The operand locations of an instruction, in the order the packed checker's
    annotation lists them: destination first, then sources, a memory cell as its
    base and offset. `none` for an instruction the packed checker has no arm for. -/
def opLocs : JInstr 64 → Option (List Loc)
  | .mov d (.reg r) => some [.reg d, .reg r]
  | .mov d (.imm _) => some [.reg d]
  | .loadMem d b o => some [.reg d, .cell b o]
  | .storeMem b o (.reg r) => some [.cell b o, .reg r]
  | .storeMem b o (.imm _) => some [.cell b o]
  | .mulx hd ld (.reg a) (.reg b) => some [.reg hd, .reg ld, .reg a, .reg b]
  | .imul d (.reg r) => some [.reg d, .reg r]
  | .xor_ d (.reg r) => some [.reg d, .reg r]
  | .or_ d (.reg r) => some [.reg d, .reg r]
  | .cmovne d (.reg r) => some [.reg d, .reg r]
  | .adcx d (.reg r) => some [.reg d, .reg r]
  | .bt a (.imm _) => some [.reg a]
  | .setc d => some [.reg d]
  | .test a (.reg b) => some [.reg a, .reg b]
  | .adcxMem d b o => some [.reg d, .cell b o]
  | _ => none

/-- Location equality, by constructor and fields. -/
def locEq : Loc → Loc → Bool
  | .reg a, .reg b => a == b
  | .cell a o, .cell b p => a == b && o == p
  | _, _ => false

/-- Append a location unless it is already listed. -/
def addLoc (ls : List Loc) (l : Loc) : List Loc :=
  if ls.any (locEq l) then ls else ls ++ [l]

/-- The index of a location in a list, by `locEq`. -/
def locIdx (ls : List Loc) (l : Loc) : Option Nat :=
  (ls.zipIdx.find? fun p => locEq p.1 l).map (·.2)

/-- The location list of a half check and the annotation of each instruction: the
    exit map's locations first, then every operand location in order of first use, and
    for each instruction the indices of its operands. `none` when an instruction has no
    packed arm. -/
def annotate (mOut : List (Loc × WE)) (blk : List (JInstr 64)) :
    Option (List Loc × List (List Nat)) := do
  let base := mOut.foldl (fun ls p => addLoc ls p.1) []
  let ops ← blk.mapM opLocs
  let locs := ops.foldl (fun ls os => os.foldl addLoc ls) base
  let anns ← ops.mapM fun os => os.mapM (locIdx locs)
  pure (locs, anns)

/-- The greatest slot an expression mentions. -/
def maxSlot : WE → Nat
  | .v j => j
  | .lit _ => 0
  | .add a b | .sub a b | .and a b | .xor a b | .mul a b | .mulhi a b =>
      max (maxSlot a) (maxSlot b)
  | .shr a _ => maxSlot a

/-- A part check: its arguments as values and as the source text the theorems use. -/
structure Part where
  n : Nat
  a : Nat
  es : List WE
  esSrc : String
  esLen : String
  mIn : List (Loc × WE)
  mInSrc : String
  cIn : Option WE
  cInSrc : String
  zIn : Option WE
  zInSrc : String
  A : DState
  ASrc : String
  mOut : List (Loc × WE)
  mOutSrc : String
  cOut : Option WE
  cOutSrc : String
  zOut : Option WE
  zOutSrc : String

/-- The ten part checks, with the arguments `Ed25519PointAddShippedChecksA` and
    `Ed25519PointAddShippedChecksB` give them. -/
def parts : List Part :=
  [⟨1, 57, paSl1, "paSl1", "paSl1_len", paIn, "paIn", none, "none", none, "none",
     {}, "{}", paMap1, "paMap1", some (aoWE (.v 238)), "(some (aoWE (.v 238)))", none, "none"⟩,
   ⟨2, 239, paSl2, "paSl2", "paSl2_len", paMap1, "paMap1", some (aoWE (.v 238)),
     "(some (aoWE (.v 238)))", none, "none", paState 1, "(paState 1)", paMap2, "paMap2",
     none, "none", none, "none"⟩,
   ⟨3, 499, paSl3, "paSl3", "paSl3_len", paMap2, "paMap2", none, "none", none, "none",
     paState 2, "(paState 2)", paMap3, "paMap3", some (.v 761), "(some (.v 761))", none, "none"⟩,
   ⟨4, 762, paSl4, "paSl4", "paSl4_len", paMap3, "paMap3", some (.v 761), "(some (.v 761))",
     none, "none", paState 3, "(paState 3)", paMap4, "paMap4", some (.v 1019),
     "(some (.v 1019))", none, "none"⟩,
   ⟨5, 1020, paSl5, "paSl5", "paSl5_len", paMap4, "paMap4", some (.v 1019), "(some (.v 1019))",
     none, "none", paState 4, "(paState 4)", paMap5, "paMap5", some (.v 1269),
     "(some (.v 1269))", none, "none"⟩,
   ⟨6, 1270, paSl6, "paSl6", "paSl6_len", paMap5, "paMap5", some (.v 1269), "(some (.v 1269))",
     none, "none", paState 5, "(paState 5)", paMap6, "paMap6", some (aoWE (.v 1494)),
     "(some (aoWE (.v 1494)))", none, "none"⟩,
   ⟨7, 1495, paSl7, "paSl7", "paSl7_len", paMap6, "paMap6", some (aoWE (.v 1494)),
     "(some (aoWE (.v 1494)))", none, "none", paState 6, "(paState 6)", paMap7, "paMap7",
     some (.v 1747), "(some (.v 1747))", none, "none"⟩,
   ⟨8, 1748, paSl8, "paSl8", "paSl8_len", paMap7, "paMap7", some (.v 1747), "(some (.v 1747))",
     none, "none", paState 7, "(paState 7)", paMap8, "paMap8", none, "none", none, "none"⟩,
   ⟨9, 1996, paSl9, "paSl9", "paSl9_len", paMap8, "paMap8", none, "none", none, "none",
     paState 8, "(paState 8)", paMap9, "paMap9", some (aoWE (.v 2250)),
     "(some (aoWE (.v 2250)))", none, "none"⟩,
   ⟨10, 2251, paSl10, "paSl10", "paSl10_len", paMap9, "paMap9", some (aoWE (.v 2250)),
     "(some (aoWE (.v 2250)))", none, "none", paState 9, "(paState 9)", paOut, "paOut",
     none, "none", none, "none"⟩]

/-- A certificate at a boundary, with the base of the second half and the abstract state. -/
structure Cut where
  b : Nat
  locs : List (Loc × WE)
  cf : Option WE
  zf : Option WE
  base : Nat
  st : DState

/-- The certificate at segment boundary `b` of part `p`, when the run completes, the
    locations read back to a bounded size and both halves evaluate `true`. -/
def cutAt (p : Part) (b : Nat) : Option Cut := do
  let segs := paSegs p.n
  let hA := (segs.take b).flatten
  let hB := (segs.drop b).flatten
  let n := p.a + p.es.length
  let (T₀, S₀) ← enterF p.a Tb.empty {} p.mIn p.cIn p.zIn
  let (T₁, σ) ← internS p.a [] p.a T₀ p.es
  let (T₂, S₂) ← symRun2 T₁ S₀ (canonFromD shippedBank p.A hA)
  let locs := mapOf T₂ σ n S₂.base
  let cf ← match S₂.cfw with
    | none => some none
    | some x => (weOf T₂ σ n x).map some
  let zf ← match S₂.zfn with
    | none => some none
    | some x => (weOf T₂ σ n x).map some
  if (toString (repr locs)).length > 60000 then none
  let s1 := locs.foldl (fun m q => max m (maxSlot q.2)) 0
  let s2 := match cf with | some e => max s1 (maxSlot e) | none => s1
  let s3 := match zf with | some e => max s2 (maxSlot e) | none => s2
  let base := max p.a (s3 + 1)
  let k := base - p.a
  let st := runD shippedBank p.A hA
  let h1 := partCheck2 p.a (p.es.take k) p.mIn p.cIn p.zIn locs cf zf (canonFromD shippedBank p.A hA)
  let h2 := partCheck2 base (p.es.drop k) locs cf zf p.mOut p.cOut p.zOut
    (canonFromD shippedBank st hB)
  if h1 && h2 then some ⟨b, locs, cf, zf, base, st⟩ else none

/-- The boundaries of a part of `m` segments, the middle first, then outward. -/
def order (m : Nat) : List Nat :=
  let mid := m / 2
  (List.range m).filter (fun b => 0 < b ∧ b < m) |>.mergeSort
    (fun x y => (if x ≤ mid then mid - x else x - mid) ≤ (if y ≤ mid then mid - y else y - mid))

/-- The first boundary of a part that yields a certificate. -/
def findCut (p : Part) : Option Cut :=
  (order (paSegs p.n).length).findSome? (cutAt p)

/-- A two-digit part number. -/
def nn (n : Nat) : String := if n < 10 then s!"0{n}" else toString n

/-- The module text for part `p` cut at `c`. -/
def moduleText (p : Part) (c : Cut) : String :=
  let N := nn p.n
  let k := c.base - p.a
  let hA := s!"((paSegs {p.n}).take {c.b}).flatten"
  let hB := s!"((paSegs {p.n}).drop {c.b}).flatten"
  let ns := "CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddShippedProof"
  let lines : List String := [
    "/-",
    "Copyright (c) 2026 CatCrypt Contributors. All rights reserved.",
    "Released under MIT license as described in the file LICENSE.",
    "Authors: CatCrypt Contributors",
    "-/",
    "module",
    "",
    "public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddSegments",
    "",
    "/-!",
    s!"# Part {p.n} of the shipped point addition, checked in two halves",
    "",
    s!"The part check of part {p.n} reduces a symbolic run of the whole part in `decide +kernel`;",
    s!"this module checks the part as two runs, split after segment {c.b} of `paSegs {p.n}`, joined",
    s!"at the boundary certificate `paCut{N}`. The certificate is the symbolic state at the",
    "boundary, produced by `scripts/cutgen/Ed25519PointAddCutAll.lean` from the same executor",
    s!"outside the kernel. The second half starts at slot {c.base}, one past the last slot the",
    "certificate mentions.",
    "",
    "## Main results",
    "",
    s!"* `pa_part{N}a`, `pa_part{N}b`: the two half checks.",
    s!"* `pa_part{N}_of_halves`: the conclusion `partCheck2_sound` draws from the whole-part",
    "  check, derived from the two halves.",
    "-/",
    "",
    "@[expose] public section",
    "",
    "set_option autoImplicit false",
    "set_option Elab.async false",
    "set_option exponentiation.threshold 600",
    "",
    s!"namespace {ns}",
    "",
    "open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin",
    "open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem",
    "open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived",
    "open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519PointAddShipped",
    "open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof",
    "",
    s!"/-- The locations of the symbolic state after segment {c.b} of part {p.n}. -/",
    s!"def paCut{N} : List (Loc × WE) :=",
    "  " ++ toString (repr c.locs),
    "",
    "/-- The carry flag at the boundary. -/",
    s!"def paCut{N}Carry : Option WE := " ++ toString (repr c.cf),
    "",
    "/-- The zero flag at the boundary. -/",
    s!"def paCut{N}Zero : Option WE := " ++ toString (repr c.zf),
    "",
    "/-- The abstract state at the boundary. -/",
    s!"def paCut{N}State : DState :=",
    "  ⟨" ++ toString (repr c.st.entry) ++ ", " ++ toString (repr c.st.regs) ++ ", " ++
      toString (repr c.st.cells) ++ "⟩",
    "",
    (if p.n == 10 then
      "theorem paSl10_len : paSl10.length = 117 := by\n  rw [paSl10, List.length_drop, paR9_len]\n"
    else ""),
    s!"/-- The first half carries the entry of part {p.n} to the certificate. -/",
    s!"theorem pa_part{N}a :",
    s!"    partCheck2 {p.a} ({p.esSrc}.take {k}) {p.mInSrc} {p.cInSrc} {p.zInSrc} paCut{N}",
    s!"      paCut{N}Carry paCut{N}Zero (canonFromD shippedBank {p.ASrc} {hA}) = true := by",
    "  decide +kernel",
    "",
    s!"/-- The second half carries the certificate to the exit of part {p.n}. -/",
    s!"theorem pa_part{N}b :",
    s!"    partCheck2 {c.base} ({p.esSrc}.drop {k}) paCut{N} paCut{N}Carry paCut{N}Zero {p.mOutSrc}",
    s!"      {p.cOutSrc} {p.zOutSrc} (canonFromD shippedBank paCut{N}State {hB}) = true := by",
    "  decide +kernel",
    "",
    s!"/-- The two halves carry the entry of part {p.n} to its exit across the canonical block of",
    "    the whole part: the conclusion `partCheck2_sound` draws from the whole-part check. -/",
    s!"theorem pa_part{N}_of_halves (ρ : Nat → BitVec 64) (hH : Holds ρ {p.a} {p.esSrc})",
    "    (hK : ∀ j c, cK j = some c → ρ j = BitVec.ofNat 64 c)",
    s!"    (s : JState 64) (hin : MapHolds ρ {p.mInSrc} s) (hc : CfHolds ρ {p.cInSrc} s)",
    s!"    (hz : ZfHolds ρ {p.zInSrc} s) :",
    s!"    MapHolds ρ {p.mOutSrc} (runBlock s (canonFromD shippedBank {p.ASrc} (paPart {p.n}))) ∧",
    s!"      CfHolds ρ {p.cOutSrc} (runBlock s (canonFromD shippedBank {p.ASrc} (paPart {p.n}))) ∧",
    s!"      ZfHolds ρ {p.zOutSrc} (runBlock s (canonFromD shippedBank {p.ASrc} (paPart {p.n}))) := by",
    s!"  have hlen : ({p.esSrc}.take {k}).length = {k} := by",
    s!"    simp only [List.length_take, {p.esLen}]",
    "    omega",
    s!"  obtain ⟨h1, h2⟩ := (holds_append ρ ({p.esSrc}.take {k}) ({p.esSrc}.drop {k}) {p.a}).1 (by",
    "    rw [List.take_append_drop]",
    "    exact hH)",
    "  rw [hlen] at h2",
    s!"  obtain ⟨q1, c1, z1⟩ := partCheck2_sound {p.a} _ {p.mInSrc} {p.cInSrc} {p.zInSrc} paCut{N}",
    s!"    paCut{N}Carry paCut{N}Zero _ pa_part{N}a ρ h1 (fun j c _ hc => hK j c hc) s hin hc hz",
    s!"  obtain ⟨q2, c2, z2⟩ := partCheck2_sound {c.base} _ paCut{N} paCut{N}Carry paCut{N}Zero",
    s!"    {p.mOutSrc} {p.cOutSrc} {p.zOutSrc} _ pa_part{N}b ρ h2 (fun j c _ hc => hK j c hc) _ q1 c1 z1",
    s!"  have hstate : runD shippedBank {p.ASrc} {hA} = paCut{N}State := by decide +kernel",
    s!"  rw [paPart_cut {p.n} {c.b} (by decide), canonFromD_append, hstate, runBlock_cat]",
    "  exact ⟨q2, c2, z2⟩",
    "",
    s!"end {ns}",
    ""]
  String.intercalate "\n" lines

/-- Cut every part, write its module, and report the boundaries. -/
def run : IO Unit := do
  let dir := "CatCrypt/Crypto/SecureCompilation/Ascent/Demos"
  let mut missing : List Nat := []
  for p in parts do
    match findCut p with
    | none =>
      IO.println s!"part {p.n}: no boundary yields a certificate"
      missing := missing ++ [p.n]
    | some c =>
      IO.FS.writeFile s!"{dir}/Ed25519PointAddCut{nn p.n}.lean" (moduleText p c)
      IO.println s!"part {p.n}: segment {c.b} of {(paSegs p.n).length}, base {c.base}, {c.locs.length} locations"
  if !missing.isEmpty then
    throw <| IO.userError s!"no certificate for parts {missing}"

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddCutAll

#eval CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddCutAll.run
