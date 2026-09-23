/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceSegments

/-!
# Cut every part check of the shipped scalar reduction in two

For each part of `ed25519_sc_reduce` with more than one segment this tool finds a segment
boundary at which the part check splits into two, and writes `Ed25519ScReduceCutNN.lean`:
the boundary certificate, the two half checks, and `scr_partNN_of_halves`, which derives
from the halves the conclusion `partCheck_sound` draws from the whole-part check.

A boundary is accepted when the certificate reads back to a bounded size and both halves
evaluate `true`; the middle boundary is tried first, then its neighbours. The symbolic state
holds node indices into a hash-consed table, so the certificate needs the inverse of
interning: a node that is a statement slot's reads back as that slot, where `internS`
conses so that slot `j` sits at index `n - 1 - j` of `σ`. A second half starts at the slot
one past the last its entry map mentions, since `enter` interns an entry map with no
statements in scope.

    lake env lean scripts/cutgen/Ed25519ScReduceCutAll.lean
-/

set_option autoImplicit false
set_option maxRecDepth 100000

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519ScReduceShipped
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceCutAll

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
  b : Nat
  mIn : List (Loc × WE)
  mInSrc : String
  A : DState
  ASrc : String
  mOut : List (Loc × WE)
  mOutSrc : String

/-- The eight part checks, with the arguments `Ed25519ScReduceShippedProof` gives them. -/
def parts : List Part :=
  [⟨1, 16, 64, scrIn, "scrIn", {}, "{}", scrMap1, "scrMap1"⟩,
   ⟨2, 64, 116, scrMap1, "scrMap1", scrState 1, "(scrState 1)", scrMap2, "scrMap2"⟩,
   ⟨3, 116, 169, scrMap2, "scrMap2", scrState 2, "(scrState 2)", scrMap3, "scrMap3"⟩,
   ⟨4, 169, 219, scrMap3, "scrMap3", scrState 3, "(scrState 3)", scrMap4, "scrMap4"⟩,
   ⟨5, 219, 269, scrMap4, "scrMap4", scrState 4, "(scrState 4)", scrMap5, "scrMap5"⟩,
   ⟨6, 269, 320, scrMap5, "scrMap5", scrState 5, "(scrState 5)", scrMap6, "scrMap6"⟩,
   ⟨7, 320, 354, scrMap6, "scrMap6", scrState 6, "(scrState 6)", scrOut, "scrOut"⟩,
   ⟨8, 354, 354, scrOut, "scrOut", scrState 7, "(scrState 7)", scrOut, "scrOut"⟩]

/-- A certificate at a boundary, with the base of the second half and the abstract state. -/
structure Cut where
  b : Nat
  locs : List (Loc × WE)
  base : Nat
  st : DState

/-- The certificate at segment boundary `b` of part `p`, when the run completes, the
    locations read back to a bounded size and both halves evaluate `true`. -/
def cutAt (p : Part) (b : Nat) : Option Cut := do
  let segs := scrSegs p.n
  let hA := (segs.take b).flatten
  let hB := (segs.drop b).flatten
  let es := xSlice p.a p.b
  let n := p.a + es.length
  let (T₀, S₀) ← enter p.a Tb.empty {} p.mIn
  let (T₁, σ) ← internS p.a [] p.a T₀ es
  let (T₂, S₂) ← symRun T₁ S₀ (canonFromD shippedBank p.A hA)
  let locs := mapOf T₂ σ n S₂
  if (toString (repr locs)).length > 60000 then none
  let base := max p.a (locs.foldl (fun m q => max m (maxSlot q.2)) 0 + 1)
  let k := base - p.a
  let st := runD shippedBank p.A hA
  let h1 := partCheck p.a (es.take k) p.mIn locs (canonFromD shippedBank p.A hA)
  let h2 := partCheck base (es.drop k) locs p.mOut (canonFromD shippedBank st hB)
  if h1 && h2 then some ⟨b, locs, base, st⟩ else none

/-- The boundaries of a part of `m` segments, the middle first, then outward. -/
def order (m : Nat) : List Nat :=
  let mid := m / 2
  (List.range m).filter (fun b => 0 < b ∧ b < m) |>.mergeSort
    (fun x y => (if x ≤ mid then mid - x else x - mid) ≤ (if y ≤ mid then mid - y else y - mid))

/-- The first boundary of a part that yields a certificate. -/
def findCut (p : Part) : Option Cut :=
  (order (scrSegs p.n).length).findSome? (cutAt p)

/-- A two-digit part number. -/
def nn (n : Nat) : String := if n < 10 then s!"0{n}" else toString n

/-- The module text for part `p` cut at `c`. -/
def moduleText (p : Part) (c : Cut) : String :=
  let N := nn p.n
  let k := c.base - p.a
  let es := s!"(xSlice {p.a} {p.b})"
  let hA := s!"((scrSegs {p.n}).take {c.b}).flatten"
  let hB := s!"((scrSegs {p.n}).drop {c.b}).flatten"
  let ns := "CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof"
  let lines : List String := [
    "/-",
    "Copyright (c) 2026 CatCrypt Contributors. All rights reserved.",
    "Released under MIT license as described in the file LICENSE.",
    "Authors: CatCrypt Contributors",
    "-/",
    "module",
    "",
    "public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceSegments",
    "",
    "/-!",
    s!"# Part {p.n} of the shipped scalar reduction, checked in two halves",
    "",
    s!"The part check of part {p.n} reduces a symbolic run of the whole part in `decide +kernel`;",
    s!"this module checks the part as two runs, split after segment {c.b} of `scrSegs {p.n}`, joined",
    s!"at the boundary certificate `scrCut{N}`. The certificate is the symbolic state at the",
    "boundary, produced by `scripts/cutgen/Ed25519ScReduceCutAll.lean` from the same executor",
    s!"outside the kernel. The second half starts at slot {c.base}, one past the last slot the",
    "certificate mentions.",
    "",
    "## Main results",
    "",
    s!"* `scr_part{N}a`, `scr_part{N}b`: the two half checks.",
    s!"* `scr_part{N}_of_halves`: the conclusion `partCheck_sound` draws from the whole-part",
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
    "open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519ScReduceShipped",
    "",
    s!"/-- The locations of the symbolic state after segment {c.b} of part {p.n}. -/",
    s!"def scrCut{N} : List (Loc × WE) :=",
    "  " ++ toString (repr c.locs),
    "",
    "/-- The abstract state at the boundary. -/",
    s!"def scrCut{N}State : DState :=",
    "  ⟨" ++ toString (repr c.st.entry) ++ ", " ++ toString (repr c.st.regs) ++ ", " ++
      toString (repr c.st.cells) ++ "⟩",
    "",
    s!"/-- The first half carries the entry of part {p.n} to the certificate. -/",
    s!"theorem scr_part{N}a :",
    s!"    partCheck {p.a} ({es}.take {k}) {p.mInSrc} scrCut{N}",
    s!"      (canonFromD shippedBank {p.ASrc} {hA}) = true := by",
    "  decide +kernel",
    "",
    s!"/-- The second half carries the certificate to the exit of part {p.n}. -/",
    s!"theorem scr_part{N}b :",
    s!"    partCheck {c.base} ({es}.drop {k}) scrCut{N} {p.mOutSrc}",
    s!"      (canonFromD shippedBank scrCut{N}State {hB}) = true := by",
    "  decide +kernel",
    "",
    s!"/-- The two halves carry the entry of part {p.n} to its exit across the canonical block of",
    "    the whole part: the conclusion `partCheck_sound` draws from the whole-part check. -/",
    s!"theorem scr_part{N}_of_halves (ρ : Nat → BitVec 64) (hH : Holds ρ {p.a} {es})",
    "    (hK : ∀ j c, cK j = some c → ρ j = BitVec.ofNat 64 c)",
    s!"    (s : JState 64) (hin : MapHolds ρ {p.mInSrc} s) :",
    s!"    MapHolds ρ {p.mOutSrc} (runBlock s (canonFromD shippedBank {p.ASrc} (scrPart {p.n}))) := by",
    s!"  have hlen : ({es}.take {k}).length = {k} := by",
    s!"    rw [List.length_take, xSlice_length {p.a} {p.b} (by omega) (by omega) (by omega)]",
    "    omega",
    s!"  obtain ⟨h1, h2⟩ := (holds_append ρ ({es}.take {k}) ({es}.drop {k}) {p.a}).1 (by",
    "    rw [List.take_append_drop]",
    "    exact hH)",
    "  rw [hlen] at h2",
    s!"  have q1 := partCheck_sound {p.a} _ {p.mInSrc} scrCut{N} _ scr_part{N}a ρ h1",
    "    (fun j c _ hc => hK j c hc) s hin",
    s!"  have q2 := partCheck_sound {c.base} _ scrCut{N} {p.mOutSrc} _ scr_part{N}b ρ h2",
    "    (fun j c _ hc => hK j c hc) _ q1",
    s!"  have hstate : runD shippedBank {p.ASrc} {hA} = scrCut{N}State := by decide +kernel",
    s!"  rw [scrPart_cut {p.n} {c.b} (by decide), canonFromD_append, hstate, runBlock_cat]",
    "  exact q2",
    "",
    s!"end {ns}",
    ""]
  String.intercalate "\n" lines

/-- Cut every part of more than one segment, write its module, and report the boundaries. -/
def run : IO Unit := do
  let dir := "CatCrypt/Crypto/SecureCompilation/Ascent/Demos"
  let mut missing : List Nat := []
  for p in parts do
    if (scrSegs p.n).length < 2 then
      IO.println s!"part {p.n}: one segment, not cut"
    else
      match findCut p with
      | none =>
        IO.println s!"part {p.n}: no boundary yields a certificate"
        missing := missing ++ [p.n]
      | some c =>
        IO.FS.writeFile s!"{dir}/Ed25519ScReduceCut{nn p.n}.lean" (moduleText p c)
        IO.println s!"part {p.n}: segment {c.b} of {(scrSegs p.n).length}, base {c.base}, {c.locs.length} locations"
  if !missing.isEmpty then
    throw <| IO.userError s!"no certificate for parts {missing}"

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceCutAll

#eval CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceCutAll.run
