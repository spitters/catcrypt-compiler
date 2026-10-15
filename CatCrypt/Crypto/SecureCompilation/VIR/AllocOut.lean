/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.WellFormedX86
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions

/-!
# `AllocOut`: the operand form of an allocated program over an instruction set

`AllocOut I P` is the form of the program `P` after register allocation over the
instruction-set data `I`: every operand of an operation is resolved over `I`
(`WellFormedX86.opResolvedI`), every operation printed in tied form by `I` has a mnemonic of
the width alphabet (`WidthAlphabet`: untagged or `:64`-tagged), and no operand names a
`tsave.*` slot or the liveness pin `%livepin`.

`exportR_alphabet` proves the alphabet clause on the region export `exportR`: its operations
carry the mnemonics `opToLinstrR` and the frames build by `withWidthTag`, so an operation that
`I` ties has a mnemonic of the alphabet whenever `I` ties neither the call and rotate
families, nor a vector mnemonic, nor a guard instruction outside the alphabet
(`ExportTieWF I`). `x86Data_exportTieWF` proves this of `x86Data`.

## Main definitions

* `WidthAlphabet`: an untagged or `:64`-tagged mnemonic.
* `TiedInAlphabet I x`: an operation `x` printed in tied form by `I` has a mnemonic of the
  alphabet.
* `AllocOutInstr I x`, `AllocOut I P`: the operand form of an instruction and of a program.
* `ExportTieWF I`: the conditions on `I` under which the export has the alphabet clause.

## Main statements

* `opResolvedI_x86` (in `WellFormedX86`): `opResolvedI x86Data = opResolved`.
* `exportR_alphabet`: every instruction of the export is `TiedInAlphabet I`
  (`AllTied I r.code`).
* `x86Data_exportTieWF`, `exportR_alphabet_x86`: the x86 data satisfy `ExportTieWF`, so the
  x86 export has the alphabet clause.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.AllocForm

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (IsaData)
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize (tieBase x86Data needsTie
  tiedBases)
open CatCrypt.Crypto.SecureCompilation.X86Backend.WellFormedX86 (opResolvedI)

/-! ## 1. The width alphabet of the tied form -/

/-- **The width alphabet**: a mnemonic that is its own base (untagged) or its base followed
    by the width tag `:64`. -/
def WidthAlphabet (opn : String) : Prop :=
  opn = tieBase opn ∨ opn = tieBase opn ++ ":64"

/-- **An operation tied over `I` lies in the alphabet**: an operation
    `Lopn dsts opn [a, b]` that `I` prints in tied form has a mnemonic of `WidthAlphabet`.
    Every other instruction satisfies it. -/
def TiedInAlphabet (I : IsaData) (x : LinstrR) : Prop :=
  ∀ (dsts : List LOperand) (opn : String) (a b : LOperand),
    x = .Lopn dsts opn [a, b] → I.tied opn b = true → WidthAlphabet opn

/-- A character list without `:` is its own `:`-free prefix. -/
theorem takeWhile_ne_colon_of_colonFree :
    ∀ {l : List Char}, ':' ∉ l → l.takeWhile (· != ':') = l
  | [], _ => rfl
  | c :: l, h => by
      have hc : c ≠ ':' := fun e => h (e ▸ List.mem_cons_self)
      rw [List.takeWhile_cons_of_pos (by simpa using hc),
        takeWhile_ne_colon_of_colonFree (fun hm => h (List.mem_cons_of_mem _ hm))]

/-- The base of a mnemonic without `:` is the mnemonic. -/
theorem tieBase_of_colonFree {s : String} (h : ':' ∉ s.toList) : tieBase s = s := by
  unfold tieBase
  rw [takeWhile_ne_colon_of_colonFree h, String.ofList_toList]

/-- The base of a mnemonic `s ++ ":" ++ t` with `s` without `:` is `s`. -/
theorem tieBase_append_colon {s : String} (t : String) (h : ':' ∉ s.toList) :
    tieBase (s ++ ":" ++ t) = s := by
  unfold tieBase
  rw [String.toList_append, String.toList_append, List.append_assoc,
    List.takeWhile_append_of_pos (fun c hc => by
      simp only [bne_iff_ne, ne_eq]; exact fun e => h (e ▸ hc))]
  rw [show ":".toList = [':'] from rfl]
  simp

/-- A width-tagged mnemonic over a base without `:` lies in the alphabet. -/
theorem widthAlphabet_withWidthTag (w : Nat) {s : String} (h : ':' ∉ s.toList) :
    WidthAlphabet (withWidthTag w s) := by
  unfold WidthAlphabet withWidthTag
  split
  · right
    have e : s ++ ":64" = s ++ ":" ++ "64" := by rw [String.append_assoc]; rfl
    rw [e, tieBase_append_colon _ h]
    exact e.symm
  · left; exact (tieBase_of_colonFree h).symm

/-- A mnemonic without `:` lies in the alphabet. -/
theorem widthAlphabet_of_colonFree {s : String} (h : ':' ∉ s.toList) : WidthAlphabet s :=
  Or.inl (tieBase_of_colonFree h).symm

/-- An instruction whose two-source operations all have mnemonics of the alphabet is
    `TiedInAlphabet I` for every `I`. -/
theorem tiedInAlphabet_of_alpha (I : IsaData) {x : LinstrR}
    (h : ∀ (dsts : List LOperand) (opn : String) (a b : LOperand),
      x = .Lopn dsts opn [a, b] → WidthAlphabet opn) : TiedInAlphabet I x :=
  fun dsts opn a b hx _ => h dsts opn a b hx

/-- An operation with a mnemonic of the alphabet is `TiedInAlphabet I`. -/
theorem tiedInAlphabet_Lopn (I : IsaData) (dsts : List LOperand) {opn : String}
    (srcs : List LOperand) (h : WidthAlphabet opn) : TiedInAlphabet I (.Lopn dsts opn srcs) :=
  tiedInAlphabet_of_alpha I fun _ _ _ _ hx => by cases hx; exact h

/-- An operation whose sources are not two is `TiedInAlphabet I`. -/
theorem tiedInAlphabet_Lopn_of_length (I : IsaData) (dsts : List LOperand) (opn : String)
    (srcs : List LOperand) (h : srcs.length ≠ 2) : TiedInAlphabet I (.Lopn dsts opn srcs) :=
  fun _ _ _ _ hx => by cases hx; exact absurd rfl h

/-! ## 2. The operand form of an allocated program -/

/-- The operands of an operation: its destinations and sources; none for every other
    instruction. -/
def lopnOperands : LinstrR → List LOperand
  | .Lopn dsts _ srcs => dsts ++ srcs
  | _ => []

/-- The names an operand mentions: the register of a register operand, the base and the
    index of a register-indexed address. -/
def operandNames : LOperand → List String
  | .reg n => [n]
  | .arr b _ => [b]
  | .arrIdx b i _ => [b, i]
  | .imm _ => []

/-- **The operand form of an allocated instruction over `I`**: every operand of an operation
    is resolved over `I`, an operation tied by `I` has a mnemonic of the alphabet, and no
    operand names a `tsave.*` slot or the liveness pin `%livepin`. -/
structure AllocOutInstr (I : IsaData) (x : LinstrR) : Prop where
  /-- Every operand of an operation is resolved over `I`. -/
  resolved : ∀ o ∈ lopnOperands x, opResolvedI I o = true
  /-- An operation tied by `I` has a mnemonic of the alphabet. -/
  tiedAlphabet : TiedInAlphabet I x
  /-- No operand names a `tsave.*` slot. -/
  noTsave : ∀ o ∈ lopnOperands x, ∀ n ∈ operandNames o, hasPrefix n "tsave." = false
  /-- No operand names the liveness pin. -/
  noLivepin : ∀ o ∈ lopnOperands x, ∀ n ∈ operandNames o, n ≠ "%livepin"

/-- **The operand form of an allocated program over `I`**: every instruction of every
    function body is `AllocOutInstr I`. -/
def AllocOut (I : IsaData) (P : Lprog) : Prop :=
  ∀ f ∈ P.lp_funcs, ∀ i ∈ f.2.lfd_body, AllocOutInstr I i.li_i

/-- At `x86Data` the operands of an `AllocOut` instruction are `opResolved`. -/
theorem AllocOutInstr.opResolved_x86 {x : LinstrR} (h : AllocOutInstr x86Data x) :
    ∀ o ∈ lopnOperands x, X86Backend.WellFormedX86.opResolved o = true := by
  intro o ho
  rw [← X86Backend.WellFormedX86.opResolvedI_x86]
  exact h.resolved o ho

/-! ## 3. The mnemonics of the export -/

/-- The bases of the call and rotate mnemonics, whose payload follows a `:`. -/
def colonFamilyBases : List String := ["CALL", "CALLW", "CALLN", "CALLNW", "ROR"]

/-- A vector mnemonic: its first character is `V` or `v`. -/
def VectorMnem (opn : String) : Prop :=
  opn.toList.head? = some 'V' ∨ opn.toList.head? = some 'v'

/-- **The conditions on `I` for the alphabet clause of the export**: `I` ties no mnemonic of
    the call and rotate families and no vector mnemonic, and the instructions of its loop
    guard and of its zero-trip guard are `TiedInAlphabet I`. -/
structure ExportTieWF (I : IsaData) : Prop where
  /-- No mnemonic of the call and rotate families is tied. -/
  untiedFamily : ∀ (opn : String) (b : LOperand), I.tied opn b = true →
    tieBase opn ∉ colonFamilyBases
  /-- No vector mnemonic is tied. -/
  untiedVector : ∀ (opn : String) (b : LOperand), I.tied opn b = true → ¬ VectorMnem opn
  /-- The loop guard lies in the alphabet. -/
  loopGuard : ∀ (ctr : String) (top : LLabel), ∀ x ∈ I.loopGuard ctr top, TiedInAlphabet I x
  /-- The zero-trip guard lies in the alphabet. -/
  zeroTripGuard : ∀ (ctr : String) (top endL : LLabel), ∀ x ∈ I.zeroTripGuard ctr top endL,
    TiedInAlphabet I x

/-- The base of `s ++ ":" ++ t ++ u` with `s` without `:` is `s`. -/
theorem tieBase_append_colon_append {s : String} (t u : String) (h : ':' ∉ s.toList) :
    tieBase (s ++ ":" ++ t ++ u) = s := by
  have e : s ++ ":" ++ t ++ u = s ++ ":" ++ (t ++ u) := by rw [String.append_assoc]
  rw [e]
  exact tieBase_append_colon _ h

/-- An operation of the call or rotate family is `TiedInAlphabet I` under `ExportTieWF I`. -/
theorem tiedInAlphabet_family {I : IsaData} (hI : ExportTieWF I) (dsts : List LOperand)
    {opn : String} (srcs : List LOperand) (h : tieBase opn ∈ colonFamilyBases) :
    TiedInAlphabet I (.Lopn dsts opn srcs) := fun _ _ _ b hx ht => by
  cases hx
  exact absurd h (hI.untiedFamily _ b ht)

/-- A vector operation is `TiedInAlphabet I` under `ExportTieWF I`. -/
theorem tiedInAlphabet_vector {I : IsaData} (hI : ExportTieWF I) (dsts : List LOperand)
    {opn : String} (srcs : List LOperand) (h : VectorMnem opn) :
    TiedInAlphabet I (.Lopn dsts opn srcs) := fun _ _ _ b hx ht => by
  cases hx
  exact absurd h (hI.untiedVector _ b ht)

/-- A mnemonic that begins with a vector mnemonic is a vector mnemonic. -/
theorem VectorMnem.append {s : String} (t : String) (h : VectorMnem s) :
    VectorMnem (s ++ t) := by
  unfold VectorMnem at *
  rw [String.toList_append, List.head?_append]
  rcases h with h | h <;> simp [h]

/-- The names of the binary operations carry no `:`. -/
theorem binOpName_colonFree (b : JasminBinOp) : ':' ∉ (binOpName b).toList := by
  cases b <;> decide

/-- The names of the comparisons carry no `:`. -/
theorem cmpName_colonFree (c : JasminCmp) : ':' ∉ (cmpName c).toList := by
  cases c <;> decide

/-- The cast mnemonics carry no `:`. -/
theorem castWMnem_colonFree (w w' : Nat) : ':' ∉ (castWMnem w w').toList := by
  unfold castWMnem
  split_ifs <;> decide

/-- The SIMD mnemonics are vector mnemonics. -/
theorem simdMnemonic_vector (op : SimdOp) : VectorMnem op.mnemonic := by
  unfold SimdOp.mnemonic
  split <;> simp [VectorMnem, String.toList_append]

/-- The YMM mnemonics are vector mnemonics. -/
theorem ymmMnemonic_vector (op : YmmDialect.YmmOp) : VectorMnem op.jasminMnemonic := by
  unfold YmmDialect.YmmOp.jasminMnemonic
  split <;> simp [VectorMnem, String.toList_append]

/-- The base of a mnemonic with the prefix `p ++ ":"`, `p` without `:`, is `p`, also under
    the width tag. -/
theorem tieBase_withWidthTag_colon (w : Nat) {p : String} (t : String) (h : ':' ∉ p.toList) :
    tieBase (withWidthTag w (p ++ ":" ++ t)) = p := by
  unfold withWidthTag
  split
  · exact tieBase_append_colon_append _ _ h
  · exact tieBase_append_colon _ h

/-- **The mnemonics of `opToLinstrR`**: under `ExportTieWF I`, the operation `opToLinstrR`
    emits on as many sources as the operation has arguments is `TiedInAlphabet I`. -/
theorem opToLinstrR_tiedInAlphabet {I : IsaData} (hI : ExportTieWF I) (op : JasminOp)
    (dst : String) (srcs : List LOperand)
    (hlen : srcs.length = (DialectSignature.sig (d := jasminDialect) op).length) :
    TiedInAlphabet I (opToLinstrR op dst srcs) := by
  cases op with
  | regArith bop w => exact tiedInAlphabet_Lopn I _ _ (widthAlphabet_withWidthTag w
      (binOpName_colonFree bop))
  | select w => exact tiedInAlphabet_Lopn I _ _ (widthAlphabet_withWidthTag w (by decide))
  | stackLoad w n =>
      dsimp only [opToLinstrR]; split <;>
        exact tiedInAlphabet_Lopn I _ _ (widthAlphabet_of_colonFree (by decide))
  | stackStore w n =>
      dsimp only [opToLinstrR]; split <;>
        exact tiedInAlphabet_Lopn I _ _ (widthAlphabet_of_colonFree (by decide))
  | castW w w' =>
      dsimp only [opToLinstrR]; split
      · exact tiedInAlphabet_Lopn I _ _ (widthAlphabet_of_colonFree (castWMnem_colonFree w w'))
      · exact tiedInAlphabet_Lopn I _ _ (widthAlphabet_of_colonFree (by split <;> decide))
  | extCall name argTys retTy =>
      dsimp only [opToLinstrR]; split
      · exact tiedInAlphabet_Lopn I _ _ (widthAlphabet_of_colonFree (by decide))
      · split
        · apply tiedInAlphabet_family hI
          simp only [encodeCallW, String.append_assoc]
          rw [show "CALLW:" = "CALLW" ++ ":" from rfl, tieBase_append_colon _ (by decide)]
          decide
        · apply tiedInAlphabet_family hI
          rw [show "CALL:" = "CALL" ++ ":" from rfl, tieBase_append_colon _ (by decide)]
          decide
  | regConst w n => exact tiedInAlphabet_Lopn I _ _ (widthAlphabet_withWidthTag w (by decide))
  | vpackZMM bop => exact tiedInAlphabet_vector hI _ _ (VectorMnem.append _ (by
      simp [VectorMnem]))
  | vpackZMMd bop => exact tiedInAlphabet_vector hI _ _ (VectorMnem.append _ (by
      simp [VectorMnem]))
  | vprordZMM n => exact tiedInAlphabet_vector hI _ _ (VectorMnem.append _ (by
      simp [VectorMnem]))
  | vpslldq n => exact tiedInAlphabet_vector hI _ _ (VectorMnem.append _ (by
      simp [VectorMnem]))
  | vpsrldq n => exact tiedInAlphabet_vector hI _ _ (VectorMnem.append _ (by
      simp [VectorMnem]))
  | vsimd op => exact tiedInAlphabet_vector hI _ _ (simdMnemonic_vector op)
  | vymm op => exact tiedInAlphabet_vector hI _ _ (ymmMnemonic_vector op)
  | mulhi w => exact tiedInAlphabet_Lopn I _ _ (widthAlphabet_withWidthTag w (by decide))
  | addCarryLo w => exact tiedInAlphabet_Lopn I _ _ (widthAlphabet_withWidthTag w (by decide))
  | addCarryHi w => exact tiedInAlphabet_Lopn I _ _ (widthAlphabet_withWidthTag w (by decide))
  | rorImm w n =>
      apply tiedInAlphabet_family hI
      rw [show "ROR:" = "ROR" ++ ":" from rfl, tieBase_withWidthTag_colon _ _ (by decide)]
      decide
  | shrImm w n =>
      exact tiedInAlphabet_Lopn_of_length I _ _ _ (by rw [hlen]; exact (by decide : 1 ≠ 2))
  | sarImm w n =>
      exact tiedInAlphabet_Lopn_of_length I _ _ _ (by rw [hlen]; exact (by decide : 1 ≠ 2))
  | shlImm w n =>
      exact tiedInAlphabet_Lopn_of_length I _ _ _ (by rw [hlen]; exact (by decide : 1 ≠ 2))
  | callN name argTys retTys =>
      dsimp only [opToLinstrR]; split
      · apply tiedInAlphabet_family hI
        simp only [encodeCallW, String.append_assoc]
        rw [show "CALLNW:" = "CALLNW" ++ ":" from rfl, tieBase_append_colon _ (by decide)]
        decide
      · apply tiedInAlphabet_family hI
        rw [show "CALLN:" = "CALLN" ++ ":" from rfl, tieBase_append_colon _ (by decide)]
        decide
  | cmp c w => exact tiedInAlphabet_Lopn I _ _ (widthAlphabet_withWidthTag w
      (cmpName_colonFree c))
  | cmpImm c w n => exact tiedInAlphabet_Lopn I _ _ (widthAlphabet_withWidthTag w
      (cmpName_colonFree c))
  | stackZero w n => exact tiedInAlphabet_Lopn I _ _ (widthAlphabet_of_colonFree (by decide))
  | stackStoreImm w n i =>
      exact tiedInAlphabet_Lopn I _ _ (widthAlphabet_of_colonFree (by decide))

/-- The resolution of an argument vector has one operand for each argument. -/
theorem exprArgs_go_length (d nArgs : Nat) (argNames : Nat → String)
    (immSlotMap : ImmSlotMap) {Γ : Ctxt jasminDialect} :
    ∀ {tys : List JasminTy} (hv : HVector (fun ty => Ctxt.Var Γ ty) tys),
      (exprArgs.go d nArgs argNames immSlotMap hv).length = tys.length
  | [], _ => by simp [exprArgs.go]
  | _ :: _, .cons _ rest => by
      show (_ :: exprArgs.go d nArgs argNames immSlotMap rest).length = _
      rw [List.length_cons, exprArgs_go_length d nArgs argNames immSlotMap rest]
      rfl

/-- **The binding instruction of the export** is `TiedInAlphabet I` under `ExportTieWF I`. -/
theorem bindOps_tiedInAlphabet {I : IsaData} (hI : ExportTieWF I) (nArgs : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t) (d : Nat) :
    ∀ x ∈ ExportRegions.bindOps nArgs e d, TiedInAlphabet I x.1 := by
  have hlen : (exprArgs d nArgs argName (fun _ => none) e).length =
      (DialectSignature.sig e.op).length := exprArgs_go_length _ _ _ _ _
  simp only [ExportRegions.bindOps, JasminLsemMem.straightOpsMem, List.mem_cons,
    List.not_mem_nil, or_false]
  rintro x rfl
  generalize exprArgs d nArgs argName (fun _ => none) e = src at hlen ⊢
  generalize e.op = op at hlen ⊢
  have hshift : ∀ (m : String) (w n : Nat) (s : LOperand), ':' ∉ m.toList →
      TiedInAlphabet I (JasminLsemShift.shiftLinstr m w (regName d) s n) := fun m w _ s hm =>
    tiedInAlphabet_Lopn I _ _ (widthAlphabet_withWidthTag w hm)
  split
  · exact opToLinstrR_tiedInAlphabet hI _ _ _ hlen
  · exact opToLinstrR_tiedInAlphabet hI _ _ _ hlen
  · exact opToLinstrR_tiedInAlphabet hI _ _ _ hlen
  · exact opToLinstrR_tiedInAlphabet hI _ _ _ hlen
  · exact opToLinstrR_tiedInAlphabet hI _ _ _ hlen
  · exact opToLinstrR_tiedInAlphabet hI _ _ _ hlen
  · dsimp only
    split
    · exact hshift _ _ _ _ (by decide)
    · exact hshift _ _ _ _ (by decide)
    · exact hshift _ _ _ _ (by decide)
    · exact opToLinstrR_tiedInAlphabet hI _ _ _ hlen

/-! ## 4. The frames of the export -/

section Frames

open ExportRegions (labelI movI movImmI guardI stageMoves commitMoves seedMoves shiftMoves
  regMoves advanceOps arrMove arrMoves ArrMove typedMoves arrParMoves ifResMoves flagWord)

variable (I : IsaData)

/-- Every instruction of a typed code is `TiedInAlphabet I`. -/
def AllTied (L : List JasminLsemMem.LinstrRM) : Prop := ∀ x ∈ L, TiedInAlphabet I x.1

variable {I}

@[simp] theorem allTied_nil : AllTied I [] := by simp [AllTied]

@[simp] theorem allTied_append (a b : List JasminLsemMem.LinstrRM) :
    AllTied I (a ++ b) ↔ AllTied I a ∧ AllTied I b := by
  simp only [AllTied, List.mem_append]
  exact ⟨fun h => ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩,
    fun h x hx => hx.elim (h.1 x) (h.2 x)⟩

@[simp] theorem allTied_cons (x : JasminLsemMem.LinstrRM) (l : List JasminLsemMem.LinstrRM) :
    AllTied I (x :: l) ↔ TiedInAlphabet I x.1 ∧ AllTied I l := by
  simp [AllTied]

@[simp] theorem movI_tied (dst : String) (src : LOperand) : TiedInAlphabet I (movI dst src).1 :=
  tiedInAlphabet_Lopn I _ _ (widthAlphabet_withWidthTag 64 (by decide))

@[simp] theorem movImmI_tied (dst : String) (k : Nat) : TiedInAlphabet I (movImmI dst k).1 :=
  movI_tied dst _

@[simp] theorem labelI_tied (l : LLabel) : TiedInAlphabet I (labelI l).1 :=
  fun _ _ _ _ hx => nomatch hx

/-- A list of copies is `AllTied I`. -/
theorem allTied_map_movI {α : Type} (l : List α) (f : α → String) (g : α → LOperand) :
    AllTied I (l.map fun p => movI (f p) (g p)) := by
  intro x hx
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hx
  exact movI_tied _ _

@[simp] theorem stageMoves_tied (D : Nat) (ops : List LOperand) :
    AllTied I (stageMoves D ops) := allTied_map_movI _ _ _

@[simp] theorem commitMoves_tied (D : Nat) (tgts : List String) :
    AllTied I (commitMoves D tgts) := allTied_map_movI _ _ _

@[simp] theorem parMoves_tied (D : Nat) (tgts : List String) (ops : List LOperand) :
    AllTied I (ExportRegions.parMoves D tgts ops) := by
  simp [ExportRegions.parMoves]

@[simp] theorem seedMoves_tied (car : List String) (ops : List LOperand) :
    AllTied I (seedMoves car ops) := allTied_map_movI _ _ _

@[simp] theorem shiftMoves_tied (d nCar : Nat) : AllTied I (shiftMoves d nCar) :=
  allTied_map_movI _ _ _

@[simp] theorem regMoves_tied (mv : List (String × String)) : AllTied I (regMoves mv) :=
  allTied_map_movI _ _ _

@[simp] theorem advanceOps_tied (idx ctr : String) : AllTied I (advanceOps idx ctr) := by
  simp only [advanceOps, allTied_cons, allTied_nil, and_true]
  exact ⟨tiedInAlphabet_Lopn I _ _ (widthAlphabet_withWidthTag 64 (by decide)),
    tiedInAlphabet_Lopn I _ _ (widthAlphabet_withWidthTag 64 (by decide))⟩

@[simp] theorem arrMoves_tied (z t : String) (mv : List ArrMove) :
    AllTied I (arrMoves z t mv) := by
  intro x hx
  obtain ⟨a, -, hx⟩ := List.mem_flatMap.mp hx
  simp only [arrMove, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;>
    exact tiedInAlphabet_Lopn I _ _ (widthAlphabet_of_colonFree (by decide))

@[simp] theorem typedMoves_tied (z t : String) (tp : List (JasminTy × String × String)) :
    AllTied I (typedMoves z t tp) := by
  simp [typedMoves]

@[simp] theorem arrParMoves_tied (z t : String) (D : Nat) (mv : List ArrMove) :
    AllTied I (arrParMoves z t D mv) := by
  unfold arrParMoves; split <;> simp

@[simp] theorem ifResMoves_tied (rs : List JasminTy) (d D : Nat) (ops : List LOperand) :
    AllTied I (ifResMoves rs d D ops) := by
  unfold ifResMoves; split <;> simp

@[simp] theorem flagWord_tied (r z : String) (op : LOperand) : AllTied I (flagWord I r z op) := by
  unfold flagWord
  split
  · split
    · simp only [allTied_cons, allTied_nil, movImmI_tied, true_and, and_true]
      exact tiedInAlphabet_Lopn_of_length I _ _ _ (by simp)
    · simp
  · simp

/-- The instructions of the loop guard of `I` are `AllTied I` under `ExportTieWF I`. -/
theorem loopGuard_tied (hI : ExportTieWF I) (ctr : String) (top : LLabel) :
    AllTied I ((I.loopGuard ctr top).map guardI) := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
  exact hI.loopGuard ctr top g hg

/-- The instructions of the zero-trip guard of `I` are `AllTied I` under `ExportTieWF I`. -/
theorem zeroTripGuard_tied (hI : ExportTieWF I) (ctr : String) (top endL : LLabel) :
    AllTied I ((I.zeroTripGuard ctr top endL).map guardI) := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
  exact hI.zeroTripGuard ctr top endL g hg

/-- The shadow instruction of a call is `TiedInAlphabet I` under `ExportTieWF I`. -/
theorem callI_tied (hI : ExportTieWF I) (dst f : String) (srcs : List LOperand) :
    TiedInAlphabet I (ExportRegions.callI dst f srcs).1 := by
  apply tiedInAlphabet_family hI
  show tieBase ("CALL:" ++ f) ∈ colonFamilyBases
  rw [show "CALL:" = "CALL" ++ ":" from rfl, tieBase_append_colon _ (by decide)]
  decide

end Frames

open ExportRegions in
/-- **The export emits only tied mnemonics of the width alphabet**: under `ExportTieWF I`,
    every instruction of the region export `exportR` is `TiedInAlphabet I`. -/
theorem exportR_alphabet {I : IsaData} (hI : ExportTieWF I) (nArgs : Nat) (fn : String)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) :
    ∀ (d n : Nat) (r : Exported), exportR nArgs fn p d n I = some r → AllTied I r.code := by
  induction p with
  | ret vs =>
      intro d n r h
      simp only [exportR, Option.some.injEq] at h
      subst h; exact allTied_nil
  | var e k ih =>
      intro d n r h
      simp only [exportR, Option.map_eq_some_iff] at h
      obtain ⟨rk, hk, rfl⟩ := h
      simp only [Exported.prepend, allTied_append]
      exact ⟨bindOps_tiedInAlphabet hI nArgs e d, ih _ _ _ hk⟩
  | forLoop count inits body k ihb ihk =>
      intro d n r h
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hk, rfl⟩ := h
      simp [Exported.prepend, forArrFrame, ihb _ _ _ hb, ihk _ _ _ hk,
        loopGuard_tied hI, zeroTripGuard_tied hI]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro d n r h
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨t, ht, e, he, rk, hk, rfl⟩ := h
      simp [Exported.prepend, ifFrame, iht _ _ _ ht, ihe _ _ _ he, ihk _ _ _ hk,
        loopGuard_tied hI, zeroTripGuard_tied hI]
  | whileLoop inits body k ihb ihk =>
      intro d n r h
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hk, rfl⟩ := h
      simp [Exported.prepend, whileFrame, ihb _ _ _ hb, ihk _ _ _ hk, loopGuard_tied hI]
  | call f args k ih =>
      intro d n r h
      obtain ⟨-, rk, hk, rfl⟩ := exportR_call_eq_some.mp h
      simp [Exported.prepend, ih _ _ _ hk, callI_tied hI]

/-! ## 5. The x86 instance -/

/-- A mnemonic with a non-empty base begins with the first character of its base. -/
theorem head?_eq_of_tieBase {opn : String} (h : (tieBase opn).toList ≠ []) :
    opn.toList.head? = (tieBase opn).toList.head? := by
  unfold tieBase at *
  rw [String.toList_ofList] at *
  cases hl : opn.toList with
  | nil => rw [hl] at h; simp at h
  | cons a t =>
      rw [hl] at h
      rw [List.takeWhile_cons] at *
      split at h
      · rename_i ha; simp [ha]
      · simp at h

/-- The bases that x86 prints in tied form. -/
def x86TiedBases : List String := tiedBases ++ ["SHL", "SHR", "SAR"]

/-- A mnemonic that x86 ties has its base in `x86TiedBases`. -/
theorem tieBase_mem_of_needsTie {opn : String} {b : LOperand} (h : needsTie opn b = true) :
    tieBase opn ∈ x86TiedBases := by
  unfold needsTie at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at h
  simp only [x86TiedBases, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  rcases h with h | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr (by rcases h with (h | h) | h <;> simp [h])

/-- **The x86 data satisfy `ExportTieWF`.** -/
theorem x86Data_exportTieWF : ExportTieWF x86Data where
  untiedFamily opn b h := by
    have hm := tieBase_mem_of_needsTie h
    generalize tieBase opn = s at hm ⊢
    revert s
    decide
  untiedVector opn b h := by
    have hm := tieBase_mem_of_needsTie h
    have hall : ∀ s ∈ x86TiedBases, s.toList ≠ [] ∧ s.toList.head? ≠ some 'V' ∧
        s.toList.head? ≠ some 'v' := by decide
    obtain ⟨hne, hV, hv⟩ := hall _ hm
    unfold VectorMnem
    rw [head?_eq_of_tieBase hne]
    exact fun h' => h'.elim hV hv
  loopGuard ctr top x hx := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact tiedInAlphabet_Lopn _ _ _ (widthAlphabet_withWidthTag 64 (by decide))
    · exact fun _ _ _ _ h => nomatch h
  zeroTripGuard ctr top endL x hx := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact tiedInAlphabet_Lopn _ _ _ (widthAlphabet_withWidthTag 64 (by decide))
    · exact fun _ _ _ _ h => nomatch h

/-- The x86 region export emits only tied mnemonics of the width alphabet. -/
theorem exportR_alphabet_x86 (nArgs : Nat) (fn : String) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (d n : Nat)
    (r : ExportRegions.Exported) (h : ExportRegions.exportR nArgs fn p d n x86Data = some r) :
    AllTied x86Data r.code :=
  exportR_alphabet x86Data_exportTieWF nArgs fn p d n r h

end CatCrypt.Crypto.SecureCompilation.VIR.AllocForm
