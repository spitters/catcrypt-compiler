/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked
import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegionsAbi
import CatCrypt.Crypto.SecureCompilation.Haxc.RegionBackend
import CatCrypt.Crypto.SecureCompilation.X86Backend.LinkShapeComplete

/-!
# Reasons for a refusal by the checks of the region back half

Each function returns a short string naming the first component of a check that is `false`,
in the order of the definition of the check, by evaluating the sub-functions of the check on
the same arguments.

## Main definitions

* `instrStr`: a rendering of a linear instruction (mnemonic, operand shapes, the bit length
  of each immediate).
* `ownedWhy outs B B'`: the first component of `ownedCheckMC outs B B'` that is `false`: an
  absent control-flow graph, an empty body, the block counts, the first block pair whose
  terminators differ or whose check `blockOkR` is `false` with the sub-check (`guardsT`,
  `termAgreeT`, `exitAgreeT` with the register, flag or array compared, the pairing
  facts `pairingStr` of the two exit states and the instructions of the two blocks, each
  list cut after sixty-four), the first
  instruction of the block outside the symbolic step, or the first block whose index
  obligations `oblOk` are not met.
* `idxWhy entry ann B`: the first component of `idxInvCheckB entry ann B` that is `false`:
  the first block `blockInvOk` refuses with the facts of the annotation and the index
  obligation that does not follow from them, or the entry facts.
* `narrowWhy body`: the first conjunct of `printedAddrB body` that is `false`, with the
  index and the rendering of the first instruction `instrOKB` refuses, the arm `classifyA`
  reads it into, and the value of `instrOKWB` on it.
* `wideWhy body`: the first conjunct of `printedAddrWB body` that is `false`, or the first
  cell access of `body`.
* `printedWhy body`: the reason `body` is outside both classes of the printed-body check of
  the region back half, `narrowWhy body` followed by `wideWhy body`.
* `callClassWhy G body`, `callGateWhy frame slotArr body`, `bitsDeadWhy frame D body`: the first
  part refused of the class, the gate and the check of the width analysis of a calling body.
* `exportableWhy p`: the first node of `p`, in the order of `regionExportableB`, at which
  the test is `false`: a binding with its operation, a `whileLoop` with a carried type that
  is an array, or a call.
* `coCfgWhy σ body L obs`: the first component of `coCfgB σ body L obs` that is `false`:
  the observed names not live at the end, or the first position `coInstrB` refuses with
  the rendering of its instruction and the sub-checks `coInstrWhy` that are `false`.
* `regCoWhy τ pre C L AN`: the first component of `regCoB τ pre C L AN` that is `false`.
* `regionMergeWhy d`: the synthesised merge pairs of the parts `d` of the reference and,
  when their check refuses them, the reason `regCoWhy`.
* `regionNopWhy d`: the part of `regionNopB d` that is `false`.
* `imgWhy sl R outs body`: the part of `regionImgB sl R outs body` that is `false`, after
  the printed class of `body`, read at the cell body of `body`: the first instruction
  `instrGateB` refuses, and for a body outside `printedAddrB` or with cells the values of
  the cell checks and the first instruction `instrGateBW` refuses with the width analysis
  there, or the observed names `retOutsB` finds in the analysis at the return.
* `imgGateWhyW frame slotArr body`: the first part of `imgGateBW frame slotArr body` that is
  `false`, in one pass over the body: the first instruction the instruction gate refuses
  (`gateFirstW`) with its position, its rendering, the width analysis there and the conjunct
  of `gateAtW` that is `false` with the values it compares (`gateAtWWhy`), else a last
  instruction that is no return, else the first reload `reloadSavedB` refuses
  (`reloadSavedWhy`).
* `fuseOKWhy E L c`: the first instruction or position at which the fusion check `fuseOKL`
  is `false`.
* `regionCoWhy stage σ nm body t code res`: the reason for a refusal of `regionCoB` at the
  stages `coClass`, `coCfgB`, `coEntryFix`, `renB`, `coResultName`, `coResultCopy`,
  `regMerge`, `regionNopB`, `fuseOKL`, `fuseResultName`, `regionFoldB`, `ownedCheckMC`,
  `regionPrintedB`, `idxInvCheckB`, `regionImgB`, `cellNamesRB` and `cellRegions` of
  `regionCoStage`.
* `linkFormWhy b`: the first instruction of `b` without a link form
  (`LinkShapeComplete.linkFormB`) and the first conjunct of the link form it fails.
* `calleeLinkWhy T b`: the first component of `calleeLinkB T b` that is `false`: a function of
  the table with empty code, the link forms (`linkFormWhy`), the first instruction without a
  computed shape, or
  the branch check and the program of the items.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RegionDiag

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (LOperand LinstrR Linstr Lcmd)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions (regVar? bindMemNB
  isRegTy)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM MemTag)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG (Term Block CFG cfgOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV (STerm SArr SSt SOut SG Tbl TEnt tRun
  symRun bodyAt okIn okInT okInAT okInFT okInGT normGT guardsT termAgreeT exitAgreeT arrAgreeT
  blockOkR runsOf liveIter)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked (symObl oblOk)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeLayout (decodableLcmd)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (isRetB gpOk)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (AArm classifyA)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (instrOKB condPrevB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW (instrOKWB carryPrevB
  castPosB)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem (cellA?)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (Params)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment (opMemB)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (LLabel)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (storeStruct? zeroStruct?)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (findLabelMem)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (cmpArgs? movRegArgs?
  flagCondCC? carryArgs? wideArgs?)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (mulxFree)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (clsB)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (arrReads arrWrite
  chainAlias chainAliasO)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg (subB coInstrB renArr
  arrShapeB plainArrB coArrStepB callTagB)

/-! ## 1. Renderings -/

/-- The shape of an operand: a register with its name, an array element at a constant
    offset, an immediate with its value and bit length, or an indexed array element. -/
def operandStr : LOperand → String
  | .reg n => s!"reg {n}"
  | .arr b i => s!"arr {b}[{i}]"
  | .imm k => s!"imm {k} ({(Nat.toDigits 2 k).length} bits)"
  | .arrIdx b i s => s!"idx ({b};{i};{s})"

/-- The names of the registers an operand reads or writes. -/
def operandNames : LOperand → List String
  | .reg n => [n]
  | .arr b _ => [b]
  | .imm _ => []
  | .arrIdx b i _ => [b, i]

/-- A rendering of a linear instruction: for an `Lopn` the mnemonic with the shapes of the
    destinations and of the sources, else the constructor with its label. -/
def instrStr : LinstrR → String
  | .Lopn ds m ss =>
      s!"{m} [{"; ".intercalate (ds.map operandStr)}] <- [{"; ".intercalate (ss.map operandStr)}]"
  | .Lsyscall n => s!"Lsyscall {n}"
  | .Lcall _ t => s!"Lcall {t.1}"
  | .Lret => "Lret"
  | .Lalign => "Lalign"
  | .Llabel _ l => s!"Llabel {l}"
  | .Lgoto t => s!"Lgoto {t.2}"
  | .Ligoto t => s!"Ligoto {operandStr t}"
  | .LstoreLabel d l => s!"LstoreLabel {d} {l}"
  | .Lcond c l => s!"Lcond {operandStr c} {l}"

/-- The names of an `Lopn` that are no general-purpose register names. -/
def slotNames : LinstrR → List String
  | .Lopn ds _ ss => (((ds ++ ss).flatMap operandNames).filter fun n => !gpOk n).eraseDups
  | _ => []

/-- A rendering of a memory tag. -/
def tagStr : MemTag → String
  | .reg none => "reg"
  | .reg (some w) => s!"reg cast {w}"
  | .load w n => s!"load {w} {n}"
  | .store w n => s!"store {w} {n}"
  | .loadC => "loadC"
  | .storeC => "storeC"
  | .zero w n => s!"zero {w} {n}"
  | .storeImm w n => s!"storeImm {w} {n}"

/-- A rendering of a tagged instruction. -/
def taggedStr (i : LinstrRM) : String := s!"{instrStr i.1} tag {tagStr i.2}"

/-- A rendering of a terminator. -/
def termStr : Term → String
  | .fall nx => s!"fall {nx}"
  | .goto t => s!"goto {t}"
  | .cond t nx => s!"cond {t} {nx}"
  | .ret => "ret"

/-- The name of an operation of `jasminDialect` with its widths. -/
def jasOpStr : JasminOp → String
  | .regArith op w => s!"regArith {reprStr op} {w}"
  | .stackLoad w n => s!"stackLoad {w} {n}"
  | .stackStore w n => s!"stackStore {w} {n}"
  | .castW w w' => s!"castW {w} {w'}"
  | .extCall f _ _ => s!"extCall {f}"
  | .regConst w n => s!"regConst {w} {n}"
  | .mulhi w => s!"mulhi {w}"
  | .addCarryLo w => s!"addCarryLo {w}"
  | .addCarryHi w => s!"addCarryHi {w}"
  | .rorImm w n => s!"rorImm {w} {n}"
  | .shrImm w n => s!"shrImm {w} {n}"
  | .sarImm w n => s!"sarImm {w} {n}"
  | .shlImm w n => s!"shlImm {w} {n}"
  | .select w => s!"select {w}"
  | .callN f _ _ => s!"callN {f}"
  | .cmp c w => s!"cmp {reprStr c} {w}"
  | .cmpImm c w n => s!"cmpImm {reprStr c} {w} {n}"
  | _ => "vector operation"

/-- A rendering of a type of `jasminDialect`. -/
def jasTyStr : JasminTy → String
  | .reg w => s!"reg {w}"
  | .stackArr w n => s!"stackArr {w} {n}"
  | .inlineInt => "inlineInt"
  | .bool => "bool"

/-! ## 2. The register allocation check -/

/-- The first instruction of `xs` at which the symbolic run `tRun` from the start state over
    the table `T0` stops: its index, the instruction, and whether the step always fails
    (`true`) or is outside the fragment of the symbolic step (`false`). -/
def stuckAt (xs : List LinstrRM) (T0 : Tbl) : Option (Nat × LinstrRM × Bool) :=
  (List.range xs.length).findSome? fun n =>
    match (tRun (xs.take (n + 1)) SSt.start T0).2, xs[n]? with
    | .fail, some i => some (n, i, true)
    | .unk, some i => some (n, i, false)
    | _, _ => none

/-- A rendering of the result of `stuckAt` on the instructions of a block that starts at the
    index `start` of the body named `side`. -/
def stuckStr (side : String) (start : Nat) : Option (Nat × LinstrRM × Bool) → String
  | some (n, i, f) =>
      s!"{side} instruction {start + n} (offset {n} in the block) " ++
        (if f then "always fails" else "outside symStep") ++ s!": {taggedStr i}"
  | none => s!"{side} run stops at no instruction"

/-- The kind of a guard. -/
def guardKind : SG → String
  | .wid _ w => s!"width {w}"
  | .eqW _ _ => "equal widths"
  | .shp _ w n => s!"array shape {w} {n}"

/-- The first component of `guardsT E n gs gs'` that is `false`. -/
def guardsWhy (E : Array TEnt) (n : List String × Bool) (gs gs' : List SG) : String :=
  if (gs ++ gs').all (SG.refsLt E.size) = false then
    "guardsT: a guard refers outside the term table"
  else
    match (normGT E gs').zipIdx.find? fun p =>
        !((normGT E gs).contains p.1 && okInGT E n p.1) with
    | some (g, i) =>
        s!"guardsT: guard {i} ({guardKind g}) of the {(normGT E gs').length} of the allocated " ++
          "block " ++
          (if (normGT E gs).contains g then "reads a name not live at the block start"
           else s!"is none of the {(normGT E gs).length} guards of the reference block")
    | none => "guardsT"

/-- The first `k` entries of `xs` separated by `sep`, followed by the count of the entries
    left out. -/
def boundedStr (k : Nat) (sep : String) (xs : List String) : String :=
  sep.intercalate (xs.take k) ++
    (if xs.length ≤ k then "" else s!"{sep}(+{xs.length - k} more)")

/-- A rendering of a symbolic word or a symbolic array to the depth `d`, with an entry of
    the term table `E` replaced by its node; `..` below the depth. -/
def symStr (E : Array TEnt) : Nat → STerm ⊕ SArr → String
  | 0, _ => ".."
  | d + 1, .inl t =>
      let w := fun (x : STerm) => symStr E d (.inl x)
      match t with
      | .reg r => r
      | .immW wd k => s!"{k}:{wd}"
      | .immAt k x => s!"{k}@{w x}"
      | .bin m x y => s!"{m}({w x},{w y})"
      | .un m x => s!"{m}({w x})"
      | .shImm m k x => s!"{m}{k}({w x})"
      | .aget a wd k i => s!"{symStr E d (.inr a)}[{w i}]:{wd}x{k}"
      | .cin ofl => if ofl then "OF0" else "CF0"
      | .aluF _ ofl x y _ => s!"aluF{if ofl then "o" else "c"}({w x},{w y})"
      | .carryW _ x y c => s!"carryW({w x},{w y},{w c})"
      | .carryF _ ofl x y c => s!"carryF{if ofl then "o" else "c"}({w x},{w y},{w c})"
      | .mulx hi x y => s!"mulx{if hi then "hi" else "lo"}({w x},{w y})"
      | .setcc _ x y => s!"setcc({w x},{w y})"
      | .cout sub x y c => s!"{if sub then "bout" else "cout"}({w x},{w y},{w c})"
      | .sel x y c => s!"sel({w x},{w y},{w c})"
      | .ref k =>
          match E[k]? with
          | some e => symStr E d (.inl e.node)
          | none => s!"#{k}"
  | d + 1, .inr a =>
      match a with
      | .cell r => r
      | .zero w n => s!"zero:{w}x{n}"
      | .aset b wd k i v =>
          s!"{symStr E d (.inr b)}[{symStr E d (.inl i)}:={symStr E d (.inl v)}]:{wd}x{k}"

/-- The facts on a block pair that decide whether a renaming of the reference names makes
    the exit states `ss` (reference) and `ss'` (allocated) agree, as parts separated by
    ` || `, each list cut after twelve entries:

    * `live`: for each successor `j` of `T`, the names `(L j).1` and whether the flags are
      live (`+flags`);
    * `ref=>img`: for each reference name (a name live at a successor, an output name when
      `T` halts, or a name the reference block writes, the last marked `*`), the allocated
      names `y` with `ss'.regs y == ss.regs x`, or `-` with the reference term when there is
      none. The allocated names searched are those the allocated block writes, the live
      names, the output names and the names the reference block writes;
    * `img unpaired`: the names the allocated block writes that are live at a successor and
      whose exit term is the exit term of no reference name, each with its term;
    * `arrays`: the array names each block writes, and for each array the reference block
      writes the names `q'` whose allocated array is the reference array of `q` or has its
      normal form `SArr.nfT` under the guards `gs'`, `gs` of the two blocks;
    * `injective`: `yes` when assigning each reference name with a partner its first
      partner not yet assigned leaves none without one; else the reference names left
      without one, each with its partners. -/
def pairingStr (E : Array TEnt) (outs : List String) (L : Nat → List String × Bool)
    (T : Term) (ss ss' : SSt) (gs gs' : List SG) : String :=
  let cut := boundedStr 12
  let liveAll := (T.succs.flatMap fun j => (L j).1).eraseDups
  let outN := if T.halts then outs else []
  let xs := (liveAll ++ outN ++ ss.wr).eraseDups
  let ys := (ss'.wr ++ liveAll ++ outN ++ ss.wr).eraseDups
  let partners := fun (x : String) => ys.filter fun y => ss'.regs y == ss.regs x
  let liveStr := cut " " (T.succs.map fun j =>
    s!"s{j}=[{cut " " (L j).1}]" ++ (if (L j).2 then "+flags" else ""))
  let pairStr := cut "; " (xs.map fun x =>
    let ps := partners x
    s!"{x}{if ss.wr.contains x then "*" else ""}=>" ++
      (if ps.isEmpty then "- {" ++ symStr E 3 (.inl (ss.regs x)) ++ "}" else cut "," ps))
  let lone := (ss'.wr.eraseDups.filter fun y =>
    liveAll.contains y && !xs.any fun x => ss.regs x == ss'.regs y)
  let loneStr := cut "; " (lone.map fun y => y ++ " {" ++ symStr E 3 (.inl (ss'.regs y)) ++ "}")
  let aqs := ss.awr.eraseDups
  let aqs' := (ss'.awr ++ ss.awr).eraseDups
  let arrStr := s!"ref [{cut " " aqs}] img [{cut " " ss'.awr.eraseDups}]" ++
    (if aqs.isEmpty then "" else "; " ++ cut "; " (aqs.map fun q =>
      let ps := aqs'.filter fun q' => ss'.arrs q' == ss.arrs q
        || (ss'.arrs q').nfT E gs' == (ss.arrs q).nfT E gs
      s!"{q}=>" ++ (if ps.isEmpty then "- {" ++ symStr E 3 (.inr (ss.arrs q)) ++ "}"
        else cut "," ps)))
  let greedy := xs.foldl (fun (acc : List String × List String) x =>
    let ps := partners x
    if ps.isEmpty then acc
    else
      match ps.find? fun y => !acc.1.contains y with
      | some y => (y :: acc.1, acc.2)
      | none => (acc.1, acc.2 ++ [s!"{x} (partners {cut "," ps} taken)"])) ([], [])
  let injStr := if greedy.2.isEmpty then "yes" else "no: " ++ cut "; " greedy.2
  s!"live: {liveStr} || ref=>img: {pairStr} || img unpaired: [{loneStr}] || " ++
    s!"arrays: {arrStr} || injective: {injStr}"

/-- The first component of `exitAgreeT E outs L n T ss ss' gs gs'` that is `false`: the
    register live at a successor, the flag live at a successor or the output register whose
    symbolic values differ or read a name not live at the block start, or the written array
    that `arrAgreeT` refuses: its two symbolic arrays differ and so do their normal forms
    `SArr.nfT`, or they read a name not live at the block start. For a register, whether
    each block writes it. -/
def exitFirstWhy (E : Array TEnt) (outs : List String) (L : Nat → List String × Bool)
    (n : List String × Bool) (T : Term) (ss ss' : SSt) (gs gs' : List SG) : String :=
  let regWhy (r : String) : String :=
    if ss.regs r == ss'.regs r then "reads a name not live at the block start"
    else s!"differs (written by the reference block: {ss.wr.contains r}; by the allocated " ++
      s!"block: {ss'.wr.contains r})"
  let succWhy : Option String := T.succs.findSome? fun j =>
    match (L j).1.find? fun r => !(ss.regs r == ss'.regs r && okInT E n (ss.regs r)) with
    | some r => some s!"exitAgreeT: register {r} live at successor {j} {regWhy r}"
    | none =>
        if (L j).2 = false then none
        else if (ss.zf == ss'.zf) = false then
          some s!"exitAgreeT: zero flag live at successor {j} differs"
        else if okInFT E n ss.zf = false then
          some s!"exitAgreeT: zero flag live at successor {j} reads a name not live"
        else if (ss.cf == ss'.cf) = false then
          some s!"exitAgreeT: carry flag live at successor {j} differs"
        else if okInT E n ss.cf = false then
          some s!"exitAgreeT: carry flag live at successor {j} reads a name not live"
        else if (ss.of == ss'.of) = false then
          some s!"exitAgreeT: overflow flag live at successor {j} differs"
        else if okInT E n ss.of = false then
          some s!"exitAgreeT: overflow flag live at successor {j} reads a name not live"
        else none
  match succWhy with
  | some s => s
  | none =>
      match (if T.halts then
          outs.find? fun r => !(ss.regs r == ss'.regs r && okInT E n (ss.regs r))
        else none) with
      | some r => s!"exitAgreeT: output register {r} {regWhy r}"
      | none =>
          match (ss.awr ++ ss'.awr).find? fun q =>
              !arrAgreeT E n gs gs' (ss.arrs q) (ss'.arrs q) with
          | some q =>
              s!"exitAgreeT: written array {q} " ++
                (if ss.arrs q == ss'.arrs q
                    || (ss.arrs q).nfT E gs == (ss'.arrs q).nfT E gs' then
                  "reads a name not live at the block start"
                 else s!"differs, also in normal form (written by the reference block: " ++
                   s!"{ss.awr.contains q}; by the allocated block: {ss'.awr.contains q})")
          | none => "exitAgreeT"

/-- `exitFirstWhy E outs L n T ss ss' gs gs'` followed, after ` || `, by the pairing facts
    `pairingStr E outs L T ss ss' gs gs'` of the block pair. -/
def exitWhy (E : Array TEnt) (outs : List String) (L : Nat → List String × Bool)
    (n : List String × Bool) (T : Term) (ss ss' : SSt) (gs gs' : List SG) : String :=
  exitFirstWhy E outs L n T ss ss' gs gs' ++ " || " ++ pairingStr E outs L T ss ss' gs gs'

/-- The first component of the check of the block pair `k` in `ownedCheckWithR` that is
    `false`, for the graphs `G`, `G'`, the shared runs `R` and the live sets `L`; `none`
    when the pair passes. -/
def blockWhy (outs : List String) (L : Nat → List String × Bool) (B B' : List LinstrRM)
    (G G' : CFG) (R : Array (Tbl × SOut × SOut)) (k : Nat) : Option String :=
  let b := G.blk k
  let b' := G'.blk k
  let T := b.term
  if (T == b'.term) = false then
    some s!"terminators differ: reference {termStr T}, allocated {termStr b'.term}"
  else
    match R[k]? with
    | none => some "no shared run"
    | some r =>
        if blockOkR outs L k T r B B' b b' then none
        else
          match r.2.1, r.2.2 with
          | .ok ss gs, .ok ss' gs' =>
              if guardsT r.1.ents (L k) gs gs' = false then
                some (guardsWhy r.1.ents (L k) gs gs')
              else if termAgreeT r.1.ents T (L k) ss ss' B[b.stop - 1]? B'[b'.stop - 1]?
                  = false then
                some (s!"termAgreeT: reference " ++
                  ((B[b.stop - 1]?).map taggedStr).getD "none" ++ "; allocated " ++
                  ((B'[b'.stop - 1]?).map taggedStr).getD "none")
              else some (exitWhy r.1.ents outs L (L k) T ss ss' gs gs' ++
                " || reference block: " ++
                boundedStr 64 "; " ((bodyAt B b T).map fun i => instrStr i.1) ++
                " || allocated block: " ++
                boundedStr 64 "; " ((bodyAt B' b' T).map fun i => instrStr i.1))
          | .ok _ _, _ =>
              some (stuckStr "allocated" b'.start
                (stuckAt (bodyAt B' b' T) (tRun (bodyAt B b T) SSt.start Tbl.empty).1))
          | _, _ => some (stuckStr "reference" b.start (stuckAt (bodyAt B b T) Tbl.empty))

/-- The first component of `oblOk L k T B B' b b'` that is `false`: the first index
    obligation of the allocated block that is none of the reference block, or that reads a
    name not live at the block start. -/
def oblWhy (L : Nat → List String × Bool) (k : Nat) (T : Term) (B B' : List LinstrRM)
    (b b' : Block) : String :=
  let os := symObl (bodyAt B b T) SSt.start
  match (symObl (bodyAt B' b' T) SSt.start).zipIdx.find? fun p =>
      !(os.contains p.1 && okIn (L k) p.1.1.vars p.1.1.readsF) with
  | some (o, i) =>
      s!"index obligation {i} (array length {o.2}) of the allocated block " ++
        (if os.contains o then "reads a name not live at the block start"
         else s!"is none of the {os.length} obligations of the reference block")
  | none => "oblOk"

/-- The first component of `ownedCheckMC outs B B'` that is `false`, at the x86 symbolic
    step, in the order of its definition: the control-flow graphs, the empty bodies and the
    block counts of `ownedCheckWithR`, the first block pair `blockWhy` refuses, then the
    first block whose index obligations `oblOk` refuses. `B` is the reference body and `B'`
    the allocated body. The empty string when no component is `false`. -/
def ownedWhy (outs : List String) (B B' : List LinstrRM) : String :=
  match cfgOf (B.map Prod.fst), cfgOf (B'.map Prod.fst) with
  | none, _ => "cfgOf of the reference body is none"
  | some _, none => "cfgOf of the allocated body is none"
  | some G, some G' =>
      let R := runsOf B B' G G'
      let La := liveIter outs B G R (4 * G.blocks.size + 64)
        (Array.replicate G.blocks.size ([], false))
      let L : Nat → List String × Bool := fun k => La.getD k ([], false)
      if B.isEmpty then "the reference body is empty"
      else if B'.isEmpty then "the allocated body is empty"
      else if (G.blocks.size == G'.blocks.size) = false then
        s!"block counts differ: reference {G.blocks.size}, allocated {G'.blocks.size}"
      else
        match (List.range G.blocks.size).findSome? fun k =>
            (blockWhy outs L B B' G G' R k).map fun s =>
              s!"block {k} of {G.blocks.size} (reference instructions {(G.blk k).start} to " ++
                s!"{(G.blk k).stop}; allocated {(G'.blk k).start} to {(G'.blk k).stop}): {s}" with
        | some s => s
        | none =>
            match (List.range G.blocks.size).find? fun k =>
                !oblOk L k (G.blk k).term B B' (G.blk k) (G'.blk k) with
            | some k =>
                s!"oblCheckWith block {k} of {G.blocks.size}: " ++
                  oblWhy L k (G.blk k).term B B' (G.blk k) (G'.blk k)
            | none => ""

open CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck (IdxFact entails startF annAt
  blockInvOk idxAnnot boundFacts)

/-- A rendering of a fact of the bounds invariant: `r1+r2<=b`, `r>=k`, `a[*]<=b` or `r:64`. -/
def factStr : IdxFact → String
  | .le rs b => s!"{"+".intercalate rs}<={b}"
  | .ale a b => s!"{a}[*]<={b}"
  | .ge r k => s!"{r}>={k}"
  | .w64 r => s!"{r}:64"

/-- The first component of `idxInvCheckB entry ann B` that is `false`, in the order of its
    definition: an absent control-flow graph; the first block `blockInvOk` refuses, with its
    instruction range and the facts `annAt ann k` of the annotation (cut after twelve), and
    there a symbolic run outside the fragment, the first index obligation `oblsOk` refuses
    with the facts and the width facts `guardW64` of the guards of the run (the index term
    and the array length), or the successor facts;
    or the entry facts not giving a fact of block `0`. The empty string when no component
    is `false`. -/
def idxWhy (entry : List IdxFact) (ann : List (List IdxFact)) (B : List LinstrRM) : String :=
  match cfgOf (B.map Prod.fst) with
  | none => "cfgOf of the reference body is none"
  | some G =>
      match (List.range G.blocks.size).find? fun k => !blockInvOk ann B G k with
      | some k =>
          let T := (G.blk k).term
          let F := startF (annAt ann k)
          let hd := s!"block {k} of {G.blocks.size} (reference instructions " ++
            s!"{(G.blk k).start} to {(G.blk k).stop}; facts " ++
            s!"[{boundedStr 12 "," ((annAt ann k).map factStr)}]): "
          match symRun (bodyAt B (G.blk k) T) SSt.start with
          | .unk => hd ++ "symbolic run outside the fragment"
          | .fail => hd ++ "blockInvOk"
          | .ok _ gs =>
              let Fg := F ++ gs.flatMap
                CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck.guardW64
              match (symObl (bodyAt B (G.blk k) T) SSt.start).find? fun o =>
                  !CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck.oblsOk Fg [o] with
              | some o =>
                  hd ++ s!"index {symStr #[] 6 (.inl o.1)} of an array of length {o.2} " ++
                    "is not bounded by the facts (outside the domain: an index must be " ++
                    "bounded by a layout bound, a loop or conditional guard, a mask or a " ++
                    "constant)"
              | none => hd ++ "the facts of a successor do not follow"
      | none =>
          match (annAt ann 0).find? fun f =>
              !entails (startF entry) (f.toS STerm.reg SArr.cell) with
          | some f => s!"the entry facts do not give {factStr f} of block 0"
          | none => ""

/-! ## 3. The printed-address check -/

/-- The name of the arm `classifyA` reads an instruction into. -/
def armKind : AArm → String
  | .reg _ => "reg"
  | .st .. => "st"
  | .ld .. => "ld"
  | .cmpR .. => "cmpR"
  | .cmpI .. => "cmpI"
  | .cmpM .. => "cmpM"
  | .ldx .. => "ldx"
  | .stx .. => "stx"
  | .mul .. => "mul"
  | .mulxS .. => "mulxS"
  | .mulx .. => "mulx"
  | .zero .. => "zero"
  | .simm .. => "simm"
  | .leaF .. => "leaF"

/-- The first conjunct of `printedAddrB body` that is `false`, in the order of its
    definition. For the conjunct on `instrOKB`: the index and the rendering of the first
    instruction refused, the arm `classifyA` reads it into (an arm named there fails its
    conditions `AArm.ok`), its names that are no general-purpose register names, and the
    value of `instrOKWB` on it. For the conjunct on `condPrevB`: the index of the first
    conditional branch refused and the instruction before it. The empty string when no
    conjunct is `false`. -/
def narrowWhy (body : Lcmd) : String :=
  let P := Params.ofBody body
  if decodableLcmd body = false then "decodableLcmd"
  else if (body.getLast?.any fun r => isRetB r.li_i) = false then "the last instruction is no return"
  else
    match body.dropLast.zipIdx.find? fun p => !instrOKB body P p.1.li_i with
    | some (i, k) =>
        let arm :=
          match i.li_i with
          | .Lopn .. =>
              (match classifyA i.li_i with
                | some a => s!"arm {armKind a} fails its conditions"
                | none => "no arm")
          | _ => "branch form or label not covered"
        let sl := slotNames i.li_i
        s!"instruction {k} of {body.length}: {instrStr i.li_i}; {arm}" ++
          (if sl.isEmpty then "" else s!"; names outside the registers: {" ".intercalate sl}") ++
          s!"; instrOKWB={instrOKWB body P i.li_i}"
    | none =>
        match (List.range body.length).find? fun k => !condPrevB body k with
        | some k =>
            s!"condPrevB at instruction {k}: preceded by " ++
              ((body[k - 1]?).map fun j => instrStr j.li_i).getD "none"
        | none => ""

/-- The first conjunct of `printedAddrWB body` that is `false`, in the order of its
    definition, or, when all hold, the first cell access of `body` (`cellA?`). For the
    conjunct on `instrOKWB`: the index and the rendering of the first instruction refused.
    For the conjuncts on `condPrevB`, `carryPrevB` and `castPosB`: the index of the first
    position refused. The empty string when `printedAddrWB body` holds and `body` has no
    cell access. -/
def wideWhy (body : Lcmd) : String :=
  let P := Params.ofBody body
  if decodableLcmd body = false then "decodableLcmd"
  else if (body.getLast?.any fun r => isRetB r.li_i) = false then "the last instruction is no return"
  else
    match body.dropLast.zipIdx.find? fun p => !instrOKWB body P p.1.li_i with
    | some (i, k) => s!"instrOKWB at instruction {k} of {body.length}: {instrStr i.li_i}"
    | none =>
        match (List.range body.length).find? fun k => !condPrevB body k with
        | some k => s!"condPrevB at instruction {k}"
        | none =>
            match (List.range body.length).find? fun k => !carryPrevB body k with
            | some k => s!"carryPrevB at instruction {k}"
            | none =>
                match (List.range body.length).find? fun k => !castPosB body k with
                | some k => s!"castPosB at instruction {k}"
                | none =>
                    match body.zipIdx.find? fun p => (cellA? p.1.li_i).isSome with
                    | some (i, k) => s!"cell access at instruction {k}: {instrStr i.li_i}"
                    | none => ""

/-- The reason the printed body `body` is outside the class
    `printedAddrB body || (printedAddrWB body && no cell access)` of the region back half:
    `narrowWhy body` for the first class, then `wideWhy body` for the second. The empty
    string when `body` is in one of the two classes. -/
def printedWhy (body : Lcmd) : String :=
  let n := narrowWhy body
  let w := wideWhy body
  if n.isEmpty || w.isEmpty then "" else s!"{n} | second class: {w}"

/-! ## 4. The exportability test -/

/-- The first node of `p` at which `regionExportableB` is `false`, in the order of its
    definition, with the path of regions to it: a binding with its operation (no register
    variable in scope, or an operation outside `opMemB`), an exit-flag loop whose carried
    types include an array, or a call. `none` when the test holds. -/
def exportableWhy : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} →
    NFProg jasminDialect Γ ts → Option String
  | _, _, .ret _ => none
  | Γ, _, .var (t := t) e k =>
      if bindMemNB e then exportableWhy k
      else if (regVar? (t :: Γ)).isNone then
        some s!"binding {jasOpStr e.op} : {jasTyStr t}: no register variable in scope"
      else if opMemB e.op = false then
        some s!"binding {jasOpStr e.op} : {jasTyStr t}: operation outside opMemB"
      else some s!"binding {jasOpStr e.op} : {jasTyStr t}"
  | _, _, .forLoop _ _ body k =>
      match exportableWhy body with
      | some s => some s!"forLoop body > {s}"
      | none => exportableWhy k
  | _, _, .ifThenElse _ thn els k =>
      match exportableWhy thn with
      | some s => some s!"then branch > {s}"
      | none =>
          match exportableWhy els with
          | some s => some s!"else branch > {s}"
          | none => exportableWhy k
  | _, _, .whileLoop (cs := cs) _ body k =>
      match cs.find? fun t => !isRegTy t with
      | some t => some s!"whileLoop carries {jasTyStr t}"
      | none =>
          match exportableWhy body with
          | some s => some s!"whileLoop body > {s}"
          | none => exportableWhy k
  | _, _, .call f _ _ => some s!"call {f}"

/-! ## 6. The check of the coalesced reference -/

/-- The names of `A` outside `B`, at most six of them. -/
def outsideStr (A B : List String) : String :=
  boundedStr 6 "," (A.filter fun r => !B.contains r)

/-- The names of `ns` that `σ` renames, each with its image, at most six of them. -/
def imagesStr (σ : String → String) (ns : List String) : String :=
  boundedStr 6 "," (((ns.filter fun n => σ n != n).eraseDups).map fun n => s!"{n}->{σ n}")

/-- Two reasons joined; an empty reason is left out. -/
def joinWhy (a b : String) : String :=
  if a.isEmpty then b else if b.isEmpty then a else a ++ "; " ++ b

/-- The reason `jumpB body L k lbl` is `false`: the label is the last instruction, or the
    names live after it that are not live at `k`. Empty when it is `true`. -/
def jumpWhy (body : List LinstrRM) (L : Nat → List String) (k : Nat) (lbl : LLabel) : String :=
  match findLabelMem lbl body with
  | some p =>
      if p + 1 ≤ body.length then
        if subB (L (p + 1)) (L k) then ""
        else s!"jumpB: live at {p + 1}, not at {k}: {outsideStr (L (p + 1)) (L k)}"
      else s!"jumpB: the label at {p} is past the body"
  | none => ""

/-- The reason `coArrStepB σ i after` is `false`: the names of `after` that share the image
    of the destination of a store or of an array zeroing, or a compile-time-offset access.
    Empty when it is `true`. -/
def coStepWhy (σ : String → String) (i : LinstrRM) (after : List String) : String :=
  if coArrStepB σ i after then ""
  else match i.2 with
    | .store _ _ =>
        match storeStruct? i.1 with
        | some (d, _, _, _) =>
            let clash := boundedStr 6 "," (after.filter fun r => !(r == d || σ r != σ d))
            s!"coArrStepB: live after the store with the image {σ d} of {d}: {clash}"
        | none => ""
    | .zero _ _ =>
        match zeroStruct? i.1 with
        | some d =>
            let clash := boundedStr 6 "," (after.filter fun r => !(r == d || σ r != σ d))
            s!"coArrStepB: live after the zeroing with the image {σ d} of {d}: {clash}"
        | none => ""
    | .loadC | .storeC => "coArrStepB: compile-time-offset access"
    | _ => ""

/-- The first operand of a call from the argument position `j` that `callOpsB σ a live j os`
    refuses: an array operand whose register is not in `live`, or a word operand whose
    register `σ` renames. Empty when `callOpsB` is `true`. -/
def callOpsWhy (σ : String → String) (a : Nat → Option Nat) (live : List String) :
    Nat → List LOperand → String
  | _, [] => ""
  | j, o :: os =>
      match o with
      | .reg x =>
          if (a j).isSome then
            if live.contains x then callOpsWhy σ a live (j + 1) os
            else s!"array operand {j} ({x}) not live before the call"
          else if σ x == x then callOpsWhy σ a live (j + 1) os
          else s!"word operand {j} ({x}) with the image {σ x}"
      | _ => callOpsWhy σ a live (j + 1) os

/-- The sub-checks of `callB σ L k aa ao tag dst f srcs` that are `false`: the load or store
    tag, the operand `callOpsWhy` refuses, and by the result of `f`: at a word result the
    renaming of `dst` and the names live at `k + 1` not live at `k`; at an array result the
    names `r ≠ dst` live at `k + 1` whose image under `σ` is the image of `dst`, and the
    names other than `dst` live at `k + 1` not live at `k`. Empty when `callB` is
    `true`. -/
def callWhy (σ : String → String) (L : Nat → List String) (k : Nat)
    (aa : String → Nat → Option Nat) (ao : String → Option Nat) (tag : MemTag)
    (dst f : String) (srcs : List LOperand) : String :=
  let tagW := if callTagB tag then "" else s!"call {f} with a load or store tag"
  let opsW := callOpsWhy σ (aa f) (L k) 0 srcs
  let resW :=
    match ao f with
    | none =>
        joinWhy (if σ dst == dst then "" else s!"word result {dst} with the image {σ dst}")
          (if subB (L (k + 1)) (L k) then ""
           else s!"live at {k + 1}, not at {k}: {outsideStr (L (k + 1)) (L k)}")
    | some n =>
        let clash := (L (k + 1)).filter fun r => r != dst && σ r == σ dst
        let after := (L (k + 1)).filter fun r => r != dst
        joinWhy
          (if clash.isEmpty then ""
           else s!"callB: live after the call {f} with the image {σ dst} of its result {dst} \
             (length {n}): {boundedStr 6 "," clash}")
          (if subB after (L k) then ""
           else s!"live at {k + 1}, not at {k}: {outsideStr after (L k)}")
  joinWhy tagW (joinWhy opsW resW)

/-- The sub-checks of `coInstrB σ body L k i aa ao` that are `false`, by the arm of
    `coInstrB` that reads `i`: `callWhy` on a shadow instruction of a call, `plainArrB` on
    an instruction with an array position or on its renaming, `coArrStepB`, the inclusion
    of the names the operation needs in those live at `k`, the inclusion of the names live
    at `k + 1` in those live at `k` (not checked at a constant-taken guard), `jumpB`, or the
    refused instruction kind. -/
def coInstrWhy (σ : String → String) (body : List LinstrRM) (L : Nat → List String) (k : Nat)
    (i : LinstrRM) (aa : String → Nat → Option Nat := fun _ _ => none)
    (ao : String → Option Nat := fun _ => none) : String :=
  let liveW :=
    if subB (L (k + 1)) (L k) then ""
    else s!"live at {k + 1}, not at {k}: {outsideStr (L (k + 1)) (L k)}"
  let guardW := if X86Backend.ConstGuard.constTakenB body k then "" else liveW
  let need := arrReads i ++ (L (k + 1)).filter fun r => some r != arrWrite i
  let needW :=
    if subB need (L k) then "" else s!"needed, not live at {k}: {outsideStr need (L k)}"
  match LprogIsa.shadowCall? i.1 with
  | some (dst, f, srcs) => callWhy σ L k aa ao i.2 dst f srcs
  | none =>
  if arrShapeB i then
    joinWhy (if plainArrB i then "" else "plainArrB")
      (joinWhy
        (if plainArrB (renArr σ i) then ""
         else s!"plainArrB of the renaming {taggedStr (renArr σ i)}")
        (joinWhy (coStepWhy σ i (L (k + 1))) needW))
  else if (cmpArgs? i).isSome || (movRegArgs? i).isSome then liveW
  else match flagCondCC? i with
    | some (_, lbl) => joinWhy guardW (jumpWhy body L k lbl)
    | none =>
      match i.1 with
      | .Llabel _ _ => liveW
      | .Lcond _ lbl => joinWhy guardW (jumpWhy body L k lbl)
      | .Lgoto (_, lbl) => jumpWhy body L k lbl
      | .Lopn _ _ _ =>
          if (carryArgs? i).isSome || (wideArgs? i).isSome then liveW
          else joinWhy (coStepWhy σ i (L (k + 1))) needW
      | _ => "instruction kind refused"

/-- The reason `coCfgB σ body L obs aa ao` is `false`: the names of `obs` not live at the
    end, or the first position whose instruction `coInstrB` refuses, with the rendering of
    the instruction and `coInstrWhy`. Empty when it is `true`. -/
def coCfgWhy (σ : String → String) (body : List LinstrRM) (L : Nat → List String)
    (obs : List String) (aa : String → Nat → Option Nat := fun _ _ => none)
    (ao : String → Option Nat := fun _ => none) : String :=
  if subB obs (L body.length) = false then
    s!"observed, not live at the end: {outsideStr obs (L body.length)}"
  else
    let bad := (List.range body.length).find? fun k =>
      match body[k]? with
      | some i => !coInstrB σ body L k i aa ao
      | none => false
    match bad with
    | some k =>
        match body[k]? with
        | some i => s!"at {k}: {taggedStr i}: {coInstrWhy σ body L k i aa ao}"
        | none => ""
    | none => ""

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc (useNames regDefs arrDefs
  arrUse? jumpLabel?) in
/-- The reason `regCoB τ pre C L AN` is `false`: the merge renames the empty name, an array
    name of `AN` or a name live at the first position of `C`, or the first position whose
    instruction `regCoInstrB` refuses, with the rendering of the instruction and the
    sub-checks that are `false`: `condOKB`, the names read that are not live, the array
    read outside `AN`, the names live after a write that share the image of the written
    name or are not live before it, the array write, and the names live after the label of
    a jump that are not live at the jump, and the call check `regCallB` at the array
    positions `aa` and the result lengths `ao`. Empty when it is `true`. -/
def regCoWhy (τ : String → String) (pre C : List LinstrRM) (L : Nat → List String)
    (AN : List String) (aa : String → Nat → Option Nat := fun _ _ => none)
    (ao : String → Option Nat := fun _ => none) : String :=
  let Lr := liveAt L (pre ++ C).length
  if τ "" != "" then "the merge renames the empty name"
  else if AN.all (fun a => τ a == a) = false then s!"array names renamed: {imagesStr τ AN}"
  else if (Lr pre.length).all (fun r => τ r == r) = false then
    s!"live at the entry and renamed: {imagesStr τ (Lr pre.length)}"
  else
    let bad := (List.range C.length).find? fun j =>
      match C[j]? with
      | some i => !regCoInstrB τ (pre ++ C) Lr AN (pre.length + j) i aa ao
      | none => false
    match bad with
    | some j =>
        match C[j]? with
        | some i =>
            let k := pre.length + j
            let ds := regDefs i
            let clash := (Lr (k + 1)).filter fun r =>
              !(ds == [r] || ((Lr k).contains r && ds.all fun d => τ r != τ d))
            let jumpW :=
              match jumpLabel? i.1 with
              | some l =>
                  match findLabelMem l (pre ++ C) with
                  | some p =>
                      if subB (Lr (p + 1)) (Lr k) then ""
                      else s!"live at {p + 1}, not at {k}: {outsideStr (Lr (p + 1)) (Lr k)}"
                  | none => ""
              | none => ""
            let keepW :=
              if keepsB τ (Lr k) (Lr (k + 1)) ds then ""
              else
                s!"live after the write of {boundedStr 2 "," ds} with its image or not live "
                  ++ s!"before it: {boundedStr 6 "," clash}"
            let parts :=
              joinWhy (if condOKB i then "" else "condOKB")
                (joinWhy
                  (if subB (useNames i.1) (Lr k) then ""
                   else s!"read, not live at {k}: {outsideStr (useNames i.1) (Lr k)}")
                  (joinWhy
                    (if (arrUse? i).all AN.contains then ""
                     else "array read outside the array names")
                    (joinWhy keepW
                      (joinWhy (if keepsB τ AN AN (arrDefs i) then "" else "array write")
                        (joinWhy jumpW
                          (if regCallB τ Lr AN aa ao k i then "" else "call operands"))))))
            s!"at {k}: {taggedStr i}: {parts}"
        | none => ""
    | none => ""

/-- The state of the register merge of the parts `d` of a reference: the merge pairs
    `d.tau` of the allocation certificate and, when `regCoB` refuses them, the reason
    `regCoWhy`; the empty string when there is no merge pair. -/
def regionMergeWhy (d : CoParts) : String :=
  let ts := d.tau
  if ts.isEmpty then ""
  else
    let why := regCoWhy (renOf ts) d.pre d.ren (tabAt d.live) d.arrs d.aa d.ao
    let pairs := boundedStr 12 "," (ts.map fun p => s!"{p.1}->{p.2}")
    if why.isEmpty then s!"merge: {pairs}" else s!"merge refused: {pairs}: {why}"

/-- The part of `regionNopB d` that is `false`: the reason `regCoWhy` for which the
    identity merge is refused on the merged code at the table `d.liveM`, or the targets of
    the result copy that the table does not give the end of the body. Empty when
    `regionNopB d` is `true`. -/
def regionNopWhy (d : CoParts) : String :=
  let why := regCoWhy id d.pre d.merged (tabAt d.liveM) d.arrsM d.aa d.ao
  let dead := d.outs.filter fun y => !(tabAt d.liveM (d.pre ++ d.merged).length).contains y
  if !why.isEmpty then s!"liveness table of the merged code refused: {why}"
  else if dead.isEmpty then ""
  else s!"result copy target not live at the end: {boundedStr 2 "," dead}"

open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (printedAddrB) in
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame (frameNames frameMark) in
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (instrGateB reloadSavedB) in
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimW (instrGateBW oneBitAt
  readOkB) in
/-- The gate of `regionImgB sl R outs body` that is `false`, for a body of the class
    `regionPrintedB`, after the printed class of `body` that decides the gate. The gates
    are read at the cell body of `body` and the frame marks with the cells of `R`, which
    are the body and its frame marks at no cell array on a body with no cell access. For
    `imgGateB`: the index and the rendering of the first
    instruction `instrGateB` refuses, else the last instruction that is no return, else
    `reloadSavedB`. For a body outside `printedAddrB` or with cells, before it the values
    of `cellAccB` and `cellNoSlotB`, and after it the part of the gate with carry chains
    and indexed stores through a cell: the index and the rendering of the first instruction
    `ImageAddrCidx.gateCW` refuses with the width analysis `oneBitAt` there and the value of
    `readOkB`, else the
    last instruction that is no return, else `reloadSavedB`, else the observed names that
    `retOutsB` finds in the width analysis at the return. Empty when the gate holds. -/
def imgWhy (sl : String → Option (String × Nat)) (R : X86Backend.ImageCellFold.Slots)
    (outs : List String) (body0 : Lcmd) : String :=
  let body := X86Backend.ImageAddrCells.cellBody sl body0
  let fr := X86Backend.ImageStraightCells.frameMarkC R body0
  let at' (k : Nat) : String := ((body[k]?).map fun i => instrStr i.li_i).getD ""
  let tail : String :=
    if (body.getLast?.any fun r => isRetB r.li_i) = false then
      "the last instruction is no return"
    else if reloadSavedB sl body = false then "reloadSavedB"
    else ""
  let plain : String :=
    match (List.range (body.length - 1)).find? fun k =>
        !((body[k]?).all fun i => instrGateB fr sl body k i.li_i) with
    | some k => s!"instrGateB at instruction {k} of {body.length}: {at' k}"
    | none => tail
  if regionImgB sl R outs body0 then ""
  else if printedAddrB body0 && cellFreeB body0 && R.isEmpty then
    s!"class printedAddrB: {plain}"
  else
    let wide : String :=
      match (List.range (body.length - 1)).find? fun k =>
          !((body[k]?).all fun i => X86Backend.ImageAddrCidx.gateCW fr sl body k i.li_i) with
      | some k =>
          let W := oneBitAt fr body k
          s!"gateCW at instruction {k} of {body.length}: {at' k}; width analysis \
            [{boundedStr 8 "," W}]; readOkB \
            {(body[k]?).all fun i => readOkB W i.li_i}"
      | none =>
          if !tail.isEmpty then tail
          else
            let W := oneBitAt fr body (body.length - 1)
            s!"retOutsB: observed names in the width analysis at the return: \
              {boundedStr 4 "," (outs.filter W.contains)}"
    s!"class printedAddrWB: cellAccB \
      {X86Backend.ImageStraightCells.cellAccB sl R body0}, cellNoSlotB \
      {X86Backend.ImageStraightCells.cellNoSlotB sl body0}: {plain} | with carry chains: {wide}"

/-- The kind of the name `q` at a frame map and a slot map: whether it is a general-purpose
    name, whether it has a frame word, and the array whose pointer its slot holds. -/
def nameKindStr (frame : String → Option (BitVec 64))
    (slotArr : String → Option (String × Nat)) (q : String) : String :=
  s!"{q} (gp {gpOk q}, frame {(frame q).isSome}, slot of {(slotArr q).map (·.1)})"

open X86Backend.ImageAddrSimW (oneBitAt readOkB gateReadSet castReadB carryOkB carryI?
  readNames movlNames castDsts sImmB sCmovB regGateBW cmovCondOkB castGateB) in
open X86Backend.ImageAddrSim (ICase icase regOkB) in
open VIR.JasminLsemAddrRun (condPol labelAt bitMovB normA) in
open VIR.JasminLsemAddrImage (accArr bitStore?) in
/-- The first conjunct of `gateAtW frame slotArr body k W x` that is `false`, in the order of
    its definition, with the values it compares: the frame-array operand names, the names
    read that lie in the read set `gateReadSet` (with `castReadB` false), the kinds of the
    names of a carry-chain instruction that `carryOkB` refuses, and in the arm of `icase`
    the components of its test. Empty when the gate holds. -/
def gateAtWWhy (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (body : Lcmd) (k : Nat) (W : List String) (x : LinstrR) : String :=
  let kd := nameKindStr frame slotArr
  let fa := (JasminLsemExportRewrites.instrNames x).filter JasminLprogExport.faB
  let RS := gateReadSet frame W x
  if !fa.isEmpty then s!"frame-array operand names [{boundedStr 4 "," fa}]"
  else if !(readOkB RS x || castReadB body k x) then
    let bad := (readNames x).filter fun r =>
      !(X86Backend.DecodePrintedAddrW.carryIns x).contains r && RS.contains r
    s!"readOkB: names read in the width analysis [{boundedStr 6 "," bad}]; castReadB false"
  else
    match carryI? x with
    | some (_, d, a, s, c) =>
        if carryOkB frame slotArr d a s c then ""
        else s!"carryOkB: dst {kd d}, src {kd a}, src {kd s}, carry-in {kd c}, \
          sources differ from the carry-in {a != c && s != c}"
    | none =>
        match icase frame x with
        | .label => ""
        | .cond cc l =>
            if (condPol cc).isNone then s!"branch on {cc}: condPol has no polarity"
            else
              match labelAt body l with
              | none => "branch target label not in the body"
              | some p =>
                  let V := oneBitAt frame body (p + 1)
                  let miss := W.filter fun r => !V.contains r
                  if miss.isEmpty then ""
                  else s!"branch to the label at {p}: names of the width analysis not in \
                    the analysis one past the label [{boundedStr 6 "," miss}]"
        | .ldx d b idx =>
            s!"indexed load: accArr {b} {(accArr slotArr body k b).isSome}, dst {kd d}, \
              index {kd idx}, base {kd b}"
        | .stx _ b idx v =>
            s!"indexed store: accArr {b} {(accArr slotArr body k b).isSome}, \
              index {kd idx}, base {kd b}, value {kd v}"
        | .sload d q =>
            s!"frame-word load {d} := {q}: dst {kd d}, {q} in the width analysis \
              {W.contains q}, movlNames has {q} {(movlNames body).contains q}, {kd q}"
        | .sstore q S =>
            s!"frame-word store {q} := {S}: source {kd S}, {S} in the width analysis \
              {W.contains S}, castDsts has {S} {(castDsts body).contains S}, slot {kd q}, \
              cell name {JasminLprogExport.hasPrefix q "mem."}"
        | .scmp _ y _ => s!"frame-word compare: operand {kd y}"
        | .reg =>
            match VIR.JasminLsemCast.movImmStruct? x with
            | some (d, _) =>
                s!"immediate move: bitMovB {bitMovB body k x}, dst {kd d}"
            | none =>
                match bitStore? body k x with
                | some (d, _) => s!"stored carry constant into {d}: sImmB false, dst {kd d}"
                | none =>
                    s!"register instruction: sImmB {sImmB frame slotArr x}, sCmovB \
                      {sCmovB frame slotArr x}, regOkB {regOkB frame (normA x)}, regGateBW \
                      {regGateBW frame W (normA x)}, cmovCondOkB {cmovCondOkB W x}"
        | .zarr .. => "ZEROARR is outside the gate with carry chains"
        | .simm .. => "STOREIMM is outside the gate with carry chains"
        | .other => s!"castGateB {castGateB frame x}: no width-carrying cast between \
            general-purpose names without a frame word"

open X86Backend.ImageAddrSimW (gateAtW oneBitStepF FwdTab) in
/-- The first instruction that the one-pass loop `gateLoop` refuses: from position `k` with
    the width analysis and its table of forward branches `S` at `k` and the remaining
    instructions, at most `n` instructions, the analysis and the table advanced by
    `oneBitStepF` after each; the position, the analysis there and the instruction. -/
def gateFirstW (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (body : Lcmd) : Nat → Nat → List String × FwdTab → Lcmd →
      Option (Nat × List String × LinstrR)
  | 0, _, _, _ => none
  | _ + 1, _, _, [] => none
  | n + 1, k, S, i :: rest =>
      if gateAtW frame slotArr body k S.1 i.li_i then
        gateFirstW frame slotArr body n (k + 1) (oneBitStepF frame body k S i.li_i) rest
      else some (k, S.1, i.li_i)

open X86Backend.ImageAddrSim (heldReg?) in
/-- The first position at which `reloadSavedB slotArr body` is `false`: a reload of the
    pointer of an array from a slot that is not entry-held and that no earlier save writes,
    with its instruction. Empty when the check holds. -/
def reloadSavedWhy (slotArr : String → Option (String × Nat)) (body : Lcmd) : String :=
  let ok (k : Nat) : Bool :=
    match body[k]? with
    | some i =>
        match VIR.JasminLsemAddrMem.slotMov? i.li_i with
        | some (_, q) =>
            (slotArr q).isNone || (heldReg? q).isSome || (List.range k).any fun j =>
              (body[j]?).any fun i' => VIR.JasminLsemAddrImage.isSaveB i'.li_i
                && ((VIR.JasminLsemAddrMem.slotMov? i'.li_i).map Prod.fst == some q)
        | none => true
    | none => true
  match (List.range body.length).find? fun k => !ok k with
  | some k =>
      let ins := ((body[k]?).map fun i => instrStr i.li_i).getD ""
      s!"reloadSavedB at instruction {k} of {body.length}: {ins}: reload of an array \
        pointer with no earlier save"
  | none => ""

/-- The first part of `imgGateBW frame slotArr body` that is `false`: the first instruction
    the instruction gate refuses (`gateFirstW`, one pass with the width analysis advanced
    as in `gateLoop`, at the frame map tabulated over the names of the body as in
    `imgGateBWImpl`), with its position, its rendering, the width analysis there and the
    conjunct `gateAtWWhy`; else a last instruction that is no return; else
    `reloadSavedWhy`. Empty when the gate holds. -/
def imgGateWhyW (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (body : Lcmd) : String :=
  let fr := X86Backend.ImageAddrSimW.tabFrame frame
    ((X86Backend.ImageAddrFrame.bodyNamesI body).eraseDups.map fun q => (q, frame q))
  match gateFirstW fr slotArr body (body.length - 1) 0 ([], []) body with
  | some (k, W, x) =>
      s!"instrGateBW at instruction {k} of {body.length}: {instrStr x}; width analysis \
        [{boundedStr 8 "," W}]; {gateAtWWhy fr slotArr body k W x}"
  | none =>
      if !(body.getLast?.any fun r => isRetB r.li_i) then "no final ret"
      else reloadSavedWhy slotArr body

/-! ## 7. The check of the multiplication fusion -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (wireOK nameOK mulOK posOK siteOK
  w64 mulLoB blk fuseLoPre) in
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (instrNames) in
/-- The reason `fuseOKL E L c` is `false`: the first instruction outside the covered
    classes, with a name the fusion reserves or an untagged `MULX`, with the values of
    `clsB`, `wireOK` and `mulxFree`, its names `nameOK` refuses and the value of `mulOK`; or
    the first position `posOK` refuses, with its instruction, and there an undescribed
    symbolic state, the registers of `E` whose word has no known width `64`, and for a
    fused site its low destination with the conjuncts of `siteOK`. Empty when it is
    `true`. -/
def fuseOKWhy (E : List String) (L : List (Option String)) (c : List LinstrRM) : String :=
  match c.zipIdx.find? fun p => !(clsB p.1 && wireOK p.1.1 && mulxFree p.1) with
  | some (i, k) =>
      let bad := boundedStr 6 "," ((instrNames i.1).filter fun n => !nameOK n)
      s!"at {k}: {taggedStr i}: clsB {clsB i}, wireOK {wireOK i.1}, mulxFree {mulxFree i}, \
        reserved names [{bad}], mulOK {mulOK i.1}"
  | none =>
      match (List.range (c.length + 1)).find? fun k => !posOK E L c k with
      | some k =>
          let ins := match c[k]? with
            | some i => taggedStr i
            | none => "end of the body"
          let why := match blk c k with
            | .unk => "symbolic state not described"
            | .fail => ""
            | .ok ss _ =>
                let wide := E.filter fun x => !w64 E (ss.regs x)
                let site := match L[k]?, c[k]? with
                  | some (some d), some (.Lopn [.reg _] _ [.reg h1, .reg s2], _) =>
                      s!"site with low destination {d}: siteOK \
                        {(c[k]?).any fun i => siteOK E d i ss}, \
                        low name {nameOK d && d != "RDX"}, \
                        w64 {h1} {w64 E (ss.regs h1)}, w64 {s2} {w64 E (ss.regs s2)}, \
                        low product {mulLoB (ss.regs d) (ss.regs h1) (ss.regs s2)}"
                  | some (some d), _ => s!"site with low destination {d}: not a MULXHI shape"
                  | _, _ => ""
                joinWhy
                  (if wide.isEmpty then ""
                   else s!"no known width 64: {boundedStr 6 "," wide}") site
          s!"at {k}: {ins}: {why}"
      | none => ""

/-! ## 8. The reasons by stage -/

open X86Backend.ImageAddrCall (relocFrameB remoteCallB callFreeB frameNonnegB) in
/-- The first conjunct of `ImageAddrCallW.printedAddrCWB G body` that is `false`, in the order of
    its definition. For the conjunct on calls and `instrOKWB`: the index and the rendering of the
    first instruction refused. For the conjuncts on `condPrevB`, `carryPrevB` and `castPosB`: the
    index of the first position refused. Empty when the class holds. -/
def callClassWhy (G : Nat) (body : Lcmd) : String :=
  let P := Params.ofBody body
  if relocFrameB body = false then "relocFrameB"
  else if (body.getLast?.any fun r => isRetB r.li_i) = false then
    "the last instruction is no return"
  else
    match body.dropLast.zipIdx.find? fun p =>
        !(remoteCallB p.1.li_i || instrOKWB body P p.1.li_i) with
    | some (i, k) => s!"instrOKWB at instruction {k} of {body.length}: {instrStr i.li_i}"
    | none =>
        match (List.range body.length).find? fun k => !condPrevB body k with
        | some k => s!"condPrevB at instruction {k}"
        | none =>
            match (List.range body.length).find? fun k => !carryPrevB body k with
            | some k => s!"carryPrevB at instruction {k}"
            | none =>
                match (List.range body.length).find? fun k => !castPosB body k with
                | some k => s!"castPosB at instruction {k}"
                | none =>
                    if callFreeB body || frameNonnegB body G then ""
                    else s!"frameNonnegB at the frame {G}"

/-- The frame map `frame` tabulated over the names of `body`. -/
def bodyFrameTab (frame : String → Option (BitVec 64)) (body : Lcmd) :
    String → Option (BitVec 64) :=
  X86Backend.ImageAddrSimW.tabFrame frame
    ((X86Backend.ImageAddrFrame.bodyNamesI body).eraseDups.map fun q => (q, frame q))

/-- The first part of `ImageAddrCallW.imgGateCBW frame slotArr body` that is `false`: the first
    instruction the instruction gate refuses, with its position, its rendering, the width
    analysis there and the conjunct of `gateAtW` that is `false` (`gateAtWWhy`), else a last
    instruction that is no return, else the first reload `reloadSavedB` refuses
    (`reloadSavedWhy`). Empty when the gate holds. -/
def callGateWhy (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (body : Lcmd) : String :=
  let fr := bodyFrameTab frame body
  let tab := X86Backend.ImageAddrCallW.oneBitTab fr body
  match body.dropLast.zipIdx.find? fun p =>
      !X86Backend.ImageAddrCallW.gateAtTab fr slotArr body tab p.2 p.1.li_i with
  | some (i, k) =>
      let W := tab.getD k []
      s!"gate at instruction {k} of {body.length}: {instrStr i.li_i}; width analysis \
        [{boundedStr 8 "," W}]; gateAtW: {gateAtWWhy fr slotArr body k W i.li_i}"
  | none =>
      if (body.getLast?.any fun r => isRetB r.li_i) = false then
        "the last instruction is no return"
      else reloadSavedWhy slotArr body

/-- The first position, of the last position and the call positions, at which
    `ImageAddrCallW.bitsDeadB frame D body` is `false`, with the names of the width analysis not
    dead there. Empty when the check holds. -/
def bitsDeadWhy (frame : String → Option (BitVec 64)) (D : X86Backend.ImageAddrCall.DeadTab)
    (body : Lcmd) : String :=
  let tab := X86Backend.ImageAddrCallW.oneBitTab (bodyFrameTab frame body) body
  let live (p : Nat) : List String := (tab.getD p []).filter fun r => !(D.dead p).contains r
  match ((body.length - 1) :: X86Backend.ImageAddrCall.callPos body).find?
      fun p => !(live p).isEmpty with
  | some p => s!"bitsDeadB at position {p} of {body.length}: width analysis names not dead \
      [{boundedStr 8 "," (live p)}]"
  | none => ""

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (fuseLoPre) in
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (virtImg) in
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (fuseRegs slotRen
  slotArrOf) in
/-- The reason for a refusal of `regionCoB σ nm body t code res` at the stage `stage` of
    `regionCoStage`. `coClass`: the first instruction outside the covered classes.
    `coCfgB`: `coCfgWhy` on the arguments of the stage. `coEntryFix`: the array names live
    at the entry that the alias map renames. `renB`: the pairs `certArgs` of the
    allocation certificate `cert`.
    `coResultName`: the returned array names with their aliases. `coResultCopy`: the result
    copy and the image of its target under the pairs. `regMerge`: `regionMergeWhy` and the
    result copy with the image of its target under the merge, at the merge pairs of the
    certificate. `regionNopB`:
    `regionNopWhy`. `fuseOKL`: `fuseOKWhy` on the arguments of the stage, the code `nop`
    of the parts with the fusion behind the prefix. `fuseResultName`: the renamed aliases
    of the returned array names and the targets of the result copy. `regionFoldB`,
    `cellNamesRB`, `cellRegions`: the cell arrays of the parts, whether the code has a cell
    fold, and the pairs with a cell name. `ownedCheckMC`: `ownedWhy` on the reference `ref`
    of the parts against the image of the cell body of the printed body, observing the
    targets of the result copy and the cell names `cellOuts`.
    `regionPrintedB`: `printedWhy` on the printed body. `idxInvCheckB`: `idxWhy` on the
    reference `ref` of the parts with the annotation `idxAnnot`. `regionImgB`: without a
    table, `imgWhy` at the slot map renamed by the pairs of the parts, with the cell arrays of
    the parts at length `0`, and the observed names of `ownedCheckMC`; at a table,
    `callClassWhy` at its frame, then `callGateWhy`. `calleeBodyB`: at a table, `bitsDeadWhy`.
    The stages `coClass`, `coCfgB` and `coEntryFix` are read at the optional callee
    `callee` of `regionCoStage`: the code `calleeCodeT`, the alias map of `regionAliasTab`
    (the map `chainAliasO` at the out symbols `calleeOutsT`), and the liveness table
    `liveArrTab` at the array positions `calleeAAT` and the result lengths `calleeAOT`.
    Empty at every other stage. -/
def regionCoWhy (stage : String) (σ : AbiLayout) (nm : String → String) (body : Lcmd)
    (t : JasminTy) (code : List LinstrRM) (res : List LOperand) (cert : List (String × String))
    (callee : Option CalleeTab := none) : String :=
  let codeC := calleeCodeT callee code
  let cpC := regionCopy σ nm t callee codeC res
  let CC := regionCoCode σ nm t codeC res cpC
  let ρC := JasminLprogExport.canonMemrefName (regionAliasTab σ nm t callee res CC)
  let obsC := regionCoObs t (regionOut cpC res)
  let LA := liveArrTab CC obsC (calleeAAT callee) (calleeAOT callee)
  let C := regionCoCodeN σ nm t code res
  let ρ := regionAliasN σ nm t res C
  let obs := regionCoObs t (regionOutN σ nm t code res)
  if stage == "coClass" then
    match CC.zipIdx.find? fun p => !(clsB p.1 && mulxFree p.1) with
    | some (i, k) => s!"at {k}: {taggedStr i}: clsB {clsB i}, mulxFree {mulxFree i}"
    | none => ""
  else if stage == "coCfgB" then
    coCfgWhy ρC CC (tabAt LA) obsC (calleeAAT callee) (calleeAOT callee)
  else if stage == "coEntryFix" then
    s!"live at the entry and renamed: {imagesStr ρC (tabAt LA 0)}"
  else if stage == "renB" then
    let ps := certArgs σ cert
    s!"pairs: {boundedStr 12 "," (ps.map fun p => s!"{p.1}->{p.2}")}"
  else if stage == "coResultName" then
    s!"returned: {boundedStr 6 "," (obs.map fun A => s!"{A}->{ρ A}")}"
  else if stage == "coResultCopy" then
    let ps := certArgs σ cert
    let cp := (regionRet σ nm t res).toList.map fun p =>
      s!"{p.1}->{p.2}, pairs send {p.2} to {renOf ps p.2}"
    s!"result copy: {boundedStr 2 "," cp}"
  else if stage == "regMerge" then
    let d := regionCoParts σ nm body t code res cert
    let cp := (regionRet σ nm t res).toList.map fun p =>
      s!"{p.2}, merge sends it to {renOf d.tau p.2}"
    s!"{regionMergeWhy d}; result copy target: {boundedStr 2 "," cp}"
  else if stage == "regionNopB" then regionNopWhy (regionCoParts σ nm body t code res cert)
  else if stage == "fuseOKL" then
    let d := regionCoParts σ nm body t code res cert
    let L := d.nop.drop d.pre.length
    fuseOKWhy (fuseRegs σ nm) (fuseLoPre d.pre L) (d.pre ++ L)
  else if stage == "fuseResultName" then
    let d := regionCoParts σ nm body t code res cert
    s!"returned: {boundedStr 6 "," d.obs}; result copy target: {boundedStr 2 "," d.outs}"
  else if stage == "regionFoldB" || stage == "cellNamesRB" || stage == "cellRegions" then
    let d := regionCoParts σ nm body t code res cert
    let cells := d.cells.map fun p => s!"{p.1}[{p.2}]"
    let atCell := (d.ps.filter fun p =>
      X86Backend.ImageCellFold.isCellB d.cells p.1
        || X86Backend.ImageCellFold.isCellB d.cells p.2).map fun p => s!"{p.1}->{p.2}"
    s!"cell arrays: {boundedStr 4 "," cells}; cellFoldLR \
      {(X86Backend.CellFoldLReg.cellFoldLR d.cells [] (d.fused.drop d.pre.length)).isSome}; \
      pairs at a cell name: {boundedStr 4 "," atCell}"
  else if stage == "ownedCheckMC" then
    let d := regionCoParts σ nm body t code res cert
    let sl := X86Backend.ImageStraightCells.slotArrC d.cells
      (slotRen (slotArrOf σ nm) (renOf d.ps))
    ownedWhy (d.outs ++ d.cellOuts) d.ref
      (virtImg sl (X86Backend.ImageAddrCells.cellBody sl body))
  else if stage == "regionPrintedB" then printedWhy body
  else if stage == "idxInvCheckB" then
    let B := (regionCoParts σ nm body t code res cert).ref
    idxWhy (boundFacts σ nm) (idxAnnot (boundFacts σ nm) B) B
  else if stage == "regionImgB" then
    match callee with
    | none =>
        let d := regionCoParts σ nm body t code res cert
        imgWhy (X86Backend.ImageStraightCells.slotArrC d.cells
          (slotRen (slotArrOf σ nm) (renOf d.ps))) d.cells (d.outs ++ d.cellOuts) body
    | some T =>
        let d := regionCoParts σ nm body t codeC res cert callee
        let c := callClassWhy T.frame body
        if c.isEmpty then
          callGateWhy (X86Backend.ImageAddrFrame.frameMark
              (X86Backend.ImageAddrFrame.frameNames body))
            (X86Backend.ImageStraightCells.slotArrC d.cells
              (slotRen (slotArrOf σ nm) (renOf d.ps))) body
        else s!"class printedAddrCWB: {c}"
  else if stage == "calleeBodyB" then
    match callee with
    | none => ""
    | some T =>
        let d := regionCoParts σ nm body t codeC res cert callee
        let sl := slotRen (slotArrOf σ nm) (renOf d.ps)
        let img := X86Backend.ImageAddrCall.callImg sl (siteFn T.lookup sl body) body
        bitsDeadWhy (X86Backend.ImageAddrFrame.frameMark
          (X86Backend.ImageAddrFrame.frameNames body)) (deadTab img d.outs) body
  else ""

open CatCrypt.Crypto.SecureCompilation.X86Backend.LinkShapeComplete (opdDispB
  narrowFreeB narrowIdxFreeB) in
/-- The first conjunct of `linkFormB F W Q i` that is `false`, in the order of its
    definition, or the empty string. -/
def linkFormConjWhy (F W Q : Nat) : LinstrR → String
  | .Lopn ds o ss =>
      let b := JasminLprogExport.stripWidthTag o
      if b == "ADOXHI" then "ADOXHI (seto has no decoder)"
      else if !(ds ++ ss).all (opdDispB F W Q) then "a displacement outside dispOk32"
      else if !narrowFreeB o then "narrowFreeB (32-bit or narrower operation)"
      else if !narrowIdxFreeB b ss then "narrowIdxFreeB (element stride other than 8)"
      else ""
  | _ => ""

open CatCrypt.Crypto.SecureCompilation.X86Backend.LinkShapeComplete (linkFormB) in
/-- The first instruction of `b` without a link form at the parameters of `b`, with the
    conjunct it fails; the empty string when every instruction has one. -/
def linkFormWhy (b : Lcmd) : String :=
  let P := Params.ofBody b
  match b.zipIdx.find? fun p => !linkFormB P.frame P.spillW P.qsaveB p.1.li_i with
  | some (i, k) =>
      s!"linkFormB at instruction {k} of {b.length}: {instrStr i.li_i}; " ++
        linkFormConjWhy P.frame P.spillW P.qsaveB i.li_i
  | none => ""

/-- The first component of `calleeLinkB T b` that is `false`, in the order of its definition,
    with the link forms reported before the shapes: the first function of the table with empty
    code, the first instruction without a link form (`linkFormWhy`), the first instruction
    without a computed shape, and the branch check with the program of the items. The empty
    string when the check holds. -/
def calleeLinkWhy (T : CalleeTab) (b : Lcmd) : String :=
  let P := Params.ofBody b
  match T.fns.find? (·.bytes.isEmpty) with
  | some c => s!"the code of the callee {c.name} is empty"
  | none =>
    if linkFormWhy b != "" then linkFormWhy b
    else
      match b.zipIdx.find? fun p => (X86Backend.DecodeGen.shapeOf P p.1.li_i).isNone with
      | some (i, k) => s!"no computed shape at instruction {k} of {b.length}: {instrStr i.li_i}"
      | none => if calleeLinkB T b then "" else "the branch check or the program of the items"

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionDiag
