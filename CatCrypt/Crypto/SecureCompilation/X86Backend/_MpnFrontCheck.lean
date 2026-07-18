-- TEMPORARY elaboration-check file (deleted after use): inlines the new
-- JasminLprogExportScalarAcc defs + MpnLoopFrontEmit content with the
-- native_decide gates sorry-swapped, so the combined draft can be
-- LSP-elaborated against prebuilt imports only.
import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddCarryFrontPrototype

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

def ComL.toLfundefPhysAbiScalarAcc {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : ComL Γ t)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (abiArgs : List String := ["RDI", "RSI", "RDX", "RCX"])
    (abiTyin : List Nat := [64, 64, 64, 64]) :
    Lfundef :=
  let virt0 := ComL.toLfundef c immSlotMap
  let livePin : Lcmd :=
    if abiArgs.length ≥ 3 then
      [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
            ((List.range abiArgs.length).map (fun j => (.reg (argName j) : LOperand)))⟩]
    else []
  let body1 := livePin ++ canonicalizeMemrefThread virt0.lfd_body
  let virt := { virt0 with lfd_body := body1 }
  let tbl := physTableOut virt.lfd_body []
  let extraInputSaves : Lcmd :=
    (abiArgs.drop 2).filterMap (fun abiReg =>
      match abiSaveOfExt abiReg with
      | some saveName => some (⟨0, .Lopn [.reg saveName] "MOVQ" [.reg abiReg]⟩ : Linstr)
      | none => none)
  let prologue := buildPrologue virt tbl (fun _ => none) ++ extraInputSaves
  let argMat := buildArgPtrMaterialize virt tbl abiArgs (fun _ => none)
  let movTbl : Array (Option Nat) := movImmTable virt.lfd_body
  let shiftImm' : ShiftImmOracle := fun nm =>
    match shiftImm nm with
    | some v => some v
    | none => movImmLookup movTbl nm
  let memrefBaseReload : String → Option String :=
    let pairs : List (String × String) :=
      (abiArgs.zipIdx).filterMap (fun ⟨abiReg, j⟩ =>
        match abiSaveOfExt abiReg with
        | some saveName =>
            some (physNameForBody virt.lfd_body tbl (argName j), saveName)
        | none => none)
    fun base => (pairs.find? (fun p => p.1 == base)).map Prod.snd
  let bodyWithReload := (physBodyWithStores shiftImm' virt.lfd_body
    (fun _ => none) reloadScratch2 [] reloadScratch2 0 memrefBaseReload).filter
    (fun i => match i.li_i with | .Lopn _ opn _ => opn != "LIVEPIN" | _ => true)
  let retMat : Lcmd :=
    match virt.lfd_res.head? with
    | some rn =>
        let phys := physNameForBody virt.lfd_body tbl rn
        if phys == sysvRetReg then []
        else [⟨0, .Lopn [.reg sysvRetReg] "MOVQ" [.reg phys]⟩]
    | none => []
  let bodyWithRestore := insertEpilogue bodyWithReload (retMat ++ calleeSaveRestoreEpilogue)
  { virt with
    lfd_body := prologue ++ argMat ++ bodyWithRestore
    lfd_arg := abiArgs
    lfd_tyin := abiTyin
    lfd_res := [sysvRetReg]
    lfd_tyout := [64] }

def ComL.toLprogPhysAbiScalarAcc {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : ComL Γ t) (fname : String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (abiArgs : List String := ["RDI", "RSI", "RDX", "RCX"])
    (abiTyin : List Nat := [64, 64, 64, 64]) : Lprog :=
  { lp_rip := "RIP"
    lp_rsp := "RSP"
    lp_globs := []
    lp_glob_names := []
    lp_funcs :=
      [(fname, ComL.toLfundefPhysAbiScalarAcc c shiftImm immSlotMap
                 abiArgs abiTyin)] }

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopFrontEmit

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddCarryFrontPrototype
  (seqAll halfCarry mask64 N AN r64 Γbody addBodyLowCT)

def binBody (op : SExpr → SExpr → SExpr) : LowCT := seqAll
  [ .RScalarSetExpr "ix" (.SVar "idx")
  , .RArrLoad ⟨"ai", .TU64⟩ ⟨"a", .TBytes (8 * N)⟩ "ix"
  , .RArrLoad ⟨"bi", .TU64⟩ ⟨"b", .TBytes (8 * N)⟩ "ix"
  , .RScalarSetExpr "r" (op (.SVar "ai") (.SVar "bi"))
  , .RArrStore ⟨"out", .TBytes (8 * N)⟩ "ix" ⟨"r", .TU64⟩ ]

def ΓbodyBin : Ctx := [.memref N, .sword 64, .memref N, .memref N]
def vmBin : VarMap ΓbodyBin :=
  ((((VarMap.empty.bind (t := .memref N) "b").bind
      (t := .memref N) "a").bind (t := .sword 64) "idx").bind (t := .memref N) "out")

def ΓouterBin : Ctxt jasminDialect := [.reg 64, AN, AN, AN]

def binLprog (name : String) (op : SExpr → SExpr → SExpr) : Option Lprog :=
  rolledForLoopNRtLprog (Γouter := ΓouterBin) (accCTy := .memref N)
    (invCTys := [.memref N, .memref N])
    vmBin "out" (binBody op)
    (count := .here)
    (init := .there (.there (.there .here)))
    (invs := .cons (.there (.there .here)) (.cons (.there .here) .nil))
    name (argName 0) [argName 1, argName 2]
    ["RDI", "RSI", "RDX", "RCX"] [64, 64, 64, 64]

def andLprog : Option Lprog := binLprog "mpn_and_n_loop_owned" .SAnd
def iorLprog : Option Lprog := binLprog "mpn_ior_n_loop_owned"
  (fun x y => .SXor (.SXor x y) (.SAnd x y))
def xorLprog : Option Lprog := binLprog "mpn_xor_n_loop_owned" .SXor

def unBody (f : SExpr → SExpr) : LowCT := seqAll
  [ .RScalarSetExpr "ix" (.SVar "idx")
  , .RArrLoad ⟨"ai", .TU64⟩ ⟨"a", .TBytes (8 * N)⟩ "ix"
  , .RScalarSetExpr "r" (f (.SVar "ai"))
  , .RArrStore ⟨"out", .TBytes (8 * N)⟩ "ix" ⟨"r", .TU64⟩ ]

def ΓbodyUn : Ctx := [.memref N, .sword 64, .memref N]
def vmUn : VarMap ΓbodyUn :=
  (((VarMap.empty.bind (t := .memref N) "a").bind
      (t := .sword 64) "idx").bind (t := .memref N) "out")

def ΓouterUn : Ctxt jasminDialect := [.reg 64, AN, AN]

def unLprog (name : String) (f : SExpr → SExpr) : Option Lprog :=
  rolledForLoopNRtLprog (Γouter := ΓouterUn) (accCTy := .memref N)
    (invCTys := [.memref N])
    vmUn "out" (unBody f)
    (count := .here)
    (init := .there (.there .here))
    (invs := .cons (.there .here) .nil)
    name (argName 0) [argName 1]
    ["RDI", "RSI", "RDX"] [64, 64, 64]

def comLprog : Option Lprog := unLprog "mpn_com_n_loop_owned"
  (fun x => .SXor x (.SLit mask64))
def copyLprog : Option Lprog := unLprog "mpn_copyi_loop_owned" (fun x => x)

def zeroBody : LowCT := seqAll
  [ .RScalarSetExpr "ix" (.SVar "idx")
  , .RScalarSetExpr "r" (.SLit 0)
  , .RArrStore ⟨"out", .TBytes (8 * N)⟩ "ix" ⟨"r", .TU64⟩ ]

def ΓbodyZero : Ctx := [.memref N, .sword 64]
def vmZero : VarMap ΓbodyZero :=
  ((VarMap.empty.bind (t := .sword 64) "idx").bind (t := .memref N) "out")

def ΓouterZero : Ctxt jasminDialect := [.reg 64, AN]

def zeroLprog : Option Lprog :=
  rolledForLoopNRtLprog (Γouter := ΓouterZero) (accCTy := .memref N)
    (invCTys := [])
    vmZero "out" zeroBody
    (count := .here)
    (init := .there .here)
    (invs := .nil)
    "mpn_zero_loop_owned" (argName 0) []
    ["RDI", "RSI"] [64, 64]

def ΓouterCarry : Ctxt jasminDialect := [r64, r64, AN, AN, AN]

def mpnSeedImm : ImmSlotMap := fun j => if j == 4 then some 0 else none

def gmpAbiArgs : List String := ["RDI", "RSI", "RDX", "RCX"]

def addRtProgOpt : Option (ComL ΓouterCarry (mapTy (.sword 64))) :=
  rolledForLoopNRt (Γouter := ΓouterCarry) (accCTy := .sword 64)
    (invCTys := [.memref N, .memref N, .memref N])
    CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddCarryFrontPrototype.vmBody
    "cy" addBodyLowCT
    (count := .there .here)
    (init := .here)
    (invs := .cons (.there (.there (.there .here)))
      (.cons (.there (.there .here))
        (.cons (.there (.there (.there (.there .here)))) .nil)))

def subBodyLowCT : LowCT := seqAll
  [ .RScalarSetExpr "ix" (.SVar "idx")
  , .RArrLoad ⟨"ai", .TU64⟩ ⟨"a", .TBytes (8 * N)⟩ "ix"
  , .RArrLoad ⟨"bi", .TU64⟩ ⟨"b", .TBytes (8 * N)⟩ "ix"
  , .RScalarSetExpr "nb" (.SXor (.SVar "bi") (.SLit mask64))
  , .RScalarSetExpr "cx" (.SXor (.SVar "bw") (.SLit 1))
  , .RScalarSetExpr "c1" (halfCarry "ai" "nb")
  , .RScalarSetExpr "s1" (.SAnd (.SAdd (.SVar "ai") (.SVar "nb")) (.SLit mask64))
  , .RScalarSetExpr "c2" (halfCarry "s1" "cx")
  , .RScalarSetExpr "df" (.SAnd (.SAdd (.SVar "s1") (.SVar "cx")) (.SLit mask64))
  , .RArrStore ⟨"out", .TBytes (8 * N)⟩ "ix" ⟨"df", .TU64⟩
  , .RScalarSetExpr "bw" (.SXor (.SAdd (.SVar "c1") (.SVar "c2")) (.SLit 1)) ]

def vmBodySub : VarMap Γbody :=
  (((((VarMap.empty.bind (t := .memref N) "out").bind
      (t := .memref N) "b").bind
      (t := .memref N) "a").bind
      (t := .sword 64) "idx").bind
      (t := .sword 64) "bw")

def subRtProgOpt : Option (ComL ΓouterCarry (mapTy (.sword 64))) :=
  rolledForLoopNRt (Γouter := ΓouterCarry) (accCTy := .sword 64)
    (invCTys := [.memref N, .memref N, .memref N])
    vmBodySub "bw" subBodyLowCT
    (count := .there .here)
    (init := .here)
    (invs := .cons (.there (.there (.there .here)))
      (.cons (.there (.there .here))
        (.cons (.there (.there (.there (.there .here)))) .nil)))

def addLprogFront : Option Lprog :=
  addRtProgOpt.map (fun c =>
    ComL.toLprogPhysAbiScalarAcc c "mpn_add_n_loop_owned"
      (fun _ => none) mpnSeedImm gmpAbiArgs [64, 64, 64, 64])

def subLprogFront : Option Lprog :=
  subRtProgOpt.map (fun c =>
    ComL.toLprogPhysAbiScalarAcc c "mpn_sub_n_loop_owned"
      (fun _ => none) mpnSeedImm gmpAbiArgs [64, 64, 64, 64])

-- Gates sorry-swapped for the elaboration check (real file: native_decide;
-- ORCHESTRATOR-VERIFY).
theorem andLprog_isSome : andLprog.isSome := by sorry
theorem addLprogFront_isSome : addLprogFront.isSome := by sorry
theorem subLprogFront_isSome : subLprogFront.isSome := by sorry

open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)

def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/integration/gen_com"
  let wr (p : String) (o : Option Lprog) : IO Unit := do
    match o with
    | some lp => IO.FS.writeFile p (renderLprogAtt lp)
    | none => throw (IO.userError s!"front-compile failed for {p}")
  wr "bench/integration/gen_com/mpn_and_n_loop_owned.s" andLprog
  wr "bench/integration/gen_com/mpn_ior_n_loop_owned.s" iorLprog
  wr "bench/integration/gen_com/mpn_xor_n_loop_owned.s" xorLprog
  wr "bench/integration/gen_com/mpn_com_n_loop_owned.s" comLprog
  wr "bench/integration/gen_com/mpn_copyi_loop_owned.s" copyLprog
  wr "bench/integration/gen_com/mpn_zero_loop_owned.s" zeroLprog
  wr "bench/integration/gen_com/mpn_add_n_loop_owned.s" addLprogFront
  wr "bench/integration/gen_com/mpn_sub_n_loop_owned.s" subLprogFront
  IO.println "wrote 8 front-sourced mpn loop kernels (add/sub via scalar-acc export)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopFrontEmit
