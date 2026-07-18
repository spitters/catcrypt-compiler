import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopOwnedEmit

set_option autoImplicit false

namespace MpnFrontScratch

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)

abbrev N : Nat := 4
abbrev AN : JasminTy := .stackArr 64 N
def mask64 : Nat := 18446744073709551615

def seqAll : List LowCT → LowCT
  | [] => .RSkip
  | [c] => c
  | c :: cs => .RSeq c (seqAll cs)

/-! ### Binary no-carry (and/ior/xor): out[i] = a[i] OP b[i] -/

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

-- Γouter newest-first [n, b, a, out]: .here=n(a3→RCX), b(a2→RDX), a(a1→RSI), out(a0→RDI)
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
-- a OR b = (a XOR b) XOR (a AND b)   (no SOr in the SExpr alphabet)
def iorLprog : Option Lprog := binLprog "mpn_ior_n_loop_owned"
  (fun x y => .SXor (.SXor x y) (.SAnd x y))
def xorLprog : Option Lprog := binLprog "mpn_xor_n_loop_owned" .SXor

/-! ### Unary (com: r=~a, copyi: r=a) -/

def unBody (f : SExpr → SExpr) : LowCT := seqAll
  [ .RScalarSetExpr "ix" (.SVar "idx")
  , .RArrLoad ⟨"ai", .TU64⟩ ⟨"a", .TBytes (8 * N)⟩ "ix"
  , .RScalarSetExpr "r" (f (.SVar "ai"))
  , .RArrStore ⟨"out", .TBytes (8 * N)⟩ "ix" ⟨"r", .TU64⟩ ]

def ΓbodyUn : Ctx := [.memref N, .sword 64, .memref N]
def vmUn : VarMap ΓbodyUn :=
  (((VarMap.empty.bind (t := .memref N) "a").bind
      (t := .sword 64) "idx").bind (t := .memref N) "out")

-- Γouter newest-first [n, a, out]: .here=n(a2→RDX), a(a1→RSI), out(a0→RDI)
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

def comLprog : Option Lprog := unLprog "mpn_com_n_loop_owned" (fun x => .SXor x (.SLit mask64))
def copyLprog : Option Lprog := unLprog "mpn_copyi_loop_owned" (fun x => x)

/-! ### zero: r=0 -/

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

/-! ### isSome gates -/

theorem andLprog_isSome : andLprog.isSome := by native_decide
theorem iorLprog_isSome : iorLprog.isSome := by native_decide
theorem xorLprog_isSome : xorLprog.isSome := by native_decide
theorem comLprog_isSome : comLprog.isSome := by native_decide
theorem copyLprog_isSome : copyLprog.isSome := by native_decide
theorem zeroLprog_isSome : zeroLprog.isSome := by native_decide

/-! ### emit front no-carry .s, hand add/sub/blk/cmp from MpnLoopOwnedEmit -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopOwnedEmit

def emitScratch : IO Unit := do
  IO.FS.createDirAll "bench/integration/gen_com"
  let wr (p : String) (o : Option Lprog) : IO Unit := match o with
    | some lp => IO.FS.writeFile p (renderLprogAtt lp)
    | none => throw (IO.userError s!"front-compile failed for {p}")
  wr "bench/integration/gen_com/mpn_and_n_loop_owned.s" andLprog
  wr "bench/integration/gen_com/mpn_ior_n_loop_owned.s" iorLprog
  wr "bench/integration/gen_com/mpn_xor_n_loop_owned.s" xorLprog
  wr "bench/integration/gen_com/mpn_com_n_loop_owned.s" comLprog
  wr "bench/integration/gen_com/mpn_copyi_loop_owned.s" copyLprog
  wr "bench/integration/gen_com/mpn_zero_loop_owned.s" zeroLprog
  -- keep hand-authored add/sub/blk/cmp for now
  IO.FS.writeFile "bench/integration/gen_com/mpn_add_n_loop_owned.s" addAsm
  IO.FS.writeFile "bench/integration/gen_com/mpn_sub_n_loop_owned.s" subAsm
  IO.FS.writeFile "bench/integration/gen_com/mpn_add_n_blk4_loop_owned.s" addBlk4Asm
  IO.FS.writeFile "bench/integration/gen_com/mpn_sub_n_blk4_loop_owned.s" subBlk4Asm
  IO.FS.writeFile "bench/integration/gen_com/mpn_cmp_loop_owned.s" cmpAsm
  IO.println "wrote front no-carry .s + hand add/sub/cmp"

#eval (andLprog.map (fun _ => "and-some")).getD "and-NONE"

end MpnFrontScratch
