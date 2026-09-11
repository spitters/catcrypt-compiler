/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.JasminTranslate

/-!
# AES Jasmin Program (AST Representation)

This file encodes the Jasmin AES-128 implementation as Lean AST values,
matching the program from `aes_jazz.v` in the CatCrypt jasmin branch.

The program consists of three functions:
1. `keys_expand` — AES-128 key expansion (10 rounds)
2. `aes_rounds` — AES encryption rounds (9 main + 1 final)
3. `aes` — Top-level: key expansion + encryption

## References

- `aes_jazz.v` from CatCrypt jasmin branch
- Jasmin AES-NI implementation
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.AES

/-! ## Variable Declarations -/

/-- AES key parameter. -/
def vKey : Var := { vname := "key", vtype := .sword .U128 }
/-- AES plaintext message parameter. -/
def vMsg : Var := { vname := "msg", vtype := .sword .U128 }
/-- AES ciphertext result. -/
def vCipher : Var := { vname := "cipher", vtype := .sword .U128 }
/-- Round keys array (11 × 128-bit keys = 176 bytes). -/
def vRKeys : Var := { vname := "rkeys", vtype := .sarr 176 }
/-- Current state during encryption. -/
def vState : Var := { vname := "state", vtype := .sword .U128 }
/-- Temporary for key expansion. -/
def vTmp1 : Var := { vname := "tmp1", vtype := .sword .U128 }
/-- Temporary for key expansion. -/
def vTmp2 : Var := { vname := "tmp2", vtype := .sword .U128 }
/-- Round constant. -/
def vRCon : Var := { vname := "rcon", vtype := .sword .U128 }
/-- Loop counter. -/
def vI : Var := { vname := "i", vtype := .sint }

/-! ## Helper: VarI and GVar construction -/

def mkVarI (v : Var) : VarI := { var := v }
def mkGVar (v : Var) : GVar := { gv := mkVarI v, gs := false }
def mkLVar (v : Var) : LVal := .Lvar (mkVarI v)
def mkPVar (v : Var) : PExpr := .Pvar (mkGVar v)

/-! ## AES Key Expansion

Jasmin pseudocode:
```
fn keys_expand(reg u128 key) -> stack u128[11] {
  stack u128[11] rkeys;
  reg u128 tmp1, tmp2;
  rkeys[0] = key;
  // Round 1
  tmp1 = VAESKEYGENASSIST(key, 0x01);
  tmp1 = VPSHUFD(tmp1, 0xFF);
  tmp2 = VPSLLDQ(key, 4);
  key = key ^ tmp2;
  tmp2 = VPSLLDQ(key, 4);
  key = key ^ tmp2;
  tmp2 = VPSLLDQ(key, 4);
  key = key ^ tmp2;
  key = key ^ tmp1;
  rkeys[1] = key;
  // ... rounds 2–10 similarly with different rcon
}
```
-/

/-- Single key expansion round as Jasmin instructions.
    `expandRound rconByte roundIdx` produces instructions for one round. -/
def expandRound (rconByte : Int) (roundIdx : Nat) : Cmd :=
  let aeskeygenassist := SOpn.Oasm { name := "VAESKEYGENASSIST" }
  let vpshufd := SOpn.Oasm { name := "VPSHUFD" }
  let vpslldq := SOpn.Oasm { name := "VPSLLDQ" }
  let vpxor := SOpn.Oasm { name := "VPXOR" }
  [ -- tmp1 = VAESKEYGENASSIST(key, rcon)
    .Copn [mkLVar vTmp1] .AT_none aeskeygenassist
      [mkPVar vKey, .Pconst rconByte],
    -- tmp1 = VPSHUFD(tmp1, 0xFF)
    .Copn [mkLVar vTmp1] .AT_none vpshufd
      [mkPVar vTmp1, .Pconst 0xFF],
    -- tmp2 = VPSLLDQ(key, 4)
    .Copn [mkLVar vTmp2] .AT_none vpslldq
      [mkPVar vKey, .Pconst 4],
    -- key = key ^ tmp2
    .Copn [mkLVar vKey] .AT_none vpxor
      [mkPVar vKey, mkPVar vTmp2],
    -- tmp2 = VPSLLDQ(key, 4)
    .Copn [mkLVar vTmp2] .AT_none vpslldq
      [mkPVar vKey, .Pconst 4],
    -- key = key ^ tmp2
    .Copn [mkLVar vKey] .AT_none vpxor
      [mkPVar vKey, mkPVar vTmp2],
    -- tmp2 = VPSLLDQ(key, 4)
    .Copn [mkLVar vTmp2] .AT_none vpslldq
      [mkPVar vKey, .Pconst 4],
    -- key = key ^ tmp2
    .Copn [mkLVar vKey] .AT_none vpxor
      [mkPVar vKey, mkPVar vTmp2],
    -- key = key ^ tmp1
    .Copn [mkLVar vKey] .AT_none vpxor
      [mkPVar vKey, mkPVar vTmp1],
    -- rkeys[roundIdx] = key (as array set)
    .Cassgn (.Laset .AAscale .U128 (mkVarI vRKeys) (.Pconst roundIdx))
      .AT_none (.sword .U128) (mkPVar vKey) ]

/-- Full key expansion body. -/
def keysExpandBody : Cmd :=
  -- rkeys[0] = key
  [ .Cassgn (.Laset .AAscale .U128 (mkVarI vRKeys) (.Pconst 0))
      .AT_none (.sword .U128) (mkPVar vKey) ] ++
  -- Rounds 1–10 with respective rcon values
  expandRound 0x01 1 ++ expandRound 0x02 2 ++ expandRound 0x04 3 ++
  expandRound 0x08 4 ++ expandRound 0x10 5 ++ expandRound 0x20 6 ++
  expandRound 0x40 7 ++ expandRound 0x80 8 ++ expandRound 0x1B 9 ++
  expandRound 0x36 10

/-- Key expansion function declaration. -/
def keysExpandFun : FunDecl :=
  { name := { name := "keys_expand" },
    params := [{ var := mkVarI vKey }],
    body := keysExpandBody,
    results := [mkVarI vRKeys] }

/-! ## AES Encryption Rounds

```
fn aes_rounds(stack u128[11] rkeys, reg u128 msg) -> reg u128 {
  reg u128 state;
  state = msg ^ rkeys[0];
  state = AESENC(state, rkeys[1]);
  ...
  state = AESENC(state, rkeys[9]);
  state = AESENCLAST(state, rkeys[10]);
  return state;
}
```
-/

/-- Single encryption round instruction. -/
def aesencRound (roundIdx : Nat) : InstrR :=
  let aesenc := SOpn.Oasm { name := "AESENC" }
  .Copn [mkLVar vState] .AT_none aesenc
    [mkPVar vState,
     .Pget .AAscale .U128 (mkGVar vRKeys) (.Pconst roundIdx)]

/-- Final encryption round instruction. -/
def aesenclastRound : InstrR :=
  let aesenclast := SOpn.Oasm { name := "AESENCLAST" }
  .Copn [mkLVar vState] .AT_none aesenclast
    [mkPVar vState,
     .Pget .AAscale .U128 (mkGVar vRKeys) (.Pconst 10)]

/-- AES rounds function body. -/
def aesRoundsBody : Cmd :=
  let vpxor := SOpn.Oasm { name := "VPXOR" }
  -- state = msg ^ rkeys[0]
  [ .Copn [mkLVar vState] .AT_none vpxor
      [mkPVar vMsg,
       .Pget .AAscale .U128 (mkGVar vRKeys) (.Pconst 0)] ] ++
  -- 9 main rounds: AESENC(state, rkeys[i]) for i = 1..9
  (List.range 9).map (fun i => aesencRound (i + 1)) ++
  -- Final round: AESENCLAST(state, rkeys[10])
  [aesenclastRound]

/-- AES rounds function declaration. -/
def aesRoundsFun : FunDecl :=
  { name := { name := "aes_rounds" },
    params := [{ var := mkVarI vRKeys }, { var := mkVarI vMsg }],
    body := aesRoundsBody,
    results := [mkVarI vState] }

/-! ## Top-Level AES Function

```
fn aes(reg u128 key, reg u128 msg) -> reg u128 {
  stack u128[11] rkeys;
  reg u128 cipher;
  rkeys = keys_expand(key);
  cipher = aes_rounds(rkeys, msg);
  return cipher;
}
```
-/

/-- Top-level AES function body (key expansion + encryption). -/
def aesBody : Cmd :=
  [ -- rkeys = keys_expand(key)
    .Ccall .DoInline [mkLVar vRKeys] { name := "keys_expand" }
      [mkPVar vKey],
    -- cipher = aes_rounds(rkeys, msg)
    .Ccall .DoInline [mkLVar vCipher] { name := "aes_rounds" }
      [mkPVar vRKeys, mkPVar vMsg] ]

/-- Top-level AES function declaration. -/
def aesFun : FunDecl :=
  { name := { name := "aes" },
    params := [{ var := mkVarI vKey }, { var := mkVarI vMsg }],
    body := aesBody,
    results := [mkVarI vCipher] }

/-! ## Complete AES Program -/

/-- The complete Jasmin AES program with all three functions. -/
def aesProg : JasminProg :=
  { funcs := [keysExpandFun, aesRoundsFun, aesFun] }

/-- Function name for the AES entry point. -/
def aesEntryFn : FunName := { name := "aes" }

/-- Translate the AES program to RawCode. -/
noncomputable def aesTranslated (key msg : TypedValue) :
    Option (CatCrypt.Deep.RawCode (List TypedValue)) :=
  translateProg aesProg aesEntryFn [key, msg]

end CatCrypt.Crypto.Jasmin.AES
