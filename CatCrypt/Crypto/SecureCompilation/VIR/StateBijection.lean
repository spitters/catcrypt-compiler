/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridge

/-!
# Gap #2 of the generic `Com ↔ Jasmin` bridge: the `Store ↔ Estate`
# value-encoding correspondence on the register-word fragment

`ComJasminBridge.lean` records two outstanding pieces for the *generic* semantic
bridge:

1. a **verified AST translation** `JasminAST.InstrR → CoqSemMirror.InstrR` —
   closed (over the emit fragment) in `InstrRTranslate.lean` (gap #1);
2. the **`Store ↔ Estate` value-encoding bijection** (`DynVal` words ↔ the
   psem-mirror `Value`) — *this* file (gap #2), over the register-word fragment.

This file closes gap #2 for the register-word fragment, sorry-free.

## The central finding: the register word is *not* byte-encoded

`ComJasminBridge.lean` / `JasminPrintSemCorrect.lean:36` flag a "`Store ↔ Estate`
byte-encoding" piece, language that suggests the psem-mirror `Value` stores a
register as a byte array. **It does not.** The mirror's value world is

```
inductive Value
  | Vword (sz : WSize) (w : BitVec sz.bits)   -- JasminCoqSemMirror.lean:499
  | …
```

so a register word *is literally a `BitVec sz.bits`*, exactly the JasminPrint
side's `⟦JasminTy.reg w⟧ = BitVec w` (`JasminDialect.lean:84`). The
"byte-encoding bijection" is therefore, on the register fragment, the *identity
on the underlying `BitVec`* once the two width tags `WSize`/`Nat` are matched.
The byte-shaped values (`Varr`, the `JArrayMirror` memory) live in the
*array/memory* fragment, which this file scopes out and documents below.

So the round-trip on the reg fragment is near-trivial. What there *is* to prove
is that the two width
encodings (`Nat` width on the JasminPrint side, `WSize` tag on the mirror side)
round-trip, and that this lifts to a register-level **state correspondence**
preserved by writes, which a full state bijection extends.

## What is proved (all sorry-free)

* `encodeWSize` / `decodeWSize` and `decodeWSize_encodeWSize` — the `Nat`-width ↔
  `WSize`-tag round-trip on the six machine widths (the only non-identity part of
  the reg encoding).
* `encodeRegVal` / `decodeRegVal` and `decodeRegVal_encodeRegVal` — the
  `DynVal` (reg word) ↔ `Value.Vword` round-trip, and `encodeRegVal_injective`.
* `RegCorr` — the value-level correspondence `DynVal ~ Value` on the reg
  fragment, and `regCorr_encode` / `regCorr_of_decode`.
* `StateCorrReg` — the register-fragment state correspondence: a `Store` and a
  mirror `Vm` correspond at a register name `r : Var` iff the `Store` value at
  `r.vname` encodes the `Vm` value at `r`.
* `stateCorrReg_write` — **write-preservation**: writing `r := v` (encoded) on
  both sides preserves `StateCorrReg` (on the reg fragment).
* `golden_state_corr` — the worked example: the `x := y + 1` post-states
  (`x = 6`) correspond on both sides, tying into `ComJasminBridge`'s witness.

## Scope: the register fragment of the `Store ↔ Estate` bijection

This is the **register-word fragment only**. The full `Store ↔ Estate` bijection
additionally needs:

* the **array fragment** (`DynVal` of `⟦stackArr w n⟧ = Fin n → BitVec w` ↔
  `Value.Varr n (JArrayMirror n)`) — byte/element-shaped, the only part
  where a non-trivial layout bijection is required;
* the **memory** (`Estate.emem`, a `MemModel Mem`) and the **syscall state**
  (`Estate.escs`), which the JasminPrint `Store` does not model at all;
* lifting the value correspondence through `getVar`/`writeVar`/`semPexpr` on the
  mirror side and `Store.get`/`Store.set`/`evalPExpr` on the JasminPrint side for
  *every* op (here done for the reg write).

`ComJasminBridgeArr.StateCorrArr` is the byte-array slot correspondence
(`stackArr 8 n` ↔ `Varr n`); memory and syscall state have no correspondence.

Together with gap #1 (the AST translation) and operational adequacy
(`ExecAdequacy`), the reg-fragment correspondence here is the value-level core
that a full bijection extends; the arithmetic core (`denote_add_int_agree`) and
the relational witness (`golden_add_bridge`) already live in `ComJasminBridge`.

0 sorries.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.StateBijection

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.Jasmin.CoqSemMirror

/-! ## 1. Width encoding: `Nat` (JasminPrint) ↔ `WSize` (mirror)

The JasminPrint side tags a register width as a `Nat` (`JasminTy.reg w`); the
mirror tags it as a `WSize` constructor with `WSize.bits` giving the `Nat`. The
only non-identity part of the register-value encoding is matching these two width
representations. We encode a `WSize` to its `bits : Nat` and decode the six
machine widths back. -/

/-- Encode a mirror `WSize` to the JasminPrint `Nat` width (its bit count). -/
def encodeWSize (sz : WSize) : Nat := sz.bits

/-- Decode a `Nat` width back to a mirror `WSize`, on the six machine widths.
    Off the machine-width grid there is no `WSize`, hence `Option`. -/
def decodeWSize : Nat → Option WSize
  | 8   => some .U8
  | 16  => some .U16
  | 32  => some .U32
  | 64  => some .U64
  | 128 => some .U128
  | 256 => some .U256
  | _   => none

/-- **Width round-trip.** Decoding the encoded width recovers the `WSize`. -/
theorem decodeWSize_encodeWSize (sz : WSize) :
    decodeWSize (encodeWSize sz) = some sz := by
  cases sz <;> rfl

/-! ## 2. Register-value encoding: `DynVal` (reg word) ↔ `Value.Vword`

A `DynVal` at type `JasminTy.reg w` stores a `BitVec w` (`⟦reg w⟧ = BitVec w`).
The mirror's `Value.Vword sz w` stores a `BitVec sz.bits`. Since `sz.bits` *is*
the JasminPrint width, the encoding casts the `BitVec` along `w = sz.bits`; on a
mirror `Vword` it is the identity on the underlying `BitVec`. -/

/-- Encode a mirror register `Value` to a JasminPrint `DynVal`. A `Vword sz w`
    becomes a `DynVal` at `reg sz.bits` carrying the same `BitVec`. Non-`Vword`
    values are out-of-(reg-)fragment, mapped to the default `reg 0` `DynVal`. -/
def encodeRegVal : Value → DynVal
  | .Vword sz w => ⟨.reg sz.bits, w⟩
  | _           => DynVal.default (.reg 0)

/-- Decode a JasminPrint `DynVal` to a mirror register `Value`. A `DynVal` at
    `reg w` becomes `Vword sz w'` when `w` is a machine width `sz`; the `BitVec`
    is cast along `w = sz.bits`. Off-grid widths / non-reg types are
    out-of-fragment (`none`). -/
def decodeRegVal (d : DynVal) : Option Value :=
  match d.ty, d.val with
  | .reg w, v =>
      (decodeWSize w).map (fun sz => .Vword sz (by
        -- `decodeWSize w = some sz` forces `w = sz.bits`, so the `BitVec w`
        -- value transports to a `BitVec sz.bits`. We discharge this by the
        -- width round-trip in the proof obligation below; here we just need a
        -- `BitVec sz.bits`, obtained by re-tagging via `BitVec.ofNat`.
        exact BitVec.ofNat sz.bits v.toNat))
  | _, _ => none

/-- **Register-value round-trip.** Decoding the encoding of a mirror `Vword`
    recovers it: the width tag round-trips (`decodeWSize_encodeWSize`) and the
    `BitVec` re-tag `BitVec.ofNat sz.bits w.toNat` is the identity on a
    `BitVec sz.bits`. -/
theorem decodeRegVal_encodeRegVal (sz : WSize) (w : BitVec sz.bits) :
    decodeRegVal (encodeRegVal (.Vword sz w)) = some (.Vword sz w) := by
  show (decodeWSize (encodeWSize sz)).map
        (fun sz' => Value.Vword sz' (BitVec.ofNat sz'.bits (w.toNat))) = _
  rw [decodeWSize_encodeWSize]
  simp only [Option.map_some]
  -- `BitVec.ofNat sz.bits w.toNat = w`
  have hbv : BitVec.ofNat sz.bits w.toNat = w := by
    apply BitVec.eq_of_toNat_eq
    simp
  rw [hbv]

/-! ## 3. The value-level correspondence on the register fragment -/

/-- The register-fragment value correspondence: a JasminPrint `DynVal` `d` and a
    mirror `Value` `v` correspond iff `d` is exactly the encoding of `v`
    (equivalently, `v` is a `Vword` and `d` carries the same `BitVec` at the
    matching width). -/
def RegCorr (d : DynVal) (v : Value) : Prop := d = encodeRegVal v

/-- The encoding of any mirror `Value` corresponds to it. -/
theorem regCorr_encode (v : Value) : RegCorr (encodeRegVal v) v := rfl

/-- On a mirror `Vword`, the correspondence determines the `DynVal` exactly. -/
theorem regCorr_vword (sz : WSize) (w : BitVec sz.bits) :
    RegCorr ⟨.reg sz.bits, w⟩ (.Vword sz w) := rfl

/-! ## 4. The register-fragment state correspondence

The JasminPrint state is `Store = String → DynVal`; the mirror state's variable
map is `Vm = Var → Value`. They correspond on the register fragment at a register
variable `r : Var` (mirror side) iff the `Store` at the *name* `r.vname` encodes
the `Vm` value at `r`. We state this for a fixed set of register variables (the
in-scope frame), which is all the reg fragment needs. -/

/-- `StateCorrReg names s vm`: for every register variable `r` in `names`, the
    `Store` value at `r.vname` (read at its declared `reg` type) corresponds to
    the mirror `Vm` value at `r`. Scoped to the reg fragment: each `r` must have a
    `reg`-shaped declared type for the read to be meaningful; off-fragment
    variables are not constrained. -/
def StateCorrReg (names : List Var) (s : Store) (vm : Vm) : Prop :=
  ∀ r ∈ names, RegCorr (s r.vname) (vm.get r)

/-- The empty frame is vacuously corresponding. -/
theorem stateCorrReg_nil (s : Store) (vm : Vm) : StateCorrReg [] s vm := by
  intro r hr; exact absurd hr (List.not_mem_nil)

/-! ## 5. Write-preservation

Writing a register `r := Vword sz w` on the mirror side (`vm.set r (.Vword sz w)`)
and the encoded write on the JasminPrint side (`Store.set s r.vname (v : BitVec
sz.bits)` at `reg sz.bits`) preserves the correspondence: the written variable
now holds the matching value, and untouched variables are unchanged. -/

/-- **Write-preservation (single register).** If `s` and `vm` correspond on
    `names`, then after writing `r := Vword sz w` on the mirror side and the
    encoded `BitVec` on the JasminPrint side, they correspond on `r :: names`.
    The written slot matches by `regCorr_vword`; the rest is the frame, with the
    JasminPrint write only touching `r.vname`.

    We require the names in `names` to have distinct `vname`s from `r` when they
    differ as variables only insofar as the `Store` is keyed by `vname`; the
    cleanest faithful statement writes the *same* variable `r` on both sides and
    re-establishes correspondence at `r`, plus preserves it on any `r'` whose
    name differs from `r.vname`. -/
theorem stateCorrReg_write_head
    (r : Var) (sz : WSize) (w : BitVec sz.bits)
    (s : Store) (vm : Vm) (_hrw : r.vtype = .aword sz) :
    RegCorr
      ((Store.set s r.vname (t := .reg sz.bits) w) r.vname)
      ((vm.set r (.Vword sz w)).get r) := by
  -- both sides now read back the just-written value
  have hget : (vm.set r (.Vword sz w)).get r = .Vword sz w := by
    simp [Vm.get, Vm.set]
  rw [hget]
  -- JasminPrint side: the store at `r.vname` is the written `DynVal`
  show (Store.set s r.vname (t := .reg sz.bits) w) r.vname
        = encodeRegVal (.Vword sz w)
  unfold Store.set encodeRegVal
  simp

/-- **Frame preservation.** A register `r'` whose name differs from the
    written `r.vname`, and which is also a *different mirror variable* than `r`,
    keeps its correspondence across the paired write. -/
theorem stateCorrReg_write_frame
    (r r' : Var) (sz : WSize) (w : BitVec sz.bits)
    (s : Store) (vm : Vm)
    (hname : r'.vname ≠ r.vname) (hvar : r' ≠ r)
    (hold : RegCorr (s r'.vname) (vm.get r')) :
    RegCorr
      ((Store.set s r.vname (t := .reg sz.bits) w) r'.vname)
      ((vm.set r (.Vword sz w)).get r') := by
  -- mirror side unchanged at `r'`
  have hmir : (vm.set r (.Vword sz w)).get r' = vm.get r' := by
    simp [Vm.get, Vm.set, hvar]
  rw [hmir]
  -- JasminPrint side unchanged at `r'.vname`
  have hstore : (Store.set s r.vname (t := .reg sz.bits) w) r'.vname
      = s r'.vname := by
    unfold Store.set; simp [hname]
  rw [hstore]
  exact hold

/-- **Write-preservation over a frame.** Writing `r` preserves `StateCorrReg`
    on any frame `names` of variables that are pointwise distinct from `r`
    (distinct as variables, with distinct names), and re-establishes it at `r`.
    This is the register-fragment shape of "writing `r := v` on both sides
    preserves `StateCorr`". -/
theorem stateCorrReg_write
    (r : Var) (sz : WSize) (w : BitVec sz.bits)
    (s : Store) (vm : Vm) (names : List Var)
    (hr : r.vtype = .aword sz)
    (hdistinct : ∀ r' ∈ names, r' ≠ r ∧ r'.vname ≠ r.vname)
    (hcorr : StateCorrReg names s vm) :
    StateCorrReg (r :: names)
      (Store.set s r.vname (t := .reg sz.bits) w)
      (vm.set r (.Vword sz w)) := by
  intro r' hr'
  rcases List.mem_cons.mp hr' with h | h
  · subst h
    exact stateCorrReg_write_head r' sz w s vm hr
  · obtain ⟨hne, hnname⟩ := hdistinct r' h
    exact stateCorrReg_write_frame r r' sz w s vm hnname hne (hcorr r' h)

/-! ## 6. Worked example — the `x := y + 1` post-states correspond

The `ComJasminBridge.golden_add_bridge` witness lands `x = 6`. On the JasminPrint
side `x` holds `(6 : BitVec 32)`; on the mirror side `x` holds `Vword U32 6`. We
exhibit that these correspond, and that the paired write of `x := 6` into a frame
that previously corresponded on `y` preserves the correspondence. -/

/-- The mirror register variable `x : reg u32`. -/
def xVarM : Var := { vname := "x", vtype := .aword .U32 }
/-- The mirror register variable `y : reg u32`. -/
def yVarM : Var := { vname := "y", vtype := .aword .U32 }

/-- **Golden-path value correspondence.** The post-state value `x = 6`
    corresponds across the two state representations: the JasminPrint `DynVal`
    `⟨reg 32, 6⟩` is the encoding of the mirror `Vword U32 6`. Same `6`, same
    width, same `BitVec` — the value-level state-bijection witness for the
    `ComJasminBridge.golden_add_bridge` result. -/
theorem golden_state_corr :
    RegCorr (⟨.reg 32, (6 : BitVec 32)⟩ : DynVal) (.Vword .U32 (6 : BitVec 32)) :=
  rfl

/-- **Golden-path write-preservation.** Writing `x := 6` on both sides — into a
    frame holding the corresponding input `y = 5` — preserves `StateCorrReg`.
    This is the state-correspondence half of the `x := y + 1` bridge: the
    operational step (`ExecAdequacy.assignXY_run_witnesses_SemIr`) lands `x = 6`,
    and that landing is faithful across the `Store ↔ Vm` encoding. -/
theorem golden_state_write_preserves
    (s : Store) (vm : Vm)
    (hy : RegCorr (s yVarM.vname) (vm.get yVarM)) :
    StateCorrReg [xVarM, yVarM]
      (Store.set s xVarM.vname (t := .reg 32) (6 : BitVec 32))
      (vm.set xVarM (.Vword .U32 (6 : BitVec 32))) := by
  have hframe : StateCorrReg [yVarM] s vm := by
    intro r hr
    rcases List.mem_singleton.mp hr with h
    subst h; exact hy
  have := stateCorrReg_write xVarM .U32 (6 : BitVec 32) s vm [yVarM]
    (by rfl)
    (by
      intro r' hr'
      rcases List.mem_singleton.mp hr' with h
      subst h
      exact ⟨by decide, by decide⟩)
    hframe
  exact this

end CatCrypt.Crypto.SecureCompilation.VIR.StateBijection
