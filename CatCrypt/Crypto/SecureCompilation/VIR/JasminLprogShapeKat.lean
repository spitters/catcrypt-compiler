/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-!
# Emitted-shape known-answer test, as a program

The instruction-text shape of the exported Jasmin bodies, checked by running a
program against a golden file rather than by `decide` inside a proof.

`decide` on rendered text reduces `String.decEq` through `ByteArray`, which
costs elaboration time, puts the check in the module's build, and blocks the
module system for every importer. Run it instead:

```
lake exe jasmin-lprog-shape-kat            # compare against the golden file
lake exe jasmin-lprog-shape-kat --write    # regenerate it
```

## Main definitions

* `shapes`: the exported bodies paired with their names.
* `main`: compares `shapes` against `goldenPath`, exiting non-zero on a
  mismatch and reporting the first differing line.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogShapeKat

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-- Where the expected rendering lives, relative to the repository root. -/
def goldenPath : System.FilePath :=
  "scripts/golden/jasmin-lprog-shape.txt"

/-- The exported bodies whose instruction text is pinned. -/
def shapes : List (String × List String) :=
  [ ("loopSmokePhysBody",  loopSmokePhysBody.map (fun i => i.li_i.toText))
  , ("mapAddOnePhysBody",  mapAddOnePhysBody.map (fun i => i.li_i.toText))
  , ("framedDemoBodyText", framedDemoBodyText)
  , ("mapAddOneAbiBody",   mapAddOneAbiBody.map (fun i => i.li_i.toText))
  , ("mixedClassBody",     (physBody (fun _ => none) mixedClassBody).map (fun i => i.li_i.toText))
  , ("edDblCallBodyW",     edDblCallBodyW.map (fun i => i.li_i.toText))
  , ("edAddCallBodyW",     edAddCallBodyW.map (fun i => i.li_i.toText)) ]

/-- Renderings that must agree with each other, rather than with a literal.
    Splicing the call op into the loop alphabet must leave a call-free loop
    byte-identical to the shadow walk. -/
def equalities : List (String × List String × List String) :=
  [ ("loopBodyWalkNCall_callfree_eq_loopBodyWalkN"
    , (loopBodyWalkNCall 1 "RAX" "Lidx1" [] (fun _ => none) dblCallfreeBody 2).1.map
        (fun i => i.li_i.toText)
    , (loopBodyWalkN 1 "RAX" "Lidx1" [] (fun _ => none) dblCallfreeBody 2).1.map
        (fun i => i.li_i.toText)) ]

/-- One line per instruction, prefixed by its body's name. -/
def render : String :=
  String.intercalate "\n"
    (shapes.flatMap (fun p => p.2.map (fun s => p.1 ++ "\t" ++ s))) ++ "\n"

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogShapeKat

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogShapeKat in
def main (args : List String) : IO UInt32 := do
  if args.contains "--write" then
    IO.FS.createDirAll (goldenPath.parent.getD ".")
    IO.FS.writeFile goldenPath render
    IO.println s!"wrote {goldenPath}"
    return 0
  unless ← goldenPath.pathExists do
    IO.eprintln s!"missing {goldenPath}; regenerate with --write"
    return 1
  let expected ← IO.FS.readFile goldenPath
  let mut bad := 0
  for (nm, a, b) in equalities do
    if a != b then
      IO.eprintln s!"jasmin-lprog-shape: {nm} DIFFERS"
      bad := bad + 1
  if expected == render && bad == 0 then
    IO.println s!"jasmin-lprog-shape: {shapes.length} bodies match, {equalities.length} equalities hold"
    return 0
  if expected == render then return 1
  let el := expected.splitOn "\n"
  let al := render.splitOn "\n"
  let firstDiff := (List.range (max el.length al.length)).find?
    (fun i => el[i]? != al[i]?)
  IO.eprintln "jasmin-lprog-shape: MISMATCH"
  match firstDiff with
  | some i =>
      IO.eprintln s!"  line {i + 1}"
      IO.eprintln s!"    expected: {el[i]?.getD "<none>"}"
      IO.eprintln s!"    actual:   {al[i]?.getD "<none>"}"
  | none => pure ()
  return 1

