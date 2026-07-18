# Documentation

Three complementary doc systems. All are heavy builds on the full module set —
run them capped (see the README build note), ideally in a quiet window.

## 1. docgen4 — API reference (wired)

Hyperlinked HTML reference generated from module docstrings. The dev-only
dependency is declared in `lakefile.lean` behind `env=doc`:

```
lake -R -Kenv=doc update            # pulls doc-gen4
lake -R -Kenv=doc build CatCryptCompiler:docs
# output: .lake/build/doc/  (open index.html)
```

One HTML unit per module (1851 modules) — the heaviest of the three. Requires
the docstrings to be clean (the pre-publish scrub covers this).

## 2. leanblueprint — proof map (scaffolded)

A math-style blueprint linking informal statements to formal theorems with a
dependency graph. The real content is in `blueprint/src/content.tex` (the
covered fragment + the three end-to-end capstones as `\lean{...}\leanok` nodes).

The plasTeX wrappers (`web.tex`, `print.tex`, `macros/`) are tool-generated —
generate them once, then build:

```
pip install leanblueprint            # once
leanblueprint new                    # generates web.tex/print.tex/macros around content.tex
leanblueprint pdf                    # print version
leanblueprint web                    # dependency-graph website (blueprint/web/)
leanblueprint checkdecls             # verify every \lean{} name resolves in the built oleans
```

Use the dev tree's `blueprint/` as the config template. Next authoring step:
add the intermediate nodes (front totality, backend machine model,
`decode∘encode`, CT/leakage preservation) so the graph faithfully maps the proof.

## 3. Verso — narrative manual (scoped)

A prose "how the verified compiler works" guide with checked code, best as a
paper/release companion. Setup (not yet added, to avoid an unbuilt lib in the
tree):

```
-- lakefile.lean, behind env=doc:
require verso from git "https://github.com/leanprover/verso" @ "<tag matching v4.30.0>"
-- add a `lean_lib Manual` + a `@[main] def` rendering Verso.Genre.Manual
```

Then author `Manual/*.lean` chapters (Overview → Fronts → Com IR → Backend →
Trust surface → Scope & limitations) and `lake build Manual` to render HTML.
The Scope chapter must state the `IsCoveredCtl` fragment honestly.

## Order of work

docgen4 first (cheapest, already wired), then flesh out the blueprint nodes,
then Verso for the narrative. Gate all three on the pre-publish scrub + the
axiom audit so the docs never present an unverified or mis-scoped claim.
