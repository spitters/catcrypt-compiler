#!/usr/bin/env bash
# Hand-authored Com/Lcmd owned-emit provenance ratchet (see EMIT_PROVENANCE.md,
# GOLDEN_PATH_PRIMITIVES.md).
#
# CANONICAL RULE (EMIT_PROVENANCE.md): the deployed emitted artifact is GENERATED
# by the verified front (compileFromHax / haxToLowCT / RelationalCompile /
# FieldEmitGoldenPath -> Com -> cryptoDialectToJasminCom -> owned x86 backend). It
# is NEVER hand-authored as `Com` / `Lcmd` / `Linstr` / `.s`. A hand-authored
# `Lcmd` block + self-authored spec is a vacuous proof; if a front cannot express
# the kernel, FIX THE FRONT, don't hand-author around it. The front now makes this
# avoidable for scalar kernels (the *FrontEmit / *FrontRolledEmit / *FrontValidate
# reroute recipe — TranslateDialectRolledLoop.rolledForLoopN /
# translateDialectControl / cryptoDialectToJasminCom / reifyLowCT).
#
# This guard counts `CatCrypt/**/ *.lean` modules whose owned-emit kernel is
# HAND-AUTHORED as Com/Lcmd rather than produced by a front. Provenance is decided
# by where the emitted object COMES FROM, not by what text a single file contains.
# All marker tests run over source with docstrings, comments, string literals, and
# match-arm patterns removed, so prose, expected-output literals, and `| .Lopn … =>`
# matchers do not count.
#
#   CONSTRUCTION marker (this module builds the IR node):
#     Lopn | LinstrR | mkLinstr (raw Linstr construction),
#     `.var { op :=` | `args := .cons`  (hand de-Bruijn Com chains)
#   RENDER marker (this module prints or lowers an object defined somewhere):
#     renderLfundef | renderLprogAtt | Com.toLprogPhysAbi | Com.toLprogPhys |
#     ComL.toLprogPhys | Com.toLfundef | ComL.toLfundef | toLfundefPhys*
#   FRONT marker (routes through the verified front):
#     reifyLowCT | translateDialectControl | cryptoDialectToJasminCom |
#     rolledForLoopN | FieldEmitGoldenPath | RelationalCompile | emitDialectOwnedArr |
#     FrontRoutePlan.{compile,compileLoop,compileNested,compileBlock} — the
#     rolled-loop dispatcher, which selects one of the rolled-loop combinators
#     (a site that reaches the family through it names no combinator; see
#     scripts/front-callsite-ratchet.sh)
#
# A candidate (construction or render marker present) counts unless `front_sourced`
# clears it: a front marker in the file clears it; a construction marker in the file
# condemns it; otherwise the `Com`/`Lfundef` it renders is followed to the module
# that defines it and that module is judged the same way. So a render-only module
# whose Com is lowered one import up — `VIR/MontRedcEmit.lean` printing
# `montRedcWordJasmin`, lowered by `cryptoDialectToJasminCom` in
# `VIR/MontRedcCatCryptEmit.lean` — reads as front-generated, which it is.
# Calibrated on the MAYO pair:
#   KernelFromRustcmdOwnedEmit.lean       -> 1  (hand Lcmd + renderLfundef, no front)
#   KernelFromRustcmdFrontRolledEmit.lean -> 0  (rolledForLoopN front marker)
#
# KNOWN DETECTOR GAP: a `Com` built with the positional constructor form
# `.var (.mk op rfl (.cons …))` carries no construction marker, so a module using it
# is judged only by what it renders. `VIR/GgmNodeLoopEmit.lean` is such a module; it
# is covered by an entry in the exemption list rather than by the detector.
#
# ---------------------------------------------------------------------------
# DETECTOR B — a hand-authored `Linstr` reaching a WRITTEN artifact
# ---------------------------------------------------------------------------
# Detector A above clears a module as soon as ANY front marker appears anywhere in
# it, so a module that routes SOME of its artifacts through a front and hand-writes
# OTHERS reads as front-generated. That is the common shape: `CmovSelectEmit`
# front-generates the mask swap and hand-builds the cmov swap; `MpnLoopEmit`
# front-generates the deployed mpn symbols and hand-builds the `*_handtwin.s`
# bench twins. Detector B closes that hole by deciding provenance PER WRITTEN
# ARTIFACT instead of per file, and by keying on the IR literal itself rather than
# on which helper produced it.
#
# DISCRIMINATOR. A module counts when an `IO.FS.writeFile` argument traces back to
# a LITERAL low-level IR term — an anonymous-constructor `Linstr` (`⟨<info>, .Lopn
# …⟩`, likewise `.Lcond`/`.Llabel`/`.Lgoto`/`.Lalign`/`.Lret`/`.Lcall`), or
# `Linstr.mk` / `LinstrR.mk` / `mkLinstr` — without meeting a front marker first.
# The trace starts at the identifiers in each `writeFile` call, follows `def`/
# `abbrev`/`let` right-hand sides (and, across modules, any name the declaration
# index resolves), and stops on the first of: a front marker (CLEARED — the object
# is front-generated and whatever the module does to it afterwards is a pass), a
# literal IR term (COUNTED — this is where the program was authored), or a dead end.
# Deciding on WHAT REACHES THE ARTIFACT, not on what text the file contains, is
# what makes the two legitimate shapes below fall out rather than needing to be
# pattern-matched away.
#
# EXCLUDED SHAPE 1 — a pass that MATCHES on `.Lopn` and reconstructs. Verified on
# `X86Backend/Sha256RoundThirEmit.lean` (the `legalizeShiftImm*` /
# `expandRotInPlace` family, 8 literal `.Lopn` in-file): its `roundELprog` is
# `legalizeShiftImmLprog (Com.toLprogPhysAbi (lowerThir …))`, so the trace meets
# `lowerThir` at the first hop and stops. The pass rewrites a front-generated
# object; it never originates one. The same holds for the other five `*ThirEmit`
# modules. Backend passes that are not on any artifact path
# (`X86Backend/LcmdCopyPropagate.lean`, `LcmdReloadElim.lean`) write no artifact at
# all and are not candidates.
#
# EXCLUDED SHAPE 2 — `#guard` / demo / proof-subject fixtures. A literal that is
# only ever fed to `#guard`, a shape theorem, or an `#eval` is unreachable from any
# `writeFile` and never enters the trace. Verified on
# `X86Backend/MpnAdxLprog.lean`, whose hand `addLprog`/`subLprog` reach only the §6
# `#guard` shape checks while `emitMain` writes `MpnAddFrontEmit.toAsm` output; and
# on `VIR/ZkSumCheckWholeProverEmit.lean`, whose hand `sumcheckRoundBody`/
# `sumcheckLoop` are the proof subjects of `sumcheckLoopFundef_eq_buildOrchLoop`
# while the emitted `sumcheckLoopFundef` is `buildOrchLoop (sumcheckSpec …)`.
#
# `bench/` IS SCANNED by detector B. A hand-built `Lcmd` in a `bench/*.lean` driver
# writes a `.s` that the bench harness measures and the scoreboard quotes, so it is
# a shipped artifact under the same rule; leaving it out let five such drivers sit
# outside the ratchet. Detector A stays `CatCrypt/`-only — its render-marker scan
# over ~400 bench drivers would be judging compiler infrastructure by proxy, and
# every bench driver that hand-authors IR is already a detector-B candidate.
#
# DETECTOR B GAP: it only considers modules that call `IO.FS.writeFile` themselves.
# A kernel module whose artifact is written by a separate `*Main.lean` `lean_exe`
# driver is judged by detector A instead (the driver modules are on the exemption
# list as drivers that author no IR).
#
# EXCLUDED (compiler infra, not owned-emit kernels): the loop-node definitions
# (forLoopNRt / nestLoopLcmd / whileLcmd) in JasminLprogExport.lean and
# LprogControlFlow.lean — these are shared compiler infrastructure the fronts emit
# THROUGH, not hand-authored kernels.
#
# RATCHET: the count must be MONOTONE NON-INCREASING. The guard FAILS if it GROWS
# (a NEW hand-Com owned-emit module was added — re-source it through a front), and
# AUTO-TIGHTENS the baseline (rewrites scripts/handcom-provenance-baseline.txt) when
# it SHRINKS (a kernel was rerouted through a front). It does NOT require removing
# existing hand-Com modules; it only forbids growth while reroutes land.
#
# Run from anywhere in the repo: `bash scripts/handcom-provenance-ratchet.sh`
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
BASELINE_FILE="scripts/handcom-provenance-baseline.txt"

# Front markers: the original front API set, plus (2026-07-03 triage) the thir
# front (`lowerThir` / `ThirToCom*` — the *ThirOwnedEmit families are
# front-sourced Coms with an owned render tail) and references to a
# `*CatCryptEmit.` module's Com (render-only modules whose Com is lowered from
# the high catCryptDialect in a sibling front module).
#
# `translBB` (2026-07-05): the block-expanding whole-program field→jasmin
# translator (`FieldDescentBB.translBB : Com fieldDialect → Com jasminDialect`),
# a VERIFIED Com-dialect descent — the same category as `cryptoDialectToJasminCom`
# — with `translBB_denote` proving whole-program `bbEnc`-transport
# (`(translBB c).denote (mapValF V) = bbEnc (c.denote V)` for GoodF-covered `c`,
# unconditional). A module routing its kernel through `translBB` (e.g. the
# Poseidon2-BabyBear `fieldFrontStagedCom = translBB fieldPermComAtInBodyStaged`,
# 16-in/16-out, both ABI gaps closed) is front-sourced, not hand-authored.
# 2026-07-06 session fronts (each a VERIFIED front producing owned `.s`, each flip
# REFERENCE-KAT-validated): HIGH-LEVEL-SOURCE DESCENTS `MpnAddFrontEmit` (LowCT ->
# translateDialectCarrySelect -> catCryptDialect -> RA; GMP conform), `MpnLoopFrontEmit`
# (rolledForLoopNRt; GMP conform), `serByteStore` (memrefDialect byte store; bincode).
# VERIFIED STEP-COMPOSITION fronts (same category as the accepted OrchFront/buildOrchCom
# — a proven step-language interpreter renders an owned schedule authored in the front's
# language, NOT raw hand-Lcmd): `QuerySampleBranchFront` (BStep; render KATs),
# `Shake256SpongeFront` (SpStep; FIPS-202+PQClean), `Fe25519UnifyingFront` (UStep;
# RFC 7748+s2n), `MpnCmpEarlyExitFront` (SpStep; GMP), `SolveGf16FrontGen` (recursive
# forLoopBlock GF(16) nest; mayo-solve-emit-kat). CAVEAT: step-composition is weaker
# provenance than a high-level-source descent (schedule hand-authored in a verified DSL);
# re-sourcing from a high-level source (like Poseidon2 via translBB) is a future strengthening.
FRONT_RE='(reifyLowCT|translateDialectControl|cryptoDialectToJasminCom|rolledForLoopN|compileLoop|compileNested|compileBlock|FrontRoutePlan|FieldEmitGoldenPath|RelationalCompile|emitDialectOwnedArr|lowerThir|ThirToCom|CatCryptEmit\.|buildOrchCom|OrchestrationFront|OrchFront|toLfundefPhysFramedAbi|translBB|MpnAddFrontEmit|MpnLoopFrontEmit|serByteStore|QuerySampleBranchFront|Shake256SpongeFront|Fe25519UnifyingFront|MpnCmpEarlyExitFront|SolveGf16FrontGen)'

# The construction markers are split from the render markers. Building an IR node
# (`Lopn` / `LinstrR` / `mkLinstr` / a de-Bruijn `Com` chain) is authorship;
# calling the asm printer is not. A module that only renders is judged by the
# module its `Com`/`Lfundef` comes from (see `front_sourced` below), so a
# render-only tail on a front-generated kernel does not read as hand-authored.
CONSTRUCT_RE='(\bLopn\b|\bLinstrR\b|\bmkLinstr\b|\.var \{ op :=|args := \.cons)'
RENDER_RE='(renderLfundef|renderLprogAtt|Com\.toLprogPhysAbi|Com\.toLprogPhys|ComL\.toLprogPhys|Com\.toLfundef|ComL\.toLfundef|toLfundefPhys[A-Za-z]*)'

# Source text with docstrings/comments, string literals, and match-arm patterns
# removed. Marker tests run on this, so prose that names `renderLfundef`, an
# expected-output literal `"Lopn [RAX] MOV:64"`, and a matcher `| .Lopn d _ s =>`
# all read as what they are (not construction).
code_text() {
  perl -0777 -ne '
    s{/-.*?-/}{}gs;
    s{--[^\n]*}{}g;
    s{"(?:[^"\\]|\\.)*"}{""}gs;
    s{\|[^|\n=]*=>}{}g;
    print;' "$1"
}

has_construct() { code_text "$1" | grep -qE "$CONSTRUCT_RE"; }
has_render()    { code_text "$1" | grep -qE "$RENDER_RE"; }
has_front()     { code_text "$1" | grep -qE "$FRONT_RE"; }

# Declaration index: `<name>\t<file>` for every `def`/`abbrev` under CatCrypt/.
# Built once; `def_file` resolves an identifier to the module that defines it.
DECL_INDEX="$(mktemp)"
trap 'rm -f "$DECL_INDEX" "${TMP:-}"' EXIT
grep -rHE '^[[:space:]]*(noncomputable |private |protected |partial )*(def|abbrev) [A-Za-z_]' \
  --include='*.lean' CatCrypt/ \
  | sed -E "s/^([^:]+):[[:space:]]*(noncomputable |private |protected |partial )*(def|abbrev)[[:space:]]+([A-Za-z_][A-Za-z0-9_'!?]*).*/\4\t\1/" \
  | sort -u > "$DECL_INDEX"

def_file() { awk -F'\t' -v n="$1" '$1==n {print $2; exit}' "$DECL_INDEX"; }

# The identifiers this module hands to a render/lower entry point. A qualified
# name is reduced to its last component, so `Plonky3CompressEmit.compressComFinal`
# resolves the same way as a bare `compressComFinal`.
emit_sources() {
  code_text "$1" | perl -0777 -ne '
    while (/(?:renderLprogAtt|renderLfundef|Com\.toLprogPhysAbi|Com\.toLprogPhys|ComL\.toLprogPhys|Com\.toLfundef|ComL\.toLfundef|toLfundefPhys[A-Za-z]*)\s+\(?\s*([A-Za-z_][A-Za-z0-9_.]*)/g) {
      my $n = $1; $n =~ s/.*\.//; print "$n\n";
    }' | sort -u
}

# The identifiers on the right-hand side of `<name>`s definition inside `<file>`,
# used to keep following a locally-named object back to where it comes from.
rhs_idents() {
  [ -n "$2" ] || return 0
  export RHS_NAME="$2"
  code_text "$1" | perl -0777 -ne '
    my $n = quotemeta $ENV{RHS_NAME};
    next unless length $ENV{RHS_NAME};
    next unless /^[ \t]*(?:noncomputable |private |protected |partial )*(?:def|abbrev)[ \t]+$n\b(.*?)(?=\n[ \t]*(?:\@\[|(?:noncomputable |private |protected |partial )*(?:def|abbrev|theorem|lemma|instance|structure|inductive|end)[ \t])|\z)/ms;
    my $body = $1;
    while ($body =~ /([A-Za-z_][A-Za-z0-9_.]*)/g) { my $x = $1; $x =~ s/.*\.//; print "$x\n"; }
  ' | sort -u
  unset RHS_NAME
}

# Is every emitted object in `<file>` traceable to a verified front?
#   front marker in the file          -> yes
#   IR construction in the file       -> no (this is where the kernel is authored)
#   otherwise                         -> follow what it renders, one module up
# A module that neither constructs IR nor draws an object from elsewhere authors
# nothing, so it cannot be the origin of a hand-authored kernel.
FRONT_SOURCED_DEPTH=5
front_sourced() {
  local f=$1 depth=$2 seen=$3
  [ "$depth" -le 0 ] && return 1
  case "$seen" in *" $f "*) return 0 ;; esac
  has_front "$f" && return 0
  has_construct "$f" && return 1
  local ids id target src
  ids="$(emit_sources "$f")"
  for id in $ids; do
    target="$(def_file "$id")"
    if [ -n "$target" ] && [ "$target" != "$f" ]; then
      front_sourced "$target" $((depth - 1)) "$seen $f " || return 1
      continue
    fi
    # Defined here: follow the identifiers its body draws on.
    for src in $(rhs_idents "$f" "$id"); do
      target="$(def_file "$src")"
      [ -n "$target" ] || continue
      [ "$target" = "$f" ] && continue
      front_sourced "$target" $((depth - 1)) "$seen $f " || return 1
    done
  done
  return 0
}

# Compiler infrastructure + capability-validate modules (excluded — not owned-emit
# KERNELS). The loop-node files are shared IR infra the fronts emit. The
# *Validate/*Pilot modules + StraightLineLeafCallEmit hand-author a TRIVIAL test
# Com to exercise a front/backend arm (loop / call / vsimd / memref), not to
# deploy a crypto kernel — the same category as the front *FrontValidate files.
is_infra() {
  # File-based exemption list (2026-07-03 triage of all 255 baseline modules):
  # compiler/proof infrastructure, fronts, optimizer passes, predicates,
  # drivers, and backend-arm demos with no deployable emit artifact. Each line
  # carries its justification; placeholder-leaf KERNELS are not exemptible.
  if [ -f scripts/handcom-infra-exempt.txt ] &&
     grep -qxF "$1" <(sed 's/[[:space:]]*#.*$//' scripts/handcom-infra-exempt.txt | grep .); then
    return 0
  fi
  case "$1" in
    *SecureCompilation/VIR/JasminLprogExport.lean|*X86Backend/LprogControlFlow.lean) return 0 ;;
    *Validate.lean|*Pilot.lean|*LeafCall*Emit.lean) return 0 ;;
    # Front translation arms/nodes ARE the front (the thing kernels route
    # through), never deployed kernels themselves.
    *SecureCompilation/Dialects/TranslateDialect*.lean) return 0 ;;
    # Pass-level gate checks on expandCallShadows (sibling of the exempt
    # StraightLineLeafCallEmit; split out for a lake mimalloc workaround).
    *StraightLineLeafCallPassGates.lean) return 0 ;;
    # The labeled-lsem semantics/faithfulness layer hand-constructs Lcmd/Linstr
    # programs as PROOF SUBJECTS of export-faithfulness theorems, not as
    # deployed emit kernels.
    *SecureCompilation/VIR/JasminLsem*.lean) return 0 ;;
    # The Lprog optimizer (`optRunBody`/`renderOwned`), its LICM pass, and the
    # Com↔SStmt bridge hand-construct example Com/Lprog/Lcmd programs as PROOF
    # SUBJECTS of pass store-preservation, LICM store-agreement, and
    # denotation-agreement theorems — not as deployed emit kernels (same category
    # as JasminLsem* / the scheduler).
    *X86Backend/LprogOptPipeline.lean|*X86Backend/LprogLICM.lean|*Optimizer/ComSStmtBridge.lean) return 0 ;;
    *) return 1 ;;
  esac
}

# The exemption list is keyed by path, so a rename silently voids an exemption
# and turns the renamed module into a phantom "new hand-Com module". Every listed
# path must resolve to a file; a stale line is a check failure, not a warning.
STALE_EXEMPT="$(sed 's/[[:space:]]*#.*$//' scripts/handcom-infra-exempt.txt | grep . \
                 | while IFS= read -r p; do [ -f "$p" ] || echo "$p"; done)"
if [ -n "$STALE_EXEMPT" ]; then
  echo "FAIL: scripts/handcom-infra-exempt.txt names path(s) that no longer exist."
  echo "      A renamed or deleted module keeps its exemption line pointing at the old"
  echo "      path, so the module loses its exemption AND the list stops covering it."
  echo "      Point each line at the current path, or drop it if the module is gone:"
  printf '        %s\n' $STALE_EXEMPT
  exit 1
fi

# ---------------------------------------------------------------------------
# Detector B: per-written-artifact provenance (see the header).
# ---------------------------------------------------------------------------

# A LITERAL low-level IR term: an anonymous-constructor `Linstr` or an explicit
# `Linstr`/`LinstrR` constructor call. Match-arm patterns are already gone from
# `code_text`, so `| .Lopn d _ s =>` in a pass does not read as one.
AUTHORED_IR_RE='⟨[^⟨⟩,]*,[[:space:]]*\.(Lopn|Lcond|Llabel|Lgoto|Lalign|Lret|Lcall|Lsyscall)\b|\bmkLinstr\b|\bLinstrR\.mk\b|\bLinstr\.mk\b'

BCACHE="$(mktemp -d)"
trap 'rm -f "$DECL_INDEX" "${TMP:-}"; rm -rf "$BCACHE"' EXIT
ct() {  # cached code_text
  local k="$BCACHE/ct_${1//\//_}"
  [ -f "$k" ] || code_text "$1" > "$k"
  cat "$k"
}

# The right-hand side of `<name>` in `<file>`, as a `def`/`abbrev` or as a `let`
# inside an `IO` block (emit drivers bind the rendered string with `let`).
local_body() {
  export LB_NAME="$2"
  ct "$1" | perl -0777 -ne '
    my $n = quotemeta $ENV{LB_NAME};
    exit unless length $ENV{LB_NAME};
    if (/^[ \t]*(?:noncomputable |private |protected |partial )*(?:def|abbrev)[ \t]+$n\b(.*?)(?=\n[ \t]*(?:\@\[|(?:noncomputable |private |protected |partial )*(?:def|abbrev|theorem|lemma|instance|structure|inductive|end)[ \t])|\z)/ms) { print $1; }
    elsif (/^([ \t]*)let[ \t]+$n\b[^\n]*?:=([^\n]*(?:\n\1[ \t]+[^\n]*)*)/m) { print $2; }'
  unset LB_NAME
}

# Does `<ident>` in `<file>` trace back to a literal IR term? Prints the origin
# `<file> :: <ident>` and returns 0 when it does. A front marker cuts the branch.
AUTHORED_DEPTH=40
authored_from() {
  local f=$1 id=$2 depth=$3
  [ "$depth" -le 0 ] && return 1
  local key="$BCACHE/seen_$(printf '%s' "$f:$id" | tr -c 'A-Za-z0-9' '_')"
  [ -f "$key" ] && return 1
  : > "$key"
  local body; body="$(local_body "$f" "$id")"
  [ -z "$body" ] && return 1
  printf '%s' "$body" | grep -qE "$FRONT_RE" && return 1
  if printf '%s' "$body" | grep -qE "$AUTHORED_IR_RE"; then echo "$f :: $id"; return 0; fi
  local x tgt
  for x in $(printf '%s' "$body" | grep -oE "[A-Za-z_][A-Za-z0-9_.]*" | sed 's/.*\.//' | sort -u); do
    [ "$x" = "$id" ] && continue
    if [ -n "$(local_body "$f" "$x")" ]; then
      authored_from "$f" "$x" $((depth - 1)) && return 0
    else
      tgt="$(def_file "$x")"
      [ -n "$tgt" ] || continue
      [ "$tgt" = "$f" ] && continue
      # Never follow into a front or into exempt compiler infrastructure: those
      # modules legitimately build IR nodes, and they are judged by detector A.
      printf '%s' "$tgt" | grep -qE "$FRONT_RE" && continue
      is_infra "$tgt" && continue
      ct "$tgt" | grep -qE "$AUTHORED_IR_RE" || continue
      authored_from "$tgt" "$x" $((depth - 1)) && return 0
    fi
  done
  return 1
}

# The identifiers appearing in this module's `IO.FS.writeFile` calls (the call
# line plus the following line, since the rendered string is often on its own).
write_idents() {
  ct "$1" | perl -0777 -ne '
    while (/IO\.FS\.writeFile(.*?\n.*?)\n/gs) { my $s = $1;
      while ($s =~ /([A-Za-z_][A-Za-z0-9_.]*)/g) { my $t = $1; $t =~ s/.*\.//; print "$t\n"; } }' \
    | sort -u
}

writes_hand_authored_artifact() {
  local id
  for id in $(write_idents "$1"); do
    authored_from "$1" "$id" "$AUTHORED_DEPTH" >/dev/null && return 0
  done
  return 1
}

TMP="$(mktemp)"
{
  for f in $(grep -rlE "$CONSTRUCT_RE|$RENDER_RE" --include='*.lean' CatCrypt/); do
    has_construct "$f" || has_render "$f" || continue
    is_infra "$f" && continue
    front_sourced "$f" "$FRONT_SOURCED_DEPTH" " " && continue
    echo "$f"
  done
  for f in $(grep -rl 'IO\.FS\.writeFile' --include='*.lean' CatCrypt/ bench/); do
    ct "$f" | grep -qE "$AUTHORED_IR_RE" || continue
    is_infra "$f" && continue
    writes_hand_authored_artifact "$f" && echo "$f"
  done
} | sort -u > "$TMP"
CURRENT="$(grep -c . "$TMP" || true)"

# Baseline = first integer line; the file also stores the sorted module list (after
# the count) for diffability — so a FAIL can name exactly which module is new.
# Each listed path carries a trailing `# <reason>` saying why its emitted artifact
# is not front-generated; `baseline_paths` reads the paths without those reasons.
baseline_paths() {
  sed 's/[[:space:]]*#.*$//' "$BASELINE_FILE" | grep -E '^(CatCrypt|bench)/' | sort
}
# Reasons are read from a SNAPSHOT, not from `$BASELINE_FILE`: the auto-tighten
# block below redirects into that file, which truncates it before the first
# `baseline_reason` call runs and would otherwise drop every reason on the floor.
BASELINE_SNAPSHOT="$BCACHE/baseline-snapshot.txt"
cp "$BASELINE_FILE" "$BASELINE_SNAPSHOT"
baseline_reason() {
  sed -n "s|^$1[[:space:]]*#[[:space:]]*|# |p" "$BASELINE_SNAPSHOT" | head -1
}
BASELINE="$(grep -m1 -oE '^[0-9]+' "$BASELINE_FILE" || echo 0)"
echo "Hand-Com owned-emit modules: current=$CURRENT  baseline=$BASELINE  (front-routed emits exempt)"

if [ "$CURRENT" -gt "$BASELINE" ]; then
  echo ""
  echo "FAIL: the hand-Com owned-emit module count GREW ($BASELINE -> $CURRENT)."
  echo "      Emit kernels are GENERATED through a verified front, NEVER hand-authored"
  echo "      as Com/Lcmd/.s (a hand-Lcmd + self-authored spec is a vacuous proof)."
  echo "      Re-source the kernel through a front (TranslateDialectRolledLoop.rolledForLoopN"
  echo "      / translateDialectControl / cryptoDialectToJasminCom / reifyLowCT /"
  echo "      FieldEmitGoldenPath). See EMIT_PROVENANCE.md + GOLDEN_PATH_PRIMITIVES.md."
  echo "      NEW hand-Com module(s) (not in the baseline):"
  comm -13 <(baseline_paths) "$TMP" | sed 's/^/        /'
  exit 1
fi

if [ "$CURRENT" -lt "$BASELINE" ]; then
  echo ""
  echo "Good — the count SHRANK ($BASELINE -> $CURRENT). Auto-tightening the baseline."
  {
    echo "$CURRENT"
    echo "# Hand-authored Com/Lcmd owned-emit modules (frozen baseline; auto-tightened"
    echo "# by scripts/handcom-provenance-ratchet.sh). First line = count; each path"
    echo "# below carries the reason its emitted artifact is not front-generated. See"
    echo "# EMIT_PROVENANCE.md — the goal is to re-source each through a front (-> 0)."
    while IFS= read -r m; do
      printf '%s  %s\n' "$m" "$(baseline_reason "$m")"
    done < "$TMP"
  } > "$BASELINE_FILE"
fi

echo "OK: hand-Com owned-emit provenance ratchet satisfied."
