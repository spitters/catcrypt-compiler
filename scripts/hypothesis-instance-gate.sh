#!/usr/bin/env bash
#
# hypothesis-instance-gate.sh — evaluate a conditional theorem's side conditions
# over the programs this tree ships, and fail when the answer is zero.
#
# ## The defect class
#
# A FALSE theorem reports itself. Some consumer or some later change breaks a
# build, loudly, at a named declaration. A theorem whose HYPOTHESIS is satisfied
# by nothing never breaks a build. It stays green for as long as it exists, and
# what it says about the situation its name claims is nothing. Nothing in a Lean
# build evaluates a `Prop`-level hypothesis against the objects the tree ships,
# so this needs an active check.
#
# The worked case. `X86Backend/ToLprogFaithfulMulCarrySel.toLprogPhysAbi_faithful_uniformMCS`
# is whole-function register-allocation faithfulness, conditional on
# `hcd : CoverDataMCS body (bodyPhysTable body) nArgs com d bs`. That inductive's
# binop arms carried one condition `hcol`, the two-address collapse: the allocator
# placed a binding's first source and its destination on one physical register.
# Measured over the emitted programs, `hcol` held for 0 of 1 binop bindings of one
# golden-path kernel, 0 of 4 of another, and 0 of 221 of the shipped Ed25519 point
# addition. It is structurally forced: the allocator is a linear scan with no
# coalescing, whose expiry keeps a source interval alive where the destination is
# defined. The theorem had been green for months.
#
# ## What this gate does
#
# Where a hypothesis is DECIDABLE on a finite domain, evaluate it over the SHIPPED
# instances and fail at zero. Three parts:
#
#   * scripts/vacuity/HypothesisInstanceProbe.lean — the evaluator. It computes
#     the emitted binding heads, the allocator's table, and the conditions, and
#     prints one `RESULT` row per (theorem, hypothesis, instance) with the number
#     of bindings satisfying the condition and the number it applies to. It is an
#     EVALUATION, not a proof obligation: `decide` cannot reach any of this,
#     because `physLiveData` routes through `List.mergeSort`, whose well-founded
#     recursion does not reduce in the kernel.
#   * scripts/vacuity/hypothesis-instances.tsv — the registry. One row per
#     (theorem, hypothesis, instance), carrying the policy and the finite domain
#     the evaluation ranges over. This file is where a hypothesis is REGISTERED;
#     the header of the file states the column and policy vocabulary.
#   * this script — runs the evaluator, joins its rows against the registry,
#     enforces the policies, and checks that the registry still covers the
#     programs the tree exports.
#
# A hypothesis becomes checked by adding a `RESULT` row to the evaluator and the
# matching row to the registry. Neither half is optional: a registry row with no
# measurement fails (the evaluator stopped covering it), and a measurement with no
# registry row fails (a number nobody decided the meaning of). That is deliberate;
# a gate whose two halves can drift apart measures the drift, not the tree.
#
# ## The instance set, which is the whole question
#
# A gate evaluated at fixtures measures the fixtures. In this very case, the
# faithfulness tree's own one- and two-binding covers were built by hand to
# satisfy `hcol`, so a version of this gate pointed at them would report a healthy
# count while every kernel the tree emits failed the same condition. So the
# instance set is the EMITTED programs, and the gate derives it rather than
# accepting it:
#
#   * a shipped instance is a `Com jasminDialect` that some tracked module hands
#     to the physical exporter. The exporter is not one identifier — bytes leave
#     through `Com.toLprogPhysAbi` and through wrappers that apply it to a `Com`
#     parameter (`compileComToElf`, `compileComToElfJInstrFull6` through
#     `physBodyOf`, `optimizedCompileComToElf`, `physBodyOfAbi`,
#     `Com.toLprogPhysAbiText`/`Bytes`/`writeLprogPhysAbiFile`, and the resident
#     emitters of the SHA-2 producer). `--instances` computes that closure from
#     the source and then collects the identifiers passed to any member. An
#     identifier is kept only when it is declared as a `Com jasminDialect` in a
#     tracked file, which drops the local binders (`com`, `c`, `jc`) and the type
#     names the same grep otherwise picks up.
#   * names are qualified by the declaring file's namespace, because the
#     workspace has two `fieldAddCom`s — one in `FieldEmitGoldenPath`, one in
#     `Pairing/Bls12_377Emit` — and they are different programs.
#   * the number of exported programs no registry row covers is a RATCHET: it may
#     fall and may not rise. A new emitted kernel therefore forces either a row or
#     a deliberate decision, and the 3 instances registered today do not silently
#     become the definition of "shipped".
#
# A theorem with no shipped instance at all is a FINDING, not a pass. The registry
# carries at least one `require` row per theorem, and a `require` row whose
# `total` is zero — the hypothesis applies to no binding of that program — fails
# as `NO-SHIPPED-BINDING` rather than passing vacuously.
#
# ## What the first run measured (2026-09-16)
#
# The three registered instances, at the exporter's own parameters:
#
#   instance                 heads   hcol   mov_arm    hinj   cover_arm
#   pointAddCom               2110   0/221  221/221  0/2110      0/2110
#   fieldAddCom                  1    0/1      1/1      1/1         1/1
#   fieldCondSub251Com           7    0/4      4/4      3/7         3/7
#
# `hcol` reproduces the measurement this gate was built for: zero on all three,
# for the structural reason above. The binop arms are not the obstruction any
# more — `ToLprogFaithfulBinopMov` added `varMov` and `var64Mov` arms that carry
# no collapse condition, and the mov arm's conditions hold for every binop head of
# all three programs, which is why `hcol` is a `route` row rather than a
# `require` row: the theorem has an arm, and the dead condition is printed as a
# note rather than failed.
#
# What decides applicability now is `hinj`, which every binding structure of the
# fragment carries: the renaming must send no other name to the destination's
# physical register. It holds for 0 of the 2110 heads of the point addition,
# where 2142 logical names are allocated onto sixteen registers and the spill
# file, so `CoverDataMCS` cannot be constructed for that program and the theorem
# does not reach the kernel the tree ships. The gate reports that as
# VACUOUS-ON-SHIPPED on the `cover_arm` row. The golden-path kernels are small
# enough that the renaming stays injective on part of the body, and they pass.
#
# Two further readings come out of the same run and decide nothing here: 144 of
# the point addition's heads carry no `:64` tag (the width-1 carry-in constants),
# and `CoverDataMCS` fixes one width for the whole binding list; and the
# conditional-subtract kernel has one head outside the fragment alphabet
# (`SHR:63:64`, a `shrImm` the cover has no constructor for).
#
# ## What this gate cannot catch
#
#   * a hypothesis that is satisfiable but only on inputs nobody ships. The gate
#     measures the instances the tree exports; a condition that holds only for a
#     program no module emits reads here exactly as a condition that holds. The
#     instance-set derivation above is what bounds this, and it bounds it at
#     "what this tree emits", not at "what is reachable".
#   * a hypothesis that is not decidable, or not decidable on a domain this
#     evaluator can enumerate. `hinj` is in scope only because `physRename`
#     factors through `nameSlot`, whose range is finite, so a quantifier over all
#     strings is settled by the body's names plus one name absent from them. A
#     semantic hypothesis over states (`StoreRelOff`, `ArgMatAbi`, `hop`) has no
#     such factorisation and is out of scope here.
#   * everything about the CONCLUSION. A theorem whose hypotheses are all live can
#     still conclude something weaker than its name suggests.
#
# The two neighbouring classes are covered elsewhere, and this gate is narrower
# than both on purpose:
#
#   * a syntactically unused binder is a SHAPE, found by a matcher over source —
#     `scripts/vacuous-theorem-ratchet.sh` here and `model-vacuity-ratchet.sh` in
#     the dev tree (its `silenced_binder` dimension). Those scan `git ls-files` of
#     one repository, and neither scans this package.
#   * a well-named hypothesis that the proof discards is found by Lean's own
#     unused-variable linter, unless an underscore prefix suppresses it.
#   * a hypothesis that is well-formed, used in the proof, and satisfied by
#     nothing is invisible to both. That is this gate.
#
# Usage:
#   bash scripts/hypothesis-instance-gate.sh              # the gate
#   bash scripts/hypothesis-instance-gate.sh --measure    # the evaluator's rows
#   bash scripts/hypothesis-instance-gate.sh --list       # the registry
#   bash scripts/hypothesis-instance-gate.sh --instances  # the derived instance set
#
# Env:
#   HYP_GATE_PREFIX   command prefix for the evaluator run, e.g.
#                     "bash ../SSProve-lean/scripts/heavy-run.sh" to keep the Lean
#                     process out of a memory-tight shell scope.
#   LEAN_NUM_THREADS  bounds the concurrent Lean workers of the import build
#                     (default 1 here).
#   HYP_GATE_PROBE_OUT  a file holding a captured evaluator run, used in place of
#                     running one. For re-checking the joins after a registry edit.
set -uo pipefail
cd "$(git rev-parse --show-toplevel)" || exit 2

REGISTRY="scripts/vacuity/hypothesis-instances.tsv"
EXCLUDE="scripts/vacuity/hypothesis-instance-exclude.txt"
PROBE="scripts/vacuity/HypothesisInstanceProbe.lean"
MODE="${1:-check}"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"

# Exported programs no registry row covers. May fall, may not rise.
UNCOVERED_BASELINE=83

rc=0
fail() { echo "FAIL: $*"; rc=1; }

[ -f "$REGISTRY" ] || { echo "FAIL: $REGISTRY is missing (the registry decides what is checked)."; exit 2; }
[ -f "$PROBE" ]    || { echo "FAIL: $PROBE is missing (the evaluator)."; exit 2; }

TMPD="$(mktemp -d)"; trap 'rm -rf "$TMPD"' EXIT

registry_rows() { grep -v '^[[:space:]]*#' "$REGISTRY" | grep -vE '^[[:space:]]*$'; }
exclude_rows()  { [ -f "$EXCLUDE" ] && grep -v '^[[:space:]]*#' "$EXCLUDE" | grep -vE '^[[:space:]]*$'; }

# ── the evaluator ─────────────────────────────────────────────────────────────
# `lake lean FILE` builds the file's imports and elaborates it, which runs its
# `#eval`. The same invocation emits the benched artifacts from the bench tree,
# so the interpreter is known to carry programs of this size. `lake env lean` is
# the fallback for a Lake that does not take the target: the retry is decided by
# the absence of the evaluator's own marker line, never by the exit status, so a
# Lean error is reported as a Lean error rather than retried.
run_probe() {
  local out
  # A captured run, for exercising the joins below without a Lean process. The
  # capture is the evaluator's own output; it is not a fixture of the counts, and
  # a stale capture is visible as a drift failure against the registry.
  if [ -n "${HYP_GATE_PROBE_OUT:-}" ]; then
    [ -f "$HYP_GATE_PROBE_OUT" ] || { echo "no such capture: $HYP_GATE_PROBE_OUT" > "$TMPD/probe.err"; return 1; }
    cat "$HYP_GATE_PROBE_OUT"; return 0
  fi
  out="$( ${HYP_GATE_PREFIX:-} lake lean "$PROBE" 2>&1 )"
  if ! grep -q '^PROBE' <<< "$out"; then
    local out2
    out2="$( ${HYP_GATE_PREFIX:-} lake env lean "$PROBE" 2>&1 )"
    if grep -q '^PROBE' <<< "$out2"; then out="$out2"; else
      printf '%s\n' "$out" "$out2" > "$TMPD/probe.err"
      return 1
    fi
  fi
  printf '%s\n' "$out"
}

# ── the derived instance set ──────────────────────────────────────────────────
# The exporter closure: `Com.toLprogPhysAbi`, plus any def that takes a
# `Com jasminDialect` parameter and names a member in its body. Three rounds; the
# measured closure stabilises at one.
exporter_closure() {
  local set="Com\.toLprogPhysAbi" round names
  for round in 1 2 3; do
    names="$(git grep -lE "$set" -- '*.lean' | while IFS= read -r f; do
      SETRE="$set" perl -0777 -ne '
        my $re = $ENV{SETRE};
        while (/\b(?:def|abbrev)\s+([A-Za-z_][A-Za-z0-9_.\x27]*)\s*(?:\{[^}]*\}\s*)*\([^)]*Com\s+jasminDialect[^)]*\)[^=]*:=(.{0,1200}?)(?=\n(?:\/-|\@\[|def |theorem |abbrev |end ))/gs) {
          my ($n, $b) = ($1, $2);
          print "$n\n" if $b =~ /$re/;
        }' "$f"
    done | sort -u)"
    [ -n "$names" ] || break
    local add
    add="$(printf '%s\n' $names | sed -E 's/[.]/\\./g' | paste -sd'|' -)"
    [ -n "$add" ] || break
    set="$set|$add"
  done
  printf '%s\n' "$set"
}

# Every identifier handed to a member of the closure as its first argument.
exporter_args() {
  local re="$1"
  git grep -hoE "($re)[[:space:]]+[A-Za-z_][A-Za-z0-9_.\x27]*" -- '*.lean' \
    | awk '{print $NF}' | sort -u
}

# `<bare name>\t<qualified name>` for every `Com jasminDialect` declared here.
com_decls() {
  git grep -nE "^[[:space:]]*(@\[[^]]*\][[:space:]]*)?(noncomputable |private |protected |public )*(def|abbrev) [A-Za-z_][A-Za-z0-9_.']*" -- '*.lean' \
    | grep -E ': *Com jasminDialect' \
    | while IFS=: read -r f _ decl; do
        local ns n
        ns="$(grep -m1 '^namespace ' "$f" | awk '{print $2}')"
        n="$(sed -E 's/.*(def|abbrev) ([A-Za-z_][A-Za-z0-9_.'"'"']*).*/\2/' <<< "$decl")"
        [ -n "$n" ] || continue
        printf '%s\t%s\n' "${n##*.}" "${ns:+$ns.}$n"
      done | sort -u
}

shipped_instances() {
  local re args
  re="$(exporter_closure)"
  args="$TMPD/args"; exporter_args "$re" > "$args"
  com_decls | awk -F'\t' -v A="$args" '
    BEGIN { while ((getline l < A) > 0) seen[l] = 1 }
    ($1 in seen) { print $2 }' | sort -u
}

if [ "$MODE" = "--instances" ]; then
  reg="$TMPD/reg"; registry_rows | cut -f3 | sort -u > "$reg"
  printf '%-78s %s\n' INSTANCE REGISTERED
  n_all=0; n_cov=0
  while IFS= read -r i; do
    n_all=$((n_all+1))
    if grep -qxF -- "$i" "$reg"; then printf '%-78s %s\n' "$i" yes; n_cov=$((n_cov+1))
    else printf '%-78s %s\n' "$i" no; fi
  done < <(shipped_instances)
  echo "instances: $n_all exported, $n_cov registered, $((n_all - n_cov)) uncovered"
  exit 0
fi

if [ "$MODE" = "--list" ]; then
  printf '%-12s %-14s %s\n' HYPOTHESIS POLICY 'INSTANCE (theorem in column 1 of the file)'
  registry_rows | while IFS=$'\t' read -r _thm hyp inst pol _dom; do
    printf '%-12s %-14s %s\n' "$hyp" "$pol" "$inst"
  done
  exit 0
fi

MEAS="$TMPD/meas"
if ! run_probe > "$TMPD/out"; then
  echo "FAIL: the evaluator did not run. Its output:"
  sed 's/^/      /' "$TMPD/probe.err" | tail -n 40
  exit 2
fi
grep '^RESULT' "$TMPD/out" | cut -f2- > "$MEAS"

if [ "$MODE" = "--measure" ]; then
  printf '%-64s %-12s %s\n' INSTANCE HYPOTHESIS COUNT
  while IFS=$'\t' read -r _thm hyp inst sat total; do
    printf '%-64s %-12s %s of %s\n' "${inst##*SecureCompilation.}" "$hyp" "$sat" "$total"
  done < "$MEAS"
  grep '^INFO' "$TMPD/out" | cut -f2- | while IFS=$'\t' read -r inst k v; do
    printf '%-64s %-12s %s\n' "${inst##*SecureCompilation.}" "$k" "$v"
  done
  exit 0
fi

# ── the joins ─────────────────────────────────────────────────────────────────
excluded() { exclude_rows | awk -F'\t' -v t="$1" -v h="$2" -v i="$3" -v p="$4" \
  '$1==t && ($2==h || $2==p) && $3==i { found=1 } END { exit found?0:1 }'; }
measure_of() { awk -F'\t' -v t="$1" -v h="$2" -v i="$3" '$1==t && $2==h && $3==i {print $4"\t"$5; exit}' "$MEAS"; }

n_rows=0; n_req=0; n_sil=0
declare -A GROUP_BEST=() GROUP_ROWS=()

while IFS=$'\t' read -r thm hyp inst pol _dom; do
  n_rows=$((n_rows+1))
  m="$(measure_of "$thm" "$hyp" "$inst")"
  if [ -z "$m" ]; then
    fail "the evaluator printed no row for ${hyp} on ${inst##*.}; the registry and $PROBE have drifted."
    n_sil=$((n_sil+1)); continue
  fi
  sat="${m%%$'\t'*}"; total="${m##*$'\t'}"
  case "$pol" in
    require)
      n_req=$((n_req+1))
      if [ "$total" -eq 0 ]; then
        excluded "$thm" "$hyp" "$inst" "$pol" \
          || fail "NO-SHIPPED-BINDING: ${hyp} of ${thm##*.} applies to no binding of ${inst##*.}. The theorem's fragment does not reach this program."
      elif [ "$sat" -eq 0 ]; then
        excluded "$thm" "$hyp" "$inst" "$pol" \
          || fail "VACUOUS-ON-SHIPPED: ${hyp} of ${thm##*.} holds for 0 of $total bindings of ${inst##*.}."
      fi ;;
    route:*)
      g="$thm|${pol#route:}|$inst"
      GROUP_ROWS["$g"]="${GROUP_ROWS[$g]:-} $hyp($sat/$total)"
      cur="${GROUP_BEST[$g]:-0}"
      [ "$sat" -gt "$cur" ] && GROUP_BEST["$g"]="$sat"
      if [ "$sat" -eq 0 ]; then
        echo "note:     ${hyp} carries no binding of ${inst##*.} (0 of $total)"
      fi ;;
    report) ;;
    *) fail "$REGISTRY row ${hyp}/${inst##*.} carries the unknown policy \`$pol\`." ;;
  esac
done < <(registry_rows)

for g in "${!GROUP_BEST[@]}"; do
  if [ "${GROUP_BEST[$g]}" -eq 0 ]; then
    thm="${g%%|*}"; rest="${g#*|}"; grp="${rest%%|*}"; inst="${rest#*|}"
    excluded "$thm" "route:$grp" "$inst" "route:$grp" \
      || fail "VACUOUS-ON-SHIPPED: every route of group \`$grp\` measures zero on ${inst##*.} —${GROUP_ROWS[$g]}. The theorem has no arm this program can use."
  fi
done

# A measurement nobody registered.
while IFS=$'\t' read -r thm hyp inst _sat _total; do
  registry_rows | awk -F'\t' -v t="$thm" -v h="$hyp" -v i="$inst" \
    '$1==t && $2==h && $3==i {found=1} END {exit found?0:1}' \
    || fail "the evaluator measures ${hyp} on ${inst##*.}, which no $REGISTRY row registers."
done < "$MEAS"

# A stale excuse.
while IFS=$'\t' read -r thm hyp inst _why; do
  [ -n "${thm:-}" ] || continue
  registry_rows | awk -F'\t' -v t="$thm" -v h="$hyp" -v i="$inst" \
    '$1==t && ($2==h || $4==h) && $3==i {found=1} END {exit found?0:1}' \
    || fail "$EXCLUDE excuses ${hyp} on ${inst##*.}, which the registry does not carry."
done < <(exclude_rows)

echo "rows:     $n_rows registered ($n_req require), $n_sil unmeasured"

# ── coverage of the exported programs ─────────────────────────────────────────
reg="$TMPD/reg"; registry_rows | cut -f3 | sort -u > "$reg"
n_all=0; n_unc=0
while IFS= read -r i; do
  n_all=$((n_all+1))
  grep -qxF -- "$i" "$reg" || n_unc=$((n_unc+1))
done < <(shipped_instances)
echo "coverage: $n_all exported program(s), $((n_all - n_unc)) registered, $n_unc uncovered (baseline $UNCOVERED_BASELINE)"
if [ "$n_unc" -gt "$UNCOVERED_BASELINE" ]; then
  fail "$n_unc exported program(s) carry no registered hypothesis; the baseline is $UNCOVERED_BASELINE."
  echo "      A program this tree emits and no gate evaluates is the state the"
  echo "      point addition was in. List them with:"
  echo "        bash scripts/hypothesis-instance-gate.sh --instances"
elif [ "$n_unc" -lt "$UNCOVERED_BASELINE" ]; then
  echo "          (lower the baseline: UNCOVERED_BASELINE=$n_unc)"
fi

if [ "$rc" -ne 0 ]; then
  echo "FAIL: a registered hypothesis is satisfied by nothing the tree ships."
  echo "      Read the counts with:"
  echo "        bash scripts/hypothesis-instance-gate.sh --measure"
  echo "      Then either widen the theorem so a shipped program satisfies it, or"
  echo "      record the row in $EXCLUDE with the reason its scope is narrower."
  exit 1
fi
echo "OK: every registered hypothesis holds for at least one binding of every"
echo "    program it is registered against, and no exported program lost its gate."
