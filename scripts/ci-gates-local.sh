#!/usr/bin/env bash
# Runs, locally, every text-scan gate that CI runs, and reports all failures at once.
#
# The steps are read from `.github/workflows/ci.yml`, so this script cannot drift from
# the workflow: a step is run when its `run:` is one line of the form
# `bash scripts/<name>.sh [args]` and the script does not load Lean or another build
# tool. Steps that CI runs only against a pull-request base, that build, or whose script
# is marked `# ci-gates-local: network` (it fetches or restores remote state), are listed
# as skipped. A step marked `continue-on-error: true` is a report: it is run, its
# failure is shown, and it does not fail this script. The pre-push hook calls this
# script.
#
#   scripts/ci-gates-local.sh            run every gate, print a summary
#   scripts/ci-gates-local.sh --list     print the gates that would run
#   CI_GATES_JOBS="gates" …              restrict to the named jobs
set -u
ROOT="$(git rev-parse --show-toplevel)"
cd "$ROOT"
WF=".github/workflows/ci.yml"
mode="${1:-run}"

steps="$(python3 - "$WF" "${CI_GATES_JOBS:-}" <<'PY'
import re, sys
wf, only = sys.argv[1], set(sys.argv[2].split())
job, in_jobs, name, report = None, False, "", False
for line in open(wf):
    if re.match(r'^jobs:\s*$', line): in_jobs = True; continue
    if not in_jobs: continue
    m = re.match(r'^  ([A-Za-z0-9_-]+):\s*$', line)
    if m: job = m.group(1); continue
    m = re.match(r'^\s*- name:\s*(.*)$', line)
    if m: name = m.group(1).strip().strip('"\''); report = False; continue
    if re.match(r'^\s*continue-on-error:\s*true\s*$', line): report = True; continue
    m = re.match(r'^\s*run:\s*(bash scripts/[A-Za-z0-9_./-]+\.sh(?: [^|>$]*)?)\s*$', line)
    if m and job and (not only or job in only):
        print(f"{job}\t{name}\t{m.group(1).strip()}\t{'report' if report else 'gate'}")
PY
)"

fails=0; ran=0; skipped=0; out="$(mktemp)"; trap 'rm -f "$out"' EXIT
summary=""
while IFS=$'\t' read -r job name cmd kind; do
  [ -n "$cmd" ] || continue
  script="$(printf '%s' "$cmd" | awk '{print $2}')"
  if [ ! -f "$script" ]; then summary+="MISSING  $cmd"$'\n'; fails=$((fails+1)); continue; fi
  # A step whose script declares `# ci-gates-local: network` reads or writes remote state
  # (restore-cloud-cache.sh replaces .lake/build from a cache release); it is CI setup, not
  # a gate, and run here it would overwrite or delete the local build.
  if grep -qE '^# *ci-gates-local: network' "$script"; then
    summary+="skip     $cmd   (network)"$'\n'; skipped=$((skipped+1)); continue
  fi
  # A gate that starts a build is not a text scan; CI runs it in a build job.
  if grep -qE '(^|[^A-Za-z_-])(lake (build|exe|env)|cargo |cmake )' "$script" \
     && ! grep -qE '^# *ci-gates-local: text-scan' "$script"; then
    summary+="skip     $cmd   (builds)"$'\n'; skipped=$((skipped+1)); continue
  fi
  if [ "$mode" = "--list" ]; then echo "$job: $cmd"; continue; fi
  if eval "$cmd" >"$out" 2>&1; then
    summary+="ok       $cmd"$'\n'
  elif [ "$kind" = "report" ]; then
    summary+="report   $cmd   (non-blocking in CI)"$'\n'
    echo "──── report [$job] $name"; echo "     $cmd"; tail -15 "$out" | sed 's/^/     /'
  else
    summary+="FAIL     $cmd"$'\n'
    fails=$((fails+1))
    echo "──── FAIL [$job] $name"; echo "     $cmd"; tail -15 "$out" | sed 's/^/     /'
  fi
  ran=$((ran+1))
done <<< "$steps"
[ "$mode" = "--list" ] && exit 0

echo "──── gates: $ran run, $fails failed, $skipped skipped"
printf '%s' "$summary" | grep -E '^(FAIL|MISSING|skip|report)' || true
# A ratchet that rewrote its baseline leaves a diff that CI rejects.
if ! git diff --quiet -- scripts/ 2>/dev/null; then
  echo "note: files under scripts/ differ from the index (a baseline was rewritten or is uncommitted):"
  git diff --stat -- scripts/ | sed 's/^/     /'
fi
[ "$fails" -eq 0 ]
