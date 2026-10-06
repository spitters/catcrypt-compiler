#!/usr/bin/env bash
# Ascent block provenance: the check lives in scripts/audit_emit_provenance.sh.
#
# This wrapper keeps the old entry point working. The audit classifies every
# (ascent module, block) pair as generated, imported or recorded with a reason in
# scripts/ascent-block-provenance-baseline.txt, and its header describes the detection.
#
# Usage: bash scripts/ascent-block-provenance.sh [--list | --record]
exec bash "$(dirname "$0")/audit_emit_provenance.sh" "$@"
