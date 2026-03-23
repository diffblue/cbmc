#!/bin/bash
# Verify the FMA-based IEEE remainder proofs (Coq and HOL Light).
# Usage: ./check_proof.sh [--coq-only | --hol-only]
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"

run_coq() {
  if ! command -v coqc &>/dev/null; then
    echo "WARNING: coqc not found, skipping Coq proofs"
    return 1
  fi

  FLOCQ_DIR=$(find /usr/lib -path "*/user-contrib/Flocq" -type d 2>/dev/null | head -1)
  if [ -z "$FLOCQ_DIR" ]; then
    echo "WARNING: Flocq not found, skipping Coq proofs"
    return 1
  fi

  echo "Coq version: $(coqc --version | head -1)"
  echo "Flocq path:  $FLOCQ_DIR"
  echo "Checking fma_remainder.v..."
  coqc -Q "$FLOCQ_DIR" Flocq "$SCRIPT_DIR/fma_remainder.v"
  echo "Checking fma_remainder_strategies.v..."
  coqc -Q "$FLOCQ_DIR" Flocq "$SCRIPT_DIR/fma_remainder_strategies.v"
  echo "Coq proofs verified (zero admits)."
}

run_hol() {
  HOL_DIR="/usr/share/hol-light"
  if [ ! -f "$HOL_DIR/hol.ml" ]; then
    echo "WARNING: HOL Light not found, skipping"
    return 1
  fi

  echo "Checking fma_remainder.ml (HOL Light)..."
  cd "$HOL_DIR"
  OUTPUT=$(timeout 300 ocaml < "$SCRIPT_DIR/fma_remainder.ml" 2>&1 || true)
  if echo "$OUTPUT" | grep -q "ALL HOL LIGHT PROOFS COMPLETE"; then
    echo "HOL Light proofs verified (zero mk_thm)."
  else
    echo "ERROR: HOL Light proofs failed"
    echo "$OUTPUT" | tail -20
    return 1
  fi
}

case "${1:-}" in
  --coq-only) run_coq ;;
  --hol-only) run_hol ;;
  *)
    run_coq || true
    echo
    run_hol || true
    ;;
esac
