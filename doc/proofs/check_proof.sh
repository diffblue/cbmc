#!/bin/bash
# Verify the FMA-based IEEE remainder Coq proof on Ubuntu 24.04
# Usage: ./check_proof.sh
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROOF="$SCRIPT_DIR/fma_remainder.v"

if [ ! -f "$PROOF" ]; then
  echo "Error: $PROOF not found" >&2
  exit 1
fi

# Install Coq and Flocq if not present
if ! command -v coqc &>/dev/null; then
  echo "Installing Coq and Flocq..."
  sudo apt-get update -qq
  sudo apt-get install -y -qq coq libcoq-flocq
fi

# Find Flocq
FLOCQ_DIR=$(find /usr/lib -path "*/user-contrib/Flocq" -type d 2>/dev/null | head -1)
if [ -z "$FLOCQ_DIR" ]; then
  echo "Error: Flocq not found" >&2
  exit 1
fi

echo "Coq version: $(coqc --version | head -1)"
echo "Flocq path:  $FLOCQ_DIR"
echo "Checking:    $PROOF"
echo

coqc -Q "$FLOCQ_DIR" Flocq "$PROOF"

echo
echo "All proofs verified successfully."
