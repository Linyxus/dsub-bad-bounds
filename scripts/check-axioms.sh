#!/usr/bin/env bash
# Checks that the main theorem depends on exactly the three standard axioms, and the side
# result on a subset of them. Run after `lake build`, from anywhere.
set -euo pipefail
cd "$(dirname "$0")/.."
expected="'Dsub.decidable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Dsub.Sub.trans' depends on axioms: [propext, Quot.sound]"
actual=$(lake env lean Check.lean)
echo "$actual"
if [ "$actual" != "$expected" ]; then
  echo "error: unexpected axioms" >&2
  exit 1
fi
