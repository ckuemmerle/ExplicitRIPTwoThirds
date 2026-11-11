#!/usr/bin/env bash
# Compare Challenge.lean and Solution.lean with Comparator where no bubblewrap sandbox exists (macOS).
# Run from the repository root after `lake build`. The two modules are exported with the toolchain's
# `leanexport`, using the export targets of `lake comparator` itself: Lean's quotient constants, the compared
# theorems and permitted axioms of comparator.json, the kernel's primitive constants, and the definitions
# named in comparator.json. The exports are then compared without a sandbox.
set -euo pipefail
cd "$(dirname "$0")/.."
bin="$(dirname "$(lake env which lean)")"
out="$(mktemp -d)"
config() { python3 -c "import json, sys; c = json.load(open('comparator.json')); print(' '.join($1))"; }
targets="Quot Quot.mk Quot.lift Quot.ind $(config "c['theorem_names'] + c['permitted_axioms']")"
targets="$targets Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor"
targets="$targets Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String"
targets="$targets String.mk Char optParam autoParam semiOutParam outParam $(config "c.get('definition_names', [])")"
# shellcheck disable=SC2086
lake env "$bin/leanexport" Challenge -- $targets > "$out/challenge.ndjson"
# shellcheck disable=SC2086
lake env "$bin/leanexport" Solution -- $targets > "$out/solution.ndjson"
lake comparator --config comparator.json --challenge-from-export "$out/challenge.ndjson" \
  --solution-from-export "$out/solution.ndjson" --inadvisably-no-sandbox
