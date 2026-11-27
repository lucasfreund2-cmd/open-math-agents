#!/usr/bin/env bash
set -euo pipefail

# Run from any directory after tools/oma.sh setup has prepared the pinned toolchain.
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$REPO_ROOT"
FC="${OMA_FC:-$REPO_ROOT/.oma/formal-conjectures}"
OUT="$REPO_ROOT/.oma/repro/mse-2822876"
mkdir -p "$OUT"

# Serialize the checker: its temporary filename uses its process ID.
bash tools/check.sh statements/mse-2822876.lean "$OUT/statement.json"
bash tools/check.sh proofs/mse-2822876.lean "$OUT/proof.json"

# Audit every auxiliary result as well as the exact target.
AUDIT="$(mktemp "$FC/OMAUFDRepro_XXXXXXXX.lean")"
trap 'rm -f -- "$AUDIT"' EXIT
cat proofs/mse-2822876.lean > "$AUDIT"
cat >> "$AUDIT" <<'LEAN'

#print axioms OMA.MSE2822876.common_divisor_of_pairwise
#print axioms OMA.MSE2822876.pairwise_iff_exists_prime
#print axioms OMA.MSE2822876.positive_totalDegree_iff
#print axioms OMA.MSE2822876.polynomial_ideal_common_factor
#print axioms OMA.solution
LEAN
(
  cd "$FC"
  lake env lean "$(basename "$AUDIT")"
) | tee "$OUT/all-theorems.log"

python3 - "$OUT" <<'PY'
import json
from pathlib import Path
import re
import sys

out = Path(sys.argv[1])
for name in ("statement", "proof"):
    verdict = json.loads((out / (name + ".json")).read_text())
    if verdict.get("verdict") != "accepted":
        raise SystemExit(f"{name} rejected: {verdict}")
text = (out / "all-theorems.log").read_text()
names = [
    "OMA.MSE2822876.common_divisor_of_pairwise",
    "OMA.MSE2822876.pairwise_iff_exists_prime",
    "OMA.MSE2822876.positive_totalDegree_iff",
    "OMA.MSE2822876.polynomial_ideal_common_factor",
    "OMA.solution",
]
allowed = {"propext", "Classical.choice", "Quot.sound"}
for name in names:
    match = re.search(r"'" + re.escape(name) + r"' depends on axioms: \[(.*?)\]", text, re.S)
    if match is None:
        raise SystemExit(f"Missing axiom report for {name}")
    axioms = {s.strip() for s in match.group(1).replace("\n", " ").split(",") if s.strip()}
    if not axioms <= allowed:
        raise SystemExit(f"Unexpected axioms for {name}: {sorted(axioms - allowed)}")
print("Statement elaborates; complete proof and all four helper theorems pass the axiom audit.")
print("This local result does not assert upstream statement review or proof acceptance.")
PY
