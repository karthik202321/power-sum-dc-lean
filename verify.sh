#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lake build
lake env lean AxiomAudit.lean | tee AXIOM_AUDIT.txt
python3 audit_axioms.py
python3 audit_imports.py
