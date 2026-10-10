#!/usr/bin/env python3
"""Check the actual Lean axiom transcript, including all requested declarations."""
from pathlib import Path
import re

root = Path(__file__).resolve().parent
commands = (root / 'AxiomAudit.lean').read_text()
output = (root / 'AXIOM_AUDIT.txt').read_text()
expected = commands.count('#print axioms')
reports = re.findall(r'depends on axioms:\s*\[([^]]*)\]', output)
axiom_free = len(re.findall(r'does not depend on any axioms', output))
if 'error:' in output or len(reports) + axiom_free != expected:
    raise SystemExit(f'Incomplete or failed axiom audit: '
                     f'{len(reports) + axiom_free}/{expected} declarations')
actual = {a.strip() for report in reports for a in report.split(',') if a.strip()}
unexpected = actual - {'propext', 'Classical.choice', 'Quot.sound'}
if unexpected:
    raise SystemExit(f'Unexpected foundational dependencies: {sorted(unexpected)}')
print(f'PASS: {expected} declarations; only standard foundational axioms.')
