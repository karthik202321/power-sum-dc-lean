#!/usr/bin/env python3
"""Audit the original-route source graph, not historical idea provenance."""
from pathlib import Path
import re

root = Path(__file__).resolve().parent
forbidden = {
    'ExactKernelLifts', 'BorderPolarFamily', 'BorderIncidence',
    'Results', 'PaperAxioms', 'Exact',
}
seen = set()
edges = []

def strip_comments_and_strings(source):
    """Drop nested Lean comments and strings before auditing trusted shortcuts."""
    out, i, depth = [], 0, 0
    while i < len(source):
        if depth:
            if source.startswith('/-', i):
                depth += 1
                i += 2
            elif source.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                i += 1
        elif source.startswith('/-', i):
            depth = 1
            i += 2
            out.append(' ')
        elif source.startswith('--', i):
            i = source.find('\n', i)
            if i == -1:
                break
            out.append('\n')
        elif source[i] == '"':
            i += 1
            while i < len(source):
                if source[i] == '\\':
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            out.append(' ')
        else:
            out.append(source[i])
            i += 1
    return ''.join(out)

def visit(module):
    if module in seen:
        return
    seen.add(module)
    path = root / (module.replace('.', '/') + '.lean')
    if not path.is_file():
        raise SystemExit(f'Missing local dependency: {module}')
    name = module.rsplit('.', 1)[-1]
    if name.startswith(('Explicit', 'Expanded')) or name in forbidden:
        raise SystemExit(f'Excluded route imported: {module}')
    source = path.read_text()
    code = strip_comments_and_strings(source)
    prohibited = re.search(r'\b(axiom|sorry|sorryAx|admit|unsafe|native_decide)\b', code)
    if prohibited:
        raise SystemExit(f'Untrusted shortcut in {module}: {prohibited.group()}')
    for imported in re.findall(r'^import\s+(\S+)', source, re.M):
        if imported.startswith('Sheshadri.') or imported == 'OriginalConormal':
            edges.append((module, imported))
            visit(imported)

visit('OriginalConormal')
print(f'PASS: {len(seen)} original-route modules; {len(edges)} local import edges.')
print('No explicit-slice or expanded alternative-proof dependency.')
print('This is an import audit, not an assertion of historical idea originality.')
print('PASS: no custom axiom, sorry, admit, unsafe or native_decide in local source graph.')
for module in sorted(seen):
    print(module)
