#!/usr/bin/env python3
"""Check local consistency; fail publication readiness when DOI/repository are absent.

Copyright 2026 Karthik Sheshadri
SPDX-License-Identifier: Apache-2.0
"""

import argparse
import json
import sys

from set_release_metadata import HEADER_MARKER, ROOT, generated_files, lean_paths, pins, validate_doi, validate_repository


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--allow-pending", action="store_true", help="Check a local candidate without asserting publication readiness")
    args = parser.parse_args()
    meta = json.loads((ROOT / "release-metadata.json").read_text())
    errors = []
    if meta["dependencies"] != pins(ROOT):
        errors.append("Pinned toolchain/manifest metadata is stale.")
    for name, expected in generated_files(meta).items():
        if not (ROOT / name).is_file() or (ROOT / name).read_text() != expected:
            errors.append(f"Generated metadata is inconsistent: {name}")
    for path in lean_paths(ROOT):
        source = path.read_text()
        attribution = source.split("-/", 1)[0]
        required = ("2026 Karthik Sheshadri", "SPDX-License-Identifier: Apache-2.0", "Author: Karthik Sheshadri", meta["paper_url"])
        if not source.startswith(HEADER_MARKER) or not all(text in attribution for text in required):
            errors.append(f"Managed attribution header is missing or inconsistent: {path.relative_to(ROOT)}")
        if meta["repository_url"] and "Repository URL: " + meta["repository_url"] not in attribution:
            errors.append(f"Repository URL missing from header: {path.relative_to(ROOT)}")
        if meta["zenodo_doi"] and "Archive DOI: " + meta["zenodo_doi"] not in attribution:
            errors.append(f"Archive DOI missing from header: {path.relative_to(ROOT)}")
    for field, validator in (("repository_url", validate_repository), ("zenodo_doi", validate_doi)):
        if not meta[field]:
            if not args.allow_pending:
                errors.append(f"Publication metadata incomplete: {field}")
        else:
            try:
                validator(meta[field])
            except ValueError as error:
                errors.append(str(error))
    if meta["publication_status"] != "not_published":
        errors.append("This release-preparation checker does not certify a publication claim.")
    if errors:
        print("\n".join("ERROR: " + error for error in errors), file=sys.stderr)
        return 1
    print("Local release metadata is consistent." + (" DOI/repository may still be pending." if args.allow_pending else " Identifiers are present; publication itself has not been checked."))
    return 0


if __name__ == "__main__":
    sys.exit(main())
