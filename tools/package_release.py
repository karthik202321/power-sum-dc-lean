#!/usr/bin/env python3
"""Refresh source checksums and create deterministic release/arXiv ZIP files.

Copyright 2026 Karthik Sheshadri
SPDX-License-Identifier: Apache-2.0

This packaging step does not build, audit, reserve a DOI or publish anything.
Finish those checks before packaging. Only Python's standard library is used.
"""

from __future__ import annotations

import argparse
import hashlib
import os
from pathlib import Path
import stat
import tempfile
import time
import zipfile

ROOT = Path(__file__).resolve().parents[1]
RELEASE_NAME = "Sheshadri_Quadratic_Lean_Release"
MAIN_ZIP = RELEASE_NAME + ".zip"
ARXIV_ZIP = "Sheshadri_Quadratic_arXiv_Source.zip"
ARCHIVE_SUMS = "Sheshadri_Quadratic_Archives_SHA256SUMS.txt"
MANIFEST = "SOURCE_SHA256SUMS.txt"
EXCLUDED_DIRS = {".lake", ".git", "__pycache__"}
ROOT_SUFFIXES = {".lean", ".py", ".sh", ".toml", ".json", ".cff", ".md", ".txt"}
ROOT_NAMES = {"LICENSE", "NOTICE", "lean-toolchain", ".gitignore"}
PAPER_NAMES = {
    "main.tex", "lean-verification.tex", "release-metadata.tex", "acmart.cls",
    "main.pdf", "BUILDING.txt", "PAPER_BUILD_LOG.txt", "PAPER_LAYOUT_QA.txt",
}
VENDOR_SUFFIXES = {".cls", ".sty", ".dtx", ".ins", ".bib", ".bst", ".tex", ".txt", ".md"}
VENDOR_NAMES = {"LICENSE", "NOTICE", "README", "COPYING"}
REQUIRED = {
    "OriginalConormal.lean", "AxiomAudit.lean", "verify.sh", "README.md",
    "LICENSE", "NOTICE", "CITATION.cff", ".zenodo.json", "release-metadata.json",
    "lakefile.toml", "lake-manifest.json", "lean-toolchain",
    "AXIOM_AUDIT.txt", "BUILD_LOG.txt", "IMPORT_AUDIT.txt",
    "paper/main.tex", "paper/lean-verification.tex", "paper/release-metadata.tex",
    "paper/acmart.cls", "paper/main.pdf", "paper/BUILDING.txt",
    "paper/PAPER_BUILD_LOG.txt", "paper/vendor/acmart/LICENSE",
}


def selected(relative: Path) -> bool:
    parts = relative.parts
    if EXCLUDED_DIRS.intersection(parts) or relative.name == MANIFEST:
        return False
    if len(parts) == 1:
        return relative.name in ROOT_NAMES or relative.suffix in ROOT_SUFFIXES
    if parts[0] == "Sheshadri":
        return relative.suffix == ".lean"
    if parts[0] == "tools":
        return relative.suffix == ".py"
    if parts[0] == "paper":
        if len(parts) == 2:
            return relative.name in PAPER_NAMES
        if parts[1:3] == ("vendor", "acmart"):
            return relative.suffix in VENDOR_SUFFIXES or relative.name in VENDOR_NAMES
    return False


def source_snapshot(root: Path) -> dict[str, tuple[bytes, int]]:
    """Read selected source bytes once, without following directory symlinks."""
    result = {}
    for directory, subdirs, files in os.walk(root, followlinks=False):
        current = Path(directory)
        subdirs[:] = sorted(name for name in subdirs if name not in EXCLUDED_DIRS)
        for name in sorted(subdirs):
            child = current / name
            if child.is_symlink():
                raise ValueError(f"Unexpected source directory symlink: {child.relative_to(root)}")
        for name in files:
            path = current / name
            relative = path.relative_to(root)
            if not selected(relative):
                continue
            if path.is_symlink() or not path.is_file():
                raise ValueError(f"Selected source is not a regular file: {relative}")
            key = relative.as_posix()
            if "\n" in key or "\r" in key or "\\" in key:
                raise ValueError(f"Filename cannot be represented safely in the manifest: {key!r}")
            # Keep executable files executable, without carrying special permission bits.
            mode = 0o755 if path.stat().st_mode & 0o111 else 0o644
            result[key] = (path.read_bytes(), mode)
    missing = REQUIRED - result.keys()
    if missing:
        raise ValueError("Required release files are missing: " + ", ".join(sorted(missing)))
    if not any(name.startswith("Sheshadri/") and name.endswith(".lean") for name in result):
        raise ValueError("The release has no project Lean modules")
    return dict(sorted(result.items()))


def checksum_manifest(files: dict[str, tuple[bytes, int]]) -> bytes:
    return "".join(f"{hashlib.sha256(data).hexdigest()}  {name}\n" for name, (data, _) in sorted(files.items())).encode()


def archive_timestamp() -> tuple[int, int, int, int, int, int]:
    # This canonical container timestamp is not a publication timestamp.
    raw = os.environ.get("SOURCE_DATE_EPOCH", "315532800")
    try:
        epoch = int(raw)
    except ValueError as error:
        raise ValueError("SOURCE_DATE_EPOCH must be an integer Unix timestamp") from error
    if not 315532800 <= epoch <= 4354819198:
        raise ValueError("SOURCE_DATE_EPOCH must lie within ZIP's 1980--2107 range")
    stamp = time.gmtime(epoch)
    return stamp.tm_year, stamp.tm_mon, stamp.tm_mday, stamp.tm_hour, stamp.tm_min, stamp.tm_sec // 2 * 2


def write_zip(path: Path, files: dict[str, tuple[bytes, int]], prefix: str, timestamp: tuple[int, int, int, int, int, int]) -> None:
    descriptor, temporary_name = tempfile.mkstemp(prefix=".release-", suffix=".zip", dir=path.parent)
    os.close(descriptor)
    temporary = Path(temporary_name)
    try:
        with zipfile.ZipFile(temporary, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
            for name, (data, mode) in sorted(files.items()):
                entry = zipfile.ZipInfo(prefix + name, timestamp)
                entry.create_system = 3
                entry.external_attr = (stat.S_IFREG | mode) << 16
                archive.writestr(entry, data, compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
        os.replace(temporary, path)
    finally:
        if temporary.exists():
            temporary.unlink()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=ROOT.parent, help="Archive destination, outside this source tree (default: its parent)")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--manifest-only", action="store_true", help="Refresh SOURCE_SHA256SUMS.txt without creating archives")
    mode.add_argument("--check-manifest", action="store_true", help="Check the manifest without changing any file")
    args = parser.parse_args()
    try:
        output = args.output_dir.expanduser().resolve()
        if output == ROOT or ROOT in output.parents:
            raise ValueError("The output directory must be outside the source tree")
        files = source_snapshot(ROOT)
        manifest = checksum_manifest(files)
        manifest_path = ROOT / MANIFEST
        if args.check_manifest:
            if not manifest_path.is_file() or manifest_path.read_bytes() != manifest:
                raise ValueError("The source manifest is absent or stale; finish verification, then run --manifest-only")
            print(f"PASS: {MANIFEST} matches all {len(files)} selected delivered files.")
            return
        timestamp = archive_timestamp()
        manifest_path.write_bytes(manifest)
        print(f"Wrote {MANIFEST}: {len(files)} selected delivered files; manifest itself excluded.")
        if args.manifest_only:
            return
        output.mkdir(parents=True, exist_ok=True)
        release = dict(files)
        release[MANIFEST] = (manifest, 0o644)
        # arXiv source has main.tex at ZIP root, no PDF and no generated build log.
        arxiv = {
            name.removeprefix("paper/"): value
            for name, value in files.items()
            if name.startswith("paper/") and name not in {"paper/main.pdf", "paper/PAPER_BUILD_LOG.txt"}
        }
        arxiv[MANIFEST] = (checksum_manifest(arxiv), 0o644)
        write_zip(output / MAIN_ZIP, release, RELEASE_NAME + "/", timestamp)
        write_zip(output / ARXIV_ZIP, arxiv, "", timestamp)
        sums = []
        for name, count in ((MAIN_ZIP, len(release)), (ARXIV_ZIP, len(arxiv))):
            data = (output / name).read_bytes()
            checksum = hashlib.sha256(data).hexdigest()
            sums.append(f"{checksum}  {name}\n")
            print(f"{name}: {count} files, {len(data)} bytes, SHA-256 {checksum}")
        (output / ARCHIVE_SUMS).write_text("".join(sums))
        print(f"Archive checksums: {output / ARCHIVE_SUMS}")
        print("Packaging complete. No mathematical check or public publication was performed by this command.")
    except (OSError, ValueError) as error:
        parser.error(str(error))


if __name__ == "__main__":
    main()
