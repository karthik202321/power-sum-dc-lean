#!/usr/bin/env python3
"""Synchronize verified release identifiers without changing Lean proof bodies.

Copyright 2026 Karthik Sheshadri
SPDX-License-Identifier: Apache-2.0

This program neither reserves a DOI nor publishes anything. The operator must
copy the repository URL and reserved DOI from their actual repository/deposit.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path
from urllib.parse import urlsplit

ROOT = Path(__file__).resolve().parents[1]
HEADER_MARKER = "/-\nRelease attribution (managed; proof body unchanged).\n"
PAPER_URL = "https://arxiv.org/abs/2606.13628"


def validate_repository(value: str) -> str:
    parsed = urlsplit(value)
    forbidden = ("example", "placeholder", "your-name", "yourname", "your-repo", "yourrepo")
    if (
        parsed.scheme != "https"
        or not parsed.hostname
        or parsed.username
        or parsed.password
        or parsed.query
        or parsed.fragment
        or len([part for part in parsed.path.split("/") if part]) < 2
        or any(part in value.lower() for part in forbidden)
        or not re.fullmatch(r"https://[A-Za-z0-9./_~:+@-]+", value)
        or "/-" in value
        or "-/" in value
        or parsed.hostname in {"localhost", "127.0.0.1"}
        or parsed.hostname.endswith((".invalid", ".test", ".localhost"))
    ):
        raise ValueError("Supply the actual HTTPS repository URL, without credentials, query or fragment.")
    return value.rstrip("/")


def validate_doi(value: str) -> str:
    value = value.removeprefix("https://doi.org/")
    if not re.fullmatch(r"10\.5281/zenodo\.[1-9][0-9]{3,}", value):
        raise ValueError("Supply the actual production Zenodo DOI (10.5281/zenodo.<record number>).")
    if value.rsplit(".", 1)[1] in {"1234", "12345", "123456", "1234567", "12345678", "1003150"}:
        raise ValueError("An example DOI is not a release DOI.")
    return value


def pins(root: Path) -> dict:
    manifest = json.loads((root / "lake-manifest.json").read_text())
    mathlib = next(package for package in manifest["packages"] if package["name"] == "mathlib")
    return {
        "lean_toolchain": (root / "lean-toolchain").read_text().strip(),
        "mathlib_repository": mathlib["url"],
        "mathlib_commit": mathlib["rev"],
        "lean_toolchain_sha256": hashlib.sha256((root / "lean-toolchain").read_bytes()).hexdigest(),
        "lake_manifest_sha256": hashlib.sha256((root / "lake-manifest.json").read_bytes()).hexdigest(),
    }


def citation_data(meta: dict) -> dict:
    result = {
        "cff-version": "1.2.0",
        "message": "If you use this formalization, please cite this software and the associated paper.",
        "type": "software",
        "title": meta["title"],
        "authors": [{"family-names": "Sheshadri", "given-names": "Karthik", "email": meta["author_email"]}],
        "version": meta["version"],
        "license": "Apache-2.0",
        "abstract": "Lean 4 formalization accompanying quadratic lower bounds for ordinary and symmetric determinantal complexity, including exact and border representations. See the verification report for the precise formal statements, scope and reproduction instructions.",
        "keywords": ["Lean 4", "formal verification", "determinantal complexity", "conormal specialization"],
        "references": [{
            "type": "article",
            "title": "A near-quadratic lower bound on the border determinantal complexity of $\\sum_i x_i^n$ via conormal specialization",
            "authors": [{"family-names": "Sheshadri", "given-names": "Karthik"}],
            "year": 2026,
            "url": meta["paper_url"],
            "notes": "Original arXiv record (title of v1). The accompanying revision is titled 'A fully Lean-verified quadratic lower bound on the border determinantal complexity of x_1^n + ... + x_n^n over C, including the symmetric and exact models' and adds the Lean verification report.",
        }],
    }
    if meta["repository_url"]:
        result["repository-code"] = meta["repository_url"]
        result["url"] = meta["repository_url"]
    if meta["zenodo_doi"]:
        result["doi"] = meta["zenodo_doi"]
    return result


def yaml_text(value: object, indent: int = 0) -> str:
    """Emit this metadata's JSON-shaped values as readable YAML 1.2."""
    prefix = " " * indent
    if isinstance(value, dict):
        lines = []
        for key, item in value.items():
            if isinstance(item, (dict, list)):
                lines.append(f"{prefix}{key}:\n{yaml_text(item, indent + 2)}")
            else:
                lines.append(f"{prefix}{key}: {json.dumps(item, ensure_ascii=False)}")
        return "\n".join(lines)
    if isinstance(value, list):
        lines = []
        for item in value:
            if isinstance(item, (dict, list)):
                rendered = yaml_text(item, indent + 2).splitlines()
                lines.append(prefix + "- " + rendered[0][indent + 2:])
                lines.extend(rendered[1:])
            else:
                lines.append(prefix + "- " + json.dumps(item, ensure_ascii=False))
        return "\n".join(lines)
    raise TypeError(type(value))


def zenodo_data(meta: dict) -> dict:
    related = [{"identifier": meta["paper_url"], "relation": "isSupplementTo", "resource_type": "publication-preprint"}]
    if meta["repository_url"]:
        related.append({"identifier": meta["repository_url"], "relation": "isSupplementTo", "resource_type": "software"})
    result = {
        "title": meta["title"],
        "creators": [{"name": "Sheshadri, Karthik"}],
        "description": "Lean 4 formalization and reproduction materials for quadratic ordinary and symmetric determinantal complexity lower bounds. The included paper explains the proof and formalization scope. Apache-2.0 applies to code, scripts and reproduction documentation; the paper retains its author's copyright as stated in NOTICE.",
        "upload_type": "software",
        "version": meta["version"],
        "license": "apache-2.0",
        "access_right": "open",
        "related_identifiers": related,
        "keywords": ["Lean 4", "formal verification", "determinantal complexity", "conormal specialization"],
    }
    if meta["zenodo_doi"]:
        result["doi"] = meta["zenodo_doi"]
    return result


def header(meta: dict) -> str:
    repo = meta["repository_url"] or "not yet assigned; see release-metadata.json"
    doi = meta["zenodo_doi"] or "not yet assigned"
    return (
        HEADER_MARKER
        + "Copyright 2026 Karthik Sheshadri\n"
        + "SPDX-License-Identifier: Apache-2.0\n"
        + "Author: Karthik Sheshadri\n"
        + f"Repository URL: {repo}\n"
        + f"Archive DOI: {doi}\n"
        + f"Paper: {meta['paper_url']}\n"
        + "Existing notices below remain in force.\n-/\n\n"
    )


def strip_managed_header(text: str) -> str:
    if not text.startswith(HEADER_MARKER):
        return text
    end = text.find("-/", len(HEADER_MARKER))
    if end < 0:
        raise ValueError("Unterminated managed Lean header")
    return text[end + 2:]


def replace_managed_header(source: str, meta: dict) -> str:
    if not source.startswith(HEADER_MARKER):
        return header(meta) + source
    end = source.find("-/", len(HEADER_MARKER))
    if end < 0:
        raise ValueError("Unterminated managed Lean header")
    old_header, body = source[:end], source[end:]
    new_lines = []
    doi_seen = False
    repository_seen = False
    for line in old_header.splitlines():
        if line.startswith(("Repository:", "Repository URL:")):
            new_lines.append("Repository URL: " + meta["repository_url"])
            repository_seen = True
        elif line.startswith("Archive DOI:"):
            new_lines.append("Archive DOI: " + meta["zenodo_doi"])
            doi_seen = True
        else:
            new_lines.append(line)
    if not repository_seen:
        new_lines.append("Repository URL: " + meta["repository_url"])
    if not doi_seen:
        new_lines.append("Archive DOI: " + meta["zenodo_doi"])
    # Retain legacy annotations and all bytes after the managed comment.
    return "\n".join(new_lines) + "\n" + body


def lean_paths(root: Path) -> list[Path]:
    return sorted(path for path in root.rglob("*.lean") if not any(part in {".lake", ".git"} for part in path.relative_to(root).parts))


def tex_metadata(meta: dict) -> str:
    def link_or_pending(value: str | None, label: str) -> str:
        return r"\url{" + value + "}" if value else label + " not yet assigned"
    repo = link_or_pending(meta["repository_url"], "Repository URL")
    doi = link_or_pending("https://doi.org/" + meta["zenodo_doi"] if meta["zenodo_doi"] else None, "Archive DOI")
    status = "DOI reserved; archive not yet published" if meta["zenodo_doi"] else "Release candidate; archive not yet published"
    return (
        "% Generated by tools/set_release_metadata.py; no public action is performed.\n"
        + r"\providecommand{\leanRepositoryURL}{" + repo + "}\n"
        + r"\providecommand{\leanArchiveDOI}{" + doi + "}\n"
        + r"\providecommand{\leanPaperURL}{\url{" + meta["paper_url"] + "}}\n"
        + r"\providecommand{\leanPublicationStatus}{" + status + "}\n"
    )


def generated_files(meta: dict) -> dict[str, str]:
    return {
        "CITATION.cff": yaml_text(citation_data(meta)) + "\n",
        ".zenodo.json": json.dumps(zenodo_data(meta), indent=2, ensure_ascii=False) + "\n",
        "paper/release-metadata.tex": tex_metadata(meta),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository", required=True, help="Verified actual HTTPS repository URL")
    parser.add_argument("--doi", required=True, help="DOI copied from your actual production Zenodo draft")
    args = parser.parse_args()
    try:
        repository = validate_repository(args.repository)
        doi = validate_doi(args.doi)
        meta = json.loads((ROOT / "release-metadata.json").read_text())
        if meta.get("publication_status") == "published":
            raise ValueError("This is a published release; prepare a new version before changing identifiers.")
        meta.update(repository_url=repository, zenodo_doi=doi, doi_status="reserved", publication_status="not_published")
        meta["dependencies"] = pins(ROOT)
        updates = generated_files(meta)
        updates["release-metadata.json"] = json.dumps(meta, indent=2, ensure_ascii=False) + "\n"
        paths = lean_paths(ROOT)
        for path in paths:
            source = path.read_text()
            body = strip_managed_header(source)
            replacement = replace_managed_header(source, meta)
            if source.startswith(HEADER_MARKER) and strip_managed_header(replacement) != body:
                raise ValueError(f"Proof body would change: {path}")
            updates[str(path.relative_to(ROOT))] = replacement
        # All inputs and replacements are validated before the first write.
        for relative, content in updates.items():
            (ROOT / relative).write_text(content)
    except (ValueError, KeyError, OSError) as error:
        parser.error(str(error))
    print(f"Updated release identifiers and {len(paths)} managed Lean headers; proof bodies unchanged.")
    print("Nothing has been published. Rebuild the PDF, refresh hashes, verify, and prepare a new archive.")


if __name__ == "__main__":
    main()
