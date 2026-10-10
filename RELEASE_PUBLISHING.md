# Publishing this formalization

This is a locally prepared release candidate, version `1.0.0-rc.1`, authored by
Karthik Sheshadri. The repository URL and the reserved Zenodo DOI have been
inserted with the tools below. No upload, publication or arXiv replacement has
been performed. The actual state is in `release-metadata.json`.

The code can be built and audited before these publication details exist.
Publication readiness and mathematical verification are separate checks.

## 1. Establish the repository and reserve a real archive DOI

Create the intended repository under the author's account and obtain its exact
HTTPS URL. Place `LICENSE`, `NOTICE` and `CITATION.cff` in its root. GitHub uses
a root `CITATION.cff` on the default branch to display “Cite this repository.”
The citation is for the software; its references also identify the paper.

For a DOI that can be inserted into this very archive before publication, use
a **manual Zenodo upload**. In an authenticated Zenodo account, create a new
upload, choose Software as the resource type, and enter Karthik Sheshadri as
creator. In the DOI field, select that the upload does not already have a DOI,
then click **Get a DOI now!** Copy the number from that actual draft. Keep the
draft: deleting it loses the reservation. Reserving a DOI does not publish the
record or register a working public DOI.

Zenodo's GitHub integration is a different route: it archives a GitHub release
and then assigns a DOI. Zenodo's documentation states that a DOI cannot be
pre-reserved through that integration. Do not mix a manual reservation with
an independent automatic deposit for the same release.

## 2. Insert the verified identifiers and regenerate the release

From the release root, after putting the actual URL and reserved DOI into the
two shell variables below, run:

```bash
read -r -p 'Actual repository HTTPS URL: ' RELEASE_REPOSITORY_URL
read -r -p 'DOI copied from the Zenodo draft: ' RELEASE_ZENODO_DOI
python3 tools/set_release_metadata.py \
  --repository "$RELEASE_REPOSITORY_URL" \
  --doi "$RELEASE_ZENODO_DOI"
python3 tools/check_release_metadata.py
```

The setter updates `CITATION.cff`, `.zenodo.json`, `release-metadata.json`,
`paper/release-metadata.tex` and the managed attribution comment in every
project Lean file. It preserves existing notices, legacy-scope annotations and
the Lean proof bodies. It does not contact Zenodo, verify ownership of an
identifier, reserve a DOI, change mathematical statements or publish anything.
Copy identifiers from the real records; passing its syntax checks is not
evidence that a DOI belongs to this release.

Before identifiers are available, the following checks consistency while
explicitly allowing an unpublished candidate:

```bash
python3 tools/check_release_metadata.py --allow-pending
```

Without `--allow-pending`, the checker fails if the DOI or repository URL is
missing. This is intentional. It also checks that the generated citation,
paper metadata, author headers and pinned dependency metadata agree.

Rebuild the manuscript PDF after changing its metadata. Follow the exact TeX
build command and reproduction steps in `README.md` and the verification
appendix. Run `bash verify.sh` again after the final source changes. Refresh
`SOURCE_SHA256SUMS.txt` using the manifest procedure below after
the final files and audit outputs have been generated. The old manifest is
expected to be stale after changing metadata or headers; do not present an
earlier hash or an earlier audit as a hash or audit of the rebuilt archive.

Prepare a fresh source ZIP containing the final files, the rebuilt PDF and
the reproduction materials. Exclude dependency/build caches and credentials.
Retain the exact Lean toolchain and dependency revisions; do not use `lake
update` to select newer versions during reproduction. See `NOTICE` for the
paper's separate copyright/licensing status.

### Refresh checksums and create the ZIPs

After the proof audits, PDF build and metadata changes are finished, use the
same packaging script for selection, checksums and archives:

```bash
python3 tools/package_release.py --manifest-only
python3 tools/package_release.py --check-manifest
python3 tools/package_release.py --output-dir ../release-archives
```

The first command refreshes `SOURCE_SHA256SUMS.txt`; the second only checks
it. The third refreshes it again and writes two archives and a checksum file
to the specified directory. That directory must be outside the source tree.
The default output directory is the source tree's parent. Existing archives
with these exact names in the output directory are replaced:

- `Sheshadri_Quadratic_Lean_Release.zip`: one enclosing release folder,
  with the Lean sources, documentation, metadata, audits, paper sources and PDF.
- `Sheshadri_Quadratic_arXiv_Source.zip`: `main.tex` at ZIP root, with its
  source includes, build instructions, the vendored class and its license;
  no compiled PDF or generated paper build log.
- `Sheshadri_Quadratic_Archives_SHA256SUMS.txt`: checksums of both ZIPs.

Both ZIPs include a manifest covering their selected files except the manifest
itself. The packager excludes `.lake`, `.git`, `__pycache__`, dependency/build
caches and TeX auxiliaries. The intentional `paper/PAPER_BUILD_LOG.txt` is kept
in the full release. It includes root release documents/configuration,
`Sheshadri/**/*.lean`, `tools/**/*.py` and the explicitly listed paper files;
if new asset types are added, update the script's selection policy first.
It does not follow source symlinks and preserves executable status for scripts.

ZIP entries are sorted and assigned a canonical 1980-01-01 container timestamp
by default; this is not a publication date. Set `SOURCE_DATE_EPOCH` to an
integer Unix timestamp within ZIP's supported range to use another fixed
timestamp. Identical selected bytes and executable bits, with the same
timestamp and Python/zlib environment, produce identical ZIP bytes. Rebuilding
a PDF or regenerating logs may change their bytes, so finish them first.
Checksums identify bytes; neither refreshing them nor creating ZIPs establishes
that the proof was checked. On an untouched download, use `sha256sum -c
SOURCE_SHA256SUMS.txt` (or the packager's `--check-manifest`) before regenerating
logs. Verify the outside checksum file with `sha256sum -c
Sheshadri_Quadratic_Archives_SHA256SUMS.txt` from the archive destination.

## 3. Publish the archive, then submit the arXiv revision

Upload that ZIP to the **same Zenodo draft** that reserved the DOI. Check its
creator, software title, version, license scope and related paper URL. A
single compressed source archive is the layout Zenodo documents for software
archival in Software Heritage. The supplied `.zenodo.json` follows Zenodo's
documented GitHub metadata format; for a manual deposit, review the actual
web-form metadata rather than assuming the ZIP imports that file.

Preview the record and check the ZIP by downloading it before publishing.
Publish only the intended final archive. The record becomes publicly citable
when Zenodo publishes it and registers its DOI. The packaged metadata may
truthfully record the pre-publication reservation state; do not edit the
already archived bytes merely to change that historical state. Verify the
public record and DOI afterward, and record the published URL in the live
repository. Use Zenodo versioning for subsequent source releases.

Upload an arXiv **replacement** for arXiv:2606.13628 using the revised TeX
source and its included files. The revised paper must contain the actual
archive DOI and repository link generated above, and the formalization
metadata must link back to the arXiv paper. Check the replacement preview and
the resulting public paper before treating the cross-links as published.
The supplied source and PDF are a prepared revision, not evidence that arXiv
has accepted or displayed a replacement. This package does not alter the
paper's existing arXiv license.

## Official documentation

These sources were checked while preparing the release on 2026-10-10 (UTC).

- [Zenodo: reserve a DOI](https://help.zenodo.org/docs/deposit/describe-records/reserve-doi/)
- [Zenodo: create and publish an upload](https://help.zenodo.org/docs/deposit/create-new-upload/)
- [Zenodo: DOI reservation and GitHub releases](https://support.zenodo.org/help/en-gb/24-github-integration/73-can-i-pre-reserved-a-doi-before-a-github-release)
- [Zenodo: upload software manually](https://help.zenodo.org/docs/github/archive-software/manual-upload/)
- [Zenodo: metadata in `.zenodo.json`](https://help.zenodo.org/docs/github/describe-software/zenodo-json/)
- [GitHub: `CITATION.cff` and the citation button](https://docs.github.com/en/repositories/managing-your-repositorys-settings-and-features/customizing-your-repository/about-citation-files)
- [Citation File Format 1.2.0 schema](https://github.com/citation-file-format/citation-file-format/blob/1.2.0/schema.json)
- [arXiv: submit a new version](https://info.arxiv.org/help/replace.html)

When both `CITATION.cff` and `.zenodo.json` exist, Zenodo's GitHub integration
uses `.zenodo.json`. The setter keeps their author, title, version and DOI
fields synchronized; GitHub still uses `CITATION.cff` for its citation button.
