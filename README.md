# Quadratic determinantal lower bounds: Lean verification

**Author:** Karthik Sheshadri  
**Version:** `1.0.0-rc.1`  
**Repository:** https://github.com/karthik202321/power-sum-dc-lean  
**Archived release:** [doi:10.5281/zenodo.23274251](https://doi.org/10.5281/zenodo.23274251)

This source release accompanies *A fully Lean-verified quadratic lower bound
on the border determinantal complexity of x₁ⁿ + ⋯ + xₙⁿ over ℂ,
including the symmetric and exact models* (proof by conormal specialization).

- [Paper with the full verification report (PDF)](paper/main.pdf)
- [Paper TeX source](paper/main.tex) and [verification appendix source](paper/lean-verification.tex)
- [arXiv record of the paper](https://arxiv.org/abs/2606.13628)
- [Release notes](RELEASE_NOTES.txt) and [publication instructions](RELEASE_PUBLISHING.md)

[CITATION.cff](CITATION.cff) records the author, version, DOI and repository;
[release-metadata.json](release-metadata.json) records the same identifiers
and the pinned dependencies.

This development gives exact and border determinantal lower bounds for the
Fermat polynomial `f_n = ∑ i : Fin n, X i ^ n`, using local Gauss sections and
specialization of their full intersection multiplicities. For `n ≥ 3`, an
ordinary size-`m` representation, or membership in its border, implies

\[
\frac{(n-1)^2}{4e}\le m.
\]

For symmetric representations and their border, the bound is

\[
\frac{(n-1)^2}{2e}\le m.
\]

The final exact and border endpoints compile. Their theorem statements
assume only `3 ≤ n` and the corresponding literal representation or
border-membership predicate. They have no
`GaussDegreeTheory`, family, genericity, finiteness, multiplicity-persistence,
Bézout, closure-comparison, or cycle certificate as an additional hypothesis.

## Final endpoints

| Case | Namespace | Count endpoints | Quadratic endpoints |
| --- | --- | --- | --- |
| Exact | `Sheshadri.ConormalExactMultiplicity` | `ordinary_exact_count`, `symmetric_exact_count` | `ordinary_exact_quadratic`, `symmetric_exact_quadratic` |
| Finite-support Euclidean border | `Sheshadri.ConormalBorderMultiplicity` | `ordinary_border_count`, `symmetric_border_count` | `ordinary_border_quadratic`, `symmetric_border_quadratic` |
| Canonical-support Euclidean border | `Sheshadri.ConormalBorderMultiplicity` | `ordinary_borderAtSize_count`, `symmetric_borderAtSize_count` | `ordinary_borderAtSize_quadratic`, `symmetric_borderAtSize_quadratic` |
| Zariski border | `Sheshadri.ConormalBorderMultiplicity` | `ordinary_zariski_count`, `symmetric_zariski_count` | `ordinary_zariski_quadratic`, `symmetric_zariski_quadratic` |

The count endpoints bound `fermatCount n = n*(n-1)^(n-2)` by
`ordinaryBezout m n` or `symmetricBezout m n`. The quadratic endpoints apply
the proved estimates for these incidence coefficients. Positive matrix size
is derived from the actual representation or constructed family.

An exact representation is an affine-linear complex matrix pencil whose
determinant is literally `f_n`. In the symmetric case its coefficient
matrices are symmetric. `OrdinaryFiniteSupportBorder` and
`SymmetricFiniteSupportBorder` mean that the Fermat coefficient vector lies
in the Euclidean closure of the actual determinant locus in some finite
coefficient space. The `*_borderAtSize_*` wrappers use the canonical support
containing both Fermat and every size-`m` determinant. The
`ordinary_zariski_count`, `symmetric_zariski_count`,
`ordinary_zariski_quadratic`, and `symmetric_zariski_quadratic` endpoints
start directly from the literal Zariski-border predicates. The quadratic
wrappers compose the count bounds with the proved numerical estimates;
they do not need a Zariski-to-Euclidean closure theorem.

The exact module additionally treats a nonzero homogeneous degree-`d`
polynomial, smooth away from the vertex: from `2 ≤ n`, `0 < d`, and a literal
representation, `ordinary_smooth_degree_bound` and
`symmetric_smooth_degree_bound` bound `d*(d-1)^(n-2)` by the corresponding
incidence coefficient.

## Proof route

1. **Construct the special Gauss section and its degree.** Euler's identity,
   Nullstellensatz, and associated-prime avoidance give successive regular
   polar cuts after irrelevant saturation. Exact sequences compute the
   eventual Hilbert value `n*(n-1)^(n-2)`. A support-avoiding chart gives an
   actual finite algebra, whose decomposition into localized rings identifies
   this value with the sum of their full lengths. The section need not be
   reduced.
2. **Construct the actual border family.** Euclidean closure is contained in
   Zariski closure by a proved coefficient-space argument. Algebraic curve
   selection, normalization, and a finite extension produce an actual DVR
   family with residue field ℂ and one coherent generic matrix pencil. Its
   polynomial specializes exactly to Fermat. No converse closure theorem or
   parametrization of an arbitrary curve by the affine line is assumed.
3. **Construct a finite generic section with the prescribed special flags.**
   `ActualGenericGaussSection.exists_actual_section` chooses DVR coefficients
   retaining the special residues. Associated-prime avoidance and Hilbert
   degree descent prove finiteness of an actual generic quotient `L[x]/J`.
   The ideal `J` is the derivative saturation of the literal polar equations.
   A proved unit gradient combination ensures that every geometric support
   point is smooth. The unsaturated generic equations may have excess
   components.
4. **Preserve full special local multiplicities.** The special square
   equation systems are regular sequences at their isolated Artinian local
   rings. Uniformizer regularity allows denominator cancellation; a nonzero
   special derivative allows saturation cancellation. Thus contracted generic
   equations preserve the complete special local algebras, including
   nilpotents. Simultaneous interpolation and the DVR fibre-dimension
   inequality give
   `fermatCount n ≤ finrank L (L[x]/J)`.
5. **Apply incidence Bézout over the actual generic field.** Scalar extension
   to its algebraic closure preserves the finite quotient dimension.
   Normalized kernel-incidence isomorphisms identify the actual local rings
   with the polar local rings. The proved singular isolated-zero Bézout
   theorem bounds their full lengths and permits excess components elsewhere.
   This gives `finrank L (L[x]/J) ≤ ordinaryBezout m n` or the symmetric bound,
   then the two quadratic constants.

The exact proof uses the special section and incidence comparison directly.
The border proof constructs and applies every intermediate object above; it
never identifies the generic function field with ℂ. Full multiplicities
replace a need for generic reducedness or Kleiman transversality.

## Method and scope

This is a local Gauss-section implementation of conormal/Gauss
specialization. General polar flags supply the special degree; no original
Fermat variable is fixed to manufacture an explicit polar point count. The
chart `x₀ = 1` in the generic construction sets the **added homogenizing
coordinate** to one. It is ordinary dehomogenization of the represented
polynomial.

This does not claim a verbatim formalization of every manuscript step or
establish historical originality of ideas. The older `ConormalExact`
`GaussDegreeTheory` and `ConormalBorder.FamilyCertificate` interfaces remain
conditional interfaces; the final endpoints above do not require their
instantiation. A separately developed global Chow/intersection library and
global projective fibre-cycle assembly are not claimed or needed for these
numerical endpoints. Independently proved Gauss-family, grading, and chart
cycle results remain available.

The isolated-zero local rings are literal polynomial-equation quotients
localized at actual evaluation points in valid projective charts. A separate
identification with stalks on a constructed product of Mathlib `Proj`
schemes is not asserted. Neither support containment alone nor a pointwise
bigraded Hilbert inequality is used to infer the required multiplicity or
mixed-coefficient bound.

## Audits and reproduction

`ORIGINAL_CONORMAL_SCOPE.txt` and `END_TO_END_HYPOTHESES_AUDIT.txt` describe the
current endpoint statements and how their geometric inputs are discharged.
`GENERIC_GAUSS_SECTION_AUDIT.txt`, `DVR_LOCAL_PERSISTENCE_AUDIT.txt`,
`GAUSS_DEGREE_CONSTRUCTION_AUDIT.txt`, `BORDER_DVR_CONSTRUCTION_AUDIT.txt`, and
`EXACT_MULTIPLICITY_AUDIT.txt` detail the constructions. Earlier audits,
including earlier “remaining obligations” lists, are historical snapshots;
the current scope and end-to-end hypothesis audit supersede their old
completion-status statements.

`BUILD_LOG.txt`, `AXIOM_AUDIT.txt`, and `IMPORT_AUDIT.txt` are the verification
transcripts. The axiom audit and the mathematical hypothesis audit serve
different purposes: standard foundational axioms alone do not establish
that a theorem's geometric hypotheses have been discharged. The printed
endpoint types make those hypotheses inspectable. The current audit requests
349 principal declarations. The implementation and semantic source reviews
were AI-assisted; these are not independent human peer-review reports.
Lean compilation and axiom inspection provide the reproducible machine checks.

The verification appendix in [the paper](paper/main.pdf) explains the full
dependency chain and includes a standalone Lean file for inspecting endpoint
types and definitions. Start with `OriginalConormal.lean`, then the two
`Conormal*Multiplicity` endpoint modules and
`END_TO_END_HYPOTHESES_AUDIT.txt`.

## Reproduce the proofs and paper

Lean 4.19.0; Mathlib v4.19.0, commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`.

The archive contains every local Lean source needed by its entry point.
It is **source-complete, not an offline toolchain bundle**: Lean, Mathlib,
their dependency packages and optional compiled caches must be downloaded
on first setup. Install Elan, Git and Python 3, retain the delivered
`lake-manifest.json`, and run from the release root:

```bash
elan toolchain install leanprover/lean4:v4.19.0
lake env lean --version
lake exe cache get
bash verify.sh
```

`verify.sh` builds the project, runs `AxiomAudit.lean`, rejects missing reports
or nonstandard axiom dependencies with `audit_axioms.py`, and runs
`audit_imports.py`. It stops on failure. The cache accelerates dependency
setup; omit its download if intentionally building dependencies from source.
Do not run `lake update` during an exact release reproduction: it can
regenerate dependency metadata. If you deliberately use it, compare all
resolved revisions with the archived manifest before claiming the same build.

To rebuild the PDF, install the TeX dependencies described in
[paper/BUILDING.txt](paper/BUILDING.txt), then run:

```bash
cd paper
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The source preserves the original ACM article format and includes the
unmodified upstream `acmart` class with its provenance and license. It uses
embedded bibliography entries and needs no external `.bib` file or shell
escape. `paper/PAPER_BUILD_LOG.txt` records the manuscript build.

On an untouched extraction, run `sha256sum -c SOURCE_SHA256SUMS.txt` before
regenerating any logs. The manifest covers delivered files except itself.
Build caches and temporary proof experiments are excluded from the archive.
For an intentionally modified release, finish the proof and paper builds,
then use the authoritative packaging selection to refresh and check its manifest:

```bash
python3 tools/package_release.py --manifest-only
python3 tools/package_release.py --check-manifest
python3 tools/package_release.py --output-dir ../release-archives
```

The last command produces the complete release ZIP, a separate arXiv source
ZIP and their checksums in a directory outside the source tree. The packager
excludes dependency/build caches and TeX auxiliaries, while retaining the
intentional audit logs and `paper/PAPER_BUILD_LOG.txt`. See
[RELEASE_PUBLISHING.md](RELEASE_PUBLISHING.md) for file-selection and
determinism details. Updating hashes or packaging does not run the
mathematical checks and does not publish the archive.

## License and attribution

The Lean source, project scripts and reproduction documentation are released
under [Apache-2.0](LICENSE). [NOTICE](NOTICE) describes the scope, attribution,
dependency notices and the paper's separate licensing status. The software
license does not replace the paper's existing arXiv license or third-party
licenses. Managed author headers identify Karthik Sheshadri and 2026 in every
project Lean file; the repository link remains explicitly pending until an
actual URL is supplied. Existing third-party notices are retained.

See [RELEASE_PUBLISHING.md](RELEASE_PUBLISHING.md) for the final steps to
reserve a real Zenodo DOI, populate the metadata and author links, publish
the archive, and submit the linked arXiv revision.
