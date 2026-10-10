/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.ConormalBorder
import Sheshadri.LocalNormalForm
import Sheshadri.SchurDeterminant
import Sheshadri.TransverseCotangent
import Sheshadri.Isolatedness
import Sheshadri.ConormalOffVertex
import Sheshadri.AlgebraicCurveSelection
import Sheshadri.ActualGaussCycles
import Sheshadri.ActualGaussHilbert
import Sheshadri.ActualGaussCoefficientHomogeneous
import Sheshadri.ActualGaussHomogeneous
import Sheshadri.ActualGaussBaseChange
import Sheshadri.ActualGaussHilbertPolynomial
import Sheshadri.CurveThroughBoundary
import Sheshadri.GeneralConormalFlatFamily
import Sheshadri.GeneralConormalDominance
import Sheshadri.ProjectiveFlatFamily
import Sheshadri.ConormalChartPresentation
import Sheshadri.ProjectiveCycleLengths
import Sheshadri.SmoothGradientIdeal
import Sheshadri.HomogeneousQuotientExact
import Sheshadri.CompleteIntersectionHilbert
import Sheshadri.ActualGaussProjectiveFlatCharts
import Sheshadri.ActualProjectiveFibreCharts
import Sheshadri.GeneralFlatHilbertPolynomial
import Sheshadri.SaturatedFlatHilbert
import Sheshadri.BezoutWithExcess
import Sheshadri.BezoutExcessRegressions
import Sheshadri.SingularBezoutWithExcess
import Sheshadri.IsolatedPointLocalRing
import Sheshadri.SingularMultiplicityExamples
import Sheshadri.SingularContractionRegressions
import Sheshadri.ConormalExactMultiplicity
import Sheshadri.ActualProjectiveCycleMultiplicities
import Sheshadri.ProjectiveHilbertLocalLengths
import Sheshadri.DeterminantDvrFamily
import Sheshadri.DVRGaussContainment
import Sheshadri.BorderDvrFamily
import Sheshadri.DVRGaussHomogeneous
import Sheshadri.DeterminantDvrGaussContainment
import Sheshadri.ConormalBorderMultiplicity
import Sheshadri.MixedHilbertComparison
import Sheshadri.AdicScalarCompatibility
import Sheshadri.CompletionFiniteGeneration
import Sheshadri.DVRCompletionDomain

/-!
Independent entry point for the original conormal-specialization route.
No explicit Fermat polar slice is imported transitively.

Both simple-zero and full isolated-local-multiplicity Bezout are proved with
arbitrary excess components allowed.
ConormalExactMultiplicity proves both exact coefficient and quadratic bounds.
ConormalBorderMultiplicity proves both border coefficient and quadratic bounds
from literal border membership, without geometric certificates. The actual
DVR family, special and generic Gauss sections, full multiplicity comparison,
and generic-field incidence degree bound are all constructed in the proof.
The specialization is implemented through local Gauss sections; no claim of
verbatim manuscript formalization or a complete global cycle library is made.
See ORIGINAL_CONORMAL_SCOPE.txt for the precise verification boundary.
-/
