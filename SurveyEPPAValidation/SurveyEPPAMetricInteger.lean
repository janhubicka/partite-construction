import SurveyEPPACorrectedHerwigLascar
import AllThoseEPPA.IntegerMetricEPPA

/-!
# Finite bounded integer metrics: direct survey-facing EPPA consequences

The public AllThoseEPPA.IntegerMetricEPPA interface provides ordinary EPPA
and a strengthening that preserves the largest distance-one clique for
every finite metric with natural-number distances bounded by D.

These statements are direct consequences of the public library API,
not additional hypotheses on automorphism-preserving completions.

IMPORTANT: This does NOT formalize the general real-valued metric EPPA
example printed in the survey; its distance alphabet can include
arbitrary positive real numbers. Nor does this file establish coherent
EPPA, APA, or the result for finite diversities.
-/

namespace SurveyEPPA
namespace Metric
open AllThoseEPPA.IntegerMetric

universe u

/-- The class of all finite D-bounded integer-valued metric spaces
has ordinary EPPA, uniformly for all D, including D=0,1 and empty
carriers. Isometries between arbitrary subsets extend to global
isometries of the finite witness. -/
theorem allFiniteBoundedIntegerMetrics_haveEPPA :
    AllFiniteBoundedMetricsHaveEPPA.{u} := by
  intro D α hα A
  exact eppa D A

/-- Stronger direct consequence: the witness may be chosen to
preserve the maximum size of a unit-distance clique exactly.
This does not automatically follow from ordinary EPPA for
an arbitrary chosen witness. -/
theorem allFiniteBoundedIntegerMetrics_preserveUnitClique :
    AllFiniteBoundedMetricsHaveEPPAAndPreserveUnitClique.{u} := by
  intro D α hα A
  exact eppaPreservingUnitCliqueNumber D A

end Metric
end SurveyEPPA
