module

public import JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticProfilesTemplate
public import JanetCartan.Iteration.PhysicalPrimary.OriginalJointResponseRegularity
public import JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaves
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivative
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticProfilesTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate

/-!
# Actual original mean quadratic inputs

The fixed geometry below is read from the SAME original scalar tester and
contains the complete whole-source derivative observation support. The low
`H^0 × H^(n/2+2)` estimate and all-order source profile must use task14's actual
G, task26's one common event and task88's single positive-current inverse.
Geometry alone does not assert either quadratic estimate or completion of the
mean Picard construction (`app:ch_mean_pairs:eq:block-bilinear`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

construct_original_mean_quadratic_geometry

set_option maxHeartbeats 600000 in
construct_original_mean_response_integral_continuity

set_option maxHeartbeats 600000 in
construct_original_mean_whole_derivative_integral

set_option maxHeartbeats 600000 in
construct_original_mean_whole_refined_integral

construct_original_mean_inner_annular
construct_original_mean_full_annular

namespace JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles

/-- One ordinary prehistory pays both the saved native-event threshold and the
sampled-moment chart threshold; the same reached history is reused. -/
theorem common_prehistory_max (Snative Smoment : ℝ) :
    Snative ≤ max Snative Smoment ∧ Smoment ≤ max Snative Smoment :=
  ⟨le_max_left _ _, le_max_right _ _⟩

end JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles
