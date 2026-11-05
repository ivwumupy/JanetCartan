module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalWordGradient
public import JanetCartan.Iteration.PhysicalParameterRemainder.PhaseProfiles
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalObservationPhaseTemplate

/-!
# Global observation jets of the same original physical phase

Use the existing physical-history producer on the COMPLETE support of the
already chosen original phase cutoff. Unlike the finite-word profiles on the
original source box, these bounds include every cutoff shoulder and hold at
all physical and parameter points. The phase is definitionally the SAME
`OriginalWordGradient.φ`, with only its coordinate order changed.

The only new selection is a derivative profile and its prehistory threshold.
No phase, cutoff, source scale, frame, residual, inverse or operator is selected.
Consumer: `exists_observed_parameter_remainders_of_original_profiles` and the
full-inverse remainder field of `complex_inverse_parameter_envelopes_of_actual_finite_words`
(`app:ch_regular:eq:inverse-remainder`, `app:ch_response:eq:response-graded-reduced`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 16000

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPrimary.OriginalObservationPhase
open PhysicalSeed PhysicalInitialization

/-- The canonical positive original phase and the retained extension are the
same function, not merely germs on the source set. This identity fixes every
cutoff shoulder before using the global observation profile
(`app:ch_regular:eq:inverse-remainder`). -/
theorem canonical_phase_eq_retained {d : ℕ} (hn : 5 ≤ d+1)
    (a : OriginalPatchIndex hn)
    (χ : Euclidean (d+1) × (Euclidean 3 × Euclidean d) → ℝ) (Q : _) :
    (fun (c : Euclidean 3 × Euclidean d) (x : Euclidean (d+1)) ↦
      OriginalWordGradient.original_physical_phase hn a χ Q (x,c)) =
    (fun c x ↦ ResponsePrimarySources.retainedPhaseExtension
      (OriginalBoundary.T hn a) Q χ x c) := by
  rfl

end JanetCartan.PhysicalPrimary.OriginalObservationPhase

construct_original_observation_phase_profiles
