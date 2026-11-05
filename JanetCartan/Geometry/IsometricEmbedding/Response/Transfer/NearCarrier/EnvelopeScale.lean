module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.VectorEnvelope
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.FiniteFiber.Bounds

/-!
# The existing vector Sobolev scale for near-carrier envelopes

The scale adapter for `app:ch_response:eq:direct-envelope-profile` is the same
`ResponseTransfer.Complement.vectorFourierSobolevScale` already used by the
complete complement. In particular, with `I := Fin r`, its base is
`Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))`.
This module reuses that construction and its profile equivalence:

* `Complement.mem_vectorFourierSobolevScale` identifies its levels exactly with
  the existing `MemVectorFourierSobolev`.
* `Complement.vectorFourierSobolevScale_gradeNorm` identifies its norms on
  members exactly with the existing `vectorFourierSobolevNorm`.
* The scale's `level_zero`, `seminorm_zero`, `antitone_level`, and
  `monotone_seminorm` prove normalization, nesting, and norm monotonicity.
  `GradedScale.gradeNorm_zero` and `GradedScale.gradeNorm_mono` give the
  corresponding statements for `gradeNorm`.
* `Complement.hasEnvelopeProfile_vectorFourier_iff` identifies
  `HasEnvelopeProfile` with the uniform vector Fourier-Sobolev membership and
  bound, with the same constants, amplitude, and powers of the source scale.

`vectorSpatialEnvelopeProfile_eq_sum_gradeNorm` connects the finite-fiber
weighted profile to `HasEnvelopeProfile.of_direct_estimate`. The parent must
still instantiate the actual `MatrixSpatialEstimate` and
`MatrixParameterEstimate` from raw profiles; this adapter introduces no graph
estimate premise and makes no assertion of a completed graph construction.
-/

@[expose] public noncomputable section

open MeasureTheory
open JanetCartan.Pseudodifferential JanetCartan.ResponseTransfer.Complement

namespace JanetCartan.IsometricEmbedding.Response.NearCarrier.FiniteFiber

variable {d r : ℕ}

/-- The exact weighted sum in `app:ch_response:eq:direct-envelope-profile`,
expressed in the shared graded scale. Membership at the top order supplies
every lower-order domain needed by `HasEnvelopeProfile.of_direct_estimate`.
The parent's `MatrixSpatialEstimate` supplies the actual operator estimate. -/
theorem vectorSpatialEnvelopeProfile_eq_sum_gradeNorm (s : ℕ) (L : ℝ)
    (f : Lp (EuclideanSpace ℂ (Fin r)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hf : MemVectorFourierSobolev s f) :
    vectorSpatialEnvelopeProfile s L f =
      ∑ p ∈ Finset.range (s + 1),
        L ^ (s - p) * vectorFourierSobolevScale.gradeNorm p f := by
  unfold vectorSpatialEnvelopeProfile
  apply Finset.sum_congr rfl
  intro p hp
  have hps : p ≤ s := Nat.le_of_lt_succ (Finset.mem_range.mp hp)
  have hfp : MemVectorFourierSobolev p f :=
    vectorFourierSobolevScale.antitone_level hps hf
  rw [vectorFourierSobolevScale_gradeNorm p hfp]

end JanetCartan.IsometricEmbedding.Response.NearCarrier.FiniteFiber
