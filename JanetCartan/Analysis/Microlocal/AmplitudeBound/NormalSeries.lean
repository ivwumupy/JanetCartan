module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.OperatorSeries

/-!
# Two-position normal-operator series

The summation step for `app:ch_osc:eq:two-position-normal-bound` in `paper.tex`.
The coefficient operators below represent multiplication by `cₚq g`. Their bounds
are inputs; identifying the series with the full integral kernel remains separate.
-/

@[expose] public noncomputable section

namespace JanetCartan.AmplitudeBound

variable {ι H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- One `T [cₚq g] T*` coefficient of `app:ch_osc:eq:two-position-normal-bound`. -/
def normalCoefficient (T : K →L[ℂ] H) (C : ι → K →L[ℂ] K) (i : ι) : H →L[ℂ] H :=
  T.comp ((C i).comp T.adjoint)

/-- The normal series from `app:ch_osc:eq:two-position-normal-bound`. -/
def normalAmplitudeOperator (L R : ι → H →L[ℂ] H) (T : K →L[ℂ] H)
    (C : ι → K →L[ℂ] K) : H →L[ℂ] H :=
  amplitudeOperator L R (normalCoefficient T C)

/-- The squared norm of `T` in `app:ch_osc:eq:two-position-normal-bound` comes from
composition with `T` and its actual Hilbert adjoint. -/
theorem norm_normalCoefficient_le (T : K →L[ℂ] H) (C : ι → K →L[ℂ] K)
    (c : ι → ℝ) (G : ℝ)
    (hC : ∀ i, ‖C i‖ ≤ c i * G) (i : ι) :
    ‖normalCoefficient T C i‖ ≤ c i * ‖T‖ ^ 2 * G := by
  calc
    ‖normalCoefficient T C i‖ ≤ ‖T‖ * ‖(C i).comp T.adjoint‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖T‖ * (‖C i‖ * ‖T.adjoint‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ ≤ ‖T‖ * ((c i * G) * ‖T‖) := by
      rw [LinearIsometryEquiv.norm_map]
      gcongr
      exact hC i
    _ = c i * ‖T‖ ^ 2 * G := by ring

/-- Absolute convergence of the normal series in
`app:ch_osc:eq:two-position-normal-bound`. -/
theorem hasSum_normalCoefficient (L R : ι → H →L[ℂ] H) (T : K →L[ℂ] H)
    (C : ι → K →L[ℂ] K) (c : ι → ℝ) (G : ℝ)
    (hL : ∀ i, ‖L i‖ ≤ 1) (hR : ∀ i, ‖R i‖ ≤ 1)
    (hC : ∀ i, ‖C i‖ ≤ c i * G)
    (hs : Summable c) :
    HasSum (modulatedTerm L R (normalCoefficient T C)) (normalAmplitudeOperator L R T C) :=
  hasSum_modulatedTerm L R _ (fun i ↦ c i * ‖T‖ ^ 2 * G) hL hR
    (norm_normalCoefficient_le T C c G hC) ((hs.mul_right _).mul_right _)

/-- The normal-series estimate in `app:ch_osc:eq:two-position-normal-bound`,
conditional on the summable physical coefficient estimates. -/
theorem norm_normalAmplitudeOperator_le (L R : ι → H →L[ℂ] H) (T : K →L[ℂ] H)
    (C : ι → K →L[ℂ] K) (c : ι → ℝ) (G : ℝ)
    (hL : ∀ i, ‖L i‖ ≤ 1) (hR : ∀ i, ‖R i‖ ≤ 1)
    (hC : ∀ i, ‖C i‖ ≤ c i * G)
    (hs : Summable c) :
    ‖normalAmplitudeOperator L R T C‖ ≤ (∑' i, c i) * ‖T‖ ^ 2 * G := by
  calc
    ‖normalAmplitudeOperator L R T C‖ ≤ ∑' i, c i * ‖T‖ ^ 2 * G :=
      norm_amplitudeOperator_le L R _ _ hL hR
        (norm_normalCoefficient_le T C c G hC) ((hs.mul_right _).mul_right _)
    _ = (∑' i, c i) * ‖T‖ ^ 2 * G := by rw [tsum_mul_right, tsum_mul_right]

end JanetCartan.AmplitudeBound
