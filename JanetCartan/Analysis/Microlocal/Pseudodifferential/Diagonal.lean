module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Taylor
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Frequency

/-!
# Exact diagonal reduction of integrable amplitudes

The identity in `app:ch_regular_base:eq:actual-pdo-remainder` for actual Bochner
kernels. Smoothness and integrability of the frequency-dependent Taylor coefficient
are explicit hypotheses. Removing frequency regularization and proving uniform
symbol seminorm bounds are separate analytic obligations.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

namespace JanetCartan.Pseudodifferential

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

local instance : ContinuousENorm (V →L[ℝ] V →L[ℝ] F) :=
  (@SeminormedAddGroup.toESeminormedAddMonoid
    (V →L[ℝ] V →L[ℝ] F) inferInstance).toContinuousENorm

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the diagonal principal term
with its fixed source multiplier. -/
def diagonalAmplitude (c : V → V → V → F) (β : V → ℝ) (x y ξ : V) : F :=
  β y • c x x ξ

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the full linear Taylor
coefficient, including both physical positions and the source mask. -/
def fullTaylorCoefficient (c : V → V → V → F) (β : V → ℝ) (x y ξ : V) : V →L[ℝ] F :=
  sourceTaylorCoefficient (fun z ↦ c x z ξ) β x y

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the differentiated full
remainder amplitude, with the `2π` frequency normalization. -/
def diagonalRemainderAmplitude {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (c : V → V → V → F) (β : V → ℝ) (x y ξ : V) : F :=
  normalizedFrequencyDivergence b (fullTaylorCoefficient c β x y) ξ

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: exact diagonal reduction of
an absolutely integrable full amplitude. The integrability hypotheses concern the
explicit Taylor integral and its derivative, not the desired kernel identity. -/
theorem amplitudeKernel_eq_diagonal_add_remainder [CompleteSpace F]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (c : V → V → V → F) (β : V → ℝ) (x y : V)
    (hc : ∀ ξ, ContDiff ℝ 1 (fun z ↦ c x z ξ))
    (hβ : ∀ ξ z, c x z ξ ≠ 0 → β z = 1)
    (hdiag : Integrable (diagonalAmplitude c β x y))
    (hB : Integrable (fullTaylorCoefficient c β x y))
    (hdB : Differentiable ℝ (fullTaylorCoefficient c β x y))
    (hDB : Integrable (fderiv ℝ (fullTaylorCoefficient c β x y))) :
    amplitudeKernel c x y = amplitudeKernel (diagonalAmplitude c β) x y +
      amplitudeKernel (diagonalRemainderAmplitude b c β) x y := by
  have heq (ξ : V) : c x y ξ = diagonalAmplitude c β x y ξ +
      fullTaylorCoefficient c β x y ξ (y - x) :=
    amplitude_eq_diagonal_add_sourceTaylorCoefficient (fun z ↦ c x z ξ) β x y
      (hc ξ) (hβ ξ)
  have hsplit : amplitudeKernel c x y = amplitudeKernel (diagonalAmplitude c β) x y +
      (𝓕 (fullTaylorCoefficient c β x y) (y - x)) (y - x) := by
    rw [Real.fourier_continuousLinearMap_apply hB]
    simp only [amplitudeKernel, Real.fourier_eq]
    simp_rw [heq, smul_add]
    apply integral_add
    · exact (Real.fourierIntegral_convergent_iff (y - x)).mpr hdiag
    · exact (Real.fourierIntegral_convergent_iff (y - x)).mpr
        (hB.apply_continuousLinearMap (y - x))
  rw [hsplit]
  congr 1
  exact (fourier_normalizedFrequencyDivergence b _ (y - x) hB hdB hDB).symm

end JanetCartan.Pseudodifferential
