module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalDataBounds.Estimates

/-!
# Finite accumulation of canonical initial data

Support and Fourier variation for `main:eq:variation`. The band count and ceiling
may vary at every update. The same continuum inverse is used throughout, and
the bounds never divide by a sample weight. The residual sum bound is an input
from the mean recurrence; the canonical Fourier bounds are proved here.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.CanonicalDataBounds

open RawInputRealization

variable {n : ℕ} {κ : Type*} {J : κ → ℕ}
  {Output : Type*} [NormedAddCommGroup Output] [InnerProductSpace ℝ Output]
  [CompleteSpace Output]
  (s : Finset κ) (β : ∀ l, Fin (J l) → Euclidean (n - 1) → ℂ)
  (A : ∀ l, Input n (fun i : Fin (J l) ↦ (2 : ℝ) ^ i.val) →L[ℝ] Output)
  (Q0 : Output →L[ℝ] Output) (r : κ → Output)

/-- Finite canonical accumulation preserves the largest initial Fourier
ceiling, as used after `main:eq:variation`. -/
theorem sum_fourierDensity_eq_zero_above_ceiling {C Kmax : ℝ}
    (hceil : ∀ l ∈ s, (2 : ℝ) ^ J l ≤ C * Kmax)
    {η : Euclidean (n - 1)} (hη : C * Kmax < ‖η‖) :
    (∑ l ∈ s, fourierDensity (β l) (A l) Q0 (r l) η) = 0 := by
  exact Finset.sum_eq_zero fun l hl ↦
    fourierDensity_eq_zero_of_dyadic_ceiling (A l) Q0 (hceil l hl) (r l) hη

/-- The finite sum of actual data is the inverse Fourier integral of the
finite sum of their actual densities (`main:eq:variation`). -/
theorem sum_initialDatum_eq_fourierIntegral
    (hβ : ∀ l ∈ s, ∀ i, Measurable (β l i)) {M : ℝ}
    (hM : ∀ l ∈ s, ∀ i η, ‖β l i η‖ ≤ M) :
    (fun x ↦ ∑ l ∈ s, initialDatum (β l) (A l) Q0 (r l) x) =
      VectorFourier.fourierIntegral Real.fourierChar volume
        (radianPairing n).toLinearMap₁₂
        (fun η ↦ ∑ l ∈ s, fourierDensity (β l) (A l) Q0 (r l) η) := by
  funext x
  simp only [VectorFourier.fourierIntegral, Finset.smul_sum]
  rw [integral_finsetSum s]
  · rfl
  · intro l hl
    exact (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar
      (radianPairing n).continuous₂ x).2
        (integrable_fourierDensity (hβ l hl) (hM l hl) (A l) Q0 (r l))

/-- The Fourier norm of the accumulated datum is bounded by its total Fourier
variation (`main:eq:variation`), without cancellation assumptions. -/
theorem integral_norm_sum_fourierDensity_le
    (hβ : ∀ l ∈ s, ∀ i, Measurable (β l i)) {M : ℝ}
    (hM : ∀ l ∈ s, ∀ i η, ‖β l i η‖ ≤ M) :
    (∫ η, ‖∑ l ∈ s, fourierDensity (β l) (A l) Q0 (r l) η‖) ≤
      ∑ l ∈ s, ∫ η, ‖fourierDensity (β l) (A l) Q0 (r l) η‖ := by
  have hi (l) (hl : l ∈ s) :=
    integrable_fourierDensity (hβ l hl) (hM l hl) (A l) Q0 (r l)
  rw [← integral_finsetSum s (fun l hl ↦ (hi l hl).norm)]
  exact integral_mono (integrable_finsetSum s hi).norm
    (integrable_finsetSum s (fun l hl ↦ (hi l hl).norm))
    (fun η ↦ norm_sum_le s _)

/-- Sum the proved individual Fourier estimates using the largest ceiling.
The only accumulation input is the sum of residual norms, supplied separately
by the recurrence in `main:eq:variation`. -/
theorem sum_integral_norm_fourierDensity_le (hn : 1 ≤ n)
    (hβ : ∀ l ∈ s, ∀ i, Measurable (β l i)) {M C CA CQ Kmax : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ l ∈ s, ∀ i η, ‖β l i η‖ ≤ M)
    (hC : 0 ≤ C) (hCA : 0 ≤ CA) (K : κ → ℝ)
    (hK : ∀ l ∈ s, 0 < K l) (hmax : ∀ l ∈ s, K l ≤ Kmax)
    (hceil : ∀ l ∈ s, (2 : ℝ) ^ J l ≤ C * K l)
    (hA : ∀ l ∈ s, ‖A l‖ ≤ CA * Real.sqrt (K l)) (hQ : ‖Q0‖ ≤ CQ) :
    (∑ l ∈ s, ∫ η, ‖fourierDensity (β l) (A l) Q0 (r l) η‖) ≤
      (M * Real.sqrt (unitBallVolume n) * C ^ ((n : ℝ) / 2) * CA * CQ) *
        Kmax ^ (((n : ℝ) + 1) / 2) * ∑ l ∈ s, ‖r l‖ := by
  have hQ0 : 0 ≤ CQ := (norm_nonneg _).trans hQ
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l hl
  apply (integral_norm_fourierDensity_le (A l) Q0 hn (hβ l hl) hM0 (hM l hl)
    hC hCA (hK l hl) (hceil l hl) (hA l hl) hQ (r l)).trans
  gcongr
  · exact (hK l hl).le
  · exact hmax l hl

/-- The quantitative Fourier variation in `main:eq:variation`, conditional
only on the raw analytic inputs and the recurrence's residual budget. -/
theorem sum_integral_norm_fourierDensity_le_of_residual_budget (hn : 1 ≤ n)
    (hβ : ∀ l ∈ s, ∀ i, Measurable (β l i)) {M C CA CQ Kmax ε : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ l ∈ s, ∀ i η, ‖β l i η‖ ≤ M)
    (hC : 0 ≤ C) (hCA : 0 ≤ CA) (hmax0 : 0 ≤ Kmax) (K : κ → ℝ)
    (hK : ∀ l ∈ s, 0 < K l) (hmax : ∀ l ∈ s, K l ≤ Kmax)
    (hceil : ∀ l ∈ s, (2 : ℝ) ^ J l ≤ C * K l)
    (hA : ∀ l ∈ s, ‖A l‖ ≤ CA * Real.sqrt (K l)) (hQ : ‖Q0‖ ≤ CQ)
    (hbudget : ∑ l ∈ s, ‖r l‖ ≤ ε) :
    (∑ l ∈ s, ∫ η, ‖fourierDensity (β l) (A l) Q0 (r l) η‖) ≤
      (M * Real.sqrt (unitBallVolume n) * C ^ ((n : ℝ) / 2) * CA * CQ) *
        ε * Kmax ^ (((n : ℝ) + 1) / 2) := by
  have hQ0 : 0 ≤ CQ := (norm_nonneg _).trans hQ
  apply (sum_integral_norm_fourierDensity_le s β A Q0 r hn hβ hM0 hM hC hCA K
    hK hmax hceil hA hQ).trans
  calc
    _ ≤ (M * Real.sqrt (unitBallVolume n) * C ^ ((n : ℝ) / 2) * CA * CQ) *
        Kmax ^ (((n : ℝ) + 1) / 2) * ε :=
      mul_le_mul_of_nonneg_left hbudget (by positivity)
    _ = _ := by ring

end JanetCartan.CanonicalDataBounds
