module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingKernelBounds.Synthesis
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputRealization.Bounds

/-!
# The literal oscillatory band kernel and its squared integral

For `app:ch_waves:eq:sampling-operator-bounds`, the half derivative contributes
one power of the band radius and the initial annular volume contributes `n-1`.
The amplitude includes the physical measurement cutoff and any fixed Fourier
normalization. The mask is retained literally. These estimates do not use phase
nondegeneracy and do not prove the sharper single-channel operator norm bound.
-/

@[expose] public noncomputable section

open MeasureTheory
open JanetCartan.RawInputRealization

namespace JanetCartan.SamplingKernelBounds

variable {n : ℕ}

/-- The measured half-derivative oscillatory kernel of
`app:ch_waves:eq:sampling-operator-bounds`. Its input uses `annularMeasure n R`. -/
def bandKernel (phase : Euclidean (n - 1) → Euclidean n → ℝ)
    (mask : Euclidean (n - 1) → ℂ)
    (amplitude : Euclidean (n - 1) → Euclidean n → EuclideanSpace ℂ (Fin n))
    (η : Euclidean (n - 1)) (x : Euclidean n) : EuclideanSpace ℂ (Fin n) :=
  (Complex.exp ((phase η x : ℂ) * Complex.I) * (Real.sqrt ‖η‖ : ℂ) * mask η) •
    amplitude η x

/-- The phase has modulus one, so the squared kernel has exactly the
half-derivative factor in `app:ch_waves:eq:sampling-operator-bounds`. -/
theorem norm_bandKernel_sq (phase : Euclidean (n - 1) → Euclidean n → ℝ)
    (mask : Euclidean (n - 1) → ℂ)
    (a : Euclidean (n - 1) → Euclidean n → EuclideanSpace ℂ (Fin n))
    (η : Euclidean (n - 1)) (x : Euclidean n) :
    ‖bandKernel phase mask a η x‖ ^ 2 = ‖η‖ * ‖mask η‖ ^ 2 * ‖a η x‖ ^ 2 := by
  simp only [bandKernel, norm_smul, norm_mul, Complex.norm_exp_ofReal_mul_I,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    one_mul, mul_pow, Real.sq_sqrt (norm_nonneg _)]

/-- Compact physical measurement bounds the inner squared-kernel integral
in `app:ch_waves:eq:sampling-operator-bounds`. -/
theorem integral_norm_bandKernel_sq_le
    (phase : Euclidean (n - 1) → Euclidean n → ℝ)
    (mask : Euclidean (n - 1) → ℂ)
    (a : Euclidean (n - 1) → Euclidean n → EuclideanSpace ℂ (Fin n))
    {S : Set (Euclidean n)} (hS : IsCompact S)
    {M B : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hmask : ∀ η, ‖mask η‖ ≤ B) (ha : ∀ η x, ‖a η x‖ ≤ M)
    (hsupport : ∀ η x, x ∉ S → a η x = 0) (η : Euclidean (n - 1)) :
    (∫ x, ‖bandKernel phase mask a η x‖ ^ 2) ≤
      volume.real S * (‖η‖ * B ^ 2 * M ^ 2) := by
  classical
  rw [← smul_eq_mul, ← integral_indicator_const _ hS.measurableSet]
  apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ ↦ sq_nonneg _))
    ((integrableOn_const (C := ‖η‖ * B ^ 2 * M ^ 2) hS.measure_lt_top.ne).integrable_indicator hS.measurableSet)
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  rw [norm_bandKernel_sq]
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem hx]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) hB).mpr (hmask η))
        (norm_nonneg _))
      ((sq_le_sq₀ (norm_nonneg _) hM).mpr (ha η x)) (sq_nonneg _) (by positivity)
  · simp [Set.indicator_of_notMem hx, hsupport η x hx]

/-- The actual annular squared-kernel bound has exponent `n`, with a constant
independent of radius, phase, color and parameter
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem double_integral_norm_bandKernel_sq_le (hn : 1 ≤ n)
    (phase : Euclidean (n - 1) → Euclidean n → ℝ)
    (mask : Euclidean (n - 1) → ℂ)
    (a : Euclidean (n - 1) → Euclidean n → EuclideanSpace ℂ (Fin n))
    {S : Set (Euclidean n)} (hS : IsCompact S)
    {R M B : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hmask : ∀ η, ‖mask η‖ ≤ B) (ha : ∀ η x, ‖a η x‖ ≤ M)
    (hsupport : ∀ η x, x ∉ S → a η x = 0) :
    (∫ η, ∫ x, ‖bandKernel phase mask a η x‖ ^ 2 ∂volume ∂annularMeasure n R) ≤
      (volume.real S * B ^ 2 * M ^ 2 * unitBallVolume n) * R ^ n := by
  have hinner : ∀ᵐ η ∂annularMeasure n R,
      (∫ x, ‖bandKernel phase mask a η x‖ ^ 2) ≤ volume.real S * (R * B ^ 2 * M ^ 2) := by
    filter_upwards [ae_restrict_mem (measurableSet_annulus n R)] with η hη
    have hηR : ‖η‖ ≤ R := by simpa using hη.1
    exact (integral_norm_bandKernel_sq_le phase mask a hS hM hB hmask ha hsupport η).trans
      (by gcongr)
  calc
    _ ≤ ∫ _η, volume.real S * (R * B ^ 2 * M ^ 2) ∂annularMeasure n R :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ ↦ integral_nonneg
        (fun _ ↦ sq_nonneg _))) (integrable_const _) hinner
    _ = (annularMeasure n R Set.univ).toReal *
        (volume.real S * (R * B ^ 2 * M ^ 2)) := by rw [integral_const]; rfl
    _ ≤ (R ^ (n - 1) * unitBallVolume n) *
        (volume.real S * (R * B ^ 2 * M ^ 2)) :=
      mul_le_mul_of_nonneg_right (annularMeasure_real_le hR) (by positivity)
    _ = _ := by
      have he : R * R ^ (n - 1) = R ^ n := by
        rw [← pow_succ']; congr 1; omega
      calc
        _ = (volume.real S * B ^ 2 * M ^ 2 * unitBallVolume n) *
            (R * R ^ (n - 1)) := by ring
        _ = _ := by rw [he]

end JanetCartan.SamplingKernelBounds
