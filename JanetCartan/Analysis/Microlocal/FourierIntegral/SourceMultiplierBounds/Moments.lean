module

public import JanetCartan.Analysis.Microlocal.Localization.PhysicalPlancherel
public import JanetCartan.Analysis.Microlocal.FourierIntegral.Kernel
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Fixed physical source Fourier moments

The near/far proof following `app:ch_regular_base:eq:fixed-source-multiplication`
uses moments of one and the same source cutoff. The density below includes
`(2π)⁻ⁿ` and converts Mathlib's unit-period Fourier transform to physical
covectors. In particular, the decay order never changes the source function.

These lemmas are consumed by `SourceMultiplierBounds` and ultimately by the
finite graph calculus. Compact smooth sources can be supplied by
`HasCompactSupport.toSchwartzMap`; Schwartz sources already suffice here.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped SchwartzMap

namespace JanetCartan.FourierIntegral.SourceBounds

variable {n : ℕ}

/-- The fixed source density in physical frequency, including the inverse Fourier
normalization (`app:ch_regular_base:eq:fixed-source-multiplication`). -/
def physicalSourceDensity (m : 𝓢(Euclidean n, ℂ)) : 𝓢(Euclidean n, ℂ) :=
  (((2 * Real.pi) ^ n : ℝ)⁻¹ : ℂ) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (ContinuousLinearEquiv.smulLeft (Units.mk0 ((2 * Real.pi)⁻¹ : ℝ) (by positivity))) (𝓕 m)

/-- Identification with the existing literal physical Fourier integral; no
Fourier normalization is suppressed (`app:ch_regular_base:eq:fixed-source-multiplication`). -/
theorem physicalSourceDensity_apply (m : 𝓢(Euclidean n, ℂ)) (v : Euclidean n) :
    physicalSourceDensity m v = (((2 * Real.pi) ^ n : ℝ)⁻¹ : ℂ) *
      Localization.physicalFourierIntegral volume m
        (InnerProductSpace.toDual ℝ (Euclidean n) v) := by
  rw [Localization.physicalFourierIntegral_eq_fourier]
  rfl

/-- An absolute Fourier moment, used for both halves of the same exact source
remainder (`app:ch_regular_base:eq:fixed-source-multiplication`). -/
def sourceMoment (h : 𝓢(Euclidean n, ℂ)) (k : ℕ) : ℝ :=
  ∫ v, ‖v‖ ^ k * ‖h v‖

/-- All moments of the fixed source density are finite; this includes zero
frequency (`app:ch_regular_base:eq:fixed-source-multiplication`). -/
theorem integrable_sourceMoment (h : 𝓢(Euclidean n, ℂ)) (k : ℕ) :
    Integrable (fun v ↦ ‖v‖ ^ k * ‖h v‖) :=
  h.integrable_pow_mul volume k

/-- Positivity needed when adding the near and far bounds in
`app:ch_regular_base:eq:fixed-source-multiplication`. -/
theorem sourceMoment_nonneg (h : 𝓢(Euclidean n, ℂ)) (k : ℕ) :
    0 ≤ sourceMoment h k :=
  integral_nonneg fun _ ↦ mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)

/-- Trading a far-region radius for a higher moment, with the *same* Schwartz
function, is the arbitrary-order tail argument after
`app:ch_regular_base:eq:fixed-source-multiplication`. -/
theorem sourceMoment_tail_le (h : 𝓢(Euclidean n, ℂ)) (k N : ℕ)
    {R : ℝ} (hR : 0 < R) :
    (∫ v in {v : Euclidean n | R ≤ ‖v‖}, ‖v‖ ^ k * ‖h v‖) ≤
      (R ^ N)⁻¹ * sourceMoment h (k + N) := by
  have hs : MeasurableSet {v : Euclidean n | R ≤ ‖v‖} :=
    measurableSet_le measurable_const measurable_norm
  calc
    _ ≤ ∫ v in {v : Euclidean n | R ≤ ‖v‖},
        (R ^ N)⁻¹ * (‖v‖ ^ (k + N) * ‖h v‖) := by
      apply setIntegral_mono_on (integrable_sourceMoment h k).integrableOn
        ((integrable_sourceMoment h (k + N)).const_mul _).integrableOn hs
      intro v hv
      have hp : R ^ N ≤ ‖v‖ ^ N := pow_le_pow_left₀ hR.le hv N
      have hinv : 1 ≤ (R ^ N)⁻¹ * ‖v‖ ^ N := by
        rw [inv_mul_eq_div]
        exact (le_div_iff₀ (pow_pos hR N)).mpr (by simpa using hp)
      calc
        _ ≤ ((R ^ N)⁻¹ * ‖v‖ ^ N) * (‖v‖ ^ k * ‖h v‖) :=
          le_mul_of_one_le_left (by positivity) hinv
        _ = _ := by rw [pow_add]; ring
    _ ≤ ∫ v, (R ^ N)⁻¹ * (‖v‖ ^ (k + N) * ‖h v‖) :=
      setIntegral_le_integral ((integrable_sourceMoment h (k + N)).const_mul _)
        (Filter.Eventually.of_forall fun _ ↦ by positivity)
    _ = _ := by rw [integral_const_mul]; rfl

end JanetCartan.FourierIntegral.SourceBounds
