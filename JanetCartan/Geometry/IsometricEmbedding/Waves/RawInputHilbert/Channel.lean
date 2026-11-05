module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputHilbert.Multiplication

/-!
# One annular complex synthesis channel

The literal half-derivative density of `app:ch_waves:thm:individual` is realized
in Lebesgue L². Measurability and bounds of the actual masks remain inputs
from the raw-input producer; no synthesis or adjoint estimate is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
namespace JanetCartan.RawInputHilbert

open RawInputRealization



/-- Full Lebesgue output of the density map in `app:ch_waves:thm:individual`. -/
abbrev Output (n : ℕ) := Lp (α := Euclidean (n - 1)) ℂ 2 volume

variable {n : ℕ} {R M : ℝ} {β : Euclidean (n - 1) → ℂ}

/-- Annular zero extension with the shared named measure
(`app:ch_waves:thm:individual`). -/
def annularExtension : AnnularL2 n R →ₗᵢ[ℂ] Output n :=
  zeroExtension (measurableSet_annulus n R)

/-- Annular restriction with the shared named measure
(`app:ch_waves:eq:sampling-prefix-normal`). -/
def annularRestriction : Output n →L[ℂ] AnnularL2 n R := restriction (annulus n R)

/-- The annular extension and restriction are adjoints
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem adjoint_annularExtension :
    (annularExtension (n := n) (R := R)).toContinuousLinearMap.adjoint =
      annularRestriction := adjoint_zeroExtension (measurableSet_annulus n R)

/-- The actual half-derivative coefficient (`app:ch_waves:eq:B-bounds`). -/
def halfCoefficient (β : Euclidean (n - 1) → ℂ) (η : Euclidean (n - 1)) : ℂ :=
  (Real.sqrt ‖η‖ : ℂ) * β η

/-- Measurability of the half-derivative coefficient on the annulus
(`app:ch_waves:eq:B-bounds`). -/
theorem halfCoefficient_measurable
    (hβ : AEStronglyMeasurable β (annularMeasure n R)) :
    AEStronglyMeasurable (halfCoefficient β) (annularMeasure n R) := by
  exact (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp continuous_norm)).aestronglyMeasurable.mul hβ

/-- The pointwise annular estimate producing the channel norm bound
(`app:ch_waves:eq:B-bounds`). -/
theorem halfCoefficient_bound (_hM : 0 ≤ M)
    (hb : ∀ᵐ η ∂annularMeasure n R, ‖β η‖ ≤ M) :
    ∀ᵐ η ∂annularMeasure n R, ‖halfCoefficient β η‖ ≤ Real.sqrt R * M := by
  filter_upwards [hb, ae_restrict_mem (measurableSet_annulus n R)] with η hβ hη
  have hηR : ‖η‖ ≤ R := by simpa using hη.1
  simp only [halfCoefficient, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul (Real.sqrt_le_sqrt hηR) hβ (norm_nonneg _) (Real.sqrt_nonneg _)

/-- One genuine complex annular density channel, extended by zero
(`app:ch_waves:thm:individual`). -/
def channel (hβ : AEStronglyMeasurable β (annularMeasure n R))
    (hM : 0 ≤ M) (hb : ∀ᵐ η ∂annularMeasure n R, ‖β η‖ ≤ M) :
    AnnularL2 n R →L[ℂ] Output n :=
  annularExtension.toContinuousLinearMap.comp
    (boundedMultiplier (halfCoefficient_measurable hβ) (halfCoefficient_bound hM hb))

/-- The constructed channel agrees with the shared literal density
(`app:ch_waves:thm:individual`). -/
theorem channel_coeFn (hβ : AEStronglyMeasurable β (annularMeasure n R))
    (hM : 0 ≤ M) (hb : ∀ᵐ η ∂annularMeasure n R, ‖β η‖ ≤ M)
    (v : AnnularL2 n R) : channel hβ hM hb v =ᵐ[volume] channelDensity β v := by
  have hm := (ae_eq_restrict_iff_indicator_ae_eq (measurableSet_annulus n R)).mp
    (boundedMultiplier_coeFn (halfCoefficient_measurable hβ) (halfCoefficient_bound hM hb) v)
  exact (zeroExtension_coeFn (measurableSet_annulus n R) _).trans hm

/-- Actual channel operator estimate, with no scale-count constant
(`app:ch_waves:eq:B-bounds`). -/
theorem norm_channel_le (hβ : AEStronglyMeasurable β (annularMeasure n R))
    (hM : 0 ≤ M) (hb : ∀ᵐ η ∂annularMeasure n R, ‖β η‖ ≤ M) :
    ‖channel hβ hM hb‖ ≤ Real.sqrt R * M := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Real.sqrt_nonneg _) hM)
  intro v
  change ‖annularExtension
    (boundedMultiplier (halfCoefficient_measurable hβ) (halfCoefficient_bound hM hb) v)‖ ≤ _
  rw [LinearIsometry.norm_map]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right
      (norm_boundedMultiplier_le _ (mul_nonneg (Real.sqrt_nonneg _) hM) _) (norm_nonneg _))

/-- Exact annular adjoint channel: conjugated half-derivative coefficient
following restriction (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem adjoint_channel (hβ : AEStronglyMeasurable β (annularMeasure n R))
    (hM : 0 ≤ M) (hb : ∀ᵐ η ∂annularMeasure n R, ‖β η‖ ≤ M) :
    (channel hβ hM hb).adjoint =
      (boundedMultiplier (halfCoefficient_measurable hβ).star
        (conj_bound (halfCoefficient_bound hM hb))).comp annularRestriction := by
  unfold channel
  rw [ContinuousLinearMap.adjoint_comp, adjoint_annularExtension, adjoint_boundedMultiplier]

/-- Literal adjoint formula preserving the imaginary quadrature
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem adjoint_channel_coeFn (hβ : AEStronglyMeasurable β (annularMeasure n R))
    (hM : 0 ≤ M) (hb : ∀ᵐ η ∂annularMeasure n R, ‖β η‖ ≤ M) (f : Output n) :
    (channel hβ hM hb).adjoint f =ᵐ[annularMeasure n R]
      fun η ↦ (Real.sqrt ‖η‖ : ℂ) * starRingEnd ℂ (β η) * f η := by
  rw [adjoint_channel]
  filter_upwards [boundedMultiplier_coeFn (halfCoefficient_measurable hβ).star
    (conj_bound (halfCoefficient_bound hM hb)) (annularRestriction f),
    (show annularRestriction f =ᵐ[annularMeasure n R] f from restriction_coeFn (annulus n R) f)] with η h₁ h₂
  simpa [halfCoefficient, h₂, ContinuousLinearMap.comp_apply] using h₁

end JanetCartan.RawInputHilbert
