module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputRealization.Estimates

/-!
# Linearity of Euclidean raw synthesis

`L²` representatives are linear only almost everywhere. The densities below have
that exact scope; the actual inverse Fourier fields are pointwise linear.
These are the raw maps used in `app:ch_waves:thm:individual`.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.RawInputRealization

variable {n : ℕ} {R : ℝ}

/-- Annular density is additive almost everywhere (`app:ch_waves:thm:individual`). -/
theorem channelDensity_add (β : Euclidean (n - 1) → ℂ) (v w : AnnularL2 n R) :
    channelDensity β (v + w) =ᵐ[volume] channelDensity β v + channelDensity β w := by
  have h : (fun η ↦ (Real.sqrt ‖η‖ : ℂ) * β η * (v + w) η) =ᵐ[annularMeasure n R]
      (fun η ↦ (Real.sqrt ‖η‖ : ℂ) * β η * v η + (Real.sqrt ‖η‖ : ℂ) * β η * w η) := by
    filter_upwards [Lp.coeFn_add v w] with η hη
    simp only [hη, Pi.add_apply, mul_add]
  simpa only [channelDensity, Set.indicator_add, Pi.add_def] using
    (ae_eq_restrict_iff_indicator_ae_eq (measurableSet_annulus n R)).mp h

/-- Real homogeneity retains both quadratures (`app:ch_waves:thm:individual`). -/
theorem channelDensity_smul (β : Euclidean (n - 1) → ℂ) (c : ℝ) (v : AnnularL2 n R) :
    channelDensity β (c • v) =ᵐ[volume] c • channelDensity β v := by
  have h : (fun η ↦ (Real.sqrt ‖η‖ : ℂ) * β η * (c • v) η) =ᵐ[annularMeasure n R]
      (fun η ↦ c • ((Real.sqrt ‖η‖ : ℂ) * β η * v η)) := by
    filter_upwards [Lp.coeFn_smul c v] with η hη
    simp only [hη, Pi.smul_apply, mul_smul_comm]
  simpa only [channelDensity, Set.indicator_smul, Pi.smul_def] using
    (ae_eq_restrict_iff_indicator_ae_eq (measurableSet_annulus n R)).mp h

variable {ι : Type*} [Fintype ι] {radius : ι → ℝ}

/-- Additivity of the actual density, with its necessary almost-everywhere scope
(`app:ch_waves:thm:individual`). -/
theorem density_add (β : ι → Euclidean (n - 1) → ℂ) (v w : Input n radius) :
    density β (v + w) =ᵐ[volume] density β v + density β w := by
  have h := Filter.eventually_all.mpr (fun i ↦ channelDensity_add (β i) (v i) (w i))
  filter_upwards [h] with η hη
  simp only [density, PiLp.add_apply, Pi.add_apply]
  simp_rw [hη, Pi.add_apply, Finset.sum_add_distrib]

/-- Real homogeneity of the density (`app:ch_waves:thm:individual`). -/
theorem density_smul (β : ι → Euclidean (n - 1) → ℂ) (c : ℝ) (v : Input n radius) :
    density β (c • v) =ᵐ[volume] c • density β v := by
  have h := Filter.eventually_all.mpr (fun i ↦ channelDensity_smul (β i) c (v i))
  filter_upwards [h] with η hη
  simp only [density, PiLp.smul_apply, Pi.smul_apply]
  simp_rw [hη, Pi.smul_apply, Finset.smul_sum]

/-- Pointwise additivity of the smooth field, deduced from actual integrability
(`app:ch_waves:thm:individual`). -/
theorem field_add {β : ι → Euclidean (n - 1) → ℂ}
    (hβ : ∀ i, Measurable (β i)) {M : ℝ} (hM : ∀ i η, ‖β i η‖ ≤ M)
    (v w : Input n radius) : field β (v + w) = field β v + field β w := by
  unfold field
  rw [VectorFourier.fourierIntegral_congr_ae _ _ _ (density_add β v w)]
  exact VectorFourier.fourierIntegral_add Real.continuous_fourierChar
    (radianPairing n).continuous₂ (integrable_density hβ hM v) (integrable_density hβ hM w)

/-- Pointwise real homogeneity of the field (`app:ch_waves:thm:individual`). -/
theorem field_smul (β : ι → Euclidean (n - 1) → ℂ) (c : ℝ) (v : Input n radius) :
    field β (c • v) = c • field β v := by
  unfold field
  rw [VectorFourier.fourierIntegral_congr_ae _ _ _ (density_smul β c v)]
  funext x
  simp only [VectorFourier.fourierIntegral, Pi.smul_apply, smul_comm _ c, integral_smul]

/-- The genuine real linear raw synthesis operator (`app:ch_waves:thm:individual`). -/
def synthesisLinearMap {β : ι → Euclidean (n - 1) → ℂ}
    (hβ : ∀ i, Measurable (β i)) {M : ℝ} (hM : ∀ i η, ‖β i η‖ ≤ M) :
    Input n radius →ₗ[ℝ] (Euclidean (n - 1) → ℂ) where
  toFun := field β
  map_add' := field_add hβ hM
  map_smul' := field_smul β

end JanetCartan.RawInputRealization
