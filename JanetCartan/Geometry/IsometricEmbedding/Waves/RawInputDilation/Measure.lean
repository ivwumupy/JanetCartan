module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputRealization.Spaces
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Restricted Lebesgue change of variables for raw annular inputs

The substitution preceding `app:ch_waves:eq:sampling-prefix-normal` uses the
literal initial annulus of `app:ch_waves:thm:individual`, in dimension `n - 1`.
These identities supply the measure calculation for `annularDilation`.
-/

@[expose] public noncomputable section
open MeasureTheory
namespace JanetCartan.RawInputDilation
open RawInputRealization
variable {n : ℕ} {K : ℝ}

/-- The exact annulus pulls back under positive dilation, including both boundary
spheres (`app:ch_waves:thm:sampling`). -/
theorem preimage_annulus_smul (hK : 0 < K) (R : ℝ) :
    (fun θ : Euclidean (n - 1) ↦ K • θ) ⁻¹' annulus n (K * R) = annulus n R := by
  ext θ
  simp only [annulus, Set.mem_preimage, Set.mem_sdiff, Metric.mem_closedBall,
    Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hK,
    not_lt]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨(mul_le_mul_iff_right₀ hK).mp h₁,
      (mul_le_mul_iff_right₀ hK).mp (by nlinarith)⟩
  · rintro ⟨h₁, h₂⟩
    constructor <;> nlinarith

/-- Pushforward of the restricted Lebesgue measure, with its actual Jacobian
(`app:ch_waves:thm:sampling`). -/
theorem map_annularMeasure_smul (hK : 0 < K) (R : ℝ) :
    (annularMeasure n R).map (fun θ ↦ K • θ) =
      ENNReal.ofReal ((K ^ (n - 1))⁻¹) • annularMeasure n (K * R) := by
  unfold annularMeasure
  rw [← preimage_annulus_smul hK R, ← Measure.restrict_map (by fun_prop)
    (measurableSet_annulus n (K * R)), Measure.map_addHaar_smul volume hK.ne']
  simp only [Euclidean, finrank_euclideanSpace_fin,
    abs_of_pos (inv_pos.mpr (pow_pos hK _)), Measure.restrict_smul]

/-- Exact restricted-integral substitution, also valid for a nonintegrable
Bochner integrand (`app:ch_waves:thm:sampling`). -/
theorem integral_annular_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hK : 0 < K) (R : ℝ) (f : Euclidean (n - 1) → F) :
    (∫ θ, f (K • θ) ∂annularMeasure n R) =
      (K ^ (n - 1))⁻¹ • ∫ η, f η ∂annularMeasure n (K * R) := by
  let e := (Homeomorph.smul (Units.mk0 K hK.ne') :
    Euclidean (n - 1) ≃ₜ Euclidean (n - 1)).toMeasurableEquiv
  have he : ⇑e = (fun θ : Euclidean (n - 1) ↦ K • θ) := rfl
  change (∫ θ, f (e θ) ∂annularMeasure n R) = _
  rw [← integral_map_equiv e f, he, map_annularMeasure_smul hK R,
    integral_smul_measure, ENNReal.toReal_ofReal (by positivity)]

/-- Null sets pull back under the annular dilation
(`app:ch_waves:thm:sampling`), used to descend to `L²` classes. -/
theorem ae_annular_smul (hK : 0 < K) (R : ℝ)
    {p : Euclidean (n - 1) → Prop} (hp : ∀ᵐ η ∂annularMeasure n (K * R), p η) :
    ∀ᵐ θ ∂annularMeasure n R, p (K • θ) := by
  apply ae_of_ae_map (by fun_prop : AEMeasurable (fun θ : Euclidean (n - 1) ↦ K • θ) (annularMeasure n R))
  rw [map_annularMeasure_smul hK R]
  exact Measure.ae_smul_measure hp _

end JanetCartan.RawInputDilation
