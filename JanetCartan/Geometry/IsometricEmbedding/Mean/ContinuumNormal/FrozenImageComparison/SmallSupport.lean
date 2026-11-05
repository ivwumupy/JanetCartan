module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.Comparison
public import JanetCartan.Analysis.Operator.Retarded.L2

/-!
# Absorption of the fixed image comparison error

For `paper-v2.tex`, `app:ch_background:prop:bg-frame`, the actual physical
support bounds the L¹-squared error by its Lebesgue volume times the L² norm
squared. Only the inner radius shrinks: the two outer masks, frozen arrays,
and comparison constant have already been fixed. The resulting error can be
made arbitrarily small, including for the literal inner-cutoff localization
used by the parent continuum-normal construction. Dimension zero is handled
by the zero output space, without a spurious small-volume assertion.
-/

@[expose] public noncomputable section

open MeasureTheory Metric
open JanetCartan.ContinuumRow JanetCartan.PeriodicLocalL2

namespace JanetCartan.ContinuumNormal.FrozenImageComparison

variable {n : ℕ} {r R : ℝ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Cauchy–Schwarz for the actual cell zero extension on its inner physical
ball (`app:ch_background:prop:bg-frame`). This applies the checked finite-measure
Cauchy–Schwarz estimate and the proved Haar-to-Lebesgue norm identity.
It supplies the absorption step below. -/
theorem sq_integral_norm_zeroExtension_le_ball_volume
    (hR : 0 < R) (hcell : 4 * R < 1 / 2) (hrR : r ≤ R)
    (f : OutputL2 n)
    (hf : ∀ᵐ z ∂volume, z ∉ torusQuotient '' ball (0 : E) r → f z = 0) :
    (∫ x, ‖toEuclidean (𝕜 := ℝ) f x‖) ^ 2 ≤
      (volume (ball (0 : E) r)).toReal * ‖f‖ ^ 2 := by
  let u : EuclideanL2 n E := toEuclidean (𝕜 := ℝ) f
  let s : Set E := ball 0 r
  have hu := toEuclidean_supported_innerBall hR hcell hrR f hf
  let : IsFiniteMeasure (volume.restrict s) := ⟨by
    simpa only [Measure.restrict_apply_univ] using (measure_ball_lt_top (μ := volume)
      (x := (0 : E)) (r := r))⟩
  have heq (p : ℕ) (hp : p ≠ 0) : (∫ x in s, ‖u x‖ ^ p) = ∫ x, ‖u x‖ ^ p := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [hu] with x hx hxs
    rw [show u x = 0 from hx hxs]
    simp [hp]
  have hl1 : (∫ x in s, ‖u x‖) = ∫ x, ‖u x‖ := by simpa using heq 1 (by decide)
  have h := Retarded.integral_norm_sq_le_measure_mul (volume.restrict s) u
    ((Lp.memLp u).restrict s)
  have hl2 : (∫ x, ‖u x‖ ^ 2) = ‖u‖ ^ 2 := by
    simpa only [real_inner_self_eq_norm_sq] using (L2.inner_def (𝕜 := ℝ) u u).symm
  rw [hl1, heq 2 (by decide), hl2] at h
  simpa only [Measure.real, Measure.restrict_apply_univ, u, s, norm_zeroExtension] using h

/-- Shrinking only the inner physical support absorbs the proved image error
into any prescribed L² allowance (`app:ch_background:prop:bg-frame`). The
radius works uniformly over all smaller positive radii, supported L² inputs,
and coefficient extensions agreeing with the same constants on the fixed
measurement plateau. No positivity hypothesis on the image symbol is used. -/
theorem exists_small_support_imageChannel_energyDifference_le
    (hR : 0 < R) (hcell : 4 * R < 1 / 2)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ R ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∀ c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ),
        (∀ k z, FixedCutoffs.periodic hR hcell 1 z = 1 →
          c k z = constantImageCoefficients A k z) →
        ∀ f : OutputL2 n,
          (∀ᵐ z ∂volume, z ∉ torusQuotient '' ball (0 : E) r → f z = 0) →
          |‖(imageChannel c (FixedCutoffs.periodic hR hcell 1)
              (FixedCutoffs.periodic hR hcell 2)).adjoint f‖ ^ 2 -
            fourierEnergy A (toEuclidean (𝕜 := ℝ) f)| ≤ ε * ‖f‖ ^ 2 := by
  by_cases hn : n = 0
  · subst n
    refine ⟨R, hR, le_rfl, fun _ _ _ _ _ f _ ↦ ?_⟩
    have hf : f = 0 := by
      apply Lp.ext
      exact Filter.Eventually.of_forall fun _ ↦ Subsingleton.elim _ _
    simp [hf, ← norm_uncutRealChannel_adjoint_sq_eq_fourierEnergy]
  obtain ⟨C, hC, hbound⟩ := exists_imageChannel_energyDifference_le_l1_sq hR hcell A
  let v := (volume (ball (0 : E) 1)).toReal
  have hv : 0 ≤ v := ENNReal.toReal_nonneg
  let r₀ := min R (min 1 (ε / ((C + 1) * (v + 1))))
  have hr₀ : 0 < r₀ := lt_min hR (lt_min zero_lt_one (by positivity))
  refine ⟨r₀, hr₀, min_le_left _ _, fun r hr hrr c hc f hf ↦ ?_⟩
  have hrR : r ≤ R := hrr.trans (min_le_left _ _)
  have hr1 : r ≤ 1 := hrr.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrbound : r ≤ ε / ((C + 1) * (v + 1)) :=
    hrr.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hvol : (volume (ball (0 : E) r)).toReal = r ^ n * v := by
    rw [Measure.addHaar_ball_of_pos volume (0 : E) hr]
    simp [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr.le _),
      finrank_euclideanSpace, v]
  have hpow : r ^ n ≤ r := by
    simpa using pow_le_pow_of_le_one hr.le hr1 (Nat.pos_of_ne_zero hn)
  have hsmall : C * (volume (ball (0 : E) r)).toReal ≤ ε := by
    rw [hvol]
    have hscaled := (le_div_iff₀ (by positivity : 0 < (C + 1) * (v + 1))).mp hrbound
    have hmono : C * (r ^ n * v) ≤ C * (r * v) := by gcongr
    have hprod : C * v ≤ (C + 1) * (v + 1) := by nlinarith
    have := mul_le_mul_of_nonneg_right hprod hr.le
    nlinarith
  calc
    _ ≤ C * (∫ x, ‖toEuclidean (𝕜 := ℝ) f x‖) ^ 2 := hbound r hrR c hc f hf
    _ ≤ C * ((volume (ball (0 : E) r)).toReal * ‖f‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (sq_integral_norm_zeroExtension_le_ball_volume hR hcell hrR f hf) hC
    _ = (C * (volume (ball (0 : E) r)).toReal) * ‖f‖ ^ 2 := by ring
    _ ≤ ε * ‖f‖ ^ 2 := mul_le_mul_of_nonneg_right hsmall (sq_nonneg _)

/-- The actual inner-cutoff localization has an arbitrarily small frozen
image comparison error (`app:ch_background:prop:bg-frame`). Its support is
proved by `innerCutoff_supported`, rather than assumed of the localized field.
Both source and measurement masks still use the original outer radius `R`;
the parent may use this inner cutoff for the original exterior channel. -/
theorem exists_innerCutoff_imageChannel_energyDifference_le
    (hR : 0 < R) (hcell : 4 * R < 1 / 2)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (r : ℝ) (hr : 0 < r) (hrcell : r < 1 / 2), r ≤ R ∧
      ∀ c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ),
        (∀ k z, FixedCutoffs.periodic hR hcell 1 z = 1 →
          c k z = constantImageCoefficients A k z) →
        ∀ f : OutputL2 n,
          let g := cutoffMultiplier (innerCutoff hr hrcell) f
          |‖(imageChannel c (FixedCutoffs.periodic hR hcell 1)
              (FixedCutoffs.periodic hR hcell 2)).adjoint g‖ ^ 2 -
            fourierEnergy A (toEuclidean (𝕜 := ℝ) g)| ≤ ε * ‖g‖ ^ 2 := by
  obtain ⟨r, hr, hrR, hbound⟩ :=
    exists_small_support_imageChannel_energyDifference_le hR hcell A hε
  have hrcell : r < 1 / 2 := by linarith
  refine ⟨r, hr, hrcell, hrR, fun c hc f ↦ ?_⟩
  exact hbound r hr le_rfl c hc _ (innerCutoff_supported hr hrcell f)

end JanetCartan.ContinuumNormal.FrozenImageComparison
