module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Image
public import JanetCartan.Analysis.Operator.NormalPerturbation.Basic

/-!
# Coefficient perturbations of the actual image normal

For `paper-v2.tex`, `app:ch_background:prop:bg-frame`, the image channel is
the existing periodic operator `χmeas P J χsrc`, including the source mask
and all zeroth-order coefficients. Its difference is constructed by subtracting
the coefficient arrays. Consequently the normal difference is controlled by
coefficient sup norms; no continuity or difference bound for an operator is
assumed. The carrier normals with changing phases require a different argument.
-/

@[expose] public noncomputable section

namespace JanetCartan.ContinuumNormal

open ContinuumRow

variable {n : ℕ}

/-- Coefficient subtraction commutes with the actual L² multiplier
(`app:ch_background:defn:bg-row`). -/
theorem cutoffMultiplier_sub (a b : C(Torus n, ℝ)) :
    cutoffMultiplier (a - b) = cutoffMultiplier a - cutoffMultiplier b := by
  unfold cutoffMultiplier coefficientMultiplier
  rw [map_sub, map_sub]

/-- The principal and connection arrays both enter linearly in the weak
reduced operator (`app:ch_waves:eq:reduced-symbol`). -/
theorem reducedWeakOperator_sub
    (c d : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ)) :
    reducedWeakOperator (c - d) = reducedWeakOperator c - reducedWeakOperator d := by
  simp only [reducedWeakOperator, reducedCoefficientMultiplier, Pi.sub_apply,
    cutoffMultiplier_sub, ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp,
    Finset.sum_sub_distrib]
  abel

/-- Exact subtraction for the same fixed source and measurement masks
(`paper-v2.tex`, `app:ch_background:prop:bg-frame`). -/
theorem imageChannel_sub
    (c d : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc : C(Torus n, ℝ)) :
    imageChannel (c - d) χmeas χsrc =
      imageChannel c χmeas χsrc - imageChannel d χmeas χsrc := by
  simp only [imageChannel, reducedWeakOperator_sub, ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.sub_comp]

/-- The image-channel difference is bounded by the actual coefficient
differences (`paper-v2.tex`, `app:ch_background:prop:bg-frame`). -/
theorem norm_imageChannel_sub_le
    (c d : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc : C(Torus n, ℝ)) :
    ‖imageChannel c χmeas χsrc - imageChannel d χmeas χsrc‖ ≤
      ‖χmeas‖ * reducedCoefficientBound (c - d) * ‖χsrc‖ := by
  rw [← imageChannel_sub]
  exact imageChannel_norm_le _ _ _

/-- Full coefficient sup norms, with explicit dimension factors, control the
image difference (`paper-v2.tex`, `app:ch_background:prop:bg-frame`). -/
theorem norm_imageChannel_sub_le_of_coefficient_bounds
    (c d : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc : C(Torus n, ℝ)) {ε₁ ε₀ : ℝ}
    (hε₁ : 0 ≤ ε₁) (hε₀ : 0 ≤ ε₀)
    (hfirst : ∀ a i k x, |c (.inl (a, i, k)) x - d (.inl (a, i, k)) x| ≤ ε₁)
    (hzero : ∀ i k x, |c (.inr (i, k)) x - d (.inr (i, k)) x| ≤ ε₀) :
    ‖imageChannel c χmeas χsrc - imageChannel d χmeas χsrc‖ ≤
      ‖χmeas‖ * ((n : ℝ) ^ 3 * ε₁ + (n : ℝ) ^ 2 * ε₀) * ‖χsrc‖ := by
  rw [← imageChannel_sub]
  exact imageChannel_norm_le_of_bounds (c - d) χmeas χsrc hε₁ hε₀ hfirst hzero

/-- A quantitative comparison of the literal image normals, derived from
their coefficient formulas (`paper-v2.tex`, `app:ch_background:prop:bg-frame`).
Both source-mask/Bessel factors are retained by Hilbert adjunction. -/
theorem norm_imageNormal_sub_le
    (c d : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc : C(Torus n, ℝ)) :
    ‖NormalPerturbation.normal (imageChannel c χmeas χsrc) -
        NormalPerturbation.normal (imageChannel d χmeas χsrc)‖ ≤
      2 * (‖χmeas‖ * reducedCoefficientBound d * ‖χsrc‖) *
        (‖χmeas‖ * reducedCoefficientBound (c - d) * ‖χsrc‖) +
      (‖χmeas‖ * reducedCoefficientBound (c - d) * ‖χsrc‖) ^ 2 := by
  have h := NormalPerturbation.norm_normal_add_sub_le_of_bounds
    (imageChannel d χmeas χsrc) (imageChannel (c - d) χmeas χsrc)
    (imageChannel_norm_le d χmeas χsrc) (imageChannel_norm_le (c - d) χmeas χsrc)
  simpa only [imageChannel_sub, add_sub_cancel] using h

/-- The literal image channel is Lipschitz in the finite array of coefficient
sup norms (`paper-v2.tex`, `app:ch_background:prop:bg-frame`). -/
theorem lipschitzWith_imageChannel (χmeas χsrc : C(Torus n, ℝ)) :
    LipschitzWith (Real.toNNReal (‖χmeas‖ * ((n : ℝ) ^ 3 + (n : ℝ) ^ 2) * ‖χsrc‖))
      (fun c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ) ↦
        imageChannel c χmeas χsrc) := by
  apply LipschitzWith.of_dist_le'
  intro c d
  rw [dist_eq_norm, dist_eq_norm]
  have hentry (j : GeometricProfile.ReducedCoefficientIndex n) (x : Torus n) :
      |c j x - d j x| ≤ ‖c - d‖ := by
    exact ((c j - d j).norm_coe_le_norm x).trans (norm_le_pi_norm (c - d) j)
  have h := norm_imageChannel_sub_le_of_coefficient_bounds c d χmeas χsrc
    (norm_nonneg (c - d)) (norm_nonneg (c - d))
    (fun a i k x ↦ hentry (.inl (a, i, k)) x)
    (fun i k x ↦ hentry (.inr (i, k)) x)
  convert h using 1
  ring

/-- Operator-norm continuity of the actual image normal follows from its
coefficient formula and the continuity of Hilbert adjunction
(`paper-v2.tex`, `app:ch_background:prop:bg-frame`). -/
theorem continuous_imageNormal (χmeas χsrc : C(Torus n, ℝ)) :
    Continuous (fun c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ) ↦
      NormalPerturbation.normal (imageChannel c χmeas χsrc)) := by
  have hc := (lipschitzWith_imageChannel χmeas χsrc).continuous
  exact hc.clm_comp (ContinuousLinearMap.adjoint.continuous.comp hc)

/-- A positive coefficient tolerance for a prescribed image-normal tolerance,
derived from the actual operator (`paper-v2.tex`, `app:ch_background:prop:bg-frame`). -/
theorem exists_imageNormal_coefficient_neighborhood
    (d : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc : C(Torus n, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ),
      ‖c - d‖ < η →
      ‖NormalPerturbation.normal (imageChannel c χmeas χsrc) -
        NormalPerturbation.normal (imageChannel d χmeas χsrc)‖ < ε := by
  have h := (continuous_imageNormal χmeas χsrc).continuousAt (x := d)
  obtain ⟨η, hη, hclose⟩ := (Metric.continuousAt_iff
    (f := fun c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ) ↦
      NormalPerturbation.normal (imageChannel c χmeas χsrc)) (a := d)).mp h ε hε
  refine ⟨η, hη, fun c hc ↦ ?_⟩
  simpa only [dist_eq_norm] using hclose (by simpa only [dist_eq_norm] using hc)

end JanetCartan.ContinuumNormal
