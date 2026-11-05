module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.BesselSymbol
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.PrimitiveDiagonal

/-!
# The fixed-source Bessel commutator

For the image-normal paragraph in `app:ch_background:prop:bg-frame`, Step 1,
identify the literal Schwartz-test commutator and the source Taylor remainder
of `J χsrc²`. The estimate is pointwise frequency decay; mixed derivative bounds
and the passage through the other multiplier and first-order factors remain
obligations of the image-normal construction. Euclidean tests use Lebesgue
measure and the shared Fourier convention. No torus identification is asserted.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff
open JanetCartan.Pseudodifferential
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The literal source-square commutator on Schwartz tests is a full amplitude
with both physical positions retained (`app:ch_background:prop:bg-frame`,
Step 1). This identity makes no source-independent commutation assumption. -/
theorem imageBessel_commutator_eq_fullAmplitude (χ : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (u : 𝓢(E, ℂ)) (x : E) :
    fullAmplitudeOperator (fun x y ξ ↦ ((χ y)^2 - (χ x)^2) •
      (imageBesselSymbol ξ : ℂ)) u x =
      schwartzFrequencyMultiplier (fun ξ ↦ (imageBesselSymbol ξ : ℂ))
        (SchwartzMap.smulLeftCLM ℂ (fun y ↦ ((χ y)^2 : ℂ)) u) x -
      (χ x)^2 • schwartzFrequencyMultiplier (fun ξ ↦ (imageBesselSymbol ξ : ℂ)) u x := by
  have ht : χ.HasTemperateGrowth := hχc.hasTemperateGrowth hχ
  have hsq : (fun y ↦ ((χ y)^2 : ℂ)).HasTemperateGrowth := by fun_prop
  let v := SchwartzMap.smulLeftCLM ℂ (fun y ↦ ((χ y)^2 : ℂ)) u -
    ((χ x)^2 : ℂ) • u
  have hv (y : E) : v y = ((χ y)^2 - (χ x)^2) • u y := by
    simp only [v, sub_apply, smul_apply,
      SchwartzMap.smulLeftCLM_apply_apply hsq, smul_eq_mul, Complex.real_smul]
    push_cast
    ring
  have he : fullAmplitudeOperator (fun x y ξ ↦ ((χ y)^2 - (χ x)^2) •
      (imageBesselSymbol ξ : ℂ)) u x =
      fullAmplitudeOperator (fun _ _ ξ ↦ (imageBesselSymbol ξ : ℂ)) v x := by
    unfold fullAmplitudeOperator sourceAmplitudeTransform
    apply congrArg (fun f : E → ℂ ↦ 𝓕⁻ f x)
    funext ξ
    apply congrArg (fun f : E → ℂ ↦ 𝓕 f ξ)
    funext y
    rw [hv, smul_comm]
    simp only [smul_assoc]
  rw [he, fullAmplitudeOperator_sourceIndependent,
    ← schwartzFrequencyMultiplier_eq_sourceIndependentOperator _
      hasTemperateGrowth_complex_imageBesselSymbol]
  simp only [v, schwartzFrequencyMultiplier,
    ← FourierTransform.fourierCLM_apply (R := ℂ), ← FourierTransform.fourierInvCLM_apply (R := ℂ),
    map_sub, map_smul,
    sub_apply, smul_apply, Complex.real_smul, Complex.ofReal_pow, smul_eq_mul]

/-- The diagonal-reduction remainder for `J χsrc²` differentiates the actual
Bessel symbol once and keeps the full source Taylor coefficient
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem imageSourceSquare_remainder_eq (b : OrthonormalBasis (Fin d) ℝ E) (χ β : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (x y ξ : E) :
    diagonalRemainderAmplitude b
      (fun _ y ξ ↦ imageBesselSymbol ξ • ((χ y)^2 : ℂ)) β x y ξ =
    frequencyCutoffError b imageBesselSymbol
      (fun _ ↦ sourceTaylorCoefficient (fun y ↦ ((χ y)^2 : ℂ)) β x y) ξ := by
  have hc : ContDiff ℝ ∞ (fun p : E × E ↦ ((χ p.1)^2 : ℂ)) :=
    (Complex.ofRealCLM.contDiff.comp (hχ.comp contDiff_fst)).pow 2
  have hq := hasTemperateGrowth_imageBesselSymbol (d := d)
  have h := diagonalRemainderAmplitude_frequency_smul b
    (fun _ y _ ↦ ((χ y)^2 : ℂ)) β imageBesselSymbol x y ξ hc
      (hq.1.differentiable (by simp) ξ)
  have hconst : fullTaylorCoefficient (fun _ y _ : E ↦ ((χ y)^2 : ℂ)) β x y =
      fun _ ↦ sourceTaylorCoefficient (fun y ↦ ((χ y)^2 : ℂ)) β x y := rfl
  have hz : diagonalRemainderAmplitude b (fun _ y _ : E ↦ ((χ y)^2 : ℂ)) β x y ξ = 0 := by
    rw [diagonalRemainderAmplitude, hconst]
    simp only [normalizedFrequencyDivergence, frequencyDivergence, fderiv_const_apply,
      zero_apply, Finset.sum_const_zero, smul_zero]
  rw [hz, smul_zero, zero_add, hconst] at h
  exact h

/-- A primitive derivative bound on the fixed source square bounds its
Taylor coefficient (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem norm_sourceSquareTaylorCoefficient_le (χ β : E → ℝ) (x y : E) (C : ℝ)
    (hC : ∀ z, ‖fderiv ℝ (fun y ↦ ((χ y)^2 : ℂ)) z‖ ≤ C) :
    ‖sourceTaylorCoefficient (fun y ↦ ((χ y)^2 : ℂ)) β x y‖ ≤ |β y| * C := by
  unfold sourceTaylorCoefficient
  rw [norm_smul, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact (intervalIntegral.norm_integral_le_of_norm_le_const
    (fun t _ ↦ hC (x + t • (y - x)))).trans_eq (by simp)

/-- The actual source-square diagonal remainder has pointwise physical
frequency decay of order minus two, derived from the Bessel symbol and a
primitive first derivative of the fixed cutoff. This is the zeroth seminorm,
not the complete symbol-class assertion (`app:ch_background:prop:bg-frame`,
Step 1). -/
theorem norm_imageSourceSquare_remainder_le
    (b : OrthonormalBasis (Fin d) ℝ E) (χ β : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (C : ℝ)
    (hC : ∀ z, ‖fderiv ℝ (fun y ↦ ((χ y)^2 : ℂ)) z‖ ≤ C) (x y ξ : E) :
    ‖diagonalRemainderAmplitude b
      (fun _ y ξ ↦ imageBesselSymbol ξ • ((χ y)^2 : ℂ)) β x y ξ‖ ≤
      (‖(2 * Real.pi * Complex.I)⁻¹‖ * d * (2 * Real.pi) * (|β y| * C)) *
        (1 + ‖(2 * Real.pi) • ξ‖ ^ 2)⁻¹ := by
  rw [imageSourceSquare_remainder_eq b χ β hχ]
  apply (norm_frequencyCutoffError_le b imageBesselSymbol _ ξ).trans
  have hC₀ : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hq := norm_fderiv_imageBesselSymbol_le ξ
  have ht := norm_sourceSquareTaylorCoefficient_le χ β x y C hC
  calc
    _ ≤ ‖(2 * Real.pi * Complex.I)⁻¹‖ * Fintype.card (Fin d) *
        ((2 * Real.pi) * (1 + ‖(2 * Real.pi) • ξ‖ ^ 2)⁻¹) * (|β y| * C) := by
      gcongr
    _ = _ := by simp only [Fintype.card_fin]; ring

/-- Every fixed smooth compact cutoff supplies the primitive derivative
constant in `norm_imageSourceSquare_remainder_le`. No decay estimate for an
unknown remainder is assumed (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem exists_sourceSquare_derivative_bound (χ : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖fderiv ℝ (fun y ↦ ((χ y)^2 : ℂ)) z‖ ≤ C := by
  have hs : ContDiff ℝ ∞ (fun y ↦ ((χ y)^2 : ℂ)) :=
    (Complex.ofRealCLM.contDiff.comp hχ).pow 2
  have hc : HasCompactSupport (fun y ↦ ((χ y)^2 : ℂ)) := by
    apply hχc.comp_left (g := fun t : ℝ ↦ (t : ℂ)^2)
    simp
  obtain ⟨C, hC⟩ := (hc.fderiv ℝ).exists_bound_of_continuous
    (hs.continuous_fderiv (by simp))
  exact ⟨C, (norm_nonneg _).trans (hC 0), hC⟩

end JanetCartan.ContinuumNormalReduction.ImageNormal
