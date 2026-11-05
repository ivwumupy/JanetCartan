module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.PhysicalJets
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.TestAction
/-!
# The actual source-square commutator after diagonal reduction

For `app:ch_background:prop:bg-frame`, Step 1, identify the Bessel commutator
with the explicit two-position diagonal remainder on compact Schwartz tests.
All four convergence conditions of the primitive unregularized reduction are
proved here from the actual multiplier and smooth compact source profiles.
The primitive theorem accounts for the frequency-cutoff defect in the limit.

The only analytic inputs are the fixed smooth compact cutoffs and their
plateau relation. The source mask remains inside the literal multiplier.
This is a Euclidean Lebesgue test identity; no equality with the periodic
Bessel kernel is asserted. Composition with the remaining normal factors
and the Euclidean/torus comparison belong to the parent construction.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff FourierTransform SchwartzMap
open JanetCartan.Pseudodifferential
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem integrable_sourceTransform_fixed_profile
    {F G : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (L : E → F →L[ℝ] G) (K : ℝ) (hK : ∀ ξ, ‖L ξ‖ ≤ K)
    (g : E → F) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hc : Continuous (fun p : E × E ↦ L p.1 (g p.2)))
    (u : E → ℂ) (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) (x : E) :
    Integrable (sourceAmplitudeTransform (fun _ y ξ ↦ L ξ (g y)) u x) := by
  have hb (j : ℕ) := (hgc.iteratedFDeriv j).exists_bound_of_continuous
    (hg.continuous_iteratedFDeriv (by simp))
  choose M hM using hb
  apply integrable_sourceAmplitudeTransform_of_sourceSymbolBounds _ u x 0
    hc
    (hu.of_le (by simp)) huc
    (fun ξ ↦ ((L ξ).contDiff.comp hg).of_le (by simp)) (fun j ↦ K * M j)
  intro j _ y ξ
  simp only [pow_zero, mul_one]
  exact ((L ξ).norm_iteratedFDeriv_comp_left hg.contDiffAt (by simp)).trans
    (mul_le_mul (hK ξ) (hM j y) (norm_nonneg _) ((norm_nonneg _).trans (hK ξ)))

private theorem norm_imageBesselSymbol_le_one (ξ : E) : ‖imageBesselSymbol ξ‖ ≤ 1 := by
  rw [imageBesselSymbol, Real.norm_eq_abs, abs_of_pos (euclideanSobolevWeight_pos _ _)]
  exact (euclideanSobolevWeight_mono (by norm_num : (-1 : ℝ) ≤ 0) _).trans_eq
    (euclideanSobolevWeight_zero _)

private theorem integrable_sourceTransform_bessel_profile
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (g : E → F) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (u : E → ℂ) (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) (x : E) :
    Integrable (sourceAmplitudeTransform (fun _ y ξ ↦ imageBesselSymbol ξ • g y) u x) := by
  apply integrable_sourceTransform_fixed_profile
    (fun ξ ↦ imageBesselSymbol ξ • ContinuousLinearMap.id ℝ F)
    1 (fun ξ ↦ ?_) g hg hgc
    ((hasTemperateGrowth_imageBesselSymbol.1.continuous.comp continuous_fst).smul
      (hg.continuous.comp continuous_snd)) u hu huc x
  rw [norm_smul]
  exact (mul_le_mul (norm_imageBesselSymbol_le_one ξ) ContinuousLinearMap.norm_id_le
    (norm_nonneg _) zero_le_one).trans_eq (by ring)

private theorem continuous_imageBesselContraction_apply
    (b : OrthonormalBasis (Fin d) ℝ E) (T : E → E →L[ℝ] ℂ) (hT : Continuous T) :
    Continuous (fun p : E × E ↦ imageBesselContraction b p.1 (T p.2)) := by
  simp_rw [imageBesselContraction_apply, frequencyCutoffError]
  apply Continuous.const_smul (c := (2 * Real.pi * Complex.I)⁻¹)
  apply continuous_finsetSum
  intro j _
  exact (((hasTemperateGrowth_imageBesselSymbol.1.continuous_fderiv (by simp)).comp
    continuous_fst).clm_apply continuous_const).smul
      ((hT.comp continuous_snd).clm_apply continuous_const)

private theorem norm_imageBesselContraction_uniform (b : OrthonormalBasis (Fin d) ℝ E) (ξ : E) :
    ‖imageBesselContraction b ξ‖ ≤ ‖(2 * Real.pi * Complex.I)⁻¹‖ * d * (2 * Real.pi) := by
  apply (norm_imageBesselContraction_le b ξ).trans
  apply mul_le_of_le_one_right (by positivity)
  exact inv_le_one_of_one_le₀ (by linarith [sq_nonneg ‖(2 * Real.pi) • ξ‖])

private theorem contDiff_sourceSquareTaylor (χ β : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hβ : ContDiff ℝ ∞ β) (x : E) :
    ContDiff ℝ ∞ (sourceTaylorCoefficient (fun y ↦ ((χ y)^2 : ℂ)) β x) := by
  have hc : ContDiff ℝ ∞ (fun p : E × E × E ↦ ((χ p.2.1)^2 : ℂ)) :=
    (Complex.ofRealCLM.contDiff.comp (hχ.comp contDiff_snd.fst)).pow 2
  exact (contDiff_fullTaylorCoefficient_joint (fun _ y _ : E ↦ ((χ y)^2 : ℂ)) β hc hβ).comp
    (f := fun y : E ↦ (x, y, (0 : E))) (by fun_prop)

private theorem hasCompactSupport_sourceSquareTaylor (χ β : E → ℝ)
    (hβc : HasCompactSupport β) (x : E) :
    HasCompactSupport (sourceTaylorCoefficient (fun y ↦ ((χ y)^2 : ℂ)) β x) :=
  hβc.smul_right

/-- Exact unregularized diagonal reduction of the actual source-square
Bessel amplitude. Its four source-tested frequency integrals converge by
bounds proved from the Bessel symbol and the fixed compact profiles
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem imageSourceSquare_diagonal_reduction
    (b : OrthonormalBasis (Fin d) ℝ E) (χ β : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
    (hplateau : ∀ y, χ y ≠ 0 → β y = 1)
    (u : E → ℂ) (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) (x : E) :
    let c := fun _ y ξ : E ↦ imageBesselSymbol ξ • ((χ y)^2 : ℂ)
    fullAmplitudeOperator c u x = fullAmplitudeOperator (diagonalAmplitude c β) u x +
      fullAmplitudeOperator (diagonalRemainderAmplitude b c β) u x := by
  let c := fun _ y ξ : E ↦ imageBesselSymbol ξ • ((χ y)^2 : ℂ)
  have hc : ContDiff ℝ ∞ (fun p : E × E × E ↦ c p.1 p.2.1 p.2.2) :=
    (hasTemperateGrowth_imageBesselSymbol.1.comp contDiff_snd.snd).smul
      ((Complex.ofRealCLM.contDiff.comp (hχ.comp contDiff_snd.fst)).pow 2)
  have hs : ContDiff ℝ ∞ (fun y ↦ ((χ y)^2 : ℂ)) :=
    (Complex.ofRealCLM.contDiff.comp hχ).pow 2
  have hsc : HasCompactSupport (fun y ↦ ((χ y)^2 : ℂ)) := by
    apply hχc.comp_left (g := fun t : ℝ ↦ (t : ℂ)^2)
    simp
  apply fullAmplitudeOperator_eq_diagonal_add_remainder b c β u x hc hβ
    (fun _ y hy ↦ hplateau y (fun hy₀ ↦ hy (by simp [c, hy₀]))) hu.continuous huc
  · exact integrable_sourceTransform_bessel_profile _ hs hsc u hu huc x
  · have he : diagonalAmplitude c β =
        fun x y ξ : E ↦ imageBesselSymbol ξ • (β y • ((χ x)^2 : ℂ)) := by
      funext x y ξ
      exact smul_comm _ _ _
    rw [he]
    change Integrable (fun ξ ↦ sourceAmplitudeTransform _ u x ξ)
    unfold sourceAmplitudeTransform
    have hg : ContDiff ℝ ∞ (fun y : E ↦ β y • ((χ x)^2 : ℂ)) :=
      hβ.smul contDiff_const
    have hgc : HasCompactSupport (fun y : E ↦ β y • ((χ x)^2 : ℂ)) :=
      hβc.smul_right
    have hi := integrable_sourceTransform_bessel_profile (fun y : E ↦ β y • ((χ x)^2 : ℂ))
      hg hgc u hu huc x
    change Integrable (fun ξ ↦ sourceAmplitudeTransform _ u x ξ) at hi
    unfold sourceAmplitudeTransform at hi
    exact hi
  · have he (y ξ : E) : diagonalRemainderAmplitude b c β x y ξ =
        imageBesselContraction b ξ
          (sourceTaylorCoefficient (fun z ↦ ((χ z)^2 : ℂ)) β x y) := by
      exact (imageSourceSquare_remainder_eq b χ β hχ x y ξ).trans
        (imageBesselContraction_apply b ξ _).symm
    change Integrable (fun ξ ↦ sourceAmplitudeTransform _ u x ξ)
    unfold sourceAmplitudeTransform
    simp_rw [he]
    exact integrable_sourceTransform_fixed_profile (imageBesselContraction b)
      _ (norm_imageBesselContraction_uniform b)
      (sourceTaylorCoefficient (fun z ↦ ((χ z)^2 : ℂ)) β x)
      (contDiff_sourceSquareTaylor χ β hχ hβ x)
      (hasCompactSupport_sourceSquareTaylor χ β hβc x)
      (continuous_imageBesselContraction_apply b _
        (contDiff_sourceSquareTaylor χ β hχ hβ x).continuous) u hu huc x
  · have he (y ξ : E) : fullTaylorCoefficient c β x y ξ =
        imageBesselSymbol ξ •
          sourceTaylorCoefficient (fun z ↦ ((χ z)^2 : ℂ)) β x y := by
      exact fullTaylorCoefficient_frequency_smul (fun _ y _ : E ↦ ((χ y)^2 : ℂ)) β
        imageBesselSymbol x y ξ (hs.differentiable (by simp))
    change Integrable (fun ξ ↦ sourceAmplitudeTransform _ u x ξ)
    unfold sourceAmplitudeTransform
    simp_rw [he]
    exact integrable_sourceTransform_bessel_profile _ (contDiff_sourceSquareTaylor χ β hχ hβ x)
      (hasCompactSupport_sourceSquareTaylor χ β hβc x) u hu huc x

/-- The literal commutator `[J, χ²]` on the localized input `βu` equals the
explicit two-position remainder. Together with `PhysicalJets`, this identifies
the actual test operator whose physical jets have order-minus-two decay
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem imageBessel_sourceSquare_commutator_eq_remainder
    (b : OrthonormalBasis (Fin d) ℝ E) (χ β : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
    (hplateau : ∀ y, χ y ≠ 0 → β y = 1)
    (u : 𝓢(E, ℂ)) (huc : HasCompactSupport (u : E → ℂ)) (x : E) :
    schwartzFrequencyMultiplier (fun ξ ↦ (imageBesselSymbol ξ : ℂ))
      (SchwartzMap.smulLeftCLM ℂ (fun y ↦ ((χ y)^2 : ℂ))
        (SchwartzMap.smulLeftCLM ℂ (fun y ↦ (β y : ℂ)) u)) x -
      (χ x)^2 • schwartzFrequencyMultiplier (fun ξ ↦ (imageBesselSymbol ξ : ℂ))
        (SchwartzMap.smulLeftCLM ℂ (fun y ↦ (β y : ℂ)) u) x =
      fullAmplitudeOperator (diagonalRemainderAmplitude b
        (fun _ y ξ ↦ imageBesselSymbol ξ • ((χ y)^2 : ℂ)) β) u x := by
  have htχ : χ.HasTemperateGrowth := hχc.hasTemperateGrowth hχ
  have htβ : β.HasTemperateGrowth := hβc.hasTemperateGrowth hβ
  have htχ₂ : (fun y ↦ ((χ y)^2 : ℂ)).HasTemperateGrowth := by fun_prop
  have htβℂ : (fun y ↦ (β y : ℂ)).HasTemperateGrowth := by fun_prop
  have hmask : SchwartzMap.smulLeftCLM ℂ (fun y ↦ ((χ y)^2 : ℂ))
        (SchwartzMap.smulLeftCLM ℂ (fun y ↦ (β y : ℂ)) u) =
      SchwartzMap.smulLeftCLM ℂ (fun y ↦ ((χ y)^2 : ℂ)) u := by
    ext y
    rw [SchwartzMap.smulLeftCLM_apply_apply htχ₂,
      SchwartzMap.smulLeftCLM_apply_apply htβℂ,
      SchwartzMap.smulLeftCLM_apply_apply htχ₂]
    by_cases hy : χ y = 0
    · simp [hy]
    · simp [hplateau y hy]
  rw [hmask]
  have h := imageSourceSquare_diagonal_reduction b χ β hχ hχc hβ hβc hplateau
    u (u.smooth ⊤) huc x
  dsimp only at h
  rw [imageBessel_masked_fullAmplitude _ htχ₂,
    imageBessel_diagonal_fullAmplitude χ β htβ] at h
  rw [h]
  abel

end JanetCartan.ContinuumNormalReduction.ImageNormal
