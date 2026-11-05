module

public import JanetCartan.Geometry.IsometricEmbedding.Basic

/-!
# Exact source dilation of a smooth reference

The geometric rescaling in `app:ch_seed:cor:seed-uniform-dilation` of `paper.tex`:
`sourceDilation F σ x = σ⁻¹ • F (σ • x)`. The first derivative, induced metric,
and normal space are evaluated at `σ • x`; the second derivative, second form,
and geometric normal map `B_F` acquire one factor of `σ`. These are also the
geometric inputs to the reconstruction scaling in `app:ch_background:eq:bg-Nsigma`.

This is source-immersion dilation, distinct from the target metric estimates in
`Reference.Dilation`. The results apply to any supplied smooth map, without using
the unfinished existence theorem for the flat reference. No norm estimates or
existence of a reference with quantitative geometric gaps are asserted here.

For a reference normalized by `F 0 = 0`, `sourceDilation_eq_centered` identifies
this map with the manuscript's centered expression. The geometric formulas also
hold without this normalization, since translation does not affect derivatives.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan

/-- Source-immersion scaling in `app:ch_seed:cor:seed-uniform-dilation`. -/
def sourceDilation {n N : ℕ} (F : Euclidean n → Euclidean N) (σ : ℝ) :
    Euclidean n → Euclidean N := fun x ↦ σ⁻¹ • F (σ • x)

variable {n N : ℕ} {F : Euclidean n → Euclidean N} {σ : ℝ}

/-- The rescaled reference stays smooth (`app:ch_seed:cor:seed-uniform-dilation`). -/
theorem contDiff_sourceDilation (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (sourceDilation F σ) :=
  (hF.comp (contDiff_id.const_smul σ)).const_smul σ⁻¹

/-- Exact first derivative in `app:ch_seed:cor:seed-uniform-dilation`. -/
theorem fderiv_sourceDilation (hσ : 0 < σ) {x : Euclidean n}
    (hF : DifferentiableAt ℝ F (σ • x)) :
    fderiv ℝ (sourceDilation F σ) x = fderiv ℝ F (σ • x) := by
  unfold sourceDilation
  have h := ((hF.hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul σ)).const_smul
    σ⁻¹).fderiv
  simpa [Function.comp_def, Pi.smul_def, ContinuousLinearMap.comp_smul,
    smul_smul, ne_of_gt hσ] using h

/-- Coordinate first derivatives in `app:ch_seed:cor:seed-uniform-dilation`. -/
theorem partialDeriv_sourceDilation (hσ : 0 < σ) {x : Euclidean n}
    (hF : DifferentiableAt ℝ F (σ • x)) (i : Fin n) :
    partialDeriv (sourceDilation F σ) x i = partialDeriv F (σ • x) i := by
  simp only [partialDeriv, fderiv_sourceDilation hσ hF]

/-- Exact second Fréchet derivative in `app:ch_seed:cor:seed-uniform-dilation`. -/
theorem fderiv_fderiv_sourceDilation (hσ : 0 < σ) (hF : ContDiff ℝ ∞ F)
    (x : Euclidean n) :
    fderiv ℝ (fderiv ℝ (sourceDilation F σ)) x =
      σ • fderiv ℝ (fderiv ℝ F) (σ • x) := by
  have hfirst : fderiv ℝ (sourceDilation F σ) = fun y ↦ fderiv ℝ F (σ • y) :=
    funext fun y ↦ fderiv_sourceDilation hσ (hF.differentiable (by simp) _)
  rw [hfirst]
  have hDF : Differentiable ℝ (fderiv ℝ F) :=
    (hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  simpa [Function.comp_def, ContinuousLinearMap.comp_smul] using
    ((hDF (σ • x)).hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul σ)).fderiv

/-- Derivatives of coordinate first derivatives in
`app:ch_seed:cor:seed-uniform-dilation`. -/
theorem fderiv_partialDeriv_sourceDilation (hσ : 0 < σ) (hF : ContDiff ℝ ∞ F)
    (x : Euclidean n) (j : Fin n) :
    fderiv ℝ (fun y ↦ partialDeriv (sourceDilation F σ) y j) x =
      σ • fderiv ℝ (fun y ↦ partialDeriv F y j) (σ • x) := by
  have hfirst : (fun y ↦ partialDeriv (sourceDilation F σ) y j) =
      fun y ↦ partialDeriv F (σ • y) j :=
    funext fun y ↦ partialDeriv_sourceDilation hσ (hF.differentiable (by simp) _) j
  rw [hfirst]
  have hDF : Differentiable ℝ (fun y ↦ partialDeriv F y j) :=
    ((hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).differentiable (by simp)
  simpa [Function.comp_def, ContinuousLinearMap.comp_smul] using
    ((hDF (σ • x)).hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul σ)).fderiv

/-- The metric pulls back with no scalar factor
(`app:ch_seed:cor:seed-uniform-dilation`). -/
theorem inducedMetric_sourceDilation (hσ : 0 < σ) {x : Euclidean n}
    (hF : DifferentiableAt ℝ F (σ • x)) :
    inducedMetric (sourceDilation F σ) x = inducedMetric F (σ • x) := by
  ext i j
  simp only [inducedMetric, partialDeriv_sourceDilation hσ hF]

/-- The actual normal spaces agree (`app:ch_seed:cor:seed-uniform-dilation`). -/
theorem normalSpace_sourceDilation (hσ : 0 < σ) {x : Euclidean n}
    (hF : DifferentiableAt ℝ F (σ • x)) :
    normalSpace (sourceDilation F σ) x = normalSpace F (σ • x) := by
  simp only [normalSpace, fderiv_sourceDilation hσ hF]

/-- The orthogonal normal projectors agree
(`app:ch_seed:cor:seed-uniform-dilation`). -/
theorem normalSpace_starProjection_sourceDilation (hσ : 0 < σ) {x : Euclidean n}
    (hF : DifferentiableAt ℝ F (σ • x)) :
    (normalSpace (sourceDilation F σ) x).starProjection =
      (normalSpace F (σ • x)).starProjection :=
  congrArg (fun P : Submodule ℝ (Euclidean N) ↦ P.starProjection)
    (normalSpace_sourceDilation hσ hF)

/-- The actual second form scales by `σ`
(`app:ch_seed:cor:seed-uniform-dilation`). -/
theorem secondFundamentalForm_sourceDilation (hσ : 0 < σ) (hF : ContDiff ℝ ∞ F)
    (x : Euclidean n) (i j : Fin n) :
    secondFundamentalForm (sourceDilation F σ) x i j =
      σ • secondFundamentalForm F (σ • x) i j := by
  change (normalSpace (sourceDilation F σ) x).starProjection
      (fderiv ℝ (fun y ↦ partialDeriv (sourceDilation F σ) y j) x
        (EuclideanSpace.single i 1)) =
    σ • (normalSpace F (σ • x)).starProjection
      (fderiv ℝ (fun y ↦ partialDeriv F y j) (σ • x) (EuclideanSpace.single i 1))
  rw [normalSpace_starProjection_sourceDilation hσ (hF.differentiable (by simp) _),
    fderiv_partialDeriv_sourceDilation hσ hF]
  simp only [smul_apply, map_smul]

/-- The geometric normal map `B_G = σ B_F(σ x)` in
`app:ch_seed:cor:seed-uniform-dilation`. This is the map defined in `Basic`,
not its inverse-adjoint reconstruction operator. -/
theorem normalMap_sourceDilation (hσ : 0 < σ) (hF : ContDiff ℝ ∞ F)
    (x : Euclidean n) (H : MetricTensor n) :
    normalMap (sourceDilation F σ) x H = σ • normalMap F (σ • x) H := by
  simp only [normalMap, secondFundamentalForm_sourceDilation hσ hF, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact smul_comm _ _ _

/-- The stress kernel pulls back unchanged
(`app:ch_seed:cor:seed-uniform-dilation`). -/
theorem stressSpace_sourceDilation (hσ : 0 < σ) (hF : ContDiff ℝ ∞ F)
    (x : Euclidean n) :
    stressSpace (sourceDilation F σ) x = stressSpace F (σ • x) := by
  ext H
  simp only [stressSpace, Set.mem_ofPred_eq, normalMap_sourceDilation hσ hF,
    smul_eq_zero, ne_of_gt hσ, false_or]

/-- Immersion is preserved on corresponding domains
(`app:ch_seed:cor:seed-uniform-dilation`). -/
theorem isImmersionOn_sourceDilation_iff (hσ : 0 < σ) (hF : ContDiff ℝ ∞ F)
    (s : Set (Euclidean n)) :
    IsImmersionOn (sourceDilation F σ) s ↔ IsImmersionOn F ((fun x ↦ σ • x) '' s) := by
  simp only [IsImmersionOn, Set.forall_mem_image,
    fderiv_sourceDilation hσ (hF.differentiable (by simp) _)]

/-- The normal-map range is unchanged by positive dilation
(`app:ch_seed:cor:seed-uniform-dilation`). -/
theorem normalMap_sourceDilation_range (hσ : 0 < σ) (hF : ContDiff ℝ ∞ F)
    (x : Euclidean n) :
    Set.range (normalMap (sourceDilation F σ) x) = Set.range (normalMap F (σ • x)) := by
  have hsmul (c : ℝ) (H : MetricTensor n) :
      normalMap F (σ • x) (c • H) = c • normalMap F (σ • x) H := by
    simp only [normalMap, Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
  ext v
  constructor
  · rintro ⟨H, rfl⟩
    exact ⟨σ • H, (hsmul σ H).trans (normalMap_sourceDilation hσ hF x H).symm⟩
  · rintro ⟨H, rfl⟩
    refine ⟨σ⁻¹ • H, ?_⟩
    rw [normalMap_sourceDilation hσ hF, hsmul, smul_inv_smul₀ (ne_of_gt hσ)]

/-- Full normal rank is preserved on corresponding domains
(`app:ch_seed:cor:seed-uniform-dilation`). -/
theorem hasFullNormalRankOn_sourceDilation_iff (hσ : 0 < σ) (hF : ContDiff ℝ ∞ F)
    (s : Set (Euclidean n)) :
    HasFullNormalRankOn (sourceDilation F σ) s ↔
      HasFullNormalRankOn F ((fun x ↦ σ • x) '' s) := by
  simp only [HasFullNormalRankOn, Set.forall_mem_image,
    normalMap_sourceDilation_range hσ hF,
    normalSpace_sourceDilation hσ (hF.differentiable (by simp) _)]

/-- An actually flat reference remains exactly flat
(`app:ch_seed:cor:seed-uniform-dilation`). -/
theorem inducedMetric_sourceDilation_eq_one (hσ : 0 < σ) (hF : ContDiff ℝ ∞ F)
    (hflat : ∀ x, inducedMetric F x = 1) (x : Euclidean n) :
    inducedMetric (sourceDilation F σ) x = 1 := by
  rw [inducedMetric_sourceDilation hσ (hF.differentiable (by simp) _), hflat]

/-- For a center-zero reference, the source dilation is precisely the centered
formula of `app:ch_seed:cor:seed-uniform-dilation` and `app:ch_background:eq:bg-Nsigma`. -/
theorem sourceDilation_eq_centered (hF₀ : F 0 = 0) :
    sourceDilation F σ = fun x ↦ σ⁻¹ • (F (σ • x) - F 0) := by
  unfold sourceDilation
  simp only [hF₀, sub_zero]

/-- The normalized center is preserved (`app:ch_seed:cor:seed-uniform-dilation`). -/
theorem sourceDilation_zero (hF₀ : F 0 = 0) : sourceDilation F σ 0 = 0 := by
  simp only [sourceDilation, smul_zero, hF₀]

end JanetCartan
