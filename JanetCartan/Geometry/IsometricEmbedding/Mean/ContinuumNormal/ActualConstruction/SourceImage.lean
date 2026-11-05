module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.ActualConstruction.ImageComparison
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenCoercivity.ImageEnergy
public import JanetCartan.Geometry.IsometricEmbedding.Mean.RetainedAssembly.NormalizedImage

/-!
# Actual normalized-source image comparison on the supplied cutoff

The source coefficient producer supplies every analytic estimate here. Its
zero-scale array is identified with the retained frozen image, including the
transpose convention and zero connection coefficients. One coefficient bound
precedes every requested tolerance and source cap. The source cap applies
to every smaller scale and every periodic extension with the SAME literal
coefficient formula. Thus a later initializer may use this cap without
identifying independently chosen source scales or image operators.
Consumer: `exists_initialized_density_coercivity_threshold`'s image input.
Sources: `app:ch_background:prop:bg-normalized`, `app:ch_background:prop:bg-frame`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff

namespace JanetCartan.ContinuumNormal.ActualConstruction

open ContinuumRow GeometricProfile ProtectedFlow FrozenCoercivity FrozenImageComparison
open AmplitudeBound

variable {n : ℕ}

/-- The normalized source's zero-scale coefficient array is exactly the
frozen cube image, with zero connection term. Symmetry accounts for the
principal-index transpose (`app:ch_background:prop:bg-normalized`). -/
theorem frozen_cube_imageCoefficients_eq_background
    (j : ReducedCoefficientIndex n) (z : Torus n) (x : Euclidean n) :
    constantImageCoefficients (frozenImageArrays (cubeStress n)) j z =
      reducedCoefficientBackground (fun _ _ ↦ 0) x j := by
  rcases j with ⟨a, i, k⟩ | ⟨i, k⟩
  · simp only [constantImageCoefficients, ContinuousMap.const_apply, frozenImageArrays,
      reducedCoefficientBackground, cubeStress, and_comm]
  · rfl

/-- Construct the actual source-to-frozen image-normal threshold from the
checked normalized coefficient producer. The reference, physical extension,
source/measurement masks and frozen array are all supplied first; the cap
works at EVERY smaller positive source scale. No coefficient or operator
continuity estimate is assumed (`app:ch_background:prop:bg-normalized`,
`app:ch_background:prop:bg-frame`). -/
theorem exists_normalized_source_imageNormal_threshold (H : FlatReference n)
    {r₀ r₁ R : ℝ} (hr₀ : 0 < r₀) (h₀₁ : r₀ < r₁) (h₁R : r₁ < R)
    (hR : R < 1 / 2) {χcoeff : Euclidean n → ℝ} (hχ : ContDiff ℝ ∞ χcoeff)
    (hs : tsupport χcoeff ⊆ ball 0 r₁)
    (hp : closedBall 0 r₀ ⊆ interior {x | χcoeff x = 1})
    (d : ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hd : ∀ j z, d j z = χcoeff (centeredTorusRepresentative z) *
      constantImageCoefficients (frozenImageArrays (cubeStress n)) j z)
    (χmeas χsrc : C(Torus n, ℝ)) :
    ∃ Bimage > (0 : ℝ), (∀ j z, |d j z| ≤ Bimage) ∧
    ∀ ε > (0 : ℝ), ∃ σcap > (0 : ℝ), σcap ≤ 1 ∧
      ∀ σ ∈ Ioc (0 : ℝ) σcap,
      ∀ c : ReducedCoefficientIndex n → C(Torus n, ℝ),
        (∀ j z, c j z = χcoeff (centeredTorusRepresentative z) *
          geometricReducedCoefficients (sourceDilation H.map σ)
            (centeredTorusRepresentative z) j) →
        (∀ j z, |c j z| ≤ Bimage) ∧
        ‖imageChannel c χmeas χsrc‖ ≤
          ‖χmeas‖ * (((n : ℝ) ^ 3 + (n : ℝ) ^ 2) * Bimage) * ‖χsrc‖ ∧
        ‖c - d‖ < ε ∧
        ‖NormalPerturbation.normal (imageChannel c χmeas χsrc) -
          NormalPerturbation.normal (imageChannel d χmeas χsrc)‖ < ε := by
  obtain ⟨σ₀, hσ₀, hσ₁, c₀, c, hc₀, _hc₀smooth, _hc₀plateau, hc,
    _hcsmooth, _hcplateau, hjets, _hformula, _hweak, _hadjoint⟩ :=
    RetainedAssembly.NormalizedImage.exists_normalized_image_coefficients H
      hr₀ h₀₁ h₁R hR hχ hs hp
  have hd₀ : d = c₀ := by
    funext j
    ext z
    rw [hd, hc₀, frozen_cube_imageCoefficients_eq_background j z
      (centeredTorusRepresentative z)]
  obtain ⟨C, hC, hzero, hbound⟩ := hjets 0
  refine ⟨C, hC, ?_, ?_⟩
  · intro j z
    rw [hd₀]
    simpa only [norm_iteratedFDeriv_zero, periodicLift, Function.comp_apply,
      torusQuotient_centeredTorusRepresentative, Real.norm_eq_abs] using
      hzero j (centeredTorusRepresentative z)
  intro ε hε
  obtain ⟨η, hη, himage⟩ := exists_imageNormal_coefficient_neighborhood d χmeas χsrc hε
  let σcap := min σ₀ (min η ε / (2 * C))
  refine ⟨σcap, lt_min hσ₀ (div_pos (lt_min hη hε) (by positivity)),
    (min_le_left _ _).trans hσ₁, ?_⟩
  intro σ hσ a ha
  have hσold : σ ∈ Ioc (0 : ℝ) σ₀ := ⟨hσ.1, hσ.2.trans (min_le_left _ _)⟩
  have haeq : a = c σ hσold := by
    funext j
    ext z
    rw [ha, hc]
  have habsolute (j : ReducedCoefficientIndex n) (z : Torus n) : |a j z| ≤ C := by
    rw [haeq]
    simpa only [norm_iteratedFDeriv_zero, periodicLift, Function.comp_apply,
      torusQuotient_centeredTorusRepresentative, Real.norm_eq_abs] using
      (hbound σ hσold j (centeredTorusRepresentative z)).2
  have hnorm : ‖a - d‖ ≤ C * σ := by
    rw [haeq, hd₀]
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC.le hσ.1.le)).mpr
    intro j
    apply (ContinuousMap.norm_le _ (mul_nonneg hC.le hσ.1.le)).mpr
    intro z
    have h := (hbound σ hσold j (centeredTorusRepresentative z)).1
    simpa only [norm_iteratedFDeriv_zero, periodicLift, Function.comp_apply,
      torusQuotient_centeredTorusRepresentative, Pi.sub_apply,
      ContinuousMap.sub_apply] using h
  have hscale := (le_div_iff₀ (show 0 < 2 * C by positivity)).mp
    (hσ.2.trans (min_le_right _ _))
  have hsmall : C * σ < min η ε := by
    have hmin : 0 < min η ε := lt_min hη hε
    nlinarith
  refine ⟨habsolute, ?_, (hnorm.trans_lt hsmall).trans_le (min_le_right _ _),
    himage a ((hnorm.trans_lt hsmall).trans_le (min_le_left _ _))⟩
  simpa only [add_mul] using imageChannel_norm_le_of_bounds a χmeas χsrc hC.le hC.le
    (fun a i j x ↦ habsolute (.inl (a, i, j)) x)
    (fun i j x ↦ habsolute (.inr (i, j)) x)

end JanetCartan.ContinuumNormal.ActualConstruction
