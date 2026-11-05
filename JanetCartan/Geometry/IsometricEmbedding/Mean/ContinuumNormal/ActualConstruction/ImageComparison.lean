module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.ImageGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.ImageGeometry.Periodization

/-!
# Image comparison with the retained coefficient extension

The fixed physical extension cutoff is the one exported by the initialized row.
The order-zero primitive coefficient difference controls its literal periodic
arrays with constant one. Consequently the image-normal tolerance can be chosen
before the varying immersion or density. This supplies the image input of the
same-row lower bound in `app:ch_background:prop:bg-frame`. The actual immersion
coefficient neighborhood is applied to the supplied cutoff here; `SourceImage`
separately applies the normalized source coefficient producer.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff

namespace JanetCartan.ContinuumNormal.ActualConstruction

open ContinuumRow ImageGeometry.Periodization GeometricProfile AmplitudeBound

variable {n : ℕ}

/-- The SAME physical coefficient cutoff preserves the primitive order-zero
difference bound, without a derivative reserve or cutoff loss. The formulas are
the conclusions of the initialized row's coefficient producer
(`app:ch_background:defn:bg-row`, `app:ch_background:prop:bg-frame`). -/
theorem norm_retained_periodicCoefficients_sub_le
    {χ : Euclidean n → ℝ} {r R : ℝ}
    (hrR : r < R) (hr : r < 1 / 2) (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ ball 0 r) (hχrange : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    (q q₀ : Euclidean n → ReducedCoefficientIndex n → ℝ)
    (hq : ContDiffOn ℝ ∞ q (ball 0 R)) (hq₀ : ContDiffOn ℝ ∞ q₀ (ball 0 R))
    (c d : ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hc : ∀ j z, c j z = χ (centeredTorusRepresentative z) *
      q (centeredTorusRepresentative z) j)
    (hd : ∀ j z, d j z = χ (centeredTorusRepresentative z) *
      q₀ (centeredTorusRepresentative z) j) :
    ‖c - d‖ ≤ cNorm (closedBall 0 r) 0 (q - q₀) := by
  apply (pi_norm_le_iff_of_nonneg (cNorm_nonneg _ _ _)).mpr
  intro j
  apply (ContinuousMap.norm_le _ (cNorm_nonneg _ _ _)).mpr
  intro z
  have h := abs_periodicReducedCoefficients_le hrR hr hχ hs hχrange
    (q - q₀) (hq.sub hq₀) j z
  simpa only [periodicReducedCoefficients_apply, Pi.sub_apply, ContinuousMap.sub_apply,
    Real.norm_eq_abs, hc, hd, mul_sub] using h

/-- Choose the normal-comparison tolerance from the original coefficient
extension and cutoffs, before any varying coefficient field. The analytic input
is the primitive `C⁰` coefficient error, produced by normalized source convergence
or the retained immersion neighborhood (`app:ch_background:prop:bg-frame`). -/
theorem exists_retained_imageNormal_coefficient_threshold
    {χ : Euclidean n → ℝ} {r R : ℝ}
    (hrR : r < R) (hr : r < 1 / 2) (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ ball 0 r) (hχrange : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    (q₀ : Euclidean n → ReducedCoefficientIndex n → ℝ)
    (hq₀ : ContDiffOn ℝ ∞ q₀ (ball 0 R))
    (d : ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hd : ∀ j z, d j z = χ (centeredTorusRepresentative z) *
      q₀ (centeredTorusRepresentative z) j)
    (χmeas χsrc : C(Torus n, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ q : Euclidean n → ReducedCoefficientIndex n → ℝ,
      ContDiffOn ℝ ∞ q (ball 0 R) → cNorm (closedBall 0 r) 0 (q - q₀) < δ →
      ∀ c : ReducedCoefficientIndex n → C(Torus n, ℝ),
        (∀ j z, c j z = χ (centeredTorusRepresentative z) *
          q (centeredTorusRepresentative z) j) →
        ‖NormalPerturbation.normal (imageChannel c χmeas χsrc) -
          NormalPerturbation.normal (imageChannel d χmeas χsrc)‖ < ε := by
  obtain ⟨δ, hδ, hclose⟩ := exists_imageNormal_coefficient_neighborhood d χmeas χsrc hε
  refine ⟨δ, hδ, ?_⟩
  intro q hq hnorm c hc
  exact hclose c ((norm_retained_periodicCoefficients_sub_le hrR hr hχ hs hχrange
    q q₀ hq hq₀ c d hc hd).trans_lt hnorm)

/-- The actual immersion neighborhood controls the SAME retained image
extension, without selecting a new coefficient cutoff or reference operator.
Its primitive `C⁸` input is supplied by the initialized history neighborhood.
Both the coefficient and image-normal tolerances are conclusions
(`app:ch_background:prop:bg-frame`, history perturbation). -/
theorem exists_retained_imageNormal_immersion_threshold (G : FlatReference n)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    {χ : Euclidean n → ℝ} (hs : tsupport χ ⊆ ball 0 r)
    (hχrange : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    (d : ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hd : ∀ j z, d j z = χ (centeredTorusRepresentative z) *
      geometricReducedCoefficients G.map (centeredTorusRepresentative z) j)
    (χmeas χsrc : C(Torus n, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ F : Euclidean n → Euclidean (embeddingDimension n),
      ContDiff ℝ ∞ F → cNorm (closedBall 0 R) 8 (F - G.map) < δ →
      ∀ c : ReducedCoefficientIndex n → C(Torus n, ℝ),
        (∀ j z, c j z = χ (centeredTorusRepresentative z) *
          geometricReducedCoefficients F (centeredTorusRepresentative z) j) →
        ‖c - d‖ < ε ∧
        ‖NormalPerturbation.normal (imageChannel c χmeas χsrc) -
          NormalPerturbation.normal (imageChannel d χmeas χsrc)‖ < ε := by
  obtain ⟨η, hη, hop⟩ := exists_imageNormal_coefficient_neighborhood d χmeas χsrc hε
  have ht : 0 < min η ε := lt_min hη hε
  obtain ⟨δ, hδ, hgeom⟩ := exists_geometricReducedCoefficients_neighborhood G
    hr hrR hR (half_pos ht)
  refine ⟨δ, hδ, ?_⟩
  intro F hF hclose c hc
  have hnorm : ‖c - d‖ ≤ min η ε / 2 := by
    apply (pi_norm_le_iff_of_nonneg (half_pos ht).le).mpr
    intro j
    apply (ContinuousMap.norm_le _ (half_pos ht).le).mpr
    intro z
    change ‖c j z - d j z‖ ≤ min η ε / 2
    rw [hc, hd, ← mul_sub, norm_mul]
    let x := centeredTorusRepresentative z
    change ‖χ x‖ * ‖geometricReducedCoefficients F x j -
      geometricReducedCoefficients G.map x j‖ ≤ min η ε / 2
    by_cases hx : χ x = 0
    · simpa only [hx, norm_zero, zero_mul] using (half_pos ht).le
    · have hxs := ball_subset_closedBall (hs (subset_tsupport _ hx))
      have hcoeff := hgeom F hF hclose x hxs
      have hentry := norm_le_pi_norm
        (geometricReducedCoefficients F x - geometricReducedCoefficients G.map x) j
      have hχone : ‖χ x‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (hχrange x).1]
        exact (hχrange x).2
      exact (mul_le_of_le_one_left (norm_nonneg _) hχone).trans (hentry.trans hcoeff.le)
  have hsmall : ‖c - d‖ < min η ε := hnorm.trans_lt (half_lt_self ht)
  exact ⟨hsmall.trans_le (min_le_right _ _), hop c (hsmall.trans_le (min_le_left _ _))⟩

end JanetCartan.ContinuumNormal.ActualConstruction
