module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.ImagePerturbation
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.ImageGeometry.Coefficients

/-!
# Actual geometric continuity of the image normal

For `paper-v2.tex`, `app:ch_background:prop:bg-frame`, the image-normal
neighborhood is obtained from the actual reference and primitive C8 closeness.
The smooth ambient second-jet formula and its compact admissible range supply
coefficient continuity. The fixed coefficient extension, measurement cutoff,
source cutoff and reference operator precede every requested tolerance.
No normal-operator continuity or coefficient closeness is assumed.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.ContinuumNormal

open ContinuumRow ImageGeometry GeometricProfile ProjectedStressFrame
open CurrentGeometricNeighborhood

variable {n : ℕ}

set_option maxHeartbeats 800000 in
/-- Primitive C8 map closeness controls every principal and connection
coefficient on a fixed inner ball (`paper-v2.tex`,
`app:ch_background:prop:bg-frame`). -/
theorem exists_geometricReducedCoefficients_neighborhood (G : FlatReference n)
    {r R ε : ℝ} (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ F : Euclidean n → Euclidean (embeddingDimension n),
      ContDiff ℝ ∞ F → cNorm (closedBall 0 R) 8 (F - G.map) < δ →
      ∀ x ∈ closedBall (0 : Euclidean n) r,
        ‖geometricReducedCoefficients F x - geometricReducedCoefficients G.map x‖ < ε := by
  obtain ⟨djet, hdjet, L, hL, hu, hjet⟩ := exists_image_coefficient_jet_neighborhood G hR
  obtain ⟨dgeo, hdgeo, _, _, _, _, hgeo⟩ :=
    exists_geometric_neighborhood G hr hrR hR (by norm_num : (0 : ℝ) < 1)
  have hc : ContinuousOn (@ambientReducedCoefficients n (embeddingDimension n)) L :=
    fun J hJ ↦ (contDiffAt_ambientReducedCoefficients (hu J hJ).1
      (hu J hJ).2).continuousAt.continuousWithinAt
  have huc : UniformContinuousOn (@ambientReducedCoefficients n (embeddingDimension n)) L :=
    hL.uniformContinuousOn_of_continuous hc
  obtain ⟨d, hd, hcont⟩ := (Metric.uniformContinuousOn_iff
    (f := @ambientReducedCoefficients n (embeddingDimension n)) (s := L)).mp huc ε hε
  have hself (δ : ℝ) (hδ : 0 < δ) :
      cNorm (closedBall (0 : Euclidean n) R) 8 (G.map - G.map) < δ := by
    simpa only [sub_self, cNorm_zero] using hδ
  obtain ⟨hGi, hGn, _⟩ := hgeo univ G.map isOpen_univ (subset_univ _)
    G.contDiff.contDiffOn (hself dgeo hdgeo)
  refine ⟨min djet (min dgeo (d / 2)), lt_min hdjet (lt_min hdgeo (half_pos hd)), ?_⟩
  intro F hF hclose x hx
  have hFjet := hclose.trans_le (min_le_left djet _)
  have hFgeo := hclose.trans_le ((min_le_right djet _).trans (min_le_left dgeo _))
  have hFd := hclose.trans_le ((min_le_right djet _).trans (min_le_right dgeo _))
  have hxR : x ∈ closedBall (0 : Euclidean n) R := closedBall_subset_closedBall hrR.le hx
  have hxB : x ∈ ball (0 : Euclidean n) R := closedBall_subset_ball hrR hx
  obtain ⟨hFi, hFn, _⟩ := hgeo univ F isOpen_univ (subset_univ _) hF.contDiffOn hFgeo
  rw [← ambientReducedCoefficients_stressJet hF (hFi x hxB) (hFn x hxB),
    ← ambientReducedCoefficients_stressJet G.contDiff (hGi x hxB) (hGn x hxB)]
  apply (show dist (ambientReducedCoefficients (stressJet F x))
    (ambientReducedCoefficients (stressJet G.map x)) < ε from ?_)
  apply hcont _ (hjet F hF hFjet hxR) _ (hjet G.map G.contDiff (hself djet hdjet) hxR)
  have hdident := @dist_eq_norm (StressJet n (embeddingDimension n)) _
    (stressJet F x) (stressJet G.map x)
  rw [hdident]
  have hb := norm_stressJet_sub_le (isCompact_closedBall (0 : Euclidean n) R)
    isOpen_univ (subset_univ _) hF.contDiffOn G.contDiff.contDiffOn hxR
  linarith

set_option maxHeartbeats 800000 in
/-- Construct a single periodic reference image operator and derive its
operator-norm neighborhood from primitive C8 immersion closeness. The same
literal geometric coefficient extension is used for every tolerance and map.
Source: `paper-v2.tex`, `app:ch_background:prop:bg-frame`, perturbation step. -/
theorem exists_reference_imageNormal_neighborhood (G : FlatReference n)
    {r₀ r₁ R : ℝ} (hr₀ : 0 < r₀) (h₀₁ : r₀ < r₁) (h₁R : r₁ < R)
    (hRG : R < G.domain.chartRadius) (hR : R < 1 / 2)
    (χmeas χsrc : C(Torus n, ℝ)) :
    ∃ (χ : Euclidean n → ℝ)
      (c₀ : ReducedCoefficientIndex n → C(Torus n, ℝ)),
      ContDiff ℝ ∞ χ ∧ (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ ball 0 r₁ ∧ closedBall 0 r₀ ⊆ interior {x | χ x = 1} ∧
      (∀ j z, c₀ j z = χ (AmplitudeBound.centeredTorusRepresentative z) *
        geometricReducedCoefficients G.map (AmplitudeBound.centeredTorusRepresentative z) j) ∧
      (∀ j, IsSmoothPeriodic (c₀ j)) ∧
      ∀ ε > 0, ∃ δ > 0,
        ∀ F : Euclidean n → Euclidean (embeddingDimension n), ContDiff ℝ ∞ F →
          cNorm (closedBall 0 R) 8 (F - G.map) < δ →
          ∃ c : ReducedCoefficientIndex n → C(Torus n, ℝ),
            (∀ j z, c j z = χ (AmplitudeBound.centeredTorusRepresentative z) *
              geometricReducedCoefficients F (AmplitudeBound.centeredTorusRepresentative z) j) ∧
            (∀ j, IsSmoothPeriodic (c j)) ∧
            (∀ j x, x ∈ closedBall 0 r₀ → periodicLift (c j) =ᶠ[nhds x]
              (fun y ↦ geometricReducedCoefficients F y j)) ∧
            ‖NormalPerturbation.normal (imageChannel c χmeas χsrc) -
              NormalPerturbation.normal (imageChannel c₀ χmeas χsrc)‖ < ε := by
  obtain ⟨χ, dbase, B, C, hχ, hrange, hcompact, hs, hp, hdbase, _, _, hperiod⟩ :=
    exists_reference_periodic_coefficients G hr₀ h₀₁ h₁R hRG hR
  obtain ⟨c₀, hc₀, hc₀smooth, _, _, _⟩ := hperiod G.map G.contDiff
    (by simpa only [sub_self, cNorm_zero] using hdbase)
  refine ⟨χ, c₀, hχ, hrange, hcompact, hs, hp, hc₀, hc₀smooth, ?_⟩
  intro ε hε
  obtain ⟨η, hη, hop⟩ := exists_imageNormal_coefficient_neighborhood c₀ χmeas χsrc hε
  obtain ⟨dgeo, hdgeo, hgeom⟩ := exists_geometricReducedCoefficients_neighborhood G
    (hr₀.trans h₀₁) h₁R hRG (half_pos hη)
  refine ⟨min dbase dgeo, lt_min hdbase hdgeo, ?_⟩
  intro F hF hclose
  obtain ⟨c, hc, hcsmooth, heq, _, _⟩ := hperiod F hF (hclose.trans_le (min_le_left _ _))
  refine ⟨c, hc, hcsmooth, heq, ?_⟩
  apply hop c
  have hb : ‖c - c₀‖ ≤ η / 2 := by
    apply (pi_norm_le_iff_of_nonneg (half_pos hη).le).mpr
    intro j
    apply (ContinuousMap.norm_le _ (half_pos hη).le).mpr
    intro z
    change ‖c j z - c₀ j z‖ ≤ η / 2
    rw [hc, hc₀, ← mul_sub, norm_mul]
    let x := AmplitudeBound.centeredTorusRepresentative z
    change ‖χ x‖ * ‖geometricReducedCoefficients F x j -
      geometricReducedCoefficients G.map x j‖ ≤ η / 2
    by_cases hx : χ x = 0
    · simp only [hx, norm_zero, zero_mul]
      exact (half_pos hη).le
    · have hxs : x ∈ closedBall (0 : Euclidean n) r₁ := ball_subset_closedBall (hs (subset_tsupport _ hx))
      have hcoeff := hgeom F hF (hclose.trans_le (min_le_right _ _)) x hxs
      have hentry := norm_le_pi_norm
        (geometricReducedCoefficients F x - geometricReducedCoefficients G.map x) j
      have hχone : ‖χ x‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (hrange x).1]
        exact (hrange x).2
      exact (mul_le_of_le_one_left (norm_nonneg _) hχone).trans (hentry.trans hcoeff.le)
  exact hb.trans_lt (half_lt_self hη)

end JanetCartan.ContinuumNormal
