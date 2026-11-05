module

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.ReducedCoefficients
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.ImageGeometry.Neighborhood

/-!
# Primitive current-map neighborhoods for the full coefficient extension

For `app:ch_regular:thm:no-return`, finite-order continuity of the entire
reduced array follows from its actual second-jet formula. Both the principal
frame and the lower-order stress-Christoffel contraction are retained. The
consumer is the low-class assertion for the single fixed affine extension;
no coefficient comparison is assumed of the current immersion.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ProtectedFlow
open GeometricProfile ProjectedStressFrame CurrentGeometricNeighborhood
open ContinuumRow.ImageGeometry HamiltonPhase.CompositionContinuity

/-- The complete actual coefficient array is continuous in the primitive map
topology, with loss two at every fixed order. Rank and immersion on the open
working ball are derived from the same neighborhood. This supplies the input
to `exists_extendedReducedCoefficients_comparison_radius`
(`app:ch_regular:thm:no-return`). -/
theorem exists_reducedCoefficients_comparison_radius {n : ℕ} (G : FlatReference n)
    {r R : ℝ} (_hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ F : Euclidean n → Euclidean (embeddingDimension n),
      ContDiff ℝ ∞ F → cNorm (closedBall 0 R) (max 8 (m + 2)) (F - G.map) < δ →
      IsImmersionOn F (ball 0 R) ∧ HasFullNormalRankOn F (ball 0 R) ∧
      cNorm (closedBall 0 r) m
        (geometricReducedCoefficients F - geometricReducedCoefficients G.map) < ε := by
  obtain ⟨djet, hdjet, L, hL, hu, hjet⟩ := exists_image_coefficient_jet_neighborhood G hR
  obtain ⟨dgeo, hdgeo, κ, _hκ, hgeo⟩ := exists_stress_neighborhood G hrR hR zero_lt_one
  have hGrange : MapsTo (stressJet G.map) (closedBall 0 r) L := by
    intro x hx
    apply hjet G.map G.contDiff (by simpa only [sub_self, cNorm_zero] using hdjet)
    exact closedBall_subset_closedBall hrR.le hx
  have hcoeff : ∀ J ∈ L, ContDiffAt ℝ m (@ambientReducedCoefficients n (embeddingDimension n)) J :=
    fun J hJ ↦ (contDiffAt_ambientReducedCoefficients (hu J hJ).1 (hu J hJ).2).of_le (by simp)
  obtain ⟨dcomp, hdcomp, hcomp⟩ := exists_cNorm_comp_sub_lt
    (isCompact_closedBall (0 : Euclidean n) r) hL hcoeff
    (fun _ _ ↦ (contDiff_stressJet G.contDiff).contDiffAt.of_le (by simp)) hGrange hε
  refine ⟨min djet (min dgeo (dcomp / 2)),
    lt_min hdjet (lt_min hdgeo (half_pos hdcomp)), ?_⟩
  intro F hF hclose
  have h8 : cNorm (closedBall (0 : Euclidean n) R) 8 (F - G.map) ≤
      cNorm (closedBall 0 R) (max 8 (m + 2)) (F - G.map) :=
    cNorm_mono_order (le_max_left _ _)
  have hFL := hjet F hF (h8.trans_lt (hclose.trans_le (min_le_left _ _)))
  obtain ⟨hi, hrank, _hgap, _hsmooth, _hcomp⟩ := hgeo univ F isOpen_univ (subset_univ _)
    hF.contDiffOn (h8.trans_lt (hclose.trans_le ((min_le_right _ _).trans (min_le_left _ _))))
  have hdiff : cNorm (closedBall (0 : Euclidean n) r) m
      (stressJet F - stressJet G.map) < dcomp := by
    have h1 := cNorm_stressJet_sub_le (isCompact_closedBall (0 : Euclidean n) r)
      isOpen_univ (subset_univ _) hF.contDiffOn G.contDiff.contDiffOn m
    have h2 : cNorm (closedBall (0 : Euclidean n) r) (m + 2) (F - G.map) ≤
        cNorm (closedBall 0 R) (max 8 (m + 2)) (F - G.map) :=
      (cNorm_mono_set_of_contDiffAt (closedBall_subset_closedBall hrR.le)
        (isCompact_closedBall (0 : Euclidean n) R)
        (fun _ _ ↦ (hF.sub G.contDiff).contDiffAt.of_le (by simp))).trans
          (cNorm_mono_order (le_max_right _ _))
    have hc := hclose.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  have hc := hcomp ambientReducedCoefficients (stressJet F) hcoeff
    (fun _ _ ↦ (contDiff_stressJet hF).contDiffAt.of_le (by simp))
    (fun x hx ↦ hFL (closedBall_subset_closedBall hrR.le hx))
    (by simpa only [sub_self, cNorm_zero] using hdcomp) hdiff
  refine ⟨hi, hrank, ?_⟩
  have heq : cNorm (closedBall (0 : Euclidean n) r) m
      (ambientReducedCoefficients ∘ stressJet F - ambientReducedCoefficients ∘ stressJet G.map) =
      cNorm (closedBall 0 r) m
        (geometricReducedCoefficients F - geometricReducedCoefficients G.map) := by
    apply cNorm_eq_of_eventuallyEq _ m
    intro x hx
    exact (ambientReducedCoefficients_eventuallyEq hF isOpen_ball hi hrank
      (closedBall_subset_ball hrR hx)).sub
        (ambientReducedCoefficients_eventuallyEq G.contDiff isOpen_ball
          (fun y _ ↦ reference_isImmersion G y)
          (fun y hy ↦ G.fullNormalRank y (ball_subset_ball hR.le hy))
          (closedBall_subset_ball hrR hx))
  rwa [heq] at hc

/-- Backgrounds cancel from the difference of the two literal affine
extensions. This identity retains the same fixed Seeley operator
(`app:ch_regular:eq:coefficient-extension`). -/
theorem extendedReducedCoefficients_sub_eq {n N : ℕ}
    (p : BallExtension.Parameters (Euclidean n))
    (Z₀ : Euclidean n → Fin n × Fin n → ℝ)
    (F G : Euclidean n → Euclidean N) :
    extendedReducedCoefficients p Z₀ F - extendedReducedCoefficients p Z₀ G =
      p.seeleyExtension (geometricReducedCoefficients F - geometricReducedCoefficients G) := by
  simp only [extendedReducedCoefficients, map_sub]
  abel

/-- A primitive finite-order neighborhood of the reference controls the full
extended coefficient array globally. In particular the lower-order entries
need no separate current-coefficient hypothesis. The single extension and its
background are fixed before the requested tolerance and current map
(`app:ch_regular:thm:no-return`). -/
theorem exists_extendedReducedCoefficients_comparison_radius {n : ℕ} (G : FlatReference n)
    (p : BallExtension.Parameters (Euclidean n)) (hp0 : p.center = 0)
    {R : ℝ} (hpR : p.radius < R) (hR : R < G.domain.chartRadius)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ F : Euclidean n → Euclidean (embeddingDimension n),
      ContDiff ℝ ∞ F → cNorm (closedBall 0 R) (max 8 (m + 2)) (F - G.map) < δ →
      IsImmersionOn F (ball 0 R) ∧ HasFullNormalRankOn F (ball 0 R) ∧
      ∀ Z₀ : Euclidean n → Fin n × Fin n → ℝ,
        cNorm univ m (extendedReducedCoefficients p Z₀ F -
          extendedReducedCoefficients p Z₀ G.map) < ε := by
  obtain ⟨A, hA, hbound⟩ := exists_cNorm_vector_seeleyExtension_le
    (F := ReducedCoefficientIndex n → ℝ) p m
  obtain ⟨δ, hδ, hnear⟩ := exists_reducedCoefficients_comparison_radius G
    p.radius_pos hpR hR m (div_pos hε hA)
  refine ⟨δ, hδ, ?_⟩
  intro F hF hsmall
  obtain ⟨hi, hrank, hclose⟩ := hnear F hF hsmall
  refine ⟨hi, hrank, ?_⟩
  intro Z₀
  rw [extendedReducedCoefficients_sub_eq]
  have hlocal : ∀ x ∈ closedBall p.center p.radius, ContDiffAt ℝ ∞
      (geometricReducedCoefficients F - geometricReducedCoefficients G.map) x := by
    intro x hx
    have hxR : x ∈ ball (0 : Euclidean n) R := closedBall_subset_ball hpR (hp0 ▸ hx)
    exact ((contDiffOn_geometricReducedCoefficients hF isOpen_ball hi hrank).contDiffAt
      (isOpen_ball.mem_nhds hxR)).sub
      ((contDiffOn_geometricReducedCoefficients G.contDiff isOpen_ball
        (fun y _ ↦ reference_isImmersion G y)
        (fun y hy ↦ G.fullNormalRank y (ball_subset_ball hR.le hy))).contDiffAt
          (isOpen_ball.mem_nhds hxR))
  have he := hbound _ hlocal
  rw [hp0] at he
  exact he.trans_lt ((mul_lt_mul_of_pos_left hclose hA).trans_eq (mul_div_cancel₀ ε hA.ne'))

/-- The frozen low-class margin and primitive map closeness put the complete
actual extension in the prescribed low class. Only the fixed reference array
is compared to the chosen cube background; the current array comparison is
derived above. The reference margin precedes the reference itself and is
discharged by `exists_reference_frame_extension_low_class` from the constructed
background and the primitive reference frame margin
(`app:ch_regular:thm:no-return`). -/
theorem exists_extendedReducedCoefficients_low_neighborhood {n : ℕ}
    (p : BallExtension.Parameters (Euclidean n)) (hp0 : p.center = 0)
    {R : ℝ} (hpR : p.radius < R) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > (0 : ℝ), ∀ G : FlatReference n, R < G.domain.chartRadius →
      ∃ δ > (0 : ℝ),
      ∀ (Z₀ : Euclidean n → Fin n × Fin n → ℝ), ContDiff ℝ ∞ Z₀ →
        cNorm (closedBall 0 p.radius) m
          (geometricReducedCoefficients G.map - reducedCoefficientBackground Z₀) < η →
        ∀ F : Euclidean n → Euclidean (embeddingDimension n), ContDiff ℝ ∞ F →
          cNorm (closedBall 0 R) (max 8 (m + 2)) (F - G.map) < δ →
          IsImmersionOn F (ball 0 R) ∧ HasFullNormalRankOn F (ball 0 R) ∧
          ContDiff ℝ ∞ (extendedReducedCoefficients p Z₀ F) ∧
          cNorm univ m
            (extendedReducedCoefficients p Z₀ F - reducedCoefficientBackground Z₀) < ε := by
  obtain ⟨A, hA, hbound⟩ := exists_cNorm_vector_seeleyExtension_le
    (F := ReducedCoefficientIndex n → ℝ) p m
  let η : ℝ := ε / (2 * A)
  have hη : 0 < η := div_pos hε (by positivity)
  refine ⟨η, hη, ?_⟩
  intro G hR
  obtain ⟨δ, hδ, hnear⟩ := exists_reducedCoefficients_comparison_radius G
    p.radius_pos hpR hR m hη
  refine ⟨δ, hδ, ?_⟩
  intro Z₀ hZ₀ href F hF hsmall
  obtain ⟨hi, hrank, hclose⟩ := hnear F hF hsmall
  have hpU : closedBall p.center p.radius ⊆ ball (0 : Euclidean n) R := by
    rw [hp0]
    exact closedBall_subset_ball hpR
  have hcurrent := contDiffOn_geometricReducedCoefficients hF isOpen_ball hi hrank
  have hreference := contDiffOn_geometricReducedCoefficients G.contDiff isOpen_ball
    (fun y _ ↦ reference_isImmersion G y)
    (fun y hy ↦ G.fullNormalRank y (ball_subset_ball hR.le hy))
  have h₀ := contDiff_reducedCoefficientBackground hZ₀
  have hlocal : ∀ x ∈ closedBall p.center p.radius, ContDiffAt ℝ ∞
      (geometricReducedCoefficients F - reducedCoefficientBackground Z₀) x :=
    fun x hx ↦ (hcurrent.contDiffAt (isOpen_ball.mem_nhds (hpU hx))).sub h₀.contDiffAt
  refine ⟨hi, hrank, contDiff_extendedReducedCoefficients p Z₀ hZ₀ hF isOpen_ball hi hrank hpU, ?_⟩
  have htri := cNorm_add_le_of_contDiffAt (isCompact_closedBall (0 : Euclidean n) p.radius)
    (r := m)
    (f := geometricReducedCoefficients F - geometricReducedCoefficients G.map)
    (g := geometricReducedCoefficients G.map - reducedCoefficientBackground Z₀)
    (fun x hx ↦ ((hcurrent.contDiffAt (isOpen_ball.mem_nhds (closedBall_subset_ball hpR hx))).sub
      (hreference.contDiffAt (isOpen_ball.mem_nhds (closedBall_subset_ball hpR hx)))).of_le (by simp))
    (fun x hx ↦ ((hreference.contDiffAt (isOpen_ball.mem_nhds (closedBall_subset_ball hpR hx))).sub
      h₀.contDiffAt).of_le (by simp))
  rw [sub_add_sub_cancel] at htri
  have htotal : cNorm (closedBall (0 : Euclidean n) p.radius) m
      (geometricReducedCoefficients F - reducedCoefficientBackground Z₀) < ε / A := by
    have hηeq : 2 * η = ε / A := by dsimp [η]; ring
    linarith
  have he := hbound _ hlocal
  rw [hp0] at he
  change cNorm univ m (reducedCoefficientBackground Z₀ +
    p.seeleyExtension (geometricReducedCoefficients F - reducedCoefficientBackground Z₀) -
      reducedCoefficientBackground Z₀) < ε
  rw [add_sub_cancel_left]
  exact he.trans_lt ((mul_lt_mul_of_pos_left htotal hA).trans_eq (mul_div_cancel₀ ε hA.ne'))

end JanetCartan.ProtectedFlow
