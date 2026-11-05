module

public import JanetCartan.Geometry.IsometricEmbedding.Response.PhaseChoice.ConicGeometry.Phase

/-!
# Uniform annular bounds on the entire selected cone

The two annular estimates required by `ResponseTransfer.reverseSource_gap_uniform`
come from the nonzero frozen Hamilton momentum, compactness of the normalized
buffer, and the actual family's primitive `C⁶` comparison threshold. Positive
homogeneity transfers them to every radius in the full active cone, as required
by the complete-complement paragraph of
`app:ch_response:thm:response-literal-transfer`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff InnerProductSpace Topology Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu FrozenPhaseReference CompatibleResponse

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Positive upper and lower momentum bounds on a compact part of the selected
target, uniformly from a primitive frame threshold. The lower bound uses actual
frozen symbol-domain membership, not a desired annular hypothesis
(`app:ch_response:thm:response-compatible-choice`). -/
theorem exists_compact_sectionEnergy_momentum_bounds
    {K : Set (Euclidean n × (ℝ × Euclidean (n - 1)))}
    (hK : IsCompact K) (hKt : K ⊆ T.target) :
    ∃ a > (0 : ℝ), ∃ b > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ Q,
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ →
      ∀ q ∈ K, a ≤ ‖(T.currentChart Q).chartMomentum q‖ ∧
        ‖(T.currentChart Q).chartMomentum q‖ ≤ b := by
  have hcont := (T.reference.chart.contDiffOn_chartMomentum
    T.reference.momentum_smooth T.reference.coordinates_smooth).continuousOn.mono hKt
  have hnonzero : ∀ q ∈ K, T.reference.chart.chartMomentum q ≠ 0 := by
    intro q hq
    have ha := T.reference.chart.source_admissible _
      (T.reference.chart.maps_to_source q (hKt hq))
    exact (mem_frozenSymbol_domain _).mp (T.reference.flow.state_mem _ ha.1 _ ha.2)
  obtain ⟨g, hg, hgb⟩ := exists_uniform_positive_bound hK hcont.norm
    (fun q hq ↦ norm_pos_iff.mpr (hnonzero q hq))
  obtain ⟨B, hB, hBb⟩ := (hK.image_of_continuousOn hcont).isBounded.exists_pos_norm_le
  obtain ⟨δ, hδ, hcomp⟩ := T.family.exists_momentum_comparison_threshold
    (lt_min (half_pos hg) zero_lt_one)
  refine ⟨g / 2, half_pos hg, B + 1, by linarith, δ, hδ, ?_⟩
  intro Q hQ q hq
  have hc := (hcomp Q hQ q (ball_subset_closedBall (hKt hq))).1
  have hc' : ‖(T.currentChart Q).chartMomentum q -
      T.reference.chart.chartMomentum q‖ < min (g / 2) 1 := hc
  have hlo := norm_le_norm_sub_add (T.reference.chart.chartMomentum q)
    ((T.currentChart Q).chartMomentum q)
  rw [norm_sub_rev] at hlo
  have hhi := norm_le_norm_sub_add ((T.currentChart Q).chartMomentum q)
    (T.reference.chart.chartMomentum q)
  have hgb' := hgb q hq
  have hBb' := hBb _ ⟨q, hq, rfl⟩
  constructor
  · linarith [hc'.trans_le (min_le_left _ _)]
  · linarith [hc'.trans_le (min_le_right _ _)]

set_option maxHeartbeats 800000 in
/-- The continued gradient is the positive multiple of the literal current
momentum at the normalized point
(`app:ch_response:thm:response-literal-transfer`, complete complement). -/
theorem conicSectionEnergyPhase_gradient
    (ℓ : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ) {r : ℝ}
    (hr : r ≤ min T.family.radius (3 * T.family.sourceRadius)) (Q : _)
    {x : Euclidean n} (hx : x ∈ ball 0 T.physicalRadius)
    {η : ℝ × Euclidean (n - 1)} (hη : η ∈ T.sectionEnergyCone ℓ r) :
    gradient (fun y ↦ T.conicSectionEnergyPhase ℓ Q y η) x =
      ℓ η • (T.currentChart Q).chartMomentum (x, (ℓ η)⁻¹ • η) :=
  (T.currentChart Q).gradient_conicPhase ℓ (z := (x, η))
    ⟨hη.1, T.sectionEnergyDomain_subset_target Q hx (ball_subset_ball hr hη.2)⟩

/-- Uniform positive annular bounds at every point and every radius of the
entire buffered active cone. The physical radius and primitive threshold are
chosen before the current frame, frequencies, and samples
(`app:ch_response:thm:response-literal-transfer`, complete complement). -/
theorem exists_conicSectionEnergyPhase_annular_bounds
    (ℓ : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ) {r : ℝ} (hr : 0 < r)
    (hrR : r < min T.family.radius (3 * T.family.sourceRadius)) :
    ∃ ρ > (0 : ℝ), ∃ a > (0 : ℝ), ∃ b > (0 : ℝ), ∃ δ > (0 : ℝ),
      closedBall (0 : Euclidean n) (2 * ρ) ⊆ ball 0 T.physicalRadius ∧
      ∀ Q, cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ →
      ∀ x ∈ closedBall (0 : Euclidean n) (2 * ρ),
      ∀ η ∈ T.sectionEnergyCone ℓ r,
        a * ‖η‖ ≤ ‖gradient (fun y ↦ T.conicSectionEnergyPhase ℓ Q y η) x‖ ∧
        ‖gradient (fun y ↦ T.conicSectionEnergyPhase ℓ Q y η) x‖ ≤ b * ‖η‖ := by
  let ρ := T.physicalRadius / 4
  have hρ : 0 < ρ := div_pos T.physicalRadius_pos (by norm_num)
  have hball : closedBall (0 : Euclidean n) (2 * ρ) ⊆ ball 0 T.physicalRadius :=
    closedBall_subset_ball (by dsimp [ρ]; linarith [T.physicalRadius_pos])
  let K := closedBall (0 : Euclidean n) (2 * ρ) ×ˢ
    closedBall T.data.adapted.baseData.2 r
  have hKt : K ⊆ T.target := by
    rintro ⟨x, η⟩ ⟨hx, hη⟩
    change dist (x, η) (T.data.adapted.embedding T.data.adapted.baseData.1,
      T.data.adapted.baseData.2) < T.family.radius
    rw [Prod.dist_eq, max_lt_iff]
    have hp : T.physicalRadius < T.family.radius := by
      have hh := min_le_left T.family.radius (3 * T.family.sourceRadius)
      have hpos := T.physicalRadius_pos
      dsimp [physicalRadius] at hpos ⊢
      linarith
    exact ⟨by simpa [AdaptedSection.baseData] using (hball hx).trans hp,
      hη.trans_lt (hrR.trans_le (min_le_left _ _))⟩
  obtain ⟨g, hg, B, hB, δ, hδ, hb⟩ := T.exists_compact_sectionEnergy_momentum_bounds
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)) hKt
  let N := ‖T.data.adapted.baseData.2‖ + r
  let d := ‖T.data.adapted.baseData.2‖ - r
  have hN : 0 < N := by dsimp [N]; positivity
  have hd : 0 < d := by
    have hh := hrR.trans_le T.sectionEnergy_radius_le_center_norm
    simpa [d, AdaptedSection.baseData, sub_pos] using hh
  refine ⟨ρ, hρ, g / N, div_pos hg hN, B / d, div_pos hB hd, δ, hδ, hball, ?_⟩
  intro Q hQ x hx η hη
  let ν := (ℓ η)⁻¹ • η
  have hν : ν ∈ closedBall T.data.adapted.baseData.2 r := ball_subset_closedBall hη.2
  have hνupper : ‖ν‖ ≤ N := by
    have hh := norm_le_norm_sub_add ν T.data.adapted.baseData.2
    have hh' : ‖ν - T.data.adapted.baseData.2‖ ≤ r := by
      simpa only [mem_closedBall, dist_eq_norm] using hν
    dsimp [N]
    linarith
  have hνlower : d ≤ ‖ν‖ := by
    have hh := norm_le_norm_sub_add T.data.adapted.baseData.2 ν
    rw [norm_sub_rev] at hh
    have hh' : ‖ν - T.data.adapted.baseData.2‖ ≤ r := by
      simpa only [mem_closedBall, dist_eq_norm] using hν
    dsimp [d]
    linarith
  have hscale : η = ℓ η • ν := (smul_inv_smul₀ hη.1.ne' η).symm
  have hnorm : ‖η‖ = ℓ η * ‖ν‖ := by
    conv_lhs => rw [hscale]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη.1]
  have hb' := hb Q hQ (x, ν) ⟨hx, hν⟩
  rw [T.conicSectionEnergyPhase_gradient ℓ hrR.le Q (hball hx) hη,
    norm_smul, Real.norm_eq_abs, abs_of_pos hη.1, hnorm]
  constructor
  · have hh : (g / N) * ‖ν‖ ≤ g := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hN]
      exact mul_le_mul_of_nonneg_left hνupper hg.le
    nlinarith [mul_le_mul_of_nonneg_left (hh.trans hb'.1) hη.1.le]
  · have hh : B ≤ (B / d) * ‖ν‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hd]
      exact mul_le_mul_of_nonneg_left hνlower hB.le
    nlinarith [mul_le_mul_of_nonneg_left (hb'.2.trans hh) hη.1.le]

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
