module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading.HamiltonComparison.LowOrder
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

/-!
# Retained inverse comparison on the original target

For `app:lem:common-hamilton-phase`, the original source half gap transfers
the direct root/ODE comparison to the same inverse coordinates on their
entire original target. The order-zero estimate also gives a common compact
source buffer for any prescribed compact target, without shrinking that target.
The consumer is the higher-order Hamilton comparison required by
`RetainedLeading.exists_originalScalar_primitives_sub_tolerance`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading
open HamiltonPhase ActualCarriers CurrentFullPhase FrozenMenu FrozenPhaseReference

variable {n : ℕ} {ξ : Euclidean n} {a : AdaptedSection ξ} {N : LocalFrozenReference a}
  {U : Set (Euclidean n)} {hU : IsOpen U}
  (hdomain : ∀ z ∈ N.stateDomain, z.1 ∈ U)
  (L : LocalQuantitativeFamily N U hU) {R : ℝ} (hR : 0 < R)
  (hRN : R < N.stateRadius)
  (A : (ℝ × InitialData (Euclidean (n - 1))) ≃L[ℝ]
    (Euclidean n × (ℝ × Euclidean (n - 1))))
  (hhalf : ∀ Q, ∀ q ∈ ball ((0 : ℝ), a.baseData) (3 * L.sourceRadius),
    ‖(A.symm : _ →L[ℝ] _).comp (fderiv ℝ (L.flow Q).augmentedProjection q) -
      ContinuousLinearMap.id ℝ _‖ ≤ 1 / 2)
  (hrange : ∀ Q, ∀ q ∈ (L.flow Q).time ×ˢ (L.flow Q).parameters,
    ((L.flow Q).position q, (L.flow Q).momentum q) ∈ closedBall (0, ξ) R)
  (Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) N.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < L.threshold})
  (hgap₀ : ∀ z ∈ closedBall (0, ξ) R,
    ⟪(normalizedHomogeneousSymbol hU Q₀.1 Q₀.2.1).hp z, a.normal⟫_ℝ ≠ 0)

include hdomain hR hRN hhalf hrange hgap₀

/-- Uniform comparison of the SAME retained inverse coordinates on the whole
original target from the scalar order-one symbol difference. The half gap and
state range are exactly those retained by the producer; no inverse-coordinate
continuity or smaller-target containment is assumed
(`app:lem:common-hamilton-phase`). -/
theorem exists_retained_coordinates_sub_le_symbol :
    ∃ B > (0 : ℝ), ∀ Q,
      ∀ z ∈ ball (a.embedding a.baseData.1, a.baseData.2) (2 * L.radius),
        ‖(L.chart Q).coordinates z - (L.chart Q₀).coordinates z‖ ≤
          B * cNorm (closedBall (0, ξ) N.stateRadius) 1
            (normalizedSymbol Q.1 - normalizedSymbol Q₀.1) := by
  obtain ⟨B, hB, hstate⟩ := exists_retained_state_sub_le_symbol
    hdomain L hR hRN hrange Q₀ hgap₀
  let C := 2 * ‖(A.symm : (Euclidean n × (ℝ × Euclidean (n - 1))) →L[ℝ]
    (ℝ × InitialData (Euclidean (n - 1))))‖ * B
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C + 1, by positivity, ?_⟩
  intro Q z hz
  have hsource (Q : _) : (L.chart Q).source ⊆
      ball ((0 : ℝ), a.baseData) (3 * L.sourceRadius) := by
    rw [L.source_eq]; exact inter_subset_left
  have hprojection (q) (hq : q ∈ ball ((0 : ℝ), a.baseData) (3 * L.sourceRadius)) :
      ‖(L.flow Q).augmentedProjection q - (L.flow Q₀).augmentedProjection q‖ ≤
        B * cNorm (closedBall (0, ξ) N.stateRadius) 1
          (normalizedSymbol Q.1 - normalizedSymbol Q₀.1) := by
    have hp := (norm_fst_le (((L.flow Q).position q, (L.flow Q).momentum q) -
      ((L.flow Q₀).position q, (L.flow Q₀).momentum q))).trans (hstate Q q hq)
    simpa only [HamiltonFlow.augmentedProjection, Prod.mk_sub_mk, sub_self,
      Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)] using hp
  have hh := (L.chart Q).norm_coordinates_sub_le_of_projection_close (L.chart Q₀)
    (convex_ball _ _) A (L.source_admissible Q) (hhalf Q) hprojection
    (L.target_contains Q hz) (L.target_contains Q₀ hz)
    (hsource Q ((L.chart Q).maps_to_source z (L.target_contains Q hz)))
    (hsource Q₀ ((L.chart Q₀).maps_to_source z (L.target_contains Q₀ hz)))
  have he := cNorm_nonneg (closedBall (0, ξ) N.stateRadius) 1
    (normalizedSymbol Q.1 - normalizedSymbol Q₀.1)
  change _ ≤ (C + 1) * _
  dsimp only [C]
  nlinarith only [hh, he]

/-- Order-zero coordinate and phase comparison on any prescribed compact in
the ORIGINAL retained target. This proves the base case of
`app:lem:common-hamilton-phase` on that compact; higher derivative orders are
a separate obligation. The input is the scalar order-one difference. -/
theorem exists_retained_coordinates_phase_zero_tolerance
    {J : Set (Euclidean n × (ℝ × Euclidean (n - 1)))}
    (hJ : IsCompact J)
    (hJT : J ⊆ ball (a.embedding a.baseData.1, a.baseData.2) (2 * L.radius))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ Q,
      cNorm (closedBall (0, ξ) N.stateRadius) 1
        (normalizedSymbol Q.1 - normalizedSymbol Q₀.1) < δ →
      cNorm J 0 ((L.chart Q).coordinates - (L.chart Q₀).coordinates) +
        cNorm J 0 (phase (L.chart Q).coordinates - phase (L.chart Q₀).coordinates) < ε := by
  obtain ⟨B, hB, hb⟩ := exists_retained_coordinates_sub_le_symbol
    hdomain L hR hRN A hhalf hrange Q₀ hgap₀
  obtain ⟨D, hD, hd⟩ := exists_phase_finiteOrder_bound hJ 0
  have hBD : 0 < (1 + D) * B := mul_pos (by linarith) hB
  refine ⟨ε / ((1 + D) * B), div_pos hε hBD, ?_⟩
  intro Q hsmall
  have hc : cNorm J 0 ((L.chart Q).coordinates - (L.chart Q₀).coordinates) ≤
      B * cNorm (closedBall (0, ξ) N.stateRadius) 1
        (normalizedSymbol Q.1 - normalizedSymbol Q₀.1) := by
    apply (cNorm_le_sum_of_bounds (C := fun _ ↦ B * cNorm
      (closedBall (0, ξ) N.stateRadius) 1 (normalizedSymbol Q.1 - normalizedSymbol Q₀.1))
      (fun _ _ ↦ mul_nonneg hB.le (cNorm_nonneg _ _ _)) ?_).trans_eq (by simp)
    intro j hj z hz
    have hj₀ : j = 0 := by omega
    subst j
    simpa only [norm_iteratedFDeriv_zero, Pi.sub_apply] using hb Q z (hJT hz)
  have hs := hd _ (L.chart Q).coordinates (L.chart Q₀).coordinates
    isOpen_ball hJT ((L.coordinates_smooth Q).of_le (by simp))
      ((L.coordinates_smooth Q₀).of_le (by simp))
  have hs' : cNorm J 0 (phase (L.chart Q).coordinates - phase (L.chart Q₀).coordinates) ≤
      D * cNorm J 0 ((L.chart Q).coordinates - (L.chart Q₀).coordinates) := by
    convert! hs using 1
  have ht := (lt_div_iff₀ hBD).mp hsmall
  nlinarith

/-- A prescribed compact in the original target has a common compact source
buffer for all sufficiently close admitted symbols. The radius bounds the
actual inverse lifts strictly inside the ORIGINAL source ball, and is chosen
without reducing the prescribed target compact. This discharges the source
range prerequisite for its differentiated inverse comparison
(`app:lem:common-hamilton-phase`). -/
theorem exists_retained_originalTarget_source_buffer
    {J : Set (Euclidean n × (ℝ × Euclidean (n - 1)))}
    (hJ : IsCompact J)
    (hJT : J ⊆ ball (a.embedding a.baseData.1, a.baseData.2) (2 * L.radius)) :
    ∃ r δ : ℝ, 0 < r ∧ r < 3 * L.sourceRadius ∧ 0 < δ ∧
      ∀ Q, cNorm (closedBall (0, ξ) N.stateRadius) 1
        (normalizedSymbol Q.1 - normalizedSymbol Q₀.1) < δ →
        MapsTo (chartLift (L.chart Q).coordinates) J
          (ball ((0 : ℝ), a.baseData) r) := by
  obtain ⟨B, hB, hb⟩ := exists_retained_coordinates_sub_le_symbol
    hdomain L hR hRN A hhalf hrange Q₀ hgap₀
  have hlift₀ : ContDiffOn ℝ ∞ (chartLift (L.chart Q₀).coordinates)
      (ball (a.embedding a.baseData.1, a.baseData.2) (2 * L.radius)) :=
    (L.coordinates_smooth Q₀).fst.prodMk
      ((L.coordinates_smooth Q₀).snd.prodMk contDiffOn_snd)
  have hcompact : IsCompact (chartLift (L.chart Q₀).coordinates '' J) :=
    hJ.image_of_continuousOn (hlift₀.continuousOn.mono hJT)
  have hsource : chartLift (L.chart Q₀).coordinates '' J ⊆
      ball ((0 : ℝ), a.baseData) (3 * L.sourceRadius) := by
    rintro _ ⟨z, hz, rfl⟩
    have hh := (L.chart Q₀).maps_to_source z (L.target_contains Q₀ (hJT hz))
    rw [L.source_eq] at hh
    exact hh.1
  obtain ⟨r₀, hr₀, hJr₀⟩ := exists_pos_lt_subset_ball
    (mul_pos (by norm_num) L.sourceRadius_pos) hcompact.isClosed hsource
  let r := (r₀ + 3 * L.sourceRadius) / 2
  have hrr₀ : r₀ < r := by dsimp [r]; linarith [hr₀.2]
  have hr : r < 3 * L.sourceRadius := by dsimp [r]; linarith [hr₀.2]
  refine ⟨r, (r - r₀) / B, hr₀.1.trans hrr₀, hr,
    div_pos (sub_pos.mpr hrr₀) hB, ?_⟩
  intro Q hsmall z hz
  have hd : dist (chartLift (L.chart Q).coordinates z)
      (chartLift (L.chart Q₀).coordinates z) < r - r₀ := by
    have he : dist (chartLift (L.chart Q).coordinates z)
        (chartLift (L.chart Q₀).coordinates z) =
        ‖(L.chart Q).coordinates z - (L.chart Q₀).coordinates z‖ := by
      simp [dist_eq_norm, chartLift, Prod.norm_def]
    rw [he]
    apply (hb Q z (hJT hz)).trans_lt
    have hh := (lt_div_iff₀ hB).mp hsmall
    linarith
  have h₀ := hJr₀ (mem_image_of_mem _ hz)
  have ht := dist_triangle (chartLift (L.chart Q).coordinates z)
    (chartLift (L.chart Q₀).coordinates z) ((0 : ℝ), a.baseData)
  change dist _ _ < r
  change dist _ _ < r₀ at h₀
  linarith

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading
