module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.CurrentFullPhase.LocalFamily

/-!
# Inverse comparison for the retained Hamilton family

Consumer: `exists_localQuantitativeFamily_with_transverse_control`, which
discharges all geometric premises below using the actual frame constructor.
The only remaining comparison is the forward Hamilton projection difference.
This is the inverse-equation step of `app:lem:common-hamilton-phase`, consumed
by `app:ch_osc:prop:osc-normal`, Step 4'.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference
open HamiltonPhase ActualCarriers CurrentFullPhase FrozenMenu FrozenPhaseReference

/-- At any fixed member, forward projection differences control the SAME
retained inverse coordinates and phase. The actual producer
`exists_localQuantitativeFamily_with_transverse_control` supplies the source
buffer, half gap and forward smoothness. Restriction changes only the target
set, never the coordinates (`app:lem:common-hamilton-phase`). -/
theorem exists_retained_coordinates_phase_sub_tolerance {n : ℕ} {ξ : Euclidean n}
    {a : AdaptedSection ξ} {N : LocalFrozenReference a}
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (L : LocalQuantitativeFamily N U hU)
    (A : (ℝ × InitialData (Euclidean (n - 1))) ≃L[ℝ]
      (Euclidean n × (ℝ × Euclidean (n - 1))))
    (hbuffer : ∀ Q, (L.chart Q).source ⊆
      ball ((0 : ℝ), a.baseData) (2 * L.sourceRadius))
    (hgap : ∀ Q, ∀ q ∈ ball ((0 : ℝ), a.baseData) (3 * L.sourceRadius),
      ‖(A.symm : _ →L[ℝ] _).comp (fderiv ℝ (L.flow Q).augmentedProjection q) -
        ContinuousLinearMap.id ℝ _‖ ≤ 1 / 2)
    (hposition : ∀ Q, ContDiffOn ℝ ∞ (L.flow Q).position
      ((L.flow Q).time ×ˢ (L.flow Q).parameters))
    (Q₀ : _) {K : Set (Euclidean n × (ℝ × Euclidean (n - 1)))}
    (hK : IsCompact K)
    (hKV : K ⊆ ball (a.embedding a.baseData.1, a.baseData.2) (2 * L.radius))
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ d > (0 : ℝ), ∀ Q,
      cNorm (closedBall ((0 : ℝ), a.baseData) (2 * L.sourceRadius)) m
        ((L.flow Q).augmentedProjection - (L.flow Q₀).augmentedProjection) < d →
      cNorm K m ((L.chart Q).coordinates - (L.chart Q₀).coordinates) +
        cNorm K m (phase (L.chart Q).coordinates - phase (L.chart Q₀).coordinates) < ε := by
  let V := ball (a.embedding a.baseData.1, a.baseData.2) (2 * L.radius)
  let C (Q : _) := restrictChart (L.chart Q) isOpen_ball (L.target_contains Q)
  have hforward (Q : _) : ContDiffOn ℝ ∞ (L.flow Q).augmentedProjection
      (ball ((0 : ℝ), a.baseData) (3 * L.sourceRadius)) :=
    ((hposition Q).mono (L.source_admissible Q)).prodMk contDiffOn_snd.snd
  have hrange (Q : _) : MapsTo (chartLift (C Q).coordinates) K
      (ball ((0 : ℝ), a.baseData) (2 * L.sourceRadius)) := by
    intro z hz
    exact hbuffer Q ((L.chart Q).maps_to_source z (L.target_contains Q (hKV hz)))
  obtain ⟨B, hB, hphase⟩ := exists_phase_finiteOrder_bound hK m
  have he : 0 < ε / (1 + B) := div_pos hε (by linarith)
  obtain ⟨d, hd, hinverse⟩ := (C Q₀).exists_coordinates_finiteOrder_continuity
    ((0 : ℝ), a.baseData) L.sourceRadius_pos hK isOpen_ball hKV (Subset.refl V)
    (hforward Q₀) (L.coordinates_smooth Q₀) A (hrange Q₀) m he
  refine ⟨d, hd, ?_⟩
  intro Q hsmall
  have hi := hinverse (normalizedHomogeneousSymbol hU Q.1 Q.2.1) (L.flow Q) (C Q)
    (Subset.refl V) (hforward Q) (L.coordinates_smooth Q) (hrange Q) (hgap Q) hsmall
  have hc : cNorm K m ((L.chart Q).coordinates - (L.chart Q₀).coordinates) <
      ε / (1 + B) := by
    change cNorm K m (chartLift (L.chart Q).coordinates - chartLift (L.chart Q₀).coordinates) +
      cNorm K m ((L.chart Q).coordinates - (L.chart Q₀).coordinates) < ε / (1 + B) at hi
    linarith [cNorm_nonneg K m
      (chartLift (L.chart Q).coordinates - chartLift (L.chart Q₀).coordinates)]
  have hs := hphase V (L.chart Q).coordinates (L.chart Q₀).coordinates isOpen_ball hKV
    ((L.coordinates_smooth Q).of_le (by simp)) ((L.coordinates_smooth Q₀).of_le (by simp))
  have hs' : cNorm K m (phase (L.chart Q).coordinates - phase (L.chart Q₀).coordinates) ≤
      B * cNorm K m ((L.chart Q).coordinates - (L.chart Q₀).coordinates) := by
    convert! hs using 1
  have hmul := (lt_div_iff₀ (show 0 < 1 + B by linarith)).mp hc
  nlinarith only [hs', hmul]

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference
