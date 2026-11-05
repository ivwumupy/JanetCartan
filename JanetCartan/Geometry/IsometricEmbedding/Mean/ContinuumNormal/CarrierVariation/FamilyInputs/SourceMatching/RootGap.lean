module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching.Hamilton

/-!
# A primitive frame threshold for source-chart branch matching

`exists_transverse_localFrozenReference_in_physical_ball` produces the fixed
frozen gap used here. The scalar-symbol comparison producer converts a `C⁶`
frame neighborhood to a gap for the actual seed. This discharges the branch
input of `projected_current_chart_source_dilation` without an assumption about
any chosen root, phase, or trajectory.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching
open HamiltonPhase ActualCarriers CurrentFullPhase FrozenPhaseReference

/-- The fixed frozen transverse gap yields a primitive `C⁶` frame threshold
for the seed root band, before scale, density, and history. The state ball is
exactly the retained ball, with no unproved shrinking of trajectories.
Source: `app:lem:common-hamilton-phase`, `app:ch_background:eq:bg-Nsigma`.
Consumer: the `htrans` input of `projected_current_chart_source_dilation`. -/
theorem exists_retained_seed_transverse_threshold
    {n : ℕ} {P : FrozenMenu.Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    {c : ℝ} (hc : 0 < c)
    (hgap : ∀ z ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      c ≤ |⟪(frozenSymbol n).hp z, T.data.adapted.normal⟫_ℝ|) :
    ∃ δ > (0 : ℝ), ∀ Q : {Q : Euclidean n → Fin n → MetricTensor n //
        ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold},
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ →
      ∀ z ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
        c / 2 ≤ |⟪(normalizedHomogeneousSymbol hU Q.1 Q.2.1).hp z,
          T.data.adapted.normal⟫_ℝ| ∧
        ⟪(normalizedHomogeneousSymbol hU Q.1 Q.2.1).hp z, T.data.adapted.normal⟫_ℝ ≠ 0 := by
  have hzero : ∀ p ∈ closedBall T.data.center T.data.localReference.stateRadius, p ≠ 0 := by
    intro p hp
    apply (mem_frozenSymbol_domain (0, p)).mp
    apply T.data.localReference.state_subset
    apply T.data.localReference.stateBall_subset
    simpa only [T.data.adapted.baseState_eq, mem_closedBall, Prod.dist_eq,
      dist_self, max_eq_right (dist_nonneg)] using hp
  obtain ⟨δ, hδ, hclose⟩ := NormalizedSymbolBounds.exists_cube_symbol_C3_C6_comparison_radius
    (0, T.data.center) T.data.localReference.stateRadius_pos hzero
    (half_pos hc) (by norm_num : (0 : ℝ) < 1)
  refine ⟨δ, hδ, fun Q hQ z hz ↦ ?_⟩
  have hsub : normalizedSymbolDomain U ⊆ (frozenSymbol n).domain :=
    fun q hq ↦ (mem_frozenSymbol_domain q).mpr hq.2
  have hsmall := (hclose U hU hphysical Q.1 Q.2.1 hQ).1.le
  have hhalf := normal_velocity_half_gap_of_cNorm_three
    (normalizedHomogeneousSymbol hU Q.1 Q.2.1) (frozenSymbol n)
    (isOpen_normalizedSymbolDomain hU) Subset.rfl hsub
    ((contDiffOn_normalizedSymbol hU Q.2.1).of_le (by simp))
    (((frozenSymbol_smooth n).mono hsub).of_le (by simp))
    (isCompact_closedBall _ _) (retained_stateBall_subset T Q hphysical)
    T.data.adapted.normal T.data.adapted.normal_unit hgap hsmall z hz
  refine ⟨hhalf, ?_⟩
  exact abs_pos.mp ((half_pos hc).trans_le hhalf)

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching
