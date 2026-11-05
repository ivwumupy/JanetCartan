module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame

/-! # Uniform normal gaps on compact admissible jet sets

The ambient inverse realizes the varying normal spaces in
`app:ch_seed:setup:seed-current`; no identification of those spaces is assumed.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius Topology
open JanetCartan.ProjectedStressFrame JanetCartan.AmbientResponse
namespace JanetCartan.CurrentGeometricNeighborhood

/-- Ambient invertibility implies full actual normal rank, by projecting the
ambient inverse equation (`app:ch_seed:setup:seed-current`). -/
theorem normal_rank_of_ambient_isUnit {n N : ℕ} {F : Euclidean n → Euclidean N}
    {x : Euclidean n} (hu : IsUnit (ambientNormalOperator F x)) :
    Set.range (normalMap F x) = (normalSpace F x : Set (Euclidean N)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨H, rfl⟩
    exact normalMap_mem_normalSpace F x H
  · intro w hw
    let z := Ring.inverse (ambientNormalOperator F x) w
    have he : ambientNormalOperator F x z = w :=
      congrArg (fun T : Euclidean N →L[ℝ] Euclidean N ↦ T w)
        (Ring.mul_inverse_cancel _ hu)
    refine ⟨normalPairing F (fun _ ↦ z) x, ?_⟩
    have hp := congrArg (normalProjection F x) he
    simpa only [ambientNormalOperator_apply, map_add, normalProjection_normalMap,
      normalProjection_tangentProjection, add_zero,
      normalProjection_eq_self_of_mem_normalSpace hw] using hp

/-- A compact set in both unit loci supplies a single positive gap for the
actual normal pairing of every map whose jet lies there. This is the normal
gap prerequisite of `app:ch_seed:setup:seed-current`. -/
theorem exists_normal_gap_of_compact_jets {n N : ℕ} {L : Set (StressJet n N)}
    (hL : IsCompact L)
    (hunit : ∀ J ∈ L, IsUnit (jetMetric J) ∧ IsUnit (jetAmbient J)) :
    ∃ κ > 0, ∀ (F : Euclidean n → Euclidean N) (x : Euclidean n),
      ContDiffAt ℝ 2 F x → Function.Injective (fderiv ℝ F x) → stressJet F x ∈ L →
      ∀ w ∈ normalSpace F x, κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖ := by
  have hi : ContinuousOn (fun J : StressJet n N ↦ Ring.inverse (jetAmbient J)) L := by
    intro J hJ
    have h := (hunit J hJ).2
    have hc : ContDiffAt ℝ ∞ Ring.inverse (jetAmbient J) := by
      simpa only [IsUnit.unit_spec] using contDiffAt_ringInverse ℝ h.unit
    exact (hc.comp J (contDiffAt_jetAmbient (hunit J hJ).1)).continuousAt.continuousWithinAt
  obtain ⟨A, hA⟩ := hL.exists_bound_of_continuousOn hi
  obtain ⟨B, hB⟩ := hL.exists_bound_of_continuousOn
    (fun J hJ ↦ (contDiffAt_jetNormalMap (hunit J hJ).1).continuousAt.continuousWithinAt)
  let C := (max A 0 + 1) * (max B 0 + 1)
  have hC : 0 < C := mul_pos (by positivity) (by positivity)
  refine ⟨C⁻¹, inv_pos.mpr hC, ?_⟩
  intro F x hF himm hjet w hw
  have hu := (hunit _ hjet).2
  have he : Ring.inverse (jetAmbient (stressJet F x))
      (jetAmbient (stressJet F x) w) = w :=
    congrArg (fun T : Euclidean N →L[ℝ] Euclidean N ↦ T w)
      (Ring.inverse_mul_cancel _ hu)
  have heA : jetAmbient (stressJet F x) w =
      jetNormalMap (stressJet F x) (normalPairing F (fun _ ↦ w) x) := by
    rw [jetAmbient_stressJet hF himm, ambientNormalOperator_apply,
      tangentProjection_eq_zero_of_mem_normalSpace hw, add_zero,
      jetNormalMap_stressJet hF himm]
    rfl
  have hbound : ‖w‖ ≤ C * ‖normalPairing F (fun _ ↦ w) x‖ := by
    calc
      ‖w‖ = ‖Ring.inverse (jetAmbient (stressJet F x))
          (jetAmbient (stressJet F x) w)‖ := congrArg norm he.symm
      _ ≤ ‖Ring.inverse (jetAmbient (stressJet F x))‖ *
          ‖jetAmbient (stressJet F x) w‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (max A 0 + 1) * ‖jetAmbient (stressJet F x) w‖ := by
        gcongr
        exact (hA _ hjet).trans (by linarith [le_max_left A 0])
      _ ≤ (max A 0 + 1) * ((max B 0 + 1) * ‖normalPairing F (fun _ ↦ w) x‖) := by
        gcongr
        rw [heA]
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right ((hB _ hjet).trans (by linarith [le_max_left B 0]))
            (norm_nonneg _))
      _ = _ := by dsimp [C]; ring
  exact (inv_mul_le_iff₀ hC).mpr hbound

end JanetCartan.CurrentGeometricNeighborhood
