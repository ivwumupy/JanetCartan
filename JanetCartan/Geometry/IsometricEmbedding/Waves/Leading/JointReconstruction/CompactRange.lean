module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.JointReconstruction.LocalIdentity
public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.Neighborhood

/-!
# Compact second-jet range from the primitive geometric gaps

For `app:ch_waves:eq:joint-tame`, a fixed second-jet norm bound, metric-energy
bound and normal-pairing bound supply a compact range of immersive, full-normal-
rank jets. The range is chosen before the map or the physical point.

The normal bound is imposed on the first-jet projection of every ambient
vector. This is a closed condition on the closed positive metric-gap locus,
where both the projection and second-jet normal map are continuous. No ambient
inverse estimate or compact containment is assumed.

The consumer is the joint reconstruction estimate in `JointReconstruction`.
Its parent construction supplies the pointwise second-jet norm bound from its
fixed C4 budget and instantiates the primitive gaps from
`CurrentGeometricNeighborhood.exists_geometric_neighborhood`.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
open Set
namespace JanetCartan.LeadingWave.JointReconstruction
open GeometricProfile

/-- The primitive metric-energy gap in `app:ch_seed:setup:seed-current`
forces immersion. This is the continuity-domain input for the compact range
used by `app:ch_waves:eq:joint-tame`. -/
theorem firstJet_injective_of_metricEnergyGap {n N : ℕ}
    {L : Euclidean n →L[ℝ] Euclidean N} {γ : ℝ} (hγ : 0 < γ)
    (hgap : ∀ v, γ * ‖v‖ ^ 2 ≤ ‖L v‖ ^ 2) : Function.Injective L := by
  apply (injective_iff_map_eq_zero L).mpr
  intro v hv
  have h := hgap v
  rw [hv, norm_zero, zero_pow (by omega)] at h
  have hn : ‖v‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖v‖]
  exact norm_eq_zero.mp ((sq_eq_zero_iff).mp hn)

/-- The bounded jet range for `app:ch_waves:eq:joint-tame`, defined only by
the norm bound and the separate primitive gaps. Projecting an arbitrary
ambient vector expresses the normal gap on a fixed domain. -/
def boundedSecondJetGaps (n N : ℕ) (M γ κ : ℝ) :
    Set (SecondJet (Euclidean n) (Euclidean N)) :=
  {J | ‖J‖ ≤ M ∧ (∀ v, γ * ‖v‖ ^ 2 ≤ ‖J.1 v‖ ^ 2) ∧
    ∀ w, κ * ‖firstJetNormalProjection J.1 w‖ ≤
      ‖(secondJetNormalMap J).adjoint (firstJetNormalProjection J.1 w)‖}

/-- The projected normal-pairing gap forces full normal rank on each jet
in the compact range for `app:ch_waves:eq:joint-tame`. The restricted normal
map is surjective because its adjoint has a positive lower bound. -/
theorem secondJetNormalMap_range_of_projected_gap {n N : ℕ}
    {J : SecondJet (Euclidean n) (Euclidean N)} (hi : Function.Injective J.1)
    {κ : ℝ} (hκ : 0 < κ)
    (hgap : ∀ w, κ * ‖firstJetNormalProjection J.1 w‖ ≤
      ‖(secondJetNormalMap J).adjoint (firstJetNormalProjection J.1 w)‖) :
    Set.range (secondJetNormalMap J) =
      ((LinearMap.range J.1.toLinearMap)ᗮ : Set (Euclidean N)) := by
  let P := (LinearMap.range J.1.toLinearMap)ᗮ
  let B : MetricTensor n →L[ℝ] P :=
    (secondJetNormalMap J).codRestrict P (secondJetNormalMap_mem_orthogonal hi)
  have hadj (w : P) : B.adjoint w = (secondJetNormalMap J).adjoint w := by
    apply ext_inner_right ℝ
    intro H
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
    rfl
  have hb (w : P) : κ * ‖w‖ ≤ ‖B.adjoint w‖ := by
    have hp : firstJetNormalProjection J.1 w = (w : Euclidean N) := by
      rw [firstJetNormalProjection_eq_starProjection hi]
      exact Submodule.starProjection_eq_self_iff.mpr w.property
    simpa only [hp, hadj, Submodule.norm_coe] using hgap w
  have hs := (NormalRankStability.surjective_and_normal_gap_of_adjoint_lower_bound B hκ hb).1
  apply Set.Subset.antisymm
  · rintro _ ⟨H, rfl⟩
    exact secondJetNormalMap_mem_orthogonal hi H
  · intro w hw
    obtain ⟨H, hH⟩ := hs ⟨w, hw⟩
    exact ⟨H, congrArg Subtype.val hH⟩

/-- The range used by `app:ch_waves:eq:joint-tame` is compact: the normal
gap is closed relative to the closed positive metric-gap locus, and the jet
norm bounds this closed set in a finite-dimensional space. -/
theorem isCompact_boundedSecondJetGaps {n N : ℕ} (M κ : ℝ)
    {γ : ℝ} (hγ : 0 < γ) : IsCompact (boundedSecondJetGaps n N M γ κ) := by
  let : ProperSpace (SecondJet (Euclidean n) (Euclidean N)) :=
    FiniteDimensional.proper ℝ (SecondJet (Euclidean n) (Euclidean N))
  let S : Set (SecondJet (Euclidean n) (Euclidean N)) :=
    {J | ∀ v, γ * ‖v‖ ^ 2 ≤ ‖J.1 v‖ ^ 2}
  have hS : IsClosed S := by
    simp only [S, ofPred_forall]
    apply isClosed_iInter
    intro v
    exact isClosed_le continuous_const ((continuous_fst.clm_apply continuous_const).norm.pow 2)
  have hi {J} (hJ : J ∈ S) : Function.Injective J.1 :=
    firstJet_injective_of_metricEnergyGap hγ hJ
  have hP : ContinuousOn
      (fun J : SecondJet (Euclidean n) (Euclidean N) ↦ firstJetNormalProjection J.1) S := by
    intro J hJ
    exact ((contDiffAt_firstJetNormalProjection
      (firstJetMetric_isUnit_of_injective (hi hJ))).continuousAt.comp
      continuousAt_fst).continuousWithinAt
  have hB : ContinuousOn
      (fun J : SecondJet (Euclidean n) (Euclidean N) ↦ (secondJetNormalMap J).adjoint) S := by
    intro J hJ
    exact ((NormalInverse.contDiff_adjoint (k := ∞)).continuous.continuousAt.comp
      (contDiffAt_secondJetNormalMap
        (firstJetMetric_isUnit_of_injective (hi hJ))).continuousAt).continuousWithinAt
  have hc (w : Euclidean N) : IsClosed
      {J ∈ S | κ * ‖firstJetNormalProjection J.1 w‖ ≤
        ‖(secondJetNormalMap J).adjoint (firstJetNormalProjection J.1 w)‖} :=
    hS.isClosed_le (continuousOn_const.mul (hP.clm_apply continuousOn_const).norm)
      (hB.clm_apply (hP.clm_apply continuousOn_const)).norm
  have hall : IsClosed {J : SecondJet (Euclidean n) (Euclidean N) |
      J ∈ S ∧ ∀ w, κ * ‖firstJetNormalProjection J.1 w‖ ≤
        ‖(secondJetNormalMap J).adjoint (firstJetNormalProjection J.1 w)‖} := by
    have h := isClosed_iInter hc
    simpa only [Set.iInter_ofPred, forall_and, forall_const] using h
  have hball : IsCompact (Metric.closedBall (0 : SecondJet (Euclidean n) (Euclidean N)) M) :=
    isCompact_closedBall _ _
  have hcompact := hball.inter_right hall
  convert hcompact using 1
  ext J
  simp only [boundedSecondJetGaps, Set.mem_ofPred_eq, Set.mem_inter_iff,
    Metric.mem_closedBall, S]
  rw [show dist J 0 = ‖J‖ from dist_zero_right J]

/-- The actual local second jet belongs to the fixed range from the
primitive bounds in `app:ch_seed:setup:seed-current`. This supplies the
pointwise compact containment needed by `app:ch_waves:eq:joint-tame`, using
only C2 regularity at the given point. -/
theorem secondJet_mem_boundedSecondJetGaps {n N : ℕ}
    {F : Euclidean n → Euclidean N} {x : Euclidean n} {M γ κ : ℝ}
    (hF : ContDiffAt ℝ 2 F x) (hi : Function.Injective (fderiv ℝ F x))
    (hM : ‖secondJet F x‖ ≤ M)
    (hmetric : ∀ v, γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2)
    (hnormal : ∀ w ∈ normalSpace F x,
      κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) :
    secondJet F x ∈ boundedSecondJetGaps n N M γ κ := by
  refine ⟨hM, hmetric, ?_⟩
  intro w
  have hp : firstJetNormalProjection (secondJet F x).1 = normalProjection F x :=
    firstJetNormalProjection_eq hi
  rw [hp, secondJetNormalMap_eq_of_contDiffAt hF hi]
  have ha (z : Euclidean N) : (NormalRankStability.ambientNormalMap F x).adjoint z =
      normalPairing F (fun _ ↦ z) x := by
    apply ext_inner_right ℝ
    intro H
    rw [ContinuousLinearMap.adjoint_inner_left]
    change inner ℝ z (normalMap F x H) =
      tensorPairing (normalPairing F (fun _ ↦ z) x) H
    rw [inner_normalMap_eq_tensorPairing F (fun _ ↦ z)]
    exact real_inner_comm _ H
  rw [ha]
  exact hnormal _ (normalProjection_mem_normalSpace F x w)

/-- A compact second-jet range, chosen before the map and point, from the
separate primitive metric-energy and normal-pairing gaps. This closes the
compact-range prerequisite of `app:ch_waves:eq:joint-tame` for the actual
joint reconstruction. Every jet in the range is immersive and has full
normal rank. The parent supplies the second-jet norm bound from its fixed
C4 bound; no inverse estimate or compact-containment hypothesis is required. -/
theorem exists_compact_secondJet_range {n N : ℕ} {M γ κ : ℝ}
    (_hM : 0 < M) (hγ : 0 < γ) (hκ : 0 < κ) :
    ∃ T : Set (SecondJet (Euclidean n) (Euclidean N)), IsCompact T ∧
      (∀ J ∈ T, Function.Injective J.1) ∧
      (∀ J ∈ T, Set.range (secondJetNormalMap J) =
        ((LinearMap.range J.1.toLinearMap)ᗮ : Set (Euclidean N))) ∧
      ∀ (F : Euclidean n → Euclidean N) (x : Euclidean n),
        ContDiffAt ℝ 2 F x → Function.Injective (fderiv ℝ F x) →
        Set.range (normalMap F x) = (normalSpace F x : Set (Euclidean N)) →
        ‖secondJet F x‖ ≤ M →
        (∀ v, γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        secondJet F x ∈ T := by
  refine ⟨boundedSecondJetGaps n N M γ κ,
    isCompact_boundedSecondJetGaps M κ hγ, ?_, ?_, ?_⟩
  · intro J hJ
    exact firstJet_injective_of_metricEnergyGap hγ hJ.2.1
  · intro J hJ
    exact secondJetNormalMap_range_of_projected_gap
      (firstJet_injective_of_metricEnergyGap hγ hJ.2.1) hκ hJ.2.2
  · intro F x hF hi _hrank hM hmetric hnormal
    exact secondJet_mem_boundedSecondJetGaps hF hi hM hmetric hnormal

end JanetCartan.LeadingWave.JointReconstruction
