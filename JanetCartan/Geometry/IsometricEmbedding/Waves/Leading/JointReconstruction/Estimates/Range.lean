module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.JointReconstruction.Estimates.JetBounds

/-!
# The compact joint reconstruction range

For `app:ch_waves:eq:joint-tame`, adjoin fixed balls for the covector, its
physical differential and the phase covector to the stipulated compact
physical second-jet range. The parent geometric construction must still
supply that physical range; this module only closes the joint extension.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
open Set

namespace JanetCartan.LeadingWave.JointReconstruction

set_option maxSynthPendingDepth 5

open GeometricProfile

/-- The common compact coefficient range for `app:ch_waves:eq:joint-tame`.
Its radius is the fixed joint `C¹` bound, independent of all high norms. -/
def jointJetRange {n N : ℕ} (T : Set (SecondJet (Euclidean n) (Euclidean N)))
    (M : ℝ) : Set (JointJet n N) :=
  (T ×ˢ (Metric.closedBall 0 M ×ˢ Metric.closedBall 0 M)) ×ˢ Metric.closedBall 0 M

/-- The joint coefficient range for `app:ch_waves:eq:joint-tame` is compact
whenever the physical second-jet range is compact. -/
theorem isCompact_jointJetRange {n N : ℕ}
    {T : Set (SecondJet (Euclidean n) (Euclidean N))} (hT : IsCompact T) (M : ℝ) :
    IsCompact (jointJetRange T M) :=
  (hT.prod ((isCompact_closedBall 0 M).prod (isCompact_closedBall 0 M))).prod
    (isCompact_closedBall 0 M)

/-- The fixed `C¹` bounds imply actual joint-jet containment
(`app:ch_waves:eq:joint-tame`). Only physical second-jet containment remains
conditional, with its producer in the parent reconstruction construction. -/
theorem mapsTo_jointJet_range {n N : ℕ} {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (a : Euclidean n × Z) (ρ : ℝ)
    {F : Euclidean n → Euclidean N} {b ξ : Euclidean n × Z → Euclidean n}
    {T : Set (SecondJet (Euclidean n) (Euclidean N))} {M : ℝ}
    (hFT : MapsTo (secondJet F) (Metric.closedBall a.1 ρ) T)
    (hb : ∀ p ∈ Metric.closedBall a ρ, ContDiffAt ℝ 1 b p)
    (hξ : ∀ p ∈ Metric.closedBall a ρ, ContDiffAt ℝ 1 ξ p)
    (hbM : cNorm (Metric.closedBall a ρ) 1 b ≤ M)
    (hξM : cNorm (Metric.closedBall a ρ) 1 ξ ≤ M) :
    MapsTo (jointJet F b ξ) (Metric.closedBall a ρ) (jointJetRange T M) := by
  intro p hp
  have hpx : p.1 ∈ Metric.closedBall a.1 ρ := by
    have := hp
    rw [← closedBall_prod_same a.1 a.2 ρ] at this
    exact this.1
  have hb0 : ‖b p‖ ≤ M := by
    have h := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall ..)
      hb hp (by omega : 0 ≤ 1)
    rw [norm_iteratedFDeriv_zero] at h
    exact h.trans hbM
  have hb1 : ‖fderiv ℝ b p‖ ≤ M := by
    have h := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall ..)
      hb hp (le_refl 1)
    rw [norm_iteratedFDeriv_one] at h
    exact h.trans hbM
  have hbr : ‖(fderiv ℝ b p).comp (ContinuousLinearMap.inl ℝ (Euclidean n) Z)‖ ≤ M := by
    calc
      _ ≤ ‖fderiv ℝ b p‖ * ‖ContinuousLinearMap.inl ℝ (Euclidean n) Z‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖fderiv ℝ b p‖ * 1 := mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.norm_inl_le_one ..) (norm_nonneg _)
      _ ≤ M := by simpa using hb1
  have hξ0 : ‖ξ p‖ ≤ M := by
    have h := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall ..)
      hξ hp (by omega : 0 ≤ 1)
    rw [norm_iteratedFDeriv_zero] at h
    exact h.trans hξM
  exact ⟨⟨hFT hpx, by simpa only [jointJet, Metric.mem_closedBall, dist_zero_right] using hb0,
    by simpa only [jointJet, Metric.mem_closedBall, dist_zero_right] using hbr⟩,
    by simpa only [jointJet, Metric.mem_closedBall, dist_zero_right] using hξ0⟩

end JanetCartan.LeadingWave.JointReconstruction
