module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.Phase
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedCarrierJets.FixedPullback

/-!
# Full-covector gradient bounds with the carrier label retained

The input for the full null-coefficient construction is the literal physical
gradient with independent `(z,ζ)` parameters. A fixed linear restriction and
one physical derivative of the same Hamilton phase give the sharp immersion
reserve four. This closes the phase-gradient high-norm input in
`app:ch_waves:eq:joint-tame`, before construction of the full transport flow.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.LeadingWave.FullModulation
open ActualCarriers FrozenMenu CurrentFullPhase HamiltonPhase ConstructedCarrierJets

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Remove the spectator carrier label without coupling it to the full
covector (`app:ch_waves:eq:joint-tame`). -/
def physicalCovectorProjection : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) →L[ℝ]
    Euclidean n × Euclidean (n - 1) :=
  (ContinuousLinearMap.fst ℝ _ _).prod
    ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))

/-- Full joint domain before any minor refinement
(`app:ch_waves:thm:leading`). -/
def domain : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1))) :=
  physicalCovectorProjection ⁻¹' phaseDomain T

/-- The full joint domain is open, so physical slices require no extension
(`app:ch_waves:eq:exact-half-strain`). -/
theorem isOpen_domain : IsOpen (domain T) :=
  isOpen_ball.preimage physicalCovectorProjection.continuous

/-- Joint smoothness with the carrier label retained
(`app:ch_waves:eq:joint-tame`). -/
theorem phaseGradient_joint_smooth (Q : _) :
    ContDiffOn ℝ ∞
      (fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦ phaseGradient T Q w.1 w.2.2)
      (domain T) :=
  (phaseGradient_smooth T Q).comp physicalCovectorProjection.contDiff.contDiffOn
    (fun _ hw ↦ hw)

/-- One full phase derivative controls every joint full-covector gradient jet.
Only the fixed linear restriction contributes to the constants
(`app:ch_waves:eq:joint-tame`). -/
theorem exists_phaseGradient_le_phase
    {J : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hJ : IsCompact J) (hJO : J ⊆ domain T) :
    ∃ D : ℕ → ℝ, (∀ m, 0 < D m) ∧ ∀ Q m,
      cNorm J m (fun w ↦ phaseGradient T Q w.1 w.2.2) ≤
        D m * cNorm (closedBall (T.data.adapted.embedding T.data.adapted.baseData.1,
          T.data.adapted.baseData.2) T.family.radius) (m + 1)
          (HamiltonPhase.phase (T.currentChart Q).coordinates) := by
  let ψ := (zeroEnergyInclusion (n := n)).comp physicalCovectorProjection
  have hψ : ∀ x ∈ J, ContDiffAt ℝ ∞ ψ x := fun _ _ ↦ ψ.contDiff.contDiffAt
  choose D hD hb using fun m ↦ exists_cNorm_fixed_pullback_le_jet_bound
    (G := Euclidean n) hJ hψ m
  refine ⟨D, hD, fun Q m ↦ ?_⟩
  let S := HamiltonPhase.phase (T.currentChart Q).coordinates
  let L := closedBall (T.data.adapted.embedding T.data.adapted.baseData.1,
    T.data.adapted.baseData.2) T.family.radius
  have hS : ∀ x ∈ L, ContDiffAt ℝ ∞ S x := fun x hx ↦
    (T.family.phase_smooth Q).contDiffAt (isOpen_ball.mem_nhds
      (closedBall_subset_ball (by linarith [T.family.radius_pos] :
        T.family.radius < 2 * T.family.radius) hx))
  have hψL : MapsTo ψ J L := fun w hw ↦
    ball_subset_closedBall ((inclusion_mem_ball T).mpr (hJO hw))
  let g := momentumDifferentialExtraction (n := n) ∘ fderiv ℝ S
  have hg : ∀ x ∈ L, ContDiffAt ℝ ∞ g x := fun x hx ↦
    momentumDifferentialExtraction.contDiff.contDiffAt.comp x
      ((hS x hx).fderiv_right (m := ∞) (by simp))
  have he : cNorm J m (fun w ↦ phaseGradient T Q w.1 w.2.2) = cNorm J m (g ∘ ψ) := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq _ m
    intro w hw
    apply eventuallyEq_of_mem ((isOpen_domain T).mem_nhds (hJO hw))
    intro v hv
    have ht : (v.1, (0, v.2.2)) ∈ (T.currentChart Q).target :=
      (inclusion_mem_ball T (w := (v.1, v.2.2))).mpr hv
    exact (phaseGradient_eq_chartMomentum T Q (w := (v.1, v.2.2)) hv).trans
      (chartMomentum_eq_extracted_phaseDifferential (T.currentChart Q) ht)
  rw [he]
  apply hb m g (cNorm L (m + 1) S) (cNorm_nonneg ..)
    (fun x hx ↦ (hg _ (hψL hx)).of_le (by simp))
  intro j hj x hx
  calc
    _ ≤ ‖momentumDifferentialExtraction (n := n)‖ *
        ‖iteratedFDeriv ℝ j (fderiv ℝ S) (ψ x)‖ :=
      momentumDifferentialExtraction.norm_iteratedFDeriv_comp_left
        ((hS _ (hψL hx)).fderiv_right (m := ∞) (by simp)) (by simp)
    _ ≤ 1 * ‖iteratedFDeriv ℝ j (fderiv ℝ S) (ψ x)‖ :=
      mul_le_mul_of_nonneg_right norm_momentumDifferentialExtraction_le (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ (j + 1) S (ψ x)‖ := by
      rw [one_mul, norm_iteratedFDeriv_fderiv]
    _ ≤ _ := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall _ _)
      (fun y hy ↦ (hS y hy).of_le (by simp : ((m + 1 : ℕ) : ℕ∞ω) ≤ ∞))
      (hψL hx) (by omega)

/-- Actual joint full-gradient estimates have immersion reserve four. Constants
and the compact joint domain precede the immersion and all high norms
(`app:ch_waves:eq:joint-tame`). -/
theorem exists_phaseGradient_projected_sharp_bound {N : ℕ}
    {J : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hJ : IsCompact J) (hJO : J ⊆ domain T)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (M : ℝ) {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ) :
    ∃ A : ℕ → ℝ, (∀ m, 0 < A m) ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K 4 F ≤ M →
        (∀ x ∈ K, ∀ v, γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x, κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (ProjectedStressFrame.projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨ProjectedStressFrame.projectedStress F,
          contDiffOn_pi.mpr (ProjectedStressFrame.contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        ∀ m, cNorm J m (fun w ↦ phaseGradient T Q w.1 w.2.2) ≤
          A m * (1 + cNorm K (m + 4) F) := by
  obtain ⟨D, hD, hd⟩ := exists_phaseGradient_le_phase T hJ hJO
  obtain ⟨B, hB, hb⟩ := T.exists_projected_phase_sharp_bound hK hKU hball M hγ hκ
  refine ⟨fun m ↦ D m * B (m + 1), fun m ↦ mul_pos (hD m) (hB _), ?_⟩
  intro F hF hi hrank hFM hmet hnormal hlow
  dsimp only
  intro m
  apply (hd _ m).trans
  simpa only [Nat.add_assoc, Nat.reduceAdd, mul_assoc] using
    mul_le_mul_of_nonneg_left (hb F hF hi hrank hFM hmet hnormal hlow (m + 1)) (hD m).le

end JanetCartan.LeadingWave.FullModulation
