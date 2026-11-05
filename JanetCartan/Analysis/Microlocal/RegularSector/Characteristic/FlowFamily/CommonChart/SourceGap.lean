module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.FlowFamily.ProjectionJets
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.FlowFamily.ShearBounds

/-!
# A common normalized projection gap

The scalar `C³` bound in `app:ch_regular_base:lem:characteristic-kernel`
chooses the source radius before the Hamiltonian and its actual flow. The
consumer is the common inverse chart, followed by the spatial mixed half-gap
in `app:ch_regular_base:lem:retarded-kernel`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff

namespace JanetCartan.RegularSector.Characteristic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

local instance : NormedSpace ℝ E := InnerProductSpace.toNormedSpace

omit [FiniteDimensional ℝ E] in
/-- The actual ODE supplies the central projection differential used to
normalize the common chart (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem rootFlow_fderiv_twoTimeProjection_diagonal
    {z : RootState E} {R T : ℝ} (hR : 0 < R) (hT : 0 < T)
    {h : RootState E → ℝ} {Φ : RootState E × ℝ → RootState E}
    (hΦ : ODE.IsSmoothFlowOn (rootHamiltonField h) z R (R / 2) T Φ) :
    fderiv ℝ (twoTimeProjection Φ) (z.1, z) =
      (twoTimeProjectionEquiv (-rootMomentumGradient h z)).toContinuousLinearMap := by
  have hz : z ∈ ball z (R / 2) := mem_ball_self (by positivity)
  have ht : (0 : ℝ) ∈ Ioo (-T) T := ⟨by linarith, hT⟩
  apply HasFDerivAt.fderiv
  apply hasFDerivAt_twoTimeProjection_diagonal
    ((hΦ.smooth.contDiffAt ((isOpen_ball.prod isOpen_Ioo).mem_nhds
      ⟨hz, ht⟩)).differentiableAt (by simp))
  · simpa only [hΦ.initial z (ball_subset_closedBall hz)] using
      hΦ.hasDerivAt (ball_subset_closedBall hz) ht
  · exact hΦ.variation_initial z hz

/-- Any prescribed positive normalized tolerance is achieved on one common
source ball. The radius depends only on the fixed scalar `C³` budget and
the fixed domains, before choosing either the root or its flow. This is the
quantitative input of the common inverse constructor and its mixed-matrix
estimate (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem exists_common_twoTimeProjection_gap
    (z : RootState E) {R T M δ : ℝ} (hR : 0 < R) (hT : 0 < T)
    (hM : 0 ≤ M) (hδ : 0 < δ)
    {D : Set (RootState E)} (hD : IsOpen D) (hRD : closedBall z R ⊆ D) :
    ∃ ρ > (0 : ℝ), 2 * ρ ≤ R / 4 ∧ 2 * ρ ≤ T / 4 ∧
      closedBall (z.1, z) (2 * ρ) ⊆ twoTimeDomain z (R / 2) T ∧
      ∀ (h : RootState E → ℝ) (Φ : RootState E × ℝ → RootState E),
        ContDiffOn ℝ ∞ h D → cNorm (closedBall z R) 3 h ≤ M →
        ODE.IsSmoothFlowOn (rootHamiltonField h) z R (R / 2) T Φ →
        ∀ q ∈ closedBall (z.1, z) ρ,
          ‖(twoTimeProjectionEquiv (-rootMomentumGradient h z)).symm.toContinuousLinearMap.comp
            (fderiv ℝ (twoTimeProjection Φ) q) -
              ContinuousLinearMap.id ℝ (TwoTimePoint E)‖ ≤ δ := by
  let a := min (R / 16) (T / 16)
  have ha : 0 < a := lt_min (by positivity) (by positivity)
  have haR : 2 * a ≤ R / 4 := by have := min_le_left (R / 16) (T / 16); dsimp [a]; linarith
  have haT : 2 * a ≤ T / 4 := by have := min_le_right (R / 16) (T / 16); dsimp [a]; linarith
  obtain ⟨B, hB, hb⟩ := exists_rootFlow_twoTime_cNorm_bound z hR hT hM haR haT hD hRD 2
  let K := B * (1 + M)
  let L := 1 + 2 * M
  have hK : 0 < K := mul_pos hB (by positivity)
  have hL : 0 < L := by dsimp [L]; positivity
  let ρ := min (a / 2) (δ / (L * K))
  have hρ : 0 < ρ := lt_min (by positivity) (by positivity)
  have hρa : 2 * ρ ≤ a := by have := min_le_left (a / 2) (δ / (L * K)); linarith
  have hρδ : L * (K * ρ) ≤ δ := by
    have := (le_div_iff₀ (mul_pos hL hK)).mp (min_le_right (a / 2) (δ / (L * K)))
    nlinarith
  have hsub := closedBall_subset_twoTimeDomain z hR hT haR haT
  refine ⟨ρ, hρ, by linarith, by linarith,
    (closedBall_subset_closedBall hρa).trans hsub, ?_⟩
  intro h Φ hh hlow hΦ
  have hs := rootFlow_twoTimeProjection_smooth hΦ
  have hbound : cNorm (closedBall (z.1, z) a) 2 (twoTimeProjection Φ) ≤ K := by
    have hhigher := hb h Φ hh hlow hΦ
    have hnonneg := cNorm_nonneg (closedBall (z.1, z) a) 2 (twoTimeState Φ)
    have hmul := mul_le_mul_of_nonneg_left hlow hB.le
    dsimp [K]
    norm_num only at hhigher
    nlinarith
  have hlip := (ODE.field_and_fderiv_lipschitzOnWith_of_cNorm
    (isOpen_twoTimeDomain z (R / 2) T) hsub hs (K := ⟨K, hK.le⟩) hbound).2
  intro q hq
  have hqa : q ∈ closedBall (z.1, z) a :=
    closedBall_subset_closedBall (by linarith : ρ ≤ a) hq
  have hdiff : ‖fderiv ℝ (twoTimeProjection Φ) q -
      fderiv ℝ (twoTimeProjection Φ) (z.1, z)‖ ≤ K * ρ := by
    have hb := hlip.dist_le_mul q hqa (z.1, z) (mem_closedBall_self ha.le)
    rw [dist_eq_norm] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left hq hK.le)
  rw [rootFlow_fderiv_twoTimeProjection_diagonal hR hT hΦ] at hdiff
  let A := twoTimeProjectionEquiv (-rootMomentumGradient h z)
  have heq : A.symm.toContinuousLinearMap.comp (fderiv ℝ (twoTimeProjection Φ) q) -
      ContinuousLinearMap.id ℝ (TwoTimePoint E) =
        A.symm.toContinuousLinearMap.comp
          (fderiv ℝ (twoTimeProjection Φ) q - A.toContinuousLinearMap) := by
    apply ContinuousLinearMap.ext
    intro v
    simp
  change ‖A.symm.toContinuousLinearMap.comp _ - _‖ ≤ δ
  rw [heq]
  calc
    _ ≤ ‖A.symm.toContinuousLinearMap‖ *
        ‖fderiv ℝ (twoTimeProjection Φ) q - A.toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ L * (K * ρ) := mul_le_mul
      (rootProjectionShear_bounds_of_cNorm_three hD hR.le hRD hh hlow).2
      hdiff (norm_nonneg _) hL.le
    _ ≤ δ := hρδ

end JanetCartan.RegularSector.Characteristic
