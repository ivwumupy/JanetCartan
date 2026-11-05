module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.FlowFamily.CommonChart.SourceGap
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.SmoothBufferedChart

/-!
# Common quantitative inverse projection charts

The actual projection of any flow with the fixed scalar-root budget has a
smooth inverse on one fixed source ball. The target contains one fixed closed
buffer. These are the inverse domains consumed by the two-time phase and
amplitude bounds in `app:ch_regular_base:lem:characteristic-kernel`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff

namespace JanetCartan.RegularSector.Characteristic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

local instance : NormedSpace ℝ E := InnerProductSpace.toNormedSpace

/-- Common inverse charts constructed from the scalar-root budget and the
actual ODE. Both radii precede the root and flow, and the prescribed normalized
tolerance is retained for the spatial mixed estimate. The inverse has uniform
Lipschitz constant `2 * (1 + 2 * M)` on its entire target
(`app:ch_regular_base:lem:characteristic-kernel`,
`app:ch_regular_base:lem:retarded-kernel`). -/
theorem exists_common_twoTimeProjectionChart
    (z : RootState E) (hz : z.2.2 ≠ 0) {R T M δ : ℝ}
    (hR : 0 < R) (hT : 0 < T) (hM : 0 ≤ M) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    {D : Set (RootState E)} (hD : IsOpen D) (hRD : closedBall z R ⊆ D) :
    ∃ ρ > (0 : ℝ), ∃ ε > (0 : ℝ),
      2 * ρ ≤ R / 4 ∧ 2 * ρ ≤ T / 4 ∧ 2 * ε < ‖z.2.2‖ ∧
      closedBall (z.1, z) (2 * ρ) ⊆ twoTimeDomain z (R / 2) T ∧
      ∀ (h : RootState E → ℝ) (Φ : RootState E × ℝ → RootState E),
        ContDiffOn ℝ ∞ h D → cNorm (closedBall z R) 3 h ≤ M →
        ODE.IsSmoothFlowOn (rootHamiltonField h) z R (R / 2) T Φ →
        ∃ C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E),
          (C : TwoTimePoint E → TwoTimePoint E) = twoTimeProjection Φ ∧
          C.source = ball (z.1, z) ρ ∧
          ContDiffOn ℝ ∞ C.symm C.target ∧
          closedBall (z.1, z) (2 * ε) ⊆ C.target ∧
          (∀ q ∈ closedBall (z.1, z) ρ,
            ‖(twoTimeProjectionEquiv (-rootMomentumGradient h z)).symm.toContinuousLinearMap.comp
              (fderiv ℝ (twoTimeProjection Φ) q) -
                ContinuousLinearMap.id ℝ (TwoTimePoint E)‖ ≤ δ) ∧
          (∀ q ∈ C.target, ∀ q' ∈ C.target,
            ‖C.symm q - C.symm q'‖ ≤ (2 * (1 + 2 * M)) * ‖q - q'‖) := by
  obtain ⟨ρ, hρ, hρR, hρT, hdomain, hgap⟩ :=
    exists_common_twoTimeProjection_gap z hR hT hM hδ hD hRD
  let L := 1 + 2 * M
  have hL : 0 < L := by dsimp [L]; positivity
  let ε := min (ρ / (8 * L)) (‖z.2.2‖ / 4)
  have hη : 0 < ‖z.2.2‖ := norm_pos_iff.mpr hz
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hεL : L * (2 * ε) ≤ ρ / 4 := by
    have := (le_div_iff₀ (by positivity : 0 < 8 * L)).mp
      (min_le_left (ρ / (8 * L)) (‖z.2.2‖ / 4))
    nlinarith
  have hεη : 2 * ε < ‖z.2.2‖ := by
    have := min_le_right (ρ / (8 * L)) (‖z.2.2‖ / 4)
    linarith
  have hsub : closedBall (z.1, z) ρ ⊆ twoTimeDomain z (R / 2) T :=
    (closedBall_subset_closedBall (by linarith : ρ ≤ 2 * ρ)).trans hdomain
  refine ⟨ρ, hρ, ε, hε, hρR, hρT, hεη, hdomain, ?_⟩
  intro h Φ hh hlow hΦ
  let A := twoTimeProjectionEquiv (-rootMomentumGradient h z)
  have hnorm : ‖A.symm.toContinuousLinearMap‖ ≤ L :=
    (rootProjectionShear_bounds_of_cNorm_three hD hR.le hRD hh hlow).2
  have hg := hgap h Φ hh hlow hΦ
  have hgclosed : ∀ q ∈ closedBall (z.1, z) ρ,
      ‖A.symm.toContinuousLinearMap.comp (fderiv ℝ (twoTimeProjection Φ) q) -
        ContinuousLinearMap.id ℝ (TwoTimePoint E)‖ ≤ 1 / 2 :=
    fun q hq ↦ (hg q hq).trans hδhalf
  have hs := rootFlow_twoTimeProjection_smooth hΦ
  have hd (q) (hq : q ∈ closedBall (z.1, z) ρ) :
      DifferentiableAt ℝ (twoTimeProjection Φ) q :=
    (hs.contDiffAt ((isOpen_twoTimeDomain z (R / 2) T).mem_nhds
      (hsub hq))).differentiableAt (by simp)
  obtain ⟨C, hC, hsource, _, hinv⟩ :=
    HamiltonPhase.exists_smoothInverse_of_normalized_half_gap
      isOpen_ball (convex_ball (z.1, z) ρ) A (twoTimeProjection Φ)
      (hs.mono (ball_subset_closedBall.trans hsub))
      (fun q hq ↦ hgclosed q (ball_subset_closedBall hq))
  refine ⟨C, hC, hsource, hinv, ?_, hg, ?_⟩
  · intro q hq
    have hcenter : twoTimeProjection Φ (z.1, z) = (z.1, z) :=
      (rootFlow_twoTime_diagonal hΦ (mem_closedBall_self (by positivity))).2
    have hb : ‖A.symm (q - twoTimeProjection Φ (z.1, z))‖ ≤ (ρ / 2) / 2 := by
      rw [hcenter]
      calc
        _ ≤ ‖A.symm.toContinuousLinearMap‖ * ‖q - (z.1, z)‖ :=
          A.symm.toContinuousLinearMap.le_opNorm _
        _ ≤ L * (2 * ε) := mul_le_mul hnorm
          (by simpa only [mem_closedBall, dist_eq_norm] using hq) (norm_nonneg _) hL.le
        _ ≤ (ρ / 2) / 2 := by linarith [hεL]
    obtain ⟨w, hw, hwq⟩ := mem_image_closedBall_of_normalized_derivative_gap
      (convex_closedBall (z.1, z) ρ) A hd hgclosed (by positivity : 0 ≤ ρ / 2)
      (closedBall_subset_closedBall (by linarith : ρ / 2 ≤ ρ)) hb
    have hws : w ∈ C.source := hsource ▸ closedBall_subset_ball (by linarith) hw
    simpa only [hC, hwq] using C.map_source hws
  · intro q hq q' hq'
    have hx : C.symm q ∈ closedBall (z.1, z) ρ :=
      ball_subset_closedBall (hsource ▸ C.map_target hq)
    have hy : C.symm q' ∈ closedBall (z.1, z) ρ :=
      ball_subset_closedBall (hsource ▸ C.map_target hq')
    have hl := normalized_lower_lipschitz_of_derivative_gap
      (convex_closedBall (z.1, z) ρ) A hd hgclosed hx hy
    have heq : twoTimeProjection Φ (C.symm q) = q := by rw [← hC]; exact C.right_inv hq
    have heq' : twoTimeProjection Φ (C.symm q') = q' := by rw [← hC]; exact C.right_inv hq'
    rw [heq, heq'] at hl
    have hn := (A.symm.toContinuousLinearMap.le_opNorm (q - q')).trans
      (mul_le_mul_of_nonneg_right hnorm (norm_nonneg (q - q')))
    change ‖A.symm (q - q')‖ ≤ L * ‖q - q'‖ at hn
    change ‖C.symm q - C.symm q'‖ ≤ (2 * L) * ‖q - q'‖
    linarith

end JanetCartan.RegularSector.Characteristic
