module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Definitions
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.PhaseJets
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.JointDomains

/-!
# Actual full-phase covector grades

The phase is the SAME `FullModulation.phase T Q` used in the corrected
family. Its sharp reserve-three estimate is proved from the immersion and
the separate metric/normal gaps. The reserve-fourteen profile threshold
with the manuscript's `r_par+2` allowance therefore implies both the
`L^(r-1)` physical estimate and the stronger joint profile needed by
`SliceBounds.exists_normalizedRawSliceBranch_profiles`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary.AmplitudeGrades
open LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ProjectedStressFrame AmbientResponse

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- The free-covector differential is a restriction of the full joint
phase differential. The carrier label is held fixed, rather than replaced
by the carrier graph (`app:ch_waves:eq:graded-phase`). -/
theorem fullPhase_parameter_fderiv_eq {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))}
    (hw : w ∈ domain T) :
    fderiv ℝ (phase T Q w.1) w.2.2 =
      (fderiv ℝ (fun y : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
        phase T Q y.1 y.2.2) w).comp
          ((ContinuousLinearMap.inr ℝ (Euclidean n) (Euclidean 3 × Euclidean (n - 1))).comp
            (ContinuousLinearMap.inr ℝ (Euclidean 3) (Euclidean (n - 1)))) := by
  have hd := ((contDiffOn_fullPhase T Q (Ω := domain T) (fun _ h ↦ h)).contDiffAt
    ((isOpen_domain T).mem_nhds hw)).differentiableAt (by simp)
  have hinc := (hasFDerivAt_const (𝕜 := ℝ) w.1 w.2.2).prodMk
    ((hasFDerivAt_const (𝕜 := ℝ) w.2.1 w.2.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) w.2.2))
  exact (hd.hasFDerivAt.comp w.2.2 hinc).fderiv

/-- Joint free-covector jets use exactly one additional joint phase jet
on the original common chart (`app:ch_waves:eq:graded-phase`). -/
theorem norm_iteratedFDeriv_fullPhase_parameter_fderiv_le
    {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))}
    (hw : w ∈ domain T) (j : ℕ) :
    ‖iteratedFDeriv ℝ j
      (fun y : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
        fderiv ℝ (phase T Q y.1) y.2.2) w‖ ≤
      ‖iteratedFDeriv ℝ (j + 1)
        (fun y : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
          phase T Q y.1 y.2.2) w‖ := by
  let B := (ContinuousLinearMap.inr ℝ (Euclidean n) (Euclidean 3 × Euclidean (n - 1))).comp
    (ContinuousLinearMap.inr ℝ (Euclidean 3) (Euclidean (n - 1)))
  have hB : ‖B‖ ≤ 1 := by
    apply B.opNorm_le_bound zero_le_one
    intro v
    simp [B]
  have he : (fun y : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
      fderiv ℝ (phase T Q y.1) y.2.2) =ᶠ[𝓝 w]
        (fun y ↦ (fderiv ℝ (fun q : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
          phase T Q q.1 q.2.2) y).comp B) := by
    filter_upwards [(isOpen_domain T).mem_nhds hw] with y hy
    exact fullPhase_parameter_fderiv_eq T Q hy
  rw [(he.iteratedFDeriv (𝕜 := ℝ) (n := j)).eq_of_nhds]
  exact norm_iteratedFDeriv_restricted_fderiv_le
    ((contDiffOn_fullPhase T Q (Ω := domain T) (fun _ h ↦ h)).contDiffAt
      ((isOpen_domain T).mem_nhds hw)) B hB j

/-- The actual free-covector differential is jointly smooth, as required
by the raw physical and differentiated slice estimates
(`app:ch_waves:eq:individual-grading`). -/
theorem contDiffOn_fullPhase_parameter_fderiv :
    ContDiffOn ℝ ∞
      (fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
        fderiv ℝ (phase T Q w.1) w.2.2) (domain T) := by
  have hd := (contDiffOn_fullPhase T Q (Ω := domain T) (fun _ h ↦ h)).fderiv_of_isOpen
    (isOpen_domain T) (m := ∞) (by simp)
  apply (hd.clm_comp (contDiffOn_const (c :=
    (ContinuousLinearMap.inr ℝ (Euclidean n) (Euclidean 3 × Euclidean (n - 1))).comp
      (ContinuousLinearMap.inr ℝ (Euclidean 3) (Euclidean (n - 1)))))).congr
  intro w hw
  exact fullPhase_parameter_fderiv_eq T Q hw

omit Q in
/-- Uniform grades of the SAME full phase, derived from its primitive
immersion profile and geometric gaps. The constants precede the immersion,
its stress field, and the varying scale. The original reserve is fourteen
with the additional `r_par+2` allowance; the sharp phase producer costs only
three, leaving the stronger joint profile used by the differentiated slice
consumer (`app:ch_waves:eq:graded-phase`, `app:ch_waves:eq:individual-grading`). -/
theorem exists_fullPhase_parameter_grades {N : ℕ}
    {J : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hJ : IsCompact J) (hJO : J ⊆ domain T)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (M : ℝ) {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ)
    (AF : ℕ → ℝ) (hAF : ∀ j, 0 ≤ AF j) :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
      cNorm K 4 F ≤ M →
      (∀ x ∈ K, ∀ v, γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x, κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
      let Q := ⟨projectedStress F,
        contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
      ∀ (RF rpar : ℕ) (L : ℝ), 1 ≤ L → 14 + (rpar + 2) ≤ RF →
      HasDerivativeProfile K F RF L AF →
      (∀ j, ∀ w ∈ J,
        ‖iteratedFDeriv ℝ j
          (fun y : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
            fderiv ℝ (phase T Q y.1) y.2.2) w‖ ≤
              C j * L ^ (j - 1 - (rpar + 2))) ∧
      (∀ j k : ℕ, 1 ≤ j → k ≤ rpar → ∀ w ∈ J,
        ‖iteratedFDeriv ℝ (j + k)
          (fun y : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
            fderiv ℝ (phase T Q y.1) y.2.2) w‖ ≤ C (j + k) * L ^ (j - 1)) ∧
      (∀ j : ℕ, 1 ≤ j → ∀ w ∈ J,
        ‖iteratedFDeriv ℝ j (fun x ↦ fderiv ℝ (phase T Q x) w.2.2) w.1‖ ≤
          C j * L ^ (j - 1)) := by
  obtain ⟨A, hA, hbound⟩ := exists_phase_joint_projected_sharp_bound
    (N := N) T hJ hJO hK hKU hball M hγ hκ
  refine ⟨fun j ↦ A (j + 1) * (1 + AF (j + 1 + 3)),
    fun j ↦ mul_pos (hA _) (by have := hAF (j + 1 + 3); positivity), ?_⟩
  intro F hF hi hrank hFM hmetric hnormal hlow
  dsimp only
  let Q := (⟨projectedStress F,
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
    {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  intro RF rpar L hL hRF hprofile
  have hS := contDiffOn_fullPhase T Q (Ω := domain T) (fun _ h ↦ h)
  have hSP : HasDerivativeProfile J
      (fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦ phase T Q w.1 w.2.2)
      (rpar + 4) L (fun j ↦ A j * (1 + AF (j + 3))) := by
    intro j
    exact JointBudget.fixed_profile_transfer_bound hL (hAF _) (hA j).le
      (by omega : 3 + (rpar + 4) ≤ RF) (hprofile (j + 3))
      (hbound F hF hi hrank hFM hmetric hnormal hlow j)
  have hjoint (j : ℕ) (w) (hw : w ∈ J) :
      ‖iteratedFDeriv ℝ j
        (fun y : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
          fderiv ℝ (phase T Q y.1) y.2.2) w‖ ≤
        (A (j + 1) * (1 + AF (j + 1 + 3))) * L ^ (j - 1 - (rpar + 2)) := by
    apply (norm_iteratedFDeriv_fullPhase_parameter_fderiv_le T Q (hJO hw) j).trans
    convert norm_iteratedFDeriv_le_profile hJ (isOpen_domain T) hJO hS hSP (j + 1) hw using 1
    congr 2
    omega
  refine ⟨hjoint, ?_, ?_⟩
  · intro j k hj hk w hw
    exact (hjoint (j + k) w hw).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hL (by omega : j + k - 1 - (rpar + 2) ≤ j - 1))
      (mul_nonneg (hA _).le (by have := hAF (j + k + 1 + 3); positivity)))
  · intro j hj w hw
    apply (norm_iteratedFDeriv_physical_slice_le (isOpen_domain T)
      (contDiffOn_fullPhase_parameter_fderiv T Q) (hJO hw) j).trans
    exact (hjoint j w hw).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hL (by omega : j - 1 - (rpar + 2) ≤ j - 1))
      (mul_nonneg (hA _).le (by have := hAF (j + 1 + 3); positivity)))

omit Q in
/-- The physical gradient of the SAME phase has the companion grade, from
the primitive reserve-four gradient producer. Its joint profile is retained
for the geometric correction reconstruction; its mixed-order consequence
is the other half of `app:ch_waves:eq:graded-phase`. -/
theorem exists_fullPhase_gradient_grades {N : ℕ}
    {J : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hJ : IsCompact J) (hJO : J ⊆ domain T)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (M : ℝ) {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ)
    (AF : ℕ → ℝ) (hAF : ∀ j, 0 ≤ AF j) :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
      cNorm K 4 F ≤ M →
      (∀ x ∈ K, ∀ v, γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x, κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
      let Q := ⟨projectedStress F,
        contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
      ∀ (RF rpar : ℕ) (L : ℝ), 1 ≤ L → 14 + (rpar + 2) ≤ RF →
      HasDerivativeProfile K F RF L AF →
      HasDerivativeProfile J
        (fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
          phaseGradient T Q w.1 w.2.2) (rpar + 3) L C ∧
      (∀ j k : ℕ, 1 ≤ j → k ≤ rpar → ∀ w ∈ J,
        ‖iteratedFDeriv ℝ (j + k)
          (fun y : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
            phaseGradient T Q y.1 y.2.2) w‖ ≤ C (j + k) * L ^ (j - 1)) := by
  obtain ⟨A, hA, hbound⟩ := exists_phaseGradient_projected_sharp_bound
    (N := N) T hJ hJO hK hKU hball M hγ hκ
  refine ⟨fun j ↦ A j * (1 + AF (j + 4)),
    fun j ↦ mul_pos (hA _) (by have := hAF (j + 4); positivity), ?_⟩
  intro F hF hi hrank hFM hmetric hnormal hlow
  dsimp only
  let Q := (⟨projectedStress F,
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
    {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  intro RF rpar L hL hRF hprofile
  have hp : HasDerivativeProfile J
      (fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
        phaseGradient T Q w.1 w.2.2) (rpar + 3) L
          (fun j ↦ A j * (1 + AF (j + 4))) := by
    intro j
    exact JointBudget.fixed_profile_transfer_bound hL (hAF _) (hA j).le
      (by omega : 4 + (rpar + 3) ≤ RF) (hprofile (j + 4))
      (hbound F hF hi hrank hFM hmetric hnormal hlow j)
  refine ⟨hp, ?_⟩
  intro j k hj hk w hw
  exact (norm_iteratedFDeriv_le_profile hJ (isOpen_domain T) hJO
    (phaseGradient_joint_smooth T Q) hp (j + k) hw).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hL (by omega : j + k - (rpar + 3) ≤ j - 1))
        (mul_nonneg (hA _).le (by have := hAF (j + k + 4); positivity)))

end JanetCartan.RawPrimary.AmplitudeGrades
