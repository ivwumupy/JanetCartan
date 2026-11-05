module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.RetainedLowBudget.PrincipalNormal
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.LeadingPrimitive.NormalBounds

/-!
# The retained normal from the already constructed null amplitude

The history constructor exports the reserve-thirteen null-amplitude estimate
before the initializer discards it. This leaf uses that estimate directly;
recovering the full flow estimates or redoing scalar transport is unnecessary.
Its concrete consumer is the strengthened initialized leading construction in
`RetainedLowBudget.Initialized`, for `app:ch_background:eq:bg-commutator`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumCommutator.RetainedLowBudget
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open LeadingWave LeadingWave.FullModulation ContinuumRow.LeadingPrimitive
open ProjectedStressFrame AmbientResponse

/-- The reserve-thirteen null estimate supplied by the actual leading-wave
producer gives a uniform order `μ+1` normal bound using only the original
order `μ+14` map and scalar budgets. Constants precede the varying maps,
flows and scalar. The null estimate is instantiated by `hsolution` in the
initialized construction; no normal or reflected-amplitude estimate is an
input (`app:ch_waves:eq:joint-tame`, `app:ch_background:eq:bg-commutator`). -/
theorem exists_fullNormal_low_bound_of_null_bounds {n N : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (z : Euclidean 3 × Euclidean (n - 1)) {σ : ℝ} (hσ : 0 < σ)
    (hJK : closedBall (0 : Euclidean n) (2 * σ) ⊆ K)
    (hJphase : closedBall ((0 : Euclidean n), z) (2 * σ) ⊆ domain T)
    (Kinitial : Set (Euclidean (n - 1) × Euclidean 3)) (B : ℕ → ℝ)
    {MF Mr κmet κnormal : ℝ} (hMF : 0 ≤ MF) (hMr : 0 ≤ Mr)
    (hκmet : 0 < κmet) (hκnormal : 0 < κnormal) :
    ∃ Cnormal > (0 : ℝ),
      ∀ (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
        (F : Euclidean n → Euclidean N) (row col : Fin n)
        (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
          Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
        (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
        (O : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))),
      Q.1 = projectedStress F →
      ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
      cNorm K (2 * (n + 1) + 14) F ≤ MF →
      cNorm Kinitial (2 * (n + 1) + 14) initial ≤ Mr →
      (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x,
        κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      closedBall ((0 : Euclidean n), z) (2 * σ) ⊆ O →
      ContDiffOn ℝ ∞ (fun w ↦ scalarAmplitude T Q F row col Φ Y initial w •
        nullvector T Q col w) O →
      (∀ j, cNorm (closedBall ((0 : Euclidean n), z) σ) j
          (fun w ↦ scalarAmplitude T Q F row col Φ Y initial w • nullvector T Q col w) ≤
        B j * (1 + cNorm K (j + 13) F + cNorm Kinitial (j + 13) initial)) →
      cNorm (closedBall ((0 : Euclidean n), z) σ) (2 * (n + 1) + 1)
        (fullNormal T Q F row col Φ Y initial) ≤ Cnormal := by
  let p := 2 * (n + 1) + 1
  let a := ((0 : Euclidean n), z)
  let J := closedBall a σ
  have hJ2 : J ⊆ closedBall a (2 * σ) := closedBall_subset_closedBall (by linarith)
  obtain ⟨G, hG, hphase⟩ := exists_phaseGradient_projected_sharp_bound T (N := N)
    (isCompact_closedBall _ _) (hJ2.trans hJphase) hK hKU hball MF hκmet hκnormal
  let Bcov := |B 1| * (1 + MF + Mr) + G 1 * (1 + MF)
  obtain ⟨E, hE, hrec⟩ := exists_cNorm_principalNormal_le_of_primitive_bounds
    (N := N) a hσ (by linarith : 0 < 1 + MF) hκmet hκnormal Bcov
  refine ⟨E p * (1 + MF + |B p| * (1 + MF + Mr) + G p * (1 + MF)),
    mul_pos (hE p) (by have := hG p; positivity), ?_⟩
  intro Q F row col Φ Y initial O hQ hF hi hrank hFM hrM hmet hnormal hJO hnull hbJ
  have hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold := by
    rw [← hQ]
    exact Q.2.2
  have hQeq : (⟨projectedStress F,
      contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
        {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
          cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (Q - fun _ ↦ cubeStress n) < T.family.threshold}) = Q := Subtype.ext hQ.symm
  have hξbound := hphase F hF hi hrank
    ((cNorm_mono_order (by omega : 4 ≤ 2 * (n + 1) + 14)).trans hFM) hmet hnormal hlow
  dsimp only at hξbound
  rw [hQeq] at hξbound
  let b := fun w ↦ scalarAmplitude T Q F row col Φ Y initial w • nullvector T Q col w
  let ξ : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) → Euclidean n :=
    fun w ↦ phaseGradient T Q w.1 w.2.2
  have hb (j : ℕ) (hj : j ≤ p) : cNorm J j b ≤ |B j| * (1 + MF + Mr) := by
    apply (hbJ j).trans
    apply mul_le_mul (le_abs_self _) _
      (by linarith [cNorm_nonneg K (j + 13) F, cNorm_nonneg Kinitial (j + 13) initial])
      (abs_nonneg _)
    exact add_le_add (add_le_add le_rfl
      ((cNorm_mono_order (by dsimp [p] at hj; omega)).trans hFM))
      ((cNorm_mono_order (by dsimp [p] at hj; omega)).trans hrM)
  have hξ (j : ℕ) (hj : j ≤ p) : cNorm J j ξ ≤ G j * (1 + MF) :=
    (hξbound j).trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl
      ((cNorm_mono_order (by dsimp [p] at hj; omega)).trans hFM)) (hG j).le)
  let U₀ := ball (0 : Euclidean n) (2 * σ)
  let V₀ := ball z (2 * σ)
  have hprod : U₀ ×ˢ V₀ ⊆ closedBall a (2 * σ) := by
    rw [show U₀ ×ˢ V₀ = ball a (2 * σ) from ball_prod_same ..]
    exact ball_subset_closedBall
  have hU₀U : U₀ ⊆ U := ball_subset_closedBall.trans (hJK.trans hKU)
  have hphysical : closedBall (0 : Euclidean n) σ ⊆ K :=
    (closedBall_subset_closedBall (by linarith)).trans hJK
  have hFmono (j) : cNorm (closedBall (0 : Euclidean n) σ) j F ≤ cNorm K j F :=
    cNorm_mono_set_of_contDiffAt hphysical hK
      (fun x hx ↦ (hF.contDiffAt (hU.mem_nhds (hKU hx))).of_le (by simp))
  have hbound := hrec U₀ V₀ isOpen_ball isOpen_ball
    (closedBall_subset_ball (by linarith)) (closedBall_subset_ball (by linarith))
    F b ξ (hF.mono hU₀U) (fun x hx ↦ hi x (hU₀U hx))
    (fun x hx ↦ hrank x (hU₀U hx)) (hnull.mono (hprod.trans hJO))
    ((phaseGradient_joint_smooth T Q).mono (hprod.trans hJphase))
    ((hFmono 4).trans ((cNorm_mono_order (by omega : 4 ≤ 2 * (n + 1) + 14)).trans
      (hFM.trans (by linarith))))
    (fun x hx ↦ hmet x (hphysical hx)) (fun x hx ↦ hnormal x (hphysical hx))
    ((hb 1 (by dsimp [p]; omega)).trans
      (le_add_of_nonneg_right (mul_nonneg (hG 1).le (by positivity))))
    ((hξ 1 (by dsimp [p]; omega)).trans
      (le_add_of_nonneg_left (mul_nonneg (abs_nonneg _) (by positivity)))) p
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (add_le_add le_rfl
      ((hFmono (p + 2)).trans ((cNorm_mono_order (by dsimp [p]; omega)).trans hFM)))
        (hb p le_rfl)) (hξ p le_rfl)) (hE p).le)

end JanetCartan.ContinuumCommutator.RetainedLowBudget
