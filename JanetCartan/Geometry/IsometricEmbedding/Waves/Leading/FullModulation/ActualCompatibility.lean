module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.CarrierCompatibility
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.Transport.LowBounds

/-!
# Quantitative comparison of the two actual transport constructions

The constructed flow budgets give uniform speeds; the named full coefficient
budget gives the Lipschitz constant needed for ODE uniqueness. These close the
quantitative inputs of `compatibility_on_common_buffer`, instantiated by
`exists_actual_positive_amplitude` (`app:ch_waves:thm:leading`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius NNReal
namespace JanetCartan.LeadingWave.FullModulation
open NullTransport ActualFlow ActualCarriers FrozenMenu CurrentFullPhase FlowAmplitude
open CarrierCompatibility

/-- The actual joint `C¹` flow budget controls its time velocity on the
original cylinder (`app:ch_waves:thm:leading`). -/
theorem flow_speed_le_cNorm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {p₀ : E} {R τ M : ℝ} (hR : 0 < R) (hτ : 0 < τ)
    {Φ : ℝ × E → E}
    (hΦ : ContDiffOn ℝ ∞ Φ (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p₀ (R / 4)))
    (hbound : cNorm (Icc (-τ) τ ×ˢ closedBall p₀ (R / 8)) 1 Φ ≤ M)
    {p : E} (hp : p ∈ ball p₀ (R / 8)) {t : ℝ} (ht : t ∈ Ioo (-τ) τ)
    {v : E} (hd : HasDerivAt (fun s ↦ Φ (s, p)) v t) : ‖v‖ ≤ M := by
  let J := Icc (-τ) τ ×ˢ closedBall p₀ (R / 8)
  have hJ : IsCompact J := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hreg (q : ℝ × E) (hq : q ∈ J) : ContDiffAt ℝ 1 Φ q := by
    apply (hΦ.contDiffAt ((isOpen_Ioo.prod isOpen_ball).mem_nhds ?_)).of_le (by simp)
    exact ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩,
      closedBall_subset_ball (by linarith) hq.2⟩
  have htp : (t, p) ∈ J := ⟨⟨ht.1.le, ht.2.le⟩, ball_subset_closedBall hp⟩
  have hf : ‖fderiv ℝ Φ (t, p)‖ ≤ M := by
    simpa only [norm_iteratedFDeriv_one] using
      (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hJ hreg htp le_rfl).trans hbound
  have hder := ((hreg (t, p) htp).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t p))
  have heq : v = fderiv ℝ Φ (t, p) (1, 0) := hd.unique hder
  rw [heq]
  simpa only [Prod.norm_def, norm_one, norm_zero, max_eq_left zero_le_one, mul_one] using
    ((fderiv ℝ Φ (t, p)).le_opNorm (1, 0)).trans
      (mul_le_mul_of_nonneg_right hf (norm_nonneg (1, (0 : E))))

/-- The actual full coefficient budget gives a uniform spatial Lipschitz
constant on the common uniqueness ball. No bound on a solution is assumed
(`app:ch_waves:thm:leading`). -/
theorem fullVelocity_lipschitz_of_direction_bound {n : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (row col : Fin n) {Ω K : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hd : ContDiffOn ℝ ∞ (transportDirection T Q row col) Ω)
    {M R τ : ℝ} (hM : 0 ≤ M) (hR : 0 < R) (hτR : τ ≤ R / 16)
    (hbound : cNorm K 1 (transportDirection T Q row col) ≤ M)
    {p₀ : Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))}
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall ((0 : ℝ), p₀) R) K)
    {t : ℝ} (ht : t ∈ Ioo (-τ) τ) :
    LipschitzOnWith ⟨liftedLowBound T M, liftedLowBound_nonneg T hM⟩
      (fullVelocity T Q row col t) (closedBall p₀ (R / 2)) := by
  let C := coordinates (Z := Euclidean 3 × Euclidean (n - 1))
    (adaptedCoordinates T.data.adapted)
  let J := closedBall ((0 : ℝ), p₀) R
  have hreg (q) (hq : q ∈ J) : DifferentiableAt ℝ (liftedDirection T Q row col) q :=
    ((contDiffOn_liftedDirection T Q row col hd).contDiffAt
      ((hΩ.preimage C.symm.continuous).mem_nhds (hKΩ (hbuffer hq)))).differentiableAt (by simp)
  have hlip : LipschitzOnWith ⟨liftedLowBound T M, liftedLowBound_nonneg T hM⟩
      (liftedDirection T Q row col) J := by
    apply (convex_closedBall _ _).lipschitzOnWith_of_nnnorm_fderiv_le hreg
    intro q hq
    exact (liftedDirection_low_bounds T Q row col hΩ hd hK hKΩ hM hbound (hbuffer hq)).2
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro p hp q hq
  have hmem {p} (hp : p ∈ closedBall p₀ (R / 2)) : (t, p) ∈ J := by
    rw [mem_closedBall, Prod.dist_eq, max_le_iff]
    refine ⟨?_, (mem_closedBall.mp hp).trans (by linarith)⟩
    simpa only [Real.dist_eq, sub_zero] using
      (abs_le.mpr ⟨ht.1.le, ht.2.le⟩).trans (show τ ≤ R by linarith)
  have hh := hlip.dist_le_mul _ (hmem hp) _ (hmem hq)
  have hv : dist (fullVelocity T Q row col t p) (fullVelocity T Q row col t q) ≤
      dist (liftedDirection T Q row col (t, p)) (liftedDirection T Q row col (t, q)) :=
    le_max_right _ _
  have he : dist (t, p) (t, q) = dist p q := by
    rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
  rw [he] at hh
  exact hv.trans hh

end JanetCartan.LeadingWave.FullModulation
