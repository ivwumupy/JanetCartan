module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.PhaseBounds
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.TameBounds

/-!
# Fixed working domains and full joint phase bounds

The full transport cylinder contains one physical product ball, fixed before
the immersion and at every derivative order. The phase bound includes the
spectator carrier label by its literal fixed projection. These inputs are
consumed by the actual full reconstruction estimate
(`app:ch_waves:eq:joint-tame`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace JanetCartan.LeadingWave.FullModulation
open ActualCarriers FrozenMenu CurrentFullPhase ProjectedStressFrame
open NullTransport ActualFlow FlowAmplitude FullPhaseCharts.ActualPhase

/-- A single fixed product ball lies inside the quantitative amplitude
cylinder and the original coefficient ball (`app:ch_waves:eq:joint-tame`). -/
theorem exists_full_joint_working_ball {n : ℕ} {P : Patch n}
    {c₀ C₀ : ℝ} (hP : P.IsValid c₀ C₀)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    (z : Euclidean 3) (hz : z ∈ parameterCube P.radius)
    {ρ R τ : ℝ} (hρ : 0 < ρ) (hR : 0 < R) (hτ : 0 < τ) :
    ∃ σ > (0 : ℝ),
      closedBall ((0 : Euclidean n), (z, T.reference.spatialPatch z)) (2 * σ) ⊆
        (coordinates (adaptedCoordinates T.data.adapted)).symm ''
          (Icc (-τ / 2) (τ / 2) ×ˢ
            closedBall ((0 : Euclidean (n - 1)), (z, T.reference.spatialPatch z)) (R / 64)) ∧
      closedBall ((0 : Euclidean n), (z, T.reference.spatialPatch z)) (2 * σ) ⊆
        closedBall ((0 : Euclidean n), (z, T.reference.spatialPatch z)) ρ ∧
      ∀ w ∈ closedBall ((0 : Euclidean n), (z, T.reference.spatialPatch z)) (2 * σ),
        w.2.2 ∈ ball (covectorCenter T) (min T.family.radius (3 * T.family.sourceRadius)) := by
  let zf := (z, T.reference.spatialPatch z)
  let a := ((0 : Euclidean n), zf)
  let C := coordinates (Z := Euclidean 3 × Euclidean (n - 1)) (adaptedCoordinates T.data.adapted)
  let O := C ⁻¹' (Ioo (-τ / 2) (τ / 2) ×ˢ
    ball ((0 : Euclidean (n - 1)), zf) (R / 64)) ∩
      (ball a ρ ∩ (fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦ w.2.2) ⁻¹'
        ball (covectorCenter T) (min T.family.radius (3 * T.family.sourceRadius)))
  have hO : IsOpen O := ((isOpen_Ioo.prod isOpen_ball).preimage C.continuous).inter
    (isOpen_ball.inter (isOpen_ball.preimage (continuous_snd.comp continuous_snd)))
  have hcenter : a ∈ O := by
    refine ⟨?_, mem_ball_self hρ, ?_⟩
    · change C a ∈ Ioo (-τ / 2) (τ / 2) ×ˢ
        ball ((0 : Euclidean (n - 1)), zf) (R / 64)
      have he : C a = (0, 0, zf) := by simp [C, a]
      rw [he]
      exact ⟨⟨by linarith, half_pos hτ⟩, mem_ball_self (by positivity)⟩
    · have hh := T.patch_buffer z (fun i ↦ (hz i).trans (by linarith [hP.1]))
      change (0, T.reference.spatialPatch z) ∈
        ball T.data.adapted.baseData.2 (min T.family.radius (3 * T.family.sourceRadius)) at hh
      simpa [mem_ball, Prod.dist_eq, FrozenPhaseReference.AdaptedSection.baseData,
        covectorCenter, a, zf, max_lt_iff] using hh
  obtain ⟨ε, hε, hεO⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hcenter)
  have hsub : closedBall a (2 * (ε / 4)) ⊆ O :=
    (closedBall_subset_ball (by linarith)).trans hεO
  refine ⟨ε / 4, by positivity, ?_, fun w hw ↦ ball_subset_closedBall (hsub hw).2.1,
    fun w hw ↦ (hsub hw).2.2⟩
  intro w hw
  exact ⟨C w, ⟨⟨(hsub hw).1.1.1.le, (hsub hw).1.1.2.le⟩,
    ball_subset_closedBall (hsub hw).1.2⟩, C.symm_apply_apply w⟩

/-- The actual full phase has the same reserve-three bound with the independent
carrier label included in the joint domain (`app:ch_waves:eq:joint-tame`). -/
theorem exists_phase_joint_projected_sharp_bound {n N : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
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
          (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        ∀ m, cNorm J m (fun w ↦ phase T Q w.1 w.2.2) ≤ A m * (1 + cNorm K (m + 3) F) := by
  let ψ := (zeroEnergyInclusion (n := n)).comp physicalCovectorProjection
  let L := closedBall (T.data.adapted.embedding T.data.adapted.baseData.1,
    T.data.adapted.baseData.2) T.family.radius
  have hψ : ∀ w ∈ J, ContDiffAt ℝ ∞ ψ w := fun _ _ ↦ ψ.contDiff.contDiffAt
  have hψL : MapsTo ψ J L := fun w hw ↦
    ball_subset_closedBall ((inclusion_mem_ball T (w := (w.1, w.2.2))).mpr (hJO hw))
  obtain ⟨D, hD, hd⟩ := ConstructedCarrierJets.exists_cNorm_fixed_pullback_le
    (G := ℝ) hJ (isCompact_closedBall _ _) hψ hψL
  obtain ⟨A, hA, ha⟩ := T.exists_projected_phase_sharp_bound (N := N) hK hKU hball M hγ hκ
  refine ⟨fun m ↦ D m * A m, fun m ↦ mul_pos (hD m) (hA m), ?_⟩
  intro F hF hi hrank hFM hmet hnormal hlow
  dsimp only
  let Q := (⟨projectedStress F,
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
    {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  have hs : ∀ x ∈ L, ContDiffAt ℝ ∞ (HamiltonPhase.phase (T.currentChart Q).coordinates) x :=
    fun x hx ↦ (T.family.phase_smooth Q).contDiffAt (isOpen_ball.mem_nhds
      (closedBall_subset_ball (by linarith [T.family.radius_pos]) hx))
  intro m
  exact (hd _ hs m).trans ((mul_le_mul_of_nonneg_left
    (ha F hF hi hrank hFM hmet hnormal hlow m) (hD m).le).trans_eq (by ring))

end JanetCartan.LeadingWave.FullModulation
