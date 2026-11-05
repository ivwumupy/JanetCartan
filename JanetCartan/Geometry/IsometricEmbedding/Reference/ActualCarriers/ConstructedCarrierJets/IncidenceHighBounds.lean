module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedCarrierJets.IncidenceDomain

/-!
# Projected frame and carrier budgets in incidence variables

These supply the three high primitive bounds of
`exists_cNorm_incidence_root_le_reserve_six` directly from the original immersion,
its separate gaps and its primitive frame neighborhood. No root is used.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu ConstructedCarrierJets ProjectedStressFrame
variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- The literal incidence pullbacks have frame loss two, carrier-gradient
loss four, and a fixed testing-covector budget. All constants precede the
immersion and all high orders (`app:ch_seed:eq:seed-frame-tame`,
`app:ch_seed:eq:seed-phase-tame`, actual-menu Step 3). -/
theorem exists_projected_incidence_high_budgets {N : ℕ}
    {c C : ℝ} (hP : P.IsValid c C)
    (a : (Euclidean n × Euclidean n) × ℝ) (ρ : ℝ) (z : Euclidean 3)
    {Kx : Set (Euclidean n)} {Kz : Set (Euclidean 3)}
    (hKx : IsCompact Kx) (hKz : IsCompact Kz)
    (hKxO : Kx ⊆ ball (0 : Euclidean n) T.physicalRadius)
    (hKzO : Kz ⊆ parameterInterior (2 * P.radius))
    (hKxframe : Kx ⊆ closedBall (0 : Euclidean n) T.data.localReference.stateRadius)
    (hx : closedBall a.1.1 ρ ⊆ Kx)
    (hz : ∀ t ∈ Icc (a.2 - ρ) (a.2 + ρ), incidenceParameter z t ∈ Kz)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (C₀ : ℝ) {κmet κ : ℝ} (hκmet : 0 < κmet) (hκ : 0 < κ) :
    ∃ A B D : ℕ → ℝ, (∀ m, 0 < A m) ∧ (∀ m, 0 < B m) ∧ (∀ m, 0 < D m) ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K 4 F ≤ C₀ →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold} := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        ∀ m,
          cNorm (closedBall a ρ) m (fun p ↦ projectedStress F p.1.1) ≤
            A m * (1 + cNorm K (m + 2) F) ∧
          cNorm (closedBall a ρ) m
            (fun p ↦ T.carrierGradient Q p.1.1 (incidenceParameter z p.2)) ≤
            B m * (1 + cNorm K (m + 4) F) ∧
          cNorm (closedBall a ρ) m (fun p ↦ p.1.2) ≤ D m := by
  obtain ⟨A₀, B₀, D, hA₀, hB₀, hD, hframe, hgrad, hk⟩ :=
    exists_incidence_coordinate_budgets a ρ hKx hKz z hx hz
  obtain ⟨B₁, hB₁, hb₁⟩ := T.exists_projected_carrierGradient_sharp_bound
    (N := N) hP (hKx.prod hKz) (Set.prod_mono hKxO hKzO) hK hKU hball C₀ hκmet hκ
  choose A₁ hA₁ ha₁ using fun m ↦ exists_cNorm_projectedStress_le_tame
    (N := N) (0 : Euclidean n) T.data.localReference.stateRadius_pos C₀ hκmet hκ m
  refine ⟨fun m ↦ A₀ m * ((m + 1) * A₁ m), fun m ↦ B₀ m * B₁ m, D,
    fun m ↦ mul_pos (hA₀ m) (mul_pos (by positivity) (hA₁ m)),
    fun m ↦ mul_pos (hB₀ m) (hB₁ m), hD, ?_⟩
  intro F hF hi hrank hlowF hmet hnormal hlow
  dsimp only
  intro m
  let Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold} := ⟨projectedStress F,
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
  have hs : ContDiffOn ℝ ∞ (projectedStress F) U := Q.2.1
  have hat : ∀ x ∈ Kx, ContDiffAt ℝ ∞ (projectedStress F) x :=
    fun x hx ↦ hs.contDiffAt (hU.mem_nhds (hKU (hball (hKxframe hx))))
  have hcomponent := ha₁ m F U K hU hK hball hKU hF hi hlowF hmet hnormal
  have hbframe := frame_cNorm_le_of_componentwise
    (isCompact_closedBall (0 : Euclidean n) T.data.localReference.stateRadius)
    (fun x hx ↦ (hs.contDiffAt (hU.mem_nhds (hKU (hball hx)))).of_le
      (by simp : (m : ℕ∞ω) ≤ ∞))
    (mul_nonneg (hA₁ m).le (by linarith [cNorm_nonneg K (m + 2) F])) hcomponent
  have hmono : cNorm Kx m (projectedStress F) ≤
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) m
        (projectedStress F) := cNorm_mono_set_of_contDiffAt hKxframe (isCompact_closedBall _ _)
      (fun x hx ↦ (hs.contDiffAt (hU.mem_nhds (hKU (hball hx)))).of_le (by simp))
  refine ⟨(hframe _ hat m).trans ?_, (hgrad _ (fun q hq ↦
    (T.carrierGradient_smooth hP Q).contDiffAt
      ((isOpen_ball.prod (isOpen_parameterInterior _)).mem_nhds
        ⟨hKxO hq.1, hKzO hq.2⟩)) m).trans ?_, hk m⟩
  · exact (mul_le_mul_of_nonneg_left (hmono.trans hbframe) (hA₀ m).le).trans_eq (by ring)
  · exact (mul_le_mul_of_nonneg_left
      (hb₁ F hF hi hrank hlowF hmet hnormal hlow m) (hB₀ m).le).trans_eq (by ring)

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
