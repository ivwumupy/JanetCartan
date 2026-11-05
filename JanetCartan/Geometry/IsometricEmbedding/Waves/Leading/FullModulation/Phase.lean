module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualPhaseBounds

/-!
# The retained leading phase with an independent full covector

The transport construction for `app:ch_waves:thm:leading` must allow the full
spatial covector to vary independently of the three carrier parameters. These
are restrictions of the SAME `T.currentChart`, with exact agreement on the
carrier graph. Characteristicity, the initial value, and the sharp phase bound
are proved from the existing Hamilton construction. The full transport
extension consumes these results; its existence is not asserted here.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.LeadingWave.FullModulation
open ActualCarriers FrozenMenu CurrentFullPhase HamiltonPhase
open FullPhaseCharts.ActualPhase

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The zero-energy inclusion with the full spatial covector still free
(`app:ch_waves:thm:leading`). -/
def zeroEnergyInclusion : Euclidean n × Euclidean (n - 1) →L[ℝ]
    Euclidean n × (ℝ × Euclidean (n - 1)) :=
  (ContinuousLinearMap.fst ℝ _ _).prod
    ((0 : Euclidean n × Euclidean (n - 1) →L[ℝ] ℝ).prod
      (ContinuousLinearMap.snd ℝ _ _))

/-- This literal restriction costs no operator norm
(`app:ch_waves:eq:joint-tame`). -/
theorem norm_zeroEnergyInclusion_le : ‖zeroEnergyInclusion (n := n)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro w
  simp [zeroEnergyInclusion, Prod.norm_def]

/-- Fixed full-covector domain inside the current and frozen chart targets
(`app:ch_waves:thm:leading`). -/
def phaseDomain : Set (Euclidean n × Euclidean (n - 1)) :=
  ball (0, covectorCenter T) T.family.radius

/-- The physical full phase, before carrier restriction
(`app:ch_waves:thm:leading`). -/
def phase (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (x : Euclidean n) (ζ : Euclidean (n - 1)) : ℝ :=
  carrierPhase (T.currentChart Q) id x ζ

/-- The physical gradient of that same full phase
(`app:ch_waves:eq:arbitrary-b-amplitudes`). -/
def phaseGradient (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (x : Euclidean n) (ζ : Euclidean (n - 1)) : Euclidean n :=
  gradient (fun y ↦ phase T Q y ζ) x

/-- The zero-energy inclusion preserves distance to the fixed phase center
(`app:ch_waves:thm:leading`). -/
theorem inclusion_mem_ball {r : ℝ} {w : Euclidean n × Euclidean (n - 1)} :
    zeroEnergyInclusion w ∈ ball
      (T.data.adapted.embedding T.data.adapted.baseData.1, T.data.adapted.baseData.2) r ↔
      w ∈ ball (0, covectorCenter T) r := by
  simp [zeroEnergyInclusion, mem_ball, Prod.dist_eq,
    FrozenPhaseReference.AdaptedSection.baseData, covectorCenter]

/-- The corresponding closed-ball containment used in the sharp bound
(`app:ch_waves:eq:joint-tame`). -/
theorem inclusion_mem_closedBall {r : ℝ} {w : Euclidean n × Euclidean (n - 1)} :
    zeroEnergyInclusion w ∈ closedBall
      (T.data.adapted.embedding T.data.adapted.baseData.1, T.data.adapted.baseData.2) r ↔
      w ∈ closedBall (0, covectorCenter T) r := by
  simp [zeroEnergyInclusion, mem_closedBall, Prod.dist_eq,
    FrozenPhaseReference.AdaptedSection.baseData, covectorCenter]

/-- The original doubled carrier patch lies in the full phase domain
(`app:ch_waves:thm:leading`). -/
theorem carrier_mem_phaseDomain {x : Euclidean n}
    (hx : x ∈ ball 0 T.physicalRadius) {z : Euclidean 3}
    (hz : z ∈ parameterCube (2 * P.radius)) :
    (x, T.reference.spatialPatch z) ∈ phaseDomain T :=
  (inclusion_mem_ball T).mp (T.target_contains_closed hx hz)

/-- Exact carrier agreement; no new Hamilton family is selected
(`app:ch_waves:thm:leading`). -/
theorem phase_on_carrier (Q : _) (x : Euclidean n) (z : Euclidean 3) :
    phase T Q x (T.reference.spatialPatch z) = T.carrier Q x z := rfl

/-- Exact gradient agreement on the carrier graph
(`app:ch_waves:eq:arbitrary-b-amplitudes`). -/
theorem phaseGradient_on_carrier (Q : _) (x : Euclidean n) (z : Euclidean 3) :
    phaseGradient T Q x (T.reference.spatialPatch z) = T.carrierGradient Q x z := rfl

/-- Agreement with the full phase used by the actual modulation and quotient
charts, including its orthogonal physical coordinates
(`app:ch_seed:prop:seed-phase-charts`, `app:ch_waves:thm:leading`). -/
theorem phase_in_adapted_coordinates (Q : _)
    (q : WithLp 2 (ℝ × Euclidean (n - 1)) × Euclidean (n - 1)) :
    phase T Q (FullPhaseCharts.adaptedSpacetime T.data.adapted q.1) q.2 =
      FullPhaseCharts.ActualPhase.current T Q q := rfl

/-- Joint full-phase smoothness on a fixed open enlargement
(`app:ch_waves:eq:joint-tame`). -/
theorem phase_smooth (Q : _) :
    ContDiffOn ℝ ∞ (fun w : Euclidean n × Euclidean (n - 1) ↦ phase T Q w.1 w.2)
      (ball (0, covectorCenter T) (2 * T.family.radius)) :=
  (T.family.phase_smooth Q).comp zeroEnergyInclusion.contDiff.contDiffOn
    (fun _ hw ↦ (inclusion_mem_ball T).mpr hw)

/-- The full gradient is the momentum of the retained chart
(`app:ch_waves:thm:leading`). -/
theorem phaseGradient_eq_chartMomentum (Q : _) {w : Euclidean n × Euclidean (n - 1)}
    (hw : w ∈ phaseDomain T) :
    phaseGradient T Q w.1 w.2 = (T.currentChart Q).chartMomentum (w.1, (0, w.2)) :=
  (hasGradientAt_carrierPhase (T.currentChart Q) id ((inclusion_mem_ball T).mpr hw)).gradient

/-- Joint smoothness of the full gradient on the original chart target
(`app:ch_waves:eq:joint-tame`). -/
theorem phaseGradient_smooth (Q : _) :
    ContDiffOn ℝ ∞ (fun w : Euclidean n × Euclidean (n - 1) ↦ phaseGradient T Q w.1 w.2)
      (phaseDomain T) := by
  have hc : ContDiffOn ℝ ∞ (T.currentChart Q).coordinates (T.currentChart Q).target :=
    (T.family.coordinates_smooth Q).mono
      (ball_subset_ball (by linarith [T.family.radius_pos]))
  have hm := ((T.currentChart Q).contDiffOn_chartMomentum
    (T.family.momentum_smooth Q) hc).comp zeroEnergyInclusion.contDiff.contDiffOn
      (fun _ hw ↦ (inclusion_mem_ball T).mpr hw)
  exact hm.congr (fun w hw ↦ phaseGradient_eq_chartMomentum T Q hw)

/-- The full phase satisfies the literal projected determinant equation, with
no restriction to the three carrier parameters (`app:ch_waves:thm:leading`). -/
theorem phase_characteristic (Q : _) {w : Euclidean n × Euclidean (n - 1)}
    (hw : w ∈ phaseDomain T) : determinant (Q.1 w.1) (phaseGradient T Q w.1 w.2) = 0 :=
  carrierPhase_normalizedSymbol_determinant_eq_zero hU Q.1 Q.2.1
    (T.currentChart Q) id ((inclusion_mem_ball T).mpr hw)

/-- The literal full phase has the prescribed section value on the original
source buffer (`app:ch_waves:thm:leading`). -/
theorem phase_initial_value (Q : _) {y : Euclidean (n - 1)}
    (hy : ‖y‖ < T.physicalRadius) {ζ : Euclidean (n - 1)}
    (hζ : ζ ∈ ball (covectorCenter T) (min T.family.radius (3 * T.family.sourceRadius))) :
    phase T Q (T.data.adapted.embedding y) ζ = ⟪y, ζ⟫_ℝ := by
  have hlt : T.physicalRadius < 3 * T.family.sourceRadius := by
    have hh := min_le_right T.family.radius (3 * T.family.sourceRadius)
    have hp := T.physicalRadius_pos
    dsimp only [PatchQuantitativeFamily.physicalRadius] at hp ⊢
    linarith
  have hball : (0, (y, (0, ζ))) ∈
      ball ((0 : ℝ), T.data.adapted.baseData) (3 * T.family.sourceRadius) := by
    have hz := (mem_ball.mp hζ).trans_le (min_le_right _ _)
    simpa [mem_ball, Prod.dist_eq, FrozenPhaseReference.AdaptedSection.baseData,
      covectorCenter, max_lt_iff] using And.intro (hy.trans hlt) hz
  have hadm := T.family.source_admissible Q hball
  have hs : (0, (y, (0, ζ))) ∈ (T.currentChart Q).source := by
    rw [PatchQuantitativeFamily.currentChart,
      restrictChart_source_eq _ _ _ (T.family.source_eq Q)]
    refine ⟨hball, ?_⟩
    change ((T.family.flow Q).position (0, (y, (0, ζ))), (0, ζ)) ∈ T.target
    rw [(T.family.flow Q).initial_position _ hadm.2, T.family.section_eq]
    change (T.data.adapted.embedding y, (0, ζ)) ∈
      ball (T.data.adapted.embedding T.data.adapted.baseData.1, T.data.adapted.baseData.2)
        T.family.radius
    apply (inclusion_mem_ball T (w := (T.data.adapted.embedding y, ζ))).mpr
    have hxr : T.physicalRadius < T.family.radius := by
      have hh := min_le_left T.family.radius (3 * T.family.sourceRadius)
      have hp := T.physicalRadius_pos
      dsimp only [PatchQuantitativeFamily.physicalRadius] at hp ⊢
      linarith
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨by simpa using hy.trans hxr, (mem_ball.mp hζ).trans_le (min_le_left _ _)⟩
  simpa only [phase, carrierPhase, id_eq, T.family.section_eq,
    LinearIsometry.coe_toContinuousLinearMap] using (T.currentChart Q).initial_value hs

/-- Sharp one-high full-phase bounds retain immersion order `m+3` on the same
fixed domains. All constants precede the current immersion
(`app:ch_waves:eq:joint-tame`). -/
theorem exists_phase_projected_sharp_bound {N : ℕ}
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
        ∀ m J, J ⊆ closedBall (0, covectorCenter T) T.family.radius →
          cNorm J m (fun w ↦ phase T Q w.1 w.2) ≤ A m * (1 + cNorm K (m + 3) F) := by
  obtain ⟨A, hA, hb⟩ := T.exists_projected_phase_sharp_bound hK hKU hball M hγ hκ
  refine ⟨fun m ↦ (m + 1 : ℝ) * A m, fun m ↦ mul_pos (by positivity) (hA m), ?_⟩
  intro F hF hi hrank hFM hmet hnormal hlow Q m J hJ
  have hc := FullPhaseCharts.InverseEstimates.cNorm_comp_contraction_le_on
    (zeroEnergyInclusion (n := n)) norm_zeroEnergyInclusion_le
    (isCompact_closedBall _ _) isOpen_ball
    (closedBall_subset_ball (by linarith [T.family.radius_pos] :
      T.family.radius < 2 * T.family.radius))
    (T.family.phase_smooth Q) (fun _ hw ↦ (inclusion_mem_closedBall T).mpr (hJ hw)) m
  exact hc.trans ((mul_le_mul_of_nonneg_left
    (hb F hF hi hrank hFM hmet hnormal hlow m) (by positivity)).trans_eq
      (mul_assoc _ _ _).symm)

end JanetCartan.LeadingWave.FullModulation
