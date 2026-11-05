module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualEstimates.PhaseAssembly

/-!
# Actual projected-stress chart estimates with reserve six

The sharp `m+3` Hamilton phase bound is applied at phase order `r+3`.
This closes the forward, inverse and first-epsilon derivative estimate at immersion
order `r+6` on the SAME constructed common charts, as required by
`app:ch_seed:prop:seed-phase-charts` and `app:ch_seed:eq:seed-phase-tame`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FullPhaseCharts.ActualEstimates
open ActualCarriers ActualCarriers.CurrentFullPhase FrozenMenu ActualPhase ActualComparison
open ProjectedStressFrame

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- Construct the actual full and transverse inverses and prove their joint
reserve-six estimates for both directions, including the first epsilon derivative. All constants
precede the immersion; only the primitive projected-stress hypotheses remain.
Neither phase estimates nor successful charts are premises
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem exists_actual_projected_buffered_charts {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {N : ℕ} {KF : Set (Euclidean n)} (hKF : IsCompact KF) (hKU : KF ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ KF)
    (C₀ : ℝ) {κmet κ : ℝ} (hκmet : 0 < κmet) (hκ : 0 < κ) :
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    let G := FrozenIncidence.referenceEquiv T hP hz₀ hinc hd
    ∃ ρF > (0 : ℝ), ∃ ρT > (0 : ℝ),
    ∃ r > (0 : ℝ), ∃ s > (0 : ℝ), s ≤ r ∧
    3 * r < T.family.radius / 8 ∧
    (closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) ∧
    ∃ e > (0 : ℝ), 2 * r ≤ ρF ∧ 2 * r ≤ ρT ∧ e ≤ ρF ∧ e ≤ ρT ∧
    ∃ δ > (0 : ℝ),
    ∃ cF > (0 : ℝ), ∃ bF > (0 : ℝ), ∃ VF LF : Set (ℝ × Euclidean (n - 1)),
    ∃ cT > (0 : ℝ), ∃ bT > (0 : ℝ), ∃ VT LT : Set (Euclidean (n - 1)),
    ∃ A > (0 : ℝ), ∃ B > (0 : ℝ),
    ∃ H : ℕ → ℝ, (∀ m, 0 < H m) ∧
      IsOpen VF ∧ IsCompact (closure VF) ∧ IsCompact LF ∧ LF ⊆ VF ∧
      IsOpen VT ∧ IsCompact (closure VT) ∧ IsCompact LT ∧ LT ⊆ VT ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm KF 4 F ≤ C₀ →
        (∀ x ∈ KF, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ KF, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (projectedStress F - fun _ ↦ cubeStress n) < δ →
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        ContDiffOn ℝ ∞ (Function.uncurry (fullChartFamily (current T Q) (spatialCarrier T)))
          (fullParameterSet z₀ s (2 * e) ×ˢ dataSet z₀ ηb (3 * r)) ∧
        ContDiffOn ℝ ∞ (Function.uncurry (transverseChartFamily (current T Q) (spatialCarrier T)))
          (transverseParameterSet z₀ s (2 * e) ×ˢ ball ηb (3 * r)) ∧
        (∀ p ∈ fullParameterSet z₀ s (2 * e), ∀ u ∈ dataBox z₀ ηb (2 * r),
          ‖(G.symm : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1))).comp
            (fderiv ℝ (fullChartFamily (current T Q) (spatialCarrier T) p) u) -
            ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2) ∧
        (∀ p ∈ transverseParameterSet z₀ s (2 * e), ∀ η ∈ closedBall ηb (2 * r),
          ‖fderiv ℝ (transverseChartFamily (current T Q) (spatialCarrier T) p) η -
            ContinuousLinearMap.id ℝ (Euclidean (n - 1))‖ ≤ 1 / 4) ∧
        BufferedPhaseInverse (fullChartFamily (current T Q) (spatialCarrier T))
          (fullParameterSet z₀ s (2 * e))
          (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r))
          VF LF bF cF G ∧
        BufferedPhaseInverse (transverseChartFamily (current T Q) (spatialCarrier T))
          (transverseParameterSet z₀ s (2 * e))
          (closedBall ηb r) (ball ηb (2 * r)) (closedBall ηb (2 * r))
          VT LT bT cT (ContinuousLinearEquiv.refl ℝ (Euclidean (n - 1))) ∧
        ContDiffOn ℝ ∞ (fun q :
            (ℝ × Euclidean 2 × WithLp 2 (ℝ × Euclidean (n - 1)) ×
              WithLp 2 (ℝ × Euclidean (n - 1))) × (ℝ × Euclidean (n - 1)) ↦
          deriv (fun ε ↦ phaseChartInverse (fullChartFamily (current T Q) (spatialCarrier T))
            (dataSet z₀ ηb (2 * r)) (ε,q.1.2) q.2) q.1.1)
          (fullParameterSet z₀ s (2 * e) ×ˢ VF) ∧
        ContDiffOn ℝ ∞ (fun q :
            (ℝ × Euclidean 2 × ℝ × ℝ × Euclidean (n - 1) × Euclidean (n - 1)) ×
              Euclidean (n - 1) ↦
          deriv (fun ε ↦ phaseChartInverse (transverseChartFamily (current T Q) (spatialCarrier T))
            (ball ηb (2 * r)) (ε,q.1.2) q.2) q.1.1)
          (transverseParameterSet z₀ s (2 * e) ×ˢ VT) ∧
        (∀ p ∈ fullParameterSet z₀ s (2 * e), ∀ u ∈ dataBox z₀ ηb (2 * r),
          ‖(fullChartFamily (current T Q) (spatialCarrier T) p u).2 - u.2‖ ≤ ‖u.2‖ / 2 ∧
          A ≤ ‖fullChartFamily (current T Q) (spatialCarrier T) p u‖ ∧
          ‖fullChartFamily (current T Q) (spatialCarrier T) p u‖ ≤ B) ∧
        ContDiffOn ℝ ∞ (fun q :
            (ℝ × Euclidean 2 × WithLp 2 (ℝ × Euclidean (n - 1)) ×
              WithLp 2 (ℝ × Euclidean (n - 1))) × (ℝ × Euclidean (n - 1)) ↦
          Comparison.modulationPhase (current T Q) (spatialCarrier T)
            q.1.1 q.1.2.1 q.2 q.1.2.2.1)
          (fullParameterSet z₀ s (2 * e) ×ˢ dataSet z₀ ηb (2 * r)) ∧
        (∀ p ∈ fullParameterSet z₀ s (2 * e), ∀ u ∈ dataSet z₀ ηb (2 * r),
          p.1 ≠ 0 →
          Comparison.modulationPhase (current T Q) (spatialCarrier T)
            p.1 p.2.1 u p.2.2.1 =
          (current T Q (p.2.2.1, spatialCarrier T (p.2.1,u.1) + p.1 • u.2) -
            current T Q (p.2.2.1, spatialCarrier T (p.2.1,u.1))) / p.1) ∧
        let fF := Function.uncurry (fullChartFamily (current T Q) (spatialCarrier T))
        let fT := fun q ↦ transverseChartFamily (current T Q) (spatialCarrier T)
          (transverseParameterReindex q.1) q.2
        let BF := closedBall (((0 : ℝ), spectatorCenter z₀,
          (0 : WithLp 2 (ℝ × Euclidean (n - 1))), (0 : WithLp 2 (ℝ × Euclidean (n - 1)))),
          (z₀ 0,ηb)) ρF
        let BT := closedBall (((0 : ℝ), (spectatorCenter z₀, (0 : ℝ), z₀ 0),
          (0 : Euclidean (n - 1)), (0 : Euclidean (n - 1))), ηb) ρT
        let gF := Function.uncurry (phaseChartInverse
          (fullChartFamily (current T Q) (spatialCarrier T)) (dataSet z₀ ηb (2 * r)))
        let gT := fun q ↦ phaseChartInverse
          (transverseChartFamily (current T Q) (spatialCarrier T)) (ball ηb (2 * r))
          (transverseParameterReindex q.1) q.2
        ∀ m,
          ((cNorm BF m fF + cNorm BF m
            (fun q ↦ deriv (fun ε ↦ fF ((ε,q.1.2),q.2)) q.1.1)) +
          (cNorm (fullParameterBox z₀ (s / 2) e ×ˢ closure VF) m gF +
          cNorm (fullParameterBox z₀ (s / 2) e ×ˢ closure VF) m
            (fun q ↦ deriv (fun ε ↦ gF ((ε,q.1.2),q.2)) q.1.1))) +
          ((cNorm BT m fT + cNorm BT m
            (fun q ↦ deriv (fun ε ↦ fT ((ε,q.1.2),q.2)) q.1.1)) +
          (cNorm (transversePrimitiveBox z₀ (s / 2) e ×ˢ closure VT) m gT +
          cNorm (transversePrimitiveBox z₀ (s / 2) e ×ˢ closure VT) m
            (fun q ↦ deriv (fun ε ↦ gT ((ε,q.1.2),q.2)) q.1.1))) ≤
          H m * (1 + cNorm KF (m + 6) F) := by
  dsimp only
  obtain ⟨ρF, hρF, ρT, hρT, r, hr, s, hs, hsr, hphys, hcarrier, e, he, hrF, hrT, heF, heT, δ, hδ,
    cF, hcF, bF, hbF, VF, LF, cT, hcT, bT, hbT, VT, LT, A, hA, B, hB,
    H, hH, hVF, hVFc, hLFc, hLFV, hVT, hVTc, hLTc, hLTV, hcharts⟩ :=
    exists_actual_buffered_inverse_phase_bounds T hP hz₀ hk hinc hd
  obtain ⟨D, hD, hphase⟩ := exists_current_projected_sharp_bound T (N := N) hKF hKU hball C₀ hκmet hκ
  refine ⟨ρF, hρF, ρT, hρT, r, hr, s, hs, hsr, hphys, hcarrier, e, he, hrF, hrT, heF, heT, δ, hδ,
    cF, hcF, bF, hbF, VF, LF, cT, hcT, bT, hbT, VT, LT, A, hA, B, hB,
    fun m ↦ H m * (1 + D (m + 3)), fun m ↦ mul_pos (hH m) (by linarith [hD (m + 3)]),
    hVF, hVFc, hLFc, hLFV, hVT, hVTc, hLTc, hLTV, ?_⟩
  intro F hF hi hrank hlowF hmet hnormal hlow hclose
  let Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold} := ⟨projectedStress F,
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
  obtain ⟨hf, ht, hfgap, htgap, hfInv, htInv, hfe, hte, hann, hmod, hdiv, hbound⟩ := hcharts Q hclose
  refine ⟨hf, ht, hfgap, htgap, hfInv, htInv, hfe, hte, hann, hmod, hdiv, ?_⟩
  intro m
  have hp := hphase F hF hi hrank hlowF hmet hnormal hlow (m + 3)
    (closedBall (0,covectorCenter T) T.family.radius) Subset.rfl
  simp only [show m + 3 + 3 = m + 6 by omega] at hp
  apply (hbound m).trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (hH m).le
  linarith [cNorm_nonneg KF (m + 6) F]

end JanetCartan.FullPhaseCharts.ActualEstimates
