module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualEstimates.ProjectedAssembly

/-!
# Actual finite-menu full-dispersion charts

The frozen incidence and family-existence premises of the chart estimates
are discharged by `exists_constructed_carrier_phases` and the literal frozen
cover. This retains the SAME current Hamilton charts for the geometric and
reserve-six forward/inverse/epsilon bounds in `app:ch_seed:prop:seed-phase-charts`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FullPhaseCharts.ActualEstimates
open ActualCarriers ActualCarriers.CurrentFullPhase FrozenMenu ActualPhase ActualComparison
open ProjectedStressFrame

/-- Construct the finite family and its actual full/transverse inverses, with
all forward, inverse and first-epsilon derivative estimates at immersion order `r+6`.
No frozen incidence, phase comparison, chart existence, or analytic estimate
is assumed. The immersion inputs are exactly the projected-stress setup
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem exists_finite_actual_full_phase_charts {n : ℕ} (hn : 5 ≤ n)
    {U : Set (Euclidean n)} (hU : IsOpen U) {bphysical : ℝ} (hbphysical : 0 < bphysical)
    (hBU : closedBall (0 : Euclidean n) bphysical ⊆ U) :
    ∃ (D : CoverData n) (c C : ℝ), D.IsValid c C ∧
      ∃ family : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
          PatchQuantitativeFamily (D.patches i.1 i.2) U hU,
        (∀ i, ∀ q ∈ (family i).data.localReference.stateDomain,
          q.1 ∈ ball (0 : Euclidean n) bphysical) ∧
        ∀ (b : Fin D.chartCount) (a : Fin (D.patchCount b)) (k : Euclidean n),
          k ≠ 0 → k ∈ D.domain b →
    let T := family ⟨b,a⟩
    let P := D.patches b a
    let z₀ := D.roots b a k
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    ∀ (N : ℕ) (KF : Set (Euclidean n)), IsCompact KF → KF ⊆ U →
      closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ KF →
      ∀ (C₀ κmet κ : ℝ), 0 < κmet → 0 < κ →
    ∃ G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1)),
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
  obtain ⟨D, c, C, hD, family, hphysical, _⟩ :=
    exists_constructed_carrier_phases hn hU hbphysical hBU
  refine ⟨D, c, C, hD, family, hphysical, ?_⟩
  intro b a k hk hkD
  dsimp only
  intro N KF hKF hKU hball C₀ κmet κ hκmet hκ
  obtain ⟨hP, hsec⟩ := hD.2.2.2.2.1 b a
  have hz := (hsec.2.1 k hkD).1
  have hi := (hsec.2.1 k hkD).2.2.2
  have hd : fderiv ℝ (fun z ↦ incidence k ((D.patches b a).toFun z))
      (D.roots b a k) (EuclideanSpace.single 0 1) ≠ 0 :=
    abs_pos.mp (hD.1.trans_le (hsec.2.2 k hkD _ (fun i ↦ (hz i).le)))
  refine ⟨FrozenIncidence.referenceEquiv (family ⟨b,a⟩) hP hz hi hd, ?_⟩
  exact exists_actual_projected_buffered_charts (family ⟨b,a⟩) hP hz hk hi hd
    hKF hKU hball C₀ hκmet hκ

end JanetCartan.FullPhaseCharts.ActualEstimates
