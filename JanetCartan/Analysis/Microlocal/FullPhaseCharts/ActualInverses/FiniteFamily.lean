module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualInverses

/-!
# Finite actual chart geometry from the constructed carrier family

Instantiate the frozen incidence hypotheses using the actual finite cover.
The menu and the Hamilton families are constructed before any current frame;
for each fixed incidence direction the geometric conclusions of
`app:ch_seed:prop:seed-phase-charts` then follow from primitive frame closeness.
The sharp inverse/epsilon tame estimates remain a separate obligation.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.FullPhaseCharts.ActualInverses
open ActualCarriers ActualCarriers.CurrentFullPhase FrozenMenu ActualPhase ActualComparison

/-- Construct the finite menu and its SAME current Hamilton charts from
`5 ≤ n`, then construct full and transverse buffered inverse geometry at
every fixed nonzero incidence direction in that cover. No phase existence,
incidence transversality, chart comparison or inverse gap is assumed
(`app:ch_seed:prop:seed-phase-charts`, geometric conclusions). -/
theorem exists_finite_actual_buffered_charts {n : ℕ} (hn : 5 ≤ n)
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
    ∃ G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1)),
    ∃ r > (0 : ℝ), ∃ s > (0 : ℝ), s ≤ r ∧
    3 * r < T.family.radius / 8 ∧
    (closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) ∧
    ∃ e > (0 : ℝ), ∃ δ > (0 : ℝ),
    ∃ cF > (0 : ℝ), ∃ bF > (0 : ℝ), ∃ VF LF : Set (ℝ × Euclidean (n - 1)),
    ∃ cT > (0 : ℝ), ∃ bT > (0 : ℝ), ∃ VT LT : Set (Euclidean (n - 1)),
    ∃ A > (0 : ℝ), ∃ B > (0 : ℝ),
      IsOpen VF ∧ IsCompact (closure VF) ∧ IsCompact LF ∧ LF ⊆ VF ∧
      IsOpen VT ∧ IsCompact (closure VT) ∧ IsCompact LT ∧ LT ⊆ VT ∧
      ∀ Q,
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress n) < δ →
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
        ∀ p ∈ fullParameterSet z₀ s (2 * e), ∀ u ∈ dataBox z₀ ηb (2 * r),
          ‖(fullChartFamily (current T Q) (spatialCarrier T) p u).2 - u.2‖ ≤ ‖u.2‖ / 2 ∧
          A ≤ ‖fullChartFamily (current T Q) (spatialCarrier T) p u‖ ∧
          ‖fullChartFamily (current T Q) (spatialCarrier T) p u‖ ≤ B := by
  obtain ⟨D, c, C, hD, family, hphysical, _⟩ :=
    exists_constructed_carrier_phases hn hU hbphysical hBU
  refine ⟨D, c, C, hD, family, hphysical, ?_⟩
  intro b a k hk hkD
  obtain ⟨hP, hsec⟩ := hD.2.2.2.2.1 b a
  have hz := (hsec.2.1 k hkD).1
  have hi := (hsec.2.1 k hkD).2.2.2
  have hd : fderiv ℝ (fun z ↦ incidence k ((D.patches b a).toFun z))
      (D.roots b a k) (EuclideanSpace.single 0 1) ≠ 0 :=
    abs_pos.mp (hD.1.trans_le (hsec.2.2 k hkD _ (fun i ↦ (hz i).le)))
  refine ⟨FrozenIncidence.referenceEquiv (family ⟨b,a⟩) hP hz hi hd, ?_⟩
  exact exists_actual_buffered_inverses (family ⟨b,a⟩) hP hz hk hi hd

end JanetCartan.FullPhaseCharts.ActualInverses
