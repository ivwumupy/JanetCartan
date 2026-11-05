module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualEstimates.ModulationOnCharts
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualEstimates.FullInverseBounds
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualEstimates.TransverseInverseBounds

/-!
# Actual inverse families with sharp phase bounds

Construct the full and transverse inverse families of
`app:ch_seed:prop:seed-phase-charts`, and discharge all inputs of their sharp
inverse/epsilon estimates. Every buffer, gap, threshold and high constant
precedes the current frame. The SAME `T.currentChart` is used throughout.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FullPhaseCharts.ActualEstimates
open ActualCarriers ActualCarriers.CurrentFullPhase FrozenMenu ActualPhase ActualComparison
open ActualInverses

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- Actual full/transverse buffered inverse geometry and sharp phase-order
`r+3` bounds for both inverses and their first epsilon derivatives. All analytic
premises of the inverse estimates are proved from primitive frame closeness;
no chart, phase or inverse estimate is assumed
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem exists_actual_buffered_inverse_phase_bounds {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0) :
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
          H m * (1 + cNorm (closedBall (0,covectorCenter T) T.family.radius)
            (m + 3) (current T Q)) := by
  dsimp only
  let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
  let G := FrozenIncidence.referenceEquiv T hP hz₀ hinc hd
  obtain ⟨ρF, hρF, δF, hδF, AF, hAF, hfull⟩ :=
    exists_full_inverse_phase_bounds T hP hz₀ ηb G
  obtain ⟨ρT, hρT, δT, hδT, AT, hAT, htrans⟩ :=
    exists_transverse_inverse_phase_bounds T hP hz₀ ηb
  obtain ⟨eM, heM, hmod⟩ := exists_modulation_on_chart_boxes T hP z₀ ηb
  obtain ⟨r, hr, hrcap, s, hs, hsr, hphys, hcarrier, e, he, hecap, δ₀, hδ₀,
    cF, hcF, bF, hbF, VF, LF, cT, hcT, bT, hbT, VT, LT, A, hA, B, hB,
    hVF, hVFc, hLFc, hLFV, hVT, hVTc, hLTc, hLTV, hgeom⟩ :=
    exists_actual_buffered_inverses_with_caps T hP hz₀ hk hinc hd
      (show 0 < min (min ρF ρT / 2) (1 / 4) by positivity)
      (show 0 < min (min ρF ρT) (eM / 4) by positivity)
  have hrsmall : r ≤ 1 / 4 := hrcap.trans (min_le_right _ _)
  have hrball : r ≤ min ρF ρT / 2 := hrcap.trans (min_le_left _ _)
  have heball : e ≤ min ρF ρT := hecap.trans (min_le_left _ _)
  have heM' : 2 * e < eM := by
    have := hecap.trans (min_le_right _ _)
    linarith
  have hrF : 2 * r ≤ ρF := by linarith [min_le_left ρF ρT]
  have hrT : 2 * r ≤ ρT := by linarith [min_le_right ρF ρT]
  have heF : e ≤ ρF := heball.trans (min_le_left _ _)
  have heT : e ≤ ρT := heball.trans (min_le_right _ _)
  let δ := min δ₀ (min δF δT)
  have hδ : 0 < δ := lt_min hδ₀ (lt_min hδF hδT)
  refine ⟨ρF, hρF, ρT, hρT, r, hr, s, hs, hsr, hphys, hcarrier, e, he, hrF, hrT, heF, heT, δ, hδ,
    cF, hcF, bF, hbF, VF, LF, cT, hcT, bT, hbT, VT, LT, A, hA, B, hB,
    fun m ↦ AF m + AT m, fun m ↦ add_pos (hAF m) (hAT m),
    hVF, hVFc, hLFc, hLFV, hVT, hVTc, hLTc, hLTV, ?_⟩
  intro Q hQ
  obtain ⟨hf, ht, hfgap, htgap, hfInv, htInv, hfe, hte, hann⟩ :=
    hgeom Q (hQ.trans_le (min_le_left _ _))
  have hm := hmod r s e hs hsr hrsmall heM' hphys hcarrier Q
  refine ⟨hf, ht, hfgap, htgap, hfInv, htInv, hfe, hte, hann, hm.1, hm.2, ?_⟩
  intro m
  have hfbound := hfull r s e bF cF VF LF hs he hsr hrF heF hbF hVFc Q
    (hQ.trans_le ((min_le_right _ _).trans (min_le_left _ _))) hfInv
    (hf.mono (prod_mono Subset.rfl
      (prod_mono (ball_subset_ball (by linarith)) (ball_subset_ball (by linarith))))) hfgap m
  have htbound := htrans r s e bT cT VT LT hs he hsr hrT heT hbT hVTc Q
    (hQ.trans_le ((min_le_right _ _).trans (min_le_right _ _))) htInv
    (ht.mono (prod_mono Subset.rfl (ball_subset_ball (by linarith)))) htgap m
  simpa only [add_mul] using add_le_add hfbound htbound

end JanetCartan.FullPhaseCharts.ActualEstimates
