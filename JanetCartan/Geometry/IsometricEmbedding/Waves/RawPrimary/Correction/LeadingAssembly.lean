module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.LeadingInputs
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.Correction.ComplexWKB

/-!
# Cubic residual from the retained leading-family outputs

For `app:ch_waves:eq:WKB-residual`, the actual reduced transport equation
supplies solvability directly. The two nonzero adjugate nullvectors supply
the SAME selected minor, and joint regularity supplies all physical
differentiability. Thus the residual has no additional denominator, inverse,
correction regularity, or cancellation premise. The inputs below are retained
by `FullModulation.exists_finite_actual_leading_family`; the common-family
construction must apply them to its chosen flow and original scalar datum.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Matrix
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary
open NullTransport LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (Metric.closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}

/-- The retained reduced transport equation places the full complex inclusion
in the orthogonal range, with both quadratures
(`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem fullLeadingCovector_mem_complexSymbolRangePerp
    {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))}
    (htransport : conullvector T Q row w ⬝ᵥ reducedOperator F Q.1
      (fun x ↦ scalarAmplitude T Q F row col Φ Y r (x, w.2) •
        nullvector T Q col (x, w.2)) w.1 = 0) :
    euclideanComplexInclusion (WithLp.toLp 2 (reducedOperator F Q.1
      (fun x ↦ fullLeadingCovector T Q F row col Φ Y r (x, w.2)) w.1)) ∈
        complexSymbolRangePerp (reducedSymbol (Q.1 w.1)
          (phaseGradient T Q w.1 w.2.2)) row := by
  rw [mem_complexSymbolRangePerp]
  simp only [euclideanComplexInclusion_apply, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨htransport, by simp [dotProduct]⟩

/-- Apply `WKB.algebraicCorrection_cancel` to the SAME correction using the
actual leading outputs. The selected minor and all differentiability inputs
are deduced here (`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem fullCorrectionCovector_wkb_cancel_of_leading_outputs
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))} (hw : w ∈ Ω)
    (hQ : ∀ i, (Q.1 w.1 i).IsSymm)
    (hk : nullvector T Q col w ≠ 0) (hl : conullvector T Q row w ≠ 0)
    (htransport : conullvector T Q row w ⬝ᵥ reducedOperator F Q.1
      (fun x ↦ scalarAmplitude T Q F row col Φ Y r (x, w.2) •
        nullvector T Q col (x, w.2)) w.1 = 0) :
    Complex.I • WKB.principalSymbol (complexReducedDerivative Q.1)
      (fun x ↦ phase T Q x w.2.2) w.1 (fullCorrectionCovector T Q F row col Φ Y r w) +
      WKB.firstOrderApply (complexReducedDerivative Q.1) (complexReducedValue F Q.1)
        (fun x ↦ euclideanComplexInclusion (fullLeadingCovector T Q F row col Φ Y r (x, w.2)))
          w.1 = 0 := by
  have hm := fullPhase_minor_ne_zero_of_nullvectors T Q row col (hphase w hw) hk hl
  have ha := ((contDiffOn_fullLeadingCovector T Q F row col Φ Y r hspace hphase hα).contDiffAt
    (hΩ.mem_nhds hw)).differentiableAt (by simp)
  have hax : DifferentiableAt ℝ
      (fun x ↦ fullLeadingCovector T Q F row col Φ Y r (x, w.2)) w.1 :=
    ha.comp w.1 (f := fun x : Euclidean n ↦ (x, w.2)) (differentiableAt_id.prodMk (differentiableAt_const _))
  have hc : DifferentiableAt ℝ (fun x ↦ euclideanComplexInclusion
      (fullLeadingCovector T Q F row col Φ Y r (x, w.2))) w.1 :=
    euclideanComplexInclusion.differentiableAt.comp w.1 hax
  have hp := fullLeadingCovector_mem_complexSymbolRangePerp T Q F row col Φ Y r htransport
  rw [← complexReducedOperator_eq_firstOrder F Q.1 hc,
    complexReducedOperator_inclusion F Q.1 hQ hax,
    fullCorrectionCovector_eq_algebraicCorrection T Q F row col Φ Y r (hphase w hw) hm hp]
  apply WKB.algebraicCorrection_cancel
  intro v
  rw [complexReduced_principalSymbol Q.1 _ _ hQ]
  rfl

/-- The literal two-term wave has the cubic reduced residual on the actual
leading domain. In particular, correction differentiability is proved from
the primitive geometry and leading outputs rather than assumed
(`app:ch_waves:eq:WKB-residual`). -/
theorem fullTwoTermWave_reduced_residual_of_leading_outputs
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)
    (htransport : ∀ w ∈ Ω, conullvector T Q row w ⬝ᵥ reducedOperator F Q.1
      (fun x ↦ scalarAmplitude T Q F row col Φ Y r (x, w.2) •
        nullvector T Q col (x, w.2)) w.1 = 0)
    {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))} (hw : w ∈ Ω)
    (hQ : ∀ i, (Q.1 w.1 i).IsSymm) {lam : ℝ} (hlam : lam ≠ 0) :
    complexReducedOperator F Q.1
      (twoTermWave lam (fun x ↦ phase T Q x w.2.2)
        (fun x ↦ euclideanComplexInclusion (fullLeadingCovector T Q F row col Φ Y r (x, w.2)))
        (fun x ↦ fullCorrectionCovector T Q F row col Φ Y r (x, w.2))) w.1 =
      waveCarrier lam (fun x ↦ phase T Q x w.2.2) w.1 •
        (((lam : ℂ)⁻¹)^3 • complexReducedOperator F Q.1
          (fun x ↦ fullCorrectionCovector T Q F row col Φ Y r (x, w.2)) w.1) := by
  have hφ := fullPhase_physical_differentiableAt T Q (hphase w hw)
  have haJoint := ((contDiffOn_fullLeadingCovector T Q F row col Φ Y r hspace hphase hα).contDiffAt
    (hΩ.mem_nhds hw)).differentiableAt (by simp)
  have hax : DifferentiableAt ℝ
      (fun x ↦ fullLeadingCovector T Q F row col Φ Y r (x, w.2)) w.1 :=
    haJoint.comp w.1 (f := fun x : Euclidean n ↦ (x, w.2)) (differentiableAt_id.prodMk (differentiableAt_const _))
  have ha : DifferentiableAt ℝ (fun x ↦ euclideanComplexInclusion
      (fullLeadingCovector T Q F row col Φ Y r (x, w.2))) w.1 :=
    euclideanComplexInclusion.differentiableAt.comp w.1 hax
  have hbJoint := ((contDiffOn_fullCorrectionCovector_of_leading_outputs
    T Q F row col Φ Y r hΩ hspace hphase hF hi hα hnonzero).contDiffAt
      (hΩ.mem_nhds hw)).differentiableAt (by simp)
  have hb : DifferentiableAt ℝ
      (fun x ↦ fullCorrectionCovector T Q F row col Φ Y r (x, w.2)) w.1 :=
    hbJoint.comp w.1 (f := fun x : Euclidean n ↦ (x, w.2)) (differentiableAt_id.prodMk (differentiableAt_const _))
  have ht : DifferentiableAt ℝ
      (twoTermWave lam (fun x ↦ phase T Q x w.2.2)
        (fun x ↦ euclideanComplexInclusion (fullLeadingCovector T Q F row col Φ Y r (x, w.2)))
        (fun x ↦ fullCorrectionCovector T Q F row col Φ Y r (x, w.2))) w.1 :=
    (hasFDerivAt_waveCarrier hφ).differentiableAt.smul
    ((ha.add (hb.const_smul ((lam : ℂ)⁻¹))).const_smul (((lam : ℂ)⁻¹)^2))
  rw [complexReducedOperator_eq_firstOrder F Q.1 ht,
    complexReducedOperator_eq_firstOrder F Q.1 hb]
  exact WKB.firstOrder_twoTermWave_residual _ _ hlam hφ ha hb
    (fullLeadingCovector_principalSymbol_null T Q F row col Φ Y r (hphase w hw) hQ)
    (fullCorrectionCovector_wkb_cancel_of_leading_outputs T Q F row col Φ Y r
      hΩ hspace hphase hα hw hQ (hnonzero w hw).1 (hnonzero w hw).2 (htransport w hw))

/-- The small-parameter residual retains exactly the factor `τ³`, on both
complex quadratures and with the induced Christoffel coefficients
(`app:ch_waves:eq:WKB-residual`). -/
theorem fullTwoTermWave_reduced_residual_tau_of_leading_outputs
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)
    (htransport : ∀ w ∈ Ω, conullvector T Q row w ⬝ᵥ reducedOperator F Q.1
      (fun x ↦ scalarAmplitude T Q F row col Φ Y r (x, w.2) •
        nullvector T Q col (x, w.2)) w.1 = 0)
    {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))} (hw : w ∈ Ω)
    (hQ : ∀ i, (Q.1 w.1 i).IsSymm) {τ : ℝ} (hτ : τ ≠ 0) :
    complexReducedOperator F Q.1
      (twoTermWave τ⁻¹ (fun x ↦ phase T Q x w.2.2)
        (fun x ↦ euclideanComplexInclusion (fullLeadingCovector T Q F row col Φ Y r (x, w.2)))
        (fun x ↦ fullCorrectionCovector T Q F row col Φ Y r (x, w.2))) w.1 =
      Complex.exp (Complex.I * (phase T Q w.1 w.2.2 : ℂ) / (τ : ℂ)) •
        ((τ : ℂ)^3 • complexReducedOperator F Q.1
          (fun x ↦ fullCorrectionCovector T Q F row col Φ Y r (x, w.2)) w.1) := by
  simpa only [LeadingWave.waveCarrier_inv_eq_exp_div, Complex.ofReal_inv, inv_inv] using
    fullTwoTermWave_reduced_residual_of_leading_outputs T Q F row col Φ Y r
      hΩ hspace hphase hF hi hα hnonzero htransport hw hQ (inv_ne_zero hτ)

end JanetCartan.RawPrimary
