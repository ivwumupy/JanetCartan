module

public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.JointLinearity
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Reconstruction.Bounds
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Polynomial.Literal

/-!
# Joint regularity of the literal density amplitudes

For `app:ch_response:eq:current-density-lipschitz`, derive raw and leading
amplitude smoothness from the actual retained geometric inputs. For the response,
joint smoothness of the fixed operator's physical output gives smoothness of its
demodulated physical derivative. The actual response producer must still supply
that output regularity; pointwise physical smoothness alone does not imply it.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.CorrectedAtoms
open RawPrimary LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open RawPrimary.AmplitudeGrades RawPrimary.AmplitudeGrades.Polynomial

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)

include hΩ hspace hphase hF hi hrank hα hnonzero

/-- The literal raw derivative amplitude is jointly smooth on its retained
chart, directly from the actual raw field and original phase
(`app:ch_waves:eq:WKB-amplitude-difference`). -/
theorem contDiffOn_retainedDerivativeAmplitude {τ : ℝ} (hτ : τ ≠ 0) :
    ContDiffOn ℝ ∞ (fullDerivativeAmplitude T Q F row col Φ Y r τ) Ω := by
  have hW := contDiffOn_fullPrimaryAtom_of_leading_outputs T Q F row col Φ Y r τ
    hΩ hspace hphase hF hi hrank hα hnonzero
  have hc : ContDiffOn ℝ ∞
      (fun w ↦ Complex.exp (-Complex.I * (phase T Q w.1 w.2.2 / τ : ℝ))) Ω :=
    (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
      ((contDiffOn_fullPhase T Q hphase).div_const τ))).cexp
  apply (hc.smul (contDiffOn_physicalJacobian hΩ hW)).congr
  intro w hw
  rw [fullDerivativeAmplitude_eq_demodulated T Q F row col Φ Y
    hΩ hspace hphase hF hi hrank hnonzero r hα hτ hw]
  congr 1
  ext i j
  exact (physicalJacobian_apply ((hW.contDiffAt (hΩ.mem_nhds hw)).differentiableAt
    (by simp)) i j).symm

omit hnonzero in
/-- The original leading matrix is jointly smooth from the actual normal
completion and scalar transport, with no independent leading-field premise
(`app:ch_waves:eq:arbitrary-b-amplitudes`). -/
theorem contDiffOn_retainedLeadingPrincipalMatrix :
    ContDiffOn ℝ ∞ (fullLeadingPrincipalMatrix T Q F row col Φ Y r) Ω := by
  have hb := euclideanComplexInclusion.contDiff.comp_contDiffOn
    (contDiffOn_fullLeadingCovector T Q F row col Φ Y r hspace hphase hα)
  have hξ : ContDiffOn ℝ ∞ (fun w ↦ phaseGradient T Q w.1 w.2.2) Ω :=
    (phaseGradient_smooth T Q).comp (contDiffOn_fst.prodMk contDiffOn_snd.snd) hphase
  have hξ' : ContDiffOn ℝ ∞
      (fun w ↦ scalarDifferential (fun x ↦ phase T Q x w.2.2) w.1) Ω := by
    simpa only [scalarDifferential_eq_gradient, phaseGradient] using hξ
  have hν := contDiffOn_joint_canonicalPrincipalNormalComplex_of_isOpen
    hΩ hspace hF hb hξ' hi hrank
  have hν' : ContDiffOn ℝ ∞ (fullLeadingNormal T Q F row col Φ Y r) Ω := by
    exact hν
  have hh := (normalTensor n N).isBoundedBilinearMap.contDiff.comp_contDiffOn (hξ.prodMk hν')
  apply hh.neg.congr
  intro w _
  exact fullLeadingPrincipalMatrix_eq_tensor T Q F row col Φ Y r w

omit hspace hF hi hrank hα hnonzero in
/-- Joint output regularity of the SAME fixed response gives joint regularity
of its demodulated PHYSICAL derivative. The producer `both-response-transfer`
must supply `hresponse`; no carrier derivative of an inverse is assumed
(`app:ch_response:eq:current-atomic-amplitudes`). -/
theorem contDiffOn_fullPrimaryResponseDerivativeAmplitude
    (χ : Euclidean n → ℝ)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N)) (τ : ℝ)
    (hresponse : ContDiffOn ℝ ∞
      (fun w ↦ fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2 w.1) Ω) :
    ContDiffOn ℝ ∞ (fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y χ B r τ) Ω := by
  have hc : ContDiffOn ℝ ∞
      (fun w ↦ Complex.exp (-Complex.I * (phase T Q w.1 w.2.2 / τ : ℝ))) Ω :=
    (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
      ((contDiffOn_fullPhase T Q hphase).div_const τ))).cexp
  apply (hc.smul (contDiffOn_physicalJacobian hΩ hresponse)).congr
  intro w hw
  unfold fullPrimaryResponseDerivativeAmplitude
  congr 1
  ext i j
  exact (physicalJacobian_apply
    ((hresponse.contDiffAt (hΩ.mem_nhds hw)).differentiableAt (by simp)) i j).symm

end JanetCartan.CorrectedAtoms
