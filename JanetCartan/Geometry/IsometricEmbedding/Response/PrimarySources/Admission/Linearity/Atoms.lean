module

public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Admission.Linearity.Calculus

/-!
# Initial-scalar linearity through correction and reconstruction

The consumer is the literal source map in `Admission.Linearity`. Every operation
uses the same full phase, leading covector, orthogonal correction, and ambient
completion from `app:ch_waves:eq:WKB-W`. The retained constructor supplies all
geometric and scalar regularity hypotheses below.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PrimarySourceAdmission
open RawPrimary LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open NullTransport ResponseTransfer InitialScalarCalculus

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)

private theorem slice_differentiable {E Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {O : Set (Euclidean n × Z)} (ho : IsOpen O)
    {f : Euclidean n × Z → E} (hf : ContDiffOn ℝ ∞ f O)
    {w : Euclidean n × Z} (hw : w ∈ O) :
    DifferentiableAt ℝ (fun x ↦ f (x, w.2)) w.1 :=
  (((hf.contDiffAt (ho.mem_nhds hw)).comp w.1
    (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp))

include hΩ hspace hphase

/-- The differentiated orthogonal correction is additive at points of the
actual chart (`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem fullCorrectionCovector_initial_add
    {r s : Euclidean (n - 1) × Euclidean 3 → ℝ}
    (hr : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hs : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y s) Ω)
    {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))} (hw : w ∈ Ω) :
    fullCorrectionCovector T Q F row col Φ Y (r + s) w =
      fullCorrectionCovector T Q F row col Φ Y r w +
        fullCorrectionCovector T Q F row col Φ Y s w := by
  have he := (fullLeadingCovectorLinearMap T Q F row col Φ Y).map_add r s
  change fullLeadingCovector T Q F row col Φ Y (r + s) =
    fullLeadingCovector T Q F row col Φ Y r + fullLeadingCovector T Q F row col Φ Y s at he
  have hd := reducedOperator_add F Q.1
    (slice_differentiable hΩ (contDiffOn_fullLeadingCovector T Q F row col Φ Y r hspace hphase hr) hw)
    (slice_differentiable hΩ (contDiffOn_fullLeadingCovector T Q F row col Φ Y s hspace hphase hs) hw)
  simp only [fullCorrectionCovector, he, Pi.add_apply]
  change reducedOperator F Q.1
    (fun x ↦ fullLeadingCovector T Q F row col Φ Y r (x, w.2) +
      fullLeadingCovector T Q F row col Φ Y s (x, w.2)) w.1 = _ at hd
  rw [hd, Matrix.mulVec_add, WithLp.toLp_add, map_add, smul_add]

/-- Real scaling of the differentiated correction on the same chart
(`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem fullCorrectionCovector_initial_smul
    {r : Euclidean (n - 1) × Euclidean 3 → ℝ}
    (hr : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω) (c : ℝ)
    {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))} (hw : w ∈ Ω) :
    fullCorrectionCovector T Q F row col Φ Y (c • r) w =
      c • fullCorrectionCovector T Q F row col Φ Y r w := by
  have he := (fullLeadingCovectorLinearMap T Q F row col Φ Y).map_smul c r
  change fullLeadingCovector T Q F row col Φ Y (c • r) =
    c • fullLeadingCovector T Q F row col Φ Y r at he
  have hd := reducedOperator_real_smul F Q.1
    (slice_differentiable hΩ (contDiffOn_fullLeadingCovector T Q F row col Φ Y r hspace hphase hr) hw) c
  simp only [fullCorrectionCovector, he, Pi.smul_apply]
  change reducedOperator F Q.1
    (fun x ↦ c • fullLeadingCovector T Q F row col Φ Y r (x, w.2)) w.1 = _ at hd
  rw [hd, Matrix.mulVec_smul, WithLp.toLp_smul, map_smul]
  exact smul_comm _ _ _

variable (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)

include hF hi hnonzero

private theorem fullTwoTermWave_differentiable (τ : ℝ)
    {r : Euclidean (n - 1) × Euclidean 3 → ℝ}
    (hr : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))} (hw : w ∈ Ω) :
    DifferentiableAt ℝ
      (twoTermWave τ⁻¹ (fun x ↦ phase T Q x w.2.2)
        (fun x ↦ euclideanComplexInclusion (fullLeadingCovector T Q F row col Φ Y r (x, w.2)))
        (fun x ↦ fullCorrectionCovector T Q F row col Φ Y r (x, w.2))) w.1 := by
  have hp := slice_differentiable hΩ (contDiffOn_fullPhase T Q hphase) hw
  have ha := euclideanComplexInclusion.differentiableAt.comp w.1
    (slice_differentiable hΩ (contDiffOn_fullLeadingCovector T Q F row col Φ Y r hspace hphase hr) hw)
  have hb := slice_differentiable hΩ (contDiffOn_fullCorrectionCovector_of_leading_outputs
    T Q F row col Φ Y r hΩ hspace hphase hF hi hr hnonzero) hw
  unfold twoTermWave modulatedWave
  simpa only [Pi.smul_def, Pi.smul_def', Pi.add_def, Function.comp_def] using
    (hasFDerivAt_waveCarrier (lam := τ⁻¹) hp).differentiableAt.smul
      ((ha.add (hb.const_smul (((τ⁻¹ : ℝ) : ℂ)⁻¹))).const_smul
        (((τ⁻¹ : ℝ) : ℂ)⁻¹ ^ 2))

/-- The literal full atom is additive in its original scalar locally, including
the derivative of its correction (`app:ch_waves:eq:WKB-W`). -/
theorem fullPrimaryAtom_initial_add (τ : ℝ)
    {r s : Euclidean (n - 1) × Euclidean 3 → ℝ}
    (hr : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hs : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y s) Ω)
    {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))} (hw : w ∈ Ω) :
    fullPrimaryAtom T Q F row col Φ Y τ (r + s) w.2.1 (w.1, w.2.2) =
      fullPrimaryAtom T Q F row col Φ Y τ r w.2.1 (w.1, w.2.2) +
        fullPrimaryAtom T Q F row col Φ Y τ s w.2.1 (w.1, w.2.2) := by
  let v := fun r ↦ twoTermWave τ⁻¹ (fun x ↦ phase T Q x w.2.2)
    (fun x ↦ euclideanComplexInclusion (fullLeadingCovector T Q F row col Φ Y r (x, w.2)))
    (fun x ↦ fullCorrectionCovector T Q F row col Φ Y r (x, w.2))
  have he : v (r + s) =ᶠ[𝓝 w.1] v r + v s := by
    have ho : {x : Euclidean n | (x, w.2) ∈ Ω} ∈ 𝓝 w.1 :=
      (hΩ.preimage (continuous_id.prodMk continuous_const)).mem_nhds hw
    filter_upwards [ho] with x hx
    have ha := congrFun ((fullLeadingCovectorLinearMap T Q F row col Φ Y).map_add r s) (x, w.2)
    change fullLeadingCovector T Q F row col Φ Y (r + s) (x, w.2) =
      fullLeadingCovector T Q F row col Φ Y r (x, w.2) +
        fullLeadingCovector T Q F row col Φ Y s (x, w.2) at ha
    simp only [v, twoTermWave, modulatedWave, ha, Pi.add_apply, map_add,
      fullCorrectionCovector_initial_add T Q F row col Φ Y hΩ hspace hphase hr hs hx,
      smul_add]
    module
  change completedVariationComplex F (v (r + s)) 0 w.1 =
    completedVariationComplex F (v r) 0 w.1 + completedVariationComplex F (v s) 0 w.1
  rw [completedVariationComplex_zero_congr F he]
  exact completedVariationComplex_zero_add F
    (fullTwoTermWave_differentiable T Q F row col Φ Y hΩ hspace hphase hF hi hnonzero τ hr hw)
    (fullTwoTermWave_differentiable T Q F row col Φ Y hΩ hspace hphase hF hi hnonzero τ hs hw)

/-- Real homogeneity of the literal full atom, with both correction quadratures
and their derivatives (`app:ch_waves:eq:WKB-W`). -/
theorem fullPrimaryAtom_initial_smul (τ : ℝ)
    {r : Euclidean (n - 1) × Euclidean 3 → ℝ}
    (hr : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω) (c : ℝ)
    {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))} (hw : w ∈ Ω) :
    fullPrimaryAtom T Q F row col Φ Y τ (c • r) w.2.1 (w.1, w.2.2) =
      c • fullPrimaryAtom T Q F row col Φ Y τ r w.2.1 (w.1, w.2.2) := by
  let v := fun r ↦ twoTermWave τ⁻¹ (fun x ↦ phase T Q x w.2.2)
    (fun x ↦ euclideanComplexInclusion (fullLeadingCovector T Q F row col Φ Y r (x, w.2)))
    (fun x ↦ fullCorrectionCovector T Q F row col Φ Y r (x, w.2))
  have he : v (c • r) =ᶠ[𝓝 w.1] c • v r := by
    have ho : {x : Euclidean n | (x, w.2) ∈ Ω} ∈ 𝓝 w.1 :=
      (hΩ.preimage (continuous_id.prodMk continuous_const)).mem_nhds hw
    filter_upwards [ho] with x hx
    have ha := congrFun ((fullLeadingCovectorLinearMap T Q F row col Φ Y).map_smul c r) (x, w.2)
    change fullLeadingCovector T Q F row col Φ Y (c • r) (x, w.2) =
      c • fullLeadingCovector T Q F row col Φ Y r (x, w.2) at ha
    simp only [v, twoTermWave, modulatedWave, ha, Pi.smul_apply, map_smul,
      fullCorrectionCovector_initial_smul T Q F row col Φ Y hΩ hspace hphase hr c hx,
      smul_comm _ c, ← smul_add]
  change completedVariationComplex F (v (c • r)) 0 w.1 =
    c • completedVariationComplex F (v r) 0 w.1
  rw [completedVariationComplex_zero_congr F he]
  exact completedVariationComplex_zero_real_smul F
    (fullTwoTermWave_differentiable T Q F row col Φ Y hΩ hspace hphase hF hi hnonzero τ hr hw) c

end JanetCartan.PrimarySourceAdmission
