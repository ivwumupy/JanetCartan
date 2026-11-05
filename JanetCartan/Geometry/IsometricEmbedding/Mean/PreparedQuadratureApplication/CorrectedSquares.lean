module

public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.JointRegularity
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PreparationTransportPrimitives.CarrierPullback

/-!
# The literal corrected self tensor before quadrature

The unit phase cancels in the self tensor of the actual corrected atom.
This equality holds in a neighborhood, so it also identifies every carrier
derivative along the original carrier graph. In particular quadrature does
not differentiate the rapidly oscillating factor. The fixed response and
the initial scalar are the same on both sides.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.CurrentMean
open CorrectedAtoms RawPrimary LeadingWave LeadingWave.FullModulation
open ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow ContinuumRow.LeadingPrimitive

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (χ : Euclidean n → ℝ)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)

include hΩ hspace hphase hF hi hrank hα hnonzero in
/-- The measured self tensor may use the actual corrected derivative
amplitude without its oscillatory phase. This is the corrected-atom version
of the cancellation required before deterministic quadrature
(`app:ch_response:eq:current-atomic-amplitudes`,
`app:ch_waves:eq:background-quadrature`). -/
theorem hermitianTensor_fullCorrectedDerivativeAmplitude_eq
    {τ : ℝ} (hτ : τ ≠ 0)
    {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))} (hw : w ∈ Ω)
    (hB : DifferentiableAt ℝ (fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2) w.1) :
    hermitianTensor (fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ w) =
      hermitianTensor (fun i j ↦ partialDeriv
        (fullCorrectedPrimaryAtom T Q F row col Φ Y χ B τ r w.2) w.1 j i) := by
  rw [fullCorrectedDerivativeAmplitude_eq_demodulated T Q F row col Φ Y χ B r
    hΩ hspace hphase hF hi hrank hα hnonzero hτ hw hB,
    hermitianTensor_smul, Complex.normSq_eq_norm_sq, Complex.norm_exp]
  simp

include hΩ hspace hphase hF hi hrank hα hnonzero in
/-- Every parameter derivative of the literal corrected self tensor along
the SAME carrier graph is the derivative of its demodulated self tensor.
Joint response smoothness is supplied by `Response.SmoothParameters` for
the retained `B`; no new response, phase, scalar, or sample is selected
(`app:ch_mean_pairs:prop:mean-coarse`). -/
theorem iteratedFDeriv_fullCorrectedSelfTensor_carrier_eq
    {c₀ C₁ : ℝ} (hP : P.IsValid c₀ C₁) {τ : ℝ} (hτ : τ ≠ 0)
    (hresponse : ContDiffOn ℝ ∞
      (fun w ↦ fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2 w.1) Ω)
    (x : Euclidean n) {z : CarrierParameter}
    (hz : CanonicalCarrier.parameter z ∈ parameterInterior (2 * P.radius))
    (hw : carrierGraph T (x, z) ∈ Ω) (p : ℕ) :
    iteratedFDeriv ℝ p (fun z : CarrierParameter ↦
      hermitianTensor (fun i j ↦ partialDeriv
        (fullCorrectedPrimaryAtom T Q F row col Φ Y χ B τ r (carrierGraph T (x,z)).2)
          x j i)) z =
      iteratedFDeriv ℝ p (fun z : CarrierParameter ↦
        hermitianTensor (fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ
          (carrierGraph T (x,z)))) z := by
  have hgraph : ContinuousAt (fun z : CarrierParameter ↦ carrierGraph T (x,z)) z := by
    have hopen : IsOpen ((univ : Set (Euclidean n)) ×ˢ (CanonicalCarrier.parameter ⁻¹'
        parameterInterior (2 * P.radius))) :=
      isOpen_univ.prod ((isOpen_parameterInterior _).preimage CanonicalCarrier.parameter.continuous)
    exact ((carrierGraph_smooth T hP).contDiffAt
      (hopen.mem_nhds (x := (x,z)) ⟨mem_univ x, hz⟩)).continuousAt.comp
        (continuousAt_const.prodMk continuousAt_id)
  have he : (fun z : CarrierParameter ↦
      hermitianTensor (fun i j ↦ partialDeriv
        (fullCorrectedPrimaryAtom T Q F row col Φ Y χ B τ r (carrierGraph T (x,z)).2)
          x j i)) =ᶠ[𝓝 z]
      (fun z : CarrierParameter ↦ hermitianTensor
        (fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ
          (carrierGraph T (x,z)))) := by
    filter_upwards [hgraph.preimage_mem_nhds (hΩ.mem_nhds hw)] with a ha
    have hB := ((hresponse.contDiffAt (hΩ.mem_nhds ha)).comp x
      (f := fun y : Euclidean n ↦ (y, (carrierGraph T (x,a)).2))
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
    exact (hermitianTensor_fullCorrectedDerivativeAmplitude_eq T Q F row col Φ Y χ B r
      hΩ hspace hphase hF hi hrank hα hnonzero hτ ha hB).symm
  exact (he.iteratedFDeriv ℝ p).self_of_nhds

end JanetCartan.CurrentMean
