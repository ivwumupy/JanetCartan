module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.SourceDensityLimitRealization.NormalWitnesses
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.RetainedAmplitudes

/-!
# The literal density-limit normal after common measurement

The supported constructor's normal is restricted on the same carrier. Its
physical sandwich equals the full reflected PDO of the literal common-chart
data. The measurement constant precedes all varying carrier and density data.
Consumer: `NormalizedNormalLimit.exists_source_family_controlled_half_gap`
(`bg-normalized`, `bg-Nsigma`, `bg-full-complex-amplitude`, `bg-real-symbol`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.SourceDensityLimitRealization
open ContinuumRow CommonMeasurement ContinuumNormalReduction TransportSymbol TransportKernel
open CarrierNormalRealization ContinuumCommutator Pseudodifferential AmplitudeBound PeriodicLocalL2

/-- The normal after common measurement is the literal reflected PDO of the
same carrier data with the common cutoff. The only normal premise is the
output of `exists_source_zero_density_limit_realization`; this lemma supplies
the exact downstream form with a constant chosen before every density
(`bg-full-complex-amplitude`, `bg-real-symbol`, `bg-frame`). -/
theorem exists_commonMeasurement_literal_normal
    {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2) :
    ∃ C ≥ (0 : ℝ), ∀ {N : ℕ} (e : CarrierData n N)
      {a : ℝ} (ha : 0 < a), 3 * r ≤ 2 * a →
      ∀ (J : InputVariables n → ℝ) (u : Variables n × Euclidean 2 → SliceVariable n)
      (Ω : Set (Variables n × Euclidean 2)) (S : Set (Euclidean 2)) (Rbox : ℝ),
      let d := coefficientsOfCarrier e (FixedCutoffs.physical ha 1)
      let b := fullReflectedMatrixAmplitude d J u Ω S
      ∀ (hb : ContDiff ℝ ∞ (Function.uncurry b))
        (hs : ∀ ξ i j, SupportedInCenteredBox Rbox (fun z ↦ b ξ z i j))
        (B : ℝ) (hB : ∀ i j, HasAmplitudeDerivativeBound
          (fun ξ z ↦ b ξ z i j) (2 * (n + 1)) B)
        (Vop : CarrierL2 n →L[ℂ] ComplexOutputL2 n),
      carrierChannel Vop ∘L (carrierChannel Vop).adjoint =
        realOutputCompression (transferOperator
          (vectorTwoPositionL2Operator hn Rbox b hb hs B hB)) →
      let eCommon := commonChartData e (closedBall 0 (4 * r)) (FixedCutoffs.periodic hr hcell 1)
      let dCommon := coefficientsOfCarrier eCommon (FixedCutoffs.physical hr 1)
      let bCommon := fullReflectedMatrixAmplitude dCommon J u Ω S
      ∃ hbCommon : ContDiff ℝ ∞ (Function.uncurry bCommon),
      ∃ hBCommon : ∀ i j, HasAmplitudeDerivativeBound
        (fun ξ z ↦ bCommon ξ z i j) (2 * (n + 1)) (C * B),
      ∃ hsCommon : ∀ ξ i j, SupportedInCenteredBox (4 * r) (fun z ↦ bCommon ξ z i j),
        dCommon = restrictCoefficients d (FixedCutoffs.physical hr 1) ∧
        bCommon = restrictAmplitude b (FixedCutoffs.physical hr 1) ∧
        carrierChannel (restrictCarrier (FixedCutoffs.periodic hr hcell 1) Vop) ∘L
          (carrierChannel (restrictCarrier (FixedCutoffs.periodic hr hcell 1) Vop)).adjoint =
            realOutputCompression (transferOperator
              (vectorTwoPositionL2Operator hn (4 * r) bCommon hbCommon hsCommon (C * B) hBCommon)) := by
  obtain ⟨C, hC, hrestrict⟩ := exists_fixedMeasurement_reflected_normal_realization hn hr hcell
  refine ⟨C, hC, ?_⟩
  intro N e a ha hra J u Ω S Rbox d b hb hs B hB Vop hnormal eCommon dCommon bCommon
  have hd : dCommon = restrictCoefficients d (FixedCutoffs.physical hr 1) := by
    dsimp only [dCommon, d, eCommon]
    unfold coefficientsOfCarrier restrictCoefficients commonChartData
    congr 1
    funext x
    exact (physical_measurement_mul hr ha hra x).symm
  have heq : bCommon = restrictAmplitude b (FixedCutoffs.physical hr 1) := by
    change fullReflectedMatrixAmplitude dCommon J u Ω S = _
    rw [hd]
    exact fullReflectedMatrixAmplitude_restrictCoefficients d (FixedCutoffs.physical hr 1) J u Ω S
  obtain ⟨hB', hn'⟩ := hrestrict d J u Ω S Rbox hb hs B hB Vop hnormal
  have hb' := contDiff_restrictAmplitude b hb (FixedCutoffs.physical hr 1)
    (FixedCutoffs.physical hr 1).contDiff
  have hs' := supportedInCenteredBox_restrictAmplitude_fixedMeasurement b hr
  have hbCommon : ContDiff ℝ ∞ (Function.uncurry bCommon) := heq.symm ▸ hb'
  have hBCommon : ∀ i j, HasAmplitudeDerivativeBound
      (fun ξ z ↦ bCommon ξ z i j) (2 * (n + 1)) (C * B) := heq.symm ▸ hB'
  have hsCommon : ∀ ξ i j, SupportedInCenteredBox (4 * r) (fun z ↦ bCommon ξ z i j) :=
    heq.symm ▸ hs'
  refine ⟨hbCommon, hBCommon, hsCommon, hd, heq, ?_⟩
  exact realized_normal_eq_of_amplitude_witnesses hn (4 * r) (4 * r) _ bCommon
    hb' hbCommon hs' hsCommon (C * B) (C * B) hB' hBCommon heq.symm _ hn'

end JanetCartan.ContinuumNormal.SourceDensityLimitRealization
