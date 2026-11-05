module
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CorrectedTransport.OriginalCarrierKernel
/-!
# Original carrier normal of the corrected transport endpoint

The exact weighted kernel identification discharges the native reassembly
premise for every grouped prefix of the corrected zero endpoint. The original
rounded raw cutoff, Fourier factor and real quadratures are retained.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.Sampling.CorrectedTransport
open CanonicalTailRealization CanonicalRowComparison RawPrimary CorrectedAtoms CorrectedMean MeasuredAmplitude
open ActualCarriers FrozenMenu CurrentFullPhase LeadingWave LeadingWave.FullModulation
open FullNormalGeometry FullPhaseCharts MeanNormalBound.NormalizedFullPhase
open RawPrimary.MaskProfiles RawKernel RawInputPartition SamplingKernelBounds
open CanonicalAtomRealization MeasuredAmplitude.ColoredApplication SeparatedSampling
open CurrentMean NullTransport ActualFlow FlowAmplitude AmplitudeBound
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumRow.LeadingPrimitive

variable {m N J : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})
  (F : Euclidean (m + 1) → Euclidean N) (row col : Fin (m + 1))
  (Φ Y : ℝ × (Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1))) →
    Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
  (r : Euclidean (m + 1 - 1) × Euclidean 3 → ℝ)
  (κ : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)) → ℝ)
  (C : Euclidean (m + 1) → MetricTensor (m + 1) →L[ℝ] Euclidean (m + 1))
  (z₀ : Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ)
  (hκc : HasCompactSupport κ)
  (hA₀ : Continuous (fun w ↦ κ w • fullLeadingPrincipalMatrix T Q F row col Φ Y r w))
  (hC : Continuous C) {c₀ C₀ : ℝ} (hP : P.IsValid c₀ C₀)
  (hcarrier : closedBall z₀ (2 * ρ) ⊆ parameterInterior (2 * P.radius))
  (mask : Euclidean (m + 1 - 1) → ℂ) (hd : Continuous mask)
  (Md : ℝ) (hMd : 0 ≤ Md) (hdb : ∀ η, ‖mask η‖ ≤ Md)

attribute [local irreducible] leadingCrossTransportKernelData

omit C hC mask hd Md hMd hdb in
/-- Every grouped prefix of the actual corrected transport endpoint has the
original rounded carrier normal, including the Fourier square and both real
quadratures (`app:ch_waves:eq:sampling-prefix-normal`). The literal weighted
kernel premise of the native reassembly theorem is discharged here. -/
theorem leadingCrossTransportPrefix_normal_eq_original
    (φ y : ℝ × (Euclidean (m + 1 - 1) × Euclidean 3) →
      Euclidean (m + 1 - 1) × Euclidean 3)
    {V : Set (ℝ × (Euclidean (m + 1 - 1) × Euclidean 3))}
    (hcompat : ∀ q ∈ V,
      let w := (coordinates (adaptedCoordinates T.data.adapted)).symm q
      scalarAmplitude T Q F row col Φ Y r (w.1, (w.2, T.reference.spatialPatch w.2)) =
        carrierScalarAmplitude T Q F row col φ y r w)
    {b : ℝ} (hb : 0 < b) (hbcell : 4 * b < 1 / 2)
    (hball : closedBall (0 : Euclidean (m + 1)) (4 * b) ⊆ U)
    (angle : Euclidean (m + 1 - 1) → ℝ) (high : ℝ → ℝ)
    (hd : Continuous (detectorMask (fun η ↦ (angle (NormedSpace.normalize η) : ℂ))
      (fun η ↦ high ‖η‖)))
    (Md : ℝ) (hMd : 0 ≤ Md)
    (hdb : ∀ η, ‖detectorMask (fun η ↦ (angle (NormedSpace.normalize η) : ℂ))
      (fun η ↦ high ‖η‖) η‖ ≤ Md)
    (ψ : Point → ℝ)
    (a : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
    (haz : a.2.1 = z₀) (hphase : closedBall a (2 * ρ) ⊆ domain T)
    (hκ : Prod.fst '' Function.support κ ⊆ closedBall a.1 (ρ / 2))
    (hψgraph : ∀ z : CarrierParameter, ψ (carrierSamplingEquiv z) ≠ 0 →
      (parameter z, T.reference.spatialPatch (parameter z)) ∈ closedBall a.2 (ρ / 4))
    (hκone : ∀ x, FixedCutoffs.physical hb 1 x ≠ 0 → ∀ z : CarrierParameter,
      ψ (carrierSamplingEquiv z) ≠ 0 →
      κ (x, parameter z, T.reference.spatialPatch (parameter z)) = 1)
    (hcoords : ∀ x : Torus (m + 1),
      FixedCutoffs.physical hb 1 (centeredTorusRepresentative x) ≠ 0 →
      ∀ z : CarrierParameter, ψ (carrierSamplingEquiv z) ≠ 0 →
      coordinates (adaptedCoordinates T.data.adapted)
        (centeredTorusRepresentative x, parameter z) ∈ V)
    {Bψ Pψ : ℝ} (hψ : PatchBounds ψ Bψ Pψ) (hψc : Continuous ψ)
    (hhigh : ∀ t, t ≤ 1 → high t = 0)
    (carrier : CarrierL2 (m + 1) →L[ℂ] ComplexOutputL2 (m + 1))
    (hadjoint : ∀ q, carrier.adjoint q =ᵐ[carrierMeasure (m + 1)]
      carrierAdjointIntegral (data T Q F row col φ y r hb hbcell
        (fun z θ ↦ Real.sqrt (ψ (carrierSamplingEquiv z)) * angle θ) high) q)
    (cutoff : ℝ) (hL : cutoffCount cutoff ≤ J) :
    let C := canonicalSamplingMeasurement Q.1 hb
    let hC := (contDiff_canonicalSamplingMeasurement T Q F row col φ y r hb hbcell
      (fun z θ ↦ Real.sqrt (ψ (carrierSamplingEquiv z)) * angle θ) high hball).continuous
    let D := leadingCrossTransportKernelData T Q F row col Φ Y r κ C z₀ hρ hκc hA₀ hC hP hcarrier
      (detectorMask (fun η ↦ (angle (NormedSpace.normalize η) : ℂ)) (fun η ↦ high ‖η‖))
      hd Md hMd hdb J
    PeriodicLocalL2.transferOperator ((4 : ℝ) • realOutputCompression
      (∫ z : Point, ψ z • atomNormal (refinedKernelPrefix D (cutoffCount cutoff) z))) =
      ((2 * Real.pi) ^ (-((m + 1 : ℕ) : ℝ) / 2)) ^ 2 •
        (carrierChannel carrier).comp ((RawCutoffBounds.carrierSquaredCutoff
          (RawInputPartition.roundedCarrierMask (m + 1) cutoff)).comp (carrierChannel carrier).adjoint) := by
  intro C hC D
  let d := data T Q F row col φ y r hb hbcell
    (fun z θ ↦ Real.sqrt (ψ (carrierSamplingEquiv z)) * angle θ) high
  have hkernel := leadingCrossTransportKernelData_eq_weighted_original (J := J) T Q F row col Φ Y r κ
    z₀ hρ hκc hA₀ hP hcarrier φ y hcompat hb hbcell hball angle high hd Md hMd hdb
    ψ a haz hphase hκ hψgraph hκone hcoords
  exact nativeSamplingPrefix_normal_eq_original d D
    (leadingCrossTransportKernelData_zero_off_wideBand T Q F row col Φ Y r κ C z₀ hρ
      hκc hA₀ hC hP hcarrier _ hd Md hMd hdb)
    ψ hψ hψc hkernel hhigh carrier hadjoint cutoff hL

end JanetCartan.Sampling.CorrectedTransport
