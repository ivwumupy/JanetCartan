module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CorrectedTransport.Support
public import JanetCartan.Geometry.IsometricEmbedding.Waves.CorrectedSamplingMean.KernelMatching
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.ColumnNormal

/-!
# Literal corrected normal at the transport path endpoint

Apply the corrected-mean kernel matching at the exact physical endpoint of
the transport path. The same phase, carrier, Lebesgue measures, detector and
real quadratures are retained.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option quotPrecheck false
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.Sampling.CorrectedTransport
open CorrectedMean
open CanonicalRowComparison CanonicalAtomRealization CorrectedAtoms
open LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open MeasuredAmplitude FullNormalGeometry FullNormalGeometry.PhaseJets FullPhaseCharts
open MeanNormalBound.NormalizedFullPhase ContinuumRow RawPrimary.MaskProfiles
open MeanNormalBound.CanonicalGap
open RawKernel RawInputPartition FullPhaseCharts.ActualComparison
open NormalComparison ColoredNormalComparison MeanNormalBound

variable {m N : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})
  (F : Euclidean (m + 1) → Euclidean N) (row col : Fin (m + 1))
  (Φ Y : ℝ × (Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1))) →
    Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
  (χ : Euclidean (m + 1) → ℝ)
  (B : MetricField (m + 1) →ₗ[ℝ] (Euclidean (m + 1) → Euclidean N))
  (r : Euclidean (m + 1 - 1) × Euclidean 3 → ℝ)
  (κ : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)) → ℝ)
  (C : Euclidean (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ →L[ℝ]
    Euclidean (m + 1))
  (z₀ : Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ)

variable {p J : ℕ}
  (hκc : HasCompactSupport κ) (rate : (Fin 3 → Fin (p + 1)) → ℝ)
  (hA : ∀ color, Continuous (fun w ↦ κ w •
    fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r (rate color) w))
  (hC : Continuous C) {c₀ C₀ : ℝ} (hP : P.IsValid c₀ C₀)
  (hcarrier : closedBall z₀ (2 * ρ) ⊆ parameterInterior (2 * P.radius))
  (hrate : ∀ color, rate color ≠ 0)
  (angular : Euclidean (m + 1 - 1) → ℂ) (highPass : Euclidean (m + 1 - 1) → ℝ)
  (hd : Continuous (detectorMask angular highPass))
  (Md : ℝ) (hMd : 0 ≤ Md) (hdb : ∀ η, ‖detectorMask angular highPass η‖ ≤ Md)

local notation "D" => correctedColoredCrossBandData T Q F row col Φ Y χ B r κ hκc rate hA C hC
  Prod.fst continuous_fst (fun q ↦ WithLp.toLp 2 q.2) (by fun_prop) hP z₀ hρ hcarrier hrate
  (detectorMask angular highPass) hd Md hMd hdb J

variable
    (a : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
    (haz : a.2.1 = z₀) (hphase : closedBall a (2 * ρ) ⊆ domain T)
    (hκ : Prod.fst '' Function.support κ ⊆ closedBall a.1 (ρ / 2))
    (ψ : SeparatedSampling.Point → ℝ) {R Pψ : ℝ}
    (hψ : SeparatedSampling.PatchBounds ψ R Pψ) (hψc : Continuous ψ)
    (hψgraph : ∀ s v, ψ (carrierSamplingEquiv (s, v)) ≠ 0 →
      (carrierParameters (v, s), T.reference.spatialPatch (carrierParameters (v, s))) ∈
        closedBall a.2 (ρ / 4))
    (hψchart : ∀ s v, ψ (carrierSamplingEquiv (s, v)) ≠ 0 →
      carrierParameters (v, s) ∈ parameterInterior (3 * P.radius / 2))
    (j : Fin J) (color : Fin 3 → Fin (p + 1)) (v : Euclidean 2)
    (hscale : |rate color| * (2 : ℝ) ^ j.val ≤ measuredPhaseRadius T hP (ρ := ρ))
    {G : UniformNormalGeometry (m + 1) (m + 1)} {Cnormal : ℕ → ℝ}
    (Ndata : UniformNormalData G Cnormal)
    (hNphase : Ndata.phase = fun ε x u ↦
      normalizedFullPhase T Q v ε x (canonicalInputCoordinates T u))
    (hNamp : Ndata.amplitude = fun ε x u ↦
      (correctedTransportNormalAmplitude T Q F row col Φ Y χ B r κ C z₀ hρ (rate color)
        angular highPass ψ j.val v ε x u).ofLp)
    (hε : rate color * (2 : ℝ) ^ j.val ∈ Icc 0 G.ε₀)

include haz hphase hκ hψ hψgraph hψchart hscale hNphase hNamp hε in
/-- The literal corrected full-band normal is exactly the operator built
from the fixed-response transport homotopy at its physical endpoint. No global phase equality is needed
off its measured support (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem correctedColoredCrossBandData_normal_eq_transportHomotopy :
    atomNormal (fullBandKernelOperator (D) (fun z ↦ (j, (color, z)))
      (continuous_const.prodMk (continuous_const.prodMk continuous_id))
      ψ hψc j.val R v) =
      samplingOutputConjugation (m + 1)
        ((Ndata.uniformOscillatoryOperator ((2 : ℝ) ^ j.val)
          (rate color * (2 : ℝ) ^ j.val)).comp
          (Ndata.uniformOscillatoryOperator ((2 : ℝ) ^ j.val)
            (rate color * (2 : ℝ) ^ j.val)).adjoint) := by
  apply fullBandKernelOperator_normal_eq_uniform_of_supported_phase
    (D) (fun z ↦ (j, (color, z)))
    (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    ψ hψc j.val R v Ndata hε
  · intro u _ x hn
    rw [hNphase]
    apply correctedColoredCrossBandData_phase_on_fixedRateNormal_support
      T Q F row col Φ Y χ B r κ C z₀ hρ hκc rate hA hC hP hcarrier hrate
      angular highPass hd Md hMd hdb a haz hphase hκ ψ hψgraph hψchart
      j color v hscale u.1 u.2 x
    intro hz
    simp only [Prod.mk.eta] at hz
    apply hn
    simp only [hNamp, correctedTransportNormalAmplitude_self
      T Q F row col Φ Y χ B r κ C z₀ hρ angular highPass ψ (hrate color)]
    change (fixedRateNormalAmplitude T Q F row col Φ Y χ B r κ C z₀ hρ (rate color)
      angular highPass ψ j.val v (rate color * (2 : ℝ) ^ j.val) x
        (fullInputCoordinates m u)).ofLp = 0
    rw [hz]
    rfl
  · intro u _ x i
    simp only [hNamp, correctedTransportNormalAmplitude_self
      T Q F row col Φ Y χ B r κ C z₀ hρ angular highPass ψ (hrate color)]
    apply correctedColoredCrossBandData_amplitude_eq_fixedRateNormal
      T Q F row col Φ Y χ B r κ C z₀ hρ hκc rate hA hC hP hcarrier hrate
      angular highPass hd Md hMd hdb ψ _ j color v u.1 u.2 x i
    intro s v' hv'
    have hg := hψgraph s v' hv'
    rw [← closedBall_prod_same] at hg
    rw [← haz]
    exact closedBall_subset_closedBall (by linarith) hg.1
  · intro u hu x
    simp only [hNamp, correctedTransportNormalAmplitude_self
      T Q F row col Φ Y χ B r κ C z₀ hρ angular highPass ψ (hrate color)]
    change (fixedRateNormalAmplitude T Q F row col Φ Y χ B r κ C z₀ hρ (rate color)
      angular highPass ψ j.val v (rate color * (2 : ℝ) ^ j.val) x u).ofLp = 0
    rw [fixedRateNormalAmplitude_eq_zero_off_fullInputDomain
      T Q F row col Φ Y χ B r κ C z₀ hρ (rate color) angular highPass ψ hψ
      j.val v (rate color * (2 : ℝ) ^ j.val) u hu]
    rfl

include haz hphase hκ hψ hψgraph hψchart hscale hNphase hNamp hε in
/-- Both original real quadratures have the exact corrected normal, including
factor four, after the literal output coordinate change
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem correctedColoredCrossBandData_real_normal_eq_transportHomotopy :
    let A := fullBandKernelOperator (D) (fun z ↦ (j, (color, z)))
      (continuous_const.prodMk (continuous_const.prodMk continuous_id)) ψ hψc j.val R v
    (realQuadratureChannel A).comp (realQuadratureChannel A).adjoint =
      samplingRealNormal (m + 1)
        ((Ndata.uniformOscillatoryOperator ((2 : ℝ) ^ j.val)
          (rate color * (2 : ℝ) ^ j.val)).comp
          (Ndata.uniformOscillatoryOperator ((2 : ℝ) ^ j.val)
            (rate color * (2 : ℝ) ^ j.val)).adjoint) := by
  dsimp only
  rw [realQuadratureChannel_normal_eq_four_realPart]
  change (4 : ℝ) • realOutputCompression (atomNormal _) = _
  rw [correctedColoredCrossBandData_normal_eq_transportHomotopy
    T Q F row col Φ Y χ B r κ C z₀ hρ hκc rate hA hC hP hcarrier hrate
    angular highPass hd Md hMd hdb a haz hphase hκ ψ hψ hψc hψgraph hψchart
    j color v hscale Ndata hNphase hNamp hε]
  rfl

end JanetCartan.Sampling.CorrectedTransport
