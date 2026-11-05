module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CorrectedTransport.WeightedNormal
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.ColoredApplication.RetainedPrefixes

/-!
# Original corrected prefixes in carrier coordinates

Reassemble both annular pieces and integrate the same corrected weighted
normal over spectators. The normal path may depend on color at a fixed
response rate. No operator-integrability premise is introduced.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option quotPrecheck false
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius ENNReal
namespace JanetCartan.Sampling.CorrectedTransport
open CorrectedMean
open CanonicalRowComparison CanonicalAtomRealization CorrectedAtoms
open LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open MeasuredAmplitude FullNormalGeometry FullNormalGeometry.PhaseJets FullPhaseCharts
open MeanNormalBound.NormalizedFullPhase ContinuumRow RawPrimary.MaskProfiles
open MeanNormalBound.CanonicalGap
open RawKernel RawInputPartition FullPhaseCharts.ActualComparison
open NormalComparison ColoredNormalComparison MeanNormalBound
open MeasuredAmplitude.ColoredApplication
open SamplingKernelBounds SeparatedSampling LatticeQuadrature BackgroundQuadrature Realization

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

variable {G : UniformNormalGeometry (m + 1) (m + 1)} {Cnormal : ℕ → ℝ}

include haz hphase hκ hψ hψc hψgraph hψchart in
/-- Every corrected grouped prefix equals the original colored slice of
its fixed-response paths. The exact patch weight and the auxiliary carrier
plateau are retained (`app:ch_waves:eq:colored-normal-comparison`). -/
theorem correctedColoredCrossBandData_colored_prefix_eq_transportSlices
    {kappa : ℝ → ℝ} (hc : HasCompactSupport kappa) (hkappa : ContDiff ℝ ∞ kappa)
    (φ : Point → ℝ) (hφ : Continuous φ) (Bφ h : ℝ)
    (hplateau : ∀ z, φ z ≠ 0 → ψ z = 1)
    (v : Euclidean 2) (Ns : (Fin 3 → Fin (p + 1)) → ℕ → UniformNormalData G Cnormal)
    (hNphase : ∀ color j, (Ns color j).phase = fun ε x u ↦
      normalizedFullPhase T Q v ε x (canonicalInputCoordinates T u))
    (hNamp : ∀ color j, (Ns color j).amplitude = fun ε x u ↦
      (correctedTransportNormalAmplitude T Q F row col Φ Y χ B r κ C z₀ hρ (rate color)
        angular highPass ψ j v ε x u).ofLp)
    (hscale : ∀ color (j : Fin J), |rate color| * (2 : ℝ) ^ j.val ≤
      measuredPhaseRadius T hP (ρ := ρ))
    (hε : ∀ color (j : Fin J), rate color * (2 : ℝ) ^ j.val ∈ Icc 0 G.ε₀)
    (g : (Fin 3 → Fin (p + 1)) → Lp ℂ ∞ (volume.restrict G.D))
    (hg : ∀ color, g color =ᵐ[volume.restrict G.D] fun u ↦
      (φ (carrierSamplingEquiv (((fullInputCoordinates m).symm u).1, v)) *
        coloredBlockMask p (integerCube (blockCutoff p Bφ h)) (convolvedBoxWindow kappa p)
          h color (carrierSamplingEquiv (((fullInputCoordinates m).symm u).1, v)) : ℂ))
    {L : ℕ} (hL : L ≤ J) :
    samplingOutputConjugation (m + 1)
      (∑ color, ∑ j ∈ Finset.range L,
        (Ns color j).uniformOscillatoryNormalOperator ((2 : ℝ) ^ j) (g color)
          (rate color * (2 : ℝ) ^ j)) =
      coloredWideSliceNormal (D) φ kappa Bφ h univ L v := by
  classical
  let β := fun color z ↦ φ z * coloredBlockMask p
    (integerCube (blockCutoff p Bφ h)) (convolvedBoxWindow kappa p) h color z
  have hβ (color) : Continuous (β color) :=
    hφ.mul (contDiff_coloredBlockMask hc hkappa p _ h color).continuous
  have hβplateau (color) (z : Point) (hz : β color z ≠ 0) : ψ z = 1 :=
    hplateau z (left_ne_zero_of_mul hz)
  let H := fun color (j : Fin J) (s : ℝ) ↦
    β color (carrierSamplingEquiv (s, v)) •
      atomNormal (wideBandKernelOperator (D) j.val (j, (color, carrierSamplingEquiv (s, v))))
  have hsingle (color) (j : Fin J) : Integrable (H color j) ∧
      samplingOutputConjugation (m + 1)
        ((Ns color j.val).uniformOscillatoryNormalOperator ((2 : ℝ) ^ j.val) (g color)
          (rate color * (2 : ℝ) ^ j.val)) = ∫ s, H color j s :=
    correctedColoredCrossBandData_weighted_normal_eq_transportHomotopy
      T Q F row col Φ Y χ B r κ C z₀ hρ hκc rate hA hC hP hcarrier hrate
      angular highPass hd Md hMd hdb a haz hphase hκ ψ hψ hψc
      hψgraph hψchart j color v (hscale color j) (Ns color j.val)
      (hNphase color j.val) (hNamp color j.val) (hε color j)
      (β color) (hβ color) (hβplateau color) (g color)
      (by simpa only [β, Complex.ofReal_mul] using hg color)
  rw [map_sum]
  unfold coloredWideSliceNormal
  apply Finset.sum_congr rfl
  intro color _
  rw [← sum_retained_fin_prefix_eq_range _ hL, map_sum]
  simp_rw [(hsingle color _).2]
  rw [← integral_finsetSum _ (fun j _ ↦ (hsingle color j).1), Measure.restrict_univ]
  apply integral_congr_ae
  filter_upwards [] with s
  simp only [H, β, Finset.smul_sum, smul_smul, mul_comm,
    wideKernelOperator, wideBandKernelOperator]

include haz hphase hκ hψ hψc hψgraph hψchart in
/-- Spectator integration of the literal corrected grouped mean. The
continuous compact kernels prove integrability of the supplied exact normal
paths, with no separate measurable-selection or integrability assumption
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem correctedColoredCrossBandData_patchMeanNormal_eq_transportIntegral
    {kappa : ℝ → ℝ} (hc : HasCompactSupport kappa) (hkappa : ContDiff ℝ ∞ kappa)
    (hkappaint : ∫ t, kappa t = 1) (hkappanonneg : ∀ t, 0 ≤ kappa t)
    (hkappasupport : Function.support kappa ⊆ Icc (-(1 / 4)) (1 / 4)) (hp : 0 < p)
    (φ : Point → ℝ) (hφ : Continuous φ) (Bφ h : ℝ) (hh : h ≠ 0)
    (hplateau : ∀ z, φ z ≠ 0 → ψ z = 1)
    (V : Set (Euclidean 2)) (hV : MeasurableSet V)
    (hψV : ∀ t v, ψ (carrierSamplingEquiv (t, v)) ≠ 0 → v ∈ V)
    (Ns : Euclidean 2 → (Fin 3 → Fin (p + 1)) → ℕ → UniformNormalData G Cnormal)
    (hNphase : ∀ v ∈ V, ∀ color j, (Ns v color j).phase = fun ε x u ↦
      normalizedFullPhase T Q v ε x (canonicalInputCoordinates T u))
    (hNamp : ∀ v ∈ V, ∀ color j, (Ns v color j).amplitude = fun ε x u ↦
      (correctedTransportNormalAmplitude T Q F row col Φ Y χ B r κ C z₀ hρ (rate color)
        angular highPass ψ j v ε x u).ofLp)
    (hscale : ∀ color (j : Fin J), |rate color| * (2 : ℝ) ^ j.val ≤
      measuredPhaseRadius T hP (ρ := ρ))
    (hε : ∀ color (j : Fin J), rate color * (2 : ℝ) ^ j.val ∈ Icc 0 G.ε₀)
    (g : Euclidean 2 → (Fin 3 → Fin (p + 1)) → Lp ℂ ∞ (volume.restrict G.D))
    (hg : ∀ v ∈ V, ∀ color, g v color =ᵐ[volume.restrict G.D] fun u ↦
      (φ (carrierSamplingEquiv (((fullInputCoordinates m).symm u).1, v)) *
        coloredBlockMask p (integerCube (blockCutoff p Bφ h)) (convolvedBoxWindow kappa p)
          h color (carrierSamplingEquiv (((fullInputCoordinates m).symm u).1, v)) : ℂ))
    {L : ℕ} (hL : L ≤ J) :
    let E := fun v ↦ ∑ color, ∑ j ∈ Finset.range L,
      (Ns v color j).uniformOscillatoryNormalOperator ((2 : ℝ) ^ j) (g v color)
        (rate color * (2 : ℝ) ^ j)
    Integrable E (volume.restrict V) ∧
      patchMeanNormal p Bφ φ (convolvedBoxWindow kappa p) h
        (fun color z ↦ refinedKernelPrefix (D) L (color, z)) =
        samplingOutputConjugation (m + 1) (∫ v in V, E v) := by
  intro E
  have hw := convolvedBoxWindow_bounds
    (hkappa.continuous.integrable_of_hasCompactSupport hc) hkappaint hkappanonneg hkappasupport hp
  have hsplit := patchMeanNormal_refined_eq_spectator (B := Bφ) (D) hw hφ
    (contDiff_convolvedBoxWindow hc hkappa p).continuous hh univ V
    (fun t v hφz ↦ ⟨mem_univ _, hψV t v (by rw [hplateau _ hφz]; norm_num)⟩) L
  have heq : (fun v ↦ samplingOutputConjugation (m + 1) (E v)) =ᵐ[volume.restrict V]
      coloredWideSliceNormal (D) φ kappa Bφ h univ L := by
    filter_upwards [ae_restrict_mem hV] with v hv
    exact correctedColoredCrossBandData_colored_prefix_eq_transportSlices
      T Q F row col Φ Y χ B r κ C z₀ hρ hκc rate hA hC hP hcarrier hrate
      angular highPass hd Md hMd hdb a haz hphase hκ ψ hψ hψc
      hψgraph hψchart hc hkappa φ hφ Bφ h hplateau v (Ns v)
      (hNphase v hv) (hNamp v hv) hscale hε (g v) (hg v hv) hL
  refine ⟨?_, ?_⟩
  · exact (integrable_samplingOutputConjugation_iff E).mp (hsplit.1.congr heq.symm)
  · rw [hsplit.2, samplingOutputConjugation_integral]
    exact integral_congr_ae heq.symm


end JanetCartan.Sampling.CorrectedTransport
