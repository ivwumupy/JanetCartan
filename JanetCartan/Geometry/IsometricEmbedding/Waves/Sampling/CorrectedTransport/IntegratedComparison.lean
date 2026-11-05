module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CorrectedTransport.ZeroNormal
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CorrectedTransport.EndpointComparison

/-!
# Integrated corrected-to-leading transport comparison

Compare every original corrected colored prefix to the literal leading
transport kernel. The same fixed-response paths give both endpoint identities
and integrability. Constants precede every current field and response rate.
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
open RawPrimary

/-- Every original corrected colored prefix has the transport comparison
against its literal leading kernel. Exact phase and amplitude data are supplied
by `exists_correctedTransportNormalData_of_profiles`; all spectator
integrability and endpoint matching are proved here. The actual initialized
profile application remains required
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem exists_corrected_integrated_prefix_transport_bound
    {m p : ℕ} (G : UniformNormalGeometry (m + 1) (m + 1)) (Cnormal : ℕ → ℝ)
    (V : Set (Euclidean 2)) (hV : IsCompact V)
    {kappa : ℝ → ℝ} (hc : HasCompactSupport kappa) (hkappa : ContDiff ℝ ∞ kappa)
    (hm : ∫ t, kappa t = 1) (hn : ∀ t, 0 ≤ kappa t)
    (hk : Function.support kappa ⊆ Icc (-(1 / 4)) (1 / 4)) (hp : 0 < p)
    {φ : Point → ℝ} {Bφ Pφ : ℝ} (hφ : PatchBounds φ Bφ Pφ) (hφs : ContDiff ℝ ∞ φ)
    {Rmin : ℝ} (hRmin : 0 < Rmin) :
    ∃ A > (0 : ℝ),
∀ {N J : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
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

  (hκc : HasCompactSupport κ) (rate : (Fin 3 → Fin (p + 1)) → ℝ)
  (hA : ∀ color, Continuous (fun w ↦ κ w •
    fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r (rate color) w))
  (hA₀ : Continuous (fun w ↦ κ w • fullLeadingPrincipalMatrix T Q F row col Φ Y r w))
  (hC : Continuous C) {c₀ C₀ : ℝ} (hP : P.IsValid c₀ C₀)
  (hcarrier : closedBall z₀ (2 * ρ) ⊆ parameterInterior (2 * P.radius))
  (hrate : ∀ color, rate color ≠ 0)
  (angular : Euclidean (m + 1 - 1) → ℂ) (highPass : Euclidean (m + 1 - 1) → ℝ)
  (hd : Continuous (detectorMask angular highPass))
  (Md : ℝ) (hMd : 0 ≤ Md) (hdb : ∀ η, ‖detectorMask angular highPass η‖ ≤ Md)

    (a : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
    (_haz : a.2.1 = z₀) (_hphase : closedBall a (2 * ρ) ⊆ domain T)
    (_hκ : Prod.fst '' Function.support κ ⊆ closedBall a.1 (ρ / 2))
    (ψ : SeparatedSampling.Point → ℝ) {R Pψ : ℝ}
    (_hψ : SeparatedSampling.PatchBounds ψ R Pψ) (_hψc : Continuous ψ)
    (_hψgraph : ∀ s v, ψ (carrierSamplingEquiv (s, v)) ≠ 0 →
      (carrierParameters (v, s), T.reference.spatialPatch (carrierParameters (v, s))) ∈
        closedBall a.2 (ρ / 4))
    (_hψchart : ∀ s v, ψ (carrierSamplingEquiv (s, v)) ≠ 0 →
      carrierParameters (v, s) ∈ parameterInterior (3 * P.radius / 2))

  (_hplateau : ∀ z, φ z ≠ 0 → ψ z = 1)
  (_hψV : ∀ t v, ψ (carrierSamplingEquiv (t, v)) ≠ 0 → v ∈ V)
  (Ns : Euclidean 2 → (Fin 3 → Fin (p + 1)) → ℕ → UniformNormalData G Cnormal)
  (_hNp : ∀ v ∈ V, ∀ color j, (Ns v color j).phase = fun ε x u ↦
    normalizedFullPhase T Q v ε x (canonicalInputCoordinates T u))
  (_hNa : ∀ v ∈ V, ∀ color j, (Ns v color j).amplitude = fun ε x u ↦
    (correctedTransportNormalAmplitude T Q F row col Φ Y χ B r κ C z₀ hρ (rate color)
      angular highPass ψ j v ε x u).ofLp)
  (Rcolor : (Fin 3 → Fin (p + 1)) → ℝ) (_hR : ∀ c, Rmin ≤ Rcolor c)
  (h lam Λ : ℝ) (_hh : 0 < h) (_hh₁ : h ≤ 1) (_hlam : 0 < lam) (_hΛ : 1 ≤ Λ)
  (_hrateeq : ∀ c, rate c = (Rcolor c * lam)⁻¹)
  (_hbuffer : 2 * Λ / (Rmin * lam) ≤ G.ε₀)
  (_hJ : J ≤ cutoffCount Λ)
  (_hscale : ∀ color (j : Fin J), |rate color| * (2 : ℝ) ^ j.val ≤
    measuredPhaseRadius T hP (ρ := ρ))
  (L : ℕ) (_hL : L ≤ J),
  let D := correctedColoredCrossBandData T Q F row col Φ Y χ B r κ hκc rate hA C hC
    Prod.fst continuous_fst (fun q ↦ WithLp.toLp 2 q.2) (by fun_prop) hP z₀ hρ hcarrier hrate
    (detectorMask angular highPass) hd Md hMd hdb J
  let D₀ := leadingCrossTransportKernelData T Q F row col Φ Y r κ C z₀ hρ
    hκc hA₀ hC hP hcarrier (detectorMask angular highPass) hd Md hMd hdb J
  let E := patchMeanNormal p Bφ φ (convolvedBoxWindow kappa p) h
    (fun color z ↦ refinedKernelPrefix D L (color, z))
  let E₀ := ∫ z : Point, φ z • atomNormal (refinedKernelPrefix D₀ L z)
  ‖E - E₀‖ ≤ A * lam⁻¹ * Λ / h ∧
    ‖(4 : ℝ) • realOutputCompression E - (4 : ℝ) • realOutputCompression E₀‖ ≤
      4 * (A * lam⁻¹ * Λ / h) := by
  obtain ⟨A, hApos, hcomp⟩ := exists_fixedRate_colored_prefix_transport_bound G Cnormal
    hc hkappa hm hn hk hp hφ hφs (retainedCarrierProjection m) hRmin
  let Aout := (volume.real V + 1) * A
  refine ⟨Aout, by dsimp [Aout]; positivity, ?_⟩
  intro N J P U hU T Q F row col Φ Y χ B r κ C z₀ ρ hρ
    hκc rate hA hA₀ hC c₀ C₀ hP hcarrier hrate angular highPass hd Md hMd hdb
    a haz hphase hκ ψ R Pψ hψ hψc hψgraph hψchart hplateau hψV Ns hNp hNa
    Rcolor hR h lam Λ hh hh₁ hlam hΛ hrateeq hbuffer hJ hscale L hL D D₀ E E₀
  let c₀ : Fin 3 → Fin (p + 1) := fun _ ↦ 0
  let N₀ := fun v j ↦ Ns v c₀ j
  let z := fun v u ↦ carrierSamplingEquiv (((fullInputCoordinates m).symm u).1, v)
  have hz (v : Euclidean 2) (u : Euclidean (m + 1)) :
      carrierSamplingEquiv (0, v) + retainedCarrierProjection m u = z v u := by
    simpa only [MeasurableEquiv.apply_symm_apply, z] using
      retainedCarrierProjection_affine m v ((fullInputCoordinates m).symm u)
  have hzc (v : Euclidean 2) : Continuous (z v) := by
    change Continuous (fun u ↦ z v u)
    simp_rw [← hz v]
    exact continuous_const.add (retainedCarrierProjection m).continuous
  choose g hg _hgb using fun v : Euclidean 2 ↦
    exists_patch_coloredBlockMask_symbols hc hkappa hm hn hp hφ hφs.continuous
      G.D h (z v) (hzc v)
  let g₀ := fun v ↦ ∑ color, g v color
  have hg₀ (v : Euclidean 2) : g₀ v =ᵐ[volume.restrict G.D] fun u ↦ (φ (z v u) : ℂ) := by
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (g v), Filter.eventually_all.mpr (hg v)]
      with u hsum hu
    change (∑ color, g v color) u = _
    rw [hsum, Finset.sum_apply]
    simp_rw [hu, ← Complex.ofReal_mul]
    rw [← Complex.ofReal_sum, sum_patch_mul_coloredBlockMask
      (hkappa.continuous.integrable_of_hasCompactSupport hc) hm hn hk hp hφ hh hh₁]
  have hε (color) (j : Fin J) : rate color * (2 : ℝ) ^ j.val ∈ Icc 0 G.ε₀ := by
    rw [hrateeq]
    exact radial_powTwo_parameter_mem hRmin (hR color) hlam hΛ hbuffer (j.isLt.trans_le hJ)
  have hcolored := correctedColoredCrossBandData_patchMeanNormal_eq_transportIntegral
    T Q F row col Φ Y χ B r κ C z₀ hρ hκc rate hA hC hP hcarrier hrate
    angular highPass hd Md hMd hdb a haz hphase hκ ψ hψ hψc hψgraph hψchart
    hc hkappa hm hn hk hp φ hφs.continuous Bφ h hh.ne' hplateau V hV.measurableSet hψV
    Ns hNp hNa hscale hε g (fun v _ ↦ hg v) hL
  have hzero := leadingCrossTransportKernelData_prefix_eq_zeroIntegral
    T Q F row col Φ Y χ B r κ C z₀ hρ hκc hA₀ hC hP hcarrier
    angular highPass hd Md hMd hdb a haz (rate c₀) hphase hκ ψ hψ hψc hψgraph
    hφ hφs.continuous hplateau V hV.measurableSet hψV N₀
    (fun v hv j ↦ hNp v hv c₀ j) (fun v hv j ↦ hNa v hv c₀ j)
    g₀ (fun v _ ↦ hg₀ v) hL
  let Aε := fun v ↦ ∑ color, ∑ j ∈ Finset.range L,
    (Ns v color j).uniformOscillatoryNormalOperator ((2 : ℝ) ^ j) (g v color)
      (rate color * (2 : ℝ) ^ j)
  let A₀ := fun v ↦ ∑ j ∈ Finset.range L,
    (N₀ v j).uniformOscillatoryNormalOperator ((2 : ℝ) ^ j) (g₀ v) 0
  have hslicebound (v : Euclidean 2) (hv : v ∈ V) : ‖Aε v - A₀ v‖ ≤ A * lam⁻¹ * Λ / h := by
    have hpzero (color j) : (Ns v color j).phase 0 = (N₀ v j).phase 0 := by
      dsimp [N₀]
      rw [hNp v hv color j, hNp v hv c₀ j]
    have hazero (color j) : (Ns v color j).amplitude 0 = (N₀ v j).amplitude 0 := by
      dsimp [N₀]
      rw [hNa v hv color j, hNa v hv c₀ j]
      funext x u
      exact congrArg (fun f : EuclideanSpace ℂ (Fin (m + 1)) ↦ f.ofLp)
        (correctedTransportNormalAmplitude_zero_independent T Q F row col Φ Y χ B r κ C z₀ hρ
          angular highPass ψ (rate color) (rate c₀) j v x u)
    have hhg (color) : g v color =ᵐ[volume.restrict G.D] fun u ↦
        (φ (carrierSamplingEquiv (0, v) + retainedCarrierProjection m u) *
          coloredBlockMask p (integerCube (blockCutoff p Bφ h)) (convolvedBoxWindow kappa p)
            h color (carrierSamplingEquiv (0, v) + retainedCarrierProjection m u) : ℂ) := by
      simpa only [hz] using hg v color
    have hhg₀ : g₀ v =ᵐ[volume.restrict G.D] fun u ↦
        (φ (carrierSamplingEquiv (0, v) + retainedCarrierProjection m u) : ℂ) := by
      simpa only [hz] using hg₀ v
    simpa only [Aε, A₀, hrateeq] using (hcomp (Ns v) (N₀ v) hpzero hazero Rcolor hR
      (carrierSamplingEquiv (0, v)) h hh hh₁ (g v) (g₀ v) hhg hhg₀
      lam Λ hlam hΛ hbuffer L (hL.trans hJ)).1
  have hint : ‖(∫ v in V, Aε v) - ∫ v in V, A₀ v‖ ≤ Aout * lam⁻¹ * Λ / h := by
    rw [← integral_sub hcolored.1 hzero.1]
    calc
      _ ≤ (A * lam⁻¹ * Λ / h) * volume.real V :=
        norm_setIntegral_le_of_norm_le_const hV.measure_lt_top hslicebound
      _ ≤ Aout * lam⁻¹ * Λ / h := by
        calc
          _ ≤ (A * lam⁻¹ * Λ / h) * (volume.real V + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          _ = _ := by dsimp [Aout]; ring
  dsimp only [E, E₀]
  rw [hcolored.2, hzero.2]
  exact sampling_normal_comparison_of_coordinate_bound _ _ hint

end JanetCartan.Sampling.CorrectedTransport
