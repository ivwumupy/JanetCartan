module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CorrectedTransport.ZeroKernelMatching
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CorrectedTransport.PrefixIntegration

/-!
# Leading transport normals and their spectator integral

The literal leading kernel supplies the zero normal of the corrected path.
The same patch plateau removes the auxiliary carrier weight, and the original
kernel continuity proves integrability at every grouped prefix.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius ENNReal
namespace JanetCartan.Sampling.CorrectedTransport
open CanonicalRowComparison RawPrimary CorrectedAtoms CorrectedMean MeasuredAmplitude
open ActualCarriers FrozenMenu CurrentFullPhase LeadingWave LeadingWave.FullModulation
open FullNormalGeometry FullPhaseCharts MeanNormalBound.NormalizedFullPhase
open RawPrimary.MaskProfiles RawKernel RawInputPartition SamplingKernelBounds
open CanonicalAtomRealization MeasuredAmplitude.ColoredApplication SeparatedSampling
open MeanNormalBound.CanonicalGap NormalComparison RawPrimary.SliceBounds FullPhaseCharts.ActualComparison
open ColoredNormalComparison MeanNormalBound
open CurrentMean NullTransport ActualFlow FlowAmplitude
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumRow.LeadingPrimitive

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


variable {J : ℕ}
    (hκc : HasCompactSupport κ)
    (hA₀ : Continuous (fun w ↦ κ w • fullLeadingPrincipalMatrix T Q F row col Φ Y r w))
    (hC : Continuous C) {c₀ C₀ : ℝ} (hP : P.IsValid c₀ C₀)
    (hcarrier : closedBall z₀ (2 * ρ) ⊆ parameterInterior (2 * P.radius))
    (angular : Euclidean (m + 1 - 1) → ℂ) (highPass : Euclidean (m + 1 - 1) → ℝ)
    (hd : Continuous (detectorMask angular highPass))
    (Md : ℝ) (hMd : 0 ≤ Md) (hdb : ∀ η, ‖detectorMask angular highPass η‖ ≤ Md)

local notation "D₀" => leadingCrossTransportKernelData T Q F row col Φ Y r κ C z₀ hρ
  hκc hA₀ hC hP hcarrier (detectorMask angular highPass) hd Md hMd hdb J

variable
  (a : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
  (haz : a.2.1 = z₀) (τ : ℝ)
  (hphase : closedBall a (2 * ρ) ⊆ domain T)
  (hκ : Prod.fst '' Function.support κ ⊆ closedBall a.1 (ρ / 2))
  (ψ : SeparatedSampling.Point → ℝ) {R Pψ : ℝ}
  (hψ : SeparatedSampling.PatchBounds ψ R Pψ) (hψc : Continuous ψ)
  (hψgraph : ∀ s v, ψ (carrierSamplingEquiv (s, v)) ≠ 0 →
    (carrierParameters (v, s), T.reference.spatialPatch (carrierParameters (v, s))) ∈
      closedBall a.2 (ρ / 4))

variable (j : Fin J) (v : Euclidean 2)
  {G : UniformNormalGeometry (m + 1) (m + 1)} {Cnormal : ℕ → ℝ}
  (Ndata : UniformNormalData G Cnormal)
  (hNphase : Ndata.phase = fun ε x u ↦
    normalizedFullPhase T Q v ε x (canonicalInputCoordinates T u))
  (hNamp : Ndata.amplitude = fun ε x u ↦
    (correctedTransportNormalAmplitude T Q F row col Φ Y χ B r κ C z₀ hρ τ
      angular highPass ψ j.val v ε x u).ofLp)

include haz hphase hκ hψ hψc hψgraph hNphase hNamp in
/-- The patch-weighted leading kernel is the actual zero normal of the
corrected transport path. Its Bochner integrability follows from the same
continuous band kernel (`app:ch_waves:eq:colored-normal-comparison`). -/
theorem leadingCrossTransportKernelData_weighted_normal_eq_zeroHomotopy
    (φ : Point → ℝ) (hφ : Continuous φ)
    (hplateau : ∀ z, φ z ≠ 0 → ψ z = 1)
    (g₀ : Lp ℂ ∞ (volume.restrict G.D))
    (hg₀ : g₀ =ᵐ[volume.restrict G.D] fun u ↦
      (φ (carrierSamplingEquiv (((fullInputCoordinates m).symm u).1, v)) : ℂ)) :
    let f := fun s ↦ φ (carrierSamplingEquiv (s, v)) •
      atomNormal (wideBandKernelOperator (D₀) j.val (j, carrierSamplingEquiv (s, v)))
    Integrable f ∧ samplingOutputConjugation (m + 1)
      (Ndata.uniformOscillatoryNormalOperator ((2 : ℝ) ^ j.val) g₀ 0) = ∫ s : ℝ, f s := by
  obtain ⟨hi, heq⟩ := samplingNormal_eq_weighted_fullBand_slices
    (D₀) (fun z ↦ (j, z)) (continuous_const.prodMk continuous_id)
    ψ hψc φ hφ j.val R v Ndata (show (0 : ℝ) ∈ Icc 0 G.ε₀ from ⟨le_rfl, G.ε₀_pos.le⟩)
    (by
      intro u _ x hn
      rw [hNphase]
      apply leadingCrossTransportKernelData_phase_on_zero_support T Q F row col Φ Y χ B r κ C z₀ hρ
        hκc hA₀ hC hP hcarrier angular highPass hd Md hMd hdb a haz hphase hκ ψ hψgraph
        τ j v u.1 u.2 x
      intro hz
      simp only [Prod.mk.eta] at hz
      apply hn
      rw [hNamp]
      change (correctedTransportNormalAmplitude T Q F row col Φ Y χ B r κ C z₀ hρ τ
        angular highPass ψ j.val v 0 x (fullInputCoordinates m u)).ofLp = 0
      rw [hz]
      rfl)
    (by
      intro u _ x i
      rw [hNamp]
      apply leadingCrossTransportKernelData_amplitude_eq_zeroHomotopy
        T Q F row col Φ Y χ B r κ C z₀ hρ hκc hA₀ hC hP hcarrier
        angular highPass hd Md hMd hdb ψ _ τ j v u.1 u.2 x i
      intro t v' hv'
      have hg := hψgraph t v' hv'
      rw [← closedBall_prod_same] at hg
      rw [← haz]
      exact closedBall_subset_closedBall (by linarith) hg.1)
    (by
      intro u hu x
      rw [hNamp]
      change (correctedTransportNormalAmplitude T Q F row col Φ Y χ B r κ C z₀ hρ τ
        angular highPass ψ j.val v 0 x u).ofLp = 0
      rw [correctedTransportNormalAmplitude_eq_zero_off_fullInputDomain
        T Q F row col Φ Y χ B r κ C z₀ hρ τ angular highPass ψ hψ j.val v 0 u hu]
      rfl) g₀ hg₀
  have hweight (z : Point) : φ z * ψ z ^ 2 = φ z := by
    by_cases hz : φ z = 0
    · simp only [hz, zero_mul]
    · rw [hplateau z hz, one_pow, mul_one]
  simp only [hweight] at hi heq
  have hout (s : ℝ) (hs : s ∉ Icc (-R) R) :
      φ (carrierSamplingEquiv (s, v)) •
        atomNormal (wideBandKernelOperator (D₀) j.val (j, carrierSamplingEquiv (s, v))) = 0 := by
    have hz : φ (carrierSamplingEquiv (s, v)) = 0 := by
      by_contra hn
      have hp : ψ (carrierSamplingEquiv (s, v)) ≠ 0 := by rw [hplateau _ hn]; norm_num
      have h := hψ.support _ hp 0
      simp only [carrierSamplingEquiv_apply, Fin.cons_zero] at h
      exact hs (abs_le.mp h)
    rw [hz, zero_smul]
  exact ⟨IntegrableOn.integrable_of_forall_notMem_eq_zero hi hout,
    heq.trans (setIntegral_eq_integral_of_forall_compl_eq_zero hout)⟩

include haz hphase hκ hψ hψc hψgraph in
/-- The literal leading prefix has the zero-normal spectator integral
for every grouped prefix, with the original patch weight and cutoff plateau.
No independent integrability assumption is required
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem leadingCrossTransportKernelData_prefix_eq_zeroIntegral
    {φ : Point → ℝ} {Bφ Pφ : ℝ} (hφ : PatchBounds φ Bφ Pφ) (hφc : Continuous φ)
    (hplateau : ∀ z, φ z ≠ 0 → ψ z = 1)
    (V : Set (Euclidean 2)) (hV : MeasurableSet V)
    (hψV : ∀ t v, ψ (carrierSamplingEquiv (t, v)) ≠ 0 → v ∈ V)
    (Ns : Euclidean 2 → ℕ → UniformNormalData G Cnormal)
    (hNp : ∀ v ∈ V, ∀ j, (Ns v j).phase = fun ε x u ↦
      normalizedFullPhase T Q v ε x (canonicalInputCoordinates T u))
    (hNa : ∀ v ∈ V, ∀ j, (Ns v j).amplitude = fun ε x u ↦
      (correctedTransportNormalAmplitude T Q F row col Φ Y χ B r κ C z₀ hρ τ
        angular highPass ψ j v ε x u).ofLp)
    (g₀ : Euclidean 2 → Lp ℂ ∞ (volume.restrict G.D))
    (hg₀ : ∀ v ∈ V, g₀ v =ᵐ[volume.restrict G.D] fun u ↦
      (φ (carrierSamplingEquiv (((fullInputCoordinates m).symm u).1, v)) : ℂ))
    {L : ℕ} (hL : L ≤ J) :
    let E₀ := fun v ↦ ∑ j ∈ Finset.range L,
      (Ns v j).uniformOscillatoryNormalOperator ((2 : ℝ) ^ j) (g₀ v) 0
    Integrable E₀ (volume.restrict V) ∧
      (∫ z : Point, φ z • atomNormal (refinedKernelPrefix (D₀) L z)) =
        samplingOutputConjugation (m + 1) (∫ v in V, E₀ v) := by
  intro E₀
  let H := fun z : Point ↦ φ z • atomNormal (refinedKernelPrefix (D₀) L z)
  have hHint : Integrable H :=
    integrable_patch_normal hφ hφc _ (continuous_refinedKernelPrefix (D₀) L)
  have hHi := carrierSamplingEquiv_measurePreserving.integrable_comp_of_integrable hHint
  have hsingle (v : Euclidean 2) (hv : v ∈ V) (j : Fin J) :=
    leadingCrossTransportKernelData_weighted_normal_eq_zeroHomotopy
      T Q F row col Φ Y χ B r κ C z₀ hρ hκc hA₀ hC hP hcarrier
      angular highPass hd Md hMd hdb a haz τ hphase hκ ψ hψ hψc hψgraph
      j v (Ns v j.val) (hNp v hv j.val) (hNa v hv j.val) φ hφc hplateau (g₀ v) (hg₀ v hv)
  have heq (v : Euclidean 2) (hv : v ∈ V) :
      samplingOutputConjugation (m + 1) (E₀ v) = ∫ s : ℝ, H (carrierSamplingEquiv (s, v)) := by
    dsimp only [E₀]
    rw [← sum_retained_fin_prefix_eq_range _ hL, map_sum]
    simp_rw [(hsingle v hv _).2]
    rw [← integral_finsetSum _ (fun j _ ↦ (hsingle v hv j).1)]
    apply integral_congr_ae
    filter_upwards [] with s
    simp only [H, ColoredNormalComparison.refinedKernelPrefix_normal_eq_wide,
      Finset.smul_sum, wideKernelOperator, wideBandKernelOperator]
  have heqae : (fun v ↦ samplingOutputConjugation (m + 1) (E₀ v)) =ᵐ[volume.restrict V]
      (fun v ↦ ∫ s : ℝ, H (carrierSamplingEquiv (s, v))) :=
    (ae_restrict_mem (μ := volume) hV).mono heq
  have hzero (v : Euclidean 2) (hv : v ∉ V) : (∫ s : ℝ, H (carrierSamplingEquiv (s, v))) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [] with t
    have hz : φ (carrierSamplingEquiv (t, v)) = 0 := by
      by_contra hn
      apply hv
      apply hψV t v
      rw [hplateau _ hn]
      norm_num
    simp only [H, hz, zero_smul, Pi.zero_apply]
  refine ⟨(integrable_samplingOutputConjugation_iff E₀).mp
    (hHi.integral_prod_right.restrict.congr heqae.symm), ?_⟩
  change (∫ z, H z) = _
  rw [← integral_carrierSamplingEquiv,
    integral_prod_symm (fun q ↦ H (carrierSamplingEquiv q)) hHi,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    samplingOutputConjugation_integral]
  exact integral_congr_ae heqae.symm


end JanetCartan.Sampling.CorrectedTransport
