module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.ColoredApplication.RetainedWeightedNormal
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.CarrierAssembly

/-!
# Grouped prefixes of the actual patch-weighted retained kernel

Reassemble both sharp components before the normal comparison, then integrate
in the original carrier coordinates. The consumer is the full retained
application of `app:ch_waves:eq:colored-normal-comparison`. The normal family
and the kernel use the SAME retained polynomial, auxiliary carrier cutoff,
original patch weight and `2^j` normalization.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius ENNReal
namespace JanetCartan.Sampling.MeasuredAmplitude.ColoredApplication
open ActualCarriers FrozenMenu CurrentFullPhase LeadingWave.FullModulation RawKernel
open SamplingKernelBounds RawPrimary.MaskProfiles RawInputPartition FullPhaseCharts
open MeanNormalBound MeanNormalBound.NormalizedFullPhase MeanNormalBound.CanonicalGap ContinuumRow
open NormalComparison ColoredNormalComparison SeparatedSampling LatticeQuadrature BackgroundQuadrature Realization

/-- The original finite ceiling and its natural-number prefix have exactly
the same labels (`app:ch_waves:eq:colored-normal-comparison`). -/
theorem sum_retained_fin_prefix_eq_range {J L : ℕ} {E : Type*} [AddCommMonoid E]
    (f : ℕ → E) (hL : L ≤ J) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin J ↦ j.val < L), f j.val) =
      ∑ j ∈ Finset.range L, f j := by
  classical
  apply Finset.sum_bij (fun j _ ↦ j.val)
  · intro j hj
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
  · intro j _ k _ h
    exact Fin.ext h
  · intro j hj
    exact ⟨⟨j, (Finset.mem_range.mp hj).trans_le hL⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_range.mp hj⟩, rfl⟩
  · intro _ _
    rfl

variable {m N J p : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})
  (F : Euclidean (m + 1) → Euclidean N) (row col : Fin (m + 1))
  (Φ Y : ℝ × (Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1))) →
    Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
  (r : Euclidean (m + 1 - 1) × Euclidean 3 → ℝ)
  (measurement : Euclidean (m + 1) →
    Matrix (Fin N) (Fin (m + 1)) ℂ →L[ℂ] EuclideanSpace ℂ (Fin (m + 1)))
  (χ : Euclidean (m + 1) → ℝ)
  (a : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
  {ρ : ℝ} (hρ : 0 < ρ)
  {c C : ℝ} (hP : P.IsValid c C)
  (hcarrier : closedBall a.2.1 (2 * ρ) ⊆ parameterInterior (2 * P.radius))
  (hs : ContDiff ℝ ∞ (fun q : ℝ × (Euclidean (m + 1) ×
    (Euclidean 3 × Euclidean (m + 1 - 1))) ↦
      supportedMeasuredDerivativePolynomial T Q F row col Φ Y r measurement χ a hρ
        q.1 q.2.2.1 q.2.1 q.2.2.2))
  (M : ℝ) (hM : 0 ≤ M)
  (hb : ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ z x ξ,
    ‖supportedMeasuredDerivativePolynomial T Q F row col Φ Y r measurement χ a hρ
      τ z x ξ‖ ≤ M)
  (angular : Euclidean (m + 1 - 1) → ℂ) (highPass : Euclidean (m + 1 - 1) → ℝ)
  (ha : ∀ θ, θ ≠ 0 → ContDiffAt ℝ ∞ angular θ)
  (hH : ContDiff ℝ ∞ highPass) (hH₀ : ∀ η, ‖η‖ ≤ 1 → highPass η = 0)
  (B : ℝ) (hB : 0 ≤ B) (hdB : ∀ η, ‖detectorMask angular highPass η‖ ≤ B)
  (τ : (Fin 3 → Fin (p + 1)) → ℝ)
  (hτ : ∀ color, τ color ∈ Icc (-1 : ℝ) 1) (hτ₀ : ∀ color, τ color ≠ 0)

local notation "D" => retainedMeasuredKernelData (J := J) T Q F row col Φ Y r measurement χ
  a hρ hP hcarrier hs M hM hb angular highPass ha hH hH₀ B hB hdB τ hτ hτ₀

variable
  (hphase : closedBall a (2 * ρ) ⊆ domain T)
  (hχ : Function.support χ ⊆ closedBall a.1 (ρ / 2))
  (ψ : SeparatedSampling.Point → ℝ) {R Pψ : ℝ}
  (hψ : SeparatedSampling.PatchBounds ψ R Pψ) (hψc : Continuous ψ)
  (hψgraph : ∀ s v, ψ (carrierSamplingEquiv (s, v)) ≠ 0 →
    (carrierParameters (v, s), T.reference.spatialPatch (carrierParameters (v, s))) ∈
      closedBall a.2 (ρ / 4))
  (hψchart : ∀ s v, ψ (carrierSamplingEquiv (s, v)) ≠ 0 →
    carrierParameters (v, s) ∈ parameterInterior (3 * P.radius / 2))

variable {G : UniformNormalGeometry (m + 1) (m + 1)} {Cnormal : ℕ → ℝ}

include hphase hχ hψ hψc hψgraph hψchart in
/-- Every grouped prefix of the SAME retained measured kernel is the colored
slice of its actual homotopy. The original patch weight is in the multiplier;
the carrier cutoff is removed using its plateau. No normal identity, smooth
square root, or product-domain hypothesis is supplied
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem retainedMeasuredKernelData_colored_prefix_eq_slices
    {κ : ℝ → ℝ} (hc : HasCompactSupport κ) (hκ : ContDiff ℝ ∞ κ)
    (φ : Point → ℝ) (hφ : Continuous φ) (Bφ h : ℝ)
    (hplateau : ∀ z, φ z ≠ 0 → ψ z = 1)
    (v : Euclidean 2) (Ns : ℕ → UniformNormalData G Cnormal)
    (hNphase : ∀ j, (Ns j).phase = fun ε x u ↦
      normalizedFullPhase T Q v ε x (canonicalInputCoordinates T u))
    (hNamp : ∀ j, (Ns j).amplitude = fun ε x u ↦
      (supportedMeasuredNormalAmplitude T Q F row col Φ Y r measurement χ a hρ
        angular highPass ψ j v ε x u).ofLp)
    (hscale : ∀ color (j : Fin J), |τ color| * (2 : ℝ) ^ j.val ≤
      measuredPhaseRadius T hP (ρ := ρ))
    (hε : ∀ color (j : Fin J), τ color * (2 : ℝ) ^ j.val ∈ Icc 0 G.ε₀)
    (g : (Fin 3 → Fin (p + 1)) → Lp ℂ ∞ (volume.restrict G.D))
    (hg : ∀ color, g color =ᵐ[volume.restrict G.D] fun u ↦
      (φ (carrierSamplingEquiv (((fullInputCoordinates m).symm u).1, v)) *
        coloredBlockMask p (integerCube (blockCutoff p Bφ h)) (convolvedBoxWindow κ p)
          h color (carrierSamplingEquiv (((fullInputCoordinates m).symm u).1, v)) : ℂ))
    {L : ℕ} (hL : L ≤ J) :
    samplingOutputConjugation (m + 1)
      (∑ color, ∑ j ∈ Finset.range L,
        (Ns j).uniformOscillatoryNormalOperator ((2 : ℝ) ^ j) (g color)
          (τ color * (2 : ℝ) ^ j)) =
      coloredWideSliceNormal (D) φ κ Bφ h univ L v := by
  classical
  let β := fun color z ↦ φ z * coloredBlockMask p
    (integerCube (blockCutoff p Bφ h)) (convolvedBoxWindow κ p) h color z
  have hβ (color) : Continuous (β color) :=
    hφ.mul (contDiff_coloredBlockMask hc hκ p _ h color).continuous
  have hβplateau (color) (z : Point) (hz : β color z ≠ 0) : ψ z = 1 :=
    hplateau z (left_ne_zero_of_mul hz)
  let H := fun color (j : Fin J) (s : ℝ) ↦
    β color (carrierSamplingEquiv (s, v)) •
      atomNormal (wideBandKernelOperator (D) j.val (j, (color, carrierSamplingEquiv (s, v))))
  have hsingle (color) (j : Fin J) : Integrable (H color j) ∧
      samplingOutputConjugation (m + 1)
        ((Ns j.val).uniformOscillatoryNormalOperator ((2 : ℝ) ^ j.val) (g color)
          (τ color * (2 : ℝ) ^ j.val)) = ∫ s, H color j s :=
    retainedMeasuredKernelData_weighted_normal_eq_uniform
      T Q F row col Φ Y r measurement χ a hρ hP hcarrier hs M hM hb
      angular highPass ha hH hH₀ B hB hdB τ hτ hτ₀ hphase hχ ψ hψ hψc
      hψgraph hψchart j color v (hscale color j) (Ns j.val)
      (hNphase j.val) (hNamp j.val) (hε color j)
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

include hphase hχ hψ hψc hψgraph hψchart in
/-- Spectator integration of the literal retained grouped mean. Integrability
is proved from the original continuous kernel and compact colored windows.
The primitive family identities are exactly those exported by
`exists_full_retained_measuredKernel_mean`; no extra operator integrability
premise is needed (`app:ch_waves:eq:colored-normal-comparison`). -/
theorem retainedMeasuredKernelData_patchMeanNormal_eq_integral
    {κ : ℝ → ℝ} (hc : HasCompactSupport κ) (hκ : ContDiff ℝ ∞ κ)
    (hκint : ∫ t, κ t = 1) (hκnonneg : ∀ t, 0 ≤ κ t)
    (hκsupport : Function.support κ ⊆ Icc (-(1 / 4)) (1 / 4)) (hp : 0 < p)
    (φ : Point → ℝ) (hφ : Continuous φ) (Bφ h : ℝ) (hh : h ≠ 0)
    (hplateau : ∀ z, φ z ≠ 0 → ψ z = 1)
    (V : Set (Euclidean 2)) (hV : MeasurableSet V)
    (hψV : ∀ t v, ψ (carrierSamplingEquiv (t, v)) ≠ 0 → v ∈ V)
    (Ns : Euclidean 2 → ℕ → UniformNormalData G Cnormal)
    (hNphase : ∀ v ∈ V, ∀ j, (Ns v j).phase = fun ε x u ↦
      normalizedFullPhase T Q v ε x (canonicalInputCoordinates T u))
    (hNamp : ∀ v ∈ V, ∀ j, (Ns v j).amplitude = fun ε x u ↦
      (supportedMeasuredNormalAmplitude T Q F row col Φ Y r measurement χ a hρ
        angular highPass ψ j v ε x u).ofLp)
    (hscale : ∀ color (j : Fin J), |τ color| * (2 : ℝ) ^ j.val ≤
      measuredPhaseRadius T hP (ρ := ρ))
    (hε : ∀ color (j : Fin J), τ color * (2 : ℝ) ^ j.val ∈ Icc 0 G.ε₀)
    (g : Euclidean 2 → (Fin 3 → Fin (p + 1)) → Lp ℂ ∞ (volume.restrict G.D))
    (hg : ∀ v ∈ V, ∀ color, g v color =ᵐ[volume.restrict G.D] fun u ↦
      (φ (carrierSamplingEquiv (((fullInputCoordinates m).symm u).1, v)) *
        coloredBlockMask p (integerCube (blockCutoff p Bφ h)) (convolvedBoxWindow κ p)
          h color (carrierSamplingEquiv (((fullInputCoordinates m).symm u).1, v)) : ℂ))
    {L : ℕ} (hL : L ≤ J) :
    let E := fun v ↦ ∑ color, ∑ j ∈ Finset.range L,
      (Ns v j).uniformOscillatoryNormalOperator ((2 : ℝ) ^ j) (g v color)
        (τ color * (2 : ℝ) ^ j)
    Integrable E (volume.restrict V) ∧
      patchMeanNormal p Bφ φ (convolvedBoxWindow κ p) h
        (fun color z ↦ refinedKernelPrefix (D) L (color, z)) =
        samplingOutputConjugation (m + 1) (∫ v in V, E v) := by
  intro E
  have hw := convolvedBoxWindow_bounds
    (hκ.continuous.integrable_of_hasCompactSupport hc) hκint hκnonneg hκsupport hp
  have hsplit := patchMeanNormal_refined_eq_spectator (B := Bφ) (D) hw hφ
    (contDiff_convolvedBoxWindow hc hκ p).continuous hh univ V
    (fun t v hφz ↦ ⟨mem_univ _, hψV t v (by rw [hplateau _ hφz]; norm_num)⟩) L
  have heq : (fun v ↦ samplingOutputConjugation (m + 1) (E v)) =ᵐ[volume.restrict V]
      coloredWideSliceNormal (D) φ κ Bφ h univ L := by
    filter_upwards [ae_restrict_mem hV] with v hv
    exact retainedMeasuredKernelData_colored_prefix_eq_slices
      T Q F row col Φ Y r measurement χ a hρ hP hcarrier hs M hM hb
      angular highPass ha hH hH₀ B hB hdB τ hτ hτ₀ hphase hχ ψ hψ hψc
      hψgraph hψchart hc hκ φ hφ Bφ h hplateau v (Ns v)
      (hNphase v hv) (hNamp v hv) hscale hε (g v) (hg v hv) hL
  refine ⟨?_, ?_⟩
  · exact (integrable_samplingOutputConjugation_iff E).mp (hsplit.1.congr heq.symm)
  · rw [hsplit.2, samplingOutputConjugation_integral]
    exact integral_congr_ae heq.symm

end JanetCartan.Sampling.MeasuredAmplitude.ColoredApplication
