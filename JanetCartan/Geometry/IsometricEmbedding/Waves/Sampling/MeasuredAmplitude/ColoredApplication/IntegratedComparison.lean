module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.ColoredApplication.TransportNormal

/-!
# Integrated comparison for the actual retained kernel and transport kernel

Apply the patch-weighted comparison to the SAME canonical normal family,
then use the two derived carrier identities and their integrability. The
constant precedes the measured fields, radial labels and frequencies. The
primitive inputs below are supplied by the retained polynomial producer and
`exists_full_retained_measuredKernel_mean`; their final joint instantiation
remains explicit. Consumer: `app:ch_waves:eq:colored-normal-comparison`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius ENNReal
namespace JanetCartan.Sampling.MeasuredAmplitude.ColoredApplication
open ActualCarriers FrozenMenu CurrentFullPhase LeadingWave.FullModulation RawKernel
open SamplingKernelBounds RawPrimary.MaskProfiles RawInputPartition FullPhaseCharts
open MeanNormalBound MeanNormalBound.NormalizedFullPhase MeanNormalBound.CanonicalGap ContinuumRow
open NormalComparison ColoredNormalComparison SeparatedSampling LatticeQuadrature BackgroundQuadrature Realization

/-- The literal colored mean of every retained grouped prefix differs from
the uncolored normal of the constructed zero kernel by `A * lam⁻¹ * Λ / h`.
All normal identities and spectator integrability are derived here from the
actual primitive formulas. Both quadratures retain factor four and all bands
use the original ceiling. This still requires the original retained producers
to instantiate the displayed primitive polynomial and normal-family outputs
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem exists_retained_integrated_prefix_transport_bound
    {m p : ℕ} (G : UniformNormalGeometry (m + 1) (m + 1)) (Cnormal : ℕ → ℝ)
    (V : Set (Euclidean 2)) (hV : IsCompact V)
    {κ : ℝ → ℝ} (hc : HasCompactSupport κ) (hκ : ContDiff ℝ ∞ κ)
    (hκint : ∫ t, κ t = 1) (hκnonneg : ∀ t, 0 ≤ κ t)
    (hκsupport : Function.support κ ⊆ Icc (-(1 / 4)) (1 / 4)) (hp : 0 < p)
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
  (_hphase : closedBall a (2 * ρ) ⊆ domain T)
  (_hχ : Function.support χ ⊆ closedBall a.1 (ρ / 2))
  (ψ : SeparatedSampling.Point → ℝ) {R Pψ : ℝ}
  (_hψ : SeparatedSampling.PatchBounds ψ R Pψ) (_hψc : Continuous ψ)
  (_hψgraph : ∀ s v, ψ (carrierSamplingEquiv (s, v)) ≠ 0 →
    (carrierParameters (v, s), T.reference.spatialPatch (carrierParameters (v, s))) ∈
      closedBall a.2 (ρ / 4))
  (_hψchart : ∀ s v, ψ (carrierSamplingEquiv (s, v)) ≠ 0 →
    carrierParameters (v, s) ∈ parameterInterior (3 * P.radius / 2))
  (_hplateau : ∀ z, φ z ≠ 0 → ψ z = 1)
  (_hψV : ∀ t v, ψ (carrierSamplingEquiv (t, v)) ≠ 0 → v ∈ V)
  (Ns : Euclidean 2 → ℕ → UniformNormalData G Cnormal)
  (_hNp : ∀ v ∈ V, ∀ j, (Ns v j).phase = fun ε x u ↦
    normalizedFullPhase T Q v ε x (canonicalInputCoordinates T u))
  (_hNa : ∀ v ∈ V, ∀ j, (Ns v j).amplitude = fun ε x u ↦
    (supportedMeasuredNormalAmplitude T Q F row col Φ Y r measurement χ a hρ
      angular highPass ψ j v ε x u).ofLp)
  (Rcolor : (Fin 3 → Fin (p + 1)) → ℝ) (_hR : ∀ c, Rmin ≤ Rcolor c)
  (h lam Λ : ℝ) (_hh : 0 < h) (_hh₁ : h ≤ 1) (_hlam : 0 < lam) (_hΛ : 1 ≤ Λ)
  (_hτeq : ∀ c, τ c = (Rcolor c * lam)⁻¹)
  (_hbuffer : 2 * Λ / (Rmin * lam) ≤ G.ε₀)
  (_hJ : J ≤ cutoffCount Λ)
  (_hscale : ∀ color (j : Fin J), |τ color| * (2 : ℝ) ^ j.val ≤
    measuredPhaseRadius T hP (ρ := ρ))
  (L : ℕ) (_hL : L ≤ J),
  let D := retainedMeasuredKernelData (J := J) T Q F row col Φ Y r measurement χ
    a hρ hP hcarrier hs M hM hb angular highPass ha hH hH₀ B hB hdB τ hτ hτ₀
  let D₀ := retainedTransportKernelData (J := J) T Q F row col Φ Y r measurement χ
    a hρ hP hcarrier hs M hM hb angular highPass ha hH hH₀ B hB hdB
  let E := patchMeanNormal p Bφ φ (convolvedBoxWindow κ p) h
    (fun color z ↦ refinedKernelPrefix D L (color, z))
  let E₀ := ∫ z : Point, φ z • atomNormal (refinedKernelPrefix D₀ L z)
  ‖E - E₀‖ ≤ A * lam⁻¹ * Λ / h ∧
    ‖(4 : ℝ) • realOutputCompression E - (4 : ℝ) • realOutputCompression E₀‖ ≤
      4 * (A * lam⁻¹ * Λ / h) := by
  obtain ⟨A, hA, hcomp⟩ := exists_patch_powTwo_prefix_transport_bound G Cnormal
    hc hκ hκint hκnonneg hκsupport hp hφ hφs (retainedCarrierProjection m) hRmin
  let Aout := (volume.real V + 1) * A
  refine ⟨Aout, by dsimp [Aout]; positivity, ?_⟩
  intro N J P U hU T Q F row col Φ Y r measurement χ a ρ hρ c C hP hcarrier
    hs M hM hb angular highPass ha hH hH₀ B hB hdB τ hτ hτ₀
    hphase hχ ψ R Pψ hψ hψc hψgraph hψchart hplateau hψV Ns hNp hNa
    Rcolor hR h lam Λ hh hh₁ hlam hΛ hτeq hbuffer hJ hscale L hL D D₀ E E₀
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
    exists_patch_coloredBlockMask_symbols hc hκ hκint hκnonneg hp hφ hφs.continuous
      G.D h (z v) (hzc v)
  let g₀ := fun v ↦ ∑ color, g v color
  have hg₀ (v : Euclidean 2) : g₀ v =ᵐ[volume.restrict G.D] fun u ↦ (φ (z v u) : ℂ) := by
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (g v), Filter.eventually_all.mpr (hg v)]
      with u hsum hu
    change (∑ color, g v color) u = _
    rw [hsum, Finset.sum_apply]
    simp_rw [hu, ← Complex.ofReal_mul]
    rw [← Complex.ofReal_sum, sum_patch_mul_coloredBlockMask
      (hκ.continuous.integrable_of_hasCompactSupport hc) hκint hκnonneg hκsupport hp hφ hh hh₁]
  have hε (color) (j : Fin J) : τ color * (2 : ℝ) ^ j.val ∈ Icc 0 G.ε₀ := by
    rw [hτeq]
    exact radial_powTwo_parameter_mem hRmin (hR color) hlam hΛ hbuffer (j.isLt.trans_le hJ)
  have hcolored := retainedMeasuredKernelData_patchMeanNormal_eq_integral
    T Q F row col Φ Y r measurement χ a hρ hP hcarrier hs M hM hb
    angular highPass ha hH hH₀ B hB hdB τ hτ hτ₀ hphase hχ ψ hψ hψc
    hψgraph hψchart hc hκ hκint hκnonneg hκsupport hp φ hφs.continuous Bφ h hh.ne'
    hplateau V hV.measurableSet hψV Ns hNp hNa hscale hε g (fun v _ ↦ hg v) hL
  have hzero := retainedTransportKernelData_prefix_integral
    T Q F row col Φ Y r measurement χ a hρ hP hcarrier hs M hM hb
    angular highPass ha hH hH₀ B hB hdB hphase hχ ψ hψ hψc hψgraph
    hφ hφs.continuous hplateau V hV.measurableSet hψV Ns hNp hNa g₀ (fun v _ ↦ hg₀ v) hL
  let Aε := fun v ↦ ∑ color, ∑ j ∈ Finset.range L,
    (Ns v j).uniformOscillatoryNormalOperator ((2 : ℝ) ^ j) (g v color)
      (τ color * (2 : ℝ) ^ j)
  let A₀ := fun v ↦ ∑ j ∈ Finset.range L,
    (Ns v j).uniformOscillatoryNormalOperator ((2 : ℝ) ^ j) (g₀ v) 0
  have hslicebound (v : Euclidean 2) : ‖Aε v - A₀ v‖ ≤ A * lam⁻¹ * Λ / h := by
    have hhg (color) : g v color =ᵐ[volume.restrict G.D] fun u ↦
        (φ (carrierSamplingEquiv (0, v) + retainedCarrierProjection m u) *
          coloredBlockMask p (integerCube (blockCutoff p Bφ h)) (convolvedBoxWindow κ p)
            h color (carrierSamplingEquiv (0, v) + retainedCarrierProjection m u) : ℂ) := by
      simpa only [hz] using hg v color
    have hhg₀ : g₀ v =ᵐ[volume.restrict G.D] fun u ↦
        (φ (carrierSamplingEquiv (0, v) + retainedCarrierProjection m u) : ℂ) := by
      simpa only [hz] using hg₀ v
    simpa only [Aε, A₀, hτeq] using (hcomp (Ns v) Rcolor hR
      (carrierSamplingEquiv (0, v)) h hh hh₁ (g v) (g₀ v) hhg hhg₀
      lam Λ hlam hΛ hbuffer L (hL.trans hJ)).1
  have hint : ‖(∫ v in V, Aε v) - ∫ v in V, A₀ v‖ ≤ Aout * lam⁻¹ * Λ / h := by
    rw [← integral_sub hcolored.1 hzero.1]
    calc
      _ ≤ (A * lam⁻¹ * Λ / h) * volume.real V :=
        norm_setIntegral_le_of_norm_le_const hV.measure_lt_top (fun v _ ↦ hslicebound v)
      _ ≤ Aout * lam⁻¹ * Λ / h := by
        calc
          _ ≤ (A * lam⁻¹ * Λ / h) * (volume.real V + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          _ = _ := by dsimp [Aout]; ring
  dsimp only [E, E₀]
  rw [hcolored.2, hzero.2]
  exact sampling_normal_comparison_of_coordinate_bound _ _ hint

end JanetCartan.Sampling.MeasuredAmplitude.ColoredApplication
