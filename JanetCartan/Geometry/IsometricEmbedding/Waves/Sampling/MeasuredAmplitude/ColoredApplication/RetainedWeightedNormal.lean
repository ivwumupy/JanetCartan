module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.RetainedNormal
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.ColoredApplication.WeightedColumnNormal

/-!
# The weighted normal of the same retained measured kernel

Apply the full-input weighted column theorem to `retainedMeasuredKernelData`.
All phase, amplitude and support obligations come from its original retained
formulas. The auxiliary carrier cutoff is removed only on the support of the
original weight. This is the single-band identity consumed by the literal
prefix assembly of `app:ch_waves:eq:colored-normal-comparison`.
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
open NormalComparison ColoredNormalComparison

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
  (j : Fin J) (color : Fin 3 → Fin (p + 1)) (v : Euclidean 2)
  (hscale : |τ color| * (2 : ℝ) ^ j.val ≤ measuredPhaseRadius T hP (ρ := ρ))
  {G : UniformNormalGeometry (m + 1) (m + 1)} {Cnormal : ℕ → ℝ}
  (Ndata : UniformNormalData G Cnormal)
  (hNphase : Ndata.phase = fun ε x u ↦
    normalizedFullPhase T Q v ε x (canonicalInputCoordinates T u))
  (hNamp : Ndata.amplitude = fun ε x u ↦
    (supportedMeasuredNormalAmplitude T Q F row col Φ Y r measurement χ a hρ
      angular highPass ψ j.val v ε x u).ofLp)
  (hε : (τ color) * (2 : ℝ) ^ j.val ∈ Icc 0 G.ε₀)

include hphase hχ hψ hψc hψgraph hψchart hscale hNphase hNamp hε in
/-- The patch-weighted normal of the SAME retained measured band equals its
actual canonical homotopy normal on full output. The original weight is in the
multiplier, the smooth auxiliary cutoff is removed by its plateau, and the
actual phase domain has no assumed Cartesian-product structure
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem retainedMeasuredKernelData_weighted_normal_eq_uniform
    (β : SeparatedSampling.Point → ℝ) (hβ : Continuous β)
    (hplateau : ∀ z, β z ≠ 0 → ψ z = 1)
    (g : Lp ℂ ∞ (volume.restrict G.D))
    (hg : g =ᵐ[volume.restrict G.D] fun u ↦
      (β (carrierSamplingEquiv (((fullInputCoordinates m).symm u).1, v)) : ℂ)) :
    let f := fun s ↦ β (carrierSamplingEquiv (s, v)) •
      atomNormal (wideBandKernelOperator (D) j.val (j, (color, carrierSamplingEquiv (s, v))))
    Integrable f ∧
      samplingOutputConjugation (m + 1)
        (Ndata.uniformOscillatoryNormalOperator ((2 : ℝ) ^ j.val) g
          ((τ color) * (2 : ℝ) ^ j.val)) = ∫ s : ℝ, f s := by
  obtain ⟨hi, heq⟩ := samplingNormal_eq_weighted_fullBand_slices
    (D) (fun z ↦ (j, (color, z)))
    (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    ψ hψc β hβ j.val R v Ndata hε
    (by
      intro u _ x hn
      rw [hNphase]
      apply retainedMeasuredKernelData_phase_on_support T Q F row col Φ Y r measurement χ
        a hρ hP hcarrier hs M hM hb angular highPass ha hH hH₀ B hB hdB τ hτ hτ₀
        hphase hχ ψ hψgraph hψchart j color v hscale u.1 u.2 x
      intro hz
      simp only [Prod.mk.eta] at hz
      apply hn
      rw [hNamp]
      change (supportedMeasuredNormalAmplitude T Q F row col Φ Y r measurement χ a hρ
        angular highPass ψ j.val v ((τ color) * (2 : ℝ) ^ j.val) x
          (fullInputCoordinates m u)).ofLp = 0
      rw [hz]
      rfl)
    (by
      intro u _ x i
      rw [hNamp]
      exact retainedMeasuredKernelData_amplitude_normalization T Q F row col Φ Y r
        measurement χ a hρ hP hcarrier hs M hM hb angular highPass ha hH hH₀ B hB hdB
        τ hτ hτ₀ ψ hψgraph j color v u.1 u.2 x i)
    (by
      intro u hu x
      rw [hNamp]
      change (supportedMeasuredNormalAmplitude T Q F row col Φ Y r measurement χ a hρ
        angular highPass ψ j.val v ((τ color) * (2 : ℝ) ^ j.val) x u).ofLp = 0
      rw [supportedMeasuredNormalAmplitude_eq_zero_off_fullInputDomain
        T Q F row col Φ Y r measurement χ a hρ angular highPass ψ hψ]
      · rfl
      · exact hu) g hg
  have hweight (z : SeparatedSampling.Point) : β z * ψ z ^ 2 = β z := by
    by_cases hz : β z = 0
    · simp only [hz, zero_mul]
    · rw [hplateau z hz, one_pow, mul_one]
  simp only [hweight] at hi heq
  have hout (s : ℝ) (hs : s ∉ Icc (-R) R) :
      β (carrierSamplingEquiv (s, v)) •
        atomNormal (wideBandKernelOperator (D) j.val
          (j, (color, carrierSamplingEquiv (s, v)))) = 0 := by
    have hz : β (carrierSamplingEquiv (s, v)) = 0 := by
      by_contra hn
      have hp : ψ (carrierSamplingEquiv (s, v)) ≠ 0 := by rw [hplateau _ hn]; norm_num
      have h := hψ.support _ hp 0
      simp only [carrierSamplingEquiv_apply, Fin.cons_zero] at h
      exact hs (abs_le.mp h)
    rw [hz, zero_smul]
  exact ⟨IntegrableOn.integrable_of_forall_notMem_eq_zero hi hout,
    heq.trans (setIntegral_eq_integral_of_forall_compl_eq_zero hout)⟩

end JanetCartan.Sampling.MeasuredAmplitude.ColoredApplication
