module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.PhaseMatching
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.ColumnNormal

/-!
# Full normal of the actual retained measured kernel

Apply the checked support-local column identity to the concrete
`retainedMeasuredKernelData`. Its phase, amplitude and input-support conditions
are all discharged from the original retained formulas. The normal data below
are exactly the nonzero output of `exists_retained_measuredNormalData`, on the
same geometry from `FullNormalGeometry`. Their displayed field equalities
identify these already constructed objects; no operator identity is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.Sampling.MeasuredAmplitude
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

include hphase hχ hψ hψgraph hψchart hscale hNphase hNamp hε in
/-- The full output normal of the SAME retained measured band equals the
constructed nonzero canonical normal after the exact output-coordinate
isometry. Phase agreement is proved only where the measured amplitude is
nonzero; both global extensions are retained. No smooth calculus is applied
to either sharp Hilbert piece (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem retainedMeasuredKernelData_normal_eq_uniform :
    atomNormal (fullBandKernelOperator (D) (fun z ↦ (j, (color, z)))
      (continuous_const.prodMk (continuous_const.prodMk continuous_id))
      ψ hψc j.val R v) =
      samplingOutputConjugation (m + 1)
        ((Ndata.uniformOscillatoryOperator ((2 : ℝ) ^ j.val)
          ((τ color) * (2 : ℝ) ^ j.val)).comp
          (Ndata.uniformOscillatoryOperator ((2 : ℝ) ^ j.val)
            ((τ color) * (2 : ℝ) ^ j.val)).adjoint) := by
  apply fullBandKernelOperator_normal_eq_uniform_of_supported_phase
    (D) (fun z ↦ (j, (color, z)))
    (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    ψ hψc j.val R v Ndata hε
  · intro u _ x hn
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
    rfl
  · intro u _ x i
    rw [hNamp]
    exact retainedMeasuredKernelData_amplitude_normalization T Q F row col Φ Y r
      measurement χ a hρ hP hcarrier hs M hM hb angular highPass ha hH hH₀ B hB hdB
      τ hτ hτ₀ ψ hψgraph j color v u.1 u.2 x i
  · intro u hu x
    rw [hNamp]
    change (supportedMeasuredNormalAmplitude T Q F row col Φ Y r measurement χ a hρ
      angular highPass ψ j.val v ((τ color) * (2 : ℝ) ^ j.val) x u).ofLp = 0
    rw [supportedMeasuredNormalAmplitude_eq_zero_off_fullInputDomain
      T Q F row col Φ Y r measurement χ a hρ angular highPass ψ hψ]
    · rfl
    · exact hu

include hphase hχ hψ hψgraph hψchart hscale hNphase hNamp hε in
/-- The same exact normal equality for both physical real quadratures,
including the original factor four (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem retainedMeasuredKernelData_real_normal_eq_uniform :
    let A := fullBandKernelOperator (D) (fun z ↦ (j, (color, z)))
      (continuous_const.prodMk (continuous_const.prodMk continuous_id)) ψ hψc j.val R v
    (realQuadratureChannel A).comp (realQuadratureChannel A).adjoint =
      samplingRealNormal (m + 1)
        ((Ndata.uniformOscillatoryOperator ((2 : ℝ) ^ j.val)
          ((τ color) * (2 : ℝ) ^ j.val)).comp
          (Ndata.uniformOscillatoryOperator ((2 : ℝ) ^ j.val)
            ((τ color) * (2 : ℝ) ^ j.val)).adjoint) := by
  dsimp only
  rw [realQuadratureChannel_normal_eq_four_realPart]
  change (4 : ℝ) • realOutputCompression (atomNormal _) = _
  rw [retainedMeasuredKernelData_normal_eq_uniform T Q F row col Φ Y r measurement χ a hρ
    hP hcarrier hs M hM hb angular highPass ha hH hH₀ B hB hdB τ hτ hτ₀ hphase hχ
    ψ hψ hψc hψgraph hψchart j color v hscale Ndata hNphase hNamp hε]
  rfl

end JanetCartan.Sampling.MeasuredAmplitude
