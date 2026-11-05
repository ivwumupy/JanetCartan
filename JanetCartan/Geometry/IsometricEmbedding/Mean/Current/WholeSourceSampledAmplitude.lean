module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.WholeSource
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.CanonicalSampledAmplitude
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.CanonicalPrefixData

/-!
# Whole-source canonical waves realize their sampled amplitudes

The corrected physical wave applies the SAME ambient response to its complete
raw source. Its literal demodulated derivative, with the original carrier phase,
is the smooth raw map on the supplied extension plateau. This discharges the
raw-wave realization premise in the finite sampled-amplitude construction
without an atomwise response-integral premise (`main:eq:old-canonical`,
`app:ch_pairs:lem:pairs-ledger`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.CurrentMean
open CanonicalAtomRealization RawPrimary RawInputPartition CorrectedAtoms UniformStep AmplitudeBound
open ResponseSourceExtension PrimarySourceAdmission
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase

variable {n N J : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (Metric.closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (χ : Euclidean n → ℝ)

/-- The sampled derivative amplitude of the literal whole-source corrected
wave is its defined canonical derivative, with the SAME original carrier
phase (`app:ch_mean_pairs:defn:mean-canonical`). -/
theorem sampledDerivativeAmplitude_wholeSourceCorrectedWave_eq
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (τ : ℝ) (z : Euclidean 3) (d : Euclidean (n - 1) → ℂ) (v : WideInput n J) :
    sampledDerivativeAmplitude
      (fun _ : Unit ↦ wholeSourceCorrectedWave T Q F row col Φ Y r χ B τ z d v)
      (fun _ x ↦ T.carrier Q x z / τ) () =
        wholeSourceCorrectedDerivative T Q F row col Φ Y r χ B τ z d v := by
  funext x
  unfold sampledDerivativeAmplitude wholeSourceCorrectedDerivative
  have hphase : wavePhase (-(T.carrier Q x z / τ)) =
      Complex.exp (-Complex.I * (T.carrier Q x z / τ : ℝ)) := by
    unfold wavePhase
    congr 1
    push_cast
    ring
  rw [hphase]
  rfl

variable {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)
    (τ : ℝ) (z : Euclidean 3)
    {X : Set (Euclidean n)} {V : Set (Euclidean (n - 1))}
    (hshift : ∀ p ∈ X ×ˢ V, (p.1, (z, T.reference.spatialPatch z + τ • p.2)) ∈ Ω)
    (hX : IsOpen X) (hV : IsOpen V)
    (hceil : Metric.closedBall 0 ((2 : ℝ) ^ J) ⊆ V)
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ ξ, ‖d ξ‖ ≤ M)
    (hsrc : tsupport χ ⊆ X)

variable (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    {core chart : Set (Euclidean n)} (Ξ : OutputCutoff core chart)
    (η : Euclidean n → ℝ)
    (Tresp : (Euclidean n → Fin n → ℝ) →ₗ[ℝ] (Euclidean n → Fin n → ℝ))
    (Sresp : (Euclidean n → Fin n → ℝ) →ₗ[ℝ] (Euclidean n → Euclidean n))
    (hS : ∀ h : compactSmoothSources (tsupport χ), ∀ x ∈ chart,
      DifferentiableAt ℝ (Sresp (AmbientResponse.correctedStressSource Q.1 η Tresp h)) x)
    (hchart : IsOpen chart) (hchartU : chart ⊆ U)
    (hSsmooth : ∀ h : compactSmoothSources (tsupport χ),
      ContDiffOn ℝ ∞ (Sresp (AmbientResponse.correctedStressSource Q.1 η Tresp h)) chart)

variable (ψ : Euclidean n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψX : tsupport ψ ⊆ X)
    {b : ℝ} (hcell : b < 1 / 2) (hbox : ∀ x ∈ tsupport ψ, ∀ i, |x i| ≤ b)

local notation "B₀" => ambientExtension F (Subtype.val Q) η Tresp Sresp
  (compactSmoothSources (tsupport χ)) Ξ hS

/-- The actual whole-source wave realizes the smooth raw map on the
original supplied plateau and periodization box (`main:eq:old-canonical`).
This uses physical differentiation directly, so no response-integral or
final-amplitude identity is assumed. -/
theorem sampledDerivativeAmplitude_wholeSourceCorrectedWave_eq_smooth_on_plateau
    {Vsource : Set (Euclidean n)}
    (hsourceBox : ∀ x ∈ Vsource, ∀ i, |x i| < 1 - b)
    (hplateau : ∀ x ∈ Vsource, ψ x = 1) (v : WideInput n J) :
    EqOn
      (sampledDerivativeAmplitude
        (fun _ : Unit ↦ wholeSourceCorrectedWave T Q F row col Φ Y r χ B₀ τ z d v)
        (fun _ x ↦ T.carrier Q x z / τ) ())
      (periodicLift (fun x ↦
        (smoothWholeSourceCanonicalDerivative T Q F row col Φ Y r χ hΩ hspace hphase hF hi hrank
          hα hnonzero τ z hshift hX hV hceil hd hM hb hsrc hχ hc Ξ η Tresp Sresp hS
          hchart hchartU hSsmooth ψ hψ hψX hcell hbox v).val x ())) Vsource := by
  rw [sampledDerivativeAmplitude_wholeSourceCorrectedWave_eq]
  intro x hx
  have hp := preparationMatrixPeriodization_eq_of_lt
    (fun p : Euclidean n × ContinuumRow.CarrierParameter ↦ ψ p.1 •
      wholeSourceCorrectedDerivative T Q F row col Φ Y r χ B₀ τ z d v p.1) hcell
    (fun y _ hy ↦ hbox y (subset_tsupport ψ (by
      intro hzero
      exact hy (by simp [hzero])))) x 0 (hsourceBox x hx)
  change wholeSourceCorrectedDerivative T Q F row col Φ Y r χ B₀ τ z d v x =
    ψ (centeredTorusRepresentative (torusQuotient x)) •
      wholeSourceCorrectedDerivative T Q F row col Φ Y r χ B₀ τ z d v
        (centeredTorusRepresentative (torusQuotient x))
  change ψ (centeredTorusRepresentative (torusQuotient x)) •
    wholeSourceCorrectedDerivative T Q F row col Φ Y r χ B₀ τ z d v
      (centeredTorusRepresentative (torusQuotient x)) = _ at hp
  rw [hp, hplateau x hx, one_smul]

/-- Applying the original raw prefix constructs the physical wave and proves
both its smoothness and its exact sampled-amplitude realization
(`main:eq:old-canonical`, `app:ch_pairs:lem:pairs-ledger`). The full source,
response, carrier phase, extension cutoff and Hilbert datum are unchanged.
Consumer: `sampledDerivativeAmplitude_add_canonicalSum_eqOn`. -/
theorem wholeSourcePrefix_realizes_sampledAmplitude
    {Vsource : Set (Euclidean n)}
    (hsourceBox : ∀ x ∈ Vsource, ∀ i, |x i| < 1 - b)
    (hplateau : ∀ x ∈ Vsource, ψ x = 1) (L : ℕ) (v : RefinedInput n J) :
    let G := smoothWholeSourceCanonicalDerivative T Q F row col Φ Y r χ hΩ hspace hphase hF hi hrank
      hα hnonzero τ z hshift hX hV hceil hd hM hb hsrc hχ hc Ξ η Tresp Sresp hS
      hchart hchartU hSsmooth ψ hψ hψX hcell hbox
    let W := wholeSourceCorrectedWave T Q F row col Φ Y r χ B₀ τ z d
      (widePrefix n J L ((realWideRefinement n J).symm v))
    ContDiffOn ℝ ∞ W Vsource ∧
      EqOn (sampledDerivativeAmplitude (fun _ : Unit ↦ W) (fun _ x ↦ T.carrier Q x z / τ) ())
        (periodicLift (fun x ↦ (canonicalWidePrefixRawMap G L v).val x ())) Vsource := by
  constructor
  · apply (contDiffOn_wholeSourceCorrectedWave T Q F row col Φ Y r χ
      hΩ hspace hphase hF hi hrank hα hnonzero τ z hshift hX hV hceil hd hM hb hsrc
      hχ hc Ξ η Tresp Sresp hS hchart hchartU hSsmooth _).mono
    intro x hx
    exact hψX (subset_tsupport ψ (by rw [Function.mem_support, hplateau x hx]; exact one_ne_zero))
  · exact sampledDerivativeAmplitude_wholeSourceCorrectedWave_eq_smooth_on_plateau
      T Q F row col Φ Y r χ hΩ hspace hphase hF hi hrank hα hnonzero τ z hshift hX hV hceil hd hM hb hsrc
      hχ hc Ξ η Tresp Sresp hS hchart hchartU hSsmooth ψ hψ hψX hcell hbox hsourceBox hplateau _

end JanetCartan.CurrentMean
