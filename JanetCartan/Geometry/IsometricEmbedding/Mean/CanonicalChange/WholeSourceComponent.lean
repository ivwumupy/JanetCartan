module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalRowComparison.WholeSourceRow
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalChange.ComponentOperator

/-!
# The actual whole-source canonical component

Promote the checked whole-source response identity to equality of the
continuous component operators in `main:eq:old-canonical`. The original
smooth whole-source map, zero atom, detector, prefix, response and Fourier
normalization are retained. This allows taking the SAME adjoint before the
fixed continuum inverse and applying the original Fourier-data estimates.
The primitive response and extension inputs remain those of WholeSourceRow;
no component equality or canonical estimate is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.CanonicalChange
open RawPrimary RawInputPartition CorrectedAtoms ResponseSourceExtension PrimarySourceAdmission
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ResponseSmoothParameters RetardedSobolev.Spaces CurrentMean AmplitudeBound
open CanonicalAtomRealization CanonicalRowComparison Sampling Sampling.RawKernel SamplingKernelBounds

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
    (hd : Continuous d) (hM : 0 ≤ M) (hb : ∀ ξ, ‖d ξ‖ ≤ M)
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

variable {d₀ : ℕ} (e : (ℝ × (Fin d₀ → ℝ)) ≃L[ℝ] Euclidean n)
    (hB : ∀ i j : Fin n, ∀ q : ℕ, ∃ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : supportedTests (e ⁻¹' tsupport χ), ∀ x ∈ X,
        ‖iteratedFDeriv ℝ q (tensorComponentResponse e (tsupport χ) (ambientExtension F (Subtype.val Q) η Tresp Sresp (compactSmoothSources (tsupport χ)) Ξ hS) i j u) x‖ ≤
          C * ‖ofTest s volume u.val‖)
    (hresponse : ContDiffOn ℝ ∞
      (fun w ↦ fullPrimaryResponse T Q F row col Φ Y χ (ambientExtension F (Subtype.val Q) η Tresp Sresp (compactSmoothSources (tsupport χ)) Ξ hS) τ r w.2 w.1) Ω)
    (hτ : τ ≠ 0)

include hB

/-- The constructed component of the SAME whole-source smooth derivative
is the actual bounded raw-integral component (`main:eq:old-canonical`,
`app:ch_mean_pairs:defn:mean-canonical`). This applies the whole-source
producer's proved identity before taking adjoints. The raw L² continuity
witness is arbitrary and does not change the operator or normalization. -/
theorem smoothRawCrossOperator_wholeSource_eq_rawIntegral_component
    {Aparam : Type*} [TopologicalSpace Aparam] [FirstCountableTopology Aparam]
    [LocallyCompactSpace Aparam] (p₀ : Aparam)
    (Sext : Aparam → Euclidean n → Euclidean (n - 1) → ℝ)
    (Vext : Aparam → Euclidean n → Euclidean (n - 1) → Matrix (Fin N) (Fin n) ℂ)
    (ζext : Aparam → Euclidean (n - 1)) (τext : Aparam → ℝ)
    (hζext : Continuous ζext) (hτext : Continuous τext) (hτext₀ : ∀ p, τext p ≠ 0)
    (hζsample : ζext p₀ = T.reference.spatialPatch z) (hτsample : τext p₀ = τ)
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (Cper : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (hCper : IsSmoothPeriodic Cper)
    (hmeasurement : ∀ x, Cper x = C (centeredTorusRepresentative x))
    (hplateau : ∀ x, Cper x ≠ 0 → ψ (centeredTorusRepresentative x) = 1)
    (hSext : Continuous (fun q : (Aparam × Euclidean n) × Euclidean (n - 1) ↦
      Sext q.1.1 q.1.2 q.2))
    (hVext : ∀ p x, Continuous (Vext p x))
    (hphaseExt : ∀ x, Cper x ≠ 0 → ∀ ξ ∈ V,
      Sext p₀ (centeredTorusRepresentative x) (T.reference.spatialPatch z + τ • ξ) =
        phase T Q (centeredTorusRepresentative x) (T.reference.spatialPatch z + τ • ξ))
    (hampExt : ∀ x, Cper x ≠ 0 → ∀ ξ ∈ V,
      Vext p₀ (centeredTorusRepresentative x) (T.reference.spatialPatch z + τ • ξ) =
        fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ
          (ambientExtension F (Subtype.val Q) η Tresp Sresp (compactSmoothSources (tsupport χ)) Ξ hS)
          r τ (centeredTorusRepresentative x, (z, T.reference.spatialPatch z + τ • ξ)))
    (hcross : Continuous (fun q : (Aparam × Euclidean n) × Euclidean (n - 1) ↦
      complexCrossMeasurement (C q.1.2) (Vext q.1.1 q.1.2 (ζext q.1.1))
        (Vext q.1.1 q.1.2 q.2)))
    (K : Set (Euclidean n)) (hK : IsCompact K)
    (hcrossSupport : ∀ p x ξ, x ∉ K →
      complexCrossMeasurement (C x) (Vext p x (ζext p)) (Vext p x ξ) = 0)
    (Bcross : ℝ) (hBcross : 0 ≤ Bcross)
    (hcrossBound : ∀ p x ξ,
      ‖complexCrossMeasurement (C x) (Vext p x (ζext p)) (Vext p x ξ)‖ ≤ Bcross)
    (L : ℕ) :
    let hcarrier : ∀ y ∈ X, (y, (z, T.reference.spatialPatch z)) ∈ Ω := by
      intro y hy
      have hzero : (0 : Euclidean (n - 1)) ∈ V :=
        hceil (Metric.mem_closedBall_self (by positivity))
      simpa using hshift (y, 0) ⟨hy, hzero⟩
    let base := smoothCorrectedZeroAtom T Q F row col Φ Y χ
      (ambientExtension F (Subtype.val Q) η Tresp Sresp (compactSmoothSources (tsupport χ)) Ξ hS)
      τ r z (T.reference.spatialPatch z)
      hΩ hspace hphase hF hi hrank hα hnonzero hresponse hcarrier hτ hX ψ hψ hψX hcell hbox
    let G := (smoothWholeSourceCanonicalDerivative T Q F row col Φ Y r χ
      hΩ hspace hphase hF hi hrank hα hnonzero τ z hshift hX hV hceil hd.measurable hM hb hsrc
      hχ hc Ξ η Tresp Sresp hS hchart hchartU hSsmooth ψ hψ hψX hcell hbox).comp
        ((((widePrefix n J L).restrictScalars ℝ).toLinearMap).comp
          ((wideRefinement n J).symm.toLinearMap.restrictScalars ℝ))
    let D := bandKernelData (J := J) Sext
      (fun p x ξ ↦ complexCrossMeasurement (C x) (Vext p x (ζext p)) (Vext p x ξ))
      ζext τext d hSext hcross hζext hτext hτext₀
      hd K hK hcrossSupport Bcross M hBcross hM hcrossBound hb
    ∀ (CG : Unit → ℝ)
      (hG : ∀ i v, periodicL2Norm (fun x ↦ (G v).val x ()) ≤ CG i * ‖v‖),
    smoothRawCrossOperator base Cper hCper (fun _ : Unit ↦ G) CG hG () =
      ((2 * Real.pi) ^ (-(n : ℝ) / 2))⁻¹ • PeriodicLocalL2.transferOutputOperator
        (realQuadratureChannel (refinedKernelPrefix D L p₀)) := by
  dsimp only
  intro CG hG
  apply ContinuousLinearMap.ext
  intro v
  rw [smoothRawCrossOperator_apply]
  exact wholeSourceCrossResponse_toL2_eq_rawIntegral_component
    T Q F row col Φ Y r χ hΩ hspace hphase hF hi hrank hα hnonzero τ z
    hshift hX hV hceil hd hM hb hsrc hχ hc Ξ η Tresp Sresp hS hchart hchartU hSsmooth
    ψ hψ hψX hcell hbox e hB hresponse hτ p₀ Sext Vext ζext τext hζext hτext hτext₀
    hζsample hτsample C Cper hCper hmeasurement hplateau hSext hVext hphaseExt hampExt
    hcross K hK hcrossSupport Bcross hBcross hcrossBound L v

end JanetCartan.CanonicalChange
