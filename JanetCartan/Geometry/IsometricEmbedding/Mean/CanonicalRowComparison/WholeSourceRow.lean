module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalRowComparison.BandIdentification
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.SmoothIdentification

/-!
# Identify the whole-source corrected row on the original raw prefix

The actual smooth whole-source map, built with the supplied fixed response,
feeds the same uncut zero atom. The checked response-integral interchange
identifies its derivative with the bounded sampling component. Phase and
amplitude extensions agree only on the measured, retained frequency domain;
no global smoothness of the original local phase is assumed.

Consumer: `CurrentMean.completeCanonicalCorrection_toL2` and the literal row
in `app:ch_mean_pairs:eq:mean-normal-comparison`. The primitive fixed-response
Sobolev bound is the existing `both-fixed-inverse` producer input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.CanonicalRowComparison
open RawPrimary RawInputPartition CorrectedAtoms ResponseSourceExtension PrimarySourceAdmission
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ResponseSmoothParameters RetardedSobolev.Spaces CurrentMean AmplitudeBound
open CanonicalAtomRealization Sampling Sampling.RawKernel SamplingKernelBounds

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

/-- The final corrected whole-source map realizes the literal finite cross
component, with the SAME response, zero-atom background, raw measure and
original wide-to-refined prefix. The derivative representation is derived
from `smoothWholeSourceCanonicalDerivative_eq_cutIntegral`, not assumed.
The extension equalities concern only primitive phase/amplitude values on
measured points and the supplied frequency buffer. The original Fourier
normalization and real polarization factor two are explicit.
Sources: `app:ch_mean_pairs:defn:mean-canonical`,
`app:ch_waves:eq:individual-representation`, `main:eq:canonical-identity`. -/
theorem wholeSourceCrossResponse_toL2_eq_rawIntegral_component
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
    (L : ℕ) (v : RefinedInput n J) :
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
    smoothResidualToL2 n (CanonicalChange.smoothRawCrossResponse base Cper hCper
      (fun _ : Unit ↦ G) () v) =
      ((2 * Real.pi) ^ (-(n : ℝ) / 2))⁻¹ • PeriodicLocalL2.transferOutputOperator
        (realQuadratureChannel (refinedKernelPrefix D L p₀)) v := by
  dsimp only
  apply smoothRawCrossResponse_toL2_eq_rawIntegral_component Sext Vext C
    (fun p x ↦ Vext p x (ζext p)) ζext τext d hSext hVext hcross
    hζext hτext hτext₀ hd K hK hcrossSupport Bcross M hBcross hM hcrossBound hb L p₀
    _ Cper hCper _ _ hmeasurement _ v
  · intro x hx
    change ψ _ • _ = Vext p₀ (centeredTorusRepresentative x) (ζext p₀)
    rw [hplateau x hx, one_smul, hζsample]
    have hzero : (0 : Euclidean (n - 1)) ∈ V :=
      hceil (Metric.mem_closedBall_self (by positivity))
    simpa only [smul_zero, add_zero] using (hampExt x hx 0 hzero).symm
  · intro w x hx
    change (smoothWholeSourceCanonicalDerivative T Q F row col Φ Y r χ
      hΩ hspace hphase hF hi hrank hα hnonzero τ z hshift hX hV hceil hd.measurable hM hb hsrc
      hχ hc Ξ η Tresp Sresp hS hchart hchartU hSsmooth ψ hψ hψX hcell hbox
      (widePrefix n J L ((wideRefinement n J).symm w))).val x () = _
    rw [smoothWholeSourceCanonicalDerivative_eq_cutIntegral T Q F row col Φ Y r χ
      hΩ hspace hphase hF hi hrank hα hnonzero τ z hshift hX hV hceil hd.measurable hM hb hsrc
      hχ hc Ξ η Tresp Sresp hS hchart hchartU hSsmooth ψ hψ hψX hcell hbox e hB hresponse hτ,
      hplateau x hx, one_smul]
    rw [hζsample, hτsample]
    have hzero : (0 : Euclidean (n - 1)) ∈ V :=
      hceil (Metric.mem_closedBall_self (by positivity))
    have hbasePhase := hphaseExt x hx 0 hzero
    simp only [smul_zero, add_zero] at hbasePhase
    unfold rawPrimaryDemodulatedIntegral
    apply integral_congr_ae
    filter_upwards [] with ξ
    by_cases hξ : ξ ∈ V
    · simp only [rawPrimaryPhaseDifference, hphaseExt x hx ξ hξ, hbasePhase, hampExt x hx ξ hξ]
    · have hfreq : (2 : ℝ) ^ J ≤ ‖ξ‖ := by
        have hn : ξ ∉ Metric.closedBall 0 ((2 : ℝ) ^ J) := fun h ↦ hξ (hceil h)
        exact le_of_lt (by simpa using hn)
      simp only [wideDensity_eq_zero_of_ceiling_le d _ hfreq, zero_smul, smul_zero]

end JanetCartan.CanonicalRowComparison
