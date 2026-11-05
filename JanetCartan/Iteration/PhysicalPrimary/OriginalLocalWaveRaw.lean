module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveGeometry
public import JanetCartan.Iteration.PhysicalSampling.OriginalGraphResponse
public import JanetCartan.Iteration.PhysicalNormalInverse.OriginalPrefixApplication
public import JanetCartan.Iteration.PhysicalMean.OriginalWeightBridge
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.FullSuperposition
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.SourceIntegral
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.WholeSource
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWavesTemplate

/-!
# Original source53 raw atoms and both real source quadratures

This raw-only leaf retains the actual leading `T/Q/F/row/col/Φ/Y`, scalar
span, current immersion/rank and the original χ₂ source. It proves local
smoothness on the actual original source and final-cutoff charts, admitting
BOTH real source quadratures before any whole-wave response is constructed.
The namespace and Source53 ABI are unchanged.

The elementary local response/whole-wave consequences are kept here solely
as the shared proof API. Their actual graph/source applications, finite-band
shifts and full-angular restoration are checked in `OriginalLocalWaves`.
No quantitative high bound or arbitrary analytic premise is supplied by this
qualitative leaf (`app:ch_response:cor:current-atoms`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 12000

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPrimary.OriginalLocalWaves
open ResponseSourceExtension CorrectedAtoms PrimarySourceAdmission

/-- Local complexification on the unchanged comparison chart. The actual
application below supplies BOTH inputs from `OriginalGraphResponse.smoothOn`
after proving source membership; no response regularity premise survives there
(`app:ch_response:prop:response-ambient`). -/
theorem contDiffOn_complexifyResponse {n N : ℕ}
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (h : Euclidean n → Matrix (Fin n) (Fin n) ℂ) {U : Set (Euclidean n)}
    (hre : ContDiffOn ℝ ∞ (B (tensorFieldRealPart h)) U)
    (him : ContDiffOn ℝ ∞ (B (tensorFieldImagPart h)) U) :
    ContDiffOn ℝ ∞ (complexifyResponse B h) U :=
  (euclideanComplexInclusion.contDiff.comp_contDiffOn hre).add
    ((euclideanComplexInclusion.contDiff.comp_contDiffOn him).const_smul Complex.I)

/-- The same admitted complete source is corrected without cutting the output.
This elementary subtraction is applied only to the actual B and actual source
quadratures below (`app:ch_response:cor:current-atoms`). -/
theorem contDiffOn_complexCorrectedAtom {n N : ℕ}
    (F : Euclidean n → Euclidean N) (χ : Euclidean n → ℝ)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (W : Euclidean n → EuclideanSpace ℂ (Fin N)) {U : Set (Euclidean n)}
    (hW : ContDiffOn ℝ ∞ W U)
    (hre : ContDiffOn ℝ ∞ (B (tensorFieldRealPart (complexAtomicSource F χ W))) U)
    (him : ContDiffOn ℝ ∞ (B (tensorFieldImagPart (complexAtomicSource F χ W))) U) :
    ContDiffOn ℝ ∞ (complexCorrectedAtom F χ B W) U :=
  hW.sub (contDiffOn_complexifyResponse B _ hre him)

/-- The product geometry already used by the source puts its entire physical
slice inside the original immersion chart. No new space-containment premise is
requested by the actual response application. -/
theorem slice_in_space {n : ℕ} {X U : Set (Euclidean n)}
    {V : Set (Euclidean 3 × Euclidean (n-1))}
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n-1)))}
    (hproduct : X ×ˢ V ⊆ Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    {c : Euclidean 3 × Euclidean (n-1)} (hc : c ∈ V) : X ⊆ U :=
  fun x hx ↦ hspace (x,c) (hproduct ⟨hx,hc⟩)

/-- The complete closed Fourier ceiling contains zero; the actual shifted
product inclusion therefore also supplies its physical source-chart inclusion.
This closes the domain of the original uncut response, without assuming it. -/
theorem shifted_slice_in_space {n J : ℕ} {X U : Set (Euclidean n)}
    {V : Set (Euclidean (n-1))}
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n-1)))}
    {c : Euclidean (n-1) → Euclidean 3 × Euclidean (n-1)}
    (hshift : ∀ p ∈ X ×ˢ V, (p.1,c p.2) ∈ Ω)
    (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hceil : closedBall (0 : Euclidean (n-1)) ((2 : ℝ)^J) ⊆ V) : X ⊆ U := by
  intro x hx
  exact hspace _ (hshift (x,0) ⟨hx,hceil (mem_closedBall_self (by positivity))⟩)

/-- The task71 factor is the literal original incidence/spectator mask. Its
proved square identity, not an assumed nonzero sample or division, supplies the
inner carrier geometry for the full-angular whole wave. The positive baseline
is not multiplied by this factor (`main:eq:primary`). -/
theorem inner_factor_mem_carrier (zRoot : Euclidean 3) {a : ℝ} (ha : 0 < a)
    {b : SeparatedSampling.Point → ℝ}
    (hsquare : ∀ z, (b z)^2 = Sampling.originalConicCarrierWeight zRoot ha z)
    (z : SeparatedSampling.Point) (hb : b z ≠ 0) :
    ContinuumRow.carrierSamplingEquiv.symm z ∈
      ContinuumRow.CanonicalConic.carrierSupport zRoot (r := a) := by
  apply Sampling.originalConicCarrierWeight_support zRoot ha
  rw [← hsquare z]
  exact pow_ne_zero _ hb

/-- Only the selected inner angular factor can kill the whole angular wave.
On its zero set we need no admission for the unscaled wave, and this assertion
does not act on the separate outer baseline (`app:ch_waves:thm:individual`). -/
theorem contDiffOn_full_angular_of_native_factor {n N : ℕ} {X : Set (Euclidean n)}
    {b : ℝ} {Wf W : Euclidean n → EuclideanSpace ℂ (Fin N)}
    (hf : Wf = b • W) (hW : b ≠ 0 → ContDiffOn ℝ ∞ W X) :
    ContDiffOn ℝ ∞ Wf X := by
  rw [hf]
  by_cases hb : b = 0
  · rw [hb,zero_smul]
    exact contDiffOn_const
  · exact (hW hb).const_smul b

end JanetCartan.PhysicalPrimary.OriginalLocalWaves

construct_original_local_raw_atoms
