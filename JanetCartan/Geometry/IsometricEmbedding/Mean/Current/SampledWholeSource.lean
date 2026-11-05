module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalTailRealization.WholeSourceSample
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.WholeSourceCanonicalConstruction
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.WholeSourceSampledAmplitude
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.ZeroAtomSampledAmplitude

/-!
# Continuity and physical realization of the literal sampled whole-source family

Use the original `SampleIndex`, sample nodes, frequencies, chartwise raw data
and response factors from `CanonicalTailRealization.WholeSourceSample`.
The full wide map constructs one continuity witness for every grouped prefix;
the existing sampled base and derivative are realized by their physical
corrected waves on the supplied common source plateau. Nothing is resampled
or identified with an independently chosen family.

Consumers: the same-prefix prepared tail recurrence and the sampled mean in
`main:lem:mean-recurrence` / `app:ch_pairs:lem:pairs-ledger`. Sharp uniform raw
profiles, the common event and actual initialized geometry remain producer
applications; the continuity witnesses here are qualitative.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set MeasureTheory Finset
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.CurrentMean
open RawPrimary RawInputPartition CorrectedAtoms ResponseSourceExtension PrimarySourceAdmission
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ResponseSmoothParameters RetardedSobolev.Spaces AmplitudeBound UniformStep SmoothPeriodicFamily
open CanonicalAtomRealization CanonicalRowComparison CanonicalTailRealization CanonicalChange CanonicalDataBounds
open Sampling Sampling.RawKernel SamplingKernelBounds SeparatedSampling Sampling.Realization

variable {Λ : Type*} {n N J p : ℕ}
    (B : ℝ) (weights : Λ → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (shifts : Λ → Lattice → Point)


variable {P : Λ → Patch n} {U : Λ → Set (Euclidean n)} {hU : ∀ a, IsOpen (U a)}
    (T : ∀ a, PatchQuantitativeFamily (P a) (U a) (hU a))
    (Q : ∀ a, {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q (U a) ∧
      cNorm (Metric.closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < (T a).family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Λ → Fin n)
    (Φ Y : Λ → ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (r : Λ → Euclidean (n - 1) × Euclidean 3 → ℝ)
    (χ : Euclidean n → ℝ)
    (τext : Λ → ((Fin 3 → Fin (p + 1)) × Point) → ℝ)
    (hτext₀ : ∀ a q, τext a q ≠ 0)


variable {Ω : Λ → Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : ∀ a, IsOpen (Ω a)) (hspace : ∀ a, ∀ v ∈ Ω a, v.1 ∈ U a)
    (hphase : ∀ a, ∀ v ∈ Ω a, (v.1, v.2.2) ∈ phaseDomain (T a))
    (hF : ∀ a, ContDiffOn ℝ ∞ F (U a)) (hi : ∀ a, IsImmersionOn F (U a))
    (hrank : ∀ a, HasFullNormalRankOn F (U a))
    (hα : ∀ a, ContDiffOn ℝ ∞ (scalarAmplitude (T a) (Q a) F (row a) (col a) (Φ a) (Y a) (r a)) (Ω a))
    (hnonzero : ∀ a, ∀ v ∈ Ω a,
      nullvector (T a) (Q a) (col a) v ≠ 0 ∧ conullvector (T a) (Q a) (row a) v ≠ 0)
    {X : Λ → Set (Euclidean n)} {V : Λ → Set (Euclidean (n - 1))}
    (hshift : ∀ i : (SampleIndex p B weights w h shifts), ∀ q ∈ X i.1 ×ˢ V i.1,
      (q.1, (WithLp.toLp 2 (node h (shifts i.1) i.2), (T i.1).reference.spatialPatch (WithLp.toLp 2 (node h
        (shifts i.1) i.2)) + τext i.1 (color p i.2.val.1, node h (shifts i.1) i.2) • q.2)) ∈ Ω i.1)
    (hX : ∀ a, IsOpen (X a)) (hV : ∀ a, IsOpen (V a))
    (hceil : ∀ a, Metric.closedBall 0 ((2 : ℝ) ^ J) ⊆ V a)
    (d : Λ → Euclidean (n - 1) → ℂ) (M : Λ → ℝ)
    (hd : ∀ a, Continuous (d a)) (hM : ∀ a, 0 ≤ M a) (hb : ∀ a ξ, ‖d a ξ‖ ≤ M a)
    (hsrc : ∀ a, tsupport χ ⊆ X a)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    {core chart : Set (Euclidean n)} (Ξ : OutputCutoff core chart)
    (η : Euclidean n → ℝ)
    (Tresp : (Euclidean n → Fin n → ℝ) →ₗ[ℝ] (Euclidean n → Fin n → ℝ))
    (Sresp : (Euclidean n → Fin n → ℝ) →ₗ[ℝ] (Euclidean n → Euclidean n))
    (hS : ∀ a, ∀ f : compactSmoothSources (tsupport χ), ∀ x ∈ chart,
      DifferentiableAt ℝ (Sresp (AmbientResponse.correctedStressSource (Q a).1 η Tresp f)) x)
    (hchart : IsOpen chart) (hchartU : ∀ a, chart ⊆ U a)
    (hSsmooth : ∀ a, ∀ f : compactSmoothSources (tsupport χ),
      ContDiffOn ℝ ∞ (Sresp (AmbientResponse.correctedStressSource (Q a).1 η Tresp f)) chart)
    (ψ : Euclidean n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψX : ∀ a, tsupport ψ ⊆ X a)
    {b : ℝ} (hcell : b < 1 / 2) (hbox : ∀ x ∈ tsupport ψ, ∀ i, |x i| ≤ b)


variable (hresponse : ∀ i : (SampleIndex p B weights w h shifts), ContDiffOn ℝ ∞
      (fun v ↦ fullPrimaryResponse (T i.1) (Q i.1) F (row i.1) (col i.1) (Φ i.1) (Y i.1) χ
        (ambientExtension F (Q i.1).1 η Tresp Sresp (compactSmoothSources (tsupport χ)) Ξ (hS i.1)) (τext i.1
          (color p i.2.val.1, node h (shifts i.1) i.2)) (r i.1) v.2 v.1) (Ω i.1))

/-- The full wide map at the SAME sample node and frequency. The original
prefixes are supplied by `wholeSourceSampledDerivative`; no kernel, phase,
mask or response is changed (`main:eq:old-canonical`). -/
def wholeSourceSampledWideDerivative (i : (SampleIndex p B weights w h shifts)) :
    WideInput n J →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ) :=
  smoothWholeSourceCanonicalDerivative (n := n) (N := N) (J := J)
    (X := X i.1) (V := V i.1) (Ω := Ω i.1) (T i.1) (Q i.1) F (row i.1) (col i.1)
    (Φ i.1) (Y i.1) (r i.1) χ (hΩ i.1) (hspace i.1) (hphase i.1)
    (hF i.1) (hi i.1) (hrank i.1) (hα i.1) (hnonzero i.1) (τext i.1 (color p i.2.val.1, node h (shifts i.1) i.2))
      (WithLp.toLp 2 (node h (shifts i.1) i.2))
    (hshift i) (hX i.1) (hV i.1) (hceil i.1) (hd i.1).measurable (hM i.1) (hb i.1)
    (hsrc i.1) hχ hc Ξ η Tresp Sresp (hS i.1) hchart (hchartU i.1) (hSsmooth i.1)
    ψ hψ (hψX i.1) hcell hbox

/-- The literal sampled derivative is exactly the original wide-prefix map,
including both refined pieces (`main:eq:old-canonical`). This identifies the
raw maps consumed by the prepared tail and Fourier estimates. -/
theorem wholeSourceSampledDerivative_eq_widePrefix (L : ℕ) :
    wholeSourceSampledDerivative B weights w h shifts T Q F row col Φ Y r χ τext hΩ hspace hphase hF hi
      hrank hα hnonzero hshift hX hV hceil d M hd hM hb hsrc hχ hc Ξ η Tresp Sresp hS
      hchart hchartU hSsmooth ψ hψ hψX hcell hbox L =
      fun i ↦ canonicalWidePrefixRawMap (wholeSourceSampledWideDerivative B weights w h shifts T Q F row col Φ Y r χ τext hΩ hspace hphase hF hi
      hrank hα hnonzero hshift hX hV hceil d M hd hM hb hsrc hχ hc Ξ η Tresp Sresp hS
      hchart hchartU hSsmooth ψ hψ hψX hcell hbox i) L := rfl

variable {d₀ : ℕ} (e : (ℝ × (Fin d₀ → ℝ)) ≃L[ℝ] Euclidean n)
    (hB : ∀ a, ∀ i j : Fin n, ∀ q : ℕ, ∃ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : supportedTests (e ⁻¹' tsupport χ), ∀ x ∈ X a,
        ‖iteratedFDeriv ℝ q (tensorComponentResponse e (tsupport χ) (ambientExtension F (Q a).1 η Tresp Sresp
          (compactSmoothSources (tsupport χ)) Ξ (hS a)) i j u) x‖ ≤
          C * ‖ofTest s volume u.val‖)

include hB hresponse hτext₀

/-- Construct continuity bounds for the actual sampled raw maps at ALL
original prefixes before choosing the inverse, residuals or cutoff schedule
(`app:ch_mean_pairs:defn:mean-canonical`). This discharges the raw continuity
input of `exists_admissible_history_wholeSource_prepared_rawTail_bound`;
the sharp uniform profiles are still separate producer bounds. -/
theorem exists_wholeSourceSampledDerivative_l2_bounds :
    let Gwide := wholeSourceSampledWideDerivative B weights w h shifts T Q F row col Φ Y r χ τext hΩ hspace hphase hF hi
      hrank hα hnonzero hshift hX hV hceil d M hd hM hb hsrc hχ hc Ξ η Tresp Sresp hS
      hchart hchartU hSsmooth ψ hψ hψX hcell hbox
    let G := wholeSourceSampledDerivative B weights w h shifts T Q F row col Φ Y r χ τext hΩ hspace hphase hF hi
      hrank hα hnonzero hshift hX hV hceil d M hd hM hb hsrc hχ hc Ξ η Tresp Sresp hS
      hchart hchartU hSsmooth ψ hψ hψX hcell hbox
    ∃ CG : SampleIndex p B weights w h shifts → ℝ, (∀ i, 0 ≤ CG i) ∧
      (∀ i v, periodicL2Norm (fun x ↦ (Gwide i v).val x ()) ≤ CG i * ‖v‖) ∧
      ∀ L i v, periodicL2Norm (fun x ↦ (G L i v).val x ()) ≤ CG i * ‖v‖ := by
  have hbound (i : SampleIndex p B weights w h shifts) :=
    exists_smoothWholeSourceCanonicalDerivative_l2_bound
      (T i.1) (Q i.1) F (row i.1) (col i.1) (Φ i.1) (Y i.1) (r i.1) χ
      (hΩ i.1) (hspace i.1) (hphase i.1) (hF i.1) (hi i.1) (hrank i.1)
      (hα i.1) (hnonzero i.1)
      (τext i.1 (color p i.2.val.1, node h (shifts i.1) i.2))
      (WithLp.toLp 2 (node h (shifts i.1) i.2))
      (hshift i) (hX i.1) (hV i.1) (hceil i.1) (hd i.1).measurable (hM i.1) (hb i.1)
      (hsrc i.1) hχ hc Ξ η Tresp Sresp (hS i.1) hchart (hchartU i.1) (hSsmooth i.1)
      ψ hψ (hψX i.1) hcell hbox e (hB i.1) (hresponse i)
      (hτext₀ i.1 (color p i.2.val.1, node h (shifts i.1) i.2))
  choose CG hCG hfull hprefix using hbound
  exact ⟨CG, hCG, hfull, fun L i v ↦ hprefix i L v⟩

end JanetCartan.CurrentMean
