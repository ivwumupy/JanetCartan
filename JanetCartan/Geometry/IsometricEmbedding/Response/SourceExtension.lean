module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SourceExtension.Complex

/-!
# One fixed whole-source ambient response

The adapter from `AmbientResponse.ambientResponseLinear` to the linear maps
consumed by `CorrectedAtoms.realCorrectedAtomicFamily` and
`ProductSum.complete_signed_product_bounds` (`main:thm:step`).

* `nonempty_outputCutoff` constructs one compact smooth physical cutoff from a
  fixed compact core inside the open validity chart.
* `ambientExtension` uses exactly one `LinearMap.exists_extend` choice on the
  source domain, followed by that cutoff and chart zero extension.
* `ambientExtension_eq_cutoff`, `ambientExtension_eventuallyEq`, and the derivative
  and strain agreement theorems identify its values on every actual source.
* `contDiff_ambientExtension` uses the checked canonical normal completion to
  prove global smoothness for actual smooth sources and reduced solutions.
* `complexifyResponse` uses the same real map on both source quadratures. Real
  and complex finite signed assembly follows for this single operator.

There is no new response solver or analytic bound here. The actual solver,
its source domain, and all quantitative estimates are still construction inputs.
No smoothness or estimate is asserted for arbitrary sources outside that domain.
-/

@[expose] public noncomputable section

open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.ResponseSourceExtension

variable {n N : ℕ} {ι : Type*}
variable (F : Euclidean n → Euclidean N) (Q : Euclidean n → ι → MetricTensor n)
variable (η : Euclidean n → ℝ)
variable (T : (Euclidean n → ι → ℝ) →ₗ[ℝ] (Euclidean n → ι → ℝ))
variable (S : (Euclidean n → ι → ℝ) →ₗ[ℝ] (Euclidean n → Euclidean n))
variable (D : Submodule ℝ (MetricField n)) {core chart : Set (Euclidean n)}
variable (χ : OutputCutoff core chart)
variable (hS : ∀ h : D, ∀ x ∈ chart, DifferentiableAt ℝ
  (S (AmbientResponse.correctedStressSource Q η T h)) x)

/-- For actual complex sources, both quadratures agree locally with the same
real ambient response. This discharges the agreement premises in the generic
complexification lemmas (`app:ch_response:prop:response-ambient`). -/
theorem complexify_ambientExtension_eventuallyEq
    (h : Euclidean n → Matrix (Fin n) (Fin n) ℂ)
    (hr : tensorFieldRealPart h ∈ D) (hi : tensorFieldImagPart h ∈ D)
    {x : Euclidean n} (hx : x ∈ core) :
    complexifyResponse (ambientExtension F Q η T S D χ hS) h =ᶠ[𝓝 x]
      fun y ↦ euclideanComplexInclusion
        (AmbientResponse.ambientResponse F Q η T S (tensorFieldRealPart h) y) +
        Complex.I • euclideanComplexInclusion
          (AmbientResponse.ambientResponse F Q η T S (tensorFieldImagPart h) y) :=
  complexifyResponse_eventuallyEq _ h _ _
    (ambientExtension_eventuallyEq F Q η T S D χ hS ⟨_, hr⟩ hx)
    (ambientExtension_eventuallyEq F Q η T S D χ hS ⟨_, hi⟩ hx)

/-- All derivative orders of the complex response agree with the actual two
quadratures on the core, without changing the operator
(`app:ch_response:prop:response-graded`). -/
theorem iteratedFDeriv_complexify_ambientExtension_eq
    (h : Euclidean n → Matrix (Fin n) (Fin n) ℂ)
    (hr : tensorFieldRealPart h ∈ D) (hi : tensorFieldImagPart h ∈ D)
    (k : ℕ) {x : Euclidean n} (hx : x ∈ core) :
    iteratedFDeriv ℝ k (complexifyResponse (ambientExtension F Q η T S D χ hS) h) x =
      iteratedFDeriv ℝ k (fun y ↦ euclideanComplexInclusion
        (AmbientResponse.ambientResponse F Q η T S (tensorFieldRealPart h) y) +
        Complex.I • euclideanComplexInclusion
          (AmbientResponse.ambientResponse F Q η T S (tensorFieldImagPart h) y)) x :=
  ((complexify_ambientExtension_eventuallyEq F Q η T S D χ hS h hr hi hx).iteratedFDeriv ℝ k).self_of_nhds

/-- Exact local agreement of the full complex strain, preserving every term in
`app:ch_response:eq:response-full-identity`. -/
theorem complexStrain_ambientExtension_eventuallyEq
    (h : Euclidean n → Matrix (Fin n) (Fin n) ℂ)
    (hr : tensorFieldRealPart h ∈ D) (hi : tensorFieldImagPart h ∈ D)
    {x : Euclidean n} (hx : x ∈ core) :
    WKB.complexLinearizedMetric F
      (complexifyResponse (ambientExtension F Q η T S D χ hS) h) =ᶠ[𝓝 x]
      WKB.complexLinearizedMetric F (fun y ↦ euclideanComplexInclusion
        (AmbientResponse.ambientResponse F Q η T S (tensorFieldRealPart h) y) +
        Complex.I • euclideanComplexInclusion
          (AmbientResponse.ambientResponse F Q η T S (tensorFieldImagPart h) y)) :=
  complexLinearizedMetric_eventuallyEq F
    (complexify_ambientExtension_eventuallyEq F Q η T S D χ hS h hr hi hx)

/-- All complex strain derivatives agree for the one fixed extension
(`app:ch_response:prop:response-graded`). -/
theorem iteratedFDeriv_complexStrain_ambientExtension_eq
    (h : Euclidean n → Matrix (Fin n) (Fin n) ℂ)
    (hr : tensorFieldRealPart h ∈ D) (hi : tensorFieldImagPart h ∈ D)
    (k : ℕ) {x : Euclidean n} (hx : x ∈ core) :
    iteratedFDeriv ℝ k (WKB.complexLinearizedMetric F
      (complexifyResponse (ambientExtension F Q η T S D χ hS) h)) x =
      iteratedFDeriv ℝ k (WKB.complexLinearizedMetric F
        (fun y ↦ euclideanComplexInclusion
          (AmbientResponse.ambientResponse F Q η T S (tensorFieldRealPart h) y) +
          Complex.I • euclideanComplexInclusion
            (AmbientResponse.ambientResponse F Q η T S (tensorFieldImagPart h) y))) x :=
  ((complexStrain_ambientExtension_eventuallyEq F Q η T S D χ hS h hr hi hx).iteratedFDeriv ℝ k).self_of_nhds

/-- Actual smooth sources and solved quadratures produce a globally smooth
complex response. The only analytic inputs are the reduced solver's actual
chart regularity, already used by the real ambient construction
(`app:ch_response:prop:response-ambient`). -/
theorem contDiff_complexify_ambientExtension
    (h : Euclidean n → Matrix (Fin n) (Fin n) ℂ)
    (hr : tensorFieldRealPart h ∈ D) (hi : tensorFieldImagPart h ∈ D)
    (ho : IsOpen chart) (hF : ContDiffOn ℝ ∞ F chart)
    (hhr : ContDiffOn ℝ ∞ (tensorFieldRealPart h) chart)
    (hhi : ContDiffOn ℝ ∞ (tensorFieldImagPart h) chart)
    (himm : IsImmersionOn F chart) (hrank : HasFullNormalRankOn F chart)
    (hur : ContDiffOn ℝ ∞
      (S (AmbientResponse.correctedStressSource Q η T (tensorFieldRealPart h))) chart)
    (hui : ContDiffOn ℝ ∞
      (S (AmbientResponse.correctedStressSource Q η T (tensorFieldImagPart h))) chart) :
    ContDiff ℝ ∞ (complexifyResponse (ambientExtension F Q η T S D χ hS) h) :=
  contDiff_complexifyResponse _ h
    (contDiff_ambientExtension F Q η T S D χ hS ⟨_, hr⟩ ho hF hhr himm hrank hur)
    (contDiff_ambientExtension F Q η T S D χ hS ⟨_, hi⟩ ho hF hhi himm hrank hui)

/-- The same physical cutoff gives compact support for the complexified map
(`app:ch_pairs:prop:pairs-lag-sum`). -/
theorem hasCompactSupport_complexify_ambientExtension
    (h : Euclidean n → Matrix (Fin n) (Fin n) ℂ) :
    HasCompactSupport (complexifyResponse (ambientExtension F Q η T S D χ hS) h) :=
  hasCompactSupport_complexifyResponse _ h
    (hasCompactSupport_ambientExtension F Q η T S D χ hS _)
    (hasCompactSupport_ambientExtension F Q η T S D χ hS _)

end JanetCartan.ResponseSourceExtension
