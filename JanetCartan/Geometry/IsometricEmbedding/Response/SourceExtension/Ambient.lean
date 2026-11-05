module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SourceExtension.Extension
public import JanetCartan.Geometry.IsometricEmbedding.Response.Ambient

/-!
# Extending the actual ambient response

This specializes the algebraic extension to the checked canonical normal
completion in `app:ch_response:prop:response-ambient`. All source-domain
agreement premises are discharged by the definition of `ambientResponseLinear`.
The reduced solver, its smooth source domain, and its quantitative estimates
remain the responsibility of their construction, as in `main:thm:step`.
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

/-- The fixed whole-source real response for the corrected atoms and complete
signed-product consumers. The extension and output cutoff have no sign,
accuracy, norm-order, or sampling parameters
(`app:ch_response:prop:response-ambient`, `app:ch_pairs:prop:pairs-lag-sum`). -/
def ambientExtension : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N) :=
  extendResponse χ (AmbientResponse.ambientResponseLinear F Q η T S D chart hS)

/-- On each actual source, the constructed operator is exactly the cutoff of
the actual canonical ambient response (`app:ch_response:eq:response-full-map`). -/
theorem ambientExtension_eq_cutoff (h : D) :
    ambientExtension F Q η T S D χ hS h =
      fun x ↦ χ.toFun x • AmbientResponse.ambientResponse F Q η T S h x :=
  extendResponse_eq_cutoff χ _ h _ rfl

/-- The constructed operator agrees with the actual response on a neighborhood
of every core point (`app:ch_response:prop:response-ambient`). -/
theorem ambientExtension_eventuallyEq (h : D) {x : Euclidean n} (hx : x ∈ core) :
    ambientExtension F Q η T S D χ hS h =ᶠ[𝓝 x]
      AmbientResponse.ambientResponse F Q η T S h :=
  extendResponse_eventuallyEq χ _ h _ rfl hx

/-- Exact core values for every source in the actual domain
(`app:ch_response:eq:response-full-map`). -/
theorem ambientExtension_eqOn (h : D) :
    EqOn (ambientExtension F Q η T S D χ hS h)
      (AmbientResponse.ambientResponse F Q η T S h) core :=
  fun _ hx ↦ (ambientExtension_eventuallyEq F Q η T S D χ hS h hx).self_of_nhds

/-- Every derivative order uses the same operator, with exact agreement on the
core (`app:ch_response:prop:response-graded`). -/
theorem iteratedFDeriv_ambientExtension_eq (h : D) (k : ℕ)
    {x : Euclidean n} (hx : x ∈ core) :
    iteratedFDeriv ℝ k (ambientExtension F Q η T S D χ hS h) x =
      iteratedFDeriv ℝ k (AmbientResponse.ambientResponse F Q η T S h) x :=
  iteratedFDeriv_extendResponse_eq χ _ h _ rfl k hx

/-- The derivative used by the actual metric has exact core agreement
(`app:ch_response:eq:response-full-identity`). -/
theorem fderiv_ambientExtension_eq (h : D) {x : Euclidean n} (hx : x ∈ core) :
    fderiv ℝ (ambientExtension F Q η T S D χ hS h) x =
      fderiv ℝ (AmbientResponse.ambientResponse F Q η T S h) x :=
  (ambientExtension_eventuallyEq F Q η T S D χ hS h hx).fderiv_eq

/-- All coordinate derivatives agree with those of the actual ambient response
(`app:ch_response:prop:response-graded`). -/
theorem partialDeriv_ambientExtension_eq (h : D) (i : Fin n)
    {x : Euclidean n} (hx : x ∈ core) :
    partialDeriv (ambientExtension F Q η T S D χ hS h) x i =
      partialDeriv (AmbientResponse.ambientResponse F Q η T S h) x i := by
  simp only [partialDeriv, fderiv_ambientExtension_eq F Q η T S D χ hS h hx]

/-- The full strain agrees locally, including all of its derivatives; no cutoff
commutator remains on the core (`app:ch_response:eq:response-full-identity`). -/
theorem linearizedMetric_ambientExtension_eventuallyEq (h : D)
    {x : Euclidean n} (hx : x ∈ core) :
    linearizedMetric F (ambientExtension F Q η T S D χ hS h) =ᶠ[𝓝 x]
      linearizedMetric F (AmbientResponse.ambientResponse F Q η T S h) := by
  filter_upwards [(ambientExtension_eventuallyEq F Q η T S D χ hS h hx).fderiv (𝕜 := ℝ)]
    with y hy
  ext i j
  simp only [linearizedMetric, partialDeriv, hy]

/-- Exact strain agreement for the real consumers of the single extension
(`app:ch_response:eq:response-full-identity`). -/
theorem linearizedMetric_ambientExtension_eq (h : D)
    {x : Euclidean n} (hx : x ∈ core) :
    linearizedMetric F (ambientExtension F Q η T S D χ hS h) x =
      linearizedMetric F (AmbientResponse.ambientResponse F Q η T S h) x :=
  (linearizedMetric_ambientExtension_eventuallyEq F Q η T S D χ hS h hx).self_of_nhds

/-- All strain derivatives retain exact core agreement for the same operator
(`app:ch_response:prop:response-graded`). -/
theorem iteratedFDeriv_strain_ambientExtension_eq (h : D) (k : ℕ)
    {x : Euclidean n} (hx : x ∈ core) :
    iteratedFDeriv ℝ k (linearizedMetric F (ambientExtension F Q η T S D χ hS h)) x =
      iteratedFDeriv ℝ k
        (linearizedMetric F (AmbientResponse.ambientResponse F Q η T S h)) x :=
  ((linearizedMetric_ambientExtension_eventuallyEq F Q η T S D χ hS h hx).iteratedFDeriv ℝ k).self_of_nhds

/-- Smoothness is obtained from the completed normal reconstruction, the actual
smooth source, and the reduced solver's chart regularity. No new analytic
response premise is introduced (`app:ch_response:prop:response-ambient`). -/
theorem contDiff_ambientExtension (h : D) (ho : IsOpen chart)
    (hF : ContDiffOn ℝ ∞ F chart) (hh : ContDiffOn ℝ ∞ (h : MetricField n) chart)
    (hi : IsImmersionOn F chart) (hr : HasFullNormalRankOn F chart)
    (hu : ContDiffOn ℝ ∞ (S (AmbientResponse.correctedStressSource Q η T h)) chart) :
    ContDiff ℝ ∞ (ambientExtension F Q η T S D χ hS h) :=
  contDiff_extendResponse χ _ h ho _ rfl
    (AmbientResponse.contDiffOn_ambientResponse Q η T S ho hF hh hi hr hu)

/-- The single ambient extension has fixed compact physical support for every
input; this asserts no analytic estimate outside `D`
(`app:ch_pairs:prop:pairs-lag-sum`). -/
theorem hasCompactSupport_ambientExtension (h : MetricField n) :
    HasCompactSupport (ambientExtension F Q η T S D χ hS h) :=
  hasCompactSupport_extendResponse χ _ h

/-- The exact signed-product assembly for the actual ambient extension. This
is the map passed to `ProductSum.complete_signed_product_bounds`
(`app:ch_pairs:prop:pairs-lag-sum`). -/
theorem ambientExtension_weightedSignedSum {α : Type*} [Fintype α] [DecidableEq α]
    (b : ℝ) (μ : α → ℝ) (plus minus : α → α → MetricField n) :
    ambientExtension F Q η T S D χ hS (ProductSum.weightedSignedSum b μ plus minus) =
      ProductSum.weightedSignedSum b μ
        (fun j k ↦ ambientExtension F Q η T S D χ hS (plus j k))
        (fun j k ↦ ambientExtension F Q η T S D χ hS (minus j k)) :=
  ProductSum.map_weightedSignedSum _ _ _ _ _

end JanetCartan.ResponseSourceExtension
