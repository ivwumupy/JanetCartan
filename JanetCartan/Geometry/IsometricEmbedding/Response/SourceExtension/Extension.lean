module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SourceExtension.Cutoff
public import JanetCartan.Geometry.IsometricEmbedding.Waves.ProductSum.Algebra
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# A fixed algebraic extension of a chart response

`app:ch_response:prop:response-ambient` and `app:ch_pairs:prop:pairs-lag-sum`:
choose one algebraic extension from the actual source submodule, then apply one
fixed output cutoff. The operator is chosen before signs, samples, or observation
orders. No smoothness or analytic estimate outside the source submodule is claimed.
-/

@[expose] public noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace JanetCartan.ResponseSourceExtension

variable {n N : ℕ} {D : Submodule ℝ (MetricField n)}
variable {core chart : Set (Euclidean n)}

/-- The single algebraic choice from `LinearMap.exists_extend`, retaining the
chart-valued range of `ambientResponseLinear`
(`app:ch_response:prop:response-ambient`). -/
def extendChartResponse (B : D →ₗ[ℝ] (chart → Euclidean N)) :
    MetricField n →ₗ[ℝ] (chart → Euclidean N) :=
  B.exists_extend.choose

/-- The algebraic extension agrees exactly on the actual source submodule
(`app:ch_response:prop:response-ambient`). -/
@[simp] theorem extendChartResponse_apply (B : D →ₗ[ℝ] (chart → Euclidean N))
    (h : D) : extendChartResponse B h = B h :=
  DFunLike.congr_fun B.exists_extend.choose_spec h

/-- The whole-function-space response consumed by
`CorrectedAtoms.realCorrectedAtomicFamily` and
`ProductSum.complete_signed_product_bounds`. It uses one algebraic source
extension and one physical output cutoff (`main:thm:step`). -/
def extendResponse (χ : OutputCutoff core chart)
    (B : D →ₗ[ℝ] (chart → Euclidean N)) :
    MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N) :=
  χ.zeroExtend.comp (extendChartResponse B)

/-- On the actual source domain the result is the literal cutoff zero extension
of the original chart response (`app:ch_response:prop:response-ambient`). -/
@[simp] theorem extendResponse_apply (χ : OutputCutoff core chart)
    (B : D →ₗ[ℝ] (chart → Euclidean N)) (h : D) :
    extendResponse χ B h = χ.zeroExtend (B h) := by
  simp [extendResponse]

/-- Exact global agreement with the cutoff of any actual representative.
This premise identifies the supplied chart map; it is not a response estimate
(`app:ch_pairs:prop:pairs-lag-sum`). -/
theorem extendResponse_eq_cutoff (χ : OutputCutoff core chart)
    (B : D →ₗ[ℝ] (chart → Euclidean N)) (h : D)
    (v : Euclidean n → Euclidean N) (hv : B h = fun x : chart ↦ v x) :
    extendResponse χ B h = fun x ↦ χ.toFun x • v x := by
  rw [extendResponse_apply, hv, χ.zeroExtend_restrict]

/-- Equality on a neighborhood of every core point for an actual source.
All local derivatives therefore agree (`app:ch_response:prop:response-ambient`). -/
theorem extendResponse_eventuallyEq (χ : OutputCutoff core chart)
    (B : D →ₗ[ℝ] (chart → Euclidean N)) (h : D)
    (v : Euclidean n → Euclidean N) (hv : B h = fun x : chart ↦ v x)
    {x : Euclidean n} (hx : x ∈ core) :
    extendResponse χ B h =ᶠ[𝓝 x] v := by
  rw [extendResponse_apply, hv]
  exact χ.zeroExtend_eventuallyEq v hx

/-- Every derivative order of the same fixed operator agrees with the actual
response on the core (`app:ch_response:prop:response-graded`). -/
theorem iteratedFDeriv_extendResponse_eq (χ : OutputCutoff core chart)
    (B : D →ₗ[ℝ] (chart → Euclidean N)) (h : D)
    (v : Euclidean n → Euclidean N) (hv : B h = fun x : chart ↦ v x)
    (k : ℕ) {x : Euclidean n} (hx : x ∈ core) :
    iteratedFDeriv ℝ k (extendResponse χ B h) x = iteratedFDeriv ℝ k v x :=
  ((extendResponse_eventuallyEq χ B h v hv hx).iteratedFDeriv ℝ k).self_of_nhds

/-- Actual smooth chart outputs become globally smooth functions, as needed by
`CorrectedAtoms.realCorrectedAtomicFamily` (`app:ch_response:cor:current-atoms`). -/
theorem contDiff_extendResponse (χ : OutputCutoff core chart)
    (B : D →ₗ[ℝ] (chart → Euclidean N)) (h : D) (ho : IsOpen chart)
    (v : Euclidean n → Euclidean N) (hv : B h = fun x : chart ↦ v x)
    (hs : ContDiffOn ℝ ∞ v chart) : ContDiff ℝ ∞ (extendResponse χ B h) := by
  rw [extendResponse_apply, hv]
  exact χ.contDiff_zeroExtend_restrict ho hs

/-- Every output of the one algebraic extension has the same compact physical
support (`app:ch_pairs:prop:pairs-lag-sum`). No regularity is asserted here. -/
theorem hasCompactSupport_extendResponse (χ : OutputCutoff core chart)
    (B : D →ₗ[ℝ] (chart → Euclidean N)) (h : MetricField n) :
    HasCompactSupport (extendResponse χ B h) :=
  χ.hasCompactSupport_zeroExtend (extendChartResponse B h)

/-- Additivity holds on the entire source function space
(`app:ch_response:prop:response-ambient`). -/
theorem extendResponse_add (χ : OutputCutoff core chart)
    (B : D →ₗ[ℝ] (chart → Euclidean N)) (h k : MetricField n) :
    extendResponse χ B (h + k) = extendResponse χ B h + extendResponse χ B k :=
  map_add _ _ _

/-- Real homogeneity holds for the same fixed extension
(`app:ch_response:prop:response-ambient`). -/
theorem extendResponse_smul (χ : OutputCutoff core chart)
    (B : D →ₗ[ℝ] (chart → Euclidean N)) (a : ℝ) (h : MetricField n) :
    extendResponse χ B (a • h) = a • extendResponse χ B h := map_smul _ _ _

/-- Finite real synthesis uses one operator, independently of the index set and
coefficients (`main:thm:step`). -/
theorem extendResponse_sum_smul {ι : Type*} (χ : OutputCutoff core chart)
    (B : D →ₗ[ℝ] (chart → Euclidean N)) (t : Finset ι) (a : ι → ℝ)
    (h : ι → MetricField n) :
    extendResponse χ B (∑ i ∈ t, a i • h i) =
      ∑ i ∈ t, a i • extendResponse χ B (h i) := by
  simp only [map_sum, map_smul]

/-- The exact complete signed-product assembly required by
`ProductSum.complete_signed_product_bounds`, with the plus diagonal retained
and only the minus diagonal removed (`app:ch_pairs:prop:pairs-lag-sum`). -/
theorem extendResponse_weightedSignedSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (χ : OutputCutoff core chart) (B : D →ₗ[ℝ] (chart → Euclidean N))
    (b : ℝ) (μ : ι → ℝ) (plus minus : ι → ι → MetricField n) :
    extendResponse χ B (ProductSum.weightedSignedSum b μ plus minus) =
      ProductSum.weightedSignedSum b μ
        (fun j k ↦ extendResponse χ B (plus j k))
        (fun j k ↦ extendResponse χ B (minus j k)) :=
  ProductSum.map_weightedSignedSum _ _ _ _ _

/-- Finite complete signed sums of actual sources are still actual sources;
this closes the domain obligation for their single solve
(`app:ch_pairs:prop:pairs-lag-sum`). -/
theorem weightedSignedSum_mem {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ℝ) (μ : ι → ℝ) (plus minus : ι → ι → MetricField n)
    (hp : ∀ j k, plus j k ∈ D) (hm : ∀ j k, j ≠ k → minus j k ∈ D) :
    ProductSum.weightedSignedSum b μ plus minus ∈ D := by
  apply D.smul_mem
  apply D.add_mem
  · exact D.sum_mem fun j _ ↦ D.sum_mem fun k _ ↦ D.smul_mem _ (hp j k)
  · apply D.sum_mem
    intro j _
    apply D.sum_mem
    intro k hk
    exact D.smul_mem _ (hm j k (Finset.ne_of_mem_erase hk).symm)

end JanetCartan.ResponseSourceExtension
