module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SourceExtension.Ambient
public import JanetCartan.Analysis.Operator.RealQuadratures.RealPart
public import JanetCartan.Geometry.IsometricEmbedding.Waves.WKB.Strain

/-!
# Both quadratures of the same fixed response

The complex-linear extension in `app:ch_response:prop:response-ambient` is
constructed from the one real operator. Finite real and complex synthesis use
that same operator; no second algebraic extension or analytic estimate is chosen.
The range uses the shared complex Euclidean space and tensor conventions.
-/

@[expose] public noncomputable section

open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.ResponseSourceExtension

variable {n N : ℕ}

/-- Real source quadrature for `app:ch_response:prop:response-ambient`. -/
def tensorFieldRealPart : (Euclidean n → Matrix (Fin n) (Fin n) ℂ) →ₗ[ℝ] MetricField n where
  toFun h x i j := (h x i j).re
  map_add' := by intros; ext; simp; rfl
  map_smul' := by intros; ext; simp; rfl

/-- Imaginary source quadrature, retained by the same real operator
(`app:ch_response:prop:response-ambient`). -/
def tensorFieldImagPart : (Euclidean n → Matrix (Fin n) (Fin n) ℂ) →ₗ[ℝ] MetricField n where
  toFun h x i j := (h x i j).im
  map_add' := by intros; ext; simp; rfl
  map_smul' := by intros; ext; simp; rfl

private theorem tensorFieldRealPart_complex_smul (a : ℂ)
    (h : Euclidean n → Matrix (Fin n) (Fin n) ℂ) :
    tensorFieldRealPart (a • h) =
      a.re • tensorFieldRealPart h - a.im • tensorFieldImagPart h := by
  ext x i j
  exact Complex.mul_re _ _

private theorem tensorFieldImagPart_complex_smul (a : ℂ)
    (h : Euclidean n → Matrix (Fin n) (Fin n) ℂ) :
    tensorFieldImagPart (a • h) =
      a.re • tensorFieldImagPart h + a.im • tensorFieldRealPart h := by
  ext x i j
  exact Complex.mul_im _ _

/-- Complexification of one real whole-source response, with both quadratures
and the existing complex Euclidean output (`app:ch_response:prop:response-ambient`). -/
def complexifyResponse (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N)) :
    (Euclidean n → Matrix (Fin n) (Fin n) ℂ) →ₗ[ℂ]
      (Euclidean n → EuclideanSpace ℂ (Fin N)) where
  toFun h x := euclideanComplexInclusion (B (tensorFieldRealPart h) x) +
    Complex.I • euclideanComplexInclusion (B (tensorFieldImagPart h) x)
  map_add' h k := by
    simp only [map_add, Pi.add_apply, smul_add]
    ext x i
    simp
    ring
  map_smul' a h := by
    simp only [tensorFieldRealPart_complex_smul, tensorFieldImagPart_complex_smul,
      map_sub, map_add, map_smul, Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
    ext x i
    apply Complex.ext <;> simp <;> ring

/-- The real quadrature is exactly the original real response
(`app:ch_response:prop:response-ambient`). -/
@[simp] theorem complexifyResponse_re
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (h : Euclidean n → Matrix (Fin n) (Fin n) ℂ) (x : Euclidean n) (i : Fin N) :
    (complexifyResponse B h x i).re = B (tensorFieldRealPart h) x i := by
  simp [complexifyResponse]

/-- The imaginary quadrature uses the identical real response
(`app:ch_response:prop:response-ambient`). -/
@[simp] theorem complexifyResponse_im
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (h : Euclidean n → Matrix (Fin n) (Fin n) ℂ) (x : Euclidean n) (i : Fin N) :
    (complexifyResponse B h x i).im = B (tensorFieldImagPart h) x i := by
  simp [complexifyResponse]

/-- Complex coefficients and arbitrary finite synthesis require no new response
choice (`app:ch_pairs:prop:pairs-lag-sum`). -/
theorem complexifyResponse_sum_smul {α : Type*}
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (t : Finset α) (a : α → ℂ)
    (h : α → Euclidean n → Matrix (Fin n) (Fin n) ℂ) :
    complexifyResponse B (∑ i ∈ t, a i • h i) =
      ∑ i ∈ t, a i • complexifyResponse B (h i) := by
  simp only [map_sum, map_smul]

/-- The literal complete signed sum also assembles in the complex space,
retaining the plus diagonal and removing precisely the minus diagonal
(`app:ch_pairs:prop:pairs-lag-sum`). -/
theorem complexifyResponse_weightedSignedSum {α : Type*} [Fintype α] [DecidableEq α]
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N)) (b : ℝ) (μ : α → ℝ)
    (plus minus : α → α → Euclidean n → Matrix (Fin n) (Fin n) ℂ) :
    complexifyResponse B (ProductSum.weightedSignedSum b μ plus minus) =
      ProductSum.weightedSignedSum b μ
        (fun j k ↦ complexifyResponse B (plus j k))
        (fun j k ↦ complexifyResponse B (minus j k)) :=
  ProductSum.map_weightedSignedSum ((complexifyResponse B).restrictScalars ℝ) _ _ _ _

/-- Smoothness on both actual quadratures gives smoothness of their literal
complexification (`app:ch_response:prop:response-ambient`). -/
theorem contDiff_complexifyResponse
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (h : Euclidean n → Matrix (Fin n) (Fin n) ℂ)
    (hr : ContDiff ℝ ∞ (B (tensorFieldRealPart h)))
    (hi : ContDiff ℝ ∞ (B (tensorFieldImagPart h))) :
    ContDiff ℝ ∞ (complexifyResponse B h) :=
  (euclideanComplexInclusion.contDiff.comp hr).add
    ((euclideanComplexInclusion.contDiff.comp hi).const_smul Complex.I)

/-- Agreement of both actual chart responses gives local agreement of the
complexified extension, including its full derivative jet
(`app:ch_response:prop:response-ambient`). -/
theorem complexifyResponse_eventuallyEq
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (h : Euclidean n → Matrix (Fin n) (Fin n) ℂ)
    (R I : Euclidean n → Euclidean N) {x : Euclidean n}
    (hr : B (tensorFieldRealPart h) =ᶠ[𝓝 x] R)
    (hi : B (tensorFieldImagPart h) =ᶠ[𝓝 x] I) :
    complexifyResponse B h =ᶠ[𝓝 x]
      fun y ↦ euclideanComplexInclusion (R y) +
        Complex.I • euclideanComplexInclusion (I y) := by
  filter_upwards [hr, hi] with y hyr hyi
  simp only [complexifyResponse, LinearMap.coe_mk, AddHom.coe_mk, hyr, hyi]

/-- All complex response derivatives agree under local quadrature agreement
(`app:ch_response:prop:response-graded`). -/
theorem iteratedFDeriv_complexifyResponse_eq
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (h : Euclidean n → Matrix (Fin n) (Fin n) ℂ)
    (R I : Euclidean n → Euclidean N) {x : Euclidean n}
    (hr : B (tensorFieldRealPart h) =ᶠ[𝓝 x] R)
    (hi : B (tensorFieldImagPart h) =ᶠ[𝓝 x] I) (k : ℕ) :
    iteratedFDeriv ℝ k (complexifyResponse B h) x =
      iteratedFDeriv ℝ k (fun y ↦ euclideanComplexInclusion (R y) +
        Complex.I • euclideanComplexInclusion (I y)) x :=
  ((complexifyResponse_eventuallyEq B h R I hr hi).iteratedFDeriv ℝ k).self_of_nhds

/-- Compact support is retained on both quadratures by the same physical
cutoff (`app:ch_pairs:prop:pairs-lag-sum`). -/
theorem hasCompactSupport_complexifyResponse
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (h : Euclidean n → Matrix (Fin n) (Fin n) ℂ)
    (hr : HasCompactSupport (B (tensorFieldRealPart h)))
    (hi : HasCompactSupport (B (tensorFieldImagPart h))) :
    HasCompactSupport (complexifyResponse B h) :=
  (hr.comp_left euclideanComplexInclusion.map_zero).add
    ((hi.comp_left euclideanComplexInclusion.map_zero).smul_left
      (f := fun _ ↦ Complex.I))

/-- Local equality of complex fields preserves the entire complex strain on a
neighborhood, hence every strain derivative. This uses the shared coordinate
metric (`app:ch_response:eq:response-full-identity`). -/
theorem complexLinearizedMetric_eventuallyEq (F : Euclidean n → Euclidean N)
    {Y Z : Euclidean n → EuclideanSpace ℂ (Fin N)} {x : Euclidean n}
    (h : Y =ᶠ[𝓝 x] Z) :
    WKB.complexLinearizedMetric F Y =ᶠ[𝓝 x] WKB.complexLinearizedMetric F Z := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
  ext i j
  simp only [WKB.complexLinearizedMetric, partialDeriv, hy]

end JanetCartan.ResponseSourceExtension
