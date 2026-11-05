module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ConicChart.Basic
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.JacobianBounds

/-!
# The degree-one conic Jacobian

For `app:ch_background:eq:bg-jacobian`, differentiate covector dilation while
fixing the incidence variable. The input dilation has determinant `t^dim E`,
whereas the output dilation has determinant `t^(1 + dim E)`. Cancelling gives
degree one. Annular determinant bounds are inputs from `FullPhaseCharts`;
no conic determinant law or bound is assumed.
-/

@[expose] public noncomputable section
open Set Filter
open scoped Topology
namespace JanetCartan.ContinuumNormalReduction.ConicChart
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The differential of covector dilation for `app:ch_background:eq:bg-Psi`. -/
def radialLinearMap (t : ℝ) : (ℝ × E) →L[ℝ] (ℝ × E) :=
  (ContinuousLinearMap.id ℝ ℝ).prodMap (t • ContinuousLinearMap.id ℝ E)

/-- The linear input dilation is the covector scaling of `app:ch_background:eq:bg-Psi`. -/
@[simp] theorem radialLinearMap_apply (t : ℝ) (u : ℝ × E) :
    radialLinearMap t u = radialScale t u := rfl

variable [FiniteDimensional ℝ E]

/-- Only the covector dimensions contribute to the input dilation determinant
in `app:ch_background:eq:bg-jacobian`. -/
theorem det_radialLinearMap (t : ℝ) :
    (radialLinearMap (E := E) t).det = t ^ Module.finrank ℝ E := by
  change LinearMap.det ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).prodMap
    (t • (LinearMap.id : E →ₗ[ℝ] E))) = _
  rw [LinearMap.det_prodMap, LinearMap.det_smul]
  simp

namespace AnnularData
variable (A : AnnularData E)

/-- Literal absolute determinant in `app:ch_background:eq:bg-jacobian`. -/
def jacobian (u : ℝ × E) : ℝ := |(fderiv ℝ A.map u).det|

omit [FiniteDimensional ℝ E] in
/-- Differentiated partial homogeneity, retaining the fixed incidence parameter
in `app:ch_background:eq:bg-jacobian`. The literal phase is homogeneous at every
input, so this argument also works on the cone over a closed compact support. No openness of that support is needed. -/
theorem fderiv_comp_radialLinearMap
    (hhom : ∀ w : ℝ × E, ∀ t : ℝ, 0 < t →
      A.map (radialScale t w) = t • A.map w)
    (hd : ∀ u ∈ A.cone, DifferentiableAt ℝ A.map u)
    {u : ℝ × E} (hu : u ∈ A.cone) {t : ℝ} (ht : 0 < t) :
    (fderiv ℝ A.map (radialScale t u)).comp (radialLinearMap t) =
      t • fderiv ℝ A.map u := by
  have hleft := (hd _ (A.scale_mem u hu t ht)).hasFDerivAt.comp u
    (show HasFDerivAt (radialScale t) (radialLinearMap (E := E) t) u from
      (radialLinearMap (E := E) t).hasFDerivAt)
  have hright := (hd u hu).hasFDerivAt.const_smul t
  apply hleft.unique
  apply hright.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun w ↦ hhom w t ht)

/-- The determinant scales by exactly one power, as required by
`app:ch_background:eq:bg-jacobian`; this is derived from the forward map. -/
theorem det_fderiv_radialScale
    (hhom : ∀ w : ℝ × E, ∀ t : ℝ, 0 < t →
      A.map (radialScale t w) = t • A.map w)
    (hd : ∀ u ∈ A.cone, DifferentiableAt ℝ A.map u)
    {u : ℝ × E} (hu : u ∈ A.cone) {t : ℝ} (ht : 0 < t) :
    (fderiv ℝ A.map (radialScale t u)).det = t * (fderiv ℝ A.map u).det := by
  have he := congrArg ContinuousLinearMap.det (A.fderiv_comp_radialLinearMap hhom hd hu ht)
  change LinearMap.det ((fderiv ℝ A.map (radialScale t u)).toLinearMap.comp
    (radialLinearMap t).toLinearMap) =
    LinearMap.det (t • (fderiv ℝ A.map u).toLinearMap) at he
  rw [LinearMap.det_comp, LinearMap.det_smul] at he
  change (fderiv ℝ A.map (radialScale t u)).det * (radialLinearMap (E := E) t).det = _ at he
  rw [det_radialLinearMap, Module.finrank_prod, Module.finrank_self] at he
  apply mul_right_cancel₀ (pow_ne_zero _ ht.ne')
  calc
    _ = t ^ (1 + Module.finrank ℝ E) * (fderiv ℝ A.map u).det := he
    _ = _ := by rw [pow_add, pow_one]; ring

/-- Absolute Jacobian homogeneity in `app:ch_background:eq:bg-jacobian`. -/
theorem jacobian_radialScale
    (hhom : ∀ w : ℝ × E, ∀ t : ℝ, 0 < t →
      A.map (radialScale t w) = t • A.map w)
    (hd : ∀ u ∈ A.cone, DifferentiableAt ℝ A.map u)
    {u : ℝ × E} (hu : u ∈ A.cone) {t : ℝ} (ht : 0 < t) :
    A.jacobian (radialScale t u) = t * A.jacobian u := by
  simp only [jacobian, A.det_fderiv_radialScale hhom hd hu ht, abs_mul, abs_of_pos ht]

end AnnularData
end JanetCartan.ContinuumNormalReduction.ConicChart
