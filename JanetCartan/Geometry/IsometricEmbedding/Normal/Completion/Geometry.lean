module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.Tangent
public import JanetCartan.Geometry.IsometricEmbedding.Normal.SmoothProjection
public import JanetCartan.Geometry.IsometricEmbedding.Response.Ambient.NormalMap
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Smooth geometric coefficients for normal completion

The fixed ambient-space coefficients in `app:ch_waves:eq:ambient-normal-inverse`.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
open Set

namespace JanetCartan

/-- The tangent projection in `app:ch_waves:eq:ambient-normal-inverse` applied to
a smooth ambient field is smooth on an open immersion domain. -/
theorem contDiffOn_tangentProjection_apply {n N : ℕ}
    {F w : Euclidean n → Euclidean N} {s : Set (Euclidean n)}
    (hs : IsOpen s) (hF : ContDiffOn ℝ ∞ F s) (hw : ContDiffOn ℝ ∞ w s)
    (himm : IsImmersionOn F s) :
    ContDiffOn ℝ ∞ (fun x ↦ tangentProjection F x (w x)) s := by
  let u : Euclidean n → Euclidean n :=
    fun x ↦ WithLp.toLp 2 (fun j ↦ inner ℝ (partialDeriv F x j) (w x))
  have hu : ContDiffOn ℝ ∞ u s := by
    apply (contDiffOn_piLp 2).mpr
    intro j
    exact (contDiffOn_partialDeriv hs hF j).inner ℝ hw
  apply (contDiffOn_tangentLift hs hF hu himm).congr
  intro x hx
  exact tangentProjection_eq_sum (himm x hx) (w x)

/-- Smooth dependence of the tangent projection as an ambient operator in
`app:ch_waves:eq:ambient-normal-inverse`. -/
theorem contDiffOn_tangentProjection_of_smooth {n N : ℕ}
    {F : Euclidean n → Euclidean N} {s : Set (Euclidean n)}
    (hs : IsOpen s) (hF : ContDiffOn ℝ ∞ F s) (himm : IsImmersionOn F s) :
    ContDiffOn ℝ ∞ (tangentProjection F) s := by
  exact contDiffOn_tangentProjection hs hF (by simp) himm

/-- Smoothness of the second fundamental form in `app:ch_waves:defn:geometry`. -/
theorem contDiffOn_secondFundamentalForm_of_smooth {n N : ℕ}
    {F : Euclidean n → Euclidean N} {s : Set (Euclidean n)}
    (hs : IsOpen s) (hF : ContDiffOn ℝ ∞ F s) (himm : IsImmersionOn F s)
    (i j : Fin n) : ContDiffOn ℝ ∞ (fun x ↦ secondFundamentalForm F x i j) s := by
  exact contDiffOn_secondFundamentalForm hs hF (by simp) himm i j

namespace AmbientResponse

/-- Smoothness of the actual normal map applied to a smooth tensor field in
`main:eq:normal-completion`, using the existing Frobenius norm. -/
theorem contDiffOn_normalMap_apply {n N : ℕ}
    {F : Euclidean n → Euclidean N} {H : MetricField n} {s : Set (Euclidean n)}
    (hs : IsOpen s) (hF : ContDiffOn ℝ ∞ F s) (hH : ContDiffOn ℝ ∞ H s)
    (himm : IsImmersionOn F s) :
    ContDiffOn ℝ ∞ (fun x ↦ normalMap F x (H x)) s := by
  apply ContDiffOn.sum
  intro i _
  apply ContDiffOn.sum
  intro j _
  let L : MetricTensor n →ₗ[ℝ] ℝ :=
    (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ ℝ) j).comp
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ Fin n → ℝ) i)
  let C : MetricTensor n →L[ℝ] ℝ := ⟨L, L.continuous_of_finiteDimensional⟩
  have hc : ContDiffOn ℝ ∞ (fun x ↦ H x i j) s := C.contDiff.comp_contDiffOn hH
  exact hc.smul (contDiffOn_secondFundamentalForm_of_smooth hs hF himm i j)

end AmbientResponse
end JanetCartan
