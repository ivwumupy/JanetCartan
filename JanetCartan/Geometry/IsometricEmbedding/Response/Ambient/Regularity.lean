module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.Completion
public import JanetCartan.Geometry.IsometricEmbedding.Normal.Christoffel

/-!
# Regularity of the strain used in normal completion

Smoothness inputs for `main:eq:normal-completion` and
`app:ch_response:eq:response-full-map` on the actual immersion domain.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
open Set

namespace JanetCartan.AmbientResponse

/-- Smoothness of the linearized metric in `main:eq:tangent-normal`, using the
Frobenius tensor norm. -/
theorem contDiffOn_linearizedMetric {n N : ℕ}
    {F Y : Euclidean n → Euclidean N} {s : Set (Euclidean n)}
    (hs : IsOpen s) (hF : ContDiffOn ℝ ∞ F s) (hY : ContDiffOn ℝ ∞ Y s) :
    ContDiffOn ℝ ∞ (linearizedMetric F Y) s := by
  let L : (Fin n → Fin n → ℝ) →ₗ[ℝ] MetricTensor n := LinearMap.id
  let C : (Fin n → Fin n → ℝ) →L[ℝ] MetricTensor n :=
    ⟨L, L.continuous_of_finiteDimensional⟩
  apply C.contDiff.comp_contDiffOn
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  exact ((contDiffOn_partialDeriv hs hF i).inner ℝ
    (contDiffOn_partialDeriv hs hY j)).add
    ((contDiffOn_partialDeriv hs hY i).inner ℝ (contDiffOn_partialDeriv hs hF j))

/-- The covariant strain in `main:eq:normal-completion` is smooth on the open
immersion domain, by the proved tangent strain identity. -/
theorem contDiffOn_symmCovariantDeriv {n N : ℕ}
    {F : Euclidean n → Euclidean N} {u : Euclidean n → Euclidean n}
    {s : Set (Euclidean n)} (hs : IsOpen s)
    (hF : ContDiffOn ℝ ∞ F s) (hu : ContDiffOn ℝ ∞ u s)
    (himm : IsImmersionOn F s) : ContDiffOn ℝ ∞ (symmCovariantDeriv F u) s := by
  apply ((contDiffOn_linearizedMetric hs hF
    (contDiffOn_tangentLift hs hF hu himm)).const_smul (1 / 2 : ℝ)).congr
  intro x hx
  rw [linearizedMetric_tangentLift hs hF hu himm hx]
  ext i j
  simp only [Pi.smul_apply, two_smul, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

end JanetCartan.AmbientResponse
