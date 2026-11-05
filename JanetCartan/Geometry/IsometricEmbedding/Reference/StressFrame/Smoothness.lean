module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.Geometry

/-!
# Smoothness of the actual projected stress frame

Smoothness in `app:ch_seed:setup:seed-current`, proved from the actual ambient
inverse formula without a moving normal frame.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
open JanetCartan.AmbientResponse

namespace JanetCartan.ProjectedStressFrame

variable {n N : ℕ} {F : Euclidean n → Euclidean N} {s : Set (Euclidean n)}

/-- Smoothness of the actual adjoint pairing in
`app:ch_seed:setup:seed-current`, in the fixed Frobenius tensor space. -/
theorem contDiffOn_normalPairing {w : Euclidean n → Euclidean N}
    (hs : IsOpen s) (hF : ContDiffOn ℝ ∞ F s) (hw : ContDiffOn ℝ ∞ w s)
    (himm : IsImmersionOn F s) : ContDiffOn ℝ ∞ (normalPairing F w) s := by
  let L : (Fin n → Fin n → ℝ) →ₗ[ℝ] MetricTensor n := LinearMap.id
  let C : (Fin n → Fin n → ℝ) →L[ℝ] MetricTensor n :=
    ⟨L, L.continuous_of_finiteDimensional⟩
  apply C.contDiff.comp_contDiffOn
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  exact hw.inner ℝ (contDiffOn_secondFundamentalForm hs hF (by simp) himm i j)

/-- Smoothness of the explicit projection applied to any smooth tensor field,
as used in Step 1 of `app:ch_seed:prop:seed-actual-menu`. -/
theorem contDiffOn_stressProjection_apply {H : MetricField n}
    (hs : IsOpen s) (hF : ContDiffOn ℝ ∞ F s) (hH : ContDiffOn ℝ ∞ H s)
    (himm : IsImmersionOn F s) (hrank : HasFullNormalRankOn F s) :
    ContDiffOn ℝ ∞ (fun x ↦ stressProjection F x (H x)) s := by
  apply (hH.sub (contDiffOn_normalPairing hs hF
    (contDiffOn_canonicalNormalCompletion hs hF hH himm hrank) himm)).congr
  intro x hx
  exact stressProjection_eq_sub_completion (hrank x hx) (H x)

/-- The actual projected cube stresses are smooth, as required in
`app:ch_seed:setup:seed-current` and Step 1 of `app:ch_seed:prop:seed-actual-menu`. -/
theorem contDiffOn_projectedStress
    (hs : IsOpen s) (hF : ContDiffOn ℝ ∞ F s)
    (himm : IsImmersionOn F s) (hrank : HasFullNormalRankOn F s) (i : Fin n) :
    ContDiffOn ℝ ∞ (fun x ↦ projectedStress F x i) s :=
  contDiffOn_stressProjection_apply hs hF contDiffOn_const himm hrank

end JanetCartan.ProjectedStressFrame
