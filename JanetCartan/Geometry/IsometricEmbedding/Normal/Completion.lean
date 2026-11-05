module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.Completion.Geometry
public import JanetCartan.Geometry.IsometricEmbedding.Normal.Completion.Operator

/-!
# Smoothness of canonical normal completion

The canonical normal completion in `main:eq:normal-completion` is smooth on
an open full-normal-rank immersion domain. We identify it with the fixed
ambient inverse formula in `app:ch_waves:eq:ambient-normal-inverse` and apply
smooth inversion. No choice of a moving normal frame is required.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
open Set

namespace JanetCartan.AmbientResponse

/-- Smooth dependence of `BB* + P_tan` in
`app:ch_waves:eq:ambient-normal-inverse` on the open immersion domain. -/
theorem contDiffOn_ambientNormalOperator {n N : ℕ}
    {F : Euclidean n → Euclidean N} {s : Set (Euclidean n)}
    (hs : IsOpen s) (hF : ContDiffOn ℝ ∞ F s) (himm : IsImmersionOn F s) :
    ContDiffOn ℝ ∞ (ambientNormalOperator F) s := by
  apply contDiffOn_clm_apply.mpr
  intro w
  simp only [ambientNormalOperator_apply, normalMap, normalPairing]
  apply ContDiffOn.add _ (contDiffOn_tangentProjection_apply hs hF contDiffOn_const himm)
  apply ContDiffOn.sum
  intro i _
  apply ContDiffOn.sum
  intro j _
  have hII := contDiffOn_secondFundamentalForm_of_smooth hs hF himm i j
  exact (contDiffOn_const.inner ℝ hII).smul hII

/-- Smoothness of the actual ambient inverse in
`app:ch_waves:eq:ambient-normal-inverse`; invertibility follows from full normal rank. -/
theorem contDiffOn_inverse_ambientNormalOperator {n N : ℕ}
    {F : Euclidean n → Euclidean N} {s : Set (Euclidean n)}
    (hs : IsOpen s) (hF : ContDiffOn ℝ ∞ F s)
    (himm : IsImmersionOn F s) (hrank : HasFullNormalRankOn F s) :
    ContDiffOn ℝ ∞ (fun x ↦ Ring.inverse (ambientNormalOperator F x)) s := by
  intro x hx
  have hu := ambientNormalOperator_isUnit (hrank x hx)
  have hi : ContDiffAt ℝ ∞ Ring.inverse (ambientNormalOperator F x) := by
    simpa only [IsUnit.unit_spec] using contDiffAt_ringInverse ℝ hu.unit
  exact hi.comp_contDiffWithinAt x (contDiffOn_ambientNormalOperator hs hF himm x hx)

/-- The actual canonical normal completion from `main:eq:normal-completion`
is smooth for every smooth tensor field on an open full-normal-rank immersion
domain. This uses the proven ambient inverse formula
`app:ch_waves:eq:ambient-normal-inverse` and requires no symmetry of the tensor. -/
theorem contDiffOn_canonicalNormalCompletion {n N : ℕ}
    {F : Euclidean n → Euclidean N} {H : MetricField n} {s : Set (Euclidean n)}
    (hs : IsOpen s) (hF : ContDiffOn ℝ ∞ F s) (hH : ContDiffOn ℝ ∞ H s)
    (himm : IsImmersionOn F s) (hrank : HasFullNormalRankOn F s) :
    ContDiffOn ℝ ∞ (fun x ↦ canonicalNormalCompletion F x (H x)) s := by
  apply ((contDiffOn_inverse_ambientNormalOperator hs hF himm hrank).clm_apply
    (contDiffOn_normalMap_apply hs hF hH himm)).congr
  intro x hx
  exact canonicalNormalCompletion_eq_ambient_inverse (hrank x hx) (H x)

end JanetCartan.AmbientResponse
