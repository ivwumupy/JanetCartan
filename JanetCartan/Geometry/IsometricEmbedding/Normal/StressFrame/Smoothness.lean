module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.StressFrame.Projection
public import JanetCartan.Geometry.IsometricEmbedding.Normal.SmoothInverse

/-!
# Smooth projected cube stresses

The qualitative smoothness assertion for `Q_i(G) = Π_(ker B_G) Q_i⁰`
in `app:ch_waves:thm:leading` and `app:ch_background:defn:bg-geometry`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius ContDiff Topology

namespace JanetCartan.StressFrame

variable {n : ℕ} {F X : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- `app:ch_background:defn:bg-geometry`: the specified orthogonal projections
are smooth on the open full-rank operator locus. -/
theorem contDiffOn_projectedCubeStress {k : ℕ∞ω} (i : Fin n) :
    ContDiffOn ℝ k (fun B : SymmetricTensor n →L[ℝ] F ↦
      projectedCubeStress B.toLinearMap i) {B | Function.Surjective B} := by
  exact (NormalInverse.contDiffOn_starProjection_ker_family contDiffOn_id
    (fun _ h ↦ h)).clm_apply contDiffOn_const

/-- `app:ch_waves:thm:leading`: smooth dependence of the actual projected
stress, for any smooth full-rank operator family, including joint parameters. -/
theorem contDiffOn_projectedCubeStress_family {k : ℕ∞ω}
    {B : X → SymmetricTensor n →L[ℝ] F} {s : Set X}
    (hB : ContDiffOn ℝ k B s) (hsurj : ∀ x ∈ s, Function.Surjective (B x))
    (i : Fin n) :
    ContDiffOn ℝ k (fun x ↦ projectedCubeStress (B x).toLinearMap i) s :=
  (contDiffOn_projectedCubeStress i).comp hB hsurj

/-- `app:ch_background:defn:bg-geometry`: continuity at a full-rank operator,
needed to obtain the frame neighborhood from operator closeness. -/
theorem continuousAt_projectedCubeStress (B : SymmetricTensor n →L[ℝ] F)
    (hB : Function.Surjective B) (i : Fin n) :
    ContinuousAt (fun C : SymmetricTensor n →L[ℝ] F ↦
      projectedCubeStress C.toLinearMap i) B :=
  ((contDiffOn_projectedCubeStress (k := ∞) i).contDiffAt
    (NormalInverse.isOpen_surjective.mem_nhds hB)).continuousAt

end JanetCartan.StressFrame
