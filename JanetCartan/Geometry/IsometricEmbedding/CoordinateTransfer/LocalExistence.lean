module

public import JanetCartan.Geometry.IsometricEmbedding.CoordinateTransfer.Charts
public import JanetCartan.Geometry.IsometricEmbedding.CoordinateTransfer.Metric

/-!
# Reduction to Euclidean local metric realization

For Theorem `main:thm:main` of `paper.tex`, construct centered Euclidean
coordinates and the smooth positive definite inverse-coordinate metric, apply
Euclidean local existence, and transfer the resulting solution back to a smaller
manifold neighborhood. The transfer supplies a smooth embedding as in the final
paragraph of `main:sec:convergence`.

This is the conditional coordinate reduction consumed by
`exists_local_isometric_embedding` in `Main.lean`. Its sole existence premise is
local smooth realization of an arbitrary smooth positive definite Euclidean
metric. Proving that premise is a separate analytic obligation; no dimension
lower bound is needed for the coordinate reduction itself.
-/

public noncomputable section

open scoped ContDiff Manifold Matrix.Norms.Frobenius
open Bundle TopologicalSpace

namespace JanetCartan

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ E]

/-- The coordinate reduction for `main:thm:main`: Euclidean local metric
realization in the Janet–Cartan dimension implies the exact smooth embedding
and metric preservation conclusion of `exists_local_isometric_embedding`.

The Euclidean input requires smoothness only on the resulting neighborhood and
does not assume that its solution is an embedding. Centered coordinates and
regularity and positivity of the coordinate metric are constructed in the proof.
The analytic existence premise remains to be discharged for the unconditional
theorem, where the dimension assumption belongs.
-/
theorem exists_local_isometric_embedding_of_euclidean_local_existence
    (hlocal : ∀ (g0 : MetricField (Module.finrank ℝ E))
      (V : Set (Euclidean (Module.finrank ℝ E))),
      IsOpen V → (0 : Euclidean (Module.finrank ℝ E)) ∈ V →
      IsRiemannianMetricOn g0 V →
      ∃ s : Set (Euclidean (Module.finrank ℝ E)),
        IsOpen s ∧ (0 : Euclidean (Module.finrank ℝ E)) ∈ s ∧ s ⊆ V ∧
        ∃ F : Euclidean (Module.finrank ℝ E) →
            Euclidean (embeddingDimension (Module.finrank ℝ E)),
          ContDiffOn ℝ ∞ F s ∧ IsIsometricOn g0 F s)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    (p : M) :
    ∃ U : Opens M, p ∈ U ∧
      ∃ f : U → Euclidean (embeddingDimension (Module.finrank ℝ E)),
        Manifold.IsSmoothEmbedding 𝓘(ℝ, E)
          𝓘(ℝ, Euclidean (embeddingDimension (Module.finrank ℝ E))) ∞ f ∧
        PreservesRiemannianMetric g.toRiemannianMetric U f := by
  obtain ⟨e, hp, he0, he, he'⟩ := exists_centered_euclidean_chart (E := E) p
  have h0 : (0 : Euclidean (Module.finrank ℝ E)) ∈ e.target := by
    simpa only [he0] using e.map_source hp
  obtain ⟨s, hs, h0s, hst, F, hF, hmetric⟩ :=
    hlocal (inverseCoordinateMetric g.toRiemannianMetric e.symm) e.target
      e.open_target h0 (isRiemannianMetricOn_inverseCoordinateMetric g e he he')
  have hps : e p ∈ s := he0.symm ▸ h0s
  obtain ⟨U, hpU, _, hemb, hpres⟩ :=
    exists_local_isometric_embedding_of_coordinate_solution
      g.toRiemannianMetric e hp he he' hs hst hps hF hmetric
  exact ⟨U, hpU, (fun x : U ↦ F (e x.val)), hemb, hpres⟩

end JanetCartan
