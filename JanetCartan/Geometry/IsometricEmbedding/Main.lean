module

public import JanetCartan.Geometry.IsometricEmbedding.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Local
public import JanetCartan.Geometry.IsometricEmbedding.MetricPreservation
public import JanetCartan.Geometry.IsometricEmbedding.CoordinateTransfer.LocalExistence
public import JanetCartan.Iteration.RevisedUniform.OriginalUniformCorrection

/-!
# Smooth local isometric embeddings in the Janet–Cartan dimension

Theorem main:thm:main of paper.tex and paper-v2.tex (Theorem 1.1).

The metric is given explicitly, so no distance-space compatibility assumption is
needed. The metric equation says that the differential preserves inner products.
The local version allows the metric to be defined only on a prescribed neighborhood.

The original-data uniform physical correction supplies one smooth isometric limit.
The Euclidean coordinate reduction restores the given metric and restricts once
for a smooth embedding, with the same map and neighborhood at every order.
-/

@[expose] public noncomputable section

open scoped ContDiff Manifold
open Bundle TopologicalSpace

namespace JanetCartan

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Theorem 1.1, main:thm:main: every smooth Riemannian metric in dimension at least
five has a smooth local isometric embedding in dimension n(n + 1)/2.

The single map and neighborhood are smooth at every order. Applying this theorem to
an open submanifold gives the case of a metric defined only near the base point.
-/
theorem exists_local_isometric_embedding [FiniteDimensional ℝ E]
    (hn : 5 ≤ Module.finrank ℝ E)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    (p : M) :
    ∃ U : Opens M, p ∈ U ∧
      ∃ f : U → Euclidean (embeddingDimension (Module.finrank ℝ E)),
        Manifold.IsSmoothEmbedding 𝓘(ℝ, E)
          𝓘(ℝ, Euclidean (embeddingDimension (Module.finrank ℝ E))) ∞ f ∧
        PreservesRiemannianMetric g.toRiemannianMetric U f := by
  refine exists_local_isometric_embedding_of_euclidean_local_existence ?_ g p
  intro g0 V hV h0 hg0
  exact RevisedUniform.OriginalUniformCorrection.exists_local_metric
    (Module.finrank ℝ E) hn g0 V hV h0 hg0

/-- Theorem 1.1 with the domain of the given local metric made explicit.

The resulting open submanifold is contained in W, and hence gives an open
neighborhood in the original manifold.
-/
theorem exists_local_isometric_embedding_on [FiniteDimensional ℝ E]
    (hn : 5 ≤ Module.finrank ℝ E) (W : Opens M)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (fun x : W ↦ TangentSpace 𝓘(ℝ, E) x))
    (p : W) :
    ∃ U : Opens W, p ∈ U ∧
      ∃ f : U → Euclidean (embeddingDimension (Module.finrank ℝ E)),
        Manifold.IsSmoothEmbedding 𝓘(ℝ, E)
          𝓘(ℝ, Euclidean (embeddingDimension (Module.finrank ℝ E))) ∞ f ∧
        PreservesRiemannianMetric g.toRiemannianMetric U f :=
  exists_local_isometric_embedding hn g p

end JanetCartan
