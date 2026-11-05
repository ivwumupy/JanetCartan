module

public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import Mathlib.Geometry.Manifold.SmoothEmbedding

/-!
# Preservation of a Riemannian metric by a local map

The differential metric equation used in Theorem `main:thm:main` of `paper.tex`.
This shared definition is independent of the local existence theorem and its
coordinate constructions.
-/

@[expose] public noncomputable section

open scoped ContDiff Manifold
open Bundle TopologicalSpace

namespace JanetCartan

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- A map on an open submanifold realizes the restriction of a Riemannian metric.

The differential of the inclusion transports tangent vectors to the ambient manifold,
where the given metric is defined.
-/
def PreservesRiemannianMetric {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F]
    (g : RiemannianMetric (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    (U : Opens M) (f : U → F) : Prop :=
  ∀ (x : U) (v w : TangentSpace 𝓘(ℝ, E) x),
    inner ℝ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x v)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x w) =
    g.inner x.val
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : U → M) x v)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : U → M) x w)

/-- Metric preservation forces the differential to be injective at every point. -/
theorem PreservesRiemannianMetric.mfderiv_injective
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {g : RiemannianMetric (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)}
    {U : Opens M} {f : U → F}
    (hf : PreservesRiemannianMetric g U f) (x : U) :
    Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x) := by
  have hi := (Manifold.IsImmersion.of_opens (I := 𝓘(ℝ, E)) (n := ∞) U).mfderiv_injective
    (by simp) x
  intro v w hvw
  have hz : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x (v - w) = 0 := by
    rw [map_sub, hvw, sub_self]
  have hmetric := hf x (v - w) (v - w)
  rw [hz, inner_zero_left] at hmetric
  have hzero : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : U → M) x (v - w) = 0 := by
    by_contra hne
    exact (g.pos x.val _ hne).ne' hmetric.symm
  apply hi
  simpa only [map_sub, sub_eq_zero] using hzero

end JanetCartan
