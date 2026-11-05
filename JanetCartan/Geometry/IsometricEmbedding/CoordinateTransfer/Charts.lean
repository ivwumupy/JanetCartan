module

public import JanetCartan.Geometry.IsometricEmbedding.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Centered Euclidean charts

The coordinate reduction for Theorem `main:thm:main` of `paper.tex` starts by
identifying the finite-dimensional model space with standard Euclidean space
and translating the chart so that the base point has coordinates zero.

This supplies the chart input to
`exists_local_isometric_embedding_of_euclidean_local_existence` in
`CoordinateTransfer/LocalExistence.lean`. The construction uses only the smooth
manifold structure and finite dimensionality; it needs no metric data.
-/

public noncomputable section

open scoped ContDiff Manifold

namespace JanetCartan

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ E]

/-- The coordinate reduction in `main:thm:main`: every point of a smooth
finite-dimensional manifold admits a chart into standard Euclidean space
centered at zero, smooth in both directions on its source and target.

The continuous linear equivalence changes the model space, and a translation
centers the chart. This discharges the chart-existence input to
`exists_local_isometric_embedding_of_euclidean_local_existence`.
-/
theorem exists_centered_euclidean_chart (p : M) :
    ∃ e : OpenPartialHomeomorph M (Euclidean (Module.finrank ℝ E)),
      p ∈ e.source ∧ e p = 0 ∧
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, Euclidean (Module.finrank ℝ E)) ∞ e e.source ∧
      ContMDiffOn 𝓘(ℝ, Euclidean (Module.finrank ℝ E)) 𝓘(ℝ, E) ∞ e.symm e.target := by
  let L : E ≃L[ℝ] Euclidean (Module.finrank ℝ E) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let c := chartAt E p
  let a := L (c p)
  let h : E ≃ₜ Euclidean (Module.finrank ℝ E) :=
    L.toHomeomorph.trans (Homeomorph.addRight (-a))
  let e := c.transHomeomorph h
  have hh : ContDiff ℝ ∞ h := L.contDiff.add contDiff_const
  have hh' : ContDiff ℝ ∞ h.symm :=
    L.symm.contDiff.comp (contDiff_id.add contDiff_const)
  refine ⟨e, mem_chart_source E p, ?_, ?_, ?_⟩
  · change L (c p) + -L (c p) = 0
    exact add_neg_cancel _
  · exact hh.contMDiff.comp_contMDiffOn
      (contMDiffOn_chart (I := 𝓘(ℝ, E)) (x := p))
  · exact (contMDiffOn_chart_symm (I := 𝓘(ℝ, E)) (x := p)).comp
      hh'.contMDiff.contMDiffOn (fun _ hy ↦ hy)

end JanetCartan
