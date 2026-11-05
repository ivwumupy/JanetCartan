module

public import JanetCartan.Geometry.IsometricEmbedding.Basic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Normed.Module.ContinuousInverse
public import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# Restricting an immersion to an embedding

The topological restriction used at the end of Section 9 of paper.tex. Composing
with a continuous linear left inverse of the differential reduces the assertion
to the inverse function theorem.
-/

public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius
open Set Topology TopologicalSpace

namespace JanetCartan

/-- A C¹ map with injective differential into a finite-dimensional space is a
topological embedding on some open neighborhood of the point. -/
theorem exists_isEmbedding_restrict_of_injective_fderiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E → F} {s : Set E} {p : E}
    (hs : IsOpen s) (hp : p ∈ s) (hf : ContDiffOn ℝ 1 f s)
    (hdf : Function.Injective (fderiv ℝ f p)) :
    ∃ U : Opens E, p ∈ U ∧ (U : Set E) ⊆ s ∧
      IsEmbedding (fun x : U ↦ f x.val) := by
  obtain ⟨L, hL⟩ :=
    ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hdf
  have hfp : ContDiffAt ℝ 1 f p := hf.contDiffAt (hs.mem_nhds hp)
  have hlin : L.comp (fderiv ℝ f p) = ContinuousLinearMap.id ℝ E := by
    ext v
    exact hL v
  have hcomp : HasFDerivAt (L ∘ f)
      (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) p := by
    change HasFDerivAt (L ∘ f) (ContinuousLinearMap.id ℝ E) p
    rw [← hlin]
    exact L.hasFDerivAt.comp p (hfp.differentiableAt (by decide)).hasFDerivAt
  have hreg : ContDiffAt ℝ 1 (L ∘ f) p := L.contDiff.contDiffAt.comp p hfp
  let e := hreg.toOpenPartialHomeomorph (L ∘ f) hcomp (by decide)
  let U : Opens E := ⟨e.source ∩ s, e.open_source.inter hs⟩
  have hUs : (U : Set E) ⊆ s := fun _ hx ↦ hx.2
  refine ⟨U, ⟨hreg.mem_toOpenPartialHomeomorph_source hcomp (by decide), hp⟩, hUs, ?_⟩
  apply Topology.IsEmbedding.of_comp
    (continuousOn_iff_continuous_domRestrict.mp (hf.continuousOn.mono hUs)) L.continuous
  exact e.isEmbedding_restrict.comp (Topology.IsEmbedding.inclusion
    (show (U : Set E) ⊆ e.source from fun _ hx ↦ hx.1))

/-- The final restriction in Section 9: a smooth realization of a positive definite
metric is a topological embedding on a smaller open neighborhood, and retains
smoothness and the metric equation there. -/
theorem exists_local_embedding_of_isIsometricOn {n N : ℕ}
    {g : MetricField n} {F : Euclidean n → Euclidean N}
    {s : Set (Euclidean n)} {p : Euclidean n}
    (hs : IsOpen s) (hp : p ∈ s) (hF : ContDiffOn ℝ ∞ F s)
    (hg : ∀ x ∈ s, (g x).PosDef) (hmetric : IsIsometricOn g F s) :
    ∃ U : Opens (Euclidean n), p ∈ U ∧ (U : Set (Euclidean n)) ⊆ s ∧
      ContDiffOn ℝ ∞ F U ∧ IsEmbedding (fun x : U ↦ F x.val) ∧
      IsIsometricOn g F U := by
  have himm : ∀ x ∈ s, Function.Injective (fderiv ℝ F x) :=
    isImmersionOn_of_isIsometricOn hg hmetric
  have hmetric' : EqOn (inducedMetric F) g s := hmetric
  obtain ⟨U, hpU, hUs, hemb⟩ := exists_isEmbedding_restrict_of_injective_fderiv
    hs hp (hF.of_le (by simp)) (himm p hp)
  exact ⟨U, hpU, hUs, hF.mono hUs, hemb, hmetric'.mono hUs⟩

end JanetCartan
