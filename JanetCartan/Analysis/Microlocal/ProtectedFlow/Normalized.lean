module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Compact normalized phase-graph families

The compact-buffer argument in `app:ch_regular:thm:no-return`. Parameters can
include a finite chart index, annular covectors, and a compact coefficient
family. The buffer is uniform over all parameters and physical points.
-/

@[expose] public noncomputable section

open Set Metric

namespace JanetCartan.ProtectedFlow

variable {E P F : Type*} [TopologicalSpace E] [TopologicalSpace P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Angular normalization of a covector (`app:ch_regular:defn:protected-saturation`). -/
def normalizedCovector (p : F) : F := ‖p‖⁻¹ • p

/-- The normalized image over the complete physical-parameter product
(`app:ch_regular:thm:no-return`). -/
def normalizedGraphImage (g : P → E → F) (X : Set E) (V : Set P) : Set F :=
  (fun y : E × P ↦ normalizedCovector (g y.2 y.1)) '' (X ×ˢ V)

/-- Compact annular phase graphs have compact normalized images
(`app:ch_regular:thm:no-return`). Nonvanishing is needed on the whole product. -/
theorem isCompact_normalizedGraphImage {g : P → E → F} {X : Set E} {V : Set P}
    (hX : IsCompact X) (hV : IsCompact V)
    (hg : ContinuousOn (fun y : E × P ↦ g y.2 y.1) (X ×ˢ V))
    (hne : ∀ x ∈ X, ∀ η ∈ V, g η x ≠ 0) :
    IsCompact (normalizedGraphImage g X V) := by
  apply (hX.prod hV).image_of_continuousOn
  exact (hg.norm.inv₀ (fun y hy ↦ norm_ne_zero_iff.mpr (hne y.1 hy.1 y.2 hy.2))).smul hg

/-- An open regular sector and a closed nonprincipal set give one positive
angular buffer for all graphs over a compact product
(`app:ch_regular:thm:no-return`). This is a buffer for the entire graph image,
not merely for its source slice. -/
theorem exists_normalizedGraphImage_buffer {g : P → E → F}
    {X : Set E} {V : Set P} {G M : Set F}
    (hX : IsCompact X) (hV : IsCompact V)
    (hg : ContinuousOn (fun y : E × P ↦ g y.2 y.1) (X ×ˢ V))
    (hne : ∀ x ∈ X, ∀ η ∈ V, g η x ≠ 0)
    (hG : IsOpen G) (hM : IsClosed M)
    (hregular : ∀ x ∈ X, ∀ η ∈ V, normalizedCovector (g η x) ∈ G \ M) :
    ∃ ε > 0, cthickening ε (normalizedGraphImage g X V) ⊆ G \ M := by
  apply (isCompact_normalizedGraphImage hX hV hg hne).exists_cthickening_subset_open
    (hG.inter hM.isOpen_compl)
  rintro _ ⟨⟨x, η⟩, ⟨hx, hη⟩, rfl⟩
  exact hregular x hx η hη

/-- The compact-image buffer controls closed balls around every normalized
covector of the family (`app:ch_regular:thm:no-return`). -/
theorem exists_normalized_graph_ball_buffer {g : P → E → F}
    {X : Set E} {V : Set P} {G M : Set F}
    (hX : IsCompact X) (hV : IsCompact V)
    (hg : ContinuousOn (fun y : E × P ↦ g y.2 y.1) (X ×ˢ V))
    (hne : ∀ x ∈ X, ∀ η ∈ V, g η x ≠ 0)
    (hG : IsOpen G) (hM : IsClosed M)
    (hregular : ∀ x ∈ X, ∀ η ∈ V, normalizedCovector (g η x) ∈ G \ M) :
    ∃ ε > 0, ∀ x ∈ X, ∀ η ∈ V,
      closedBall (normalizedCovector (g η x)) ε ⊆ G \ M := by
  obtain ⟨ε, hε, hbuffer⟩ :=
    exists_normalizedGraphImage_buffer hX hV hg hne hG hM hregular
  refine ⟨ε, hε, fun x hx η hη ↦ ?_⟩
  exact (closedBall_subset_cthickening (E := normalizedGraphImage g X V)
    ⟨(x, η), ⟨hx, hη⟩, rfl⟩ ε).trans hbuffer

end JanetCartan.ProtectedFlow
