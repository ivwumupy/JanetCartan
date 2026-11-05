module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.IncidenceCover.Bounds

/-!
# One finite detecting incidence chart

Data and the full local conclusion needed before compactness of the covector
sphere in Step 4 of `app:ch_seed:prop:seed-frozen-menu`. These specifications
do not assert the existence of a chart.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace

namespace JanetCartan.FrozenMenu

/-- One neighborhood with its finite list of patches and incidence roots,
before selecting a finite cover in `app:ch_seed:prop:seed-frozen-menu`, Step 4.
Zero selected patches are permitted. -/
structure ChartData (n : ℕ) where
  patchCount : ℕ
  patches : Fin patchCount → Patch n
  domain : Set (Euclidean n)
  roots : Fin patchCount → Euclidean n → Euclidean 3

/-- All local chart properties in `app:ch_seed:prop:seed-frozen-menu`, Step 4,
including the full image channel. Existence remains a separate obligation. -/
def ChartData.IsValid {n : ℕ} (D : ChartData n) (c C : ℝ) : Prop :=
  0 < c ∧ 0 < C ∧ IsOpen D.domain ∧
  (∀ a, (D.patches a).IsValid c C ∧
    (D.patches a).IsIncidenceSection D.domain (D.roots a) c) ∧
  (∀ k ∈ D.domain, ∀ s : Euclidean n,
    c * ‖s‖ ^ 2 ≤ ‖ActualCarriers.imageChannel (cubePencil k) s‖ ^ 2 +
      ∑ a, ⟪CubeCarrier.quadratic ((D.patches a).toFun (D.roots a k)), s⟫_ℝ ^ 2)

/-- Choosing common positive lower and upper margins preserves every chart
field (`app:ch_seed:prop:seed-frozen-menu`, Step 4). -/
theorem ChartData.IsValid.mono {n : ℕ} {D : ChartData n} {c C c' C' : ℝ}
    (h : D.IsValid c C) (hc' : 0 < c') (hc : c' ≤ c) (hC : C ≤ C') :
    D.IsValid c' C' := by
  refine ⟨hc', h.2.1.trans_le hC, h.2.2.1, ?_, ?_⟩
  · intro a
    exact ⟨(h.2.2.2.1 a).1.mono hc' hc hC,
      (h.2.2.2.1 a).2.mono Set.Subset.rfl hc⟩
  · intro k hk s
    exact (mul_le_mul_of_nonneg_right hc (sq_nonneg ‖s‖)).trans (h.2.2.2.2 k hk s)

end JanetCartan.FrozenMenu
