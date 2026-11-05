module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.Detection

/-!
# Finite-cover specification for frozen carriers

Shared indexing and the exact full detector inequality in
`app:ch_seed:eq:seed-frozen-detection`. There is no existence assertion in this
module. In particular, none of the geometric or detection properties below is
assumed as a substitute for constructing the menu.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace

namespace JanetCartan.FrozenMenu

/-- Finite cover data for `app:ch_seed:prop:seed-frozen-menu`, item 2.
Patch indices are retained literally, including duplicate specifications.
A chart may have zero selected patches, as in the invertible-pencil case. -/
structure CoverData (n : ℕ) where
  chartCount : ℕ
  patchCount : Fin chartCount → ℕ
  patches : (b : Fin chartCount) → Fin (patchCount b) → Patch n
  domain : Fin chartCount → Set (Euclidean n)
  roots : (b : Fin chartCount) → Fin (patchCount b) → Euclidean n → Euclidean 3

/-- The finite-cover conclusion before assigning radial labels, including
smooth interior roots, the first-coordinate derivative gap, and the image
channel in the full detector inequality
(`app:ch_seed:prop:seed-frozen-menu`, items 1–2). -/
def CoverData.IsValid {n : ℕ} (D : CoverData n) (c C : ℝ) : Prop :=
  0 < c ∧ 0 < C ∧
  (∀ b, IsOpen (D.domain b)) ∧
  Metric.sphere (0 : Euclidean n) 1 ⊆ ⋃ b, D.domain b ∧
  (∀ b a, (D.patches b a).IsValid c C ∧
    (D.patches b a).IsIncidenceSection (D.domain b) (D.roots b a) c) ∧
  (∀ b, ∀ k ∈ D.domain b, ∀ s : Euclidean n,
    c * ‖s‖ ^ 2 ≤ ‖ActualCarriers.imageChannel (cubePencil k) s‖ ^ 2 +
      ∑ a, ⟪CubeCarrier.quadratic ((D.patches b a).toFun (D.roots b a k)), s⟫_ℝ ^ 2)

end JanetCartan.FrozenMenu
