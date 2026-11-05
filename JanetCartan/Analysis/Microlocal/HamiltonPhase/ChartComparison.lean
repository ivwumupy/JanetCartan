module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.LocalChart
public import JanetCartan.Analysis.Calculus.BufferedInverse

/-!
# Comparing Hamilton phases on common targets

The normalized projection gap controls inverse coordinates and hence the explicit
phase in `app:lem:common-hamilton-phase`. These estimates are used by
`exists_commonBufferedHamiltonPhases` to transfer scalar-symbol stability to phases.
-/

@[expose] public noncomputable section
open Set
open scoped InnerProductSpace ContDiff

namespace JanetCartan.HamiltonPhase
variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]

namespace ProjectionChart
variable {H H₀ : HomogeneousSymbol E} {Φ : HamiltonFlow H U} {Φ₀ : HamiltonFlow H₀ U}
  (C : ProjectionChart Φ) (C₀ : ProjectionChart Φ₀)

/-- Smoothness of the explicit phase (`app:lem:common-hamilton-phase`). -/
theorem contDiffOn_phase {n : WithTop ℕ∞}
    (hC : ContDiffOn ℝ n C.coordinates C.target) :
    ContDiffOn ℝ n (phase C.coordinates) C.target :=
  (contDiff_snd.fst.contDiffOn.mul hC.fst).add
    (hC.snd.inner ℝ contDiff_snd.snd.contDiffOn)

/-- Canonical derivatives of the constructed chart phase
(`app:lem:common-hamilton-phase`). -/
theorem hasFDerivAt_phase_canonical {z : E × (ℝ × U)} (hz : z ∈ C.target) :
    HasFDerivAt (fun η ↦ phase C.coordinates (z.1, η))
      (canonicalCovector (C.coordinates z)) z.2 := by
  have ha := C.source_admissible _ (C.maps_to_source z hz)
  exact Φ.hasFDerivAt_phase_parameter (C.hasFDerivAt_coordinates z hz) ha.1 ha.2
    (Filter.eventuallyEq_of_mem (C.isOpen_target.mem_nhds hz)
      (fun w hw ↦ C.right_inverse w hw))

/-- The phase difference is controlled by the inverse-coordinate difference,
with the split canonical maximum norm (`app:lem:common-hamilton-phase`). -/
theorem norm_phase_sub_le (z : E × (ℝ × U)) :
    ‖phase C.coordinates z - phase C₀.coordinates z‖ ≤
      (|z.2.1| + ‖z.2.2‖) * ‖C.coordinates z - C₀.coordinates z‖ := by
  have he : phase C.coordinates z - phase C₀.coordinates z =
      z.2.1 * ((C.coordinates z).1 - (C₀.coordinates z).1) +
        ⟪(C.coordinates z).2 - (C₀.coordinates z).2, z.2.2⟫_ℝ := by
    simp only [phase, inner_sub_left]
    ring
  rw [he]
  calc
    _ ≤ ‖z.2.1 * ((C.coordinates z).1 - (C₀.coordinates z).1)‖ +
        ‖⟪(C.coordinates z).2 - (C₀.coordinates z).2, z.2.2⟫_ℝ‖ := norm_add_le _ _
    _ ≤ |z.2.1| * ‖(C.coordinates z).1 - (C₀.coordinates z).1‖ +
        ‖(C.coordinates z).2 - (C₀.coordinates z).2‖ * ‖z.2.2‖ := by
      rw [norm_mul, Real.norm_eq_abs z.2.1]
      exact add_le_add le_rfl (norm_inner_le_norm (𝕜 := ℝ) ((C.coordinates z).2 - (C₀.coordinates z).2) z.2.2)
    _ ≤ _ := by
      have h₁ : ‖(C.coordinates z).1 - (C₀.coordinates z).1‖ ≤
          ‖C.coordinates z - C₀.coordinates z‖ := le_max_left _ _
      have h₂ : ‖(C.coordinates z).2 - (C₀.coordinates z).2‖ ≤
          ‖C.coordinates z - C₀.coordinates z‖ := le_max_right _ _
      nlinarith [mul_le_mul_of_nonneg_left h₁ (abs_nonneg z.2.1),
        mul_le_mul_of_nonneg_right h₂ (norm_nonneg z.2.2)]

/-- A normalized projection gap transfers a uniform projection perturbation to
inverse coordinates on their common target (`app:lem:common-hamilton-phase`).
Both inverse lifts must belong to the same convex source domain. -/
theorem norm_coordinates_sub_le_of_projection_close
    {D : Set (ℝ × InitialData U)} (hD : Convex ℝ D)
    (A : (ℝ × InitialData U) ≃L[ℝ] (E × (ℝ × U)))
    (hadm : D ⊆ Φ.time ×ˢ Φ.parameters)
    (hgap : ∀ q ∈ D,
      ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp
        (fderiv ℝ Φ.augmentedProjection q) - ContinuousLinearMap.id ℝ (ℝ × InitialData U)‖
        ≤ 1 / 2)
    {ε : ℝ} (hclose : ∀ q ∈ D, ‖Φ.augmentedProjection q - Φ₀.augmentedProjection q‖ ≤ ε)
    {z : E × (ℝ × U)} (hz : z ∈ C.target) (hz₀ : z ∈ C₀.target)
    (hlift : chartLift C.coordinates z ∈ D) (hlift₀ : chartLift C₀.coordinates z ∈ D) :
    ‖C.coordinates z - C₀.coordinates z‖ ≤
      2 * ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U))‖ * ε := by
  have hright : Φ.augmentedProjection (chartLift C.coordinates z) = z := by
    exact Prod.ext (C.right_inverse z hz) rfl
  have hright₀ : Φ₀.augmentedProjection (chartLift C₀.coordinates z) = z := by
    exact Prod.ext (C₀.right_inverse z hz₀) rfl
  have hlower := normalized_lower_lipschitz_of_derivative_gap hD A
    (fun q hq ↦ (Φ.hasFDerivAt_augmentedProjection (hadm hq)).differentiableAt)
    hgap hlift hlift₀
  have he : ‖chartLift C.coordinates z - chartLift C₀.coordinates z‖ =
      ‖C.coordinates z - C₀.coordinates z‖ := by
    simp [chartLift, Prod.norm_def]
  rw [he, hright] at hlower
  have hn := (A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).le_opNorm
    (z - Φ.augmentedProjection (chartLift C₀.coordinates z))
  have hc := hclose _ hlift₀
  rw [hright₀, norm_sub_rev] at hc
  have hb := mul_le_mul_of_nonneg_left hc
    (norm_nonneg (A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)))
  have hh : ‖C.coordinates z - C₀.coordinates z‖ / 2 ≤
      ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U))‖ * ε :=
    hlower.trans (hn.trans hb)
  linarith only [hh]

end ProjectionChart
end JanetCartan.HamiltonPhase
