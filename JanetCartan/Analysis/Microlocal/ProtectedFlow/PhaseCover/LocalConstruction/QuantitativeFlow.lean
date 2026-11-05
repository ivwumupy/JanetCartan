module

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.PhaseCover.LocalConstruction.StateBall

/-!
# Quantitative compatibility for the retained comparison flows

The local construction in `app:ch_regular:thm:no-return` uses these facts to
transfer a fixed projection bound from an auxiliary Hamilton construction to
the same flow and inverse chart used for complete-source graph coverage.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace

namespace JanetCartan.ProtectedFlow.PhaseCover

open HamiltonPhase

variable {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]

/-- A source ball cannot exceed the physical state ball: test the initial
section along a unit tangent vector. This lets the comparison producer place
its whole source in an independently constructed quantitative flow domain
(`app:ch_regular:thm:no-return`). -/
theorem sourceRadius_le_stateRadius
    {H : HomogeneousSymbol E} (Φ : HamiltonFlow H U)
    (j : U →ₗᵢ[ℝ] E) (hj : Φ.sectionMap = j.toContinuousLinearMap)
    (v : U) (hv : ‖v‖ = 1) (η : ℝ × U) {ξ : E} {r R : ℝ}
    (hr : 0 < r)
    (hadm : closure (ball ((0 : ℝ), (0, η)) (3 * r)) ⊆ Φ.time ×ˢ Φ.parameters)
    (hrange : ∀ q ∈ Φ.time ×ˢ Φ.parameters,
      (Φ.position q, Φ.momentum q) ∈ closedBall ((0 : E), ξ) R) :
    3 * r ≤ R := by
  have hq : ((0 : ℝ), ((3 * r) • v, η)) ∈
      closure (ball ((0 : ℝ), (0, η)) (3 * r)) := by
    rw [closure_ball _ (by positivity : 3 * r ≠ 0)]
    simp only [mem_closedBall, Prod.dist_eq, dist_self, dist_zero_right,
      norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 3 * r), hv,
      mul_one, max_le_iff]
    exact ⟨by positivity, le_rfl, by positivity⟩
  have hx := Φ.initial_position ((3 * r) • v, η) (hadm hq).2
  have hb := (le_max_left _ _).trans (mem_closedBall.mp (hrange _ (hadm hq)))
  simpa only [hx, hj, LinearIsometry.coe_toContinuousLinearMap,
    dist_zero_right, j.norm_map, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 3 * r), hv, mul_one] using hb

/-- The normalized projection half-gap gives a uniform upper Lipschitz
bound for physical positions on the full convex source domain. The auxiliary
buffered Hamilton producer supplies this gap; uniqueness transfers the bound
to the retained comparison charts (`app:ch_regular:thm:no-return`). -/
theorem position_dist_le_of_projection_gap
    {H : HomogeneousSymbol E} (Φ : HamiltonFlow H U)
    {B : Set (ℝ × InitialData U)} (hB : Convex ℝ B)
    (hadm : B ⊆ Φ.time ×ˢ Φ.parameters)
    (A : (ℝ × InitialData U) ≃L[ℝ] (E × (ℝ × U)))
    (hgap : ∀ q ∈ B,
      ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp
        (fderiv ℝ Φ.augmentedProjection q) -
          ContinuousLinearMap.id ℝ (ℝ × InitialData U)‖ ≤ 1 / 2)
    {q w : ℝ × InitialData U} (hq : q ∈ B) (hw : w ∈ B) :
    dist (Φ.position q) (Φ.position w) ≤
      (2 * ‖(A : (ℝ × InitialData U) →L[ℝ] (E × (ℝ × U)))‖) * dist q w := by
  have hb (z) (hz : z ∈ B) :
      ‖fderiv ℝ Φ.augmentedProjection z‖ ≤
        2 * ‖(A : (ℝ × InitialData U) →L[ℝ] (E × (ℝ × U)))‖ := by
    let P := fderiv ℝ Φ.augmentedProjection z
    have hn : ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp P‖ ≤ 2 := by
      have hh := norm_add_le
        ((A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp P -
          ContinuousLinearMap.id ℝ _) (ContinuousLinearMap.id ℝ (ℝ × InitialData U))
      rw [sub_add_cancel] at hh
      have hi := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := ℝ × InitialData U)
      linarith [hgap z hz]
    have he : P = (A : (ℝ × InitialData U) →L[ℝ] (E × (ℝ × U))).comp
        ((A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp P) := by
      apply ContinuousLinearMap.ext
      intro v
      exact (A.apply_symm_apply (P v)).symm
    calc
      ‖P‖ = _ := congrArg norm he
      _ ≤ ‖(A : (ℝ × InitialData U) →L[ℝ] (E × (ℝ × U)))‖ *
          ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp P‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ _ := by nlinarith [norm_nonneg (A : (ℝ × InitialData U) →L[ℝ] (E × (ℝ × U)))]
  have hh := hB.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz ↦ (Φ.hasFDerivAt_augmentedProjection (hadm hz)).differentiableAt)
    hb hw hq
  have hp : ‖Φ.position q - Φ.position w‖ ≤
      ‖Φ.augmentedProjection q - Φ.augmentedProjection w‖ := by
    exact norm_fst_le (Φ.augmentedProjection q - Φ.augmentedProjection w)
  simpa only [dist_eq_norm] using hp.trans hh

end JanetCartan.ProtectedFlow.PhaseCover
