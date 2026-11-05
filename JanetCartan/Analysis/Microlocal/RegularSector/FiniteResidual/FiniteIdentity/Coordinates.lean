module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.Localization
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteEvolution.PhysicalCoordinates

/-!
# Distributional transport to the original physical coordinates

The canonical time-zero chart permutes independent variables, leaving the
matrix fiber unchanged. Transport the complete tested equation by the actual
volume-preserving permutation, including the derivatives of the test times
the coefficients and the full zeroth-order term. Consumer: the finite physical
solver equation, `app:ch_regular_base:eq:energy-complete-residual` and
`app:ch_regular_base:eq:sector-theorem-identity`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.RegularSector.FiniteResidual.FiniteIdentity
open Characteristic.ResidualCoordinates Characteristic.EvolutionIntegral
open FiniteEvolution JanetCartan.CharacteristicTransport.CompleteResidual ActualCarriers
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "H" => SpacetimeL2 d (d+1)

/-- Pullback of the complete physical test action, with the same real
coefficients and without a smoothness assumption on its input. The total
Fréchet derivative also transforms at nondifferentiability points because
the coordinate map is an equivalence (`energy-complete-residual`). -/
theorem physicalTestAction_physicalCoordinates
    (i : Fin (d+1)) (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (u : E → Fin (d+1) → ℂ) (φ : E → ℝ) (j : Fin (d+1)) :
    physicalTestAction (coefficient i Q) (zeroth i B)
      (u ∘ physicalCoordinates i) (φ ∘ physicalCoordinates i) j =
      physicalTestAction (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B u φ j := by
  let e := physicalCoordinates i
  have hd (f : E → ℝ) (y : E) (a : Fin (d+1)) :
      partialDeriv (f ∘ e) y a = fderiv ℝ f (e y) (e (EuclideanSpace.single a 1)) := by
    rw [partialDeriv, e.comp_right_fderiv]
    rfl
  have hc0 (y : E) : coefficient i Q y 0 = ActualCarriers.pencil (Q (e y)) (EuclideanSpace.single i 1) := by
    simp [coefficient, physicalCoordinates_single_zero, e]
  have hcs (y : E) (a : Fin d) : coefficient i Q y a.succ = ActualCarriers.pencil (Q (e y)) (EuclideanSpace.single (i.succAbove a) 1) := by
    simp [coefficient, physicalCoordinates_single_succ, e]
  have hint (f : E → ℂ) : (∫ y, f (e y)) = ∫ y, f y :=
    (measurePreserving_physicalCoordinates i).integral_comp e.toHomeomorph.measurableEmbedding f
  unfold physicalTestAction
  congr 1
  · congr 1
    conv_lhs => rw [Fin.sum_univ_succ]
    conv_rhs => rw [← Fin.add_sum_removeNth i]
    congr 1
    · apply Finset.sum_congr rfl
      intro k _
      simp only [Function.comp_apply, hc0]
      change (∫ y, partialDeriv ((fun z ↦ φ z * ActualCarriers.pencil (Q z) (EuclideanSpace.single i 1) j k) ∘ e) y 0 • u (e y) k) = _
      simp only [hd, e, physicalCoordinates_single_zero]
      exact hint (fun y ↦ partialDeriv (fun z ↦ φ z * ActualCarriers.pencil (Q z) (EuclideanSpace.single i 1) j k) y i • u y k)
    · apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro k _
      simp only [Function.comp_apply, hcs]
      change (∫ y, partialDeriv ((fun z ↦ φ z * ActualCarriers.pencil (Q z) (EuclideanSpace.single (i.succAbove a) 1) j k) ∘ e) y a.succ • u (e y) k) = _
      simp only [hd, e, physicalCoordinates_single_succ]
      exact hint (fun y ↦ partialDeriv (fun z ↦ φ z * ActualCarriers.pencil (Q z) (EuclideanSpace.single (i.succAbove a) 1) j k) y (i.succAbove a) • u y k)
  · apply Finset.sum_congr rfl
    intro k _
    exact hint (fun y ↦ (φ y * B y j k) • u y k)

/-- The representative pullback in the physical test action is precisely the
existing Lebesgue L² pullback (`sector-theorem-identity`). -/
theorem physicalTestAction_physicalPullbackL2
    (i : Fin (d+1)) (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (u : H) (φ : E → ℝ) (j : Fin (d+1)) :
    physicalTestAction (coefficient i Q) (zeroth i B)
      (fun y ↦ (physicalPullbackL2 i u y).ofLp) (φ ∘ physicalCoordinates i) j =
      physicalTestAction (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B (fun y ↦ (u y).ofLp) φ j := by
  rw [SelectedChart.physicalTestAction_eq_of_ae_on (coefficient i Q) (zeroth i B)
    MeasurableSet.univ _ ((fun y ↦ (u y).ofLp) ∘ physicalCoordinates i)
    (by
      rw [Measure.restrict_univ]
      filter_upwards [physicalPullbackL2_coeFn i u] with y hy
      exact congrArg (fun v ↦ v.ofLp) hy)
    _ (subset_univ _) j]
  exact physicalTestAction_physicalCoordinates i Q B _ φ j

/-- Test pairing is preserved by the same unit-Jacobian coordinate change.
No Fourier normalization or matrix-coordinate change is inserted
(`fixed-time-representation`, `sector-theorem-identity`). -/
theorem testPairing_physicalPullbackL2
    (i : Fin (d+1)) (u : H) (φ : E → ℝ) (j : Fin (d+1)) :
    (∫ y, φ (physicalCoordinates i y) • physicalPullbackL2 i u y j) =
      ∫ y, φ y • u y j := by
  calc
    _ = ∫ y, φ (physicalCoordinates i y) • u (physicalCoordinates i y) j := by
      apply integral_congr_ae
      filter_upwards [physicalPullbackL2_coeFn i u] with y hy
      rw [hy]
      rfl
    _ = _ := (measurePreserving_physicalCoordinates i).integral_comp
      (physicalCoordinates i).toHomeomorph.measurableEmbedding (fun y ↦ φ y • u y j)

/-- Transport the actual common-chart tested identity to its original physical
measurement domain. Its premise is supplied by
`SelectedChart.completeResidual_of_common_selected_chart`; the solver and the
entire source-plus-residual operator undergo the SAME L² conjugation
(`energy-complete-residual`). -/
theorem tested_equation_physicalOperator
    (i : Fin (d+1)) (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (S T : H →L[ℂ] H) (U : Set E)
    (ht : ∀ u φ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ physicalCoordinates i ⁻¹' U → ∀ j,
      physicalTestAction (coefficient i Q) (zeroth i B) (fun y ↦ (S u y).ofLp) φ j =
        ∫ y, φ y • T u y j) :
    ∀ u φ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∀ j,
      physicalTestAction (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B (fun y ↦ (physicalOperator i S u y).ofLp) φ j =
        ∫ y, φ y • physicalOperator i T u y j := by
  intro u φ hφ hc hφU j
  let e := physicalCoordinates i
  have hp : HasCompactSupport (φ ∘ e) := hc.comp_homeomorph e.toHomeomorph
  have hs : tsupport (φ ∘ e) ⊆ e ⁻¹' U :=
    (tsupport_comp_subset_preimage φ e.continuous).trans (preimage_mono hφU)
  have he := ht (physicalPullbackL2 i u) (φ ∘ e) (hφ.comp e.contDiff) hp hs j
  rw [← physicalTestAction_physicalPullbackL2 i Q B,
    ← testPairing_physicalPullbackL2 i]
  simpa only [physicalOperator_apply, LinearIsometryEquiv.apply_symm_apply, Function.comp_apply, e] using he

end JanetCartan.RegularSector.FiniteResidual.FiniteIdentity
