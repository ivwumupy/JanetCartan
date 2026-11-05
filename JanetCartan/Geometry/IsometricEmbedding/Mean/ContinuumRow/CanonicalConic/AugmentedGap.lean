module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.AugmentedComparison

/-!
# The actual augmented derivative half-gap

The fixed triangular reference and the literal joint Hamilton comparison
close the normalized differential premise of the global carrier producer.
Every radius and threshold precedes the current frame (`bg-Psi`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CanonicalConic
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualPhase ActualComparison CanonicalCarrier ContinuumNormalReduction TransportSymbol

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Actual augmented half-gap on an arbitrarily capped common input ball,
from primitive frozen incidence and frame closeness. In particular the
reference equivalence, radius and positive threshold do not depend on `F`.
Consumer: the supported variant of
`exists_carrierL2Extension_globalNormal_of_primitiveNorms` (`bg-Psi`). -/
theorem exists_actual_augmented_gap {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {cap : ℝ} (hcap : 0 < cap) :
    ∃ ρ > (0 : ℝ), ρ < cap ∧ ∃ δ > (0 : ℝ), ∀ Q,
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ →
      ∀ p ∈ closedBall (augmentedInputCenter T (z₀ := z₀) (k := k)) ρ,
        ‖(augmentedReferenceEquiv T hP hz₀ hinc hd).symm.toContinuousLinearMap.comp
          (fderiv ℝ (augmentedTransportGradient (transportPosition T Q)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2 := by
  let A := augmentedReferenceEquiv T hP hz₀ hinc hd
  let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
  obtain ⟨r, hr, hrbox⟩ := exists_box_radius T hP hz₀
  obtain ⟨_, hphys, hcarrier⟩ := hrbox r hr le_rfl
  have hcarrier' : closedBall (spectatorCenter z₀) r ×ˢ closedBall (z₀ 0) r ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2) :=
    fun p hp ↦ hcarrier ⟨closedBall_subset_closedBall (by linarith) hp.1,
      closedBall_subset_closedBall (by linarith) hp.2⟩
  obtain ⟨ρ, hρ, hρcap, hgap⟩ := exists_frozen_augmented_gap T hP hz₀ hinc hd
    (lt_min hcap (half_pos hr))
  obtain ⟨δ, hδ, hcomp⟩ := exists_augmented_comparison_threshold T hP z₀ ηb hr
    (by linarith) hcarrier'
    (show 0 < 1 / (4 * (‖A.symm.toContinuousLinearMap‖ + 1)) by positivity)
  refine ⟨ρ, hρ, hρcap.trans_le (min_le_left _ _), δ, hδ, ?_⟩
  intro Q hQ p hp
  apply normalized_derivative_gap_of_perturbation A (hgap p hp)
  have hb := hcomp Q hQ p (closedBall_subset_closedBall
    (hρcap.le.trans (min_le_right _ _)) hp)
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans
  have hpos : 0 < 4 * (‖A.symm.toContinuousLinearMap‖ + 1) := by positivity
  rw [mul_one_div, div_le_iff₀ hpos]
  nlinarith [norm_nonneg A.symm.toContinuousLinearMap]

end JanetCartan.ContinuumRow.CanonicalConic
