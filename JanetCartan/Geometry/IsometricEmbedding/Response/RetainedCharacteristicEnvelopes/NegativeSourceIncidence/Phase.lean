module

public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.ConicRootIncidence
public import JanetCartan.Analysis.Microlocal.FullSourceStationary.PhaseProfiles

/-!
# The negative of the original full source phase

The source parameters, Hamilton chart and physical coordinate permutation stay
fixed. The sign here is the sign of the entire source phase; it is independent
of the literal adjoint orientation in `fullSourceJointPhase`.

Consumer: the negative source incidence and stationary maps for the reflected
letters in `app:ch_response:eq:fixed-factor-transfer`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu CompatibleResponse LeadingWave.FullModulation

variable {d : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
local notation "E" => Euclidean (d + 1)
local notation "Coeff" => Fin (d + 1) → MetricTensor (d + 1)
local notation "Param" => Euclidean 3 × Euclidean d

/-- Negate the entire original full source phase, retaining its independent
free covector and carrier labels (`app:ch_response:eq:response-exact-phase`). -/
def negativeFullSourcePhaseInCoordinates (i : Fin (d + 1))
    (Q : {Q : E → Coeff // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress (d + 1)) < T.family.threshold})
    (x : E) (c : Param) : ℝ :=
  -T.fullSourcePhaseInCoordinates i Q x c

/-- Smoothness of the actual negative source, on exactly the original full
source domain (`app:ch_response:eq:direct-envelope-profile`). -/
theorem negativeFullSourcePhaseInCoordinates_smooth (i : Fin (d + 1)) (Q : _)
    {Ω : Set (E × Param)}
    (hΩ : ∀ q ∈ Ω, ((primaryCoordinateChange i).symm q.1, q.2.2) ∈ phaseDomain T) :
    ContDiffOn ℝ ∞ (Function.uncurry (T.negativeFullSourcePhaseInCoordinates i Q)) Ω :=
  (T.fullSourcePhaseInCoordinates_smooth i Q hΩ).neg

/-- The negative source covector is the negative of the original full
Hamilton momentum in the same solver coordinates
(`app:ch_response:eq:response-exact-phase`). -/
theorem negativeFullSourcePhaseInCoordinates_gradient (i : Fin (d + 1)) (Q : _)
    {x : E} {c : Param}
    (hx : ((primaryCoordinateChange i).symm x, c.2) ∈ phaseDomain T) :
    gradient (fun y ↦ T.negativeFullSourcePhaseInCoordinates i Q y c) x =
      primaryCoordinateChange i
        (-phaseGradient T Q ((primaryCoordinateChange i).symm x) c.2) := by
  have hneg : gradient (fun y ↦ T.negativeFullSourcePhaseInCoordinates i Q y c) x =
      -gradient (fun y ↦ T.fullSourcePhaseInCoordinates i Q y c) x := by
    simp only [negativeFullSourcePhaseInCoordinates, gradient, fderiv_fun_neg, map_neg]
  rw [hneg, T.fullSourcePhaseInCoordinates_gradient i Q hx, map_neg]

/-- Homogeneity of the original determinant proves characteristicity of
the negative full source momentum, without changing the retained root or field
(`app:ch_response:eq:response-exact-phase`). -/
theorem negative_full_source_characteristic (Q : _)
    {w : E × Euclidean d} (hw : w ∈ phaseDomain T) :
    determinant (Q.1 w.1) (-phaseGradient T Q w.1 w.2) = 0 := by
  simpa only [neg_one_smul, phase_characteristic T Q hw, mul_zero] using
    determinant_smul (Q.1 w.1) (phaseGradient T Q w.1 w.2) (-1)

/-- Negating the whole phase preserves every source seminorm. This supplies
the actual low budgets for the negative stationary branch
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem negativeFullSourcePhaseInCoordinates_cNorm (i : Fin (d + 1)) (Q : _)
    (K : Set (E × Param)) (m : ℕ) :
    cNorm K m (Function.uncurry (T.negativeFullSourcePhaseInCoordinates i Q)) =
      cNorm K m (Function.uncurry (T.fullSourcePhaseInCoordinates i Q)) := by
  change cNorm K m (-(Function.uncurry (T.fullSourcePhaseInCoordinates i Q))) = _
  exact cNorm_neg _ _ _

/-- The full Hamilton momentum comparison is unchanged by negating both
covectors. The threshold still precedes every field and source parameter
(`app:ch_response:eq:response-exact-phase`). -/
theorem exists_negative_full_source_covector_comparison {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ Q,
      cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress (d + 1)) < δ →
      ∀ w ∈ phaseDomain T,
        ‖-phaseGradient T Q w.1 w.2 - -T.reference.covector (0, w.2)‖ < ε := by
  obtain ⟨δ, hδ, hcompare⟩ := T.exists_full_source_covector_comparison hε
  refine ⟨δ, hδ, ?_⟩
  intro Q hQ w hw
  simpa only [neg_sub_neg, norm_sub_rev] using hcompare Q hQ w hw

/-- Reflect the covector argument of an arbitrary open incidence set. The
existing actual comparison theorem then admits all negative source covectors
in that SAME set, with one threshold on the original compact support
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem exists_uniform_negative_full_source_pair_neighborhood
    (hframe : closedBall (0 : E) T.data.localReference.stateRadius ⊆ U)
    {J : Set (E × Param)} (hJ : IsCompact J) (hJT : J ⊆ domain T)
    {V : Set (Coeff × E)} (hV : IsOpen V)
    (hJV : ∀ w ∈ J, (cubeStress (d + 1), -T.reference.covector (0, w.2.2)) ∈ V) :
    ∃ δ > (0 : ℝ), δ ≤ T.family.threshold ∧
      ∀ Q, cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress (d + 1)) < δ →
        ∀ w ∈ J, (Q.1 w.1, -phaseGradient T Q w.1 w.2.2) ∈ V := by
  exact T.exists_uniform_full_source_pair_neighborhood hframe hJ hJT
    (hV.preimage (continuous_fst.prodMk continuous_snd.neg)) hJV

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
