module

public import JanetCartan.Analysis.Microlocal.FullSourceStationary.JointPhaseBounds
public import JanetCartan.Analysis.Microlocal.FullSourceStationary.CoefficientCap
public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.NegativeSourceIncidence.Phase

/-!
# Actual negative source budgets before the common reference

A supplied order-four coefficient cap controls the negative original full source through
order three and both literal joint orientations through order three. The actual
phase producers retain coefficient shift one. No reference or history is used
to choose these budgets. The universal cap and its actual admission producer
are in `CoefficientCap`. Consumer: the pre-reference stationary radii used by
`FixedResponseSelection.IncidenceStationary`, for
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu CompatibleResponse
open RegularSector.Characteristic ConicPhase EvolutionIntegral FullSourceStationary
open ResponseTransfer.DirectEvolution LeadingWave.FullModulation

variable {d : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
local notation "E" => Euclidean (d + 1)
local notation "Param" => Euclidean 3 × Euclidean d
local notation "TC" => TwoTimePoint (Euclidean d)

/-- Every coefficient-dependent bound for the original full phase also
bounds its negative, with the identical coefficient order. This is the actual
source budget for negative stationary maps
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_negativeFullSourcePhaseInCoordinates_frame_bound (i : Fin (d + 1))
    {K : Set (E × Param)} (hK : IsCompact K)
    (hKD : ∀ q ∈ K, ((primaryCoordinateChange i).symm q.1, q.2.2) ∈ phaseDomain T) :
    ∃ A : ℕ → ℝ, (∀ m, 0 < A m) ∧ ∀ Q m,
      cNorm K m (fun q ↦ T.negativeFullSourcePhaseInCoordinates i Q q.1 q.2) ≤ A m *
        (1 + cNorm (closedBall (0 : E) T.data.localReference.stateRadius) (m + 1) Q.1) := by
  obtain ⟨A, hA, hbound⟩ := T.exists_fullSourcePhaseInCoordinates_frame_bound i hK hKD
  refine ⟨A, hA, ?_⟩
  intro Q m
  change cNorm K m (Function.uncurry (T.negativeFullSourcePhaseInCoordinates i Q)) ≤ _
  rw [T.negativeFullSourcePhaseInCoordinates_cNorm]
  exact hbound Q m

/-- The actual source and both literal joint phases have fixed low budgets
from one order-four coefficient cap. The constants precede the field and chart,
and in particular every common reference and history. The cap is produced by
`exists_reference_tolerance_for_stationary_coefficient_cap`; the chart budget
is the original retained-evolution `phaseCost`. These are actual phase bounds,
not premises asserting successful stationary geometry
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_negative_full_source_low_phase_budgets_of_coefficient_cap
    (i : Fin (d + 1)) (ℓ : Euclidean d →L[ℝ] ℝ)
    {K : Set (FullSourcePoint d)} {J : Set TC} {KP : Set (E × Param)}
    (hK : IsCompact K) (hJ : IsCompact J) (hKP : IsCompact KP)
    (hpos : ∀ v ∈ K, 0 < ℓ (spatialPart v.2.snd))
    (hmap : ∀ adj : Bool, MapsTo (ConicPhase.normalize ℓ ∘ fullSourceGraphPoint adj) K J)
    (hsrc : ∀ v ∈ K, (v.2.fst, v.1.2.2) ∈ KP)
    (hout : ∀ v ∈ K, v.1.2 ∈ KP)
    (hKD : ∀ q ∈ KP, ((primaryCoordinateChange i).symm q.1, q.2.2) ∈ phaseDomain T)
    {cap : ℝ} (hcap : 0 ≤ cap) (KQ : Set E)
    (phaseCost : ℕ → ℝ) (hphaseCost : ∀ m, 0 < phaseCost m) :
    ∃ AP AF : ℕ → ℝ, (∀ m, 0 < AP m) ∧ (∀ m, 0 < AF m) ∧
      ∀ Q, cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 4 Q.1 ≤ cap →
        cNorm KQ 4 Q.1 ≤ cap →
        (∀ m ≤ 3, cNorm KP m
          (Function.uncurry (T.negativeFullSourcePhaseInCoordinates i Q)) ≤ AP m) ∧
        ∀ C : OpenPartialHomeomorph TC TC, J ⊆ C.target →
          ContDiffOn ℝ ∞ (twoTimePhase C) C.target →
          (∀ m ≤ 3, cNorm J m (twoTimePhase C) ≤
            phaseCost m * (1 + cNorm KQ (m + 1) Q.1)) →
          ∀ adj : Bool, ∀ m ≤ 3,
            cNorm K m (fullSourceJointPhase adj (curriedPhase ℓ C)
              (T.negativeFullSourcePhaseInCoordinates i Q)) ≤ AF m := by
  obtain ⟨BP, hBP, hbP⟩ := T.exists_negativeFullSourcePhaseInCoordinates_frame_bound i hKP hKD
  have hbounds (adj : Bool) := exists_fullSourceJointPhase_cNorm_bound adj ℓ
    hK hJ hKP hpos (hmap adj) hsrc hout
  choose BF hBF hbF using hbounds
  let AP := fun m ↦ BP m * (1 + cap)
  let B := fun m ↦ BF false m + BF true m
  let AF := fun m ↦ B m * (1 + phaseCost m * (1 + cap) + AP m)
  have hAP m : 0 < AP m := mul_pos (hBP m) (by linarith)
  have hB m : 0 < B m := add_pos (hBF false m) (hBF true m)
  have hBFle (adj : Bool) m : BF adj m ≤ B m := by
    cases adj <;> dsimp [B] <;> linarith [hBF false m, hBF true m]
  have hAF m : 0 < AF m := by
    dsimp [AF]
    exact mul_pos (hB m) (by have hp := hphaseCost m; have ha := hAP m; positivity)
  refine ⟨AP, AF, hAP, hAF, ?_⟩
  intro Q hQframe hQcap
  have hprimary m (hm : m ≤ 3) :
      cNorm KP m (Function.uncurry (T.negativeFullSourcePhaseInCoordinates i Q)) ≤ AP m := by
    have hcoeff := (cNorm_mono_order (by omega : m + 1 ≤ 4)).trans hQframe
    change cNorm KP m (fun q ↦ T.negativeFullSourcePhaseInCoordinates i Q q.1 q.2) ≤ AP m
    exact (hbP Q m).trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hcoeff) (hBP m).le)
  refine ⟨hprimary, ?_⟩
  intro C hJC hC hchart adj m hm
  have hφ : ∀ q ∈ KP, ContDiffAt ℝ ∞
      (Function.uncurry (T.negativeFullSourcePhaseInCoordinates i Q)) q := by
    intro q hq
    have hF : ContDiff ℝ ∞ (fun q : E × Param ↦
        ((primaryCoordinateChange i).symm q.1, q.2.2)) :=
      ((primaryCoordinateChange i).symm.contDiff.comp contDiff_fst).prodMk contDiff_snd.snd
    have hh := ((phase_smooth T Q).contDiffAt (isOpen_ball.mem_nhds
      (ball_subset_ball (by linarith [T.family.radius_pos] :
        T.family.radius ≤ 2 * T.family.radius) (hKD q hq)))).comp q hF.contDiffAt
    exact hh.neg
  have hcoeff := (cNorm_mono_order (by omega : m + 1 ≤ 4)).trans hQcap
  have hc := (hchart m hm).trans
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl hcoeff) (hphaseCost m).le)
  apply (hbF adj C hJC hC (T.negativeFullSourcePhaseInCoordinates i Q) hφ m).trans
  exact mul_le_mul (hBFle adj m)
    (add_le_add (add_le_add le_rfl hc) (hprimary m hm))
    (by linarith [cNorm_nonneg J m (twoTimePhase C),
      cNorm_nonneg KP m (Function.uncurry (T.negativeFullSourcePhaseInCoordinates i Q))] :
      0 ≤ 1 + cNorm J m (twoTimePhase C) +
      cNorm KP m (Function.uncurry (T.negativeFullSourcePhaseInCoordinates i Q))) (hB m).le

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
