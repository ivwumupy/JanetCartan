module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.Terms
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.DerivativeTransfer.OperatorIteration

/-!
# Literal full-amplitude differential commutator

The scalar Euclidean kernel identity in `app:ch_background:eq:bg-commutator`.
The operator is the existing two-position L² realization; neither the identity
nor its L² representability is assumed. The full amplitude includes its physical
cutoffs. Geometric normal reduction and transfer to unit-torus charts are separate
producer obligations, not asserted by these Euclidean identities.
-/

@[expose] public noncomputable section

open MeasureTheory LineDeriv
open scoped ContDiff SchwartzMap
open JanetCartan.AmplitudeBound

set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.Pseudodifferential
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp ℂ 2 (volume : Measure E)

/-- `app:ch_background:eq:bg-commutator`: the actual L² sum of surviving
branches on a compact smooth datum. The primitive budget reserves a fixed
`2 * (d + 1)` derivatives beyond the commutator order. -/
def differentialCommutatorCompactL2
    (hd : 0 < d) (R : ℝ)
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (A : ℝ)
    (is : List (Fin d))
    (hA : HasAmplitudeDerivativeBound b (2 * (d + 1) + is.length) A)
    (u : E → ℂ) (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u) : L² :=
  ((differentialCommutatorTerms is).attach.map fun p =>
    orderedTransferTermL2Operator hd R b hb hs A is hA
      ⟨p.val, differentialCommutatorTerms_mem_transfer is p.val p.property⟩
      (((contDiff_euclideanCoordinateDerivList hu p.val.2).continuous.memLp_of_hasCompactSupport
        (hasCompactSupport_euclideanCoordinateDerivList hus p.val.2)).toLp
          (euclideanCoordinateDerivList p.val.2 u))).sum

/-- `app:ch_background:eq:bg-commutator`: the L² commutator sum pairs with
Schwartz tests as the explicit literal kernel sum. All source derivatives and
physical masks remain inside `iteratedTransferAmplitude`. -/
theorem differentialCommutatorCompactL2_pairing
    (hd : 0 < d) (R : ℝ)
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (A : ℝ)
    (is : List (Fin d))
    (hA : HasAmplitudeDerivativeBound b (2 * (d + 1) + is.length) A)
    (u : E → ℂ) (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u)
    (φ : 𝓢(E, ℂ)) :
    (differentialCommutatorCompactL2 hd R b hb hs A is hA u hu hus : 𝓢'(E, ℂ)) φ =
      ((differentialCommutatorTerms is).map fun p => ∫ x, φ x * fullAmplitudeOperator
        (fun x y ξ => iteratedTransferAmplitude b p.1 ξ (pairedPosition x y))
        (euclideanCoordinateDerivList p.2 u) x).sum := by
  let ev : L² →+ ℂ :=
    { toFun := fun v => (v : 𝓢'(E, ℂ)) φ
      map_zero' := congrArg (fun T : 𝓢'(E, ℂ) => T φ)
        ((Lp.toTemperedDistributionCLM ℂ volume 2).map_zero)
      map_add' := fun v w => congrArg (fun T : 𝓢'(E, ℂ) => T φ)
        ((Lp.toTemperedDistributionCLM ℂ volume 2).map_add v w) }
  change ev _ = _
  rw [differentialCommutatorCompactL2, map_list_sum, List.map_map]
  rw [← List.attach_map_val (l := differentialCommutatorTerms is)]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  exact twoPositionL2Operator_pairing_eq_fullAmplitudeOperator hd R
    (iteratedTransferAmplitude b p.val.1)
    (contDiff_uncurry_iteratedTransferAmplitude hb p.val.1)
    (supportedInCenteredBox_iteratedTransferAmplitude b R hs p.val.1) _ _
    (euclideanCoordinateDerivList p.val.2 u)
    (contDiff_euclideanCoordinateDerivList hu p.val.2)
    (hasCompactSupport_euclideanCoordinateDerivList hus p.val.2) φ

/-- `app:ch_background:eq:bg-commutator`: exact distributional commutator
identity for the actual full-amplitude operator on compact smooth tests.
Subtracting `E D^is u` cancels the unique all-datum branch; every remaining
branch has at least one physical derivative by `differentialCommutatorTerms_spec`.
The analytic premises are only smoothness, support, and primitive amplitude bounds. -/
theorem twoPositionL2Operator_differential_commutator
    (hd : 0 < d) (R : ℝ)
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (A : ℝ)
    (is : List (Fin d))
    (hA : HasAmplitudeDerivativeBound b (2 * (d + 1) + is.length) A)
    (u : E → ℂ) (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u) :
    let T := twoPositionL2Operator hd R b hb hs A
      (amplitudeDerivativeBound_of_le hA (Nat.le_add_right _ _))
    orderedTransferAction (fun i => lineDerivOp (EuclideanSpace.single i 1 : E)) is
      (T ((hu.continuous.memLp_of_hasCompactSupport hus).toLp u) : 𝓢'(E, ℂ)) -
      (T (((contDiff_euclideanCoordinateDerivList hu is).continuous.memLp_of_hasCompactSupport
        (hasCompactSupport_euclideanCoordinateDerivList hus is)).toLp
          (euclideanCoordinateDerivList is u)) : 𝓢'(E, ℂ)) =
      (differentialCommutatorCompactL2 hd R b hb hs A is hA u hu hus : 𝓢'(E, ℂ)) := by
  dsimp only
  ext φ
  change (orderedTransferAction (fun i => lineDerivOp (EuclideanSpace.single i 1 : E)) is
      (twoPositionL2Operator hd R b hb hs A
        (amplitudeDerivativeBound_of_le hA (Nat.le_add_right _ _))
        ((hu.continuous.memLp_of_hasCompactSupport hus).toLp u) : 𝓢'(E, ℂ))) φ -
      (twoPositionL2Operator hd R b hb hs A
        (amplitudeDerivativeBound_of_le hA (Nat.le_add_right _ _))
        (((contDiff_euclideanCoordinateDerivList hu is).continuous.memLp_of_hasCompactSupport
          (hasCompactSupport_euclideanCoordinateDerivList hus is)).toLp
            (euclideanCoordinateDerivList is u)) : 𝓢'(E, ℂ)) φ = _
  rw [twoPositionL2Operator_iteratedLineDeriv_apply hd R b hb hs A is hA u hu hus φ,
    twoPositionL2Operator_pairing_eq_fullAmplitudeOperator hd R b hb hs A _
      (euclideanCoordinateDerivList is u) (contDiff_euclideanCoordinateDerivList hu is)
      (hasCompactSupport_euclideanCoordinateDerivList hus is),
    differentialCommutatorCompactL2_pairing,
    orderedTransferTerms_sum_eq_commutator_add]
  simp only [iteratedTransferAmplitude, orderedTransferAction, add_sub_cancel_right]

end JanetCartan.Pseudodifferential
