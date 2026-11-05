module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.DerivativeTransfer.FrequencyTransfer
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.DerivativeTransfer.Iteration

/-!
# Finite derivative transfer for the actual scalar operator

The assembly of `app:ch_regular_base:eq:graph-derivative-transfer` for phase
`x · ξ`. The induction uses only a finite primitive budget on the original
amplitude; the actual single-derivative identity is proved by frequency limits.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff SchwartzMap
open JanetCartan.AmplitudeBound LineDeriv

namespace JanetCartan.Pseudodifferential
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: every ordered datum
derivative remains compactly supported. -/
theorem hasCompactSupport_euclideanCoordinateDerivList
    {u : E → ℂ} (hu : HasCompactSupport u) (is : List (Fin d)) :
    HasCompactSupport (euclideanCoordinateDerivList is u) := by
  induction is with
  | nil => exact hu
  | cons i is ih => exact ih.fderiv_apply ℝ (EuclideanSpace.single i 1)

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: the actual L²
realization pairs with every Schwartz test as the literal full integral. -/
theorem twoPositionL2Operator_pairing_eq_fullAmplitudeOperator
    (hd : 0 < d) (R : ℝ)
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (A : ℝ)
    (hA : HasAmplitudeDerivativeBound b (2 * (d + 1)) A)
    (u : E → ℂ) (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u)
    (φ : 𝓢(E, ℂ)) :
    (twoPositionL2Operator hd R b hb hs A hA
      ((hu.continuous.memLp_of_hasCompactSupport hus).toLp u) : 𝓢'(E, ℂ)) φ =
      ∫ x, φ x * fullAmplitudeOperator (fun x y ξ ↦ b ξ (pairedPosition x y)) u x := by
  rw [Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  exact (twoPositionL2Operator_toLp_ae_fullAmplitudeOperator_of_physicalBudget
    hd R b hb hs A hA u (hu.continuous.memLp_of_hasCompactSupport hus)
    (hu.of_le (by simp)) hus).mono (fun x hx ↦ congrArg (fun z ↦ φ x * z) hx)

private theorem fullAmplitudeOperator_pairing_transfer
    (hd : 0 < d) (R : ℝ)
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (A : ℝ)
    (hA : HasAmplitudeDerivativeBound b (2 * (d + 1) + 1) A)
    (i : Fin d) (u : E → ℂ) (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u)
    (φ : 𝓢(E, ℂ)) :
    -(∫ x, (lineDerivOp (EuclideanSpace.single i 1 : E) φ) x *
      fullAmplitudeOperator (fun x y ξ ↦ b ξ (pairedPosition x y)) u x) =
      (∫ x, φ x * fullAmplitudeOperator
        (fun x y ξ ↦ transferAmplitude b i ξ (pairedPosition x y)) u x) +
      (∫ x, φ x * fullAmplitudeOperator (fun x y ξ ↦ b ξ (pairedPosition x y))
        (euclideanCoordinateDerivList [i] u) x) := by
  have hbase := amplitudeDerivativeBound_of_le hA (Nat.le_succ (2 * (d + 1)))
  have ht := hasAmplitudeDerivativeBound_transferAmplitude b
    (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) i (2 * (d + 1)) A hA
  have ht₂ := memLp_fullAmplitudeOperator_of_physicalBudget hd R (transferAmplitude b i)
    (contDiff_uncurry_transferAmplitude hb i)
    (supportedInCenteredBox_transferAmplitude b R hs i) (2 * A) ht u hu hus
  have hd₂ := memLp_fullAmplitudeOperator_of_physicalBudget hd R b hb hs A hbase
    (euclideanCoordinateDerivList [i] u) (contDiff_euclideanCoordinateDerivList hu _)
    (hasCompactSupport_euclideanCoordinateDerivList hus _)
  simp_rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rw [fullAmplitudeOperator_weak_transfer hd R b hb hs A hA i u hu hus φ, neg_neg]
  simp_rw [mul_add]
  exact integral_add ((φ.memLp 2).integrable_mul ht₂) ((φ.memLp 2).integrable_mul hd₂)

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: finite ordered
output derivatives of the actual bounded realization, tested against Schwartz
functions, equal the explicit `2 ^ s` branch sum of literal full operators.
Only `2 * (d + 1) + s` primitive physical derivatives are required. -/
theorem twoPositionL2Operator_iteratedLineDeriv_apply
    (hd : 0 < d) (R : ℝ)
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (A : ℝ)
    (is : List (Fin d))
    (hA : HasAmplitudeDerivativeBound b (2 * (d + 1) + is.length) A)
    (u : E → ℂ) (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u)
    (φ : 𝓢(E, ℂ)) :
    (orderedTransferAction (fun i ↦ lineDerivOp (EuclideanSpace.single i 1 : E)) is
      (twoPositionL2Operator hd R b hb hs A
        (amplitudeDerivativeBound_of_le hA (Nat.le_add_right _ _))
        ((hu.continuous.memLp_of_hasCompactSupport hus).toLp u) : 𝓢'(E, ℂ))) φ =
      ((orderedTransferTerms is).map fun p ↦ ∫ x, φ x * fullAmplitudeOperator
        (fun x y ξ ↦ iteratedTransferAmplitude b p.1 ξ (pairedPosition x y))
        (euclideanCoordinateDerivList p.2 u) x).sum := by
  induction is generalizing φ with
  | nil =>
    simpa [orderedTransferAction, orderedTransferTerms, iteratedTransferAmplitude,
      euclideanCoordinateDerivList] using
      twoPositionL2Operator_pairing_eq_fullAmplitudeOperator hd R b hb hs A hA u hu hus φ
  | cons i is ih =>
    have htail : HasAmplitudeDerivativeBound b (2 * (d + 1) + is.length) A :=
      amplitudeDerivativeBound_of_le hA (by simp only [List.length_cons]; omega)
    simp only [orderedTransferAction, TemperedDistribution.lineDerivOp_apply_apply, map_neg]
    rw [ih htail (lineDerivOp (EuclideanSpace.single i 1 : E) φ)]
    simp only [orderedTransferTerms, List.map_append, List.map_map,
      List.sum_append, Function.comp_def]
    rw [← List.sum_map_add, List.sum_neg]
    apply congrArg List.sum
    rw [List.map_map]
    apply List.map_congr_left
    intro p hp
    have hpcount := (orderedTransferTerms_spec is p hp).2.2
    have hbudget : HasAmplitudeDerivativeBound b
        ((2 * (d + 1) + 1) + p.1.length) A :=
      amplitudeDerivativeBound_of_le hA (by simp only [List.length_cons]; omega)
    have hpA := hasAmplitudeDerivativeBound_iteratedTransferAmplitude b
      (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) p.1
      (2 * (d + 1) + 1) A hbudget
    exact fullAmplitudeOperator_pairing_transfer hd R (iteratedTransferAmplitude b p.1)
      (contDiff_uncurry_iteratedTransferAmplitude hb p.1)
      (supportedInCenteredBox_iteratedTransferAmplitude b R hs p.1) (2 ^ p.1.length * A)
      hpA i (euclideanCoordinateDerivList p.2 u)
      (contDiff_euclideanCoordinateDerivList hu p.2)
      (hasCompactSupport_euclideanCoordinateDerivList hus p.2) φ

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: the actual bounded
operator attached to an enumerated branch. A branch with `k` datum derivatives
uses `s - k` transfers; its budget is derived from the original amplitude. -/
def orderedTransferTermL2Operator
    (hd : 0 < d) (R : ℝ)
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (A : ℝ)
    (is : List (Fin d))
    (hA : HasAmplitudeDerivativeBound b (2 * (d + 1) + is.length) A)
    (p : {p // p ∈ orderedTransferTerms is}) :
    Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  twoPositionL2Operator hd R (iteratedTransferAmplitude b p.val.1)
    (contDiff_uncurry_iteratedTransferAmplitude hb p.val.1)
    (supportedInCenteredBox_iteratedTransferAmplitude b R hs p.val.1)
    (2 ^ p.val.1.length * A)
    (hasAmplitudeDerivativeBound_iteratedTransferAmplitude b
      (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) p.val.1 (2 * (d + 1)) A
      (amplitudeDerivativeBound_of_le hA (Nat.add_le_add_left
        (orderedTransferTerms_spec is p.val p.property).1.length_le _)))

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: finite derivative
transfer for the actual L² realization as an equality of tempered distributions.
Each of the `2 ^ s` terms is the bounded realization of its full transferred
amplitude applied to its ordered datum derivative. -/
theorem twoPositionL2Operator_iteratedLineDeriv_transfer
    (hd : 0 < d) (R : ℝ)
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (A : ℝ)
    (is : List (Fin d))
    (hA : HasAmplitudeDerivativeBound b (2 * (d + 1) + is.length) A)
    (u : E → ℂ) (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u) :
    orderedTransferAction (fun i ↦ lineDerivOp (EuclideanSpace.single i 1 : E)) is
      (twoPositionL2Operator hd R b hb hs A
        (amplitudeDerivativeBound_of_le hA (Nat.le_add_right _ _))
        ((hu.continuous.memLp_of_hasCompactSupport hus).toLp u) : 𝓢'(E, ℂ)) =
      ((orderedTransferTerms is).attach.map fun p ↦
        (orderedTransferTermL2Operator hd R b hb hs A is hA p
          (((contDiff_euclideanCoordinateDerivList hu p.val.2).continuous.memLp_of_hasCompactSupport
            (hasCompactSupport_euclideanCoordinateDerivList hus p.val.2)).toLp
              (euclideanCoordinateDerivList p.val.2 u)) : 𝓢'(E, ℂ))).sum := by
  ext φ
  rw [twoPositionL2Operator_iteratedLineDeriv_apply hd R b hb hs A is hA u hu hus φ]
  let ev : 𝓢'(E, ℂ) →+ ℂ :=
    { toFun := fun v ↦ v φ, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
  change _ = ev _
  rw [map_list_sum, List.map_map]
  rw [← List.attach_map_val (l := orderedTransferTerms is)]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  exact (twoPositionL2Operator_pairing_eq_fullAmplitudeOperator hd R
    (iteratedTransferAmplitude b p.val.1)
    (contDiff_uncurry_iteratedTransferAmplitude hb p.val.1)
    (supportedInCenteredBox_iteratedTransferAmplitude b R hs p.val.1)
    (2 ^ p.val.1.length * A) _ (euclideanCoordinateDerivList p.val.2 u)
    (contDiff_euclideanCoordinateDerivList hu p.val.2)
    (hasCompactSupport_euclideanCoordinateDerivList hus p.val.2) φ).symm

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: the literal full
operator, embedded in tempered distributions using its proved L² integrability,
has the same finite derivative expansion into actual bounded operators. -/
theorem fullAmplitudeOperator_iteratedLineDeriv_transfer
    (hd : 0 < d) (R : ℝ)
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (A : ℝ)
    (is : List (Fin d))
    (hA : HasAmplitudeDerivativeBound b (2 * (d + 1) + is.length) A)
    (u : E → ℂ) (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u) :
    let hbase := amplitudeDerivativeBound_of_le hA (Nat.le_add_right _ _)
    let hv := memLp_fullAmplitudeOperator_of_physicalBudget hd R b hb hs A hbase u hu hus
    orderedTransferAction (fun i ↦ lineDerivOp (EuclideanSpace.single i 1 : E)) is
      (hv.toLp (fullAmplitudeOperator (fun x y ξ ↦ b ξ (pairedPosition x y)) u) : 𝓢'(E, ℂ)) =
      ((orderedTransferTerms is).attach.map fun p ↦
        (orderedTransferTermL2Operator hd R b hb hs A is hA p
          (((contDiff_euclideanCoordinateDerivList hu p.val.2).continuous.memLp_of_hasCompactSupport
            (hasCompactSupport_euclideanCoordinateDerivList hus p.val.2)).toLp
              (euclideanCoordinateDerivList p.val.2 u)) : 𝓢'(E, ℂ))).sum := by
  dsimp only
  have heq :
      ((memLp_fullAmplitudeOperator_of_physicalBudget hd R b hb hs A
        (amplitudeDerivativeBound_of_le hA (Nat.le_add_right _ _)) u hu hus).toLp
        (fullAmplitudeOperator (fun x y ξ ↦ b ξ (pairedPosition x y)) u) : 𝓢'(E, ℂ)) =
      (twoPositionL2Operator hd R b hb hs A
        (amplitudeDerivativeBound_of_le hA (Nat.le_add_right _ _))
        ((hu.continuous.memLp_of_hasCompactSupport hus).toLp u) : 𝓢'(E, ℂ)) := by
    ext φ
    rw [twoPositionL2Operator_pairing_eq_fullAmplitudeOperator hd R b hb hs A _ u hu hus φ]
    rw [Lp.toTemperedDistribution_apply]
    exact integral_congr_ae
      ((memLp_fullAmplitudeOperator_of_physicalBudget hd R b hb hs A
        (amplitudeDerivativeBound_of_le hA (Nat.le_add_right _ _)) u hu hus).coeFn_toLp.mono
        (fun x hx ↦ congrArg (fun z ↦ φ x * z) hx))
  rw [heq]
  exact twoPositionL2Operator_iteratedLineDeriv_transfer hd R b hb hs A is hA u hu hus

end JanetCartan.Pseudodifferential
