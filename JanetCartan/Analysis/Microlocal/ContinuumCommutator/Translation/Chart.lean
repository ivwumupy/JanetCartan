module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Translation.Chart.Translation
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Translation.Chart.Support

/-!
# Periodic chart transfer of the full matrix translation commutator

The order-one difference-quotient justification in
`app:ch_background:prop:bg-inverse`. Both physical positions translate. The
buffered support, literal Lebesgue L² construction, normalized torus measure,
and positive periodic translation convention are retained throughout.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
open JanetCartan.AmplitudeBound JanetCartan.Pseudodifferential
open JanetCartan.PeriodicLocalL2 JanetCartan.Pseudodifferential.DifferentialChart

namespace JanetCartan.ContinuumCommutator

variable {d : ℕ} {I : Type} [Fintype I]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "P" => EuclideanSpace ℝ (Fin (2 * d))
local notation "V" => EuclideanSpace ℂ I
local notation "L²" => EuclideanL2 d V

/-- The actual matrix PDO conjugation transfers to the periodic chart. The
source-locality and output-support hypotheses are proved from the amplitude,
including the cell-boundary case (`app:ch_background:prop:bg-inverse`). -/
theorem periodicTranslation_transfer_vectorTwoPositionL2Operator
    (hd : 0 < d) (R h₀ : ℝ) (b : E → P → Matrix I I ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ r s, SupportedInCenteredBox R (fun z ↦ b ξ z r s)) (A : ℝ)
    (hA : ∀ r s, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z r s) (2 * (d + 1)) A)
    (hbuffer : R + h₀ < 1 / 2) (i : Fin d) (h : ℝ) (hsmall : |h| ≤ h₀)
    (u : PeriodicL2 d V) :
    periodicL2Translation (periodicCoordinateShift i h)
      (transferOperator (vectorTwoPositionL2Operator hd R b hb hs A hA)
        (periodicL2Translation (-periodicCoordinateShift i h) u)) =
      toTorus (𝕜 := ℂ) (euclideanVectorL2Translation (h • EuclideanSpace.single i 1)
        (vectorTwoPositionL2Operator hd R b hb hs A hA
          (euclideanVectorL2Translation (-(h • EuclideanSpace.single i 1))
            (toEuclidean (𝕜 := ℂ) u)))) := by
  let a : E := h • EuclideanSpace.single i 1
  have hq : torusQuotient a = periodicCoordinateShift i h :=
    torusQuotient_coordinateShift i h
  have hqn : torusQuotient (-a) = -periodicCoordinateShift i h := by
    rw [← hq]
    ext j
    exact AddCircle.coe_neg 1
  have hcell : chartBox R ⊆ halfOpenCell d :=
    chartBox_subset_cell (by linarith [(abs_nonneg h).trans hsmall])
  have hshift (x : E) (hx : x ∈ chartBox R) : x - a ∈ halfOpenCell d := by
    simpa only [a, neg_smul, sub_eq_add_neg] using
      chartBox_add_coordinateShift_mem_cell hbuffer
        (show |-h| ≤ h₀ by simpa only [abs_neg] using hsmall) i hx
  change periodicL2Translation (periodicCoordinateShift i h)
    (toTorus (𝕜 := ℂ) (vectorTwoPositionL2Operator hd R b hb hs A hA
      (toEuclidean (𝕜 := ℂ) (periodicL2Translation (-periodicCoordinateShift i h) u)))) = _
  rw [← hq, toTorus_vectorTranslation_of_supported hcell a hshift _
    (vectorTwoPositionL2Operator_supported hd R b hb hs A hA _)]
  congr 2
  apply vectorTwoPositionL2Operator_congr_on_source
  rw [hq, ← hqn]
  exact toEuclidean_periodicTranslation_eq_on_chart hcell (-a)
    (fun x hx ↦ by simpa only [sub_eq_add_neg] using hshift x hx) u

/-- Exact transfer of the full two-position matrix divided commutator from
Lebesgue L² to normalized torus L² (`app:ch_background:prop:bg-inverse`).
The primitive entry budget supplies the lower budget of the original PDO. -/
theorem periodicConjugationDifference_transfer_twoPosition_eq
    (hd : 0 < d) (R h₀ : ℝ) (b : E → P → Matrix I I ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ r s, SupportedInCenteredBox R (fun z ↦ b ξ z r s)) (A : ℝ)
    (hA : ∀ r s, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z r s)
      (2 * (d + 1) + 1) A)
    (hbuffer : R + h₀ < 1 / 2) (i : Fin d) (h : ℝ) (hh : h ≠ 0)
    (hsmall : |h| ≤ h₀) :
    periodicConjugationDifference
      ((transferOperator (vectorTwoPositionL2Operator hd R b hb hs A
        (fun r s ξ is his ↦ hA r s ξ is (Nat.le_succ_of_le his)))).restrictScalars ℝ) i h =
      (transferOperator (vectorMatrixL2Operator (fun r s ↦
        translationDifferenceL2Operator hd R h₀ (fun ξ z ↦ b ξ z r s)
          ((matrixEntryEvaluation r s).contDiff.comp hb) (fun ξ ↦ hs ξ r s)
          A (hA r s) i h hh hsmall))).restrictScalars ℝ := by
  ext1 u
  let B := vectorTwoPositionL2Operator hd R b hb hs A
    (fun r s ξ is his ↦ hA r s ξ is (Nat.le_succ_of_le his))
  change h⁻¹ • (periodicL2Translation (periodicCoordinateShift i h)
    (transferOperator B (periodicL2Translation (-periodicCoordinateShift i h) u)) -
      transferOperator B u) = _
  dsimp only [B]
  rw [periodicTranslation_transfer_vectorTwoPositionL2Operator hd R h₀ b hb hs A
    (fun r s ξ is his ↦ hA r s ξ is (Nat.le_succ_of_le his)) hbuffer i h hsmall u]
  have he := congrArg (fun T : L² →L[ℂ] L² ↦
    toTorus (𝕜 := ℂ) (T (toEuclidean (𝕜 := ℂ) u)))
      (euclideanVectorConjugationDifference_twoPosition_eq hd R h₀ b hb hs A hA
        i h hh hsmall)
  simpa only [transferOperator, ContinuousLinearMap.coe_restrictScalars',
    euclideanVectorConjugationDifference, smul_apply,
    sub_apply, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, map_sub,
    (toTorus (𝕜 := ℂ)).map_smul_of_tower] using he

/-- The uniform periodic matrix commutator bound from the fixed enlarged
chart and the primitive amplitude budget (`app:ch_background:prop:bg-inverse`).
There is no inverse power of the translation step in this bound. -/
theorem norm_periodicConjugationDifference_transfer_twoPosition_le
    (hd : 0 < d) (R h₀ : ℝ) (b : E → P → Matrix I I ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ r s, SupportedInCenteredBox R (fun z ↦ b ξ z r s)) (A : ℝ)
    (hA : ∀ r s, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z r s)
      (2 * (d + 1) + 1) A)
    (hbuffer : R + h₀ < 1 / 2) (i : Fin d) (h : ℝ) (hh : h ≠ 0)
    (hsmall : |h| ≤ h₀) :
    ‖periodicConjugationDifference
      ((transferOperator (vectorTwoPositionL2Operator hd R b hb hs A
        (fun r s ξ is his ↦ hA r s ξ is (Nat.le_succ_of_le his)))).restrictScalars ℝ) i h‖ ≤
      (Fintype.card I : ℝ) ^ 2 * (fixedBoxAmplitudeConstant d (R + h₀) * (2 * A)) := by
  rw [periodicConjugationDifference_transfer_twoPosition_eq hd R h₀ b hb hs A hA
    hbuffer i h hh hsmall, ContinuousLinearMap.norm_restrictScalars]
  apply (norm_transferOperator_le _).trans
  simpa only [pow_two] using norm_vectorMatrixL2Operator_le_of_entry_bound _ _
    (fun r s ↦ norm_translationDifferenceL2Operator_le hd R h₀ (fun ξ z ↦ b ξ z r s)
      ((matrixEntryEvaluation r s).contDiff.comp hb) (fun ξ ↦ hs ξ r s)
      A (hA r s) i h hh hsmall)

end JanetCartan.ContinuumCommutator
