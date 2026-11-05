module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Translation.Matrix
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.Chart.Localization

/-!
# Support of the literal matrix PDO

The source-locality and output-support inputs to the periodic translation
commutator in `app:ch_background:prop:bg-inverse` follow entrywise through the
exact coordinate isometry. Their scalar producers use literal compact-frequency
kernels and strong limits, so these are properties of the actual full operator.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
open JanetCartan.AmplitudeBound JanetCartan.Pseudodifferential
open JanetCartan.PeriodicLocalL2 JanetCartan.Pseudodifferential.DifferentialChart

namespace JanetCartan.ContinuumCommutator

variable {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "P" => EuclideanSpace ℝ (Fin (2 * d))
local notation "VI" => EuclideanL2 d (EuclideanSpace ℂ I)
local notation "VJ" => EuclideanL2 d (EuclideanSpace ℂ J)

/-- Literal chart restriction commutes with the existing coordinate isometry
(`app:ch_background:prop:bg-inverse`). -/
theorem finiteL2CoordinateIsometry_chartProjection {K : Set E} (hK : MeasurableSet K)
    (u : VI) (r : I) :
    finiteL2CoordinateIsometry volume (chartProjection (𝕜 := ℂ) hK u) r =
      chartProjection (𝕜 := ℂ) hK (finiteL2CoordinateIsometry volume u r) := by
  apply Lp.ext
  filter_upwards [finiteL2Coordinates_apply_ae volume (chartProjection (𝕜 := ℂ) hK u) r,
    chartProjection_coe (𝕜 := ℂ) hK u,
    chartProjection_coe (𝕜 := ℂ) hK (finiteL2CoordinateIsometry volume u r),
    finiteL2Coordinates_apply_ae volume u r] with x hc hv hs hu
  change finiteL2CoordinateIsometry volume (chartProjection (𝕜 := ℂ) hK u) r x = _ at hc
  change finiteL2CoordinateIsometry volume u r x = _ at hu
  rw [hc, hv, hs]
  by_cases hx : x ∈ K
  · simpa only [Set.indicator_of_mem hx] using hu.symm
  · simp only [Set.indicator_of_notMem hx, PiLp.zero_apply]

/-- Source locality of the full matrix PDO on arbitrary L² inputs, with its
support premise discharged from the amplitude (`app:ch_background:prop:bg-inverse`). -/
theorem vectorTwoPositionL2Operator_congr_on_source
    (hd : 0 < d) (R : ℝ) (b : E → P → Matrix I J ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ r s, SupportedInCenteredBox R (fun z ↦ b ξ z r s)) (A : ℝ)
    (hA : ∀ r s, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z r s) (2 * (d + 1)) A)
    (u v : VJ)
    (huv : ∀ᵐ y ∂volume, y ∈ chartBox R → u y = v y) :
    vectorTwoPositionL2Operator hd R b hb hs A hA u =
      vectorTwoPositionL2Operator hd R b hb hs A hA v := by
  apply (finiteL2CoordinateIsometry volume).injective
  apply PiLp.ext
  intro r
  simp only [vectorTwoPositionL2Operator,
    finiteL2CoordinateIsometry_vectorMatrixL2Operator, matrixOperator_apply]
  apply Finset.sum_congr rfl
  intro s _
  apply twoPositionL2Operator_congr_on_source
  filter_upwards [huv, finiteL2Coordinates_apply_ae volume u s,
    finiteL2Coordinates_apply_ae volume v s] with y hy hu hv hyK
  exact hu.trans ((congrArg (fun w : EuclideanSpace ℂ J ↦ w s) (hy hyK)).trans hv.symm)

/-- Output support of the full matrix PDO on arbitrary L² inputs, obtained
from the scalar strong-limit construction (`app:ch_background:prop:bg-inverse`). -/
theorem vectorTwoPositionL2Operator_supported
    (hd : 0 < d) (R : ℝ) (b : E → P → Matrix I J ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ r s, SupportedInCenteredBox R (fun z ↦ b ξ z r s)) (A : ℝ)
    (hA : ∀ r s, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z r s) (2 * (d + 1)) A)
    (u : VJ) :
    ∀ᵐ x ∂volume, x ∉ chartBox R → vectorTwoPositionL2Operator hd R b hb hs A hA u x = 0 := by
  have hK := (isCompact_chartBox (d := d) R).isClosed.measurableSet
  have hp : chartProjection (𝕜 := ℂ) hK
      (vectorTwoPositionL2Operator hd R b hb hs A hA u) =
        vectorTwoPositionL2Operator hd R b hb hs A hA u := by
    apply (finiteL2CoordinateIsometry volume).injective
    apply PiLp.ext
    intro r
    rw [finiteL2CoordinateIsometry_chartProjection]
    simp only [vectorTwoPositionL2Operator,
      finiteL2CoordinateIsometry_vectorMatrixL2Operator, matrixOperator_apply, map_sum]
    apply Finset.sum_congr rfl
    intro s _
    exact chartProjection_eq_self hK _
      (twoPositionL2Operator_supported hd R (fun ξ z ↦ b ξ z r s)
        ((matrixEntryEvaluation r s).contDiff.comp hb) (fun ξ ↦ hs ξ r s) A (hA r s) _)
  rw [← hp]
  exact chartProjection_supported hK _

end JanetCartan.ContinuumCommutator
