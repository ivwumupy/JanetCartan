module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.PaperEstimates.RowApplication.FiniteRegularity.Operator
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.PaperEstimates.RowKernel
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-!
# Original kernels under finite physical regularity

The finite `C^ell` construction in `app:ch_osc:eq:amplitude-row` is identified
with its literal original amplitude times kernel.  The natural L¹∩L² core
is sufficient, so no absolute-convergence assumption is imposed on all L²
data for Fourier kernels.  The supplied-channel norm consequence is also
recorded for the original compact-cutoff channels.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter
open scoped ENNReal Topology

namespace JanetCartan.AmplitudeBound.PaperEstimates

variable {d : ℕ} {X : Type*} [MeasurableSpace X] {μ : Measure X}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "Mode" => Fin d → ℤ
local notation "Output" => Lp ℂ 2 (volume : Measure E)

variable (R : ℝ) (b : X → EuclideanSpace ℝ (Fin d) → ℂ) (hb : StronglyMeasurable (Function.uncurry b))
  (hc : ∀ u, ContDiff ℝ (d / 2 + 1 : ℕ) (b u))
  (hs : ∀ u, SupportedInCenteredBox R (b u))
  (A : ℝ) (hA : 0 ≤ A)
  (hjet : ∀ u (is : List (Fin d)), is.length ≤ d / 2 + 1 → ∀ x,
    ‖euclideanCoordinateDerivList is (b u) x‖ ≤ A)

/-- The actual finite-regularity row has the original multiplied kernel
whenever the original kernel action is integrable for this input
(`app:ch_osc:eq:amplitude-row`). -/
theorem finiteRegularityRowAmplitudeOperator_ae_kernel
    (T : Lp ℂ 2 μ →L[ℂ] Output) (K : E → X → ℂ) (f : Lp ℂ 2 μ)
    (hKint : ∀ᵐ x ∂volume, Integrable (fun u ↦ K x u * f u) μ)
    (hT : ∀ k, T (multiplicationOperator (finiteRegularityRowSymbol R b hb hc hs A hA hjet k) f) =ᵐ[volume]
      fun x ↦ ∫ u, K x u * (multiplicationOperator
        (finiteRegularityRowSymbol R b hb hc hs A hA hjet k) f) u ∂μ) :
    finiteRegularityRowAmplitudeOperator R b hb hc hs A hA hjet T f =ᵐ[volume]
      fun x ↦ ∫ u, b u x * K x u * f u ∂μ := by
  obtain ⟨s, _, hs'⟩ := exists_seq_monotone_tendsto_atTop_atTop (Finset Mode)
  exact RowKernel.cutoff_row_operator_ae_kernel_of_strong_limit T
    (finiteRegularityRowAmplitudeOperator R b hb hc hs A hA hjet T)
    (finiteRegularityRowSymbol R b hb hc hs A hA hjet) (rowFourierCoefficient R b)
    (fun k ↦ (stronglyMeasurable_rowFourierCoefficient R b hb k).aestronglyMeasurable)
    (finiteRowAmplitudeConstant d R * A)
    (fun u ↦ (rowFourierCoefficient_absolute_sum_bound_of_finiteRegularity R b hc hs A hA hjet u).1)
    (fun u ↦ (rowFourierCoefficient_absolute_sum_bound_of_finiteRegularity R b hc hs A hA hjet u).2)
    (finiteRegularityRowSymbol_coeFn R b hb hc hs A hA hjet)
    (scaledTorusChart (amplitudeBoxScale R)) (measurable_scaledTorusChart _)
    (boxCellCutoff (amplitudeBoxScale R)) (aestronglyMeasurable_boxCellCutoff _)
    (Eventually.of_forall (norm_boxCellCutoff_le _)) b
    (rowFourierCoefficient_hasSum_of_finiteRegularity R b hc hs A hA hjet)
    s hs' K f hKint hT
    (tendsto_finiteRegularityRowAmplitudeOperator_apply R b hb hc hs A hA hjet T f s hs')

/-- Literal original kernel on the natural integrable L² core; bounded
coefficient multiplication preserves that core
(`app:ch_osc:eq:amplitude-row`). -/
theorem finiteRegularityRowAmplitudeOperator_ae_kernel_on_L1_core
    (T : Lp ℂ 2 μ →L[ℂ] Output) (K : E → X → ℂ)
    (hT : ∀ g : Lp ℂ 2 μ, Integrable (g : X → ℂ) μ →
      T g =ᵐ[volume] fun x ↦ ∫ u, K x u * g u ∂μ)
    (f : Lp ℂ 2 μ) (hf : Integrable (f : X → ℂ) μ)
    (hKint : ∀ᵐ x ∂volume, Integrable (fun u ↦ K x u * f u) μ) :
    finiteRegularityRowAmplitudeOperator R b hb hc hs A hA hjet T f =ᵐ[volume]
      fun x ↦ ∫ u, b u x * K x u * f u ∂μ := by
  apply finiteRegularityRowAmplitudeOperator_ae_kernel R b hb hc hs A hA hjet T K f hKint
  intro k
  apply hT
  exact (hf.mul_of_top_right (Lp.memLp
    (finiteRegularityRowSymbol R b hb hc hs A hA hjet k))).congr
    (multiplicationOperator_coeFn _ f).symm

include hb hc hs hA hjet in
/-- The finite physical `C^ell` input constructs the actual bounded row
and its original core kernel, without Sobolev or coefficient hypotheses
(`app:ch_osc:eq:amplitude-row`). -/
theorem exists_rowAmplitudeOperator_of_finiteRegularity
    (T : Lp ℂ 2 μ →L[ℂ] Output) :
    ∃ S : Lp ℂ 2 μ →L[ℂ] Output,
      ‖S‖ ≤ finiteRowAmplitudeConstant d R * ‖T‖ * A ∧
      ∀ (K : E → X → ℂ),
        (∀ g : Lp ℂ 2 μ, Integrable (g : X → ℂ) μ →
          T g =ᵐ[volume] fun x ↦ ∫ u, K x u * g u ∂μ) →
        ∀ (f : Lp ℂ 2 μ), Integrable (f : X → ℂ) μ →
          (∀ᵐ x ∂volume, Integrable (fun u ↦ K x u * f u) μ) →
            S f =ᵐ[volume] fun x ↦ ∫ u, b u x * K x u * f u ∂μ :=
  ⟨finiteRegularityRowAmplitudeOperator R b hb hc hs A hA hjet T,
    norm_finiteRegularityRowAmplitudeOperator_le R b hb hc hs A hA hjet T,
    finiteRegularityRowAmplitudeOperator_ae_kernel_on_L1_core R b hb hc hs A hA hjet T⟩

include hb hc hs hA hjet in
/-- The finite-regularity row estimate applies to the same already
constructed cutoff channel via its literal kernel. In particular an
amplitude difference needs only physical derivatives through `ell`
(`app:ch_osc:prop:osc-normal`). -/
theorem norm_integralRowAmplitudeOperator_le_of_finiteRegularity
    (T S : Lp ℂ 2 μ →L[ℂ] Output) (K : E → X → ℂ)
    (hKint : ∀ f : Lp ℂ 2 μ, ∀ᵐ x ∂volume,
      Integrable (fun u ↦ K x u * f u) μ)
    (hT : ∀ f : Lp ℂ 2 μ, T f =ᵐ[volume] fun x ↦ ∫ u, K x u * f u ∂μ)
    (hS : ∀ f : Lp ℂ 2 μ, S f =ᵐ[volume] fun x ↦ ∫ u, b u x * K x u * f u ∂μ) :
    ‖S‖ ≤ finiteRowAmplitudeConstant d R * ‖T‖ * A := by
  have he : S = finiteRegularityRowAmplitudeOperator R b hb hc hs A hA hjet T := by
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    exact (hS f).trans (finiteRegularityRowAmplitudeOperator_ae_kernel R b hb hc hs A hA hjet
      T K f (hKint f) (fun _ ↦ hT _)).symm
  rw [he]
  exact norm_finiteRegularityRowAmplitudeOperator_le R b hb hc hs A hA hjet T

end JanetCartan.AmplitudeBound.PaperEstimates
