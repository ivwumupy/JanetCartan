module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.PaperEstimates.RowApplication.Basic
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.PaperEstimates.RowKernel
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-!
# The original kernel of the sharp row operator

The literal finite coefficient operators converge in operator norm by
the proved Sobolev column and diagonal estimates. Their actual kernels
converge by the proved uniform absolute coefficient bound. Thus the
constructed operator has kernel `b(x,u) K(x,u)` on its natural domain.
No parameterwise almost-everywhere identity is evaluated on a diagonal.
Consumer: `app:ch_osc:eq:amplitude-row`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter
open scoped ENNReal Topology

namespace JanetCartan.AmplitudeBound.PaperEstimates

open Pseudodifferential RowCoefficients DiagonalTrace

variable {d : ℕ} {X : Type*} [MeasurableSpace X] {μ : Measure X}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "Mode" => Fin d → ℤ
local notation "Output" => Lp ℂ 2 (volume : Measure E)

variable (R : ℝ) (b : X → EuclideanSpace ℝ (Fin d) → ℂ)
  (hb : StronglyMeasurable (Function.uncurry b))
  (hc : ∀ u, Continuous (b u))
  (hs : ∀ u, SupportedInCenteredBox R (b u))
  (hm : ∀ u, MemLp (b u) 2 volume)
  (hHs : ∀ u, MemFourierSobolev (d / 2 + 1 : ℕ) ((hm u).toLp (b u)))
  (A : ℝ) (hA : 0 ≤ A)
  (hbound : ∀ u, fourierSobolevNorm (d / 2 + 1 : ℕ) ((hm u).toLp (b u)) ≤ A)

include hc hs hm hHs in
omit [MeasurableSpace X] in
/-- The actual original Fourier coefficients reconstruct the original
continuous Sobolev row with the literal output modulations
(`app:ch_osc:eq:amplitude-row`). -/
theorem rowFourierCoefficient_hasSum (u : X) (x : E) :
    HasSum (fun k ↦ boxCellCutoff (amplitudeBoxScale R) x *
      UnitAddTorus.mFourier k (scaledTorusChart (amplitudeBoxScale R) x) *
        rowFourierCoefficient R b k u) (b u x) := by
  have h := actual_row_fourier_hasSum_cutoff R (d / 2 + 1) (by omega)
    (b u) (hc u) (hs u) (hm u) (hHs u) x
  convert h using 1
  funext k
  unfold rowFourierCoefficient
  ring

/-- Actual finite row operators converge strongly along any cofinal
sequence of Fourier modes, with the same original amplitude and input
(`app:ch_osc:eq:amplitude-row`). -/
theorem tendsto_compactRowAmplitudeOperator_apply
    (T : Lp ℂ 2 μ →L[ℂ] Output) (f : Lp ℂ 2 μ)
    (s : ℕ → Finset Mode) (hs' : Tendsto s atTop atTop) :
    Tendsto (fun N ↦ finiteRowAmplitudeOperator (rowPhysicalModulation R) T
      (rowCoefficientSymbol R b hb hs hm hHs A hA hbound) (s N) f) atTop
        (𝓝 (compactRowAmplitudeOperator R b hb hs hm hHs A hA hbound T f)) := by
  exact ((show Continuous (fun P : Lp ℂ 2 μ →L[ℂ] Output ↦ P f) by
    fun_prop).continuousAt.tendsto.comp
      ((tendsto_compactRowAmplitudeOperator R b hb hs hm hHs A hA hbound T).comp hs'))

include hc in
/-- The constructed sharp row operator has the original amplitude times
the original kernel. Only this input's original kernel integrability
and the original operator's identities on its multiplied inputs enter
the kernel interpretation (`app:ch_osc:eq:amplitude-row`). -/
theorem compactRowAmplitudeOperator_ae_kernel
    (T : Lp ℂ 2 μ →L[ℂ] Output) (K : E → X → ℂ) (f : Lp ℂ 2 μ)
    (hKint : ∀ᵐ x ∂volume, Integrable (fun u ↦ K x u * f u) μ)
    (hT : ∀ k, T (multiplicationOperator
        (rowCoefficientSymbol R b hb hs hm hHs A hA hbound k) f) =ᵐ[volume]
      fun x ↦ ∫ u, K x u * (multiplicationOperator
        (rowCoefficientSymbol R b hb hs hm hHs A hA hbound k) f) u ∂μ) :
    compactRowAmplitudeOperator R b hb hs hm hHs A hA hbound T f =ᵐ[volume]
      fun x ↦ ∫ u, b u x * K x u * f u ∂μ := by
  obtain ⟨s, _, hs'⟩ := exists_seq_monotone_tendsto_atTop_atTop (Finset Mode)
  exact RowKernel.cutoff_row_operator_ae_kernel_of_strong_limit T
    (compactRowAmplitudeOperator R b hb hs hm hHs A hA hbound T)
    (rowCoefficientSymbol R b hb hs hm hHs A hA hbound)
    (rowFourierCoefficient R b)
    (fun k ↦ (stronglyMeasurable_rowFourierCoefficient R b hb k).aestronglyMeasurable)
    (rowAmplitudeConstant d R * A)
    (fun u ↦ (rowFourierCoefficient_absolute_sum_bound R b hs hm hHs A hA hbound u).1)
    (fun u ↦ (rowFourierCoefficient_absolute_sum_bound R b hs hm hHs A hA hbound u).2)
    (rowCoefficientSymbol_coeFn R b hb hs hm hHs A hA hbound)
    (scaledTorusChart (amplitudeBoxScale R)) (measurable_scaledTorusChart _)
    (boxCellCutoff (amplitudeBoxScale R)) (aestronglyMeasurable_boxCellCutoff _)
    (Eventually.of_forall (norm_boxCellCutoff_le _)) b
    (rowFourierCoefficient_hasSum R b hc hs hm hHs) s hs' K f hKint hT
    (tendsto_compactRowAmplitudeOperator_apply R b hb hs hm hHs A hA hbound T f s hs')

include hc in
/-- Natural integrable-L²-core kernel formula for the constructed sharp
row operator. In particular this permits Fourier kernels without
asserting absolute kernel integration on every L² input
(`app:ch_osc:eq:amplitude-row`). -/
theorem compactRowAmplitudeOperator_ae_kernel_on_L1_core
    (T : Lp ℂ 2 μ →L[ℂ] Output) (K : E → X → ℂ)
    (hT : ∀ g : Lp ℂ 2 μ, Integrable (g : X → ℂ) μ →
      T g =ᵐ[volume] fun x ↦ ∫ u, K x u * g u ∂μ)
    (f : Lp ℂ 2 μ) (hf : Integrable (f : X → ℂ) μ)
    (hKint : ∀ᵐ x ∂volume, Integrable (fun u ↦ K x u * f u) μ) :
    compactRowAmplitudeOperator R b hb hs hm hHs A hA hbound T f =ᵐ[volume]
      fun x ↦ ∫ u, b u x * K x u * f u ∂μ := by
  apply compactRowAmplitudeOperator_ae_kernel R b hb hc hs hm hHs A hA hbound T K f hKint
  intro k
  apply hT
  exact (hf.mul_of_top_right (Lp.memLp
    (rowCoefficientSymbol R b hb hs hm hHs A hA hbound k))).congr
      (multiplicationOperator_coeFn _ f).symm

include hb hc hs hm hHs hA hbound in
/-- Apply the sharp row estimate to an already supplied integral
operator with the literal multiplied kernel. The original operator
and its kernel are retained; no independent output witness enters the
consumer (`app:ch_osc:eq:amplitude-row`). Compact input cutoffs in the
normal-channel application supply the displayed kernel integrability. -/
theorem norm_integralRowAmplitudeOperator_le
    (T S : Lp ℂ 2 μ →L[ℂ] Output) (K : E → X → ℂ)
    (hKint : ∀ f : Lp ℂ 2 μ, ∀ᵐ x ∂volume,
      Integrable (fun u ↦ K x u * f u) μ)
    (hT : ∀ f : Lp ℂ 2 μ, T f =ᵐ[volume]
      fun x ↦ ∫ u, K x u * f u ∂μ)
    (hS : ∀ f : Lp ℂ 2 μ, S f =ᵐ[volume]
      fun x ↦ ∫ u, b u x * K x u * f u ∂μ) :
    ‖S‖ ≤ rowAmplitudeConstant d R * ‖T‖ * A := by
  have he : S = compactRowAmplitudeOperator R b hb hs hm hHs A hA hbound T := by
    ext f
    exact (hS f).trans (compactRowAmplitudeOperator_ae_kernel R b hb hc hs hm hHs A hA
      hbound T K f (hKint f) (fun _ ↦ hT _)).symm
  rw [he]
  exact norm_compactRowAmplitudeOperator_le R b hb hs hm hHs A hA hbound T

end JanetCartan.AmplitudeBound.PaperEstimates
