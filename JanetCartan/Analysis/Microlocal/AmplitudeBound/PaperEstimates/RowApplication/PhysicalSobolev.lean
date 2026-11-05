module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.PaperEstimates.RowApplication.Kernel
public import JanetCartan.Analysis.Fourier.Conventions.PhysicalSobolev

/-!
# The sharp row bound with the manuscript's physical Sobolev norm

The actual original input is `‖⟨D⟩^ell b(·,u)‖₂`, where `D=-i∂`.
Its unitary Fourier expression has weight `⟨2πξ⟩^ell`. The smaller
unit-period weight needed by the coefficient construction follows
from the checked convention comparison, with no derivative loss.
Consumer: `app:ch_osc:eq:amplitude-row`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory FourierTransform
open scoped ENNReal

namespace JanetCartan.AmplitudeBound.PaperEstimates

open Pseudodifferential FourierConventions

variable {d : ℕ} {X : Type*} [MeasurableSpace X] {μ : Measure X}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "Output" => Lp ℂ 2 (volume : Measure E)

/-- The actual operator in the sharp row estimate, starting from the
paper's physical Sobolev norm. The quantitative constant was fixed
from dimension and support before the source measure, original
operator, or amplitude was supplied. Kernel interpretation is on the
natural integrable-L² core (`app:ch_osc:eq:amplitude-row`). -/
theorem exists_rowAmplitudeOperator_of_physicalSobolev
    (R : ℝ) (b : X → E → ℂ) (hb : StronglyMeasurable (Function.uncurry b))
    (hc : ∀ u, Continuous (b u)) (hs : ∀ u, SupportedInCenteredBox R (b u))
    (hm : ∀ u, MemLp (b u) 2 volume)
    (hphys : ∀ u, MemLp (fun ξ ↦ euclideanSobolevWeight (d / 2 + 1 : ℕ)
      ((2 * Real.pi) • ξ) • (𝓕 ((hm u).toLp (b u)) : Output) ξ) 2 volume)
    (A : ℝ) (hA : 0 ≤ A)
    (hbound : ∀ u, (eLpNorm (fun ξ ↦ euclideanSobolevWeight (d / 2 + 1 : ℕ)
      ((2 * Real.pi) • ξ) • (𝓕 ((hm u).toLp (b u)) : Output) ξ) 2 volume).toReal ≤ A)
    (T : Lp ℂ 2 μ →L[ℂ] Output) :
    ∃ S : Lp ℂ 2 μ →L[ℂ] Output,
      ‖S‖ ≤ rowAmplitudeConstant d R * ‖T‖ * A ∧
      ∀ (K : E → X → ℂ),
        (∀ g : Lp ℂ 2 μ, Integrable (g : X → ℂ) μ →
          T g =ᵐ[volume] fun x ↦ ∫ u, K x u * g u ∂μ) →
        ∀ (f : Lp ℂ 2 μ), Integrable (f : X → ℂ) μ →
          (∀ᵐ x ∂volume, Integrable (fun u ↦ K x u * f u) μ) →
            S f =ᵐ[volume] fun x ↦ ∫ u, b u x * K x u * f u ∂μ := by
  have hHs (u : X) := (fourierSobolev_of_physical_weight (d / 2 + 1)
    ((hm u).toLp (b u)) (hphys u)).1
  have hrow (u : X) : fourierSobolevNorm (d / 2 + 1 : ℕ) ((hm u).toLp (b u)) ≤ A :=
    (fourierSobolev_of_physical_weight (d / 2 + 1) ((hm u).toLp (b u)) (hphys u)).2.trans
      (hbound u)
  refine ⟨compactRowAmplitudeOperator R b hb hs hm hHs A hA hrow T,
    norm_compactRowAmplitudeOperator_le R b hb hs hm hHs A hA hrow T, ?_⟩
  intro K hT f hf hKint
  exact compactRowAmplitudeOperator_ae_kernel_on_L1_core R b hb hc hs hm hHs A hA hrow
    T K hT f hf hKint

/-- The physical-norm row estimate for an already constructed channel
with its original multiplied kernel. This is the same-phase amplitude
difference application in `app:ch_osc:lem:osc-amplitude`; no derivatives
in the input parameter are required. -/
theorem norm_integralRowAmplitudeOperator_le_of_physicalSobolev
    (R : ℝ) (b : X → E → ℂ) (hb : StronglyMeasurable (Function.uncurry b))
    (hc : ∀ u, Continuous (b u)) (hs : ∀ u, SupportedInCenteredBox R (b u))
    (hm : ∀ u, MemLp (b u) 2 volume)
    (hphys : ∀ u, MemLp (fun ξ ↦ euclideanSobolevWeight (d / 2 + 1 : ℕ)
      ((2 * Real.pi) • ξ) • (𝓕 ((hm u).toLp (b u)) : Output) ξ) 2 volume)
    (A : ℝ) (hA : 0 ≤ A)
    (hbound : ∀ u, (eLpNorm (fun ξ ↦ euclideanSobolevWeight (d / 2 + 1 : ℕ)
      ((2 * Real.pi) • ξ) • (𝓕 ((hm u).toLp (b u)) : Output) ξ) 2 volume).toReal ≤ A)
    (T S : Lp ℂ 2 μ →L[ℂ] Output) (K : E → X → ℂ)
    (hKint : ∀ f : Lp ℂ 2 μ, ∀ᵐ x ∂volume,
      Integrable (fun u ↦ K x u * f u) μ)
    (hT : ∀ f : Lp ℂ 2 μ, T f =ᵐ[volume] fun x ↦ ∫ u, K x u * f u ∂μ)
    (hS : ∀ f : Lp ℂ 2 μ, S f =ᵐ[volume] fun x ↦ ∫ u, b u x * K x u * f u ∂μ) :
    ‖S‖ ≤ rowAmplitudeConstant d R * ‖T‖ * A := by
  exact norm_integralRowAmplitudeOperator_le R b hb hc hs hm
    (fun u ↦ (fourierSobolev_of_physical_weight (d / 2 + 1) ((hm u).toLp (b u)) (hphys u)).1)
    A hA (fun u ↦
      (fourierSobolev_of_physical_weight (d / 2 + 1) ((hm u).toLp (b u)) (hphys u)).2.trans
        (hbound u)) T S K hKint hT hS

end JanetCartan.AmplitudeBound.PaperEstimates
