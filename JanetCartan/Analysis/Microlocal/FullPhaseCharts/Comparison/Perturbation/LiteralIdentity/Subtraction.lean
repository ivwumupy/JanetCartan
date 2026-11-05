module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Comparison.Perturbation.IntegralCalculus

/-!
# Subtraction of locally smooth phase kernel integrals

The comparison in `app:ch_seed:prop:seed-phase-charts` applies the mixed kernel
to the phase error. Smoothness on the open phase domain supplies integrability
for both segment integrals in `app:ch_seed:eq:seed-quotient-integral`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ContDiff

namespace JanetCartan.FullPhaseCharts.Comparison

variable {P X E : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [CompleteSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance literalSubtractionNormedSpaceX : NormedSpace ℝ X := InnerProductSpace.toNormedSpace

private theorem contDiffOn_phaseChartKernel_segments
    {S : X × E → ℝ} {ζ : P × ℝ → E} {ε : ℝ}
    {Ω : Set (X × E)} {W : Set ℝ} (hΩ : IsOpen Ω)
    (hS : ContDiffOn ℝ ∞ S Ω) (q : P × (X × X) × (ℝ × E))
    (hmem : ∀ r ∈ W, ∀ s ∈ W, phaseChartPoint ζ ε q r s ∈ Ω) :
    ContDiffOn ℝ ∞ (fun a : ℝ × ℝ ↦ phaseChartKernel S ζ ε q a.1 a.2) (W ×ˢ W) := by
  intro a ha
  have hK := contDiffAt_phaseMixedKernel
    (hS.contDiffAt (hΩ.mem_nhds (hmem a.1 ha.1 a.2 ha.2)))
  have hp : ContDiffAt ℝ ∞ (fun a : ℝ × ℝ ↦ phaseChartPoint ζ ε q a.1 a.2) a := by
    unfold phaseChartPoint
    fun_prop
  exact ((hK.comp a hp).clm_apply contDiffAt_const).contDiffWithinAt

/-- Subtraction commutes with the two mixed-Hessian integrals for locally smooth
phases (`app:ch_seed:prop:seed-phase-charts`). Integrability is derived from
smoothness; it is not an additional comparison hypothesis. -/
theorem phaseChartKernelIntegral_sub
    {S S₀ : X × E → ℝ} {ζ : P × ℝ → E} {ε : ℝ}
    {Ω : Set (X × E)} {W : Set ℝ} (hΩ : IsOpen Ω) (hW : IsOpen W)
    (hIW : Icc (0 : ℝ) 1 ⊆ W)
    (hS : ContDiffOn ℝ ∞ S Ω) (hS₀ : ContDiffOn ℝ ∞ S₀ Ω)
    (q : P × (X × X) × (ℝ × E))
    (hmem : ∀ r ∈ W, ∀ s ∈ W, phaseChartPoint ζ ε q r s ∈ Ω) :
    phaseChartKernelIntegral (S - S₀) ζ ε q =
      phaseChartKernelIntegral S ζ ε q - phaseChartKernelIntegral S₀ ζ ε q := by
  have hc := contDiffOn_phaseChartKernel_segments hΩ hS q hmem
  have hc₀ := contDiffOn_phaseChartKernel_segments hΩ hS₀ q hmem
  have hi (r : ℝ) (hr : r ∈ W) :
      IntervalIntegrable (phaseChartKernel S ζ ε q r) volume 0 1 := by
    have hcont : ContinuousOn (phaseChartKernel S ζ ε q r) (Icc (0 : ℝ) 1) :=
      hc.continuousOn.comp (f := fun s : ℝ ↦ (r,s))
        (continuous_const.prodMk continuous_id).continuousOn (fun s hs ↦ ⟨hr, hIW hs⟩)
    exact hcont.intervalIntegrable_of_Icc zero_le_one
  have hi₀ (r : ℝ) (hr : r ∈ W) :
      IntervalIntegrable (phaseChartKernel S₀ ζ ε q r) volume 0 1 := by
    have hcont : ContinuousOn (phaseChartKernel S₀ ζ ε q r) (Icc (0 : ℝ) 1) :=
      hc₀.continuousOn.comp (f := fun s : ℝ ↦ (r,s))
        (continuous_const.prodMk continuous_id).continuousOn (fun s hs ↦ ⟨hr, hIW hs⟩)
    exact hcont.intervalIntegrable_of_Icc zero_le_one
  have ho : IntervalIntegrable (fun r ↦ ∫ s in (0 : ℝ)..1,
      phaseChartKernel S ζ ε q r s) volume 0 1 :=
    ((contDiffOn_unitIntervalParameterIntegral hW hW hIW hc).continuousOn.mono hIW).intervalIntegrable_of_Icc zero_le_one
  have ho₀ : IntervalIntegrable (fun r ↦ ∫ s in (0 : ℝ)..1,
      phaseChartKernel S₀ ζ ε q r s) volume 0 1 :=
    ((contDiffOn_unitIntervalParameterIntegral hW hW hIW hc₀).continuousOn.mono hIW).intervalIntegrable_of_Icc zero_le_one
  unfold phaseChartKernelIntegral
  rw [← intervalIntegral.integral_sub ho ho₀]
  apply intervalIntegral.integral_congr
  intro r hr
  have hrW : r ∈ W := hIW (by simpa using hr)
  dsimp only
  rw [← intervalIntegral.integral_sub (hi r hrW) (hi₀ r hrW)]
  apply intervalIntegral.integral_congr
  intro s hs
  have hm := hmem r hrW s (hIW (by simpa using hs))
  unfold phaseChartKernel
  rw [phaseMixedKernel_sub
    ((hS.contDiffAt (hΩ.mem_nhds hm)).of_le (by simp))
    ((hS₀.contDiffAt (hΩ.mem_nhds hm)).of_le (by simp))]
  rfl

end JanetCartan.FullPhaseCharts.Comparison
