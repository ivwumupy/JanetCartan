module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseFamily.Buffered

/-!
# Regularity past the closure of the common inverse chart

The outer buffer in `app:ch_seed:prop:seed-phase-charts` puts the closure of
the common inverse target strictly inside every data image. The SAME inverse
choice therefore extends smoothly to an open neighborhood of that closure.
This permits estimates on the entire closed target, not only the image core.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff
namespace JanetCartan.FullPhaseCharts.ActualEstimates

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Extend the regularity of the SAME fiberwise inverse to the fixed outer
buffer. Its inverse identities and data containment continue to hold there
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem bufferedInverse_outer_regular (f : P → E → E)
    {U : Set P} {K D₁ D V L : Set E} {b c : ℝ} {G : E ≃L[ℝ] E}
    (hU : IsOpen U) (hD₁ : IsOpen D₁) (hD : D₁ ⊆ D) (hb : 0 < b)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ D₁))
    (h : BufferedPhaseInverse f U K D₁ D V L b c G) :
    let W := thickening (b / 2) (closure V)
    closure V ⊆ W ∧
    ContDiffOn ℝ ∞ (Function.uncurry (phaseChartInverse f D₁)) (U ×ˢ W) ∧
    ∀ p ∈ U, ∀ y ∈ W,
      phaseChartInverse f D₁ p y ∈ D₁ ∧ f p (phaseChartInverse f D₁ p y) = y := by
  dsimp only
  have himage : ∀ p ∈ U, thickening (b / 2) (closure V) ⊆ f p '' D₁ := by
    intro p hp
    exact (thickening_subset_cthickening_of_le (by linarith : b / 2 ≤ b) _).trans
      (h.outer_buffer p hp)
  refine ⟨self_subset_thickening (by positivity) _, ?_, ?_⟩
  · exact contDiffOn_phaseChartInverse hU hD₁ isOpen_thickening hf
      (fun p hp ↦ (h.injective p hp).mono hD) himage
      (fun p hp u hu ↦ (h.differential_bounds p hp u (hD hu)).1)
  · intro p hp y hy
    exact phaseChartInverse_spec (himage p hp hy)

end JanetCartan.FullPhaseCharts.ActualEstimates
