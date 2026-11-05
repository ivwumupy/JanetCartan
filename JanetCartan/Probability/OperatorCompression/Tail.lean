module

public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.Analysis.Normed.Group.Continuity

/-!
# Passing strict tail bounds to a pointwise limit

The set form of the Fatou step in `app:ch_waves:thm:sampling` of `paper.tex`.
-/

@[expose] public noncomputable section

open Filter MeasureTheory
open scoped Topology ENNReal

namespace JanetCartan.OperatorCompression

/-- A uniform strict tail bound passes to a pointwise limit. This is the set form
of Fatou used in `app:ch_waves:thm:sampling`; it even holds for outer measures of
nonmeasurable events. -/
theorem measure_strict_tail_le_of_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : ℕ → Ω → ℝ) (g : Ω → ℝ) (hlim : ∀ ω, Tendsto (fun n ↦ f n ω) atTop (𝓝 (g ω)))
    (t : ℝ) (B : ℝ≥0∞) (hbound : ∀ n, μ {ω | t < f n ω} ≤ B) :
    μ {ω | t < g ω} ≤ B := by
  let A : ℕ → Set Ω := fun N ↦ {ω | ∀ n ≥ N, t < f n ω}
  have hmono : Monotone A := fun N M hNM ω hω n hn ↦ hω n (hNM.trans hn)
  have hsub : {ω | t < g ω} ⊆ ⋃ N, A N := by
    intro ω hω
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((hlim ω).eventually (eventually_gt_nhds hω))
    exact Set.mem_iUnion.mpr ⟨N, hN⟩
  calc
    μ {ω | t < g ω} ≤ μ (⋃ N, A N) := measure_mono hsub
    _ = ⨆ N, μ (A N) := hmono.measure_iUnion
    _ ≤ B := iSup_le fun N ↦
      (measure_mono (show A N ⊆ {ω | t < f N ω} from fun _ hω ↦ hω N le_rfl)).trans
        (hbound N)

/-- The norm-tail specialization of the Fatou step in
`app:ch_waves:thm:sampling`. -/
theorem measure_norm_tail_le_of_tendsto
    {Ω E : Type*} [MeasurableSpace Ω] [SeminormedAddCommGroup E]
    (μ : Measure Ω) (f : ℕ → Ω → E) (g : Ω → E)
    (hlim : ∀ ω, Tendsto (fun n ↦ f n ω) atTop (𝓝 (g ω)))
    (t : ℝ) (B : ℝ≥0∞) (hbound : ∀ n, μ {ω | t < ‖f n ω‖} ≤ B) :
    μ {ω | t < ‖g ω‖} ≤ B :=
  measure_strict_tail_le_of_tendsto μ (fun n ω ↦ ‖f n ω‖) (fun ω ↦ ‖g ω‖)
    (fun ω ↦ (hlim ω).norm) t B hbound

end JanetCartan.OperatorCompression
