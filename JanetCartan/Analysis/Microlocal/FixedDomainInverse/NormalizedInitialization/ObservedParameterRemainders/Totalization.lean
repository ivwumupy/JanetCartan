module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ObservedParameterRemainders.CompactMultiplier

/-!
# The original phase on its retained parameter domain

Continuity of slices is only known on the retained open parameter domain.
Use zero phase elsewhere when writing the total demodulation family. This
changes no germ, mixed jet, or compact support used by the observed remainder
(`app:ch_response:eq:response-graded-reduced`).
-/

@[expose] public noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace JanetCartan.FixedDomainInverse.ObservedParameterRemainders

variable {n : ℕ} {Par : Type} [NormedAddCommGroup Par] [NormedSpace ℝ Par]
local notation "E" => Euclidean n

/-- The original observation phase on the retained parameter domain, and zero
outside it. This only supplies a total family of continuous spatial slices
(`app:ch_regular:eq:inverse-remainder`). -/
def totalizedObservationPhase (V : Set Par) (φ : Par → E → ℝ) : Par → E → ℝ := by
  classical
  exact fun c ↦ if c ∈ V then φ c else 0

omit [NormedAddCommGroup Par] [NormedSpace ℝ Par] in
/-- Totalization preserves the original retained phase exactly
(`app:ch_response:eq:response-graded-reduced`). -/
theorem totalizedObservationPhase_of_mem {V : Set Par} (φ : Par → E → ℝ)
    {c : Par} (hc : c ∈ V) : totalizedObservationPhase V φ c = φ c := by
  simp [totalizedObservationPhase, hc]

/-- The totalized phase has continuous spatial slices for every parameter.
Only joint smoothness on the original retained domain is assumed
(`app:ch_regular:eq:inverse-remainder`). -/
theorem continuous_totalizedObservationPhase {V : Set Par} {φ : Par → E → ℝ}
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ univ))
    (c : Par) : Continuous (totalizedObservationPhase V φ c) := by
  by_cases hc : c ∈ V
  · rw [totalizedObservationPhase_of_mem φ hc]
    exact hφ.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun x ↦ ⟨hc, mem_univ x⟩)
  · have he : totalizedObservationPhase V φ c = 0 := by simp [totalizedObservationPhase, hc]
    rw [he]
    exact continuous_const

/-- Joint smoothness on the original retained domain is unchanged
(`app:ch_response:eq:response-graded-reduced`). -/
theorem contDiffOn_totalizedObservationPhase {V : Set Par} {φ : Par → E → ℝ}
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ univ)) :
    ContDiffOn ℝ ∞ (Function.uncurry (totalizedObservationPhase V φ)) (V ×ˢ univ) := by
  apply hφ.congr
  intro z hz
  exact congrFun (totalizedObservationPhase_of_mem φ hz.1) z.2

/-- Every actual mixed phase derivative agrees on the same open domain.
There is no differentiability requirement on the totalization across its
parameter boundary (`app:ch_regular:eq:inverse-remainder`). -/
theorem iteratedFDeriv_totalizedObservationPhase {V : Set Par} (hV : IsOpen V)
    (φ : Par → E → ℝ) (j : ℕ) {c : Par} (hc : c ∈ V) (x : E) :
    iteratedFDeriv ℝ j (Function.uncurry (totalizedObservationPhase V φ)) (c, x) =
      iteratedFDeriv ℝ j (Function.uncurry φ) (c, x) := by
  have he : Function.uncurry (totalizedObservationPhase V φ) =ᶠ[𝓝 (c, x)]
      Function.uncurry φ := by
    filter_upwards [(hV.prod isOpen_univ).mem_nhds ⟨hc, mem_univ x⟩] with z hz
    exact congrFun (totalizedObservationPhase_of_mem φ hz.1) z.2
  exact (he.iteratedFDeriv ℝ j).eq_of_nhds

end JanetCartan.FixedDomainInverse.ObservedParameterRemainders
