module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.Multipliers

/-!
# Bounded measurable symbols

The passage from pointwise bounds to `L∞` symbols in
`app:ch_osc:lem:osc-amplitude`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace JanetCartan.AmplitudeBound

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The `L∞` realization of a bounded measurable symbol in
`app:ch_osc:lem:osc-amplitude`. -/
def boundedSymbol (a : X → ℂ) (ha : AEStronglyMeasurable a μ) (A : ℝ)
    (hA : ∀ᵐ x ∂μ, ‖a x‖ ≤ A) : Lp ℂ ∞ μ :=
  (memLp_top_of_bound ha A hA).toLp a

/-- The symbol realization in `app:ch_osc:lem:osc-amplitude` agrees almost
everywhere with its defining function. -/
theorem boundedSymbol_coeFn (a : X → ℂ) (ha : AEStronglyMeasurable a μ) (A : ℝ)
    (hA : ∀ᵐ x ∂μ, ‖a x‖ ≤ A) : boundedSymbol a ha A hA =ᵐ[μ] a :=
  MemLp.coeFn_toLp _

/-- A pointwise symbol bound gives the same `L∞` bound, with no assumption on
the total frequency measure (`app:ch_osc:lem:osc-amplitude`). -/
theorem norm_boundedSymbol_le (a : X → ℂ) (ha : AEStronglyMeasurable a μ) (A : ℝ)
    (hA : ∀ᵐ x ∂μ, ‖a x‖ ≤ A) (hA0 : 0 ≤ A) :
    ‖boundedSymbol a ha A hA‖ ≤ A := by
  rw [boundedSymbol, Lp.norm_toLp, eLpNorm_exponent_top ha]
  apply (ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (eLpNormEssSup_le_of_ae_bound hA)).trans_eq
  exact ENNReal.toReal_ofReal hA0

end JanetCartan.AmplitudeBound
