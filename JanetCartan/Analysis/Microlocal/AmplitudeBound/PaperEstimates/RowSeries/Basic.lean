module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.Multipliers

/-!
# Actual finite row-amplitude operators

For part (i) of `app:ch_osc:lem:osc-amplitude`, a physical Fourier mode
acts by the original bounded operator on the coefficient-multiplied
input, followed by the original physical modulation. These definitions
do not assume an amplitude estimate or any source-variable derivatives.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace JanetCartan.AmplitudeBound.PaperEstimates

variable {κ X H : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- One actual Fourier mode of the original kernel multiplier in
`app:ch_osc:eq:amplitude-row`. -/
def rowModeOperator (M : κ → H →L[ℂ] H) (T : Lp ℂ 2 μ →L[ℂ] H)
    (a : κ → Lp ℂ ∞ μ) (k : κ) : Lp ℂ 2 μ →L[ℂ] H :=
  (M k).comp (T.comp (multiplicationOperator (a k)))

/-- The finite actual row-kernel multiplier whose strong limit is
identified with the original amplitude-multiplied kernel in
`app:ch_osc:eq:amplitude-row`. -/
def finiteRowAmplitudeOperator (M : κ → H →L[ℂ] H)
    (T : Lp ℂ 2 μ →L[ℂ] H) (a : κ → Lp ℂ ∞ μ) (s : Finset κ) :
    Lp ℂ 2 μ →L[ℂ] H :=
  ∑ k ∈ s, rowModeOperator M T a k

end JanetCartan.AmplitudeBound.PaperEstimates
