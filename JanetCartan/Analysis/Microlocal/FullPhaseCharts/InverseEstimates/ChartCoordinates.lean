module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.FiberBounds
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.QuotientJets

/-!
# Coordinate order for the literal quotient-chart estimates

`app:ch_seed:prop:seed-phase-charts` holds epsilon, spectators and both physical
points fixed while inverting the normalized data covector. This leaf only
reorders those coordinates; it does not change their normalization or measure.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.FullPhaseCharts.InverseEstimates
variable {R D X E : Type} [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Regroup the literal variables of `app:ch_seed:prop:seed-phase-charts`
from `(epsilon, spectators, x, x', data)` to the order of `QuotientJets`. -/
def quotientChartReindex :
    ((ℝ × (R × X × X)) × D) →L[ℝ] (((R × D) × ℝ) × X × X) :=
  let p := ContinuousLinearMap.fst ℝ (ℝ × (R × X × X)) D
  let u := ContinuousLinearMap.snd ℝ (ℝ × (R × X × X)) D
  let e := (ContinuousLinearMap.fst ℝ ℝ (R × X × X)).comp p
  let s := (ContinuousLinearMap.snd ℝ ℝ (R × X × X)).comp p
  let a := (ContinuousLinearMap.fst ℝ R (X × X)).comp s
  let x := (ContinuousLinearMap.snd ℝ R (X × X)).comp s
  ((a.prod u).prod e).prod x

/-- The regrouping retains every coordinate literally
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem quotientChartReindex_apply (q : (ℝ × (R × X × X)) × D) :
    quotientChartReindex q = (((q.1.2.1, q.2), q.1.1), q.1.2.2) := rfl

/-- Regrouping coordinates is a contraction for the product norm, uniformly
in all data (`app:ch_seed:prop:seed-phase-charts`). -/
theorem norm_quotientChartReindex_le :
    ‖quotientChartReindex (R := R) (D := D) (X := X)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro q
  simp only [quotientChartReindex_apply, Prod.norm_def, one_mul]
  exact le_of_eq (by ac_rfl)

variable [CompleteSpace X] [CompleteSpace E]

/-- The actual two-point gradient of the integral quotient, with only a fixed
linear output identification. Full charts use the Hilbert/product coordinate
identification; transverse charts put time and `z₁` among `R` and use their
transverse physical phase. This is the map of
`app:ch_seed:prop:seed-phase-charts`, in inverse-family variable order. -/
def carrierQuotientChart (O : X →L[ℝ] D)
    (S : ((R × D) × X) → E → ℝ) (z v : R × D → E)
    (q : (ℝ × (R × X × X)) × D) : D :=
  O (averagedPhaseGradient (fun p x ↦
    phaseShiftQuotient S (p.1, x) (z p.1) (v p.1) p.2)
    ((q.1.2.1, q.2), q.1.1) q.1.2.2.1 q.1.2.2.2)

end JanetCartan.FullPhaseCharts.InverseEstimates
