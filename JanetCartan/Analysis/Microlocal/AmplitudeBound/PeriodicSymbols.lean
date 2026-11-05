module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.SmoothCoefficients
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.BoundedSymbols

/-!
# Parameter-dependent physical Fourier symbols

The actual coefficient symbols of a smooth periodic two-position amplitude, for
`app:ch_osc:lem:osc-amplitude`. The parameter can be the frequency or the normal
operator's integration variable. Bounds are derived from physical derivatives.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace JanetCartan.AmplitudeBound

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {d : ℕ}

/-- Physical Fourier coefficients are measurable in the external parameter
(`app:ch_osc:lem:osc-amplitude`). -/
theorem stronglyMeasurable_parameter_mFourierCoeff (b : X → Torus (2 * d) → ℂ)
    (hb : StronglyMeasurable (Function.uncurry b)) (k : Fin (2 * d) → ℤ) :
    StronglyMeasurable (fun ξ ↦ UnitAddTorus.mFourierCoeff (b ξ) k) := by
  exact (((UnitAddTorus.mFourier (-k)).continuous.stronglyMeasurable.comp_measurable
    measurable_snd).mul hb).integral_prod_right
      (ν := Measure.pi (fun _ : Fin (2 * d) ↦ AddCircle.haarAddCircle))

/-- The coefficient symbol constructed from a smooth two-position amplitude in
`app:ch_osc:lem:osc-amplitude`. -/
def periodicAmplitudeSymbol (b : X → Torus (2 * d) → ℂ)
    (hb : StronglyMeasurable (Function.uncurry b)) (hd : 0 < d)
    (hf : ∀ ξ, IsSmoothPeriodic (b ξ)) (A : ℝ)
    (hzero : ∀ ξ x, ‖b ξ x‖ ≤ A)
    (hderiv : ∀ ξ i x,
      ‖periodicCoordinateDerivList (List.replicate (2 * (d + 1)) i) (b ξ) x‖ ≤ A)
    (k : Fin (2 * d) → ℤ) : Lp ℂ ∞ μ :=
  boundedSymbol (fun ξ ↦ UnitAddTorus.mFourierCoeff (b ξ) k)
    (stronglyMeasurable_parameter_mFourierCoeff b hb k).aestronglyMeasurable
    ((smoothCoefficientConstant d * A) * twoPositionWeight d k)
    (Filter.Eventually.of_forall fun ξ ↦
      norm_mFourierCoeff_le_twoPositionWeight hd (hf ξ) (hzero ξ) (hderiv ξ) k)

/-- The `L∞` symbol is the actual physical Fourier coefficient almost everywhere
(`app:ch_osc:lem:osc-amplitude`). -/
theorem periodicAmplitudeSymbol_coeFn (b : X → Torus (2 * d) → ℂ)
    (hb : StronglyMeasurable (Function.uncurry b)) (hd : 0 < d)
    (hf : ∀ ξ, IsSmoothPeriodic (b ξ)) (A : ℝ)
    (hzero : ∀ ξ x, ‖b ξ x‖ ≤ A)
    (hderiv : ∀ ξ i x,
      ‖periodicCoordinateDerivList (List.replicate (2 * (d + 1)) i) (b ξ) x‖ ≤ A)
    (k : Fin (2 * d) → ℤ) :
    periodicAmplitudeSymbol (μ := μ) b hb hd hf A hzero hderiv k =ᵐ[μ]
      fun ξ ↦ UnitAddTorus.mFourierCoeff (b ξ) k := boundedSymbol_coeFn ..

/-- The uniform derivative assumptions imply the `L∞` coefficient bound in
`app:ch_osc:lem:osc-amplitude`, independently of frequency support. -/
theorem norm_periodicAmplitudeSymbol_le (b : X → Torus (2 * d) → ℂ)
    (hb : StronglyMeasurable (Function.uncurry b)) (hd : 0 < d)
    (hf : ∀ ξ, IsSmoothPeriodic (b ξ)) (A : ℝ) (hA : 0 ≤ A)
    (hzero : ∀ ξ x, ‖b ξ x‖ ≤ A)
    (hderiv : ∀ ξ i x,
      ‖periodicCoordinateDerivList (List.replicate (2 * (d + 1)) i) (b ξ) x‖ ≤ A)
    (k : Fin (2 * d) → ℤ) :
    ‖periodicAmplitudeSymbol (μ := μ) b hb hd hf A hzero hderiv k‖ ≤
      (smoothCoefficientConstant d * A) * twoPositionWeight d k :=
  norm_boundedSymbol_le _ _ _ _
    (mul_nonneg (mul_nonneg (smoothCoefficientConstant_pos d).le hA)
      (twoPositionWeight_nonneg d k))

/-- The normal-series bound of `app:ch_osc:eq:two-position-normal-bound`, now
with coefficients constructed from a smooth periodic amplitude. Identifying
this series with the full normal integral kernel is a separate obligation. -/
theorem norm_normalAmplitudeOperator_periodic_le {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (b : X → Torus (2 * d) → ℂ)
    (hb : StronglyMeasurable (Function.uncurry b)) (hd : 0 < d)
    (hf : ∀ ξ, IsSmoothPeriodic (b ξ)) (A : ℝ) (hA : 0 ≤ A)
    (hzero : ∀ ξ x, ‖b ξ x‖ ≤ A)
    (hderiv : ∀ ξ i x,
      ‖periodicCoordinateDerivList (List.replicate (2 * (d + 1)) i) (b ξ) x‖ ≤ A)
    (L R : (Fin (2 * d) → ℤ) → H →L[ℂ] H)
    (hL : ∀ k, ‖L k‖ ≤ 1) (hR : ∀ k, ‖R k‖ ≤ 1)
    (T : Lp ℂ 2 μ →L[ℂ] H) (g : Lp ℂ ∞ μ) :
    ‖normalAmplitudeOperator L R T (fun k ↦
        (multiplicationOperator (periodicAmplitudeSymbol b hb hd hf A hzero hderiv k)).comp
          (multiplicationOperator g))‖ ≤
      coefficientSumConstant d * (smoothCoefficientConstant d * A) * ‖T‖ ^ 2 * ‖g‖ :=
  norm_normalAmplitudeOperator_le_of_decay d L R T _ g _ hL hR
    (norm_periodicAmplitudeSymbol_le b hb hd hf A hA hzero hderiv)

end JanetCartan.AmplitudeBound
