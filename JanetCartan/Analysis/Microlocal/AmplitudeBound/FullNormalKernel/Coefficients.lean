module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.FullNormalKernel.IntegralSeries
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.FullNormalKernel.Adjoint

/-!
# Integral realization of the normal Fourier terms

Each coefficient of the series in `app:ch_osc:eq:two-position-normal-bound`
acts by its literal iterated integral. The actual Hilbert adjoint formula
is derived from the input-kernel identity.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal ContDiff
namespace JanetCartan.AmplitudeBound
variable {d m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "U" => EuclideanSpace ℝ (Fin m)

/-- Each modulated normal coefficient equals its literal integral term in
`app:ch_osc:eq:two-position-normal-bound`. No adjoint formula is assumed. -/
theorem boxNormalAmplitudeTerm_ae_integral
    {D : Set U} (hD : MeasurableSet D) (t : E → U → ℂ)
    (ht : ContDiff ℝ ∞ (Function.uncurry t))
    (hts : HasCompactSupport (Function.uncurry t))
    (T : Lp ℂ 2 (volume.restrict D) →L[ℂ] Lp (α := E) ℂ 2)
    (hT : ∀ h, T h =ᵐ[volume] fun x ↦ ∫ u, t x u * h u ∂volume.restrict D)
    (c : U → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hc : StronglyMeasurable (Function.uncurry c)) (hd : 0 < d)
    {R ℓ : ℝ} (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2)
    (hs : ∀ u, SupportedInCenteredBox R (c u)) (hf : ∀ u, ContDiff ℝ ∞ (c u))
    (A : ℝ) (hA : 0 ≤ A) (hzero : ∀ u z, ‖c u z‖ ≤ A)
    (hderiv : ∀ u i z,
      ‖euclideanCoordinateDerivList (List.replicate (2 * (d + 1)) i) (c u) z‖ ≤ A)
    (g : Lp ℂ ∞ (volume.restrict D)) (f : Lp (α := E) ℂ 2)
    (k : Fin (2 * d) → ℤ) :
    boxLeftModulation ℓ k
      (T (multiplicationOperator (boxAmplitudeSymbol c hc hd hℓ hR hs hf A hA hzero hderiv k)
        (multiplicationOperator g (T.adjoint (boxRightModulation ℓ k f))))) =ᵐ[volume]
      fun x ↦ ∫ u, (∫ y, t x u * boxAmplitudeFourierTerm (c u) ℓ k x y *
        star (t y u) * g u * f y) ∂volume.restrict D := by
  let a := boxAmplitudeSymbol (μ := volume.restrict D) c hc hd hℓ hR hs hf A hA hzero hderiv k
  let v := boxRightModulation ℓ k f
  let w := multiplicationOperator a (multiplicationOperator g (T.adjoint v))
  have hw : w =ᵐ[volume.restrict D] fun u ↦
      UnitAddTorus.mFourierCoeff (boxAmplitudePeriodization ℓ (c u)) k *
        (g u * ∫ y, star (t y u) * v y) := by
    filter_upwards [multiplicationOperator_coeFn a (multiplicationOperator g (T.adjoint v)),
      multiplicationOperator_coeFn g (T.adjoint v),
      adjoint_ae_integral_of_smooth_compactKernel D hD ht hts T hT v,
      boxAmplitudeSymbol_coeFn (μ := volume.restrict D) c hc hd hℓ hR hs hf A hA hzero hderiv k]
      with u h₁ h₂ h₃ h₄
    change w u = a u * _ at h₁
    change a u = _ at h₄
    rw [h₁, h₂, h₃, h₄]
  have hv : v =ᵐ[volume] fun y ↦
      (boxCellCutoff ℓ y * UnitAddTorus.mFourier k (rightPositionChart ℓ y)) * f y :=
    cutoffModulation_coeFn _ _ _ _ _ k f
  filter_upwards [cutoffModulation_coeFn (leftPositionChart ℓ)
    (measurable_leftPositionChart ℓ) (boxCellCutoff ℓ)
    (aestronglyMeasurable_boxCellCutoff ℓ)
    (Eventually.of_forall (norm_boxCellCutoff_le ℓ)) k (T w), hT w] with x hx hTx
  change boxLeftModulation ℓ k (T w) x = _
  change boxLeftModulation ℓ k (T w) x = _ at hx
  rw [hx, hTx, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hw] with u hu
  rw [hu]
  calc
    _ = ((boxCellCutoff ℓ x * UnitAddTorus.mFourier k (leftPositionChart ℓ x)) *
        t x u * UnitAddTorus.mFourierCoeff (boxAmplitudePeriodization ℓ (c u)) k * g u) *
        (∫ y, star (t y u) * v y) := by ring
    _ = ∫ y, ((boxCellCutoff ℓ x * UnitAddTorus.mFourier k (leftPositionChart ℓ x)) *
        t x u * UnitAddTorus.mFourierCoeff (boxAmplitudePeriodization ℓ (c u)) k * g u) *
        (star (t y u) * v y) := (integral_const_mul _ _).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hv] with y hy
      rw [hy]
      dsimp only [boxAmplitudeFourierTerm]
      ring
end JanetCartan.AmplitudeBound
