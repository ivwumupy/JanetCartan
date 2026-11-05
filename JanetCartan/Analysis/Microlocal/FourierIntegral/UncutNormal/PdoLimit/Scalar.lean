module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.UncutNormal.PdoLimit.Coefficients
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Realization

/-!
# Strong convergence of the existing scalar two-position PDO

For `app:ch_osc:lem:osc-amplitude`, pointwise convergence with the same fixed
physical support and finite physical derivative budget passes through the actual
operator series. The finite matrix assembly in `UncutNormal.PdoLimit` consumes
this result for `app:ch_regular_base:eq:actual-normal-amplitude`.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal ContDiff
open JanetCartan.AmplitudeBound JanetCartan.Pseudodifferential
namespace JanetCartan.FourierIntegral.UncutNormal.PdoLimit
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "P" => EuclideanSpace ℝ (Fin (2 * n))
local notation "H" => Lp ℂ 2 (volume : Measure E)

/-- The existing scalar PDO is strongly continuous under pointwise amplitude
convergence and uniform physical derivative bounds of order `2 * (n + 1)`.
The common box supplies the same modulations, and the derivative budget supplies
an explicit summable coefficient majorant (`app:ch_osc:lem:osc-amplitude`). -/
theorem tendsto_twoPositionL2Operator (hn : 0 < n) (R : ℝ)
    (a : ℕ → E → P → ℂ) (b : E → P → ℂ)
    (ha : ∀ m, ContDiff ℝ ∞ (Function.uncurry (a m)))
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hsa : ∀ m ξ, SupportedInCenteredBox R (a m ξ))
    (hsb : ∀ ξ, SupportedInCenteredBox R (b ξ)) (M : ℝ)
    (hMa : ∀ m, HasAmplitudeDerivativeBound (a m) (2 * (n + 1)) M)
    (hMb : HasAmplitudeDerivativeBound b (2 * (n + 1)) M)
    (hlim : ∀ ξ z, Tendsto (fun m ↦ a m ξ z) atTop (𝓝 (b ξ z))) (f : H) :
    Tendsto (fun m ↦ twoPositionL2Operator hn R (a m) (ha m) (hsa m) M (hMa m) f)
      atTop (𝓝 (twoPositionL2Operator hn R b hb hsb M hMb f)) := by
  let ℓ := amplitudeBoxScale R
  have hℓ : 0 < ℓ := amplitudeBoxScale_pos R
  have hR : R / ℓ < 1 / 2 := div_amplitudeBoxScale_lt R
  have hM : 0 ≤ M := (norm_nonneg _).trans (hMb.norm_le 0 0)
  let ca := fun m k ↦ boxAmplitudeSymbol (μ := (volume : Measure E)) (a m)
    (ha m).continuous.stronglyMeasurable hn hℓ hR (hsa m)
    (fun _ ↦ (ha m).comp (contDiff_const.prodMk contDiff_id)) M hM
    (hMa m).norm_le (hMa m).pure_le k
  let cb := fun k ↦ boxAmplitudeSymbol (μ := (volume : Measure E)) b
    hb.continuous.stronglyMeasurable hn hℓ hR hsb
    (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) M hM
    hMb.norm_le hMb.pure_le k
  let c := fun k ↦ (smoothCoefficientConstant n * (boxDerivativeFactor n ℓ * M)) *
    twoPositionWeight n k
  have hca (m : ℕ) (k : Fin (2 * n) → ℤ) :
      ca m k =ᵐ[volume] fun ξ ↦ UnitAddTorus.mFourierCoeff
        (boxAmplitudePeriodization ℓ (a m ξ)) k := boxAmplitudeSymbol_coeFn ..
  have hcb (k : Fin (2 * n) → ℤ) :
      cb k =ᵐ[volume] fun ξ ↦ UnitAddTorus.mFourierCoeff
        (boxAmplitudePeriodization ℓ (b ξ)) k := boxAmplitudeSymbol_coeFn ..
  have hcoef (ξ : E) (k : Fin (2 * n) → ℤ) :
      Tendsto (fun m ↦ UnitAddTorus.mFourierCoeff (boxAmplitudePeriodization ℓ (a m ξ)) k)
        atTop (𝓝 (UnitAddTorus.mFourierCoeff (boxAmplitudePeriodization ℓ (b ξ)) k)) := by
    apply tendsto_mFourierCoeff_of_pointwise
    · intro m
      exact (isSmoothPeriodic_boxAmplitudePeriodization hℓ hR (hsa m ξ)
        ((ha m).comp (contDiff_const.prodMk contDiff_id))).1.stronglyMeasurable
    · exact fun m ↦ norm_boxAmplitudePeriodization_le ((hMa m).norm_le ξ) ℓ
    · exact fun z ↦ hlim ξ (ℓ • centeredTorusRepresentative z)
  have hmul (k : Fin (2 * n) → ℤ) (g : H) :
      Tendsto (fun m ↦ fourierMultiplier (ca m k) g) atTop
        (𝓝 (fourierMultiplier (cb k) g)) := by
    apply tendsto_fourierMultiplier_of_ae _ _ hM
    · intro m
      filter_upwards [hca m k] with ξ hξ
      rw [hξ]
      exact norm_mFourierCoeff_le _ _
        (norm_boxAmplitudePeriodization_le ((hMa m).norm_le ξ) ℓ)
    · filter_upwards [hcb k] with ξ hξ
      rw [hξ]
      exact norm_mFourierCoeff_le _ _
        (norm_boxAmplitudePeriodization_le (hMb.norm_le ξ) ℓ)
    · filter_upwards [ae_all_iff.mpr (fun m ↦ hca m k), hcb k] with ξ haξ hbξ
      simpa only [haξ, hbξ] using hcoef ξ k
  change Tendsto (fun m ↦ amplitudeOperator (boxLeftModulation ℓ)
      (boxRightModulation ℓ) (fun k ↦ fourierMultiplier (ca m k)) f) atTop
    (𝓝 (amplitudeOperator (boxLeftModulation ℓ) (boxRightModulation ℓ)
      (fun k ↦ fourierMultiplier (cb k)) f))
  apply tendsto_amplitudeOperator_apply _ _ _ _ c
    (norm_boxLeftModulation_le ℓ) (norm_boxRightModulation_le ℓ)
  · intro k
    exact (norm_fourierMultiplier_le _).trans (norm_boxAmplitudeSymbol_le ..)
  · exact (summable_twoPositionWeight n).mul_left _
  · intro m k
    exact (norm_fourierMultiplier_le _).trans (norm_boxAmplitudeSymbol_le ..)
  · exact hmul
end JanetCartan.FourierIntegral.UncutNormal.PdoLimit
