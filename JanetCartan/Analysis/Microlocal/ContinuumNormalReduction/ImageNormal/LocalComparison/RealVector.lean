module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.RealVector.Chart
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.RealVector.Realizations
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.FourierAction

/-!
# Real-vector bridges for the local image comparison

The actual real periodic inverse, the complex scalar multiplier, and the
Euclidean real vector realizations used in `app:ch_background:prop:bg-frame`,
Step 1. The parent construction retains the full bounded chart comparison.
-/

public noncomputable section
open MeasureTheory
open scoped SchwartzMap
open JanetCartan.Pseudodifferential
namespace JanetCartan.ContinuumNormalReduction.ImageNormal

/-- The constructed scalar periodic inverse satisfies the previously published
Schwartz comparison interface with no Fourier-action premise
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem complexPeriodicBesselOperator_eq_periodized_euclidean_on_schwartz
    {d : ℕ} (u : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) :
    complexPeriodicBesselOperator ((schwartzTorusPeriodization u).toLp 2 volume ℂ) =
      (schwartzTorusPeriodization
        (schwartzFrequencyMultiplier (fun ξ ↦ (imageBesselSymbol ξ : ℂ)) u)).toLp
          2 volume ℂ :=
  periodicBessel_eq_periodized_euclidean_on_schwartz complexPeriodicBesselOperator
    mFourierCoeff_complexPeriodicBesselOperator u

end JanetCartan.ContinuumNormalReduction.ImageNormal
