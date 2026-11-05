module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.UncutNormal.PdoLimit.Multipliers
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.BoxOperators

/-!
# Pointwise limits of the physical Fourier coefficients

Dominated convergence on the fixed auxiliary probability torus, used by
`PdoLimit.tendsto_twoPositionL2Operator` to remove frequency cutoffs in
`app:ch_osc:lem:osc-amplitude`. No convergence of derivatives is required.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
open JanetCartan.AmplitudeBound
namespace JanetCartan.FourierIntegral.UncutNormal.PdoLimit
variable {n : ℕ}
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Pointwise convergence and a common zeroth-order bound imply convergence
of every physical Fourier coefficient. The constant bound is integrable on the
fixed probability torus (`app:ch_osc:lem:osc-amplitude`). -/
theorem tendsto_mFourierCoeff_of_pointwise
    (a : ℕ → Torus n → ℂ) (b : Torus n → ℂ)
    (ha : ∀ m, StronglyMeasurable (a m)) {C : ℝ}
    (hC : ∀ m z, ‖a m z‖ ≤ C)
    (hlim : ∀ z, Tendsto (fun m ↦ a m z) atTop (𝓝 (b z))) (k : Fin n → ℤ) :
    Tendsto (fun m ↦ UnitAddTorus.mFourierCoeff (a m) k) atTop
      (𝓝 (UnitAddTorus.mFourierCoeff b k)) := by
  simp only [UnitAddTorus.mFourierCoeff, smul_eq_mul]
  apply tendsto_integral_of_dominated_convergence (fun _ ↦ C)
  · intro m
    exact ((UnitAddTorus.mFourier (-k)).continuous.stronglyMeasurable.mul (ha m)).aestronglyMeasurable
  · exact integrable_const C
  · intro m
    exact Eventually.of_forall fun z ↦ by
      simpa [norm_mul, UnitAddTorus.mFourier, fourier_apply, norm_prod] using hC m z
  · exact Eventually.of_forall fun z ↦ (hlim z).const_mul _
end JanetCartan.FourierIntegral.UncutNormal.PdoLimit
