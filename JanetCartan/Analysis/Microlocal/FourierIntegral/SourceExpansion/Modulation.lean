module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceExpansion.Cutoff
public import JanetCartan.Analysis.Microlocal.FourierIntegral.L2Realization.Tests

/-!
# Actual vector-valued source modulations

The contractions `M_(β exp(2π i k·y/ℓ))` in
`app:ch_regular_base:thm:actual-calculus`, Step 1, on Euclidean Lebesgue L².
-/

@[expose] public noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Filter
open scoped ContDiff ENNReal
namespace JanetCartan.FourierIntegral.SourceExpansion
open AmplitudeBound
variable {n r : ℕ} {R ℓ : ℝ}
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure (Euclidean n))

/-- Actual vector multiplication, using the existing bounded cutoff symbol;
consumer: the operator series in `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
def sourceModulation (β : SourceCutoff n R ℓ) (k : Fin n → ℤ) : H →L[ℂ] H :=
  (ContinuousLinearMap.lsmul ℂ ℂ (E := V)).holderL volume ∞ 2 2
    (cutoffModulationSymbol (scaledTorusChart ℓ) (measurable_scaledTorusChart ℓ)
      β.toFun β.smooth.continuous.aestronglyMeasurable
      (Eventually.of_forall β.norm_le_one) k)

/-- The source multipliers are contractions independently of the physical mode
(`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem norm_sourceModulation_le (β : SourceCutoff n R ℓ) (k : Fin n → ℤ) :
    ‖sourceModulation (r := r) β k‖ ≤ 1 := by
  let a : Lp ℂ ∞ (volume : Measure (Euclidean n)) := cutoffModulationSymbol (scaledTorusChart ℓ) (measurable_scaledTorusChart ℓ)
    β.toFun β.smooth.continuous.aestronglyMeasurable
    (Eventually.of_forall β.norm_le_one) k
  have ha : ‖a‖ ≤ 1 := norm_boundedSymbol_le _ _ 1 _ zero_le_one
  change ‖(ContinuousLinearMap.lsmul ℂ ℂ (E := V)).holderL volume ∞ 2 2 a‖ ≤ 1
  calc
    _ ≤ ‖(ContinuousLinearMap.lsmul ℂ ℂ (E := V)).holderL volume ∞ 2 2‖ * ‖a‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * 1 := mul_le_mul
      ((ContinuousLinearMap.norm_holderL_le _).trans ContinuousLinearMap.opNorm_lsmul_le)
      ha (norm_nonneg _) zero_le_one
    _ = 1 := one_mul _

/-- Pointwise realization of the vector source multiplier on the original
Lebesgue space (`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem sourceModulation_coeFn (β : SourceCutoff n R ℓ) (k : Fin n → ℤ) (u : H) :
    sourceModulation β k u =ᵐ[volume] fun y ↦ (β.toFun y * sourceMode ℓ k y) • u y := by
  filter_upwards [(ContinuousLinearMap.lsmul ℂ ℂ (E := V)).coeFn_holder (r := (2 : ℝ≥0∞))
      (cutoffModulationSymbol (scaledTorusChart ℓ) (measurable_scaledTorusChart ℓ)
        β.toFun β.smooth.continuous.aestronglyMeasurable
        (Eventually.of_forall β.norm_le_one) k) u,
    boundedSymbol_coeFn (fun y ↦ β.toFun y * sourceMode ℓ k y) _ 1 _] with y hy hb
  exact hy.trans (congrArg (fun c : ℂ ↦ c • u y) hb)

/-- Smooth physical source characters; consumed by preservation of the compact
smooth test domain in `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem contDiff_sourceMode (ℓ : ℝ) (k : Fin n → ℤ) : ContDiff ℝ ∞ (sourceMode ℓ k) := by
  change ContDiff ℝ ∞ (fun y ↦ sourceMode ℓ k y)
  simp_rw [sourceMode_eq_exp]
  exact Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp
    (contDiff_const.mul (periodicFourierPhase k).contDiff)).mul contDiff_const)

/-- The actual cutoff modulation of a compact smooth Euclidean test
(`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
def sourceModulatedTest (β : SourceCutoff n R ℓ) (k : Fin n → ℤ)
    (u : graphTestSpace n r) : graphTestSpace n r :=
  ⟨fun y ↦ (β.toFun y * sourceMode ℓ k y) • u.val y,
    (β.smooth.mul (contDiff_sourceMode ℓ k)).smul u.property.1,
    u.property.2.smul_left (f := fun y ↦ β.toFun y * sourceMode ℓ k y)⟩

/-- The same multiplier acts on smooth tests and on their actual L² classes
(`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem sourceModulation_graphTestToLp (β : SourceCutoff n R ℓ) (k : Fin n → ℤ)
    (u : graphTestSpace n r) :
    sourceModulation β k (graphTestToLp u) = graphTestToLp (sourceModulatedTest β k u) := by
  apply Lp.ext
  filter_upwards [sourceModulation_coeFn β k (graphTestToLp u),
    (graphTest_memLp u).coeFn_toLp, (graphTest_memLp (sourceModulatedTest β k u)).coeFn_toLp]
    with y hy hu hv
  exact hy.trans ((congrArg (fun v : V ↦ (β.toFun y * sourceMode ℓ k y) • v) hu).trans hv.symm)

end JanetCartan.FourierIntegral.SourceExpansion
