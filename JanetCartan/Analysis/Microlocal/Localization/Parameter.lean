module
public import JanetCartan.Analysis.Microlocal.Localization.Vector
public import Mathlib.MeasureTheory.Measure.Complex
public import Mathlib.MeasureTheory.VectorMeasure.Integral
/-!
# Integration over the complex parameter measure

The total-variation step in `app:ch_osc:prop:osc-source-shell`. The final
estimate integrates the already proved vector-valued oscillatory kernels, with
a common compact support and uniform phase and amplitude profiles. Identification
of this average with the Fourier transform of the source additionally requires
measurability and Fubini; no such identification is asserted here.
-/

open scoped ContDiff
open MeasureTheory
@[expose] public noncomputable section
namespace JanetCartan.Localization
variable {D F : Type*} [MeasurableSpace D] [NormedAddCommGroup F]
  [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
/-- `app:ch_osc:prop:osc-source-shell`: Integration of a complex Banach-valued function against a complex measure using the scalar multiplication pairing. -/
def complexMeasureIntegral (ν : ComplexMeasure D) (f : D → F) : F :=
  ν.integral f (ContinuousLinearMap.lsmul ℝ ℂ).flip
/-- `app:ch_osc:prop:osc-source-shell`: A uniform bound integrates with the total variation of the complex measure and no additional pairing constant. -/
theorem norm_complexMeasureIntegral_le (ν : ComplexMeasure D) [IsFiniteMeasure ν.variation]
    (f : D → F) {B : ℝ} (hB : 0 ≤ B) (hf : ∀ᵐ u ∂ν.variation, ‖f u‖ ≤ B) :
    ‖complexMeasureIntegral ν f‖ ≤ B * ν.variation.real Set.univ := by
  apply VectorMeasure.norm_integral_le_of_norm_le_const hf |>.trans
  apply mul_le_mul_of_nonneg_right _ measureReal_nonneg
  apply (mul_le_mul_of_nonneg_left _ hB).trans_eq (mul_one B)
  rw [ContinuousLinearMap.opNorm_flip]
  exact ContinuousLinearMap.opNorm_lsmul_le

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace F] {μ : Measure E} [μ.IsAddHaarMeasure]
/-- `app:ch_osc:prop:osc-source-shell`: Parameter averaging preserves the repeated integration-by-parts gain, with the common support volume and total variation explicit. This estimates the average of the kernels; it does not assert a Fubini identity for the source. -/
theorem norm_parameter_oscillatory_integral_le {U K : Set E} (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) (e : ι → E) (ψ : D → E → ℝ) (a : D → E → F) (q : ℕ)
    (ν : ComplexMeasure D) [IsFiniteMeasure ν.variation]
    (hψ : ∀ u, ContDiffOn ℝ ∞ (ψ u) U) (ha : ∀ u, ContDiffOn ℝ ∞ (a u) U)
    (hs : ∀ u, tsupport (a u) ⊆ K)
    {δ G A L R : ℝ} (hδ : 0 < δ) (hA : 0 ≤ A) (hL : 0 ≤ L) (hR : 0 < R)
    (hgap : ∀ u x, x ∈ U → δ * R ^ 2 ≤ phaseGradientSquare e (ψ u) x)
    (hupper : ∀ u x, x ∈ U → ‖fderiv ℝ (ψ u) x‖ ≤ G * R)
    {P C : ℕ → ℝ} (hC : ∀ r, 0 ≤ C r)
    (hp : ∀ u x, x ∈ tsupport (a u) → ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ (j + 1) (ψ u) x‖ ≤ P j * R * L ^ j)
    (ha_bound : ∀ u x, x ∈ tsupport (a u) → ∀ r,
      ‖iteratedFDeriv ℝ r (a u) x‖ ≤ C r * (A * L ^ r)) :
    ‖complexMeasureIntegral ν (fun u ↦ ∫ x, phaseOscillation (ψ u) x • a u x ∂μ)‖ ≤
      ((transposeDerivativeConstant e (phaseCoefficientDerivativeBound e δ G P) C q 0 *
        (A * (L / R) ^ q)) * μ.real K) * ν.variation.real Set.univ := by
  have hB := transposeDerivativeConstant_nonneg e
    (phaseCoefficientDerivativeBound_nonneg e δ G P) hC q 0
  apply norm_complexMeasureIntegral_le ν _ (by positivity)
  apply Filter.Eventually.of_forall
  intro u
  apply (norm_vector_oscillatory_integral_le hU e (ψ u) (a u) q (hψ u) (ha u)
    ((hs u).trans hKU) (hK.of_isClosed_subset (isClosed_tsupport _) (hs u))
    hδ hA hL hR (hgap u) (hupper u) hC (hp u) (ha_bound u)).trans
  apply mul_le_mul_of_nonneg_left (measureReal_mono (hs u) hK.measure_lt_top.ne)
  positivity
end JanetCartan.Localization
