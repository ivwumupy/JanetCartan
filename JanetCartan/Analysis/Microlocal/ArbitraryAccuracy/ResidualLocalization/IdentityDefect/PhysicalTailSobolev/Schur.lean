module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.WeightedPrincipalLocalization.CommutatorBounds.SourceIndependentBounds.KernelSobolev.Forward.Integral.Convolution

/-!
# The physical-tail Schur estimate

The spatial weight in `app:ch_regular:eq:chain-tail` is the same integrable
Euclidean majorant already used for the frequency-kernel estimate. This leaf
applies that convolution bound to the actual output-jet integrands. Its
constant depends only on dimension, before the kernel and its budget.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ENNReal

namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.PhysicalTailSobolev

open FourierIntegral.WeightedPrincipalLocalization.SourceIndependentBounds

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The mass of the existing Euclidean Schur majorant. Consumer: the
physical-tail output jets in `app:ch_regular:eq:chain-tail`. -/
def physicalTailSchurConstant (n : ℕ) : ℝ :=
  (∫⁻ y : EuclideanSpace ℝ (Fin n),
    ENNReal.ofReal (frequencyDifferenceMajorant y)).toReal

/-- Nonnegativity of the fixed spatial Schur constant
(`app:ch_regular:eq:chain-tail`). -/
theorem physicalTailSchurConstant_nonneg : 0 ≤ physicalTailSchurConstant n :=
  ENNReal.toReal_nonneg

/-- The stated polynomial jet bound is precisely the existing Schur
majorant bound; no extra spatial reserve is used
(`app:ch_regular:eq:chain-tail`). -/
theorem le_physicalTailMajorant {B z : ℝ} (x y : E)
    (h : (1 + ‖x - y‖) ^ (n + 1) * z ≤ B) :
    z ≤ B * frequencyDifferenceMajorant (x - y) := by
  have hw : 0 < (1 + ‖x - y‖) ^ (n + 1) := by positivity
  have he : frequencyDifferenceMajorant (x - y) = ((1 + ‖x - y‖) ^ (n + 1))⁻¹ := by
    rw [frequencyDifferenceMajorant, Real.rpow_neg (by positivity)]
    simp only [← Nat.cast_add_one, Real.rpow_natCast]
  rw [he, ← div_eq_mul_inv]
  exact (le_div_iff₀ hw).mpr (by simpa only [mul_comm] using h)

/-- The literal physical output-jet integral is L² with the Schur bound.
The only analytic premise is pointwise domination of its integrand; its
producer is the output-jet formula and the kernel-jet hypothesis. This
lemma is used for each classical derivative before the weak-jet/Fourier
comparison in `app:ch_regular:eq:chain-tail`. -/
theorem physicalTail_integral_memLp_bound
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (j : E → E → F) (hj : StronglyMeasurable (Function.uncurry j))
    (f : E → ℝ) (hf : StronglyMeasurable f) (hf0 : ∀ y, 0 ≤ f y)
    (hf1 : Integrable f) (hf2 : MemLp f 2 volume)
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ x y, ‖j x y‖ ≤ B * (frequencyDifferenceMajorant (x - y) * f y)) :
    (∀ x, Integrable (j x)) ∧
    MemLp (fun x ↦ ∫ y, j x y) 2 volume ∧
      (eLpNorm (fun x ↦ ∫ y, j x y) 2 volume).toReal ≤
        physicalTailSchurConstant n * B * (eLpNorm f 2 volume).toReal := by
  let M : ℝ≥0∞ := ∫⁻ y : E, ENNReal.ofReal (frequencyDifferenceMajorant y)
  have hM : M < ∞ := by
    dsimp [M]
    rw [← ofReal_integral_eq_lintegral_ofReal integrable_frequencyDifferenceMajorant
      (.of_forall frequencyDifferenceMajorant_nonneg)]
    exact ENNReal.ofReal_lt_top
  have hgi (x : E) : Integrable (fun y ↦ frequencyDifferenceMajorant (x - y) * f y) :=
    hf1.bdd_mul
      (continuous_frequencyDifferenceMajorant.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (.of_forall (fun y ↦ by
        rw [Real.norm_of_nonneg (frequencyDifferenceMajorant_nonneg _)]
        exact frequencyDifferenceMajorant_le_one _))
  have hji (x : E) : Integrable (j x) :=
    ((hgi x).const_mul B).mono'
      (hj.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (.of_forall (hb x))
  let q : E → ℝ := fun x ↦ ∫ y, frequencyDifferenceMajorant y * f (x - y)
  have hq (x : E) : (∫ y, frequencyDifferenceMajorant (x - y) * f y) = q x := by
    simpa only [q, sub_sub_cancel] using
      integral_sub_left_eq_self (fun y ↦ frequencyDifferenceMajorant y * f (x - y)) volume x
  have hq0 (x : E) : 0 ≤ q x :=
    integral_nonneg (fun y ↦ mul_nonneg (frequencyDifferenceMajorant_nonneg _) (hf0 _))
  have hbound (x : E) : ‖∫ y, j x y‖ ≤ B * q x := by
    rw [← hq, ← integral_const_mul]
    exact norm_integral_le_of_norm_le ((hgi x).const_mul B) (.of_forall (hb x))
  have hqnorm : eLpNorm q 2 volume ≤ M * eLpNorm f 2 volume :=
    eLpNorm_frequencyMajorant_convolution_le f hf
  have hq2 : MemLp q 2 volume := hqnorm.trans_lt (ENNReal.mul_lt_top hM hf2.eLpNorm_lt_top)
  have hF2 : MemLp (fun x ↦ ∫ y, j x y) 2 volume :=
    (hq2.const_smul B).mono' hj.integral_prod_right.aestronglyMeasurable
      (.of_forall hbound)
  refine ⟨hji, hF2, ?_⟩
  have hn : eLpNorm (fun x ↦ ∫ y, j x y) 2 volume ≤
      ENNReal.ofReal B * (M * eLpNorm f 2 volume) := by
    calc
      _ ≤ eLpNorm (B • q) 2 volume :=
        eLpNorm_mono hj.integral_prod_right.aestronglyMeasurable (fun x ↦ by
          simpa only [Pi.smul_apply, smul_eq_mul,
            Real.norm_of_nonneg (mul_nonneg hB (hq0 x))] using hbound x)
      _ = ENNReal.ofReal B * eLpNorm q 2 volume := by
        rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hB]
      _ ≤ _ := mul_le_mul' le_rfl hqnorm
  have hfin : ENNReal.ofReal B * (M * eLpNorm f 2 volume) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top hM.ne hf2.eLpNorm_ne_top)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB,
    physicalTailSchurConstant, M, mul_left_comm, mul_assoc] using
      ENNReal.toReal_mono hfin hn

end JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.PhysicalTailSobolev
