module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.WeightedPrincipalLocalization.CommutatorBounds.SourceIndependentBounds.KernelSobolev.Weights
public import JanetCartan.Analysis.Extension.Mollification.Lp

/-!
# The scalar frequency-majorant convolution bound

The fixed integrable majorant from Step 1 of
`app:ch_regular_base:thm:actual-calculus` acts boundedly on L². Cauchy–Schwarz
against its density and Tonelli give the bound used by the weighted
Schwartz integral in `app:ch_regular_base:eq:fio-input`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open JanetCartan.Mollification
namespace JanetCartan.FourierIntegral.WeightedPrincipalLocalization.SourceIndependentBounds
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

private theorem enorm_integral_sq_le_mass {α F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ν : Measure α}
    {f : α → F} (hf : AEStronglyMeasurable f ν) :
    ‖∫ x, f x ∂ν‖ₑ ^ 2 ≤ (∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν) * ν Set.univ := by
  have h : ‖∫ x, f x ∂ν‖ₑ ≤ eLpNorm f 2 ν * ν Set.univ ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ ∫⁻ x, ‖f x‖ₑ ∂ν := enorm_integral_le_lintegral_enorm _
      _ = eLpNorm f 1 ν := (eLpNorm_one_eq_lintegral_enorm hf).symm
      _ ≤ _ := by
        convert eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2)
          (by norm_num) hf using 1; norm_num
  have hh := pow_le_pow_left' h 2
  rw [mul_pow, eLpNorm_two_sq hf] at hh
  simpa only [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
    show (1 / 2 : ℝ) * (2 : ℕ) = 1 by norm_num, ENNReal.rpow_one] using hh

/-- Continuity of the fixed Schur majorant in Step 1 of
`app:ch_regular_base:thm:actual-calculus`. Consumer: the weighted Schwartz
integral and its measurable sections. -/
theorem continuous_frequencyDifferenceMajorant : Continuous (frequencyDifferenceMajorant (n := n)) := by
  unfold frequencyDifferenceMajorant
  exact (continuous_const.add continuous_norm).rpow_const (fun x ↦ Or.inl (ne_of_gt (by positivity : (0 : ℝ) < 1 + ‖x‖)))

/-- The L¹–L² convolution estimate for the fixed frequency majorant.
This is the analytic Schur input to `exists_frequencyKernel_weighted_schwartz_constant`
and hence to `app:ch_regular_base:eq:fio-input`. -/
theorem eLpNorm_frequencyMajorant_convolution_le (f : E → ℝ) (hf : StronglyMeasurable f) :
    eLpNorm (fun x ↦ ∫ y, frequencyDifferenceMajorant y * f (x - y)) 2 volume ≤
      (∫⁻ y : E, ENNReal.ofReal (frequencyDifferenceMajorant y)) * eLpNorm f 2 volume := by
  let ν : Measure E := volume.withDensity (fun y ↦ ENNReal.ofReal (frequencyDifferenceMajorant y))
  let M : ℝ≥0∞ := ∫⁻ y : E, ENNReal.ofReal (frequencyDifferenceMajorant y)
  have hν : ν Set.univ = M := by simp [ν, M, withDensity_apply]
  have hM : M < ∞ := by
    dsimp [M]
    rw [← ofReal_integral_eq_lintegral_ofReal integrable_frequencyDifferenceMajorant
      (.of_forall frequencyDifferenceMajorant_nonneg)]
    exact ENNReal.ofReal_lt_top
  let : IsFiniteMeasure ν := ⟨hν ▸ hM⟩
  have he (x : E) : (∫ y, frequencyDifferenceMajorant y * f (x - y)) =
      ∫ y, f (x - y) ∂ν := by
    change _ = ∫ y, f (x - y) ∂volume.withDensity _
    rw [integral_withDensity_eq_integral_toReal_smul
      continuous_frequencyDifferenceMajorant.measurable.ennreal_ofReal (.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (frequencyDifferenceMajorant_nonneg _), smul_eq_mul]
  have hm : StronglyMeasurable (fun x ↦ ∫ y, f (x - y) ∂ν) :=
    (hf.comp_measurable (measurable_fst.sub measurable_snd)).integral_prod_right'
  simp_rw [he]
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from rfl, ENNReal.rpow_natCast, ENNReal.rpow_natCast,
    mul_pow, eLpNorm_two_sq hm.aestronglyMeasurable]
  calc
    _ ≤ ∫⁻ x : E, (∫⁻ y, ‖f (x - y)‖ₑ ^ 2 ∂ν) * M := by
      apply lintegral_mono
      intro x
      simpa only [hν] using enorm_integral_sq_le_mass (ν := ν) (f := fun y ↦ f (x - y))
        (hf.comp_measurable (measurable_const.sub measurable_id)).aestronglyMeasurable
    _ = (∫⁻ y, ∫⁻ x : E, ‖f (x - y)‖ₑ ^ 2 ∂volume ∂ν) * M := by
      rw [lintegral_mul_const]
      · congr 1
        exact lintegral_lintegral_swap
          ((hf.comp_measurable (measurable_fst.sub measurable_snd)).enorm.pow_const 2).aemeasurable
      · exact Measurable.lintegral_prod_right
          ((hf.comp_measurable (measurable_fst.sub measurable_snd)).enorm.pow_const 2)
    _ = M ^ 2 * eLpNorm f 2 volume ^ 2 := by
      simp_rw [lintegral_sub_right_eq_self (fun x ↦ ‖f x‖ₑ ^ 2)]
      rw [lintegral_const, hν, eLpNorm_two_sq hf.aestronglyMeasurable]
      ring
end JanetCartan.FourierIntegral.WeightedPrincipalLocalization.SourceIndependentBounds
