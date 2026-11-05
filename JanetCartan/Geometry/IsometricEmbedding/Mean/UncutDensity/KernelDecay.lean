module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.UncutDensity.WeightedPassage
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Reciprocal weighted kernel integrability

The analytic kernel hypothesis of the raw domain passage is proved from compact
angular carrier support and the literal half-order amplitude. These are the
geometric inputs of `app:ch_background:eq:bg-density-twice`; no upper frequency
cutoff or initial spatial cutoff is introduced.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace JanetCartan.UncutDensity
open ContinuumRow ContinuumAdjoint.DensityMultiplier

variable {n N : ℕ}

/-- Frequency decay sufficient for the literal kernel pairing in
`app:ch_background:eq:bg-density-twice`. The weight is the existing radian
transverse Bessel weight. -/
theorem memLp_inverse_transverse_weight (t : ℕ) (ht : n - 1 < 2 * t) :
    MemLp (fun η : Euclidean (n - 1) ↦ (Real.sqrt (1 + ‖η‖ ^ 2) ^ t)⁻¹) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm (show AEStronglyMeasurable
    (fun η : Euclidean (n - 1) ↦ (Real.sqrt (1 + ‖η‖ ^ 2) ^ t)⁻¹) volume from
      ((by fun_prop : Continuous (fun η : Euclidean (n - 1) ↦
        Real.sqrt (1 + ‖η‖ ^ 2) ^ t)).inv₀ (fun η ↦ by positivity)).aestronglyMeasurable)).mpr
  have hdim : (Module.finrank ℝ (Euclidean (n - 1)) : ℝ) < 2 * (t : ℝ) := by
    simpa using (show ((n - 1 : ℕ) : ℝ) < 2 * (t : ℝ) by exact_mod_cast ht)
  have hi := integrable_rpow_neg_one_add_norm_sq
    (μ := (volume : Measure (Euclidean (n - 1)))) hdim
  convert hi using 1
  funext η
  simp only [Real.norm_eq_abs, sq_abs, inv_pow, ← pow_mul]
  rw [Nat.mul_comm t 2, pow_mul, Real.sq_sqrt (by positivity)]
  rw [← Real.rpow_natCast, ← Real.rpow_neg (by positivity)]
  congr 1
  ring

/-- Compact carrier support and transverse decay give an actual product L²
majorant on Lebesgue `dz dη` (`app:ch_background:eq:bg-density-twice`). -/
theorem memLp_carrier_decay_envelope (t : ℕ) (ht : n - 1 < 2 * t)
    {K : Set CarrierParameter} (hK : IsCompact K) :
    MemLp (fun p : CarrierVariable n ↦
      K.indicator (fun _ ↦ (1 : ℝ)) p.1 * (etaBesselWeight t p)⁻¹)
      2 (carrierMeasure n) := by
  have hz := memLp_indicator_const 2
    (hK.measurableSet.nullMeasurableSet (μ := (volume.prod volume))) (1 : ℝ)
    (Or.inr hK.measure_ne_top)
  have hη := memLp_inverse_transverse_weight (n := n) t ht
  have hm : AEStronglyMeasurable (fun p : CarrierVariable n ↦
      K.indicator (fun _ ↦ (1 : ℝ)) p.1 * (etaBesselWeight t p)⁻¹)
      (carrierMeasure n) :=
    (((measurable_const.indicator hK.measurableSet).comp measurable_fst).mul
      (contDiff_inv_etaBesselWeight t).continuous.measurable).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  change Integrable _ ((volume.prod volume).prod volume)
  convert (hz.integrable_norm_pow (by decide : 2 ≠ 0)).mul_prod
    (hη.integrable_norm_pow (by decide : 2 ≠ 0)) using 1
  funext p
  simp only [norm_mul, mul_pow, etaBesselWeight]

/-- The literal kernel has precisely the half-order size dictated by its
angular mask, high cutoff, and measured stress
(`app:ch_background:eq:bg-density-twice`). -/
theorem norm_carrierKernel_le_halfOrder (d : CarrierData n N) (x : Torus n)
    (p : CarrierVariable n) {A B S : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hS : 0 ≤ S)
    (hρ : |d.angularCutoff p.1 (‖p.2‖⁻¹ • p.2)| ≤ A)
    (hhi : |d.highCutoff ‖p.2‖| ≤ B) (hst : ‖measuredStress d x p.1‖ ≤ S) :
    ‖carrierKernel d x p‖ ≤ (A * B * S) * Real.sqrt ‖p.2‖ := by
  by_cases hx : x ∈ d.outputChart
  · rw [carrierKernel_factor d hx, norm_smul, norm_mul,
      Complex.norm_exp_ofReal_mul_I, one_mul, euclideanComplexInclusion_norm]
    simp only [carrierDensitySymbol, densityFrequencySymbol, halfOrderCoefficient,
      angularHighMask, norm_mul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      _ ≤ (Real.sqrt ‖p.2‖ * (B * A)) * S := by gcongr
      _ = _ := by ring
  · rw [carrierKernel_eq_zero_outside d hx, norm_zero]
    positivity

/-- Derive reciprocal weighted kernel membership from primitive geometry.
The compact set controls only the original angular carrier support. Continuity
and bounds concern the original kernel and cutoffs, not a mean identity or a
new row (`app:ch_background:eq:bg-density-twice`). -/
theorem memLp_inverseWeight_carrierKernel (d : CarrierData n N) (t : ℕ)
    (ht : n - 1 < 2 * t) (x : Torus n)
    (hk : AEStronglyMeasurable (carrierKernel d x) (carrierMeasure n))
    {K : Set CarrierParameter} (hK : IsCompact K)
    (hsupp : ∀ z ∉ K, ∀ θ, d.angularCutoff z θ = 0)
    (hst : ContinuousOn (measuredStress d x) K)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hρ : ∀ z θ, |d.angularCutoff z θ| ≤ A)
    (hhi : ∀ r, |d.highCutoff r| ≤ B) :
    MemLp (fun p ↦ (etaBesselWeight (t + 1) p)⁻¹ • carrierKernel d x p)
      2 (carrierMeasure n) := by
  obtain ⟨S, hS⟩ := hK.exists_bound_of_continuousOn hst
  let C := A * B * max S 0
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply ((memLp_carrier_decay_envelope t ht hK).const_mul C).mono'
  · exact (contDiff_inv_etaBesselWeight (t + 1)).continuous.aestronglyMeasurable.smul hk
  · filter_upwards [] with p
    by_cases hp : p.1 ∈ K
    · simp only [Set.indicator_of_mem hp, one_mul, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr (etaBesselWeight_pos (t + 1) p))]
      have hb := norm_carrierKernel_le_halfOrder d x p hA hB (le_max_right S 0)
        (hρ _ _) (hhi _) ((hS _ hp).trans (le_max_left S 0))
      have hw : (etaBesselWeight (t + 1) p)⁻¹ * Real.sqrt ‖p.2‖ ≤
          (etaBesselWeight t p)⁻¹ := by
        rw [inv_mul_eq_div, div_le_iff₀ (etaBesselWeight_pos (t + 1) p),
          inv_mul_eq_div, le_div_iff₀ (etaBesselWeight_pos t p)]
        simpa [mul_comm] using etaBesselWeight_mul_sqrt_le t p
      calc
        _ ≤ (etaBesselWeight (t + 1) p)⁻¹ * (C * Real.sqrt ‖p.2‖) := by
          exact mul_le_mul_of_nonneg_left hb
            (inv_nonneg.mpr (etaBesselWeight_nonneg (t + 1) p))
        _ = C * ((etaBesselWeight (t + 1) p)⁻¹ * Real.sqrt ‖p.2‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hw hC
    · have hz : carrierKernel d x p = 0 := by
        classical
        by_cases hx : x ∈ d.outputChart <;>
          simp [carrierKernel, carrierAmplitude, hx, hsupp _ hp]
      simp [Set.indicator_of_notMem hp, hz]

end JanetCartan.UncutDensity
