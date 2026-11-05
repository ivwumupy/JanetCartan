module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.LatticeRemainder.HeatBounds
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Integrable time majorants for the off-diagonal Bessel integral

The small-time Gaussian gap in `app:ch_background:prop:bg-frame`, Step 1,
absorbs every nonpositive time power. The consuming declarations are the
integrability and off-diagonal jet estimates for `imageBesselKernel`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace JanetCartan.ContinuumNormalReduction.ImageNormal

/-- Polynomial weights can be absorbed in exponential decay. This supplies
both the inverse-time and spatial bounds in `app:ch_background:prop:bg-frame`,
Step 1. -/
theorem exists_rpow_mul_exp_neg_mul_bound {q a : ℝ} (hq : 0 ≤ q) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 ≤ u → u ^ q * Real.exp (-a * u) ≤ C := by
  obtain ⟨R, hR⟩ := eventually_atTop.mp
    ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero q a ha).eventually_lt_const
      (show (0 : ℝ) < 1 by norm_num))
  have hc : Continuous (fun u : ℝ ↦ u ^ q * Real.exp (-a * u)) :=
    (Real.continuous_rpow_const hq).mul (by fun_prop)
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image
    (hc.continuousOn : ContinuousOn _ (Icc 0 (max 0 R)))
  refine ⟨max 1 B, le_trans zero_le_one (le_max_left _ _), fun u hu ↦ ?_⟩
  by_cases h : u ≤ max 0 R
  · exact (hB (mem_image_of_mem _ ⟨hu, h⟩)).trans (le_max_right _ _)
  · exact (hR u ((le_max_right 0 R).trans (le_of_not_ge h))).le.trans
      (le_max_left _ _)

/-- An off-diagonal Gaussian gap absorbs every nonpositive time power;
this is the integrable majorant used for differentiating the heat integral in
`app:ch_background:prop:bg-frame`, Step 1. -/
theorem integrableOn_rpow_mul_exp_neg_div_mul_exp_neg_mul
    {s a b : ℝ} (hs : s ≤ 0) (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ ↦ t ^ s * Real.exp (-a / t) * Real.exp (-b * t))
      (Ioi 0) := by
  obtain ⟨C, _, hC⟩ := exists_rpow_mul_exp_neg_mul_bound (neg_nonneg.mpr hs) ha
  have hc : ContinuousOn (fun t : ℝ ↦ t ^ s * Real.exp (-a / t) *
      Real.exp (-b * t)) (Ioi 0) := by
    apply ContinuousOn.mul
    · exact ((continuousOn_id.rpow_const (fun t ht ↦ Or.inl (ne_of_gt ht))).mul
        ((continuousOn_const.div continuousOn_id (fun t ht ↦ ne_of_gt ht) :
          ContinuousOn (fun t : ℝ ↦ -a / t) (Ioi 0)).rexp))
    · fun_prop
  refine ((exp_neg_integrableOn_Ioi 0 hb).const_mul C).mono'
    (hc.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change 0 < t at ht
  have h : t ^ s * Real.exp (-a / t) ≤ C := by
    simpa only [Real.inv_rpow (le_of_lt ht), Real.rpow_neg (le_of_lt ht), inv_inv,
      div_eq_mul_inv] using hC t⁻¹ (inv_nonneg.mpr (le_of_lt ht))
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_right h (Real.exp_pos _).le

/-- Integrability of the precise gap majorant supplied by `HeatBounds` for
`app:ch_background:prop:bg-frame`, Step 1. Extra inverse powers of time are
allowed for its later spatial derivatives. -/
theorem integrableOn_imageBessel_gap_majorant (d n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun t : ℝ ↦
      t ^ (-(1 : ℝ) / 2 - n) * (4 * Real.pi * t) ^ (-(d : ℝ) / 2) *
        Real.exp (-(δ ^ 2) / (8 * t)) * Real.exp (-t / 2)) (Ioi 0) := by
  have hi := (integrableOn_rpow_mul_exp_neg_div_mul_exp_neg_mul
    (s := -(1 : ℝ) / 2 - n - (d : ℝ) / 2) (a := δ ^ 2 / 8) (b := 1 / 2)
    (by have := Nat.cast_nonneg (α := ℝ) n; have := Nat.cast_nonneg (α := ℝ) d; linarith)
    (by positivity) (by positivity)).const_mul
      ((4 * Real.pi) ^ (-(d : ℝ) / 2))
  refine IntegrableOn.congr_fun hi ?_ measurableSet_Ioi
  intro t ht
  dsimp only
  rw [Real.mul_rpow (by positivity : 0 ≤ 4 * Real.pi) (le_of_lt ht)]
  rw [show -(1 : ℝ) / 2 - n - (d : ℝ) / 2 =
    (-(1 : ℝ) / 2 - n) + (-(d : ℝ) / 2) by ring,
    Real.rpow_add ht]
  rw [show -(δ ^ 2 / 8) / t = -(δ ^ 2) / (8 * t) by ring,
    show -(1 / 2 : ℝ) * t = -t / 2 by ring]
  ring

end JanetCartan.ContinuumNormalReduction.ImageNormal
