module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.LatticeRemainder.HeatJets.TemporalMajorants

/-!
# Integrability and zeroth-order decay of the Bessel heat integral

These results start from the explicit normalized integral in `KernelDefinitions`.
They supply the base case for the off-diagonal differentiation in
`app:ch_background:prop:bg-frame`, Step 1.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace JanetCartan.ContinuumNormalReduction.ImageNormal

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Positive-time continuity of the actual Bessel integrand
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem continuousOn_imageBesselKernel_integrand (x : E) :
    ContinuousOn (fun t : ℝ ↦
      t ^ (-(1 : ℝ) / 2) * Real.exp (-t) * imageBesselHeatKernel t x) (Ioi 0) := by
  intro t ht
  apply ContinuousAt.continuousWithinAt
  unfold imageBesselHeatKernel
  have ht' : t ≠ 0 := ne_of_gt ht
  have hbase : 4 * Real.pi * t ≠ 0 := mul_ne_zero (by positivity) ht'
  fun_prop (disch := aesop)

/-- The positive heat integrand satisfies the norm bound needed by dominated
integration (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem norm_imageBesselKernel_integrand_le_gap_exponential {δ t : ℝ}
    (hδ : 0 ≤ δ) (ht : 0 < t) (x : E) (hx : δ ≤ ‖x‖) :
    ‖t ^ (-(1 : ℝ) / 2) * Real.exp (-t) * imageBesselHeatKernel t x‖ ≤
      (t ^ (-(1 : ℝ) / 2) * (4 * Real.pi * t) ^ (-(d : ℝ) / 2) *
        Real.exp (-(δ ^ 2) / (8 * t)) * Real.exp (-t / 2)) *
        Real.exp (-‖x‖ / 2) := by
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (by positivity) (imageBesselHeatKernel_pos ht x).le)]
  exact imageBessel_integrand_le_gap_exponential ht hδ x hx

/-- Integrability of the explicit time integrand at every nonzero spatial
point (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem integrableOn_imageBesselKernel_integrand {x : E} (hx : x ≠ 0) :
    IntegrableOn (fun t : ℝ ↦
      t ^ (-(1 : ℝ) / 2) * Real.exp (-t) * imageBesselHeatKernel t x) (Ioi 0) := by
  have hi := (integrableOn_imageBessel_gap_majorant d 0 (norm_pos_iff.mpr hx)).mul_const
    (Real.exp (-‖x‖ / 2))
  simp only [Nat.cast_zero, sub_zero] at hi
  refine hi.mono' ((continuousOn_imageBesselKernel_integrand x).aestronglyMeasurable
    measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact norm_imageBesselKernel_integrand_le_gap_exponential (norm_nonneg x) ht x le_rfl

/-- Uniform exponential decay of the actual normalized Bessel kernel outside
any positive gap (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem exists_imageBesselKernel_offDiagonal_exponential_decay {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, δ ≤ ‖x‖ →
      ‖imageBesselKernel x‖ ≤ C * Real.exp (-‖x‖ / 2) := by
  let A : ℝ → ℝ := fun t ↦
    t ^ (-(1 : ℝ) / 2) * (4 * Real.pi * t) ^ (-(d : ℝ) / 2) *
      Real.exp (-(δ ^ 2) / (8 * t)) * Real.exp (-t / 2)
  have hi : IntegrableOn A (Ioi 0) := by
    simpa only [Nat.cast_zero, sub_zero] using integrableOn_imageBessel_gap_majorant d 0 hδ
  have hI : 0 ≤ ∫ t in Ioi (0 : ℝ), A t := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    dsimp [A]
    positivity
  refine ⟨(Real.sqrt Real.pi)⁻¹ * ∫ t in Ioi (0 : ℝ), A t, by positivity, fun x hx ↦ ?_⟩
  have hb : ‖∫ t in Ioi (0 : ℝ),
      t ^ (-(1 : ℝ) / 2) * Real.exp (-t) * imageBesselHeatKernel t x‖ ≤
      (∫ t in Ioi (0 : ℝ), A t) * Real.exp (-‖x‖ / 2) := by
    rw [← integral_mul_const]
    apply norm_integral_le_of_norm_le (hi.mul_const _)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact norm_imageBesselKernel_integrand_le_gap_exponential hδ.le ht x hx
  rw [imageBesselKernel, norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (Real.sqrt Real.pi)⁻¹), mul_assoc]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

/-- All polynomially weighted zeroth-order bounds of the explicit Bessel
kernel (`app:ch_background:prop:bg-frame`, Step 1). Higher spatial derivatives
require the separate differentiation-under-the-integral argument. -/
theorem exists_imageBesselKernel_offDiagonal_decay {δ : ℝ} (hδ : 0 < δ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, δ ≤ ‖x‖ →
      (1 + ‖x‖) ^ m * ‖imageBesselKernel x‖ ≤ C := by
  obtain ⟨B, hB, hbound⟩ := exists_imageBesselKernel_offDiagonal_exponential_decay
    (d := d) hδ
  obtain ⟨D, hD, hpoly⟩ := exists_rpow_mul_exp_neg_mul_bound
    (q := (m : ℝ)) (a := 1 / 2) (by positivity) (by positivity)
  refine ⟨B * (D * Real.exp (1 / 2)), by positivity, fun x hx ↦ ?_⟩
  have hw : (1 + ‖x‖) ^ m * Real.exp (-‖x‖ / 2) ≤ D * Real.exp (1 / 2) := by
    have h := mul_le_mul_of_nonneg_right (hpoly (1 + ‖x‖) (by positivity))
      (Real.exp_pos (1 / 2)).le
    rw [Real.rpow_natCast, mul_assoc, ← Real.exp_add,
      show -(1 / 2 : ℝ) * (1 + ‖x‖) + 1 / 2 = -‖x‖ / 2 by ring] at h
    exact h
  calc
    _ ≤ (1 + ‖x‖) ^ m * (B * Real.exp (-‖x‖ / 2)) :=
      mul_le_mul_of_nonneg_left (hbound x hx) (by positivity)
    _ = B * ((1 + ‖x‖) ^ m * Real.exp (-‖x‖ / 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hw hB

end JanetCartan.ContinuumNormalReduction.ImageNormal
