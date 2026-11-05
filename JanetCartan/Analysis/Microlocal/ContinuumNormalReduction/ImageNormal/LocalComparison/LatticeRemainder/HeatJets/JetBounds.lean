module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.LatticeRemainder.HeatJets.TemporalMajorants
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Integrable bounds for all spatial heat jets

The Gaussian derivative estimates in `app:ch_background:prop:bg-frame`, Step 1,
provide the quantitative premise of
`imageBesselKernel_offDiagonal_of_integrable_jet_bounds`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.ContinuumNormalReduction.ImageNormal

variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

private theorem norm_iteratedFDeriv_norm_sq_le (i : ℕ) (hi : 1 ≤ i) (x : V) :
    ‖iteratedFDeriv ℝ i (fun y : V ↦ ‖y‖ ^ 2) x‖ ≤ 2 * (1 + ‖x‖) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  have hfd : fderiv ℝ (fun y : V ↦ ‖y‖ ^ 2) =
      (2 : ℝ) • (fun y : V ↦ innerSL ℝ y) := by
    ext y z
    simp [two_smul]
  rw [← norm_iteratedFDeriv_fderiv, hfd]
  rw [iteratedFDeriv_const_smul_apply
    ((innerSL ℝ (E := V)).contDiff.contDiffAt), norm_smul]
  norm_num only [Real.norm_ofNat]
  cases j with
  | zero =>
    rw [norm_iteratedFDeriv_zero, innerSL_apply_norm]
    nlinarith [norm_nonneg x]
  | succ j =>
    rw [← norm_iteratedFDeriv_fderiv]
    have he : fderiv ℝ (fun y : V ↦ innerSL ℝ y) = fun _ ↦ innerSL ℝ (E := V) := by
      funext y
      exact (innerSL ℝ (E := V)).fderiv
    rw [he]
    cases j with
    | zero =>
      rw [norm_iteratedFDeriv_zero]
      have := norm_innerSL_le ℝ (E := V)
      nlinarith [norm_nonneg x]
    | succ j =>
      simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero, mul_zero]
      positivity

private theorem norm_iteratedFDeriv_heat_phase_le {t : ℝ} (ht : 0 < t) (i : ℕ) (hi : 1 ≤ i) (x : V) :
    ‖iteratedFDeriv ℝ i (fun y : V ↦ -(‖y‖ ^ 2) / (4 * t)) x‖ ≤
      (2 * (1 + ‖x‖) * (1 + t⁻¹)) ^ i := by
  have he : (fun y : V ↦ -(‖y‖ ^ 2) / (4 * t)) =
      fun y : V ↦ (-1 / (4 * t)) • ‖y‖ ^ 2 := by
    funext y
    simp only [smul_eq_mul]
    ring
  rw [he, iteratedFDeriv_const_smul_apply'
    ((contDiff_norm_sq ℝ).contDiffAt), norm_smul]
  have ha : ‖(-1 : ℝ) / (4 * t)‖ ≤ 1 + t⁻¹ := by
    rw [norm_div, norm_neg, norm_one, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hsmall : 1 / (4 * t) ≤ t⁻¹ := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le ht (by linarith)
    linarith
  have hD : 1 ≤ 2 * (1 + ‖x‖) * (1 + t⁻¹) := by
    have := norm_nonneg x
    have := inv_pos.mpr ht
    nlinarith
  calc
    _ ≤ (1 + t⁻¹) * (2 * (1 + ‖x‖)) :=
      mul_le_mul ha (norm_iteratedFDeriv_norm_sq_le i hi x) (norm_nonneg _) (by positivity)
    _ = 2 * (1 + ‖x‖) * (1 + t⁻¹) := by ring
    _ ≤ _ := by simpa using pow_le_pow_right₀ hD hi

private theorem norm_iteratedFDeriv_heat_gaussian_le {t : ℝ} (ht : 0 < t) (n : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ n (fun y : V ↦ Real.exp (-(‖y‖ ^ 2) / (4 * t))) x‖ ≤
      (n.factorial : ℝ) * Real.exp (-(‖x‖ ^ 2) / (4 * t)) *
        (2 * (1 + ‖x‖) * (1 + t⁻¹)) ^ n := by
  apply norm_iteratedFDeriv_comp_le (N := ∞) Real.contDiff_exp
    ((contDiff_norm_sq ℝ).neg.div_const (4 * t)) (by simp)
  · intro i _
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate,
      Real.iter_deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  · intro i hi _
    exact norm_iteratedFDeriv_heat_phase_le ht i hi x

/-- Every spatial jet of the explicit heat integrand is controlled by the
original Gaussian times polynomial factors, as used in
`app:ch_background:prop:bg-frame`, Step 1. This supplies the derivative estimate
for `exists_imageBesselKernel_integrand_jet_majorant`. -/
theorem norm_imageBesselKernel_integrand_jet_le {t : ℝ} (ht : 0 < t) (n : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ n (fun y : V ↦
      t ^ (-(1 : ℝ) / 2) * Real.exp (-t) * imageBesselHeatKernel t y) x‖ ≤
      (n.factorial : ℝ) * (2 * (1 + ‖x‖) * (1 + t⁻¹)) ^ n *
        (t ^ (-(1 : ℝ) / 2) * Real.exp (-t) * imageBesselHeatKernel t x) := by
  let a : ℝ := t ^ (-(1 : ℝ) / 2) * Real.exp (-t) *
    (4 * Real.pi * t) ^ (-(d : ℝ) / 2)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have he : (fun y : V ↦ t ^ (-(1 : ℝ) / 2) * Real.exp (-t) *
      imageBesselHeatKernel t y) =
      fun y : V ↦ a • Real.exp (-(‖y‖ ^ 2) / (4 * t)) := by
    funext y
    simp only [a, imageBesselHeatKernel, smul_eq_mul]
    ring
  rw [he, iteratedFDeriv_const_smul_apply'
    ((((contDiff_norm_sq ℝ).neg.div_const (4 * t)).exp).contDiffAt), norm_smul,
    Real.norm_eq_abs, abs_of_nonneg ha]
  calc
    _ ≤ a * ((n.factorial : ℝ) * Real.exp (-(‖x‖ ^ 2) / (4 * t)) *
        (2 * (1 + ‖x‖) * (1 + t⁻¹)) ^ n) :=
      mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_heat_gaussian_le ht n x) ha
    _ = _ := by simp only [a, imageBesselHeatKernel]; ring

private theorem one_add_pow_le_two_pow_mul {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    (1 + u) ^ n ≤ 2 ^ n * (1 + u ^ n) := by
  by_cases h : u ≤ 1
  · calc
      _ ≤ (2 : ℝ) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
      _ ≤ _ := le_mul_of_one_le_right (by positivity)
        (le_add_of_nonneg_right (pow_nonneg hu n))
  · have h' : 1 ≤ u := le_of_not_ge h
    calc
      _ ≤ (2 * u) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
      _ = 2 ^ n * u ^ n := mul_pow _ _ _
      _ ≤ _ := by gcongr; linarith

/-- An integrable time majorant for every polynomially weighted spatial jet
of the actual Bessel heat integrand, derived from its explicit Gaussian
(`app:ch_background:prop:bg-frame`, Step 1). This discharges the quantitative
premise of `imageBesselKernel_offDiagonal_of_integrable_jet_bounds`. -/
theorem exists_imageBesselKernel_integrand_jet_majorant (δ : ℝ) (hδ : 0 < δ) (n m : ℕ) : ∃ B : ℝ → ℝ,
    IntegrableOn B (Ioi 0) ∧ ∀ t : ℝ, 0 < t → ∀ x : V, δ ≤ ‖x‖ →
      (1 + ‖x‖) ^ m * ‖iteratedFDeriv ℝ n
        (fun y : V ↦ t ^ (-(1 : ℝ) / 2) * Real.exp (-t) * imageBesselHeatKernel t y) x‖
        ≤ B t := by
  let G : ℕ → ℝ → ℝ := fun k t ↦
    t ^ (-(1 : ℝ) / 2 - k) * (4 * Real.pi * t) ^ (-(d : ℝ) / 2) *
      Real.exp (-(δ ^ 2) / (8 * t)) * Real.exp (-t / 2)
  have hG (k : ℕ) : IntegrableOn (G k) (Ioi 0) :=
    integrableOn_imageBessel_gap_majorant d k hδ
  obtain ⟨C, hC, hpoly⟩ := exists_rpow_mul_exp_neg_mul_bound
    (q := ((m + n : ℕ) : ℝ)) (a := 1 / 2) (by positivity) (by positivity)
  let K : ℝ := (n.factorial : ℝ) * 2 ^ n * (C * Real.exp (1 / 2))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨fun t ↦ K * (2 ^ n * (G 0 t + G n t)),
    (((hG 0).add (hG n)).const_mul (2 ^ n)).const_mul K, ?_⟩
  intro t ht x hx
  have hG0 : 0 ≤ G 0 t := by dsimp [G]; positivity
  have htime : (1 + t⁻¹) ^ n * G 0 t ≤ 2 ^ n * (G 0 t + G n t) := by
    have he : t⁻¹ ^ n * G 0 t = G n t := by
      simp only [G, Nat.cast_zero, sub_zero]
      rw [Real.rpow_sub ht, Real.rpow_natCast]
      simp only [inv_pow, div_eq_mul_inv]
      ring
    calc
      _ ≤ (2 ^ n * (1 + t⁻¹ ^ n)) * G 0 t :=
        mul_le_mul_of_nonneg_right (one_add_pow_le_two_pow_mul (by positivity) n) hG0
      _ = 2 ^ n * (G 0 t + t⁻¹ ^ n * G 0 t) := by ring
      _ = _ := by rw [he]
  have hspace : (1 + ‖x‖) ^ (m + n) * Real.exp (-‖x‖ / 2) ≤
      C * Real.exp (1 / 2) := by
    have h := mul_le_mul_of_nonneg_right (hpoly (1 + ‖x‖) (by positivity))
      (Real.exp_pos (1 / 2)).le
    rw [Real.rpow_natCast, mul_assoc, ← Real.exp_add,
      show -(1 / 2 : ℝ) * (1 + ‖x‖) + 1 / 2 = -‖x‖ / 2 by ring] at h
    exact h
  have hgap : t ^ (-(1 : ℝ) / 2) * Real.exp (-t) * imageBesselHeatKernel t x ≤
      G 0 t * Real.exp (-‖x‖ / 2) := by
    simpa only [G, Nat.cast_zero, sub_zero] using
      imageBessel_integrand_le_gap_exponential ht hδ.le x hx
  calc
    _ ≤ (1 + ‖x‖) ^ m * ((n.factorial : ℝ) *
        (2 * (1 + ‖x‖) * (1 + t⁻¹)) ^ n *
        (t ^ (-(1 : ℝ) / 2) * Real.exp (-t) * imageBesselHeatKernel t x)) :=
      mul_le_mul_of_nonneg_left (norm_imageBesselKernel_integrand_jet_le ht n x)
        (by positivity)
    _ ≤ (1 + ‖x‖) ^ m * ((n.factorial : ℝ) *
        (2 * (1 + ‖x‖) * (1 + t⁻¹)) ^ n *
        (G 0 t * Real.exp (-‖x‖ / 2))) := by gcongr
    _ = (n.factorial : ℝ) * 2 ^ n *
        ((1 + ‖x‖) ^ (m + n) * Real.exp (-‖x‖ / 2)) *
        ((1 + t⁻¹) ^ n * G 0 t) := by rw [pow_add]; simp only [mul_pow]; ring
    _ ≤ K * ((1 + t⁻¹) ^ n * G 0 t) := by
      dsimp [K]
      gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_left htime hK

end JanetCartan.ContinuumNormalReduction.ImageNormal
