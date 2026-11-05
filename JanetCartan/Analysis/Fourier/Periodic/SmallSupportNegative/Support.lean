module

public import JanetCartan.Analysis.Fourier.Periodic.Parseval
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Volume and Fourier coefficient bounds on small torus supports

The support estimates for Step 3 of `app:ch_background:prop:bg-frame` in `paper.tex`.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace JanetCartan

variable {n : ℕ}

/-- A measurable coordinate box containing the small quotient ball in
`app:ch_background:prop:bg-frame`, Step 3. -/
def torusSupportBox (n : ℕ) (r : ℝ) : Set (Torus n) :=
  Set.univ.pi (fun _ ↦ Metric.closedBall (0 : AddCircle (1 : ℝ)) r)

/-- Measurability of the support box used in `app:ch_background:prop:bg-frame`. -/
theorem measurableSet_torusSupportBox (r : ℝ) : MeasurableSet (torusSupportBox n r) :=
  MeasurableSet.univ_pi (fun _ ↦ measurableSet_closedBall)

/-- The Euclidean quotient ball lies in the coordinate box
(`app:ch_background:prop:bg-frame`, Step 3). -/
theorem torusQuotient_ball_subset_supportBox (r : ℝ) :
    torusQuotient '' Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r ⊆ torusSupportBox n r := by
  rintro _ ⟨x, hx, rfl⟩ i _
  have hxnorm : ‖x‖ < r := by simpa using hx
  rw [Metric.mem_closedBall, dist_zero_right]
  exact QuotientAddGroup.norm_mk_le_norm.trans
    ((PiLp.norm_apply_le x i).trans hxnorm.le)

/-- The coordinate box has volume `(2r)^n` on the unit torus
(`app:ch_background:prop:bg-frame`, Step 3). -/
theorem volume_torusSupportBox {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1 / 4) :
    (volume (torusSupportBox n r)).toReal = (2 * r) ^ n := by
  change ((Measure.pi (fun _ : Fin n ↦ (volume : Measure (AddCircle (1 : ℝ)))))
    (Set.univ.pi _)).toReal = _
  rw [Measure.pi_pi]
  simp only [AddCircle.volume_closedBall, min_eq_right (by linarith : 2 * r ≤ 1),
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * r)]

variable {E : Type*} [NormedAddCommGroup E]

/-- Cauchy–Schwarz on a measurable support, used in Step 3 of
`app:ch_background:prop:bg-frame`. The field need only vanish off the support a.e. -/
theorem integral_norm_le_sqrt_volume_mul_periodicL2Norm {f : Torus n → E}
    (hf : MemLp f 2) (s : Set (Torus n))
    (hs : ∀ᵐ x, x ∉ s → f x = 0) :
    (∫ x, ‖f x‖) ≤ Real.sqrt (volume s).toReal * periodicL2Norm f := by
  have heq (p : ℕ) (hp : p ≠ 0) : (∫ x in s, ‖f x‖ ^ p) = ∫ x, ‖f x‖ ^ p := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [hs] with x hx hxs
    simp [hx hxs, hp]
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict s)
    Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall (fun x ↦ norm_nonneg (f x)))
    (Filter.Eventually.of_forall (fun _ ↦ (zero_le_one : (0 : ℝ) ≤ 1)))
    (by simpa using hf.norm.restrict s) (by simpa using (memLp_const (μ := volume.restrict s) (p := 2) (1 : ℝ)))
  simp only [mul_one, Real.rpow_two, one_pow, integral_const,
    smul_eq_mul, mul_one] at h
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, heq 2 (by decide)] at h
  have heq1 : (∫ x in s, ‖f x‖) = ∫ x, ‖f x‖ := by simpa using heq 1 (by decide)
  rw [heq1] at h
  simpa only [periodicL2Norm, mul_comm, Measure.real, Measure.restrict_apply_univ] using h

variable [NormedSpace ℝ E]

/-- Each real component of a periodic coefficient is bounded by the L¹ norm
(`app:ch_background:prop:bg-frame`, Step 3). -/
theorem norm_periodicFourierCoeff_components_le_integral {f : Torus n → E}
    (hf : MemLp f 2) (k : Fin n → ℤ) :
    ‖(periodicFourierCoeff f k).1‖ ≤ ∫ x, ‖f x‖ ∧
    ‖(periodicFourierCoeff f k).2‖ ≤ ∫ x, ‖f x‖ := by
  have h (a : ℂ → ℝ) (ha : ∀ z, |a z| ≤ ‖z‖) :
      ‖∫ x, a (UnitAddTorus.mFourier (-k) x) • f x‖ ≤ ∫ x, ‖f x‖ := by
    apply norm_integral_le_of_norm_le (hf.integrable (by norm_num)).norm
    apply Filter.Eventually.of_forall
    intro x
    rw [norm_smul, Real.norm_eq_abs]
    apply mul_le_of_le_one_left (norm_nonneg _)
    exact (ha _).trans (by simpa only [UnitAddTorus.mFourier_norm] using
      (UnitAddTorus.mFourier (-k)).norm_coe_le_norm x)
  exact ⟨h Complex.re Complex.abs_re_le_norm, h Complex.im Complex.abs_im_le_norm⟩

/-- A coefficient-energy bound proportional to support volume, for the low-frequency
part of `app:ch_background:prop:bg-frame`, Step 3. -/
theorem sq_periodicFourierCoeff_le_support_volume {f : Torus n → E}
    (hf : MemLp f 2) (s : Set (Torus n))
    (hs : ∀ᵐ x, x ∉ s → f x = 0) (k : Fin n → ℤ) :
    ‖(periodicFourierCoeff f k).1‖ ^ 2 + ‖(periodicFourierCoeff f k).2‖ ^ 2 ≤
      2 * (volume s).toReal * periodicL2Norm f ^ 2 := by
  have h := norm_periodicFourierCoeff_components_le_integral hf k
  have hcs := integral_norm_le_sqrt_volume_mul_periodicL2Norm hf s hs
  have hnonneg : 0 ≤ Real.sqrt (volume s).toReal * periodicL2Norm f := by
    unfold periodicL2Norm
    positivity
  have ha := sq_le_sq₀ (norm_nonneg _) hnonneg |>.mpr (h.1.trans hcs)
  have hb := sq_le_sq₀ (norm_nonneg _) hnonneg |>.mpr (h.2.trans hcs)
  rw [mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg] at ha hb
  nlinarith

/-- The small-ball Fourier coefficient estimate in Step 3 of
`app:ch_background:prop:bg-frame`, valid for a.e. support in the quotient ball. -/
theorem sq_periodicFourierCoeff_le_small_support {f : Torus n → E}
    (hf : MemLp f 2) {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1 / 4)
    (hs : ∀ᵐ x, x ∉ torusQuotient '' Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r →
      f x = 0) (k : Fin n → ℤ) :
    ‖(periodicFourierCoeff f k).1‖ ^ 2 + ‖(periodicFourierCoeff f k).2‖ ^ 2 ≤
      2 * (2 * r) ^ n * periodicL2Norm f ^ 2 := by
  rw [← volume_torusSupportBox hr.le hr']
  apply sq_periodicFourierCoeff_le_support_volume hf
  filter_upwards [hs] with x hx hxs
  exact hx (fun hball ↦ hxs (torusQuotient_ball_subset_supportBox r hball))

end JanetCartan
