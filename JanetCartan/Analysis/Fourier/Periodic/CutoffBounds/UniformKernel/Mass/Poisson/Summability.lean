module

public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.UniformKernel.Mass.Euclidean
public import JanetCartan.Analysis.Fourier.Periodic.Lattice
public import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Convergence of the Euclidean cutoff periodization

For `main:lem:smoothing` and `main:eq:smoothing-low`, every derivative of a
Schwartz function has a summable lattice majorant locally in the translation
variable. These estimates apply to the exact fixed Euclidean cutoff.
-/

@[expose] public noncomputable section

open scoped SchwartzMap ContDiff

namespace JanetCartan

/-- `main:lem:smoothing`: a summable weight on the integer frequency lattice,
with an exponent strictly larger than the dimension. -/
theorem summable_one_add_frequencyNorm_inv_pow (n : ℕ) :
    Summable (fun k : Fin n → ℤ ↦ ((1 + frequencyNorm k) ^ (n + 1))⁻¹) := by
  apply (finite_frequencyNorm_le n 1).summable_compl_iff.mp
  refine ((summable_frequencyNorm_rpow (n := n)
    (p := (n + 1 : ℕ)) (by exact_mod_cast Nat.lt_succ_self n)).subtype _).of_nonneg_of_le
    (fun k ↦ by
      dsimp only [Function.comp_apply]
      exact inv_nonneg.mpr (pow_nonneg (by linarith [frequencyNorm_nonneg k.val]) _)) ?_
  intro k
  have hk : 1 < frequencyNorm k.val := lt_of_not_ge k.property
  dsimp only [Function.comp_apply]
  rw [Real.rpow_neg (frequencyNorm_nonneg _), Real.rpow_natCast]
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) _)

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `main:lem:smoothing`: all derivatives of a Schwartz function admit
summable lattice bounds uniformly on each bounded ball of translations. -/
theorem exists_summable_bound_iteratedFDeriv_schwartz_lattice
    (f : 𝓢(EuclideanSpace ℝ (Fin n), F)) (j : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    ∃ u : (Fin n → ℤ) → ℝ, Summable u ∧
      ∀ (k : Fin n → ℤ) (x : EuclideanSpace ℝ (Fin n)), ‖x‖ ≤ r →
        ‖iteratedFDeriv ℝ j f (x + WithLp.toLp 2 (fun i ↦ (k i : ℝ)))‖ ≤ u k := by
  let p := n + 1
  let C : ℝ := 2 ^ p * (Finset.Iic (p, j)).sup
    (fun m ↦ SchwartzMap.seminorm ℝ m.1 m.2) f
  let A : ℝ := 1 + 2 * Real.pi + 2 * Real.pi * r
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨fun k ↦ (A ^ p * C) * ((1 + frequencyNorm k) ^ p)⁻¹,
    (summable_one_add_frequencyNorm_inv_pow n).mul_left _, ?_⟩
  intro k x hx
  let z : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i ↦ (k i : ℝ))
  have hz : ‖z‖ ≤ ‖x + z‖ + r := by
    have h := norm_add_le (x + z) (-x)
    have he : x + z + -x = z := by abel
    rw [he, norm_neg] at h
    linarith
  have hw : 1 + frequencyNorm k ≤ A * (1 + ‖x + z‖) := by
    change 1 + 2 * Real.pi * ‖z‖ ≤ _
    have hb := mul_le_mul_of_nonneg_left hz (by positivity : 0 ≤ 2 * Real.pi)
    dsimp [A]
    nlinarith [norm_nonneg (x + z), Real.pi_pos,
      mul_nonneg (mul_nonneg (by positivity : 0 ≤ 2 * Real.pi) hr) (norm_nonneg (x + z))]
  have hdecay : (1 + ‖x + z‖) ^ p * ‖iteratedFDeriv ℝ j f (x + z)‖ ≤ C :=
    f.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (p, j)) le_rfl le_rfl (x + z)
  dsimp only
  have hwpos : 0 < 1 + frequencyNorm k := by linarith [frequencyNorm_nonneg k]
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc
    _ = (1 + frequencyNorm k) ^ p * ‖iteratedFDeriv ℝ j f (x + z)‖ := mul_comm _ _
    _ ≤ (A * (1 + ‖x + z‖)) ^ p * ‖iteratedFDeriv ℝ j f (x + z)‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hw p) (norm_nonneg _)
    _ = A ^ p * ((1 + ‖x + z‖) ^ p * ‖iteratedFDeriv ℝ j f (x + z)‖) := by
      rw [mul_pow, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left hdecay (pow_nonneg hA p)

/-- `main:eq:smoothing-low`: absolute convergence of every lattice derivative
series of a Schwartz function, at every translation. -/
theorem summable_norm_iteratedFDeriv_schwartz_lattice
    (f : 𝓢(EuclideanSpace ℝ (Fin n), F)) (j : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    Summable (fun k : Fin n → ℤ ↦
      ‖iteratedFDeriv ℝ j f (x + WithLp.toLp 2 (fun i ↦ (k i : ℝ)))‖) := by
  obtain ⟨u, hu, hb⟩ := exists_summable_bound_iteratedFDeriv_schwartz_lattice f j
    (norm_nonneg x)
  exact hu.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ hb k x le_rfl)

variable [CompleteSpace F]

/-- `main:lem:smoothing`: periodization on the normalized integer lattice. -/
def schwartzLatticePeriodization (f : 𝓢(EuclideanSpace ℝ (Fin n), F))
    (x : EuclideanSpace ℝ (Fin n)) : F :=
  ∑' k : Fin n → ℤ, f (x + WithLp.toLp 2 (fun i ↦ (k i : ℝ)))

/-- `main:eq:smoothing-low`: convergence in the multilinear operator norm. -/
theorem summable_iteratedFDeriv_schwartz_lattice
    (f : 𝓢(EuclideanSpace ℝ (Fin n), F)) (j : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    Summable (fun k : Fin n → ℤ ↦
      iteratedFDeriv ℝ j f (x + WithLp.toLp 2 (fun i ↦ (k i : ℝ)))) :=
  (summable_norm_iteratedFDeriv_schwartz_lattice f j x).of_norm

omit [CompleteSpace F] in
/-- `main:lem:smoothing`: absolute convergence of the scalar or vector
Schwartz periodization. -/
theorem summable_norm_schwartz_lattice
    (f : 𝓢(EuclideanSpace ℝ (Fin n), F)) (x : EuclideanSpace ℝ (Fin n)) :
    Summable (fun k : Fin n → ℤ ↦ ‖f (x + WithLp.toLp 2 (fun i ↦ (k i : ℝ)))‖) := by
  simpa only [norm_iteratedFDeriv_zero] using
    summable_norm_iteratedFDeriv_schwartz_lattice f 0 x

/-- `main:eq:smoothing-low`: every lattice sum of Schwartz derivatives is
continuous, by convergence uniform on a ball around each point. -/
theorem continuous_tsum_iteratedFDeriv_schwartz_lattice
    (f : 𝓢(EuclideanSpace ℝ (Fin n), F)) (j : ℕ) :
    Continuous (fun x : EuclideanSpace ℝ (Fin n) ↦ ∑' k : Fin n → ℤ,
      iteratedFDeriv ℝ j f (x + WithLp.toLp 2 (fun i ↦ (k i : ℝ)))) := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨u, hu, hb⟩ := exists_summable_bound_iteratedFDeriv_schwartz_lattice f j
    (show 0 ≤ ‖x‖ + 1 by positivity)
  have hcont := continuousOn_tsum
    (s := Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (‖x‖ + 1))
    (fun k ↦ ((f.smooth ⊤).continuous_iteratedFDeriv (by simp) |>.comp
      (continuous_id.add continuous_const)).continuousOn) hu
    (fun k y hy ↦ hb k y (le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hy)))
  exact hcont.continuousAt (Metric.isOpen_ball.mem_nhds (by
    simp only [Metric.mem_ball, dist_zero_right]; linarith))

omit [CompleteSpace F] in
/-- `main:lem:smoothing`: periodization is invariant under every integer
translation, with the same unit lattice as the periodic cutoff. -/
theorem schwartzLatticePeriodization_add_int
    (f : 𝓢(EuclideanSpace ℝ (Fin n), F)) (x : EuclideanSpace ℝ (Fin n))
    (m : Fin n → ℤ) :
    schwartzLatticePeriodization f (x + WithLp.toLp 2 (fun i ↦ (m i : ℝ))) =
      schwartzLatticePeriodization f x := by
  have he (k : Fin n → ℤ) :
      x + WithLp.toLp 2 (fun i ↦ (m i : ℝ)) + WithLp.toLp 2 (fun i ↦ (k i : ℝ)) =
        x + WithLp.toLp 2 (fun i ↦ ((k + m) i : ℝ)) := by
    ext i
    simp only [PiLp.add_apply, Pi.add_apply, Int.cast_add]
    ring
  unfold schwartzLatticePeriodization
  simp_rw [he]
  exact (Equiv.addRight m).tsum_eq
    (fun k : Fin n → ℤ ↦ f (x + WithLp.toLp 2 (fun i ↦ (k i : ℝ))))

end JanetCartan
