module

public import JanetCartan.Analysis.Iteration.BackgroundPreparation.Estimates
public import JanetCartan.Analysis.Iteration.BackgroundPreparation.Reserves
public import JanetCartan.Analysis.Iteration.FiniteAccuracy
public import JanetCartan.Analysis.ContDiff.PositiveSquareRoot
import Mathlib.Tactic.Linarith

/-!
# Finite positive-density preparation before sampling

Conditional finite preparation from `app:ch_mean_pairs:prop:mean-coarse` and
`app:ch_mean_pairs:eq:mean-density-recursion` of `paper.tex`. The signed density
correction `D`, transported density `L`, auxiliary correction `B`, and Hermitian
discrepancy `E` are maps, not fields storing the desired residual conclusion.
The exact normal cancellation and the two finite-jet analytic estimates are
explicit inputs. Backwards reserves accommodate arbitrary finite derivative
losses. The construction uses precisely `J` updates and proves its own bounded
class and positivity invariants.

This module does not construct the current atoms or their discrepancy estimate,
the density synthesis/right inverse, the high derivative profiles, or the later
sampling event. It is separate from the later fine mean recurrence with a fixed
sampled row. The abstract seminorms can be the existing derivative and Sobolev
seminorms on smooth data; no alternative torus or matrix norm is introduced.
-/

@[expose] public noncomputable section

namespace JanetCartan.BackgroundPreparation

variable {X Y : Type*} [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y]

/-- `app:ch_mean_pairs:prop:mean-coarse`: execute `J` steps using backward
finite derivative reserves. `m` is the discrepancy loss, `d` the density
synthesis loss. Only finitely many analytic estimates, at the displayed
reserves, are required. For `ε = λ⁻¹`, the residual is `O(λ^(-(J+1)))`
and the cumulative density change is `O(λ⁻¹)` at every requested low order. -/
theorem finite_preparation_with_reserves
    (D : Y →ₗ[ℝ] X) (L : X →ₗ[ℝ] Y) (B : Y →ₗ[ℝ] Y) (E : X → Y)
    (p : ℕ → Seminorm ℝ X) (q : ℕ → Seminorm ℝ Y)
    (hp : ∀ r s, r ≤ s → ∀ v, p r v ≤ p s v)
    (hq : ∀ r s, r ≤ s → ∀ e, q r e ≤ q s e)
    (m d : ℕ → ℕ) (R S J : ℕ)
    {ε C M K ρ : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hsmall : K * M * ε ≤ 1 / 2) (hradius : 2 * M * C * ε ≤ ρ)
    (hcancel : ∀ e, L (D e) - B e = -e)
    (hD : ∀ k < J, ∀ e,
      p (reserves m d R S k).1 (D e) ≤ M * q (d (reserves m d R S k).1) e)
    (hE : ∀ k < J, ∀ v w,
      p (m (reserves m d R S k).2) v ≤ ρ →
      p (m (reserves m d R S k).2) w ≤ ρ →
      q (reserves m d R S k).2 (E v - E w) ≤
        K * ε * p (m (reserves m d R S k).2) (v - w))
    (hinit : q (reserves m d R S J).2 (E 0) ≤ C * ε) :
    ∀ i ≤ J,
      q S (run D L B E i).2 ≤ C * (K * M) ^ i * ε ^ (i + 1) ∧
      p R (run D L B E i).1 ≤ 2 * M * C * ε := by
  let P := fun i ↦ p (reserves m d R S (J - i)).1
  let Q := fun i ↦ q (reserves m d R S (J - i)).2
  have hbounds := finite_preparation_bounds D L B E P Q J hε hC hM hK
    hsmall hradius hcancel
    (fun i hi v ↦ hp _ _ (reserves_forward_step m d R S J i hi).1 v)
    (fun i hi e ↦ (hD (J - (i + 1)) (by omega) e).trans
      (mul_le_mul_of_nonneg_left
        (hq _ _ (reserves_forward_step m d R S J i hi).2 e) hM))
    (fun i hi v w hv hw ↦
      (hE (J - (i + 1)) (by omega) v w
        ((hp _ _ (reserves_spec m d R S _).2.2 v).trans hv)
        ((hp _ _ (reserves_spec m d R S _).2.2 w).trans hw)).trans
      (mul_le_mul_of_nonneg_left
        (hp _ _ (reserves_spec m d R S _).2.2 (v - w)) (mul_nonneg hK hε)))
    (by simpa [Q] using hinit)
  intro i hi
  obtain ⟨he, _, hv⟩ := hbounds i hi
  constructor
  · calc
      _ ≤ Q i (run D L B E i).2 := hq _ _ (reserves_spec m d R S _).2.1 _
      _ ≤ C * ε * (K * M * ε) ^ i := he
      _ = _ := by rw [mul_pow, pow_succ]; ring
  · exact (hp _ _ (reserves_spec m d R S _).1 _).trans hv

/-- `app:ch_mean_pairs:prop:mean-coarse`: a cumulative low-order bound
preserves the full density interval. Evaluation is explicit, allowing all
carrier and initial variables in its domain. -/
theorem density_interval_of_bound {Ω : Type*} (eval : X → Ω → ℝ)
    (p : Seminorm ℝ X) (heval : ∀ v z, |eval v z| ≤ p v)
    {v : X} {b : ℝ} (hv : p v ≤ b) (hb : b ≤ 1 / 2) (z : Ω) :
    1 + eval v z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) := by
  have h := abs_le.mp ((heval v z).trans (hv.trans hb))
  constructor <;> linarith

/-- `app:ch_mean_pairs:prop:mean-coarse`: the prepared amplitude is positive,
has exactly the corrected square, and differs from its initial value by the
cumulative density bound. These conclusions use the proved scalar square-root
lemmas, independently of any background existence assertion. -/
theorem prepared_amplitude_properties {Ω : Type*} (eval : X → Ω → ℝ)
    (p : Seminorm ℝ X) (heval : ∀ v z, |eval v z| ≤ p v)
    (σ : Ω → ℝ) (hσ : ∀ z, 0 < σ z)
    {v : X} {b : ℝ} (hv : p v ≤ b) (hb : b ≤ 1 / 2) :
    ∀ z, 0 < positiveDensityAmplitude (σ z) (eval v z) ∧
      positiveDensityAmplitude (σ z) (eval v z) ^ 2 = (σ z) ^ 2 * (1 + eval v z) ∧
      |positiveDensityAmplitude (σ z) (eval v z) - σ z| ≤ |σ z| * b := by
  intro z
  have hint := density_interval_of_bound eval p heval hv hb z
  have hpos : 0 < 1 + eval v z := lt_of_lt_of_le (by norm_num) hint.1
  refine ⟨positiveDensityAmplitude_pos (hσ z) hpos,
    positiveDensityAmplitude_sq hpos.le, ?_⟩
  exact (positiveDensityAmplitude_abs_sub_initial_le hint.1).trans
    (mul_le_mul_of_nonneg_left ((heval v z).trans hv) (abs_nonneg _))

/-- `app:ch_mean_pairs:prop:mean-coarse`: explicit sufficient carrier thresholds
for the finite induction and positivity, with constants independent of `Λ`. -/
theorem carrier_threshold_bounds (C K M : ℝ) {Λ : ℝ} (hΛ : 0 < Λ)
    (hKM : 2 * K * M ≤ Λ) (hMC : 4 * M * C ≤ Λ) :
    K * M * Λ⁻¹ ≤ 1 / 2 ∧ 2 * M * C * Λ⁻¹ ≤ 1 / 2 := by
  constructor
  · rw [← div_eq_mul_inv, div_le_iff₀ hΛ]
    linarith
  · rw [← div_eq_mul_inv, div_le_iff₀ hΛ]
    linarith

/-- The natural inverse power in the finite induction is the manuscript's
real power (`app:ch_mean_pairs:prop:mean-coarse`). -/
theorem inverse_pow_eq_rpow {Λ : ℝ} (hΛ : 0 ≤ Λ) (i : ℕ) :
    (Λ⁻¹) ^ (i + 1) = Λ ^ (-((i : ℝ) + 1)) := by
  rw [Real.rpow_neg hΛ]
  norm_cast
  exact inv_pow _ _

/-- The conditional finite positive-density preparation of
`app:ch_mean_pairs:prop:mean-coarse`, before sampling. All analytic inputs are
bounds for the actual correction and discrepancy maps at finitely many orders;
no bound for an iterate is an input. The full residual is the ledger proved in
`run_residual_ledger`. The output holds at every intermediate step as well as
at `J`, where its residual is `O(Λ^(-(J+1)))`.

This proves finite preparation given the uncut cancellation and the finite-jet
estimates, not the existence of those analytic operators or the sampled field. -/
theorem finite_positive_density_preparation {Ω : Type*}
    (D : Y →ₗ[ℝ] X) (L : X →ₗ[ℝ] Y) (B : Y →ₗ[ℝ] Y) (E : X → Y)
    (p : ℕ → Seminorm ℝ X) (q : ℕ → Seminorm ℝ Y)
    (hp : ∀ r s, r ≤ s → ∀ v, p r v ≤ p s v)
    (hq : ∀ r s, r ≤ s → ∀ e, q r e ≤ q s e)
    (m d : ℕ → ℕ) (R S J : ℕ)
    (eval : X → Ω → ℝ) (heval : ∀ v z, |eval v z| ≤ p R v)
    (σ : Ω → ℝ) (hσ : ∀ z, 0 < σ z)
    {Λ C M K ρ : ℝ} (hΛ : 0 < Λ) (hC : 0 ≤ C) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hKM : 2 * K * M ≤ Λ) (hMC : 4 * M * C ≤ Λ)
    (hradius : 2 * M * C * Λ⁻¹ ≤ ρ)
    (hcancel : ∀ e, L (D e) - B e = -e)
    (hD : ∀ k < J, ∀ e,
      p (reserves m d R S k).1 (D e) ≤ M * q (d (reserves m d R S k).1) e)
    (hE : ∀ k < J, ∀ v w,
      p (m (reserves m d R S k).2) v ≤ ρ →
      p (m (reserves m d R S k).2) w ≤ ρ →
      q (reserves m d R S k).2 (E v - E w) ≤
        K * Λ⁻¹ * p (m (reserves m d R S k).2) (v - w))
    (hinit : q (reserves m d R S J).2 (E 0) ≤ C * Λ⁻¹) :
    ∀ i ≤ J,
      q S (run D L B E i).2 ≤ C * (K * M) ^ i * Λ ^ (-((i : ℝ) + 1)) ∧
      p R (run D L B E i).1 ≤ 2 * M * C * Λ⁻¹ ∧
      ∀ z, 1 + eval (run D L B E i).1 z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧
        0 < positiveDensityAmplitude (σ z) (eval (run D L B E i).1 z) ∧
        positiveDensityAmplitude (σ z) (eval (run D L B E i).1 z) ^ 2 =
          (σ z) ^ 2 * (1 + eval (run D L B E i).1 z) ∧
        |positiveDensityAmplitude (σ z) (eval (run D L B E i).1 z) - σ z| ≤
          |σ z| * (2 * M * C * Λ⁻¹) := by
  obtain ⟨hsmall, hpositive⟩ := carrier_threshold_bounds C K M hΛ hKM hMC
  have hbounds := finite_preparation_with_reserves D L B E p q hp hq m d R S J
    (inv_nonneg.mpr hΛ.le) hC hM hK hsmall hradius hcancel hD hE hinit
  intro i hi
  obtain ⟨he, hv⟩ := hbounds i hi
  rw [inverse_pow_eq_rpow hΛ.le] at he
  refine ⟨he, hv, ?_⟩
  intro z
  exact ⟨density_interval_of_bound eval (p R) heval hv hpositive z,
    prepared_amplitude_properties eval (p R) heval σ hσ hv hpositive z⟩

/-- `main:eq:preparation-orders` and `app:ch_mean_pairs:prop:mean-coarse`:
the fixed count `J = floor(2A/a)` makes the prepared power at least as small
as `R^(-2A)`. The prefactor is retained; absorbing it to obtain the paper's
unit constant requires a further large-scale threshold using the strict margin. -/
theorem preparation_order_residual_scale {R a A C e : ℝ}
    (hR : 1 ≤ R) (ha : 0 < a) (hC : 0 ≤ C)
    (he : e ≤ C * (R ^ a) ^ (-((preparationOrder A a : ℝ) + 1))) :
    e ≤ C * R ^ (-(2 * A)) := by
  have horder : (0 : ℝ) + 2 * A ≤ a * ((preparationOrder A a + 1 : ℕ) : ℝ) := by
    simpa using (lt_preparationOrder_succ_mul (A := A) ha).le
  have hpow := rpow_carrier_neg_order_le hR horder
  simp only [Real.rpow_zero, one_mul, Nat.cast_add, Nat.cast_one] at hpow
  exact he.trans (mul_le_mul_of_nonneg_left hpow hC)

end JanetCartan.BackgroundPreparation
