module

public import JanetCartan.Analysis.Microlocal.Localization.IntegrationByParts
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Tactic.Ring

/-!
# Graded bounds for transposed amplitudes

The amplitude induction in `app:ch_osc:prop:osc-source-shell`. Coefficients need
only be smooth on an open neighborhood of the amplitude support. The explicit
recursion retains the constants at every derivative order. These estimates are
conditional on derivative bounds for the coefficients; deriving those bounds
from the actual phase gradient is a separate step.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace JanetCartan.Localization

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

/-- `app:ch_osc:prop:osc-source-shell`: Transposition preserves smoothness on the open set where
its coefficients are smooth. -/
theorem contDiffOn_transposeAmplitude {U : Set E} (hU : IsOpen U) (e : ι → E) (b : ι → E → ℂ) (a : E → ℂ)
    (hb : ∀ i, ContDiffOn ℝ ∞ (b i) U) (ha : ContDiffOn ℝ ∞ a U) :
    ContDiffOn ℝ ∞ (transposeAmplitude e b a) U := by
  apply ContDiffOn.neg
  apply ContDiffOn.sum
  intro i _
  exact ((hb i |>.mul ha).fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

/-- `app:ch_osc:prop:osc-source-shell`: The local Leibniz estimate, without global regularity
assumptions. -/
theorem norm_iteratedFDeriv_mul_le_on_open {U : Set E} (hU : IsOpen U) {f g : E → ℂ}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) {x : E} (hx : x ∈ U) (r : ℕ) :
    ‖iteratedFDeriv ℝ r (fun y ↦ f y * g y) x‖ ≤
      ∑ j ∈ Finset.range (r + 1), (r.choose j : ℝ) * ‖iteratedFDeriv ℝ j f x‖ *
        ‖iteratedFDeriv ℝ (r - j) g x‖ := by
  have h := norm_iteratedFDerivWithin_mul_le hf hg hU.uniqueDiffOn hx (show (r : ℕ∞ω) ≤ ∞ by simp)
  simpa only [iteratedFDerivWithin_of_isOpen _ hU hx] using h

/-- `app:ch_osc:prop:osc-source-shell`: One transposition costs one derivative, with the exact
binomial constants. -/
theorem norm_iteratedFDeriv_transposeAmplitude_le {U : Set E} (hU : IsOpen U)
    (e : ι → E) (b : ι → E → ℂ) (a : E → ℂ)
    (hb : ∀ i, ContDiffOn ℝ ∞ (b i) U) (ha : ContDiffOn ℝ ∞ a U)
    {x : E} (hx : x ∈ U) (r : ℕ) :
    ‖iteratedFDeriv ℝ r (transposeAmplitude e b a) x‖ ≤
      ∑ i, ‖e i‖ * ∑ j ∈ Finset.range (r + 2), ((r + 1).choose j : ℝ) *
        ‖iteratedFDeriv ℝ j (b i) x‖ * ‖iteratedFDeriv ℝ (r + 1 - j) a x‖ := by
  have hd (i : ι) : ContDiffOn ℝ ∞ (fderiv ℝ (fun y ↦ b i y * a y)) U :=
    ((hb i).mul ha).fderiv_of_isOpen hU (by simp)
  have he (i : ι) : ContDiffAt ℝ r (fun y ↦ fderiv ℝ (fun z ↦ b i z * a z) y (e i)) x :=
    ((hd i).clm_apply contDiffOn_const).contDiffAt (hU.mem_nhds hx) |>.of_le (by simp)
  change ‖iteratedFDeriv ℝ r (-(fun y ↦ ∑ i, fderiv ℝ
    (fun z ↦ b i z * a z) y (e i))) x‖ ≤ _
  rw [iteratedFDeriv_neg_apply, norm_neg]
  rw [iteratedFDeriv_fun_sum_apply (fun i _ ↦ he i)]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (norm_iteratedFDeriv_clm_apply_const
    ((hd i).contDiffAt (hU.mem_nhds hx)) (by simp : (r : ℕ∞ω) ≤ ∞)).trans
  rw [norm_iteratedFDeriv_fderiv]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact norm_iteratedFDeriv_mul_le_on_open hU (hb i) ha hx (r + 1)

/-- `app:ch_osc:prop:osc-source-shell`: Explicit derivative constants after repeated
transposition. The coefficient profile is `B` and the initial amplitude profile is `C`. -/
def transposeDerivativeConstant (e : ι → E) (B C : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, r => C r
  | q + 1, r => ∑ i, ‖e i‖ * ∑ j ∈ Finset.range (r + 2),
      ((r + 1).choose j : ℝ) * B j * transposeDerivativeConstant e B C q (r + 1 - j)

omit [NormedSpace ℝ E] in
/-- `app:ch_osc:prop:osc-source-shell`: Nonnegative input profiles give nonnegative constants at
every order. -/
theorem transposeDerivativeConstant_nonneg (e : ι → E) {B C : ℕ → ℝ}
    (hB : ∀ r, 0 ≤ B r) (hC : ∀ r, 0 ≤ C r) (q r : ℕ) :
    0 ≤ transposeDerivativeConstant e B C q r := by
  induction q generalizing r with
  | zero => exact hC r
  | succ q ih =>
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg (norm_nonneg _)
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB j)) (ih _)

/-- `app:ch_osc:prop:osc-source-shell`: All transposed amplitudes are smooth on the same open set. -/
theorem contDiffOn_iterate_transposeAmplitude {U : Set E} (hU : IsOpen U)
    (e : ι → E) (b : ι → E → ℂ) (a : E → ℂ)
    (hb : ∀ i, ContDiffOn ℝ ∞ (b i) U) (ha : ContDiffOn ℝ ∞ a U) (q : ℕ) :
    ContDiffOn ℝ ∞ ((transposeAmplitude e b)^[q] a) U := by
  induction q with
  | zero => exact ha
  | succ q ih =>
    rw [Function.iterate_succ_apply']
    exact contDiffOn_transposeAmplitude hU e b _ hb ih

/-- `app:ch_osc:prop:osc-source-shell`: The repeated Leibniz bound with arbitrary derivative
majorants. -/
theorem norm_iteratedFDeriv_iterate_transposeAmplitude_le {U : Set E} (hU : IsOpen U)
    (e : ι → E) (b : ι → E → ℂ) (a : E → ℂ)
    (hb : ∀ i, ContDiffOn ℝ ∞ (b i) U) (ha : ContDiffOn ℝ ∞ a U)
    {x : E} (hx : x ∈ U) {B C : ℕ → ℝ}
    (hB : ∀ r, 0 ≤ B r)
    (hbn : ∀ i r, ‖iteratedFDeriv ℝ r (b i) x‖ ≤ B r)
    (han : ∀ r, ‖iteratedFDeriv ℝ r a x‖ ≤ C r) (q r : ℕ) :
    ‖iteratedFDeriv ℝ r ((transposeAmplitude e b)^[q] a) x‖ ≤
      transposeDerivativeConstant e B C q r := by
  induction q generalizing r with
  | zero => exact han r
  | succ q ih =>
    rw [Function.iterate_succ_apply']
    apply (norm_iteratedFDeriv_transposeAmplitude_le hU e b _ hb
      (contDiffOn_iterate_transposeAmplitude hU e b a hb ha q) hx r).trans
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hbn i j) (Nat.cast_nonneg _))
      (ih _) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hB j))

omit [NormedSpace ℝ E] in
/-- `app:ch_osc:prop:osc-source-shell`: Exact homogeneity: each transposition costs `L / R`, and
each further derivative costs `L`. -/
theorem transposeDerivativeConstant_scaling (e : ι → E) (B C : ℕ → ℝ) (A L R : ℝ) (q r : ℕ) :
    transposeDerivativeConstant e (fun j ↦ B j * L ^ j / R) (fun j ↦ C j * (A * L ^ j)) q r =
      transposeDerivativeConstant e B C q r * (A * L ^ (q + r) / R ^ q) := by
  induction q generalizing r with
  | zero => simp [transposeDerivativeConstant]
  | succ q ih =>
    simp only [transposeDerivativeConstant, ih]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hjr : j ≤ r + 1 := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hp : L ^ j * L ^ (q + (r + 1 - j)) = L ^ (q + 1+r) := by
      rw [← pow_add]
      congr 1
      omega
    calc
      _ = ((r + 1).choose j : ℝ) * B j * transposeDerivativeConstant e B C q (r + 1 - j) *
          (A * (L ^ j * L ^ (q + (r + 1 - j))) / (R * R ^ q)) := by ring
      _ = _ := by rw [hp, ← pow_succ']

/-- `app:ch_osc:prop:osc-source-shell`: The graded amplitude estimate, conditional on coefficient
bounds `Bⱼ Lʲ / R`. Set `R = ρ + ‖ξ‖` and absorb the fixed factor `Lᵇ` in `A`. -/
theorem norm_iteratedFDeriv_iterate_transposeAmplitude_le_graded {U : Set E} (hU : IsOpen U)
    (e : ι → E) (b : ι → E → ℂ) (a : E → ℂ)
    (hb : ∀ i, ContDiffOn ℝ ∞ (b i) U) (ha : ContDiffOn ℝ ∞ a U)
    {x : E} (hx : x ∈ U) {B C : ℕ → ℝ} {A L R : ℝ}
    (hB : ∀ r, 0 ≤ B r)
    (hL : 0 ≤ L) (hR : 0 < R)
    (hbn : ∀ i r, ‖iteratedFDeriv ℝ r (b i) x‖ ≤ B r * L ^ r / R)
    (han : ∀ r, ‖iteratedFDeriv ℝ r a x‖ ≤ C r * (A * L ^ r)) (q r : ℕ) :
    ‖iteratedFDeriv ℝ r ((transposeAmplitude e b)^[q] a) x‖ ≤
      transposeDerivativeConstant e B C q r * (A * L ^ (q + r) / R ^ q) := by
  have h := norm_iteratedFDeriv_iterate_transposeAmplitude_le hU e b a hb ha hx
    (fun j ↦ div_nonneg (mul_nonneg (hB j) (pow_nonneg hL j)) hR.le)
    hbn han q r
  rwa [transposeDerivativeConstant_scaling] at h

end JanetCartan.Localization
