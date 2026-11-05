module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Reconstruction.MatrixMultiplication
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Finite local coefficient product budgets

Leibniz budgets for the coefficient and phase-gradient products in
`app:ch_response:eq:response-reconstruction-grading`. The observation cutoff
turns local smooth coefficients into global compact multipliers. Smoothness or
normal rank outside its fixed neighborhood is never required.
-/

@[expose] public noncomputable section
open scoped ContDiff
namespace JanetCartan.IsometricEmbedding.Reconstruction

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The finite Leibniz convolution used for coefficient products in
`app:ch_response:eq:response-reconstruction-grading`. -/
def reconstructionProductBudget (C D : ℕ → ℝ) (r : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (r + 1), (r.choose j : ℝ) * C j * D (r - j)

/-- Nonnegativity of the product budget for
`app:ch_response:eq:response-reconstruction-grading`. -/
theorem reconstructionProductBudget_nonneg {C D : ℕ → ℝ}
    (hC : ∀ r, 0 ≤ C r) (hD : ∀ r, 0 ≤ D r) (r : ℕ) :
    0 ≤ reconstructionProductBudget C D r :=
  Finset.sum_nonneg fun j _ ↦ mul_nonneg (mul_nonneg (by positivity) (hC j)) (hD _)

/-- Local primitive coefficient bounds imply product bounds with the same
slow scale `L`, as required in `app:ch_response:eq:response-reconstruction-grading`.
This applies to a reconstruction coefficient times a phase-gradient coordinate,
and can be iterated for the two phase factors in the physical derivative. -/
theorem reconstructionProductBudget_mul {Ω : Set E} (hΩ : IsOpen Ω)
    {f g : E → ℂ} (hf : ContDiffOn ℝ ∞ f Ω) (hg : ContDiffOn ℝ ∞ g Ω)
    (C D : ℕ → ℝ) (hC : ∀ r, 0 ≤ C r) (_hD : ∀ r, 0 ≤ D r)
    {L : ℝ} (hL : 0 ≤ L) (m : ℕ)
    (hfB : ∀ r, r ≤ m → ∀ x ∈ Ω, ‖iteratedFDeriv ℝ r f x‖ ≤ C r * L ^ r)
    (hgB : ∀ r, r ≤ m → ∀ x ∈ Ω, ‖iteratedFDeriv ℝ r g x‖ ≤ D r * L ^ r)
    (r : ℕ) (hr : r ≤ m) (x : E) (hx : x ∈ Ω) :
    ‖iteratedFDeriv ℝ r (fun y ↦ f y * g y) x‖ ≤
      reconstructionProductBudget C D r * L ^ r := by
  have hfAt := hf.contDiffAt (hΩ.mem_nhds hx)
  have hgAt := hg.contDiffAt (hΩ.mem_nhds hx)
  have hle := norm_iteratedFDerivWithin_mul_le hf hg hΩ.uniqueDiffOn hx
    (n := r) (by simp)
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hΩ.uniqueDiffOn
    ((hfAt.mul hgAt).of_le (by simp)) hx] at hle
  simp_rw [iteratedFDerivWithin_eq_iteratedFDeriv hΩ.uniqueDiffOn
      (hfAt.of_le (by simp)) hx,
    iteratedFDerivWithin_eq_iteratedFDeriv hΩ.uniqueDiffOn
      (hgAt.of_le (by simp)) hx] at hle
  apply hle.trans
  rw [reconstructionProductBudget, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hjr : j ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  calc
    _ ≤ (r.choose j : ℝ) * (C j * L ^ j) * (D (r - j) * L ^ (r - j)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (hfB j (hjr.trans hr) x hx) (by positivity)
      · exact hgB (r - j) (by omega) x hx
      · exact norm_nonneg _
      · exact mul_nonneg (by positivity) (mul_nonneg (hC j) (pow_nonneg hL j))
    _ = _ := by
      rw [show (r.choose j : ℝ) * (C j * L ^ j) * (D (r - j) * L ^ (r - j)) =
        ((r.choose j : ℝ) * C j * D (r - j)) * (L ^ j * L ^ (r - j)) by ring,
        ← pow_add, Nat.add_sub_of_le hjr]

/-- A fixed cutoff globalizes a coefficient that is smooth only on its
neighborhood. This is the locality step for
`app:ch_response:eq:response-graded-displacement` and its physical derivative. -/
theorem reconstructionLocalizedCoefficient_contDiff {Ω : Set E} (hΩ : IsOpen Ω)
    {ψ c : E → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hc : ContDiffOn ℝ ∞ c Ω)
    (hsupp : tsupport ψ ⊆ Ω) : ContDiff ℝ ∞ (fun x ↦ ψ x * c x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ Ω
  · exact hψ.contDiffAt.mul (hc.contDiffAt (hΩ.mem_nhds hx))
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    have hz := notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hx (hsupp h))
    filter_upwards [hz] with y hy
    simp only [Pi.zero_apply] at hy
    simp [hy]

/-- Primitive local budgets imply the global compact multiplier budget.
Outside the cutoff support every derivative vanishes. The constant is the
explicit Leibniz convolution, independent of `L`, in
`app:ch_response:eq:response-reconstruction-grading`. -/
theorem reconstructionLocalizedCoefficient_budget {Ω : Set E} (hΩ : IsOpen Ω)
    {ψ c : E → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hc : ContDiffOn ℝ ∞ c Ω)
    (hsupp : tsupport ψ ⊆ Ω)
    (C D : ℕ → ℝ) (hC : ∀ r, 0 ≤ C r) (hD : ∀ r, 0 ≤ D r)
    {L : ℝ} (hL : 0 ≤ L) (m : ℕ)
    (hψB : ∀ r, r ≤ m → ∀ x ∈ Ω, ‖iteratedFDeriv ℝ r ψ x‖ ≤ C r * L ^ r)
    (hcB : ∀ r, r ≤ m → ∀ x ∈ Ω, ‖iteratedFDeriv ℝ r c x‖ ≤ D r * L ^ r)
    (r : ℕ) (hr : r ≤ m) (x : E) :
    ‖iteratedFDeriv ℝ r (fun y ↦ ψ y * c y) x‖ ≤
      reconstructionProductBudget C D r * L ^ r := by
  by_cases hx : x ∈ Ω
  · exact reconstructionProductBudget_mul hΩ hψ.contDiffOn hc C D hC hD hL m
      hψB hcB r hr x hx
  · have hz : iteratedFDeriv ℝ r (fun y ↦ ψ y * c y) x = 0 := by
      by_contra hn
      exact hx (hsupp (tsupport_mul_subset_left (support_iteratedFDeriv_subset r hn)))
    rw [hz, norm_zero]
    exact mul_nonneg (reconstructionProductBudget_nonneg hC hD r) (pow_nonneg hL r)

/-- Differentiating a primitive coefficient costs one slow scale, not a
physical frequency. This supplies derivative-coefficient terms in
`app:ch_response:eq:response-graded-derivative`, with only local smoothness. -/
theorem reconstructionDirectionalCoefficient_budget {Ω : Set E} (hΩ : IsOpen Ω)
    {c : E → ℂ} (hc : ContDiffOn ℝ ∞ c Ω) (C : ℕ → ℝ)
    {L : ℝ} (m : ℕ)
    (hcB : ∀ r, r ≤ m + 1 → ∀ x ∈ Ω,
      ‖iteratedFDeriv ℝ r c x‖ ≤ C r * L ^ r)
    (v : E) (hv : ‖v‖ ≤ 1) (r : ℕ) (hr : r ≤ m) (x : E) (hx : x ∈ Ω) :
    ‖iteratedFDeriv ℝ r (fun y ↦ fderiv ℝ c y v) x‖ ≤
      (C (r + 1) * L) * L ^ r := by
  have hd := (hc.contDiffAt (hΩ.mem_nhds hx)).fderiv_right (m := ∞) (by simp)
  calc
    _ ≤ ‖v‖ * ‖iteratedFDeriv ℝ r (fderiv ℝ c) x‖ :=
      norm_iteratedFDeriv_clm_apply_const hd (by simp)
    _ ≤ ‖iteratedFDeriv ℝ r (fderiv ℝ c) x‖ :=
      mul_le_of_le_one_left (norm_nonneg _) hv
    _ = ‖iteratedFDeriv ℝ (r + 1) c x‖ := norm_iteratedFDeriv_fderiv
    _ ≤ C (r + 1) * L ^ (r + 1) := hcB _ (by omega) x hx
    _ = _ := by rw [pow_succ]; ring

end JanetCartan.IsometricEmbedding.Reconstruction
