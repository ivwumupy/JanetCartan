module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.PhysicalInterpolation.Coordinates
public import JanetCartan.Analysis.ContDiff.Norm.Interpolation

/-!
# Uniform interpolation of physical derivative budgets

Step 3 of `app:ch_regular_base:thm:actual-calculus`, using the proved closed-ball
version of `app:lem:elementary-interpolation-jets`. Translating a unit ball
makes the estimate global, so fixed support is not needed for this step.
-/

@[expose] public noncomputable section
open scoped ContDiff
open JanetCartan.AmplitudeBound
namespace JanetCartan.Pseudodifferential

/-- `app:lem:elementary-interpolation-jets`: a physical budget bounds the
Fréchet seminorm on a translated set, with the same comparison constant. -/
theorem cNorm_translate_le_amplitudeBudget {X : Type*} {n N : ℕ}
    {b : X → EuclideanSpace ℝ (Fin n) → ℂ} (hb : ∀ ξ, ContDiff ℝ ∞ (b ξ))
    {A : ℝ} (hA : HasAmplitudeDerivativeBound b N A)
    (ξ : X) (z : EuclideanSpace ℝ (Fin n)) (S : Set (EuclideanSpace ℝ (Fin n))) :
    cNorm S N (fun u ↦ b ξ (z + u)) ≤ physicalBudgetCNormConstant n N * A := by
  have hnonneg : 0 ≤ A := (norm_nonneg _).trans (hA.norm_le ξ 0)
  calc
    _ ≤ ∑ k ∈ Finset.range (N + 1), (n : ℝ) ^ k * A := by
      apply cNorm_le_sum_of_bounds (fun _ _ ↦ by positivity)
      intro k hk u _
      rw [iteratedFDeriv_comp_add_left]
      exact norm_iteratedFDeriv_le_amplitudeBudget hb hA ξ hk _
    _ = _ := by rw [physicalBudgetCNormConstant, Finset.sum_mul]

/-- `app:lem:elementary-interpolation-jets`: the reverse comparison on a fixed
closed ball, for every ordered derivative through the seminorm's order. -/
theorem norm_coordinateDeriv_le_cNorm_closedBall {n N : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : ContDiff ℝ ∞ f)
    (x : EuclideanSpace ℝ (Fin n)) (ρ : ℝ) (is : List (Fin n)) (hi : is.length ≤ N)
    {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ Metric.closedBall x ρ) :
    ‖euclideanCoordinateDerivList is f z‖ ≤ cNorm (Metric.closedBall x ρ) N f :=
  (norm_euclideanCoordinateDerivList_le_iteratedFDeriv hf is z).trans
    (JanetCartan.norm_iteratedFDeriv_le_cNorm (isCompact_closedBall x ρ)
      (hf.of_le (by simp)) hz hi)

/-- `app:ch_regular_base:thm:actual-calculus`, Step 3: interpolation with one
high physical budget, uniformly in all parameters and positions. The endpoints
are included. In particular this applies to amplitudes supported in any one
fixed physical box. The constant is independent of `b`, `M`, and `H`. -/
theorem exists_physicalAmplitude_interpolation_constant {X : Type*}
    (n μ s j : ℕ) (hs : 0 < s) (hj : j ≤ s) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (b : X → EuclideanSpace ℝ (Fin n) → ℂ), (∀ ξ, ContDiff ℝ ∞ (b ξ)) →
      ∀ M H : ℝ, HasAmplitudeDerivativeBound b μ M →
        HasAmplitudeDerivativeBound b (μ + s) H →
        HasAmplitudeDerivativeBound b (μ + j)
          (C * (max 1 M) ^ (1 - (j : ℝ) / s) * (max 1 H) ^ ((j : ℝ) / s)) := by
  by_cases hj0 : j = 0
  · subst j
    refine ⟨1, zero_lt_one, ?_⟩
    intro b _ M H hM _ ξ is hi z
    simpa using (hM ξ is (by simpa using hi) z).trans (le_max_right 1 M)
  by_cases hjs : j = s
  · subst j
    refine ⟨1, zero_lt_one, ?_⟩
    intro b _ M H _ hH ξ is hi z
    have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
    simpa [hs0] using (hH ξ is hi z).trans (le_max_right 1 H)
  have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
  have hjlt : j < s := lt_of_le_of_ne hj hjs
  obtain ⟨C, hC, hinterp⟩ := cNorm_le_interpolation_closedBall
    (F := ℂ) (0 : EuclideanSpace ℝ (Fin n)) (ρ := 1) zero_lt_one
    (R := μ) (j := μ + j) (k := μ + s) (by omega) (by omega)
  let θ : ℝ := (j : ℝ) / s
  let L := physicalBudgetCNormConstant n μ
  let U := physicalBudgetCNormConstant n (μ + s)
  have hL : 0 < L := physicalBudgetCNormConstant_pos n μ
  have hU : 0 < U := physicalBudgetCNormConstant_pos n (μ + s)
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  have hθ1 : θ ≤ 1 := (div_le_one (by exact_mod_cast hs)).mpr (by exact_mod_cast hj)
  refine ⟨C * L ^ (1 - θ) * U ^ θ, by positivity, ?_⟩
  intro b hb M H hM hH ξ is hi z
  let g := fun u ↦ b ξ (z + u)
  have hg : ContDiff ℝ ∞ g := (hb ξ).comp (contDiff_const.add contDiff_id)
  have hlow : cNorm (Metric.closedBall 0 1) μ g ≤ L * max 1 M :=
    (cNorm_translate_le_amplitudeBudget hb hM ξ z _).trans
      (mul_le_mul_of_nonneg_left (le_max_right 1 M) hL.le)
  have hhigh : cNorm (Metric.closedBall 0 1) (μ + s) g ≤ U * max 1 H :=
    (cNorm_translate_le_amplitudeBudget hb hH ξ z _).trans
      (mul_le_mul_of_nonneg_left (le_max_right 1 H) hU.le)
  have hpoint : ‖euclideanCoordinateDerivList is (b ξ) z‖ ≤
      cNorm (Metric.closedBall 0 1) (μ + j) g := by
    apply (norm_euclideanCoordinateDerivList_le_iteratedFDeriv (hb ξ) is z).trans
    have hp := JanetCartan.norm_iteratedFDeriv_le_cNorm
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
      (hg.of_le (show (↑(μ + j) : ℕ∞ω) ≤ ∞ by simp))
      (show (0 : EuclideanSpace ℝ (Fin n)) ∈ Metric.closedBall 0 1 by simp) hi
    simpa [g, iteratedFDeriv_comp_add_left] using hp
  have hinterp' : cNorm (Metric.closedBall 0 1) (μ + j) g ≤
      C * (cNorm (Metric.closedBall 0 1) μ g) ^ (1 - θ) *
        (cNorm (Metric.closedBall 0 1) (μ + s) g) ^ θ := by
    simpa [θ, Nat.cast_add, add_sub_cancel_left] using hinterp g hg
  calc
    _ ≤ C * (cNorm (Metric.closedBall 0 1) μ g) ^ (1 - θ) *
        (cNorm (Metric.closedBall 0 1) (μ + s) g) ^ θ := hpoint.trans hinterp'
    _ ≤ C * (L * max 1 M) ^ (1 - θ) * (U * max 1 H) ^ θ := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (cNorm_nonneg _ _ _) hlow (sub_nonneg.mpr hθ1)) hC.le
      · exact Real.rpow_le_rpow (cNorm_nonneg _ _ _) hhigh hθ
      · exact Real.rpow_nonneg (cNorm_nonneg _ _ _) _
      · positivity
    _ = _ := by
      rw [Real.mul_rpow hL.le (by positivity), Real.mul_rpow hU.le (by positivity)]
      ring

end JanetCartan.Pseudodifferential
