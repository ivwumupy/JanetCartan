module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.PhysicalInterpolation.Bounds

/-!
# Frequency-only weights in physical interpolation

Step 3 of `app:ch_regular_base:thm:actual-calculus`: a normalized amplitude may
be multiplied by an arbitrary frequency-only weight. Physical differentiation
does not differentiate that weight.
-/

@[expose] public noncomputable section
open scoped ContDiff
open JanetCartan.AmplitudeBound
namespace JanetCartan.Pseudodifferential

/-- `app:ch_regular_base:thm:actual-calculus`, Step 3: a scalar independent of
physical position factors out of every ordered physical derivative. -/
theorem euclideanCoordinateDerivList_const_mul {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : ContDiff ℝ ∞ f)
    (w : ℂ) (is : List (Fin n)) :
    euclideanCoordinateDerivList is (fun z ↦ w * f z) =
      fun z ↦ w * euclideanCoordinateDerivList is f z := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    funext z
    simp only [euclideanCoordinateDerivList, ih]
    rw [fderiv_const_mul
      ((contDiff_euclideanCoordinateDerivList hf is).differentiable (by simp)).differentiableAt]
    rfl

/-- `app:ch_regular_base:thm:actual-calculus`, Step 3: uniform one-high
interpolation for a normalized amplitude times a frequency-only weight. No
regularity or boundedness in frequency is required for this physical estimate. -/
theorem exists_weighted_physicalAmplitude_interpolation_constant {X : Type*}
    (n μ s j : ℕ) (hs : 0 < s) (hj : j ≤ s) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (b : X → EuclideanSpace ℝ (Fin n) → ℂ), (∀ ξ, ContDiff ℝ ∞ (b ξ)) →
      ∀ (w : X → ℂ) (M H : ℝ), HasAmplitudeDerivativeBound b μ M →
        HasAmplitudeDerivativeBound b (μ + s) H →
        ∀ ξ is, is.length ≤ μ + j → ∀ z,
          ‖euclideanCoordinateDerivList is (fun u ↦ w ξ * b ξ u) z‖ ≤
            ‖w ξ‖ * (C * (max 1 M) ^ (1 - (j : ℝ) / s) *
              (max 1 H) ^ ((j : ℝ) / s)) := by
  obtain ⟨C, hC, hbound⟩ := exists_physicalAmplitude_interpolation_constant (X := X) n μ s j hs hj
  refine ⟨C, hC, ?_⟩
  intro b hb w M H hM hH ξ is hi z
  rw [euclideanCoordinateDerivList_const_mul (hb ξ), norm_mul]
  exact mul_le_mul_of_nonneg_left (hbound b hb M H hM hH ξ is hi z) (norm_nonneg _)

end JanetCartan.Pseudodifferential
