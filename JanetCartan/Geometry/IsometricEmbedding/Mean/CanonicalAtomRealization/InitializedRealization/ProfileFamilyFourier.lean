module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.InitializedRealization.ReducedFourierClassical

/-!
# Classical profiles for the original reduced-solution family

For the manuscript's preparation by profile families, the source has one
size `A` and all ordered Fourier bounds are `S k p * A * K^(p+k)`.
Spatial Sobolev embedding costs exactly the fixed factor `K^(n+1)`.
The explicit constants below depend only on dimensions and the given
Fourier profile, before the field, frequency and history. The response
reconstruction pays its two additional derivatives with carrier factors.

Consumer: the actual response profile used in
`PreparedHistory.PreparedDiscrepancyProfiles`, for
`app:ch_mean_pairs:eq:mean-prepared-scalar`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ContDiff

namespace JanetCartan.CanonicalAtomRealization

open Pseudodifferential

/-- The Sobolev embedding constant times the finite diagonal of the actual
ordered Fourier profile. It is independent of the source size and history
(`app:ch_response:eq:response-graded-reduced`). -/
def reducedProfileClassicalBudget (n d N : ℕ) (S : ℕ → ℕ → ℝ) (m : ℕ) : ℝ :=
  (exists_reducedParameterJet_fourier_constant n d N m).choose *
    ∑ k ∈ Finset.range (m+1), S k (m-k+n+1)

/-- Nonnegativity of the fixed classical budget for a nonnegative Fourier
profile (`app:ch_response:eq:response-graded-reduced`). -/
theorem reducedProfileClassicalBudget_nonneg (n d N : ℕ) {S : ℕ → ℕ → ℝ}
    (hS : ∀ k p, 0 ≤ S k p) (m : ℕ) :
    0 ≤ reducedProfileClassicalBudget n d N S m :=
  mul_nonneg (exists_reducedParameterJet_fourier_constant n d N m).choose_spec.1
    (Finset.sum_nonneg (fun k _ ↦ hS k _))

/-- Convert every ordered Fourier estimate of the same reduced solution to
its full joint derivative, retaining the original scalar size linearly.
The sole extra scale factor is `K^(n+1)`, independent of the derivative
order (`app:ch_response:eq:response-graded-reduced`). -/
theorem reducedParameter_joint_profile_of_ordered_fourier {n d N : ℕ}
    {V : Set (Euclidean 3 × Euclidean d)} (hV : IsOpen V)
    {f : Euclidean n × (Euclidean 3 × Euclidean d) → EuclideanSpace ℂ (Fin N)}
    (hf : ContDiffOn ℝ ∞ f (univ ×ˢ V))
    (S : ℕ → ℕ → ℝ) (hS : ∀ k p, 0 ≤ S k p)
    {A K : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hfourier : ∀ c ∈ V, ∀ k p : ℕ, ∀ w : Fin k → (Euclidean 3 × Euclidean d),
      (∀ l, ‖w l‖ ≤ 1) →
      ∃ u : PiLp 2 (fun _ : Fin N ↦ Lp ℂ 2 (volume : Measure (Euclidean n))),
        (∀ i, u i =ᵐ[volume]
          (fun x ↦ (iteratedFDeriv ℝ k (fun b ↦ f (x,b)) c w) i)) ∧
        MemMatrixFourierSobolev (p : ℝ) u ∧
        matrixFourierSobolevNorm (p : ℝ) u ≤ S k p * A * K^(p+k)) :
    ∀ m q, q ∈ univ ×ˢ V →
      ‖iteratedFDeriv ℝ m f q‖ ≤
        reducedProfileClassicalBudget n d N S m * (A*K^(n+1)) * K^m ∧
      ∀ i, ‖iteratedFDeriv ℝ m (fun p ↦ f p i) q‖ ≤
        reducedProfileClassicalBudget n d N S m * (A*K^(n+1)) * K^m := by
  classical
  intro m q hq
  let D := ∑ k ∈ Finset.range (m+1), S k (m-k+n+1)
  have hD : 0 ≤ D := Finset.sum_nonneg (fun k _ ↦ hS k _)
  have hb := (exists_reducedParameterJet_fourier_constant n d N m).choose_spec.2
    V hV f hf (D*A*K^(m+n+1)) (by positivity) ?_ q hq
  · have he :
        (exists_reducedParameterJet_fourier_constant n d N m).choose * (D*A*K^(m+n+1)) =
          reducedProfileClassicalBudget n d N S m * (A*K^(n+1)) * K^m := by
      unfold reducedProfileClassicalBudget
      rw [show m+n+1 = m+(n+1) by omega, pow_add]
      dsimp [D]
      ring
    simpa only [he] using hb
  · intro c hc k hk w hw
    obtain ⟨u,hrep,hu,hnorm⟩ := hfourier c hc k (m-k+n+1) w hw
    refine ⟨u,hrep,hu,?_⟩
    have hle : S k (m-k+n+1) ≤ D := by
      dsimp [D]
      exact Finset.single_le_sum (s := Finset.range (m+1))
        (f := fun j ↦ S j (m-j+n+1)) (a := k)
        (fun j _ ↦ hS j _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
    have ht : m-k+n+1+k = m+n+1 := by omega
    rw [ht] at hnorm
    exact hnorm.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hle hA) (pow_nonneg hK _))

end JanetCartan.CanonicalAtomRealization
