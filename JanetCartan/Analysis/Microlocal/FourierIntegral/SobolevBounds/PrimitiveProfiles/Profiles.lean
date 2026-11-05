module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.PrimitiveProfiles.OrderedJets

/-!
# The actual amplitude and scalar primitive profiles

The common profile indexing of `StrongAssembly` for Step 3 of
`app:ch_regular_base:thm:actual-calculus`. The amplitude includes all masks;
the scalar fields are the actual mixed matrix and its actual inverse.
The endpoint comparison with shifted phase seminorms is a separate obligation.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.PrimitiveProfiles
open FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local
variable {n r : ℕ}

/-- The literal normalized primitive majorants used by the forward and adjoint
branch estimates. Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`.
The matrix branch uses the Frobenius norm of the complete amplitude. -/
def primitiveProfile (K : Set (Point n)) (S : Euclidean n → Euclidean n → ℝ)
    (A : FullAmplitude n r) : Option (ScalarIndex n) → ℕ → ℝ
  | none, j => normalizedSeminorm K j (uncurry A)
  | some a, j => normalizedSeminorm K j (uncurry (scalarPrimitive S a))

/-- The actual profiles are nonnegative, as required in
`exists_graph_sobolev_constant_of_weighted_primitives`. Source: Step 3. -/
theorem primitiveProfile_nonneg (K : Set (Point n))
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (a : Option (ScalarIndex n)) (j : ℕ) : 0 ≤ primitiveProfile K S A a j := by
  cases a <;> exact normalizedSeminorm_nonneg _ _ _

/-- Symbol-class finiteness gives monotonicity of the actual profiles. For the
scalar fields this finiteness is obtained from degree-zero homogeneity using
`normalizedSeminorm_eq_cNorm_of_invariant`; it is not a high inverse-jet bound.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem primitiveProfile_monotone {K : Set (Point n)}
    {S : Euclidean n → Euclidean n → ℝ} {A : FullAmplitude n r}
    (hA : ∀ j, BoundedNormalizedSeminorm K j (uncurry A))
    (hS : ∀ a j, BoundedNormalizedSeminorm K j (uncurry (scalarPrimitive S a)))
    (a : Option (ScalarIndex n)) : Monotone (primitiveProfile K S A a) := by
  intro j k hjk
  cases a with
  | none => exact normalizedSeminorm_mono (hA k) hjk
  | some a => exact normalizedSeminorm_mono (hS a k) hjk

/-- Individual interpolation for all actual profiles with one constant and
the exact exponents in `StrongAssembly`. Constants precede the amplitude and
phase. Smoothness and symbol-class finiteness, rather than interpolation, are
inputs. The phase endpoint producer must discharge scalar finiteness from
homogeneity. Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem exists_primitiveProfile_interpolation (z : Point n) {ρ : ℝ} (hρ : 0 < ρ)
    {U : Set (Point n)} (hU : IsOpen U) (hball : Metric.closedBall z ρ ⊆ U) (μ s : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r),
      (∀ R : ℝ, 1 ≤ R → ContDiffOn ℝ (μ + s : ℕ) (normalizedField R (uncurry A)) U) →
      (∀ a R, 1 ≤ R → ContDiffOn ℝ (μ + s : ℕ)
        (normalizedField R (uncurry (scalarPrimitive S a))) U) →
      BoundedNormalizedSeminorm (Metric.closedBall z ρ) (μ + s) (uncurry A) →
      (∀ a, BoundedNormalizedSeminorm (Metric.closedBall z ρ) (μ + s)
        (uncurry (scalarPrimitive S a))) →
      ∀ a j, μ < j → j < μ + s →
        primitiveProfile (Metric.closedBall z ρ) S A a j ≤
          K * primitiveProfile (Metric.closedBall z ρ) S A a μ ^
            (1 - ((j - μ : ℕ) : ℝ) / s) *
            primitiveProfile (Metric.closedBall z ρ) S A a (μ + s) ^
              (((j - μ : ℕ) : ℝ) / s) := by
  obtain ⟨KA, hKA, hA⟩ := exists_normalizedSeminorm_interpolation_constant
    (F := Matrix (Fin r) (Fin r) ℂ) z hρ hU hball μ s
  obtain ⟨KS, hKS, hS⟩ := exists_normalizedSeminorm_interpolation_constant
    (F := ℂ) z hρ hU hball μ s
  refine ⟨max KA KS, hKA.trans (le_max_left _ _), ?_⟩
  intro S A hsA hsS hbA hbS a j hj hj'
  cases a with
  | none =>
    exact (hA (uncurry A) hsA hbA j hj hj').trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left KA KS)
        (Real.rpow_nonneg (normalizedSeminorm_nonneg _ _ _) _))
      (Real.rpow_nonneg (normalizedSeminorm_nonneg _ _ _) _))
  | some a =>
    exact (hS (uncurry (scalarPrimitive S a)) (hsS a) (hbS a) j hj hj').trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right KA KS)
          (Real.rpow_nonneg (normalizedSeminorm_nonneg _ _ _) _))
        (Real.rpow_nonneg (normalizedSeminorm_nonneg _ _ _) _))

end JanetCartan.FourierIntegral.PrimitiveProfiles
