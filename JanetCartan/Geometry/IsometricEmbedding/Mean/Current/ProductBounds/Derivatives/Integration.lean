module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.ProductBounds.Derivatives.Leibniz
public import Mathlib.Algebra.Order.Chebyshev
/-!
# Integrating the weighted Leibniz estimate

The integration step for the mixed estimate of `main:lem:mean-recurrence`.
Only the number of derivative terms enters the constant; the sample count does not.
-/

@[expose] public noncomputable section
open MeasureTheory
namespace JanetCartan.CurrentMean
variable {d : ℕ} {κ G : Type*} [NormedAddCommGroup G]
/-- `main:lem:mean-recurrence`: an actual finite sum of pointwise majorants
can be integrated with loss at most the square root of the number of terms.
Applied below only to derivative terms, never to the sample family. -/
theorem periodicL2Norm_le_sum_majorant (t : Finset κ) (g : κ → Torus d → ℝ) (hg : ∀ j ∈ t, Continuous (g j))
    (f : Torus d → G) (hb : ∀ x, ‖f x‖ ≤ ∑ j ∈ t, g j x) :
    periodicL2Norm f ≤ Real.sqrt (t.card : ℝ) * ∑ j ∈ t, periodicL2Norm (g j) := by
  have hi (j : κ) (hj : j ∈ t) : Integrable (fun x ↦ g j x ^ 2) :=
    ((hg j hj).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he : (∫ x, ∑ j ∈ t, g j x ^ 2) = ∑ j ∈ t, periodicL2Norm (g j) ^ 2 := by
    rw [integral_finsetSum t hi]
    apply Finset.sum_congr rfl
    intro j _
    rw [periodicL2Norm, Real.sq_sqrt (integral_nonneg (fun x ↦ sq_nonneg _))]
    simp only [Real.norm_eq_abs, sq_abs]
  calc
    _ ≤ Real.sqrt ((t.card : ℝ) * ∑ j ∈ t, periodicL2Norm (g j) ^ 2) := by
      apply Real.sqrt_le_sqrt
      calc
        (∫ x, ‖f x‖ ^ 2) ≤ ∫ x, (t.card : ℝ) * ∑ j ∈ t, g j x ^ 2 := by
          apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x ↦ sq_nonneg _))
            ((integrable_finsetSum t hi).const_mul _) (Filter.Eventually.of_forall _)
          intro x
          exact (pow_le_pow_left₀ (norm_nonneg _) (hb x) 2).trans sq_sum_le_card_mul_sum_sq
        _ = _ := by rw [integral_const_mul, he]
    _ ≤ _ := by
      rw [Real.sqrt_mul (Nat.cast_nonneg _)]
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      apply Real.sqrt_le_left (Finset.sum_nonneg (fun j _ ↦ Real.sqrt_nonneg _)) |>.2
      exact Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ ↦ Real.sqrt_nonneg _)

variable {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ F] in
/-- `main:lem:mean-recurrence`: integrating the square-root weighted energy
recovers exactly the weighted L² norm. Zero weights and empty families are allowed. -/
theorem periodicL2Norm_weightedEnergy_eq (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (E : Torus d → ι → F) (hE : ∀ i, Continuous (fun x ↦ E x i)) :
    periodicL2Norm (fun x ↦ Real.sqrt (∑ i, μ i * ‖E x i‖ ^ 2)) =
      weightedPeriodicL2Norm μ E := by
  have hi (i : ι) : Integrable (fun x ↦ ‖E x i‖ ^ 2) :=
    ((hE i).memLp_of_hasCompactSupport (p := 2)
      (HasCompactSupport.of_compactSpace _)).integrable_norm_pow (by decide)
  unfold periodicL2Norm weightedPeriodicL2Norm
  simp_rw [Real.norm_eq_abs, sq_abs, Real.sq_sqrt
    (Finset.sum_nonneg (fun i _ ↦ mul_nonneg (hμ i) (sq_nonneg _)))]
  rw [integral_finsetSum Finset.univ (fun i _ ↦ (hi i).const_mul (μ i))]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul, periodicL2Norm, Real.sq_sqrt (integral_nonneg (fun x ↦ sq_nonneg _))]

private theorem periodicL2Norm_const_mul_nonneg (c : ℝ) (hc : 0 ≤ c)
    (g : Torus d → ℝ) : periodicL2Norm (fun x ↦ c * g x) = c * periodicL2Norm g := by
  simp only [periodicL2Norm, norm_mul, mul_pow, integral_const_mul]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), Real.norm_of_nonneg hc]

variable {H V : Type*} [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- `main:lem:mean-recurrence`: the integrated weighted Leibniz estimate for
actual jets. The higher factor remains in the L² norm of its derivative of
order `s-a-r`; the Sobolev comparison is a separate prerequisite. -/
theorem periodicL2Norm_periodicJet_contracted_weightedBilinear_le
    (B : F →L[ℝ] G →L[ℝ] H) (hB : ‖B‖ ≤ 1)
    (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (D : Torus d → ι → F) (E : Torus d → ι → G)
    (hD : ∀ i, IsSmoothPeriodic (fun x ↦ D x i))
    (hE : ∀ i, IsSmoothPeriodic (fun x ↦ E x i))
    (C : Torus d → H →L[ℝ] V) (hC : IsSmoothPeriodic C) (s : ℕ) :
    periodicL2Norm (periodicJet s (fun x ↦ C x (∑ i, μ i • B (D x i) (E x i)))) ≤
      Real.sqrt (∑ a ∈ Finset.range (s + 1), (s-a+1 : ℕ) : ℕ) *
        ∑ a ∈ Finset.range (s + 1), ∑ r ∈ Finset.range (s-a+1),
          (s.choose a : ℝ) * ((s-a).choose r : ℝ) *
            cNorm (fundamentalCell d) a (periodicLift C) * weightedPeriodicCNorm μ r D *
              weightedPeriodicL2Norm μ (fun x i ↦ periodicJet (s-a-r) (fun x ↦ E x i) x) := by
  let t := (Finset.range (s+1)).sigma (fun a ↦ Finset.range (s-a+1))
  let q (p : Σ _a : ℕ, ℕ) : ℝ := (s.choose p.1 : ℝ) * ((s-p.1).choose p.2 : ℝ) *
    cNorm (fundamentalCell d) p.1 (periodicLift C) * weightedPeriodicCNorm μ p.2 D
  have hq (p) : 0 ≤ q p := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (cNorm_nonneg _ _ _)) (Real.sqrt_nonneg _)
  let g (p : Σ _a : ℕ, ℕ) (x : Torus d) : ℝ :=
    q p * Real.sqrt (∑ i, μ i * ‖periodicJet (s-p.1-p.2) (fun x ↦ E x i) x‖ ^ 2)
  have hg (p) : Continuous (g p) := by
    apply Continuous.const_mul
    apply Continuous.sqrt
    apply continuous_finsetSum
    intro i _
    exact (((periodicJet_spec (hE i) _).1.1.norm).pow 2).const_mul _
  have hb (x : Torus d) :
      ‖periodicJet s (fun x ↦ C x (∑ i, μ i • B (D x i) (E x i))) x‖ ≤
        ∑ p ∈ t, g p x := by
    simpa only [t, g, q, Finset.sum_sigma] using
      norm_periodicJet_contracted_weightedBilinear_le B hB μ hμ D E hD hE C hC s x
  have he (p) : periodicL2Norm (g p) = q p *
      weightedPeriodicL2Norm μ (fun x i ↦ periodicJet (s-p.1-p.2) (fun x ↦ E x i) x) := by
    rw [show g p = _ from rfl, periodicL2Norm_const_mul_nonneg _ (hq p),
      periodicL2Norm_weightedEnergy_eq μ hμ _ (fun i ↦ (periodicJet_spec (hE i) _).1.1)]
  have h := periodicL2Norm_le_sum_majorant t g (fun p _ ↦ hg p) _ hb
  simp_rw [he] at h
  simpa only [t, q, Finset.card_sigma, Finset.card_range, Finset.sum_sigma] using h

end JanetCartan.CurrentMean
