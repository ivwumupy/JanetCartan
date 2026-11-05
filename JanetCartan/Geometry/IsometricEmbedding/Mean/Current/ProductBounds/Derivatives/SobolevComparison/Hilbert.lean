module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.ProductBounds.Derivatives.SobolevComparison.Coordinates
public import JanetCartan.Analysis.Fourier.Periodic.Sobolev
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.ProductBounds.Derivatives.Integration

/-!
# Periodic jet and Sobolev comparisons in Hilbert codomains

The two analytic comparisons needed to assemble the joint derivative-budget
product estimate in `main:lem:mean-recurrence` in paper.tex. All summability
comes from smoothness; the constants depend only on dimension and order.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace JanetCartan.CurrentMean

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- `main:lem:mean-recurrence`, `app:not:fourier`: an ordered derivative of length
at most `t` has squared multiplier bounded by the order-`t` Bessel weight.
The physical frequency is `2π k`, as in the manuscript. -/
theorem coordinateMultiplier_le_sobolevWeight (is : List (Fin d)) (t : ℕ)
    (ht : is.length ≤ t) (k : Fin d → ℤ) :
    (is.map (fun i ↦ (2 * Real.pi * (k i : ℝ)) ^ 2)).prod ≤
      (1 + frequencyNorm k ^ 2) ^ t := by
  have hb (i : Fin d) : (2 * Real.pi * (k i : ℝ)) ^ 2 ≤ 1 + frequencyNorm k ^ 2 := by
    have h := Finset.single_le_sum (f := fun i : Fin d ↦ (2 * Real.pi * (k i : ℝ)) ^ 2)
      (fun i _ ↦ sq_nonneg _) (Finset.mem_univ i)
    rw [← frequencyNorm_sq_eq_sum] at h
    linarith
  have hprod : (is.map (fun i ↦ (2 * Real.pi * (k i : ℝ)) ^ 2)).prod ≤
      (1 + frequencyNorm k ^ 2) ^ is.length := by
    clear ht
    induction is with
    | nil => simp
    | cons i is ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
      exact mul_le_mul (hb i) ih (List.prod_nonneg (by
        intro a ha
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
        exact sq_nonneg _)) (by positivity) |>.trans_eq (mul_comm _ _)
  exact hprod.trans (pow_le_pow_right₀ (by nlinarith [sq_nonneg (frequencyNorm k)]) ht)

/-- `main:lem:mean-recurrence`: Parseval bounds each Cartesian derivative through
order `t` by the Sobolev norm. Smoothness supplies both convergent series. -/
theorem periodicL2Norm_coordinateDerivList_le_sobolev {f : Torus d → F}
    (hf : IsSmoothPeriodic f) (is : List (Fin d)) (t : ℕ) (ht : is.length ≤ t) :
    periodicL2Norm (periodicCoordinateDerivList is f) ≤ periodicSobolevNorm t f := by
  have hsum := (hf.coordinateDerivList is).hasSum_sq_periodicFourierCoeff
  conv_lhs => rw [← Real.sqrt_sq (show 0 ≤ periodicL2Norm (periodicCoordinateDerivList is f)
    from Real.sqrt_nonneg _)]
  unfold periodicSobolevNorm
  apply Real.sqrt_le_sqrt
  rw [← hsum.tsum_eq]
  apply Summable.tsum_le_tsum _ hsum.summable (hf.summable_periodicSobolevNorm t)
  intro k
  rw [sq_periodicFourierCoeff_coordinateDerivList hf, Real.rpow_natCast]
  exact mul_le_mul_of_nonneg_right (coordinateMultiplier_le_sobolevWeight is t ht k)
    (add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- `main:lem:mean-recurrence`: the operator-norm jet energy is controlled by
the Sobolev norm of any larger integer order. This supplies the higher-factor
comparison in `periodicL2Norm_periodicJet_contracted_weightedBilinear_le`. -/
theorem periodicL2Norm_periodicJet_le_sobolev {f : Torus d → F}
    (hf : IsSmoothPeriodic f) (r t : ℕ) (hrt : r ≤ t) :
    periodicL2Norm (periodicJet r f) ≤
      (Real.sqrt (d ^ r : ℕ) * (d ^ r : ℕ)) * periodicSobolevNorm t f := by
  classical
  let g (is : Fin r → Fin d) (x : Torus d) :=
    ‖periodicCoordinateDerivList (List.ofFn is) f x‖
  have hg (is) : Continuous (g is) := (hf.coordinateDerivList _).1.norm
  have hb (x) : ‖periodicJet r f x‖ ≤ ∑ is, g is x := by
    simpa only [g, periodicJet_apply_basis hf] using
      norm_multilinear_le_sum_basis r (periodicJet r f x)
  have he (is) : periodicL2Norm (g is) =
      periodicL2Norm (periodicCoordinateDerivList (List.ofFn is) f) := by
    simp only [periodicL2Norm, g, norm_norm]
  calc
    _ ≤ Real.sqrt (d ^ r : ℕ) * ∑ is, periodicL2Norm (g is) := by
      simpa using periodicL2Norm_le_sum_majorant Finset.univ g (fun is _ ↦ hg is) _ hb
    _ ≤ Real.sqrt (d ^ r : ℕ) * ∑ _is : Fin r → Fin d, periodicSobolevNorm t f := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      apply Finset.sum_le_sum
      intro is _
      rw [he]
      exact periodicL2Norm_coordinateDerivList_le_sobolev hf _ t (by simpa using hrt)
    _ = _ := by simp [mul_assoc]

/-- `main:lem:mean-recurrence`: the Fourier Sobolev norm is controlled by the
sum of actual jet energies. This converts the integrated Leibniz estimates
back to the Sobolev norm of the contracted product. -/
theorem periodicSobolevNorm_le_sum_periodicJet (S : ℕ) {f : Torus d → F}
    (hf : IsSmoothPeriodic f) :
    periodicSobolevNorm S f ≤
      (Real.sqrt (S.factorial : ℝ) * Real.sqrt ((sobolevMultiindices d S).card : ℝ)) *
        ∑ j ∈ Finset.range (S + 1), periodicL2Norm (periodicJet j f) := by
  let T := ∑ j ∈ Finset.range (S + 1), periodicL2Norm (periodicJet j f)
  have hT : 0 ≤ T := Finset.sum_nonneg (fun j _ ↦ Real.sqrt_nonneg _)
  have hb (α) (hα : α ∈ sobolevMultiindices d S) :
      periodicL2Norm (periodicMultiindexDeriv (fun i ↦ α (some i)) f) ≤ T := by
    apply (periodicL2Norm_coordinateDerivList_le_periodicJet hf
      (sobolevDerivativeList (fun i ↦ α (some i)))).trans
    apply Finset.single_le_sum (f := fun j ↦ periodicL2Norm (periodicJet j f))
      (fun j _ ↦ Real.sqrt_nonneg _)
    rw [Finset.mem_range, sobolevDerivativeList_length]
    have := mem_sobolevMultiindices.mp hα
    omega
  have hD : periodicDerivativeL2Norm S f ≤
      Real.sqrt ((sobolevMultiindices d S).card : ℝ) * T := by
    unfold periodicDerivativeL2Norm
    calc
      _ ≤ Real.sqrt (((sobolevMultiindices d S).card : ℝ) * T ^ 2) := by
        apply Real.sqrt_le_sqrt
        calc
          _ ≤ ∑ α ∈ sobolevMultiindices d S, T ^ 2 :=
            Finset.sum_le_sum (fun α hα ↦ pow_le_pow_left₀ (Real.sqrt_nonneg _) (hb α hα) 2)
          _ = _ := by simp
      _ = _ := by rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hT]
  exact (periodicSobolevNorm_le_factorial_mul_derivativeL2Norm hf S).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hD (Real.sqrt_nonneg _))
/-- `main:lem:mean-recurrence`: a jet-to-Sobolev constant depending only on
the domain dimension and the fixed order cap. -/
def periodicJetSobolevConstant (d S : ℕ) : ℝ :=
  1 + ∑ r ∈ Finset.range (S + 1), Real.sqrt (d ^ r : ℕ) * (d ^ r : ℕ)

/-- `main:lem:mean-recurrence`: the uniform forward comparison constant is at least one. -/
theorem one_le_periodicJetSobolevConstant (d S : ℕ) :
    1 ≤ periodicJetSobolevConstant d S := by
  unfold periodicJetSobolevConstant
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun r _ ↦ by positivity))

/-- `main:lem:mean-recurrence`: one constant works for all `r ≤ t ≤ S`,
with no Fourier-support or summability hypothesis. -/
theorem periodicL2Norm_periodicJet_le_sobolev_uniform (S : ℕ) {f : Torus d → F}
    (hf : IsSmoothPeriodic f) {r t : ℕ} (hrt : r ≤ t) (htS : t ≤ S) :
    periodicL2Norm (periodicJet r f) ≤ periodicJetSobolevConstant d S * periodicSobolevNorm t f := by
  apply (periodicL2Norm_periodicJet_le_sobolev hf r t hrt).trans
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  have h := Finset.single_le_sum
    (f := fun r ↦ Real.sqrt (d ^ r : ℕ) * (d ^ r : ℕ))
    (s := Finset.range (S + 1)) (fun r _ ↦ by positivity)
    (a := r) (Finset.mem_range.mpr (by omega))
  exact h.trans (le_add_of_nonneg_left zero_le_one)

/-- `main:lem:mean-recurrence`: the reverse comparison constant, enlarged
to be at least one. It depends only on the domain dimension and the order. -/
def sobolevPeriodicJetConstant (d S : ℕ) : ℝ :=
  max 1 (Real.sqrt (S.factorial : ℝ) * Real.sqrt ((sobolevMultiindices d S).card : ℝ))

/-- `main:lem:mean-recurrence`: the reverse comparison constant is at least one. -/
theorem one_le_sobolevPeriodicJetConstant (d S : ℕ) :
    1 ≤ sobolevPeriodicJetConstant d S := le_max_left _ _

/-- `main:lem:mean-recurrence`: the reverse comparison with a constant at least one,
depending only on the domain dimension and the order. -/
theorem periodicSobolevNorm_le_sum_periodicJet_uniform (S : ℕ) {f : Torus d → F}
    (hf : IsSmoothPeriodic f) :
    periodicSobolevNorm S f ≤ sobolevPeriodicJetConstant d S *
      ∑ j ∈ Finset.range (S + 1), periodicL2Norm (periodicJet j f) := by
  exact (periodicSobolevNorm_le_sum_periodicJet S hf).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Finset.sum_nonneg (fun j _ ↦ Real.sqrt_nonneg _)))


end JanetCartan.CurrentMean
