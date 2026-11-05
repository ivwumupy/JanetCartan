module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.SymbolBounds.Expressions

/-!
# Primitive mixed-jet bounds for differentiated adjoint amplitudes

The norm estimates for `app:ch_background:prop:bg-adjoint` are proved from
the original normalized amplitude and L,V. The Leibniz convolution retains
the total derivative budget, so interpolation profiles consume only one
high norm when the total primitive order is below the interpolation order.
-/

@[expose] public noncomputable section
open scoped ContDiff
namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow
variable {n : ℕ}
namespace AdjointCoefficientExpression

/-- The explicit finite Leibniz constant for a primitive expression at symbol
reserve q (`app:ch_background:prop:bg-adjoint`). It depends on the primitive
profile constants, never on the high norm H. -/
def jetConstant (B : ℕ → ℝ) : AdjointCoefficientExpression n → ℕ → ℝ
  | .amplitude, q | .field _ _, q => B q
  | .add e f, q => e.jetConstant B q + f.jetConstant B q
  | .neg e, q => e.jetConstant B q
  | .mul e f, q => ∑ i ∈ Finset.range (q + 1),
      (q.choose i : ℝ) * e.jetConstant B i * f.jetConstant B (q - i)
  | .deriv h e, q => ‖h‖ * e.jetConstant B (q + 1)

/-- Positivity of the explicit primitive-jet constant
(`app:ch_background:prop:bg-adjoint`). -/
theorem jetConstant_nonneg (B : ℕ → ℝ) (hB : ∀ q, 0 ≤ B q)
    (e : AdjointCoefficientExpression n) (q : ℕ) : 0 ≤ e.jetConstant B q := by
  induction e generalizing q with
  | amplitude | field => exact hB q
  | add e f he hf => exact add_nonneg (he q) (hf q)
  | neg e he => exact he q
  | mul e f he hf =>
      exact Finset.sum_nonneg (fun i _ ↦ mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (he i)) (hf (q-i)))
  | deriv h e he => exact mul_nonneg (norm_nonneg h) (he (q+1))

/-- Primitive interpolation profiles imply mixed-jet bounds, with exactly
`degree + q` in the exponent. Only primitive jets through that order are
required. This is the one-high budget in
`app:ch_background:prop:bg-adjoint`, before geometric instantiation. -/
theorem norm_iteratedFDeriv_evaluate_le_profile (L V a η)
    (ha : ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦ a p.1 p.2 η))
    (hfield : ∀ d j, ContDiff ℝ ∞ (branchField L V d j))
    (p : AdjointJetPoint n) (R : ℕ) (B : ℕ → ℝ) (hB : ∀ q, 0 ≤ B q)
    {H T : ℝ} (hH : 1 ≤ H) (hT : 0 < T)
    (hamp : ∀ i ≤ R, ‖iteratedFDeriv ℝ i (fun p : AdjointJetPoint n ↦ a p.1 p.2 η) p‖ ≤
      B i * H ^ ((i : ℝ) / T))
    (ds : List (InitialCarrierDerivative n))
    (hcoeff : ∀ d ∈ ds, ∀ j i, i ≤ R → ‖iteratedFDeriv ℝ i (branchField L V d j) p‖ ≤
      B i * H ^ ((i : ℝ) / T))
    (e : AdjointCoefficientExpression n) (hdirs : e.UsesDirections ds)
    (q : ℕ) (hq : e.degree + q ≤ R) :
    ‖iteratedFDeriv ℝ q (e.evaluate L V a η) p‖ ≤
      e.jetConstant B q * H ^ (((e.degree + q : ℕ) : ℝ) / T) := by
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have smooth (e : AdjointCoefficientExpression n) := contDiff_evaluate L V a η ha hfield e
  have mono (e : AdjointCoefficientExpression n) (q b : ℕ) (hb : e.degree + q ≤ b) :
      e.jetConstant B q * H ^ (((e.degree + q : ℕ) : ℝ) / T) ≤
        e.jetConstant B q * H ^ ((b : ℝ) / T) := by
    apply mul_le_mul_of_nonneg_left _ (jetConstant_nonneg B hB e q)
    apply Real.rpow_le_rpow_of_exponent_le hH
    exact div_le_div_of_nonneg_right (by exact_mod_cast hb) hT.le
  induction e generalizing q with
  | amplitude => simpa [evaluate, degree, jetConstant] using hamp q (by simpa [degree] using hq)
  | field d j =>
      simpa [evaluate, degree, jetConstant] using
        hcoeff d hdirs j q (by simpa [degree] using hq)
  | add e f he hf =>
      have hqe : e.degree + q ≤ R := (Nat.add_le_add_right (le_max_left _ _) q).trans hq
      have hqf : f.degree + q ≤ R := (Nat.add_le_add_right (le_max_right _ _) q).trans hq
      have he' := (he hdirs.1 q hqe).trans (mono e q _
        (Nat.add_le_add_right (le_max_left e.degree f.degree) q))
      have hf' := (hf hdirs.2 q hqf).trans (mono f q _
        (Nat.add_le_add_right (le_max_right e.degree f.degree) q))
      dsimp only [evaluate]
      rw [show (fun p ↦ e.evaluate L V a η p + f.evaluate L V a η p) =
          e.evaluate L V a η + f.evaluate L V a η from rfl,
        iteratedFDeriv_add ((smooth e).of_le (by simp)) ((smooth f).of_le (by simp))]
      exact (norm_add_le _ _).trans ((add_le_add he' hf').trans_eq (by
        simp only [jetConstant, degree, add_mul]))
  | neg e he =>
      change ‖iteratedFDeriv ℝ q (-e.evaluate L V a η) p‖ ≤ _
      rw [iteratedFDeriv_neg]
      simpa only [Pi.neg_apply, norm_neg, degree, jetConstant] using he hdirs q hq
  | mul e f he hf =>
      apply (norm_iteratedFDeriv_mul_le (smooth e) (smooth f) p (by simp)).trans
      simp only [jetConstant, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i hi
      have hiq : i ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hqe : e.degree + i ≤ R := by simp only [degree] at hq; omega
      have hqf : f.degree + (q-i) ≤ R := by simp only [degree] at hq; omega
      calc
        _ ≤ (q.choose i : ℝ) *
            (e.jetConstant B i * H ^ (((e.degree + i : ℕ) : ℝ) / T)) *
            (f.jetConstant B (q-i) * H ^ (((f.degree + (q-i) : ℕ) : ℝ) / T)) := by
          apply mul_le_mul
            (mul_le_mul_of_nonneg_left (he hdirs.1 i hqe) (Nat.cast_nonneg _))
            (hf hdirs.2 (q-i) hqf)
            (norm_nonneg _)
          exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
            (jetConstant_nonneg B hB e i) (Real.rpow_nonneg hHpos.le _))
        _ = _ := by
          simp only [degree, Nat.cast_add, Nat.cast_sub hiq]
          rw [show (q.choose i : ℝ) * (e.jetConstant B i * H ^ ((e.degree + i) / T)) *
              (f.jetConstant B (q-i) * H ^ ((f.degree + (q-i)) / T)) =
              ((q.choose i : ℝ) * e.jetConstant B i * f.jetConstant B (q-i)) *
                (H ^ ((e.degree + i) / T) * H ^ ((f.degree + (q-i)) / T)) by ring,
            ← Real.rpow_add hHpos]
          congr 2
          ring
  | deriv h e he =>
      have hqe : e.degree + (q+1) ≤ R := by simpa [degree, Nat.add_assoc, Nat.add_comm 1] using hq
      have hd := norm_iteratedFDeriv_clm_apply_const
        ((smooth e).fderiv_right (by simp)).contDiffAt
        (show (q : ℕ∞ω) ≤ ∞ by simp) (c := h) (x := p)
      rw [norm_iteratedFDeriv_fderiv] at hd
      exact hd.trans ((mul_le_mul_of_nonneg_left (he hdirs (q+1) hqe) (norm_nonneg h)).trans_eq
        (by simp [jetConstant, degree, Nat.add_assoc, Nat.add_comm 1, mul_assoc]))

end AdjointCoefficientExpression
end JanetCartan.ContinuumAdjoint.DerivativeKernels
