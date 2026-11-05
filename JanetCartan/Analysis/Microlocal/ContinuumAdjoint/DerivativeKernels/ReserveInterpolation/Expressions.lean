module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.SymbolBounds
public import JanetCartan.Analysis.ContDiff.Norm.JointBudget

/-!
# Fixed baseline for the actual adjoint coefficient expressions

For `app:ch_background:prop:bg-adjoint`, a primitive derivative of order j
costs only (j-Q) positive derivatives above the fixed low baseline Q.
The consumer is the raw Sobolev assembly in `DerivativeKernels`.
-/

@[expose] public noncomputable section
open scoped ContDiff
namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow
variable {n : ℕ}

namespace AdjointCoefficientExpression

/-- The actual expression evaluation preserves the truncated primitive budget
`degree + q - Q`. Product nodes use the sum of the two truncated excesses,
which is at most the truncated total excess. This is the coefficient estimate
following `app:ch_background:eq:bg-derivative-trade`, before radial factors.
Only original amplitude and L,V jets through R are hypotheses. -/
theorem norm_iteratedFDeriv_evaluateSymbol_le_reserve_profile (L V a)
    (p : AdjointSymbolPoint n)
    (ha : ContDiffAt ℝ ∞ (fun p : AdjointSymbolPoint n ↦ a p.1.1 p.1.2 p.2) p)
    (hfield : ∀ d j, ContDiffAt ℝ ∞ (fun p : AdjointSymbolPoint n ↦ branchField L V d j p.1) p) (Q R : ℕ) (B : ℕ → ℝ) (hB : ∀ q, 0 ≤ B q)
    {H T : ℝ} (hH : 1 ≤ H) (hT : 0 < T)
    (hamp : ∀ i ≤ R, ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦ a p.1.1 p.1.2 p.2) p‖ ≤
      B i * H ^ (((i - Q : ℕ) : ℝ) / T))
    (ds : List (InitialCarrierDerivative n))
    (hcoeff : ∀ d ∈ ds, ∀ j i, i ≤ R → ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦ branchField L V d j p.1) p‖ ≤
      B i * H ^ (((i - Q : ℕ) : ℝ) / T))
    (e : AdjointCoefficientExpression n) (hdirs : e.UsesDirections ds)
    (q : ℕ) (hq : e.degree + q ≤ R) :
    ‖iteratedFDeriv ℝ q (e.evaluateSymbol L V a) p‖ ≤
      e.jetConstant B q * H ^ (((e.degree + q - Q : ℕ) : ℝ) / T) := by
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have smooth (e : AdjointCoefficientExpression n) := contDiffAt_evaluateSymbol L V a p ha hfield e
  have mono (e : AdjointCoefficientExpression n) (q b : ℕ) (hb : e.degree + q ≤ b) :
      e.jetConstant B q * H ^ (((e.degree + q - Q : ℕ) : ℝ) / T) ≤
        e.jetConstant B q * H ^ (((b - Q : ℕ) : ℝ) / T) := by
    apply mul_le_mul_of_nonneg_left _ (jetConstant_nonneg B hB e q)
    apply Real.rpow_le_rpow_of_exponent_le hH
    exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.sub_le_sub_right hb Q) hT.le
  induction e generalizing q with
  | amplitude => simpa [evaluateSymbol, degree, jetConstant] using hamp q (by simpa [degree] using hq)
  | field d j =>
      simpa [evaluateSymbol, degree, jetConstant] using
        hcoeff d hdirs j q (by simpa [degree] using hq)
  | add e f he hf =>
      have hqe : e.degree + q ≤ R := (Nat.add_le_add_right (le_max_left _ _) q).trans hq
      have hqf : f.degree + q ≤ R := (Nat.add_le_add_right (le_max_right _ _) q).trans hq
      have he' := (he hdirs.1 q hqe).trans (mono e q _
        (Nat.add_le_add_right (le_max_left e.degree f.degree) q))
      have hf' := (hf hdirs.2 q hqf).trans (mono f q _
        (Nat.add_le_add_right (le_max_right e.degree f.degree) q))
      dsimp only [evaluateSymbol]
      rw [show (fun p ↦ e.evaluateSymbol L V a p + f.evaluateSymbol L V a p) =
          e.evaluateSymbol L V a + f.evaluateSymbol L V a from rfl,
        iteratedFDeriv_add_apply ((smooth e).of_le (by simp)) ((smooth f).of_le (by simp))]
      exact (norm_add_le _ _).trans ((add_le_add he' hf').trans_eq (by
        simp only [jetConstant, degree, add_mul]))
  | neg e he =>
      change ‖iteratedFDeriv ℝ q (-e.evaluateSymbol L V a) p‖ ≤ _
      rw [iteratedFDeriv_neg]
      simpa only [Pi.neg_apply, norm_neg, degree, jetConstant] using he hdirs q hq
  | mul e f he hf =>
      apply (adjoint_local_product_jet_bound q (smooth e) (smooth f)).trans
      simp only [jetConstant, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i hi
      have hiq : i ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hqe : e.degree + i ≤ R := by simp only [degree] at hq; omega
      have hqf : f.degree + (q-i) ≤ R := by simp only [degree] at hq; omega
      calc
        _ ≤ (q.choose i : ℝ) *
            (e.jetConstant B i * H ^ (((e.degree + i - Q : ℕ) : ℝ) / T)) *
            (f.jetConstant B (q-i) * H ^ (((f.degree + (q-i) - Q : ℕ) : ℝ) / T)) := by
          apply mul_le_mul
            (mul_le_mul_of_nonneg_left (he hdirs.1 i hqe) (Nat.cast_nonneg _))
            (hf hdirs.2 (q-i) hqf)
            (norm_nonneg _)
          exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
            (jetConstant_nonneg B hB e i) (Real.rpow_nonneg hHpos.le _))
        _ = ((q.choose i : ℝ) * e.jetConstant B i * f.jetConstant B (q-i)) *
            (H ^ (((e.degree + i - Q : ℕ) : ℝ) / T) *
              H ^ (((f.degree + (q-i) - Q : ℕ) : ℝ) / T)) := by ring
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _
            (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (jetConstant_nonneg B hB e i))
              (jetConstant_nonneg B hB f (q-i)))
          rw [← Real.rpow_add hHpos, ← add_div, ← Nat.cast_add]
          apply Real.rpow_le_rpow_of_exponent_le hH
          apply div_le_div_of_nonneg_right _ hT.le
          have hb : (e.degree + i - Q) + (f.degree + (q-i) - Q) ≤
              e.degree + f.degree + q - Q := by omega
          exact_mod_cast hb
  | deriv h e he =>
      have hqe : e.degree + (q+1) ≤ R := by simpa [degree, Nat.add_assoc, Nat.add_comm 1] using hq
      have hd := norm_iteratedFDeriv_clm_apply_const
        ((smooth e).fderiv_right (by simp))
        (show (q : ℕ∞ω) ≤ ∞ by simp) (c := (h, (0 : Euclidean (n-1)))) (x := p)
      rw [norm_iteratedFDeriv_fderiv] at hd
      rw [show ‖(h, (0 : Euclidean (n-1)))‖ = ‖h‖ by
        change max ‖h‖ ‖(0 : Euclidean (n-1))‖ = ‖h‖
        rw [norm_zero, max_eq_left (norm_nonneg h)]] at hd
      exact hd.trans ((mul_le_mul_of_nonneg_left (he hdirs (q+1) hqe) (norm_nonneg h)).trans_eq
        (by simp [jetConstant, degree, Nat.add_assoc, Nat.add_comm 1, mul_assoc]))


end AdjointCoefficientExpression
end JanetCartan.ContinuumAdjoint.DerivativeKernels
