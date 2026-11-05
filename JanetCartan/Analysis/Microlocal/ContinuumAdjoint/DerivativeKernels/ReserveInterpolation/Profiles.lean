module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.ReserveInterpolation.RescaledBounds

/-!
# Primitive transport profiles above a fixed baseline

The consumer is the fixed-reserve adjoint bound of
`app:ch_background:prop:bg-adjoint`. The angular mask, r(z,Y), and the flow
factor remain actual differentiated functions. Geometry maps have baseline
Q+1, while scalar factors have baseline Q. No generated jet is an input.
-/

@[expose] public noncomputable section
open scoped ContDiff
namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow CompositionBounds FourierIntegral.NormalOneHigh
variable {n : ℕ}

private theorem reserve_sum_excess_le {ι : Type*} (I : Finset ι) (j : ι → ℕ) (Q : ℕ) :
    ∑ i ∈ I, (j i - Q) ≤ (∑ i ∈ I, j i) - Q := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
      simp only [Finset.sum_insert hi]
      omega

private theorem reserve_partition_excess_le (Q : ℕ) {q : ℕ} (π : OrderedFinpartition q) :
    (π.length - Q) + ∑ i, (π.partSize i - 1 - Q) ≤ q - Q := by
  have hb := reserve_sum_excess_le Finset.univ (fun i ↦ π.partSize i - 1) Q
  have he := FlowForcing.sum_partSize_sub_one_add_length π
  omega

/-- The original primitive jet profile from fixed low and high C-norm bounds
and the explicit interpolation input of `JointBudget`. This produces the
profiles used below; geometric interpolation is supplied by the parent of
`app:ch_background:prop:bg-adjoint`, never by a generated-symbol assumption. -/
theorem adjoint_primitive_reserve_profile_of_interpolation
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : Set E) (f : E → F) (Q s j : ℕ) (B K H : ℝ)
    (hB : 1 ≤ B) (hK : 1 ≤ K) (hH : 1 ≤ H)
    (hlow : cNorm S Q f ≤ B) (hhigh : cNorm S (Q+s) f ≤ H)
    (hj : j ≤ Q+s)
    (hinterp : Q < j → j < Q+s → cNorm S j f ≤
      K * cNorm S Q f ^ (1 - ((j-Q : ℕ) : ℝ) / s) *
        cNorm S (Q+s) f ^ (((j-Q : ℕ) : ℝ) / s))
    (hbounded : BddAbove ((fun x ↦ ‖iteratedFDeriv ℝ j f x‖) '' S))
    {p : E} (hp : p ∈ S) :
    ‖iteratedFDeriv ℝ j f p‖ ≤ (K*B) * H ^ (((j-Q : ℕ) : ℝ) / s) := by
  apply (JointBudget.norm_iteratedFDeriv_le_derivativeSupNorm S j f hbounded hp).trans
  apply (JointBudget.derivativeSupNorm_le_cNorm S j f).trans
  exact JointBudget.interpolation_le_scaled_rpow (fun i ↦ cNorm S i f) Q s j B K H
    (fun i ↦ JointBudget.cNorm_nonneg S i f) (JointBudget.cNorm_monotone S f)
    hB hK hH hlow hhigh hj hinterp

/-- Fixed-baseline product estimate for the original amplitude in
`app:ch_background:prop:bg-adjoint`. -/
private theorem local_product_reserve_profile {f g : AdjointSymbolPoint n → ℂ}
    (p : AdjointSymbolPoint n) (hf : ContDiffAt ℝ ∞ f p) (hg : ContDiffAt ℝ ∞ g p)
    (Q q : ℕ) (A B : ℕ → ℝ) (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i)
    {H T : ℝ} (hH : 1 ≤ H) (hT : 0 < T)
    (hfa : ∀ i ≤ q, ‖iteratedFDeriv ℝ i f p‖ ≤ A i * H ^ (((i - Q : ℕ) : ℝ) / T))
    (hgb : ∀ i ≤ q, ‖iteratedFDeriv ℝ i g p‖ ≤ B i * H ^ (((i - Q : ℕ) : ℝ) / T)) :
    ‖iteratedFDeriv ℝ q (fun p ↦ f p * g p) p‖ ≤
      adjointLeibnizBudget A B q * H ^ (((q - Q : ℕ) : ℝ) / T) := by
  apply (adjoint_local_product_jet_bound q hf hg).trans
  unfold adjointLeibnizBudget
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hiq : i ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  calc
    _ ≤ (q.choose i : ℝ) * (A i * H ^ (((i - Q : ℕ) : ℝ) / T)) *
        (B (q-i) * H ^ (((q-i-Q : ℕ) : ℝ) / T)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hfa i hiq) (Nat.cast_nonneg _))
        (hgb (q-i) (Nat.sub_le _ _)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hA i) (Real.rpow_nonneg (le_trans zero_le_one hH) _)))
    _ = ((q.choose i : ℝ) * A i * B (q-i)) *
        (H ^ (((i-Q : ℕ) : ℝ) / T) * H ^ (((q-i-Q : ℕ) : ℝ) / T)) := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i)) (hB (q-i)))
      rw [← Real.rpow_add (lt_of_lt_of_le zero_lt_one hH), ← add_div, ← Nat.cast_add]
      apply Real.rpow_le_rpow_of_exponent_le hH
      apply div_le_div_of_nonneg_right _ hT.le
      exact_mod_cast (show (i-Q) + (q-i-Q) ≤ q-Q by omega)

/-- The scalar pullback profile for the actual composition `r(z,Y(z,x))`.
The scalar has baseline Q, and each positive-order derivative of the
geometry has baseline Q+1. The shared partition identity bounds the sum
of all truncated excesses by q-Q, including q=0
(`app:ch_background:prop:bg-adjoint`). -/
private theorem local_pullback_reserve_profile
    (Y : AdjointSymbolPoint n → CarrierParameter × Euclidean (n-1))
    (r : CarrierParameter × Euclidean (n-1) → ℂ) (p : AdjointSymbolPoint n)
    (hY : ContDiffAt ℝ ∞ Y p) (hr : ContDiffAt ℝ ∞ r (Y p)) (Q q : ℕ)
    (A B : ℕ → ℝ) (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i) {H T : ℝ} (hH : 1 ≤ H) (hT : 0 < T)
    (hrA : ∀ i ≤ q, ‖iteratedFDeriv ℝ i r (Y p)‖ ≤ A i * H ^ (((i - Q : ℕ) : ℝ) / T))
    (hYB : ∀ i, 1 ≤ i → i ≤ q →
      ‖iteratedFDeriv ℝ i Y p‖ ≤
        B i * H ^ (((i-1-Q : ℕ) : ℝ) / T)) :
    ‖iteratedFDeriv ℝ q (fun p : AdjointSymbolPoint n ↦ r (Y p)) p‖ ≤
      compositionBudget A B q * H ^ (((q - Q : ℕ) : ℝ) / T) := by
  apply (norm_iteratedFDeriv_comp_le_partition_sum
    (hr.of_le (show (q : ℕ∞ω) ≤ ∞ by simp))
    (hY.of_le (show (q : ℕ∞ω) ≤ ∞ by simp)) (le_refl q)).trans
  unfold compositionBudget
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro π _
  calc
    _ ≤ (A π.length * H ^ (((π.length - Q : ℕ) : ℝ) / T)) *
        ∏ i, B (π.partSize i) * H ^ (((π.partSize i - 1 - Q : ℕ) : ℝ) / T) :=
      mul_le_mul (hrA _ π.length_le)
        (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun i _ ↦
          hYB _ (π.partSize_pos i) (π.partSize_le i)))
        (Finset.prod_nonneg (fun _ _ ↦ norm_nonneg _))
        (mul_nonneg (hA _) (Real.rpow_nonneg (le_trans zero_le_one hH) _))
    _ = (A π.length * ∏ i, B (π.partSize i)) *
        H ^ ((((π.length - Q) + ∑ i, (π.partSize i - 1 - Q) : ℕ) : ℝ) / T) := by
      rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos (lt_of_lt_of_le zero_lt_one hH),
        mul_mul_mul_comm, ← Real.rpow_add (lt_of_lt_of_le zero_lt_one hH),
        ← Finset.sum_div, ← add_div, ← Nat.cast_sum, ← Nat.cast_add]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hA _) (Finset.prod_nonneg fun i _ ↦ hB _))
      apply Real.rpow_le_rpow_of_exponent_le hH
      apply div_le_div_of_nonneg_right _ hT.le
      exact_mod_cast reserve_partition_excess_le Q π

/-- Producer of the full primitive amplitude profile for
`exists_expansion_fixedReserve_halfOrder_bound`. Jets of rho and r are estimated
before composition. The angular normalization, actual map `(z,x) ↦ (z,Y(z,x))`,
and flow factor all remain differentiated. The partition sums preserve a
total interpolation exponent (q-Q)/T, with natural subtraction
(`app:ch_background:prop:bg-adjoint`). -/
theorem normalizedTransportAmplitude_symbol_reserve_profile (c ρ r Y flow) (R : ℝ)
    (p : AdjointSymbolPoint n) (Q q : ℕ)
    (hc : ContDiffAt ℝ ∞ (fun p : AdjointSymbolPoint n ↦ c p.1) p)
    (hρ : ContDiffAt ℝ ∞ (fun v : CarrierParameter × Euclidean (n-1) ↦ ρ v.1 v.2)
      (adjointAngularGraph R p))
    (hN : ContDiffAt ℝ ∞ (adjointAngularGraph R) p)
    (hr : ContDiffAt ℝ ∞ r (adjointScalarGraph Y p))
    (hY : ContDiffAt ℝ ∞ (adjointScalarGraph Y) p)
    (hf : ContDiffAt ℝ ∞ (fun p : AdjointSymbolPoint n ↦ flow p.1) p)
    (C P N A B F : ℕ → ℝ)
    (hC : ∀ i, 0 ≤ C i) (hP : ∀ i, 0 ≤ P i) (hNpos : ∀ i, 0 ≤ N i)
    (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i) (hF : ∀ i, 0 ≤ F i)
    {H T : ℝ} (hH : 1 ≤ H) (hT : 0 < T)
    (hcC : ∀ i ≤ q, ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦ c p.1) p‖ ≤
      C i * H ^ (((i - Q : ℕ) : ℝ) / T))
    (hρP : ∀ i ≤ q, ‖iteratedFDeriv ℝ i
      (fun v : CarrierParameter × Euclidean (n-1) ↦ ρ v.1 v.2) (adjointAngularGraph R p)‖ ≤
        P i * H ^ (((i - Q : ℕ) : ℝ) / T))
    (hNN : ∀ i, 1 ≤ i → i ≤ q →
      ‖iteratedFDeriv ℝ i (adjointAngularGraph R) p‖ ≤ N i * H ^ (((i-1-Q : ℕ) : ℝ) / T))
    (hrA : ∀ i ≤ q, ‖iteratedFDeriv ℝ i r (adjointScalarGraph Y p)‖ ≤
      A i * H ^ (((i - Q : ℕ) : ℝ) / T))
    (hYB : ∀ i, 1 ≤ i → i ≤ q →
      ‖iteratedFDeriv ℝ i (adjointScalarGraph Y) p‖ ≤ B i * H ^ (((i-1-Q : ℕ) : ℝ) / T))
    (hfF : ∀ i ≤ q, ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦ flow p.1) p‖ ≤
      F i * H ^ (((i - Q : ℕ) : ℝ) / T)) :
    ‖iteratedFDeriv ℝ q (fun p : AdjointSymbolPoint n ↦
        normalizedTransportAmplitude c ρ r Y flow p.1.1 p.1.2 (R • p.2)) p‖ ≤
      adjointLeibnizBudget
        (adjointLeibnizBudget (adjointLeibnizBudget C (compositionBudget P N))
          (compositionBudget A B)) F q * H ^ (((q - Q : ℕ) : ℝ) / T) := by
  have hPN := compositionBudget_nonneg hP hNpos
  apply local_product_reserve_profile p (((hc.mul (hρ.comp p hN)).mul (hr.comp p hY))) hf Q q _ F
    (adjointLeibnizBudget_nonneg (adjointLeibnizBudget_nonneg hC hPN)
      (compositionBudget_nonneg hA hB)) hF hH hT _ hfF
  intro i hi
  apply local_product_reserve_profile p (hc.mul (hρ.comp p hN)) (hr.comp p hY) Q i _ _
    (adjointLeibnizBudget_nonneg hC hPN) (compositionBudget_nonneg hA hB) hH hT
  · intro j hj
    apply local_product_reserve_profile p hc (hρ.comp p hN) Q j C _ hC hPN hH hT
      (fun k hk ↦ hcC k (hk.trans (hj.trans hi)))
    intro k hk
    exact local_pullback_reserve_profile (adjointAngularGraph R) _ p hN hρ Q k P N hP hNpos hH hT
      (fun l hl ↦ hρP l (hl.trans (hk.trans (hj.trans hi))))
      (fun l hl hl' ↦ hNN l hl (hl'.trans (hk.trans (hj.trans hi))))
  · intro j hj
    exact local_pullback_reserve_profile (adjointScalarGraph Y) r p hY hr Q j A B hA hB hH hT
      (fun k hk ↦ hrA k (hk.trans (hj.trans hi)))
      (fun k hk hk' ↦ hYB k hk (hk'.trans (hj.trans hi)))

end JanetCartan.ContinuumAdjoint.DerivativeKernels
