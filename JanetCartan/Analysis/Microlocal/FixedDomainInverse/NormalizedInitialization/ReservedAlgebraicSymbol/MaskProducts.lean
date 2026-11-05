module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Algebraic.LocalCalculus

/-!
# Multiply the original algebraic masks without losing reserve

Only a local inverse germ is available at a retained covector. The finite
Leibniz estimate below uses that germ and preserves the natural subtraction
reserve. Consumer: the original physical masks and radial multiplier in
`ReservedAlgebraicSymbol.exists_selected_algebraic_full_source_reserved_profiles`
(`app:ch_response:eq:direct-envelope-profile`).
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace JanetCartan.FixedDomainInverse.ReservedAlgebraicSymbol

open FiniteChain.Retarded.KernelDecay

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

/-- The original complex masks multiply the selected inverse germ with a
finite Leibniz convolution and retain the same subtraction reserve. No
global inverse smoothness is assumed (`high-amplitude`,
`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_algebraic_mask_product_reserved_jet_le
    {f : V → ℂ} {g : V → F} {v : V}
    (hf : ContDiffAt ℝ ∞ f v) (hg : ContDiffAt ℝ ∞ g v)
    {C D : ℕ → ℝ} (hC : ∀ j, 0 ≤ C j) (hD : ∀ j, 0 ≤ D j)
    {L : ℝ} (hL : 1 ≤ L) (R : ℕ)
    (hfjet : ∀ j, ‖iteratedFDeriv ℝ j f v‖ ≤ C j * L ^ (j-R))
    (hgjet : ∀ j, ‖iteratedFDeriv ℝ j g v‖ ≤ D j * L ^ (j-R)) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun w ↦ f w • g w) v‖ ≤
      derivativeConvolution C D k * L ^ (k-R) := by
  obtain ⟨U, hU, hfu⟩ := hf.contDiffOn (m := (k : ℕ∞ω)) (by simp) (by simp)
  obtain ⟨W, hW, hgu⟩ := hg.contDiffOn (m := (k : ℕ∞ω)) (by simp) (by simp)
  obtain ⟨O, hOsub, hO, hv⟩ := mem_nhds_iff.mp (inter_mem hU hW)
  have h := norm_iteratedFDerivWithin_smul_le
    (hfu.mono (hOsub.trans inter_subset_left)) (hgu.mono (hOsub.trans inter_subset_right))
    hO.uniqueDiffOn hv (n := k) le_rfl
  simp only [iteratedFDerivWithin_of_isOpen _ hO hv] at h
  apply h.trans
  simp only [derivativeConvolution, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  calc
    _ ≤ (k.choose j : ℝ) * (C j * L ^ (j-R)) * (D (k-j) * L ^ (k-j-R)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hfjet j) (Nat.cast_nonneg _)) (hgjet _)
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _)
          (mul_nonneg (hC _) (pow_nonneg (zero_le_one.trans hL) _)))
    _ = ((k.choose j : ℝ) * C j * D (k-j)) * L ^ ((j-R)+(k-j-R)) := by
      rw [pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hL (by omega))
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC _)) (hD _))

end JanetCartan.FixedDomainInverse.ReservedAlgebraicSymbol
