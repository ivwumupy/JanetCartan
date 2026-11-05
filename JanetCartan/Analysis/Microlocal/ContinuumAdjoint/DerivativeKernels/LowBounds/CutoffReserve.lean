module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.JointBounds
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.Realization.Cutoff
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.SymbolJets.PrimitiveBounds

/-!
# Uniform primitive jets of the concrete carrier exhaustion

The regularization reserve for `app:ch_background:prop:bg-adjoint`. The fixed
bump's derivatives are bounded on their compact support. After dilation, the
operator norm of the input rescaling is at most two wherever these derivatives
can be nonzero. The constant is independent of the exhaustion index.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow ModifiedNormalSymbol Pseudodifferential
variable {n : ℕ}

/-- The concrete smooth compact exhaustion satisfies the precise finite
primitive scaled-jet interface of the normal estimate. No regularizer derivative
estimate is an input (`app:ch_background:prop:bg-adjoint`). -/
theorem exists_uniform_modifiedCarrierCutoff_reserve (N : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ M ≥ 0, ∀ k, PrimitiveRegularizerReserve N ρ M (modifiedCarrierCutoff (n := n) k) := by
  obtain ⟨D, hD, hd⟩ := (hasCompactSupport_modifiedCarrierCutoff (n := n) 0).exists_bound_iteratedFDeriv (contDiff_modifiedCarrierCutoff 0) N
  refine ⟨D * 2^N, by positivity, ?_⟩
  intro k
  refine ⟨by positivity, ?_⟩
  intro r hr u hu j hj
  have hr0 : 0 < r := hρ.trans_le hr
  have hk : 0 < (k : ℝ) + 1 := by positivity
  let d : ℝ := ((k : ℝ) + 1)⁻¹
  let T : CarrierVariable n →L[ℝ] CarrierVariable n :=
    (d • ContinuousLinearMap.id ℝ CarrierParameter).prodMap
      ((d * r) • ContinuousLinearMap.id ℝ (Euclidean (n - 1)))
  have hd0 : 0 ≤ d := le_of_lt (inv_pos.mpr hk)
  have hd1 : d ≤ 1 := inv_le_one₀ hk |>.mpr (by linarith [Nat.cast_nonneg (α := ℝ) k])
  have he : scaledOriginalRegularizer (modifiedCarrierCutoff (n := n) k) r =
      modifiedCarrierCutoff 0 ∘ T := by
    funext v
    rw [scaledOriginalRegularizer, modifiedCarrierCutoff_eq_dilate]
    change modifiedCarrierCutoff 0 (d • v.1, d • (r • v.2)) =
      modifiedCarrierCutoff 0 (d • v.1, (d * r) • v.2)
    rw [smul_smul]
  rw [he]
  have hc := norm_iteratedFDeriv_comp_linear_le T (modifiedCarrierCutoff (n := n) 0)
    (contDiff_modifiedCarrierCutoff 0) j u
  by_cases hrk : r ≤ 2 * ((k : ℝ) + 1)
  · have hdr : d * r ≤ 2 := by
      rw [show d * r = r / ((k : ℝ) + 1) by dsimp [d]; ring]
      exact (div_le_iff₀ hk).mpr hrk
    have hT : ‖T‖ ≤ 2 := by
      apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
      intro v
      change ‖(d • v.1, (d * r) • v.2)‖ ≤ 2 * ‖v‖
      rw [Prod.norm_def, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hd0, abs_of_nonneg (mul_nonneg hd0 hr0.le)]
      apply max_le
      · exact mul_le_mul (hd1.trans (by norm_num)) (norm_fst_le v) (norm_nonneg _) (by norm_num)
      · exact mul_le_mul hdr (norm_snd_le v) (norm_nonneg _) (by norm_num)
    exact hc.trans ((mul_le_mul (hd j hj _) (pow_le_pow_left₀ (norm_nonneg _) hT j)
      (by positivity) hD).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num) hj) hD))
  · have hdr : 2 < d * r := by
      rw [show d * r = r / ((k : ℝ) + 1) by dsimp [d]; ring]
      exact (lt_div_iff₀ hk).mpr (lt_of_not_ge hrk)
    have hnorm : 2 < ‖T u‖ := by
      calc
        2 < d * r := hdr
        _ = ‖(T u).2‖ := by
          simp [T, norm_smul, Real.norm_eq_abs, abs_of_nonneg hd0, abs_of_pos hr0, hu]
        _ ≤ ‖T u‖ := norm_snd_le _
    have hout : T u ∉ tsupport (modifiedCarrierCutoff (n := n) 0) := by
      simpa [modifiedCarrierCutoff, ContDiffBump.tsupport_eq, modifiedCarrierCutoffBump]
        using (not_le.mpr hnorm)
    have hz : iteratedFDeriv ℝ j (modifiedCarrierCutoff (n := n) 0) (T u) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun ht ↦ hout (tsupport_iteratedFDeriv_subset j ht))
    rw [hz, norm_zero, zero_mul] at hc
    exact hc.trans (by positivity)

end JanetCartan.ContinuumAdjoint.DerivativeKernels
